/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover033
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03266 : selected 8 ⟨103081, by decide⟩
    (prefixPartial 13 27653) = some ⟨13, 2, 0, 103081, 27653, 3973, 16384⟩ := by
  decide +kernel

theorem context_13_27653_103081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27653 ⟨103081, by decide⟩ :=
  accepted_of_selected 13 27653 ⟨103081, by decide⟩ ⟨13, 2, 0, 103081, 27653, 3973, 16384⟩
    (by decide) selected_cut_03266

theorem selected_cut_03267 : selected 8 ⟨103143, by decide⟩
    (prefixPartial 13 27654) = some ⟨13, 2, 0, 103143, 27654, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_27654_103143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27654 ⟨103143, by decide⟩ :=
  accepted_of_selected 13 27654 ⟨103143, by decide⟩ ⟨13, 2, 0, 103143, 27654, 2665, 16384⟩
    (by decide) selected_cut_03267

theorem selected_cut_03268 : selected 8 ⟨103160, by decide⟩
    (prefixPartial 13 27655) = some ⟨13, 2, 0, 103160, 27655, 993, 16384⟩ := by
  decide +kernel

theorem context_13_27655_103160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27655 ⟨103160, by decide⟩ :=
  accepted_of_selected 13 27655 ⟨103160, by decide⟩ ⟨13, 2, 0, 103160, 27655, 993, 16384⟩
    (by decide) selected_cut_03268

theorem unmarked_context_12_6913_103161 : frontier 9 ⟨103161, by decide⟩
    (prefixCache 12 6913) (prefixPartial 12 6913) = false := by
  decide +kernel

theorem node_context_12_6913_103161 : EJMOriginalGlobalDAGData.nodes 9 ⟨103161, by decide⟩ =
    .split (coordinate 12) (![⟨102990, by decide⟩,⟨103081, by decide⟩,⟨103143, by decide⟩,⟨103160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6913_103161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6913 ⟨103161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6913
    ⟨103161, by decide⟩ (by decide) (![⟨102990, by decide⟩,⟨103081, by decide⟩,⟨103143, by decide⟩,⟨103160, by decide⟩]) unmarked_context_12_6913_103161 node_context_12_6913_103161
  intro a
  fin_cases a
  · exact context_13_27652_102990
  · exact context_13_27653_103081
  · exact context_13_27654_103143
  · exact context_13_27655_103160

theorem selected_cut_03269 : selected 7 ⟨103197, by decide⟩
    (prefixPartial 14 110624) = some ⟨14, 2, 0, 103197, 110624, 1673, 4096⟩ := by
  decide +kernel

theorem context_14_110624_103197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110624 ⟨103197, by decide⟩ :=
  accepted_of_selected 14 110624 ⟨103197, by decide⟩ ⟨14, 2, 0, 103197, 110624, 1673, 4096⟩
    (by decide) selected_cut_03269

theorem selected_cut_03270 : selected 7 ⟨103221, by decide⟩
    (prefixPartial 14 110625) = some ⟨14, 2, 0, 103221, 110625, 1337, 4096⟩ := by
  decide +kernel

theorem context_14_110625_103221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110625 ⟨103221, by decide⟩ :=
  accepted_of_selected 14 110625 ⟨103221, by decide⟩ ⟨14, 2, 0, 103221, 110625, 1337, 4096⟩
    (by decide) selected_cut_03270

theorem selected_cut_03271 : selected 7 ⟨103249, by decide⟩
    (prefixPartial 14 110626) = some ⟨14, 2, 0, 103249, 110626, 1525, 4096⟩ := by
  decide +kernel

theorem context_14_110626_103249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110626 ⟨103249, by decide⟩ :=
  accepted_of_selected 14 110626 ⟨103249, by decide⟩ ⟨14, 2, 0, 103249, 110626, 1525, 4096⟩
    (by decide) selected_cut_03271

theorem selected_cut_03272 : selected 7 ⟨103269, by decide⟩
    (prefixPartial 14 110627) = some ⟨14, 2, 0, 103269, 110627, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_110627_103269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110627 ⟨103269, by decide⟩ :=
  accepted_of_selected 14 110627 ⟨103269, by decide⟩ ⟨14, 2, 0, 103269, 110627, 1145, 4096⟩
    (by decide) selected_cut_03272

theorem unmarked_context_13_27656_103270 : frontier 8 ⟨103270, by decide⟩
    (prefixCache 13 27656) (prefixPartial 13 27656) = false := by
  decide +kernel

theorem node_context_13_27656_103270 : EJMOriginalGlobalDAGData.nodes 8 ⟨103270, by decide⟩ =
    .split (coordinate 13) (![⟨103197, by decide⟩,⟨103221, by decide⟩,⟨103249, by decide⟩,⟨103269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27656_103270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27656 ⟨103270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27656
    ⟨103270, by decide⟩ (by decide) (![⟨103197, by decide⟩,⟨103221, by decide⟩,⟨103249, by decide⟩,⟨103269, by decide⟩]) unmarked_context_13_27656_103270 node_context_13_27656_103270
  intro a
  fin_cases a
  · exact context_14_110624_103197
  · exact context_14_110625_103221
  · exact context_14_110626_103249
  · exact context_14_110627_103269

theorem selected_cut_03273 : selected 7 ⟨103291, by decide⟩
    (prefixPartial 14 110628) = some ⟨14, 2, 0, 103291, 110628, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_110628_103291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110628 ⟨103291, by decide⟩ :=
  accepted_of_selected 14 110628 ⟨103291, by decide⟩ ⟨14, 2, 0, 103291, 110628, 1085, 4096⟩
    (by decide) selected_cut_03273

theorem selected_cut_03274 : selected 7 ⟨103313, by decide⟩
    (prefixPartial 14 110629) = some ⟨14, 2, 0, 103313, 110629, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_110629_103313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110629 ⟨103313, by decide⟩ :=
  accepted_of_selected 14 110629 ⟨103313, by decide⟩ ⟨14, 2, 0, 103313, 110629, 1145, 4096⟩
    (by decide) selected_cut_03274

theorem selected_cut_03275 : selected 7 ⟨103333, by decide⟩
    (prefixPartial 14 110630) = some ⟨14, 2, 0, 103333, 110630, 1013, 4096⟩ := by
  decide +kernel

theorem context_14_110630_103333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110630 ⟨103333, by decide⟩ :=
  accepted_of_selected 14 110630 ⟨103333, by decide⟩ ⟨14, 2, 0, 103333, 110630, 1013, 4096⟩
    (by decide) selected_cut_03275

theorem selected_cut_03276 : selected 7 ⟨103356, by decide⟩
    (prefixPartial 14 110631) = some ⟨14, 2, 0, 103356, 110631, 1005, 4096⟩ := by
  decide +kernel

theorem context_14_110631_103356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110631 ⟨103356, by decide⟩ :=
  accepted_of_selected 14 110631 ⟨103356, by decide⟩ ⟨14, 2, 0, 103356, 110631, 1005, 4096⟩
    (by decide) selected_cut_03276

theorem unmarked_context_13_27657_103357 : frontier 8 ⟨103357, by decide⟩
    (prefixCache 13 27657) (prefixPartial 13 27657) = false := by
  decide +kernel

theorem node_context_13_27657_103357 : EJMOriginalGlobalDAGData.nodes 8 ⟨103357, by decide⟩ =
    .split (coordinate 13) (![⟨103291, by decide⟩,⟨103313, by decide⟩,⟨103333, by decide⟩,⟨103356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27657_103357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27657 ⟨103357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27657
    ⟨103357, by decide⟩ (by decide) (![⟨103291, by decide⟩,⟨103313, by decide⟩,⟨103333, by decide⟩,⟨103356, by decide⟩]) unmarked_context_13_27657_103357 node_context_13_27657_103357
  intro a
  fin_cases a
  · exact context_14_110628_103291
  · exact context_14_110629_103313
  · exact context_14_110630_103333
  · exact context_14_110631_103356

theorem selected_cut_03277 : selected 8 ⟨103416, by decide⟩
    (prefixPartial 13 27658) = some ⟨13, 2, 0, 103416, 27658, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_27658_103416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27658 ⟨103416, by decide⟩ :=
  accepted_of_selected 13 27658 ⟨103416, by decide⟩ ⟨13, 2, 0, 103416, 27658, 2757, 16384⟩
    (by decide) selected_cut_03277

theorem selected_cut_03278 : selected 8 ⟨103429, by decide⟩
    (prefixPartial 13 27659) = some ⟨13, 2, 0, 103429, 27659, 989, 16384⟩ := by
  decide +kernel

theorem context_13_27659_103429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27659 ⟨103429, by decide⟩ :=
  accepted_of_selected 13 27659 ⟨103429, by decide⟩ ⟨13, 2, 0, 103429, 27659, 989, 16384⟩
    (by decide) selected_cut_03278

theorem unmarked_context_12_6914_103430 : frontier 9 ⟨103430, by decide⟩
    (prefixCache 12 6914) (prefixPartial 12 6914) = false := by
  decide +kernel

theorem node_context_12_6914_103430 : EJMOriginalGlobalDAGData.nodes 9 ⟨103430, by decide⟩ =
    .split (coordinate 12) (![⟨103270, by decide⟩,⟨103357, by decide⟩,⟨103416, by decide⟩,⟨103429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6914_103430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6914 ⟨103430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6914
    ⟨103430, by decide⟩ (by decide) (![⟨103270, by decide⟩,⟨103357, by decide⟩,⟨103416, by decide⟩,⟨103429, by decide⟩]) unmarked_context_12_6914_103430 node_context_12_6914_103430
  intro a
  fin_cases a
  · exact context_13_27656_103270
  · exact context_13_27657_103357
  · exact context_13_27658_103416
  · exact context_13_27659_103429

theorem selected_cut_03279 : selected 7 ⟨103460, by decide⟩
    (prefixPartial 14 110640) = some ⟨14, 2, 0, 103460, 110640, 1421, 4096⟩ := by
  decide +kernel

theorem context_14_110640_103460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110640 ⟨103460, by decide⟩ :=
  accepted_of_selected 14 110640 ⟨103460, by decide⟩ ⟨14, 2, 0, 103460, 110640, 1421, 4096⟩
    (by decide) selected_cut_03279

theorem selected_cut_03280 : selected 7 ⟨103479, by decide⟩
    (prefixPartial 14 110641) = some ⟨14, 2, 0, 103479, 110641, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_110641_103479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110641 ⟨103479, by decide⟩ :=
  accepted_of_selected 14 110641 ⟨103479, by decide⟩ ⟨14, 2, 0, 103479, 110641, 1221, 4096⟩
    (by decide) selected_cut_03280

theorem selected_cut_03281 : selected 7 ⟨103500, by decide⟩
    (prefixPartial 14 110642) = some ⟨14, 2, 0, 103500, 110642, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_110642_103500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110642 ⟨103500, by decide⟩ :=
  accepted_of_selected 14 110642 ⟨103500, by decide⟩ ⟨14, 2, 0, 103500, 110642, 1193, 4096⟩
    (by decide) selected_cut_03281

theorem selected_cut_03282 : selected 7 ⟨103515, by decide⟩
    (prefixPartial 14 110643) = some ⟨14, 2, 0, 103515, 110643, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_110643_103515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110643 ⟨103515, by decide⟩ :=
  accepted_of_selected 14 110643 ⟨103515, by decide⟩ ⟨14, 2, 0, 103515, 110643, 1037, 4096⟩
    (by decide) selected_cut_03282

theorem unmarked_context_13_27660_103516 : frontier 8 ⟨103516, by decide⟩
    (prefixCache 13 27660) (prefixPartial 13 27660) = false := by
  decide +kernel

theorem node_context_13_27660_103516 : EJMOriginalGlobalDAGData.nodes 8 ⟨103516, by decide⟩ =
    .split (coordinate 13) (![⟨103460, by decide⟩,⟨103479, by decide⟩,⟨103500, by decide⟩,⟨103515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27660_103516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27660 ⟨103516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27660
    ⟨103516, by decide⟩ (by decide) (![⟨103460, by decide⟩,⟨103479, by decide⟩,⟨103500, by decide⟩,⟨103515, by decide⟩]) unmarked_context_13_27660_103516 node_context_13_27660_103516
  intro a
  fin_cases a
  · exact context_14_110640_103460
  · exact context_14_110641_103479
  · exact context_14_110642_103500
  · exact context_14_110643_103515

theorem selected_cut_03283 : selected 8 ⟨103580, by decide⟩
    (prefixPartial 13 27661) = some ⟨13, 2, 0, 103580, 27661, 3821, 16384⟩ := by
  decide +kernel

theorem context_13_27661_103580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27661 ⟨103580, by decide⟩ :=
  accepted_of_selected 13 27661 ⟨103580, by decide⟩ ⟨13, 2, 0, 103580, 27661, 3821, 16384⟩
    (by decide) selected_cut_03283

theorem selected_cut_03284 : selected 8 ⟨103615, by decide⟩
    (prefixPartial 13 27662) = some ⟨13, 2, 0, 103615, 27662, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_27662_103615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27662 ⟨103615, by decide⟩ :=
  accepted_of_selected 13 27662 ⟨103615, by decide⟩ ⟨13, 2, 0, 103615, 27662, 2509, 16384⟩
    (by decide) selected_cut_03284

theorem selected_cut_03285 : selected 8 ⟨103626, by decide⟩
    (prefixPartial 13 27663) = some ⟨13, 2, 0, 103626, 27663, 925, 16384⟩ := by
  decide +kernel

theorem context_13_27663_103626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27663 ⟨103626, by decide⟩ :=
  accepted_of_selected 13 27663 ⟨103626, by decide⟩ ⟨13, 2, 0, 103626, 27663, 925, 16384⟩
    (by decide) selected_cut_03285

theorem unmarked_context_12_6915_103627 : frontier 9 ⟨103627, by decide⟩
    (prefixCache 12 6915) (prefixPartial 12 6915) = false := by
  decide +kernel

theorem node_context_12_6915_103627 : EJMOriginalGlobalDAGData.nodes 9 ⟨103627, by decide⟩ =
    .split (coordinate 12) (![⟨103516, by decide⟩,⟨103580, by decide⟩,⟨103615, by decide⟩,⟨103626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6915_103627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6915 ⟨103627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6915
    ⟨103627, by decide⟩ (by decide) (![⟨103516, by decide⟩,⟨103580, by decide⟩,⟨103615, by decide⟩,⟨103626, by decide⟩]) unmarked_context_12_6915_103627 node_context_12_6915_103627
  intro a
  fin_cases a
  · exact context_13_27660_103516
  · exact context_13_27661_103580
  · exact context_13_27662_103615
  · exact context_13_27663_103626

theorem unmarked_context_11_1728_103628 : frontier 10 ⟨103628, by decide⟩
    (prefixCache 11 1728) (prefixPartial 11 1728) = false := by
  decide +kernel

theorem node_context_11_1728_103628 : EJMOriginalGlobalDAGData.nodes 10 ⟨103628, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨103161, by decide⟩,⟨103430, by decide⟩,⟨103627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1728_103628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1728 ⟨103628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1728
    ⟨103628, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨103161, by decide⟩,⟨103430, by decide⟩,⟨103627, by decide⟩]) unmarked_context_11_1728_103628 node_context_11_1728_103628
  intro a
  fin_cases a
  · exact context_12_6912_34034
  · exact context_12_6913_103161
  · exact context_12_6914_103430
  · exact context_12_6915_103627

theorem selected_cut_03286 : selected 7 ⟨103691, by decide⟩
    (prefixPartial 14 110656) = some ⟨14, 2, 0, 103691, 110656, 2357, 4096⟩ := by
  decide +kernel

theorem context_14_110656_103691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110656 ⟨103691, by decide⟩ :=
  accepted_of_selected 14 110656 ⟨103691, by decide⟩ ⟨14, 2, 0, 103691, 110656, 2357, 4096⟩
    (by decide) selected_cut_03286

theorem selected_cut_03287 : selected 7 ⟨103713, by decide⟩
    (prefixPartial 14 110657) = some ⟨14, 2, 0, 103713, 110657, 833, 4096⟩ := by
  decide +kernel

theorem context_14_110657_103713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110657 ⟨103713, by decide⟩ :=
  accepted_of_selected 14 110657 ⟨103713, by decide⟩ ⟨14, 2, 0, 103713, 110657, 833, 4096⟩
    (by decide) selected_cut_03287

theorem selected_cut_03288 : selected 7 ⟨103740, by decide⟩
    (prefixPartial 14 110658) = some ⟨14, 2, 0, 103740, 110658, 821, 4096⟩ := by
  decide +kernel

theorem context_14_110658_103740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110658 ⟨103740, by decide⟩ :=
  accepted_of_selected 14 110658 ⟨103740, by decide⟩ ⟨14, 2, 0, 103740, 110658, 821, 4096⟩
    (by decide) selected_cut_03288

theorem selected_cut_03289 : selected 7 ⟨103753, by decide⟩
    (prefixPartial 14 110659) = some ⟨14, 2, 0, 103753, 110659, 221, 4096⟩ := by
  decide +kernel

theorem context_14_110659_103753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110659 ⟨103753, by decide⟩ :=
  accepted_of_selected 14 110659 ⟨103753, by decide⟩ ⟨14, 2, 0, 103753, 110659, 221, 4096⟩
    (by decide) selected_cut_03289

theorem unmarked_context_13_27664_103754 : frontier 8 ⟨103754, by decide⟩
    (prefixCache 13 27664) (prefixPartial 13 27664) = false := by
  decide +kernel

theorem node_context_13_27664_103754 : EJMOriginalGlobalDAGData.nodes 8 ⟨103754, by decide⟩ =
    .split (coordinate 13) (![⟨103691, by decide⟩,⟨103713, by decide⟩,⟨103740, by decide⟩,⟨103753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27664_103754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27664 ⟨103754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27664
    ⟨103754, by decide⟩ (by decide) (![⟨103691, by decide⟩,⟨103713, by decide⟩,⟨103740, by decide⟩,⟨103753, by decide⟩]) unmarked_context_13_27664_103754 node_context_13_27664_103754
  intro a
  fin_cases a
  · exact context_14_110656_103691
  · exact context_14_110657_103713
  · exact context_14_110658_103740
  · exact context_14_110659_103753

theorem selected_cut_03290 : selected 7 ⟨103811, by decide⟩
    (prefixPartial 14 110660) = some ⟨14, 2, 0, 103811, 110660, 2097, 4096⟩ := by
  decide +kernel

theorem context_14_110660_103811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110660 ⟨103811, by decide⟩ :=
  accepted_of_selected 14 110660 ⟨103811, by decide⟩ ⟨14, 2, 0, 103811, 110660, 2097, 4096⟩
    (by decide) selected_cut_03290

theorem selected_cut_03291 : selected 7 ⟨103857, by decide⟩
    (prefixPartial 14 110661) = some ⟨14, 2, 0, 103857, 110661, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_110661_103857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110661 ⟨103857, by decide⟩ :=
  accepted_of_selected 14 110661 ⟨103857, by decide⟩ ⟨14, 2, 0, 103857, 110661, 1405, 4096⟩
    (by decide) selected_cut_03291

theorem selected_cut_03292 : selected 7 ⟨103884, by decide⟩
    (prefixPartial 14 110662) = some ⟨14, 2, 0, 103884, 110662, 829, 4096⟩ := by
  decide +kernel

theorem context_14_110662_103884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110662 ⟨103884, by decide⟩ :=
  accepted_of_selected 14 110662 ⟨103884, by decide⟩ ⟨14, 2, 0, 103884, 110662, 829, 4096⟩
    (by decide) selected_cut_03292

theorem selected_cut_03293 : selected 7 ⟨103892, by decide⟩
    (prefixPartial 14 110663) = some ⟨14, 2, 0, 103892, 110663, 197, 4096⟩ := by
  decide +kernel

theorem context_14_110663_103892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110663 ⟨103892, by decide⟩ :=
  accepted_of_selected 14 110663 ⟨103892, by decide⟩ ⟨14, 2, 0, 103892, 110663, 197, 4096⟩
    (by decide) selected_cut_03293

theorem unmarked_context_13_27665_103893 : frontier 8 ⟨103893, by decide⟩
    (prefixCache 13 27665) (prefixPartial 13 27665) = false := by
  decide +kernel

theorem node_context_13_27665_103893 : EJMOriginalGlobalDAGData.nodes 8 ⟨103893, by decide⟩ =
    .split (coordinate 13) (![⟨103811, by decide⟩,⟨103857, by decide⟩,⟨103884, by decide⟩,⟨103892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27665_103893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27665 ⟨103893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27665
    ⟨103893, by decide⟩ (by decide) (![⟨103811, by decide⟩,⟨103857, by decide⟩,⟨103884, by decide⟩,⟨103892, by decide⟩]) unmarked_context_13_27665_103893 node_context_13_27665_103893
  intro a
  fin_cases a
  · exact context_14_110660_103811
  · exact context_14_110661_103857
  · exact context_14_110662_103884
  · exact context_14_110663_103892

theorem selected_cut_03294 : selected 7 ⟨103945, by decide⟩
    (prefixPartial 14 110664) = some ⟨14, 2, 0, 103945, 110664, 1513, 4096⟩ := by
  decide +kernel

theorem context_14_110664_103945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110664 ⟨103945, by decide⟩ :=
  accepted_of_selected 14 110664 ⟨103945, by decide⟩ ⟨14, 2, 0, 103945, 110664, 1513, 4096⟩
    (by decide) selected_cut_03294

theorem selected_cut_03295 : selected 7 ⟨104005, by decide⟩
    (prefixPartial 14 110665) = some ⟨14, 2, 0, 104005, 110665, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_110665_104005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110665 ⟨104005, by decide⟩ :=
  accepted_of_selected 14 110665 ⟨104005, by decide⟩ ⟨14, 2, 0, 104005, 110665, 1361, 4096⟩
    (by decide) selected_cut_03295

theorem selected_cut_03296 : selected 7 ⟨104057, by decide⟩
    (prefixPartial 14 110666) = some ⟨14, 2, 0, 104057, 110666, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_110666_104057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110666 ⟨104057, by decide⟩ :=
  accepted_of_selected 14 110666 ⟨104057, by decide⟩ ⟨14, 2, 0, 104057, 110666, 1121, 4096⟩
    (by decide) selected_cut_03296

theorem selected_cut_03297 : selected 7 ⟨104114, by decide⟩
    (prefixPartial 14 110667) = some ⟨14, 2, 0, 104114, 110667, 893, 4096⟩ := by
  decide +kernel

theorem context_14_110667_104114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110667 ⟨104114, by decide⟩ :=
  accepted_of_selected 14 110667 ⟨104114, by decide⟩ ⟨14, 2, 0, 104114, 110667, 893, 4096⟩
    (by decide) selected_cut_03297

theorem unmarked_context_13_27666_104115 : frontier 8 ⟨104115, by decide⟩
    (prefixCache 13 27666) (prefixPartial 13 27666) = false := by
  decide +kernel

theorem node_context_13_27666_104115 : EJMOriginalGlobalDAGData.nodes 8 ⟨104115, by decide⟩ =
    .split (coordinate 13) (![⟨103945, by decide⟩,⟨104005, by decide⟩,⟨104057, by decide⟩,⟨104114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27666_104115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27666 ⟨104115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27666
    ⟨104115, by decide⟩ (by decide) (![⟨103945, by decide⟩,⟨104005, by decide⟩,⟨104057, by decide⟩,⟨104114, by decide⟩]) unmarked_context_13_27666_104115 node_context_13_27666_104115
  intro a
  fin_cases a
  · exact context_14_110664_103945
  · exact context_14_110665_104005
  · exact context_14_110666_104057
  · exact context_14_110667_104114

theorem selected_cut_03298 : selected 8 ⟨4592, by decide⟩
    (prefixPartial 13 27667) = some ⟨13, 1, 0, 4592, 27667, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27667_4592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27667 ⟨4592, by decide⟩ :=
  accepted_of_selected 13 27667 ⟨4592, by decide⟩ ⟨13, 1, 0, 4592, 27667, 1, 16384⟩
    (by decide) selected_cut_03298

theorem unmarked_context_12_6916_104116 : frontier 9 ⟨104116, by decide⟩
    (prefixCache 12 6916) (prefixPartial 12 6916) = false := by
  decide +kernel

theorem node_context_12_6916_104116 : EJMOriginalGlobalDAGData.nodes 9 ⟨104116, by decide⟩ =
    .split (coordinate 12) (![⟨103754, by decide⟩,⟨103893, by decide⟩,⟨104115, by decide⟩,⟨4592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6916_104116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6916 ⟨104116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6916
    ⟨104116, by decide⟩ (by decide) (![⟨103754, by decide⟩,⟨103893, by decide⟩,⟨104115, by decide⟩,⟨4592, by decide⟩]) unmarked_context_12_6916_104116 node_context_12_6916_104116
  intro a
  fin_cases a
  · exact context_13_27664_103754
  · exact context_13_27665_103893
  · exact context_13_27666_104115
  · exact context_13_27667_4592

theorem selected_cut_03299 : selected 7 ⟨104145, by decide⟩
    (prefixPartial 14 110672) = some ⟨14, 2, 0, 104145, 110672, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_110672_104145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110672 ⟨104145, by decide⟩ :=
  accepted_of_selected 14 110672 ⟨104145, by decide⟩ ⟨14, 2, 0, 104145, 110672, 1433, 4096⟩
    (by decide) selected_cut_03299

theorem selected_cut_03300 : selected 7 ⟨104174, by decide⟩
    (prefixPartial 14 110673) = some ⟨14, 2, 0, 104174, 110673, 1349, 4096⟩ := by
  decide +kernel

theorem context_14_110673_104174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110673 ⟨104174, by decide⟩ :=
  accepted_of_selected 14 110673 ⟨104174, by decide⟩ ⟨14, 2, 0, 104174, 110673, 1349, 4096⟩
    (by decide) selected_cut_03300

theorem selected_cut_03301 : selected 7 ⟨104200, by decide⟩
    (prefixPartial 14 110674) = some ⟨14, 2, 0, 104200, 110674, 1733, 4096⟩ := by
  decide +kernel

theorem context_14_110674_104200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110674 ⟨104200, by decide⟩ :=
  accepted_of_selected 14 110674 ⟨104200, by decide⟩ ⟨14, 2, 0, 104200, 110674, 1733, 4096⟩
    (by decide) selected_cut_03301

theorem selected_cut_03302 : selected 7 ⟨104221, by decide⟩
    (prefixPartial 14 110675) = some ⟨14, 2, 0, 104221, 110675, 1309, 4096⟩ := by
  decide +kernel

theorem context_14_110675_104221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110675 ⟨104221, by decide⟩ :=
  accepted_of_selected 14 110675 ⟨104221, by decide⟩ ⟨14, 2, 0, 104221, 110675, 1309, 4096⟩
    (by decide) selected_cut_03302

theorem unmarked_context_13_27668_104222 : frontier 8 ⟨104222, by decide⟩
    (prefixCache 13 27668) (prefixPartial 13 27668) = false := by
  decide +kernel

theorem node_context_13_27668_104222 : EJMOriginalGlobalDAGData.nodes 8 ⟨104222, by decide⟩ =
    .split (coordinate 13) (![⟨104145, by decide⟩,⟨104174, by decide⟩,⟨104200, by decide⟩,⟨104221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27668_104222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27668 ⟨104222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27668
    ⟨104222, by decide⟩ (by decide) (![⟨104145, by decide⟩,⟨104174, by decide⟩,⟨104200, by decide⟩,⟨104221, by decide⟩]) unmarked_context_13_27668_104222 node_context_13_27668_104222
  intro a
  fin_cases a
  · exact context_14_110672_104145
  · exact context_14_110673_104174
  · exact context_14_110674_104200
  · exact context_14_110675_104221

theorem selected_cut_03303 : selected 7 ⟨104241, by decide⟩
    (prefixPartial 14 110676) = some ⟨14, 2, 0, 104241, 110676, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_110676_104241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110676 ⟨104241, by decide⟩ :=
  accepted_of_selected 14 110676 ⟨104241, by decide⟩ ⟨14, 2, 0, 104241, 110676, 1093, 4096⟩
    (by decide) selected_cut_03303

theorem selected_cut_03304 : selected 7 ⟨104266, by decide⟩
    (prefixPartial 14 110677) = some ⟨14, 2, 0, 104266, 110677, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_110677_104266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110677 ⟨104266, by decide⟩ :=
  accepted_of_selected 14 110677 ⟨104266, by decide⟩ ⟨14, 2, 0, 104266, 110677, 1293, 4096⟩
    (by decide) selected_cut_03304

theorem selected_cut_03305 : selected 7 ⟨104288, by decide⟩
    (prefixPartial 14 110678) = some ⟨14, 2, 0, 104288, 110678, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_110678_104288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110678 ⟨104288, by decide⟩ :=
  accepted_of_selected 14 110678 ⟨104288, by decide⟩ ⟨14, 2, 0, 104288, 110678, 1229, 4096⟩
    (by decide) selected_cut_03305

theorem selected_cut_03306 : selected 7 ⟨104310, by decide⟩
    (prefixPartial 14 110679) = some ⟨14, 2, 0, 104310, 110679, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_110679_104310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110679 ⟨104310, by decide⟩ :=
  accepted_of_selected 14 110679 ⟨104310, by decide⟩ ⟨14, 2, 0, 104310, 110679, 1189, 4096⟩
    (by decide) selected_cut_03306

theorem unmarked_context_13_27669_104311 : frontier 8 ⟨104311, by decide⟩
    (prefixCache 13 27669) (prefixPartial 13 27669) = false := by
  decide +kernel

theorem node_context_13_27669_104311 : EJMOriginalGlobalDAGData.nodes 8 ⟨104311, by decide⟩ =
    .split (coordinate 13) (![⟨104241, by decide⟩,⟨104266, by decide⟩,⟨104288, by decide⟩,⟨104310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27669_104311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27669 ⟨104311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27669
    ⟨104311, by decide⟩ (by decide) (![⟨104241, by decide⟩,⟨104266, by decide⟩,⟨104288, by decide⟩,⟨104310, by decide⟩]) unmarked_context_13_27669_104311 node_context_13_27669_104311
  intro a
  fin_cases a
  · exact context_14_110676_104241
  · exact context_14_110677_104266
  · exact context_14_110678_104288
  · exact context_14_110679_104310

theorem selected_cut_03307 : selected 8 ⟨104391, by decide⟩
    (prefixPartial 13 27670) = some ⟨13, 2, 0, 104391, 27670, 3301, 16384⟩ := by
  decide +kernel

theorem context_13_27670_104391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27670 ⟨104391, by decide⟩ :=
  accepted_of_selected 13 27670 ⟨104391, by decide⟩ ⟨13, 2, 0, 104391, 27670, 3301, 16384⟩
    (by decide) selected_cut_03307

theorem selected_cut_03308 : selected 8 ⟨104429, by decide⟩
    (prefixPartial 13 27671) = some ⟨13, 2, 0, 104429, 27671, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_27671_104429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27671 ⟨104429, by decide⟩ :=
  accepted_of_selected 13 27671 ⟨104429, by decide⟩ ⟨13, 2, 0, 104429, 27671, 1273, 16384⟩
    (by decide) selected_cut_03308

theorem unmarked_context_12_6917_104430 : frontier 9 ⟨104430, by decide⟩
    (prefixCache 12 6917) (prefixPartial 12 6917) = false := by
  decide +kernel

theorem node_context_12_6917_104430 : EJMOriginalGlobalDAGData.nodes 9 ⟨104430, by decide⟩ =
    .split (coordinate 12) (![⟨104222, by decide⟩,⟨104311, by decide⟩,⟨104391, by decide⟩,⟨104429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6917_104430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6917 ⟨104430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6917
    ⟨104430, by decide⟩ (by decide) (![⟨104222, by decide⟩,⟨104311, by decide⟩,⟨104391, by decide⟩,⟨104429, by decide⟩]) unmarked_context_12_6917_104430 node_context_12_6917_104430
  intro a
  fin_cases a
  · exact context_13_27668_104222
  · exact context_13_27669_104311
  · exact context_13_27670_104391
  · exact context_13_27671_104429

theorem selected_cut_03309 : selected 7 ⟨104459, by decide⟩
    (prefixPartial 14 110688) = some ⟨14, 2, 0, 104459, 110688, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_110688_104459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110688 ⟨104459, by decide⟩ :=
  accepted_of_selected 14 110688 ⟨104459, by decide⟩ ⟨14, 2, 0, 104459, 110688, 1361, 4096⟩
    (by decide) selected_cut_03309

theorem selected_cut_03310 : selected 7 ⟨104485, by decide⟩
    (prefixPartial 14 110689) = some ⟨14, 2, 0, 104485, 110689, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_110689_104485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110689 ⟨104485, by decide⟩ :=
  accepted_of_selected 14 110689 ⟨104485, by decide⟩ ⟨14, 2, 0, 104485, 110689, 1297, 4096⟩
    (by decide) selected_cut_03310

theorem selected_cut_03311 : selected 7 ⟨104521, by decide⟩
    (prefixPartial 14 110690) = some ⟨14, 2, 0, 104521, 110690, 1925, 4096⟩ := by
  decide +kernel

theorem context_14_110690_104521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110690 ⟨104521, by decide⟩ :=
  accepted_of_selected 14 110690 ⟨104521, by decide⟩ ⟨14, 2, 0, 104521, 110690, 1925, 4096⟩
    (by decide) selected_cut_03311

theorem selected_cut_03312 : selected 7 ⟨104540, by decide⟩
    (prefixPartial 14 110691) = some ⟨14, 2, 0, 104540, 110691, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_110691_104540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110691 ⟨104540, by decide⟩ :=
  accepted_of_selected 14 110691 ⟨104540, by decide⟩ ⟨14, 2, 0, 104540, 110691, 1293, 4096⟩
    (by decide) selected_cut_03312

theorem unmarked_context_13_27672_104541 : frontier 8 ⟨104541, by decide⟩
    (prefixCache 13 27672) (prefixPartial 13 27672) = false := by
  decide +kernel

theorem node_context_13_27672_104541 : EJMOriginalGlobalDAGData.nodes 8 ⟨104541, by decide⟩ =
    .split (coordinate 13) (![⟨104459, by decide⟩,⟨104485, by decide⟩,⟨104521, by decide⟩,⟨104540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27672_104541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27672 ⟨104541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27672
    ⟨104541, by decide⟩ (by decide) (![⟨104459, by decide⟩,⟨104485, by decide⟩,⟨104521, by decide⟩,⟨104540, by decide⟩]) unmarked_context_13_27672_104541 node_context_13_27672_104541
  intro a
  fin_cases a
  · exact context_14_110688_104459
  · exact context_14_110689_104485
  · exact context_14_110690_104521
  · exact context_14_110691_104540

theorem selected_cut_03313 : selected 7 ⟨104565, by decide⟩
    (prefixPartial 14 110692) = some ⟨14, 2, 0, 104565, 110692, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_110692_104565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110692 ⟨104565, by decide⟩ :=
  accepted_of_selected 14 110692 ⟨104565, by decide⟩ ⟨14, 2, 0, 104565, 110692, 1277, 4096⟩
    (by decide) selected_cut_03313

theorem selected_cut_03314 : selected 7 ⟨104585, by decide⟩
    (prefixPartial 14 110693) = some ⟨14, 2, 0, 104585, 110693, 1261, 4096⟩ := by
  decide +kernel

theorem context_14_110693_104585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110693 ⟨104585, by decide⟩ :=
  accepted_of_selected 14 110693 ⟨104585, by decide⟩ ⟨14, 2, 0, 104585, 110693, 1261, 4096⟩
    (by decide) selected_cut_03314

theorem selected_cut_03315 : selected 7 ⟨104608, by decide⟩
    (prefixPartial 14 110694) = some ⟨14, 2, 0, 104608, 110694, 1309, 4096⟩ := by
  decide +kernel

theorem context_14_110694_104608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110694 ⟨104608, by decide⟩ :=
  accepted_of_selected 14 110694 ⟨104608, by decide⟩ ⟨14, 2, 0, 104608, 110694, 1309, 4096⟩
    (by decide) selected_cut_03315

theorem selected_cut_03316 : selected 7 ⟨104629, by decide⟩
    (prefixPartial 14 110695) = some ⟨14, 2, 0, 104629, 110695, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_110695_104629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110695 ⟨104629, by decide⟩ :=
  accepted_of_selected 14 110695 ⟨104629, by decide⟩ ⟨14, 2, 0, 104629, 110695, 1121, 4096⟩
    (by decide) selected_cut_03316

theorem unmarked_context_13_27673_104630 : frontier 8 ⟨104630, by decide⟩
    (prefixCache 13 27673) (prefixPartial 13 27673) = false := by
  decide +kernel

theorem node_context_13_27673_104630 : EJMOriginalGlobalDAGData.nodes 8 ⟨104630, by decide⟩ =
    .split (coordinate 13) (![⟨104565, by decide⟩,⟨104585, by decide⟩,⟨104608, by decide⟩,⟨104629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27673_104630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27673 ⟨104630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27673
    ⟨104630, by decide⟩ (by decide) (![⟨104565, by decide⟩,⟨104585, by decide⟩,⟨104608, by decide⟩,⟨104629, by decide⟩]) unmarked_context_13_27673_104630 node_context_13_27673_104630
  intro a
  fin_cases a
  · exact context_14_110692_104565
  · exact context_14_110693_104585
  · exact context_14_110694_104608
  · exact context_14_110695_104629

theorem selected_cut_03317 : selected 8 ⟨104724, by decide⟩
    (prefixPartial 13 27674) = some ⟨13, 2, 0, 104724, 27674, 3649, 16384⟩ := by
  decide +kernel

theorem context_13_27674_104724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27674 ⟨104724, by decide⟩ :=
  accepted_of_selected 13 27674 ⟨104724, by decide⟩ ⟨13, 2, 0, 104724, 27674, 3649, 16384⟩
    (by decide) selected_cut_03317

theorem selected_cut_03318 : selected 8 ⟨104758, by decide⟩
    (prefixPartial 13 27675) = some ⟨13, 2, 0, 104758, 27675, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_27675_104758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27675 ⟨104758, by decide⟩ :=
  accepted_of_selected 13 27675 ⟨104758, by decide⟩ ⟨13, 2, 0, 104758, 27675, 1345, 16384⟩
    (by decide) selected_cut_03318

theorem unmarked_context_12_6918_104759 : frontier 9 ⟨104759, by decide⟩
    (prefixCache 12 6918) (prefixPartial 12 6918) = false := by
  decide +kernel

theorem node_context_12_6918_104759 : EJMOriginalGlobalDAGData.nodes 9 ⟨104759, by decide⟩ =
    .split (coordinate 12) (![⟨104541, by decide⟩,⟨104630, by decide⟩,⟨104724, by decide⟩,⟨104758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6918_104759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6918 ⟨104759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6918
    ⟨104759, by decide⟩ (by decide) (![⟨104541, by decide⟩,⟨104630, by decide⟩,⟨104724, by decide⟩,⟨104758, by decide⟩]) unmarked_context_12_6918_104759 node_context_12_6918_104759
  intro a
  fin_cases a
  · exact context_13_27672_104541
  · exact context_13_27673_104630
  · exact context_13_27674_104724
  · exact context_13_27675_104758

theorem selected_cut_03319 : selected 7 ⟨104781, by decide⟩
    (prefixPartial 14 110704) = some ⟨14, 2, 0, 104781, 110704, 957, 4096⟩ := by
  decide +kernel

theorem context_14_110704_104781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110704 ⟨104781, by decide⟩ :=
  accepted_of_selected 14 110704 ⟨104781, by decide⟩ ⟨14, 2, 0, 104781, 110704, 957, 4096⟩
    (by decide) selected_cut_03319

theorem selected_cut_03320 : selected 7 ⟨104799, by decide⟩
    (prefixPartial 14 110705) = some ⟨14, 2, 0, 104799, 110705, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_110705_104799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110705 ⟨104799, by decide⟩ :=
  accepted_of_selected 14 110705 ⟨104799, by decide⟩ ⟨14, 2, 0, 104799, 110705, 1065, 4096⟩
    (by decide) selected_cut_03320

theorem selected_cut_03321 : selected 7 ⟨104829, by decide⟩
    (prefixPartial 14 110706) = some ⟨14, 2, 0, 104829, 110706, 1605, 4096⟩ := by
  decide +kernel

theorem context_14_110706_104829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110706 ⟨104829, by decide⟩ :=
  accepted_of_selected 14 110706 ⟨104829, by decide⟩ ⟨14, 2, 0, 104829, 110706, 1605, 4096⟩
    (by decide) selected_cut_03321

theorem selected_cut_03322 : selected 7 ⟨104843, by decide⟩
    (prefixPartial 14 110707) = some ⟨14, 2, 0, 104843, 110707, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_110707_104843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110707 ⟨104843, by decide⟩ :=
  accepted_of_selected 14 110707 ⟨104843, by decide⟩ ⟨14, 2, 0, 104843, 110707, 1089, 4096⟩
    (by decide) selected_cut_03322

theorem unmarked_context_13_27676_104844 : frontier 8 ⟨104844, by decide⟩
    (prefixCache 13 27676) (prefixPartial 13 27676) = false := by
  decide +kernel

theorem node_context_13_27676_104844 : EJMOriginalGlobalDAGData.nodes 8 ⟨104844, by decide⟩ =
    .split (coordinate 13) (![⟨104781, by decide⟩,⟨104799, by decide⟩,⟨104829, by decide⟩,⟨104843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27676_104844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27676 ⟨104844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27676
    ⟨104844, by decide⟩ (by decide) (![⟨104781, by decide⟩,⟨104799, by decide⟩,⟨104829, by decide⟩,⟨104843, by decide⟩]) unmarked_context_13_27676_104844 node_context_13_27676_104844
  intro a
  fin_cases a
  · exact context_14_110704_104781
  · exact context_14_110705_104799
  · exact context_14_110706_104829
  · exact context_14_110707_104843

theorem selected_cut_03323 : selected 7 ⟨104859, by decide⟩
    (prefixPartial 14 110708) = some ⟨14, 2, 0, 104859, 110708, 1045, 4096⟩ := by
  decide +kernel

theorem context_14_110708_104859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110708 ⟨104859, by decide⟩ :=
  accepted_of_selected 14 110708 ⟨104859, by decide⟩ ⟨14, 2, 0, 104859, 110708, 1045, 4096⟩
    (by decide) selected_cut_03323

theorem selected_cut_03324 : selected 7 ⟨104890, by decide⟩
    (prefixPartial 14 110709) = some ⟨14, 2, 0, 104890, 110709, 1305, 4096⟩ := by
  decide +kernel

theorem context_14_110709_104890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110709 ⟨104890, by decide⟩ :=
  accepted_of_selected 14 110709 ⟨104890, by decide⟩ ⟨14, 2, 0, 104890, 110709, 1305, 4096⟩
    (by decide) selected_cut_03324

theorem selected_cut_03325 : selected 7 ⟨104911, by decide⟩
    (prefixPartial 14 110710) = some ⟨14, 2, 0, 104911, 110710, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_110710_104911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110710 ⟨104911, by decide⟩ :=
  accepted_of_selected 14 110710 ⟨104911, by decide⟩ ⟨14, 2, 0, 104911, 110710, 1153, 4096⟩
    (by decide) selected_cut_03325

theorem selected_cut_03326 : selected 7 ⟨104927, by decide⟩
    (prefixPartial 14 110711) = some ⟨14, 2, 0, 104927, 110711, 1041, 4096⟩ := by
  decide +kernel

theorem context_14_110711_104927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110711 ⟨104927, by decide⟩ :=
  accepted_of_selected 14 110711 ⟨104927, by decide⟩ ⟨14, 2, 0, 104927, 110711, 1041, 4096⟩
    (by decide) selected_cut_03326

theorem unmarked_context_13_27677_104928 : frontier 8 ⟨104928, by decide⟩
    (prefixCache 13 27677) (prefixPartial 13 27677) = false := by
  decide +kernel

theorem node_context_13_27677_104928 : EJMOriginalGlobalDAGData.nodes 8 ⟨104928, by decide⟩ =
    .split (coordinate 13) (![⟨104859, by decide⟩,⟨104890, by decide⟩,⟨104911, by decide⟩,⟨104927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27677_104928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27677 ⟨104928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27677
    ⟨104928, by decide⟩ (by decide) (![⟨104859, by decide⟩,⟨104890, by decide⟩,⟨104911, by decide⟩,⟨104927, by decide⟩]) unmarked_context_13_27677_104928 node_context_13_27677_104928
  intro a
  fin_cases a
  · exact context_14_110708_104859
  · exact context_14_110709_104890
  · exact context_14_110710_104911
  · exact context_14_110711_104927

theorem selected_cut_03327 : selected 8 ⟨104998, by decide⟩
    (prefixPartial 13 27678) = some ⟨13, 2, 0, 104998, 27678, 3201, 16384⟩ := by
  decide +kernel

theorem context_13_27678_104998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27678 ⟨104998, by decide⟩ :=
  accepted_of_selected 13 27678 ⟨104998, by decide⟩ ⟨13, 2, 0, 104998, 27678, 3201, 16384⟩
    (by decide) selected_cut_03327

theorem selected_cut_03328 : selected 8 ⟨105007, by decide⟩
    (prefixPartial 13 27679) = some ⟨13, 2, 0, 105007, 27679, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_27679_105007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27679 ⟨105007, by decide⟩ :=
  accepted_of_selected 13 27679 ⟨105007, by decide⟩ ⟨13, 2, 0, 105007, 27679, 1097, 16384⟩
    (by decide) selected_cut_03328

theorem unmarked_context_12_6919_105008 : frontier 9 ⟨105008, by decide⟩
    (prefixCache 12 6919) (prefixPartial 12 6919) = false := by
  decide +kernel

theorem node_context_12_6919_105008 : EJMOriginalGlobalDAGData.nodes 9 ⟨105008, by decide⟩ =
    .split (coordinate 12) (![⟨104844, by decide⟩,⟨104928, by decide⟩,⟨104998, by decide⟩,⟨105007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6919_105008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6919 ⟨105008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6919
    ⟨105008, by decide⟩ (by decide) (![⟨104844, by decide⟩,⟨104928, by decide⟩,⟨104998, by decide⟩,⟨105007, by decide⟩]) unmarked_context_12_6919_105008 node_context_12_6919_105008
  intro a
  fin_cases a
  · exact context_13_27676_104844
  · exact context_13_27677_104928
  · exact context_13_27678_104998
  · exact context_13_27679_105007

theorem unmarked_context_11_1729_105009 : frontier 10 ⟨105009, by decide⟩
    (prefixCache 11 1729) (prefixPartial 11 1729) = false := by
  decide +kernel

theorem node_context_11_1729_105009 : EJMOriginalGlobalDAGData.nodes 10 ⟨105009, by decide⟩ =
    .split (coordinate 11) (![⟨104116, by decide⟩,⟨104430, by decide⟩,⟨104759, by decide⟩,⟨105008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1729_105009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1729 ⟨105009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1729
    ⟨105009, by decide⟩ (by decide) (![⟨104116, by decide⟩,⟨104430, by decide⟩,⟨104759, by decide⟩,⟨105008, by decide⟩]) unmarked_context_11_1729_105009 node_context_11_1729_105009
  intro a
  fin_cases a
  · exact context_12_6916_104116
  · exact context_12_6917_104430
  · exact context_12_6918_104759
  · exact context_12_6919_105008

theorem selected_cut_03329 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 6920) = some ⟨12, 1, 0, 88909, 6920, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6920_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6920 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 6920 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 6920, 1, 65536⟩
    (by decide) selected_cut_03329

theorem selected_cut_03330 : selected 7 ⟨105023, by decide⟩
    (prefixPartial 14 110736) = some ⟨14, 2, 0, 105023, 110736, 653, 4096⟩ := by
  decide +kernel

theorem context_14_110736_105023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110736 ⟨105023, by decide⟩ :=
  accepted_of_selected 14 110736 ⟨105023, by decide⟩ ⟨14, 2, 0, 105023, 110736, 653, 4096⟩
    (by decide) selected_cut_03330

theorem selected_cut_03331 : selected 7 ⟨105050, by decide⟩
    (prefixPartial 14 110737) = some ⟨14, 2, 0, 105050, 110737, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_110737_105050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110737 ⟨105050, by decide⟩ :=
  accepted_of_selected 14 110737 ⟨105050, by decide⟩ ⟨14, 2, 0, 105050, 110737, 1245, 4096⟩
    (by decide) selected_cut_03331

theorem selected_cut_03332 : selected 7 ⟨105071, by decide⟩
    (prefixPartial 14 110738) = some ⟨14, 2, 0, 105071, 110738, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_110738_105071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110738 ⟨105071, by decide⟩ :=
  accepted_of_selected 14 110738 ⟨105071, by decide⟩ ⟨14, 2, 0, 105071, 110738, 1181, 4096⟩
    (by decide) selected_cut_03332

theorem selected_cut_03333 : selected 7 ⟨105090, by decide⟩
    (prefixPartial 14 110739) = some ⟨14, 2, 0, 105090, 110739, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_110739_105090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110739 ⟨105090, by decide⟩ :=
  accepted_of_selected 14 110739 ⟨105090, by decide⟩ ⟨14, 2, 0, 105090, 110739, 1121, 4096⟩
    (by decide) selected_cut_03333

theorem unmarked_context_13_27684_105091 : frontier 8 ⟨105091, by decide⟩
    (prefixCache 13 27684) (prefixPartial 13 27684) = false := by
  decide +kernel

theorem node_context_13_27684_105091 : EJMOriginalGlobalDAGData.nodes 8 ⟨105091, by decide⟩ =
    .split (coordinate 13) (![⟨105023, by decide⟩,⟨105050, by decide⟩,⟨105071, by decide⟩,⟨105090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27684_105091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27684 ⟨105091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27684
    ⟨105091, by decide⟩ (by decide) (![⟨105023, by decide⟩,⟨105050, by decide⟩,⟨105071, by decide⟩,⟨105090, by decide⟩]) unmarked_context_13_27684_105091 node_context_13_27684_105091
  intro a
  fin_cases a
  · exact context_14_110736_105023
  · exact context_14_110737_105050
  · exact context_14_110738_105071
  · exact context_14_110739_105090

theorem selected_cut_03334 : selected 7 ⟨105105, by decide⟩
    (prefixPartial 14 110740) = some ⟨14, 2, 0, 105105, 110740, 909, 4096⟩ := by
  decide +kernel

theorem context_14_110740_105105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110740 ⟨105105, by decide⟩ :=
  accepted_of_selected 14 110740 ⟨105105, by decide⟩ ⟨14, 2, 0, 105105, 110740, 909, 4096⟩
    (by decide) selected_cut_03334

theorem selected_cut_03335 : selected 7 ⟨105126, by decide⟩
    (prefixPartial 14 110741) = some ⟨14, 2, 0, 105126, 110741, 1197, 4096⟩ := by
  decide +kernel

theorem context_14_110741_105126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110741 ⟨105126, by decide⟩ :=
  accepted_of_selected 14 110741 ⟨105126, by decide⟩ ⟨14, 2, 0, 105126, 110741, 1197, 4096⟩
    (by decide) selected_cut_03335

theorem selected_cut_03336 : selected 7 ⟨105144, by decide⟩
    (prefixPartial 14 110742) = some ⟨14, 2, 0, 105144, 110742, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_110742_105144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110742 ⟨105144, by decide⟩ :=
  accepted_of_selected 14 110742 ⟨105144, by decide⟩ ⟨14, 2, 0, 105144, 110742, 1105, 4096⟩
    (by decide) selected_cut_03336

theorem selected_cut_03337 : selected 7 ⟨105161, by decide⟩
    (prefixPartial 14 110743) = some ⟨14, 2, 0, 105161, 110743, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_110743_105161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110743 ⟨105161, by decide⟩ :=
  accepted_of_selected 14 110743 ⟨105161, by decide⟩ ⟨14, 2, 0, 105161, 110743, 1033, 4096⟩
    (by decide) selected_cut_03337

theorem unmarked_context_13_27685_105162 : frontier 8 ⟨105162, by decide⟩
    (prefixCache 13 27685) (prefixPartial 13 27685) = false := by
  decide +kernel

theorem node_context_13_27685_105162 : EJMOriginalGlobalDAGData.nodes 8 ⟨105162, by decide⟩ =
    .split (coordinate 13) (![⟨105105, by decide⟩,⟨105126, by decide⟩,⟨105144, by decide⟩,⟨105161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27685_105162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27685 ⟨105162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27685
    ⟨105162, by decide⟩ (by decide) (![⟨105105, by decide⟩,⟨105126, by decide⟩,⟨105144, by decide⟩,⟨105161, by decide⟩]) unmarked_context_13_27685_105162 node_context_13_27685_105162
  intro a
  fin_cases a
  · exact context_14_110740_105105
  · exact context_14_110741_105126
  · exact context_14_110742_105144
  · exact context_14_110743_105161

theorem selected_cut_03338 : selected 8 ⟨105215, by decide⟩
    (prefixPartial 13 27686) = some ⟨13, 2, 0, 105215, 27686, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_27686_105215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27686 ⟨105215, by decide⟩ :=
  accepted_of_selected 13 27686 ⟨105215, by decide⟩ ⟨13, 2, 0, 105215, 27686, 2777, 16384⟩
    (by decide) selected_cut_03338

theorem selected_cut_03339 : selected 8 ⟨105238, by decide⟩
    (prefixPartial 13 27687) = some ⟨13, 2, 0, 105238, 27687, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_27687_105238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27687 ⟨105238, by decide⟩ :=
  accepted_of_selected 13 27687 ⟨105238, by decide⟩ ⟨13, 2, 0, 105238, 27687, 1245, 16384⟩
    (by decide) selected_cut_03339

theorem unmarked_context_12_6921_105239 : frontier 9 ⟨105239, by decide⟩
    (prefixCache 12 6921) (prefixPartial 12 6921) = false := by
  decide +kernel

theorem node_context_12_6921_105239 : EJMOriginalGlobalDAGData.nodes 9 ⟨105239, by decide⟩ =
    .split (coordinate 12) (![⟨105091, by decide⟩,⟨105162, by decide⟩,⟨105215, by decide⟩,⟨105238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6921_105239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6921 ⟨105239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6921
    ⟨105239, by decide⟩ (by decide) (![⟨105091, by decide⟩,⟨105162, by decide⟩,⟨105215, by decide⟩,⟨105238, by decide⟩]) unmarked_context_12_6921_105239 node_context_12_6921_105239
  intro a
  fin_cases a
  · exact context_13_27684_105091
  · exact context_13_27685_105162
  · exact context_13_27686_105215
  · exact context_13_27687_105238

theorem selected_cut_03340 : selected 8 ⟨105331, by decide⟩
    (prefixPartial 13 27688) = some ⟨13, 2, 0, 105331, 27688, 3773, 16384⟩ := by
  decide +kernel

theorem context_13_27688_105331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27688 ⟨105331, by decide⟩ :=
  accepted_of_selected 13 27688 ⟨105331, by decide⟩ ⟨13, 2, 0, 105331, 27688, 3773, 16384⟩
    (by decide) selected_cut_03340

theorem selected_cut_03341 : selected 7 ⟨105348, by decide⟩
    (prefixPartial 14 110756) = some ⟨14, 2, 0, 105348, 110756, 1109, 4096⟩ := by
  decide +kernel

theorem context_14_110756_105348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110756 ⟨105348, by decide⟩ :=
  accepted_of_selected 14 110756 ⟨105348, by decide⟩ ⟨14, 2, 0, 105348, 110756, 1109, 4096⟩
    (by decide) selected_cut_03341

theorem selected_cut_03342 : selected 7 ⟨105366, by decide⟩
    (prefixPartial 14 110757) = some ⟨14, 2, 0, 105366, 110757, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_110757_105366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110757 ⟨105366, by decide⟩ :=
  accepted_of_selected 14 110757 ⟨105366, by decide⟩ ⟨14, 2, 0, 105366, 110757, 1117, 4096⟩
    (by decide) selected_cut_03342

theorem selected_cut_03343 : selected 7 ⟨105383, by decide⟩
    (prefixPartial 14 110758) = some ⟨14, 2, 0, 105383, 110758, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_110758_105383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110758 ⟨105383, by decide⟩ :=
  accepted_of_selected 14 110758 ⟨105383, by decide⟩ ⟨14, 2, 0, 105383, 110758, 1021, 4096⟩
    (by decide) selected_cut_03343

theorem selected_cut_03344 : selected 7 ⟨105398, by decide⟩
    (prefixPartial 14 110759) = some ⟨14, 2, 0, 105398, 110759, 965, 4096⟩ := by
  decide +kernel

theorem context_14_110759_105398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110759 ⟨105398, by decide⟩ :=
  accepted_of_selected 14 110759 ⟨105398, by decide⟩ ⟨14, 2, 0, 105398, 110759, 965, 4096⟩
    (by decide) selected_cut_03344

theorem unmarked_context_13_27689_105399 : frontier 8 ⟨105399, by decide⟩
    (prefixCache 13 27689) (prefixPartial 13 27689) = false := by
  decide +kernel

theorem node_context_13_27689_105399 : EJMOriginalGlobalDAGData.nodes 8 ⟨105399, by decide⟩ =
    .split (coordinate 13) (![⟨105348, by decide⟩,⟨105366, by decide⟩,⟨105383, by decide⟩,⟨105398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27689_105399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27689 ⟨105399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27689
    ⟨105399, by decide⟩ (by decide) (![⟨105348, by decide⟩,⟨105366, by decide⟩,⟨105383, by decide⟩,⟨105398, by decide⟩]) unmarked_context_13_27689_105399 node_context_13_27689_105399
  intro a
  fin_cases a
  · exact context_14_110756_105348
  · exact context_14_110757_105366
  · exact context_14_110758_105383
  · exact context_14_110759_105398

theorem selected_cut_03345 : selected 8 ⟨105442, by decide⟩
    (prefixPartial 13 27690) = some ⟨13, 2, 0, 105442, 27690, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_27690_105442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27690 ⟨105442, by decide⟩ :=
  accepted_of_selected 13 27690 ⟨105442, by decide⟩ ⟨13, 2, 0, 105442, 27690, 2665, 16384⟩
    (by decide) selected_cut_03345

theorem selected_cut_03346 : selected 8 ⟨105455, by decide⟩
    (prefixPartial 13 27691) = some ⟨13, 2, 0, 105455, 27691, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_27691_105455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27691 ⟨105455, by decide⟩ :=
  accepted_of_selected 13 27691 ⟨105455, by decide⟩ ⟨13, 2, 0, 105455, 27691, 1057, 16384⟩
    (by decide) selected_cut_03346

theorem unmarked_context_12_6922_105456 : frontier 9 ⟨105456, by decide⟩
    (prefixCache 12 6922) (prefixPartial 12 6922) = false := by
  decide +kernel

theorem node_context_12_6922_105456 : EJMOriginalGlobalDAGData.nodes 9 ⟨105456, by decide⟩ =
    .split (coordinate 12) (![⟨105331, by decide⟩,⟨105399, by decide⟩,⟨105442, by decide⟩,⟨105455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6922_105456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6922 ⟨105456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6922
    ⟨105456, by decide⟩ (by decide) (![⟨105331, by decide⟩,⟨105399, by decide⟩,⟨105442, by decide⟩,⟨105455, by decide⟩]) unmarked_context_12_6922_105456 node_context_12_6922_105456
  intro a
  fin_cases a
  · exact context_13_27688_105331
  · exact context_13_27689_105399
  · exact context_13_27690_105442
  · exact context_13_27691_105455

theorem selected_cut_03347 : selected 8 ⟨105530, by decide⟩
    (prefixPartial 13 27692) = some ⟨13, 2, 0, 105530, 27692, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_27692_105530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27692 ⟨105530, by decide⟩ :=
  accepted_of_selected 13 27692 ⟨105530, by decide⟩ ⟨13, 2, 0, 105530, 27692, 3337, 16384⟩
    (by decide) selected_cut_03347

theorem selected_cut_03348 : selected 8 ⟨105596, by decide⟩
    (prefixPartial 13 27693) = some ⟨13, 2, 0, 105596, 27693, 4041, 16384⟩ := by
  decide +kernel

theorem context_13_27693_105596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27693 ⟨105596, by decide⟩ :=
  accepted_of_selected 13 27693 ⟨105596, by decide⟩ ⟨13, 2, 0, 105596, 27693, 4041, 16384⟩
    (by decide) selected_cut_03348

theorem selected_cut_03349 : selected 8 ⟨105627, by decide⟩
    (prefixPartial 13 27694) = some ⟨13, 2, 0, 105627, 27694, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_27694_105627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27694 ⟨105627, by decide⟩ :=
  accepted_of_selected 13 27694 ⟨105627, by decide⟩ ⟨13, 2, 0, 105627, 27694, 2373, 16384⟩
    (by decide) selected_cut_03349

theorem selected_cut_03350 : selected 8 ⟨105635, by decide⟩
    (prefixPartial 13 27695) = some ⟨13, 2, 0, 105635, 27695, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_27695_105635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27695 ⟨105635, by decide⟩ :=
  accepted_of_selected 13 27695 ⟨105635, by decide⟩ ⟨13, 2, 0, 105635, 27695, 1045, 16384⟩
    (by decide) selected_cut_03350

theorem unmarked_context_12_6923_105636 : frontier 9 ⟨105636, by decide⟩
    (prefixCache 12 6923) (prefixPartial 12 6923) = false := by
  decide +kernel

theorem node_context_12_6923_105636 : EJMOriginalGlobalDAGData.nodes 9 ⟨105636, by decide⟩ =
    .split (coordinate 12) (![⟨105530, by decide⟩,⟨105596, by decide⟩,⟨105627, by decide⟩,⟨105635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6923_105636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6923 ⟨105636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6923
    ⟨105636, by decide⟩ (by decide) (![⟨105530, by decide⟩,⟨105596, by decide⟩,⟨105627, by decide⟩,⟨105635, by decide⟩]) unmarked_context_12_6923_105636 node_context_12_6923_105636
  intro a
  fin_cases a
  · exact context_13_27692_105530
  · exact context_13_27693_105596
  · exact context_13_27694_105627
  · exact context_13_27695_105635

theorem unmarked_context_11_1730_105637 : frontier 10 ⟨105637, by decide⟩
    (prefixCache 11 1730) (prefixPartial 11 1730) = false := by
  decide +kernel

theorem node_context_11_1730_105637 : EJMOriginalGlobalDAGData.nodes 10 ⟨105637, by decide⟩ =
    .split (coordinate 11) (![⟨88909, by decide⟩,⟨105239, by decide⟩,⟨105456, by decide⟩,⟨105636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1730_105637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1730 ⟨105637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1730
    ⟨105637, by decide⟩ (by decide) (![⟨88909, by decide⟩,⟨105239, by decide⟩,⟨105456, by decide⟩,⟨105636, by decide⟩]) unmarked_context_11_1730_105637 node_context_11_1730_105637
  intro a
  fin_cases a
  · exact context_12_6920_88909
  · exact context_12_6921_105239
  · exact context_12_6922_105456
  · exact context_12_6923_105636

theorem selected_cut_03351 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 6924) = some ⟨12, 1, 0, 4596, 6924, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6924_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6924 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 6924 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 6924, 1, 65536⟩
    (by decide) selected_cut_03351

theorem selected_cut_03352 : selected 8 ⟨105733, by decide⟩
    (prefixPartial 13 27700) = some ⟨13, 2, 0, 105733, 27700, 3825, 16384⟩ := by
  decide +kernel

theorem context_13_27700_105733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27700 ⟨105733, by decide⟩ :=
  accepted_of_selected 13 27700 ⟨105733, by decide⟩ ⟨13, 2, 0, 105733, 27700, 3825, 16384⟩
    (by decide) selected_cut_03352

theorem selected_cut_03353 : selected 7 ⟨105752, by decide⟩
    (prefixPartial 14 110804) = some ⟨14, 2, 0, 105752, 110804, 949, 4096⟩ := by
  decide +kernel

theorem context_14_110804_105752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110804 ⟨105752, by decide⟩ :=
  accepted_of_selected 14 110804 ⟨105752, by decide⟩ ⟨14, 2, 0, 105752, 110804, 949, 4096⟩
    (by decide) selected_cut_03353

theorem selected_cut_03354 : selected 7 ⟨105774, by decide⟩
    (prefixPartial 14 110805) = some ⟨14, 2, 0, 105774, 110805, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_110805_105774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110805 ⟨105774, by decide⟩ :=
  accepted_of_selected 14 110805 ⟨105774, by decide⟩ ⟨14, 2, 0, 105774, 110805, 1177, 4096⟩
    (by decide) selected_cut_03354

theorem selected_cut_03355 : selected 7 ⟨105790, by decide⟩
    (prefixPartial 14 110806) = some ⟨14, 2, 0, 105790, 110806, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_110806_105790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110806 ⟨105790, by decide⟩ :=
  accepted_of_selected 14 110806 ⟨105790, by decide⟩ ⟨14, 2, 0, 105790, 110806, 1145, 4096⟩
    (by decide) selected_cut_03355

theorem selected_cut_03356 : selected 7 ⟨105811, by decide⟩
    (prefixPartial 14 110807) = some ⟨14, 2, 0, 105811, 110807, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_110807_105811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110807 ⟨105811, by decide⟩ :=
  accepted_of_selected 14 110807 ⟨105811, by decide⟩ ⟨14, 2, 0, 105811, 110807, 1093, 4096⟩
    (by decide) selected_cut_03356

theorem unmarked_context_13_27701_105812 : frontier 8 ⟨105812, by decide⟩
    (prefixCache 13 27701) (prefixPartial 13 27701) = false := by
  decide +kernel

theorem node_context_13_27701_105812 : EJMOriginalGlobalDAGData.nodes 8 ⟨105812, by decide⟩ =
    .split (coordinate 13) (![⟨105752, by decide⟩,⟨105774, by decide⟩,⟨105790, by decide⟩,⟨105811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27701_105812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27701 ⟨105812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27701
    ⟨105812, by decide⟩ (by decide) (![⟨105752, by decide⟩,⟨105774, by decide⟩,⟨105790, by decide⟩,⟨105811, by decide⟩]) unmarked_context_13_27701_105812 node_context_13_27701_105812
  intro a
  fin_cases a
  · exact context_14_110804_105752
  · exact context_14_110805_105774
  · exact context_14_110806_105790
  · exact context_14_110807_105811

theorem selected_cut_03357 : selected 8 ⟨105870, by decide⟩
    (prefixPartial 13 27702) = some ⟨13, 2, 0, 105870, 27702, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_27702_105870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27702 ⟨105870, by decide⟩ :=
  accepted_of_selected 13 27702 ⟨105870, by decide⟩ ⟨13, 2, 0, 105870, 27702, 3225, 16384⟩
    (by decide) selected_cut_03357

theorem selected_cut_03358 : selected 8 ⟨105884, by decide⟩
    (prefixPartial 13 27703) = some ⟨13, 2, 0, 105884, 27703, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_27703_105884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27703 ⟨105884, by decide⟩ :=
  accepted_of_selected 13 27703 ⟨105884, by decide⟩ ⟨13, 2, 0, 105884, 27703, 1173, 16384⟩
    (by decide) selected_cut_03358

theorem unmarked_context_12_6925_105885 : frontier 9 ⟨105885, by decide⟩
    (prefixCache 12 6925) (prefixPartial 12 6925) = false := by
  decide +kernel

theorem node_context_12_6925_105885 : EJMOriginalGlobalDAGData.nodes 9 ⟨105885, by decide⟩ =
    .split (coordinate 12) (![⟨105733, by decide⟩,⟨105812, by decide⟩,⟨105870, by decide⟩,⟨105884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6925_105885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6925 ⟨105885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6925
    ⟨105885, by decide⟩ (by decide) (![⟨105733, by decide⟩,⟨105812, by decide⟩,⟨105870, by decide⟩,⟨105884, by decide⟩]) unmarked_context_12_6925_105885 node_context_12_6925_105885
  intro a
  fin_cases a
  · exact context_13_27700_105733
  · exact context_13_27701_105812
  · exact context_13_27702_105870
  · exact context_13_27703_105884

theorem selected_cut_03359 : selected 8 ⟨105959, by decide⟩
    (prefixPartial 13 27704) = some ⟨13, 2, 0, 105959, 27704, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_27704_105959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27704 ⟨105959, by decide⟩ :=
  accepted_of_selected 13 27704 ⟨105959, by decide⟩ ⟨13, 2, 0, 105959, 27704, 3421, 16384⟩
    (by decide) selected_cut_03359

theorem selected_cut_03360 : selected 7 ⟨105978, by decide⟩
    (prefixPartial 14 110820) = some ⟨14, 2, 0, 105978, 110820, 1293, 4096⟩ := by
  decide +kernel

theorem context_14_110820_105978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110820 ⟨105978, by decide⟩ :=
  accepted_of_selected 14 110820 ⟨105978, by decide⟩ ⟨14, 2, 0, 105978, 110820, 1293, 4096⟩
    (by decide) selected_cut_03360

theorem selected_cut_03361 : selected 7 ⟨105998, by decide⟩
    (prefixPartial 14 110821) = some ⟨14, 2, 0, 105998, 110821, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_110821_105998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110821 ⟨105998, by decide⟩ :=
  accepted_of_selected 14 110821 ⟨105998, by decide⟩ ⟨14, 2, 0, 105998, 110821, 1273, 4096⟩
    (by decide) selected_cut_03361

theorem selected_cut_03362 : selected 7 ⟨106022, by decide⟩
    (prefixPartial 14 110822) = some ⟨14, 2, 0, 106022, 110822, 1317, 4096⟩ := by
  decide +kernel

theorem context_14_110822_106022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110822 ⟨106022, by decide⟩ :=
  accepted_of_selected 14 110822 ⟨106022, by decide⟩ ⟨14, 2, 0, 106022, 110822, 1317, 4096⟩
    (by decide) selected_cut_03362

theorem selected_cut_03363 : selected 7 ⟨106038, by decide⟩
    (prefixPartial 14 110823) = some ⟨14, 2, 0, 106038, 110823, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_110823_106038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110823 ⟨106038, by decide⟩ :=
  accepted_of_selected 14 110823 ⟨106038, by decide⟩ ⟨14, 2, 0, 106038, 110823, 1033, 4096⟩
    (by decide) selected_cut_03363

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
