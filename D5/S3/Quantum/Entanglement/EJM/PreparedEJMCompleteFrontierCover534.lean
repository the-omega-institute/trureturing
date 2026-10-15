/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover533
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_51265 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70144) = some ⟨10, 1, 0, 1468246, 70144, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70144_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70144 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70144 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70144, 1, 1048576⟩
    (by decide) selected_cut_51265

theorem selected_cut_51266 : selected 10 ⟨1476069, by decide⟩
    (prefixPartial 11 280580) = some ⟨11, 2, 0, 1476069, 280580, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_280580_1476069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280580 ⟨1476069, by decide⟩ :=
  accepted_of_selected 11 280580 ⟨1476069, by decide⟩ ⟨11, 2, 0, 1476069, 280580, 2429, 262144⟩
    (by decide) selected_cut_51266

theorem selected_cut_51267 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 280581) = some ⟨11, 1, 0, 1468419, 280581, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280581_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280581 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 280581 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 280581, 1, 262144⟩
    (by decide) selected_cut_51267

theorem selected_cut_51268 : selected 10 ⟨1476204, by decide⟩
    (prefixPartial 11 280582) = some ⟨11, 2, 0, 1476204, 280582, 2669, 262144⟩ := by
  decide +kernel

theorem context_11_280582_1476204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280582 ⟨1476204, by decide⟩ :=
  accepted_of_selected 11 280582 ⟨1476204, by decide⟩ ⟨11, 2, 0, 1476204, 280582, 2669, 262144⟩
    (by decide) selected_cut_51268

theorem selected_cut_51269 : selected 10 ⟨1476312, by decide⟩
    (prefixPartial 11 280583) = some ⟨11, 2, 0, 1476312, 280583, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_280583_1476312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280583 ⟨1476312, by decide⟩ :=
  accepted_of_selected 11 280583 ⟨1476312, by decide⟩ ⟨11, 2, 0, 1476312, 280583, 1821, 262144⟩
    (by decide) selected_cut_51269

theorem unmarked_context_10_70145_1476313 : frontier 11 ⟨1476313, by decide⟩
    (prefixCache 10 70145) (prefixPartial 10 70145) = false := by
  decide +kernel

theorem node_context_10_70145_1476313 : EJMOriginalGlobalDAGData.nodes 11 ⟨1476313, by decide⟩ =
    .split (coordinate 10) (![⟨1476069, by decide⟩,⟨1468419, by decide⟩,⟨1476204, by decide⟩,⟨1476312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70145_1476313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70145 ⟨1476313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70145
    ⟨1476313, by decide⟩ (by decide) (![⟨1476069, by decide⟩,⟨1468419, by decide⟩,⟨1476204, by decide⟩,⟨1476312, by decide⟩]) unmarked_context_10_70145_1476313 node_context_10_70145_1476313
  intro a
  fin_cases a
  · exact context_11_280580_1476069
  · exact context_11_280581_1468419
  · exact context_11_280582_1476204
  · exact context_11_280583_1476312

theorem selected_cut_51270 : selected 11 ⟨1476508, by decide⟩
    (prefixPartial 10 70146) = some ⟨10, 2, 0, 1476508, 70146, 3297, 1048576⟩ := by
  decide +kernel

theorem context_10_70146_1476508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70146 ⟨1476508, by decide⟩ :=
  accepted_of_selected 10 70146 ⟨1476508, by decide⟩ ⟨10, 2, 0, 1476508, 70146, 3297, 1048576⟩
    (by decide) selected_cut_51270

theorem selected_cut_51271 : selected 11 ⟨1476558, by decide⟩
    (prefixPartial 10 70147) = some ⟨10, 2, 0, 1476558, 70147, 481, 1048576⟩ := by
  decide +kernel

theorem context_10_70147_1476558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70147 ⟨1476558, by decide⟩ :=
  accepted_of_selected 10 70147 ⟨1476558, by decide⟩ ⟨10, 2, 0, 1476558, 70147, 481, 1048576⟩
    (by decide) selected_cut_51271

theorem unmarked_context_9_17536_1476559 : frontier 12 ⟨1476559, by decide⟩
    (prefixCache 9 17536) (prefixPartial 9 17536) = false := by
  decide +kernel

theorem node_context_9_17536_1476559 : EJMOriginalGlobalDAGData.nodes 12 ⟨1476559, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1476313, by decide⟩,⟨1476508, by decide⟩,⟨1476558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17536_1476559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17536 ⟨1476559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17536
    ⟨1476559, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1476313, by decide⟩,⟨1476508, by decide⟩,⟨1476558, by decide⟩]) unmarked_context_9_17536_1476559 node_context_9_17536_1476559
  intro a
  fin_cases a
  · exact context_10_70144_1468246
  · exact context_10_70145_1476313
  · exact context_10_70146_1476508
  · exact context_10_70147_1476558

theorem selected_cut_51272 : selected 11 ⟨1476682, by decide⟩
    (prefixPartial 10 70148) = some ⟨10, 2, 0, 1476682, 70148, 2881, 1048576⟩ := by
  decide +kernel

theorem context_10_70148_1476682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70148 ⟨1476682, by decide⟩ :=
  accepted_of_selected 10 70148 ⟨1476682, by decide⟩ ⟨10, 2, 0, 1476682, 70148, 2881, 1048576⟩
    (by decide) selected_cut_51272

theorem selected_cut_51273 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70149) = some ⟨10, 1, 0, 1468874, 70149, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70149_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70149 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70149 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70149, 1, 1048576⟩
    (by decide) selected_cut_51273

theorem selected_cut_51274 : selected 11 ⟨1476879, by decide⟩
    (prefixPartial 10 70150) = some ⟨10, 2, 0, 1476879, 70150, 3057, 1048576⟩ := by
  decide +kernel

theorem context_10_70150_1476879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70150 ⟨1476879, by decide⟩ :=
  accepted_of_selected 10 70150 ⟨1476879, by decide⟩ ⟨10, 2, 0, 1476879, 70150, 3057, 1048576⟩
    (by decide) selected_cut_51274

theorem selected_cut_51275 : selected 11 ⟨1476986, by decide⟩
    (prefixPartial 10 70151) = some ⟨10, 2, 0, 1476986, 70151, 1425, 1048576⟩ := by
  decide +kernel

theorem context_10_70151_1476986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70151 ⟨1476986, by decide⟩ :=
  accepted_of_selected 10 70151 ⟨1476986, by decide⟩ ⟨10, 2, 0, 1476986, 70151, 1425, 1048576⟩
    (by decide) selected_cut_51275

theorem unmarked_context_9_17537_1476987 : frontier 12 ⟨1476987, by decide⟩
    (prefixCache 9 17537) (prefixPartial 9 17537) = false := by
  decide +kernel

theorem node_context_9_17537_1476987 : EJMOriginalGlobalDAGData.nodes 12 ⟨1476987, by decide⟩ =
    .split (coordinate 9) (![⟨1476682, by decide⟩,⟨1468874, by decide⟩,⟨1476879, by decide⟩,⟨1476986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17537_1476987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17537 ⟨1476987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17537
    ⟨1476987, by decide⟩ (by decide) (![⟨1476682, by decide⟩,⟨1468874, by decide⟩,⟨1476879, by decide⟩,⟨1476986, by decide⟩]) unmarked_context_9_17537_1476987 node_context_9_17537_1476987
  intro a
  fin_cases a
  · exact context_10_70148_1476682
  · exact context_10_70149_1468874
  · exact context_10_70150_1476879
  · exact context_10_70151_1476986

theorem selected_cut_51276 : selected 11 ⟨1477105, by decide⟩
    (prefixPartial 10 70152) = some ⟨10, 2, 0, 1477105, 70152, 1845, 1048576⟩ := by
  decide +kernel

theorem context_10_70152_1477105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70152 ⟨1477105, by decide⟩ :=
  accepted_of_selected 10 70152 ⟨1477105, by decide⟩ ⟨10, 2, 0, 1477105, 70152, 1845, 1048576⟩
    (by decide) selected_cut_51276

theorem selected_cut_51277 : selected 11 ⟨1477225, by decide⟩
    (prefixPartial 10 70153) = some ⟨10, 2, 0, 1477225, 70153, 1813, 1048576⟩ := by
  decide +kernel

theorem context_10_70153_1477225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70153 ⟨1477225, by decide⟩ :=
  accepted_of_selected 10 70153 ⟨1477225, by decide⟩ ⟨10, 2, 0, 1477225, 70153, 1813, 1048576⟩
    (by decide) selected_cut_51277

theorem selected_cut_51278 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70154) = some ⟨10, 1, 0, 1469103, 70154, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70154_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70154 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70154 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70154, 1, 1048576⟩
    (by decide) selected_cut_51278

theorem selected_cut_51279 : selected 11 ⟨1477277, by decide⟩
    (prefixPartial 10 70155) = some ⟨10, 2, 0, 1477277, 70155, 625, 1048576⟩ := by
  decide +kernel

theorem context_10_70155_1477277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70155 ⟨1477277, by decide⟩ :=
  accepted_of_selected 10 70155 ⟨1477277, by decide⟩ ⟨10, 2, 0, 1477277, 70155, 625, 1048576⟩
    (by decide) selected_cut_51279

theorem unmarked_context_9_17538_1477278 : frontier 12 ⟨1477278, by decide⟩
    (prefixCache 9 17538) (prefixPartial 9 17538) = false := by
  decide +kernel

theorem node_context_9_17538_1477278 : EJMOriginalGlobalDAGData.nodes 12 ⟨1477278, by decide⟩ =
    .split (coordinate 9) (![⟨1477105, by decide⟩,⟨1477225, by decide⟩,⟨1469103, by decide⟩,⟨1477277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17538_1477278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17538 ⟨1477278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17538
    ⟨1477278, by decide⟩ (by decide) (![⟨1477105, by decide⟩,⟨1477225, by decide⟩,⟨1469103, by decide⟩,⟨1477277, by decide⟩]) unmarked_context_9_17538_1477278 node_context_9_17538_1477278
  intro a
  fin_cases a
  · exact context_10_70152_1477105
  · exact context_10_70153_1477225
  · exact context_10_70154_1469103
  · exact context_10_70155_1477277

theorem selected_cut_51280 : selected 12 ⟨1477357, by decide⟩
    (prefixPartial 9 17539) = some ⟨9, 2, 0, 1477357, 17539, 1141, 4194304⟩ := by
  decide +kernel

theorem context_9_17539_1477357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17539 ⟨1477357, by decide⟩ :=
  accepted_of_selected 9 17539 ⟨1477357, by decide⟩ ⟨9, 2, 0, 1477357, 17539, 1141, 4194304⟩
    (by decide) selected_cut_51280

theorem unmarked_context_8_4384_1477358 : frontier 13 ⟨1477358, by decide⟩
    (prefixCache 8 4384) (prefixPartial 8 4384) = false := by
  decide +kernel

theorem node_context_8_4384_1477358 : EJMOriginalGlobalDAGData.nodes 13 ⟨1477358, by decide⟩ =
    .split (coordinate 8) (![⟨1476559, by decide⟩,⟨1476987, by decide⟩,⟨1477278, by decide⟩,⟨1477357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4384_1477358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4384 ⟨1477358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4384
    ⟨1477358, by decide⟩ (by decide) (![⟨1476559, by decide⟩,⟨1476987, by decide⟩,⟨1477278, by decide⟩,⟨1477357, by decide⟩]) unmarked_context_8_4384_1477358 node_context_8_4384_1477358
  intro a
  fin_cases a
  · exact context_9_17536_1476559
  · exact context_9_17537_1476987
  · exact context_9_17538_1477278
  · exact context_9_17539_1477357

theorem selected_cut_51281 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70160) = some ⟨10, 1, 0, 1468246, 70160, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70160_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70160 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70160 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70160, 1, 1048576⟩
    (by decide) selected_cut_51281

theorem selected_cut_51282 : selected 10 ⟨1477426, by decide⟩
    (prefixPartial 11 280644) = some ⟨11, 2, 0, 1477426, 280644, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_280644_1477426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280644 ⟨1477426, by decide⟩ :=
  accepted_of_selected 11 280644 ⟨1477426, by decide⟩ ⟨11, 2, 0, 1477426, 280644, 2837, 262144⟩
    (by decide) selected_cut_51282

theorem selected_cut_51283 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 280645) = some ⟨11, 1, 0, 1468419, 280645, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280645_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280645 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 280645 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 280645, 1, 262144⟩
    (by decide) selected_cut_51283

theorem selected_cut_51284 : selected 10 ⟨1477517, by decide⟩
    (prefixPartial 11 280646) = some ⟨11, 2, 0, 1477517, 280646, 3041, 262144⟩ := by
  decide +kernel

theorem context_11_280646_1477517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280646 ⟨1477517, by decide⟩ :=
  accepted_of_selected 11 280646 ⟨1477517, by decide⟩ ⟨11, 2, 0, 1477517, 280646, 3041, 262144⟩
    (by decide) selected_cut_51284

theorem selected_cut_51285 : selected 10 ⟨1477592, by decide⟩
    (prefixPartial 11 280647) = some ⟨11, 2, 0, 1477592, 280647, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_280647_1477592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280647 ⟨1477592, by decide⟩ :=
  accepted_of_selected 11 280647 ⟨1477592, by decide⟩ ⟨11, 2, 0, 1477592, 280647, 2225, 262144⟩
    (by decide) selected_cut_51285

theorem unmarked_context_10_70161_1477593 : frontier 11 ⟨1477593, by decide⟩
    (prefixCache 10 70161) (prefixPartial 10 70161) = false := by
  decide +kernel

theorem node_context_10_70161_1477593 : EJMOriginalGlobalDAGData.nodes 11 ⟨1477593, by decide⟩ =
    .split (coordinate 10) (![⟨1477426, by decide⟩,⟨1468419, by decide⟩,⟨1477517, by decide⟩,⟨1477592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70161_1477593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70161 ⟨1477593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70161
    ⟨1477593, by decide⟩ (by decide) (![⟨1477426, by decide⟩,⟨1468419, by decide⟩,⟨1477517, by decide⟩,⟨1477592, by decide⟩]) unmarked_context_10_70161_1477593 node_context_10_70161_1477593
  intro a
  fin_cases a
  · exact context_11_280644_1477426
  · exact context_11_280645_1468419
  · exact context_11_280646_1477517
  · exact context_11_280647_1477592

theorem selected_cut_51286 : selected 10 ⟨1477639, by decide⟩
    (prefixPartial 11 280648) = some ⟨11, 2, 0, 1477639, 280648, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_280648_1477639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280648 ⟨1477639, by decide⟩ :=
  accepted_of_selected 11 280648 ⟨1477639, by decide⟩ ⟨11, 2, 0, 1477639, 280648, 2313, 262144⟩
    (by decide) selected_cut_51286

theorem selected_cut_51287 : selected 10 ⟨1477704, by decide⟩
    (prefixPartial 11 280649) = some ⟨11, 2, 0, 1477704, 280649, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_280649_1477704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280649 ⟨1477704, by decide⟩ :=
  accepted_of_selected 11 280649 ⟨1477704, by decide⟩ ⟨11, 2, 0, 1477704, 280649, 2545, 262144⟩
    (by decide) selected_cut_51287

theorem selected_cut_51288 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280650) = some ⟨11, 1, 0, 1468743, 280650, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280650_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280650 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280650 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280650, 1, 262144⟩
    (by decide) selected_cut_51288

theorem selected_cut_51289 : selected 10 ⟨1477769, by decide⟩
    (prefixPartial 11 280651) = some ⟨11, 2, 0, 1477769, 280651, 2701, 262144⟩ := by
  decide +kernel

theorem context_11_280651_1477769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280651 ⟨1477769, by decide⟩ :=
  accepted_of_selected 11 280651 ⟨1477769, by decide⟩ ⟨11, 2, 0, 1477769, 280651, 2701, 262144⟩
    (by decide) selected_cut_51289

theorem unmarked_context_10_70162_1477770 : frontier 11 ⟨1477770, by decide⟩
    (prefixCache 10 70162) (prefixPartial 10 70162) = false := by
  decide +kernel

theorem node_context_10_70162_1477770 : EJMOriginalGlobalDAGData.nodes 11 ⟨1477770, by decide⟩ =
    .split (coordinate 10) (![⟨1477639, by decide⟩,⟨1477704, by decide⟩,⟨1468743, by decide⟩,⟨1477769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70162_1477770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70162 ⟨1477770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70162
    ⟨1477770, by decide⟩ (by decide) (![⟨1477639, by decide⟩,⟨1477704, by decide⟩,⟨1468743, by decide⟩,⟨1477769, by decide⟩]) unmarked_context_10_70162_1477770 node_context_10_70162_1477770
  intro a
  fin_cases a
  · exact context_11_280648_1477639
  · exact context_11_280649_1477704
  · exact context_11_280650_1468743
  · exact context_11_280651_1477769

theorem selected_cut_51290 : selected 10 ⟨1477820, by decide⟩
    (prefixPartial 11 280652) = some ⟨11, 2, 0, 1477820, 280652, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_280652_1477820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280652 ⟨1477820, by decide⟩ :=
  accepted_of_selected 11 280652 ⟨1477820, by decide⟩ ⟨11, 2, 0, 1477820, 280652, 2173, 262144⟩
    (by decide) selected_cut_51290

theorem selected_cut_51291 : selected 10 ⟨1477880, by decide⟩
    (prefixPartial 11 280653) = some ⟨11, 2, 0, 1477880, 280653, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_280653_1477880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280653 ⟨1477880, by decide⟩ :=
  accepted_of_selected 11 280653 ⟨1477880, by decide⟩ ⟨11, 2, 0, 1477880, 280653, 2377, 262144⟩
    (by decide) selected_cut_51291

theorem selected_cut_51292 : selected 10 ⟨1477947, by decide⟩
    (prefixPartial 11 280654) = some ⟨11, 2, 0, 1477947, 280654, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_280654_1477947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280654 ⟨1477947, by decide⟩ :=
  accepted_of_selected 11 280654 ⟨1477947, by decide⟩ ⟨11, 2, 0, 1477947, 280654, 2413, 262144⟩
    (by decide) selected_cut_51292

theorem selected_cut_51293 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280655) = some ⟨11, 1, 0, 1470044, 280655, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280655_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280655 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280655 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280655, 1, 262144⟩
    (by decide) selected_cut_51293

theorem unmarked_context_10_70163_1477948 : frontier 11 ⟨1477948, by decide⟩
    (prefixCache 10 70163) (prefixPartial 10 70163) = false := by
  decide +kernel

theorem node_context_10_70163_1477948 : EJMOriginalGlobalDAGData.nodes 11 ⟨1477948, by decide⟩ =
    .split (coordinate 10) (![⟨1477820, by decide⟩,⟨1477880, by decide⟩,⟨1477947, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70163_1477948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70163 ⟨1477948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70163
    ⟨1477948, by decide⟩ (by decide) (![⟨1477820, by decide⟩,⟨1477880, by decide⟩,⟨1477947, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70163_1477948 node_context_10_70163_1477948
  intro a
  fin_cases a
  · exact context_11_280652_1477820
  · exact context_11_280653_1477880
  · exact context_11_280654_1477947
  · exact context_11_280655_1470044

theorem unmarked_context_9_17540_1477949 : frontier 12 ⟨1477949, by decide⟩
    (prefixCache 9 17540) (prefixPartial 9 17540) = false := by
  decide +kernel

theorem node_context_9_17540_1477949 : EJMOriginalGlobalDAGData.nodes 12 ⟨1477949, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1477593, by decide⟩,⟨1477770, by decide⟩,⟨1477948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17540_1477949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17540 ⟨1477949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17540
    ⟨1477949, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1477593, by decide⟩,⟨1477770, by decide⟩,⟨1477948, by decide⟩]) unmarked_context_9_17540_1477949 node_context_9_17540_1477949
  intro a
  fin_cases a
  · exact context_10_70160_1468246
  · exact context_10_70161_1477593
  · exact context_10_70162_1477770
  · exact context_10_70163_1477948

theorem selected_cut_51294 : selected 11 ⟨1478037, by decide⟩
    (prefixPartial 10 70164) = some ⟨10, 2, 0, 1478037, 70164, 3853, 1048576⟩ := by
  decide +kernel

theorem context_10_70164_1478037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70164 ⟨1478037, by decide⟩ :=
  accepted_of_selected 10 70164 ⟨1478037, by decide⟩ ⟨10, 2, 0, 1478037, 70164, 3853, 1048576⟩
    (by decide) selected_cut_51294

theorem selected_cut_51295 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70165) = some ⟨10, 1, 0, 1468874, 70165, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70165_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70165 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70165 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70165, 1, 1048576⟩
    (by decide) selected_cut_51295

theorem selected_cut_51296 : selected 10 ⟨1478069, by decide⟩
    (prefixPartial 11 280664) = some ⟨11, 2, 0, 1478069, 280664, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_280664_1478069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280664 ⟨1478069, by decide⟩ :=
  accepted_of_selected 11 280664 ⟨1478069, by decide⟩ ⟨11, 2, 0, 1478069, 280664, 1773, 262144⟩
    (by decide) selected_cut_51296

theorem selected_cut_51297 : selected 10 ⟨1478113, by decide⟩
    (prefixPartial 11 280665) = some ⟨11, 2, 0, 1478113, 280665, 2293, 262144⟩ := by
  decide +kernel

theorem context_11_280665_1478113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280665 ⟨1478113, by decide⟩ :=
  accepted_of_selected 11 280665 ⟨1478113, by decide⟩ ⟨11, 2, 0, 1478113, 280665, 2293, 262144⟩
    (by decide) selected_cut_51297

theorem selected_cut_51298 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280666) = some ⟨11, 1, 0, 1468743, 280666, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280666_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280666 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280666 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280666, 1, 262144⟩
    (by decide) selected_cut_51298

theorem selected_cut_51299 : selected 10 ⟨1478148, by decide⟩
    (prefixPartial 11 280667) = some ⟨11, 2, 0, 1478148, 280667, 1701, 262144⟩ := by
  decide +kernel

theorem context_11_280667_1478148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280667 ⟨1478148, by decide⟩ :=
  accepted_of_selected 11 280667 ⟨1478148, by decide⟩ ⟨11, 2, 0, 1478148, 280667, 1701, 262144⟩
    (by decide) selected_cut_51299

theorem unmarked_context_10_70166_1478149 : frontier 11 ⟨1478149, by decide⟩
    (prefixCache 10 70166) (prefixPartial 10 70166) = false := by
  decide +kernel

theorem node_context_10_70166_1478149 : EJMOriginalGlobalDAGData.nodes 11 ⟨1478149, by decide⟩ =
    .split (coordinate 10) (![⟨1478069, by decide⟩,⟨1478113, by decide⟩,⟨1468743, by decide⟩,⟨1478148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70166_1478149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70166 ⟨1478149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70166
    ⟨1478149, by decide⟩ (by decide) (![⟨1478069, by decide⟩,⟨1478113, by decide⟩,⟨1468743, by decide⟩,⟨1478148, by decide⟩]) unmarked_context_10_70166_1478149 node_context_10_70166_1478149
  intro a
  fin_cases a
  · exact context_11_280664_1478069
  · exact context_11_280665_1478113
  · exact context_11_280666_1468743
  · exact context_11_280667_1478148

theorem selected_cut_51300 : selected 10 ⟨1478177, by decide⟩
    (prefixPartial 11 280668) = some ⟨11, 2, 0, 1478177, 280668, 1529, 262144⟩ := by
  decide +kernel

theorem context_11_280668_1478177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280668 ⟨1478177, by decide⟩ :=
  accepted_of_selected 11 280668 ⟨1478177, by decide⟩ ⟨11, 2, 0, 1478177, 280668, 1529, 262144⟩
    (by decide) selected_cut_51300

theorem selected_cut_51301 : selected 10 ⟨1478226, by decide⟩
    (prefixPartial 11 280669) = some ⟨11, 2, 0, 1478226, 280669, 2077, 262144⟩ := by
  decide +kernel

theorem context_11_280669_1478226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280669 ⟨1478226, by decide⟩ :=
  accepted_of_selected 11 280669 ⟨1478226, by decide⟩ ⟨11, 2, 0, 1478226, 280669, 2077, 262144⟩
    (by decide) selected_cut_51301

theorem selected_cut_51302 : selected 10 ⟨1478257, by decide⟩
    (prefixPartial 11 280670) = some ⟨11, 2, 0, 1478257, 280670, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_280670_1478257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280670 ⟨1478257, by decide⟩ :=
  accepted_of_selected 11 280670 ⟨1478257, by decide⟩ ⟨11, 2, 0, 1478257, 280670, 1425, 262144⟩
    (by decide) selected_cut_51302

theorem selected_cut_51303 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280671) = some ⟨11, 1, 0, 1470044, 280671, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280671_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280671 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280671 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280671, 1, 262144⟩
    (by decide) selected_cut_51303

theorem unmarked_context_10_70167_1478258 : frontier 11 ⟨1478258, by decide⟩
    (prefixCache 10 70167) (prefixPartial 10 70167) = false := by
  decide +kernel

theorem node_context_10_70167_1478258 : EJMOriginalGlobalDAGData.nodes 11 ⟨1478258, by decide⟩ =
    .split (coordinate 10) (![⟨1478177, by decide⟩,⟨1478226, by decide⟩,⟨1478257, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70167_1478258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70167 ⟨1478258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70167
    ⟨1478258, by decide⟩ (by decide) (![⟨1478177, by decide⟩,⟨1478226, by decide⟩,⟨1478257, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70167_1478258 node_context_10_70167_1478258
  intro a
  fin_cases a
  · exact context_11_280668_1478177
  · exact context_11_280669_1478226
  · exact context_11_280670_1478257
  · exact context_11_280671_1470044

theorem unmarked_context_9_17541_1478259 : frontier 12 ⟨1478259, by decide⟩
    (prefixCache 9 17541) (prefixPartial 9 17541) = false := by
  decide +kernel

theorem node_context_9_17541_1478259 : EJMOriginalGlobalDAGData.nodes 12 ⟨1478259, by decide⟩ =
    .split (coordinate 9) (![⟨1478037, by decide⟩,⟨1468874, by decide⟩,⟨1478149, by decide⟩,⟨1478258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17541_1478259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17541 ⟨1478259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17541
    ⟨1478259, by decide⟩ (by decide) (![⟨1478037, by decide⟩,⟨1468874, by decide⟩,⟨1478149, by decide⟩,⟨1478258, by decide⟩]) unmarked_context_9_17541_1478259 node_context_9_17541_1478259
  intro a
  fin_cases a
  · exact context_10_70164_1478037
  · exact context_10_70165_1468874
  · exact context_10_70166_1478149
  · exact context_10_70167_1478258

theorem selected_cut_51304 : selected 11 ⟨1478317, by decide⟩
    (prefixPartial 10 70168) = some ⟨10, 2, 0, 1478317, 70168, 3077, 1048576⟩ := by
  decide +kernel

theorem context_10_70168_1478317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70168 ⟨1478317, by decide⟩ :=
  accepted_of_selected 10 70168 ⟨1478317, by decide⟩ ⟨10, 2, 0, 1478317, 70168, 3077, 1048576⟩
    (by decide) selected_cut_51304

theorem selected_cut_51305 : selected 11 ⟨1478374, by decide⟩
    (prefixPartial 10 70169) = some ⟨10, 2, 0, 1478374, 70169, 3133, 1048576⟩ := by
  decide +kernel

theorem context_10_70169_1478374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70169 ⟨1478374, by decide⟩ :=
  accepted_of_selected 10 70169 ⟨1478374, by decide⟩ ⟨10, 2, 0, 1478374, 70169, 3133, 1048576⟩
    (by decide) selected_cut_51305

theorem selected_cut_51306 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70170) = some ⟨10, 1, 0, 1469103, 70170, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70170_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70170 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70170 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70170, 1, 1048576⟩
    (by decide) selected_cut_51306

theorem selected_cut_51307 : selected 11 ⟨1478420, by decide⟩
    (prefixPartial 10 70171) = some ⟨10, 2, 0, 1478420, 70171, 2245, 1048576⟩ := by
  decide +kernel

theorem context_10_70171_1478420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70171 ⟨1478420, by decide⟩ :=
  accepted_of_selected 10 70171 ⟨1478420, by decide⟩ ⟨10, 2, 0, 1478420, 70171, 2245, 1048576⟩
    (by decide) selected_cut_51307

theorem unmarked_context_9_17542_1478421 : frontier 12 ⟨1478421, by decide⟩
    (prefixCache 9 17542) (prefixPartial 9 17542) = false := by
  decide +kernel

theorem node_context_9_17542_1478421 : EJMOriginalGlobalDAGData.nodes 12 ⟨1478421, by decide⟩ =
    .split (coordinate 9) (![⟨1478317, by decide⟩,⟨1478374, by decide⟩,⟨1469103, by decide⟩,⟨1478420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17542_1478421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17542 ⟨1478421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17542
    ⟨1478421, by decide⟩ (by decide) (![⟨1478317, by decide⟩,⟨1478374, by decide⟩,⟨1469103, by decide⟩,⟨1478420, by decide⟩]) unmarked_context_9_17542_1478421 node_context_9_17542_1478421
  intro a
  fin_cases a
  · exact context_10_70168_1478317
  · exact context_10_70169_1478374
  · exact context_10_70170_1469103
  · exact context_10_70171_1478420

theorem selected_cut_51308 : selected 12 ⟨1478494, by decide⟩
    (prefixPartial 9 17543) = some ⟨9, 2, 0, 1478494, 17543, 2609, 4194304⟩ := by
  decide +kernel

theorem context_9_17543_1478494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17543 ⟨1478494, by decide⟩ :=
  accepted_of_selected 9 17543 ⟨1478494, by decide⟩ ⟨9, 2, 0, 1478494, 17543, 2609, 4194304⟩
    (by decide) selected_cut_51308

theorem unmarked_context_8_4385_1478495 : frontier 13 ⟨1478495, by decide⟩
    (prefixCache 8 4385) (prefixPartial 8 4385) = false := by
  decide +kernel

theorem node_context_8_4385_1478495 : EJMOriginalGlobalDAGData.nodes 13 ⟨1478495, by decide⟩ =
    .split (coordinate 8) (![⟨1477949, by decide⟩,⟨1478259, by decide⟩,⟨1478421, by decide⟩,⟨1478494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4385_1478495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4385 ⟨1478495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4385
    ⟨1478495, by decide⟩ (by decide) (![⟨1477949, by decide⟩,⟨1478259, by decide⟩,⟨1478421, by decide⟩,⟨1478494, by decide⟩]) unmarked_context_8_4385_1478495 node_context_8_4385_1478495
  intro a
  fin_cases a
  · exact context_9_17540_1477949
  · exact context_9_17541_1478259
  · exact context_9_17542_1478421
  · exact context_9_17543_1478494

theorem selected_cut_51309 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70176) = some ⟨10, 1, 0, 1468246, 70176, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70176_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70176 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70176 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70176, 1, 1048576⟩
    (by decide) selected_cut_51309

theorem selected_cut_51310 : selected 10 ⟨1478561, by decide⟩
    (prefixPartial 11 280708) = some ⟨11, 2, 0, 1478561, 280708, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_280708_1478561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280708 ⟨1478561, by decide⟩ :=
  accepted_of_selected 11 280708 ⟨1478561, by decide⟩ ⟨11, 2, 0, 1478561, 280708, 2729, 262144⟩
    (by decide) selected_cut_51310

theorem selected_cut_51311 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 280709) = some ⟨11, 1, 0, 1468419, 280709, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280709_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280709 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 280709 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 280709, 1, 262144⟩
    (by decide) selected_cut_51311

theorem selected_cut_51312 : selected 10 ⟨1478664, by decide⟩
    (prefixPartial 11 280710) = some ⟨11, 2, 0, 1478664, 280710, 3269, 262144⟩ := by
  decide +kernel

theorem context_11_280710_1478664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280710 ⟨1478664, by decide⟩ :=
  accepted_of_selected 11 280710 ⟨1478664, by decide⟩ ⟨11, 2, 0, 1478664, 280710, 3269, 262144⟩
    (by decide) selected_cut_51312

theorem selected_cut_51313 : selected 10 ⟨1478763, by decide⟩
    (prefixPartial 11 280711) = some ⟨11, 2, 0, 1478763, 280711, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_280711_1478763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280711 ⟨1478763, by decide⟩ :=
  accepted_of_selected 11 280711 ⟨1478763, by decide⟩ ⟨11, 2, 0, 1478763, 280711, 3249, 262144⟩
    (by decide) selected_cut_51313

theorem unmarked_context_10_70177_1478764 : frontier 11 ⟨1478764, by decide⟩
    (prefixCache 10 70177) (prefixPartial 10 70177) = false := by
  decide +kernel

theorem node_context_10_70177_1478764 : EJMOriginalGlobalDAGData.nodes 11 ⟨1478764, by decide⟩ =
    .split (coordinate 10) (![⟨1478561, by decide⟩,⟨1468419, by decide⟩,⟨1478664, by decide⟩,⟨1478763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70177_1478764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70177 ⟨1478764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70177
    ⟨1478764, by decide⟩ (by decide) (![⟨1478561, by decide⟩,⟨1468419, by decide⟩,⟨1478664, by decide⟩,⟨1478763, by decide⟩]) unmarked_context_10_70177_1478764 node_context_10_70177_1478764
  intro a
  fin_cases a
  · exact context_11_280708_1478561
  · exact context_11_280709_1468419
  · exact context_11_280710_1478664
  · exact context_11_280711_1478763

theorem selected_cut_51314 : selected 10 ⟨1478834, by decide⟩
    (prefixPartial 11 280712) = some ⟨11, 2, 0, 1478834, 280712, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_280712_1478834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280712 ⟨1478834, by decide⟩ :=
  accepted_of_selected 11 280712 ⟨1478834, by decide⟩ ⟨11, 2, 0, 1478834, 280712, 2397, 262144⟩
    (by decide) selected_cut_51314

theorem selected_cut_51315 : selected 10 ⟨1478873, by decide⟩
    (prefixPartial 11 280713) = some ⟨11, 2, 0, 1478873, 280713, 1325, 262144⟩ := by
  decide +kernel

theorem context_11_280713_1478873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280713 ⟨1478873, by decide⟩ :=
  accepted_of_selected 11 280713 ⟨1478873, by decide⟩ ⟨11, 2, 0, 1478873, 280713, 1325, 262144⟩
    (by decide) selected_cut_51315

theorem selected_cut_51316 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280714) = some ⟨11, 1, 0, 1468743, 280714, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280714_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280714 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280714 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280714, 1, 262144⟩
    (by decide) selected_cut_51316

theorem selected_cut_51317 : selected 10 ⟨1478908, by decide⟩
    (prefixPartial 11 280715) = some ⟨11, 2, 0, 1478908, 280715, 1365, 262144⟩ := by
  decide +kernel

theorem context_11_280715_1478908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280715 ⟨1478908, by decide⟩ :=
  accepted_of_selected 11 280715 ⟨1478908, by decide⟩ ⟨11, 2, 0, 1478908, 280715, 1365, 262144⟩
    (by decide) selected_cut_51317

theorem unmarked_context_10_70178_1478909 : frontier 11 ⟨1478909, by decide⟩
    (prefixCache 10 70178) (prefixPartial 10 70178) = false := by
  decide +kernel

theorem node_context_10_70178_1478909 : EJMOriginalGlobalDAGData.nodes 11 ⟨1478909, by decide⟩ =
    .split (coordinate 10) (![⟨1478834, by decide⟩,⟨1478873, by decide⟩,⟨1468743, by decide⟩,⟨1478908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70178_1478909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70178 ⟨1478909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70178
    ⟨1478909, by decide⟩ (by decide) (![⟨1478834, by decide⟩,⟨1478873, by decide⟩,⟨1468743, by decide⟩,⟨1478908, by decide⟩]) unmarked_context_10_70178_1478909 node_context_10_70178_1478909
  intro a
  fin_cases a
  · exact context_11_280712_1478834
  · exact context_11_280713_1478873
  · exact context_11_280714_1468743
  · exact context_11_280715_1478908

theorem selected_cut_51318 : selected 10 ⟨1478951, by decide⟩
    (prefixPartial 11 280716) = some ⟨11, 2, 0, 1478951, 280716, 2097, 262144⟩ := by
  decide +kernel

theorem context_11_280716_1478951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280716 ⟨1478951, by decide⟩ :=
  accepted_of_selected 11 280716 ⟨1478951, by decide⟩ ⟨11, 2, 0, 1478951, 280716, 2097, 262144⟩
    (by decide) selected_cut_51318

theorem selected_cut_51319 : selected 10 ⟨1479015, by decide⟩
    (prefixPartial 11 280717) = some ⟨11, 2, 0, 1479015, 280717, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_280717_1479015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280717 ⟨1479015, by decide⟩ :=
  accepted_of_selected 11 280717 ⟨1479015, by decide⟩ ⟨11, 2, 0, 1479015, 280717, 2309, 262144⟩
    (by decide) selected_cut_51319

theorem selected_cut_51320 : selected 10 ⟨1479066, by decide⟩
    (prefixPartial 11 280718) = some ⟨11, 2, 0, 1479066, 280718, 1649, 262144⟩ := by
  decide +kernel

theorem context_11_280718_1479066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280718 ⟨1479066, by decide⟩ :=
  accepted_of_selected 11 280718 ⟨1479066, by decide⟩ ⟨11, 2, 0, 1479066, 280718, 1649, 262144⟩
    (by decide) selected_cut_51320

theorem selected_cut_51321 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280719) = some ⟨11, 1, 0, 1470044, 280719, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280719_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280719 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280719 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280719, 1, 262144⟩
    (by decide) selected_cut_51321

theorem unmarked_context_10_70179_1479067 : frontier 11 ⟨1479067, by decide⟩
    (prefixCache 10 70179) (prefixPartial 10 70179) = false := by
  decide +kernel

theorem node_context_10_70179_1479067 : EJMOriginalGlobalDAGData.nodes 11 ⟨1479067, by decide⟩ =
    .split (coordinate 10) (![⟨1478951, by decide⟩,⟨1479015, by decide⟩,⟨1479066, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70179_1479067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70179 ⟨1479067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70179
    ⟨1479067, by decide⟩ (by decide) (![⟨1478951, by decide⟩,⟨1479015, by decide⟩,⟨1479066, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70179_1479067 node_context_10_70179_1479067
  intro a
  fin_cases a
  · exact context_11_280716_1478951
  · exact context_11_280717_1479015
  · exact context_11_280718_1479066
  · exact context_11_280719_1470044

theorem unmarked_context_9_17544_1479068 : frontier 12 ⟨1479068, by decide⟩
    (prefixCache 9 17544) (prefixPartial 9 17544) = false := by
  decide +kernel

theorem node_context_9_17544_1479068 : EJMOriginalGlobalDAGData.nodes 12 ⟨1479068, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1478764, by decide⟩,⟨1478909, by decide⟩,⟨1479067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17544_1479068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17544 ⟨1479068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17544
    ⟨1479068, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1478764, by decide⟩,⟨1478909, by decide⟩,⟨1479067, by decide⟩]) unmarked_context_9_17544_1479068 node_context_9_17544_1479068
  intro a
  fin_cases a
  · exact context_10_70176_1468246
  · exact context_10_70177_1478764
  · exact context_10_70178_1478909
  · exact context_10_70179_1479067

theorem selected_cut_51322 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 280720) = some ⟨11, 1, 0, 434745, 280720, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280720_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280720 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 280720 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 280720, 1, 262144⟩
    (by decide) selected_cut_51322

theorem selected_cut_51323 : selected 10 ⟨1479091, by decide⟩
    (prefixPartial 11 280721) = some ⟨11, 2, 0, 1479091, 280721, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_280721_1479091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280721 ⟨1479091, by decide⟩ :=
  accepted_of_selected 11 280721 ⟨1479091, by decide⟩ ⟨11, 2, 0, 1479091, 280721, 1149, 262144⟩
    (by decide) selected_cut_51323

theorem selected_cut_51324 : selected 10 ⟨1479116, by decide⟩
    (prefixPartial 11 280722) = some ⟨11, 2, 0, 1479116, 280722, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_280722_1479116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280722 ⟨1479116, by decide⟩ :=
  accepted_of_selected 11 280722 ⟨1479116, by decide⟩ ⟨11, 2, 0, 1479116, 280722, 1561, 262144⟩
    (by decide) selected_cut_51324

theorem selected_cut_51325 : selected 10 ⟨1479144, by decide⟩
    (prefixPartial 11 280723) = some ⟨11, 2, 0, 1479144, 280723, 1493, 262144⟩ := by
  decide +kernel

theorem context_11_280723_1479144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280723 ⟨1479144, by decide⟩ :=
  accepted_of_selected 11 280723 ⟨1479144, by decide⟩ ⟨11, 2, 0, 1479144, 280723, 1493, 262144⟩
    (by decide) selected_cut_51325

theorem unmarked_context_10_70180_1479145 : frontier 11 ⟨1479145, by decide⟩
    (prefixCache 10 70180) (prefixPartial 10 70180) = false := by
  decide +kernel

theorem node_context_10_70180_1479145 : EJMOriginalGlobalDAGData.nodes 11 ⟨1479145, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1479091, by decide⟩,⟨1479116, by decide⟩,⟨1479144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70180_1479145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70180 ⟨1479145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70180
    ⟨1479145, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1479091, by decide⟩,⟨1479116, by decide⟩,⟨1479144, by decide⟩]) unmarked_context_10_70180_1479145 node_context_10_70180_1479145
  intro a
  fin_cases a
  · exact context_11_280720_434745
  · exact context_11_280721_1479091
  · exact context_11_280722_1479116
  · exact context_11_280723_1479144

theorem selected_cut_51326 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70181) = some ⟨10, 1, 0, 1468874, 70181, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70181_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70181 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70181 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70181, 1, 1048576⟩
    (by decide) selected_cut_51326

theorem selected_cut_51327 : selected 10 ⟨1479183, by decide⟩
    (prefixPartial 11 280728) = some ⟨11, 2, 0, 1479183, 280728, 1745, 262144⟩ := by
  decide +kernel

theorem context_11_280728_1479183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280728 ⟨1479183, by decide⟩ :=
  accepted_of_selected 11 280728 ⟨1479183, by decide⟩ ⟨11, 2, 0, 1479183, 280728, 1745, 262144⟩
    (by decide) selected_cut_51327

theorem selected_cut_51328 : selected 10 ⟨1479232, by decide⟩
    (prefixPartial 11 280729) = some ⟨11, 2, 0, 1479232, 280729, 2301, 262144⟩ := by
  decide +kernel

theorem context_11_280729_1479232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280729 ⟨1479232, by decide⟩ :=
  accepted_of_selected 11 280729 ⟨1479232, by decide⟩ ⟨11, 2, 0, 1479232, 280729, 2301, 262144⟩
    (by decide) selected_cut_51328

theorem selected_cut_51329 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280730) = some ⟨11, 1, 0, 1468743, 280730, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280730_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280730 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280730 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280730, 1, 262144⟩
    (by decide) selected_cut_51329

theorem selected_cut_51330 : selected 10 ⟨1479266, by decide⟩
    (prefixPartial 11 280731) = some ⟨11, 2, 0, 1479266, 280731, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_280731_1479266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280731 ⟨1479266, by decide⟩ :=
  accepted_of_selected 11 280731 ⟨1479266, by decide⟩ ⟨11, 2, 0, 1479266, 280731, 1561, 262144⟩
    (by decide) selected_cut_51330

theorem unmarked_context_10_70182_1479267 : frontier 11 ⟨1479267, by decide⟩
    (prefixCache 10 70182) (prefixPartial 10 70182) = false := by
  decide +kernel

theorem node_context_10_70182_1479267 : EJMOriginalGlobalDAGData.nodes 11 ⟨1479267, by decide⟩ =
    .split (coordinate 10) (![⟨1479183, by decide⟩,⟨1479232, by decide⟩,⟨1468743, by decide⟩,⟨1479266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70182_1479267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70182 ⟨1479267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70182
    ⟨1479267, by decide⟩ (by decide) (![⟨1479183, by decide⟩,⟨1479232, by decide⟩,⟨1468743, by decide⟩,⟨1479266, by decide⟩]) unmarked_context_10_70182_1479267 node_context_10_70182_1479267
  intro a
  fin_cases a
  · exact context_11_280728_1479183
  · exact context_11_280729_1479232
  · exact context_11_280730_1468743
  · exact context_11_280731_1479266

theorem selected_cut_51331 : selected 10 ⟨1479298, by decide⟩
    (prefixPartial 11 280732) = some ⟨11, 2, 0, 1479298, 280732, 1437, 262144⟩ := by
  decide +kernel

theorem context_11_280732_1479298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280732 ⟨1479298, by decide⟩ :=
  accepted_of_selected 11 280732 ⟨1479298, by decide⟩ ⟨11, 2, 0, 1479298, 280732, 1437, 262144⟩
    (by decide) selected_cut_51331

theorem selected_cut_51332 : selected 10 ⟨1479340, by decide⟩
    (prefixPartial 11 280733) = some ⟨11, 2, 0, 1479340, 280733, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_280733_1479340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280733 ⟨1479340, by decide⟩ :=
  accepted_of_selected 11 280733 ⟨1479340, by decide⟩ ⟨11, 2, 0, 1479340, 280733, 1821, 262144⟩
    (by decide) selected_cut_51332

theorem selected_cut_51333 : selected 10 ⟨1479359, by decide⟩
    (prefixPartial 11 280734) = some ⟨11, 2, 0, 1479359, 280734, 1129, 262144⟩ := by
  decide +kernel

theorem context_11_280734_1479359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280734 ⟨1479359, by decide⟩ :=
  accepted_of_selected 11 280734 ⟨1479359, by decide⟩ ⟨11, 2, 0, 1479359, 280734, 1129, 262144⟩
    (by decide) selected_cut_51333

theorem selected_cut_51334 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280735) = some ⟨11, 1, 0, 1470044, 280735, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280735_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280735 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280735 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280735, 1, 262144⟩
    (by decide) selected_cut_51334

theorem unmarked_context_10_70183_1479360 : frontier 11 ⟨1479360, by decide⟩
    (prefixCache 10 70183) (prefixPartial 10 70183) = false := by
  decide +kernel

theorem node_context_10_70183_1479360 : EJMOriginalGlobalDAGData.nodes 11 ⟨1479360, by decide⟩ =
    .split (coordinate 10) (![⟨1479298, by decide⟩,⟨1479340, by decide⟩,⟨1479359, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70183_1479360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70183 ⟨1479360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70183
    ⟨1479360, by decide⟩ (by decide) (![⟨1479298, by decide⟩,⟨1479340, by decide⟩,⟨1479359, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70183_1479360 node_context_10_70183_1479360
  intro a
  fin_cases a
  · exact context_11_280732_1479298
  · exact context_11_280733_1479340
  · exact context_11_280734_1479359
  · exact context_11_280735_1470044

theorem unmarked_context_9_17545_1479361 : frontier 12 ⟨1479361, by decide⟩
    (prefixCache 9 17545) (prefixPartial 9 17545) = false := by
  decide +kernel

theorem node_context_9_17545_1479361 : EJMOriginalGlobalDAGData.nodes 12 ⟨1479361, by decide⟩ =
    .split (coordinate 9) (![⟨1479145, by decide⟩,⟨1468874, by decide⟩,⟨1479267, by decide⟩,⟨1479360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17545_1479361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17545 ⟨1479361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17545
    ⟨1479361, by decide⟩ (by decide) (![⟨1479145, by decide⟩,⟨1468874, by decide⟩,⟨1479267, by decide⟩,⟨1479360, by decide⟩]) unmarked_context_9_17545_1479361 node_context_9_17545_1479361
  intro a
  fin_cases a
  · exact context_10_70180_1479145
  · exact context_10_70181_1468874
  · exact context_10_70182_1479267
  · exact context_10_70183_1479360

theorem selected_cut_51335 : selected 11 ⟨1479407, by decide⟩
    (prefixPartial 10 70184) = some ⟨10, 2, 0, 1479407, 70184, 2025, 1048576⟩ := by
  decide +kernel

theorem context_10_70184_1479407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70184 ⟨1479407, by decide⟩ :=
  accepted_of_selected 10 70184 ⟨1479407, by decide⟩ ⟨10, 2, 0, 1479407, 70184, 2025, 1048576⟩
    (by decide) selected_cut_51335

theorem selected_cut_51336 : selected 11 ⟨1479498, by decide⟩
    (prefixPartial 10 70185) = some ⟨10, 2, 0, 1479498, 70185, 3857, 1048576⟩ := by
  decide +kernel

theorem context_10_70185_1479498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70185 ⟨1479498, by decide⟩ :=
  accepted_of_selected 10 70185 ⟨1479498, by decide⟩ ⟨10, 2, 0, 1479498, 70185, 3857, 1048576⟩
    (by decide) selected_cut_51336

theorem selected_cut_51337 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70186) = some ⟨10, 1, 0, 1469103, 70186, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70186_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70186 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70186 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70186, 1, 1048576⟩
    (by decide) selected_cut_51337

theorem selected_cut_51338 : selected 11 ⟨1479551, by decide⟩
    (prefixPartial 10 70187) = some ⟨10, 2, 0, 1479551, 70187, 2297, 1048576⟩ := by
  decide +kernel

theorem context_10_70187_1479551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70187 ⟨1479551, by decide⟩ :=
  accepted_of_selected 10 70187 ⟨1479551, by decide⟩ ⟨10, 2, 0, 1479551, 70187, 2297, 1048576⟩
    (by decide) selected_cut_51338

theorem unmarked_context_9_17546_1479552 : frontier 12 ⟨1479552, by decide⟩
    (prefixCache 9 17546) (prefixPartial 9 17546) = false := by
  decide +kernel

theorem node_context_9_17546_1479552 : EJMOriginalGlobalDAGData.nodes 12 ⟨1479552, by decide⟩ =
    .split (coordinate 9) (![⟨1479407, by decide⟩,⟨1479498, by decide⟩,⟨1469103, by decide⟩,⟨1479551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17546_1479552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17546 ⟨1479552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17546
    ⟨1479552, by decide⟩ (by decide) (![⟨1479407, by decide⟩,⟨1479498, by decide⟩,⟨1469103, by decide⟩,⟨1479551, by decide⟩]) unmarked_context_9_17546_1479552 node_context_9_17546_1479552
  intro a
  fin_cases a
  · exact context_10_70184_1479407
  · exact context_10_70185_1479498
  · exact context_10_70186_1469103
  · exact context_10_70187_1479551

theorem selected_cut_51339 : selected 12 ⟨1479613, by decide⟩
    (prefixPartial 9 17547) = some ⟨9, 2, 0, 1479613, 17547, 2609, 4194304⟩ := by
  decide +kernel

theorem context_9_17547_1479613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17547 ⟨1479613, by decide⟩ :=
  accepted_of_selected 9 17547 ⟨1479613, by decide⟩ ⟨9, 2, 0, 1479613, 17547, 2609, 4194304⟩
    (by decide) selected_cut_51339

theorem unmarked_context_8_4386_1479614 : frontier 13 ⟨1479614, by decide⟩
    (prefixCache 8 4386) (prefixPartial 8 4386) = false := by
  decide +kernel

theorem node_context_8_4386_1479614 : EJMOriginalGlobalDAGData.nodes 13 ⟨1479614, by decide⟩ =
    .split (coordinate 8) (![⟨1479068, by decide⟩,⟨1479361, by decide⟩,⟨1479552, by decide⟩,⟨1479613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4386_1479614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4386 ⟨1479614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4386
    ⟨1479614, by decide⟩ (by decide) (![⟨1479068, by decide⟩,⟨1479361, by decide⟩,⟨1479552, by decide⟩,⟨1479613, by decide⟩]) unmarked_context_8_4386_1479614 node_context_8_4386_1479614
  intro a
  fin_cases a
  · exact context_9_17544_1479068
  · exact context_9_17545_1479361
  · exact context_9_17546_1479552
  · exact context_9_17547_1479613

theorem selected_cut_51340 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70192) = some ⟨10, 1, 0, 1468246, 70192, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70192_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70192 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70192 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70192, 1, 1048576⟩
    (by decide) selected_cut_51340

theorem selected_cut_51341 : selected 10 ⟨1479687, by decide⟩
    (prefixPartial 11 280772) = some ⟨11, 2, 0, 1479687, 280772, 2801, 262144⟩ := by
  decide +kernel

theorem context_11_280772_1479687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280772 ⟨1479687, by decide⟩ :=
  accepted_of_selected 11 280772 ⟨1479687, by decide⟩ ⟨11, 2, 0, 1479687, 280772, 2801, 262144⟩
    (by decide) selected_cut_51341

theorem selected_cut_51342 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 280773) = some ⟨11, 1, 0, 1468419, 280773, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280773_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280773 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 280773 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 280773, 1, 262144⟩
    (by decide) selected_cut_51342

theorem selected_cut_51343 : selected 10 ⟨1479815, by decide⟩
    (prefixPartial 11 280774) = some ⟨11, 2, 0, 1479815, 280774, 3385, 262144⟩ := by
  decide +kernel

theorem context_11_280774_1479815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280774 ⟨1479815, by decide⟩ :=
  accepted_of_selected 11 280774 ⟨1479815, by decide⟩ ⟨11, 2, 0, 1479815, 280774, 3385, 262144⟩
    (by decide) selected_cut_51343

theorem selected_cut_51344 : selected 10 ⟨1479855, by decide⟩
    (prefixPartial 11 280775) = some ⟨11, 2, 0, 1479855, 280775, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_280775_1479855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280775 ⟨1479855, by decide⟩ :=
  accepted_of_selected 11 280775 ⟨1479855, by decide⟩ ⟨11, 2, 0, 1479855, 280775, 1481, 262144⟩
    (by decide) selected_cut_51344

theorem unmarked_context_10_70193_1479856 : frontier 11 ⟨1479856, by decide⟩
    (prefixCache 10 70193) (prefixPartial 10 70193) = false := by
  decide +kernel

theorem node_context_10_70193_1479856 : EJMOriginalGlobalDAGData.nodes 11 ⟨1479856, by decide⟩ =
    .split (coordinate 10) (![⟨1479687, by decide⟩,⟨1468419, by decide⟩,⟨1479815, by decide⟩,⟨1479855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70193_1479856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70193 ⟨1479856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70193
    ⟨1479856, by decide⟩ (by decide) (![⟨1479687, by decide⟩,⟨1468419, by decide⟩,⟨1479815, by decide⟩,⟨1479855, by decide⟩]) unmarked_context_10_70193_1479856 node_context_10_70193_1479856
  intro a
  fin_cases a
  · exact context_11_280772_1479687
  · exact context_11_280773_1468419
  · exact context_11_280774_1479815
  · exact context_11_280775_1479855

theorem selected_cut_51345 : selected 10 ⟨1479906, by decide⟩
    (prefixPartial 11 280776) = some ⟨11, 2, 0, 1479906, 280776, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_280776_1479906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280776 ⟨1479906, by decide⟩ :=
  accepted_of_selected 11 280776 ⟨1479906, by decide⟩ ⟨11, 2, 0, 1479906, 280776, 2393, 262144⟩
    (by decide) selected_cut_51345

theorem selected_cut_51346 : selected 10 ⟨1479969, by decide⟩
    (prefixPartial 11 280777) = some ⟨11, 2, 0, 1479969, 280777, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_280777_1479969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280777 ⟨1479969, by decide⟩ :=
  accepted_of_selected 11 280777 ⟨1479969, by decide⟩ ⟨11, 2, 0, 1479969, 280777, 1929, 262144⟩
    (by decide) selected_cut_51346

theorem selected_cut_51347 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280778) = some ⟨11, 1, 0, 1468743, 280778, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280778_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280778 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280778 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280778, 1, 262144⟩
    (by decide) selected_cut_51347

theorem selected_cut_51348 : selected 10 ⟨1480003, by decide⟩
    (prefixPartial 11 280779) = some ⟨11, 2, 0, 1480003, 280779, 1341, 262144⟩ := by
  decide +kernel

theorem context_11_280779_1480003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280779 ⟨1480003, by decide⟩ :=
  accepted_of_selected 11 280779 ⟨1480003, by decide⟩ ⟨11, 2, 0, 1480003, 280779, 1341, 262144⟩
    (by decide) selected_cut_51348

theorem unmarked_context_10_70194_1480004 : frontier 11 ⟨1480004, by decide⟩
    (prefixCache 10 70194) (prefixPartial 10 70194) = false := by
  decide +kernel

theorem node_context_10_70194_1480004 : EJMOriginalGlobalDAGData.nodes 11 ⟨1480004, by decide⟩ =
    .split (coordinate 10) (![⟨1479906, by decide⟩,⟨1479969, by decide⟩,⟨1468743, by decide⟩,⟨1480003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70194_1480004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70194 ⟨1480004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70194
    ⟨1480004, by decide⟩ (by decide) (![⟨1479906, by decide⟩,⟨1479969, by decide⟩,⟨1468743, by decide⟩,⟨1480003, by decide⟩]) unmarked_context_10_70194_1480004 node_context_10_70194_1480004
  intro a
  fin_cases a
  · exact context_11_280776_1479906
  · exact context_11_280777_1479969
  · exact context_11_280778_1468743
  · exact context_11_280779_1480003

theorem selected_cut_51349 : selected 10 ⟨1480070, by decide⟩
    (prefixPartial 11 280780) = some ⟨11, 2, 0, 1480070, 280780, 2389, 262144⟩ := by
  decide +kernel

theorem context_11_280780_1480070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280780 ⟨1480070, by decide⟩ :=
  accepted_of_selected 11 280780 ⟨1480070, by decide⟩ ⟨11, 2, 0, 1480070, 280780, 2389, 262144⟩
    (by decide) selected_cut_51349

theorem selected_cut_51350 : selected 10 ⟨1480105, by decide⟩
    (prefixPartial 11 280781) = some ⟨11, 2, 0, 1480105, 280781, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_280781_1480105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280781 ⟨1480105, by decide⟩ :=
  accepted_of_selected 11 280781 ⟨1480105, by decide⟩ ⟨11, 2, 0, 1480105, 280781, 1257, 262144⟩
    (by decide) selected_cut_51350

theorem selected_cut_51351 : selected 10 ⟨1480142, by decide⟩
    (prefixPartial 11 280782) = some ⟨11, 2, 0, 1480142, 280782, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_280782_1480142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280782 ⟨1480142, by decide⟩ :=
  accepted_of_selected 11 280782 ⟨1480142, by decide⟩ ⟨11, 2, 0, 1480142, 280782, 1257, 262144⟩
    (by decide) selected_cut_51351

theorem selected_cut_51352 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280783) = some ⟨11, 1, 0, 1470044, 280783, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280783_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280783 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280783 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280783, 1, 262144⟩
    (by decide) selected_cut_51352

theorem unmarked_context_10_70195_1480143 : frontier 11 ⟨1480143, by decide⟩
    (prefixCache 10 70195) (prefixPartial 10 70195) = false := by
  decide +kernel

theorem node_context_10_70195_1480143 : EJMOriginalGlobalDAGData.nodes 11 ⟨1480143, by decide⟩ =
    .split (coordinate 10) (![⟨1480070, by decide⟩,⟨1480105, by decide⟩,⟨1480142, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70195_1480143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70195 ⟨1480143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70195
    ⟨1480143, by decide⟩ (by decide) (![⟨1480070, by decide⟩,⟨1480105, by decide⟩,⟨1480142, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70195_1480143 node_context_10_70195_1480143
  intro a
  fin_cases a
  · exact context_11_280780_1480070
  · exact context_11_280781_1480105
  · exact context_11_280782_1480142
  · exact context_11_280783_1470044

theorem unmarked_context_9_17548_1480144 : frontier 12 ⟨1480144, by decide⟩
    (prefixCache 9 17548) (prefixPartial 9 17548) = false := by
  decide +kernel

theorem node_context_9_17548_1480144 : EJMOriginalGlobalDAGData.nodes 12 ⟨1480144, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1479856, by decide⟩,⟨1480004, by decide⟩,⟨1480143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17548_1480144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17548 ⟨1480144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17548
    ⟨1480144, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1479856, by decide⟩,⟨1480004, by decide⟩,⟨1480143, by decide⟩]) unmarked_context_9_17548_1480144 node_context_9_17548_1480144
  intro a
  fin_cases a
  · exact context_10_70192_1468246
  · exact context_10_70193_1479856
  · exact context_10_70194_1480004
  · exact context_10_70195_1480143

theorem selected_cut_51353 : selected 11 ⟨1480216, by decide⟩
    (prefixPartial 10 70196) = some ⟨10, 2, 0, 1480216, 70196, 3473, 1048576⟩ := by
  decide +kernel

theorem context_10_70196_1480216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70196 ⟨1480216, by decide⟩ :=
  accepted_of_selected 10 70196 ⟨1480216, by decide⟩ ⟨10, 2, 0, 1480216, 70196, 3473, 1048576⟩
    (by decide) selected_cut_51353

theorem selected_cut_51354 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70197) = some ⟨10, 1, 0, 1468874, 70197, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70197_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70197 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70197 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70197, 1, 1048576⟩
    (by decide) selected_cut_51354

theorem selected_cut_51355 : selected 10 ⟨1480256, by decide⟩
    (prefixPartial 11 280792) = some ⟨11, 2, 0, 1480256, 280792, 1785, 262144⟩ := by
  decide +kernel

theorem context_11_280792_1480256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280792 ⟨1480256, by decide⟩ :=
  accepted_of_selected 11 280792 ⟨1480256, by decide⟩ ⟨11, 2, 0, 1480256, 280792, 1785, 262144⟩
    (by decide) selected_cut_51355

theorem selected_cut_51356 : selected 10 ⟨1480314, by decide⟩
    (prefixPartial 11 280793) = some ⟨11, 2, 0, 1480314, 280793, 2477, 262144⟩ := by
  decide +kernel

theorem context_11_280793_1480314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280793 ⟨1480314, by decide⟩ :=
  accepted_of_selected 11 280793 ⟨1480314, by decide⟩ ⟨11, 2, 0, 1480314, 280793, 2477, 262144⟩
    (by decide) selected_cut_51356

theorem selected_cut_51357 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280794) = some ⟨11, 1, 0, 1468743, 280794, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280794_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280794 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280794 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280794, 1, 262144⟩
    (by decide) selected_cut_51357

theorem selected_cut_51358 : selected 10 ⟨1480342, by decide⟩
    (prefixPartial 11 280795) = some ⟨11, 2, 0, 1480342, 280795, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_280795_1480342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280795 ⟨1480342, by decide⟩ :=
  accepted_of_selected 11 280795 ⟨1480342, by decide⟩ ⟨11, 2, 0, 1480342, 280795, 1569, 262144⟩
    (by decide) selected_cut_51358

theorem unmarked_context_10_70198_1480343 : frontier 11 ⟨1480343, by decide⟩
    (prefixCache 10 70198) (prefixPartial 10 70198) = false := by
  decide +kernel

theorem node_context_10_70198_1480343 : EJMOriginalGlobalDAGData.nodes 11 ⟨1480343, by decide⟩ =
    .split (coordinate 10) (![⟨1480256, by decide⟩,⟨1480314, by decide⟩,⟨1468743, by decide⟩,⟨1480342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70198_1480343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70198 ⟨1480343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70198
    ⟨1480343, by decide⟩ (by decide) (![⟨1480256, by decide⟩,⟨1480314, by decide⟩,⟨1468743, by decide⟩,⟨1480342, by decide⟩]) unmarked_context_10_70198_1480343 node_context_10_70198_1480343
  intro a
  fin_cases a
  · exact context_11_280792_1480256
  · exact context_11_280793_1480314
  · exact context_11_280794_1468743
  · exact context_11_280795_1480342

theorem selected_cut_51359 : selected 10 ⟨1480375, by decide⟩
    (prefixPartial 11 280796) = some ⟨11, 2, 0, 1480375, 280796, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_280796_1480375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280796 ⟨1480375, by decide⟩ :=
  accepted_of_selected 11 280796 ⟨1480375, by decide⟩ ⟨11, 2, 0, 1480375, 280796, 1597, 262144⟩
    (by decide) selected_cut_51359

theorem selected_cut_51360 : selected 10 ⟨1480423, by decide⟩
    (prefixPartial 11 280797) = some ⟨11, 2, 0, 1480423, 280797, 2213, 262144⟩ := by
  decide +kernel

theorem context_11_280797_1480423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280797 ⟨1480423, by decide⟩ :=
  accepted_of_selected 11 280797 ⟨1480423, by decide⟩ ⟨11, 2, 0, 1480423, 280797, 2213, 262144⟩
    (by decide) selected_cut_51360

theorem selected_cut_51361 : selected 10 ⟨1480452, by decide⟩
    (prefixPartial 11 280798) = some ⟨11, 2, 0, 1480452, 280798, 1333, 262144⟩ := by
  decide +kernel

theorem context_11_280798_1480452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280798 ⟨1480452, by decide⟩ :=
  accepted_of_selected 11 280798 ⟨1480452, by decide⟩ ⟨11, 2, 0, 1480452, 280798, 1333, 262144⟩
    (by decide) selected_cut_51361

theorem selected_cut_51362 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280799) = some ⟨11, 1, 0, 1470044, 280799, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280799_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280799 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280799 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280799, 1, 262144⟩
    (by decide) selected_cut_51362

theorem unmarked_context_10_70199_1480453 : frontier 11 ⟨1480453, by decide⟩
    (prefixCache 10 70199) (prefixPartial 10 70199) = false := by
  decide +kernel

theorem node_context_10_70199_1480453 : EJMOriginalGlobalDAGData.nodes 11 ⟨1480453, by decide⟩ =
    .split (coordinate 10) (![⟨1480375, by decide⟩,⟨1480423, by decide⟩,⟨1480452, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70199_1480453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70199 ⟨1480453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70199
    ⟨1480453, by decide⟩ (by decide) (![⟨1480375, by decide⟩,⟨1480423, by decide⟩,⟨1480452, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70199_1480453 node_context_10_70199_1480453
  intro a
  fin_cases a
  · exact context_11_280796_1480375
  · exact context_11_280797_1480423
  · exact context_11_280798_1480452
  · exact context_11_280799_1470044

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
