/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover481
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_46275 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 370245) = some ⟨12, 1, 0, 1257136, 370245, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370245_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370245 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 370245 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 370245, 1, 65536⟩
    (by decide) selected_cut_46275

theorem selected_cut_46276 : selected 9 ⟨1289624, by decide⟩
    (prefixPartial 12 370246) = some ⟨12, 2, 0, 1289624, 370246, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_370246_1289624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370246 ⟨1289624, by decide⟩ :=
  accepted_of_selected 12 370246 ⟨1289624, by decide⟩ ⟨12, 2, 0, 1289624, 370246, 1689, 65536⟩
    (by decide) selected_cut_46276

theorem selected_cut_46277 : selected 9 ⟨1289675, by decide⟩
    (prefixPartial 12 370247) = some ⟨12, 2, 0, 1289675, 370247, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_370247_1289675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370247 ⟨1289675, by decide⟩ :=
  accepted_of_selected 12 370247 ⟨1289675, by decide⟩ ⟨12, 2, 0, 1289675, 370247, 1957, 65536⟩
    (by decide) selected_cut_46277

theorem unmarked_context_11_92561_1289676 : frontier 10 ⟨1289676, by decide⟩
    (prefixCache 11 92561) (prefixPartial 11 92561) = false := by
  decide +kernel

theorem node_context_11_92561_1289676 : EJMOriginalGlobalDAGData.nodes 10 ⟨1289676, by decide⟩ =
    .split (coordinate 11) (![⟨1289585, by decide⟩,⟨1257136, by decide⟩,⟨1289624, by decide⟩,⟨1289675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92561_1289676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92561 ⟨1289676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92561
    ⟨1289676, by decide⟩ (by decide) (![⟨1289585, by decide⟩,⟨1257136, by decide⟩,⟨1289624, by decide⟩,⟨1289675, by decide⟩]) unmarked_context_11_92561_1289676 node_context_11_92561_1289676
  intro a
  fin_cases a
  · exact context_12_370244_1289585
  · exact context_12_370245_1257136
  · exact context_12_370246_1289624
  · exact context_12_370247_1289675

theorem selected_cut_46278 : selected 10 ⟨1289773, by decide⟩
    (prefixPartial 11 92562) = some ⟨11, 2, 0, 1289773, 92562, 3937, 262144⟩ := by
  decide +kernel

theorem context_11_92562_1289773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92562 ⟨1289773, by decide⟩ :=
  accepted_of_selected 11 92562 ⟨1289773, by decide⟩ ⟨11, 2, 0, 1289773, 92562, 3937, 262144⟩
    (by decide) selected_cut_46278

theorem selected_cut_46279 : selected 9 ⟨1289830, by decide⟩
    (prefixPartial 12 370252) = some ⟨12, 2, 0, 1289830, 370252, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_370252_1289830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370252 ⟨1289830, by decide⟩ :=
  accepted_of_selected 12 370252 ⟨1289830, by decide⟩ ⟨12, 2, 0, 1289830, 370252, 2065, 65536⟩
    (by decide) selected_cut_46279

theorem selected_cut_46280 : selected 9 ⟨1289861, by decide⟩
    (prefixPartial 12 370253) = some ⟨12, 2, 0, 1289861, 370253, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_370253_1289861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370253 ⟨1289861, by decide⟩ :=
  accepted_of_selected 12 370253 ⟨1289861, by decide⟩ ⟨12, 2, 0, 1289861, 370253, 1441, 65536⟩
    (by decide) selected_cut_46280

theorem selected_cut_46281 : selected 9 ⟨1289901, by decide⟩
    (prefixPartial 12 370254) = some ⟨12, 2, 0, 1289901, 370254, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_370254_1289901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370254 ⟨1289901, by decide⟩ :=
  accepted_of_selected 12 370254 ⟨1289901, by decide⟩ ⟨12, 2, 0, 1289901, 370254, 1813, 65536⟩
    (by decide) selected_cut_46281

theorem selected_cut_46282 : selected 9 ⟨1289945, by decide⟩
    (prefixPartial 12 370255) = some ⟨12, 2, 0, 1289945, 370255, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_370255_1289945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370255 ⟨1289945, by decide⟩ :=
  accepted_of_selected 12 370255 ⟨1289945, by decide⟩ ⟨12, 2, 0, 1289945, 370255, 1901, 65536⟩
    (by decide) selected_cut_46282

theorem unmarked_context_11_92563_1289946 : frontier 10 ⟨1289946, by decide⟩
    (prefixCache 11 92563) (prefixPartial 11 92563) = false := by
  decide +kernel

theorem node_context_11_92563_1289946 : EJMOriginalGlobalDAGData.nodes 10 ⟨1289946, by decide⟩ =
    .split (coordinate 11) (![⟨1289830, by decide⟩,⟨1289861, by decide⟩,⟨1289901, by decide⟩,⟨1289945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92563_1289946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92563 ⟨1289946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92563
    ⟨1289946, by decide⟩ (by decide) (![⟨1289830, by decide⟩,⟨1289861, by decide⟩,⟨1289901, by decide⟩,⟨1289945, by decide⟩]) unmarked_context_11_92563_1289946 node_context_11_92563_1289946
  intro a
  fin_cases a
  · exact context_12_370252_1289830
  · exact context_12_370253_1289861
  · exact context_12_370254_1289901
  · exact context_12_370255_1289945

theorem unmarked_context_10_23140_1289947 : frontier 11 ⟨1289947, by decide⟩
    (prefixCache 10 23140) (prefixPartial 10 23140) = false := by
  decide +kernel

theorem node_context_10_23140_1289947 : EJMOriginalGlobalDAGData.nodes 11 ⟨1289947, by decide⟩ =
    .split (coordinate 10) (![⟨1283168, by decide⟩,⟨1289676, by decide⟩,⟨1289773, by decide⟩,⟨1289946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23140_1289947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23140 ⟨1289947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23140
    ⟨1289947, by decide⟩ (by decide) (![⟨1283168, by decide⟩,⟨1289676, by decide⟩,⟨1289773, by decide⟩,⟨1289946, by decide⟩]) unmarked_context_10_23140_1289947 node_context_10_23140_1289947
  intro a
  fin_cases a
  · exact context_11_92560_1283168
  · exact context_11_92561_1289676
  · exact context_11_92562_1289773
  · exact context_11_92563_1289946

theorem selected_cut_46283 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23141) = some ⟨10, 1, 0, 893098, 23141, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23141_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23141 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23141 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23141, 1, 1048576⟩
    (by decide) selected_cut_46283

theorem selected_cut_46284 : selected 10 ⟨1290088, by decide⟩
    (prefixPartial 11 92568) = some ⟨11, 2, 0, 1290088, 92568, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_92568_1290088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92568 ⟨1290088, by decide⟩ :=
  accepted_of_selected 11 92568 ⟨1290088, by decide⟩ ⟨11, 2, 0, 1290088, 92568, 3845, 262144⟩
    (by decide) selected_cut_46284

theorem selected_cut_46285 : selected 9 ⟨1290126, by decide⟩
    (prefixPartial 12 370276) = some ⟨12, 2, 0, 1290126, 370276, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_370276_1290126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370276 ⟨1290126, by decide⟩ :=
  accepted_of_selected 12 370276 ⟨1290126, by decide⟩ ⟨12, 2, 0, 1290126, 370276, 1557, 65536⟩
    (by decide) selected_cut_46285

theorem selected_cut_46286 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 370277) = some ⟨12, 1, 0, 1256866, 370277, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370277_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370277 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 370277 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 370277, 1, 65536⟩
    (by decide) selected_cut_46286

theorem selected_cut_46287 : selected 9 ⟨1290147, by decide⟩
    (prefixPartial 12 370278) = some ⟨12, 2, 0, 1290147, 370278, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_370278_1290147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370278 ⟨1290147, by decide⟩ :=
  accepted_of_selected 12 370278 ⟨1290147, by decide⟩ ⟨12, 2, 0, 1290147, 370278, 1169, 65536⟩
    (by decide) selected_cut_46287

theorem selected_cut_46288 : selected 9 ⟨1290174, by decide⟩
    (prefixPartial 12 370279) = some ⟨12, 2, 0, 1290174, 370279, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_370279_1290174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370279 ⟨1290174, by decide⟩ :=
  accepted_of_selected 12 370279 ⟨1290174, by decide⟩ ⟨12, 2, 0, 1290174, 370279, 1457, 65536⟩
    (by decide) selected_cut_46288

theorem unmarked_context_11_92569_1290175 : frontier 10 ⟨1290175, by decide⟩
    (prefixCache 11 92569) (prefixPartial 11 92569) = false := by
  decide +kernel

theorem node_context_11_92569_1290175 : EJMOriginalGlobalDAGData.nodes 10 ⟨1290175, by decide⟩ =
    .split (coordinate 11) (![⟨1290126, by decide⟩,⟨1256866, by decide⟩,⟨1290147, by decide⟩,⟨1290174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92569_1290175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92569 ⟨1290175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92569
    ⟨1290175, by decide⟩ (by decide) (![⟨1290126, by decide⟩,⟨1256866, by decide⟩,⟨1290147, by decide⟩,⟨1290174, by decide⟩]) unmarked_context_11_92569_1290175 node_context_11_92569_1290175
  intro a
  fin_cases a
  · exact context_12_370276_1290126
  · exact context_12_370277_1256866
  · exact context_12_370278_1290147
  · exact context_12_370279_1290174

theorem selected_cut_46289 : selected 10 ⟨1283737, by decide⟩
    (prefixPartial 11 92570) = some ⟨11, 1, 0, 1283737, 92570, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92570_1283737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92570 ⟨1283737, by decide⟩ :=
  accepted_of_selected 11 92570 ⟨1283737, by decide⟩ ⟨11, 1, 0, 1283737, 92570, 1, 262144⟩
    (by decide) selected_cut_46289

theorem selected_cut_46290 : selected 10 ⟨1290304, by decide⟩
    (prefixPartial 11 92571) = some ⟨11, 2, 0, 1290304, 92571, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_92571_1290304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92571 ⟨1290304, by decide⟩ :=
  accepted_of_selected 11 92571 ⟨1290304, by decide⟩ ⟨11, 2, 0, 1290304, 92571, 3653, 262144⟩
    (by decide) selected_cut_46290

theorem unmarked_context_10_23142_1290305 : frontier 11 ⟨1290305, by decide⟩
    (prefixCache 10 23142) (prefixPartial 10 23142) = false := by
  decide +kernel

theorem node_context_10_23142_1290305 : EJMOriginalGlobalDAGData.nodes 11 ⟨1290305, by decide⟩ =
    .split (coordinate 10) (![⟨1290088, by decide⟩,⟨1290175, by decide⟩,⟨1283737, by decide⟩,⟨1290304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23142_1290305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23142 ⟨1290305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23142
    ⟨1290305, by decide⟩ (by decide) (![⟨1290088, by decide⟩,⟨1290175, by decide⟩,⟨1283737, by decide⟩,⟨1290304, by decide⟩]) unmarked_context_10_23142_1290305 node_context_10_23142_1290305
  intro a
  fin_cases a
  · exact context_11_92568_1290088
  · exact context_11_92569_1290175
  · exact context_11_92570_1283737
  · exact context_11_92571_1290304

theorem selected_cut_46291 : selected 9 ⟨1290337, by decide⟩
    (prefixPartial 12 370288) = some ⟨12, 2, 0, 1290337, 370288, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_370288_1290337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370288 ⟨1290337, by decide⟩ :=
  accepted_of_selected 12 370288 ⟨1290337, by decide⟩ ⟨12, 2, 0, 1290337, 370288, 1437, 65536⟩
    (by decide) selected_cut_46291

theorem selected_cut_46292 : selected 9 ⟨1290355, by decide⟩
    (prefixPartial 12 370289) = some ⟨12, 2, 0, 1290355, 370289, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_370289_1290355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370289 ⟨1290355, by decide⟩ :=
  accepted_of_selected 12 370289 ⟨1290355, by decide⟩ ⟨12, 2, 0, 1290355, 370289, 1093, 65536⟩
    (by decide) selected_cut_46292

theorem selected_cut_46293 : selected 9 ⟨1290377, by decide⟩
    (prefixPartial 12 370290) = some ⟨12, 2, 0, 1290377, 370290, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_370290_1290377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370290 ⟨1290377, by decide⟩ :=
  accepted_of_selected 12 370290 ⟨1290377, by decide⟩ ⟨12, 2, 0, 1290377, 370290, 1133, 65536⟩
    (by decide) selected_cut_46293

theorem selected_cut_46294 : selected 9 ⟨1290407, by decide⟩
    (prefixPartial 12 370291) = some ⟨12, 2, 0, 1290407, 370291, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_370291_1290407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370291 ⟨1290407, by decide⟩ :=
  accepted_of_selected 12 370291 ⟨1290407, by decide⟩ ⟨12, 2, 0, 1290407, 370291, 1413, 65536⟩
    (by decide) selected_cut_46294

theorem unmarked_context_11_92572_1290408 : frontier 10 ⟨1290408, by decide⟩
    (prefixCache 11 92572) (prefixPartial 11 92572) = false := by
  decide +kernel

theorem node_context_11_92572_1290408 : EJMOriginalGlobalDAGData.nodes 10 ⟨1290408, by decide⟩ =
    .split (coordinate 11) (![⟨1290337, by decide⟩,⟨1290355, by decide⟩,⟨1290377, by decide⟩,⟨1290407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92572_1290408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92572 ⟨1290408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92572
    ⟨1290408, by decide⟩ (by decide) (![⟨1290337, by decide⟩,⟨1290355, by decide⟩,⟨1290377, by decide⟩,⟨1290407, by decide⟩]) unmarked_context_11_92572_1290408 node_context_11_92572_1290408
  intro a
  fin_cases a
  · exact context_12_370288_1290337
  · exact context_12_370289_1290355
  · exact context_12_370290_1290377
  · exact context_12_370291_1290407

theorem selected_cut_46295 : selected 10 ⟨1290465, by decide⟩
    (prefixPartial 11 92573) = some ⟨11, 2, 0, 1290465, 92573, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_92573_1290465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92573 ⟨1290465, by decide⟩ :=
  accepted_of_selected 11 92573 ⟨1290465, by decide⟩ ⟨11, 2, 0, 1290465, 92573, 3025, 262144⟩
    (by decide) selected_cut_46295

theorem selected_cut_46296 : selected 10 ⟨1290509, by decide⟩
    (prefixPartial 11 92574) = some ⟨11, 2, 0, 1290509, 92574, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_92574_1290509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92574 ⟨1290509, by decide⟩ :=
  accepted_of_selected 11 92574 ⟨1290509, by decide⟩ ⟨11, 2, 0, 1290509, 92574, 2253, 262144⟩
    (by decide) selected_cut_46296

theorem selected_cut_46297 : selected 10 ⟨1284138, by decide⟩
    (prefixPartial 11 92575) = some ⟨11, 1, 0, 1284138, 92575, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92575_1284138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92575 ⟨1284138, by decide⟩ :=
  accepted_of_selected 11 92575 ⟨1284138, by decide⟩ ⟨11, 1, 0, 1284138, 92575, 1, 262144⟩
    (by decide) selected_cut_46297

theorem unmarked_context_10_23143_1290510 : frontier 11 ⟨1290510, by decide⟩
    (prefixCache 10 23143) (prefixPartial 10 23143) = false := by
  decide +kernel

theorem node_context_10_23143_1290510 : EJMOriginalGlobalDAGData.nodes 11 ⟨1290510, by decide⟩ =
    .split (coordinate 10) (![⟨1290408, by decide⟩,⟨1290465, by decide⟩,⟨1290509, by decide⟩,⟨1284138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23143_1290510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23143 ⟨1290510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23143
    ⟨1290510, by decide⟩ (by decide) (![⟨1290408, by decide⟩,⟨1290465, by decide⟩,⟨1290509, by decide⟩,⟨1284138, by decide⟩]) unmarked_context_10_23143_1290510 node_context_10_23143_1290510
  intro a
  fin_cases a
  · exact context_11_92572_1290408
  · exact context_11_92573_1290465
  · exact context_11_92574_1290509
  · exact context_11_92575_1284138

theorem unmarked_context_9_5785_1290511 : frontier 12 ⟨1290511, by decide⟩
    (prefixCache 9 5785) (prefixPartial 9 5785) = false := by
  decide +kernel

theorem node_context_9_5785_1290511 : EJMOriginalGlobalDAGData.nodes 12 ⟨1290511, by decide⟩ =
    .split (coordinate 9) (![⟨1289947, by decide⟩,⟨893098, by decide⟩,⟨1290305, by decide⟩,⟨1290510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5785_1290511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5785 ⟨1290511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5785
    ⟨1290511, by decide⟩ (by decide) (![⟨1289947, by decide⟩,⟨893098, by decide⟩,⟨1290305, by decide⟩,⟨1290510, by decide⟩]) unmarked_context_9_5785_1290511 node_context_9_5785_1290511
  intro a
  fin_cases a
  · exact context_10_23140_1289947
  · exact context_10_23141_893098
  · exact context_10_23142_1290305
  · exact context_10_23143_1290510

theorem selected_cut_46298 : selected 10 ⟨1290545, by decide⟩
    (prefixPartial 11 92576) = some ⟨11, 2, 0, 1290545, 92576, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_92576_1290545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92576 ⟨1290545, by decide⟩ :=
  accepted_of_selected 11 92576 ⟨1290545, by decide⟩ ⟨11, 2, 0, 1290545, 92576, 1309, 262144⟩
    (by decide) selected_cut_46298

theorem selected_cut_46299 : selected 10 ⟨1290590, by decide⟩
    (prefixPartial 11 92577) = some ⟨11, 2, 0, 1290590, 92577, 1901, 262144⟩ := by
  decide +kernel

theorem context_11_92577_1290590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92577 ⟨1290590, by decide⟩ :=
  accepted_of_selected 11 92577 ⟨1290590, by decide⟩ ⟨11, 2, 0, 1290590, 92577, 1901, 262144⟩
    (by decide) selected_cut_46299

theorem selected_cut_46300 : selected 10 ⟨1290642, by decide⟩
    (prefixPartial 11 92578) = some ⟨11, 2, 0, 1290642, 92578, 2553, 262144⟩ := by
  decide +kernel

theorem context_11_92578_1290642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92578 ⟨1290642, by decide⟩ :=
  accepted_of_selected 11 92578 ⟨1290642, by decide⟩ ⟨11, 2, 0, 1290642, 92578, 2553, 262144⟩
    (by decide) selected_cut_46300

theorem selected_cut_46301 : selected 10 ⟨1290672, by decide⟩
    (prefixPartial 11 92579) = some ⟨11, 2, 0, 1290672, 92579, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_92579_1290672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92579 ⟨1290672, by decide⟩ :=
  accepted_of_selected 11 92579 ⟨1290672, by decide⟩ ⟨11, 2, 0, 1290672, 92579, 1589, 262144⟩
    (by decide) selected_cut_46301

theorem unmarked_context_10_23144_1290673 : frontier 11 ⟨1290673, by decide⟩
    (prefixCache 10 23144) (prefixPartial 10 23144) = false := by
  decide +kernel

theorem node_context_10_23144_1290673 : EJMOriginalGlobalDAGData.nodes 11 ⟨1290673, by decide⟩ =
    .split (coordinate 10) (![⟨1290545, by decide⟩,⟨1290590, by decide⟩,⟨1290642, by decide⟩,⟨1290672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23144_1290673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23144 ⟨1290673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23144
    ⟨1290673, by decide⟩ (by decide) (![⟨1290545, by decide⟩,⟨1290590, by decide⟩,⟨1290642, by decide⟩,⟨1290672, by decide⟩]) unmarked_context_10_23144_1290673 node_context_10_23144_1290673
  intro a
  fin_cases a
  · exact context_11_92576_1290545
  · exact context_11_92577_1290590
  · exact context_11_92578_1290642
  · exact context_11_92579_1290672

theorem selected_cut_46302 : selected 10 ⟨1290694, by decide⟩
    (prefixPartial 11 92580) = some ⟨11, 2, 0, 1290694, 92580, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_92580_1290694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92580 ⟨1290694, by decide⟩ :=
  accepted_of_selected 11 92580 ⟨1290694, by decide⟩ ⟨11, 2, 0, 1290694, 92580, 1369, 262144⟩
    (by decide) selected_cut_46302

theorem selected_cut_46303 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 92581) = some ⟨11, 1, 0, 892405, 92581, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92581_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92581 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 92581 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 92581, 1, 262144⟩
    (by decide) selected_cut_46303

theorem selected_cut_46304 : selected 10 ⟨1290726, by decide⟩
    (prefixPartial 11 92582) = some ⟨11, 2, 0, 1290726, 92582, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_92582_1290726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92582 ⟨1290726, by decide⟩ :=
  accepted_of_selected 11 92582 ⟨1290726, by decide⟩ ⟨11, 2, 0, 1290726, 92582, 1877, 262144⟩
    (by decide) selected_cut_46304

theorem selected_cut_46305 : selected 10 ⟨1290746, by decide⟩
    (prefixPartial 11 92583) = some ⟨11, 2, 0, 1290746, 92583, 1225, 262144⟩ := by
  decide +kernel

theorem context_11_92583_1290746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92583 ⟨1290746, by decide⟩ :=
  accepted_of_selected 11 92583 ⟨1290746, by decide⟩ ⟨11, 2, 0, 1290746, 92583, 1225, 262144⟩
    (by decide) selected_cut_46305

theorem unmarked_context_10_23145_1290747 : frontier 11 ⟨1290747, by decide⟩
    (prefixCache 10 23145) (prefixPartial 10 23145) = false := by
  decide +kernel

theorem node_context_10_23145_1290747 : EJMOriginalGlobalDAGData.nodes 11 ⟨1290747, by decide⟩ =
    .split (coordinate 10) (![⟨1290694, by decide⟩,⟨892405, by decide⟩,⟨1290726, by decide⟩,⟨1290746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23145_1290747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23145 ⟨1290747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23145
    ⟨1290747, by decide⟩ (by decide) (![⟨1290694, by decide⟩,⟨892405, by decide⟩,⟨1290726, by decide⟩,⟨1290746, by decide⟩]) unmarked_context_10_23145_1290747 node_context_10_23145_1290747
  intro a
  fin_cases a
  · exact context_11_92580_1290694
  · exact context_11_92581_892405
  · exact context_11_92582_1290726
  · exact context_11_92583_1290746

theorem selected_cut_46306 : selected 11 ⟨1290773, by decide⟩
    (prefixPartial 10 23146) = some ⟨10, 2, 0, 1290773, 23146, 1261, 1048576⟩ := by
  decide +kernel

theorem context_10_23146_1290773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23146 ⟨1290773, by decide⟩ :=
  accepted_of_selected 10 23146 ⟨1290773, by decide⟩ ⟨10, 2, 0, 1290773, 23146, 1261, 1048576⟩
    (by decide) selected_cut_46306

theorem selected_cut_46307 : selected 11 ⟨1290849, by decide⟩
    (prefixPartial 10 23147) = some ⟨10, 2, 0, 1290849, 23147, 3921, 1048576⟩ := by
  decide +kernel

theorem context_10_23147_1290849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23147 ⟨1290849, by decide⟩ :=
  accepted_of_selected 10 23147 ⟨1290849, by decide⟩ ⟨10, 2, 0, 1290849, 23147, 3921, 1048576⟩
    (by decide) selected_cut_46307

theorem unmarked_context_9_5786_1290850 : frontier 12 ⟨1290850, by decide⟩
    (prefixCache 9 5786) (prefixPartial 9 5786) = false := by
  decide +kernel

theorem node_context_9_5786_1290850 : EJMOriginalGlobalDAGData.nodes 12 ⟨1290850, by decide⟩ =
    .split (coordinate 9) (![⟨1290673, by decide⟩,⟨1290747, by decide⟩,⟨1290773, by decide⟩,⟨1290849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5786_1290850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5786 ⟨1290850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5786
    ⟨1290850, by decide⟩ (by decide) (![⟨1290673, by decide⟩,⟨1290747, by decide⟩,⟨1290773, by decide⟩,⟨1290849, by decide⟩]) unmarked_context_9_5786_1290850 node_context_9_5786_1290850
  intro a
  fin_cases a
  · exact context_10_23144_1290673
  · exact context_10_23145_1290747
  · exact context_10_23146_1290773
  · exact context_10_23147_1290849

theorem selected_cut_46308 : selected 10 ⟨1290871, by decide⟩
    (prefixPartial 11 92592) = some ⟨11, 2, 0, 1290871, 92592, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_92592_1290871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92592 ⟨1290871, by decide⟩ :=
  accepted_of_selected 11 92592 ⟨1290871, by decide⟩ ⟨11, 2, 0, 1290871, 92592, 1293, 262144⟩
    (by decide) selected_cut_46308

theorem selected_cut_46309 : selected 10 ⟨1290894, by decide⟩
    (prefixPartial 11 92593) = some ⟨11, 2, 0, 1290894, 92593, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_92593_1290894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92593 ⟨1290894, by decide⟩ :=
  accepted_of_selected 11 92593 ⟨1290894, by decide⟩ ⟨11, 2, 0, 1290894, 92593, 1537, 262144⟩
    (by decide) selected_cut_46309

theorem selected_cut_46310 : selected 10 ⟨1290905, by decide⟩
    (prefixPartial 11 92594) = some ⟨11, 2, 0, 1290905, 92594, 653, 262144⟩ := by
  decide +kernel

theorem context_11_92594_1290905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92594 ⟨1290905, by decide⟩ :=
  accepted_of_selected 11 92594 ⟨1290905, by decide⟩ ⟨11, 2, 0, 1290905, 92594, 653, 262144⟩
    (by decide) selected_cut_46310

theorem selected_cut_46311 : selected 10 ⟨1290924, by decide⟩
    (prefixPartial 11 92595) = some ⟨11, 2, 0, 1290924, 92595, 1069, 262144⟩ := by
  decide +kernel

theorem context_11_92595_1290924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92595 ⟨1290924, by decide⟩ :=
  accepted_of_selected 11 92595 ⟨1290924, by decide⟩ ⟨11, 2, 0, 1290924, 92595, 1069, 262144⟩
    (by decide) selected_cut_46311

theorem unmarked_context_10_23148_1290925 : frontier 11 ⟨1290925, by decide⟩
    (prefixCache 10 23148) (prefixPartial 10 23148) = false := by
  decide +kernel

theorem node_context_10_23148_1290925 : EJMOriginalGlobalDAGData.nodes 11 ⟨1290925, by decide⟩ =
    .split (coordinate 10) (![⟨1290871, by decide⟩,⟨1290894, by decide⟩,⟨1290905, by decide⟩,⟨1290924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23148_1290925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23148 ⟨1290925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23148
    ⟨1290925, by decide⟩ (by decide) (![⟨1290871, by decide⟩,⟨1290894, by decide⟩,⟨1290905, by decide⟩,⟨1290924, by decide⟩]) unmarked_context_10_23148_1290925 node_context_10_23148_1290925
  intro a
  fin_cases a
  · exact context_11_92592_1290871
  · exact context_11_92593_1290894
  · exact context_11_92594_1290905
  · exact context_11_92595_1290924

theorem selected_cut_46312 : selected 11 ⟨1290959, by decide⟩
    (prefixPartial 10 23149) = some ⟨10, 2, 0, 1290959, 23149, 1985, 1048576⟩ := by
  decide +kernel

theorem context_10_23149_1290959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23149 ⟨1290959, by decide⟩ :=
  accepted_of_selected 10 23149 ⟨1290959, by decide⟩ ⟨10, 2, 0, 1290959, 23149, 1985, 1048576⟩
    (by decide) selected_cut_46312

theorem selected_cut_46313 : selected 11 ⟨1290991, by decide⟩
    (prefixPartial 10 23150) = some ⟨10, 2, 0, 1290991, 23150, 1145, 1048576⟩ := by
  decide +kernel

theorem context_10_23150_1290991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23150 ⟨1290991, by decide⟩ :=
  accepted_of_selected 10 23150 ⟨1290991, by decide⟩ ⟨10, 2, 0, 1290991, 23150, 1145, 1048576⟩
    (by decide) selected_cut_46313

theorem selected_cut_46314 : selected 11 ⟨1291001, by decide⟩
    (prefixPartial 10 23151) = some ⟨10, 2, 0, 1291001, 23151, 173, 1048576⟩ := by
  decide +kernel

theorem context_10_23151_1291001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23151 ⟨1291001, by decide⟩ :=
  accepted_of_selected 10 23151 ⟨1291001, by decide⟩ ⟨10, 2, 0, 1291001, 23151, 173, 1048576⟩
    (by decide) selected_cut_46314

theorem unmarked_context_9_5787_1291002 : frontier 12 ⟨1291002, by decide⟩
    (prefixCache 9 5787) (prefixPartial 9 5787) = false := by
  decide +kernel

theorem node_context_9_5787_1291002 : EJMOriginalGlobalDAGData.nodes 12 ⟨1291002, by decide⟩ =
    .split (coordinate 9) (![⟨1290925, by decide⟩,⟨1290959, by decide⟩,⟨1290991, by decide⟩,⟨1291001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5787_1291002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5787 ⟨1291002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5787
    ⟨1291002, by decide⟩ (by decide) (![⟨1290925, by decide⟩,⟨1290959, by decide⟩,⟨1290991, by decide⟩,⟨1291001, by decide⟩]) unmarked_context_9_5787_1291002 node_context_9_5787_1291002
  intro a
  fin_cases a
  · exact context_10_23148_1290925
  · exact context_10_23149_1290959
  · exact context_10_23150_1290991
  · exact context_10_23151_1291001

theorem unmarked_context_8_1446_1291003 : frontier 13 ⟨1291003, by decide⟩
    (prefixCache 8 1446) (prefixPartial 8 1446) = false := by
  decide +kernel

theorem node_context_8_1446_1291003 : EJMOriginalGlobalDAGData.nodes 13 ⟨1291003, by decide⟩ =
    .split (coordinate 8) (![⟨1289529, by decide⟩,⟨1290511, by decide⟩,⟨1290850, by decide⟩,⟨1291002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1446_1291003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1446 ⟨1291003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1446
    ⟨1291003, by decide⟩ (by decide) (![⟨1289529, by decide⟩,⟨1290511, by decide⟩,⟨1290850, by decide⟩,⟨1291002, by decide⟩]) unmarked_context_8_1446_1291003 node_context_8_1446_1291003
  intro a
  fin_cases a
  · exact context_9_5784_1289529
  · exact context_9_5785_1290511
  · exact context_9_5786_1290850
  · exact context_9_5787_1291002

theorem selected_cut_46315 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92608) = some ⟨11, 1, 0, 434745, 92608, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92608_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92608 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92608 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92608, 1, 262144⟩
    (by decide) selected_cut_46315

theorem selected_cut_46316 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 92609) = some ⟨11, 1, 0, 167448, 92609, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92609_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92609 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 92609 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 92609, 1, 262144⟩
    (by decide) selected_cut_46316

theorem selected_cut_46317 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370440) = some ⟨12, 1, 0, 448748, 370440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370440_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370440 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370440 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370440, 1, 65536⟩
    (by decide) selected_cut_46317

theorem selected_cut_46318 : selected 9 ⟨1291072, by decide⟩
    (prefixPartial 12 370441) = some ⟨12, 2, 0, 1291072, 370441, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_370441_1291072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370441 ⟨1291072, by decide⟩ :=
  accepted_of_selected 12 370441 ⟨1291072, by decide⟩ ⟨12, 2, 0, 1291072, 370441, 2929, 65536⟩
    (by decide) selected_cut_46318

theorem selected_cut_46319 : selected 9 ⟨1291145, by decide⟩
    (prefixPartial 12 370442) = some ⟨12, 2, 0, 1291145, 370442, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_370442_1291145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370442 ⟨1291145, by decide⟩ :=
  accepted_of_selected 12 370442 ⟨1291145, by decide⟩ ⟨12, 2, 0, 1291145, 370442, 2989, 65536⟩
    (by decide) selected_cut_46319

theorem selected_cut_46320 : selected 9 ⟨1291221, by decide⟩
    (prefixPartial 12 370443) = some ⟨12, 2, 0, 1291221, 370443, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_370443_1291221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370443 ⟨1291221, by decide⟩ :=
  accepted_of_selected 12 370443 ⟨1291221, by decide⟩ ⟨12, 2, 0, 1291221, 370443, 3485, 65536⟩
    (by decide) selected_cut_46320

theorem unmarked_context_11_92610_1291222 : frontier 10 ⟨1291222, by decide⟩
    (prefixCache 11 92610) (prefixPartial 11 92610) = false := by
  decide +kernel

theorem node_context_11_92610_1291222 : EJMOriginalGlobalDAGData.nodes 10 ⟨1291222, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1291072, by decide⟩,⟨1291145, by decide⟩,⟨1291221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92610_1291222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92610 ⟨1291222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92610
    ⟨1291222, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1291072, by decide⟩,⟨1291145, by decide⟩,⟨1291221, by decide⟩]) unmarked_context_11_92610_1291222 node_context_11_92610_1291222
  intro a
  fin_cases a
  · exact context_12_370440_448748
  · exact context_12_370441_1291072
  · exact context_12_370442_1291145
  · exact context_12_370443_1291221

theorem selected_cut_46321 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370444) = some ⟨12, 1, 0, 448748, 370444, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370444_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370444 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370444 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370444, 1, 65536⟩
    (by decide) selected_cut_46321

theorem selected_cut_46322 : selected 9 ⟨1291269, by decide⟩
    (prefixPartial 12 370445) = some ⟨12, 2, 0, 1291269, 370445, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_370445_1291269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370445 ⟨1291269, by decide⟩ :=
  accepted_of_selected 12 370445 ⟨1291269, by decide⟩ ⟨12, 2, 0, 1291269, 370445, 2665, 65536⟩
    (by decide) selected_cut_46322

theorem selected_cut_46323 : selected 9 ⟨1291335, by decide⟩
    (prefixPartial 12 370446) = some ⟨12, 2, 0, 1291335, 370446, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_370446_1291335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370446 ⟨1291335, by decide⟩ :=
  accepted_of_selected 12 370446 ⟨1291335, by decide⟩ ⟨12, 2, 0, 1291335, 370446, 3081, 65536⟩
    (by decide) selected_cut_46323

theorem selected_cut_46324 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 370447) = some ⟨12, 1, 0, 903806, 370447, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370447_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370447 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 370447 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 370447, 1, 65536⟩
    (by decide) selected_cut_46324

theorem unmarked_context_11_92611_1291336 : frontier 10 ⟨1291336, by decide⟩
    (prefixCache 11 92611) (prefixPartial 11 92611) = false := by
  decide +kernel

theorem node_context_11_92611_1291336 : EJMOriginalGlobalDAGData.nodes 10 ⟨1291336, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1291269, by decide⟩,⟨1291335, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92611_1291336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92611 ⟨1291336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92611
    ⟨1291336, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1291269, by decide⟩,⟨1291335, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92611_1291336 node_context_11_92611_1291336
  intro a
  fin_cases a
  · exact context_12_370444_448748
  · exact context_12_370445_1291269
  · exact context_12_370446_1291335
  · exact context_12_370447_903806

theorem unmarked_context_10_23152_1291337 : frontier 11 ⟨1291337, by decide⟩
    (prefixCache 10 23152) (prefixPartial 10 23152) = false := by
  decide +kernel

theorem node_context_10_23152_1291337 : EJMOriginalGlobalDAGData.nodes 11 ⟨1291337, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1291222, by decide⟩,⟨1291336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23152_1291337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23152 ⟨1291337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23152
    ⟨1291337, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1291222, by decide⟩,⟨1291336, by decide⟩]) unmarked_context_10_23152_1291337 node_context_10_23152_1291337
  intro a
  fin_cases a
  · exact context_11_92608_434745
  · exact context_11_92609_167448
  · exact context_11_92610_1291222
  · exact context_11_92611_1291336

theorem selected_cut_46325 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 370448) = some ⟨12, 1, 0, 1255011, 370448, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370448_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370448 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 370448 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 370448, 1, 65536⟩
    (by decide) selected_cut_46325

theorem selected_cut_46326 : selected 9 ⟨1291381, by decide⟩
    (prefixPartial 12 370449) = some ⟨12, 2, 0, 1291381, 370449, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_370449_1291381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370449 ⟨1291381, by decide⟩ :=
  accepted_of_selected 12 370449 ⟨1291381, by decide⟩ ⟨12, 2, 0, 1291381, 370449, 2629, 65536⟩
    (by decide) selected_cut_46326

theorem selected_cut_46327 : selected 9 ⟨1291444, by decide⟩
    (prefixPartial 12 370450) = some ⟨12, 2, 0, 1291444, 370450, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_370450_1291444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370450 ⟨1291444, by decide⟩ :=
  accepted_of_selected 12 370450 ⟨1291444, by decide⟩ ⟨12, 2, 0, 1291444, 370450, 3025, 65536⟩
    (by decide) selected_cut_46327

theorem selected_cut_46328 : selected 9 ⟨1291507, by decide⟩
    (prefixPartial 12 370451) = some ⟨12, 2, 0, 1291507, 370451, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_370451_1291507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370451 ⟨1291507, by decide⟩ :=
  accepted_of_selected 12 370451 ⟨1291507, by decide⟩ ⟨12, 2, 0, 1291507, 370451, 3285, 65536⟩
    (by decide) selected_cut_46328

theorem unmarked_context_11_92612_1291508 : frontier 10 ⟨1291508, by decide⟩
    (prefixCache 11 92612) (prefixPartial 11 92612) = false := by
  decide +kernel

theorem node_context_11_92612_1291508 : EJMOriginalGlobalDAGData.nodes 10 ⟨1291508, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1291381, by decide⟩,⟨1291444, by decide⟩,⟨1291507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92612_1291508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92612 ⟨1291508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92612
    ⟨1291508, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1291381, by decide⟩,⟨1291444, by decide⟩,⟨1291507, by decide⟩]) unmarked_context_11_92612_1291508 node_context_11_92612_1291508
  intro a
  fin_cases a
  · exact context_12_370448_1255011
  · exact context_12_370449_1291381
  · exact context_12_370450_1291444
  · exact context_12_370451_1291507

theorem selected_cut_46329 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 92613) = some ⟨11, 1, 0, 892405, 92613, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92613_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92613 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 92613 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 92613, 1, 262144⟩
    (by decide) selected_cut_46329

theorem selected_cut_46330 : selected 9 ⟨1291564, by decide⟩
    (prefixPartial 12 370456) = some ⟨12, 2, 0, 1291564, 370456, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_370456_1291564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370456 ⟨1291564, by decide⟩ :=
  accepted_of_selected 12 370456 ⟨1291564, by decide⟩ ⟨12, 2, 0, 1291564, 370456, 2917, 65536⟩
    (by decide) selected_cut_46330

theorem selected_cut_46331 : selected 9 ⟨1291598, by decide⟩
    (prefixPartial 12 370457) = some ⟨12, 2, 0, 1291598, 370457, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_370457_1291598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370457 ⟨1291598, by decide⟩ :=
  accepted_of_selected 12 370457 ⟨1291598, by decide⟩ ⟨12, 2, 0, 1291598, 370457, 2345, 65536⟩
    (by decide) selected_cut_46331

theorem selected_cut_46332 : selected 9 ⟨1291660, by decide⟩
    (prefixPartial 12 370458) = some ⟨12, 2, 0, 1291660, 370458, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_370458_1291660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370458 ⟨1291660, by decide⟩ :=
  accepted_of_selected 12 370458 ⟨1291660, by decide⟩ ⟨12, 2, 0, 1291660, 370458, 2637, 65536⟩
    (by decide) selected_cut_46332

theorem selected_cut_46333 : selected 9 ⟨1291718, by decide⟩
    (prefixPartial 12 370459) = some ⟨12, 2, 0, 1291718, 370459, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_370459_1291718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370459 ⟨1291718, by decide⟩ :=
  accepted_of_selected 12 370459 ⟨1291718, by decide⟩ ⟨12, 2, 0, 1291718, 370459, 2993, 65536⟩
    (by decide) selected_cut_46333

theorem unmarked_context_11_92614_1291719 : frontier 10 ⟨1291719, by decide⟩
    (prefixCache 11 92614) (prefixPartial 11 92614) = false := by
  decide +kernel

theorem node_context_11_92614_1291719 : EJMOriginalGlobalDAGData.nodes 10 ⟨1291719, by decide⟩ =
    .split (coordinate 11) (![⟨1291564, by decide⟩,⟨1291598, by decide⟩,⟨1291660, by decide⟩,⟨1291718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92614_1291719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92614 ⟨1291719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92614
    ⟨1291719, by decide⟩ (by decide) (![⟨1291564, by decide⟩,⟨1291598, by decide⟩,⟨1291660, by decide⟩,⟨1291718, by decide⟩]) unmarked_context_11_92614_1291719 node_context_11_92614_1291719
  intro a
  fin_cases a
  · exact context_12_370456_1291564
  · exact context_12_370457_1291598
  · exact context_12_370458_1291660
  · exact context_12_370459_1291718

theorem selected_cut_46334 : selected 9 ⟨1291776, by decide⟩
    (prefixPartial 12 370460) = some ⟨12, 2, 0, 1291776, 370460, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_370460_1291776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370460 ⟨1291776, by decide⟩ :=
  accepted_of_selected 12 370460 ⟨1291776, by decide⟩ ⟨12, 2, 0, 1291776, 370460, 3073, 65536⟩
    (by decide) selected_cut_46334

theorem selected_cut_46335 : selected 9 ⟨1291809, by decide⟩
    (prefixPartial 12 370461) = some ⟨12, 2, 0, 1291809, 370461, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_370461_1291809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370461 ⟨1291809, by decide⟩ :=
  accepted_of_selected 12 370461 ⟨1291809, by decide⟩ ⟨12, 2, 0, 1291809, 370461, 2293, 65536⟩
    (by decide) selected_cut_46335

theorem selected_cut_46336 : selected 9 ⟨1291866, by decide⟩
    (prefixPartial 12 370462) = some ⟨12, 2, 0, 1291866, 370462, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_370462_1291866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370462 ⟨1291866, by decide⟩ :=
  accepted_of_selected 12 370462 ⟨1291866, by decide⟩ ⟨12, 2, 0, 1291866, 370462, 2873, 65536⟩
    (by decide) selected_cut_46336

theorem selected_cut_46337 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 370463) = some ⟨12, 1, 0, 903806, 370463, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370463_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370463 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 370463 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 370463, 1, 65536⟩
    (by decide) selected_cut_46337

theorem unmarked_context_11_92615_1291867 : frontier 10 ⟨1291867, by decide⟩
    (prefixCache 11 92615) (prefixPartial 11 92615) = false := by
  decide +kernel

theorem node_context_11_92615_1291867 : EJMOriginalGlobalDAGData.nodes 10 ⟨1291867, by decide⟩ =
    .split (coordinate 11) (![⟨1291776, by decide⟩,⟨1291809, by decide⟩,⟨1291866, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92615_1291867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92615 ⟨1291867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92615
    ⟨1291867, by decide⟩ (by decide) (![⟨1291776, by decide⟩,⟨1291809, by decide⟩,⟨1291866, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92615_1291867 node_context_11_92615_1291867
  intro a
  fin_cases a
  · exact context_12_370460_1291776
  · exact context_12_370461_1291809
  · exact context_12_370462_1291866
  · exact context_12_370463_903806

theorem unmarked_context_10_23153_1291868 : frontier 11 ⟨1291868, by decide⟩
    (prefixCache 10 23153) (prefixPartial 10 23153) = false := by
  decide +kernel

theorem node_context_10_23153_1291868 : EJMOriginalGlobalDAGData.nodes 11 ⟨1291868, by decide⟩ =
    .split (coordinate 10) (![⟨1291508, by decide⟩,⟨892405, by decide⟩,⟨1291719, by decide⟩,⟨1291867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23153_1291868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23153 ⟨1291868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23153
    ⟨1291868, by decide⟩ (by decide) (![⟨1291508, by decide⟩,⟨892405, by decide⟩,⟨1291719, by decide⟩,⟨1291867, by decide⟩]) unmarked_context_10_23153_1291868 node_context_10_23153_1291868
  intro a
  fin_cases a
  · exact context_11_92612_1291508
  · exact context_11_92613_892405
  · exact context_11_92614_1291719
  · exact context_11_92615_1291867

theorem selected_cut_46338 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 370464) = some ⟨12, 1, 0, 435790, 370464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370464_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370464 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 370464 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 370464, 1, 65536⟩
    (by decide) selected_cut_46338

theorem selected_cut_46339 : selected 9 ⟨1291908, by decide⟩
    (prefixPartial 12 370465) = some ⟨12, 2, 0, 1291908, 370465, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_370465_1291908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370465 ⟨1291908, by decide⟩ :=
  accepted_of_selected 12 370465 ⟨1291908, by decide⟩ ⟨12, 2, 0, 1291908, 370465, 2557, 65536⟩
    (by decide) selected_cut_46339

theorem selected_cut_46340 : selected 9 ⟨1291962, by decide⟩
    (prefixPartial 12 370466) = some ⟨12, 2, 0, 1291962, 370466, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_370466_1291962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370466 ⟨1291962, by decide⟩ :=
  accepted_of_selected 12 370466 ⟨1291962, by decide⟩ ⟨12, 2, 0, 1291962, 370466, 2789, 65536⟩
    (by decide) selected_cut_46340

theorem selected_cut_46341 : selected 9 ⟨1292021, by decide⟩
    (prefixPartial 12 370467) = some ⟨12, 2, 0, 1292021, 370467, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_370467_1292021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370467 ⟨1292021, by decide⟩ :=
  accepted_of_selected 12 370467 ⟨1292021, by decide⟩ ⟨12, 2, 0, 1292021, 370467, 3001, 65536⟩
    (by decide) selected_cut_46341

theorem unmarked_context_11_92616_1292022 : frontier 10 ⟨1292022, by decide⟩
    (prefixCache 11 92616) (prefixPartial 11 92616) = false := by
  decide +kernel

theorem node_context_11_92616_1292022 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292022, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1291908, by decide⟩,⟨1291962, by decide⟩,⟨1292021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92616_1292022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92616 ⟨1292022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92616
    ⟨1292022, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1291908, by decide⟩,⟨1291962, by decide⟩,⟨1292021, by decide⟩]) unmarked_context_11_92616_1292022 node_context_11_92616_1292022
  intro a
  fin_cases a
  · exact context_12_370464_435790
  · exact context_12_370465_1291908
  · exact context_12_370466_1291962
  · exact context_12_370467_1292021

theorem selected_cut_46342 : selected 9 ⟨1292093, by decide⟩
    (prefixPartial 12 370468) = some ⟨12, 2, 0, 1292093, 370468, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_370468_1292093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370468 ⟨1292093, by decide⟩ :=
  accepted_of_selected 12 370468 ⟨1292093, by decide⟩ ⟨12, 2, 0, 1292093, 370468, 3301, 65536⟩
    (by decide) selected_cut_46342

theorem selected_cut_46343 : selected 9 ⟨1292144, by decide⟩
    (prefixPartial 12 370469) = some ⟨12, 2, 0, 1292144, 370469, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_370469_1292144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370469 ⟨1292144, by decide⟩ :=
  accepted_of_selected 12 370469 ⟨1292144, by decide⟩ ⟨12, 2, 0, 1292144, 370469, 2605, 65536⟩
    (by decide) selected_cut_46343

theorem selected_cut_46344 : selected 9 ⟨1292194, by decide⟩
    (prefixPartial 12 370470) = some ⟨12, 2, 0, 1292194, 370470, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_370470_1292194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370470 ⟨1292194, by decide⟩ :=
  accepted_of_selected 12 370470 ⟨1292194, by decide⟩ ⟨12, 2, 0, 1292194, 370470, 2789, 65536⟩
    (by decide) selected_cut_46344

theorem selected_cut_46345 : selected 9 ⟨1292248, by decide⟩
    (prefixPartial 12 370471) = some ⟨12, 2, 0, 1292248, 370471, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_370471_1292248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370471 ⟨1292248, by decide⟩ :=
  accepted_of_selected 12 370471 ⟨1292248, by decide⟩ ⟨12, 2, 0, 1292248, 370471, 3109, 65536⟩
    (by decide) selected_cut_46345

theorem unmarked_context_11_92617_1292249 : frontier 10 ⟨1292249, by decide⟩
    (prefixCache 11 92617) (prefixPartial 11 92617) = false := by
  decide +kernel

theorem node_context_11_92617_1292249 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292249, by decide⟩ =
    .split (coordinate 11) (![⟨1292093, by decide⟩,⟨1292144, by decide⟩,⟨1292194, by decide⟩,⟨1292248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92617_1292249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92617 ⟨1292249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92617
    ⟨1292249, by decide⟩ (by decide) (![⟨1292093, by decide⟩,⟨1292144, by decide⟩,⟨1292194, by decide⟩,⟨1292248, by decide⟩]) unmarked_context_11_92617_1292249 node_context_11_92617_1292249
  intro a
  fin_cases a
  · exact context_12_370468_1292093
  · exact context_12_370469_1292144
  · exact context_12_370470_1292194
  · exact context_12_370471_1292248

theorem selected_cut_46346 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 370472) = some ⟨12, 1, 0, 435790, 370472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370472_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370472 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 370472 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 370472, 1, 65536⟩
    (by decide) selected_cut_46346

theorem selected_cut_46347 : selected 9 ⟨1292283, by decide⟩
    (prefixPartial 12 370473) = some ⟨12, 2, 0, 1292283, 370473, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_370473_1292283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370473 ⟨1292283, by decide⟩ :=
  accepted_of_selected 12 370473 ⟨1292283, by decide⟩ ⟨12, 2, 0, 1292283, 370473, 2125, 65536⟩
    (by decide) selected_cut_46347

theorem selected_cut_46348 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 370474) = some ⟨12, 1, 0, 1113261, 370474, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370474_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370474 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 370474 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 370474, 1, 65536⟩
    (by decide) selected_cut_46348

theorem selected_cut_46349 : selected 9 ⟨1292320, by decide⟩
    (prefixPartial 12 370475) = some ⟨12, 2, 0, 1292320, 370475, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_370475_1292320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370475 ⟨1292320, by decide⟩ :=
  accepted_of_selected 12 370475 ⟨1292320, by decide⟩ ⟨12, 2, 0, 1292320, 370475, 2573, 65536⟩
    (by decide) selected_cut_46349

theorem unmarked_context_11_92618_1292321 : frontier 10 ⟨1292321, by decide⟩
    (prefixCache 11 92618) (prefixPartial 11 92618) = false := by
  decide +kernel

theorem node_context_11_92618_1292321 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292321, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1292283, by decide⟩,⟨1113261, by decide⟩,⟨1292320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92618_1292321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92618 ⟨1292321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92618
    ⟨1292321, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1292283, by decide⟩,⟨1113261, by decide⟩,⟨1292320, by decide⟩]) unmarked_context_11_92618_1292321 node_context_11_92618_1292321
  intro a
  fin_cases a
  · exact context_12_370472_435790
  · exact context_12_370473_1292283
  · exact context_12_370474_1113261
  · exact context_12_370475_1292320

theorem selected_cut_46350 : selected 9 ⟨1292375, by decide⟩
    (prefixPartial 12 370476) = some ⟨12, 2, 0, 1292375, 370476, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_370476_1292375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370476 ⟨1292375, by decide⟩ :=
  accepted_of_selected 12 370476 ⟨1292375, by decide⟩ ⟨12, 2, 0, 1292375, 370476, 2849, 65536⟩
    (by decide) selected_cut_46350

theorem selected_cut_46351 : selected 9 ⟨1292406, by decide⟩
    (prefixPartial 12 370477) = some ⟨12, 2, 0, 1292406, 370477, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_370477_1292406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370477 ⟨1292406, by decide⟩ :=
  accepted_of_selected 12 370477 ⟨1292406, by decide⟩ ⟨12, 2, 0, 1292406, 370477, 2237, 65536⟩
    (by decide) selected_cut_46351

theorem selected_cut_46352 : selected 9 ⟨1292445, by decide⟩
    (prefixPartial 12 370478) = some ⟨12, 2, 0, 1292445, 370478, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_370478_1292445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370478 ⟨1292445, by decide⟩ :=
  accepted_of_selected 12 370478 ⟨1292445, by decide⟩ ⟨12, 2, 0, 1292445, 370478, 2537, 65536⟩
    (by decide) selected_cut_46352

theorem selected_cut_46353 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 370479) = some ⟨12, 1, 0, 903806, 370479, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370479_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370479 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 370479 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 370479, 1, 65536⟩
    (by decide) selected_cut_46353

theorem unmarked_context_11_92619_1292446 : frontier 10 ⟨1292446, by decide⟩
    (prefixCache 11 92619) (prefixPartial 11 92619) = false := by
  decide +kernel

theorem node_context_11_92619_1292446 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292446, by decide⟩ =
    .split (coordinate 11) (![⟨1292375, by decide⟩,⟨1292406, by decide⟩,⟨1292445, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92619_1292446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92619 ⟨1292446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92619
    ⟨1292446, by decide⟩ (by decide) (![⟨1292375, by decide⟩,⟨1292406, by decide⟩,⟨1292445, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92619_1292446 node_context_11_92619_1292446
  intro a
  fin_cases a
  · exact context_12_370476_1292375
  · exact context_12_370477_1292406
  · exact context_12_370478_1292445
  · exact context_12_370479_903806

theorem unmarked_context_10_23154_1292447 : frontier 11 ⟨1292447, by decide⟩
    (prefixCache 10 23154) (prefixPartial 10 23154) = false := by
  decide +kernel

theorem node_context_10_23154_1292447 : EJMOriginalGlobalDAGData.nodes 11 ⟨1292447, by decide⟩ =
    .split (coordinate 10) (![⟨1292022, by decide⟩,⟨1292249, by decide⟩,⟨1292321, by decide⟩,⟨1292446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23154_1292447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23154 ⟨1292447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23154
    ⟨1292447, by decide⟩ (by decide) (![⟨1292022, by decide⟩,⟨1292249, by decide⟩,⟨1292321, by decide⟩,⟨1292446, by decide⟩]) unmarked_context_10_23154_1292447 node_context_10_23154_1292447
  intro a
  fin_cases a
  · exact context_11_92616_1292022
  · exact context_11_92617_1292249
  · exact context_11_92618_1292321
  · exact context_11_92619_1292446

theorem selected_cut_46354 : selected 9 ⟨399079, by decide⟩
    (prefixPartial 12 370480) = some ⟨12, 1, 0, 399079, 370480, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370480_399079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370480 ⟨399079, by decide⟩ :=
  accepted_of_selected 12 370480 ⟨399079, by decide⟩ ⟨12, 1, 0, 399079, 370480, 1, 65536⟩
    (by decide) selected_cut_46354

theorem selected_cut_46355 : selected 9 ⟨1292484, by decide⟩
    (prefixPartial 12 370481) = some ⟨12, 2, 0, 1292484, 370481, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_370481_1292484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370481 ⟨1292484, by decide⟩ :=
  accepted_of_selected 12 370481 ⟨1292484, by decide⟩ ⟨12, 2, 0, 1292484, 370481, 2233, 65536⟩
    (by decide) selected_cut_46355

theorem selected_cut_46356 : selected 9 ⟨1292521, by decide⟩
    (prefixPartial 12 370482) = some ⟨12, 2, 0, 1292521, 370482, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_370482_1292521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370482 ⟨1292521, by decide⟩ :=
  accepted_of_selected 12 370482 ⟨1292521, by decide⟩ ⟨12, 2, 0, 1292521, 370482, 2349, 65536⟩
    (by decide) selected_cut_46356

theorem selected_cut_46357 : selected 9 ⟨1292568, by decide⟩
    (prefixPartial 12 370483) = some ⟨12, 2, 0, 1292568, 370483, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_370483_1292568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370483 ⟨1292568, by decide⟩ :=
  accepted_of_selected 12 370483 ⟨1292568, by decide⟩ ⟨12, 2, 0, 1292568, 370483, 2641, 65536⟩
    (by decide) selected_cut_46357

theorem unmarked_context_11_92620_1292569 : frontier 10 ⟨1292569, by decide⟩
    (prefixCache 11 92620) (prefixPartial 11 92620) = false := by
  decide +kernel

theorem node_context_11_92620_1292569 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292569, by decide⟩ =
    .split (coordinate 11) (![⟨399079, by decide⟩,⟨1292484, by decide⟩,⟨1292521, by decide⟩,⟨1292568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92620_1292569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92620 ⟨1292569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92620
    ⟨1292569, by decide⟩ (by decide) (![⟨399079, by decide⟩,⟨1292484, by decide⟩,⟨1292521, by decide⟩,⟨1292568, by decide⟩]) unmarked_context_11_92620_1292569 node_context_11_92620_1292569
  intro a
  fin_cases a
  · exact context_12_370480_399079
  · exact context_12_370481_1292484
  · exact context_12_370482_1292521
  · exact context_12_370483_1292568

theorem selected_cut_46358 : selected 9 ⟨1292626, by decide⟩
    (prefixPartial 12 370484) = some ⟨12, 2, 0, 1292626, 370484, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_370484_1292626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370484 ⟨1292626, by decide⟩ :=
  accepted_of_selected 12 370484 ⟨1292626, by decide⟩ ⟨12, 2, 0, 1292626, 370484, 2593, 65536⟩
    (by decide) selected_cut_46358

theorem selected_cut_46359 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 370485) = some ⟨12, 1, 0, 689956, 370485, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370485_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370485 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 370485 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 370485, 1, 65536⟩
    (by decide) selected_cut_46359

theorem selected_cut_46360 : selected 9 ⟨1292662, by decide⟩
    (prefixPartial 12 370486) = some ⟨12, 2, 0, 1292662, 370486, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_370486_1292662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370486 ⟨1292662, by decide⟩ :=
  accepted_of_selected 12 370486 ⟨1292662, by decide⟩ ⟨12, 2, 0, 1292662, 370486, 2225, 65536⟩
    (by decide) selected_cut_46360

theorem selected_cut_46361 : selected 9 ⟨1292703, by decide⟩
    (prefixPartial 12 370487) = some ⟨12, 2, 0, 1292703, 370487, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_370487_1292703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370487 ⟨1292703, by decide⟩ :=
  accepted_of_selected 12 370487 ⟨1292703, by decide⟩ ⟨12, 2, 0, 1292703, 370487, 2581, 65536⟩
    (by decide) selected_cut_46361

theorem unmarked_context_11_92621_1292704 : frontier 10 ⟨1292704, by decide⟩
    (prefixCache 11 92621) (prefixPartial 11 92621) = false := by
  decide +kernel

theorem node_context_11_92621_1292704 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292704, by decide⟩ =
    .split (coordinate 11) (![⟨1292626, by decide⟩,⟨689956, by decide⟩,⟨1292662, by decide⟩,⟨1292703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92621_1292704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92621 ⟨1292704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92621
    ⟨1292704, by decide⟩ (by decide) (![⟨1292626, by decide⟩,⟨689956, by decide⟩,⟨1292662, by decide⟩,⟨1292703, by decide⟩]) unmarked_context_11_92621_1292704 node_context_11_92621_1292704
  intro a
  fin_cases a
  · exact context_12_370484_1292626
  · exact context_12_370485_689956
  · exact context_12_370486_1292662
  · exact context_12_370487_1292703

theorem selected_cut_46362 : selected 9 ⟨1292755, by decide⟩
    (prefixPartial 12 370488) = some ⟨12, 2, 0, 1292755, 370488, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_370488_1292755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370488 ⟨1292755, by decide⟩ :=
  accepted_of_selected 12 370488 ⟨1292755, by decide⟩ ⟨12, 2, 0, 1292755, 370488, 2437, 65536⟩
    (by decide) selected_cut_46362

theorem selected_cut_46363 : selected 9 ⟨1292788, by decide⟩
    (prefixPartial 12 370489) = some ⟨12, 2, 0, 1292788, 370489, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_370489_1292788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370489 ⟨1292788, by decide⟩ :=
  accepted_of_selected 12 370489 ⟨1292788, by decide⟩ ⟨12, 2, 0, 1292788, 370489, 2013, 65536⟩
    (by decide) selected_cut_46363

theorem selected_cut_46364 : selected 9 ⟨1292816, by decide⟩
    (prefixPartial 12 370490) = some ⟨12, 2, 0, 1292816, 370490, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_370490_1292816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370490 ⟨1292816, by decide⟩ :=
  accepted_of_selected 12 370490 ⟨1292816, by decide⟩ ⟨12, 2, 0, 1292816, 370490, 2029, 65536⟩
    (by decide) selected_cut_46364

theorem selected_cut_46365 : selected 9 ⟨1292849, by decide⟩
    (prefixPartial 12 370491) = some ⟨12, 2, 0, 1292849, 370491, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_370491_1292849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370491 ⟨1292849, by decide⟩ :=
  accepted_of_selected 12 370491 ⟨1292849, by decide⟩ ⟨12, 2, 0, 1292849, 370491, 2277, 65536⟩
    (by decide) selected_cut_46365

theorem unmarked_context_11_92622_1292850 : frontier 10 ⟨1292850, by decide⟩
    (prefixCache 11 92622) (prefixPartial 11 92622) = false := by
  decide +kernel

theorem node_context_11_92622_1292850 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292850, by decide⟩ =
    .split (coordinate 11) (![⟨1292755, by decide⟩,⟨1292788, by decide⟩,⟨1292816, by decide⟩,⟨1292849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92622_1292850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92622 ⟨1292850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92622
    ⟨1292850, by decide⟩ (by decide) (![⟨1292755, by decide⟩,⟨1292788, by decide⟩,⟨1292816, by decide⟩,⟨1292849, by decide⟩]) unmarked_context_11_92622_1292850 node_context_11_92622_1292850
  intro a
  fin_cases a
  · exact context_12_370488_1292755
  · exact context_12_370489_1292788
  · exact context_12_370490_1292816
  · exact context_12_370491_1292849

theorem selected_cut_46366 : selected 9 ⟨1292889, by decide⟩
    (prefixPartial 12 370492) = some ⟨12, 2, 0, 1292889, 370492, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_370492_1292889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370492 ⟨1292889, by decide⟩ :=
  accepted_of_selected 12 370492 ⟨1292889, by decide⟩ ⟨12, 2, 0, 1292889, 370492, 2281, 65536⟩
    (by decide) selected_cut_46366

theorem selected_cut_46367 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 370493) = some ⟨12, 1, 0, 762108, 370493, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370493_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370493 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 370493 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 370493, 1, 65536⟩
    (by decide) selected_cut_46367

theorem selected_cut_46368 : selected 9 ⟨1292919, by decide⟩
    (prefixPartial 12 370494) = some ⟨12, 2, 0, 1292919, 370494, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_370494_1292919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370494 ⟨1292919, by decide⟩ :=
  accepted_of_selected 12 370494 ⟨1292919, by decide⟩ ⟨12, 2, 0, 1292919, 370494, 2021, 65536⟩
    (by decide) selected_cut_46368

theorem selected_cut_46369 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 370495) = some ⟨12, 1, 0, 1116246, 370495, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370495_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370495 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 370495 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 370495, 1, 65536⟩
    (by decide) selected_cut_46369

theorem unmarked_context_11_92623_1292920 : frontier 10 ⟨1292920, by decide⟩
    (prefixCache 11 92623) (prefixPartial 11 92623) = false := by
  decide +kernel

theorem node_context_11_92623_1292920 : EJMOriginalGlobalDAGData.nodes 10 ⟨1292920, by decide⟩ =
    .split (coordinate 11) (![⟨1292889, by decide⟩,⟨762108, by decide⟩,⟨1292919, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92623_1292920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92623 ⟨1292920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92623
    ⟨1292920, by decide⟩ (by decide) (![⟨1292889, by decide⟩,⟨762108, by decide⟩,⟨1292919, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_92623_1292920 node_context_11_92623_1292920
  intro a
  fin_cases a
  · exact context_12_370492_1292889
  · exact context_12_370493_762108
  · exact context_12_370494_1292919
  · exact context_12_370495_1116246

theorem unmarked_context_10_23155_1292921 : frontier 11 ⟨1292921, by decide⟩
    (prefixCache 10 23155) (prefixPartial 10 23155) = false := by
  decide +kernel

theorem node_context_10_23155_1292921 : EJMOriginalGlobalDAGData.nodes 11 ⟨1292921, by decide⟩ =
    .split (coordinate 10) (![⟨1292569, by decide⟩,⟨1292704, by decide⟩,⟨1292850, by decide⟩,⟨1292920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23155_1292921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23155 ⟨1292921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23155
    ⟨1292921, by decide⟩ (by decide) (![⟨1292569, by decide⟩,⟨1292704, by decide⟩,⟨1292850, by decide⟩,⟨1292920, by decide⟩]) unmarked_context_10_23155_1292921 node_context_10_23155_1292921
  intro a
  fin_cases a
  · exact context_11_92620_1292569
  · exact context_11_92621_1292704
  · exact context_11_92622_1292850
  · exact context_11_92623_1292920

theorem unmarked_context_9_5788_1292922 : frontier 12 ⟨1292922, by decide⟩
    (prefixCache 9 5788) (prefixPartial 9 5788) = false := by
  decide +kernel

theorem node_context_9_5788_1292922 : EJMOriginalGlobalDAGData.nodes 12 ⟨1292922, by decide⟩ =
    .split (coordinate 9) (![⟨1291337, by decide⟩,⟨1291868, by decide⟩,⟨1292447, by decide⟩,⟨1292921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5788_1292922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5788 ⟨1292922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5788
    ⟨1292922, by decide⟩ (by decide) (![⟨1291337, by decide⟩,⟨1291868, by decide⟩,⟨1292447, by decide⟩,⟨1292921, by decide⟩]) unmarked_context_9_5788_1292922 node_context_9_5788_1292922
  intro a
  fin_cases a
  · exact context_10_23152_1291337
  · exact context_10_23153_1291868
  · exact context_10_23154_1292447
  · exact context_10_23155_1292921

theorem selected_cut_46370 : selected 10 ⟨1283168, by decide⟩
    (prefixPartial 11 92624) = some ⟨11, 1, 0, 1283168, 92624, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92624_1283168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92624 ⟨1283168, by decide⟩ :=
  accepted_of_selected 11 92624 ⟨1283168, by decide⟩ ⟨11, 1, 0, 1283168, 92624, 1, 262144⟩
    (by decide) selected_cut_46370

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
