/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover336
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32355 : selected 8 ⟨831696, by decide⟩
    (prefixPartial 13 433281) = some ⟨13, 2, 0, 831696, 433281, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_433281_831696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433281 ⟨831696, by decide⟩ :=
  accepted_of_selected 13 433281 ⟨831696, by decide⟩ ⟨13, 2, 0, 831696, 433281, 2761, 16384⟩
    (by decide) selected_cut_32355

theorem selected_cut_32356 : selected 8 ⟨831712, by decide⟩
    (prefixPartial 13 433282) = some ⟨13, 2, 0, 831712, 433282, 837, 16384⟩ := by
  decide +kernel

theorem context_13_433282_831712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433282 ⟨831712, by decide⟩ :=
  accepted_of_selected 13 433282 ⟨831712, by decide⟩ ⟨13, 2, 0, 831712, 433282, 837, 16384⟩
    (by decide) selected_cut_32356

theorem selected_cut_32357 : selected 8 ⟨831722, by decide⟩
    (prefixPartial 13 433283) = some ⟨13, 2, 0, 831722, 433283, 769, 16384⟩ := by
  decide +kernel

theorem context_13_433283_831722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433283 ⟨831722, by decide⟩ :=
  accepted_of_selected 13 433283 ⟨831722, by decide⟩ ⟨13, 2, 0, 831722, 433283, 769, 16384⟩
    (by decide) selected_cut_32357

theorem unmarked_context_12_108320_831723 : frontier 9 ⟨831723, by decide⟩
    (prefixCache 12 108320) (prefixPartial 12 108320) = false := by
  decide +kernel

theorem node_context_12_108320_831723 : EJMOriginalGlobalDAGData.nodes 9 ⟨831723, by decide⟩ =
    .split (coordinate 12) (![⟨831640, by decide⟩,⟨831696, by decide⟩,⟨831712, by decide⟩,⟨831722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108320_831723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108320 ⟨831723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108320
    ⟨831723, by decide⟩ (by decide) (![⟨831640, by decide⟩,⟨831696, by decide⟩,⟨831712, by decide⟩,⟨831722, by decide⟩]) unmarked_context_12_108320_831723 node_context_12_108320_831723
  intro a
  fin_cases a
  · exact context_13_433280_831640
  · exact context_13_433281_831696
  · exact context_13_433282_831712
  · exact context_13_433283_831722

theorem selected_cut_32358 : selected 8 ⟨831757, by decide⟩
    (prefixPartial 13 433284) = some ⟨13, 2, 0, 831757, 433284, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_433284_831757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433284 ⟨831757, by decide⟩ :=
  accepted_of_selected 13 433284 ⟨831757, by decide⟩ ⟨13, 2, 0, 831757, 433284, 1593, 16384⟩
    (by decide) selected_cut_32358

theorem selected_cut_32359 : selected 8 ⟨831810, by decide⟩
    (prefixPartial 13 433285) = some ⟨13, 2, 0, 831810, 433285, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_433285_831810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433285 ⟨831810, by decide⟩ :=
  accepted_of_selected 13 433285 ⟨831810, by decide⟩ ⟨13, 2, 0, 831810, 433285, 2541, 16384⟩
    (by decide) selected_cut_32359

theorem selected_cut_32360 : selected 8 ⟨831825, by decide⟩
    (prefixPartial 13 433286) = some ⟨13, 2, 0, 831825, 433286, 901, 16384⟩ := by
  decide +kernel

theorem context_13_433286_831825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433286 ⟨831825, by decide⟩ :=
  accepted_of_selected 13 433286 ⟨831825, by decide⟩ ⟨13, 2, 0, 831825, 433286, 901, 16384⟩
    (by decide) selected_cut_32360

theorem selected_cut_32361 : selected 8 ⟨831833, by decide⟩
    (prefixPartial 13 433287) = some ⟨13, 2, 0, 831833, 433287, 629, 16384⟩ := by
  decide +kernel

theorem context_13_433287_831833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433287 ⟨831833, by decide⟩ :=
  accepted_of_selected 13 433287 ⟨831833, by decide⟩ ⟨13, 2, 0, 831833, 433287, 629, 16384⟩
    (by decide) selected_cut_32361

theorem unmarked_context_12_108321_831834 : frontier 9 ⟨831834, by decide⟩
    (prefixCache 12 108321) (prefixPartial 12 108321) = false := by
  decide +kernel

theorem node_context_12_108321_831834 : EJMOriginalGlobalDAGData.nodes 9 ⟨831834, by decide⟩ =
    .split (coordinate 12) (![⟨831757, by decide⟩,⟨831810, by decide⟩,⟨831825, by decide⟩,⟨831833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108321_831834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108321 ⟨831834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108321
    ⟨831834, by decide⟩ (by decide) (![⟨831757, by decide⟩,⟨831810, by decide⟩,⟨831825, by decide⟩,⟨831833, by decide⟩]) unmarked_context_12_108321_831834 node_context_12_108321_831834
  intro a
  fin_cases a
  · exact context_13_433284_831757
  · exact context_13_433285_831810
  · exact context_13_433286_831825
  · exact context_13_433287_831833

theorem selected_cut_32362 : selected 8 ⟨831868, by decide⟩
    (prefixPartial 13 433288) = some ⟨13, 2, 0, 831868, 433288, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_433288_831868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433288 ⟨831868, by decide⟩ :=
  accepted_of_selected 13 433288 ⟨831868, by decide⟩ ⟨13, 2, 0, 831868, 433288, 1509, 16384⟩
    (by decide) selected_cut_32362

theorem selected_cut_32363 : selected 8 ⟨831927, by decide⟩
    (prefixPartial 13 433289) = some ⟨13, 2, 0, 831927, 433289, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_433289_831927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433289 ⟨831927, by decide⟩ :=
  accepted_of_selected 13 433289 ⟨831927, by decide⟩ ⟨13, 2, 0, 831927, 433289, 2401, 16384⟩
    (by decide) selected_cut_32363

theorem selected_cut_32364 : selected 8 ⟨831945, by decide⟩
    (prefixPartial 13 433290) = some ⟨13, 2, 0, 831945, 433290, 857, 16384⟩ := by
  decide +kernel

theorem context_13_433290_831945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433290 ⟨831945, by decide⟩ :=
  accepted_of_selected 13 433290 ⟨831945, by decide⟩ ⟨13, 2, 0, 831945, 433290, 857, 16384⟩
    (by decide) selected_cut_32364

theorem selected_cut_32365 : selected 8 ⟨831954, by decide⟩
    (prefixPartial 13 433291) = some ⟨13, 2, 0, 831954, 433291, 665, 16384⟩ := by
  decide +kernel

theorem context_13_433291_831954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433291 ⟨831954, by decide⟩ :=
  accepted_of_selected 13 433291 ⟨831954, by decide⟩ ⟨13, 2, 0, 831954, 433291, 665, 16384⟩
    (by decide) selected_cut_32365

theorem unmarked_context_12_108322_831955 : frontier 9 ⟨831955, by decide⟩
    (prefixCache 12 108322) (prefixPartial 12 108322) = false := by
  decide +kernel

theorem node_context_12_108322_831955 : EJMOriginalGlobalDAGData.nodes 9 ⟨831955, by decide⟩ =
    .split (coordinate 12) (![⟨831868, by decide⟩,⟨831927, by decide⟩,⟨831945, by decide⟩,⟨831954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108322_831955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108322 ⟨831955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108322
    ⟨831955, by decide⟩ (by decide) (![⟨831868, by decide⟩,⟨831927, by decide⟩,⟨831945, by decide⟩,⟨831954, by decide⟩]) unmarked_context_12_108322_831955 node_context_12_108322_831955
  intro a
  fin_cases a
  · exact context_13_433288_831868
  · exact context_13_433289_831927
  · exact context_13_433290_831945
  · exact context_13_433291_831954

theorem selected_cut_32366 : selected 8 ⟨831986, by decide⟩
    (prefixPartial 13 433292) = some ⟨13, 2, 0, 831986, 433292, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_433292_831986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433292 ⟨831986, by decide⟩ :=
  accepted_of_selected 13 433292 ⟨831986, by decide⟩ ⟨13, 2, 0, 831986, 433292, 1473, 16384⟩
    (by decide) selected_cut_32366

theorem selected_cut_32367 : selected 8 ⟨832033, by decide⟩
    (prefixPartial 13 433293) = some ⟨13, 2, 0, 832033, 433293, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_433293_832033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433293 ⟨832033, by decide⟩ :=
  accepted_of_selected 13 433293 ⟨832033, by decide⟩ ⟨13, 2, 0, 832033, 433293, 2549, 16384⟩
    (by decide) selected_cut_32367

theorem selected_cut_32368 : selected 8 ⟨832052, by decide⟩
    (prefixPartial 13 433294) = some ⟨13, 2, 0, 832052, 433294, 917, 16384⟩ := by
  decide +kernel

theorem context_13_433294_832052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433294 ⟨832052, by decide⟩ :=
  accepted_of_selected 13 433294 ⟨832052, by decide⟩ ⟨13, 2, 0, 832052, 433294, 917, 16384⟩
    (by decide) selected_cut_32368

theorem selected_cut_32369 : selected 8 ⟨832058, by decide⟩
    (prefixPartial 13 433295) = some ⟨13, 2, 0, 832058, 433295, 577, 16384⟩ := by
  decide +kernel

theorem context_13_433295_832058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433295 ⟨832058, by decide⟩ :=
  accepted_of_selected 13 433295 ⟨832058, by decide⟩ ⟨13, 2, 0, 832058, 433295, 577, 16384⟩
    (by decide) selected_cut_32369

theorem unmarked_context_12_108323_832059 : frontier 9 ⟨832059, by decide⟩
    (prefixCache 12 108323) (prefixPartial 12 108323) = false := by
  decide +kernel

theorem node_context_12_108323_832059 : EJMOriginalGlobalDAGData.nodes 9 ⟨832059, by decide⟩ =
    .split (coordinate 12) (![⟨831986, by decide⟩,⟨832033, by decide⟩,⟨832052, by decide⟩,⟨832058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108323_832059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108323 ⟨832059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108323
    ⟨832059, by decide⟩ (by decide) (![⟨831986, by decide⟩,⟨832033, by decide⟩,⟨832052, by decide⟩,⟨832058, by decide⟩]) unmarked_context_12_108323_832059 node_context_12_108323_832059
  intro a
  fin_cases a
  · exact context_13_433292_831986
  · exact context_13_433293_832033
  · exact context_13_433294_832052
  · exact context_13_433295_832058

theorem unmarked_context_11_27080_832060 : frontier 10 ⟨832060, by decide⟩
    (prefixCache 11 27080) (prefixPartial 11 27080) = false := by
  decide +kernel

theorem node_context_11_27080_832060 : EJMOriginalGlobalDAGData.nodes 10 ⟨832060, by decide⟩ =
    .split (coordinate 11) (![⟨831723, by decide⟩,⟨831834, by decide⟩,⟨831955, by decide⟩,⟨832059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27080_832060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27080 ⟨832060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27080
    ⟨832060, by decide⟩ (by decide) (![⟨831723, by decide⟩,⟨831834, by decide⟩,⟨831955, by decide⟩,⟨832059, by decide⟩]) unmarked_context_11_27080_832060 node_context_11_27080_832060
  intro a
  fin_cases a
  · exact context_12_108320_831723
  · exact context_12_108321_831834
  · exact context_12_108322_831955
  · exact context_12_108323_832059

theorem selected_cut_32370 : selected 8 ⟨832082, by decide⟩
    (prefixPartial 13 433296) = some ⟨13, 2, 0, 832082, 433296, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_433296_832082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433296 ⟨832082, by decide⟩ :=
  accepted_of_selected 13 433296 ⟨832082, by decide⟩ ⟨13, 2, 0, 832082, 433296, 1253, 16384⟩
    (by decide) selected_cut_32370

theorem selected_cut_32371 : selected 8 ⟨832149, by decide⟩
    (prefixPartial 13 433297) = some ⟨13, 2, 0, 832149, 433297, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_433297_832149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433297 ⟨832149, by decide⟩ :=
  accepted_of_selected 13 433297 ⟨832149, by decide⟩ ⟨13, 2, 0, 832149, 433297, 2749, 16384⟩
    (by decide) selected_cut_32371

theorem selected_cut_32372 : selected 8 ⟨832168, by decide⟩
    (prefixPartial 13 433298) = some ⟨13, 2, 0, 832168, 433298, 913, 16384⟩ := by
  decide +kernel

theorem context_13_433298_832168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433298 ⟨832168, by decide⟩ :=
  accepted_of_selected 13 433298 ⟨832168, by decide⟩ ⟨13, 2, 0, 832168, 433298, 913, 16384⟩
    (by decide) selected_cut_32372

theorem selected_cut_32373 : selected 8 ⟨832182, by decide⟩
    (prefixPartial 13 433299) = some ⟨13, 2, 0, 832182, 433299, 909, 16384⟩ := by
  decide +kernel

theorem context_13_433299_832182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433299 ⟨832182, by decide⟩ :=
  accepted_of_selected 13 433299 ⟨832182, by decide⟩ ⟨13, 2, 0, 832182, 433299, 909, 16384⟩
    (by decide) selected_cut_32373

theorem unmarked_context_12_108324_832183 : frontier 9 ⟨832183, by decide⟩
    (prefixCache 12 108324) (prefixPartial 12 108324) = false := by
  decide +kernel

theorem node_context_12_108324_832183 : EJMOriginalGlobalDAGData.nodes 9 ⟨832183, by decide⟩ =
    .split (coordinate 12) (![⟨832082, by decide⟩,⟨832149, by decide⟩,⟨832168, by decide⟩,⟨832182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108324_832183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108324 ⟨832183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108324
    ⟨832183, by decide⟩ (by decide) (![⟨832082, by decide⟩,⟨832149, by decide⟩,⟨832168, by decide⟩,⟨832182, by decide⟩]) unmarked_context_12_108324_832183 node_context_12_108324_832183
  intro a
  fin_cases a
  · exact context_13_433296_832082
  · exact context_13_433297_832149
  · exact context_13_433298_832168
  · exact context_13_433299_832182

theorem selected_cut_32374 : selected 8 ⟨832208, by decide⟩
    (prefixPartial 13 433300) = some ⟨13, 2, 0, 832208, 433300, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_433300_832208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433300 ⟨832208, by decide⟩ :=
  accepted_of_selected 13 433300 ⟨832208, by decide⟩ ⟨13, 2, 0, 832208, 433300, 1437, 16384⟩
    (by decide) selected_cut_32374

theorem selected_cut_32375 : selected 8 ⟨832249, by decide⟩
    (prefixPartial 13 433301) = some ⟨13, 2, 0, 832249, 433301, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_433301_832249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433301 ⟨832249, by decide⟩ :=
  accepted_of_selected 13 433301 ⟨832249, by decide⟩ ⟨13, 2, 0, 832249, 433301, 2349, 16384⟩
    (by decide) selected_cut_32375

theorem selected_cut_32376 : selected 8 ⟨832261, by decide⟩
    (prefixPartial 13 433302) = some ⟨13, 2, 0, 832261, 433302, 905, 16384⟩ := by
  decide +kernel

theorem context_13_433302_832261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433302 ⟨832261, by decide⟩ :=
  accepted_of_selected 13 433302 ⟨832261, by decide⟩ ⟨13, 2, 0, 832261, 433302, 905, 16384⟩
    (by decide) selected_cut_32376

theorem selected_cut_32377 : selected 8 ⟨832273, by decide⟩
    (prefixPartial 13 433303) = some ⟨13, 2, 0, 832273, 433303, 653, 16384⟩ := by
  decide +kernel

theorem context_13_433303_832273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433303 ⟨832273, by decide⟩ :=
  accepted_of_selected 13 433303 ⟨832273, by decide⟩ ⟨13, 2, 0, 832273, 433303, 653, 16384⟩
    (by decide) selected_cut_32377

theorem unmarked_context_12_108325_832274 : frontier 9 ⟨832274, by decide⟩
    (prefixCache 12 108325) (prefixPartial 12 108325) = false := by
  decide +kernel

theorem node_context_12_108325_832274 : EJMOriginalGlobalDAGData.nodes 9 ⟨832274, by decide⟩ =
    .split (coordinate 12) (![⟨832208, by decide⟩,⟨832249, by decide⟩,⟨832261, by decide⟩,⟨832273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108325_832274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108325 ⟨832274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108325
    ⟨832274, by decide⟩ (by decide) (![⟨832208, by decide⟩,⟨832249, by decide⟩,⟨832261, by decide⟩,⟨832273, by decide⟩]) unmarked_context_12_108325_832274 node_context_12_108325_832274
  intro a
  fin_cases a
  · exact context_13_433300_832208
  · exact context_13_433301_832249
  · exact context_13_433302_832261
  · exact context_13_433303_832273

theorem selected_cut_32378 : selected 8 ⟨832302, by decide⟩
    (prefixPartial 13 433304) = some ⟨13, 2, 0, 832302, 433304, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_433304_832302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433304 ⟨832302, by decide⟩ :=
  accepted_of_selected 13 433304 ⟨832302, by decide⟩ ⟨13, 2, 0, 832302, 433304, 1365, 16384⟩
    (by decide) selected_cut_32378

theorem selected_cut_32379 : selected 8 ⟨832352, by decide⟩
    (prefixPartial 13 433305) = some ⟨13, 2, 0, 832352, 433305, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_433305_832352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433305 ⟨832352, by decide⟩ :=
  accepted_of_selected 13 433305 ⟨832352, by decide⟩ ⟨13, 2, 0, 832352, 433305, 2405, 16384⟩
    (by decide) selected_cut_32379

theorem selected_cut_32380 : selected 8 ⟨832367, by decide⟩
    (prefixPartial 13 433306) = some ⟨13, 2, 0, 832367, 433306, 853, 16384⟩ := by
  decide +kernel

theorem context_13_433306_832367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433306 ⟨832367, by decide⟩ :=
  accepted_of_selected 13 433306 ⟨832367, by decide⟩ ⟨13, 2, 0, 832367, 433306, 853, 16384⟩
    (by decide) selected_cut_32380

theorem selected_cut_32381 : selected 8 ⟨832383, by decide⟩
    (prefixPartial 13 433307) = some ⟨13, 2, 0, 832383, 433307, 853, 16384⟩ := by
  decide +kernel

theorem context_13_433307_832383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433307 ⟨832383, by decide⟩ :=
  accepted_of_selected 13 433307 ⟨832383, by decide⟩ ⟨13, 2, 0, 832383, 433307, 853, 16384⟩
    (by decide) selected_cut_32381

theorem unmarked_context_12_108326_832384 : frontier 9 ⟨832384, by decide⟩
    (prefixCache 12 108326) (prefixPartial 12 108326) = false := by
  decide +kernel

theorem node_context_12_108326_832384 : EJMOriginalGlobalDAGData.nodes 9 ⟨832384, by decide⟩ =
    .split (coordinate 12) (![⟨832302, by decide⟩,⟨832352, by decide⟩,⟨832367, by decide⟩,⟨832383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108326_832384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108326 ⟨832384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108326
    ⟨832384, by decide⟩ (by decide) (![⟨832302, by decide⟩,⟨832352, by decide⟩,⟨832367, by decide⟩,⟨832383, by decide⟩]) unmarked_context_12_108326_832384 node_context_12_108326_832384
  intro a
  fin_cases a
  · exact context_13_433304_832302
  · exact context_13_433305_832352
  · exact context_13_433306_832367
  · exact context_13_433307_832383

theorem selected_cut_32382 : selected 8 ⟨832406, by decide⟩
    (prefixPartial 13 433308) = some ⟨13, 2, 0, 832406, 433308, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_433308_832406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433308 ⟨832406, by decide⟩ :=
  accepted_of_selected 13 433308 ⟨832406, by decide⟩ ⟨13, 2, 0, 832406, 433308, 1389, 16384⟩
    (by decide) selected_cut_32382

theorem selected_cut_32383 : selected 8 ⟨832451, by decide⟩
    (prefixPartial 13 433309) = some ⟨13, 2, 0, 832451, 433309, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_433309_832451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433309 ⟨832451, by decide⟩ :=
  accepted_of_selected 13 433309 ⟨832451, by decide⟩ ⟨13, 2, 0, 832451, 433309, 2381, 16384⟩
    (by decide) selected_cut_32383

theorem selected_cut_32384 : selected 8 ⟨832473, by decide⟩
    (prefixPartial 13 433310) = some ⟨13, 2, 0, 832473, 433310, 989, 16384⟩ := by
  decide +kernel

theorem context_13_433310_832473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433310 ⟨832473, by decide⟩ :=
  accepted_of_selected 13 433310 ⟨832473, by decide⟩ ⟨13, 2, 0, 832473, 433310, 989, 16384⟩
    (by decide) selected_cut_32384

theorem selected_cut_32385 : selected 8 ⟨832476, by decide⟩
    (prefixPartial 13 433311) = some ⟨13, 2, 0, 832476, 433311, 657, 16384⟩ := by
  decide +kernel

theorem context_13_433311_832476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433311 ⟨832476, by decide⟩ :=
  accepted_of_selected 13 433311 ⟨832476, by decide⟩ ⟨13, 2, 0, 832476, 433311, 657, 16384⟩
    (by decide) selected_cut_32385

theorem unmarked_context_12_108327_832477 : frontier 9 ⟨832477, by decide⟩
    (prefixCache 12 108327) (prefixPartial 12 108327) = false := by
  decide +kernel

theorem node_context_12_108327_832477 : EJMOriginalGlobalDAGData.nodes 9 ⟨832477, by decide⟩ =
    .split (coordinate 12) (![⟨832406, by decide⟩,⟨832451, by decide⟩,⟨832473, by decide⟩,⟨832476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108327_832477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108327 ⟨832477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108327
    ⟨832477, by decide⟩ (by decide) (![⟨832406, by decide⟩,⟨832451, by decide⟩,⟨832473, by decide⟩,⟨832476, by decide⟩]) unmarked_context_12_108327_832477 node_context_12_108327_832477
  intro a
  fin_cases a
  · exact context_13_433308_832406
  · exact context_13_433309_832451
  · exact context_13_433310_832473
  · exact context_13_433311_832476

theorem unmarked_context_11_27081_832478 : frontier 10 ⟨832478, by decide⟩
    (prefixCache 11 27081) (prefixPartial 11 27081) = false := by
  decide +kernel

theorem node_context_11_27081_832478 : EJMOriginalGlobalDAGData.nodes 10 ⟨832478, by decide⟩ =
    .split (coordinate 11) (![⟨832183, by decide⟩,⟨832274, by decide⟩,⟨832384, by decide⟩,⟨832477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27081_832478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27081 ⟨832478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27081
    ⟨832478, by decide⟩ (by decide) (![⟨832183, by decide⟩,⟨832274, by decide⟩,⟨832384, by decide⟩,⟨832477, by decide⟩]) unmarked_context_11_27081_832478 node_context_11_27081_832478
  intro a
  fin_cases a
  · exact context_12_108324_832183
  · exact context_12_108325_832274
  · exact context_12_108326_832384
  · exact context_12_108327_832477

theorem selected_cut_32386 : selected 8 ⟨832492, by decide⟩
    (prefixPartial 13 433312) = some ⟨13, 2, 0, 832492, 433312, 953, 16384⟩ := by
  decide +kernel

theorem context_13_433312_832492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433312 ⟨832492, by decide⟩ :=
  accepted_of_selected 13 433312 ⟨832492, by decide⟩ ⟨13, 2, 0, 832492, 433312, 953, 16384⟩
    (by decide) selected_cut_32386

theorem selected_cut_32387 : selected 8 ⟨832528, by decide⟩
    (prefixPartial 13 433313) = some ⟨13, 2, 0, 832528, 433313, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_433313_832528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433313 ⟨832528, by decide⟩ :=
  accepted_of_selected 13 433313 ⟨832528, by decide⟩ ⟨13, 2, 0, 832528, 433313, 2109, 16384⟩
    (by decide) selected_cut_32387

theorem selected_cut_32388 : selected 8 ⟨832551, by decide⟩
    (prefixPartial 13 433314) = some ⟨13, 2, 0, 832551, 433314, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_433314_832551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433314 ⟨832551, by decide⟩ :=
  accepted_of_selected 13 433314 ⟨832551, by decide⟩ ⟨13, 2, 0, 832551, 433314, 1013, 16384⟩
    (by decide) selected_cut_32388

theorem selected_cut_32389 : selected 8 ⟨832558, by decide⟩
    (prefixPartial 13 433315) = some ⟨13, 2, 0, 832558, 433315, 881, 16384⟩ := by
  decide +kernel

theorem context_13_433315_832558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433315 ⟨832558, by decide⟩ :=
  accepted_of_selected 13 433315 ⟨832558, by decide⟩ ⟨13, 2, 0, 832558, 433315, 881, 16384⟩
    (by decide) selected_cut_32389

theorem unmarked_context_12_108328_832559 : frontier 9 ⟨832559, by decide⟩
    (prefixCache 12 108328) (prefixPartial 12 108328) = false := by
  decide +kernel

theorem node_context_12_108328_832559 : EJMOriginalGlobalDAGData.nodes 9 ⟨832559, by decide⟩ =
    .split (coordinate 12) (![⟨832492, by decide⟩,⟨832528, by decide⟩,⟨832551, by decide⟩,⟨832558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108328_832559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108328 ⟨832559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108328
    ⟨832559, by decide⟩ (by decide) (![⟨832492, by decide⟩,⟨832528, by decide⟩,⟨832551, by decide⟩,⟨832558, by decide⟩]) unmarked_context_12_108328_832559 node_context_12_108328_832559
  intro a
  fin_cases a
  · exact context_13_433312_832492
  · exact context_13_433313_832528
  · exact context_13_433314_832551
  · exact context_13_433315_832558

theorem selected_cut_32390 : selected 8 ⟨832574, by decide⟩
    (prefixPartial 13 433316) = some ⟨13, 2, 0, 832574, 433316, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_433316_832574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433316 ⟨832574, by decide⟩ :=
  accepted_of_selected 13 433316 ⟨832574, by decide⟩ ⟨13, 2, 0, 832574, 433316, 1101, 16384⟩
    (by decide) selected_cut_32390

theorem selected_cut_32391 : selected 8 ⟨832606, by decide⟩
    (prefixPartial 13 433317) = some ⟨13, 2, 0, 832606, 433317, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_433317_832606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433317 ⟨832606, by decide⟩ :=
  accepted_of_selected 13 433317 ⟨832606, by decide⟩ ⟨13, 2, 0, 832606, 433317, 1813, 16384⟩
    (by decide) selected_cut_32391

theorem selected_cut_32392 : selected 8 ⟨832623, by decide⟩
    (prefixPartial 13 433318) = some ⟨13, 2, 0, 832623, 433318, 977, 16384⟩ := by
  decide +kernel

theorem context_13_433318_832623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433318 ⟨832623, by decide⟩ :=
  accepted_of_selected 13 433318 ⟨832623, by decide⟩ ⟨13, 2, 0, 832623, 433318, 977, 16384⟩
    (by decide) selected_cut_32392

theorem selected_cut_32393 : selected 8 ⟨832629, by decide⟩
    (prefixPartial 13 433319) = some ⟨13, 2, 0, 832629, 433319, 757, 16384⟩ := by
  decide +kernel

theorem context_13_433319_832629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433319 ⟨832629, by decide⟩ :=
  accepted_of_selected 13 433319 ⟨832629, by decide⟩ ⟨13, 2, 0, 832629, 433319, 757, 16384⟩
    (by decide) selected_cut_32393

theorem unmarked_context_12_108329_832630 : frontier 9 ⟨832630, by decide⟩
    (prefixCache 12 108329) (prefixPartial 12 108329) = false := by
  decide +kernel

theorem node_context_12_108329_832630 : EJMOriginalGlobalDAGData.nodes 9 ⟨832630, by decide⟩ =
    .split (coordinate 12) (![⟨832574, by decide⟩,⟨832606, by decide⟩,⟨832623, by decide⟩,⟨832629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108329_832630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108329 ⟨832630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108329
    ⟨832630, by decide⟩ (by decide) (![⟨832574, by decide⟩,⟨832606, by decide⟩,⟨832623, by decide⟩,⟨832629, by decide⟩]) unmarked_context_12_108329_832630 node_context_12_108329_832630
  intro a
  fin_cases a
  · exact context_13_433316_832574
  · exact context_13_433317_832606
  · exact context_13_433318_832623
  · exact context_13_433319_832629

theorem selected_cut_32394 : selected 8 ⟨832643, by decide⟩
    (prefixPartial 13 433320) = some ⟨13, 2, 0, 832643, 433320, 913, 16384⟩ := by
  decide +kernel

theorem context_13_433320_832643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433320 ⟨832643, by decide⟩ :=
  accepted_of_selected 13 433320 ⟨832643, by decide⟩ ⟨13, 2, 0, 832643, 433320, 913, 16384⟩
    (by decide) selected_cut_32394

theorem selected_cut_32395 : selected 8 ⟨832675, by decide⟩
    (prefixPartial 13 433321) = some ⟨13, 2, 0, 832675, 433321, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_433321_832675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433321 ⟨832675, by decide⟩ :=
  accepted_of_selected 13 433321 ⟨832675, by decide⟩ ⟨13, 2, 0, 832675, 433321, 1709, 16384⟩
    (by decide) selected_cut_32395

theorem selected_cut_32396 : selected 8 ⟨832688, by decide⟩
    (prefixPartial 13 433322) = some ⟨13, 2, 0, 832688, 433322, 885, 16384⟩ := by
  decide +kernel

theorem context_13_433322_832688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433322 ⟨832688, by decide⟩ :=
  accepted_of_selected 13 433322 ⟨832688, by decide⟩ ⟨13, 2, 0, 832688, 433322, 885, 16384⟩
    (by decide) selected_cut_32396

theorem selected_cut_32397 : selected 8 ⟨832698, by decide⟩
    (prefixPartial 13 433323) = some ⟨13, 2, 0, 832698, 433323, 797, 16384⟩ := by
  decide +kernel

theorem context_13_433323_832698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433323 ⟨832698, by decide⟩ :=
  accepted_of_selected 13 433323 ⟨832698, by decide⟩ ⟨13, 2, 0, 832698, 433323, 797, 16384⟩
    (by decide) selected_cut_32397

theorem unmarked_context_12_108330_832699 : frontier 9 ⟨832699, by decide⟩
    (prefixCache 12 108330) (prefixPartial 12 108330) = false := by
  decide +kernel

theorem node_context_12_108330_832699 : EJMOriginalGlobalDAGData.nodes 9 ⟨832699, by decide⟩ =
    .split (coordinate 12) (![⟨832643, by decide⟩,⟨832675, by decide⟩,⟨832688, by decide⟩,⟨832698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108330_832699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108330 ⟨832699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108330
    ⟨832699, by decide⟩ (by decide) (![⟨832643, by decide⟩,⟨832675, by decide⟩,⟨832688, by decide⟩,⟨832698, by decide⟩]) unmarked_context_12_108330_832699 node_context_12_108330_832699
  intro a
  fin_cases a
  · exact context_13_433320_832643
  · exact context_13_433321_832675
  · exact context_13_433322_832688
  · exact context_13_433323_832698

theorem selected_cut_32398 : selected 8 ⟨832712, by decide⟩
    (prefixPartial 13 433324) = some ⟨13, 2, 0, 832712, 433324, 917, 16384⟩ := by
  decide +kernel

theorem context_13_433324_832712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433324 ⟨832712, by decide⟩ :=
  accepted_of_selected 13 433324 ⟨832712, by decide⟩ ⟨13, 2, 0, 832712, 433324, 917, 16384⟩
    (by decide) selected_cut_32398

theorem selected_cut_32399 : selected 8 ⟨832740, by decide⟩
    (prefixPartial 13 433325) = some ⟨13, 2, 0, 832740, 433325, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_433325_832740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433325 ⟨832740, by decide⟩ :=
  accepted_of_selected 13 433325 ⟨832740, by decide⟩ ⟨13, 2, 0, 832740, 433325, 1929, 16384⟩
    (by decide) selected_cut_32399

theorem selected_cut_32400 : selected 8 ⟨832754, by decide⟩
    (prefixPartial 13 433326) = some ⟨13, 2, 0, 832754, 433326, 993, 16384⟩ := by
  decide +kernel

theorem context_13_433326_832754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433326 ⟨832754, by decide⟩ :=
  accepted_of_selected 13 433326 ⟨832754, by decide⟩ ⟨13, 2, 0, 832754, 433326, 993, 16384⟩
    (by decide) selected_cut_32400

theorem selected_cut_32401 : selected 8 ⟨832761, by decide⟩
    (prefixPartial 13 433327) = some ⟨13, 2, 0, 832761, 433327, 709, 16384⟩ := by
  decide +kernel

theorem context_13_433327_832761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433327 ⟨832761, by decide⟩ :=
  accepted_of_selected 13 433327 ⟨832761, by decide⟩ ⟨13, 2, 0, 832761, 433327, 709, 16384⟩
    (by decide) selected_cut_32401

theorem unmarked_context_12_108331_832762 : frontier 9 ⟨832762, by decide⟩
    (prefixCache 12 108331) (prefixPartial 12 108331) = false := by
  decide +kernel

theorem node_context_12_108331_832762 : EJMOriginalGlobalDAGData.nodes 9 ⟨832762, by decide⟩ =
    .split (coordinate 12) (![⟨832712, by decide⟩,⟨832740, by decide⟩,⟨832754, by decide⟩,⟨832761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108331_832762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108331 ⟨832762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108331
    ⟨832762, by decide⟩ (by decide) (![⟨832712, by decide⟩,⟨832740, by decide⟩,⟨832754, by decide⟩,⟨832761, by decide⟩]) unmarked_context_12_108331_832762 node_context_12_108331_832762
  intro a
  fin_cases a
  · exact context_13_433324_832712
  · exact context_13_433325_832740
  · exact context_13_433326_832754
  · exact context_13_433327_832761

theorem unmarked_context_11_27082_832763 : frontier 10 ⟨832763, by decide⟩
    (prefixCache 11 27082) (prefixPartial 11 27082) = false := by
  decide +kernel

theorem node_context_11_27082_832763 : EJMOriginalGlobalDAGData.nodes 10 ⟨832763, by decide⟩ =
    .split (coordinate 11) (![⟨832559, by decide⟩,⟨832630, by decide⟩,⟨832699, by decide⟩,⟨832762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27082_832763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27082 ⟨832763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27082
    ⟨832763, by decide⟩ (by decide) (![⟨832559, by decide⟩,⟨832630, by decide⟩,⟨832699, by decide⟩,⟨832762, by decide⟩]) unmarked_context_11_27082_832763 node_context_11_27082_832763
  intro a
  fin_cases a
  · exact context_12_108328_832559
  · exact context_12_108329_832630
  · exact context_12_108330_832699
  · exact context_12_108331_832762

theorem selected_cut_32402 : selected 8 ⟨832773, by decide⟩
    (prefixPartial 13 433328) = some ⟨13, 2, 0, 832773, 433328, 817, 16384⟩ := by
  decide +kernel

theorem context_13_433328_832773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433328 ⟨832773, by decide⟩ :=
  accepted_of_selected 13 433328 ⟨832773, by decide⟩ ⟨13, 2, 0, 832773, 433328, 817, 16384⟩
    (by decide) selected_cut_32402

theorem selected_cut_32403 : selected 8 ⟨832815, by decide⟩
    (prefixPartial 13 433329) = some ⟨13, 2, 0, 832815, 433329, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_433329_832815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433329 ⟨832815, by decide⟩ :=
  accepted_of_selected 13 433329 ⟨832815, by decide⟩ ⟨13, 2, 0, 832815, 433329, 2117, 16384⟩
    (by decide) selected_cut_32403

theorem selected_cut_32404 : selected 8 ⟨832832, by decide⟩
    (prefixPartial 13 433330) = some ⟨13, 2, 0, 832832, 433330, 869, 16384⟩ := by
  decide +kernel

theorem context_13_433330_832832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433330 ⟨832832, by decide⟩ :=
  accepted_of_selected 13 433330 ⟨832832, by decide⟩ ⟨13, 2, 0, 832832, 433330, 869, 16384⟩
    (by decide) selected_cut_32404

theorem selected_cut_32405 : selected 8 ⟨832844, by decide⟩
    (prefixPartial 13 433331) = some ⟨13, 2, 0, 832844, 433331, 773, 16384⟩ := by
  decide +kernel

theorem context_13_433331_832844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433331 ⟨832844, by decide⟩ :=
  accepted_of_selected 13 433331 ⟨832844, by decide⟩ ⟨13, 2, 0, 832844, 433331, 773, 16384⟩
    (by decide) selected_cut_32405

theorem unmarked_context_12_108332_832845 : frontier 9 ⟨832845, by decide⟩
    (prefixCache 12 108332) (prefixPartial 12 108332) = false := by
  decide +kernel

theorem node_context_12_108332_832845 : EJMOriginalGlobalDAGData.nodes 9 ⟨832845, by decide⟩ =
    .split (coordinate 12) (![⟨832773, by decide⟩,⟨832815, by decide⟩,⟨832832, by decide⟩,⟨832844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108332_832845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108332 ⟨832845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108332
    ⟨832845, by decide⟩ (by decide) (![⟨832773, by decide⟩,⟨832815, by decide⟩,⟨832832, by decide⟩,⟨832844, by decide⟩]) unmarked_context_12_108332_832845 node_context_12_108332_832845
  intro a
  fin_cases a
  · exact context_13_433328_832773
  · exact context_13_433329_832815
  · exact context_13_433330_832832
  · exact context_13_433331_832844

theorem selected_cut_32406 : selected 8 ⟨832862, by decide⟩
    (prefixPartial 13 433332) = some ⟨13, 2, 0, 832862, 433332, 933, 16384⟩ := by
  decide +kernel

theorem context_13_433332_832862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433332 ⟨832862, by decide⟩ :=
  accepted_of_selected 13 433332 ⟨832862, by decide⟩ ⟨13, 2, 0, 832862, 433332, 933, 16384⟩
    (by decide) selected_cut_32406

theorem selected_cut_32407 : selected 8 ⟨832893, by decide⟩
    (prefixPartial 13 433333) = some ⟨13, 2, 0, 832893, 433333, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_433333_832893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433333 ⟨832893, by decide⟩ :=
  accepted_of_selected 13 433333 ⟨832893, by decide⟩ ⟨13, 2, 0, 832893, 433333, 1869, 16384⟩
    (by decide) selected_cut_32407

theorem selected_cut_32408 : selected 8 ⟨832916, by decide⟩
    (prefixPartial 13 433334) = some ⟨13, 2, 0, 832916, 433334, 957, 16384⟩ := by
  decide +kernel

theorem context_13_433334_832916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433334 ⟨832916, by decide⟩ :=
  accepted_of_selected 13 433334 ⟨832916, by decide⟩ ⟨13, 2, 0, 832916, 433334, 957, 16384⟩
    (by decide) selected_cut_32408

theorem selected_cut_32409 : selected 8 ⟨832924, by decide⟩
    (prefixPartial 13 433335) = some ⟨13, 2, 0, 832924, 433335, 665, 16384⟩ := by
  decide +kernel

theorem context_13_433335_832924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433335 ⟨832924, by decide⟩ :=
  accepted_of_selected 13 433335 ⟨832924, by decide⟩ ⟨13, 2, 0, 832924, 433335, 665, 16384⟩
    (by decide) selected_cut_32409

theorem unmarked_context_12_108333_832925 : frontier 9 ⟨832925, by decide⟩
    (prefixCache 12 108333) (prefixPartial 12 108333) = false := by
  decide +kernel

theorem node_context_12_108333_832925 : EJMOriginalGlobalDAGData.nodes 9 ⟨832925, by decide⟩ =
    .split (coordinate 12) (![⟨832862, by decide⟩,⟨832893, by decide⟩,⟨832916, by decide⟩,⟨832924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108333_832925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108333 ⟨832925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108333
    ⟨832925, by decide⟩ (by decide) (![⟨832862, by decide⟩,⟨832893, by decide⟩,⟨832916, by decide⟩,⟨832924, by decide⟩]) unmarked_context_12_108333_832925 node_context_12_108333_832925
  intro a
  fin_cases a
  · exact context_13_433332_832862
  · exact context_13_433333_832893
  · exact context_13_433334_832916
  · exact context_13_433335_832924

theorem selected_cut_32410 : selected 8 ⟨832940, by decide⟩
    (prefixPartial 13 433336) = some ⟨13, 2, 0, 832940, 433336, 821, 16384⟩ := by
  decide +kernel

theorem context_13_433336_832940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433336 ⟨832940, by decide⟩ :=
  accepted_of_selected 13 433336 ⟨832940, by decide⟩ ⟨13, 2, 0, 832940, 433336, 821, 16384⟩
    (by decide) selected_cut_32410

theorem selected_cut_32411 : selected 8 ⟨832976, by decide⟩
    (prefixPartial 13 433337) = some ⟨13, 2, 0, 832976, 433337, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_433337_832976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433337 ⟨832976, by decide⟩ :=
  accepted_of_selected 13 433337 ⟨832976, by decide⟩ ⟨13, 2, 0, 832976, 433337, 1853, 16384⟩
    (by decide) selected_cut_32411

theorem selected_cut_32412 : selected 8 ⟨832988, by decide⟩
    (prefixPartial 13 433338) = some ⟨13, 2, 0, 832988, 433338, 805, 16384⟩ := by
  decide +kernel

theorem context_13_433338_832988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433338 ⟨832988, by decide⟩ :=
  accepted_of_selected 13 433338 ⟨832988, by decide⟩ ⟨13, 2, 0, 832988, 433338, 805, 16384⟩
    (by decide) selected_cut_32412

theorem selected_cut_32413 : selected 8 ⟨832999, by decide⟩
    (prefixPartial 13 433339) = some ⟨13, 2, 0, 832999, 433339, 753, 16384⟩ := by
  decide +kernel

theorem context_13_433339_832999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433339 ⟨832999, by decide⟩ :=
  accepted_of_selected 13 433339 ⟨832999, by decide⟩ ⟨13, 2, 0, 832999, 433339, 753, 16384⟩
    (by decide) selected_cut_32413

theorem unmarked_context_12_108334_833000 : frontier 9 ⟨833000, by decide⟩
    (prefixCache 12 108334) (prefixPartial 12 108334) = false := by
  decide +kernel

theorem node_context_12_108334_833000 : EJMOriginalGlobalDAGData.nodes 9 ⟨833000, by decide⟩ =
    .split (coordinate 12) (![⟨832940, by decide⟩,⟨832976, by decide⟩,⟨832988, by decide⟩,⟨832999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108334_833000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108334 ⟨833000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108334
    ⟨833000, by decide⟩ (by decide) (![⟨832940, by decide⟩,⟨832976, by decide⟩,⟨832988, by decide⟩,⟨832999, by decide⟩]) unmarked_context_12_108334_833000 node_context_12_108334_833000
  intro a
  fin_cases a
  · exact context_13_433336_832940
  · exact context_13_433337_832976
  · exact context_13_433338_832988
  · exact context_13_433339_832999

theorem selected_cut_32414 : selected 8 ⟨833029, by decide⟩
    (prefixPartial 13 433340) = some ⟨13, 2, 0, 833029, 433340, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_433340_833029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433340 ⟨833029, by decide⟩ :=
  accepted_of_selected 13 433340 ⟨833029, by decide⟩ ⟨13, 2, 0, 833029, 433340, 1229, 16384⟩
    (by decide) selected_cut_32414

theorem selected_cut_32415 : selected 8 ⟨833118, by decide⟩
    (prefixPartial 13 433341) = some ⟨13, 2, 0, 833118, 433341, 2825, 16384⟩ := by
  decide +kernel

theorem context_13_433341_833118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433341 ⟨833118, by decide⟩ :=
  accepted_of_selected 13 433341 ⟨833118, by decide⟩ ⟨13, 2, 0, 833118, 433341, 2825, 16384⟩
    (by decide) selected_cut_32415

theorem selected_cut_32416 : selected 8 ⟨833179, by decide⟩
    (prefixPartial 13 433342) = some ⟨13, 2, 0, 833179, 433342, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_433342_833179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433342 ⟨833179, by decide⟩ :=
  accepted_of_selected 13 433342 ⟨833179, by decide⟩ ⟨13, 2, 0, 833179, 433342, 1485, 16384⟩
    (by decide) selected_cut_32416

theorem selected_cut_32417 : selected 8 ⟨833195, by decide⟩
    (prefixPartial 13 433343) = some ⟨13, 2, 0, 833195, 433343, 933, 16384⟩ := by
  decide +kernel

theorem context_13_433343_833195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433343 ⟨833195, by decide⟩ :=
  accepted_of_selected 13 433343 ⟨833195, by decide⟩ ⟨13, 2, 0, 833195, 433343, 933, 16384⟩
    (by decide) selected_cut_32417

theorem unmarked_context_12_108335_833196 : frontier 9 ⟨833196, by decide⟩
    (prefixCache 12 108335) (prefixPartial 12 108335) = false := by
  decide +kernel

theorem node_context_12_108335_833196 : EJMOriginalGlobalDAGData.nodes 9 ⟨833196, by decide⟩ =
    .split (coordinate 12) (![⟨833029, by decide⟩,⟨833118, by decide⟩,⟨833179, by decide⟩,⟨833195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108335_833196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108335 ⟨833196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108335
    ⟨833196, by decide⟩ (by decide) (![⟨833029, by decide⟩,⟨833118, by decide⟩,⟨833179, by decide⟩,⟨833195, by decide⟩]) unmarked_context_12_108335_833196 node_context_12_108335_833196
  intro a
  fin_cases a
  · exact context_13_433340_833029
  · exact context_13_433341_833118
  · exact context_13_433342_833179
  · exact context_13_433343_833195

theorem unmarked_context_11_27083_833197 : frontier 10 ⟨833197, by decide⟩
    (prefixCache 11 27083) (prefixPartial 11 27083) = false := by
  decide +kernel

theorem node_context_11_27083_833197 : EJMOriginalGlobalDAGData.nodes 10 ⟨833197, by decide⟩ =
    .split (coordinate 11) (![⟨832845, by decide⟩,⟨832925, by decide⟩,⟨833000, by decide⟩,⟨833196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27083_833197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27083 ⟨833197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27083
    ⟨833197, by decide⟩ (by decide) (![⟨832845, by decide⟩,⟨832925, by decide⟩,⟨833000, by decide⟩,⟨833196, by decide⟩]) unmarked_context_11_27083_833197 node_context_11_27083_833197
  intro a
  fin_cases a
  · exact context_12_108332_832845
  · exact context_12_108333_832925
  · exact context_12_108334_833000
  · exact context_12_108335_833196

theorem unmarked_context_10_6770_833198 : frontier 11 ⟨833198, by decide⟩
    (prefixCache 10 6770) (prefixPartial 10 6770) = false := by
  decide +kernel

theorem node_context_10_6770_833198 : EJMOriginalGlobalDAGData.nodes 11 ⟨833198, by decide⟩ =
    .split (coordinate 10) (![⟨832060, by decide⟩,⟨832478, by decide⟩,⟨832763, by decide⟩,⟨833197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6770_833198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6770 ⟨833198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6770
    ⟨833198, by decide⟩ (by decide) (![⟨832060, by decide⟩,⟨832478, by decide⟩,⟨832763, by decide⟩,⟨833197, by decide⟩]) unmarked_context_10_6770_833198 node_context_10_6770_833198
  intro a
  fin_cases a
  · exact context_11_27080_832060
  · exact context_11_27081_832478
  · exact context_11_27082_832763
  · exact context_11_27083_833197

theorem selected_cut_32418 : selected 8 ⟨833211, by decide⟩
    (prefixPartial 13 433344) = some ⟨13, 2, 0, 833211, 433344, 577, 16384⟩ := by
  decide +kernel

theorem context_13_433344_833211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433344 ⟨833211, by decide⟩ :=
  accepted_of_selected 13 433344 ⟨833211, by decide⟩ ⟨13, 2, 0, 833211, 433344, 577, 16384⟩
    (by decide) selected_cut_32418

theorem selected_cut_32419 : selected 8 ⟨833249, by decide⟩
    (prefixPartial 13 433345) = some ⟨13, 2, 0, 833249, 433345, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_433345_833249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433345 ⟨833249, by decide⟩ :=
  accepted_of_selected 13 433345 ⟨833249, by decide⟩ ⟨13, 2, 0, 833249, 433345, 1981, 16384⟩
    (by decide) selected_cut_32419

theorem selected_cut_32420 : selected 8 ⟨833275, by decide⟩
    (prefixPartial 13 433346) = some ⟨13, 2, 0, 833275, 433346, 969, 16384⟩ := by
  decide +kernel

theorem context_13_433346_833275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433346 ⟨833275, by decide⟩ :=
  accepted_of_selected 13 433346 ⟨833275, by decide⟩ ⟨13, 2, 0, 833275, 433346, 969, 16384⟩
    (by decide) selected_cut_32420

theorem selected_cut_32421 : selected 8 ⟨833285, by decide⟩
    (prefixPartial 13 433347) = some ⟨13, 2, 0, 833285, 433347, 873, 16384⟩ := by
  decide +kernel

theorem context_13_433347_833285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433347 ⟨833285, by decide⟩ :=
  accepted_of_selected 13 433347 ⟨833285, by decide⟩ ⟨13, 2, 0, 833285, 433347, 873, 16384⟩
    (by decide) selected_cut_32421

theorem unmarked_context_12_108336_833286 : frontier 9 ⟨833286, by decide⟩
    (prefixCache 12 108336) (prefixPartial 12 108336) = false := by
  decide +kernel

theorem node_context_12_108336_833286 : EJMOriginalGlobalDAGData.nodes 9 ⟨833286, by decide⟩ =
    .split (coordinate 12) (![⟨833211, by decide⟩,⟨833249, by decide⟩,⟨833275, by decide⟩,⟨833285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108336_833286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108336 ⟨833286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108336
    ⟨833286, by decide⟩ (by decide) (![⟨833211, by decide⟩,⟨833249, by decide⟩,⟨833275, by decide⟩,⟨833285, by decide⟩]) unmarked_context_12_108336_833286 node_context_12_108336_833286
  intro a
  fin_cases a
  · exact context_13_433344_833211
  · exact context_13_433345_833249
  · exact context_13_433346_833275
  · exact context_13_433347_833285

theorem selected_cut_32422 : selected 8 ⟨833300, by decide⟩
    (prefixPartial 13 433348) = some ⟨13, 2, 0, 833300, 433348, 629, 16384⟩ := by
  decide +kernel

theorem context_13_433348_833300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433348 ⟨833300, by decide⟩ :=
  accepted_of_selected 13 433348 ⟨833300, by decide⟩ ⟨13, 2, 0, 833300, 433348, 629, 16384⟩
    (by decide) selected_cut_32422

theorem selected_cut_32423 : selected 8 ⟨833347, by decide⟩
    (prefixPartial 13 433349) = some ⟨13, 2, 0, 833347, 433349, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_433349_833347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433349 ⟨833347, by decide⟩ :=
  accepted_of_selected 13 433349 ⟨833347, by decide⟩ ⟨13, 2, 0, 833347, 433349, 2013, 16384⟩
    (by decide) selected_cut_32423

theorem selected_cut_32424 : selected 8 ⟨833364, by decide⟩
    (prefixPartial 13 433350) = some ⟨13, 2, 0, 833364, 433350, 905, 16384⟩ := by
  decide +kernel

theorem context_13_433350_833364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433350 ⟨833364, by decide⟩ :=
  accepted_of_selected 13 433350 ⟨833364, by decide⟩ ⟨13, 2, 0, 833364, 433350, 905, 16384⟩
    (by decide) selected_cut_32424

theorem selected_cut_32425 : selected 8 ⟨833370, by decide⟩
    (prefixPartial 13 433351) = some ⟨13, 2, 0, 833370, 433351, 709, 16384⟩ := by
  decide +kernel

theorem context_13_433351_833370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433351 ⟨833370, by decide⟩ :=
  accepted_of_selected 13 433351 ⟨833370, by decide⟩ ⟨13, 2, 0, 833370, 433351, 709, 16384⟩
    (by decide) selected_cut_32425

theorem unmarked_context_12_108337_833371 : frontier 9 ⟨833371, by decide⟩
    (prefixCache 12 108337) (prefixPartial 12 108337) = false := by
  decide +kernel

theorem node_context_12_108337_833371 : EJMOriginalGlobalDAGData.nodes 9 ⟨833371, by decide⟩ =
    .split (coordinate 12) (![⟨833300, by decide⟩,⟨833347, by decide⟩,⟨833364, by decide⟩,⟨833370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108337_833371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108337 ⟨833371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108337
    ⟨833371, by decide⟩ (by decide) (![⟨833300, by decide⟩,⟨833347, by decide⟩,⟨833364, by decide⟩,⟨833370, by decide⟩]) unmarked_context_12_108337_833371 node_context_12_108337_833371
  intro a
  fin_cases a
  · exact context_13_433348_833300
  · exact context_13_433349_833347
  · exact context_13_433350_833364
  · exact context_13_433351_833370

theorem selected_cut_32426 : selected 8 ⟨833382, by decide⟩
    (prefixPartial 13 433352) = some ⟨13, 2, 0, 833382, 433352, 525, 16384⟩ := by
  decide +kernel

theorem context_13_433352_833382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433352 ⟨833382, by decide⟩ :=
  accepted_of_selected 13 433352 ⟨833382, by decide⟩ ⟨13, 2, 0, 833382, 433352, 525, 16384⟩
    (by decide) selected_cut_32426

theorem selected_cut_32427 : selected 8 ⟨833419, by decide⟩
    (prefixPartial 13 433353) = some ⟨13, 2, 0, 833419, 433353, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_433353_833419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433353 ⟨833419, by decide⟩ :=
  accepted_of_selected 13 433353 ⟨833419, by decide⟩ ⟨13, 2, 0, 833419, 433353, 2021, 16384⟩
    (by decide) selected_cut_32427

theorem selected_cut_32428 : selected 8 ⟨833436, by decide⟩
    (prefixPartial 13 433354) = some ⟨13, 2, 0, 833436, 433354, 845, 16384⟩ := by
  decide +kernel

theorem context_13_433354_833436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433354 ⟨833436, by decide⟩ :=
  accepted_of_selected 13 433354 ⟨833436, by decide⟩ ⟨13, 2, 0, 833436, 433354, 845, 16384⟩
    (by decide) selected_cut_32428

theorem selected_cut_32429 : selected 8 ⟨833444, by decide⟩
    (prefixPartial 13 433355) = some ⟨13, 2, 0, 833444, 433355, 741, 16384⟩ := by
  decide +kernel

theorem context_13_433355_833444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433355 ⟨833444, by decide⟩ :=
  accepted_of_selected 13 433355 ⟨833444, by decide⟩ ⟨13, 2, 0, 833444, 433355, 741, 16384⟩
    (by decide) selected_cut_32429

theorem unmarked_context_12_108338_833445 : frontier 9 ⟨833445, by decide⟩
    (prefixCache 12 108338) (prefixPartial 12 108338) = false := by
  decide +kernel

theorem node_context_12_108338_833445 : EJMOriginalGlobalDAGData.nodes 9 ⟨833445, by decide⟩ =
    .split (coordinate 12) (![⟨833382, by decide⟩,⟨833419, by decide⟩,⟨833436, by decide⟩,⟨833444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108338_833445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108338 ⟨833445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108338
    ⟨833445, by decide⟩ (by decide) (![⟨833382, by decide⟩,⟨833419, by decide⟩,⟨833436, by decide⟩,⟨833444, by decide⟩]) unmarked_context_12_108338_833445 node_context_12_108338_833445
  intro a
  fin_cases a
  · exact context_13_433352_833382
  · exact context_13_433353_833419
  · exact context_13_433354_833436
  · exact context_13_433355_833444

theorem selected_cut_32430 : selected 8 ⟨833455, by decide⟩
    (prefixPartial 13 433356) = some ⟨13, 2, 0, 833455, 433356, 541, 16384⟩ := by
  decide +kernel

theorem context_13_433356_833455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433356 ⟨833455, by decide⟩ :=
  accepted_of_selected 13 433356 ⟨833455, by decide⟩ ⟨13, 2, 0, 833455, 433356, 541, 16384⟩
    (by decide) selected_cut_32430

theorem selected_cut_32431 : selected 8 ⟨833496, by decide⟩
    (prefixPartial 13 433357) = some ⟨13, 2, 0, 833496, 433357, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_433357_833496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433357 ⟨833496, by decide⟩ :=
  accepted_of_selected 13 433357 ⟨833496, by decide⟩ ⟨13, 2, 0, 833496, 433357, 2041, 16384⟩
    (by decide) selected_cut_32431

theorem selected_cut_32432 : selected 8 ⟨833516, by decide⟩
    (prefixPartial 13 433358) = some ⟨13, 2, 0, 833516, 433358, 981, 16384⟩ := by
  decide +kernel

theorem context_13_433358_833516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433358 ⟨833516, by decide⟩ :=
  accepted_of_selected 13 433358 ⟨833516, by decide⟩ ⟨13, 2, 0, 833516, 433358, 981, 16384⟩
    (by decide) selected_cut_32432

theorem selected_cut_32433 : selected 8 ⟨833527, by decide⟩
    (prefixPartial 13 433359) = some ⟨13, 2, 0, 833527, 433359, 673, 16384⟩ := by
  decide +kernel

theorem context_13_433359_833527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 433359 ⟨833527, by decide⟩ :=
  accepted_of_selected 13 433359 ⟨833527, by decide⟩ ⟨13, 2, 0, 833527, 433359, 673, 16384⟩
    (by decide) selected_cut_32433

theorem unmarked_context_12_108339_833528 : frontier 9 ⟨833528, by decide⟩
    (prefixCache 12 108339) (prefixPartial 12 108339) = false := by
  decide +kernel

theorem node_context_12_108339_833528 : EJMOriginalGlobalDAGData.nodes 9 ⟨833528, by decide⟩ =
    .split (coordinate 12) (![⟨833455, by decide⟩,⟨833496, by decide⟩,⟨833516, by decide⟩,⟨833527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_108339_833528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108339 ⟨833528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 108339
    ⟨833528, by decide⟩ (by decide) (![⟨833455, by decide⟩,⟨833496, by decide⟩,⟨833516, by decide⟩,⟨833527, by decide⟩]) unmarked_context_12_108339_833528 node_context_12_108339_833528
  intro a
  fin_cases a
  · exact context_13_433356_833455
  · exact context_13_433357_833496
  · exact context_13_433358_833516
  · exact context_13_433359_833527

theorem unmarked_context_11_27084_833529 : frontier 10 ⟨833529, by decide⟩
    (prefixCache 11 27084) (prefixPartial 11 27084) = false := by
  decide +kernel

theorem node_context_11_27084_833529 : EJMOriginalGlobalDAGData.nodes 10 ⟨833529, by decide⟩ =
    .split (coordinate 11) (![⟨833286, by decide⟩,⟨833371, by decide⟩,⟨833445, by decide⟩,⟨833528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27084_833529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27084 ⟨833529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27084
    ⟨833529, by decide⟩ (by decide) (![⟨833286, by decide⟩,⟨833371, by decide⟩,⟨833445, by decide⟩,⟨833528, by decide⟩]) unmarked_context_11_27084_833529 node_context_11_27084_833529
  intro a
  fin_cases a
  · exact context_12_108336_833286
  · exact context_12_108337_833371
  · exact context_12_108338_833445
  · exact context_12_108339_833528

theorem selected_cut_32434 : selected 9 ⟨833628, by decide⟩
    (prefixPartial 12 108340) = some ⟨12, 2, 0, 833628, 108340, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_108340_833628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108340 ⟨833628, by decide⟩ :=
  accepted_of_selected 12 108340 ⟨833628, by decide⟩ ⟨12, 2, 0, 833628, 108340, 4089, 65536⟩
    (by decide) selected_cut_32434

theorem selected_cut_32435 : selected 9 ⟨833700, by decide⟩
    (prefixPartial 12 108341) = some ⟨12, 2, 0, 833700, 108341, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_108341_833700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108341 ⟨833700, by decide⟩ :=
  accepted_of_selected 12 108341 ⟨833700, by decide⟩ ⟨12, 2, 0, 833700, 108341, 3497, 65536⟩
    (by decide) selected_cut_32435

theorem selected_cut_32436 : selected 9 ⟨833760, by decide⟩
    (prefixPartial 12 108342) = some ⟨12, 2, 0, 833760, 108342, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_108342_833760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108342 ⟨833760, by decide⟩ :=
  accepted_of_selected 12 108342 ⟨833760, by decide⟩ ⟨12, 2, 0, 833760, 108342, 3589, 65536⟩
    (by decide) selected_cut_32436

theorem selected_cut_32437 : selected 9 ⟨833823, by decide⟩
    (prefixPartial 12 108343) = some ⟨12, 2, 0, 833823, 108343, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_108343_833823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108343 ⟨833823, by decide⟩ :=
  accepted_of_selected 12 108343 ⟨833823, by decide⟩ ⟨12, 2, 0, 833823, 108343, 3757, 65536⟩
    (by decide) selected_cut_32437

theorem unmarked_context_11_27085_833824 : frontier 10 ⟨833824, by decide⟩
    (prefixCache 11 27085) (prefixPartial 11 27085) = false := by
  decide +kernel

theorem node_context_11_27085_833824 : EJMOriginalGlobalDAGData.nodes 10 ⟨833824, by decide⟩ =
    .split (coordinate 11) (![⟨833628, by decide⟩,⟨833700, by decide⟩,⟨833760, by decide⟩,⟨833823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27085_833824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27085 ⟨833824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27085
    ⟨833824, by decide⟩ (by decide) (![⟨833628, by decide⟩,⟨833700, by decide⟩,⟨833760, by decide⟩,⟨833823, by decide⟩]) unmarked_context_11_27085_833824 node_context_11_27085_833824
  intro a
  fin_cases a
  · exact context_12_108340_833628
  · exact context_12_108341_833700
  · exact context_12_108342_833760
  · exact context_12_108343_833823

theorem selected_cut_32438 : selected 9 ⟨833915, by decide⟩
    (prefixPartial 12 108344) = some ⟨12, 2, 0, 833915, 108344, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_108344_833915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108344 ⟨833915, by decide⟩ :=
  accepted_of_selected 12 108344 ⟨833915, by decide⟩ ⟨12, 2, 0, 833915, 108344, 4033, 65536⟩
    (by decide) selected_cut_32438

theorem selected_cut_32439 : selected 9 ⟨833991, by decide⟩
    (prefixPartial 12 108345) = some ⟨12, 2, 0, 833991, 108345, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_108345_833991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108345 ⟨833991, by decide⟩ :=
  accepted_of_selected 12 108345 ⟨833991, by decide⟩ ⟨12, 2, 0, 833991, 108345, 3673, 65536⟩
    (by decide) selected_cut_32439

theorem selected_cut_32440 : selected 9 ⟨834044, by decide⟩
    (prefixPartial 12 108346) = some ⟨12, 2, 0, 834044, 108346, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_108346_834044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108346 ⟨834044, by decide⟩ :=
  accepted_of_selected 12 108346 ⟨834044, by decide⟩ ⟨12, 2, 0, 834044, 108346, 3421, 65536⟩
    (by decide) selected_cut_32440

theorem selected_cut_32441 : selected 9 ⟨834097, by decide⟩
    (prefixPartial 12 108347) = some ⟨12, 2, 0, 834097, 108347, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_108347_834097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108347 ⟨834097, by decide⟩ :=
  accepted_of_selected 12 108347 ⟨834097, by decide⟩ ⟨12, 2, 0, 834097, 108347, 3649, 65536⟩
    (by decide) selected_cut_32441

theorem unmarked_context_11_27086_834098 : frontier 10 ⟨834098, by decide⟩
    (prefixCache 11 27086) (prefixPartial 11 27086) = false := by
  decide +kernel

theorem node_context_11_27086_834098 : EJMOriginalGlobalDAGData.nodes 10 ⟨834098, by decide⟩ =
    .split (coordinate 11) (![⟨833915, by decide⟩,⟨833991, by decide⟩,⟨834044, by decide⟩,⟨834097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27086_834098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27086 ⟨834098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27086
    ⟨834098, by decide⟩ (by decide) (![⟨833915, by decide⟩,⟨833991, by decide⟩,⟨834044, by decide⟩,⟨834097, by decide⟩]) unmarked_context_11_27086_834098 node_context_11_27086_834098
  intro a
  fin_cases a
  · exact context_12_108344_833915
  · exact context_12_108345_833991
  · exact context_12_108346_834044
  · exact context_12_108347_834097

theorem selected_cut_32442 : selected 9 ⟨834161, by decide⟩
    (prefixPartial 12 108348) = some ⟨12, 2, 0, 834161, 108348, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_108348_834161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108348 ⟨834161, by decide⟩ :=
  accepted_of_selected 12 108348 ⟨834161, by decide⟩ ⟨12, 2, 0, 834161, 108348, 3597, 65536⟩
    (by decide) selected_cut_32442

theorem selected_cut_32443 : selected 9 ⟨834217, by decide⟩
    (prefixPartial 12 108349) = some ⟨12, 2, 0, 834217, 108349, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_108349_834217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108349 ⟨834217, by decide⟩ :=
  accepted_of_selected 12 108349 ⟨834217, by decide⟩ ⟨12, 2, 0, 834217, 108349, 3237, 65536⟩
    (by decide) selected_cut_32443

theorem selected_cut_32444 : selected 9 ⟨834268, by decide⟩
    (prefixPartial 12 108350) = some ⟨12, 2, 0, 834268, 108350, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_108350_834268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108350 ⟨834268, by decide⟩ :=
  accepted_of_selected 12 108350 ⟨834268, by decide⟩ ⟨12, 2, 0, 834268, 108350, 3089, 65536⟩
    (by decide) selected_cut_32444

theorem selected_cut_32445 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 108351) = some ⟨12, 1, 0, 512556, 108351, 1, 65536⟩ := by
  decide +kernel

theorem context_12_108351_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108351 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 108351 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 108351, 1, 65536⟩
    (by decide) selected_cut_32445

theorem unmarked_context_11_27087_834269 : frontier 10 ⟨834269, by decide⟩
    (prefixCache 11 27087) (prefixPartial 11 27087) = false := by
  decide +kernel

theorem node_context_11_27087_834269 : EJMOriginalGlobalDAGData.nodes 10 ⟨834269, by decide⟩ =
    .split (coordinate 11) (![⟨834161, by decide⟩,⟨834217, by decide⟩,⟨834268, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27087_834269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27087 ⟨834269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27087
    ⟨834269, by decide⟩ (by decide) (![⟨834161, by decide⟩,⟨834217, by decide⟩,⟨834268, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_27087_834269 node_context_11_27087_834269
  intro a
  fin_cases a
  · exact context_12_108348_834161
  · exact context_12_108349_834217
  · exact context_12_108350_834268
  · exact context_12_108351_512556

theorem unmarked_context_10_6771_834270 : frontier 11 ⟨834270, by decide⟩
    (prefixCache 10 6771) (prefixPartial 10 6771) = false := by
  decide +kernel

theorem node_context_10_6771_834270 : EJMOriginalGlobalDAGData.nodes 11 ⟨834270, by decide⟩ =
    .split (coordinate 10) (![⟨833529, by decide⟩,⟨833824, by decide⟩,⟨834098, by decide⟩,⟨834269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6771_834270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6771 ⟨834270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6771
    ⟨834270, by decide⟩ (by decide) (![⟨833529, by decide⟩,⟨833824, by decide⟩,⟨834098, by decide⟩,⟨834269, by decide⟩]) unmarked_context_10_6771_834270 node_context_10_6771_834270
  intro a
  fin_cases a
  · exact context_11_27084_833529
  · exact context_11_27085_833824
  · exact context_11_27086_834098
  · exact context_11_27087_834269

theorem unmarked_context_9_1692_834271 : frontier 12 ⟨834271, by decide⟩
    (prefixCache 9 1692) (prefixPartial 9 1692) = false := by
  decide +kernel

theorem node_context_9_1692_834271 : EJMOriginalGlobalDAGData.nodes 12 ⟨834271, by decide⟩ =
    .split (coordinate 9) (![⟨830451, by decide⟩,⟨831609, by decide⟩,⟨833198, by decide⟩,⟨834270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1692_834271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1692 ⟨834271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1692
    ⟨834271, by decide⟩ (by decide) (![⟨830451, by decide⟩,⟨831609, by decide⟩,⟨833198, by decide⟩,⟨834270, by decide⟩]) unmarked_context_9_1692_834271 node_context_9_1692_834271
  intro a
  fin_cases a
  · exact context_10_6768_830451
  · exact context_10_6769_831609
  · exact context_10_6770_833198
  · exact context_10_6771_834270

theorem selected_cut_32446 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 6772) = some ⟨10, 1, 0, 145424, 6772, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6772_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6772 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 6772 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 6772, 1, 1048576⟩
    (by decide) selected_cut_32446

theorem selected_cut_32447 : selected 9 ⟨834327, by decide⟩
    (prefixPartial 12 108368) = some ⟨12, 2, 0, 834327, 108368, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_108368_834327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108368 ⟨834327, by decide⟩ :=
  accepted_of_selected 12 108368 ⟨834327, by decide⟩ ⟨12, 2, 0, 834327, 108368, 3005, 65536⟩
    (by decide) selected_cut_32447

theorem selected_cut_32448 : selected 9 ⟨834379, by decide⟩
    (prefixPartial 12 108369) = some ⟨12, 2, 0, 834379, 108369, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_108369_834379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108369 ⟨834379, by decide⟩ :=
  accepted_of_selected 12 108369 ⟨834379, by decide⟩ ⟨12, 2, 0, 834379, 108369, 2985, 65536⟩
    (by decide) selected_cut_32448

theorem selected_cut_32449 : selected 9 ⟨834465, by decide⟩
    (prefixPartial 12 108370) = some ⟨12, 2, 0, 834465, 108370, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_108370_834465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108370 ⟨834465, by decide⟩ :=
  accepted_of_selected 12 108370 ⟨834465, by decide⟩ ⟨12, 2, 0, 834465, 108370, 3301, 65536⟩
    (by decide) selected_cut_32449

theorem selected_cut_32450 : selected 9 ⟨834530, by decide⟩
    (prefixPartial 12 108371) = some ⟨12, 2, 0, 834530, 108371, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_108371_834530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 108371 ⟨834530, by decide⟩ :=
  accepted_of_selected 12 108371 ⟨834530, by decide⟩ ⟨12, 2, 0, 834530, 108371, 2885, 65536⟩
    (by decide) selected_cut_32450

theorem unmarked_context_11_27092_834531 : frontier 10 ⟨834531, by decide⟩
    (prefixCache 11 27092) (prefixPartial 11 27092) = false := by
  decide +kernel

theorem node_context_11_27092_834531 : EJMOriginalGlobalDAGData.nodes 10 ⟨834531, by decide⟩ =
    .split (coordinate 11) (![⟨834327, by decide⟩,⟨834379, by decide⟩,⟨834465, by decide⟩,⟨834530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27092_834531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27092 ⟨834531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27092
    ⟨834531, by decide⟩ (by decide) (![⟨834327, by decide⟩,⟨834379, by decide⟩,⟨834465, by decide⟩,⟨834530, by decide⟩]) unmarked_context_11_27092_834531 node_context_11_27092_834531
  intro a
  fin_cases a
  · exact context_12_108368_834327
  · exact context_12_108369_834379
  · exact context_12_108370_834465
  · exact context_12_108371_834530

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
