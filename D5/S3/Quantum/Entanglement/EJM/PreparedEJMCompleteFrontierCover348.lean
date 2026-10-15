/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover347
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33412 : selected 9 ⟨860091, by decide⟩
    (prefixPartial 12 110194) = some ⟨12, 2, 0, 860091, 110194, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_110194_860091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110194 ⟨860091, by decide⟩ :=
  accepted_of_selected 12 110194 ⟨860091, by decide⟩ ⟨12, 2, 0, 860091, 110194, 2165, 65536⟩
    (by decide) selected_cut_33412

theorem selected_cut_33413 : selected 9 ⟨860133, by decide⟩
    (prefixPartial 12 110195) = some ⟨12, 2, 0, 860133, 110195, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_110195_860133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110195 ⟨860133, by decide⟩ :=
  accepted_of_selected 12 110195 ⟨860133, by decide⟩ ⟨12, 2, 0, 860133, 110195, 2741, 65536⟩
    (by decide) selected_cut_33413

theorem unmarked_context_11_27548_860134 : frontier 10 ⟨860134, by decide⟩
    (prefixCache 11 27548) (prefixPartial 11 27548) = false := by
  decide +kernel

theorem node_context_11_27548_860134 : EJMOriginalGlobalDAGData.nodes 10 ⟨860134, by decide⟩ =
    .split (coordinate 11) (![⟨860027, by decide⟩,⟨860061, by decide⟩,⟨860091, by decide⟩,⟨860133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27548_860134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27548 ⟨860134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27548
    ⟨860134, by decide⟩ (by decide) (![⟨860027, by decide⟩,⟨860061, by decide⟩,⟨860091, by decide⟩,⟨860133, by decide⟩]) unmarked_context_11_27548_860134 node_context_11_27548_860134
  intro a
  fin_cases a
  · exact context_12_110192_860027
  · exact context_12_110193_860061
  · exact context_12_110194_860091
  · exact context_12_110195_860133

theorem selected_cut_33414 : selected 9 ⟨860181, by decide⟩
    (prefixPartial 12 110196) = some ⟨12, 2, 0, 860181, 110196, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_110196_860181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110196 ⟨860181, by decide⟩ :=
  accepted_of_selected 12 110196 ⟨860181, by decide⟩ ⟨12, 2, 0, 860181, 110196, 2393, 65536⟩
    (by decide) selected_cut_33414

theorem selected_cut_33415 : selected 9 ⟨860213, by decide⟩
    (prefixPartial 12 110197) = some ⟨12, 2, 0, 860213, 110197, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_110197_860213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110197 ⟨860213, by decide⟩ :=
  accepted_of_selected 12 110197 ⟨860213, by decide⟩ ⟨12, 2, 0, 860213, 110197, 2313, 65536⟩
    (by decide) selected_cut_33415

theorem selected_cut_33416 : selected 9 ⟨860240, by decide⟩
    (prefixPartial 12 110198) = some ⟨12, 2, 0, 860240, 110198, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_110198_860240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110198 ⟨860240, by decide⟩ :=
  accepted_of_selected 12 110198 ⟨860240, by decide⟩ ⟨12, 2, 0, 860240, 110198, 1989, 65536⟩
    (by decide) selected_cut_33416

theorem selected_cut_33417 : selected 9 ⟨860286, by decide⟩
    (prefixPartial 12 110199) = some ⟨12, 2, 0, 860286, 110199, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_110199_860286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110199 ⟨860286, by decide⟩ :=
  accepted_of_selected 12 110199 ⟨860286, by decide⟩ ⟨12, 2, 0, 860286, 110199, 2597, 65536⟩
    (by decide) selected_cut_33417

theorem unmarked_context_11_27549_860287 : frontier 10 ⟨860287, by decide⟩
    (prefixCache 11 27549) (prefixPartial 11 27549) = false := by
  decide +kernel

theorem node_context_11_27549_860287 : EJMOriginalGlobalDAGData.nodes 10 ⟨860287, by decide⟩ =
    .split (coordinate 11) (![⟨860181, by decide⟩,⟨860213, by decide⟩,⟨860240, by decide⟩,⟨860286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27549_860287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27549 ⟨860287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27549
    ⟨860287, by decide⟩ (by decide) (![⟨860181, by decide⟩,⟨860213, by decide⟩,⟨860240, by decide⟩,⟨860286, by decide⟩]) unmarked_context_11_27549_860287 node_context_11_27549_860287
  intro a
  fin_cases a
  · exact context_12_110196_860181
  · exact context_12_110197_860213
  · exact context_12_110198_860240
  · exact context_12_110199_860286

theorem selected_cut_33418 : selected 9 ⟨860323, by decide⟩
    (prefixPartial 12 110200) = some ⟨12, 2, 0, 860323, 110200, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_110200_860323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110200 ⟨860323, by decide⟩ :=
  accepted_of_selected 12 110200 ⟨860323, by decide⟩ ⟨12, 2, 0, 860323, 110200, 2009, 65536⟩
    (by decide) selected_cut_33418

theorem selected_cut_33419 : selected 9 ⟨860350, by decide⟩
    (prefixPartial 12 110201) = some ⟨12, 2, 0, 860350, 110201, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_110201_860350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110201 ⟨860350, by decide⟩ :=
  accepted_of_selected 12 110201 ⟨860350, by decide⟩ ⟨12, 2, 0, 860350, 110201, 1945, 65536⟩
    (by decide) selected_cut_33419

theorem selected_cut_33420 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 110202) = some ⟨12, 1, 0, 662655, 110202, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110202_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110202 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 110202 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 110202, 1, 65536⟩
    (by decide) selected_cut_33420

theorem selected_cut_33421 : selected 9 ⟨860378, by decide⟩
    (prefixPartial 12 110203) = some ⟨12, 2, 0, 860378, 110203, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_110203_860378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110203 ⟨860378, by decide⟩ :=
  accepted_of_selected 12 110203 ⟨860378, by decide⟩ ⟨12, 2, 0, 860378, 110203, 2057, 65536⟩
    (by decide) selected_cut_33421

theorem unmarked_context_11_27550_860379 : frontier 10 ⟨860379, by decide⟩
    (prefixCache 11 27550) (prefixPartial 11 27550) = false := by
  decide +kernel

theorem node_context_11_27550_860379 : EJMOriginalGlobalDAGData.nodes 10 ⟨860379, by decide⟩ =
    .split (coordinate 11) (![⟨860323, by decide⟩,⟨860350, by decide⟩,⟨662655, by decide⟩,⟨860378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27550_860379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27550 ⟨860379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27550
    ⟨860379, by decide⟩ (by decide) (![⟨860323, by decide⟩,⟨860350, by decide⟩,⟨662655, by decide⟩,⟨860378, by decide⟩]) unmarked_context_11_27550_860379 node_context_11_27550_860379
  intro a
  fin_cases a
  · exact context_12_110200_860323
  · exact context_12_110201_860350
  · exact context_12_110202_662655
  · exact context_12_110203_860378

theorem selected_cut_33422 : selected 10 ⟨860471, by decide⟩
    (prefixPartial 11 27551) = some ⟨11, 2, 0, 860471, 27551, 2997, 262144⟩ := by
  decide +kernel

theorem context_11_27551_860471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27551 ⟨860471, by decide⟩ :=
  accepted_of_selected 11 27551 ⟨860471, by decide⟩ ⟨11, 2, 0, 860471, 27551, 2997, 262144⟩
    (by decide) selected_cut_33422

theorem unmarked_context_10_6887_860472 : frontier 11 ⟨860472, by decide⟩
    (prefixCache 10 6887) (prefixPartial 10 6887) = false := by
  decide +kernel

theorem node_context_10_6887_860472 : EJMOriginalGlobalDAGData.nodes 11 ⟨860472, by decide⟩ =
    .split (coordinate 10) (![⟨860134, by decide⟩,⟨860287, by decide⟩,⟨860379, by decide⟩,⟨860471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6887_860472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6887 ⟨860472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6887
    ⟨860472, by decide⟩ (by decide) (![⟨860134, by decide⟩,⟨860287, by decide⟩,⟨860379, by decide⟩,⟨860471, by decide⟩]) unmarked_context_10_6887_860472 node_context_10_6887_860472
  intro a
  fin_cases a
  · exact context_11_27548_860134
  · exact context_11_27549_860287
  · exact context_11_27550_860379
  · exact context_11_27551_860471

theorem unmarked_context_9_1721_860473 : frontier 12 ⟨860473, by decide⟩
    (prefixCache 9 1721) (prefixPartial 9 1721) = false := by
  decide +kernel

theorem node_context_9_1721_860473 : EJMOriginalGlobalDAGData.nodes 12 ⟨860473, by decide⟩ =
    .split (coordinate 9) (![⟨858418, by decide⟩,⟨859288, by decide⟩,⟨859974, by decide⟩,⟨860472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1721_860473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1721 ⟨860473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1721
    ⟨860473, by decide⟩ (by decide) (![⟨858418, by decide⟩,⟨859288, by decide⟩,⟨859974, by decide⟩,⟨860472, by decide⟩]) unmarked_context_9_1721_860473 node_context_9_1721_860473
  intro a
  fin_cases a
  · exact context_10_6884_858418
  · exact context_10_6885_859288
  · exact context_10_6886_859974
  · exact context_10_6887_860472

theorem selected_cut_33423 : selected 9 ⟨860494, by decide⟩
    (prefixPartial 12 110208) = some ⟨12, 2, 0, 860494, 110208, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_110208_860494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110208 ⟨860494, by decide⟩ :=
  accepted_of_selected 12 110208 ⟨860494, by decide⟩ ⟨12, 2, 0, 860494, 110208, 2133, 65536⟩
    (by decide) selected_cut_33423

theorem selected_cut_33424 : selected 9 ⟨860519, by decide⟩
    (prefixPartial 12 110209) = some ⟨12, 2, 0, 860519, 110209, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_110209_860519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110209 ⟨860519, by decide⟩ :=
  accepted_of_selected 12 110209 ⟨860519, by decide⟩ ⟨12, 2, 0, 860519, 110209, 2289, 65536⟩
    (by decide) selected_cut_33424

theorem selected_cut_33425 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 110210) = some ⟨12, 1, 0, 813440, 110210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110210_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110210 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 110210 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 110210, 1, 65536⟩
    (by decide) selected_cut_33425

theorem selected_cut_33426 : selected 9 ⟨860550, by decide⟩
    (prefixPartial 12 110211) = some ⟨12, 2, 0, 860550, 110211, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_110211_860550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110211 ⟨860550, by decide⟩ :=
  accepted_of_selected 12 110211 ⟨860550, by decide⟩ ⟨12, 2, 0, 860550, 110211, 2285, 65536⟩
    (by decide) selected_cut_33426

theorem unmarked_context_11_27552_860551 : frontier 10 ⟨860551, by decide⟩
    (prefixCache 11 27552) (prefixPartial 11 27552) = false := by
  decide +kernel

theorem node_context_11_27552_860551 : EJMOriginalGlobalDAGData.nodes 10 ⟨860551, by decide⟩ =
    .split (coordinate 11) (![⟨860494, by decide⟩,⟨860519, by decide⟩,⟨813440, by decide⟩,⟨860550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27552_860551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27552 ⟨860551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27552
    ⟨860551, by decide⟩ (by decide) (![⟨860494, by decide⟩,⟨860519, by decide⟩,⟨813440, by decide⟩,⟨860550, by decide⟩]) unmarked_context_11_27552_860551 node_context_11_27552_860551
  intro a
  fin_cases a
  · exact context_12_110208_860494
  · exact context_12_110209_860519
  · exact context_12_110210_813440
  · exact context_12_110211_860550

theorem selected_cut_33427 : selected 9 ⟨860585, by decide⟩
    (prefixPartial 12 110212) = some ⟨12, 2, 0, 860585, 110212, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_110212_860585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110212 ⟨860585, by decide⟩ :=
  accepted_of_selected 12 110212 ⟨860585, by decide⟩ ⟨12, 2, 0, 860585, 110212, 2165, 65536⟩
    (by decide) selected_cut_33427

theorem selected_cut_33428 : selected 9 ⟨860609, by decide⟩
    (prefixPartial 12 110213) = some ⟨12, 2, 0, 860609, 110213, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_110213_860609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110213 ⟨860609, by decide⟩ :=
  accepted_of_selected 12 110213 ⟨860609, by decide⟩ ⟨12, 2, 0, 860609, 110213, 2265, 65536⟩
    (by decide) selected_cut_33428

theorem selected_cut_33429 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 110214) = some ⟨12, 1, 0, 813440, 110214, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110214_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110214 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 110214 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 110214, 1, 65536⟩
    (by decide) selected_cut_33429

theorem selected_cut_33430 : selected 9 ⟨860637, by decide⟩
    (prefixPartial 12 110215) = some ⟨12, 2, 0, 860637, 110215, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_110215_860637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110215 ⟨860637, by decide⟩ :=
  accepted_of_selected 12 110215 ⟨860637, by decide⟩ ⟨12, 2, 0, 860637, 110215, 2345, 65536⟩
    (by decide) selected_cut_33430

theorem unmarked_context_11_27553_860638 : frontier 10 ⟨860638, by decide⟩
    (prefixCache 11 27553) (prefixPartial 11 27553) = false := by
  decide +kernel

theorem node_context_11_27553_860638 : EJMOriginalGlobalDAGData.nodes 10 ⟨860638, by decide⟩ =
    .split (coordinate 11) (![⟨860585, by decide⟩,⟨860609, by decide⟩,⟨813440, by decide⟩,⟨860637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27553_860638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27553 ⟨860638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27553
    ⟨860638, by decide⟩ (by decide) (![⟨860585, by decide⟩,⟨860609, by decide⟩,⟨813440, by decide⟩,⟨860637, by decide⟩]) unmarked_context_11_27553_860638 node_context_11_27553_860638
  intro a
  fin_cases a
  · exact context_12_110212_860585
  · exact context_12_110213_860609
  · exact context_12_110214_813440
  · exact context_12_110215_860637

theorem selected_cut_33431 : selected 9 ⟨860658, by decide⟩
    (prefixPartial 12 110216) = some ⟨12, 2, 0, 860658, 110216, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_110216_860658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110216 ⟨860658, by decide⟩ :=
  accepted_of_selected 12 110216 ⟨860658, by decide⟩ ⟨12, 2, 0, 860658, 110216, 1873, 65536⟩
    (by decide) selected_cut_33431

theorem selected_cut_33432 : selected 9 ⟨860682, by decide⟩
    (prefixPartial 12 110217) = some ⟨12, 2, 0, 860682, 110217, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_110217_860682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110217 ⟨860682, by decide⟩ :=
  accepted_of_selected 12 110217 ⟨860682, by decide⟩ ⟨12, 2, 0, 860682, 110217, 2021, 65536⟩
    (by decide) selected_cut_33432

theorem selected_cut_33433 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 110218) = some ⟨12, 1, 0, 813440, 110218, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110218_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110218 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 110218 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 110218, 1, 65536⟩
    (by decide) selected_cut_33433

theorem selected_cut_33434 : selected 9 ⟨860707, by decide⟩
    (prefixPartial 12 110219) = some ⟨12, 2, 0, 860707, 110219, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_110219_860707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110219 ⟨860707, by decide⟩ :=
  accepted_of_selected 12 110219 ⟨860707, by decide⟩ ⟨12, 2, 0, 860707, 110219, 1853, 65536⟩
    (by decide) selected_cut_33434

theorem unmarked_context_11_27554_860708 : frontier 10 ⟨860708, by decide⟩
    (prefixCache 11 27554) (prefixPartial 11 27554) = false := by
  decide +kernel

theorem node_context_11_27554_860708 : EJMOriginalGlobalDAGData.nodes 10 ⟨860708, by decide⟩ =
    .split (coordinate 11) (![⟨860658, by decide⟩,⟨860682, by decide⟩,⟨813440, by decide⟩,⟨860707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27554_860708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27554 ⟨860708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27554
    ⟨860708, by decide⟩ (by decide) (![⟨860658, by decide⟩,⟨860682, by decide⟩,⟨813440, by decide⟩,⟨860707, by decide⟩]) unmarked_context_11_27554_860708 node_context_11_27554_860708
  intro a
  fin_cases a
  · exact context_12_110216_860658
  · exact context_12_110217_860682
  · exact context_12_110218_813440
  · exact context_12_110219_860707

theorem selected_cut_33435 : selected 9 ⟨860734, by decide⟩
    (prefixPartial 12 110220) = some ⟨12, 2, 0, 860734, 110220, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_110220_860734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110220 ⟨860734, by decide⟩ :=
  accepted_of_selected 12 110220 ⟨860734, by decide⟩ ⟨12, 2, 0, 860734, 110220, 2085, 65536⟩
    (by decide) selected_cut_33435

theorem selected_cut_33436 : selected 9 ⟨860762, by decide⟩
    (prefixPartial 12 110221) = some ⟨12, 2, 0, 860762, 110221, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_110221_860762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110221 ⟨860762, by decide⟩ :=
  accepted_of_selected 12 110221 ⟨860762, by decide⟩ ⟨12, 2, 0, 860762, 110221, 2197, 65536⟩
    (by decide) selected_cut_33436

theorem selected_cut_33437 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 110222) = some ⟨12, 1, 0, 813440, 110222, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110222_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110222 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 110222 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 110222, 1, 65536⟩
    (by decide) selected_cut_33437

theorem selected_cut_33438 : selected 9 ⟨860787, by decide⟩
    (prefixPartial 12 110223) = some ⟨12, 2, 0, 860787, 110223, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_110223_860787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110223 ⟨860787, by decide⟩ :=
  accepted_of_selected 12 110223 ⟨860787, by decide⟩ ⟨12, 2, 0, 860787, 110223, 2177, 65536⟩
    (by decide) selected_cut_33438

theorem unmarked_context_11_27555_860788 : frontier 10 ⟨860788, by decide⟩
    (prefixCache 11 27555) (prefixPartial 11 27555) = false := by
  decide +kernel

theorem node_context_11_27555_860788 : EJMOriginalGlobalDAGData.nodes 10 ⟨860788, by decide⟩ =
    .split (coordinate 11) (![⟨860734, by decide⟩,⟨860762, by decide⟩,⟨813440, by decide⟩,⟨860787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27555_860788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27555 ⟨860788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27555
    ⟨860788, by decide⟩ (by decide) (![⟨860734, by decide⟩,⟨860762, by decide⟩,⟨813440, by decide⟩,⟨860787, by decide⟩]) unmarked_context_11_27555_860788 node_context_11_27555_860788
  intro a
  fin_cases a
  · exact context_12_110220_860734
  · exact context_12_110221_860762
  · exact context_12_110222_813440
  · exact context_12_110223_860787

theorem unmarked_context_10_6888_860789 : frontier 11 ⟨860789, by decide⟩
    (prefixCache 10 6888) (prefixPartial 10 6888) = false := by
  decide +kernel

theorem node_context_10_6888_860789 : EJMOriginalGlobalDAGData.nodes 11 ⟨860789, by decide⟩ =
    .split (coordinate 10) (![⟨860551, by decide⟩,⟨860638, by decide⟩,⟨860708, by decide⟩,⟨860788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6888_860789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6888 ⟨860789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6888
    ⟨860789, by decide⟩ (by decide) (![⟨860551, by decide⟩,⟨860638, by decide⟩,⟨860708, by decide⟩,⟨860788, by decide⟩]) unmarked_context_10_6888_860789 node_context_10_6888_860789
  intro a
  fin_cases a
  · exact context_11_27552_860551
  · exact context_11_27553_860638
  · exact context_11_27554_860708
  · exact context_11_27555_860788

theorem selected_cut_33439 : selected 9 ⟨860820, by decide⟩
    (prefixPartial 12 110224) = some ⟨12, 2, 0, 860820, 110224, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_110224_860820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110224 ⟨860820, by decide⟩ :=
  accepted_of_selected 12 110224 ⟨860820, by decide⟩ ⟨12, 2, 0, 860820, 110224, 2249, 65536⟩
    (by decide) selected_cut_33439

theorem selected_cut_33440 : selected 9 ⟨860852, by decide⟩
    (prefixPartial 12 110225) = some ⟨12, 2, 0, 860852, 110225, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_110225_860852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110225 ⟨860852, by decide⟩ :=
  accepted_of_selected 12 110225 ⟨860852, by decide⟩ ⟨12, 2, 0, 860852, 110225, 2429, 65536⟩
    (by decide) selected_cut_33440

theorem selected_cut_33441 : selected 9 ⟨813889, by decide⟩
    (prefixPartial 12 110226) = some ⟨12, 1, 0, 813889, 110226, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110226_813889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110226 ⟨813889, by decide⟩ :=
  accepted_of_selected 12 110226 ⟨813889, by decide⟩ ⟨12, 1, 0, 813889, 110226, 1, 65536⟩
    (by decide) selected_cut_33441

theorem selected_cut_33442 : selected 9 ⟨860882, by decide⟩
    (prefixPartial 12 110227) = some ⟨12, 2, 0, 860882, 110227, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_110227_860882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110227 ⟨860882, by decide⟩ :=
  accepted_of_selected 12 110227 ⟨860882, by decide⟩ ⟨12, 2, 0, 860882, 110227, 2349, 65536⟩
    (by decide) selected_cut_33442

theorem unmarked_context_11_27556_860883 : frontier 10 ⟨860883, by decide⟩
    (prefixCache 11 27556) (prefixPartial 11 27556) = false := by
  decide +kernel

theorem node_context_11_27556_860883 : EJMOriginalGlobalDAGData.nodes 10 ⟨860883, by decide⟩ =
    .split (coordinate 11) (![⟨860820, by decide⟩,⟨860852, by decide⟩,⟨813889, by decide⟩,⟨860882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27556_860883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27556 ⟨860883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27556
    ⟨860883, by decide⟩ (by decide) (![⟨860820, by decide⟩,⟨860852, by decide⟩,⟨813889, by decide⟩,⟨860882, by decide⟩]) unmarked_context_11_27556_860883 node_context_11_27556_860883
  intro a
  fin_cases a
  · exact context_12_110224_860820
  · exact context_12_110225_860852
  · exact context_12_110226_813889
  · exact context_12_110227_860882

theorem selected_cut_33443 : selected 9 ⟨860907, by decide⟩
    (prefixPartial 12 110228) = some ⟨12, 2, 0, 860907, 110228, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_110228_860907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110228 ⟨860907, by decide⟩ :=
  accepted_of_selected 12 110228 ⟨860907, by decide⟩ ⟨12, 2, 0, 860907, 110228, 2077, 65536⟩
    (by decide) selected_cut_33443

theorem selected_cut_33444 : selected 9 ⟨860924, by decide⟩
    (prefixPartial 12 110229) = some ⟨12, 2, 0, 860924, 110229, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_110229_860924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110229 ⟨860924, by decide⟩ :=
  accepted_of_selected 12 110229 ⟨860924, by decide⟩ ⟨12, 2, 0, 860924, 110229, 2217, 65536⟩
    (by decide) selected_cut_33444

theorem selected_cut_33445 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 110230) = some ⟨12, 1, 0, 813979, 110230, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110230_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110230 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 110230 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 110230, 1, 65536⟩
    (by decide) selected_cut_33445

theorem selected_cut_33446 : selected 9 ⟨860963, by decide⟩
    (prefixPartial 12 110231) = some ⟨12, 2, 0, 860963, 110231, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_110231_860963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110231 ⟨860963, by decide⟩ :=
  accepted_of_selected 12 110231 ⟨860963, by decide⟩ ⟨12, 2, 0, 860963, 110231, 2329, 65536⟩
    (by decide) selected_cut_33446

theorem unmarked_context_11_27557_860964 : frontier 10 ⟨860964, by decide⟩
    (prefixCache 11 27557) (prefixPartial 11 27557) = false := by
  decide +kernel

theorem node_context_11_27557_860964 : EJMOriginalGlobalDAGData.nodes 10 ⟨860964, by decide⟩ =
    .split (coordinate 11) (![⟨860907, by decide⟩,⟨860924, by decide⟩,⟨813979, by decide⟩,⟨860963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27557_860964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27557 ⟨860964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27557
    ⟨860964, by decide⟩ (by decide) (![⟨860907, by decide⟩,⟨860924, by decide⟩,⟨813979, by decide⟩,⟨860963, by decide⟩]) unmarked_context_11_27557_860964 node_context_11_27557_860964
  intro a
  fin_cases a
  · exact context_12_110228_860907
  · exact context_12_110229_860924
  · exact context_12_110230_813979
  · exact context_12_110231_860963

theorem selected_cut_33447 : selected 9 ⟨860990, by decide⟩
    (prefixPartial 12 110232) = some ⟨12, 2, 0, 860990, 110232, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_110232_860990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110232 ⟨860990, by decide⟩ :=
  accepted_of_selected 12 110232 ⟨860990, by decide⟩ ⟨12, 2, 0, 860990, 110232, 1669, 65536⟩
    (by decide) selected_cut_33447

theorem selected_cut_33448 : selected 9 ⟨861014, by decide⟩
    (prefixPartial 12 110233) = some ⟨12, 2, 0, 861014, 110233, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_110233_861014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110233 ⟨861014, by decide⟩ :=
  accepted_of_selected 12 110233 ⟨861014, by decide⟩ ⟨12, 2, 0, 861014, 110233, 1985, 65536⟩
    (by decide) selected_cut_33448

theorem selected_cut_33449 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 110234) = some ⟨12, 1, 0, 813979, 110234, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110234_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110234 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 110234 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 110234, 1, 65536⟩
    (by decide) selected_cut_33449

theorem selected_cut_33450 : selected 9 ⟨861034, by decide⟩
    (prefixPartial 12 110235) = some ⟨12, 2, 0, 861034, 110235, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_110235_861034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110235 ⟨861034, by decide⟩ :=
  accepted_of_selected 12 110235 ⟨861034, by decide⟩ ⟨12, 2, 0, 861034, 110235, 1721, 65536⟩
    (by decide) selected_cut_33450

theorem unmarked_context_11_27558_861035 : frontier 10 ⟨861035, by decide⟩
    (prefixCache 11 27558) (prefixPartial 11 27558) = false := by
  decide +kernel

theorem node_context_11_27558_861035 : EJMOriginalGlobalDAGData.nodes 10 ⟨861035, by decide⟩ =
    .split (coordinate 11) (![⟨860990, by decide⟩,⟨861014, by decide⟩,⟨813979, by decide⟩,⟨861034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27558_861035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27558 ⟨861035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27558
    ⟨861035, by decide⟩ (by decide) (![⟨860990, by decide⟩,⟨861014, by decide⟩,⟨813979, by decide⟩,⟨861034, by decide⟩]) unmarked_context_11_27558_861035 node_context_11_27558_861035
  intro a
  fin_cases a
  · exact context_12_110232_860990
  · exact context_12_110233_861014
  · exact context_12_110234_813979
  · exact context_12_110235_861034

theorem selected_cut_33451 : selected 9 ⟨861057, by decide⟩
    (prefixPartial 12 110236) = some ⟨12, 2, 0, 861057, 110236, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_110236_861057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110236 ⟨861057, by decide⟩ :=
  accepted_of_selected 12 110236 ⟨861057, by decide⟩ ⟨12, 2, 0, 861057, 110236, 1877, 65536⟩
    (by decide) selected_cut_33451

theorem selected_cut_33452 : selected 9 ⟨861084, by decide⟩
    (prefixPartial 12 110237) = some ⟨12, 2, 0, 861084, 110237, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_110237_861084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110237 ⟨861084, by decide⟩ :=
  accepted_of_selected 12 110237 ⟨861084, by decide⟩ ⟨12, 2, 0, 861084, 110237, 2005, 65536⟩
    (by decide) selected_cut_33452

theorem selected_cut_33453 : selected 9 ⟨814048, by decide⟩
    (prefixPartial 12 110238) = some ⟨12, 1, 0, 814048, 110238, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110238_814048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110238 ⟨814048, by decide⟩ :=
  accepted_of_selected 12 110238 ⟨814048, by decide⟩ ⟨12, 1, 0, 814048, 110238, 1, 65536⟩
    (by decide) selected_cut_33453

theorem selected_cut_33454 : selected 9 ⟨861108, by decide⟩
    (prefixPartial 12 110239) = some ⟨12, 2, 0, 861108, 110239, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_110239_861108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110239 ⟨861108, by decide⟩ :=
  accepted_of_selected 12 110239 ⟨861108, by decide⟩ ⟨12, 2, 0, 861108, 110239, 2009, 65536⟩
    (by decide) selected_cut_33454

theorem unmarked_context_11_27559_861109 : frontier 10 ⟨861109, by decide⟩
    (prefixCache 11 27559) (prefixPartial 11 27559) = false := by
  decide +kernel

theorem node_context_11_27559_861109 : EJMOriginalGlobalDAGData.nodes 10 ⟨861109, by decide⟩ =
    .split (coordinate 11) (![⟨861057, by decide⟩,⟨861084, by decide⟩,⟨814048, by decide⟩,⟨861108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27559_861109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27559 ⟨861109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27559
    ⟨861109, by decide⟩ (by decide) (![⟨861057, by decide⟩,⟨861084, by decide⟩,⟨814048, by decide⟩,⟨861108, by decide⟩]) unmarked_context_11_27559_861109 node_context_11_27559_861109
  intro a
  fin_cases a
  · exact context_12_110236_861057
  · exact context_12_110237_861084
  · exact context_12_110238_814048
  · exact context_12_110239_861108

theorem unmarked_context_10_6889_861110 : frontier 11 ⟨861110, by decide⟩
    (prefixCache 10 6889) (prefixPartial 10 6889) = false := by
  decide +kernel

theorem node_context_10_6889_861110 : EJMOriginalGlobalDAGData.nodes 11 ⟨861110, by decide⟩ =
    .split (coordinate 10) (![⟨860883, by decide⟩,⟨860964, by decide⟩,⟨861035, by decide⟩,⟨861109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6889_861110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6889 ⟨861110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6889
    ⟨861110, by decide⟩ (by decide) (![⟨860883, by decide⟩,⟨860964, by decide⟩,⟨861035, by decide⟩,⟨861109, by decide⟩]) unmarked_context_10_6889_861110 node_context_10_6889_861110
  intro a
  fin_cases a
  · exact context_11_27556_860883
  · exact context_11_27557_860964
  · exact context_11_27558_861035
  · exact context_11_27559_861109

theorem selected_cut_33455 : selected 9 ⟨861125, by decide⟩
    (prefixPartial 12 110240) = some ⟨12, 2, 0, 861125, 110240, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_110240_861125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110240 ⟨861125, by decide⟩ :=
  accepted_of_selected 12 110240 ⟨861125, by decide⟩ ⟨12, 2, 0, 861125, 110240, 1329, 65536⟩
    (by decide) selected_cut_33455

theorem selected_cut_33456 : selected 9 ⟨861144, by decide⟩
    (prefixPartial 12 110241) = some ⟨12, 2, 0, 861144, 110241, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_110241_861144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110241 ⟨861144, by decide⟩ :=
  accepted_of_selected 12 110241 ⟨861144, by decide⟩ ⟨12, 2, 0, 861144, 110241, 1481, 65536⟩
    (by decide) selected_cut_33456

theorem selected_cut_33457 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 110242) = some ⟨12, 1, 0, 769937, 110242, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110242_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110242 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 110242 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 110242, 1, 65536⟩
    (by decide) selected_cut_33457

theorem selected_cut_33458 : selected 9 ⟨861163, by decide⟩
    (prefixPartial 12 110243) = some ⟨12, 2, 0, 861163, 110243, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_110243_861163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110243 ⟨861163, by decide⟩ :=
  accepted_of_selected 12 110243 ⟨861163, by decide⟩ ⟨12, 2, 0, 861163, 110243, 1533, 65536⟩
    (by decide) selected_cut_33458

theorem unmarked_context_11_27560_861164 : frontier 10 ⟨861164, by decide⟩
    (prefixCache 11 27560) (prefixPartial 11 27560) = false := by
  decide +kernel

theorem node_context_11_27560_861164 : EJMOriginalGlobalDAGData.nodes 10 ⟨861164, by decide⟩ =
    .split (coordinate 11) (![⟨861125, by decide⟩,⟨861144, by decide⟩,⟨769937, by decide⟩,⟨861163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27560_861164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27560 ⟨861164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27560
    ⟨861164, by decide⟩ (by decide) (![⟨861125, by decide⟩,⟨861144, by decide⟩,⟨769937, by decide⟩,⟨861163, by decide⟩]) unmarked_context_11_27560_861164 node_context_11_27560_861164
  intro a
  fin_cases a
  · exact context_12_110240_861125
  · exact context_12_110241_861144
  · exact context_12_110242_769937
  · exact context_12_110243_861163

theorem selected_cut_33459 : selected 9 ⟨861179, by decide⟩
    (prefixPartial 12 110244) = some ⟨12, 2, 0, 861179, 110244, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_110244_861179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110244 ⟨861179, by decide⟩ :=
  accepted_of_selected 12 110244 ⟨861179, by decide⟩ ⟨12, 2, 0, 861179, 110244, 1345, 65536⟩
    (by decide) selected_cut_33459

theorem selected_cut_33460 : selected 9 ⟨861197, by decide⟩
    (prefixPartial 12 110245) = some ⟨12, 2, 0, 861197, 110245, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_110245_861197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110245 ⟨861197, by decide⟩ :=
  accepted_of_selected 12 110245 ⟨861197, by decide⟩ ⟨12, 2, 0, 861197, 110245, 1469, 65536⟩
    (by decide) selected_cut_33460

theorem selected_cut_33461 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 110246) = some ⟨12, 1, 0, 769937, 110246, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110246_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110246 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 110246 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 110246, 1, 65536⟩
    (by decide) selected_cut_33461

theorem selected_cut_33462 : selected 9 ⟨861212, by decide⟩
    (prefixPartial 12 110247) = some ⟨12, 2, 0, 861212, 110247, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_110247_861212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110247 ⟨861212, by decide⟩ :=
  accepted_of_selected 12 110247 ⟨861212, by decide⟩ ⟨12, 2, 0, 861212, 110247, 1561, 65536⟩
    (by decide) selected_cut_33462

theorem unmarked_context_11_27561_861213 : frontier 10 ⟨861213, by decide⟩
    (prefixCache 11 27561) (prefixPartial 11 27561) = false := by
  decide +kernel

theorem node_context_11_27561_861213 : EJMOriginalGlobalDAGData.nodes 10 ⟨861213, by decide⟩ =
    .split (coordinate 11) (![⟨861179, by decide⟩,⟨861197, by decide⟩,⟨769937, by decide⟩,⟨861212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27561_861213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27561 ⟨861213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27561
    ⟨861213, by decide⟩ (by decide) (![⟨861179, by decide⟩,⟨861197, by decide⟩,⟨769937, by decide⟩,⟨861212, by decide⟩]) unmarked_context_11_27561_861213 node_context_11_27561_861213
  intro a
  fin_cases a
  · exact context_12_110244_861179
  · exact context_12_110245_861197
  · exact context_12_110246_769937
  · exact context_12_110247_861212

theorem selected_cut_33463 : selected 10 ⟨861263, by decide⟩
    (prefixPartial 11 27562) = some ⟨11, 2, 0, 861263, 27562, 3253, 262144⟩ := by
  decide +kernel

theorem context_11_27562_861263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27562 ⟨861263, by decide⟩ :=
  accepted_of_selected 11 27562 ⟨861263, by decide⟩ ⟨11, 2, 0, 861263, 27562, 3253, 262144⟩
    (by decide) selected_cut_33463

theorem selected_cut_33464 : selected 9 ⟨861280, by decide⟩
    (prefixPartial 12 110252) = some ⟨12, 2, 0, 861280, 110252, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_110252_861280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110252 ⟨861280, by decide⟩ :=
  accepted_of_selected 12 110252 ⟨861280, by decide⟩ ⟨12, 2, 0, 861280, 110252, 1357, 65536⟩
    (by decide) selected_cut_33464

theorem selected_cut_33465 : selected 9 ⟨861297, by decide⟩
    (prefixPartial 12 110253) = some ⟨12, 2, 0, 861297, 110253, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_110253_861297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110253 ⟨861297, by decide⟩ :=
  accepted_of_selected 12 110253 ⟨861297, by decide⟩ ⟨12, 2, 0, 861297, 110253, 1413, 65536⟩
    (by decide) selected_cut_33465

theorem selected_cut_33466 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 110254) = some ⟨12, 1, 0, 769937, 110254, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110254_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110254 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 110254 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 110254, 1, 65536⟩
    (by decide) selected_cut_33466

theorem selected_cut_33467 : selected 9 ⟨861321, by decide⟩
    (prefixPartial 12 110255) = some ⟨12, 2, 0, 861321, 110255, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_110255_861321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110255 ⟨861321, by decide⟩ :=
  accepted_of_selected 12 110255 ⟨861321, by decide⟩ ⟨12, 2, 0, 861321, 110255, 1497, 65536⟩
    (by decide) selected_cut_33467

theorem unmarked_context_11_27563_861322 : frontier 10 ⟨861322, by decide⟩
    (prefixCache 11 27563) (prefixPartial 11 27563) = false := by
  decide +kernel

theorem node_context_11_27563_861322 : EJMOriginalGlobalDAGData.nodes 10 ⟨861322, by decide⟩ =
    .split (coordinate 11) (![⟨861280, by decide⟩,⟨861297, by decide⟩,⟨769937, by decide⟩,⟨861321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27563_861322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27563 ⟨861322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27563
    ⟨861322, by decide⟩ (by decide) (![⟨861280, by decide⟩,⟨861297, by decide⟩,⟨769937, by decide⟩,⟨861321, by decide⟩]) unmarked_context_11_27563_861322 node_context_11_27563_861322
  intro a
  fin_cases a
  · exact context_12_110252_861280
  · exact context_12_110253_861297
  · exact context_12_110254_769937
  · exact context_12_110255_861321

theorem unmarked_context_10_6890_861323 : frontier 11 ⟨861323, by decide⟩
    (prefixCache 10 6890) (prefixPartial 10 6890) = false := by
  decide +kernel

theorem node_context_10_6890_861323 : EJMOriginalGlobalDAGData.nodes 11 ⟨861323, by decide⟩ =
    .split (coordinate 10) (![⟨861164, by decide⟩,⟨861213, by decide⟩,⟨861263, by decide⟩,⟨861322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6890_861323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6890 ⟨861323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6890
    ⟨861323, by decide⟩ (by decide) (![⟨861164, by decide⟩,⟨861213, by decide⟩,⟨861263, by decide⟩,⟨861322, by decide⟩]) unmarked_context_10_6890_861323 node_context_10_6890_861323
  intro a
  fin_cases a
  · exact context_11_27560_861164
  · exact context_11_27561_861213
  · exact context_11_27562_861263
  · exact context_11_27563_861322

theorem selected_cut_33468 : selected 10 ⟨861360, by decide⟩
    (prefixPartial 11 27564) = some ⟨11, 2, 0, 861360, 27564, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_27564_861360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27564 ⟨861360, by decide⟩ :=
  accepted_of_selected 11 27564 ⟨861360, by decide⟩ ⟨11, 2, 0, 861360, 27564, 3725, 262144⟩
    (by decide) selected_cut_33468

theorem selected_cut_33469 : selected 10 ⟨861402, by decide⟩
    (prefixPartial 11 27565) = some ⟨11, 2, 0, 861402, 27565, 3213, 262144⟩ := by
  decide +kernel

theorem context_11_27565_861402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27565 ⟨861402, by decide⟩ :=
  accepted_of_selected 11 27565 ⟨861402, by decide⟩ ⟨11, 2, 0, 861402, 27565, 3213, 262144⟩
    (by decide) selected_cut_33469

theorem selected_cut_33470 : selected 10 ⟨861438, by decide⟩
    (prefixPartial 11 27566) = some ⟨11, 2, 0, 861438, 27566, 2581, 262144⟩ := by
  decide +kernel

theorem context_11_27566_861438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27566 ⟨861438, by decide⟩ :=
  accepted_of_selected 11 27566 ⟨861438, by decide⟩ ⟨11, 2, 0, 861438, 27566, 2581, 262144⟩
    (by decide) selected_cut_33470

theorem selected_cut_33471 : selected 10 ⟨861447, by decide⟩
    (prefixPartial 11 27567) = some ⟨11, 2, 0, 861447, 27567, 257, 262144⟩ := by
  decide +kernel

theorem context_11_27567_861447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27567 ⟨861447, by decide⟩ :=
  accepted_of_selected 11 27567 ⟨861447, by decide⟩ ⟨11, 2, 0, 861447, 27567, 257, 262144⟩
    (by decide) selected_cut_33471

theorem unmarked_context_10_6891_861448 : frontier 11 ⟨861448, by decide⟩
    (prefixCache 10 6891) (prefixPartial 10 6891) = false := by
  decide +kernel

theorem node_context_10_6891_861448 : EJMOriginalGlobalDAGData.nodes 11 ⟨861448, by decide⟩ =
    .split (coordinate 10) (![⟨861360, by decide⟩,⟨861402, by decide⟩,⟨861438, by decide⟩,⟨861447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6891_861448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6891 ⟨861448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6891
    ⟨861448, by decide⟩ (by decide) (![⟨861360, by decide⟩,⟨861402, by decide⟩,⟨861438, by decide⟩,⟨861447, by decide⟩]) unmarked_context_10_6891_861448 node_context_10_6891_861448
  intro a
  fin_cases a
  · exact context_11_27564_861360
  · exact context_11_27565_861402
  · exact context_11_27566_861438
  · exact context_11_27567_861447

theorem unmarked_context_9_1722_861449 : frontier 12 ⟨861449, by decide⟩
    (prefixCache 9 1722) (prefixPartial 9 1722) = false := by
  decide +kernel

theorem node_context_9_1722_861449 : EJMOriginalGlobalDAGData.nodes 12 ⟨861449, by decide⟩ =
    .split (coordinate 9) (![⟨860789, by decide⟩,⟨861110, by decide⟩,⟨861323, by decide⟩,⟨861448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1722_861449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1722 ⟨861449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1722
    ⟨861449, by decide⟩ (by decide) (![⟨860789, by decide⟩,⟨861110, by decide⟩,⟨861323, by decide⟩,⟨861448, by decide⟩]) unmarked_context_9_1722_861449 node_context_9_1722_861449
  intro a
  fin_cases a
  · exact context_10_6888_860789
  · exact context_10_6889_861110
  · exact context_10_6890_861323
  · exact context_10_6891_861448

theorem selected_cut_33472 : selected 10 ⟨861485, by decide⟩
    (prefixPartial 11 27568) = some ⟨11, 2, 0, 861485, 27568, 3529, 262144⟩ := by
  decide +kernel

theorem context_11_27568_861485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27568 ⟨861485, by decide⟩ :=
  accepted_of_selected 11 27568 ⟨861485, by decide⟩ ⟨11, 2, 0, 861485, 27568, 3529, 262144⟩
    (by decide) selected_cut_33472

theorem selected_cut_33473 : selected 10 ⟨861528, by decide⟩
    (prefixPartial 11 27569) = some ⟨11, 2, 0, 861528, 27569, 3341, 262144⟩ := by
  decide +kernel

theorem context_11_27569_861528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27569 ⟨861528, by decide⟩ :=
  accepted_of_selected 11 27569 ⟨861528, by decide⟩ ⟨11, 2, 0, 861528, 27569, 3341, 262144⟩
    (by decide) selected_cut_33473

theorem selected_cut_33474 : selected 10 ⟨861553, by decide⟩
    (prefixPartial 11 27570) = some ⟨11, 2, 0, 861553, 27570, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_27570_861553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27570 ⟨861553, by decide⟩ :=
  accepted_of_selected 11 27570 ⟨861553, by decide⟩ ⟨11, 2, 0, 861553, 27570, 1805, 262144⟩
    (by decide) selected_cut_33474

theorem selected_cut_33475 : selected 10 ⟨861588, by decide⟩
    (prefixPartial 11 27571) = some ⟨11, 2, 0, 861588, 27571, 3037, 262144⟩ := by
  decide +kernel

theorem context_11_27571_861588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27571 ⟨861588, by decide⟩ :=
  accepted_of_selected 11 27571 ⟨861588, by decide⟩ ⟨11, 2, 0, 861588, 27571, 3037, 262144⟩
    (by decide) selected_cut_33475

theorem unmarked_context_10_6892_861589 : frontier 11 ⟨861589, by decide⟩
    (prefixCache 10 6892) (prefixPartial 10 6892) = false := by
  decide +kernel

theorem node_context_10_6892_861589 : EJMOriginalGlobalDAGData.nodes 11 ⟨861589, by decide⟩ =
    .split (coordinate 10) (![⟨861485, by decide⟩,⟨861528, by decide⟩,⟨861553, by decide⟩,⟨861588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6892_861589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6892 ⟨861589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6892
    ⟨861589, by decide⟩ (by decide) (![⟨861485, by decide⟩,⟨861528, by decide⟩,⟨861553, by decide⟩,⟨861588, by decide⟩]) unmarked_context_10_6892_861589 node_context_10_6892_861589
  intro a
  fin_cases a
  · exact context_11_27568_861485
  · exact context_11_27569_861528
  · exact context_11_27570_861553
  · exact context_11_27571_861588

theorem selected_cut_33476 : selected 10 ⟨861615, by decide⟩
    (prefixPartial 11 27572) = some ⟨11, 2, 0, 861615, 27572, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_27572_861615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27572 ⟨861615, by decide⟩ :=
  accepted_of_selected 11 27572 ⟨861615, by decide⟩ ⟨11, 2, 0, 861615, 27572, 2545, 262144⟩
    (by decide) selected_cut_33476

theorem selected_cut_33477 : selected 10 ⟨861638, by decide⟩
    (prefixPartial 11 27573) = some ⟨11, 2, 0, 861638, 27573, 2021, 262144⟩ := by
  decide +kernel

theorem context_11_27573_861638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27573 ⟨861638, by decide⟩ :=
  accepted_of_selected 11 27573 ⟨861638, by decide⟩ ⟨11, 2, 0, 861638, 27573, 2021, 262144⟩
    (by decide) selected_cut_33477

theorem selected_cut_33478 : selected 10 ⟨861653, by decide⟩
    (prefixPartial 11 27574) = some ⟨11, 2, 0, 861653, 27574, 1113, 262144⟩ := by
  decide +kernel

theorem context_11_27574_861653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27574 ⟨861653, by decide⟩ :=
  accepted_of_selected 11 27574 ⟨861653, by decide⟩ ⟨11, 2, 0, 861653, 27574, 1113, 262144⟩
    (by decide) selected_cut_33478

theorem selected_cut_33479 : selected 10 ⟨861670, by decide⟩
    (prefixPartial 11 27575) = some ⟨11, 2, 0, 861670, 27575, 1693, 262144⟩ := by
  decide +kernel

theorem context_11_27575_861670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27575 ⟨861670, by decide⟩ :=
  accepted_of_selected 11 27575 ⟨861670, by decide⟩ ⟨11, 2, 0, 861670, 27575, 1693, 262144⟩
    (by decide) selected_cut_33479

theorem unmarked_context_10_6893_861671 : frontier 11 ⟨861671, by decide⟩
    (prefixCache 10 6893) (prefixPartial 10 6893) = false := by
  decide +kernel

theorem node_context_10_6893_861671 : EJMOriginalGlobalDAGData.nodes 11 ⟨861671, by decide⟩ =
    .split (coordinate 10) (![⟨861615, by decide⟩,⟨861638, by decide⟩,⟨861653, by decide⟩,⟨861670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6893_861671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6893 ⟨861671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6893
    ⟨861671, by decide⟩ (by decide) (![⟨861615, by decide⟩,⟨861638, by decide⟩,⟨861653, by decide⟩,⟨861670, by decide⟩]) unmarked_context_10_6893_861671 node_context_10_6893_861671
  intro a
  fin_cases a
  · exact context_11_27572_861615
  · exact context_11_27573_861638
  · exact context_11_27574_861653
  · exact context_11_27575_861670

theorem selected_cut_33480 : selected 11 ⟨861729, by decide⟩
    (prefixPartial 10 6894) = some ⟨10, 2, 0, 861729, 6894, 3709, 1048576⟩ := by
  decide +kernel

theorem context_10_6894_861729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6894 ⟨861729, by decide⟩ :=
  accepted_of_selected 10 6894 ⟨861729, by decide⟩ ⟨10, 2, 0, 861729, 6894, 3709, 1048576⟩
    (by decide) selected_cut_33480

theorem selected_cut_33481 : selected 11 ⟨861759, by decide⟩
    (prefixPartial 10 6895) = some ⟨10, 2, 0, 861759, 6895, 953, 1048576⟩ := by
  decide +kernel

theorem context_10_6895_861759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6895 ⟨861759, by decide⟩ :=
  accepted_of_selected 10 6895 ⟨861759, by decide⟩ ⟨10, 2, 0, 861759, 6895, 953, 1048576⟩
    (by decide) selected_cut_33481

theorem unmarked_context_9_1723_861760 : frontier 12 ⟨861760, by decide⟩
    (prefixCache 9 1723) (prefixPartial 9 1723) = false := by
  decide +kernel

theorem node_context_9_1723_861760 : EJMOriginalGlobalDAGData.nodes 12 ⟨861760, by decide⟩ =
    .split (coordinate 9) (![⟨861589, by decide⟩,⟨861671, by decide⟩,⟨861729, by decide⟩,⟨861759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1723_861760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1723 ⟨861760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1723
    ⟨861760, by decide⟩ (by decide) (![⟨861589, by decide⟩,⟨861671, by decide⟩,⟨861729, by decide⟩,⟨861759, by decide⟩]) unmarked_context_9_1723_861760 node_context_9_1723_861760
  intro a
  fin_cases a
  · exact context_10_6892_861589
  · exact context_10_6893_861671
  · exact context_10_6894_861729
  · exact context_10_6895_861759

theorem unmarked_context_8_430_861761 : frontier 13 ⟨861761, by decide⟩
    (prefixCache 8 430) (prefixPartial 8 430) = false := by
  decide +kernel

theorem node_context_8_430_861761 : EJMOriginalGlobalDAGData.nodes 13 ⟨861761, by decide⟩ =
    .split (coordinate 8) (![⟨857480, by decide⟩,⟨860473, by decide⟩,⟨861449, by decide⟩,⟨861760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_430_861761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 430 ⟨861761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 430
    ⟨861761, by decide⟩ (by decide) (![⟨857480, by decide⟩,⟨860473, by decide⟩,⟨861449, by decide⟩,⟨861760, by decide⟩]) unmarked_context_8_430_861761 node_context_8_430_861761
  intro a
  fin_cases a
  · exact context_9_1720_857480
  · exact context_9_1721_860473
  · exact context_9_1722_861449
  · exact context_9_1723_861760

theorem selected_cut_33482 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 27584) = some ⟨11, 1, 0, 434745, 27584, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27584_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27584 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 27584 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 27584, 1, 262144⟩
    (by decide) selected_cut_33482

theorem selected_cut_33483 : selected 10 ⟨861762, by decide⟩
    (prefixPartial 11 27585) = some ⟨11, 2, 0, 861762, 27585, 5, 262144⟩ := by
  decide +kernel

theorem context_11_27585_861762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27585 ⟨861762, by decide⟩ :=
  accepted_of_selected 11 27585 ⟨861762, by decide⟩ ⟨11, 2, 0, 861762, 27585, 5, 262144⟩
    (by decide) selected_cut_33483

theorem selected_cut_33484 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 110344) = some ⟨12, 1, 0, 448748, 110344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110344_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110344 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 110344 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 110344, 1, 65536⟩
    (by decide) selected_cut_33484

theorem selected_cut_33485 : selected 7 ⟨861780, by decide⟩
    (prefixPartial 14 1765520) = some ⟨14, 2, 0, 861780, 1765520, 237, 4096⟩ := by
  decide +kernel

theorem context_14_1765520_861780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1765520 ⟨861780, by decide⟩ :=
  accepted_of_selected 14 1765520 ⟨861780, by decide⟩ ⟨14, 2, 0, 861780, 1765520, 237, 4096⟩
    (by decide) selected_cut_33485

theorem selected_cut_33486 : selected 7 ⟨861839, by decide⟩
    (prefixPartial 14 1765521) = some ⟨14, 2, 0, 861839, 1765521, 1761, 4096⟩ := by
  decide +kernel

theorem context_14_1765521_861839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1765521 ⟨861839, by decide⟩ :=
  accepted_of_selected 14 1765521 ⟨861839, by decide⟩ ⟨14, 2, 0, 861839, 1765521, 1761, 4096⟩
    (by decide) selected_cut_33486

theorem selected_cut_33487 : selected 7 ⟨861899, by decide⟩
    (prefixPartial 14 1765522) = some ⟨14, 2, 0, 861899, 1765522, 1725, 4096⟩ := by
  decide +kernel

theorem context_14_1765522_861899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1765522 ⟨861899, by decide⟩ :=
  accepted_of_selected 14 1765522 ⟨861899, by decide⟩ ⟨14, 2, 0, 861899, 1765522, 1725, 4096⟩
    (by decide) selected_cut_33487

theorem selected_cut_33488 : selected 7 ⟨861921, by decide⟩
    (prefixPartial 14 1765523) = some ⟨14, 2, 0, 861921, 1765523, 973, 4096⟩ := by
  decide +kernel

theorem context_14_1765523_861921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1765523 ⟨861921, by decide⟩ :=
  accepted_of_selected 14 1765523 ⟨861921, by decide⟩ ⟨14, 2, 0, 861921, 1765523, 973, 4096⟩
    (by decide) selected_cut_33488

theorem unmarked_context_13_441380_861922 : frontier 8 ⟨861922, by decide⟩
    (prefixCache 13 441380) (prefixPartial 13 441380) = false := by
  decide +kernel

theorem node_context_13_441380_861922 : EJMOriginalGlobalDAGData.nodes 8 ⟨861922, by decide⟩ =
    .split (coordinate 13) (![⟨861780, by decide⟩,⟨861839, by decide⟩,⟨861899, by decide⟩,⟨861921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_441380_861922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441380 ⟨861922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 441380
    ⟨861922, by decide⟩ (by decide) (![⟨861780, by decide⟩,⟨861839, by decide⟩,⟨861899, by decide⟩,⟨861921, by decide⟩]) unmarked_context_13_441380_861922 node_context_13_441380_861922
  intro a
  fin_cases a
  · exact context_14_1765520_861780
  · exact context_14_1765521_861839
  · exact context_14_1765522_861899
  · exact context_14_1765523_861921

theorem selected_cut_33489 : selected 8 ⟨862034, by decide⟩
    (prefixPartial 13 441381) = some ⟨13, 2, 0, 862034, 441381, 3789, 16384⟩ := by
  decide +kernel

theorem context_13_441381_862034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441381 ⟨862034, by decide⟩ :=
  accepted_of_selected 13 441381 ⟨862034, by decide⟩ ⟨13, 2, 0, 862034, 441381, 3789, 16384⟩
    (by decide) selected_cut_33489

theorem selected_cut_33490 : selected 8 ⟨862170, by decide⟩
    (prefixPartial 13 441382) = some ⟨13, 2, 0, 862170, 441382, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_441382_862170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441382 ⟨862170, by decide⟩ :=
  accepted_of_selected 13 441382 ⟨862170, by decide⟩ ⟨13, 2, 0, 862170, 441382, 2593, 16384⟩
    (by decide) selected_cut_33490

theorem selected_cut_33491 : selected 8 ⟨862191, by decide⟩
    (prefixPartial 13 441383) = some ⟨13, 2, 0, 862191, 441383, 729, 16384⟩ := by
  decide +kernel

theorem context_13_441383_862191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441383 ⟨862191, by decide⟩ :=
  accepted_of_selected 13 441383 ⟨862191, by decide⟩ ⟨13, 2, 0, 862191, 441383, 729, 16384⟩
    (by decide) selected_cut_33491

theorem unmarked_context_12_110345_862192 : frontier 9 ⟨862192, by decide⟩
    (prefixCache 12 110345) (prefixPartial 12 110345) = false := by
  decide +kernel

theorem node_context_12_110345_862192 : EJMOriginalGlobalDAGData.nodes 9 ⟨862192, by decide⟩ =
    .split (coordinate 12) (![⟨861922, by decide⟩,⟨862034, by decide⟩,⟨862170, by decide⟩,⟨862191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110345_862192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110345 ⟨862192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110345
    ⟨862192, by decide⟩ (by decide) (![⟨861922, by decide⟩,⟨862034, by decide⟩,⟨862170, by decide⟩,⟨862191, by decide⟩]) unmarked_context_12_110345_862192 node_context_12_110345_862192
  intro a
  fin_cases a
  · exact context_13_441380_861922
  · exact context_13_441381_862034
  · exact context_13_441382_862170
  · exact context_13_441383_862191

theorem selected_cut_33492 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 110346) = some ⟨12, 1, 0, 763842, 110346, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110346_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110346 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 110346 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 110346, 1, 65536⟩
    (by decide) selected_cut_33492

theorem selected_cut_33493 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 110347) = some ⟨12, 1, 0, 604131, 110347, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110347_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110347 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 110347 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 110347, 1, 65536⟩
    (by decide) selected_cut_33493

theorem unmarked_context_11_27586_862193 : frontier 10 ⟨862193, by decide⟩
    (prefixCache 11 27586) (prefixPartial 11 27586) = false := by
  decide +kernel

theorem node_context_11_27586_862193 : EJMOriginalGlobalDAGData.nodes 10 ⟨862193, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨862192, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27586_862193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27586 ⟨862193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27586
    ⟨862193, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨862192, by decide⟩,⟨763842, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_27586_862193 node_context_11_27586_862193
  intro a
  fin_cases a
  · exact context_12_110344_448748
  · exact context_12_110345_862192
  · exact context_12_110346_763842
  · exact context_12_110347_604131

theorem selected_cut_33494 : selected 10 ⟨789341, by decide⟩
    (prefixPartial 11 27587) = some ⟨11, 1, 0, 789341, 27587, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27587_789341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27587 ⟨789341, by decide⟩ :=
  accepted_of_selected 11 27587 ⟨789341, by decide⟩ ⟨11, 1, 0, 789341, 27587, 1, 262144⟩
    (by decide) selected_cut_33494

theorem unmarked_context_10_6896_862194 : frontier 11 ⟨862194, by decide⟩
    (prefixCache 10 6896) (prefixPartial 10 6896) = false := by
  decide +kernel

theorem node_context_10_6896_862194 : EJMOriginalGlobalDAGData.nodes 11 ⟨862194, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨861762, by decide⟩,⟨862193, by decide⟩,⟨789341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6896_862194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6896 ⟨862194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6896
    ⟨862194, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨861762, by decide⟩,⟨862193, by decide⟩,⟨789341, by decide⟩]) unmarked_context_10_6896_862194 node_context_10_6896_862194
  intro a
  fin_cases a
  · exact context_11_27584_434745
  · exact context_11_27585_861762
  · exact context_11_27586_862193
  · exact context_11_27587_789341

theorem selected_cut_33495 : selected 8 ⟨862241, by decide⟩
    (prefixPartial 13 441408) = some ⟨13, 2, 0, 862241, 441408, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_441408_862241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441408 ⟨862241, by decide⟩ :=
  accepted_of_selected 13 441408 ⟨862241, by decide⟩ ⟨13, 2, 0, 862241, 441408, 2669, 16384⟩
    (by decide) selected_cut_33495

theorem selected_cut_33496 : selected 8 ⟨862274, by decide⟩
    (prefixPartial 13 441409) = some ⟨13, 2, 0, 862274, 441409, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_441409_862274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441409 ⟨862274, by decide⟩ :=
  accepted_of_selected 13 441409 ⟨862274, by decide⟩ ⟨13, 2, 0, 862274, 441409, 2505, 16384⟩
    (by decide) selected_cut_33496

theorem selected_cut_33497 : selected 8 ⟨862329, by decide⟩
    (prefixPartial 13 441410) = some ⟨13, 2, 0, 862329, 441410, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_441410_862329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441410 ⟨862329, by decide⟩ :=
  accepted_of_selected 13 441410 ⟨862329, by decide⟩ ⟨13, 2, 0, 862329, 441410, 1501, 16384⟩
    (by decide) selected_cut_33497

theorem selected_cut_33498 : selected 8 ⟨862336, by decide⟩
    (prefixPartial 13 441411) = some ⟨13, 2, 0, 862336, 441411, 721, 16384⟩ := by
  decide +kernel

theorem context_13_441411_862336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441411 ⟨862336, by decide⟩ :=
  accepted_of_selected 13 441411 ⟨862336, by decide⟩ ⟨13, 2, 0, 862336, 441411, 721, 16384⟩
    (by decide) selected_cut_33498

theorem unmarked_context_12_110352_862337 : frontier 9 ⟨862337, by decide⟩
    (prefixCache 12 110352) (prefixPartial 12 110352) = false := by
  decide +kernel

theorem node_context_12_110352_862337 : EJMOriginalGlobalDAGData.nodes 9 ⟨862337, by decide⟩ =
    .split (coordinate 12) (![⟨862241, by decide⟩,⟨862274, by decide⟩,⟨862329, by decide⟩,⟨862336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110352_862337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110352 ⟨862337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110352
    ⟨862337, by decide⟩ (by decide) (![⟨862241, by decide⟩,⟨862274, by decide⟩,⟨862329, by decide⟩,⟨862336, by decide⟩]) unmarked_context_12_110352_862337 node_context_12_110352_862337
  intro a
  fin_cases a
  · exact context_13_441408_862241
  · exact context_13_441409_862274
  · exact context_13_441410_862329
  · exact context_13_441411_862336

theorem selected_cut_33499 : selected 8 ⟨862400, by decide⟩
    (prefixPartial 13 441412) = some ⟨13, 2, 0, 862400, 441412, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_441412_862400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441412 ⟨862400, by decide⟩ :=
  accepted_of_selected 13 441412 ⟨862400, by decide⟩ ⟨13, 2, 0, 862400, 441412, 3205, 16384⟩
    (by decide) selected_cut_33499

theorem selected_cut_33500 : selected 8 ⟨862445, by decide⟩
    (prefixPartial 13 441413) = some ⟨13, 2, 0, 862445, 441413, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_441413_862445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441413 ⟨862445, by decide⟩ :=
  accepted_of_selected 13 441413 ⟨862445, by decide⟩ ⟨13, 2, 0, 862445, 441413, 2737, 16384⟩
    (by decide) selected_cut_33500

theorem selected_cut_33501 : selected 8 ⟨862497, by decide⟩
    (prefixPartial 13 441414) = some ⟨13, 2, 0, 862497, 441414, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_441414_862497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441414 ⟨862497, by decide⟩ :=
  accepted_of_selected 13 441414 ⟨862497, by decide⟩ ⟨13, 2, 0, 862497, 441414, 1805, 16384⟩
    (by decide) selected_cut_33501

theorem selected_cut_33502 : selected 8 ⟨862504, by decide⟩
    (prefixPartial 13 441415) = some ⟨13, 2, 0, 862504, 441415, 625, 16384⟩ := by
  decide +kernel

theorem context_13_441415_862504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441415 ⟨862504, by decide⟩ :=
  accepted_of_selected 13 441415 ⟨862504, by decide⟩ ⟨13, 2, 0, 862504, 441415, 625, 16384⟩
    (by decide) selected_cut_33502

theorem unmarked_context_12_110353_862505 : frontier 9 ⟨862505, by decide⟩
    (prefixCache 12 110353) (prefixPartial 12 110353) = false := by
  decide +kernel

theorem node_context_12_110353_862505 : EJMOriginalGlobalDAGData.nodes 9 ⟨862505, by decide⟩ =
    .split (coordinate 12) (![⟨862400, by decide⟩,⟨862445, by decide⟩,⟨862497, by decide⟩,⟨862504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110353_862505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110353 ⟨862505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110353
    ⟨862505, by decide⟩ (by decide) (![⟨862400, by decide⟩,⟨862445, by decide⟩,⟨862497, by decide⟩,⟨862504, by decide⟩]) unmarked_context_12_110353_862505 node_context_12_110353_862505
  intro a
  fin_cases a
  · exact context_13_441412_862400
  · exact context_13_441413_862445
  · exact context_13_441414_862497
  · exact context_13_441415_862504

theorem selected_cut_33503 : selected 8 ⟨862554, by decide⟩
    (prefixPartial 13 441416) = some ⟨13, 2, 0, 862554, 441416, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_441416_862554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441416 ⟨862554, by decide⟩ :=
  accepted_of_selected 13 441416 ⟨862554, by decide⟩ ⟨13, 2, 0, 862554, 441416, 2441, 16384⟩
    (by decide) selected_cut_33503

theorem selected_cut_33504 : selected 8 ⟨862600, by decide⟩
    (prefixPartial 13 441417) = some ⟨13, 2, 0, 862600, 441417, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_441417_862600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441417 ⟨862600, by decide⟩ :=
  accepted_of_selected 13 441417 ⟨862600, by decide⟩ ⟨13, 2, 0, 862600, 441417, 2421, 16384⟩
    (by decide) selected_cut_33504

theorem selected_cut_33505 : selected 8 ⟨862643, by decide⟩
    (prefixPartial 13 441418) = some ⟨13, 2, 0, 862643, 441418, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_441418_862643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441418 ⟨862643, by decide⟩ :=
  accepted_of_selected 13 441418 ⟨862643, by decide⟩ ⟨13, 2, 0, 862643, 441418, 1365, 16384⟩
    (by decide) selected_cut_33505

theorem selected_cut_33506 : selected 8 ⟨862649, by decide⟩
    (prefixPartial 13 441419) = some ⟨13, 2, 0, 862649, 441419, 629, 16384⟩ := by
  decide +kernel

theorem context_13_441419_862649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441419 ⟨862649, by decide⟩ :=
  accepted_of_selected 13 441419 ⟨862649, by decide⟩ ⟨13, 2, 0, 862649, 441419, 629, 16384⟩
    (by decide) selected_cut_33506

theorem unmarked_context_12_110354_862650 : frontier 9 ⟨862650, by decide⟩
    (prefixCache 12 110354) (prefixPartial 12 110354) = false := by
  decide +kernel

theorem node_context_12_110354_862650 : EJMOriginalGlobalDAGData.nodes 9 ⟨862650, by decide⟩ =
    .split (coordinate 12) (![⟨862554, by decide⟩,⟨862600, by decide⟩,⟨862643, by decide⟩,⟨862649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110354_862650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110354 ⟨862650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110354
    ⟨862650, by decide⟩ (by decide) (![⟨862554, by decide⟩,⟨862600, by decide⟩,⟨862643, by decide⟩,⟨862649, by decide⟩]) unmarked_context_12_110354_862650 node_context_12_110354_862650
  intro a
  fin_cases a
  · exact context_13_441416_862554
  · exact context_13_441417_862600
  · exact context_13_441418_862643
  · exact context_13_441419_862649

theorem selected_cut_33507 : selected 8 ⟨862694, by decide⟩
    (prefixPartial 13 441420) = some ⟨13, 2, 0, 862694, 441420, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_441420_862694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441420 ⟨862694, by decide⟩ :=
  accepted_of_selected 13 441420 ⟨862694, by decide⟩ ⟨13, 2, 0, 862694, 441420, 2625, 16384⟩
    (by decide) selected_cut_33507

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
