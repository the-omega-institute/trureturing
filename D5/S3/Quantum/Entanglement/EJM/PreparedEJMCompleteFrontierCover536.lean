/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover535
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_51459 : selected 10 ⟨1484335, by decide⟩
    (prefixPartial 11 281223) = some ⟨11, 2, 0, 1484335, 281223, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_281223_1484335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281223 ⟨1484335, by decide⟩ :=
  accepted_of_selected 11 281223 ⟨1484335, by decide⟩ ⟨11, 2, 0, 1484335, 281223, 2357, 262144⟩
    (by decide) selected_cut_51459

theorem unmarked_context_10_70305_1484336 : frontier 11 ⟨1484336, by decide⟩
    (prefixCache 10 70305) (prefixPartial 10 70305) = false := by
  decide +kernel

theorem node_context_10_70305_1484336 : EJMOriginalGlobalDAGData.nodes 11 ⟨1484336, by decide⟩ =
    .split (coordinate 10) (![⟨1483983, by decide⟩,⟨1468419, by decide⟩,⟨1484175, by decide⟩,⟨1484335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70305_1484336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70305 ⟨1484336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70305
    ⟨1484336, by decide⟩ (by decide) (![⟨1483983, by decide⟩,⟨1468419, by decide⟩,⟨1484175, by decide⟩,⟨1484335, by decide⟩]) unmarked_context_10_70305_1484336 node_context_10_70305_1484336
  intro a
  fin_cases a
  · exact context_11_281220_1483983
  · exact context_11_281221_1468419
  · exact context_11_281222_1484175
  · exact context_11_281223_1484335

theorem selected_cut_51460 : selected 11 ⟨1484428, by decide⟩
    (prefixPartial 10 70306) = some ⟨10, 2, 0, 1484428, 70306, 2041, 1048576⟩ := by
  decide +kernel

theorem context_10_70306_1484428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70306 ⟨1484428, by decide⟩ :=
  accepted_of_selected 10 70306 ⟨1484428, by decide⟩ ⟨10, 2, 0, 1484428, 70306, 2041, 1048576⟩
    (by decide) selected_cut_51460

theorem selected_cut_51461 : selected 11 ⟨1484549, by decide⟩
    (prefixPartial 10 70307) = some ⟨10, 2, 0, 1484549, 70307, 1217, 1048576⟩ := by
  decide +kernel

theorem context_10_70307_1484549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70307 ⟨1484549, by decide⟩ :=
  accepted_of_selected 10 70307 ⟨1484549, by decide⟩ ⟨10, 2, 0, 1484549, 70307, 1217, 1048576⟩
    (by decide) selected_cut_51461

theorem unmarked_context_9_17576_1484550 : frontier 12 ⟨1484550, by decide⟩
    (prefixCache 9 17576) (prefixPartial 9 17576) = false := by
  decide +kernel

theorem node_context_9_17576_1484550 : EJMOriginalGlobalDAGData.nodes 12 ⟨1484550, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1484336, by decide⟩,⟨1484428, by decide⟩,⟨1484549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17576_1484550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17576 ⟨1484550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17576
    ⟨1484550, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1484336, by decide⟩,⟨1484428, by decide⟩,⟨1484549, by decide⟩]) unmarked_context_9_17576_1484550 node_context_9_17576_1484550
  intro a
  fin_cases a
  · exact context_10_70304_1468246
  · exact context_10_70305_1484336
  · exact context_10_70306_1484428
  · exact context_10_70307_1484549

theorem selected_cut_51462 : selected 11 ⟨1484704, by decide⟩
    (prefixPartial 10 70308) = some ⟨10, 2, 0, 1484704, 70308, 2721, 1048576⟩ := by
  decide +kernel

theorem context_10_70308_1484704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70308 ⟨1484704, by decide⟩ :=
  accepted_of_selected 10 70308 ⟨1484704, by decide⟩ ⟨10, 2, 0, 1484704, 70308, 2721, 1048576⟩
    (by decide) selected_cut_51462

theorem selected_cut_51463 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70309) = some ⟨10, 1, 0, 1468874, 70309, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70309_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70309 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70309 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70309, 1, 1048576⟩
    (by decide) selected_cut_51463

theorem selected_cut_51464 : selected 11 ⟨1484813, by decide⟩
    (prefixPartial 10 70310) = some ⟨10, 2, 0, 1484813, 70310, 1365, 1048576⟩ := by
  decide +kernel

theorem context_10_70310_1484813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70310 ⟨1484813, by decide⟩ :=
  accepted_of_selected 10 70310 ⟨1484813, by decide⟩ ⟨10, 2, 0, 1484813, 70310, 1365, 1048576⟩
    (by decide) selected_cut_51464

theorem selected_cut_51465 : selected 11 ⟨1484884, by decide⟩
    (prefixPartial 10 70311) = some ⟨10, 2, 0, 1484884, 70311, 609, 1048576⟩ := by
  decide +kernel

theorem context_10_70311_1484884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70311 ⟨1484884, by decide⟩ :=
  accepted_of_selected 10 70311 ⟨1484884, by decide⟩ ⟨10, 2, 0, 1484884, 70311, 609, 1048576⟩
    (by decide) selected_cut_51465

theorem unmarked_context_9_17577_1484885 : frontier 12 ⟨1484885, by decide⟩
    (prefixCache 9 17577) (prefixPartial 9 17577) = false := by
  decide +kernel

theorem node_context_9_17577_1484885 : EJMOriginalGlobalDAGData.nodes 12 ⟨1484885, by decide⟩ =
    .split (coordinate 9) (![⟨1484704, by decide⟩,⟨1468874, by decide⟩,⟨1484813, by decide⟩,⟨1484884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17577_1484885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17577 ⟨1484885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17577
    ⟨1484885, by decide⟩ (by decide) (![⟨1484704, by decide⟩,⟨1468874, by decide⟩,⟨1484813, by decide⟩,⟨1484884, by decide⟩]) unmarked_context_9_17577_1484885 node_context_9_17577_1484885
  intro a
  fin_cases a
  · exact context_10_70308_1484704
  · exact context_10_70309_1468874
  · exact context_10_70310_1484813
  · exact context_10_70311_1484884

theorem selected_cut_51466 : selected 12 ⟨1485022, by decide⟩
    (prefixPartial 9 17578) = some ⟨9, 2, 0, 1485022, 17578, 1381, 4194304⟩ := by
  decide +kernel

theorem context_9_17578_1485022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17578 ⟨1485022, by decide⟩ :=
  accepted_of_selected 9 17578 ⟨1485022, by decide⟩ ⟨9, 2, 0, 1485022, 17578, 1381, 4194304⟩
    (by decide) selected_cut_51466

theorem selected_cut_51467 : selected 12 ⟨1485072, by decide⟩
    (prefixPartial 9 17579) = some ⟨9, 2, 0, 1485072, 17579, 397, 4194304⟩ := by
  decide +kernel

theorem context_9_17579_1485072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17579 ⟨1485072, by decide⟩ :=
  accepted_of_selected 9 17579 ⟨1485072, by decide⟩ ⟨9, 2, 0, 1485072, 17579, 397, 4194304⟩
    (by decide) selected_cut_51467

theorem unmarked_context_8_4394_1485073 : frontier 13 ⟨1485073, by decide⟩
    (prefixCache 8 4394) (prefixPartial 8 4394) = false := by
  decide +kernel

theorem node_context_8_4394_1485073 : EJMOriginalGlobalDAGData.nodes 13 ⟨1485073, by decide⟩ =
    .split (coordinate 8) (![⟨1484550, by decide⟩,⟨1484885, by decide⟩,⟨1485022, by decide⟩,⟨1485072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4394_1485073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4394 ⟨1485073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4394
    ⟨1485073, by decide⟩ (by decide) (![⟨1484550, by decide⟩,⟨1484885, by decide⟩,⟨1485022, by decide⟩,⟨1485072, by decide⟩]) unmarked_context_8_4394_1485073 node_context_8_4394_1485073
  intro a
  fin_cases a
  · exact context_9_17576_1484550
  · exact context_9_17577_1484885
  · exact context_9_17578_1485022
  · exact context_9_17579_1485072

theorem selected_cut_51468 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70320) = some ⟨10, 1, 0, 1468246, 70320, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70320_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70320 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70320 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70320, 1, 1048576⟩
    (by decide) selected_cut_51468

theorem selected_cut_51469 : selected 10 ⟨1485155, by decide⟩
    (prefixPartial 11 281284) = some ⟨11, 2, 0, 1485155, 281284, 3285, 262144⟩ := by
  decide +kernel

theorem context_11_281284_1485155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281284 ⟨1485155, by decide⟩ :=
  accepted_of_selected 11 281284 ⟨1485155, by decide⟩ ⟨11, 2, 0, 1485155, 281284, 3285, 262144⟩
    (by decide) selected_cut_51469

theorem selected_cut_51470 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 281285) = some ⟨11, 1, 0, 1468419, 281285, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281285_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281285 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 281285 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 281285, 1, 262144⟩
    (by decide) selected_cut_51470

theorem selected_cut_51471 : selected 10 ⟨1485260, by decide⟩
    (prefixPartial 11 281286) = some ⟨11, 2, 0, 1485260, 281286, 3365, 262144⟩ := by
  decide +kernel

theorem context_11_281286_1485260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281286 ⟨1485260, by decide⟩ :=
  accepted_of_selected 11 281286 ⟨1485260, by decide⟩ ⟨11, 2, 0, 1485260, 281286, 3365, 262144⟩
    (by decide) selected_cut_51471

theorem selected_cut_51472 : selected 10 ⟨1485352, by decide⟩
    (prefixPartial 11 281287) = some ⟨11, 2, 0, 1485352, 281287, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_281287_1485352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281287 ⟨1485352, by decide⟩ :=
  accepted_of_selected 11 281287 ⟨1485352, by decide⟩ ⟨11, 2, 0, 1485352, 281287, 2541, 262144⟩
    (by decide) selected_cut_51472

theorem unmarked_context_10_70321_1485353 : frontier 11 ⟨1485353, by decide⟩
    (prefixCache 10 70321) (prefixPartial 10 70321) = false := by
  decide +kernel

theorem node_context_10_70321_1485353 : EJMOriginalGlobalDAGData.nodes 11 ⟨1485353, by decide⟩ =
    .split (coordinate 10) (![⟨1485155, by decide⟩,⟨1468419, by decide⟩,⟨1485260, by decide⟩,⟨1485352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70321_1485353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70321 ⟨1485353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70321
    ⟨1485353, by decide⟩ (by decide) (![⟨1485155, by decide⟩,⟨1468419, by decide⟩,⟨1485260, by decide⟩,⟨1485352, by decide⟩]) unmarked_context_10_70321_1485353 node_context_10_70321_1485353
  intro a
  fin_cases a
  · exact context_11_281284_1485155
  · exact context_11_281285_1468419
  · exact context_11_281286_1485260
  · exact context_11_281287_1485352

theorem selected_cut_51473 : selected 10 ⟨1485405, by decide⟩
    (prefixPartial 11 281288) = some ⟨11, 2, 0, 1485405, 281288, 2537, 262144⟩ := by
  decide +kernel

theorem context_11_281288_1485405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281288 ⟨1485405, by decide⟩ :=
  accepted_of_selected 11 281288 ⟨1485405, by decide⟩ ⟨11, 2, 0, 1485405, 281288, 2537, 262144⟩
    (by decide) selected_cut_51473

theorem selected_cut_51474 : selected 10 ⟨1485429, by decide⟩
    (prefixPartial 11 281289) = some ⟨11, 2, 0, 1485429, 281289, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_281289_1485429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281289 ⟨1485429, by decide⟩ :=
  accepted_of_selected 11 281289 ⟨1485429, by decide⟩ ⟨11, 2, 0, 1485429, 281289, 1089, 262144⟩
    (by decide) selected_cut_51474

theorem selected_cut_51475 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 281290) = some ⟨11, 1, 0, 1468743, 281290, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281290_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281290 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 281290 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 281290, 1, 262144⟩
    (by decide) selected_cut_51475

theorem selected_cut_51476 : selected 10 ⟨1485452, by decide⟩
    (prefixPartial 11 281291) = some ⟨11, 2, 0, 1485452, 281291, 1229, 262144⟩ := by
  decide +kernel

theorem context_11_281291_1485452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281291 ⟨1485452, by decide⟩ :=
  accepted_of_selected 11 281291 ⟨1485452, by decide⟩ ⟨11, 2, 0, 1485452, 281291, 1229, 262144⟩
    (by decide) selected_cut_51476

theorem unmarked_context_10_70322_1485453 : frontier 11 ⟨1485453, by decide⟩
    (prefixCache 10 70322) (prefixPartial 10 70322) = false := by
  decide +kernel

theorem node_context_10_70322_1485453 : EJMOriginalGlobalDAGData.nodes 11 ⟨1485453, by decide⟩ =
    .split (coordinate 10) (![⟨1485405, by decide⟩,⟨1485429, by decide⟩,⟨1468743, by decide⟩,⟨1485452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70322_1485453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70322 ⟨1485453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70322
    ⟨1485453, by decide⟩ (by decide) (![⟨1485405, by decide⟩,⟨1485429, by decide⟩,⟨1468743, by decide⟩,⟨1485452, by decide⟩]) unmarked_context_10_70322_1485453 node_context_10_70322_1485453
  intro a
  fin_cases a
  · exact context_11_281288_1485405
  · exact context_11_281289_1485429
  · exact context_11_281290_1468743
  · exact context_11_281291_1485452

theorem selected_cut_51477 : selected 10 ⟨1485513, by decide⟩
    (prefixPartial 11 281292) = some ⟨11, 2, 0, 1485513, 281292, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_281292_1485513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281292 ⟨1485513, by decide⟩ :=
  accepted_of_selected 11 281292 ⟨1485513, by decide⟩ ⟨11, 2, 0, 1485513, 281292, 2853, 262144⟩
    (by decide) selected_cut_51477

theorem selected_cut_51478 : selected 10 ⟨1485544, by decide⟩
    (prefixPartial 11 281293) = some ⟨11, 2, 0, 1485544, 281293, 1349, 262144⟩ := by
  decide +kernel

theorem context_11_281293_1485544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281293 ⟨1485544, by decide⟩ :=
  accepted_of_selected 11 281293 ⟨1485544, by decide⟩ ⟨11, 2, 0, 1485544, 281293, 1349, 262144⟩
    (by decide) selected_cut_51478

theorem selected_cut_51479 : selected 10 ⟨1485570, by decide⟩
    (prefixPartial 11 281294) = some ⟨11, 2, 0, 1485570, 281294, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_281294_1485570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281294 ⟨1485570, by decide⟩ :=
  accepted_of_selected 11 281294 ⟨1485570, by decide⟩ ⟨11, 2, 0, 1485570, 281294, 1293, 262144⟩
    (by decide) selected_cut_51479

theorem selected_cut_51480 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 281295) = some ⟨11, 1, 0, 1470044, 281295, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281295_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281295 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 281295 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 281295, 1, 262144⟩
    (by decide) selected_cut_51480

theorem unmarked_context_10_70323_1485571 : frontier 11 ⟨1485571, by decide⟩
    (prefixCache 10 70323) (prefixPartial 10 70323) = false := by
  decide +kernel

theorem node_context_10_70323_1485571 : EJMOriginalGlobalDAGData.nodes 11 ⟨1485571, by decide⟩ =
    .split (coordinate 10) (![⟨1485513, by decide⟩,⟨1485544, by decide⟩,⟨1485570, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70323_1485571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70323 ⟨1485571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70323
    ⟨1485571, by decide⟩ (by decide) (![⟨1485513, by decide⟩,⟨1485544, by decide⟩,⟨1485570, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70323_1485571 node_context_10_70323_1485571
  intro a
  fin_cases a
  · exact context_11_281292_1485513
  · exact context_11_281293_1485544
  · exact context_11_281294_1485570
  · exact context_11_281295_1470044

theorem unmarked_context_9_17580_1485572 : frontier 12 ⟨1485572, by decide⟩
    (prefixCache 9 17580) (prefixPartial 9 17580) = false := by
  decide +kernel

theorem node_context_9_17580_1485572 : EJMOriginalGlobalDAGData.nodes 12 ⟨1485572, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1485353, by decide⟩,⟨1485453, by decide⟩,⟨1485571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17580_1485572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17580 ⟨1485572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17580
    ⟨1485572, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1485353, by decide⟩,⟨1485453, by decide⟩,⟨1485571, by decide⟩]) unmarked_context_9_17580_1485572 node_context_9_17580_1485572
  intro a
  fin_cases a
  · exact context_10_70320_1468246
  · exact context_10_70321_1485353
  · exact context_10_70322_1485453
  · exact context_10_70323_1485571

theorem selected_cut_51481 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 281296) = some ⟨11, 1, 0, 434745, 281296, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281296_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281296 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 281296 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 281296, 1, 262144⟩
    (by decide) selected_cut_51481

theorem selected_cut_51482 : selected 10 ⟨1485624, by decide⟩
    (prefixPartial 11 281297) = some ⟨11, 2, 0, 1485624, 281297, 2869, 262144⟩ := by
  decide +kernel

theorem context_11_281297_1485624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281297 ⟨1485624, by decide⟩ :=
  accepted_of_selected 11 281297 ⟨1485624, by decide⟩ ⟨11, 2, 0, 1485624, 281297, 2869, 262144⟩
    (by decide) selected_cut_51482

theorem selected_cut_51483 : selected 10 ⟨1485647, by decide⟩
    (prefixPartial 11 281298) = some ⟨11, 2, 0, 1485647, 281298, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_281298_1485647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281298 ⟨1485647, by decide⟩ :=
  accepted_of_selected 11 281298 ⟨1485647, by decide⟩ ⟨11, 2, 0, 1485647, 281298, 1801, 262144⟩
    (by decide) selected_cut_51483

theorem selected_cut_51484 : selected 10 ⟨1485675, by decide⟩
    (prefixPartial 11 281299) = some ⟨11, 2, 0, 1485675, 281299, 1781, 262144⟩ := by
  decide +kernel

theorem context_11_281299_1485675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281299 ⟨1485675, by decide⟩ :=
  accepted_of_selected 11 281299 ⟨1485675, by decide⟩ ⟨11, 2, 0, 1485675, 281299, 1781, 262144⟩
    (by decide) selected_cut_51484

theorem unmarked_context_10_70324_1485676 : frontier 11 ⟨1485676, by decide⟩
    (prefixCache 10 70324) (prefixPartial 10 70324) = false := by
  decide +kernel

theorem node_context_10_70324_1485676 : EJMOriginalGlobalDAGData.nodes 11 ⟨1485676, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1485624, by decide⟩,⟨1485647, by decide⟩,⟨1485675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70324_1485676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70324 ⟨1485676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70324
    ⟨1485676, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1485624, by decide⟩,⟨1485647, by decide⟩,⟨1485675, by decide⟩]) unmarked_context_10_70324_1485676 node_context_10_70324_1485676
  intro a
  fin_cases a
  · exact context_11_281296_434745
  · exact context_11_281297_1485624
  · exact context_11_281298_1485647
  · exact context_11_281299_1485675

theorem selected_cut_51485 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70325) = some ⟨10, 1, 0, 1468874, 70325, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70325_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70325 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70325 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70325, 1, 1048576⟩
    (by decide) selected_cut_51485

theorem selected_cut_51486 : selected 10 ⟨1485711, by decide⟩
    (prefixPartial 11 281304) = some ⟨11, 2, 0, 1485711, 281304, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_281304_1485711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281304 ⟨1485711, by decide⟩ :=
  accepted_of_selected 11 281304 ⟨1485711, by decide⟩ ⟨11, 2, 0, 1485711, 281304, 1861, 262144⟩
    (by decide) selected_cut_51486

theorem selected_cut_51487 : selected 10 ⟨1485758, by decide⟩
    (prefixPartial 11 281305) = some ⟨11, 2, 0, 1485758, 281305, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_281305_1485758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281305 ⟨1485758, by decide⟩ :=
  accepted_of_selected 11 281305 ⟨1485758, by decide⟩ ⟨11, 2, 0, 1485758, 281305, 2341, 262144⟩
    (by decide) selected_cut_51487

theorem selected_cut_51488 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 281306) = some ⟨11, 1, 0, 1468743, 281306, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281306_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281306 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 281306 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 281306, 1, 262144⟩
    (by decide) selected_cut_51488

theorem selected_cut_51489 : selected 10 ⟨1485779, by decide⟩
    (prefixPartial 11 281307) = some ⟨11, 2, 0, 1485779, 281307, 1545, 262144⟩ := by
  decide +kernel

theorem context_11_281307_1485779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281307 ⟨1485779, by decide⟩ :=
  accepted_of_selected 11 281307 ⟨1485779, by decide⟩ ⟨11, 2, 0, 1485779, 281307, 1545, 262144⟩
    (by decide) selected_cut_51489

theorem unmarked_context_10_70326_1485780 : frontier 11 ⟨1485780, by decide⟩
    (prefixCache 10 70326) (prefixPartial 10 70326) = false := by
  decide +kernel

theorem node_context_10_70326_1485780 : EJMOriginalGlobalDAGData.nodes 11 ⟨1485780, by decide⟩ =
    .split (coordinate 10) (![⟨1485711, by decide⟩,⟨1485758, by decide⟩,⟨1468743, by decide⟩,⟨1485779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70326_1485780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70326 ⟨1485780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70326
    ⟨1485780, by decide⟩ (by decide) (![⟨1485711, by decide⟩,⟨1485758, by decide⟩,⟨1468743, by decide⟩,⟨1485779, by decide⟩]) unmarked_context_10_70326_1485780 node_context_10_70326_1485780
  intro a
  fin_cases a
  · exact context_11_281304_1485711
  · exact context_11_281305_1485758
  · exact context_11_281306_1468743
  · exact context_11_281307_1485779

theorem selected_cut_51490 : selected 10 ⟨1485819, by decide⟩
    (prefixPartial 11 281308) = some ⟨11, 2, 0, 1485819, 281308, 1765, 262144⟩ := by
  decide +kernel

theorem context_11_281308_1485819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281308 ⟨1485819, by decide⟩ :=
  accepted_of_selected 11 281308 ⟨1485819, by decide⟩ ⟨11, 2, 0, 1485819, 281308, 1765, 262144⟩
    (by decide) selected_cut_51490

theorem selected_cut_51491 : selected 10 ⟨1485860, by decide⟩
    (prefixPartial 11 281309) = some ⟨11, 2, 0, 1485860, 281309, 2269, 262144⟩ := by
  decide +kernel

theorem context_11_281309_1485860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281309 ⟨1485860, by decide⟩ :=
  accepted_of_selected 11 281309 ⟨1485860, by decide⟩ ⟨11, 2, 0, 1485860, 281309, 2269, 262144⟩
    (by decide) selected_cut_51491

theorem selected_cut_51492 : selected 10 ⟨1485888, by decide⟩
    (prefixPartial 11 281310) = some ⟨11, 2, 0, 1485888, 281310, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_281310_1485888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281310 ⟨1485888, by decide⟩ :=
  accepted_of_selected 11 281310 ⟨1485888, by decide⟩ ⟨11, 2, 0, 1485888, 281310, 1413, 262144⟩
    (by decide) selected_cut_51492

theorem selected_cut_51493 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 281311) = some ⟨11, 1, 0, 1470044, 281311, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281311_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281311 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 281311 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 281311, 1, 262144⟩
    (by decide) selected_cut_51493

theorem unmarked_context_10_70327_1485889 : frontier 11 ⟨1485889, by decide⟩
    (prefixCache 10 70327) (prefixPartial 10 70327) = false := by
  decide +kernel

theorem node_context_10_70327_1485889 : EJMOriginalGlobalDAGData.nodes 11 ⟨1485889, by decide⟩ =
    .split (coordinate 10) (![⟨1485819, by decide⟩,⟨1485860, by decide⟩,⟨1485888, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70327_1485889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70327 ⟨1485889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70327
    ⟨1485889, by decide⟩ (by decide) (![⟨1485819, by decide⟩,⟨1485860, by decide⟩,⟨1485888, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70327_1485889 node_context_10_70327_1485889
  intro a
  fin_cases a
  · exact context_11_281308_1485819
  · exact context_11_281309_1485860
  · exact context_11_281310_1485888
  · exact context_11_281311_1470044

theorem unmarked_context_9_17581_1485890 : frontier 12 ⟨1485890, by decide⟩
    (prefixCache 9 17581) (prefixPartial 9 17581) = false := by
  decide +kernel

theorem node_context_9_17581_1485890 : EJMOriginalGlobalDAGData.nodes 12 ⟨1485890, by decide⟩ =
    .split (coordinate 9) (![⟨1485676, by decide⟩,⟨1468874, by decide⟩,⟨1485780, by decide⟩,⟨1485889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17581_1485890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17581 ⟨1485890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17581
    ⟨1485890, by decide⟩ (by decide) (![⟨1485676, by decide⟩,⟨1468874, by decide⟩,⟨1485780, by decide⟩,⟨1485889, by decide⟩]) unmarked_context_9_17581_1485890 node_context_9_17581_1485890
  intro a
  fin_cases a
  · exact context_10_70324_1485676
  · exact context_10_70325_1468874
  · exact context_10_70326_1485780
  · exact context_10_70327_1485889

theorem selected_cut_51494 : selected 11 ⟨1485961, by decide⟩
    (prefixPartial 10 70328) = some ⟨10, 2, 0, 1485961, 70328, 3993, 1048576⟩ := by
  decide +kernel

theorem context_10_70328_1485961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70328 ⟨1485961, by decide⟩ :=
  accepted_of_selected 10 70328 ⟨1485961, by decide⟩ ⟨10, 2, 0, 1485961, 70328, 3993, 1048576⟩
    (by decide) selected_cut_51494

theorem selected_cut_51495 : selected 10 ⟨1485984, by decide⟩
    (prefixPartial 11 281316) = some ⟨11, 2, 0, 1485984, 281316, 1349, 262144⟩ := by
  decide +kernel

theorem context_11_281316_1485984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281316 ⟨1485984, by decide⟩ :=
  accepted_of_selected 11 281316 ⟨1485984, by decide⟩ ⟨11, 2, 0, 1485984, 281316, 1349, 262144⟩
    (by decide) selected_cut_51495

theorem selected_cut_51496 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 281317) = some ⟨11, 1, 0, 1468419, 281317, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281317_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281317 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 281317 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 281317, 1, 262144⟩
    (by decide) selected_cut_51496

theorem selected_cut_51497 : selected 10 ⟨1486021, by decide⟩
    (prefixPartial 11 281318) = some ⟨11, 2, 0, 1486021, 281318, 1793, 262144⟩ := by
  decide +kernel

theorem context_11_281318_1486021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281318 ⟨1486021, by decide⟩ :=
  accepted_of_selected 11 281318 ⟨1486021, by decide⟩ ⟨11, 2, 0, 1486021, 281318, 1793, 262144⟩
    (by decide) selected_cut_51497

theorem selected_cut_51498 : selected 10 ⟨1486044, by decide⟩
    (prefixPartial 11 281319) = some ⟨11, 2, 0, 1486044, 281319, 1077, 262144⟩ := by
  decide +kernel

theorem context_11_281319_1486044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281319 ⟨1486044, by decide⟩ :=
  accepted_of_selected 11 281319 ⟨1486044, by decide⟩ ⟨11, 2, 0, 1486044, 281319, 1077, 262144⟩
    (by decide) selected_cut_51498

theorem unmarked_context_10_70329_1486045 : frontier 11 ⟨1486045, by decide⟩
    (prefixCache 10 70329) (prefixPartial 10 70329) = false := by
  decide +kernel

theorem node_context_10_70329_1486045 : EJMOriginalGlobalDAGData.nodes 11 ⟨1486045, by decide⟩ =
    .split (coordinate 10) (![⟨1485984, by decide⟩,⟨1468419, by decide⟩,⟨1486021, by decide⟩,⟨1486044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70329_1486045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70329 ⟨1486045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70329
    ⟨1486045, by decide⟩ (by decide) (![⟨1485984, by decide⟩,⟨1468419, by decide⟩,⟨1486021, by decide⟩,⟨1486044, by decide⟩]) unmarked_context_10_70329_1486045 node_context_10_70329_1486045
  intro a
  fin_cases a
  · exact context_11_281316_1485984
  · exact context_11_281317_1468419
  · exact context_11_281318_1486021
  · exact context_11_281319_1486044

theorem selected_cut_51499 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70330) = some ⟨10, 1, 0, 1469103, 70330, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70330_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70330 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70330 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70330, 1, 1048576⟩
    (by decide) selected_cut_51499

theorem selected_cut_51500 : selected 11 ⟨1486103, by decide⟩
    (prefixPartial 10 70331) = some ⟨10, 2, 0, 1486103, 70331, 2945, 1048576⟩ := by
  decide +kernel

theorem context_10_70331_1486103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70331 ⟨1486103, by decide⟩ :=
  accepted_of_selected 10 70331 ⟨1486103, by decide⟩ ⟨10, 2, 0, 1486103, 70331, 2945, 1048576⟩
    (by decide) selected_cut_51500

theorem unmarked_context_9_17582_1486104 : frontier 12 ⟨1486104, by decide⟩
    (prefixCache 9 17582) (prefixPartial 9 17582) = false := by
  decide +kernel

theorem node_context_9_17582_1486104 : EJMOriginalGlobalDAGData.nodes 12 ⟨1486104, by decide⟩ =
    .split (coordinate 9) (![⟨1485961, by decide⟩,⟨1486045, by decide⟩,⟨1469103, by decide⟩,⟨1486103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17582_1486104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17582 ⟨1486104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17582
    ⟨1486104, by decide⟩ (by decide) (![⟨1485961, by decide⟩,⟨1486045, by decide⟩,⟨1469103, by decide⟩,⟨1486103, by decide⟩]) unmarked_context_9_17582_1486104 node_context_9_17582_1486104
  intro a
  fin_cases a
  · exact context_10_70328_1485961
  · exact context_10_70329_1486045
  · exact context_10_70330_1469103
  · exact context_10_70331_1486103

theorem selected_cut_51501 : selected 12 ⟨1486185, by decide⟩
    (prefixPartial 9 17583) = some ⟨9, 2, 0, 1486185, 17583, 3385, 4194304⟩ := by
  decide +kernel

theorem context_9_17583_1486185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17583 ⟨1486185, by decide⟩ :=
  accepted_of_selected 9 17583 ⟨1486185, by decide⟩ ⟨9, 2, 0, 1486185, 17583, 3385, 4194304⟩
    (by decide) selected_cut_51501

theorem unmarked_context_8_4395_1486186 : frontier 13 ⟨1486186, by decide⟩
    (prefixCache 8 4395) (prefixPartial 8 4395) = false := by
  decide +kernel

theorem node_context_8_4395_1486186 : EJMOriginalGlobalDAGData.nodes 13 ⟨1486186, by decide⟩ =
    .split (coordinate 8) (![⟨1485572, by decide⟩,⟨1485890, by decide⟩,⟨1486104, by decide⟩,⟨1486185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4395_1486186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4395 ⟨1486186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4395
    ⟨1486186, by decide⟩ (by decide) (![⟨1485572, by decide⟩,⟨1485890, by decide⟩,⟨1486104, by decide⟩,⟨1486185, by decide⟩]) unmarked_context_8_4395_1486186 node_context_8_4395_1486186
  intro a
  fin_cases a
  · exact context_9_17580_1485572
  · exact context_9_17581_1485890
  · exact context_9_17582_1486104
  · exact context_9_17583_1486185

theorem unmarked_context_7_1098_1486187 : frontier 14 ⟨1486187, by decide⟩
    (prefixCache 7 1098) (prefixPartial 7 1098) = false := by
  decide +kernel

theorem node_context_7_1098_1486187 : EJMOriginalGlobalDAGData.nodes 14 ⟨1486187, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨1485073, by decide⟩,⟨1486186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1098_1486187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1098 ⟨1486187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1098
    ⟨1486187, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨1485073, by decide⟩,⟨1486186, by decide⟩]) unmarked_context_7_1098_1486187 node_context_7_1098_1486187
  intro a
  fin_cases a
  · exact context_8_4392_14300
  · exact context_8_4393_14300
  · exact context_8_4394_1485073
  · exact context_8_4395_1486186

theorem selected_cut_51502 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4396) = some ⟨8, 1, 0, 14300, 4396, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4396_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4396 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4396 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4396, 1, 16777216⟩
    (by decide) selected_cut_51502

theorem selected_cut_51503 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4397) = some ⟨8, 1, 0, 14300, 4397, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4397_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4397 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4397 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4397, 1, 16777216⟩
    (by decide) selected_cut_51503

theorem selected_cut_51504 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4398) = some ⟨8, 1, 0, 14300, 4398, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4398_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4398 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4398 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4398, 1, 16777216⟩
    (by decide) selected_cut_51504

theorem selected_cut_51505 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70384) = some ⟨10, 1, 0, 1468246, 70384, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70384_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70384 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70384 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70384, 1, 1048576⟩
    (by decide) selected_cut_51505

theorem selected_cut_51506 : selected 10 ⟨1486307, by decide⟩
    (prefixPartial 11 281540) = some ⟨11, 2, 0, 1486307, 281540, 3421, 262144⟩ := by
  decide +kernel

theorem context_11_281540_1486307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281540 ⟨1486307, by decide⟩ :=
  accepted_of_selected 11 281540 ⟨1486307, by decide⟩ ⟨11, 2, 0, 1486307, 281540, 3421, 262144⟩
    (by decide) selected_cut_51506

theorem selected_cut_51507 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 281541) = some ⟨11, 1, 0, 1468419, 281541, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281541_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281541 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 281541 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 281541, 1, 262144⟩
    (by decide) selected_cut_51507

theorem selected_cut_51508 : selected 10 ⟨1486463, by decide⟩
    (prefixPartial 11 281542) = some ⟨11, 2, 0, 1486463, 281542, 3013, 262144⟩ := by
  decide +kernel

theorem context_11_281542_1486463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281542 ⟨1486463, by decide⟩ :=
  accepted_of_selected 11 281542 ⟨1486463, by decide⟩ ⟨11, 2, 0, 1486463, 281542, 3013, 262144⟩
    (by decide) selected_cut_51508

theorem selected_cut_51509 : selected 10 ⟨1486510, by decide⟩
    (prefixPartial 11 281543) = some ⟨11, 2, 0, 1486510, 281543, 1417, 262144⟩ := by
  decide +kernel

theorem context_11_281543_1486510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281543 ⟨1486510, by decide⟩ :=
  accepted_of_selected 11 281543 ⟨1486510, by decide⟩ ⟨11, 2, 0, 1486510, 281543, 1417, 262144⟩
    (by decide) selected_cut_51509

theorem unmarked_context_10_70385_1486511 : frontier 11 ⟨1486511, by decide⟩
    (prefixCache 10 70385) (prefixPartial 10 70385) = false := by
  decide +kernel

theorem node_context_10_70385_1486511 : EJMOriginalGlobalDAGData.nodes 11 ⟨1486511, by decide⟩ =
    .split (coordinate 10) (![⟨1486307, by decide⟩,⟨1468419, by decide⟩,⟨1486463, by decide⟩,⟨1486510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70385_1486511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70385 ⟨1486511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70385
    ⟨1486511, by decide⟩ (by decide) (![⟨1486307, by decide⟩,⟨1468419, by decide⟩,⟨1486463, by decide⟩,⟨1486510, by decide⟩]) unmarked_context_10_70385_1486511 node_context_10_70385_1486511
  intro a
  fin_cases a
  · exact context_11_281540_1486307
  · exact context_11_281541_1468419
  · exact context_11_281542_1486463
  · exact context_11_281543_1486510

theorem selected_cut_51510 : selected 11 ⟨1486630, by decide⟩
    (prefixPartial 10 70386) = some ⟨10, 2, 0, 1486630, 70386, 3105, 1048576⟩ := by
  decide +kernel

theorem context_10_70386_1486630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70386 ⟨1486630, by decide⟩ :=
  accepted_of_selected 10 70386 ⟨1486630, by decide⟩ ⟨10, 2, 0, 1486630, 70386, 3105, 1048576⟩
    (by decide) selected_cut_51510

theorem selected_cut_51511 : selected 11 ⟨1486633, by decide⟩
    (prefixPartial 10 70387) = some ⟨10, 2, 0, 1486633, 70387, 17, 1048576⟩ := by
  decide +kernel

theorem context_10_70387_1486633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70387 ⟨1486633, by decide⟩ :=
  accepted_of_selected 10 70387 ⟨1486633, by decide⟩ ⟨10, 2, 0, 1486633, 70387, 17, 1048576⟩
    (by decide) selected_cut_51511

theorem unmarked_context_9_17596_1486634 : frontier 12 ⟨1486634, by decide⟩
    (prefixCache 9 17596) (prefixPartial 9 17596) = false := by
  decide +kernel

theorem node_context_9_17596_1486634 : EJMOriginalGlobalDAGData.nodes 12 ⟨1486634, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1486511, by decide⟩,⟨1486630, by decide⟩,⟨1486633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17596_1486634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17596 ⟨1486634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17596
    ⟨1486634, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1486511, by decide⟩,⟨1486630, by decide⟩,⟨1486633, by decide⟩]) unmarked_context_9_17596_1486634 node_context_9_17596_1486634
  intro a
  fin_cases a
  · exact context_10_70384_1468246
  · exact context_10_70385_1486511
  · exact context_10_70386_1486630
  · exact context_10_70387_1486633

theorem selected_cut_51512 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 281552) = some ⟨11, 1, 0, 434745, 281552, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281552_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281552 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 281552 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 281552, 1, 262144⟩
    (by decide) selected_cut_51512

theorem selected_cut_51513 : selected 10 ⟨1486725, by decide⟩
    (prefixPartial 11 281553) = some ⟨11, 2, 0, 1486725, 281553, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_281553_1486725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281553 ⟨1486725, by decide⟩ :=
  accepted_of_selected 11 281553 ⟨1486725, by decide⟩ ⟨11, 2, 0, 1486725, 281553, 2897, 262144⟩
    (by decide) selected_cut_51513

theorem selected_cut_51514 : selected 10 ⟨1486768, by decide⟩
    (prefixPartial 11 281554) = some ⟨11, 2, 0, 1486768, 281554, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_281554_1486768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281554 ⟨1486768, by decide⟩ :=
  accepted_of_selected 11 281554 ⟨1486768, by decide⟩ ⟨11, 2, 0, 1486768, 281554, 1697, 262144⟩
    (by decide) selected_cut_51514

theorem selected_cut_51515 : selected 10 ⟨1486791, by decide⟩
    (prefixPartial 11 281555) = some ⟨11, 2, 0, 1486791, 281555, 833, 262144⟩ := by
  decide +kernel

theorem context_11_281555_1486791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281555 ⟨1486791, by decide⟩ :=
  accepted_of_selected 11 281555 ⟨1486791, by decide⟩ ⟨11, 2, 0, 1486791, 281555, 833, 262144⟩
    (by decide) selected_cut_51515

theorem unmarked_context_10_70388_1486792 : frontier 11 ⟨1486792, by decide⟩
    (prefixCache 10 70388) (prefixPartial 10 70388) = false := by
  decide +kernel

theorem node_context_10_70388_1486792 : EJMOriginalGlobalDAGData.nodes 11 ⟨1486792, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1486725, by decide⟩,⟨1486768, by decide⟩,⟨1486791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70388_1486792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70388 ⟨1486792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70388
    ⟨1486792, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1486725, by decide⟩,⟨1486768, by decide⟩,⟨1486791, by decide⟩]) unmarked_context_10_70388_1486792 node_context_10_70388_1486792
  intro a
  fin_cases a
  · exact context_11_281552_434745
  · exact context_11_281553_1486725
  · exact context_11_281554_1486768
  · exact context_11_281555_1486791

theorem selected_cut_51516 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70389) = some ⟨10, 1, 0, 1468874, 70389, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70389_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70389 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70389 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70389, 1, 1048576⟩
    (by decide) selected_cut_51516

theorem selected_cut_51517 : selected 11 ⟨1486955, by decide⟩
    (prefixPartial 10 70390) = some ⟨10, 2, 0, 1486955, 70390, 3613, 1048576⟩ := by
  decide +kernel

theorem context_10_70390_1486955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70390 ⟨1486955, by decide⟩ :=
  accepted_of_selected 10 70390 ⟨1486955, by decide⟩ ⟨10, 2, 0, 1486955, 70390, 3613, 1048576⟩
    (by decide) selected_cut_51517

theorem selected_cut_51518 : selected 11 ⟨1487007, by decide⟩
    (prefixPartial 10 70391) = some ⟨10, 2, 0, 1487007, 70391, 1617, 1048576⟩ := by
  decide +kernel

theorem context_10_70391_1487007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70391 ⟨1487007, by decide⟩ :=
  accepted_of_selected 10 70391 ⟨1487007, by decide⟩ ⟨10, 2, 0, 1487007, 70391, 1617, 1048576⟩
    (by decide) selected_cut_51518

theorem unmarked_context_9_17597_1487008 : frontier 12 ⟨1487008, by decide⟩
    (prefixCache 9 17597) (prefixPartial 9 17597) = false := by
  decide +kernel

theorem node_context_9_17597_1487008 : EJMOriginalGlobalDAGData.nodes 12 ⟨1487008, by decide⟩ =
    .split (coordinate 9) (![⟨1486792, by decide⟩,⟨1468874, by decide⟩,⟨1486955, by decide⟩,⟨1487007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17597_1487008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17597 ⟨1487008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17597
    ⟨1487008, by decide⟩ (by decide) (![⟨1486792, by decide⟩,⟨1468874, by decide⟩,⟨1486955, by decide⟩,⟨1487007, by decide⟩]) unmarked_context_9_17597_1487008 node_context_9_17597_1487008
  intro a
  fin_cases a
  · exact context_10_70388_1486792
  · exact context_10_70389_1468874
  · exact context_10_70390_1486955
  · exact context_10_70391_1487007

theorem selected_cut_51519 : selected 11 ⟨1487116, by decide⟩
    (prefixPartial 10 70392) = some ⟨10, 2, 0, 1487116, 70392, 3229, 1048576⟩ := by
  decide +kernel

theorem context_10_70392_1487116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70392 ⟨1487116, by decide⟩ :=
  accepted_of_selected 10 70392 ⟨1487116, by decide⟩ ⟨10, 2, 0, 1487116, 70392, 3229, 1048576⟩
    (by decide) selected_cut_51519

theorem selected_cut_51520 : selected 11 ⟨1487231, by decide⟩
    (prefixPartial 10 70393) = some ⟨10, 2, 0, 1487231, 70393, 2149, 1048576⟩ := by
  decide +kernel

theorem context_10_70393_1487231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70393 ⟨1487231, by decide⟩ :=
  accepted_of_selected 10 70393 ⟨1487231, by decide⟩ ⟨10, 2, 0, 1487231, 70393, 2149, 1048576⟩
    (by decide) selected_cut_51520

theorem selected_cut_51521 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70394) = some ⟨10, 1, 0, 1469103, 70394, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70394_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70394 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70394 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70394, 1, 1048576⟩
    (by decide) selected_cut_51521

theorem selected_cut_51522 : selected 11 ⟨1487255, by decide⟩
    (prefixPartial 10 70395) = some ⟨10, 2, 0, 1487255, 70395, 769, 1048576⟩ := by
  decide +kernel

theorem context_10_70395_1487255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70395 ⟨1487255, by decide⟩ :=
  accepted_of_selected 10 70395 ⟨1487255, by decide⟩ ⟨10, 2, 0, 1487255, 70395, 769, 1048576⟩
    (by decide) selected_cut_51522

theorem unmarked_context_9_17598_1487256 : frontier 12 ⟨1487256, by decide⟩
    (prefixCache 9 17598) (prefixPartial 9 17598) = false := by
  decide +kernel

theorem node_context_9_17598_1487256 : EJMOriginalGlobalDAGData.nodes 12 ⟨1487256, by decide⟩ =
    .split (coordinate 9) (![⟨1487116, by decide⟩,⟨1487231, by decide⟩,⟨1469103, by decide⟩,⟨1487255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17598_1487256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17598 ⟨1487256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17598
    ⟨1487256, by decide⟩ (by decide) (![⟨1487116, by decide⟩,⟨1487231, by decide⟩,⟨1469103, by decide⟩,⟨1487255, by decide⟩]) unmarked_context_9_17598_1487256 node_context_9_17598_1487256
  intro a
  fin_cases a
  · exact context_10_70392_1487116
  · exact context_10_70393_1487231
  · exact context_10_70394_1469103
  · exact context_10_70395_1487255

theorem selected_cut_51523 : selected 12 ⟨1487324, by decide⟩
    (prefixPartial 9 17599) = some ⟨9, 2, 0, 1487324, 17599, 1525, 4194304⟩ := by
  decide +kernel

theorem context_9_17599_1487324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17599 ⟨1487324, by decide⟩ :=
  accepted_of_selected 9 17599 ⟨1487324, by decide⟩ ⟨9, 2, 0, 1487324, 17599, 1525, 4194304⟩
    (by decide) selected_cut_51523

theorem unmarked_context_8_4399_1487325 : frontier 13 ⟨1487325, by decide⟩
    (prefixCache 8 4399) (prefixPartial 8 4399) = false := by
  decide +kernel

theorem node_context_8_4399_1487325 : EJMOriginalGlobalDAGData.nodes 13 ⟨1487325, by decide⟩ =
    .split (coordinate 8) (![⟨1486634, by decide⟩,⟨1487008, by decide⟩,⟨1487256, by decide⟩,⟨1487324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4399_1487325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4399 ⟨1487325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4399
    ⟨1487325, by decide⟩ (by decide) (![⟨1486634, by decide⟩,⟨1487008, by decide⟩,⟨1487256, by decide⟩,⟨1487324, by decide⟩]) unmarked_context_8_4399_1487325 node_context_8_4399_1487325
  intro a
  fin_cases a
  · exact context_9_17596_1486634
  · exact context_9_17597_1487008
  · exact context_9_17598_1487256
  · exact context_9_17599_1487324

theorem unmarked_context_7_1099_1487326 : frontier 14 ⟨1487326, by decide⟩
    (prefixCache 7 1099) (prefixPartial 7 1099) = false := by
  decide +kernel

theorem node_context_7_1099_1487326 : EJMOriginalGlobalDAGData.nodes 14 ⟨1487326, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨14300, by decide⟩,⟨1487325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1099_1487326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1099 ⟨1487326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1099
    ⟨1487326, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨14300, by decide⟩,⟨1487325, by decide⟩]) unmarked_context_7_1099_1487326 node_context_7_1099_1487326
  intro a
  fin_cases a
  · exact context_8_4396_14300
  · exact context_8_4397_14300
  · exact context_8_4398_14300
  · exact context_8_4399_1487325

theorem unmarked_context_6_274_1487327 : frontier 15 ⟨1487327, by decide⟩
    (prefixCache 6 274) (prefixPartial 6 274) = false := by
  decide +kernel

theorem node_context_6_274_1487327 : EJMOriginalGlobalDAGData.nodes 15 ⟨1487327, by decide⟩ =
    .split (coordinate 6) (![⟨1480756, by decide⟩,⟨1483833, by decide⟩,⟨1486187, by decide⟩,⟨1487326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_274_1487327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 274 ⟨1487327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 274
    ⟨1487327, by decide⟩ (by decide) (![⟨1480756, by decide⟩,⟨1483833, by decide⟩,⟨1486187, by decide⟩,⟨1487326, by decide⟩]) unmarked_context_6_274_1487327 node_context_6_274_1487327
  intro a
  fin_cases a
  · exact context_7_1096_1480756
  · exact context_7_1097_1483833
  · exact context_7_1098_1486187
  · exact context_7_1099_1487326

theorem selected_cut_51524 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 275) = some ⟨6, 1, 0, 116314, 275, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_275_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 275 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 275 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 275, 1, 268435456⟩
    (by decide) selected_cut_51524

theorem unmarked_context_5_68_1487328 : frontier 16 ⟨1487328, by decide⟩
    (prefixCache 5 68) (prefixPartial 5 68) = false := by
  decide +kernel

theorem node_context_5_68_1487328 : EJMOriginalGlobalDAGData.nodes 16 ⟨1487328, by decide⟩ =
    .split (coordinate 5) (![⟨1475983, by decide⟩,⟨1475984, by decide⟩,⟨1487327, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_68_1487328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 68 ⟨1487328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 68
    ⟨1487328, by decide⟩ (by decide) (![⟨1475983, by decide⟩,⟨1475984, by decide⟩,⟨1487327, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_68_1487328 node_context_5_68_1487328
  intro a
  fin_cases a
  · exact context_6_272_1475983
  · exact context_6_273_1475984
  · exact context_6_274_1487327
  · exact context_6_275_116314

theorem selected_cut_51525 : selected 13 ⟨1487329, by decide⟩
    (prefixPartial 8 4416) = some ⟨8, 1, 0, 1487329, 4416, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4416_1487329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4416 ⟨1487329, by decide⟩ :=
  accepted_of_selected 8 4416 ⟨1487329, by decide⟩ ⟨8, 1, 0, 1487329, 4416, 1, 16777216⟩
    (by decide) selected_cut_51525

theorem selected_cut_51526 : selected 13 ⟨1487330, by decide⟩
    (prefixPartial 8 4417) = some ⟨8, 1, 0, 1487330, 4417, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4417_1487330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4417 ⟨1487330, by decide⟩ :=
  accepted_of_selected 8 4417 ⟨1487330, by decide⟩ ⟨8, 1, 0, 1487330, 4417, 1, 16777216⟩
    (by decide) selected_cut_51526

theorem selected_cut_51527 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70688) = some ⟨10, 1, 0, 1468246, 70688, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70688_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70688 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70688 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70688, 1, 1048576⟩
    (by decide) selected_cut_51527

theorem selected_cut_51528 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 1131024) = some ⟨12, 1, 0, 448748, 1131024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1131024_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1131024 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 1131024 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 1131024, 1, 65536⟩
    (by decide) selected_cut_51528

theorem selected_cut_51529 : selected 9 ⟨1487386, by decide⟩
    (prefixPartial 12 1131025) = some ⟨12, 2, 0, 1487386, 1131025, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_1131025_1487386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1131025 ⟨1487386, by decide⟩ :=
  accepted_of_selected 12 1131025 ⟨1487386, by decide⟩ ⟨12, 2, 0, 1487386, 1131025, 1465, 65536⟩
    (by decide) selected_cut_51529

theorem selected_cut_51530 : selected 9 ⟨1487422, by decide⟩
    (prefixPartial 12 1131026) = some ⟨12, 2, 0, 1487422, 1131026, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_1131026_1487422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1131026 ⟨1487422, by decide⟩ :=
  accepted_of_selected 12 1131026 ⟨1487422, by decide⟩ ⟨12, 2, 0, 1487422, 1131026, 1357, 65536⟩
    (by decide) selected_cut_51530

theorem selected_cut_51531 : selected 9 ⟨1487461, by decide⟩
    (prefixPartial 12 1131027) = some ⟨12, 2, 0, 1487461, 1131027, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_1131027_1487461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1131027 ⟨1487461, by decide⟩ :=
  accepted_of_selected 12 1131027 ⟨1487461, by decide⟩ ⟨12, 2, 0, 1487461, 1131027, 1477, 65536⟩
    (by decide) selected_cut_51531

theorem unmarked_context_11_282756_1487462 : frontier 10 ⟨1487462, by decide⟩
    (prefixCache 11 282756) (prefixPartial 11 282756) = false := by
  decide +kernel

theorem node_context_11_282756_1487462 : EJMOriginalGlobalDAGData.nodes 10 ⟨1487462, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1487386, by decide⟩,⟨1487422, by decide⟩,⟨1487461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_282756_1487462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282756 ⟨1487462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 282756
    ⟨1487462, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1487386, by decide⟩,⟨1487422, by decide⟩,⟨1487461, by decide⟩]) unmarked_context_11_282756_1487462 node_context_11_282756_1487462
  intro a
  fin_cases a
  · exact context_12_1131024_448748
  · exact context_12_1131025_1487386
  · exact context_12_1131026_1487422
  · exact context_12_1131027_1487461

theorem selected_cut_51532 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 282757) = some ⟨11, 1, 0, 1468419, 282757, 1, 262144⟩ := by
  decide +kernel

theorem context_11_282757_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282757 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 282757 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 282757, 1, 262144⟩
    (by decide) selected_cut_51532

theorem selected_cut_51533 : selected 10 ⟨1487571, by decide⟩
    (prefixPartial 11 282758) = some ⟨11, 2, 0, 1487571, 282758, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_282758_1487571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282758 ⟨1487571, by decide⟩ :=
  accepted_of_selected 11 282758 ⟨1487571, by decide⟩ ⟨11, 2, 0, 1487571, 282758, 2989, 262144⟩
    (by decide) selected_cut_51533

theorem selected_cut_51534 : selected 10 ⟨1487650, by decide⟩
    (prefixPartial 11 282759) = some ⟨11, 2, 0, 1487650, 282759, 2937, 262144⟩ := by
  decide +kernel

theorem context_11_282759_1487650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282759 ⟨1487650, by decide⟩ :=
  accepted_of_selected 11 282759 ⟨1487650, by decide⟩ ⟨11, 2, 0, 1487650, 282759, 2937, 262144⟩
    (by decide) selected_cut_51534

theorem unmarked_context_10_70689_1487651 : frontier 11 ⟨1487651, by decide⟩
    (prefixCache 10 70689) (prefixPartial 10 70689) = false := by
  decide +kernel

theorem node_context_10_70689_1487651 : EJMOriginalGlobalDAGData.nodes 11 ⟨1487651, by decide⟩ =
    .split (coordinate 10) (![⟨1487462, by decide⟩,⟨1468419, by decide⟩,⟨1487571, by decide⟩,⟨1487650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70689_1487651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70689 ⟨1487651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70689
    ⟨1487651, by decide⟩ (by decide) (![⟨1487462, by decide⟩,⟨1468419, by decide⟩,⟨1487571, by decide⟩,⟨1487650, by decide⟩]) unmarked_context_10_70689_1487651 node_context_10_70689_1487651
  intro a
  fin_cases a
  · exact context_11_282756_1487462
  · exact context_11_282757_1468419
  · exact context_11_282758_1487571
  · exact context_11_282759_1487650

theorem selected_cut_51535 : selected 10 ⟨1487768, by decide⟩
    (prefixPartial 11 282760) = some ⟨11, 2, 0, 1487768, 282760, 3217, 262144⟩ := by
  decide +kernel

theorem context_11_282760_1487768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282760 ⟨1487768, by decide⟩ :=
  accepted_of_selected 11 282760 ⟨1487768, by decide⟩ ⟨11, 2, 0, 1487768, 282760, 3217, 262144⟩
    (by decide) selected_cut_51535

theorem selected_cut_51536 : selected 10 ⟨1487848, by decide⟩
    (prefixPartial 11 282761) = some ⟨11, 2, 0, 1487848, 282761, 2701, 262144⟩ := by
  decide +kernel

theorem context_11_282761_1487848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282761 ⟨1487848, by decide⟩ :=
  accepted_of_selected 11 282761 ⟨1487848, by decide⟩ ⟨11, 2, 0, 1487848, 282761, 2701, 262144⟩
    (by decide) selected_cut_51536

theorem selected_cut_51537 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 282762) = some ⟨11, 1, 0, 1468743, 282762, 1, 262144⟩ := by
  decide +kernel

theorem context_11_282762_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282762 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 282762 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 282762, 1, 262144⟩
    (by decide) selected_cut_51537

theorem selected_cut_51538 : selected 10 ⟨1487920, by decide⟩
    (prefixPartial 11 282763) = some ⟨11, 2, 0, 1487920, 282763, 2493, 262144⟩ := by
  decide +kernel

theorem context_11_282763_1487920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282763 ⟨1487920, by decide⟩ :=
  accepted_of_selected 11 282763 ⟨1487920, by decide⟩ ⟨11, 2, 0, 1487920, 282763, 2493, 262144⟩
    (by decide) selected_cut_51538

theorem unmarked_context_10_70690_1487921 : frontier 11 ⟨1487921, by decide⟩
    (prefixCache 10 70690) (prefixPartial 10 70690) = false := by
  decide +kernel

theorem node_context_10_70690_1487921 : EJMOriginalGlobalDAGData.nodes 11 ⟨1487921, by decide⟩ =
    .split (coordinate 10) (![⟨1487768, by decide⟩,⟨1487848, by decide⟩,⟨1468743, by decide⟩,⟨1487920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70690_1487921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70690 ⟨1487921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70690
    ⟨1487921, by decide⟩ (by decide) (![⟨1487768, by decide⟩,⟨1487848, by decide⟩,⟨1468743, by decide⟩,⟨1487920, by decide⟩]) unmarked_context_10_70690_1487921 node_context_10_70690_1487921
  intro a
  fin_cases a
  · exact context_11_282760_1487768
  · exact context_11_282761_1487848
  · exact context_11_282762_1468743
  · exact context_11_282763_1487920

theorem selected_cut_51539 : selected 10 ⟨1488003, by decide⟩
    (prefixPartial 11 282764) = some ⟨11, 2, 0, 1488003, 282764, 3293, 262144⟩ := by
  decide +kernel

theorem context_11_282764_1488003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282764 ⟨1488003, by decide⟩ :=
  accepted_of_selected 11 282764 ⟨1488003, by decide⟩ ⟨11, 2, 0, 1488003, 282764, 3293, 262144⟩
    (by decide) selected_cut_51539

theorem selected_cut_51540 : selected 10 ⟨1488070, by decide⟩
    (prefixPartial 11 282765) = some ⟨11, 2, 0, 1488070, 282765, 2345, 262144⟩ := by
  decide +kernel

theorem context_11_282765_1488070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282765 ⟨1488070, by decide⟩ :=
  accepted_of_selected 11 282765 ⟨1488070, by decide⟩ ⟨11, 2, 0, 1488070, 282765, 2345, 262144⟩
    (by decide) selected_cut_51540

theorem selected_cut_51541 : selected 10 ⟨1488120, by decide⟩
    (prefixPartial 11 282766) = some ⟨11, 2, 0, 1488120, 282766, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_282766_1488120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282766 ⟨1488120, by decide⟩ :=
  accepted_of_selected 11 282766 ⟨1488120, by decide⟩ ⟨11, 2, 0, 1488120, 282766, 2197, 262144⟩
    (by decide) selected_cut_51541

theorem selected_cut_51542 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 282767) = some ⟨11, 1, 0, 1470044, 282767, 1, 262144⟩ := by
  decide +kernel

theorem context_11_282767_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282767 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 282767 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 282767, 1, 262144⟩
    (by decide) selected_cut_51542

theorem unmarked_context_10_70691_1488121 : frontier 11 ⟨1488121, by decide⟩
    (prefixCache 10 70691) (prefixPartial 10 70691) = false := by
  decide +kernel

theorem node_context_10_70691_1488121 : EJMOriginalGlobalDAGData.nodes 11 ⟨1488121, by decide⟩ =
    .split (coordinate 10) (![⟨1488003, by decide⟩,⟨1488070, by decide⟩,⟨1488120, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70691_1488121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70691 ⟨1488121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70691
    ⟨1488121, by decide⟩ (by decide) (![⟨1488003, by decide⟩,⟨1488070, by decide⟩,⟨1488120, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70691_1488121 node_context_10_70691_1488121
  intro a
  fin_cases a
  · exact context_11_282764_1488003
  · exact context_11_282765_1488070
  · exact context_11_282766_1488120
  · exact context_11_282767_1470044

theorem unmarked_context_9_17672_1488122 : frontier 12 ⟨1488122, by decide⟩
    (prefixCache 9 17672) (prefixPartial 9 17672) = false := by
  decide +kernel

theorem node_context_9_17672_1488122 : EJMOriginalGlobalDAGData.nodes 12 ⟨1488122, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1487651, by decide⟩,⟨1487921, by decide⟩,⟨1488121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17672_1488122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17672 ⟨1488122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17672
    ⟨1488122, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1487651, by decide⟩,⟨1487921, by decide⟩,⟨1488121, by decide⟩]) unmarked_context_9_17672_1488122 node_context_9_17672_1488122
  intro a
  fin_cases a
  · exact context_10_70688_1468246
  · exact context_10_70689_1487651
  · exact context_10_70690_1487921
  · exact context_10_70691_1488121

theorem selected_cut_51543 : selected 11 ⟨1488179, by decide⟩
    (prefixPartial 10 70692) = some ⟨10, 2, 0, 1488179, 70692, 2961, 1048576⟩ := by
  decide +kernel

theorem context_10_70692_1488179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70692 ⟨1488179, by decide⟩ :=
  accepted_of_selected 10 70692 ⟨1488179, by decide⟩ ⟨10, 2, 0, 1488179, 70692, 2961, 1048576⟩
    (by decide) selected_cut_51543

theorem selected_cut_51544 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70693) = some ⟨10, 1, 0, 1468874, 70693, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70693_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70693 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70693 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70693, 1, 1048576⟩
    (by decide) selected_cut_51544

theorem selected_cut_51545 : selected 10 ⟨1488215, by decide⟩
    (prefixPartial 11 282776) = some ⟨11, 2, 0, 1488215, 282776, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_282776_1488215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282776 ⟨1488215, by decide⟩ :=
  accepted_of_selected 11 282776 ⟨1488215, by decide⟩ ⟨11, 2, 0, 1488215, 282776, 1669, 262144⟩
    (by decide) selected_cut_51545

theorem selected_cut_51546 : selected 10 ⟨1488271, by decide⟩
    (prefixPartial 11 282777) = some ⟨11, 2, 0, 1488271, 282777, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_282777_1488271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282777 ⟨1488271, by decide⟩ :=
  accepted_of_selected 11 282777 ⟨1488271, by decide⟩ ⟨11, 2, 0, 1488271, 282777, 2521, 262144⟩
    (by decide) selected_cut_51546

theorem selected_cut_51547 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 282778) = some ⟨11, 1, 0, 1468743, 282778, 1, 262144⟩ := by
  decide +kernel

theorem context_11_282778_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282778 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 282778 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 282778, 1, 262144⟩
    (by decide) selected_cut_51547

theorem selected_cut_51548 : selected 10 ⟨1488307, by decide⟩
    (prefixPartial 11 282779) = some ⟨11, 2, 0, 1488307, 282779, 1497, 262144⟩ := by
  decide +kernel

theorem context_11_282779_1488307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282779 ⟨1488307, by decide⟩ :=
  accepted_of_selected 11 282779 ⟨1488307, by decide⟩ ⟨11, 2, 0, 1488307, 282779, 1497, 262144⟩
    (by decide) selected_cut_51548

theorem unmarked_context_10_70694_1488308 : frontier 11 ⟨1488308, by decide⟩
    (prefixCache 10 70694) (prefixPartial 10 70694) = false := by
  decide +kernel

theorem node_context_10_70694_1488308 : EJMOriginalGlobalDAGData.nodes 11 ⟨1488308, by decide⟩ =
    .split (coordinate 10) (![⟨1488215, by decide⟩,⟨1488271, by decide⟩,⟨1468743, by decide⟩,⟨1488307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70694_1488308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70694 ⟨1488308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70694
    ⟨1488308, by decide⟩ (by decide) (![⟨1488215, by decide⟩,⟨1488271, by decide⟩,⟨1468743, by decide⟩,⟨1488307, by decide⟩]) unmarked_context_10_70694_1488308 node_context_10_70694_1488308
  intro a
  fin_cases a
  · exact context_11_282776_1488215
  · exact context_11_282777_1488271
  · exact context_11_282778_1468743
  · exact context_11_282779_1488307

theorem selected_cut_51549 : selected 10 ⟨1488339, by decide⟩
    (prefixPartial 11 282780) = some ⟨11, 2, 0, 1488339, 282780, 1333, 262144⟩ := by
  decide +kernel

theorem context_11_282780_1488339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282780 ⟨1488339, by decide⟩ :=
  accepted_of_selected 11 282780 ⟨1488339, by decide⟩ ⟨11, 2, 0, 1488339, 282780, 1333, 262144⟩
    (by decide) selected_cut_51549

theorem selected_cut_51550 : selected 10 ⟨1488382, by decide⟩
    (prefixPartial 11 282781) = some ⟨11, 2, 0, 1488382, 282781, 2045, 262144⟩ := by
  decide +kernel

theorem context_11_282781_1488382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282781 ⟨1488382, by decide⟩ :=
  accepted_of_selected 11 282781 ⟨1488382, by decide⟩ ⟨11, 2, 0, 1488382, 282781, 2045, 262144⟩
    (by decide) selected_cut_51550

theorem selected_cut_51551 : selected 10 ⟨1488407, by decide⟩
    (prefixPartial 11 282782) = some ⟨11, 2, 0, 1488407, 282782, 1197, 262144⟩ := by
  decide +kernel

theorem context_11_282782_1488407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282782 ⟨1488407, by decide⟩ :=
  accepted_of_selected 11 282782 ⟨1488407, by decide⟩ ⟨11, 2, 0, 1488407, 282782, 1197, 262144⟩
    (by decide) selected_cut_51551

theorem selected_cut_51552 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 282783) = some ⟨11, 1, 0, 1470044, 282783, 1, 262144⟩ := by
  decide +kernel

theorem context_11_282783_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 282783 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 282783 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 282783, 1, 262144⟩
    (by decide) selected_cut_51552

theorem unmarked_context_10_70695_1488408 : frontier 11 ⟨1488408, by decide⟩
    (prefixCache 10 70695) (prefixPartial 10 70695) = false := by
  decide +kernel

theorem node_context_10_70695_1488408 : EJMOriginalGlobalDAGData.nodes 11 ⟨1488408, by decide⟩ =
    .split (coordinate 10) (![⟨1488339, by decide⟩,⟨1488382, by decide⟩,⟨1488407, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70695_1488408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70695 ⟨1488408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70695
    ⟨1488408, by decide⟩ (by decide) (![⟨1488339, by decide⟩,⟨1488382, by decide⟩,⟨1488407, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70695_1488408 node_context_10_70695_1488408
  intro a
  fin_cases a
  · exact context_11_282780_1488339
  · exact context_11_282781_1488382
  · exact context_11_282782_1488407
  · exact context_11_282783_1470044

theorem unmarked_context_9_17673_1488409 : frontier 12 ⟨1488409, by decide⟩
    (prefixCache 9 17673) (prefixPartial 9 17673) = false := by
  decide +kernel

theorem node_context_9_17673_1488409 : EJMOriginalGlobalDAGData.nodes 12 ⟨1488409, by decide⟩ =
    .split (coordinate 9) (![⟨1488179, by decide⟩,⟨1468874, by decide⟩,⟨1488308, by decide⟩,⟨1488408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17673_1488409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17673 ⟨1488409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17673
    ⟨1488409, by decide⟩ (by decide) (![⟨1488179, by decide⟩,⟨1468874, by decide⟩,⟨1488308, by decide⟩,⟨1488408, by decide⟩]) unmarked_context_9_17673_1488409 node_context_9_17673_1488409
  intro a
  fin_cases a
  · exact context_10_70692_1488179
  · exact context_10_70693_1468874
  · exact context_10_70694_1488308
  · exact context_10_70695_1488408

theorem selected_cut_51553 : selected 11 ⟨1488444, by decide⟩
    (prefixPartial 10 70696) = some ⟨10, 2, 0, 1488444, 70696, 1917, 1048576⟩ := by
  decide +kernel

theorem context_10_70696_1488444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70696 ⟨1488444, by decide⟩ :=
  accepted_of_selected 10 70696 ⟨1488444, by decide⟩ ⟨10, 2, 0, 1488444, 70696, 1917, 1048576⟩
    (by decide) selected_cut_51553

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
