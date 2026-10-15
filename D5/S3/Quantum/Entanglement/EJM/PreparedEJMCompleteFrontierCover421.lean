/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover420
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_40419 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 309528) = some ⟨12, 1, 0, 26677, 309528, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309528_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309528 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 309528 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 309528, 1, 65536⟩
    (by decide) selected_cut_40419

theorem selected_cut_40420 : selected 9 ⟨1099096, by decide⟩
    (prefixPartial 12 309529) = some ⟨12, 2, 0, 1099096, 309529, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_309529_1099096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309529 ⟨1099096, by decide⟩ :=
  accepted_of_selected 12 309529 ⟨1099096, by decide⟩ ⟨12, 2, 0, 1099096, 309529, 2329, 65536⟩
    (by decide) selected_cut_40420

theorem selected_cut_40421 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 309530) = some ⟨12, 1, 0, 3161, 309530, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309530_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309530 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 309530 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 309530, 1, 65536⟩
    (by decide) selected_cut_40421

theorem selected_cut_40422 : selected 9 ⟨1099132, by decide⟩
    (prefixPartial 12 309531) = some ⟨12, 2, 0, 1099132, 309531, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_309531_1099132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309531 ⟨1099132, by decide⟩ :=
  accepted_of_selected 12 309531 ⟨1099132, by decide⟩ ⟨12, 2, 0, 1099132, 309531, 2361, 65536⟩
    (by decide) selected_cut_40422

theorem unmarked_context_11_77382_1099133 : frontier 10 ⟨1099133, by decide⟩
    (prefixCache 11 77382) (prefixPartial 11 77382) = false := by
  decide +kernel

theorem node_context_11_77382_1099133 : EJMOriginalGlobalDAGData.nodes 10 ⟨1099133, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1099096, by decide⟩,⟨3161, by decide⟩,⟨1099132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77382_1099133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77382 ⟨1099133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77382
    ⟨1099133, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1099096, by decide⟩,⟨3161, by decide⟩,⟨1099132, by decide⟩]) unmarked_context_11_77382_1099133 node_context_11_77382_1099133
  intro a
  fin_cases a
  · exact context_12_309528_26677
  · exact context_12_309529_1099096
  · exact context_12_309530_3161
  · exact context_12_309531_1099132

theorem selected_cut_40423 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 309532) = some ⟨12, 1, 0, 26677, 309532, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309532_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309532 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 309532 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 309532, 1, 65536⟩
    (by decide) selected_cut_40423

theorem selected_cut_40424 : selected 9 ⟨1099176, by decide⟩
    (prefixPartial 12 309533) = some ⟨12, 2, 0, 1099176, 309533, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_309533_1099176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309533 ⟨1099176, by decide⟩ :=
  accepted_of_selected 12 309533 ⟨1099176, by decide⟩ ⟨12, 2, 0, 1099176, 309533, 2397, 65536⟩
    (by decide) selected_cut_40424

theorem selected_cut_40425 : selected 9 ⟨1099203, by decide⟩
    (prefixPartial 12 309534) = some ⟨12, 2, 0, 1099203, 309534, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_309534_1099203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309534 ⟨1099203, by decide⟩ :=
  accepted_of_selected 12 309534 ⟨1099203, by decide⟩ ⟨12, 2, 0, 1099203, 309534, 1349, 65536⟩
    (by decide) selected_cut_40425

theorem selected_cut_40426 : selected 9 ⟨1099241, by decide⟩
    (prefixPartial 12 309535) = some ⟨12, 2, 0, 1099241, 309535, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_309535_1099241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309535 ⟨1099241, by decide⟩ :=
  accepted_of_selected 12 309535 ⟨1099241, by decide⟩ ⟨12, 2, 0, 1099241, 309535, 2381, 65536⟩
    (by decide) selected_cut_40426

theorem unmarked_context_11_77383_1099242 : frontier 10 ⟨1099242, by decide⟩
    (prefixCache 11 77383) (prefixPartial 11 77383) = false := by
  decide +kernel

theorem node_context_11_77383_1099242 : EJMOriginalGlobalDAGData.nodes 10 ⟨1099242, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1099176, by decide⟩,⟨1099203, by decide⟩,⟨1099241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77383_1099242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77383 ⟨1099242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77383
    ⟨1099242, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1099176, by decide⟩,⟨1099203, by decide⟩,⟨1099241, by decide⟩]) unmarked_context_11_77383_1099242 node_context_11_77383_1099242
  intro a
  fin_cases a
  · exact context_12_309532_26677
  · exact context_12_309533_1099176
  · exact context_12_309534_1099203
  · exact context_12_309535_1099241

theorem unmarked_context_10_19345_1099243 : frontier 11 ⟨1099243, by decide⟩
    (prefixCache 10 19345) (prefixPartial 10 19345) = false := by
  decide +kernel

theorem node_context_10_19345_1099243 : EJMOriginalGlobalDAGData.nodes 11 ⟨1099243, by decide⟩ =
    .split (coordinate 10) (![⟨1098985, by decide⟩,⟨1099055, by decide⟩,⟨1099133, by decide⟩,⟨1099242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19345_1099243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19345 ⟨1099243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19345
    ⟨1099243, by decide⟩ (by decide) (![⟨1098985, by decide⟩,⟨1099055, by decide⟩,⟨1099133, by decide⟩,⟨1099242, by decide⟩]) unmarked_context_10_19345_1099243 node_context_10_19345_1099243
  intro a
  fin_cases a
  · exact context_11_77380_1098985
  · exact context_11_77381_1099055
  · exact context_11_77382_1099133
  · exact context_11_77383_1099242

theorem selected_cut_40427 : selected 10 ⟨1099314, by decide⟩
    (prefixPartial 11 77384) = some ⟨11, 2, 0, 1099314, 77384, 3253, 262144⟩ := by
  decide +kernel

theorem context_11_77384_1099314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77384 ⟨1099314, by decide⟩ :=
  accepted_of_selected 11 77384 ⟨1099314, by decide⟩ ⟨11, 2, 0, 1099314, 77384, 3253, 262144⟩
    (by decide) selected_cut_40427

theorem selected_cut_40428 : selected 10 ⟨1099351, by decide⟩
    (prefixPartial 11 77385) = some ⟨11, 2, 0, 1099351, 77385, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_77385_1099351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77385 ⟨1099351, by decide⟩ :=
  accepted_of_selected 11 77385 ⟨1099351, by decide⟩ ⟨11, 2, 0, 1099351, 77385, 2117, 262144⟩
    (by decide) selected_cut_40428

theorem selected_cut_40429 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 77386) = some ⟨11, 1, 0, 900587, 77386, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77386_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77386 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 77386 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 77386, 1, 262144⟩
    (by decide) selected_cut_40429

theorem selected_cut_40430 : selected 10 ⟨1099413, by decide⟩
    (prefixPartial 11 77387) = some ⟨11, 2, 0, 1099413, 77387, 3449, 262144⟩ := by
  decide +kernel

theorem context_11_77387_1099413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77387 ⟨1099413, by decide⟩ :=
  accepted_of_selected 11 77387 ⟨1099413, by decide⟩ ⟨11, 2, 0, 1099413, 77387, 3449, 262144⟩
    (by decide) selected_cut_40430

theorem unmarked_context_10_19346_1099414 : frontier 11 ⟨1099414, by decide⟩
    (prefixCache 10 19346) (prefixPartial 10 19346) = false := by
  decide +kernel

theorem node_context_10_19346_1099414 : EJMOriginalGlobalDAGData.nodes 11 ⟨1099414, by decide⟩ =
    .split (coordinate 10) (![⟨1099314, by decide⟩,⟨1099351, by decide⟩,⟨900587, by decide⟩,⟨1099413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19346_1099414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19346 ⟨1099414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19346
    ⟨1099414, by decide⟩ (by decide) (![⟨1099314, by decide⟩,⟨1099351, by decide⟩,⟨900587, by decide⟩,⟨1099413, by decide⟩]) unmarked_context_10_19346_1099414 node_context_10_19346_1099414
  intro a
  fin_cases a
  · exact context_11_77384_1099314
  · exact context_11_77385_1099351
  · exact context_11_77386_900587
  · exact context_11_77387_1099413

theorem selected_cut_40431 : selected 11 ⟨1099531, by decide⟩
    (prefixPartial 10 19347) = some ⟨10, 2, 0, 1099531, 19347, 3561, 1048576⟩ := by
  decide +kernel

theorem context_10_19347_1099531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19347 ⟨1099531, by decide⟩ :=
  accepted_of_selected 10 19347 ⟨1099531, by decide⟩ ⟨10, 2, 0, 1099531, 19347, 3561, 1048576⟩
    (by decide) selected_cut_40431

theorem unmarked_context_9_4836_1099532 : frontier 12 ⟨1099532, by decide⟩
    (prefixCache 9 4836) (prefixPartial 9 4836) = false := by
  decide +kernel

theorem node_context_9_4836_1099532 : EJMOriginalGlobalDAGData.nodes 12 ⟨1099532, by decide⟩ =
    .split (coordinate 9) (![⟨1098868, by decide⟩,⟨1099243, by decide⟩,⟨1099414, by decide⟩,⟨1099531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4836_1099532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4836 ⟨1099532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4836
    ⟨1099532, by decide⟩ (by decide) (![⟨1098868, by decide⟩,⟨1099243, by decide⟩,⟨1099414, by decide⟩,⟨1099531, by decide⟩]) unmarked_context_9_4836_1099532 node_context_9_4836_1099532
  intro a
  fin_cases a
  · exact context_10_19344_1098868
  · exact context_10_19345_1099243
  · exact context_10_19346_1099414
  · exact context_10_19347_1099531

theorem selected_cut_40432 : selected 9 ⟨290056, by decide⟩
    (prefixPartial 12 309568) = some ⟨12, 1, 0, 290056, 309568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309568_290056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309568 ⟨290056, by decide⟩ :=
  accepted_of_selected 12 309568 ⟨290056, by decide⟩ ⟨12, 1, 0, 290056, 309568, 1, 65536⟩
    (by decide) selected_cut_40432

theorem selected_cut_40433 : selected 9 ⟨1099564, by decide⟩
    (prefixPartial 12 309569) = some ⟨12, 2, 0, 1099564, 309569, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_309569_1099564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309569 ⟨1099564, by decide⟩ :=
  accepted_of_selected 12 309569 ⟨1099564, by decide⟩ ⟨12, 2, 0, 1099564, 309569, 1805, 65536⟩
    (by decide) selected_cut_40433

theorem selected_cut_40434 : selected 9 ⟨1099600, by decide⟩
    (prefixPartial 12 309570) = some ⟨12, 2, 0, 1099600, 309570, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_309570_1099600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309570 ⟨1099600, by decide⟩ :=
  accepted_of_selected 12 309570 ⟨1099600, by decide⟩ ⟨12, 2, 0, 1099600, 309570, 2025, 65536⟩
    (by decide) selected_cut_40434

theorem selected_cut_40435 : selected 9 ⟨1099634, by decide⟩
    (prefixPartial 12 309571) = some ⟨12, 2, 0, 1099634, 309571, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_309571_1099634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309571 ⟨1099634, by decide⟩ :=
  accepted_of_selected 12 309571 ⟨1099634, by decide⟩ ⟨12, 2, 0, 1099634, 309571, 1805, 65536⟩
    (by decide) selected_cut_40435

theorem unmarked_context_11_77392_1099635 : frontier 10 ⟨1099635, by decide⟩
    (prefixCache 11 77392) (prefixPartial 11 77392) = false := by
  decide +kernel

theorem node_context_11_77392_1099635 : EJMOriginalGlobalDAGData.nodes 10 ⟨1099635, by decide⟩ =
    .split (coordinate 11) (![⟨290056, by decide⟩,⟨1099564, by decide⟩,⟨1099600, by decide⟩,⟨1099634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77392_1099635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77392 ⟨1099635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77392
    ⟨1099635, by decide⟩ (by decide) (![⟨290056, by decide⟩,⟨1099564, by decide⟩,⟨1099600, by decide⟩,⟨1099634, by decide⟩]) unmarked_context_11_77392_1099635 node_context_11_77392_1099635
  intro a
  fin_cases a
  · exact context_12_309568_290056
  · exact context_12_309569_1099564
  · exact context_12_309570_1099600
  · exact context_12_309571_1099634

theorem selected_cut_40436 : selected 9 ⟨1099684, by decide⟩
    (prefixPartial 12 309572) = some ⟨12, 2, 0, 1099684, 309572, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_309572_1099684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309572 ⟨1099684, by decide⟩ :=
  accepted_of_selected 12 309572 ⟨1099684, by decide⟩ ⟨12, 2, 0, 1099684, 309572, 2489, 65536⟩
    (by decide) selected_cut_40436

theorem selected_cut_40437 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 309573) = some ⟨12, 1, 0, 891951, 309573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_309573_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309573 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 309573 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 309573, 1, 65536⟩
    (by decide) selected_cut_40437

theorem selected_cut_40438 : selected 9 ⟨1099724, by decide⟩
    (prefixPartial 12 309574) = some ⟨12, 2, 0, 1099724, 309574, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_309574_1099724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309574 ⟨1099724, by decide⟩ :=
  accepted_of_selected 12 309574 ⟨1099724, by decide⟩ ⟨12, 2, 0, 1099724, 309574, 1945, 65536⟩
    (by decide) selected_cut_40438

theorem selected_cut_40439 : selected 9 ⟨1099759, by decide⟩
    (prefixPartial 12 309575) = some ⟨12, 2, 0, 1099759, 309575, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_309575_1099759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309575 ⟨1099759, by decide⟩ :=
  accepted_of_selected 12 309575 ⟨1099759, by decide⟩ ⟨12, 2, 0, 1099759, 309575, 1817, 65536⟩
    (by decide) selected_cut_40439

theorem unmarked_context_11_77393_1099760 : frontier 10 ⟨1099760, by decide⟩
    (prefixCache 11 77393) (prefixPartial 11 77393) = false := by
  decide +kernel

theorem node_context_11_77393_1099760 : EJMOriginalGlobalDAGData.nodes 10 ⟨1099760, by decide⟩ =
    .split (coordinate 11) (![⟨1099684, by decide⟩,⟨891951, by decide⟩,⟨1099724, by decide⟩,⟨1099759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77393_1099760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77393 ⟨1099760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77393
    ⟨1099760, by decide⟩ (by decide) (![⟨1099684, by decide⟩,⟨891951, by decide⟩,⟨1099724, by decide⟩,⟨1099759, by decide⟩]) unmarked_context_11_77393_1099760 node_context_11_77393_1099760
  intro a
  fin_cases a
  · exact context_12_309572_1099684
  · exact context_12_309573_891951
  · exact context_12_309574_1099724
  · exact context_12_309575_1099759

theorem selected_cut_40440 : selected 9 ⟨1099803, by decide⟩
    (prefixPartial 12 309576) = some ⟨12, 2, 0, 1099803, 309576, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_309576_1099803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309576 ⟨1099803, by decide⟩ :=
  accepted_of_selected 12 309576 ⟨1099803, by decide⟩ ⟨12, 2, 0, 1099803, 309576, 2149, 65536⟩
    (by decide) selected_cut_40440

theorem selected_cut_40441 : selected 9 ⟨1099834, by decide⟩
    (prefixPartial 12 309577) = some ⟨12, 2, 0, 1099834, 309577, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_309577_1099834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309577 ⟨1099834, by decide⟩ :=
  accepted_of_selected 12 309577 ⟨1099834, by decide⟩ ⟨12, 2, 0, 1099834, 309577, 1737, 65536⟩
    (by decide) selected_cut_40441

theorem selected_cut_40442 : selected 9 ⟨1099867, by decide⟩
    (prefixPartial 12 309578) = some ⟨12, 2, 0, 1099867, 309578, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_309578_1099867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309578 ⟨1099867, by decide⟩ :=
  accepted_of_selected 12 309578 ⟨1099867, by decide⟩ ⟨12, 2, 0, 1099867, 309578, 1877, 65536⟩
    (by decide) selected_cut_40442

theorem selected_cut_40443 : selected 9 ⟨1099896, by decide⟩
    (prefixPartial 12 309579) = some ⟨12, 2, 0, 1099896, 309579, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_309579_1099896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309579 ⟨1099896, by decide⟩ :=
  accepted_of_selected 12 309579 ⟨1099896, by decide⟩ ⟨12, 2, 0, 1099896, 309579, 1725, 65536⟩
    (by decide) selected_cut_40443

theorem unmarked_context_11_77394_1099897 : frontier 10 ⟨1099897, by decide⟩
    (prefixCache 11 77394) (prefixPartial 11 77394) = false := by
  decide +kernel

theorem node_context_11_77394_1099897 : EJMOriginalGlobalDAGData.nodes 10 ⟨1099897, by decide⟩ =
    .split (coordinate 11) (![⟨1099803, by decide⟩,⟨1099834, by decide⟩,⟨1099867, by decide⟩,⟨1099896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77394_1099897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77394 ⟨1099897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77394
    ⟨1099897, by decide⟩ (by decide) (![⟨1099803, by decide⟩,⟨1099834, by decide⟩,⟨1099867, by decide⟩,⟨1099896, by decide⟩]) unmarked_context_11_77394_1099897 node_context_11_77394_1099897
  intro a
  fin_cases a
  · exact context_12_309576_1099803
  · exact context_12_309577_1099834
  · exact context_12_309578_1099867
  · exact context_12_309579_1099896

theorem selected_cut_40444 : selected 9 ⟨1099956, by decide⟩
    (prefixPartial 12 309580) = some ⟨12, 2, 0, 1099956, 309580, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_309580_1099956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309580 ⟨1099956, by decide⟩ :=
  accepted_of_selected 12 309580 ⟨1099956, by decide⟩ ⟨12, 2, 0, 1099956, 309580, 2345, 65536⟩
    (by decide) selected_cut_40444

theorem selected_cut_40445 : selected 9 ⟨1099987, by decide⟩
    (prefixPartial 12 309581) = some ⟨12, 2, 0, 1099987, 309581, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_309581_1099987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309581 ⟨1099987, by decide⟩ :=
  accepted_of_selected 12 309581 ⟨1099987, by decide⟩ ⟨12, 2, 0, 1099987, 309581, 1721, 65536⟩
    (by decide) selected_cut_40445

theorem selected_cut_40446 : selected 9 ⟨1100037, by decide⟩
    (prefixPartial 12 309582) = some ⟨12, 2, 0, 1100037, 309582, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_309582_1100037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309582 ⟨1100037, by decide⟩ :=
  accepted_of_selected 12 309582 ⟨1100037, by decide⟩ ⟨12, 2, 0, 1100037, 309582, 1961, 65536⟩
    (by decide) selected_cut_40446

theorem selected_cut_40447 : selected 9 ⟨1100068, by decide⟩
    (prefixPartial 12 309583) = some ⟨12, 2, 0, 1100068, 309583, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_309583_1100068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309583 ⟨1100068, by decide⟩ :=
  accepted_of_selected 12 309583 ⟨1100068, by decide⟩ ⟨12, 2, 0, 1100068, 309583, 1697, 65536⟩
    (by decide) selected_cut_40447

theorem unmarked_context_11_77395_1100069 : frontier 10 ⟨1100069, by decide⟩
    (prefixCache 11 77395) (prefixPartial 11 77395) = false := by
  decide +kernel

theorem node_context_11_77395_1100069 : EJMOriginalGlobalDAGData.nodes 10 ⟨1100069, by decide⟩ =
    .split (coordinate 11) (![⟨1099956, by decide⟩,⟨1099987, by decide⟩,⟨1100037, by decide⟩,⟨1100068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77395_1100069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77395 ⟨1100069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77395
    ⟨1100069, by decide⟩ (by decide) (![⟨1099956, by decide⟩,⟨1099987, by decide⟩,⟨1100037, by decide⟩,⟨1100068, by decide⟩]) unmarked_context_11_77395_1100069 node_context_11_77395_1100069
  intro a
  fin_cases a
  · exact context_12_309580_1099956
  · exact context_12_309581_1099987
  · exact context_12_309582_1100037
  · exact context_12_309583_1100068

theorem unmarked_context_10_19348_1100070 : frontier 11 ⟨1100070, by decide⟩
    (prefixCache 10 19348) (prefixPartial 10 19348) = false := by
  decide +kernel

theorem node_context_10_19348_1100070 : EJMOriginalGlobalDAGData.nodes 11 ⟨1100070, by decide⟩ =
    .split (coordinate 10) (![⟨1099635, by decide⟩,⟨1099760, by decide⟩,⟨1099897, by decide⟩,⟨1100069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19348_1100070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19348 ⟨1100070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19348
    ⟨1100070, by decide⟩ (by decide) (![⟨1099635, by decide⟩,⟨1099760, by decide⟩,⟨1099897, by decide⟩,⟨1100069, by decide⟩]) unmarked_context_10_19348_1100070 node_context_10_19348_1100070
  intro a
  fin_cases a
  · exact context_11_77392_1099635
  · exact context_11_77393_1099760
  · exact context_11_77394_1099897
  · exact context_11_77395_1100069

theorem selected_cut_40448 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19349) = some ⟨10, 1, 0, 893098, 19349, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19349_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19349 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19349 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19349, 1, 1048576⟩
    (by decide) selected_cut_40448

theorem selected_cut_40449 : selected 9 ⟨1100103, by decide⟩
    (prefixPartial 12 309600) = some ⟨12, 2, 0, 1100103, 309600, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_309600_1100103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309600 ⟨1100103, by decide⟩ :=
  accepted_of_selected 12 309600 ⟨1100103, by decide⟩ ⟨12, 2, 0, 1100103, 309600, 1533, 65536⟩
    (by decide) selected_cut_40449

theorem selected_cut_40450 : selected 9 ⟨1100132, by decide⟩
    (prefixPartial 12 309601) = some ⟨12, 2, 0, 1100132, 309601, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_309601_1100132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309601 ⟨1100132, by decide⟩ :=
  accepted_of_selected 12 309601 ⟨1100132, by decide⟩ ⟨12, 2, 0, 1100132, 309601, 1385, 65536⟩
    (by decide) selected_cut_40450

theorem selected_cut_40451 : selected 9 ⟨1100171, by decide⟩
    (prefixPartial 12 309602) = some ⟨12, 2, 0, 1100171, 309602, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_309602_1100171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309602 ⟨1100171, by decide⟩ :=
  accepted_of_selected 12 309602 ⟨1100171, by decide⟩ ⟨12, 2, 0, 1100171, 309602, 1329, 65536⟩
    (by decide) selected_cut_40451

theorem selected_cut_40452 : selected 9 ⟨1100195, by decide⟩
    (prefixPartial 12 309603) = some ⟨12, 2, 0, 1100195, 309603, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_309603_1100195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309603 ⟨1100195, by decide⟩ :=
  accepted_of_selected 12 309603 ⟨1100195, by decide⟩ ⟨12, 2, 0, 1100195, 309603, 1293, 65536⟩
    (by decide) selected_cut_40452

theorem unmarked_context_11_77400_1100196 : frontier 10 ⟨1100196, by decide⟩
    (prefixCache 11 77400) (prefixPartial 11 77400) = false := by
  decide +kernel

theorem node_context_11_77400_1100196 : EJMOriginalGlobalDAGData.nodes 10 ⟨1100196, by decide⟩ =
    .split (coordinate 11) (![⟨1100103, by decide⟩,⟨1100132, by decide⟩,⟨1100171, by decide⟩,⟨1100195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77400_1100196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77400 ⟨1100196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77400
    ⟨1100196, by decide⟩ (by decide) (![⟨1100103, by decide⟩,⟨1100132, by decide⟩,⟨1100171, by decide⟩,⟨1100195, by decide⟩]) unmarked_context_11_77400_1100196 node_context_11_77400_1100196
  intro a
  fin_cases a
  · exact context_12_309600_1100103
  · exact context_12_309601_1100132
  · exact context_12_309602_1100171
  · exact context_12_309603_1100195

theorem selected_cut_40453 : selected 10 ⟨1100283, by decide⟩
    (prefixPartial 11 77401) = some ⟨11, 2, 0, 1100283, 77401, 4037, 262144⟩ := by
  decide +kernel

theorem context_11_77401_1100283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77401 ⟨1100283, by decide⟩ :=
  accepted_of_selected 11 77401 ⟨1100283, by decide⟩ ⟨11, 2, 0, 1100283, 77401, 4037, 262144⟩
    (by decide) selected_cut_40453

theorem selected_cut_40454 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 77402) = some ⟨11, 1, 0, 900587, 77402, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77402_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77402 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 77402 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 77402, 1, 262144⟩
    (by decide) selected_cut_40454

theorem selected_cut_40455 : selected 9 ⟨1100315, by decide⟩
    (prefixPartial 12 309612) = some ⟨12, 2, 0, 1100315, 309612, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_309612_1100315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309612 ⟨1100315, by decide⟩ :=
  accepted_of_selected 12 309612 ⟨1100315, by decide⟩ ⟨12, 2, 0, 1100315, 309612, 1413, 65536⟩
    (by decide) selected_cut_40455

theorem selected_cut_40456 : selected 9 ⟨1100341, by decide⟩
    (prefixPartial 12 309613) = some ⟨12, 2, 0, 1100341, 309613, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_309613_1100341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309613 ⟨1100341, by decide⟩ :=
  accepted_of_selected 12 309613 ⟨1100341, by decide⟩ ⟨12, 2, 0, 1100341, 309613, 1209, 65536⟩
    (by decide) selected_cut_40456

theorem selected_cut_40457 : selected 9 ⟨1100366, by decide⟩
    (prefixPartial 12 309614) = some ⟨12, 2, 0, 1100366, 309614, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_309614_1100366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309614 ⟨1100366, by decide⟩ :=
  accepted_of_selected 12 309614 ⟨1100366, by decide⟩ ⟨12, 2, 0, 1100366, 309614, 1189, 65536⟩
    (by decide) selected_cut_40457

theorem selected_cut_40458 : selected 9 ⟨1100391, by decide⟩
    (prefixPartial 12 309615) = some ⟨12, 2, 0, 1100391, 309615, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_309615_1100391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309615 ⟨1100391, by decide⟩ :=
  accepted_of_selected 12 309615 ⟨1100391, by decide⟩ ⟨12, 2, 0, 1100391, 309615, 1237, 65536⟩
    (by decide) selected_cut_40458

theorem unmarked_context_11_77403_1100392 : frontier 10 ⟨1100392, by decide⟩
    (prefixCache 11 77403) (prefixPartial 11 77403) = false := by
  decide +kernel

theorem node_context_11_77403_1100392 : EJMOriginalGlobalDAGData.nodes 10 ⟨1100392, by decide⟩ =
    .split (coordinate 11) (![⟨1100315, by decide⟩,⟨1100341, by decide⟩,⟨1100366, by decide⟩,⟨1100391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77403_1100392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77403 ⟨1100392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77403
    ⟨1100392, by decide⟩ (by decide) (![⟨1100315, by decide⟩,⟨1100341, by decide⟩,⟨1100366, by decide⟩,⟨1100391, by decide⟩]) unmarked_context_11_77403_1100392 node_context_11_77403_1100392
  intro a
  fin_cases a
  · exact context_12_309612_1100315
  · exact context_12_309613_1100341
  · exact context_12_309614_1100366
  · exact context_12_309615_1100391

theorem unmarked_context_10_19350_1100393 : frontier 11 ⟨1100393, by decide⟩
    (prefixCache 10 19350) (prefixPartial 10 19350) = false := by
  decide +kernel

theorem node_context_10_19350_1100393 : EJMOriginalGlobalDAGData.nodes 11 ⟨1100393, by decide⟩ =
    .split (coordinate 10) (![⟨1100196, by decide⟩,⟨1100283, by decide⟩,⟨900587, by decide⟩,⟨1100392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19350_1100393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19350 ⟨1100393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19350
    ⟨1100393, by decide⟩ (by decide) (![⟨1100196, by decide⟩,⟨1100283, by decide⟩,⟨900587, by decide⟩,⟨1100392, by decide⟩]) unmarked_context_10_19350_1100393 node_context_10_19350_1100393
  intro a
  fin_cases a
  · exact context_11_77400_1100196
  · exact context_11_77401_1100283
  · exact context_11_77402_900587
  · exact context_11_77403_1100392

theorem selected_cut_40459 : selected 9 ⟨1100417, by decide⟩
    (prefixPartial 12 309616) = some ⟨12, 2, 0, 1100417, 309616, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_309616_1100417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309616 ⟨1100417, by decide⟩ :=
  accepted_of_selected 12 309616 ⟨1100417, by decide⟩ ⟨12, 2, 0, 1100417, 309616, 1149, 65536⟩
    (by decide) selected_cut_40459

theorem selected_cut_40460 : selected 9 ⟨1100440, by decide⟩
    (prefixPartial 12 309617) = some ⟨12, 2, 0, 1100440, 309617, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_309617_1100440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309617 ⟨1100440, by decide⟩ :=
  accepted_of_selected 12 309617 ⟨1100440, by decide⟩ ⟨12, 2, 0, 1100440, 309617, 1137, 65536⟩
    (by decide) selected_cut_40460

theorem selected_cut_40461 : selected 9 ⟨1100465, by decide⟩
    (prefixPartial 12 309618) = some ⟨12, 2, 0, 1100465, 309618, 1053, 65536⟩ := by
  decide +kernel

theorem context_12_309618_1100465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309618 ⟨1100465, by decide⟩ :=
  accepted_of_selected 12 309618 ⟨1100465, by decide⟩ ⟨12, 2, 0, 1100465, 309618, 1053, 65536⟩
    (by decide) selected_cut_40461

theorem selected_cut_40462 : selected 9 ⟨1100485, by decide⟩
    (prefixPartial 12 309619) = some ⟨12, 2, 0, 1100485, 309619, 973, 65536⟩ := by
  decide +kernel

theorem context_12_309619_1100485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 309619 ⟨1100485, by decide⟩ :=
  accepted_of_selected 12 309619 ⟨1100485, by decide⟩ ⟨12, 2, 0, 1100485, 309619, 973, 65536⟩
    (by decide) selected_cut_40462

theorem unmarked_context_11_77404_1100486 : frontier 10 ⟨1100486, by decide⟩
    (prefixCache 11 77404) (prefixPartial 11 77404) = false := by
  decide +kernel

theorem node_context_11_77404_1100486 : EJMOriginalGlobalDAGData.nodes 10 ⟨1100486, by decide⟩ =
    .split (coordinate 11) (![⟨1100417, by decide⟩,⟨1100440, by decide⟩,⟨1100465, by decide⟩,⟨1100485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77404_1100486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77404 ⟨1100486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77404
    ⟨1100486, by decide⟩ (by decide) (![⟨1100417, by decide⟩,⟨1100440, by decide⟩,⟨1100465, by decide⟩,⟨1100485, by decide⟩]) unmarked_context_11_77404_1100486 node_context_11_77404_1100486
  intro a
  fin_cases a
  · exact context_12_309616_1100417
  · exact context_12_309617_1100440
  · exact context_12_309618_1100465
  · exact context_12_309619_1100485

theorem selected_cut_40463 : selected 10 ⟨1100553, by decide⟩
    (prefixPartial 11 77405) = some ⟨11, 2, 0, 1100553, 77405, 2953, 262144⟩ := by
  decide +kernel

theorem context_11_77405_1100553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77405 ⟨1100553, by decide⟩ :=
  accepted_of_selected 11 77405 ⟨1100553, by decide⟩ ⟨11, 2, 0, 1100553, 77405, 2953, 262144⟩
    (by decide) selected_cut_40463

theorem selected_cut_40464 : selected 10 ⟨1100621, by decide⟩
    (prefixPartial 11 77406) = some ⟨11, 2, 0, 1100621, 77406, 3133, 262144⟩ := by
  decide +kernel

theorem context_11_77406_1100621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77406 ⟨1100621, by decide⟩ :=
  accepted_of_selected 11 77406 ⟨1100621, by decide⟩ ⟨11, 2, 0, 1100621, 77406, 3133, 262144⟩
    (by decide) selected_cut_40464

theorem selected_cut_40465 : selected 10 ⟨1100675, by decide⟩
    (prefixPartial 11 77407) = some ⟨11, 2, 0, 1100675, 77407, 2289, 262144⟩ := by
  decide +kernel

theorem context_11_77407_1100675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77407 ⟨1100675, by decide⟩ :=
  accepted_of_selected 11 77407 ⟨1100675, by decide⟩ ⟨11, 2, 0, 1100675, 77407, 2289, 262144⟩
    (by decide) selected_cut_40465

theorem unmarked_context_10_19351_1100676 : frontier 11 ⟨1100676, by decide⟩
    (prefixCache 10 19351) (prefixPartial 10 19351) = false := by
  decide +kernel

theorem node_context_10_19351_1100676 : EJMOriginalGlobalDAGData.nodes 11 ⟨1100676, by decide⟩ =
    .split (coordinate 10) (![⟨1100486, by decide⟩,⟨1100553, by decide⟩,⟨1100621, by decide⟩,⟨1100675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19351_1100676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19351 ⟨1100676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19351
    ⟨1100676, by decide⟩ (by decide) (![⟨1100486, by decide⟩,⟨1100553, by decide⟩,⟨1100621, by decide⟩,⟨1100675, by decide⟩]) unmarked_context_10_19351_1100676 node_context_10_19351_1100676
  intro a
  fin_cases a
  · exact context_11_77404_1100486
  · exact context_11_77405_1100553
  · exact context_11_77406_1100621
  · exact context_11_77407_1100675

theorem unmarked_context_9_4837_1100677 : frontier 12 ⟨1100677, by decide⟩
    (prefixCache 9 4837) (prefixPartial 9 4837) = false := by
  decide +kernel

theorem node_context_9_4837_1100677 : EJMOriginalGlobalDAGData.nodes 12 ⟨1100677, by decide⟩ =
    .split (coordinate 9) (![⟨1100070, by decide⟩,⟨893098, by decide⟩,⟨1100393, by decide⟩,⟨1100676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4837_1100677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4837 ⟨1100677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4837
    ⟨1100677, by decide⟩ (by decide) (![⟨1100070, by decide⟩,⟨893098, by decide⟩,⟨1100393, by decide⟩,⟨1100676, by decide⟩]) unmarked_context_9_4837_1100677 node_context_9_4837_1100677
  intro a
  fin_cases a
  · exact context_10_19348_1100070
  · exact context_10_19349_893098
  · exact context_10_19350_1100393
  · exact context_10_19351_1100676

theorem selected_cut_40466 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 4838) = some ⟨9, 1, 0, 33466, 4838, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4838_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4838 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 4838 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 4838, 1, 4194304⟩
    (by decide) selected_cut_40466

theorem selected_cut_40467 : selected 10 ⟨1100728, by decide⟩
    (prefixPartial 11 77424) = some ⟨11, 2, 0, 1100728, 77424, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_77424_1100728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77424 ⟨1100728, by decide⟩ :=
  accepted_of_selected 11 77424 ⟨1100728, by decide⟩ ⟨11, 2, 0, 1100728, 77424, 1949, 262144⟩
    (by decide) selected_cut_40467

theorem selected_cut_40468 : selected 10 ⟨1100775, by decide⟩
    (prefixPartial 11 77425) = some ⟨11, 2, 0, 1100775, 77425, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_77425_1100775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77425 ⟨1100775, by decide⟩ :=
  accepted_of_selected 11 77425 ⟨1100775, by decide⟩ ⟨11, 2, 0, 1100775, 77425, 1597, 262144⟩
    (by decide) selected_cut_40468

theorem selected_cut_40469 : selected 10 ⟨1100811, by decide⟩
    (prefixPartial 11 77426) = some ⟨11, 2, 0, 1100811, 77426, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_77426_1100811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77426 ⟨1100811, by decide⟩ :=
  accepted_of_selected 11 77426 ⟨1100811, by decide⟩ ⟨11, 2, 0, 1100811, 77426, 1313, 262144⟩
    (by decide) selected_cut_40469

theorem selected_cut_40470 : selected 10 ⟨1100898, by decide⟩
    (prefixPartial 11 77427) = some ⟨11, 2, 0, 1100898, 77427, 1237, 262144⟩ := by
  decide +kernel

theorem context_11_77427_1100898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77427 ⟨1100898, by decide⟩ :=
  accepted_of_selected 11 77427 ⟨1100898, by decide⟩ ⟨11, 2, 0, 1100898, 77427, 1237, 262144⟩
    (by decide) selected_cut_40470

theorem unmarked_context_10_19356_1100899 : frontier 11 ⟨1100899, by decide⟩
    (prefixCache 10 19356) (prefixPartial 10 19356) = false := by
  decide +kernel

theorem node_context_10_19356_1100899 : EJMOriginalGlobalDAGData.nodes 11 ⟨1100899, by decide⟩ =
    .split (coordinate 10) (![⟨1100728, by decide⟩,⟨1100775, by decide⟩,⟨1100811, by decide⟩,⟨1100898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19356_1100899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19356 ⟨1100899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19356
    ⟨1100899, by decide⟩ (by decide) (![⟨1100728, by decide⟩,⟨1100775, by decide⟩,⟨1100811, by decide⟩,⟨1100898, by decide⟩]) unmarked_context_10_19356_1100899 node_context_10_19356_1100899
  intro a
  fin_cases a
  · exact context_11_77424_1100728
  · exact context_11_77425_1100775
  · exact context_11_77426_1100811
  · exact context_11_77427_1100898

theorem selected_cut_40471 : selected 11 ⟨1100984, by decide⟩
    (prefixPartial 10 19357) = some ⟨10, 2, 0, 1100984, 19357, 1893, 1048576⟩ := by
  decide +kernel

theorem context_10_19357_1100984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19357 ⟨1100984, by decide⟩ :=
  accepted_of_selected 10 19357 ⟨1100984, by decide⟩ ⟨10, 2, 0, 1100984, 19357, 1893, 1048576⟩
    (by decide) selected_cut_40471

theorem selected_cut_40472 : selected 11 ⟨1101009, by decide⟩
    (prefixPartial 10 19358) = some ⟨10, 2, 0, 1101009, 19358, 313, 1048576⟩ := by
  decide +kernel

theorem context_10_19358_1101009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19358 ⟨1101009, by decide⟩ :=
  accepted_of_selected 10 19358 ⟨1101009, by decide⟩ ⟨10, 2, 0, 1101009, 19358, 313, 1048576⟩
    (by decide) selected_cut_40472

theorem selected_cut_40473 : selected 11 ⟨1101010, by decide⟩
    (prefixPartial 10 19359) = some ⟨10, 2, 0, 1101010, 19359, 25, 1048576⟩ := by
  decide +kernel

theorem context_10_19359_1101010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19359 ⟨1101010, by decide⟩ :=
  accepted_of_selected 10 19359 ⟨1101010, by decide⟩ ⟨10, 2, 0, 1101010, 19359, 25, 1048576⟩
    (by decide) selected_cut_40473

theorem unmarked_context_9_4839_1101011 : frontier 12 ⟨1101011, by decide⟩
    (prefixCache 9 4839) (prefixPartial 9 4839) = false := by
  decide +kernel

theorem node_context_9_4839_1101011 : EJMOriginalGlobalDAGData.nodes 12 ⟨1101011, by decide⟩ =
    .split (coordinate 9) (![⟨1100899, by decide⟩,⟨1100984, by decide⟩,⟨1101009, by decide⟩,⟨1101010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4839_1101011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4839 ⟨1101011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4839
    ⟨1101011, by decide⟩ (by decide) (![⟨1100899, by decide⟩,⟨1100984, by decide⟩,⟨1101009, by decide⟩,⟨1101010, by decide⟩]) unmarked_context_9_4839_1101011 node_context_9_4839_1101011
  intro a
  fin_cases a
  · exact context_10_19356_1100899
  · exact context_10_19357_1100984
  · exact context_10_19358_1101009
  · exact context_10_19359_1101010

theorem unmarked_context_8_1209_1101012 : frontier 13 ⟨1101012, by decide⟩
    (prefixCache 8 1209) (prefixPartial 8 1209) = false := by
  decide +kernel

theorem node_context_8_1209_1101012 : EJMOriginalGlobalDAGData.nodes 13 ⟨1101012, by decide⟩ =
    .split (coordinate 8) (![⟨1099532, by decide⟩,⟨1100677, by decide⟩,⟨33466, by decide⟩,⟨1101011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1209_1101012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1209 ⟨1101012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1209
    ⟨1101012, by decide⟩ (by decide) (![⟨1099532, by decide⟩,⟨1100677, by decide⟩,⟨33466, by decide⟩,⟨1101011, by decide⟩]) unmarked_context_8_1209_1101012 node_context_8_1209_1101012
  intro a
  fin_cases a
  · exact context_9_4836_1099532
  · exact context_9_4837_1100677
  · exact context_9_4838_33466
  · exact context_9_4839_1101011

theorem selected_cut_40474 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1210) = some ⟨8, 1, 0, 979897, 1210, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1210_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1210 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1210 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1210, 1, 16777216⟩
    (by decide) selected_cut_40474

theorem selected_cut_40475 : selected 10 ⟨1101055, by decide⟩
    (prefixPartial 11 77504) = some ⟨11, 2, 0, 1101055, 77504, 1809, 262144⟩ := by
  decide +kernel

theorem context_11_77504_1101055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77504 ⟨1101055, by decide⟩ :=
  accepted_of_selected 11 77504 ⟨1101055, by decide⟩ ⟨11, 2, 0, 1101055, 77504, 1809, 262144⟩
    (by decide) selected_cut_40475

theorem selected_cut_40476 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 310020) = some ⟨12, 1, 0, 34034, 310020, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310020_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310020 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 310020 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 310020, 1, 65536⟩
    (by decide) selected_cut_40476

theorem selected_cut_40477 : selected 8 ⟨1101086, by decide⟩
    (prefixPartial 13 1240084) = some ⟨13, 2, 0, 1101086, 1240084, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_1240084_1101086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1240084 ⟨1101086, by decide⟩ :=
  accepted_of_selected 13 1240084 ⟨1101086, by decide⟩ ⟨13, 2, 0, 1101086, 1240084, 1709, 16384⟩
    (by decide) selected_cut_40477

theorem selected_cut_40478 : selected 8 ⟨1101102, by decide⟩
    (prefixPartial 13 1240085) = some ⟨13, 2, 0, 1101102, 1240085, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_1240085_1101102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1240085 ⟨1101102, by decide⟩ :=
  accepted_of_selected 13 1240085 ⟨1101102, by decide⟩ ⟨13, 2, 0, 1101102, 1240085, 1065, 16384⟩
    (by decide) selected_cut_40478

theorem selected_cut_40479 : selected 8 ⟨1101117, by decide⟩
    (prefixPartial 13 1240086) = some ⟨13, 2, 0, 1101117, 1240086, 745, 16384⟩ := by
  decide +kernel

theorem context_13_1240086_1101117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1240086 ⟨1101117, by decide⟩ :=
  accepted_of_selected 13 1240086 ⟨1101117, by decide⟩ ⟨13, 2, 0, 1101117, 1240086, 745, 16384⟩
    (by decide) selected_cut_40479

theorem selected_cut_40480 : selected 8 ⟨1101126, by decide⟩
    (prefixPartial 13 1240087) = some ⟨13, 2, 0, 1101126, 1240087, 577, 16384⟩ := by
  decide +kernel

theorem context_13_1240087_1101126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1240087 ⟨1101126, by decide⟩ :=
  accepted_of_selected 13 1240087 ⟨1101126, by decide⟩ ⟨13, 2, 0, 1101126, 1240087, 577, 16384⟩
    (by decide) selected_cut_40480

theorem unmarked_context_12_310021_1101127 : frontier 9 ⟨1101127, by decide⟩
    (prefixCache 12 310021) (prefixPartial 12 310021) = false := by
  decide +kernel

theorem node_context_12_310021_1101127 : EJMOriginalGlobalDAGData.nodes 9 ⟨1101127, by decide⟩ =
    .split (coordinate 12) (![⟨1101086, by decide⟩,⟨1101102, by decide⟩,⟨1101117, by decide⟩,⟨1101126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_310021_1101127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310021 ⟨1101127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 310021
    ⟨1101127, by decide⟩ (by decide) (![⟨1101086, by decide⟩,⟨1101102, by decide⟩,⟨1101117, by decide⟩,⟨1101126, by decide⟩]) unmarked_context_12_310021_1101127 node_context_12_310021_1101127
  intro a
  fin_cases a
  · exact context_13_1240084_1101086
  · exact context_13_1240085_1101102
  · exact context_13_1240086_1101117
  · exact context_13_1240087_1101126

theorem selected_cut_40481 : selected 9 ⟨1101191, by decide⟩
    (prefixPartial 12 310022) = some ⟨12, 2, 0, 1101191, 310022, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_310022_1101191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310022 ⟨1101191, by decide⟩ :=
  accepted_of_selected 12 310022 ⟨1101191, by decide⟩ ⟨12, 2, 0, 1101191, 310022, 3617, 65536⟩
    (by decide) selected_cut_40481

theorem selected_cut_40482 : selected 9 ⟨1101243, by decide⟩
    (prefixPartial 12 310023) = some ⟨12, 2, 0, 1101243, 310023, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_310023_1101243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310023 ⟨1101243, by decide⟩ :=
  accepted_of_selected 12 310023 ⟨1101243, by decide⟩ ⟨12, 2, 0, 1101243, 310023, 3149, 65536⟩
    (by decide) selected_cut_40482

theorem unmarked_context_11_77505_1101244 : frontier 10 ⟨1101244, by decide⟩
    (prefixCache 11 77505) (prefixPartial 11 77505) = false := by
  decide +kernel

theorem node_context_11_77505_1101244 : EJMOriginalGlobalDAGData.nodes 10 ⟨1101244, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1101127, by decide⟩,⟨1101191, by decide⟩,⟨1101243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77505_1101244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77505 ⟨1101244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77505
    ⟨1101244, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1101127, by decide⟩,⟨1101191, by decide⟩,⟨1101243, by decide⟩]) unmarked_context_11_77505_1101244 node_context_11_77505_1101244
  intro a
  fin_cases a
  · exact context_12_310020_34034
  · exact context_12_310021_1101127
  · exact context_12_310022_1101191
  · exact context_12_310023_1101243

theorem selected_cut_40483 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 310024) = some ⟨12, 1, 0, 34034, 310024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310024_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310024 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 310024 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 310024, 1, 65536⟩
    (by decide) selected_cut_40483

theorem selected_cut_40484 : selected 9 ⟨1101296, by decide⟩
    (prefixPartial 12 310025) = some ⟨12, 2, 0, 1101296, 310025, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_310025_1101296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310025 ⟨1101296, by decide⟩ :=
  accepted_of_selected 12 310025 ⟨1101296, by decide⟩ ⟨12, 2, 0, 1101296, 310025, 3557, 65536⟩
    (by decide) selected_cut_40484

theorem selected_cut_40485 : selected 9 ⟨1101344, by decide⟩
    (prefixPartial 12 310026) = some ⟨12, 2, 0, 1101344, 310026, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_310026_1101344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310026 ⟨1101344, by decide⟩ :=
  accepted_of_selected 12 310026 ⟨1101344, by decide⟩ ⟨12, 2, 0, 1101344, 310026, 3229, 65536⟩
    (by decide) selected_cut_40485

theorem selected_cut_40486 : selected 9 ⟨1101389, by decide⟩
    (prefixPartial 12 310027) = some ⟨12, 2, 0, 1101389, 310027, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_310027_1101389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310027 ⟨1101389, by decide⟩ :=
  accepted_of_selected 12 310027 ⟨1101389, by decide⟩ ⟨12, 2, 0, 1101389, 310027, 3037, 65536⟩
    (by decide) selected_cut_40486

theorem unmarked_context_11_77506_1101390 : frontier 10 ⟨1101390, by decide⟩
    (prefixCache 11 77506) (prefixPartial 11 77506) = false := by
  decide +kernel

theorem node_context_11_77506_1101390 : EJMOriginalGlobalDAGData.nodes 10 ⟨1101390, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1101296, by decide⟩,⟨1101344, by decide⟩,⟨1101389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77506_1101390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77506 ⟨1101390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77506
    ⟨1101390, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1101296, by decide⟩,⟨1101344, by decide⟩,⟨1101389, by decide⟩]) unmarked_context_11_77506_1101390 node_context_11_77506_1101390
  intro a
  fin_cases a
  · exact context_12_310024_34034
  · exact context_12_310025_1101296
  · exact context_12_310026_1101344
  · exact context_12_310027_1101389

theorem selected_cut_40487 : selected 9 ⟨1101477, by decide⟩
    (prefixPartial 12 310028) = some ⟨12, 2, 0, 1101477, 310028, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_310028_1101477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310028 ⟨1101477, by decide⟩ :=
  accepted_of_selected 12 310028 ⟨1101477, by decide⟩ ⟨12, 2, 0, 1101477, 310028, 3857, 65536⟩
    (by decide) selected_cut_40487

theorem selected_cut_40488 : selected 9 ⟨1101541, by decide⟩
    (prefixPartial 12 310029) = some ⟨12, 2, 0, 1101541, 310029, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_310029_1101541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310029 ⟨1101541, by decide⟩ :=
  accepted_of_selected 12 310029 ⟨1101541, by decide⟩ ⟨12, 2, 0, 1101541, 310029, 3857, 65536⟩
    (by decide) selected_cut_40488

theorem selected_cut_40489 : selected 9 ⟨1101612, by decide⟩
    (prefixPartial 12 310030) = some ⟨12, 2, 0, 1101612, 310030, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_310030_1101612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310030 ⟨1101612, by decide⟩ :=
  accepted_of_selected 12 310030 ⟨1101612, by decide⟩ ⟨12, 2, 0, 1101612, 310030, 3649, 65536⟩
    (by decide) selected_cut_40489

theorem selected_cut_40490 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 310031) = some ⟨12, 1, 0, 903806, 310031, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310031_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310031 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 310031 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 310031, 1, 65536⟩
    (by decide) selected_cut_40490

theorem unmarked_context_11_77507_1101613 : frontier 10 ⟨1101613, by decide⟩
    (prefixCache 11 77507) (prefixPartial 11 77507) = false := by
  decide +kernel

theorem node_context_11_77507_1101613 : EJMOriginalGlobalDAGData.nodes 10 ⟨1101613, by decide⟩ =
    .split (coordinate 11) (![⟨1101477, by decide⟩,⟨1101541, by decide⟩,⟨1101612, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77507_1101613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77507 ⟨1101613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77507
    ⟨1101613, by decide⟩ (by decide) (![⟨1101477, by decide⟩,⟨1101541, by decide⟩,⟨1101612, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77507_1101613 node_context_11_77507_1101613
  intro a
  fin_cases a
  · exact context_12_310028_1101477
  · exact context_12_310029_1101541
  · exact context_12_310030_1101612
  · exact context_12_310031_903806

theorem unmarked_context_10_19376_1101614 : frontier 11 ⟨1101614, by decide⟩
    (prefixCache 10 19376) (prefixPartial 10 19376) = false := by
  decide +kernel

theorem node_context_10_19376_1101614 : EJMOriginalGlobalDAGData.nodes 11 ⟨1101614, by decide⟩ =
    .split (coordinate 10) (![⟨1101055, by decide⟩,⟨1101244, by decide⟩,⟨1101390, by decide⟩,⟨1101613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19376_1101614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19376 ⟨1101614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19376
    ⟨1101614, by decide⟩ (by decide) (![⟨1101055, by decide⟩,⟨1101244, by decide⟩,⟨1101390, by decide⟩,⟨1101613, by decide⟩]) unmarked_context_10_19376_1101614 node_context_10_19376_1101614
  intro a
  fin_cases a
  · exact context_11_77504_1101055
  · exact context_11_77505_1101244
  · exact context_11_77506_1101390
  · exact context_11_77507_1101613

theorem selected_cut_40491 : selected 9 ⟨1101657, by decide⟩
    (prefixPartial 12 310032) = some ⟨12, 2, 0, 1101657, 310032, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_310032_1101657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310032 ⟨1101657, by decide⟩ :=
  accepted_of_selected 12 310032 ⟨1101657, by decide⟩ ⟨12, 2, 0, 1101657, 310032, 1657, 65536⟩
    (by decide) selected_cut_40491

theorem selected_cut_40492 : selected 9 ⟨1101703, by decide⟩
    (prefixPartial 12 310033) = some ⟨12, 2, 0, 1101703, 310033, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_310033_1101703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310033 ⟨1101703, by decide⟩ :=
  accepted_of_selected 12 310033 ⟨1101703, by decide⟩ ⟨12, 2, 0, 1101703, 310033, 3093, 65536⟩
    (by decide) selected_cut_40492

theorem selected_cut_40493 : selected 9 ⟨1101743, by decide⟩
    (prefixPartial 12 310034) = some ⟨12, 2, 0, 1101743, 310034, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_310034_1101743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310034 ⟨1101743, by decide⟩ :=
  accepted_of_selected 12 310034 ⟨1101743, by decide⟩ ⟨12, 2, 0, 1101743, 310034, 2709, 65536⟩
    (by decide) selected_cut_40493

theorem selected_cut_40494 : selected 9 ⟨1101783, by decide⟩
    (prefixPartial 12 310035) = some ⟨12, 2, 0, 1101783, 310035, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_310035_1101783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310035 ⟨1101783, by decide⟩ :=
  accepted_of_selected 12 310035 ⟨1101783, by decide⟩ ⟨12, 2, 0, 1101783, 310035, 2605, 65536⟩
    (by decide) selected_cut_40494

theorem unmarked_context_11_77508_1101784 : frontier 10 ⟨1101784, by decide⟩
    (prefixCache 11 77508) (prefixPartial 11 77508) = false := by
  decide +kernel

theorem node_context_11_77508_1101784 : EJMOriginalGlobalDAGData.nodes 10 ⟨1101784, by decide⟩ =
    .split (coordinate 11) (![⟨1101657, by decide⟩,⟨1101703, by decide⟩,⟨1101743, by decide⟩,⟨1101783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77508_1101784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77508 ⟨1101784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77508
    ⟨1101784, by decide⟩ (by decide) (![⟨1101657, by decide⟩,⟨1101703, by decide⟩,⟨1101743, by decide⟩,⟨1101783, by decide⟩]) unmarked_context_11_77508_1101784 node_context_11_77508_1101784
  intro a
  fin_cases a
  · exact context_12_310032_1101657
  · exact context_12_310033_1101703
  · exact context_12_310034_1101743
  · exact context_12_310035_1101783

theorem selected_cut_40495 : selected 9 ⟨1101828, by decide⟩
    (prefixPartial 12 310036) = some ⟨12, 2, 0, 1101828, 310036, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_310036_1101828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310036 ⟨1101828, by decide⟩ :=
  accepted_of_selected 12 310036 ⟨1101828, by decide⟩ ⟨12, 2, 0, 1101828, 310036, 2981, 65536⟩
    (by decide) selected_cut_40495

theorem selected_cut_40496 : selected 9 ⟨969470, by decide⟩
    (prefixPartial 12 310037) = some ⟨12, 1, 0, 969470, 310037, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310037_969470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310037 ⟨969470, by decide⟩ :=
  accepted_of_selected 12 310037 ⟨969470, by decide⟩ ⟨12, 1, 0, 969470, 310037, 1, 65536⟩
    (by decide) selected_cut_40496

theorem selected_cut_40497 : selected 9 ⟨1101870, by decide⟩
    (prefixPartial 12 310038) = some ⟨12, 2, 0, 1101870, 310038, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_310038_1101870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310038 ⟨1101870, by decide⟩ :=
  accepted_of_selected 12 310038 ⟨1101870, by decide⟩ ⟨12, 2, 0, 1101870, 310038, 3025, 65536⟩
    (by decide) selected_cut_40497

theorem selected_cut_40498 : selected 9 ⟨1101912, by decide⟩
    (prefixPartial 12 310039) = some ⟨12, 2, 0, 1101912, 310039, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_310039_1101912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310039 ⟨1101912, by decide⟩ :=
  accepted_of_selected 12 310039 ⟨1101912, by decide⟩ ⟨12, 2, 0, 1101912, 310039, 2817, 65536⟩
    (by decide) selected_cut_40498

theorem unmarked_context_11_77509_1101913 : frontier 10 ⟨1101913, by decide⟩
    (prefixCache 11 77509) (prefixPartial 11 77509) = false := by
  decide +kernel

theorem node_context_11_77509_1101913 : EJMOriginalGlobalDAGData.nodes 10 ⟨1101913, by decide⟩ =
    .split (coordinate 11) (![⟨1101828, by decide⟩,⟨969470, by decide⟩,⟨1101870, by decide⟩,⟨1101912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77509_1101913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77509 ⟨1101913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77509
    ⟨1101913, by decide⟩ (by decide) (![⟨1101828, by decide⟩,⟨969470, by decide⟩,⟨1101870, by decide⟩,⟨1101912, by decide⟩]) unmarked_context_11_77509_1101913 node_context_11_77509_1101913
  intro a
  fin_cases a
  · exact context_12_310036_1101828
  · exact context_12_310037_969470
  · exact context_12_310038_1101870
  · exact context_12_310039_1101912

theorem selected_cut_40499 : selected 9 ⟨1101955, by decide⟩
    (prefixPartial 12 310040) = some ⟨12, 2, 0, 1101955, 310040, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_310040_1101955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310040 ⟨1101955, by decide⟩ :=
  accepted_of_selected 12 310040 ⟨1101955, by decide⟩ ⟨12, 2, 0, 1101955, 310040, 2689, 65536⟩
    (by decide) selected_cut_40499

theorem selected_cut_40500 : selected 9 ⟨1101993, by decide⟩
    (prefixPartial 12 310041) = some ⟨12, 2, 0, 1101993, 310041, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_310041_1101993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310041 ⟨1101993, by decide⟩ :=
  accepted_of_selected 12 310041 ⟨1101993, by decide⟩ ⟨12, 2, 0, 1101993, 310041, 3069, 65536⟩
    (by decide) selected_cut_40500

theorem selected_cut_40501 : selected 9 ⟨1102036, by decide⟩
    (prefixPartial 12 310042) = some ⟨12, 2, 0, 1102036, 310042, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_310042_1102036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310042 ⟨1102036, by decide⟩ :=
  accepted_of_selected 12 310042 ⟨1102036, by decide⟩ ⟨12, 2, 0, 1102036, 310042, 2701, 65536⟩
    (by decide) selected_cut_40501

theorem selected_cut_40502 : selected 9 ⟨1102077, by decide⟩
    (prefixPartial 12 310043) = some ⟨12, 2, 0, 1102077, 310043, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_310043_1102077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310043 ⟨1102077, by decide⟩ :=
  accepted_of_selected 12 310043 ⟨1102077, by decide⟩ ⟨12, 2, 0, 1102077, 310043, 2729, 65536⟩
    (by decide) selected_cut_40502

theorem unmarked_context_11_77510_1102078 : frontier 10 ⟨1102078, by decide⟩
    (prefixCache 11 77510) (prefixPartial 11 77510) = false := by
  decide +kernel

theorem node_context_11_77510_1102078 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102078, by decide⟩ =
    .split (coordinate 11) (![⟨1101955, by decide⟩,⟨1101993, by decide⟩,⟨1102036, by decide⟩,⟨1102077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77510_1102078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77510 ⟨1102078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77510
    ⟨1102078, by decide⟩ (by decide) (![⟨1101955, by decide⟩,⟨1101993, by decide⟩,⟨1102036, by decide⟩,⟨1102077, by decide⟩]) unmarked_context_11_77510_1102078 node_context_11_77510_1102078
  intro a
  fin_cases a
  · exact context_12_310040_1101955
  · exact context_12_310041_1101993
  · exact context_12_310042_1102036
  · exact context_12_310043_1102077

theorem selected_cut_40503 : selected 9 ⟨1102122, by decide⟩
    (prefixPartial 12 310044) = some ⟨12, 2, 0, 1102122, 310044, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_310044_1102122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310044 ⟨1102122, by decide⟩ :=
  accepted_of_selected 12 310044 ⟨1102122, by decide⟩ ⟨12, 2, 0, 1102122, 310044, 2873, 65536⟩
    (by decide) selected_cut_40503

theorem selected_cut_40504 : selected 9 ⟨1102168, by decide⟩
    (prefixPartial 12 310045) = some ⟨12, 2, 0, 1102168, 310045, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_310045_1102168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310045 ⟨1102168, by decide⟩ :=
  accepted_of_selected 12 310045 ⟨1102168, by decide⟩ ⟨12, 2, 0, 1102168, 310045, 3045, 65536⟩
    (by decide) selected_cut_40504

theorem selected_cut_40505 : selected 9 ⟨1102209, by decide⟩
    (prefixPartial 12 310046) = some ⟨12, 2, 0, 1102209, 310046, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_310046_1102209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310046 ⟨1102209, by decide⟩ :=
  accepted_of_selected 12 310046 ⟨1102209, by decide⟩ ⟨12, 2, 0, 1102209, 310046, 2833, 65536⟩
    (by decide) selected_cut_40505

theorem selected_cut_40506 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 310047) = some ⟨12, 1, 0, 903806, 310047, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310047_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310047 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 310047 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 310047, 1, 65536⟩
    (by decide) selected_cut_40506

theorem unmarked_context_11_77511_1102210 : frontier 10 ⟨1102210, by decide⟩
    (prefixCache 11 77511) (prefixPartial 11 77511) = false := by
  decide +kernel

theorem node_context_11_77511_1102210 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102210, by decide⟩ =
    .split (coordinate 11) (![⟨1102122, by decide⟩,⟨1102168, by decide⟩,⟨1102209, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77511_1102210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77511 ⟨1102210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77511
    ⟨1102210, by decide⟩ (by decide) (![⟨1102122, by decide⟩,⟨1102168, by decide⟩,⟨1102209, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77511_1102210 node_context_11_77511_1102210
  intro a
  fin_cases a
  · exact context_12_310044_1102122
  · exact context_12_310045_1102168
  · exact context_12_310046_1102209
  · exact context_12_310047_903806

theorem unmarked_context_10_19377_1102211 : frontier 11 ⟨1102211, by decide⟩
    (prefixCache 10 19377) (prefixPartial 10 19377) = false := by
  decide +kernel

theorem node_context_10_19377_1102211 : EJMOriginalGlobalDAGData.nodes 11 ⟨1102211, by decide⟩ =
    .split (coordinate 10) (![⟨1101784, by decide⟩,⟨1101913, by decide⟩,⟨1102078, by decide⟩,⟨1102210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19377_1102211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19377 ⟨1102211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19377
    ⟨1102211, by decide⟩ (by decide) (![⟨1101784, by decide⟩,⟨1101913, by decide⟩,⟨1102078, by decide⟩,⟨1102210, by decide⟩]) unmarked_context_10_19377_1102211 node_context_10_19377_1102211
  intro a
  fin_cases a
  · exact context_11_77508_1101784
  · exact context_11_77509_1101913
  · exact context_11_77510_1102078
  · exact context_11_77511_1102210

theorem selected_cut_40507 : selected 9 ⟨1082322, by decide⟩
    (prefixPartial 12 310048) = some ⟨12, 1, 0, 1082322, 310048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310048_1082322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310048 ⟨1082322, by decide⟩ :=
  accepted_of_selected 12 310048 ⟨1082322, by decide⟩ ⟨12, 1, 0, 1082322, 310048, 1, 65536⟩
    (by decide) selected_cut_40507

theorem selected_cut_40508 : selected 9 ⟨1102244, by decide⟩
    (prefixPartial 12 310049) = some ⟨12, 2, 0, 1102244, 310049, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_310049_1102244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310049 ⟨1102244, by decide⟩ :=
  accepted_of_selected 12 310049 ⟨1102244, by decide⟩ ⟨12, 2, 0, 1102244, 310049, 2545, 65536⟩
    (by decide) selected_cut_40508

theorem selected_cut_40509 : selected 9 ⟨1102286, by decide⟩
    (prefixPartial 12 310050) = some ⟨12, 2, 0, 1102286, 310050, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_310050_1102286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310050 ⟨1102286, by decide⟩ :=
  accepted_of_selected 12 310050 ⟨1102286, by decide⟩ ⟨12, 2, 0, 1102286, 310050, 2365, 65536⟩
    (by decide) selected_cut_40509

theorem selected_cut_40510 : selected 9 ⟨1102320, by decide⟩
    (prefixPartial 12 310051) = some ⟨12, 2, 0, 1102320, 310051, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_310051_1102320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310051 ⟨1102320, by decide⟩ :=
  accepted_of_selected 12 310051 ⟨1102320, by decide⟩ ⟨12, 2, 0, 1102320, 310051, 2069, 65536⟩
    (by decide) selected_cut_40510

theorem unmarked_context_11_77512_1102321 : frontier 10 ⟨1102321, by decide⟩
    (prefixCache 11 77512) (prefixPartial 11 77512) = false := by
  decide +kernel

theorem node_context_11_77512_1102321 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102321, by decide⟩ =
    .split (coordinate 11) (![⟨1082322, by decide⟩,⟨1102244, by decide⟩,⟨1102286, by decide⟩,⟨1102320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77512_1102321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77512 ⟨1102321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77512
    ⟨1102321, by decide⟩ (by decide) (![⟨1082322, by decide⟩,⟨1102244, by decide⟩,⟨1102286, by decide⟩,⟨1102320, by decide⟩]) unmarked_context_11_77512_1102321 node_context_11_77512_1102321
  intro a
  fin_cases a
  · exact context_12_310048_1082322
  · exact context_12_310049_1102244
  · exact context_12_310050_1102286
  · exact context_12_310051_1102320

theorem selected_cut_40511 : selected 9 ⟨1102355, by decide⟩
    (prefixPartial 12 310052) = some ⟨12, 2, 0, 1102355, 310052, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_310052_1102355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310052 ⟨1102355, by decide⟩ :=
  accepted_of_selected 12 310052 ⟨1102355, by decide⟩ ⟨12, 2, 0, 1102355, 310052, 2557, 65536⟩
    (by decide) selected_cut_40511

theorem selected_cut_40512 : selected 9 ⟨1102400, by decide⟩
    (prefixPartial 12 310053) = some ⟨12, 2, 0, 1102400, 310053, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_310053_1102400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310053 ⟨1102400, by decide⟩ :=
  accepted_of_selected 12 310053 ⟨1102400, by decide⟩ ⟨12, 2, 0, 1102400, 310053, 2945, 65536⟩
    (by decide) selected_cut_40512

theorem selected_cut_40513 : selected 9 ⟨1102446, by decide⟩
    (prefixPartial 12 310054) = some ⟨12, 2, 0, 1102446, 310054, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_310054_1102446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310054 ⟨1102446, by decide⟩ :=
  accepted_of_selected 12 310054 ⟨1102446, by decide⟩ ⟨12, 2, 0, 1102446, 310054, 2537, 65536⟩
    (by decide) selected_cut_40513

theorem selected_cut_40514 : selected 9 ⟨1102490, by decide⟩
    (prefixPartial 12 310055) = some ⟨12, 2, 0, 1102490, 310055, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_310055_1102490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310055 ⟨1102490, by decide⟩ :=
  accepted_of_selected 12 310055 ⟨1102490, by decide⟩ ⟨12, 2, 0, 1102490, 310055, 2337, 65536⟩
    (by decide) selected_cut_40514

theorem unmarked_context_11_77513_1102491 : frontier 10 ⟨1102491, by decide⟩
    (prefixCache 11 77513) (prefixPartial 11 77513) = false := by
  decide +kernel

theorem node_context_11_77513_1102491 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102491, by decide⟩ =
    .split (coordinate 11) (![⟨1102355, by decide⟩,⟨1102400, by decide⟩,⟨1102446, by decide⟩,⟨1102490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77513_1102491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77513 ⟨1102491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77513
    ⟨1102491, by decide⟩ (by decide) (![⟨1102355, by decide⟩,⟨1102400, by decide⟩,⟨1102446, by decide⟩,⟨1102490, by decide⟩]) unmarked_context_11_77513_1102491 node_context_11_77513_1102491
  intro a
  fin_cases a
  · exact context_12_310052_1102355
  · exact context_12_310053_1102400
  · exact context_12_310054_1102446
  · exact context_12_310055_1102490

theorem selected_cut_40515 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 77514) = some ⟨11, 1, 0, 900587, 77514, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77514_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77514 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 77514 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 77514, 1, 262144⟩
    (by decide) selected_cut_40515

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
