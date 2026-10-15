/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover255
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_4827_621307 : frontier 11 ⟨621307, by decide⟩
    (prefixCache 10 4827) (prefixPartial 10 4827) = false := by
  decide +kernel

theorem node_context_10_4827_621307 : EJMOriginalGlobalDAGData.nodes 11 ⟨621307, by decide⟩ =
    .split (coordinate 10) (![⟨621121, by decide⟩,⟨621185, by decide⟩,⟨621252, by decide⟩,⟨621306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4827_621307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4827 ⟨621307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4827
    ⟨621307, by decide⟩ (by decide) (![⟨621121, by decide⟩,⟨621185, by decide⟩,⟨621252, by decide⟩,⟨621306, by decide⟩]) unmarked_context_10_4827_621307 node_context_10_4827_621307
  intro a
  fin_cases a
  · exact context_11_19308_621121
  · exact context_11_19309_621185
  · exact context_11_19310_621252
  · exact context_11_19311_621306

theorem unmarked_context_9_1206_621308 : frontier 12 ⟨621308, by decide⟩
    (prefixCache 9 1206) (prefixPartial 9 1206) = false := by
  decide +kernel

theorem node_context_9_1206_621308 : EJMOriginalGlobalDAGData.nodes 12 ⟨621308, by decide⟩ =
    .split (coordinate 9) (![⟨620270, by decide⟩,⟨620692, by decide⟩,⟨621050, by decide⟩,⟨621307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1206_621308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1206 ⟨621308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1206
    ⟨621308, by decide⟩ (by decide) (![⟨620270, by decide⟩,⟨620692, by decide⟩,⟨621050, by decide⟩,⟨621307, by decide⟩]) unmarked_context_9_1206_621308 node_context_9_1206_621308
  intro a
  fin_cases a
  · exact context_10_4824_620270
  · exact context_10_4825_620692
  · exact context_10_4826_621050
  · exact context_10_4827_621307

theorem selected_cut_24580 : selected 9 ⟨621316, by decide⟩
    (prefixPartial 12 77248) = some ⟨12, 2, 0, 621316, 77248, 881, 65536⟩ := by
  decide +kernel

theorem context_12_77248_621316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77248 ⟨621316, by decide⟩ :=
  accepted_of_selected 12 77248 ⟨621316, by decide⟩ ⟨12, 2, 0, 621316, 77248, 881, 65536⟩
    (by decide) selected_cut_24580

theorem selected_cut_24581 : selected 9 ⟨621324, by decide⟩
    (prefixPartial 12 77249) = some ⟨12, 2, 0, 621324, 77249, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_77249_621324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77249 ⟨621324, by decide⟩ :=
  accepted_of_selected 12 77249 ⟨621324, by decide⟩ ⟨12, 2, 0, 621324, 77249, 1013, 65536⟩
    (by decide) selected_cut_24581

theorem selected_cut_24582 : selected 9 ⟨621330, by decide⟩
    (prefixPartial 12 77250) = some ⟨12, 2, 0, 621330, 77250, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_77250_621330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77250 ⟨621330, by decide⟩ :=
  accepted_of_selected 12 77250 ⟨621330, by decide⟩ ⟨12, 2, 0, 621330, 77250, 1125, 65536⟩
    (by decide) selected_cut_24582

theorem selected_cut_24583 : selected 9 ⟨621349, by decide⟩
    (prefixPartial 12 77251) = some ⟨12, 2, 0, 621349, 77251, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_77251_621349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77251 ⟨621349, by decide⟩ :=
  accepted_of_selected 12 77251 ⟨621349, by decide⟩ ⟨12, 2, 0, 621349, 77251, 1145, 65536⟩
    (by decide) selected_cut_24583

theorem unmarked_context_11_19312_621350 : frontier 10 ⟨621350, by decide⟩
    (prefixCache 11 19312) (prefixPartial 11 19312) = false := by
  decide +kernel

theorem node_context_11_19312_621350 : EJMOriginalGlobalDAGData.nodes 10 ⟨621350, by decide⟩ =
    .split (coordinate 11) (![⟨621316, by decide⟩,⟨621324, by decide⟩,⟨621330, by decide⟩,⟨621349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19312_621350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19312 ⟨621350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19312
    ⟨621350, by decide⟩ (by decide) (![⟨621316, by decide⟩,⟨621324, by decide⟩,⟨621330, by decide⟩,⟨621349, by decide⟩]) unmarked_context_11_19312_621350 node_context_11_19312_621350
  intro a
  fin_cases a
  · exact context_12_77248_621316
  · exact context_12_77249_621324
  · exact context_12_77250_621330
  · exact context_12_77251_621349

theorem selected_cut_24584 : selected 10 ⟨621386, by decide⟩
    (prefixPartial 11 19313) = some ⟨11, 2, 0, 621386, 19313, 3553, 262144⟩ := by
  decide +kernel

theorem context_11_19313_621386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19313 ⟨621386, by decide⟩ :=
  accepted_of_selected 11 19313 ⟨621386, by decide⟩ ⟨11, 2, 0, 621386, 19313, 3553, 262144⟩
    (by decide) selected_cut_24584

theorem selected_cut_24585 : selected 10 ⟨621415, by decide⟩
    (prefixPartial 11 19314) = some ⟨11, 2, 0, 621415, 19314, 3329, 262144⟩ := by
  decide +kernel

theorem context_11_19314_621415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19314 ⟨621415, by decide⟩ :=
  accepted_of_selected 11 19314 ⟨621415, by decide⟩ ⟨11, 2, 0, 621415, 19314, 3329, 262144⟩
    (by decide) selected_cut_24585

theorem selected_cut_24586 : selected 10 ⟨621448, by decide⟩
    (prefixPartial 11 19315) = some ⟨11, 2, 0, 621448, 19315, 3029, 262144⟩ := by
  decide +kernel

theorem context_11_19315_621448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19315 ⟨621448, by decide⟩ :=
  accepted_of_selected 11 19315 ⟨621448, by decide⟩ ⟨11, 2, 0, 621448, 19315, 3029, 262144⟩
    (by decide) selected_cut_24586

theorem unmarked_context_10_4828_621449 : frontier 11 ⟨621449, by decide⟩
    (prefixCache 10 4828) (prefixPartial 10 4828) = false := by
  decide +kernel

theorem node_context_10_4828_621449 : EJMOriginalGlobalDAGData.nodes 11 ⟨621449, by decide⟩ =
    .split (coordinate 10) (![⟨621350, by decide⟩,⟨621386, by decide⟩,⟨621415, by decide⟩,⟨621448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4828_621449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4828 ⟨621449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4828
    ⟨621449, by decide⟩ (by decide) (![⟨621350, by decide⟩,⟨621386, by decide⟩,⟨621415, by decide⟩,⟨621448, by decide⟩]) unmarked_context_10_4828_621449 node_context_10_4828_621449
  intro a
  fin_cases a
  · exact context_11_19312_621350
  · exact context_11_19313_621386
  · exact context_11_19314_621415
  · exact context_11_19315_621448

theorem selected_cut_24587 : selected 10 ⟨621483, by decide⟩
    (prefixPartial 11 19316) = some ⟨11, 2, 0, 621483, 19316, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_19316_621483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19316 ⟨621483, by decide⟩ :=
  accepted_of_selected 11 19316 ⟨621483, by decide⟩ ⟨11, 2, 0, 621483, 19316, 2717, 262144⟩
    (by decide) selected_cut_24587

theorem selected_cut_24588 : selected 10 ⟨621507, by decide⟩
    (prefixPartial 11 19317) = some ⟨11, 2, 0, 621507, 19317, 1729, 262144⟩ := by
  decide +kernel

theorem context_11_19317_621507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19317 ⟨621507, by decide⟩ :=
  accepted_of_selected 11 19317 ⟨621507, by decide⟩ ⟨11, 2, 0, 621507, 19317, 1729, 262144⟩
    (by decide) selected_cut_24588

theorem selected_cut_24589 : selected 10 ⟨621531, by decide⟩
    (prefixPartial 11 19318) = some ⟨11, 2, 0, 621531, 19318, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_19318_621531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19318 ⟨621531, by decide⟩ :=
  accepted_of_selected 11 19318 ⟨621531, by decide⟩ ⟨11, 2, 0, 621531, 19318, 2265, 262144⟩
    (by decide) selected_cut_24589

theorem selected_cut_24590 : selected 10 ⟨621556, by decide⟩
    (prefixPartial 11 19319) = some ⟨11, 2, 0, 621556, 19319, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_19319_621556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19319 ⟨621556, by decide⟩ :=
  accepted_of_selected 11 19319 ⟨621556, by decide⟩ ⟨11, 2, 0, 621556, 19319, 1949, 262144⟩
    (by decide) selected_cut_24590

theorem unmarked_context_10_4829_621557 : frontier 11 ⟨621557, by decide⟩
    (prefixCache 10 4829) (prefixPartial 10 4829) = false := by
  decide +kernel

theorem node_context_10_4829_621557 : EJMOriginalGlobalDAGData.nodes 11 ⟨621557, by decide⟩ =
    .split (coordinate 10) (![⟨621483, by decide⟩,⟨621507, by decide⟩,⟨621531, by decide⟩,⟨621556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4829_621557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4829 ⟨621557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4829
    ⟨621557, by decide⟩ (by decide) (![⟨621483, by decide⟩,⟨621507, by decide⟩,⟨621531, by decide⟩,⟨621556, by decide⟩]) unmarked_context_10_4829_621557 node_context_10_4829_621557
  intro a
  fin_cases a
  · exact context_11_19316_621483
  · exact context_11_19317_621507
  · exact context_11_19318_621531
  · exact context_11_19319_621556

theorem selected_cut_24591 : selected 10 ⟨621579, by decide⟩
    (prefixPartial 11 19320) = some ⟨11, 2, 0, 621579, 19320, 1593, 262144⟩ := by
  decide +kernel

theorem context_11_19320_621579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19320 ⟨621579, by decide⟩ :=
  accepted_of_selected 11 19320 ⟨621579, by decide⟩ ⟨11, 2, 0, 621579, 19320, 1593, 262144⟩
    (by decide) selected_cut_24591

theorem selected_cut_24592 : selected 10 ⟨621602, by decide⟩
    (prefixPartial 11 19321) = some ⟨11, 2, 0, 621602, 19321, 1409, 262144⟩ := by
  decide +kernel

theorem context_11_19321_621602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19321 ⟨621602, by decide⟩ :=
  accepted_of_selected 11 19321 ⟨621602, by decide⟩ ⟨11, 2, 0, 621602, 19321, 1409, 262144⟩
    (by decide) selected_cut_24592

theorem selected_cut_24593 : selected 10 ⟨621618, by decide⟩
    (prefixPartial 11 19322) = some ⟨11, 2, 0, 621618, 19322, 1073, 262144⟩ := by
  decide +kernel

theorem context_11_19322_621618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19322 ⟨621618, by decide⟩ :=
  accepted_of_selected 11 19322 ⟨621618, by decide⟩ ⟨11, 2, 0, 621618, 19322, 1073, 262144⟩
    (by decide) selected_cut_24593

theorem selected_cut_24594 : selected 10 ⟨621631, by decide⟩
    (prefixPartial 11 19323) = some ⟨11, 2, 0, 621631, 19323, 841, 262144⟩ := by
  decide +kernel

theorem context_11_19323_621631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19323 ⟨621631, by decide⟩ :=
  accepted_of_selected 11 19323 ⟨621631, by decide⟩ ⟨11, 2, 0, 621631, 19323, 841, 262144⟩
    (by decide) selected_cut_24594

theorem unmarked_context_10_4830_621632 : frontier 11 ⟨621632, by decide⟩
    (prefixCache 10 4830) (prefixPartial 10 4830) = false := by
  decide +kernel

theorem node_context_10_4830_621632 : EJMOriginalGlobalDAGData.nodes 11 ⟨621632, by decide⟩ =
    .split (coordinate 10) (![⟨621579, by decide⟩,⟨621602, by decide⟩,⟨621618, by decide⟩,⟨621631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4830_621632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4830 ⟨621632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4830
    ⟨621632, by decide⟩ (by decide) (![⟨621579, by decide⟩,⟨621602, by decide⟩,⟨621618, by decide⟩,⟨621631, by decide⟩]) unmarked_context_10_4830_621632 node_context_10_4830_621632
  intro a
  fin_cases a
  · exact context_11_19320_621579
  · exact context_11_19321_621602
  · exact context_11_19322_621618
  · exact context_11_19323_621631

theorem selected_cut_24595 : selected 11 ⟨621663, by decide⟩
    (prefixPartial 10 4831) = some ⟨10, 2, 0, 621663, 4831, 1125, 1048576⟩ := by
  decide +kernel

theorem context_10_4831_621663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4831 ⟨621663, by decide⟩ :=
  accepted_of_selected 10 4831 ⟨621663, by decide⟩ ⟨10, 2, 0, 621663, 4831, 1125, 1048576⟩
    (by decide) selected_cut_24595

theorem unmarked_context_9_1207_621664 : frontier 12 ⟨621664, by decide⟩
    (prefixCache 9 1207) (prefixPartial 9 1207) = false := by
  decide +kernel

theorem node_context_9_1207_621664 : EJMOriginalGlobalDAGData.nodes 12 ⟨621664, by decide⟩ =
    .split (coordinate 9) (![⟨621449, by decide⟩,⟨621557, by decide⟩,⟨621632, by decide⟩,⟨621663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1207_621664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1207 ⟨621664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1207
    ⟨621664, by decide⟩ (by decide) (![⟨621449, by decide⟩,⟨621557, by decide⟩,⟨621632, by decide⟩,⟨621663, by decide⟩]) unmarked_context_9_1207_621664 node_context_9_1207_621664
  intro a
  fin_cases a
  · exact context_10_4828_621449
  · exact context_10_4829_621557
  · exact context_10_4830_621632
  · exact context_10_4831_621663

theorem unmarked_context_8_301_621665 : frontier 13 ⟨621665, by decide⟩
    (prefixCache 8 301) (prefixPartial 8 301) = false := by
  decide +kernel

theorem node_context_8_301_621665 : EJMOriginalGlobalDAGData.nodes 13 ⟨621665, by decide⟩ =
    .split (coordinate 8) (![⟨616639, by decide⟩,⟨619684, by decide⟩,⟨621308, by decide⟩,⟨621664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_301_621665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 301 ⟨621665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 301
    ⟨621665, by decide⟩ (by decide) (![⟨616639, by decide⟩,⟨619684, by decide⟩,⟨621308, by decide⟩,⟨621664, by decide⟩]) unmarked_context_8_301_621665 node_context_8_301_621665
  intro a
  fin_cases a
  · exact context_9_1204_616639
  · exact context_9_1205_619684
  · exact context_9_1206_621308
  · exact context_9_1207_621664

theorem selected_cut_24596 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 19328) = some ⟨11, 1, 0, 434745, 19328, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19328_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19328 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 19328 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 19328, 1, 262144⟩
    (by decide) selected_cut_24596

theorem selected_cut_24597 : selected 10 ⟨621666, by decide⟩
    (prefixPartial 11 19329) = some ⟨11, 2, 0, 621666, 19329, 5, 262144⟩ := by
  decide +kernel

theorem context_11_19329_621666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19329 ⟨621666, by decide⟩ :=
  accepted_of_selected 11 19329 ⟨621666, by decide⟩ ⟨11, 2, 0, 621666, 19329, 5, 262144⟩
    (by decide) selected_cut_24597

theorem selected_cut_24598 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 77320) = some ⟨12, 1, 0, 448748, 77320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77320_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77320 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 77320 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 77320, 1, 65536⟩
    (by decide) selected_cut_24598

theorem selected_cut_24599 : selected 8 ⟨621762, by decide⟩
    (prefixPartial 13 309284) = some ⟨13, 2, 0, 621762, 309284, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_309284_621762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309284 ⟨621762, by decide⟩ :=
  accepted_of_selected 13 309284 ⟨621762, by decide⟩ ⟨13, 2, 0, 621762, 309284, 3077, 16384⟩
    (by decide) selected_cut_24599

theorem selected_cut_24600 : selected 8 ⟨621827, by decide⟩
    (prefixPartial 13 309285) = some ⟨13, 2, 0, 621827, 309285, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_309285_621827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309285 ⟨621827, by decide⟩ :=
  accepted_of_selected 13 309285 ⟨621827, by decide⟩ ⟨13, 2, 0, 621827, 309285, 3061, 16384⟩
    (by decide) selected_cut_24600

theorem selected_cut_24601 : selected 8 ⟨621873, by decide⟩
    (prefixPartial 13 309286) = some ⟨13, 2, 0, 621873, 309286, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_309286_621873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309286 ⟨621873, by decide⟩ :=
  accepted_of_selected 13 309286 ⟨621873, by decide⟩ ⟨13, 2, 0, 621873, 309286, 2125, 16384⟩
    (by decide) selected_cut_24601

theorem selected_cut_24602 : selected 8 ⟨621921, by decide⟩
    (prefixPartial 13 309287) = some ⟨13, 2, 0, 621921, 309287, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_309287_621921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309287 ⟨621921, by decide⟩ :=
  accepted_of_selected 13 309287 ⟨621921, by decide⟩ ⟨13, 2, 0, 621921, 309287, 1365, 16384⟩
    (by decide) selected_cut_24602

theorem unmarked_context_12_77321_621922 : frontier 9 ⟨621922, by decide⟩
    (prefixCache 12 77321) (prefixPartial 12 77321) = false := by
  decide +kernel

theorem node_context_12_77321_621922 : EJMOriginalGlobalDAGData.nodes 9 ⟨621922, by decide⟩ =
    .split (coordinate 12) (![⟨621762, by decide⟩,⟨621827, by decide⟩,⟨621873, by decide⟩,⟨621921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77321_621922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77321 ⟨621922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77321
    ⟨621922, by decide⟩ (by decide) (![⟨621762, by decide⟩,⟨621827, by decide⟩,⟨621873, by decide⟩,⟨621921, by decide⟩]) unmarked_context_12_77321_621922 node_context_12_77321_621922
  intro a
  fin_cases a
  · exact context_13_309284_621762
  · exact context_13_309285_621827
  · exact context_13_309286_621873
  · exact context_13_309287_621921

theorem selected_cut_24603 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 77322) = some ⟨12, 1, 0, 524302, 77322, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77322_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77322 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 77322 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 77322, 1, 65536⟩
    (by decide) selected_cut_24603

theorem selected_cut_24604 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 77323) = some ⟨12, 1, 0, 604131, 77323, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77323_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77323 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 77323 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 77323, 1, 65536⟩
    (by decide) selected_cut_24604

theorem unmarked_context_11_19330_621923 : frontier 10 ⟨621923, by decide⟩
    (prefixCache 11 19330) (prefixPartial 11 19330) = false := by
  decide +kernel

theorem node_context_11_19330_621923 : EJMOriginalGlobalDAGData.nodes 10 ⟨621923, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨621922, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19330_621923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19330 ⟨621923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19330
    ⟨621923, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨621922, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_19330_621923 node_context_11_19330_621923
  intro a
  fin_cases a
  · exact context_12_77320_448748
  · exact context_12_77321_621922
  · exact context_12_77322_524302
  · exact context_12_77323_604131

theorem selected_cut_24605 : selected 10 ⟨604133, by decide⟩
    (prefixPartial 11 19331) = some ⟨11, 2, 0, 604133, 19331, 5, 262144⟩ := by
  decide +kernel

theorem context_11_19331_604133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19331 ⟨604133, by decide⟩ :=
  accepted_of_selected 11 19331 ⟨604133, by decide⟩ ⟨11, 2, 0, 604133, 19331, 5, 262144⟩
    (by decide) selected_cut_24605

theorem unmarked_context_10_4832_621924 : frontier 11 ⟨621924, by decide⟩
    (prefixCache 10 4832) (prefixPartial 10 4832) = false := by
  decide +kernel

theorem node_context_10_4832_621924 : EJMOriginalGlobalDAGData.nodes 11 ⟨621924, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨621666, by decide⟩,⟨621923, by decide⟩,⟨604133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4832_621924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4832 ⟨621924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4832
    ⟨621924, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨621666, by decide⟩,⟨621923, by decide⟩,⟨604133, by decide⟩]) unmarked_context_10_4832_621924 node_context_10_4832_621924
  intro a
  fin_cases a
  · exact context_11_19328_434745
  · exact context_11_19329_621666
  · exact context_11_19330_621923
  · exact context_11_19331_604133

theorem selected_cut_24606 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 77328) = some ⟨12, 1, 0, 435160, 77328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77328_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77328 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 77328 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 77328, 1, 65536⟩
    (by decide) selected_cut_24606

theorem selected_cut_24607 : selected 8 ⟨621975, by decide⟩
    (prefixPartial 13 309316) = some ⟨13, 2, 0, 621975, 309316, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_309316_621975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309316 ⟨621975, by decide⟩ :=
  accepted_of_selected 13 309316 ⟨621975, by decide⟩ ⟨13, 2, 0, 621975, 309316, 2193, 16384⟩
    (by decide) selected_cut_24607

theorem selected_cut_24608 : selected 8 ⟨622013, by decide⟩
    (prefixPartial 13 309317) = some ⟨13, 2, 0, 622013, 309317, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_309317_622013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309317 ⟨622013, by decide⟩ :=
  accepted_of_selected 13 309317 ⟨622013, by decide⟩ ⟨13, 2, 0, 622013, 309317, 2097, 16384⟩
    (by decide) selected_cut_24608

theorem selected_cut_24609 : selected 8 ⟨622040, by decide⟩
    (prefixPartial 13 309318) = some ⟨13, 2, 0, 622040, 309318, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_309318_622040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309318 ⟨622040, by decide⟩ :=
  accepted_of_selected 13 309318 ⟨622040, by decide⟩ ⟨13, 2, 0, 622040, 309318, 1665, 16384⟩
    (by decide) selected_cut_24609

theorem selected_cut_24610 : selected 8 ⟨622055, by decide⟩
    (prefixPartial 13 309319) = some ⟨13, 2, 0, 622055, 309319, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_309319_622055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309319 ⟨622055, by decide⟩ :=
  accepted_of_selected 13 309319 ⟨622055, by decide⟩ ⟨13, 2, 0, 622055, 309319, 1013, 16384⟩
    (by decide) selected_cut_24610

theorem unmarked_context_12_77329_622056 : frontier 9 ⟨622056, by decide⟩
    (prefixCache 12 77329) (prefixPartial 12 77329) = false := by
  decide +kernel

theorem node_context_12_77329_622056 : EJMOriginalGlobalDAGData.nodes 9 ⟨622056, by decide⟩ =
    .split (coordinate 12) (![⟨621975, by decide⟩,⟨622013, by decide⟩,⟨622040, by decide⟩,⟨622055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77329_622056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77329 ⟨622056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77329
    ⟨622056, by decide⟩ (by decide) (![⟨621975, by decide⟩,⟨622013, by decide⟩,⟨622040, by decide⟩,⟨622055, by decide⟩]) unmarked_context_12_77329_622056 node_context_12_77329_622056
  intro a
  fin_cases a
  · exact context_13_309316_621975
  · exact context_13_309317_622013
  · exact context_13_309318_622040
  · exact context_13_309319_622055

theorem selected_cut_24611 : selected 8 ⟨622091, by decide⟩
    (prefixPartial 13 309320) = some ⟨13, 2, 0, 622091, 309320, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_309320_622091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309320 ⟨622091, by decide⟩ :=
  accepted_of_selected 13 309320 ⟨622091, by decide⟩ ⟨13, 2, 0, 622091, 309320, 1549, 16384⟩
    (by decide) selected_cut_24611

theorem selected_cut_24612 : selected 8 ⟨622120, by decide⟩
    (prefixPartial 13 309321) = some ⟨13, 2, 0, 622120, 309321, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_309321_622120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309321 ⟨622120, by decide⟩ :=
  accepted_of_selected 13 309321 ⟨622120, by decide⟩ ⟨13, 2, 0, 622120, 309321, 1769, 16384⟩
    (by decide) selected_cut_24612

theorem selected_cut_24613 : selected 8 ⟨622143, by decide⟩
    (prefixPartial 13 309322) = some ⟨13, 2, 0, 622143, 309322, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_309322_622143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309322 ⟨622143, by decide⟩ :=
  accepted_of_selected 13 309322 ⟨622143, by decide⟩ ⟨13, 2, 0, 622143, 309322, 1217, 16384⟩
    (by decide) selected_cut_24613

theorem selected_cut_24614 : selected 8 ⟨622154, by decide⟩
    (prefixPartial 13 309323) = some ⟨13, 2, 0, 622154, 309323, 925, 16384⟩ := by
  decide +kernel

theorem context_13_309323_622154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309323 ⟨622154, by decide⟩ :=
  accepted_of_selected 13 309323 ⟨622154, by decide⟩ ⟨13, 2, 0, 622154, 309323, 925, 16384⟩
    (by decide) selected_cut_24614

theorem unmarked_context_12_77330_622155 : frontier 9 ⟨622155, by decide⟩
    (prefixCache 12 77330) (prefixPartial 12 77330) = false := by
  decide +kernel

theorem node_context_12_77330_622155 : EJMOriginalGlobalDAGData.nodes 9 ⟨622155, by decide⟩ =
    .split (coordinate 12) (![⟨622091, by decide⟩,⟨622120, by decide⟩,⟨622143, by decide⟩,⟨622154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77330_622155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77330 ⟨622155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77330
    ⟨622155, by decide⟩ (by decide) (![⟨622091, by decide⟩,⟨622120, by decide⟩,⟨622143, by decide⟩,⟨622154, by decide⟩]) unmarked_context_12_77330_622155 node_context_12_77330_622155
  intro a
  fin_cases a
  · exact context_13_309320_622091
  · exact context_13_309321_622120
  · exact context_13_309322_622143
  · exact context_13_309323_622154

theorem selected_cut_24615 : selected 8 ⟨622191, by decide⟩
    (prefixPartial 13 309324) = some ⟨13, 2, 0, 622191, 309324, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_309324_622191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309324 ⟨622191, by decide⟩ :=
  accepted_of_selected 13 309324 ⟨622191, by decide⟩ ⟨13, 2, 0, 622191, 309324, 1853, 16384⟩
    (by decide) selected_cut_24615

theorem selected_cut_24616 : selected 8 ⟨622225, by decide⟩
    (prefixPartial 13 309325) = some ⟨13, 2, 0, 622225, 309325, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_309325_622225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309325 ⟨622225, by decide⟩ :=
  accepted_of_selected 13 309325 ⟨622225, by decide⟩ ⟨13, 2, 0, 622225, 309325, 2449, 16384⟩
    (by decide) selected_cut_24616

theorem selected_cut_24617 : selected 8 ⟨622257, by decide⟩
    (prefixPartial 13 309326) = some ⟨13, 2, 0, 622257, 309326, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_309326_622257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309326 ⟨622257, by decide⟩ :=
  accepted_of_selected 13 309326 ⟨622257, by decide⟩ ⟨13, 2, 0, 622257, 309326, 1665, 16384⟩
    (by decide) selected_cut_24617

theorem selected_cut_24618 : selected 8 ⟨622276, by decide⟩
    (prefixPartial 13 309327) = some ⟨13, 2, 0, 622276, 309327, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_309327_622276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309327 ⟨622276, by decide⟩ :=
  accepted_of_selected 13 309327 ⟨622276, by decide⟩ ⟨13, 2, 0, 622276, 309327, 1037, 16384⟩
    (by decide) selected_cut_24618

theorem unmarked_context_12_77331_622277 : frontier 9 ⟨622277, by decide⟩
    (prefixCache 12 77331) (prefixPartial 12 77331) = false := by
  decide +kernel

theorem node_context_12_77331_622277 : EJMOriginalGlobalDAGData.nodes 9 ⟨622277, by decide⟩ =
    .split (coordinate 12) (![⟨622191, by decide⟩,⟨622225, by decide⟩,⟨622257, by decide⟩,⟨622276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77331_622277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77331 ⟨622277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77331
    ⟨622277, by decide⟩ (by decide) (![⟨622191, by decide⟩,⟨622225, by decide⟩,⟨622257, by decide⟩,⟨622276, by decide⟩]) unmarked_context_12_77331_622277 node_context_12_77331_622277
  intro a
  fin_cases a
  · exact context_13_309324_622191
  · exact context_13_309325_622225
  · exact context_13_309326_622257
  · exact context_13_309327_622276

theorem unmarked_context_11_19332_622278 : frontier 10 ⟨622278, by decide⟩
    (prefixCache 11 19332) (prefixPartial 11 19332) = false := by
  decide +kernel

theorem node_context_11_19332_622278 : EJMOriginalGlobalDAGData.nodes 10 ⟨622278, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨622056, by decide⟩,⟨622155, by decide⟩,⟨622277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19332_622278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19332 ⟨622278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19332
    ⟨622278, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨622056, by decide⟩,⟨622155, by decide⟩,⟨622277, by decide⟩]) unmarked_context_11_19332_622278 node_context_11_19332_622278
  intro a
  fin_cases a
  · exact context_12_77328_435160
  · exact context_12_77329_622056
  · exact context_12_77330_622155
  · exact context_12_77331_622277

theorem selected_cut_24619 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 77332) = some ⟨12, 1, 0, 435160, 77332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77332_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77332 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 77332 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 77332, 1, 65536⟩
    (by decide) selected_cut_24619

theorem selected_cut_24620 : selected 8 ⟨622323, by decide⟩
    (prefixPartial 13 309332) = some ⟨13, 2, 0, 622323, 309332, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_309332_622323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309332 ⟨622323, by decide⟩ :=
  accepted_of_selected 13 309332 ⟨622323, by decide⟩ ⟨13, 2, 0, 622323, 309332, 1989, 16384⟩
    (by decide) selected_cut_24620

theorem selected_cut_24621 : selected 8 ⟨622359, by decide⟩
    (prefixPartial 13 309333) = some ⟨13, 2, 0, 622359, 309333, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_309333_622359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309333 ⟨622359, by decide⟩ :=
  accepted_of_selected 13 309333 ⟨622359, by decide⟩ ⟨13, 2, 0, 622359, 309333, 2069, 16384⟩
    (by decide) selected_cut_24621

theorem selected_cut_24622 : selected 8 ⟨622382, by decide⟩
    (prefixPartial 13 309334) = some ⟨13, 2, 0, 622382, 309334, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_309334_622382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309334 ⟨622382, by decide⟩ :=
  accepted_of_selected 13 309334 ⟨622382, by decide⟩ ⟨13, 2, 0, 622382, 309334, 1613, 16384⟩
    (by decide) selected_cut_24622

theorem selected_cut_24623 : selected 8 ⟨622399, by decide⟩
    (prefixPartial 13 309335) = some ⟨13, 2, 0, 622399, 309335, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_309335_622399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309335 ⟨622399, by decide⟩ :=
  accepted_of_selected 13 309335 ⟨622399, by decide⟩ ⟨13, 2, 0, 622399, 309335, 1029, 16384⟩
    (by decide) selected_cut_24623

theorem unmarked_context_12_77333_622400 : frontier 9 ⟨622400, by decide⟩
    (prefixCache 12 77333) (prefixPartial 12 77333) = false := by
  decide +kernel

theorem node_context_12_77333_622400 : EJMOriginalGlobalDAGData.nodes 9 ⟨622400, by decide⟩ =
    .split (coordinate 12) (![⟨622323, by decide⟩,⟨622359, by decide⟩,⟨622382, by decide⟩,⟨622399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77333_622400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77333 ⟨622400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77333
    ⟨622400, by decide⟩ (by decide) (![⟨622323, by decide⟩,⟨622359, by decide⟩,⟨622382, by decide⟩,⟨622399, by decide⟩]) unmarked_context_12_77333_622400 node_context_12_77333_622400
  intro a
  fin_cases a
  · exact context_13_309332_622323
  · exact context_13_309333_622359
  · exact context_13_309334_622382
  · exact context_13_309335_622399

theorem selected_cut_24624 : selected 8 ⟨622439, by decide⟩
    (prefixPartial 13 309336) = some ⟨13, 2, 0, 622439, 309336, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_309336_622439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309336 ⟨622439, by decide⟩ :=
  accepted_of_selected 13 309336 ⟨622439, by decide⟩ ⟨13, 2, 0, 622439, 309336, 1493, 16384⟩
    (by decide) selected_cut_24624

theorem selected_cut_24625 : selected 8 ⟨622478, by decide⟩
    (prefixPartial 13 309337) = some ⟨13, 2, 0, 622478, 309337, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_309337_622478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309337 ⟨622478, by decide⟩ :=
  accepted_of_selected 13 309337 ⟨622478, by decide⟩ ⟨13, 2, 0, 622478, 309337, 2025, 16384⟩
    (by decide) selected_cut_24625

theorem selected_cut_24626 : selected 8 ⟨622498, by decide⟩
    (prefixPartial 13 309338) = some ⟨13, 2, 0, 622498, 309338, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_309338_622498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309338 ⟨622498, by decide⟩ :=
  accepted_of_selected 13 309338 ⟨622498, by decide⟩ ⟨13, 2, 0, 622498, 309338, 1305, 16384⟩
    (by decide) selected_cut_24626

theorem selected_cut_24627 : selected 8 ⟨622508, by decide⟩
    (prefixPartial 13 309339) = some ⟨13, 2, 0, 622508, 309339, 933, 16384⟩ := by
  decide +kernel

theorem context_13_309339_622508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309339 ⟨622508, by decide⟩ :=
  accepted_of_selected 13 309339 ⟨622508, by decide⟩ ⟨13, 2, 0, 622508, 309339, 933, 16384⟩
    (by decide) selected_cut_24627

theorem unmarked_context_12_77334_622509 : frontier 9 ⟨622509, by decide⟩
    (prefixCache 12 77334) (prefixPartial 12 77334) = false := by
  decide +kernel

theorem node_context_12_77334_622509 : EJMOriginalGlobalDAGData.nodes 9 ⟨622509, by decide⟩ =
    .split (coordinate 12) (![⟨622439, by decide⟩,⟨622478, by decide⟩,⟨622498, by decide⟩,⟨622508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77334_622509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77334 ⟨622509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77334
    ⟨622509, by decide⟩ (by decide) (![⟨622439, by decide⟩,⟨622478, by decide⟩,⟨622498, by decide⟩,⟨622508, by decide⟩]) unmarked_context_12_77334_622509 node_context_12_77334_622509
  intro a
  fin_cases a
  · exact context_13_309336_622439
  · exact context_13_309337_622478
  · exact context_13_309338_622498
  · exact context_13_309339_622508

theorem selected_cut_24628 : selected 8 ⟨622550, by decide⟩
    (prefixPartial 13 309340) = some ⟨13, 2, 0, 622550, 309340, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_309340_622550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309340 ⟨622550, by decide⟩ :=
  accepted_of_selected 13 309340 ⟨622550, by decide⟩ ⟨13, 2, 0, 622550, 309340, 1849, 16384⟩
    (by decide) selected_cut_24628

theorem selected_cut_24629 : selected 8 ⟨622586, by decide⟩
    (prefixPartial 13 309341) = some ⟨13, 2, 0, 622586, 309341, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_309341_622586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309341 ⟨622586, by decide⟩ :=
  accepted_of_selected 13 309341 ⟨622586, by decide⟩ ⟨13, 2, 0, 622586, 309341, 2473, 16384⟩
    (by decide) selected_cut_24629

theorem selected_cut_24630 : selected 8 ⟨622616, by decide⟩
    (prefixPartial 13 309342) = some ⟨13, 2, 0, 622616, 309342, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_309342_622616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309342 ⟨622616, by decide⟩ :=
  accepted_of_selected 13 309342 ⟨622616, by decide⟩ ⟨13, 2, 0, 622616, 309342, 1825, 16384⟩
    (by decide) selected_cut_24630

theorem selected_cut_24631 : selected 8 ⟨622632, by decide⟩
    (prefixPartial 13 309343) = some ⟨13, 2, 0, 622632, 309343, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_309343_622632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309343 ⟨622632, by decide⟩ :=
  accepted_of_selected 13 309343 ⟨622632, by decide⟩ ⟨13, 2, 0, 622632, 309343, 1073, 16384⟩
    (by decide) selected_cut_24631

theorem unmarked_context_12_77335_622633 : frontier 9 ⟨622633, by decide⟩
    (prefixCache 12 77335) (prefixPartial 12 77335) = false := by
  decide +kernel

theorem node_context_12_77335_622633 : EJMOriginalGlobalDAGData.nodes 9 ⟨622633, by decide⟩ =
    .split (coordinate 12) (![⟨622550, by decide⟩,⟨622586, by decide⟩,⟨622616, by decide⟩,⟨622632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77335_622633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77335 ⟨622633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77335
    ⟨622633, by decide⟩ (by decide) (![⟨622550, by decide⟩,⟨622586, by decide⟩,⟨622616, by decide⟩,⟨622632, by decide⟩]) unmarked_context_12_77335_622633 node_context_12_77335_622633
  intro a
  fin_cases a
  · exact context_13_309340_622550
  · exact context_13_309341_622586
  · exact context_13_309342_622616
  · exact context_13_309343_622632

theorem unmarked_context_11_19333_622634 : frontier 10 ⟨622634, by decide⟩
    (prefixCache 11 19333) (prefixPartial 11 19333) = false := by
  decide +kernel

theorem node_context_11_19333_622634 : EJMOriginalGlobalDAGData.nodes 10 ⟨622634, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨622400, by decide⟩,⟨622509, by decide⟩,⟨622633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19333_622634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19333 ⟨622634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19333
    ⟨622634, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨622400, by decide⟩,⟨622509, by decide⟩,⟨622633, by decide⟩]) unmarked_context_11_19333_622634 node_context_11_19333_622634
  intro a
  fin_cases a
  · exact context_12_77332_435160
  · exact context_12_77333_622400
  · exact context_12_77334_622509
  · exact context_12_77335_622633

theorem selected_cut_24632 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 77336) = some ⟨12, 1, 0, 449505, 77336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77336_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77336 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 77336 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 77336, 1, 65536⟩
    (by decide) selected_cut_24632

theorem selected_cut_24633 : selected 8 ⟨622675, by decide⟩
    (prefixPartial 13 309348) = some ⟨13, 2, 0, 622675, 309348, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_309348_622675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309348 ⟨622675, by decide⟩ :=
  accepted_of_selected 13 309348 ⟨622675, by decide⟩ ⟨13, 2, 0, 622675, 309348, 1857, 16384⟩
    (by decide) selected_cut_24633

theorem selected_cut_24634 : selected 8 ⟨622711, by decide⟩
    (prefixPartial 13 309349) = some ⟨13, 2, 0, 622711, 309349, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_309349_622711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309349 ⟨622711, by decide⟩ :=
  accepted_of_selected 13 309349 ⟨622711, by decide⟩ ⟨13, 2, 0, 622711, 309349, 2001, 16384⟩
    (by decide) selected_cut_24634

theorem selected_cut_24635 : selected 8 ⟨622740, by decide⟩
    (prefixPartial 13 309350) = some ⟨13, 2, 0, 622740, 309350, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_309350_622740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309350 ⟨622740, by decide⟩ :=
  accepted_of_selected 13 309350 ⟨622740, by decide⟩ ⟨13, 2, 0, 622740, 309350, 1921, 16384⟩
    (by decide) selected_cut_24635

theorem selected_cut_24636 : selected 8 ⟨622762, by decide⟩
    (prefixPartial 13 309351) = some ⟨13, 2, 0, 622762, 309351, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_309351_622762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309351 ⟨622762, by decide⟩ :=
  accepted_of_selected 13 309351 ⟨622762, by decide⟩ ⟨13, 2, 0, 622762, 309351, 1161, 16384⟩
    (by decide) selected_cut_24636

theorem unmarked_context_12_77337_622763 : frontier 9 ⟨622763, by decide⟩
    (prefixCache 12 77337) (prefixPartial 12 77337) = false := by
  decide +kernel

theorem node_context_12_77337_622763 : EJMOriginalGlobalDAGData.nodes 9 ⟨622763, by decide⟩ =
    .split (coordinate 12) (![⟨622675, by decide⟩,⟨622711, by decide⟩,⟨622740, by decide⟩,⟨622762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77337_622763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77337 ⟨622763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77337
    ⟨622763, by decide⟩ (by decide) (![⟨622675, by decide⟩,⟨622711, by decide⟩,⟨622740, by decide⟩,⟨622762, by decide⟩]) unmarked_context_12_77337_622763 node_context_12_77337_622763
  intro a
  fin_cases a
  · exact context_13_309348_622675
  · exact context_13_309349_622711
  · exact context_13_309350_622740
  · exact context_13_309351_622762

theorem selected_cut_24637 : selected 8 ⟨622819, by decide⟩
    (prefixPartial 13 309352) = some ⟨13, 2, 0, 622819, 309352, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_309352_622819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309352 ⟨622819, by decide⟩ :=
  accepted_of_selected 13 309352 ⟨622819, by decide⟩ ⟨13, 2, 0, 622819, 309352, 2245, 16384⟩
    (by decide) selected_cut_24637

theorem selected_cut_24638 : selected 8 ⟨622879, by decide⟩
    (prefixPartial 13 309353) = some ⟨13, 2, 0, 622879, 309353, 3497, 16384⟩ := by
  decide +kernel

theorem context_13_309353_622879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309353 ⟨622879, by decide⟩ :=
  accepted_of_selected 13 309353 ⟨622879, by decide⟩ ⟨13, 2, 0, 622879, 309353, 3497, 16384⟩
    (by decide) selected_cut_24638

theorem selected_cut_24639 : selected 8 ⟨622937, by decide⟩
    (prefixPartial 13 309354) = some ⟨13, 2, 0, 622937, 309354, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_309354_622937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309354 ⟨622937, by decide⟩ :=
  accepted_of_selected 13 309354 ⟨622937, by decide⟩ ⟨13, 2, 0, 622937, 309354, 2401, 16384⟩
    (by decide) selected_cut_24639

theorem selected_cut_24640 : selected 8 ⟨622988, by decide⟩
    (prefixPartial 13 309355) = some ⟨13, 2, 0, 622988, 309355, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_309355_622988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309355 ⟨622988, by decide⟩ :=
  accepted_of_selected 13 309355 ⟨622988, by decide⟩ ⟨13, 2, 0, 622988, 309355, 1401, 16384⟩
    (by decide) selected_cut_24640

theorem unmarked_context_12_77338_622989 : frontier 9 ⟨622989, by decide⟩
    (prefixCache 12 77338) (prefixPartial 12 77338) = false := by
  decide +kernel

theorem node_context_12_77338_622989 : EJMOriginalGlobalDAGData.nodes 9 ⟨622989, by decide⟩ =
    .split (coordinate 12) (![⟨622819, by decide⟩,⟨622879, by decide⟩,⟨622937, by decide⟩,⟨622988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77338_622989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77338 ⟨622989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77338
    ⟨622989, by decide⟩ (by decide) (![⟨622819, by decide⟩,⟨622879, by decide⟩,⟨622937, by decide⟩,⟨622988, by decide⟩]) unmarked_context_12_77338_622989 node_context_12_77338_622989
  intro a
  fin_cases a
  · exact context_13_309352_622819
  · exact context_13_309353_622879
  · exact context_13_309354_622937
  · exact context_13_309355_622988

theorem selected_cut_24641 : selected 8 ⟨623015, by decide⟩
    (prefixPartial 13 309356) = some ⟨13, 2, 0, 623015, 309356, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_309356_623015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309356 ⟨623015, by decide⟩ :=
  accepted_of_selected 13 309356 ⟨623015, by decide⟩ ⟨13, 2, 0, 623015, 309356, 1457, 16384⟩
    (by decide) selected_cut_24641

theorem selected_cut_24642 : selected 8 ⟨623049, by decide⟩
    (prefixPartial 13 309357) = some ⟨13, 2, 0, 623049, 309357, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_309357_623049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309357 ⟨623049, by decide⟩ :=
  accepted_of_selected 13 309357 ⟨623049, by decide⟩ ⟨13, 2, 0, 623049, 309357, 2441, 16384⟩
    (by decide) selected_cut_24642

theorem selected_cut_24643 : selected 8 ⟨623072, by decide⟩
    (prefixPartial 13 309358) = some ⟨13, 2, 0, 623072, 309358, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_309358_623072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309358 ⟨623072, by decide⟩ :=
  accepted_of_selected 13 309358 ⟨623072, by decide⟩ ⟨13, 2, 0, 623072, 309358, 1785, 16384⟩
    (by decide) selected_cut_24643

theorem selected_cut_24644 : selected 8 ⟨623090, by decide⟩
    (prefixPartial 13 309359) = some ⟨13, 2, 0, 623090, 309359, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_309359_623090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309359 ⟨623090, by decide⟩ :=
  accepted_of_selected 13 309359 ⟨623090, by decide⟩ ⟨13, 2, 0, 623090, 309359, 1081, 16384⟩
    (by decide) selected_cut_24644

theorem unmarked_context_12_77339_623091 : frontier 9 ⟨623091, by decide⟩
    (prefixCache 12 77339) (prefixPartial 12 77339) = false := by
  decide +kernel

theorem node_context_12_77339_623091 : EJMOriginalGlobalDAGData.nodes 9 ⟨623091, by decide⟩ =
    .split (coordinate 12) (![⟨623015, by decide⟩,⟨623049, by decide⟩,⟨623072, by decide⟩,⟨623090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77339_623091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77339 ⟨623091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77339
    ⟨623091, by decide⟩ (by decide) (![⟨623015, by decide⟩,⟨623049, by decide⟩,⟨623072, by decide⟩,⟨623090, by decide⟩]) unmarked_context_12_77339_623091 node_context_12_77339_623091
  intro a
  fin_cases a
  · exact context_13_309356_623015
  · exact context_13_309357_623049
  · exact context_13_309358_623072
  · exact context_13_309359_623090

theorem unmarked_context_11_19334_623092 : frontier 10 ⟨623092, by decide⟩
    (prefixCache 11 19334) (prefixPartial 11 19334) = false := by
  decide +kernel

theorem node_context_11_19334_623092 : EJMOriginalGlobalDAGData.nodes 10 ⟨623092, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨622763, by decide⟩,⟨622989, by decide⟩,⟨623091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19334_623092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19334 ⟨623092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19334
    ⟨623092, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨622763, by decide⟩,⟨622989, by decide⟩,⟨623091, by decide⟩]) unmarked_context_11_19334_623092 node_context_11_19334_623092
  intro a
  fin_cases a
  · exact context_12_77336_449505
  · exact context_12_77337_622763
  · exact context_12_77338_622989
  · exact context_12_77339_623091

theorem selected_cut_24645 : selected 8 ⟨623122, by decide⟩
    (prefixPartial 13 309360) = some ⟨13, 2, 0, 623122, 309360, 697, 16384⟩ := by
  decide +kernel

theorem context_13_309360_623122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309360 ⟨623122, by decide⟩ :=
  accepted_of_selected 13 309360 ⟨623122, by decide⟩ ⟨13, 2, 0, 623122, 309360, 697, 16384⟩
    (by decide) selected_cut_24645

theorem selected_cut_24646 : selected 8 ⟨623184, by decide⟩
    (prefixPartial 13 309361) = some ⟨13, 2, 0, 623184, 309361, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_309361_623184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309361 ⟨623184, by decide⟩ :=
  accepted_of_selected 13 309361 ⟨623184, by decide⟩ ⟨13, 2, 0, 623184, 309361, 1897, 16384⟩
    (by decide) selected_cut_24646

theorem selected_cut_24647 : selected 8 ⟨623236, by decide⟩
    (prefixPartial 13 309362) = some ⟨13, 2, 0, 623236, 309362, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_309362_623236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309362 ⟨623236, by decide⟩ :=
  accepted_of_selected 13 309362 ⟨623236, by decide⟩ ⟨13, 2, 0, 623236, 309362, 1937, 16384⟩
    (by decide) selected_cut_24647

theorem selected_cut_24648 : selected 8 ⟨508985, by decide⟩
    (prefixPartial 13 309363) = some ⟨13, 1, 0, 508985, 309363, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309363_508985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309363 ⟨508985, by decide⟩ :=
  accepted_of_selected 13 309363 ⟨508985, by decide⟩ ⟨13, 1, 0, 508985, 309363, 1, 16384⟩
    (by decide) selected_cut_24648

theorem unmarked_context_12_77340_623237 : frontier 9 ⟨623237, by decide⟩
    (prefixCache 12 77340) (prefixPartial 12 77340) = false := by
  decide +kernel

theorem node_context_12_77340_623237 : EJMOriginalGlobalDAGData.nodes 9 ⟨623237, by decide⟩ =
    .split (coordinate 12) (![⟨623122, by decide⟩,⟨623184, by decide⟩,⟨623236, by decide⟩,⟨508985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77340_623237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77340 ⟨623237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77340
    ⟨623237, by decide⟩ (by decide) (![⟨623122, by decide⟩,⟨623184, by decide⟩,⟨623236, by decide⟩,⟨508985, by decide⟩]) unmarked_context_12_77340_623237 node_context_12_77340_623237
  intro a
  fin_cases a
  · exact context_13_309360_623122
  · exact context_13_309361_623184
  · exact context_13_309362_623236
  · exact context_13_309363_508985

theorem selected_cut_24649 : selected 8 ⟨623263, by decide⟩
    (prefixPartial 13 309364) = some ⟨13, 2, 0, 623263, 309364, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_309364_623263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309364 ⟨623263, by decide⟩ :=
  accepted_of_selected 13 309364 ⟨623263, by decide⟩ ⟨13, 2, 0, 623263, 309364, 1397, 16384⟩
    (by decide) selected_cut_24649

theorem selected_cut_24650 : selected 8 ⟨623298, by decide⟩
    (prefixPartial 13 309365) = some ⟨13, 2, 0, 623298, 309365, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_309365_623298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309365 ⟨623298, by decide⟩ :=
  accepted_of_selected 13 309365 ⟨623298, by decide⟩ ⟨13, 2, 0, 623298, 309365, 2321, 16384⟩
    (by decide) selected_cut_24650

theorem selected_cut_24651 : selected 8 ⟨623320, by decide⟩
    (prefixPartial 13 309366) = some ⟨13, 2, 0, 623320, 309366, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_309366_623320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309366 ⟨623320, by decide⟩ :=
  accepted_of_selected 13 309366 ⟨623320, by decide⟩ ⟨13, 2, 0, 623320, 309366, 1669, 16384⟩
    (by decide) selected_cut_24651

theorem selected_cut_24652 : selected 8 ⟨623330, by decide⟩
    (prefixPartial 13 309367) = some ⟨13, 2, 0, 623330, 309367, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_309367_623330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309367 ⟨623330, by decide⟩ :=
  accepted_of_selected 13 309367 ⟨623330, by decide⟩ ⟨13, 2, 0, 623330, 309367, 1017, 16384⟩
    (by decide) selected_cut_24652

theorem unmarked_context_12_77341_623331 : frontier 9 ⟨623331, by decide⟩
    (prefixCache 12 77341) (prefixPartial 12 77341) = false := by
  decide +kernel

theorem node_context_12_77341_623331 : EJMOriginalGlobalDAGData.nodes 9 ⟨623331, by decide⟩ =
    .split (coordinate 12) (![⟨623263, by decide⟩,⟨623298, by decide⟩,⟨623320, by decide⟩,⟨623330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77341_623331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77341 ⟨623331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77341
    ⟨623331, by decide⟩ (by decide) (![⟨623263, by decide⟩,⟨623298, by decide⟩,⟨623320, by decide⟩,⟨623330, by decide⟩]) unmarked_context_12_77341_623331 node_context_12_77341_623331
  intro a
  fin_cases a
  · exact context_13_309364_623263
  · exact context_13_309365_623298
  · exact context_13_309366_623320
  · exact context_13_309367_623330

theorem selected_cut_24653 : selected 8 ⟨623353, by decide⟩
    (prefixPartial 13 309368) = some ⟨13, 2, 0, 623353, 309368, 929, 16384⟩ := by
  decide +kernel

theorem context_13_309368_623353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309368 ⟨623353, by decide⟩ :=
  accepted_of_selected 13 309368 ⟨623353, by decide⟩ ⟨13, 2, 0, 623353, 309368, 929, 16384⟩
    (by decide) selected_cut_24653

theorem selected_cut_24654 : selected 8 ⟨623389, by decide⟩
    (prefixPartial 13 309369) = some ⟨13, 2, 0, 623389, 309369, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_309369_623389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309369 ⟨623389, by decide⟩ :=
  accepted_of_selected 13 309369 ⟨623389, by decide⟩ ⟨13, 2, 0, 623389, 309369, 2097, 16384⟩
    (by decide) selected_cut_24654

theorem selected_cut_24655 : selected 8 ⟨623409, by decide⟩
    (prefixPartial 13 309370) = some ⟨13, 2, 0, 623409, 309370, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_309370_623409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309370 ⟨623409, by decide⟩ :=
  accepted_of_selected 13 309370 ⟨623409, by decide⟩ ⟨13, 2, 0, 623409, 309370, 1229, 16384⟩
    (by decide) selected_cut_24655

theorem selected_cut_24656 : selected 8 ⟨623417, by decide⟩
    (prefixPartial 13 309371) = some ⟨13, 2, 0, 623417, 309371, 929, 16384⟩ := by
  decide +kernel

theorem context_13_309371_623417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309371 ⟨623417, by decide⟩ :=
  accepted_of_selected 13 309371 ⟨623417, by decide⟩ ⟨13, 2, 0, 623417, 309371, 929, 16384⟩
    (by decide) selected_cut_24656

theorem unmarked_context_12_77342_623418 : frontier 9 ⟨623418, by decide⟩
    (prefixCache 12 77342) (prefixPartial 12 77342) = false := by
  decide +kernel

theorem node_context_12_77342_623418 : EJMOriginalGlobalDAGData.nodes 9 ⟨623418, by decide⟩ =
    .split (coordinate 12) (![⟨623353, by decide⟩,⟨623389, by decide⟩,⟨623409, by decide⟩,⟨623417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77342_623418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77342 ⟨623418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77342
    ⟨623418, by decide⟩ (by decide) (![⟨623353, by decide⟩,⟨623389, by decide⟩,⟨623409, by decide⟩,⟨623417, by decide⟩]) unmarked_context_12_77342_623418 node_context_12_77342_623418
  intro a
  fin_cases a
  · exact context_13_309368_623353
  · exact context_13_309369_623389
  · exact context_13_309370_623409
  · exact context_13_309371_623417

theorem selected_cut_24657 : selected 8 ⟨623438, by decide⟩
    (prefixPartial 13 309372) = some ⟨13, 2, 0, 623438, 309372, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_309372_623438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309372 ⟨623438, by decide⟩ :=
  accepted_of_selected 13 309372 ⟨623438, by decide⟩ ⟨13, 2, 0, 623438, 309372, 1125, 16384⟩
    (by decide) selected_cut_24657

theorem selected_cut_24658 : selected 8 ⟨623472, by decide⟩
    (prefixPartial 13 309373) = some ⟨13, 2, 0, 623472, 309373, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_309373_623472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309373 ⟨623472, by decide⟩ :=
  accepted_of_selected 13 309373 ⟨623472, by decide⟩ ⟨13, 2, 0, 623472, 309373, 2525, 16384⟩
    (by decide) selected_cut_24658

theorem selected_cut_24659 : selected 8 ⟨623493, by decide⟩
    (prefixPartial 13 309374) = some ⟨13, 2, 0, 623493, 309374, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_309374_623493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309374 ⟨623493, by decide⟩ :=
  accepted_of_selected 13 309374 ⟨623493, by decide⟩ ⟨13, 2, 0, 623493, 309374, 1641, 16384⟩
    (by decide) selected_cut_24659

theorem selected_cut_24660 : selected 8 ⟨623503, by decide⟩
    (prefixPartial 13 309375) = some ⟨13, 2, 0, 623503, 309375, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_309375_623503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309375 ⟨623503, by decide⟩ :=
  accepted_of_selected 13 309375 ⟨623503, by decide⟩ ⟨13, 2, 0, 623503, 309375, 1037, 16384⟩
    (by decide) selected_cut_24660

theorem unmarked_context_12_77343_623504 : frontier 9 ⟨623504, by decide⟩
    (prefixCache 12 77343) (prefixPartial 12 77343) = false := by
  decide +kernel

theorem node_context_12_77343_623504 : EJMOriginalGlobalDAGData.nodes 9 ⟨623504, by decide⟩ =
    .split (coordinate 12) (![⟨623438, by decide⟩,⟨623472, by decide⟩,⟨623493, by decide⟩,⟨623503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77343_623504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77343 ⟨623504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77343
    ⟨623504, by decide⟩ (by decide) (![⟨623438, by decide⟩,⟨623472, by decide⟩,⟨623493, by decide⟩,⟨623503, by decide⟩]) unmarked_context_12_77343_623504 node_context_12_77343_623504
  intro a
  fin_cases a
  · exact context_13_309372_623438
  · exact context_13_309373_623472
  · exact context_13_309374_623493
  · exact context_13_309375_623503

theorem unmarked_context_11_19335_623505 : frontier 10 ⟨623505, by decide⟩
    (prefixCache 11 19335) (prefixPartial 11 19335) = false := by
  decide +kernel

theorem node_context_11_19335_623505 : EJMOriginalGlobalDAGData.nodes 10 ⟨623505, by decide⟩ =
    .split (coordinate 11) (![⟨623237, by decide⟩,⟨623331, by decide⟩,⟨623418, by decide⟩,⟨623504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19335_623505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19335 ⟨623505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19335
    ⟨623505, by decide⟩ (by decide) (![⟨623237, by decide⟩,⟨623331, by decide⟩,⟨623418, by decide⟩,⟨623504, by decide⟩]) unmarked_context_11_19335_623505 node_context_11_19335_623505
  intro a
  fin_cases a
  · exact context_12_77340_623237
  · exact context_12_77341_623331
  · exact context_12_77342_623418
  · exact context_12_77343_623504

theorem unmarked_context_10_4833_623506 : frontier 11 ⟨623506, by decide⟩
    (prefixCache 10 4833) (prefixPartial 10 4833) = false := by
  decide +kernel

theorem node_context_10_4833_623506 : EJMOriginalGlobalDAGData.nodes 11 ⟨623506, by decide⟩ =
    .split (coordinate 10) (![⟨622278, by decide⟩,⟨622634, by decide⟩,⟨623092, by decide⟩,⟨623505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4833_623506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4833 ⟨623506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4833
    ⟨623506, by decide⟩ (by decide) (![⟨622278, by decide⟩,⟨622634, by decide⟩,⟨623092, by decide⟩,⟨623505, by decide⟩]) unmarked_context_10_4833_623506 node_context_10_4833_623506
  intro a
  fin_cases a
  · exact context_11_19332_622278
  · exact context_11_19333_622634
  · exact context_11_19334_623092
  · exact context_11_19335_623505

theorem selected_cut_24661 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 77344) = some ⟨12, 1, 0, 435790, 77344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77344_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77344 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 77344 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 77344, 1, 65536⟩
    (by decide) selected_cut_24661

theorem selected_cut_24662 : selected 8 ⟨623529, by decide⟩
    (prefixPartial 13 309380) = some ⟨13, 2, 0, 623529, 309380, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_309380_623529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309380 ⟨623529, by decide⟩ :=
  accepted_of_selected 13 309380 ⟨623529, by decide⟩ ⟨13, 2, 0, 623529, 309380, 1041, 16384⟩
    (by decide) selected_cut_24662

theorem selected_cut_24663 : selected 8 ⟨623560, by decide⟩
    (prefixPartial 13 309381) = some ⟨13, 2, 0, 623560, 309381, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_309381_623560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309381 ⟨623560, by decide⟩ :=
  accepted_of_selected 13 309381 ⟨623560, by decide⟩ ⟨13, 2, 0, 623560, 309381, 2137, 16384⟩
    (by decide) selected_cut_24663

theorem selected_cut_24664 : selected 8 ⟨623582, by decide⟩
    (prefixPartial 13 309382) = some ⟨13, 2, 0, 623582, 309382, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_309382_623582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309382 ⟨623582, by decide⟩ :=
  accepted_of_selected 13 309382 ⟨623582, by decide⟩ ⟨13, 2, 0, 623582, 309382, 1685, 16384⟩
    (by decide) selected_cut_24664

theorem selected_cut_24665 : selected 8 ⟨623590, by decide⟩
    (prefixPartial 13 309383) = some ⟨13, 2, 0, 623590, 309383, 781, 16384⟩ := by
  decide +kernel

theorem context_13_309383_623590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309383 ⟨623590, by decide⟩ :=
  accepted_of_selected 13 309383 ⟨623590, by decide⟩ ⟨13, 2, 0, 623590, 309383, 781, 16384⟩
    (by decide) selected_cut_24665

theorem unmarked_context_12_77345_623591 : frontier 9 ⟨623591, by decide⟩
    (prefixCache 12 77345) (prefixPartial 12 77345) = false := by
  decide +kernel

theorem node_context_12_77345_623591 : EJMOriginalGlobalDAGData.nodes 9 ⟨623591, by decide⟩ =
    .split (coordinate 12) (![⟨623529, by decide⟩,⟨623560, by decide⟩,⟨623582, by decide⟩,⟨623590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77345_623591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77345 ⟨623591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77345
    ⟨623591, by decide⟩ (by decide) (![⟨623529, by decide⟩,⟨623560, by decide⟩,⟨623582, by decide⟩,⟨623590, by decide⟩]) unmarked_context_12_77345_623591 node_context_12_77345_623591
  intro a
  fin_cases a
  · exact context_13_309380_623529
  · exact context_13_309381_623560
  · exact context_13_309382_623582
  · exact context_13_309383_623590

theorem selected_cut_24666 : selected 8 ⟨623606, by decide⟩
    (prefixPartial 13 309384) = some ⟨13, 2, 0, 623606, 309384, 757, 16384⟩ := by
  decide +kernel

theorem context_13_309384_623606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309384 ⟨623606, by decide⟩ :=
  accepted_of_selected 13 309384 ⟨623606, by decide⟩ ⟨13, 2, 0, 623606, 309384, 757, 16384⟩
    (by decide) selected_cut_24666

theorem selected_cut_24667 : selected 8 ⟨623629, by decide⟩
    (prefixPartial 13 309385) = some ⟨13, 2, 0, 623629, 309385, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_309385_623629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309385 ⟨623629, by decide⟩ :=
  accepted_of_selected 13 309385 ⟨623629, by decide⟩ ⟨13, 2, 0, 623629, 309385, 1465, 16384⟩
    (by decide) selected_cut_24667

theorem selected_cut_24668 : selected 8 ⟨623651, by decide⟩
    (prefixPartial 13 309386) = some ⟨13, 2, 0, 623651, 309386, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_309386_623651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309386 ⟨623651, by decide⟩ :=
  accepted_of_selected 13 309386 ⟨623651, by decide⟩ ⟨13, 2, 0, 623651, 309386, 1205, 16384⟩
    (by decide) selected_cut_24668

theorem selected_cut_24669 : selected 8 ⟨623661, by decide⟩
    (prefixPartial 13 309387) = some ⟨13, 2, 0, 623661, 309387, 733, 16384⟩ := by
  decide +kernel

theorem context_13_309387_623661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309387 ⟨623661, by decide⟩ :=
  accepted_of_selected 13 309387 ⟨623661, by decide⟩ ⟨13, 2, 0, 623661, 309387, 733, 16384⟩
    (by decide) selected_cut_24669

theorem unmarked_context_12_77346_623662 : frontier 9 ⟨623662, by decide⟩
    (prefixCache 12 77346) (prefixPartial 12 77346) = false := by
  decide +kernel

theorem node_context_12_77346_623662 : EJMOriginalGlobalDAGData.nodes 9 ⟨623662, by decide⟩ =
    .split (coordinate 12) (![⟨623606, by decide⟩,⟨623629, by decide⟩,⟨623651, by decide⟩,⟨623661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77346_623662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77346 ⟨623662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77346
    ⟨623662, by decide⟩ (by decide) (![⟨623606, by decide⟩,⟨623629, by decide⟩,⟨623651, by decide⟩,⟨623661, by decide⟩]) unmarked_context_12_77346_623662 node_context_12_77346_623662
  intro a
  fin_cases a
  · exact context_13_309384_623606
  · exact context_13_309385_623629
  · exact context_13_309386_623651
  · exact context_13_309387_623661

theorem selected_cut_24670 : selected 8 ⟨623683, by decide⟩
    (prefixPartial 13 309388) = some ⟨13, 2, 0, 623683, 309388, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_309388_623683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309388 ⟨623683, by decide⟩ :=
  accepted_of_selected 13 309388 ⟨623683, by decide⟩ ⟨13, 2, 0, 623683, 309388, 1021, 16384⟩
    (by decide) selected_cut_24670

theorem selected_cut_24671 : selected 8 ⟨623711, by decide⟩
    (prefixPartial 13 309389) = some ⟨13, 2, 0, 623711, 309389, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_309389_623711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309389 ⟨623711, by decide⟩ :=
  accepted_of_selected 13 309389 ⟨623711, by decide⟩ ⟨13, 2, 0, 623711, 309389, 2285, 16384⟩
    (by decide) selected_cut_24671

theorem selected_cut_24672 : selected 8 ⟨623738, by decide⟩
    (prefixPartial 13 309390) = some ⟨13, 2, 0, 623738, 309390, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_309390_623738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309390 ⟨623738, by decide⟩ :=
  accepted_of_selected 13 309390 ⟨623738, by decide⟩ ⟨13, 2, 0, 623738, 309390, 1713, 16384⟩
    (by decide) selected_cut_24672

theorem selected_cut_24673 : selected 8 ⟨623749, by decide⟩
    (prefixPartial 13 309391) = some ⟨13, 2, 0, 623749, 309391, 913, 16384⟩ := by
  decide +kernel

theorem context_13_309391_623749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309391 ⟨623749, by decide⟩ :=
  accepted_of_selected 13 309391 ⟨623749, by decide⟩ ⟨13, 2, 0, 623749, 309391, 913, 16384⟩
    (by decide) selected_cut_24673

theorem unmarked_context_12_77347_623750 : frontier 9 ⟨623750, by decide⟩
    (prefixCache 12 77347) (prefixPartial 12 77347) = false := by
  decide +kernel

theorem node_context_12_77347_623750 : EJMOriginalGlobalDAGData.nodes 9 ⟨623750, by decide⟩ =
    .split (coordinate 12) (![⟨623683, by decide⟩,⟨623711, by decide⟩,⟨623738, by decide⟩,⟨623749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77347_623750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77347 ⟨623750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77347
    ⟨623750, by decide⟩ (by decide) (![⟨623683, by decide⟩,⟨623711, by decide⟩,⟨623738, by decide⟩,⟨623749, by decide⟩]) unmarked_context_12_77347_623750 node_context_12_77347_623750
  intro a
  fin_cases a
  · exact context_13_309388_623683
  · exact context_13_309389_623711
  · exact context_13_309390_623738
  · exact context_13_309391_623749

theorem unmarked_context_11_19336_623751 : frontier 10 ⟨623751, by decide⟩
    (prefixCache 11 19336) (prefixPartial 11 19336) = false := by
  decide +kernel

theorem node_context_11_19336_623751 : EJMOriginalGlobalDAGData.nodes 10 ⟨623751, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨623591, by decide⟩,⟨623662, by decide⟩,⟨623750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19336_623751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19336 ⟨623751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19336
    ⟨623751, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨623591, by decide⟩,⟨623662, by decide⟩,⟨623750, by decide⟩]) unmarked_context_11_19336_623751 node_context_11_19336_623751
  intro a
  fin_cases a
  · exact context_12_77344_435790
  · exact context_12_77345_623591
  · exact context_12_77346_623662
  · exact context_12_77347_623750

theorem selected_cut_24674 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 77348) = some ⟨12, 1, 0, 450498, 77348, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77348_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77348 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 77348 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 77348, 1, 65536⟩
    (by decide) selected_cut_24674

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
