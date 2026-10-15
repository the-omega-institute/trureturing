/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover077
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07490 : selected 8 ⟨217269, by decide⟩
    (prefixPartial 13 90257) = some ⟨13, 2, 0, 217269, 90257, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_90257_217269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90257 ⟨217269, by decide⟩ :=
  accepted_of_selected 13 90257 ⟨217269, by decide⟩ ⟨13, 2, 0, 217269, 90257, 2669, 16384⟩
    (by decide) selected_cut_07490

theorem selected_cut_07491 : selected 8 ⟨217287, by decide⟩
    (prefixPartial 13 90258) = some ⟨13, 2, 0, 217287, 90258, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_90258_217287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90258 ⟨217287, by decide⟩ :=
  accepted_of_selected 13 90258 ⟨217287, by decide⟩ ⟨13, 2, 0, 217287, 90258, 1257, 16384⟩
    (by decide) selected_cut_07491

theorem selected_cut_07492 : selected 8 ⟨217297, by decide⟩
    (prefixPartial 13 90259) = some ⟨13, 2, 0, 217297, 90259, 909, 16384⟩ := by
  decide +kernel

theorem context_13_90259_217297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90259 ⟨217297, by decide⟩ :=
  accepted_of_selected 13 90259 ⟨217297, by decide⟩ ⟨13, 2, 0, 217297, 90259, 909, 16384⟩
    (by decide) selected_cut_07492

theorem unmarked_context_12_22564_217298 : frontier 9 ⟨217298, by decide⟩
    (prefixCache 12 22564) (prefixPartial 12 22564) = false := by
  decide +kernel

theorem node_context_12_22564_217298 : EJMOriginalGlobalDAGData.nodes 9 ⟨217298, by decide⟩ =
    .split (coordinate 12) (![⟨217224, by decide⟩,⟨217269, by decide⟩,⟨217287, by decide⟩,⟨217297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22564_217298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22564 ⟨217298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22564
    ⟨217298, by decide⟩ (by decide) (![⟨217224, by decide⟩,⟨217269, by decide⟩,⟨217287, by decide⟩,⟨217297, by decide⟩]) unmarked_context_12_22564_217298 node_context_12_22564_217298
  intro a
  fin_cases a
  · exact context_13_90256_217224
  · exact context_13_90257_217269
  · exact context_13_90258_217287
  · exact context_13_90259_217297

theorem selected_cut_07493 : selected 8 ⟨217309, by decide⟩
    (prefixPartial 13 90260) = some ⟨13, 2, 0, 217309, 90260, 793, 16384⟩ := by
  decide +kernel

theorem context_13_90260_217309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90260 ⟨217309, by decide⟩ :=
  accepted_of_selected 13 90260 ⟨217309, by decide⟩ ⟨13, 2, 0, 217309, 90260, 793, 16384⟩
    (by decide) selected_cut_07493

theorem selected_cut_07494 : selected 8 ⟨217335, by decide⟩
    (prefixPartial 13 90261) = some ⟨13, 2, 0, 217335, 90261, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_90261_217335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90261 ⟨217335, by decide⟩ :=
  accepted_of_selected 13 90261 ⟨217335, by decide⟩ ⟨13, 2, 0, 217335, 90261, 1901, 16384⟩
    (by decide) selected_cut_07494

theorem selected_cut_07495 : selected 8 ⟨217351, by decide⟩
    (prefixPartial 13 90262) = some ⟨13, 2, 0, 217351, 90262, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_90262_217351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90262 ⟨217351, by decide⟩ :=
  accepted_of_selected 13 90262 ⟨217351, by decide⟩ ⟨13, 2, 0, 217351, 90262, 1281, 16384⟩
    (by decide) selected_cut_07495

theorem selected_cut_07496 : selected 8 ⟨217360, by decide⟩
    (prefixPartial 13 90263) = some ⟨13, 2, 0, 217360, 90263, 949, 16384⟩ := by
  decide +kernel

theorem context_13_90263_217360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90263 ⟨217360, by decide⟩ :=
  accepted_of_selected 13 90263 ⟨217360, by decide⟩ ⟨13, 2, 0, 217360, 90263, 949, 16384⟩
    (by decide) selected_cut_07496

theorem unmarked_context_12_22565_217361 : frontier 9 ⟨217361, by decide⟩
    (prefixCache 12 22565) (prefixPartial 12 22565) = false := by
  decide +kernel

theorem node_context_12_22565_217361 : EJMOriginalGlobalDAGData.nodes 9 ⟨217361, by decide⟩ =
    .split (coordinate 12) (![⟨217309, by decide⟩,⟨217335, by decide⟩,⟨217351, by decide⟩,⟨217360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22565_217361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22565 ⟨217361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22565
    ⟨217361, by decide⟩ (by decide) (![⟨217309, by decide⟩,⟨217335, by decide⟩,⟨217351, by decide⟩,⟨217360, by decide⟩]) unmarked_context_12_22565_217361 node_context_12_22565_217361
  intro a
  fin_cases a
  · exact context_13_90260_217309
  · exact context_13_90261_217335
  · exact context_13_90262_217351
  · exact context_13_90263_217360

theorem selected_cut_07497 : selected 8 ⟨217376, by decide⟩
    (prefixPartial 13 90264) = some ⟨13, 2, 0, 217376, 90264, 989, 16384⟩ := by
  decide +kernel

theorem context_13_90264_217376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90264 ⟨217376, by decide⟩ :=
  accepted_of_selected 13 90264 ⟨217376, by decide⟩ ⟨13, 2, 0, 217376, 90264, 989, 16384⟩
    (by decide) selected_cut_07497

theorem selected_cut_07498 : selected 8 ⟨217412, by decide⟩
    (prefixPartial 13 90265) = some ⟨13, 2, 0, 217412, 90265, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_90265_217412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90265 ⟨217412, by decide⟩ :=
  accepted_of_selected 13 90265 ⟨217412, by decide⟩ ⟨13, 2, 0, 217412, 90265, 2569, 16384⟩
    (by decide) selected_cut_07498

theorem selected_cut_07499 : selected 8 ⟨217430, by decide⟩
    (prefixPartial 13 90266) = some ⟨13, 2, 0, 217430, 90266, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_90266_217430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90266 ⟨217430, by decide⟩ :=
  accepted_of_selected 13 90266 ⟨217430, by decide⟩ ⟨13, 2, 0, 217430, 90266, 1421, 16384⟩
    (by decide) selected_cut_07499

theorem selected_cut_07500 : selected 8 ⟨217439, by decide⟩
    (prefixPartial 13 90267) = some ⟨13, 2, 0, 217439, 90267, 901, 16384⟩ := by
  decide +kernel

theorem context_13_90267_217439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90267 ⟨217439, by decide⟩ :=
  accepted_of_selected 13 90267 ⟨217439, by decide⟩ ⟨13, 2, 0, 217439, 90267, 901, 16384⟩
    (by decide) selected_cut_07500

theorem unmarked_context_12_22566_217440 : frontier 9 ⟨217440, by decide⟩
    (prefixCache 12 22566) (prefixPartial 12 22566) = false := by
  decide +kernel

theorem node_context_12_22566_217440 : EJMOriginalGlobalDAGData.nodes 9 ⟨217440, by decide⟩ =
    .split (coordinate 12) (![⟨217376, by decide⟩,⟨217412, by decide⟩,⟨217430, by decide⟩,⟨217439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22566_217440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22566 ⟨217440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22566
    ⟨217440, by decide⟩ (by decide) (![⟨217376, by decide⟩,⟨217412, by decide⟩,⟨217430, by decide⟩,⟨217439, by decide⟩]) unmarked_context_12_22566_217440 node_context_12_22566_217440
  intro a
  fin_cases a
  · exact context_13_90264_217376
  · exact context_13_90265_217412
  · exact context_13_90266_217430
  · exact context_13_90267_217439

theorem selected_cut_07501 : selected 8 ⟨217454, by decide⟩
    (prefixPartial 13 90268) = some ⟨13, 2, 0, 217454, 90268, 969, 16384⟩ := by
  decide +kernel

theorem context_13_90268_217454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90268 ⟨217454, by decide⟩ :=
  accepted_of_selected 13 90268 ⟨217454, by decide⟩ ⟨13, 2, 0, 217454, 90268, 969, 16384⟩
    (by decide) selected_cut_07501

theorem selected_cut_07502 : selected 8 ⟨217494, by decide⟩
    (prefixPartial 13 90269) = some ⟨13, 2, 0, 217494, 90269, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_90269_217494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90269 ⟨217494, by decide⟩ :=
  accepted_of_selected 13 90269 ⟨217494, by decide⟩ ⟨13, 2, 0, 217494, 90269, 2629, 16384⟩
    (by decide) selected_cut_07502

theorem selected_cut_07503 : selected 8 ⟨217509, by decide⟩
    (prefixPartial 13 90270) = some ⟨13, 2, 0, 217509, 90270, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_90270_217509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90270 ⟨217509, by decide⟩ :=
  accepted_of_selected 13 90270 ⟨217509, by decide⟩ ⟨13, 2, 0, 217509, 90270, 1273, 16384⟩
    (by decide) selected_cut_07503

theorem selected_cut_07504 : selected 8 ⟨217518, by decide⟩
    (prefixPartial 13 90271) = some ⟨13, 2, 0, 217518, 90271, 921, 16384⟩ := by
  decide +kernel

theorem context_13_90271_217518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90271 ⟨217518, by decide⟩ :=
  accepted_of_selected 13 90271 ⟨217518, by decide⟩ ⟨13, 2, 0, 217518, 90271, 921, 16384⟩
    (by decide) selected_cut_07504

theorem unmarked_context_12_22567_217519 : frontier 9 ⟨217519, by decide⟩
    (prefixCache 12 22567) (prefixPartial 12 22567) = false := by
  decide +kernel

theorem node_context_12_22567_217519 : EJMOriginalGlobalDAGData.nodes 9 ⟨217519, by decide⟩ =
    .split (coordinate 12) (![⟨217454, by decide⟩,⟨217494, by decide⟩,⟨217509, by decide⟩,⟨217518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22567_217519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22567 ⟨217519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22567
    ⟨217519, by decide⟩ (by decide) (![⟨217454, by decide⟩,⟨217494, by decide⟩,⟨217509, by decide⟩,⟨217518, by decide⟩]) unmarked_context_12_22567_217519 node_context_12_22567_217519
  intro a
  fin_cases a
  · exact context_13_90268_217454
  · exact context_13_90269_217494
  · exact context_13_90270_217509
  · exact context_13_90271_217518

theorem unmarked_context_11_5641_217520 : frontier 10 ⟨217520, by decide⟩
    (prefixCache 11 5641) (prefixPartial 11 5641) = false := by
  decide +kernel

theorem node_context_11_5641_217520 : EJMOriginalGlobalDAGData.nodes 10 ⟨217520, by decide⟩ =
    .split (coordinate 11) (![⟨217298, by decide⟩,⟨217361, by decide⟩,⟨217440, by decide⟩,⟨217519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5641_217520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5641 ⟨217520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5641
    ⟨217520, by decide⟩ (by decide) (![⟨217298, by decide⟩,⟨217361, by decide⟩,⟨217440, by decide⟩,⟨217519, by decide⟩]) unmarked_context_11_5641_217520 node_context_11_5641_217520
  intro a
  fin_cases a
  · exact context_12_22564_217298
  · exact context_12_22565_217361
  · exact context_12_22566_217440
  · exact context_12_22567_217519

theorem selected_cut_07505 : selected 8 ⟨217538, by decide⟩
    (prefixPartial 13 90272) = some ⟨13, 2, 0, 217538, 90272, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_90272_217538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90272 ⟨217538, by decide⟩ :=
  accepted_of_selected 13 90272 ⟨217538, by decide⟩ ⟨13, 2, 0, 217538, 90272, 1033, 16384⟩
    (by decide) selected_cut_07505

theorem selected_cut_07506 : selected 8 ⟨217599, by decide⟩
    (prefixPartial 13 90273) = some ⟨13, 2, 0, 217599, 90273, 3529, 16384⟩ := by
  decide +kernel

theorem context_13_90273_217599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90273 ⟨217599, by decide⟩ :=
  accepted_of_selected 13 90273 ⟨217599, by decide⟩ ⟨13, 2, 0, 217599, 90273, 3529, 16384⟩
    (by decide) selected_cut_07506

theorem selected_cut_07507 : selected 8 ⟨217622, by decide⟩
    (prefixPartial 13 90274) = some ⟨13, 2, 0, 217622, 90274, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_90274_217622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90274 ⟨217622, by decide⟩ :=
  accepted_of_selected 13 90274 ⟨217622, by decide⟩ ⟨13, 2, 0, 217622, 90274, 1817, 16384⟩
    (by decide) selected_cut_07507

theorem selected_cut_07508 : selected 8 ⟨217638, by decide⟩
    (prefixPartial 13 90275) = some ⟨13, 2, 0, 217638, 90275, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_90275_217638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90275 ⟨217638, by decide⟩ :=
  accepted_of_selected 13 90275 ⟨217638, by decide⟩ ⟨13, 2, 0, 217638, 90275, 1133, 16384⟩
    (by decide) selected_cut_07508

theorem unmarked_context_12_22568_217639 : frontier 9 ⟨217639, by decide⟩
    (prefixCache 12 22568) (prefixPartial 12 22568) = false := by
  decide +kernel

theorem node_context_12_22568_217639 : EJMOriginalGlobalDAGData.nodes 9 ⟨217639, by decide⟩ =
    .split (coordinate 12) (![⟨217538, by decide⟩,⟨217599, by decide⟩,⟨217622, by decide⟩,⟨217638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22568_217639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22568 ⟨217639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22568
    ⟨217639, by decide⟩ (by decide) (![⟨217538, by decide⟩,⟨217599, by decide⟩,⟨217622, by decide⟩,⟨217638, by decide⟩]) unmarked_context_12_22568_217639 node_context_12_22568_217639
  intro a
  fin_cases a
  · exact context_13_90272_217538
  · exact context_13_90273_217599
  · exact context_13_90274_217622
  · exact context_13_90275_217638

theorem selected_cut_07509 : selected 8 ⟨217660, by decide⟩
    (prefixPartial 13 90276) = some ⟨13, 2, 0, 217660, 90276, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_90276_217660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90276 ⟨217660, by decide⟩ :=
  accepted_of_selected 13 90276 ⟨217660, by decide⟩ ⟨13, 2, 0, 217660, 90276, 1217, 16384⟩
    (by decide) selected_cut_07509

theorem selected_cut_07510 : selected 8 ⟨217708, by decide⟩
    (prefixPartial 13 90277) = some ⟨13, 2, 0, 217708, 90277, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_90277_217708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90277 ⟨217708, by decide⟩ :=
  accepted_of_selected 13 90277 ⟨217708, by decide⟩ ⟨13, 2, 0, 217708, 90277, 3085, 16384⟩
    (by decide) selected_cut_07510

theorem selected_cut_07511 : selected 8 ⟨217738, by decide⟩
    (prefixPartial 13 90278) = some ⟨13, 2, 0, 217738, 90278, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_90278_217738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90278 ⟨217738, by decide⟩ :=
  accepted_of_selected 13 90278 ⟨217738, by decide⟩ ⟨13, 2, 0, 217738, 90278, 1885, 16384⟩
    (by decide) selected_cut_07511

theorem selected_cut_07512 : selected 8 ⟨217749, by decide⟩
    (prefixPartial 13 90279) = some ⟨13, 2, 0, 217749, 90279, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_90279_217749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90279 ⟨217749, by decide⟩ :=
  accepted_of_selected 13 90279 ⟨217749, by decide⟩ ⟨13, 2, 0, 217749, 90279, 1201, 16384⟩
    (by decide) selected_cut_07512

theorem unmarked_context_12_22569_217750 : frontier 9 ⟨217750, by decide⟩
    (prefixCache 12 22569) (prefixPartial 12 22569) = false := by
  decide +kernel

theorem node_context_12_22569_217750 : EJMOriginalGlobalDAGData.nodes 9 ⟨217750, by decide⟩ =
    .split (coordinate 12) (![⟨217660, by decide⟩,⟨217708, by decide⟩,⟨217738, by decide⟩,⟨217749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22569_217750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22569 ⟨217750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22569
    ⟨217750, by decide⟩ (by decide) (![⟨217660, by decide⟩,⟨217708, by decide⟩,⟨217738, by decide⟩,⟨217749, by decide⟩]) unmarked_context_12_22569_217750 node_context_12_22569_217750
  intro a
  fin_cases a
  · exact context_13_90276_217660
  · exact context_13_90277_217708
  · exact context_13_90278_217738
  · exact context_13_90279_217749

theorem selected_cut_07513 : selected 9 ⟨93922, by decide⟩
    (prefixPartial 12 22570) = some ⟨12, 1, 0, 93922, 22570, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22570_93922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22570 ⟨93922, by decide⟩ :=
  accepted_of_selected 12 22570 ⟨93922, by decide⟩ ⟨12, 1, 0, 93922, 22570, 1, 65536⟩
    (by decide) selected_cut_07513

theorem selected_cut_07514 : selected 8 ⟨217773, by decide⟩
    (prefixPartial 13 90284) = some ⟨13, 2, 0, 217773, 90284, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_90284_217773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90284 ⟨217773, by decide⟩ :=
  accepted_of_selected 13 90284 ⟨217773, by decide⟩ ⟨13, 2, 0, 217773, 90284, 1449, 16384⟩
    (by decide) selected_cut_07514

theorem selected_cut_07515 : selected 7 ⟨217797, by decide⟩
    (prefixPartial 14 361140) = some ⟨14, 2, 0, 217797, 361140, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_361140_217797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361140 ⟨217797, by decide⟩ :=
  accepted_of_selected 14 361140 ⟨217797, by decide⟩ ⟨14, 2, 0, 217797, 361140, 1181, 4096⟩
    (by decide) selected_cut_07515

theorem selected_cut_07516 : selected 7 ⟨217818, by decide⟩
    (prefixPartial 14 361141) = some ⟨14, 2, 0, 217818, 361141, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_361141_217818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361141 ⟨217818, by decide⟩ :=
  accepted_of_selected 14 361141 ⟨217818, by decide⟩ ⟨14, 2, 0, 217818, 361141, 1085, 4096⟩
    (by decide) selected_cut_07516

theorem selected_cut_07517 : selected 7 ⟨217828, by decide⟩
    (prefixPartial 14 361142) = some ⟨14, 2, 0, 217828, 361142, 985, 4096⟩ := by
  decide +kernel

theorem context_14_361142_217828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361142 ⟨217828, by decide⟩ :=
  accepted_of_selected 14 361142 ⟨217828, by decide⟩ ⟨14, 2, 0, 217828, 361142, 985, 4096⟩
    (by decide) selected_cut_07517

theorem selected_cut_07518 : selected 7 ⟨217841, by decide⟩
    (prefixPartial 14 361143) = some ⟨14, 2, 0, 217841, 361143, 877, 4096⟩ := by
  decide +kernel

theorem context_14_361143_217841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 361143 ⟨217841, by decide⟩ :=
  accepted_of_selected 14 361143 ⟨217841, by decide⟩ ⟨14, 2, 0, 217841, 361143, 877, 4096⟩
    (by decide) selected_cut_07518

theorem unmarked_context_13_90285_217842 : frontier 8 ⟨217842, by decide⟩
    (prefixCache 13 90285) (prefixPartial 13 90285) = false := by
  decide +kernel

theorem node_context_13_90285_217842 : EJMOriginalGlobalDAGData.nodes 8 ⟨217842, by decide⟩ =
    .split (coordinate 13) (![⟨217797, by decide⟩,⟨217818, by decide⟩,⟨217828, by decide⟩,⟨217841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_90285_217842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90285 ⟨217842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 90285
    ⟨217842, by decide⟩ (by decide) (![⟨217797, by decide⟩,⟨217818, by decide⟩,⟨217828, by decide⟩,⟨217841, by decide⟩]) unmarked_context_13_90285_217842 node_context_13_90285_217842
  intro a
  fin_cases a
  · exact context_14_361140_217797
  · exact context_14_361141_217818
  · exact context_14_361142_217828
  · exact context_14_361143_217841

theorem selected_cut_07519 : selected 8 ⟨217865, by decide⟩
    (prefixPartial 13 90286) = some ⟨13, 2, 0, 217865, 90286, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_90286_217865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90286 ⟨217865, by decide⟩ :=
  accepted_of_selected 13 90286 ⟨217865, by decide⟩ ⟨13, 2, 0, 217865, 90286, 1901, 16384⟩
    (by decide) selected_cut_07519

theorem selected_cut_07520 : selected 8 ⟨217880, by decide⟩
    (prefixPartial 13 90287) = some ⟨13, 2, 0, 217880, 90287, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_90287_217880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90287 ⟨217880, by decide⟩ :=
  accepted_of_selected 13 90287 ⟨217880, by decide⟩ ⟨13, 2, 0, 217880, 90287, 1221, 16384⟩
    (by decide) selected_cut_07520

theorem unmarked_context_12_22571_217881 : frontier 9 ⟨217881, by decide⟩
    (prefixCache 12 22571) (prefixPartial 12 22571) = false := by
  decide +kernel

theorem node_context_12_22571_217881 : EJMOriginalGlobalDAGData.nodes 9 ⟨217881, by decide⟩ =
    .split (coordinate 12) (![⟨217773, by decide⟩,⟨217842, by decide⟩,⟨217865, by decide⟩,⟨217880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22571_217881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22571 ⟨217881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22571
    ⟨217881, by decide⟩ (by decide) (![⟨217773, by decide⟩,⟨217842, by decide⟩,⟨217865, by decide⟩,⟨217880, by decide⟩]) unmarked_context_12_22571_217881 node_context_12_22571_217881
  intro a
  fin_cases a
  · exact context_13_90284_217773
  · exact context_13_90285_217842
  · exact context_13_90286_217865
  · exact context_13_90287_217880

theorem unmarked_context_11_5642_217882 : frontier 10 ⟨217882, by decide⟩
    (prefixCache 11 5642) (prefixPartial 11 5642) = false := by
  decide +kernel

theorem node_context_11_5642_217882 : EJMOriginalGlobalDAGData.nodes 10 ⟨217882, by decide⟩ =
    .split (coordinate 11) (![⟨217639, by decide⟩,⟨217750, by decide⟩,⟨93922, by decide⟩,⟨217881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5642_217882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5642 ⟨217882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5642
    ⟨217882, by decide⟩ (by decide) (![⟨217639, by decide⟩,⟨217750, by decide⟩,⟨93922, by decide⟩,⟨217881, by decide⟩]) unmarked_context_11_5642_217882 node_context_11_5642_217882
  intro a
  fin_cases a
  · exact context_12_22568_217639
  · exact context_12_22569_217750
  · exact context_12_22570_93922
  · exact context_12_22571_217881

theorem selected_cut_07521 : selected 8 ⟨217892, by decide⟩
    (prefixPartial 13 90288) = some ⟨13, 2, 0, 217892, 90288, 581, 16384⟩ := by
  decide +kernel

theorem context_13_90288_217892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90288 ⟨217892, by decide⟩ :=
  accepted_of_selected 13 90288 ⟨217892, by decide⟩ ⟨13, 2, 0, 217892, 90288, 581, 16384⟩
    (by decide) selected_cut_07521

theorem selected_cut_07522 : selected 8 ⟨217928, by decide⟩
    (prefixPartial 13 90289) = some ⟨13, 2, 0, 217928, 90289, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_90289_217928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90289 ⟨217928, by decide⟩ :=
  accepted_of_selected 13 90289 ⟨217928, by decide⟩ ⟨13, 2, 0, 217928, 90289, 2445, 16384⟩
    (by decide) selected_cut_07522

theorem selected_cut_07523 : selected 8 ⟨217947, by decide⟩
    (prefixPartial 13 90290) = some ⟨13, 2, 0, 217947, 90290, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_90290_217947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90290 ⟨217947, by decide⟩ :=
  accepted_of_selected 13 90290 ⟨217947, by decide⟩ ⟨13, 2, 0, 217947, 90290, 1253, 16384⟩
    (by decide) selected_cut_07523

theorem selected_cut_07524 : selected 8 ⟨217955, by decide⟩
    (prefixPartial 13 90291) = some ⟨13, 2, 0, 217955, 90291, 857, 16384⟩ := by
  decide +kernel

theorem context_13_90291_217955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90291 ⟨217955, by decide⟩ :=
  accepted_of_selected 13 90291 ⟨217955, by decide⟩ ⟨13, 2, 0, 217955, 90291, 857, 16384⟩
    (by decide) selected_cut_07524

theorem unmarked_context_12_22572_217956 : frontier 9 ⟨217956, by decide⟩
    (prefixCache 12 22572) (prefixPartial 12 22572) = false := by
  decide +kernel

theorem node_context_12_22572_217956 : EJMOriginalGlobalDAGData.nodes 9 ⟨217956, by decide⟩ =
    .split (coordinate 12) (![⟨217892, by decide⟩,⟨217928, by decide⟩,⟨217947, by decide⟩,⟨217955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22572_217956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22572 ⟨217956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22572
    ⟨217956, by decide⟩ (by decide) (![⟨217892, by decide⟩,⟨217928, by decide⟩,⟨217947, by decide⟩,⟨217955, by decide⟩]) unmarked_context_12_22572_217956 node_context_12_22572_217956
  intro a
  fin_cases a
  · exact context_13_90288_217892
  · exact context_13_90289_217928
  · exact context_13_90290_217947
  · exact context_13_90291_217955

theorem selected_cut_07525 : selected 8 ⟨217966, by decide⟩
    (prefixPartial 13 90292) = some ⟨13, 2, 0, 217966, 90292, 641, 16384⟩ := by
  decide +kernel

theorem context_13_90292_217966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90292 ⟨217966, by decide⟩ :=
  accepted_of_selected 13 90292 ⟨217966, by decide⟩ ⟨13, 2, 0, 217966, 90292, 641, 16384⟩
    (by decide) selected_cut_07525

theorem selected_cut_07526 : selected 8 ⟨217995, by decide⟩
    (prefixPartial 13 90293) = some ⟨13, 2, 0, 217995, 90293, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_90293_217995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90293 ⟨217995, by decide⟩ :=
  accepted_of_selected 13 90293 ⟨217995, by decide⟩ ⟨13, 2, 0, 217995, 90293, 2193, 16384⟩
    (by decide) selected_cut_07526

theorem selected_cut_07527 : selected 8 ⟨218018, by decide⟩
    (prefixPartial 13 90294) = some ⟨13, 2, 0, 218018, 90294, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_90294_218018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90294 ⟨218018, by decide⟩ :=
  accepted_of_selected 13 90294 ⟨218018, by decide⟩ ⟨13, 2, 0, 218018, 90294, 1441, 16384⟩
    (by decide) selected_cut_07527

theorem selected_cut_07528 : selected 8 ⟨218024, by decide⟩
    (prefixPartial 13 90295) = some ⟨13, 2, 0, 218024, 90295, 877, 16384⟩ := by
  decide +kernel

theorem context_13_90295_218024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90295 ⟨218024, by decide⟩ :=
  accepted_of_selected 13 90295 ⟨218024, by decide⟩ ⟨13, 2, 0, 218024, 90295, 877, 16384⟩
    (by decide) selected_cut_07528

theorem unmarked_context_12_22573_218025 : frontier 9 ⟨218025, by decide⟩
    (prefixCache 12 22573) (prefixPartial 12 22573) = false := by
  decide +kernel

theorem node_context_12_22573_218025 : EJMOriginalGlobalDAGData.nodes 9 ⟨218025, by decide⟩ =
    .split (coordinate 12) (![⟨217966, by decide⟩,⟨217995, by decide⟩,⟨218018, by decide⟩,⟨218024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22573_218025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22573 ⟨218025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22573
    ⟨218025, by decide⟩ (by decide) (![⟨217966, by decide⟩,⟨217995, by decide⟩,⟨218018, by decide⟩,⟨218024, by decide⟩]) unmarked_context_12_22573_218025 node_context_12_22573_218025
  intro a
  fin_cases a
  · exact context_13_90292_217966
  · exact context_13_90293_217995
  · exact context_13_90294_218018
  · exact context_13_90295_218024

theorem selected_cut_07529 : selected 8 ⟨218038, by decide⟩
    (prefixPartial 13 90296) = some ⟨13, 2, 0, 218038, 90296, 765, 16384⟩ := by
  decide +kernel

theorem context_13_90296_218038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90296 ⟨218038, by decide⟩ :=
  accepted_of_selected 13 90296 ⟨218038, by decide⟩ ⟨13, 2, 0, 218038, 90296, 765, 16384⟩
    (by decide) selected_cut_07529

theorem selected_cut_07530 : selected 8 ⟨218070, by decide⟩
    (prefixPartial 13 90297) = some ⟨13, 2, 0, 218070, 90297, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_90297_218070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90297 ⟨218070, by decide⟩ :=
  accepted_of_selected 13 90297 ⟨218070, by decide⟩ ⟨13, 2, 0, 218070, 90297, 2725, 16384⟩
    (by decide) selected_cut_07530

theorem selected_cut_07531 : selected 8 ⟨218091, by decide⟩
    (prefixPartial 13 90298) = some ⟨13, 2, 0, 218091, 90298, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_90298_218091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90298 ⟨218091, by decide⟩ :=
  accepted_of_selected 13 90298 ⟨218091, by decide⟩ ⟨13, 2, 0, 218091, 90298, 1557, 16384⟩
    (by decide) selected_cut_07531

theorem selected_cut_07532 : selected 8 ⟨218100, by decide⟩
    (prefixPartial 13 90299) = some ⟨13, 2, 0, 218100, 90299, 861, 16384⟩ := by
  decide +kernel

theorem context_13_90299_218100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90299 ⟨218100, by decide⟩ :=
  accepted_of_selected 13 90299 ⟨218100, by decide⟩ ⟨13, 2, 0, 218100, 90299, 861, 16384⟩
    (by decide) selected_cut_07532

theorem unmarked_context_12_22574_218101 : frontier 9 ⟨218101, by decide⟩
    (prefixCache 12 22574) (prefixPartial 12 22574) = false := by
  decide +kernel

theorem node_context_12_22574_218101 : EJMOriginalGlobalDAGData.nodes 9 ⟨218101, by decide⟩ =
    .split (coordinate 12) (![⟨218038, by decide⟩,⟨218070, by decide⟩,⟨218091, by decide⟩,⟨218100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22574_218101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22574 ⟨218101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22574
    ⟨218101, by decide⟩ (by decide) (![⟨218038, by decide⟩,⟨218070, by decide⟩,⟨218091, by decide⟩,⟨218100, by decide⟩]) unmarked_context_12_22574_218101 node_context_12_22574_218101
  intro a
  fin_cases a
  · exact context_13_90296_218038
  · exact context_13_90297_218070
  · exact context_13_90298_218091
  · exact context_13_90299_218100

theorem selected_cut_07533 : selected 8 ⟨218113, by decide⟩
    (prefixPartial 13 90300) = some ⟨13, 2, 0, 218113, 90300, 669, 16384⟩ := by
  decide +kernel

theorem context_13_90300_218113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90300 ⟨218113, by decide⟩ :=
  accepted_of_selected 13 90300 ⟨218113, by decide⟩ ⟨13, 2, 0, 218113, 90300, 669, 16384⟩
    (by decide) selected_cut_07533

theorem selected_cut_07534 : selected 8 ⟨218155, by decide⟩
    (prefixPartial 13 90301) = some ⟨13, 2, 0, 218155, 90301, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_90301_218155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90301 ⟨218155, by decide⟩ :=
  accepted_of_selected 13 90301 ⟨218155, by decide⟩ ⟨13, 2, 0, 218155, 90301, 2813, 16384⟩
    (by decide) selected_cut_07534

theorem selected_cut_07535 : selected 8 ⟨218171, by decide⟩
    (prefixPartial 13 90302) = some ⟨13, 2, 0, 218171, 90302, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_90302_218171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90302 ⟨218171, by decide⟩ :=
  accepted_of_selected 13 90302 ⟨218171, by decide⟩ ⟨13, 2, 0, 218171, 90302, 1225, 16384⟩
    (by decide) selected_cut_07535

theorem selected_cut_07536 : selected 8 ⟨218178, by decide⟩
    (prefixPartial 13 90303) = some ⟨13, 2, 0, 218178, 90303, 781, 16384⟩ := by
  decide +kernel

theorem context_13_90303_218178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90303 ⟨218178, by decide⟩ :=
  accepted_of_selected 13 90303 ⟨218178, by decide⟩ ⟨13, 2, 0, 218178, 90303, 781, 16384⟩
    (by decide) selected_cut_07536

theorem unmarked_context_12_22575_218179 : frontier 9 ⟨218179, by decide⟩
    (prefixCache 12 22575) (prefixPartial 12 22575) = false := by
  decide +kernel

theorem node_context_12_22575_218179 : EJMOriginalGlobalDAGData.nodes 9 ⟨218179, by decide⟩ =
    .split (coordinate 12) (![⟨218113, by decide⟩,⟨218155, by decide⟩,⟨218171, by decide⟩,⟨218178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22575_218179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22575 ⟨218179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22575
    ⟨218179, by decide⟩ (by decide) (![⟨218113, by decide⟩,⟨218155, by decide⟩,⟨218171, by decide⟩,⟨218178, by decide⟩]) unmarked_context_12_22575_218179 node_context_12_22575_218179
  intro a
  fin_cases a
  · exact context_13_90300_218113
  · exact context_13_90301_218155
  · exact context_13_90302_218171
  · exact context_13_90303_218178

theorem unmarked_context_11_5643_218180 : frontier 10 ⟨218180, by decide⟩
    (prefixCache 11 5643) (prefixPartial 11 5643) = false := by
  decide +kernel

theorem node_context_11_5643_218180 : EJMOriginalGlobalDAGData.nodes 10 ⟨218180, by decide⟩ =
    .split (coordinate 11) (![⟨217956, by decide⟩,⟨218025, by decide⟩,⟨218101, by decide⟩,⟨218179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5643_218180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5643 ⟨218180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5643
    ⟨218180, by decide⟩ (by decide) (![⟨217956, by decide⟩,⟨218025, by decide⟩,⟨218101, by decide⟩,⟨218179, by decide⟩]) unmarked_context_11_5643_218180 node_context_11_5643_218180
  intro a
  fin_cases a
  · exact context_12_22572_217956
  · exact context_12_22573_218025
  · exact context_12_22574_218101
  · exact context_12_22575_218179

theorem unmarked_context_10_1410_218181 : frontier 11 ⟨218181, by decide⟩
    (prefixCache 10 1410) (prefixPartial 10 1410) = false := by
  decide +kernel

theorem node_context_10_1410_218181 : EJMOriginalGlobalDAGData.nodes 11 ⟨218181, by decide⟩ =
    .split (coordinate 10) (![⟨217213, by decide⟩,⟨217520, by decide⟩,⟨217882, by decide⟩,⟨218180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1410_218181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1410 ⟨218181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1410
    ⟨218181, by decide⟩ (by decide) (![⟨217213, by decide⟩,⟨217520, by decide⟩,⟨217882, by decide⟩,⟨218180, by decide⟩]) unmarked_context_10_1410_218181 node_context_10_1410_218181
  intro a
  fin_cases a
  · exact context_11_5640_217213
  · exact context_11_5641_217520
  · exact context_11_5642_217882
  · exact context_11_5643_218180

theorem selected_cut_07537 : selected 8 ⟨218195, by decide⟩
    (prefixPartial 13 90304) = some ⟨13, 2, 0, 218195, 90304, 889, 16384⟩ := by
  decide +kernel

theorem context_13_90304_218195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90304 ⟨218195, by decide⟩ :=
  accepted_of_selected 13 90304 ⟨218195, by decide⟩ ⟨13, 2, 0, 218195, 90304, 889, 16384⟩
    (by decide) selected_cut_07537

theorem selected_cut_07538 : selected 8 ⟨218253, by decide⟩
    (prefixPartial 13 90305) = some ⟨13, 2, 0, 218253, 90305, 3589, 16384⟩ := by
  decide +kernel

theorem context_13_90305_218253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90305 ⟨218253, by decide⟩ :=
  accepted_of_selected 13 90305 ⟨218253, by decide⟩ ⟨13, 2, 0, 218253, 90305, 3589, 16384⟩
    (by decide) selected_cut_07538

theorem selected_cut_07539 : selected 8 ⟨218289, by decide⟩
    (prefixPartial 13 90306) = some ⟨13, 2, 0, 218289, 90306, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_90306_218289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90306 ⟨218289, by decide⟩ :=
  accepted_of_selected 13 90306 ⟨218289, by decide⟩ ⟨13, 2, 0, 218289, 90306, 2309, 16384⟩
    (by decide) selected_cut_07539

theorem selected_cut_07540 : selected 8 ⟨218301, by decide⟩
    (prefixPartial 13 90307) = some ⟨13, 2, 0, 218301, 90307, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_90307_218301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90307 ⟨218301, by decide⟩ :=
  accepted_of_selected 13 90307 ⟨218301, by decide⟩ ⟨13, 2, 0, 218301, 90307, 1133, 16384⟩
    (by decide) selected_cut_07540

theorem unmarked_context_12_22576_218302 : frontier 9 ⟨218302, by decide⟩
    (prefixCache 12 22576) (prefixPartial 12 22576) = false := by
  decide +kernel

theorem node_context_12_22576_218302 : EJMOriginalGlobalDAGData.nodes 9 ⟨218302, by decide⟩ =
    .split (coordinate 12) (![⟨218195, by decide⟩,⟨218253, by decide⟩,⟨218289, by decide⟩,⟨218301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22576_218302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22576 ⟨218302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22576
    ⟨218302, by decide⟩ (by decide) (![⟨218195, by decide⟩,⟨218253, by decide⟩,⟨218289, by decide⟩,⟨218301, by decide⟩]) unmarked_context_12_22576_218302 node_context_12_22576_218302
  intro a
  fin_cases a
  · exact context_13_90304_218195
  · exact context_13_90305_218253
  · exact context_13_90306_218289
  · exact context_13_90307_218301

theorem selected_cut_07541 : selected 8 ⟨218311, by decide⟩
    (prefixPartial 13 90308) = some ⟨13, 2, 0, 218311, 90308, 545, 16384⟩ := by
  decide +kernel

theorem context_13_90308_218311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90308 ⟨218311, by decide⟩ :=
  accepted_of_selected 13 90308 ⟨218311, by decide⟩ ⟨13, 2, 0, 218311, 90308, 545, 16384⟩
    (by decide) selected_cut_07541

theorem selected_cut_07542 : selected 8 ⟨218333, by decide⟩
    (prefixPartial 13 90309) = some ⟨13, 2, 0, 218333, 90309, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_90309_218333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90309 ⟨218333, by decide⟩ :=
  accepted_of_selected 13 90309 ⟨218333, by decide⟩ ⟨13, 2, 0, 218333, 90309, 1717, 16384⟩
    (by decide) selected_cut_07542

theorem selected_cut_07543 : selected 8 ⟨218350, by decide⟩
    (prefixPartial 13 90310) = some ⟨13, 2, 0, 218350, 90310, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_90310_218350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90310 ⟨218350, by decide⟩ :=
  accepted_of_selected 13 90310 ⟨218350, by decide⟩ ⟨13, 2, 0, 218350, 90310, 1481, 16384⟩
    (by decide) selected_cut_07543

theorem selected_cut_07544 : selected 8 ⟨218357, by decide⟩
    (prefixPartial 13 90311) = some ⟨13, 2, 0, 218357, 90311, 745, 16384⟩ := by
  decide +kernel

theorem context_13_90311_218357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90311 ⟨218357, by decide⟩ :=
  accepted_of_selected 13 90311 ⟨218357, by decide⟩ ⟨13, 2, 0, 218357, 90311, 745, 16384⟩
    (by decide) selected_cut_07544

theorem unmarked_context_12_22577_218358 : frontier 9 ⟨218358, by decide⟩
    (prefixCache 12 22577) (prefixPartial 12 22577) = false := by
  decide +kernel

theorem node_context_12_22577_218358 : EJMOriginalGlobalDAGData.nodes 9 ⟨218358, by decide⟩ =
    .split (coordinate 12) (![⟨218311, by decide⟩,⟨218333, by decide⟩,⟨218350, by decide⟩,⟨218357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22577_218358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22577 ⟨218358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22577
    ⟨218358, by decide⟩ (by decide) (![⟨218311, by decide⟩,⟨218333, by decide⟩,⟨218350, by decide⟩,⟨218357, by decide⟩]) unmarked_context_12_22577_218358 node_context_12_22577_218358
  intro a
  fin_cases a
  · exact context_13_90308_218311
  · exact context_13_90309_218333
  · exact context_13_90310_218350
  · exact context_13_90311_218357

theorem selected_cut_07545 : selected 8 ⟨218366, by decide⟩
    (prefixPartial 13 90312) = some ⟨13, 2, 0, 218366, 90312, 561, 16384⟩ := by
  decide +kernel

theorem context_13_90312_218366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90312 ⟨218366, by decide⟩ :=
  accepted_of_selected 13 90312 ⟨218366, by decide⟩ ⟨13, 2, 0, 218366, 90312, 561, 16384⟩
    (by decide) selected_cut_07545

theorem selected_cut_07546 : selected 8 ⟨218397, by decide⟩
    (prefixPartial 13 90313) = some ⟨13, 2, 0, 218397, 90313, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_90313_218397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90313 ⟨218397, by decide⟩ :=
  accepted_of_selected 13 90313 ⟨218397, by decide⟩ ⟨13, 2, 0, 218397, 90313, 2309, 16384⟩
    (by decide) selected_cut_07546

theorem selected_cut_07547 : selected 8 ⟨218421, by decide⟩
    (prefixPartial 13 90314) = some ⟨13, 2, 0, 218421, 90314, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_90314_218421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90314 ⟨218421, by decide⟩ :=
  accepted_of_selected 13 90314 ⟨218421, by decide⟩ ⟨13, 2, 0, 218421, 90314, 1549, 16384⟩
    (by decide) selected_cut_07547

theorem selected_cut_07548 : selected 8 ⟨218426, by decide⟩
    (prefixPartial 13 90315) = some ⟨13, 2, 0, 218426, 90315, 697, 16384⟩ := by
  decide +kernel

theorem context_13_90315_218426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90315 ⟨218426, by decide⟩ :=
  accepted_of_selected 13 90315 ⟨218426, by decide⟩ ⟨13, 2, 0, 218426, 90315, 697, 16384⟩
    (by decide) selected_cut_07548

theorem unmarked_context_12_22578_218427 : frontier 9 ⟨218427, by decide⟩
    (prefixCache 12 22578) (prefixPartial 12 22578) = false := by
  decide +kernel

theorem node_context_12_22578_218427 : EJMOriginalGlobalDAGData.nodes 9 ⟨218427, by decide⟩ =
    .split (coordinate 12) (![⟨218366, by decide⟩,⟨218397, by decide⟩,⟨218421, by decide⟩,⟨218426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22578_218427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22578 ⟨218427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22578
    ⟨218427, by decide⟩ (by decide) (![⟨218366, by decide⟩,⟨218397, by decide⟩,⟨218421, by decide⟩,⟨218426, by decide⟩]) unmarked_context_12_22578_218427 node_context_12_22578_218427
  intro a
  fin_cases a
  · exact context_13_90312_218366
  · exact context_13_90313_218397
  · exact context_13_90314_218421
  · exact context_13_90315_218426

theorem selected_cut_07549 : selected 8 ⟨218436, by decide⟩
    (prefixPartial 13 90316) = some ⟨13, 2, 0, 218436, 90316, 569, 16384⟩ := by
  decide +kernel

theorem context_13_90316_218436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90316 ⟨218436, by decide⟩ :=
  accepted_of_selected 13 90316 ⟨218436, by decide⟩ ⟨13, 2, 0, 218436, 90316, 569, 16384⟩
    (by decide) selected_cut_07549

theorem selected_cut_07550 : selected 8 ⟨218474, by decide⟩
    (prefixPartial 13 90317) = some ⟨13, 2, 0, 218474, 90317, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_90317_218474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90317 ⟨218474, by decide⟩ :=
  accepted_of_selected 13 90317 ⟨218474, by decide⟩ ⟨13, 2, 0, 218474, 90317, 2469, 16384⟩
    (by decide) selected_cut_07550

theorem selected_cut_07551 : selected 8 ⟨218498, by decide⟩
    (prefixPartial 13 90318) = some ⟨13, 2, 0, 218498, 90318, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_90318_218498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90318 ⟨218498, by decide⟩ :=
  accepted_of_selected 13 90318 ⟨218498, by decide⟩ ⟨13, 2, 0, 218498, 90318, 1609, 16384⟩
    (by decide) selected_cut_07551

theorem selected_cut_07552 : selected 8 ⟨218505, by decide⟩
    (prefixPartial 13 90319) = some ⟨13, 2, 0, 218505, 90319, 721, 16384⟩ := by
  decide +kernel

theorem context_13_90319_218505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90319 ⟨218505, by decide⟩ :=
  accepted_of_selected 13 90319 ⟨218505, by decide⟩ ⟨13, 2, 0, 218505, 90319, 721, 16384⟩
    (by decide) selected_cut_07552

theorem unmarked_context_12_22579_218506 : frontier 9 ⟨218506, by decide⟩
    (prefixCache 12 22579) (prefixPartial 12 22579) = false := by
  decide +kernel

theorem node_context_12_22579_218506 : EJMOriginalGlobalDAGData.nodes 9 ⟨218506, by decide⟩ =
    .split (coordinate 12) (![⟨218436, by decide⟩,⟨218474, by decide⟩,⟨218498, by decide⟩,⟨218505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22579_218506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22579 ⟨218506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22579
    ⟨218506, by decide⟩ (by decide) (![⟨218436, by decide⟩,⟨218474, by decide⟩,⟨218498, by decide⟩,⟨218505, by decide⟩]) unmarked_context_12_22579_218506 node_context_12_22579_218506
  intro a
  fin_cases a
  · exact context_13_90316_218436
  · exact context_13_90317_218474
  · exact context_13_90318_218498
  · exact context_13_90319_218505

theorem unmarked_context_11_5644_218507 : frontier 10 ⟨218507, by decide⟩
    (prefixCache 11 5644) (prefixPartial 11 5644) = false := by
  decide +kernel

theorem node_context_11_5644_218507 : EJMOriginalGlobalDAGData.nodes 10 ⟨218507, by decide⟩ =
    .split (coordinate 11) (![⟨218302, by decide⟩,⟨218358, by decide⟩,⟨218427, by decide⟩,⟨218506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5644_218507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5644 ⟨218507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5644
    ⟨218507, by decide⟩ (by decide) (![⟨218302, by decide⟩,⟨218358, by decide⟩,⟨218427, by decide⟩,⟨218506, by decide⟩]) unmarked_context_11_5644_218507 node_context_11_5644_218507
  intro a
  fin_cases a
  · exact context_12_22576_218302
  · exact context_12_22577_218358
  · exact context_12_22578_218427
  · exact context_12_22579_218506

theorem selected_cut_07553 : selected 8 ⟨218514, by decide⟩
    (prefixPartial 13 90320) = some ⟨13, 2, 0, 218514, 90320, 369, 16384⟩ := by
  decide +kernel

theorem context_13_90320_218514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90320 ⟨218514, by decide⟩ :=
  accepted_of_selected 13 90320 ⟨218514, by decide⟩ ⟨13, 2, 0, 218514, 90320, 369, 16384⟩
    (by decide) selected_cut_07553

theorem selected_cut_07554 : selected 8 ⟨218555, by decide⟩
    (prefixPartial 13 90321) = some ⟨13, 2, 0, 218555, 90321, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_90321_218555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90321 ⟨218555, by decide⟩ :=
  accepted_of_selected 13 90321 ⟨218555, by decide⟩ ⟨13, 2, 0, 218555, 90321, 2621, 16384⟩
    (by decide) selected_cut_07554

theorem selected_cut_07555 : selected 8 ⟨218578, by decide⟩
    (prefixPartial 13 90322) = some ⟨13, 2, 0, 218578, 90322, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_90322_218578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90322 ⟨218578, by decide⟩ :=
  accepted_of_selected 13 90322 ⟨218578, by decide⟩ ⟨13, 2, 0, 218578, 90322, 1493, 16384⟩
    (by decide) selected_cut_07555

theorem selected_cut_07556 : selected 8 ⟨218586, by decide⟩
    (prefixPartial 13 90323) = some ⟨13, 2, 0, 218586, 90323, 813, 16384⟩ := by
  decide +kernel

theorem context_13_90323_218586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90323 ⟨218586, by decide⟩ :=
  accepted_of_selected 13 90323 ⟨218586, by decide⟩ ⟨13, 2, 0, 218586, 90323, 813, 16384⟩
    (by decide) selected_cut_07556

theorem unmarked_context_12_22580_218587 : frontier 9 ⟨218587, by decide⟩
    (prefixCache 12 22580) (prefixPartial 12 22580) = false := by
  decide +kernel

theorem node_context_12_22580_218587 : EJMOriginalGlobalDAGData.nodes 9 ⟨218587, by decide⟩ =
    .split (coordinate 12) (![⟨218514, by decide⟩,⟨218555, by decide⟩,⟨218578, by decide⟩,⟨218586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22580_218587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22580 ⟨218587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22580
    ⟨218587, by decide⟩ (by decide) (![⟨218514, by decide⟩,⟨218555, by decide⟩,⟨218578, by decide⟩,⟨218586, by decide⟩]) unmarked_context_12_22580_218587 node_context_12_22580_218587
  intro a
  fin_cases a
  · exact context_13_90320_218514
  · exact context_13_90321_218555
  · exact context_13_90322_218578
  · exact context_13_90323_218586

theorem selected_cut_07557 : selected 8 ⟨218594, by decide⟩
    (prefixPartial 13 90324) = some ⟨13, 2, 0, 218594, 90324, 385, 16384⟩ := by
  decide +kernel

theorem context_13_90324_218594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90324 ⟨218594, by decide⟩ :=
  accepted_of_selected 13 90324 ⟨218594, by decide⟩ ⟨13, 2, 0, 218594, 90324, 385, 16384⟩
    (by decide) selected_cut_07557

theorem selected_cut_07558 : selected 8 ⟨218624, by decide⟩
    (prefixPartial 13 90325) = some ⟨13, 2, 0, 218624, 90325, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_90325_218624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90325 ⟨218624, by decide⟩ :=
  accepted_of_selected 13 90325 ⟨218624, by decide⟩ ⟨13, 2, 0, 218624, 90325, 1821, 16384⟩
    (by decide) selected_cut_07558

theorem selected_cut_07559 : selected 8 ⟨218642, by decide⟩
    (prefixPartial 13 90326) = some ⟨13, 2, 0, 218642, 90326, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_90326_218642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90326 ⟨218642, by decide⟩ :=
  accepted_of_selected 13 90326 ⟨218642, by decide⟩ ⟨13, 2, 0, 218642, 90326, 1477, 16384⟩
    (by decide) selected_cut_07559

theorem selected_cut_07560 : selected 8 ⟨218648, by decide⟩
    (prefixPartial 13 90327) = some ⟨13, 2, 0, 218648, 90327, 765, 16384⟩ := by
  decide +kernel

theorem context_13_90327_218648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90327 ⟨218648, by decide⟩ :=
  accepted_of_selected 13 90327 ⟨218648, by decide⟩ ⟨13, 2, 0, 218648, 90327, 765, 16384⟩
    (by decide) selected_cut_07560

theorem unmarked_context_12_22581_218649 : frontier 9 ⟨218649, by decide⟩
    (prefixCache 12 22581) (prefixPartial 12 22581) = false := by
  decide +kernel

theorem node_context_12_22581_218649 : EJMOriginalGlobalDAGData.nodes 9 ⟨218649, by decide⟩ =
    .split (coordinate 12) (![⟨218594, by decide⟩,⟨218624, by decide⟩,⟨218642, by decide⟩,⟨218648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22581_218649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22581 ⟨218649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22581
    ⟨218649, by decide⟩ (by decide) (![⟨218594, by decide⟩,⟨218624, by decide⟩,⟨218642, by decide⟩,⟨218648, by decide⟩]) unmarked_context_12_22581_218649 node_context_12_22581_218649
  intro a
  fin_cases a
  · exact context_13_90324_218594
  · exact context_13_90325_218624
  · exact context_13_90326_218642
  · exact context_13_90327_218648

theorem selected_cut_07561 : selected 8 ⟨218654, by decide⟩
    (prefixPartial 13 90328) = some ⟨13, 2, 0, 218654, 90328, 445, 16384⟩ := by
  decide +kernel

theorem context_13_90328_218654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90328 ⟨218654, by decide⟩ :=
  accepted_of_selected 13 90328 ⟨218654, by decide⟩ ⟨13, 2, 0, 218654, 90328, 445, 16384⟩
    (by decide) selected_cut_07561

theorem selected_cut_07562 : selected 8 ⟨218694, by decide⟩
    (prefixPartial 13 90329) = some ⟨13, 2, 0, 218694, 90329, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_90329_218694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90329 ⟨218694, by decide⟩ :=
  accepted_of_selected 13 90329 ⟨218694, by decide⟩ ⟨13, 2, 0, 218694, 90329, 2661, 16384⟩
    (by decide) selected_cut_07562

theorem selected_cut_07563 : selected 8 ⟨218717, by decide⟩
    (prefixPartial 13 90330) = some ⟨13, 2, 0, 218717, 90330, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_90330_218717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90330 ⟨218717, by decide⟩ :=
  accepted_of_selected 13 90330 ⟨218717, by decide⟩ ⟨13, 2, 0, 218717, 90330, 1637, 16384⟩
    (by decide) selected_cut_07563

theorem selected_cut_07564 : selected 8 ⟨218723, by decide⟩
    (prefixPartial 13 90331) = some ⟨13, 2, 0, 218723, 90331, 693, 16384⟩ := by
  decide +kernel

theorem context_13_90331_218723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90331 ⟨218723, by decide⟩ :=
  accepted_of_selected 13 90331 ⟨218723, by decide⟩ ⟨13, 2, 0, 218723, 90331, 693, 16384⟩
    (by decide) selected_cut_07564

theorem unmarked_context_12_22582_218724 : frontier 9 ⟨218724, by decide⟩
    (prefixCache 12 22582) (prefixPartial 12 22582) = false := by
  decide +kernel

theorem node_context_12_22582_218724 : EJMOriginalGlobalDAGData.nodes 9 ⟨218724, by decide⟩ =
    .split (coordinate 12) (![⟨218654, by decide⟩,⟨218694, by decide⟩,⟨218717, by decide⟩,⟨218723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22582_218724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22582 ⟨218724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22582
    ⟨218724, by decide⟩ (by decide) (![⟨218654, by decide⟩,⟨218694, by decide⟩,⟨218717, by decide⟩,⟨218723, by decide⟩]) unmarked_context_12_22582_218724 node_context_12_22582_218724
  intro a
  fin_cases a
  · exact context_13_90328_218654
  · exact context_13_90329_218694
  · exact context_13_90330_218717
  · exact context_13_90331_218723

theorem selected_cut_07565 : selected 8 ⟨218731, by decide⟩
    (prefixPartial 13 90332) = some ⟨13, 2, 0, 218731, 90332, 417, 16384⟩ := by
  decide +kernel

theorem context_13_90332_218731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90332 ⟨218731, by decide⟩ :=
  accepted_of_selected 13 90332 ⟨218731, by decide⟩ ⟨13, 2, 0, 218731, 90332, 417, 16384⟩
    (by decide) selected_cut_07565

theorem selected_cut_07566 : selected 8 ⟨218764, by decide⟩
    (prefixPartial 13 90333) = some ⟨13, 2, 0, 218764, 90333, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_90333_218764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90333 ⟨218764, by decide⟩ :=
  accepted_of_selected 13 90333 ⟨218764, by decide⟩ ⟨13, 2, 0, 218764, 90333, 2777, 16384⟩
    (by decide) selected_cut_07566

theorem selected_cut_07567 : selected 8 ⟨218785, by decide⟩
    (prefixPartial 13 90334) = some ⟨13, 2, 0, 218785, 90334, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_90334_218785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90334 ⟨218785, by decide⟩ :=
  accepted_of_selected 13 90334 ⟨218785, by decide⟩ ⟨13, 2, 0, 218785, 90334, 1609, 16384⟩
    (by decide) selected_cut_07567

theorem selected_cut_07568 : selected 8 ⟨218791, by decide⟩
    (prefixPartial 13 90335) = some ⟨13, 2, 0, 218791, 90335, 809, 16384⟩ := by
  decide +kernel

theorem context_13_90335_218791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90335 ⟨218791, by decide⟩ :=
  accepted_of_selected 13 90335 ⟨218791, by decide⟩ ⟨13, 2, 0, 218791, 90335, 809, 16384⟩
    (by decide) selected_cut_07568

theorem unmarked_context_12_22583_218792 : frontier 9 ⟨218792, by decide⟩
    (prefixCache 12 22583) (prefixPartial 12 22583) = false := by
  decide +kernel

theorem node_context_12_22583_218792 : EJMOriginalGlobalDAGData.nodes 9 ⟨218792, by decide⟩ =
    .split (coordinate 12) (![⟨218731, by decide⟩,⟨218764, by decide⟩,⟨218785, by decide⟩,⟨218791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22583_218792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22583 ⟨218792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22583
    ⟨218792, by decide⟩ (by decide) (![⟨218731, by decide⟩,⟨218764, by decide⟩,⟨218785, by decide⟩,⟨218791, by decide⟩]) unmarked_context_12_22583_218792 node_context_12_22583_218792
  intro a
  fin_cases a
  · exact context_13_90332_218731
  · exact context_13_90333_218764
  · exact context_13_90334_218785
  · exact context_13_90335_218791

theorem unmarked_context_11_5645_218793 : frontier 10 ⟨218793, by decide⟩
    (prefixCache 11 5645) (prefixPartial 11 5645) = false := by
  decide +kernel

theorem node_context_11_5645_218793 : EJMOriginalGlobalDAGData.nodes 10 ⟨218793, by decide⟩ =
    .split (coordinate 11) (![⟨218587, by decide⟩,⟨218649, by decide⟩,⟨218724, by decide⟩,⟨218792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5645_218793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5645 ⟨218793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5645
    ⟨218793, by decide⟩ (by decide) (![⟨218587, by decide⟩,⟨218649, by decide⟩,⟨218724, by decide⟩,⟨218792, by decide⟩]) unmarked_context_11_5645_218793 node_context_11_5645_218793
  intro a
  fin_cases a
  · exact context_12_22580_218587
  · exact context_12_22581_218649
  · exact context_12_22582_218724
  · exact context_12_22583_218792

theorem selected_cut_07569 : selected 8 ⟨218798, by decide⟩
    (prefixPartial 13 90336) = some ⟨13, 2, 0, 218798, 90336, 273, 16384⟩ := by
  decide +kernel

theorem context_13_90336_218798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90336 ⟨218798, by decide⟩ :=
  accepted_of_selected 13 90336 ⟨218798, by decide⟩ ⟨13, 2, 0, 218798, 90336, 273, 16384⟩
    (by decide) selected_cut_07569

theorem selected_cut_07570 : selected 8 ⟨218840, by decide⟩
    (prefixPartial 13 90337) = some ⟨13, 2, 0, 218840, 90337, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_90337_218840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90337 ⟨218840, by decide⟩ :=
  accepted_of_selected 13 90337 ⟨218840, by decide⟩ ⟨13, 2, 0, 218840, 90337, 2585, 16384⟩
    (by decide) selected_cut_07570

theorem selected_cut_07571 : selected 8 ⟨218860, by decide⟩
    (prefixPartial 13 90338) = some ⟨13, 2, 0, 218860, 90338, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_90338_218860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90338 ⟨218860, by decide⟩ :=
  accepted_of_selected 13 90338 ⟨218860, by decide⟩ ⟨13, 2, 0, 218860, 90338, 1693, 16384⟩
    (by decide) selected_cut_07571

theorem selected_cut_07572 : selected 8 ⟨218867, by decide⟩
    (prefixPartial 13 90339) = some ⟨13, 2, 0, 218867, 90339, 817, 16384⟩ := by
  decide +kernel

theorem context_13_90339_218867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90339 ⟨218867, by decide⟩ :=
  accepted_of_selected 13 90339 ⟨218867, by decide⟩ ⟨13, 2, 0, 218867, 90339, 817, 16384⟩
    (by decide) selected_cut_07572

theorem unmarked_context_12_22584_218868 : frontier 9 ⟨218868, by decide⟩
    (prefixCache 12 22584) (prefixPartial 12 22584) = false := by
  decide +kernel

theorem node_context_12_22584_218868 : EJMOriginalGlobalDAGData.nodes 9 ⟨218868, by decide⟩ =
    .split (coordinate 12) (![⟨218798, by decide⟩,⟨218840, by decide⟩,⟨218860, by decide⟩,⟨218867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22584_218868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22584 ⟨218868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22584
    ⟨218868, by decide⟩ (by decide) (![⟨218798, by decide⟩,⟨218840, by decide⟩,⟨218860, by decide⟩,⟨218867, by decide⟩]) unmarked_context_12_22584_218868 node_context_12_22584_218868
  intro a
  fin_cases a
  · exact context_13_90336_218798
  · exact context_13_90337_218840
  · exact context_13_90338_218860
  · exact context_13_90339_218867

theorem selected_cut_07573 : selected 8 ⟨218874, by decide⟩
    (prefixPartial 13 90340) = some ⟨13, 2, 0, 218874, 90340, 297, 16384⟩ := by
  decide +kernel

theorem context_13_90340_218874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90340 ⟨218874, by decide⟩ :=
  accepted_of_selected 13 90340 ⟨218874, by decide⟩ ⟨13, 2, 0, 218874, 90340, 297, 16384⟩
    (by decide) selected_cut_07573

theorem selected_cut_07574 : selected 8 ⟨218901, by decide⟩
    (prefixPartial 13 90341) = some ⟨13, 2, 0, 218901, 90341, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_90341_218901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90341 ⟨218901, by decide⟩ :=
  accepted_of_selected 13 90341 ⟨218901, by decide⟩ ⟨13, 2, 0, 218901, 90341, 2229, 16384⟩
    (by decide) selected_cut_07574

theorem selected_cut_07575 : selected 8 ⟨218920, by decide⟩
    (prefixPartial 13 90342) = some ⟨13, 2, 0, 218920, 90342, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_90342_218920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90342 ⟨218920, by decide⟩ :=
  accepted_of_selected 13 90342 ⟨218920, by decide⟩ ⟨13, 2, 0, 218920, 90342, 1809, 16384⟩
    (by decide) selected_cut_07575

theorem selected_cut_07576 : selected 8 ⟨218930, by decide⟩
    (prefixPartial 13 90343) = some ⟨13, 2, 0, 218930, 90343, 821, 16384⟩ := by
  decide +kernel

theorem context_13_90343_218930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90343 ⟨218930, by decide⟩ :=
  accepted_of_selected 13 90343 ⟨218930, by decide⟩ ⟨13, 2, 0, 218930, 90343, 821, 16384⟩
    (by decide) selected_cut_07576

theorem unmarked_context_12_22585_218931 : frontier 9 ⟨218931, by decide⟩
    (prefixCache 12 22585) (prefixPartial 12 22585) = false := by
  decide +kernel

theorem node_context_12_22585_218931 : EJMOriginalGlobalDAGData.nodes 9 ⟨218931, by decide⟩ =
    .split (coordinate 12) (![⟨218874, by decide⟩,⟨218901, by decide⟩,⟨218920, by decide⟩,⟨218930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22585_218931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22585 ⟨218931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22585
    ⟨218931, by decide⟩ (by decide) (![⟨218874, by decide⟩,⟨218901, by decide⟩,⟨218920, by decide⟩,⟨218930, by decide⟩]) unmarked_context_12_22585_218931 node_context_12_22585_218931
  intro a
  fin_cases a
  · exact context_13_90340_218874
  · exact context_13_90341_218901
  · exact context_13_90342_218920
  · exact context_13_90343_218930

theorem selected_cut_07577 : selected 8 ⟨218938, by decide⟩
    (prefixPartial 13 90344) = some ⟨13, 2, 0, 218938, 90344, 241, 16384⟩ := by
  decide +kernel

theorem context_13_90344_218938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90344 ⟨218938, by decide⟩ :=
  accepted_of_selected 13 90344 ⟨218938, by decide⟩ ⟨13, 2, 0, 218938, 90344, 241, 16384⟩
    (by decide) selected_cut_07577

theorem selected_cut_07578 : selected 8 ⟨218982, by decide⟩
    (prefixPartial 13 90345) = some ⟨13, 2, 0, 218982, 90345, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_90345_218982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90345 ⟨218982, by decide⟩ :=
  accepted_of_selected 13 90345 ⟨218982, by decide⟩ ⟨13, 2, 0, 218982, 90345, 2933, 16384⟩
    (by decide) selected_cut_07578

theorem selected_cut_07579 : selected 8 ⟨219007, by decide⟩
    (prefixPartial 13 90346) = some ⟨13, 2, 0, 219007, 90346, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_90346_219007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90346 ⟨219007, by decide⟩ :=
  accepted_of_selected 13 90346 ⟨219007, by decide⟩ ⟨13, 2, 0, 219007, 90346, 1769, 16384⟩
    (by decide) selected_cut_07579

theorem selected_cut_07580 : selected 8 ⟨219015, by decide⟩
    (prefixPartial 13 90347) = some ⟨13, 2, 0, 219015, 90347, 757, 16384⟩ := by
  decide +kernel

theorem context_13_90347_219015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90347 ⟨219015, by decide⟩ :=
  accepted_of_selected 13 90347 ⟨219015, by decide⟩ ⟨13, 2, 0, 219015, 90347, 757, 16384⟩
    (by decide) selected_cut_07580

theorem unmarked_context_12_22586_219016 : frontier 9 ⟨219016, by decide⟩
    (prefixCache 12 22586) (prefixPartial 12 22586) = false := by
  decide +kernel

theorem node_context_12_22586_219016 : EJMOriginalGlobalDAGData.nodes 9 ⟨219016, by decide⟩ =
    .split (coordinate 12) (![⟨218938, by decide⟩,⟨218982, by decide⟩,⟨219007, by decide⟩,⟨219015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22586_219016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22586 ⟨219016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22586
    ⟨219016, by decide⟩ (by decide) (![⟨218938, by decide⟩,⟨218982, by decide⟩,⟨219007, by decide⟩,⟨219015, by decide⟩]) unmarked_context_12_22586_219016 node_context_12_22586_219016
  intro a
  fin_cases a
  · exact context_13_90344_218938
  · exact context_13_90345_218982
  · exact context_13_90346_219007
  · exact context_13_90347_219015

theorem selected_cut_07581 : selected 8 ⟨219021, by decide⟩
    (prefixPartial 13 90348) = some ⟨13, 2, 0, 219021, 90348, 229, 16384⟩ := by
  decide +kernel

theorem context_13_90348_219021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90348 ⟨219021, by decide⟩ :=
  accepted_of_selected 13 90348 ⟨219021, by decide⟩ ⟨13, 2, 0, 219021, 90348, 229, 16384⟩
    (by decide) selected_cut_07581

theorem selected_cut_07582 : selected 8 ⟨219063, by decide⟩
    (prefixPartial 13 90349) = some ⟨13, 2, 0, 219063, 90349, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_90349_219063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90349 ⟨219063, by decide⟩ :=
  accepted_of_selected 13 90349 ⟨219063, by decide⟩ ⟨13, 2, 0, 219063, 90349, 3101, 16384⟩
    (by decide) selected_cut_07582

theorem selected_cut_07583 : selected 8 ⟨219088, by decide⟩
    (prefixPartial 13 90350) = some ⟨13, 2, 0, 219088, 90350, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_90350_219088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90350 ⟨219088, by decide⟩ :=
  accepted_of_selected 13 90350 ⟨219088, by decide⟩ ⟨13, 2, 0, 219088, 90350, 1921, 16384⟩
    (by decide) selected_cut_07583

theorem selected_cut_07584 : selected 8 ⟨219094, by decide⟩
    (prefixPartial 13 90351) = some ⟨13, 2, 0, 219094, 90351, 849, 16384⟩ := by
  decide +kernel

theorem context_13_90351_219094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90351 ⟨219094, by decide⟩ :=
  accepted_of_selected 13 90351 ⟨219094, by decide⟩ ⟨13, 2, 0, 219094, 90351, 849, 16384⟩
    (by decide) selected_cut_07584

theorem unmarked_context_12_22587_219095 : frontier 9 ⟨219095, by decide⟩
    (prefixCache 12 22587) (prefixPartial 12 22587) = false := by
  decide +kernel

theorem node_context_12_22587_219095 : EJMOriginalGlobalDAGData.nodes 9 ⟨219095, by decide⟩ =
    .split (coordinate 12) (![⟨219021, by decide⟩,⟨219063, by decide⟩,⟨219088, by decide⟩,⟨219094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22587_219095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22587 ⟨219095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22587
    ⟨219095, by decide⟩ (by decide) (![⟨219021, by decide⟩,⟨219063, by decide⟩,⟨219088, by decide⟩,⟨219094, by decide⟩]) unmarked_context_12_22587_219095 node_context_12_22587_219095
  intro a
  fin_cases a
  · exact context_13_90348_219021
  · exact context_13_90349_219063
  · exact context_13_90350_219088
  · exact context_13_90351_219094

theorem unmarked_context_11_5646_219096 : frontier 10 ⟨219096, by decide⟩
    (prefixCache 11 5646) (prefixPartial 11 5646) = false := by
  decide +kernel

theorem node_context_11_5646_219096 : EJMOriginalGlobalDAGData.nodes 10 ⟨219096, by decide⟩ =
    .split (coordinate 11) (![⟨218868, by decide⟩,⟨218931, by decide⟩,⟨219016, by decide⟩,⟨219095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5646_219096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5646 ⟨219096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5646
    ⟨219096, by decide⟩ (by decide) (![⟨218868, by decide⟩,⟨218931, by decide⟩,⟨219016, by decide⟩,⟨219095, by decide⟩]) unmarked_context_11_5646_219096 node_context_11_5646_219096
  intro a
  fin_cases a
  · exact context_12_22584_218868
  · exact context_12_22585_218931
  · exact context_12_22586_219016
  · exact context_12_22587_219095

theorem selected_cut_07585 : selected 8 ⟨219099, by decide⟩
    (prefixPartial 13 90352) = some ⟨13, 2, 0, 219099, 90352, 125, 16384⟩ := by
  decide +kernel

theorem context_13_90352_219099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90352 ⟨219099, by decide⟩ :=
  accepted_of_selected 13 90352 ⟨219099, by decide⟩ ⟨13, 2, 0, 219099, 90352, 125, 16384⟩
    (by decide) selected_cut_07585

theorem selected_cut_07586 : selected 8 ⟨219136, by decide⟩
    (prefixPartial 13 90353) = some ⟨13, 2, 0, 219136, 90353, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_90353_219136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90353 ⟨219136, by decide⟩ :=
  accepted_of_selected 13 90353 ⟨219136, by decide⟩ ⟨13, 2, 0, 219136, 90353, 2317, 16384⟩
    (by decide) selected_cut_07586

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
