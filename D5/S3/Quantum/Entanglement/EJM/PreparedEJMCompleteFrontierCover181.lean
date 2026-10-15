/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover180
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_9_1093_442241 : frontier 12 ⟨442241, by decide⟩
    (prefixCache 9 1093) (prefixPartial 9 1093) = false := by
  decide +kernel

theorem node_context_9_1093_442241 : EJMOriginalGlobalDAGData.nodes 12 ⟨442241, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨441327, by decide⟩,⟨442240, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1093_442241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1093 ⟨442241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1093
    ⟨442241, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨441327, by decide⟩,⟨442240, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1093_442241 node_context_9_1093_442241
  intro a
  fin_cases a
  · exact context_10_4372_3442
  · exact context_10_4373_441327
  · exact context_10_4374_442240
  · exact context_10_4375_3440

theorem selected_cut_17378 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4376) = some ⟨10, 1, 0, 3442, 4376, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4376_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4376 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4376 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4376, 1, 1048576⟩
    (by decide) selected_cut_17378

theorem selected_cut_17379 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4377) = some ⟨10, 1, 0, 3442, 4377, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4377_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4377 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4377 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4377, 1, 1048576⟩
    (by decide) selected_cut_17379

theorem selected_cut_17380 : selected 10 ⟨442305, by decide⟩
    (prefixPartial 11 17512) = some ⟨11, 2, 0, 442305, 17512, 3741, 262144⟩ := by
  decide +kernel

theorem context_11_17512_442305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17512 ⟨442305, by decide⟩ :=
  accepted_of_selected 11 17512 ⟨442305, by decide⟩ ⟨11, 2, 0, 442305, 17512, 3741, 262144⟩
    (by decide) selected_cut_17380

theorem selected_cut_17381 : selected 10 ⟨442408, by decide⟩
    (prefixPartial 11 17513) = some ⟨11, 2, 0, 442408, 17513, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_17513_442408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17513 ⟨442408, by decide⟩ :=
  accepted_of_selected 11 17513 ⟨442408, by decide⟩ ⟨11, 2, 0, 442408, 17513, 2917, 262144⟩
    (by decide) selected_cut_17381

theorem selected_cut_17382 : selected 10 ⟨442433, by decide⟩
    (prefixPartial 11 17514) = some ⟨11, 2, 0, 442433, 17514, 1177, 262144⟩ := by
  decide +kernel

theorem context_11_17514_442433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17514 ⟨442433, by decide⟩ :=
  accepted_of_selected 11 17514 ⟨442433, by decide⟩ ⟨11, 2, 0, 442433, 17514, 1177, 262144⟩
    (by decide) selected_cut_17382

theorem selected_cut_17383 : selected 10 ⟨442441, by decide⟩
    (prefixPartial 11 17515) = some ⟨11, 2, 0, 442441, 17515, 461, 262144⟩ := by
  decide +kernel

theorem context_11_17515_442441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17515 ⟨442441, by decide⟩ :=
  accepted_of_selected 11 17515 ⟨442441, by decide⟩ ⟨11, 2, 0, 442441, 17515, 461, 262144⟩
    (by decide) selected_cut_17383

theorem unmarked_context_10_4378_442442 : frontier 11 ⟨442442, by decide⟩
    (prefixCache 10 4378) (prefixPartial 10 4378) = false := by
  decide +kernel

theorem node_context_10_4378_442442 : EJMOriginalGlobalDAGData.nodes 11 ⟨442442, by decide⟩ =
    .split (coordinate 10) (![⟨442305, by decide⟩,⟨442408, by decide⟩,⟨442433, by decide⟩,⟨442441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4378_442442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4378 ⟨442442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4378
    ⟨442442, by decide⟩ (by decide) (![⟨442305, by decide⟩,⟨442408, by decide⟩,⟨442433, by decide⟩,⟨442441, by decide⟩]) unmarked_context_10_4378_442442 node_context_10_4378_442442
  intro a
  fin_cases a
  · exact context_11_17512_442305
  · exact context_11_17513_442408
  · exact context_11_17514_442433
  · exact context_11_17515_442441

theorem selected_cut_17384 : selected 11 ⟨442537, by decide⟩
    (prefixPartial 10 4379) = some ⟨10, 2, 0, 442537, 4379, 2873, 1048576⟩ := by
  decide +kernel

theorem context_10_4379_442537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4379 ⟨442537, by decide⟩ :=
  accepted_of_selected 10 4379 ⟨442537, by decide⟩ ⟨10, 2, 0, 442537, 4379, 2873, 1048576⟩
    (by decide) selected_cut_17384

theorem unmarked_context_9_1094_442538 : frontier 12 ⟨442538, by decide⟩
    (prefixCache 9 1094) (prefixPartial 9 1094) = false := by
  decide +kernel

theorem node_context_9_1094_442538 : EJMOriginalGlobalDAGData.nodes 12 ⟨442538, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨442442, by decide⟩,⟨442537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1094_442538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1094 ⟨442538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1094
    ⟨442538, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨442442, by decide⟩,⟨442537, by decide⟩]) unmarked_context_9_1094_442538 node_context_9_1094_442538
  intro a
  fin_cases a
  · exact context_10_4376_3442
  · exact context_10_4377_3442
  · exact context_10_4378_442442
  · exact context_10_4379_442537

theorem selected_cut_17385 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 1095) = some ⟨9, 1, 0, 4601, 1095, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_1095_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1095 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 1095 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 1095, 1, 4194304⟩
    (by decide) selected_cut_17385

theorem unmarked_context_8_273_442539 : frontier 13 ⟨442539, by decide⟩
    (prefixCache 8 273) (prefixPartial 8 273) = false := by
  decide +kernel

theorem node_context_8_273_442539 : EJMOriginalGlobalDAGData.nodes 13 ⟨442539, by decide⟩ =
    .split (coordinate 8) (![⟨440990, by decide⟩,⟨442241, by decide⟩,⟨442538, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_273_442539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 273 ⟨442539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 273
    ⟨442539, by decide⟩ (by decide) (![⟨440990, by decide⟩,⟨442241, by decide⟩,⟨442538, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_273_442539 node_context_8_273_442539
  intro a
  fin_cases a
  · exact context_9_1092_440990
  · exact context_9_1093_442241
  · exact context_9_1094_442538
  · exact context_9_1095_4601

theorem selected_cut_17386 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17536) = some ⟨11, 1, 0, 434745, 17536, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17536_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17536 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17536 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17536, 1, 262144⟩
    (by decide) selected_cut_17386

theorem selected_cut_17387 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 70148) = some ⟨12, 1, 0, 895, 70148, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70148_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70148 ⟨895, by decide⟩ :=
  accepted_of_selected 12 70148 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 70148, 1, 65536⟩
    (by decide) selected_cut_17387

theorem selected_cut_17388 : selected 8 ⟨442628, by decide⟩
    (prefixPartial 13 280596) = some ⟨13, 2, 0, 442628, 280596, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_280596_442628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280596 ⟨442628, by decide⟩ :=
  accepted_of_selected 13 280596 ⟨442628, by decide⟩ ⟨13, 2, 0, 442628, 280596, 2721, 16384⟩
    (by decide) selected_cut_17388

theorem selected_cut_17389 : selected 8 ⟨442665, by decide⟩
    (prefixPartial 13 280597) = some ⟨13, 2, 0, 442665, 280597, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_280597_442665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280597 ⟨442665, by decide⟩ :=
  accepted_of_selected 13 280597 ⟨442665, by decide⟩ ⟨13, 2, 0, 442665, 280597, 1309, 16384⟩
    (by decide) selected_cut_17389

theorem selected_cut_17390 : selected 8 ⟨442686, by decide⟩
    (prefixPartial 13 280598) = some ⟨13, 2, 0, 442686, 280598, 593, 16384⟩ := by
  decide +kernel

theorem context_13_280598_442686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280598 ⟨442686, by decide⟩ :=
  accepted_of_selected 13 280598 ⟨442686, by decide⟩ ⟨13, 2, 0, 442686, 280598, 593, 16384⟩
    (by decide) selected_cut_17390

theorem selected_cut_17391 : selected 8 ⟨442688, by decide⟩
    (prefixPartial 13 280599) = some ⟨13, 2, 0, 442688, 280599, 133, 16384⟩ := by
  decide +kernel

theorem context_13_280599_442688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280599 ⟨442688, by decide⟩ :=
  accepted_of_selected 13 280599 ⟨442688, by decide⟩ ⟨13, 2, 0, 442688, 280599, 133, 16384⟩
    (by decide) selected_cut_17391

theorem unmarked_context_12_70149_442689 : frontier 9 ⟨442689, by decide⟩
    (prefixCache 12 70149) (prefixPartial 12 70149) = false := by
  decide +kernel

theorem node_context_12_70149_442689 : EJMOriginalGlobalDAGData.nodes 9 ⟨442689, by decide⟩ =
    .split (coordinate 12) (![⟨442628, by decide⟩,⟨442665, by decide⟩,⟨442686, by decide⟩,⟨442688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70149_442689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70149 ⟨442689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70149
    ⟨442689, by decide⟩ (by decide) (![⟨442628, by decide⟩,⟨442665, by decide⟩,⟨442686, by decide⟩,⟨442688, by decide⟩]) unmarked_context_12_70149_442689 node_context_12_70149_442689
  intro a
  fin_cases a
  · exact context_13_280596_442628
  · exact context_13_280597_442665
  · exact context_13_280598_442686
  · exact context_13_280599_442688

theorem selected_cut_17392 : selected 8 ⟨442753, by decide⟩
    (prefixPartial 13 280600) = some ⟨13, 2, 0, 442753, 280600, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_280600_442753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280600 ⟨442753, by decide⟩ :=
  accepted_of_selected 13 280600 ⟨442753, by decide⟩ ⟨13, 2, 0, 442753, 280600, 2725, 16384⟩
    (by decide) selected_cut_17392

theorem selected_cut_17393 : selected 8 ⟨442782, by decide⟩
    (prefixPartial 13 280601) = some ⟨13, 2, 0, 442782, 280601, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_280601_442782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280601 ⟨442782, by decide⟩ :=
  accepted_of_selected 13 280601 ⟨442782, by decide⟩ ⟨13, 2, 0, 442782, 280601, 2773, 16384⟩
    (by decide) selected_cut_17393

theorem selected_cut_17394 : selected 8 ⟨442807, by decide⟩
    (prefixPartial 13 280602) = some ⟨13, 2, 0, 442807, 280602, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_280602_442807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280602 ⟨442807, by decide⟩ :=
  accepted_of_selected 13 280602 ⟨442807, by decide⟩ ⟨13, 2, 0, 442807, 280602, 1717, 16384⟩
    (by decide) selected_cut_17394

theorem selected_cut_17395 : selected 8 ⟨442819, by decide⟩
    (prefixPartial 13 280603) = some ⟨13, 2, 0, 442819, 280603, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_280603_442819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280603 ⟨442819, by decide⟩ :=
  accepted_of_selected 13 280603 ⟨442819, by decide⟩ ⟨13, 2, 0, 442819, 280603, 1089, 16384⟩
    (by decide) selected_cut_17395

theorem unmarked_context_12_70150_442820 : frontier 9 ⟨442820, by decide⟩
    (prefixCache 12 70150) (prefixPartial 12 70150) = false := by
  decide +kernel

theorem node_context_12_70150_442820 : EJMOriginalGlobalDAGData.nodes 9 ⟨442820, by decide⟩ =
    .split (coordinate 12) (![⟨442753, by decide⟩,⟨442782, by decide⟩,⟨442807, by decide⟩,⟨442819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70150_442820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70150 ⟨442820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70150
    ⟨442820, by decide⟩ (by decide) (![⟨442753, by decide⟩,⟨442782, by decide⟩,⟨442807, by decide⟩,⟨442819, by decide⟩]) unmarked_context_12_70150_442820 node_context_12_70150_442820
  intro a
  fin_cases a
  · exact context_13_280600_442753
  · exact context_13_280601_442782
  · exact context_13_280602_442807
  · exact context_13_280603_442819

theorem selected_cut_17396 : selected 8 ⟨442889, by decide⟩
    (prefixPartial 13 280604) = some ⟨13, 2, 0, 442889, 280604, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_280604_442889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280604 ⟨442889, by decide⟩ :=
  accepted_of_selected 13 280604 ⟨442889, by decide⟩ ⟨13, 2, 0, 442889, 280604, 2693, 16384⟩
    (by decide) selected_cut_17396

theorem selected_cut_17397 : selected 8 ⟨442922, by decide⟩
    (prefixPartial 13 280605) = some ⟨13, 2, 0, 442922, 280605, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_280605_442922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280605 ⟨442922, by decide⟩ :=
  accepted_of_selected 13 280605 ⟨442922, by decide⟩ ⟨13, 2, 0, 442922, 280605, 2761, 16384⟩
    (by decide) selected_cut_17397

theorem selected_cut_17398 : selected 8 ⟨442953, by decide⟩
    (prefixPartial 13 280606) = some ⟨13, 2, 0, 442953, 280606, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_280606_442953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280606 ⟨442953, by decide⟩ :=
  accepted_of_selected 13 280606 ⟨442953, by decide⟩ ⟨13, 2, 0, 442953, 280606, 1909, 16384⟩
    (by decide) selected_cut_17398

theorem selected_cut_17399 : selected 8 ⟨442962, by decide⟩
    (prefixPartial 13 280607) = some ⟨13, 2, 0, 442962, 280607, 997, 16384⟩ := by
  decide +kernel

theorem context_13_280607_442962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280607 ⟨442962, by decide⟩ :=
  accepted_of_selected 13 280607 ⟨442962, by decide⟩ ⟨13, 2, 0, 442962, 280607, 997, 16384⟩
    (by decide) selected_cut_17399

theorem unmarked_context_12_70151_442963 : frontier 9 ⟨442963, by decide⟩
    (prefixCache 12 70151) (prefixPartial 12 70151) = false := by
  decide +kernel

theorem node_context_12_70151_442963 : EJMOriginalGlobalDAGData.nodes 9 ⟨442963, by decide⟩ =
    .split (coordinate 12) (![⟨442889, by decide⟩,⟨442922, by decide⟩,⟨442953, by decide⟩,⟨442962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70151_442963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70151 ⟨442963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70151
    ⟨442963, by decide⟩ (by decide) (![⟨442889, by decide⟩,⟨442922, by decide⟩,⟨442953, by decide⟩,⟨442962, by decide⟩]) unmarked_context_12_70151_442963 node_context_12_70151_442963
  intro a
  fin_cases a
  · exact context_13_280604_442889
  · exact context_13_280605_442922
  · exact context_13_280606_442953
  · exact context_13_280607_442962

theorem unmarked_context_11_17537_442964 : frontier 10 ⟨442964, by decide⟩
    (prefixCache 11 17537) (prefixPartial 11 17537) = false := by
  decide +kernel

theorem node_context_11_17537_442964 : EJMOriginalGlobalDAGData.nodes 10 ⟨442964, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨442689, by decide⟩,⟨442820, by decide⟩,⟨442963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17537_442964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17537 ⟨442964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17537
    ⟨442964, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨442689, by decide⟩,⟨442820, by decide⟩,⟨442963, by decide⟩]) unmarked_context_11_17537_442964 node_context_11_17537_442964
  intro a
  fin_cases a
  · exact context_12_70148_895
  · exact context_12_70149_442689
  · exact context_12_70150_442820
  · exact context_12_70151_442963

theorem selected_cut_17400 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 70152) = some ⟨12, 1, 0, 895, 70152, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70152_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70152 ⟨895, by decide⟩ :=
  accepted_of_selected 12 70152 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 70152, 1, 65536⟩
    (by decide) selected_cut_17400

theorem selected_cut_17401 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 70153) = some ⟨12, 1, 0, 895, 70153, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70153_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70153 ⟨895, by decide⟩ :=
  accepted_of_selected 12 70153 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 70153, 1, 65536⟩
    (by decide) selected_cut_17401

theorem selected_cut_17402 : selected 9 ⟨50180, by decide⟩
    (prefixPartial 12 70154) = some ⟨12, 1, 0, 50180, 70154, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70154_50180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70154 ⟨50180, by decide⟩ :=
  accepted_of_selected 12 70154 ⟨50180, by decide⟩ ⟨12, 1, 0, 50180, 70154, 1, 65536⟩
    (by decide) selected_cut_17402

theorem selected_cut_17403 : selected 8 ⟨443012, by decide⟩
    (prefixPartial 13 280620) = some ⟨13, 2, 0, 443012, 280620, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_280620_443012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280620 ⟨443012, by decide⟩ :=
  accepted_of_selected 13 280620 ⟨443012, by decide⟩ ⟨13, 2, 0, 443012, 280620, 2685, 16384⟩
    (by decide) selected_cut_17403

theorem selected_cut_17404 : selected 8 ⟨443044, by decide⟩
    (prefixPartial 13 280621) = some ⟨13, 2, 0, 443044, 280621, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_280621_443044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280621 ⟨443044, by decide⟩ :=
  accepted_of_selected 13 280621 ⟨443044, by decide⟩ ⟨13, 2, 0, 443044, 280621, 2861, 16384⟩
    (by decide) selected_cut_17404

theorem selected_cut_17405 : selected 8 ⟨443062, by decide⟩
    (prefixPartial 13 280622) = some ⟨13, 2, 0, 443062, 280622, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_280622_443062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280622 ⟨443062, by decide⟩ :=
  accepted_of_selected 13 280622 ⟨443062, by decide⟩ ⟨13, 2, 0, 443062, 280622, 1761, 16384⟩
    (by decide) selected_cut_17405

theorem selected_cut_17406 : selected 8 ⟨443074, by decide⟩
    (prefixPartial 13 280623) = some ⟨13, 2, 0, 443074, 280623, 949, 16384⟩ := by
  decide +kernel

theorem context_13_280623_443074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280623 ⟨443074, by decide⟩ :=
  accepted_of_selected 13 280623 ⟨443074, by decide⟩ ⟨13, 2, 0, 443074, 280623, 949, 16384⟩
    (by decide) selected_cut_17406

theorem unmarked_context_12_70155_443075 : frontier 9 ⟨443075, by decide⟩
    (prefixCache 12 70155) (prefixPartial 12 70155) = false := by
  decide +kernel

theorem node_context_12_70155_443075 : EJMOriginalGlobalDAGData.nodes 9 ⟨443075, by decide⟩ =
    .split (coordinate 12) (![⟨443012, by decide⟩,⟨443044, by decide⟩,⟨443062, by decide⟩,⟨443074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70155_443075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70155 ⟨443075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70155
    ⟨443075, by decide⟩ (by decide) (![⟨443012, by decide⟩,⟨443044, by decide⟩,⟨443062, by decide⟩,⟨443074, by decide⟩]) unmarked_context_12_70155_443075 node_context_12_70155_443075
  intro a
  fin_cases a
  · exact context_13_280620_443012
  · exact context_13_280621_443044
  · exact context_13_280622_443062
  · exact context_13_280623_443074

theorem unmarked_context_11_17538_443076 : frontier 10 ⟨443076, by decide⟩
    (prefixCache 11 17538) (prefixPartial 11 17538) = false := by
  decide +kernel

theorem node_context_11_17538_443076 : EJMOriginalGlobalDAGData.nodes 10 ⟨443076, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨50180, by decide⟩,⟨443075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17538_443076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17538 ⟨443076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17538
    ⟨443076, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨50180, by decide⟩,⟨443075, by decide⟩]) unmarked_context_11_17538_443076 node_context_11_17538_443076
  intro a
  fin_cases a
  · exact context_12_70152_895
  · exact context_12_70153_895
  · exact context_12_70154_50180
  · exact context_12_70155_443075

theorem selected_cut_17407 : selected 10 ⟨443184, by decide⟩
    (prefixPartial 11 17539) = some ⟨11, 2, 0, 443184, 17539, 2629, 262144⟩ := by
  decide +kernel

theorem context_11_17539_443184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17539 ⟨443184, by decide⟩ :=
  accepted_of_selected 11 17539 ⟨443184, by decide⟩ ⟨11, 2, 0, 443184, 17539, 2629, 262144⟩
    (by decide) selected_cut_17407

theorem unmarked_context_10_4384_443185 : frontier 11 ⟨443185, by decide⟩
    (prefixCache 10 4384) (prefixPartial 10 4384) = false := by
  decide +kernel

theorem node_context_10_4384_443185 : EJMOriginalGlobalDAGData.nodes 11 ⟨443185, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨442964, by decide⟩,⟨443076, by decide⟩,⟨443184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4384_443185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4384 ⟨443185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4384
    ⟨443185, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨442964, by decide⟩,⟨443076, by decide⟩,⟨443184, by decide⟩]) unmarked_context_10_4384_443185 node_context_10_4384_443185
  intro a
  fin_cases a
  · exact context_11_17536_434745
  · exact context_11_17537_442964
  · exact context_11_17538_443076
  · exact context_11_17539_443184

theorem selected_cut_17408 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 70160) = some ⟨12, 1, 0, 435160, 70160, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70160_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70160 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 70160 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 70160, 1, 65536⟩
    (by decide) selected_cut_17408

theorem selected_cut_17409 : selected 8 ⟨443215, by decide⟩
    (prefixPartial 13 280644) = some ⟨13, 2, 0, 443215, 280644, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_280644_443215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280644 ⟨443215, by decide⟩ :=
  accepted_of_selected 13 280644 ⟨443215, by decide⟩ ⟨13, 2, 0, 443215, 280644, 1793, 16384⟩
    (by decide) selected_cut_17409

theorem selected_cut_17410 : selected 8 ⟨443237, by decide⟩
    (prefixPartial 13 280645) = some ⟨13, 2, 0, 443237, 280645, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_280645_443237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280645 ⟨443237, by decide⟩ :=
  accepted_of_selected 13 280645 ⟨443237, by decide⟩ ⟨13, 2, 0, 443237, 280645, 1413, 16384⟩
    (by decide) selected_cut_17410

theorem selected_cut_17411 : selected 8 ⟨443257, by decide⟩
    (prefixPartial 13 280646) = some ⟨13, 2, 0, 443257, 280646, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_280646_443257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280646 ⟨443257, by decide⟩ :=
  accepted_of_selected 13 280646 ⟨443257, by decide⟩ ⟨13, 2, 0, 443257, 280646, 1417, 16384⟩
    (by decide) selected_cut_17411

theorem selected_cut_17412 : selected 8 ⟨443265, by decide⟩
    (prefixPartial 13 280647) = some ⟨13, 2, 0, 443265, 280647, 945, 16384⟩ := by
  decide +kernel

theorem context_13_280647_443265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280647 ⟨443265, by decide⟩ :=
  accepted_of_selected 13 280647 ⟨443265, by decide⟩ ⟨13, 2, 0, 443265, 280647, 945, 16384⟩
    (by decide) selected_cut_17412

theorem unmarked_context_12_70161_443266 : frontier 9 ⟨443266, by decide⟩
    (prefixCache 12 70161) (prefixPartial 12 70161) = false := by
  decide +kernel

theorem node_context_12_70161_443266 : EJMOriginalGlobalDAGData.nodes 9 ⟨443266, by decide⟩ =
    .split (coordinate 12) (![⟨443215, by decide⟩,⟨443237, by decide⟩,⟨443257, by decide⟩,⟨443265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70161_443266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70161 ⟨443266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70161
    ⟨443266, by decide⟩ (by decide) (![⟨443215, by decide⟩,⟨443237, by decide⟩,⟨443257, by decide⟩,⟨443265, by decide⟩]) unmarked_context_12_70161_443266 node_context_12_70161_443266
  intro a
  fin_cases a
  · exact context_13_280644_443215
  · exact context_13_280645_443237
  · exact context_13_280646_443257
  · exact context_13_280647_443265

theorem selected_cut_17413 : selected 8 ⟨443291, by decide⟩
    (prefixPartial 13 280648) = some ⟨13, 2, 0, 443291, 280648, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_280648_443291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280648 ⟨443291, by decide⟩ :=
  accepted_of_selected 13 280648 ⟨443291, by decide⟩ ⟨13, 2, 0, 443291, 280648, 1361, 16384⟩
    (by decide) selected_cut_17413

theorem selected_cut_17414 : selected 8 ⟨443315, by decide⟩
    (prefixPartial 13 280649) = some ⟨13, 2, 0, 443315, 280649, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_280649_443315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280649 ⟨443315, by decide⟩ :=
  accepted_of_selected 13 280649 ⟨443315, by decide⟩ ⟨13, 2, 0, 443315, 280649, 1777, 16384⟩
    (by decide) selected_cut_17414

theorem selected_cut_17415 : selected 8 ⟨443333, by decide⟩
    (prefixPartial 13 280650) = some ⟨13, 2, 0, 443333, 280650, 873, 16384⟩ := by
  decide +kernel

theorem context_13_280650_443333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280650 ⟨443333, by decide⟩ :=
  accepted_of_selected 13 280650 ⟨443333, by decide⟩ ⟨13, 2, 0, 443333, 280650, 873, 16384⟩
    (by decide) selected_cut_17415

theorem selected_cut_17416 : selected 8 ⟨443343, by decide⟩
    (prefixPartial 13 280651) = some ⟨13, 2, 0, 443343, 280651, 809, 16384⟩ := by
  decide +kernel

theorem context_13_280651_443343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280651 ⟨443343, by decide⟩ :=
  accepted_of_selected 13 280651 ⟨443343, by decide⟩ ⟨13, 2, 0, 443343, 280651, 809, 16384⟩
    (by decide) selected_cut_17416

theorem unmarked_context_12_70162_443344 : frontier 9 ⟨443344, by decide⟩
    (prefixCache 12 70162) (prefixPartial 12 70162) = false := by
  decide +kernel

theorem node_context_12_70162_443344 : EJMOriginalGlobalDAGData.nodes 9 ⟨443344, by decide⟩ =
    .split (coordinate 12) (![⟨443291, by decide⟩,⟨443315, by decide⟩,⟨443333, by decide⟩,⟨443343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70162_443344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70162 ⟨443344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70162
    ⟨443344, by decide⟩ (by decide) (![⟨443291, by decide⟩,⟨443315, by decide⟩,⟨443333, by decide⟩,⟨443343, by decide⟩]) unmarked_context_12_70162_443344 node_context_12_70162_443344
  intro a
  fin_cases a
  · exact context_13_280648_443291
  · exact context_13_280649_443315
  · exact context_13_280650_443333
  · exact context_13_280651_443343

theorem selected_cut_17417 : selected 8 ⟨443376, by decide⟩
    (prefixPartial 13 280652) = some ⟨13, 2, 0, 443376, 280652, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_280652_443376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280652 ⟨443376, by decide⟩ :=
  accepted_of_selected 13 280652 ⟨443376, by decide⟩ ⟨13, 2, 0, 443376, 280652, 1681, 16384⟩
    (by decide) selected_cut_17417

theorem selected_cut_17418 : selected 8 ⟨443400, by decide⟩
    (prefixPartial 13 280653) = some ⟨13, 2, 0, 443400, 280653, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_280653_443400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280653 ⟨443400, by decide⟩ :=
  accepted_of_selected 13 280653 ⟨443400, by decide⟩ ⟨13, 2, 0, 443400, 280653, 2117, 16384⟩
    (by decide) selected_cut_17418

theorem selected_cut_17419 : selected 8 ⟨443422, by decide⟩
    (prefixPartial 13 280654) = some ⟨13, 2, 0, 443422, 280654, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_280654_443422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280654 ⟨443422, by decide⟩ :=
  accepted_of_selected 13 280654 ⟨443422, by decide⟩ ⟨13, 2, 0, 443422, 280654, 1273, 16384⟩
    (by decide) selected_cut_17419

theorem selected_cut_17420 : selected 8 ⟨443427, by decide⟩
    (prefixPartial 13 280655) = some ⟨13, 2, 0, 443427, 280655, 705, 16384⟩ := by
  decide +kernel

theorem context_13_280655_443427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280655 ⟨443427, by decide⟩ :=
  accepted_of_selected 13 280655 ⟨443427, by decide⟩ ⟨13, 2, 0, 443427, 280655, 705, 16384⟩
    (by decide) selected_cut_17420

theorem unmarked_context_12_70163_443428 : frontier 9 ⟨443428, by decide⟩
    (prefixCache 12 70163) (prefixPartial 12 70163) = false := by
  decide +kernel

theorem node_context_12_70163_443428 : EJMOriginalGlobalDAGData.nodes 9 ⟨443428, by decide⟩ =
    .split (coordinate 12) (![⟨443376, by decide⟩,⟨443400, by decide⟩,⟨443422, by decide⟩,⟨443427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70163_443428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70163 ⟨443428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70163
    ⟨443428, by decide⟩ (by decide) (![⟨443376, by decide⟩,⟨443400, by decide⟩,⟨443422, by decide⟩,⟨443427, by decide⟩]) unmarked_context_12_70163_443428 node_context_12_70163_443428
  intro a
  fin_cases a
  · exact context_13_280652_443376
  · exact context_13_280653_443400
  · exact context_13_280654_443422
  · exact context_13_280655_443427

theorem unmarked_context_11_17540_443429 : frontier 10 ⟨443429, by decide⟩
    (prefixCache 11 17540) (prefixPartial 11 17540) = false := by
  decide +kernel

theorem node_context_11_17540_443429 : EJMOriginalGlobalDAGData.nodes 10 ⟨443429, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨443266, by decide⟩,⟨443344, by decide⟩,⟨443428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17540_443429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17540 ⟨443429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17540
    ⟨443429, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨443266, by decide⟩,⟨443344, by decide⟩,⟨443428, by decide⟩]) unmarked_context_11_17540_443429 node_context_11_17540_443429
  intro a
  fin_cases a
  · exact context_12_70160_435160
  · exact context_12_70161_443266
  · exact context_12_70162_443344
  · exact context_12_70163_443428

theorem selected_cut_17421 : selected 8 ⟨443473, by decide⟩
    (prefixPartial 13 280656) = some ⟨13, 2, 0, 443473, 280656, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_280656_443473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280656 ⟨443473, by decide⟩ :=
  accepted_of_selected 13 280656 ⟨443473, by decide⟩ ⟨13, 2, 0, 443473, 280656, 2177, 16384⟩
    (by decide) selected_cut_17421

theorem selected_cut_17422 : selected 8 ⟨443541, by decide⟩
    (prefixPartial 13 280657) = some ⟨13, 2, 0, 443541, 280657, 3269, 16384⟩ := by
  decide +kernel

theorem context_13_280657_443541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280657 ⟨443541, by decide⟩ :=
  accepted_of_selected 13 280657 ⟨443541, by decide⟩ ⟨13, 2, 0, 443541, 280657, 3269, 16384⟩
    (by decide) selected_cut_17422

theorem selected_cut_17423 : selected 8 ⟨443571, by decide⟩
    (prefixPartial 13 280658) = some ⟨13, 2, 0, 443571, 280658, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_280658_443571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280658 ⟨443571, by decide⟩ :=
  accepted_of_selected 13 280658 ⟨443571, by decide⟩ ⟨13, 2, 0, 443571, 280658, 1917, 16384⟩
    (by decide) selected_cut_17423

theorem selected_cut_17424 : selected 8 ⟨443589, by decide⟩
    (prefixPartial 13 280659) = some ⟨13, 2, 0, 443589, 280659, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_280659_443589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280659 ⟨443589, by decide⟩ :=
  accepted_of_selected 13 280659 ⟨443589, by decide⟩ ⟨13, 2, 0, 443589, 280659, 1081, 16384⟩
    (by decide) selected_cut_17424

theorem unmarked_context_12_70164_443590 : frontier 9 ⟨443590, by decide⟩
    (prefixCache 12 70164) (prefixPartial 12 70164) = false := by
  decide +kernel

theorem node_context_12_70164_443590 : EJMOriginalGlobalDAGData.nodes 9 ⟨443590, by decide⟩ =
    .split (coordinate 12) (![⟨443473, by decide⟩,⟨443541, by decide⟩,⟨443571, by decide⟩,⟨443589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70164_443590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70164 ⟨443590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70164
    ⟨443590, by decide⟩ (by decide) (![⟨443473, by decide⟩,⟨443541, by decide⟩,⟨443571, by decide⟩,⟨443589, by decide⟩]) unmarked_context_12_70164_443590 node_context_12_70164_443590
  intro a
  fin_cases a
  · exact context_13_280656_443473
  · exact context_13_280657_443541
  · exact context_13_280658_443571
  · exact context_13_280659_443589

theorem selected_cut_17425 : selected 8 ⟨443629, by decide⟩
    (prefixPartial 13 280660) = some ⟨13, 2, 0, 443629, 280660, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_280660_443629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280660 ⟨443629, by decide⟩ :=
  accepted_of_selected 13 280660 ⟨443629, by decide⟩ ⟨13, 2, 0, 443629, 280660, 2001, 16384⟩
    (by decide) selected_cut_17425

theorem selected_cut_17426 : selected 8 ⟨443650, by decide⟩
    (prefixPartial 13 280661) = some ⟨13, 2, 0, 443650, 280661, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_280661_443650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280661 ⟨443650, by decide⟩ :=
  accepted_of_selected 13 280661 ⟨443650, by decide⟩ ⟨13, 2, 0, 443650, 280661, 1457, 16384⟩
    (by decide) selected_cut_17426

theorem selected_cut_17427 : selected 8 ⟨443667, by decide⟩
    (prefixPartial 13 280662) = some ⟨13, 2, 0, 443667, 280662, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_280662_443667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280662 ⟨443667, by decide⟩ :=
  accepted_of_selected 13 280662 ⟨443667, by decide⟩ ⟨13, 2, 0, 443667, 280662, 1545, 16384⟩
    (by decide) selected_cut_17427

theorem selected_cut_17428 : selected 8 ⟨443672, by decide⟩
    (prefixPartial 13 280663) = some ⟨13, 2, 0, 443672, 280663, 981, 16384⟩ := by
  decide +kernel

theorem context_13_280663_443672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280663 ⟨443672, by decide⟩ :=
  accepted_of_selected 13 280663 ⟨443672, by decide⟩ ⟨13, 2, 0, 443672, 280663, 981, 16384⟩
    (by decide) selected_cut_17428

theorem unmarked_context_12_70165_443673 : frontier 9 ⟨443673, by decide⟩
    (prefixCache 12 70165) (prefixPartial 12 70165) = false := by
  decide +kernel

theorem node_context_12_70165_443673 : EJMOriginalGlobalDAGData.nodes 9 ⟨443673, by decide⟩ =
    .split (coordinate 12) (![⟨443629, by decide⟩,⟨443650, by decide⟩,⟨443667, by decide⟩,⟨443672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70165_443673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70165 ⟨443673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70165
    ⟨443673, by decide⟩ (by decide) (![⟨443629, by decide⟩,⟨443650, by decide⟩,⟨443667, by decide⟩,⟨443672, by decide⟩]) unmarked_context_12_70165_443673 node_context_12_70165_443673
  intro a
  fin_cases a
  · exact context_13_280660_443629
  · exact context_13_280661_443650
  · exact context_13_280662_443667
  · exact context_13_280663_443672

theorem selected_cut_17429 : selected 8 ⟨443706, by decide⟩
    (prefixPartial 13 280664) = some ⟨13, 2, 0, 443706, 280664, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_280664_443706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280664 ⟨443706, by decide⟩ :=
  accepted_of_selected 13 280664 ⟨443706, by decide⟩ ⟨13, 2, 0, 443706, 280664, 1565, 16384⟩
    (by decide) selected_cut_17429

theorem selected_cut_17430 : selected 8 ⟨443727, by decide⟩
    (prefixPartial 13 280665) = some ⟨13, 2, 0, 443727, 280665, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_280665_443727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280665 ⟨443727, by decide⟩ :=
  accepted_of_selected 13 280665 ⟨443727, by decide⟩ ⟨13, 2, 0, 443727, 280665, 1905, 16384⟩
    (by decide) selected_cut_17430

theorem selected_cut_17431 : selected 8 ⟨443747, by decide⟩
    (prefixPartial 13 280666) = some ⟨13, 2, 0, 443747, 280666, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_280666_443747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280666 ⟨443747, by decide⟩ :=
  accepted_of_selected 13 280666 ⟨443747, by decide⟩ ⟨13, 2, 0, 443747, 280666, 1273, 16384⟩
    (by decide) selected_cut_17431

theorem selected_cut_17432 : selected 8 ⟨443757, by decide⟩
    (prefixPartial 13 280667) = some ⟨13, 2, 0, 443757, 280667, 941, 16384⟩ := by
  decide +kernel

theorem context_13_280667_443757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280667 ⟨443757, by decide⟩ :=
  accepted_of_selected 13 280667 ⟨443757, by decide⟩ ⟨13, 2, 0, 443757, 280667, 941, 16384⟩
    (by decide) selected_cut_17432

theorem unmarked_context_12_70166_443758 : frontier 9 ⟨443758, by decide⟩
    (prefixCache 12 70166) (prefixPartial 12 70166) = false := by
  decide +kernel

theorem node_context_12_70166_443758 : EJMOriginalGlobalDAGData.nodes 9 ⟨443758, by decide⟩ =
    .split (coordinate 12) (![⟨443706, by decide⟩,⟨443727, by decide⟩,⟨443747, by decide⟩,⟨443757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70166_443758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70166 ⟨443758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70166
    ⟨443758, by decide⟩ (by decide) (![⟨443706, by decide⟩,⟨443727, by decide⟩,⟨443747, by decide⟩,⟨443757, by decide⟩]) unmarked_context_12_70166_443758 node_context_12_70166_443758
  intro a
  fin_cases a
  · exact context_13_280664_443706
  · exact context_13_280665_443727
  · exact context_13_280666_443747
  · exact context_13_280667_443757

theorem selected_cut_17433 : selected 8 ⟨443794, by decide⟩
    (prefixPartial 13 280668) = some ⟨13, 2, 0, 443794, 280668, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_280668_443794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280668 ⟨443794, by decide⟩ :=
  accepted_of_selected 13 280668 ⟨443794, by decide⟩ ⟨13, 2, 0, 443794, 280668, 1861, 16384⟩
    (by decide) selected_cut_17433

theorem selected_cut_17434 : selected 8 ⟨443819, by decide⟩
    (prefixPartial 13 280669) = some ⟨13, 2, 0, 443819, 280669, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_280669_443819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280669 ⟨443819, by decide⟩ :=
  accepted_of_selected 13 280669 ⟨443819, by decide⟩ ⟨13, 2, 0, 443819, 280669, 2193, 16384⟩
    (by decide) selected_cut_17434

theorem selected_cut_17435 : selected 8 ⟨443842, by decide⟩
    (prefixPartial 13 280670) = some ⟨13, 2, 0, 443842, 280670, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_280670_443842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280670 ⟨443842, by decide⟩ :=
  accepted_of_selected 13 280670 ⟨443842, by decide⟩ ⟨13, 2, 0, 443842, 280670, 1589, 16384⟩
    (by decide) selected_cut_17435

theorem selected_cut_17436 : selected 8 ⟨443850, by decide⟩
    (prefixPartial 13 280671) = some ⟨13, 2, 0, 443850, 280671, 789, 16384⟩ := by
  decide +kernel

theorem context_13_280671_443850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280671 ⟨443850, by decide⟩ :=
  accepted_of_selected 13 280671 ⟨443850, by decide⟩ ⟨13, 2, 0, 443850, 280671, 789, 16384⟩
    (by decide) selected_cut_17436

theorem unmarked_context_12_70167_443851 : frontier 9 ⟨443851, by decide⟩
    (prefixCache 12 70167) (prefixPartial 12 70167) = false := by
  decide +kernel

theorem node_context_12_70167_443851 : EJMOriginalGlobalDAGData.nodes 9 ⟨443851, by decide⟩ =
    .split (coordinate 12) (![⟨443794, by decide⟩,⟨443819, by decide⟩,⟨443842, by decide⟩,⟨443850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70167_443851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70167 ⟨443851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70167
    ⟨443851, by decide⟩ (by decide) (![⟨443794, by decide⟩,⟨443819, by decide⟩,⟨443842, by decide⟩,⟨443850, by decide⟩]) unmarked_context_12_70167_443851 node_context_12_70167_443851
  intro a
  fin_cases a
  · exact context_13_280668_443794
  · exact context_13_280669_443819
  · exact context_13_280670_443842
  · exact context_13_280671_443850

theorem unmarked_context_11_17541_443852 : frontier 10 ⟨443852, by decide⟩
    (prefixCache 11 17541) (prefixPartial 11 17541) = false := by
  decide +kernel

theorem node_context_11_17541_443852 : EJMOriginalGlobalDAGData.nodes 10 ⟨443852, by decide⟩ =
    .split (coordinate 11) (![⟨443590, by decide⟩,⟨443673, by decide⟩,⟨443758, by decide⟩,⟨443851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17541_443852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17541 ⟨443852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17541
    ⟨443852, by decide⟩ (by decide) (![⟨443590, by decide⟩,⟨443673, by decide⟩,⟨443758, by decide⟩,⟨443851, by decide⟩]) unmarked_context_11_17541_443852 node_context_11_17541_443852
  intro a
  fin_cases a
  · exact context_12_70164_443590
  · exact context_12_70165_443673
  · exact context_12_70166_443758
  · exact context_12_70167_443851

theorem selected_cut_17437 : selected 8 ⟨443883, by decide⟩
    (prefixPartial 13 280672) = some ⟨13, 2, 0, 443883, 280672, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_280672_443883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280672 ⟨443883, by decide⟩ :=
  accepted_of_selected 13 280672 ⟨443883, by decide⟩ ⟨13, 2, 0, 443883, 280672, 1933, 16384⟩
    (by decide) selected_cut_17437

theorem selected_cut_17438 : selected 8 ⟨443920, by decide⟩
    (prefixPartial 13 280673) = some ⟨13, 2, 0, 443920, 280673, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_280673_443920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280673 ⟨443920, by decide⟩ :=
  accepted_of_selected 13 280673 ⟨443920, by decide⟩ ⟨13, 2, 0, 443920, 280673, 2709, 16384⟩
    (by decide) selected_cut_17438

theorem selected_cut_17439 : selected 8 ⟨443945, by decide⟩
    (prefixPartial 13 280674) = some ⟨13, 2, 0, 443945, 280674, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_280674_443945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280674 ⟨443945, by decide⟩ :=
  accepted_of_selected 13 280674 ⟨443945, by decide⟩ ⟨13, 2, 0, 443945, 280674, 1761, 16384⟩
    (by decide) selected_cut_17439

theorem selected_cut_17440 : selected 8 ⟨443952, by decide⟩
    (prefixPartial 13 280675) = some ⟨13, 2, 0, 443952, 280675, 913, 16384⟩ := by
  decide +kernel

theorem context_13_280675_443952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280675 ⟨443952, by decide⟩ :=
  accepted_of_selected 13 280675 ⟨443952, by decide⟩ ⟨13, 2, 0, 443952, 280675, 913, 16384⟩
    (by decide) selected_cut_17440

theorem unmarked_context_12_70168_443953 : frontier 9 ⟨443953, by decide⟩
    (prefixCache 12 70168) (prefixPartial 12 70168) = false := by
  decide +kernel

theorem node_context_12_70168_443953 : EJMOriginalGlobalDAGData.nodes 9 ⟨443953, by decide⟩ =
    .split (coordinate 12) (![⟨443883, by decide⟩,⟨443920, by decide⟩,⟨443945, by decide⟩,⟨443952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70168_443953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70168 ⟨443953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70168
    ⟨443953, by decide⟩ (by decide) (![⟨443883, by decide⟩,⟨443920, by decide⟩,⟨443945, by decide⟩,⟨443952, by decide⟩]) unmarked_context_12_70168_443953 node_context_12_70168_443953
  intro a
  fin_cases a
  · exact context_13_280672_443883
  · exact context_13_280673_443920
  · exact context_13_280674_443945
  · exact context_13_280675_443952

theorem selected_cut_17441 : selected 8 ⟨443990, by decide⟩
    (prefixPartial 13 280676) = some ⟨13, 2, 0, 443990, 280676, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_280676_443990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280676 ⟨443990, by decide⟩ :=
  accepted_of_selected 13 280676 ⟨443990, by decide⟩ ⟨13, 2, 0, 443990, 280676, 1745, 16384⟩
    (by decide) selected_cut_17441

theorem selected_cut_17442 : selected 8 ⟨444010, by decide⟩
    (prefixPartial 13 280677) = some ⟨13, 2, 0, 444010, 280677, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_280677_444010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280677 ⟨444010, by decide⟩ :=
  accepted_of_selected 13 280677 ⟨444010, by decide⟩ ⟨13, 2, 0, 444010, 280677, 1253, 16384⟩
    (by decide) selected_cut_17442

theorem selected_cut_17443 : selected 8 ⟨444029, by decide⟩
    (prefixPartial 13 280678) = some ⟨13, 2, 0, 444029, 280678, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_280678_444029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280678 ⟨444029, by decide⟩ :=
  accepted_of_selected 13 280678 ⟨444029, by decide⟩ ⟨13, 2, 0, 444029, 280678, 1517, 16384⟩
    (by decide) selected_cut_17443

theorem selected_cut_17444 : selected 8 ⟨444035, by decide⟩
    (prefixPartial 13 280679) = some ⟨13, 2, 0, 444035, 280679, 957, 16384⟩ := by
  decide +kernel

theorem context_13_280679_444035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280679 ⟨444035, by decide⟩ :=
  accepted_of_selected 13 280679 ⟨444035, by decide⟩ ⟨13, 2, 0, 444035, 280679, 957, 16384⟩
    (by decide) selected_cut_17444

theorem unmarked_context_12_70169_444036 : frontier 9 ⟨444036, by decide⟩
    (prefixCache 12 70169) (prefixPartial 12 70169) = false := by
  decide +kernel

theorem node_context_12_70169_444036 : EJMOriginalGlobalDAGData.nodes 9 ⟨444036, by decide⟩ =
    .split (coordinate 12) (![⟨443990, by decide⟩,⟨444010, by decide⟩,⟨444029, by decide⟩,⟨444035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70169_444036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70169 ⟨444036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70169
    ⟨444036, by decide⟩ (by decide) (![⟨443990, by decide⟩,⟨444010, by decide⟩,⟨444029, by decide⟩,⟨444035, by decide⟩]) unmarked_context_12_70169_444036 node_context_12_70169_444036
  intro a
  fin_cases a
  · exact context_13_280676_443990
  · exact context_13_280677_444010
  · exact context_13_280678_444029
  · exact context_13_280679_444035

theorem selected_cut_17445 : selected 8 ⟨444068, by decide⟩
    (prefixPartial 13 280680) = some ⟨13, 2, 0, 444068, 280680, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_280680_444068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280680 ⟨444068, by decide⟩ :=
  accepted_of_selected 13 280680 ⟨444068, by decide⟩ ⟨13, 2, 0, 444068, 280680, 2653, 16384⟩
    (by decide) selected_cut_17445

theorem selected_cut_17446 : selected 8 ⟨444098, by decide⟩
    (prefixPartial 13 280681) = some ⟨13, 2, 0, 444098, 280681, 2989, 16384⟩ := by
  decide +kernel

theorem context_13_280681_444098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280681 ⟨444098, by decide⟩ :=
  accepted_of_selected 13 280681 ⟨444098, by decide⟩ ⟨13, 2, 0, 444098, 280681, 2989, 16384⟩
    (by decide) selected_cut_17446

theorem selected_cut_17447 : selected 8 ⟨444125, by decide⟩
    (prefixPartial 13 280682) = some ⟨13, 2, 0, 444125, 280682, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_280682_444125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280682 ⟨444125, by decide⟩ :=
  accepted_of_selected 13 280682 ⟨444125, by decide⟩ ⟨13, 2, 0, 444125, 280682, 1977, 16384⟩
    (by decide) selected_cut_17447

theorem selected_cut_17448 : selected 8 ⟨444140, by decide⟩
    (prefixPartial 13 280683) = some ⟨13, 2, 0, 444140, 280683, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_280683_444140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280683 ⟨444140, by decide⟩ :=
  accepted_of_selected 13 280683 ⟨444140, by decide⟩ ⟨13, 2, 0, 444140, 280683, 1197, 16384⟩
    (by decide) selected_cut_17448

theorem unmarked_context_12_70170_444141 : frontier 9 ⟨444141, by decide⟩
    (prefixCache 12 70170) (prefixPartial 12 70170) = false := by
  decide +kernel

theorem node_context_12_70170_444141 : EJMOriginalGlobalDAGData.nodes 9 ⟨444141, by decide⟩ =
    .split (coordinate 12) (![⟨444068, by decide⟩,⟨444098, by decide⟩,⟨444125, by decide⟩,⟨444140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70170_444141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70170 ⟨444141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70170
    ⟨444141, by decide⟩ (by decide) (![⟨444068, by decide⟩,⟨444098, by decide⟩,⟨444125, by decide⟩,⟨444140, by decide⟩]) unmarked_context_12_70170_444141 node_context_12_70170_444141
  intro a
  fin_cases a
  · exact context_13_280680_444068
  · exact context_13_280681_444098
  · exact context_13_280682_444125
  · exact context_13_280683_444140

theorem selected_cut_17449 : selected 8 ⟨444173, by decide⟩
    (prefixPartial 13 280684) = some ⟨13, 2, 0, 444173, 280684, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_280684_444173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280684 ⟨444173, by decide⟩ :=
  accepted_of_selected 13 280684 ⟨444173, by decide⟩ ⟨13, 2, 0, 444173, 280684, 1577, 16384⟩
    (by decide) selected_cut_17449

theorem selected_cut_17450 : selected 8 ⟨444197, by decide⟩
    (prefixPartial 13 280685) = some ⟨13, 2, 0, 444197, 280685, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_280685_444197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280685 ⟨444197, by decide⟩ :=
  accepted_of_selected 13 280685 ⟨444197, by decide⟩ ⟨13, 2, 0, 444197, 280685, 2197, 16384⟩
    (by decide) selected_cut_17450

theorem selected_cut_17451 : selected 8 ⟨444213, by decide⟩
    (prefixPartial 13 280686) = some ⟨13, 2, 0, 444213, 280686, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_280686_444213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280686 ⟨444213, by decide⟩ :=
  accepted_of_selected 13 280686 ⟨444213, by decide⟩ ⟨13, 2, 0, 444213, 280686, 1437, 16384⟩
    (by decide) selected_cut_17451

theorem selected_cut_17452 : selected 8 ⟨444222, by decide⟩
    (prefixPartial 13 280687) = some ⟨13, 2, 0, 444222, 280687, 689, 16384⟩ := by
  decide +kernel

theorem context_13_280687_444222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280687 ⟨444222, by decide⟩ :=
  accepted_of_selected 13 280687 ⟨444222, by decide⟩ ⟨13, 2, 0, 444222, 280687, 689, 16384⟩
    (by decide) selected_cut_17452

theorem unmarked_context_12_70171_444223 : frontier 9 ⟨444223, by decide⟩
    (prefixCache 12 70171) (prefixPartial 12 70171) = false := by
  decide +kernel

theorem node_context_12_70171_444223 : EJMOriginalGlobalDAGData.nodes 9 ⟨444223, by decide⟩ =
    .split (coordinate 12) (![⟨444173, by decide⟩,⟨444197, by decide⟩,⟨444213, by decide⟩,⟨444222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70171_444223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70171 ⟨444223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70171
    ⟨444223, by decide⟩ (by decide) (![⟨444173, by decide⟩,⟨444197, by decide⟩,⟨444213, by decide⟩,⟨444222, by decide⟩]) unmarked_context_12_70171_444223 node_context_12_70171_444223
  intro a
  fin_cases a
  · exact context_13_280684_444173
  · exact context_13_280685_444197
  · exact context_13_280686_444213
  · exact context_13_280687_444222

theorem unmarked_context_11_17542_444224 : frontier 10 ⟨444224, by decide⟩
    (prefixCache 11 17542) (prefixPartial 11 17542) = false := by
  decide +kernel

theorem node_context_11_17542_444224 : EJMOriginalGlobalDAGData.nodes 10 ⟨444224, by decide⟩ =
    .split (coordinate 11) (![⟨443953, by decide⟩,⟨444036, by decide⟩,⟨444141, by decide⟩,⟨444223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17542_444224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17542 ⟨444224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17542
    ⟨444224, by decide⟩ (by decide) (![⟨443953, by decide⟩,⟨444036, by decide⟩,⟨444141, by decide⟩,⟨444223, by decide⟩]) unmarked_context_11_17542_444224 node_context_11_17542_444224
  intro a
  fin_cases a
  · exact context_12_70168_443953
  · exact context_12_70169_444036
  · exact context_12_70170_444141
  · exact context_12_70171_444223

theorem selected_cut_17453 : selected 8 ⟨444254, by decide⟩
    (prefixPartial 13 280688) = some ⟨13, 2, 0, 444254, 280688, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_280688_444254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280688 ⟨444254, by decide⟩ :=
  accepted_of_selected 13 280688 ⟨444254, by decide⟩ ⟨13, 2, 0, 444254, 280688, 1777, 16384⟩
    (by decide) selected_cut_17453

theorem selected_cut_17454 : selected 8 ⟨444301, by decide⟩
    (prefixPartial 13 280689) = some ⟨13, 2, 0, 444301, 280689, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_280689_444301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280689 ⟨444301, by decide⟩ :=
  accepted_of_selected 13 280689 ⟨444301, by decide⟩ ⟨13, 2, 0, 444301, 280689, 2761, 16384⟩
    (by decide) selected_cut_17454

theorem selected_cut_17455 : selected 8 ⟨444328, by decide⟩
    (prefixPartial 13 280690) = some ⟨13, 2, 0, 444328, 280690, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_280690_444328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280690 ⟨444328, by decide⟩ :=
  accepted_of_selected 13 280690 ⟨444328, by decide⟩ ⟨13, 2, 0, 444328, 280690, 1837, 16384⟩
    (by decide) selected_cut_17455

theorem selected_cut_17456 : selected 8 ⟨444339, by decide⟩
    (prefixPartial 13 280691) = some ⟨13, 2, 0, 444339, 280691, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_280691_444339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280691 ⟨444339, by decide⟩ :=
  accepted_of_selected 13 280691 ⟨444339, by decide⟩ ⟨13, 2, 0, 444339, 280691, 1093, 16384⟩
    (by decide) selected_cut_17456

theorem unmarked_context_12_70172_444340 : frontier 9 ⟨444340, by decide⟩
    (prefixCache 12 70172) (prefixPartial 12 70172) = false := by
  decide +kernel

theorem node_context_12_70172_444340 : EJMOriginalGlobalDAGData.nodes 9 ⟨444340, by decide⟩ =
    .split (coordinate 12) (![⟨444254, by decide⟩,⟨444301, by decide⟩,⟨444328, by decide⟩,⟨444339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70172_444340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70172 ⟨444340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70172
    ⟨444340, by decide⟩ (by decide) (![⟨444254, by decide⟩,⟨444301, by decide⟩,⟨444328, by decide⟩,⟨444339, by decide⟩]) unmarked_context_12_70172_444340 node_context_12_70172_444340
  intro a
  fin_cases a
  · exact context_13_280688_444254
  · exact context_13_280689_444301
  · exact context_13_280690_444328
  · exact context_13_280691_444339

theorem selected_cut_17457 : selected 8 ⟨444367, by decide⟩
    (prefixPartial 13 280692) = some ⟨13, 2, 0, 444367, 280692, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_280692_444367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280692 ⟨444367, by decide⟩ :=
  accepted_of_selected 13 280692 ⟨444367, by decide⟩ ⟨13, 2, 0, 444367, 280692, 1617, 16384⟩
    (by decide) selected_cut_17457

theorem selected_cut_17458 : selected 8 ⟨444388, by decide⟩
    (prefixPartial 13 280693) = some ⟨13, 2, 0, 444388, 280693, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_280693_444388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280693 ⟨444388, by decide⟩ :=
  accepted_of_selected 13 280693 ⟨444388, by decide⟩ ⟨13, 2, 0, 444388, 280693, 1433, 16384⟩
    (by decide) selected_cut_17458

theorem selected_cut_17459 : selected 8 ⟨444406, by decide⟩
    (prefixPartial 13 280694) = some ⟨13, 2, 0, 444406, 280694, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_280694_444406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280694 ⟨444406, by decide⟩ :=
  accepted_of_selected 13 280694 ⟨444406, by decide⟩ ⟨13, 2, 0, 444406, 280694, 1529, 16384⟩
    (by decide) selected_cut_17459

theorem selected_cut_17460 : selected 8 ⟨444412, by decide⟩
    (prefixPartial 13 280695) = some ⟨13, 2, 0, 444412, 280695, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_280695_444412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280695 ⟨444412, by decide⟩ :=
  accepted_of_selected 13 280695 ⟨444412, by decide⟩ ⟨13, 2, 0, 444412, 280695, 1037, 16384⟩
    (by decide) selected_cut_17460

theorem unmarked_context_12_70173_444413 : frontier 9 ⟨444413, by decide⟩
    (prefixCache 12 70173) (prefixPartial 12 70173) = false := by
  decide +kernel

theorem node_context_12_70173_444413 : EJMOriginalGlobalDAGData.nodes 9 ⟨444413, by decide⟩ =
    .split (coordinate 12) (![⟨444367, by decide⟩,⟨444388, by decide⟩,⟨444406, by decide⟩,⟨444412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70173_444413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70173 ⟨444413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70173
    ⟨444413, by decide⟩ (by decide) (![⟨444367, by decide⟩,⟨444388, by decide⟩,⟨444406, by decide⟩,⟨444412, by decide⟩]) unmarked_context_12_70173_444413 node_context_12_70173_444413
  intro a
  fin_cases a
  · exact context_13_280692_444367
  · exact context_13_280693_444388
  · exact context_13_280694_444406
  · exact context_13_280695_444412

theorem selected_cut_17461 : selected 8 ⟨444438, by decide⟩
    (prefixPartial 13 280696) = some ⟨13, 2, 0, 444438, 280696, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_280696_444438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280696 ⟨444438, by decide⟩ :=
  accepted_of_selected 13 280696 ⟨444438, by decide⟩ ⟨13, 2, 0, 444438, 280696, 1297, 16384⟩
    (by decide) selected_cut_17461

theorem selected_cut_17462 : selected 8 ⟨444458, by decide⟩
    (prefixPartial 13 280697) = some ⟨13, 2, 0, 444458, 280697, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_280697_444458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280697 ⟨444458, by decide⟩ :=
  accepted_of_selected 13 280697 ⟨444458, by decide⟩ ⟨13, 2, 0, 444458, 280697, 1957, 16384⟩
    (by decide) selected_cut_17462

theorem selected_cut_17463 : selected 8 ⟨444478, by decide⟩
    (prefixPartial 13 280698) = some ⟨13, 2, 0, 444478, 280698, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_280698_444478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280698 ⟨444478, by decide⟩ :=
  accepted_of_selected 13 280698 ⟨444478, by decide⟩ ⟨13, 2, 0, 444478, 280698, 1185, 16384⟩
    (by decide) selected_cut_17463

theorem selected_cut_17464 : selected 8 ⟨444489, by decide⟩
    (prefixPartial 13 280699) = some ⟨13, 2, 0, 444489, 280699, 905, 16384⟩ := by
  decide +kernel

theorem context_13_280699_444489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280699 ⟨444489, by decide⟩ :=
  accepted_of_selected 13 280699 ⟨444489, by decide⟩ ⟨13, 2, 0, 444489, 280699, 905, 16384⟩
    (by decide) selected_cut_17464

theorem unmarked_context_12_70174_444490 : frontier 9 ⟨444490, by decide⟩
    (prefixCache 12 70174) (prefixPartial 12 70174) = false := by
  decide +kernel

theorem node_context_12_70174_444490 : EJMOriginalGlobalDAGData.nodes 9 ⟨444490, by decide⟩ =
    .split (coordinate 12) (![⟨444438, by decide⟩,⟨444458, by decide⟩,⟨444478, by decide⟩,⟨444489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70174_444490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70174 ⟨444490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70174
    ⟨444490, by decide⟩ (by decide) (![⟨444438, by decide⟩,⟨444458, by decide⟩,⟨444478, by decide⟩,⟨444489, by decide⟩]) unmarked_context_12_70174_444490 node_context_12_70174_444490
  intro a
  fin_cases a
  · exact context_13_280696_444438
  · exact context_13_280697_444458
  · exact context_13_280698_444478
  · exact context_13_280699_444489

theorem selected_cut_17465 : selected 8 ⟨444516, by decide⟩
    (prefixPartial 13 280700) = some ⟨13, 2, 0, 444516, 280700, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_280700_444516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280700 ⟨444516, by decide⟩ :=
  accepted_of_selected 13 280700 ⟨444516, by decide⟩ ⟨13, 2, 0, 444516, 280700, 1513, 16384⟩
    (by decide) selected_cut_17465

theorem selected_cut_17466 : selected 8 ⟨444538, by decide⟩
    (prefixPartial 13 280701) = some ⟨13, 2, 0, 444538, 280701, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_280701_444538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280701 ⟨444538, by decide⟩ :=
  accepted_of_selected 13 280701 ⟨444538, by decide⟩ ⟨13, 2, 0, 444538, 280701, 2105, 16384⟩
    (by decide) selected_cut_17466

theorem selected_cut_17467 : selected 8 ⟨444560, by decide⟩
    (prefixPartial 13 280702) = some ⟨13, 2, 0, 444560, 280702, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_280702_444560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280702 ⟨444560, by decide⟩ :=
  accepted_of_selected 13 280702 ⟨444560, by decide⟩ ⟨13, 2, 0, 444560, 280702, 1577, 16384⟩
    (by decide) selected_cut_17467

theorem selected_cut_17468 : selected 8 ⟨444569, by decide⟩
    (prefixPartial 13 280703) = some ⟨13, 2, 0, 444569, 280703, 809, 16384⟩ := by
  decide +kernel

theorem context_13_280703_444569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280703 ⟨444569, by decide⟩ :=
  accepted_of_selected 13 280703 ⟨444569, by decide⟩ ⟨13, 2, 0, 444569, 280703, 809, 16384⟩
    (by decide) selected_cut_17468

theorem unmarked_context_12_70175_444570 : frontier 9 ⟨444570, by decide⟩
    (prefixCache 12 70175) (prefixPartial 12 70175) = false := by
  decide +kernel

theorem node_context_12_70175_444570 : EJMOriginalGlobalDAGData.nodes 9 ⟨444570, by decide⟩ =
    .split (coordinate 12) (![⟨444516, by decide⟩,⟨444538, by decide⟩,⟨444560, by decide⟩,⟨444569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70175_444570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70175 ⟨444570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70175
    ⟨444570, by decide⟩ (by decide) (![⟨444516, by decide⟩,⟨444538, by decide⟩,⟨444560, by decide⟩,⟨444569, by decide⟩]) unmarked_context_12_70175_444570 node_context_12_70175_444570
  intro a
  fin_cases a
  · exact context_13_280700_444516
  · exact context_13_280701_444538
  · exact context_13_280702_444560
  · exact context_13_280703_444569

theorem unmarked_context_11_17543_444571 : frontier 10 ⟨444571, by decide⟩
    (prefixCache 11 17543) (prefixPartial 11 17543) = false := by
  decide +kernel

theorem node_context_11_17543_444571 : EJMOriginalGlobalDAGData.nodes 10 ⟨444571, by decide⟩ =
    .split (coordinate 11) (![⟨444340, by decide⟩,⟨444413, by decide⟩,⟨444490, by decide⟩,⟨444570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17543_444571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17543 ⟨444571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17543
    ⟨444571, by decide⟩ (by decide) (![⟨444340, by decide⟩,⟨444413, by decide⟩,⟨444490, by decide⟩,⟨444570, by decide⟩]) unmarked_context_11_17543_444571 node_context_11_17543_444571
  intro a
  fin_cases a
  · exact context_12_70172_444340
  · exact context_12_70173_444413
  · exact context_12_70174_444490
  · exact context_12_70175_444570

theorem unmarked_context_10_4385_444572 : frontier 11 ⟨444572, by decide⟩
    (prefixCache 10 4385) (prefixPartial 10 4385) = false := by
  decide +kernel

theorem node_context_10_4385_444572 : EJMOriginalGlobalDAGData.nodes 11 ⟨444572, by decide⟩ =
    .split (coordinate 10) (![⟨443429, by decide⟩,⟨443852, by decide⟩,⟨444224, by decide⟩,⟨444571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4385_444572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4385 ⟨444572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4385
    ⟨444572, by decide⟩ (by decide) (![⟨443429, by decide⟩,⟨443852, by decide⟩,⟨444224, by decide⟩,⟨444571, by decide⟩]) unmarked_context_10_4385_444572 node_context_10_4385_444572
  intro a
  fin_cases a
  · exact context_11_17540_443429
  · exact context_11_17541_443852
  · exact context_11_17542_444224
  · exact context_11_17543_444571

theorem selected_cut_17469 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 70176) = some ⟨12, 1, 0, 435790, 70176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70176_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70176 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 70176 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 70176, 1, 65536⟩
    (by decide) selected_cut_17469

theorem selected_cut_17470 : selected 8 ⟨444601, by decide⟩
    (prefixPartial 13 280708) = some ⟨13, 2, 0, 444601, 280708, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_280708_444601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280708 ⟨444601, by decide⟩ :=
  accepted_of_selected 13 280708 ⟨444601, by decide⟩ ⟨13, 2, 0, 444601, 280708, 1005, 16384⟩
    (by decide) selected_cut_17470

theorem selected_cut_17471 : selected 8 ⟨444616, by decide⟩
    (prefixPartial 13 280709) = some ⟨13, 2, 0, 444616, 280709, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_280709_444616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280709 ⟨444616, by decide⟩ :=
  accepted_of_selected 13 280709 ⟨444616, by decide⟩ ⟨13, 2, 0, 444616, 280709, 1161, 16384⟩
    (by decide) selected_cut_17471

theorem selected_cut_17472 : selected 8 ⟨444635, by decide⟩
    (prefixPartial 13 280710) = some ⟨13, 2, 0, 444635, 280710, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_280710_444635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280710 ⟨444635, by decide⟩ :=
  accepted_of_selected 13 280710 ⟨444635, by decide⟩ ⟨13, 2, 0, 444635, 280710, 1529, 16384⟩
    (by decide) selected_cut_17472

theorem selected_cut_17473 : selected 8 ⟨444643, by decide⟩
    (prefixPartial 13 280711) = some ⟨13, 2, 0, 444643, 280711, 809, 16384⟩ := by
  decide +kernel

theorem context_13_280711_444643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280711 ⟨444643, by decide⟩ :=
  accepted_of_selected 13 280711 ⟨444643, by decide⟩ ⟨13, 2, 0, 444643, 280711, 809, 16384⟩
    (by decide) selected_cut_17473

theorem unmarked_context_12_70177_444644 : frontier 9 ⟨444644, by decide⟩
    (prefixCache 12 70177) (prefixPartial 12 70177) = false := by
  decide +kernel

theorem node_context_12_70177_444644 : EJMOriginalGlobalDAGData.nodes 9 ⟨444644, by decide⟩ =
    .split (coordinate 12) (![⟨444601, by decide⟩,⟨444616, by decide⟩,⟨444635, by decide⟩,⟨444643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70177_444644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70177 ⟨444644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70177
    ⟨444644, by decide⟩ (by decide) (![⟨444601, by decide⟩,⟨444616, by decide⟩,⟨444635, by decide⟩,⟨444643, by decide⟩]) unmarked_context_12_70177_444644 node_context_12_70177_444644
  intro a
  fin_cases a
  · exact context_13_280708_444601
  · exact context_13_280709_444616
  · exact context_13_280710_444635
  · exact context_13_280711_444643

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
