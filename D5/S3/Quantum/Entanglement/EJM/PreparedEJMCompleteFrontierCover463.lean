/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover462
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_22134_1223080 : frontier 11 ⟨1223080, by decide⟩
    (prefixCache 10 22134) (prefixPartial 10 22134) = false := by
  decide +kernel

theorem node_context_10_22134_1223080 : EJMOriginalGlobalDAGData.nodes 11 ⟨1223080, by decide⟩ =
    .split (coordinate 10) (![⟨1222952, by decide⟩,⟨1222999, by decide⟩,⟨1223038, by decide⟩,⟨1223079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22134_1223080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22134 ⟨1223080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22134
    ⟨1223080, by decide⟩ (by decide) (![⟨1222952, by decide⟩,⟨1222999, by decide⟩,⟨1223038, by decide⟩,⟨1223079, by decide⟩]) unmarked_context_10_22134_1223080 node_context_10_22134_1223080
  intro a
  fin_cases a
  · exact context_11_88536_1222952
  · exact context_11_88537_1222999
  · exact context_11_88538_1223038
  · exact context_11_88539_1223079

theorem selected_cut_44452 : selected 9 ⟨1223107, by decide⟩
    (prefixPartial 12 354160) = some ⟨12, 2, 0, 1223107, 354160, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_354160_1223107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354160 ⟨1223107, by decide⟩ :=
  accepted_of_selected 12 354160 ⟨1223107, by decide⟩ ⟨12, 2, 0, 1223107, 354160, 1529, 65536⟩
    (by decide) selected_cut_44452

theorem selected_cut_44453 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354161) = some ⟨12, 1, 0, 896706, 354161, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354161_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354161 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354161 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354161, 1, 65536⟩
    (by decide) selected_cut_44453

theorem selected_cut_44454 : selected 9 ⟨1223128, by decide⟩
    (prefixPartial 12 354162) = some ⟨12, 2, 0, 1223128, 354162, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_354162_1223128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354162 ⟨1223128, by decide⟩ :=
  accepted_of_selected 12 354162 ⟨1223128, by decide⟩ ⟨12, 2, 0, 1223128, 354162, 1565, 65536⟩
    (by decide) selected_cut_44454

theorem selected_cut_44455 : selected 9 ⟨1223152, by decide⟩
    (prefixPartial 12 354163) = some ⟨12, 2, 0, 1223152, 354163, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_354163_1223152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354163 ⟨1223152, by decide⟩ :=
  accepted_of_selected 12 354163 ⟨1223152, by decide⟩ ⟨12, 2, 0, 1223152, 354163, 1369, 65536⟩
    (by decide) selected_cut_44455

theorem unmarked_context_11_88540_1223153 : frontier 10 ⟨1223153, by decide⟩
    (prefixCache 11 88540) (prefixPartial 11 88540) = false := by
  decide +kernel

theorem node_context_11_88540_1223153 : EJMOriginalGlobalDAGData.nodes 10 ⟨1223153, by decide⟩ =
    .split (coordinate 11) (![⟨1223107, by decide⟩,⟨896706, by decide⟩,⟨1223128, by decide⟩,⟨1223152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88540_1223153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88540 ⟨1223153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88540
    ⟨1223153, by decide⟩ (by decide) (![⟨1223107, by decide⟩,⟨896706, by decide⟩,⟨1223128, by decide⟩,⟨1223152, by decide⟩]) unmarked_context_11_88540_1223153 node_context_11_88540_1223153
  intro a
  fin_cases a
  · exact context_12_354160_1223107
  · exact context_12_354161_896706
  · exact context_12_354162_1223128
  · exact context_12_354163_1223152

theorem selected_cut_44456 : selected 10 ⟨1223201, by decide⟩
    (prefixPartial 11 88541) = some ⟨11, 2, 0, 1223201, 88541, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_88541_1223201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88541 ⟨1223201, by decide⟩ :=
  accepted_of_selected 11 88541 ⟨1223201, by decide⟩ ⟨11, 2, 0, 1223201, 88541, 2961, 262144⟩
    (by decide) selected_cut_44456

theorem selected_cut_44457 : selected 10 ⟨1223266, by decide⟩
    (prefixPartial 11 88542) = some ⟨11, 2, 0, 1223266, 88542, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_88542_1223266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88542 ⟨1223266, by decide⟩ :=
  accepted_of_selected 11 88542 ⟨1223266, by decide⟩ ⟨11, 2, 0, 1223266, 88542, 3785, 262144⟩
    (by decide) selected_cut_44457

theorem selected_cut_44458 : selected 10 ⟨1223268, by decide⟩
    (prefixPartial 11 88543) = some ⟨11, 2, 0, 1223268, 88543, 5, 262144⟩ := by
  decide +kernel

theorem context_11_88543_1223268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88543 ⟨1223268, by decide⟩ :=
  accepted_of_selected 11 88543 ⟨1223268, by decide⟩ ⟨11, 2, 0, 1223268, 88543, 5, 262144⟩
    (by decide) selected_cut_44458

theorem unmarked_context_10_22135_1223269 : frontier 11 ⟨1223269, by decide⟩
    (prefixCache 10 22135) (prefixPartial 10 22135) = false := by
  decide +kernel

theorem node_context_10_22135_1223269 : EJMOriginalGlobalDAGData.nodes 11 ⟨1223269, by decide⟩ =
    .split (coordinate 10) (![⟨1223153, by decide⟩,⟨1223201, by decide⟩,⟨1223266, by decide⟩,⟨1223268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22135_1223269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22135 ⟨1223269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22135
    ⟨1223269, by decide⟩ (by decide) (![⟨1223153, by decide⟩,⟨1223201, by decide⟩,⟨1223266, by decide⟩,⟨1223268, by decide⟩]) unmarked_context_10_22135_1223269 node_context_10_22135_1223269
  intro a
  fin_cases a
  · exact context_11_88540_1223153
  · exact context_11_88541_1223201
  · exact context_11_88542_1223266
  · exact context_11_88543_1223268

theorem unmarked_context_9_5533_1223270 : frontier 12 ⟨1223270, by decide⟩
    (prefixCache 9 5533) (prefixPartial 9 5533) = false := by
  decide +kernel

theorem node_context_9_5533_1223270 : EJMOriginalGlobalDAGData.nodes 12 ⟨1223270, by decide⟩ =
    .split (coordinate 9) (![⟨1222884, by decide⟩,⟨893098, by decide⟩,⟨1223080, by decide⟩,⟨1223269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5533_1223270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5533 ⟨1223270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5533
    ⟨1223270, by decide⟩ (by decide) (![⟨1222884, by decide⟩,⟨893098, by decide⟩,⟨1223080, by decide⟩,⟨1223269, by decide⟩]) unmarked_context_9_5533_1223270 node_context_9_5533_1223270
  intro a
  fin_cases a
  · exact context_10_22132_1222884
  · exact context_10_22133_893098
  · exact context_10_22134_1223080
  · exact context_10_22135_1223269

theorem selected_cut_44459 : selected 10 ⟨1223316, by decide⟩
    (prefixPartial 11 88544) = some ⟨11, 2, 0, 1223316, 88544, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_88544_1223316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88544 ⟨1223316, by decide⟩ :=
  accepted_of_selected 11 88544 ⟨1223316, by decide⟩ ⟨11, 2, 0, 1223316, 88544, 2909, 262144⟩
    (by decide) selected_cut_44459

theorem selected_cut_44460 : selected 10 ⟨1223374, by decide⟩
    (prefixPartial 11 88545) = some ⟨11, 2, 0, 1223374, 88545, 3761, 262144⟩ := by
  decide +kernel

theorem context_11_88545_1223374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88545 ⟨1223374, by decide⟩ :=
  accepted_of_selected 11 88545 ⟨1223374, by decide⟩ ⟨11, 2, 0, 1223374, 88545, 3761, 262144⟩
    (by decide) selected_cut_44460

theorem selected_cut_44461 : selected 10 ⟨1223436, by decide⟩
    (prefixPartial 11 88546) = some ⟨11, 2, 0, 1223436, 88546, 3217, 262144⟩ := by
  decide +kernel

theorem context_11_88546_1223436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88546 ⟨1223436, by decide⟩ :=
  accepted_of_selected 11 88546 ⟨1223436, by decide⟩ ⟨11, 2, 0, 1223436, 88546, 3217, 262144⟩
    (by decide) selected_cut_44461

theorem selected_cut_44462 : selected 10 ⟨1223465, by decide⟩
    (prefixPartial 11 88547) = some ⟨11, 2, 0, 1223465, 88547, 2349, 262144⟩ := by
  decide +kernel

theorem context_11_88547_1223465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88547 ⟨1223465, by decide⟩ :=
  accepted_of_selected 11 88547 ⟨1223465, by decide⟩ ⟨11, 2, 0, 1223465, 88547, 2349, 262144⟩
    (by decide) selected_cut_44462

theorem unmarked_context_10_22136_1223466 : frontier 11 ⟨1223466, by decide⟩
    (prefixCache 10 22136) (prefixPartial 10 22136) = false := by
  decide +kernel

theorem node_context_10_22136_1223466 : EJMOriginalGlobalDAGData.nodes 11 ⟨1223466, by decide⟩ =
    .split (coordinate 10) (![⟨1223316, by decide⟩,⟨1223374, by decide⟩,⟨1223436, by decide⟩,⟨1223465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22136_1223466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22136 ⟨1223466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22136
    ⟨1223466, by decide⟩ (by decide) (![⟨1223316, by decide⟩,⟨1223374, by decide⟩,⟨1223436, by decide⟩,⟨1223465, by decide⟩]) unmarked_context_10_22136_1223466 node_context_10_22136_1223466
  intro a
  fin_cases a
  · exact context_11_88544_1223316
  · exact context_11_88545_1223374
  · exact context_11_88546_1223436
  · exact context_11_88547_1223465

theorem selected_cut_44463 : selected 10 ⟨1223514, by decide⟩
    (prefixPartial 11 88548) = some ⟨11, 2, 0, 1223514, 88548, 3285, 262144⟩ := by
  decide +kernel

theorem context_11_88548_1223514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88548 ⟨1223514, by decide⟩ :=
  accepted_of_selected 11 88548 ⟨1223514, by decide⟩ ⟨11, 2, 0, 1223514, 88548, 3285, 262144⟩
    (by decide) selected_cut_44463

theorem selected_cut_44464 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88549) = some ⟨11, 1, 0, 892405, 88549, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88549_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88549 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88549 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88549, 1, 262144⟩
    (by decide) selected_cut_44464

theorem selected_cut_44465 : selected 10 ⟨1223553, by decide⟩
    (prefixPartial 11 88550) = some ⟨11, 2, 0, 1223553, 88550, 2481, 262144⟩ := by
  decide +kernel

theorem context_11_88550_1223553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88550 ⟨1223553, by decide⟩ :=
  accepted_of_selected 11 88550 ⟨1223553, by decide⟩ ⟨11, 2, 0, 1223553, 88550, 2481, 262144⟩
    (by decide) selected_cut_44465

theorem selected_cut_44466 : selected 10 ⟨1223584, by decide⟩
    (prefixPartial 11 88551) = some ⟨11, 2, 0, 1223584, 88551, 1969, 262144⟩ := by
  decide +kernel

theorem context_11_88551_1223584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88551 ⟨1223584, by decide⟩ :=
  accepted_of_selected 11 88551 ⟨1223584, by decide⟩ ⟨11, 2, 0, 1223584, 88551, 1969, 262144⟩
    (by decide) selected_cut_44466

theorem unmarked_context_10_22137_1223585 : frontier 11 ⟨1223585, by decide⟩
    (prefixCache 10 22137) (prefixPartial 10 22137) = false := by
  decide +kernel

theorem node_context_10_22137_1223585 : EJMOriginalGlobalDAGData.nodes 11 ⟨1223585, by decide⟩ =
    .split (coordinate 10) (![⟨1223514, by decide⟩,⟨892405, by decide⟩,⟨1223553, by decide⟩,⟨1223584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22137_1223585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22137 ⟨1223585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22137
    ⟨1223585, by decide⟩ (by decide) (![⟨1223514, by decide⟩,⟨892405, by decide⟩,⟨1223553, by decide⟩,⟨1223584, by decide⟩]) unmarked_context_10_22137_1223585 node_context_10_22137_1223585
  intro a
  fin_cases a
  · exact context_11_88548_1223514
  · exact context_11_88549_892405
  · exact context_11_88550_1223553
  · exact context_11_88551_1223584

theorem selected_cut_44467 : selected 11 ⟨1223624, by decide⟩
    (prefixPartial 10 22138) = some ⟨10, 2, 0, 1223624, 22138, 2209, 1048576⟩ := by
  decide +kernel

theorem context_10_22138_1223624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22138 ⟨1223624, by decide⟩ :=
  accepted_of_selected 10 22138 ⟨1223624, by decide⟩ ⟨10, 2, 0, 1223624, 22138, 2209, 1048576⟩
    (by decide) selected_cut_44467

theorem selected_cut_44468 : selected 10 ⟨1223668, by decide⟩
    (prefixPartial 11 88556) = some ⟨11, 2, 0, 1223668, 88556, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_88556_1223668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88556 ⟨1223668, by decide⟩ :=
  accepted_of_selected 11 88556 ⟨1223668, by decide⟩ ⟨11, 2, 0, 1223668, 88556, 2853, 262144⟩
    (by decide) selected_cut_44468

theorem selected_cut_44469 : selected 10 ⟨1223692, by decide⟩
    (prefixPartial 11 88557) = some ⟨11, 2, 0, 1223692, 88557, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_88557_1223692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88557 ⟨1223692, by decide⟩ :=
  accepted_of_selected 11 88557 ⟨1223692, by decide⟩ ⟨11, 2, 0, 1223692, 88557, 1641, 262144⟩
    (by decide) selected_cut_44469

theorem selected_cut_44470 : selected 10 ⟨1223721, by decide⟩
    (prefixPartial 11 88558) = some ⟨11, 2, 0, 1223721, 88558, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_88558_1223721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88558 ⟨1223721, by decide⟩ :=
  accepted_of_selected 11 88558 ⟨1223721, by decide⟩ ⟨11, 2, 0, 1223721, 88558, 1757, 262144⟩
    (by decide) selected_cut_44470

theorem selected_cut_44471 : selected 10 ⟨1223740, by decide⟩
    (prefixPartial 11 88559) = some ⟨11, 2, 0, 1223740, 88559, 1053, 262144⟩ := by
  decide +kernel

theorem context_11_88559_1223740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88559 ⟨1223740, by decide⟩ :=
  accepted_of_selected 11 88559 ⟨1223740, by decide⟩ ⟨11, 2, 0, 1223740, 88559, 1053, 262144⟩
    (by decide) selected_cut_44471

theorem unmarked_context_10_22139_1223741 : frontier 11 ⟨1223741, by decide⟩
    (prefixCache 10 22139) (prefixPartial 10 22139) = false := by
  decide +kernel

theorem node_context_10_22139_1223741 : EJMOriginalGlobalDAGData.nodes 11 ⟨1223741, by decide⟩ =
    .split (coordinate 10) (![⟨1223668, by decide⟩,⟨1223692, by decide⟩,⟨1223721, by decide⟩,⟨1223740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22139_1223741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22139 ⟨1223741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22139
    ⟨1223741, by decide⟩ (by decide) (![⟨1223668, by decide⟩,⟨1223692, by decide⟩,⟨1223721, by decide⟩,⟨1223740, by decide⟩]) unmarked_context_10_22139_1223741 node_context_10_22139_1223741
  intro a
  fin_cases a
  · exact context_11_88556_1223668
  · exact context_11_88557_1223692
  · exact context_11_88558_1223721
  · exact context_11_88559_1223740

theorem unmarked_context_9_5534_1223742 : frontier 12 ⟨1223742, by decide⟩
    (prefixCache 9 5534) (prefixPartial 9 5534) = false := by
  decide +kernel

theorem node_context_9_5534_1223742 : EJMOriginalGlobalDAGData.nodes 12 ⟨1223742, by decide⟩ =
    .split (coordinate 9) (![⟨1223466, by decide⟩,⟨1223585, by decide⟩,⟨1223624, by decide⟩,⟨1223741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5534_1223742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5534 ⟨1223742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5534
    ⟨1223742, by decide⟩ (by decide) (![⟨1223466, by decide⟩,⟨1223585, by decide⟩,⟨1223624, by decide⟩,⟨1223741, by decide⟩]) unmarked_context_9_5534_1223742 node_context_9_5534_1223742
  intro a
  fin_cases a
  · exact context_10_22136_1223466
  · exact context_10_22137_1223585
  · exact context_10_22138_1223624
  · exact context_10_22139_1223741

theorem selected_cut_44472 : selected 11 ⟨1223800, by decide⟩
    (prefixPartial 10 22140) = some ⟨10, 2, 0, 1223800, 22140, 3857, 1048576⟩ := by
  decide +kernel

theorem context_10_22140_1223800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22140 ⟨1223800, by decide⟩ :=
  accepted_of_selected 10 22140 ⟨1223800, by decide⟩ ⟨10, 2, 0, 1223800, 22140, 3857, 1048576⟩
    (by decide) selected_cut_44472

theorem selected_cut_44473 : selected 11 ⟨1223840, by decide⟩
    (prefixPartial 10 22141) = some ⟨10, 2, 0, 1223840, 22141, 2125, 1048576⟩ := by
  decide +kernel

theorem context_10_22141_1223840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22141 ⟨1223840, by decide⟩ :=
  accepted_of_selected 10 22141 ⟨1223840, by decide⟩ ⟨10, 2, 0, 1223840, 22141, 2125, 1048576⟩
    (by decide) selected_cut_44473

theorem selected_cut_44474 : selected 11 ⟨1223878, by decide⟩
    (prefixPartial 10 22142) = some ⟨10, 2, 0, 1223878, 22142, 1677, 1048576⟩ := by
  decide +kernel

theorem context_10_22142_1223878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22142 ⟨1223878, by decide⟩ :=
  accepted_of_selected 10 22142 ⟨1223878, by decide⟩ ⟨10, 2, 0, 1223878, 22142, 1677, 1048576⟩
    (by decide) selected_cut_44474

theorem selected_cut_44475 : selected 11 ⟨1223890, by decide⟩
    (prefixPartial 10 22143) = some ⟨10, 2, 0, 1223890, 22143, 217, 1048576⟩ := by
  decide +kernel

theorem context_10_22143_1223890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22143 ⟨1223890, by decide⟩ :=
  accepted_of_selected 10 22143 ⟨1223890, by decide⟩ ⟨10, 2, 0, 1223890, 22143, 217, 1048576⟩
    (by decide) selected_cut_44475

theorem unmarked_context_9_5535_1223891 : frontier 12 ⟨1223891, by decide⟩
    (prefixCache 9 5535) (prefixPartial 9 5535) = false := by
  decide +kernel

theorem node_context_9_5535_1223891 : EJMOriginalGlobalDAGData.nodes 12 ⟨1223891, by decide⟩ =
    .split (coordinate 9) (![⟨1223800, by decide⟩,⟨1223840, by decide⟩,⟨1223878, by decide⟩,⟨1223890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5535_1223891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5535 ⟨1223891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5535
    ⟨1223891, by decide⟩ (by decide) (![⟨1223800, by decide⟩,⟨1223840, by decide⟩,⟨1223878, by decide⟩,⟨1223890, by decide⟩]) unmarked_context_9_5535_1223891 node_context_9_5535_1223891
  intro a
  fin_cases a
  · exact context_10_22140_1223800
  · exact context_10_22141_1223840
  · exact context_10_22142_1223878
  · exact context_10_22143_1223890

theorem unmarked_context_8_1383_1223892 : frontier 13 ⟨1223892, by decide⟩
    (prefixCache 8 1383) (prefixPartial 8 1383) = false := by
  decide +kernel

theorem node_context_8_1383_1223892 : EJMOriginalGlobalDAGData.nodes 13 ⟨1223892, by decide⟩ =
    .split (coordinate 8) (![⟨1222571, by decide⟩,⟨1223270, by decide⟩,⟨1223742, by decide⟩,⟨1223891, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1383_1223892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1383 ⟨1223892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1383
    ⟨1223892, by decide⟩ (by decide) (![⟨1222571, by decide⟩,⟨1223270, by decide⟩,⟨1223742, by decide⟩,⟨1223891, by decide⟩]) unmarked_context_8_1383_1223892 node_context_8_1383_1223892
  intro a
  fin_cases a
  · exact context_9_5532_1222571
  · exact context_9_5533_1223270
  · exact context_9_5534_1223742
  · exact context_9_5535_1223891

theorem unmarked_context_7_345_1223893 : frontier 14 ⟨1223893, by decide⟩
    (prefixCache 7 345) (prefixPartial 7 345) = false := by
  decide +kernel

theorem node_context_7_345_1223893 : EJMOriginalGlobalDAGData.nodes 14 ⟨1223893, by decide⟩ =
    .split (coordinate 7) (![⟨1213833, by decide⟩,⟨1217840, by decide⟩,⟨1220784, by decide⟩,⟨1223892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_345_1223893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 345 ⟨1223893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 345
    ⟨1223893, by decide⟩ (by decide) (![⟨1213833, by decide⟩,⟨1217840, by decide⟩,⟨1220784, by decide⟩,⟨1223892, by decide⟩]) unmarked_context_7_345_1223893 node_context_7_345_1223893
  intro a
  fin_cases a
  · exact context_8_1380_1213833
  · exact context_8_1381_1217840
  · exact context_8_1382_1220784
  · exact context_8_1383_1223892

theorem selected_cut_44476 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88576) = some ⟨11, 1, 0, 434745, 88576, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88576_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88576 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88576 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88576, 1, 262144⟩
    (by decide) selected_cut_44476

theorem selected_cut_44477 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354308) = some ⟨12, 1, 0, 448748, 354308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354308_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354308 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354308 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354308, 1, 65536⟩
    (by decide) selected_cut_44477

theorem selected_cut_44478 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 354309) = some ⟨12, 1, 0, 34034, 354309, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354309_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354309 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 354309 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 354309, 1, 65536⟩
    (by decide) selected_cut_44478

theorem selected_cut_44479 : selected 9 ⟨1223957, by decide⟩
    (prefixPartial 12 354310) = some ⟨12, 2, 0, 1223957, 354310, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_354310_1223957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354310 ⟨1223957, by decide⟩ :=
  accepted_of_selected 12 354310 ⟨1223957, by decide⟩ ⟨12, 2, 0, 1223957, 354310, 3065, 65536⟩
    (by decide) selected_cut_44479

theorem selected_cut_44480 : selected 9 ⟨1224022, by decide⟩
    (prefixPartial 12 354311) = some ⟨12, 2, 0, 1224022, 354311, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_354311_1224022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354311 ⟨1224022, by decide⟩ :=
  accepted_of_selected 12 354311 ⟨1224022, by decide⟩ ⟨12, 2, 0, 1224022, 354311, 3321, 65536⟩
    (by decide) selected_cut_44480

theorem unmarked_context_11_88577_1224023 : frontier 10 ⟨1224023, by decide⟩
    (prefixCache 11 88577) (prefixPartial 11 88577) = false := by
  decide +kernel

theorem node_context_11_88577_1224023 : EJMOriginalGlobalDAGData.nodes 10 ⟨1224023, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1223957, by decide⟩,⟨1224022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88577_1224023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88577 ⟨1224023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88577
    ⟨1224023, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1223957, by decide⟩,⟨1224022, by decide⟩]) unmarked_context_11_88577_1224023 node_context_11_88577_1224023
  intro a
  fin_cases a
  · exact context_12_354308_448748
  · exact context_12_354309_34034
  · exact context_12_354310_1223957
  · exact context_12_354311_1224022

theorem selected_cut_44481 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354312) = some ⟨12, 1, 0, 448748, 354312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354312_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354312 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354312 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354312, 1, 65536⟩
    (by decide) selected_cut_44481

theorem selected_cut_44482 : selected 9 ⟨1224084, by decide⟩
    (prefixPartial 12 354313) = some ⟨12, 2, 0, 1224084, 354313, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_354313_1224084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354313 ⟨1224084, by decide⟩ :=
  accepted_of_selected 12 354313 ⟨1224084, by decide⟩ ⟨12, 2, 0, 1224084, 354313, 3097, 65536⟩
    (by decide) selected_cut_44482

theorem selected_cut_44483 : selected 9 ⟨663554, by decide⟩
    (prefixPartial 12 354314) = some ⟨12, 1, 0, 663554, 354314, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354314_663554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354314 ⟨663554, by decide⟩ :=
  accepted_of_selected 12 354314 ⟨663554, by decide⟩ ⟨12, 1, 0, 663554, 354314, 1, 65536⟩
    (by decide) selected_cut_44483

theorem selected_cut_44484 : selected 9 ⟨1224160, by decide⟩
    (prefixPartial 12 354315) = some ⟨12, 2, 0, 1224160, 354315, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_354315_1224160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354315 ⟨1224160, by decide⟩ :=
  accepted_of_selected 12 354315 ⟨1224160, by decide⟩ ⟨12, 2, 0, 1224160, 354315, 3501, 65536⟩
    (by decide) selected_cut_44484

theorem unmarked_context_11_88578_1224161 : frontier 10 ⟨1224161, by decide⟩
    (prefixCache 11 88578) (prefixPartial 11 88578) = false := by
  decide +kernel

theorem node_context_11_88578_1224161 : EJMOriginalGlobalDAGData.nodes 10 ⟨1224161, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1224084, by decide⟩,⟨663554, by decide⟩,⟨1224160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88578_1224161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88578 ⟨1224161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88578
    ⟨1224161, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1224084, by decide⟩,⟨663554, by decide⟩,⟨1224160, by decide⟩]) unmarked_context_11_88578_1224161 node_context_11_88578_1224161
  intro a
  fin_cases a
  · exact context_12_354312_448748
  · exact context_12_354313_1224084
  · exact context_12_354314_663554
  · exact context_12_354315_1224160

theorem selected_cut_44485 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354316) = some ⟨12, 1, 0, 448748, 354316, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354316_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354316 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354316 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354316, 1, 65536⟩
    (by decide) selected_cut_44485

theorem selected_cut_44486 : selected 9 ⟨1224218, by decide⟩
    (prefixPartial 12 354317) = some ⟨12, 2, 0, 1224218, 354317, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_354317_1224218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354317 ⟨1224218, by decide⟩ :=
  accepted_of_selected 12 354317 ⟨1224218, by decide⟩ ⟨12, 2, 0, 1224218, 354317, 3077, 65536⟩
    (by decide) selected_cut_44486

theorem selected_cut_44487 : selected 9 ⟨1224280, by decide⟩
    (prefixPartial 12 354318) = some ⟨12, 2, 0, 1224280, 354318, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_354318_1224280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354318 ⟨1224280, by decide⟩ :=
  accepted_of_selected 12 354318 ⟨1224280, by decide⟩ ⟨12, 2, 0, 1224280, 354318, 3205, 65536⟩
    (by decide) selected_cut_44487

theorem selected_cut_44488 : selected 9 ⟨1224335, by decide⟩
    (prefixPartial 12 354319) = some ⟨12, 2, 0, 1224335, 354319, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_354319_1224335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354319 ⟨1224335, by decide⟩ :=
  accepted_of_selected 12 354319 ⟨1224335, by decide⟩ ⟨12, 2, 0, 1224335, 354319, 3189, 65536⟩
    (by decide) selected_cut_44488

theorem unmarked_context_11_88579_1224336 : frontier 10 ⟨1224336, by decide⟩
    (prefixCache 11 88579) (prefixPartial 11 88579) = false := by
  decide +kernel

theorem node_context_11_88579_1224336 : EJMOriginalGlobalDAGData.nodes 10 ⟨1224336, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1224218, by decide⟩,⟨1224280, by decide⟩,⟨1224335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88579_1224336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88579 ⟨1224336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88579
    ⟨1224336, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1224218, by decide⟩,⟨1224280, by decide⟩,⟨1224335, by decide⟩]) unmarked_context_11_88579_1224336 node_context_11_88579_1224336
  intro a
  fin_cases a
  · exact context_12_354316_448748
  · exact context_12_354317_1224218
  · exact context_12_354318_1224280
  · exact context_12_354319_1224335

theorem unmarked_context_10_22144_1224337 : frontier 11 ⟨1224337, by decide⟩
    (prefixCache 10 22144) (prefixPartial 10 22144) = false := by
  decide +kernel

theorem node_context_10_22144_1224337 : EJMOriginalGlobalDAGData.nodes 11 ⟨1224337, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1224023, by decide⟩,⟨1224161, by decide⟩,⟨1224336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22144_1224337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22144 ⟨1224337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22144
    ⟨1224337, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1224023, by decide⟩,⟨1224161, by decide⟩,⟨1224336, by decide⟩]) unmarked_context_10_22144_1224337 node_context_10_22144_1224337
  intro a
  fin_cases a
  · exact context_11_88576_434745
  · exact context_11_88577_1224023
  · exact context_11_88578_1224161
  · exact context_11_88579_1224336

theorem selected_cut_44489 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 354320) = some ⟨12, 1, 0, 435160, 354320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354320_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354320 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 354320 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 354320, 1, 65536⟩
    (by decide) selected_cut_44489

theorem selected_cut_44490 : selected 9 ⟨1224388, by decide⟩
    (prefixPartial 12 354321) = some ⟨12, 2, 0, 1224388, 354321, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_354321_1224388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354321 ⟨1224388, by decide⟩ :=
  accepted_of_selected 12 354321 ⟨1224388, by decide⟩ ⟨12, 2, 0, 1224388, 354321, 2685, 65536⟩
    (by decide) selected_cut_44490

theorem selected_cut_44491 : selected 9 ⟨1224435, by decide⟩
    (prefixPartial 12 354322) = some ⟨12, 2, 0, 1224435, 354322, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_354322_1224435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354322 ⟨1224435, by decide⟩ :=
  accepted_of_selected 12 354322 ⟨1224435, by decide⟩ ⟨12, 2, 0, 1224435, 354322, 2757, 65536⟩
    (by decide) selected_cut_44491

theorem selected_cut_44492 : selected 9 ⟨1224491, by decide⟩
    (prefixPartial 12 354323) = some ⟨12, 2, 0, 1224491, 354323, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_354323_1224491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354323 ⟨1224491, by decide⟩ :=
  accepted_of_selected 12 354323 ⟨1224491, by decide⟩ ⟨12, 2, 0, 1224491, 354323, 2941, 65536⟩
    (by decide) selected_cut_44492

theorem unmarked_context_11_88580_1224492 : frontier 10 ⟨1224492, by decide⟩
    (prefixCache 11 88580) (prefixPartial 11 88580) = false := by
  decide +kernel

theorem node_context_11_88580_1224492 : EJMOriginalGlobalDAGData.nodes 10 ⟨1224492, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1224388, by decide⟩,⟨1224435, by decide⟩,⟨1224491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88580_1224492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88580 ⟨1224492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88580
    ⟨1224492, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1224388, by decide⟩,⟨1224435, by decide⟩,⟨1224491, by decide⟩]) unmarked_context_11_88580_1224492 node_context_11_88580_1224492
  intro a
  fin_cases a
  · exact context_12_354320_435160
  · exact context_12_354321_1224388
  · exact context_12_354322_1224435
  · exact context_12_354323_1224491

theorem selected_cut_44493 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 354324) = some ⟨12, 1, 0, 435160, 354324, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354324_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354324 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 354324 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 354324, 1, 65536⟩
    (by decide) selected_cut_44493

theorem selected_cut_44494 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 354325) = some ⟨12, 1, 0, 1118965, 354325, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354325_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354325 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 354325 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 354325, 1, 65536⟩
    (by decide) selected_cut_44494

theorem selected_cut_44495 : selected 9 ⟨1224538, by decide⟩
    (prefixPartial 12 354326) = some ⟨12, 2, 0, 1224538, 354326, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_354326_1224538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354326 ⟨1224538, by decide⟩ :=
  accepted_of_selected 12 354326 ⟨1224538, by decide⟩ ⟨12, 2, 0, 1224538, 354326, 2709, 65536⟩
    (by decide) selected_cut_44495

theorem selected_cut_44496 : selected 9 ⟨1224593, by decide⟩
    (prefixPartial 12 354327) = some ⟨12, 2, 0, 1224593, 354327, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_354327_1224593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354327 ⟨1224593, by decide⟩ :=
  accepted_of_selected 12 354327 ⟨1224593, by decide⟩ ⟨12, 2, 0, 1224593, 354327, 2973, 65536⟩
    (by decide) selected_cut_44496

theorem unmarked_context_11_88581_1224594 : frontier 10 ⟨1224594, by decide⟩
    (prefixCache 11 88581) (prefixPartial 11 88581) = false := by
  decide +kernel

theorem node_context_11_88581_1224594 : EJMOriginalGlobalDAGData.nodes 10 ⟨1224594, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1118965, by decide⟩,⟨1224538, by decide⟩,⟨1224593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88581_1224594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88581 ⟨1224594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88581
    ⟨1224594, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1118965, by decide⟩,⟨1224538, by decide⟩,⟨1224593, by decide⟩]) unmarked_context_11_88581_1224594 node_context_11_88581_1224594
  intro a
  fin_cases a
  · exact context_12_354324_435160
  · exact context_12_354325_1118965
  · exact context_12_354326_1224538
  · exact context_12_354327_1224593

theorem selected_cut_44497 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 354328) = some ⟨12, 1, 0, 449505, 354328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354328_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354328 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 354328 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 354328, 1, 65536⟩
    (by decide) selected_cut_44497

theorem selected_cut_44498 : selected 9 ⟨1224643, by decide⟩
    (prefixPartial 12 354329) = some ⟨12, 2, 0, 1224643, 354329, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_354329_1224643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354329 ⟨1224643, by decide⟩ :=
  accepted_of_selected 12 354329 ⟨1224643, by decide⟩ ⟨12, 2, 0, 1224643, 354329, 2757, 65536⟩
    (by decide) selected_cut_44498

theorem selected_cut_44499 : selected 9 ⟨1224698, by decide⟩
    (prefixPartial 12 354330) = some ⟨12, 2, 0, 1224698, 354330, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_354330_1224698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354330 ⟨1224698, by decide⟩ :=
  accepted_of_selected 12 354330 ⟨1224698, by decide⟩ ⟨12, 2, 0, 1224698, 354330, 2777, 65536⟩
    (by decide) selected_cut_44499

theorem selected_cut_44500 : selected 9 ⟨1224772, by decide⟩
    (prefixPartial 12 354331) = some ⟨12, 2, 0, 1224772, 354331, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_354331_1224772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354331 ⟨1224772, by decide⟩ :=
  accepted_of_selected 12 354331 ⟨1224772, by decide⟩ ⟨12, 2, 0, 1224772, 354331, 3389, 65536⟩
    (by decide) selected_cut_44500

theorem unmarked_context_11_88582_1224773 : frontier 10 ⟨1224773, by decide⟩
    (prefixCache 11 88582) (prefixPartial 11 88582) = false := by
  decide +kernel

theorem node_context_11_88582_1224773 : EJMOriginalGlobalDAGData.nodes 10 ⟨1224773, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨1224643, by decide⟩,⟨1224698, by decide⟩,⟨1224772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88582_1224773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88582 ⟨1224773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88582
    ⟨1224773, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨1224643, by decide⟩,⟨1224698, by decide⟩,⟨1224772, by decide⟩]) unmarked_context_11_88582_1224773 node_context_11_88582_1224773
  intro a
  fin_cases a
  · exact context_12_354328_449505
  · exact context_12_354329_1224643
  · exact context_12_354330_1224698
  · exact context_12_354331_1224772

theorem selected_cut_44501 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 354332) = some ⟨12, 1, 0, 539296, 354332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354332_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354332 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 354332 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 354332, 1, 65536⟩
    (by decide) selected_cut_44501

theorem selected_cut_44502 : selected 9 ⟨1224817, by decide⟩
    (prefixPartial 12 354333) = some ⟨12, 2, 0, 1224817, 354333, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_354333_1224817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354333 ⟨1224817, by decide⟩ :=
  accepted_of_selected 12 354333 ⟨1224817, by decide⟩ ⟨12, 2, 0, 1224817, 354333, 2697, 65536⟩
    (by decide) selected_cut_44502

theorem selected_cut_44503 : selected 9 ⟨1224873, by decide⟩
    (prefixPartial 12 354334) = some ⟨12, 2, 0, 1224873, 354334, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_354334_1224873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354334 ⟨1224873, by decide⟩ :=
  accepted_of_selected 12 354334 ⟨1224873, by decide⟩ ⟨12, 2, 0, 1224873, 354334, 2881, 65536⟩
    (by decide) selected_cut_44503

theorem selected_cut_44504 : selected 9 ⟨1224927, by decide⟩
    (prefixPartial 12 354335) = some ⟨12, 2, 0, 1224927, 354335, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_354335_1224927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354335 ⟨1224927, by decide⟩ :=
  accepted_of_selected 12 354335 ⟨1224927, by decide⟩ ⟨12, 2, 0, 1224927, 354335, 2949, 65536⟩
    (by decide) selected_cut_44504

theorem unmarked_context_11_88583_1224928 : frontier 10 ⟨1224928, by decide⟩
    (prefixCache 11 88583) (prefixPartial 11 88583) = false := by
  decide +kernel

theorem node_context_11_88583_1224928 : EJMOriginalGlobalDAGData.nodes 10 ⟨1224928, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨1224817, by decide⟩,⟨1224873, by decide⟩,⟨1224927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88583_1224928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88583 ⟨1224928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88583
    ⟨1224928, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨1224817, by decide⟩,⟨1224873, by decide⟩,⟨1224927, by decide⟩]) unmarked_context_11_88583_1224928 node_context_11_88583_1224928
  intro a
  fin_cases a
  · exact context_12_354332_539296
  · exact context_12_354333_1224817
  · exact context_12_354334_1224873
  · exact context_12_354335_1224927

theorem unmarked_context_10_22145_1224929 : frontier 11 ⟨1224929, by decide⟩
    (prefixCache 10 22145) (prefixPartial 10 22145) = false := by
  decide +kernel

theorem node_context_10_22145_1224929 : EJMOriginalGlobalDAGData.nodes 11 ⟨1224929, by decide⟩ =
    .split (coordinate 10) (![⟨1224492, by decide⟩,⟨1224594, by decide⟩,⟨1224773, by decide⟩,⟨1224928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22145_1224929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22145 ⟨1224929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22145
    ⟨1224929, by decide⟩ (by decide) (![⟨1224492, by decide⟩,⟨1224594, by decide⟩,⟨1224773, by decide⟩,⟨1224928, by decide⟩]) unmarked_context_10_22145_1224929 node_context_10_22145_1224929
  intro a
  fin_cases a
  · exact context_11_88580_1224492
  · exact context_11_88581_1224594
  · exact context_11_88582_1224773
  · exact context_11_88583_1224928

theorem selected_cut_44505 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 354336) = some ⟨12, 1, 0, 985390, 354336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354336_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354336 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 354336 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 354336, 1, 65536⟩
    (by decide) selected_cut_44505

theorem selected_cut_44506 : selected 9 ⟨1224970, by decide⟩
    (prefixPartial 12 354337) = some ⟨12, 2, 0, 1224970, 354337, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_354337_1224970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354337 ⟨1224970, by decide⟩ :=
  accepted_of_selected 12 354337 ⟨1224970, by decide⟩ ⟨12, 2, 0, 1224970, 354337, 2513, 65536⟩
    (by decide) selected_cut_44506

theorem selected_cut_44507 : selected 9 ⟨1225015, by decide⟩
    (prefixPartial 12 354338) = some ⟨12, 2, 0, 1225015, 354338, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_354338_1225015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354338 ⟨1225015, by decide⟩ :=
  accepted_of_selected 12 354338 ⟨1225015, by decide⟩ ⟨12, 2, 0, 1225015, 354338, 2525, 65536⟩
    (by decide) selected_cut_44507

theorem selected_cut_44508 : selected 9 ⟨1225068, by decide⟩
    (prefixPartial 12 354339) = some ⟨12, 2, 0, 1225068, 354339, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_354339_1225068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354339 ⟨1225068, by decide⟩ :=
  accepted_of_selected 12 354339 ⟨1225068, by decide⟩ ⟨12, 2, 0, 1225068, 354339, 2801, 65536⟩
    (by decide) selected_cut_44508

theorem unmarked_context_11_88584_1225069 : frontier 10 ⟨1225069, by decide⟩
    (prefixCache 11 88584) (prefixPartial 11 88584) = false := by
  decide +kernel

theorem node_context_11_88584_1225069 : EJMOriginalGlobalDAGData.nodes 10 ⟨1225069, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1224970, by decide⟩,⟨1225015, by decide⟩,⟨1225068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88584_1225069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88584 ⟨1225069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88584
    ⟨1225069, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1224970, by decide⟩,⟨1225015, by decide⟩,⟨1225068, by decide⟩]) unmarked_context_11_88584_1225069 node_context_11_88584_1225069
  intro a
  fin_cases a
  · exact context_12_354336_985390
  · exact context_12_354337_1224970
  · exact context_12_354338_1225015
  · exact context_12_354339_1225068

theorem selected_cut_44509 : selected 9 ⟨1197509, by decide⟩
    (prefixPartial 12 354340) = some ⟨12, 1, 0, 1197509, 354340, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354340_1197509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354340 ⟨1197509, by decide⟩ :=
  accepted_of_selected 12 354340 ⟨1197509, by decide⟩ ⟨12, 1, 0, 1197509, 354340, 1, 65536⟩
    (by decide) selected_cut_44509

theorem selected_cut_44510 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 354341) = some ⟨12, 1, 0, 719134, 354341, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354341_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354341 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 354341 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 354341, 1, 65536⟩
    (by decide) selected_cut_44510

theorem selected_cut_44511 : selected 9 ⟨1225113, by decide⟩
    (prefixPartial 12 354342) = some ⟨12, 2, 0, 1225113, 354342, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_354342_1225113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354342 ⟨1225113, by decide⟩ :=
  accepted_of_selected 12 354342 ⟨1225113, by decide⟩ ⟨12, 2, 0, 1225113, 354342, 2497, 65536⟩
    (by decide) selected_cut_44511

theorem selected_cut_44512 : selected 9 ⟨1225172, by decide⟩
    (prefixPartial 12 354343) = some ⟨12, 2, 0, 1225172, 354343, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_354343_1225172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354343 ⟨1225172, by decide⟩ :=
  accepted_of_selected 12 354343 ⟨1225172, by decide⟩ ⟨12, 2, 0, 1225172, 354343, 2937, 65536⟩
    (by decide) selected_cut_44512

theorem unmarked_context_11_88585_1225173 : frontier 10 ⟨1225173, by decide⟩
    (prefixCache 11 88585) (prefixPartial 11 88585) = false := by
  decide +kernel

theorem node_context_11_88585_1225173 : EJMOriginalGlobalDAGData.nodes 10 ⟨1225173, by decide⟩ =
    .split (coordinate 11) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1225113, by decide⟩,⟨1225172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88585_1225173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88585 ⟨1225173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88585
    ⟨1225173, by decide⟩ (by decide) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1225113, by decide⟩,⟨1225172, by decide⟩]) unmarked_context_11_88585_1225173 node_context_11_88585_1225173
  intro a
  fin_cases a
  · exact context_12_354340_1197509
  · exact context_12_354341_719134
  · exact context_12_354342_1225113
  · exact context_12_354343_1225172

theorem selected_cut_44513 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 88586) = some ⟨11, 1, 0, 900587, 88586, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88586_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88586 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 88586 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 88586, 1, 262144⟩
    (by decide) selected_cut_44513

theorem selected_cut_44514 : selected 9 ⟨1225220, by decide⟩
    (prefixPartial 12 354348) = some ⟨12, 2, 0, 1225220, 354348, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_354348_1225220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354348 ⟨1225220, by decide⟩ :=
  accepted_of_selected 12 354348 ⟨1225220, by decide⟩ ⟨12, 2, 0, 1225220, 354348, 2581, 65536⟩
    (by decide) selected_cut_44514

theorem selected_cut_44515 : selected 9 ⟨1225264, by decide⟩
    (prefixPartial 12 354349) = some ⟨12, 2, 0, 1225264, 354349, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_354349_1225264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354349 ⟨1225264, by decide⟩ :=
  accepted_of_selected 12 354349 ⟨1225264, by decide⟩ ⟨12, 2, 0, 1225264, 354349, 2545, 65536⟩
    (by decide) selected_cut_44515

theorem selected_cut_44516 : selected 9 ⟨1225318, by decide⟩
    (prefixPartial 12 354350) = some ⟨12, 2, 0, 1225318, 354350, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_354350_1225318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354350 ⟨1225318, by decide⟩ :=
  accepted_of_selected 12 354350 ⟨1225318, by decide⟩ ⟨12, 2, 0, 1225318, 354350, 2609, 65536⟩
    (by decide) selected_cut_44516

theorem selected_cut_44517 : selected 9 ⟨1225371, by decide⟩
    (prefixPartial 12 354351) = some ⟨12, 2, 0, 1225371, 354351, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_354351_1225371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354351 ⟨1225371, by decide⟩ :=
  accepted_of_selected 12 354351 ⟨1225371, by decide⟩ ⟨12, 2, 0, 1225371, 354351, 2861, 65536⟩
    (by decide) selected_cut_44517

theorem unmarked_context_11_88587_1225372 : frontier 10 ⟨1225372, by decide⟩
    (prefixCache 11 88587) (prefixPartial 11 88587) = false := by
  decide +kernel

theorem node_context_11_88587_1225372 : EJMOriginalGlobalDAGData.nodes 10 ⟨1225372, by decide⟩ =
    .split (coordinate 11) (![⟨1225220, by decide⟩,⟨1225264, by decide⟩,⟨1225318, by decide⟩,⟨1225371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88587_1225372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88587 ⟨1225372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88587
    ⟨1225372, by decide⟩ (by decide) (![⟨1225220, by decide⟩,⟨1225264, by decide⟩,⟨1225318, by decide⟩,⟨1225371, by decide⟩]) unmarked_context_11_88587_1225372 node_context_11_88587_1225372
  intro a
  fin_cases a
  · exact context_12_354348_1225220
  · exact context_12_354349_1225264
  · exact context_12_354350_1225318
  · exact context_12_354351_1225371

theorem unmarked_context_10_22146_1225373 : frontier 11 ⟨1225373, by decide⟩
    (prefixCache 10 22146) (prefixPartial 10 22146) = false := by
  decide +kernel

theorem node_context_10_22146_1225373 : EJMOriginalGlobalDAGData.nodes 11 ⟨1225373, by decide⟩ =
    .split (coordinate 10) (![⟨1225069, by decide⟩,⟨1225173, by decide⟩,⟨900587, by decide⟩,⟨1225372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22146_1225373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22146 ⟨1225373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22146
    ⟨1225373, by decide⟩ (by decide) (![⟨1225069, by decide⟩,⟨1225173, by decide⟩,⟨900587, by decide⟩,⟨1225372, by decide⟩]) unmarked_context_10_22146_1225373 node_context_10_22146_1225373
  intro a
  fin_cases a
  · exact context_11_88584_1225069
  · exact context_11_88585_1225173
  · exact context_11_88586_900587
  · exact context_11_88587_1225372

theorem selected_cut_44518 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 354352) = some ⟨12, 1, 0, 985390, 354352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354352_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354352 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 354352 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 354352, 1, 65536⟩
    (by decide) selected_cut_44518

theorem selected_cut_44519 : selected 9 ⟨1225408, by decide⟩
    (prefixPartial 12 354353) = some ⟨12, 2, 0, 1225408, 354353, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_354353_1225408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354353 ⟨1225408, by decide⟩ :=
  accepted_of_selected 12 354353 ⟨1225408, by decide⟩ ⟨12, 2, 0, 1225408, 354353, 2369, 65536⟩
    (by decide) selected_cut_44519

theorem selected_cut_44520 : selected 9 ⟨1225457, by decide⟩
    (prefixPartial 12 354354) = some ⟨12, 2, 0, 1225457, 354354, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_354354_1225457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354354 ⟨1225457, by decide⟩ :=
  accepted_of_selected 12 354354 ⟨1225457, by decide⟩ ⟨12, 2, 0, 1225457, 354354, 2593, 65536⟩
    (by decide) selected_cut_44520

theorem selected_cut_44521 : selected 9 ⟨1225512, by decide⟩
    (prefixPartial 12 354355) = some ⟨12, 2, 0, 1225512, 354355, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_354355_1225512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354355 ⟨1225512, by decide⟩ :=
  accepted_of_selected 12 354355 ⟨1225512, by decide⟩ ⟨12, 2, 0, 1225512, 354355, 2673, 65536⟩
    (by decide) selected_cut_44521

theorem unmarked_context_11_88588_1225513 : frontier 10 ⟨1225513, by decide⟩
    (prefixCache 11 88588) (prefixPartial 11 88588) = false := by
  decide +kernel

theorem node_context_11_88588_1225513 : EJMOriginalGlobalDAGData.nodes 10 ⟨1225513, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1225408, by decide⟩,⟨1225457, by decide⟩,⟨1225512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88588_1225513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88588 ⟨1225513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88588
    ⟨1225513, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1225408, by decide⟩,⟨1225457, by decide⟩,⟨1225512, by decide⟩]) unmarked_context_11_88588_1225513 node_context_11_88588_1225513
  intro a
  fin_cases a
  · exact context_12_354352_985390
  · exact context_12_354353_1225408
  · exact context_12_354354_1225457
  · exact context_12_354355_1225512

theorem selected_cut_44522 : selected 9 ⟨1197509, by decide⟩
    (prefixPartial 12 354356) = some ⟨12, 1, 0, 1197509, 354356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354356_1197509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354356 ⟨1197509, by decide⟩ :=
  accepted_of_selected 12 354356 ⟨1197509, by decide⟩ ⟨12, 1, 0, 1197509, 354356, 1, 65536⟩
    (by decide) selected_cut_44522

theorem selected_cut_44523 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 354357) = some ⟨12, 1, 0, 719134, 354357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354357_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354357 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 354357 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 354357, 1, 65536⟩
    (by decide) selected_cut_44523

theorem selected_cut_44524 : selected 9 ⟨1225560, by decide⟩
    (prefixPartial 12 354358) = some ⟨12, 2, 0, 1225560, 354358, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_354358_1225560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354358 ⟨1225560, by decide⟩ :=
  accepted_of_selected 12 354358 ⟨1225560, by decide⟩ ⟨12, 2, 0, 1225560, 354358, 2557, 65536⟩
    (by decide) selected_cut_44524

theorem selected_cut_44525 : selected 9 ⟨1225608, by decide⟩
    (prefixPartial 12 354359) = some ⟨12, 2, 0, 1225608, 354359, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_354359_1225608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354359 ⟨1225608, by decide⟩ :=
  accepted_of_selected 12 354359 ⟨1225608, by decide⟩ ⟨12, 2, 0, 1225608, 354359, 2661, 65536⟩
    (by decide) selected_cut_44525

theorem unmarked_context_11_88589_1225609 : frontier 10 ⟨1225609, by decide⟩
    (prefixCache 11 88589) (prefixPartial 11 88589) = false := by
  decide +kernel

theorem node_context_11_88589_1225609 : EJMOriginalGlobalDAGData.nodes 10 ⟨1225609, by decide⟩ =
    .split (coordinate 11) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1225560, by decide⟩,⟨1225608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88589_1225609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88589 ⟨1225609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88589
    ⟨1225609, by decide⟩ (by decide) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1225560, by decide⟩,⟨1225608, by decide⟩]) unmarked_context_11_88589_1225609 node_context_11_88589_1225609
  intro a
  fin_cases a
  · exact context_12_354356_1197509
  · exact context_12_354357_719134
  · exact context_12_354358_1225560
  · exact context_12_354359_1225608

theorem selected_cut_44526 : selected 9 ⟨1225649, by decide⟩
    (prefixPartial 12 354360) = some ⟨12, 2, 0, 1225649, 354360, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_354360_1225649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354360 ⟨1225649, by decide⟩ :=
  accepted_of_selected 12 354360 ⟨1225649, by decide⟩ ⟨12, 2, 0, 1225649, 354360, 2465, 65536⟩
    (by decide) selected_cut_44526

theorem selected_cut_44527 : selected 9 ⟨1225685, by decide⟩
    (prefixPartial 12 354361) = some ⟨12, 2, 0, 1225685, 354361, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_354361_1225685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354361 ⟨1225685, by decide⟩ :=
  accepted_of_selected 12 354361 ⟨1225685, by decide⟩ ⟨12, 2, 0, 1225685, 354361, 2253, 65536⟩
    (by decide) selected_cut_44527

theorem selected_cut_44528 : selected 9 ⟨1225728, by decide⟩
    (prefixPartial 12 354362) = some ⟨12, 2, 0, 1225728, 354362, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_354362_1225728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354362 ⟨1225728, by decide⟩ :=
  accepted_of_selected 12 354362 ⟨1225728, by decide⟩ ⟨12, 2, 0, 1225728, 354362, 2477, 65536⟩
    (by decide) selected_cut_44528

theorem selected_cut_44529 : selected 9 ⟨1225787, by decide⟩
    (prefixPartial 12 354363) = some ⟨12, 2, 0, 1225787, 354363, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_354363_1225787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354363 ⟨1225787, by decide⟩ :=
  accepted_of_selected 12 354363 ⟨1225787, by decide⟩ ⟨12, 2, 0, 1225787, 354363, 2781, 65536⟩
    (by decide) selected_cut_44529

theorem unmarked_context_11_88590_1225788 : frontier 10 ⟨1225788, by decide⟩
    (prefixCache 11 88590) (prefixPartial 11 88590) = false := by
  decide +kernel

theorem node_context_11_88590_1225788 : EJMOriginalGlobalDAGData.nodes 10 ⟨1225788, by decide⟩ =
    .split (coordinate 11) (![⟨1225649, by decide⟩,⟨1225685, by decide⟩,⟨1225728, by decide⟩,⟨1225787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88590_1225788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88590 ⟨1225788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88590
    ⟨1225788, by decide⟩ (by decide) (![⟨1225649, by decide⟩,⟨1225685, by decide⟩,⟨1225728, by decide⟩,⟨1225787, by decide⟩]) unmarked_context_11_88590_1225788 node_context_11_88590_1225788
  intro a
  fin_cases a
  · exact context_12_354360_1225649
  · exact context_12_354361_1225685
  · exact context_12_354362_1225728
  · exact context_12_354363_1225787

theorem selected_cut_44530 : selected 9 ⟨1225829, by decide⟩
    (prefixPartial 12 354364) = some ⟨12, 2, 0, 1225829, 354364, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_354364_1225829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354364 ⟨1225829, by decide⟩ :=
  accepted_of_selected 12 354364 ⟨1225829, by decide⟩ ⟨12, 2, 0, 1225829, 354364, 2237, 65536⟩
    (by decide) selected_cut_44530

theorem selected_cut_44531 : selected 9 ⟨1225862, by decide⟩
    (prefixPartial 12 354365) = some ⟨12, 2, 0, 1225862, 354365, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_354365_1225862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354365 ⟨1225862, by decide⟩ :=
  accepted_of_selected 12 354365 ⟨1225862, by decide⟩ ⟨12, 2, 0, 1225862, 354365, 2089, 65536⟩
    (by decide) selected_cut_44531

theorem selected_cut_44532 : selected 9 ⟨1225905, by decide⟩
    (prefixPartial 12 354366) = some ⟨12, 2, 0, 1225905, 354366, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_354366_1225905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354366 ⟨1225905, by decide⟩ :=
  accepted_of_selected 12 354366 ⟨1225905, by decide⟩ ⟨12, 2, 0, 1225905, 354366, 2357, 65536⟩
    (by decide) selected_cut_44532

theorem selected_cut_44533 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 354367) = some ⟨12, 1, 0, 1120582, 354367, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354367_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354367 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 354367 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 354367, 1, 65536⟩
    (by decide) selected_cut_44533

theorem unmarked_context_11_88591_1225906 : frontier 10 ⟨1225906, by decide⟩
    (prefixCache 11 88591) (prefixPartial 11 88591) = false := by
  decide +kernel

theorem node_context_11_88591_1225906 : EJMOriginalGlobalDAGData.nodes 10 ⟨1225906, by decide⟩ =
    .split (coordinate 11) (![⟨1225829, by decide⟩,⟨1225862, by decide⟩,⟨1225905, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88591_1225906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88591 ⟨1225906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88591
    ⟨1225906, by decide⟩ (by decide) (![⟨1225829, by decide⟩,⟨1225862, by decide⟩,⟨1225905, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_88591_1225906 node_context_11_88591_1225906
  intro a
  fin_cases a
  · exact context_12_354364_1225829
  · exact context_12_354365_1225862
  · exact context_12_354366_1225905
  · exact context_12_354367_1120582

theorem unmarked_context_10_22147_1225907 : frontier 11 ⟨1225907, by decide⟩
    (prefixCache 10 22147) (prefixPartial 10 22147) = false := by
  decide +kernel

theorem node_context_10_22147_1225907 : EJMOriginalGlobalDAGData.nodes 11 ⟨1225907, by decide⟩ =
    .split (coordinate 10) (![⟨1225513, by decide⟩,⟨1225609, by decide⟩,⟨1225788, by decide⟩,⟨1225906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22147_1225907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22147 ⟨1225907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22147
    ⟨1225907, by decide⟩ (by decide) (![⟨1225513, by decide⟩,⟨1225609, by decide⟩,⟨1225788, by decide⟩,⟨1225906, by decide⟩]) unmarked_context_10_22147_1225907 node_context_10_22147_1225907
  intro a
  fin_cases a
  · exact context_11_88588_1225513
  · exact context_11_88589_1225609
  · exact context_11_88590_1225788
  · exact context_11_88591_1225906

theorem unmarked_context_9_5536_1225908 : frontier 12 ⟨1225908, by decide⟩
    (prefixCache 9 5536) (prefixPartial 9 5536) = false := by
  decide +kernel

theorem node_context_9_5536_1225908 : EJMOriginalGlobalDAGData.nodes 12 ⟨1225908, by decide⟩ =
    .split (coordinate 9) (![⟨1224337, by decide⟩,⟨1224929, by decide⟩,⟨1225373, by decide⟩,⟨1225907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5536_1225908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5536 ⟨1225908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5536
    ⟨1225908, by decide⟩ (by decide) (![⟨1224337, by decide⟩,⟨1224929, by decide⟩,⟨1225373, by decide⟩,⟨1225907, by decide⟩]) unmarked_context_9_5536_1225908 node_context_9_5536_1225908
  intro a
  fin_cases a
  · exact context_10_22144_1224337
  · exact context_10_22145_1224929
  · exact context_10_22146_1225373
  · exact context_10_22147_1225907

theorem selected_cut_44534 : selected 10 ⟨1225942, by decide⟩
    (prefixPartial 11 88592) = some ⟨11, 2, 0, 1225942, 88592, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_88592_1225942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88592 ⟨1225942, by decide⟩ :=
  accepted_of_selected 11 88592 ⟨1225942, by decide⟩ ⟨11, 2, 0, 1225942, 88592, 1717, 262144⟩
    (by decide) selected_cut_44534

theorem selected_cut_44535 : selected 9 ⟨1225970, by decide⟩
    (prefixPartial 12 354372) = some ⟨12, 2, 0, 1225970, 354372, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_354372_1225970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354372 ⟨1225970, by decide⟩ :=
  accepted_of_selected 12 354372 ⟨1225970, by decide⟩ ⟨12, 2, 0, 1225970, 354372, 1601, 65536⟩
    (by decide) selected_cut_44535

theorem selected_cut_44536 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354373) = some ⟨12, 1, 0, 896706, 354373, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354373_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354373 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354373 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354373, 1, 65536⟩
    (by decide) selected_cut_44536

theorem selected_cut_44537 : selected 9 ⟨1225998, by decide⟩
    (prefixPartial 12 354374) = some ⟨12, 2, 0, 1225998, 354374, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_354374_1225998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354374 ⟨1225998, by decide⟩ :=
  accepted_of_selected 12 354374 ⟨1225998, by decide⟩ ⟨12, 2, 0, 1225998, 354374, 1673, 65536⟩
    (by decide) selected_cut_44537

theorem selected_cut_44538 : selected 9 ⟨1226028, by decide⟩
    (prefixPartial 12 354375) = some ⟨12, 2, 0, 1226028, 354375, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_354375_1226028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354375 ⟨1226028, by decide⟩ :=
  accepted_of_selected 12 354375 ⟨1226028, by decide⟩ ⟨12, 2, 0, 1226028, 354375, 1761, 65536⟩
    (by decide) selected_cut_44538

theorem unmarked_context_11_88593_1226029 : frontier 10 ⟨1226029, by decide⟩
    (prefixCache 11 88593) (prefixPartial 11 88593) = false := by
  decide +kernel

theorem node_context_11_88593_1226029 : EJMOriginalGlobalDAGData.nodes 10 ⟨1226029, by decide⟩ =
    .split (coordinate 11) (![⟨1225970, by decide⟩,⟨896706, by decide⟩,⟨1225998, by decide⟩,⟨1226028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88593_1226029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88593 ⟨1226029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88593
    ⟨1226029, by decide⟩ (by decide) (![⟨1225970, by decide⟩,⟨896706, by decide⟩,⟨1225998, by decide⟩,⟨1226028, by decide⟩]) unmarked_context_11_88593_1226029 node_context_11_88593_1226029
  intro a
  fin_cases a
  · exact context_12_354372_1225970
  · exact context_12_354373_896706
  · exact context_12_354374_1225998
  · exact context_12_354375_1226028

theorem selected_cut_44539 : selected 10 ⟨1226094, by decide⟩
    (prefixPartial 11 88594) = some ⟨11, 2, 0, 1226094, 88594, 3465, 262144⟩ := by
  decide +kernel

theorem context_11_88594_1226094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88594 ⟨1226094, by decide⟩ :=
  accepted_of_selected 11 88594 ⟨1226094, by decide⟩ ⟨11, 2, 0, 1226094, 88594, 3465, 262144⟩
    (by decide) selected_cut_44539

theorem selected_cut_44540 : selected 9 ⟨1226113, by decide⟩
    (prefixPartial 12 354380) = some ⟨12, 2, 0, 1226113, 354380, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_354380_1226113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354380 ⟨1226113, by decide⟩ :=
  accepted_of_selected 12 354380 ⟨1226113, by decide⟩ ⟨12, 2, 0, 1226113, 354380, 1453, 65536⟩
    (by decide) selected_cut_44540

theorem selected_cut_44541 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354381) = some ⟨12, 1, 0, 896706, 354381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354381_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354381 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354381 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354381, 1, 65536⟩
    (by decide) selected_cut_44541

theorem selected_cut_44542 : selected 9 ⟨1226140, by decide⟩
    (prefixPartial 12 354382) = some ⟨12, 2, 0, 1226140, 354382, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_354382_1226140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354382 ⟨1226140, by decide⟩ :=
  accepted_of_selected 12 354382 ⟨1226140, by decide⟩ ⟨12, 2, 0, 1226140, 354382, 1569, 65536⟩
    (by decide) selected_cut_44542

theorem selected_cut_44543 : selected 9 ⟨1226168, by decide⟩
    (prefixPartial 12 354383) = some ⟨12, 2, 0, 1226168, 354383, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_354383_1226168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354383 ⟨1226168, by decide⟩ :=
  accepted_of_selected 12 354383 ⟨1226168, by decide⟩ ⟨12, 2, 0, 1226168, 354383, 1605, 65536⟩
    (by decide) selected_cut_44543

theorem unmarked_context_11_88595_1226169 : frontier 10 ⟨1226169, by decide⟩
    (prefixCache 11 88595) (prefixPartial 11 88595) = false := by
  decide +kernel

theorem node_context_11_88595_1226169 : EJMOriginalGlobalDAGData.nodes 10 ⟨1226169, by decide⟩ =
    .split (coordinate 11) (![⟨1226113, by decide⟩,⟨896706, by decide⟩,⟨1226140, by decide⟩,⟨1226168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88595_1226169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88595 ⟨1226169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88595
    ⟨1226169, by decide⟩ (by decide) (![⟨1226113, by decide⟩,⟨896706, by decide⟩,⟨1226140, by decide⟩,⟨1226168, by decide⟩]) unmarked_context_11_88595_1226169 node_context_11_88595_1226169
  intro a
  fin_cases a
  · exact context_12_354380_1226113
  · exact context_12_354381_896706
  · exact context_12_354382_1226140
  · exact context_12_354383_1226168

theorem unmarked_context_10_22148_1226170 : frontier 11 ⟨1226170, by decide⟩
    (prefixCache 10 22148) (prefixPartial 10 22148) = false := by
  decide +kernel

theorem node_context_10_22148_1226170 : EJMOriginalGlobalDAGData.nodes 11 ⟨1226170, by decide⟩ =
    .split (coordinate 10) (![⟨1225942, by decide⟩,⟨1226029, by decide⟩,⟨1226094, by decide⟩,⟨1226169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22148_1226170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22148 ⟨1226170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22148
    ⟨1226170, by decide⟩ (by decide) (![⟨1225942, by decide⟩,⟨1226029, by decide⟩,⟨1226094, by decide⟩,⟨1226169, by decide⟩]) unmarked_context_10_22148_1226170 node_context_10_22148_1226170
  intro a
  fin_cases a
  · exact context_11_88592_1225942
  · exact context_11_88593_1226029
  · exact context_11_88594_1226094
  · exact context_11_88595_1226169

theorem selected_cut_44544 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22149) = some ⟨10, 1, 0, 893098, 22149, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22149_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22149 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22149 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22149, 1, 1048576⟩
    (by decide) selected_cut_44544

theorem selected_cut_44545 : selected 10 ⟨1226210, by decide⟩
    (prefixPartial 11 88600) = some ⟨11, 2, 0, 1226210, 88600, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_88600_1226210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88600 ⟨1226210, by decide⟩ :=
  accepted_of_selected 11 88600 ⟨1226210, by decide⟩ ⟨11, 2, 0, 1226210, 88600, 2521, 262144⟩
    (by decide) selected_cut_44545

theorem selected_cut_44546 : selected 10 ⟨1226280, by decide⟩
    (prefixPartial 11 88601) = some ⟨11, 2, 0, 1226280, 88601, 4045, 262144⟩ := by
  decide +kernel

theorem context_11_88601_1226280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88601 ⟨1226280, by decide⟩ :=
  accepted_of_selected 11 88601 ⟨1226280, by decide⟩ ⟨11, 2, 0, 1226280, 88601, 4045, 262144⟩
    (by decide) selected_cut_44546

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
