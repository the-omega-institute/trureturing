/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover517
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_102216_1409427 : frontier 10 ⟨1409427, by decide⟩
    (prefixCache 11 102216) (prefixPartial 11 102216) = false := by
  decide +kernel

theorem node_context_11_102216_1409427 : EJMOriginalGlobalDAGData.nodes 10 ⟨1409427, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1409323, by decide⟩,⟨1409387, by decide⟩,⟨1409426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102216_1409427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102216 ⟨1409427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102216
    ⟨1409427, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1409323, by decide⟩,⟨1409387, by decide⟩,⟨1409426, by decide⟩]) unmarked_context_11_102216_1409427 node_context_11_102216_1409427
  intro a
  fin_cases a
  · exact context_12_408864_1108174
  · exact context_12_408865_1409323
  · exact context_12_408866_1409387
  · exact context_12_408867_1409426

theorem selected_cut_49732 : selected 10 ⟨1409501, by decide⟩
    (prefixPartial 11 102217) = some ⟨11, 2, 0, 1409501, 102217, 3681, 262144⟩ := by
  decide +kernel

theorem context_11_102217_1409501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102217 ⟨1409501, by decide⟩ :=
  accepted_of_selected 11 102217 ⟨1409501, by decide⟩ ⟨11, 2, 0, 1409501, 102217, 3681, 262144⟩
    (by decide) selected_cut_49732

theorem selected_cut_49733 : selected 10 ⟨1409541, by decide⟩
    (prefixPartial 11 102218) = some ⟨11, 2, 0, 1409541, 102218, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_102218_1409541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102218 ⟨1409541, by decide⟩ :=
  accepted_of_selected 11 102218 ⟨1409541, by decide⟩ ⟨11, 2, 0, 1409541, 102218, 1525, 262144⟩
    (by decide) selected_cut_49733

theorem selected_cut_49734 : selected 10 ⟨1409639, by decide⟩
    (prefixPartial 11 102219) = some ⟨11, 2, 0, 1409639, 102219, 3969, 262144⟩ := by
  decide +kernel

theorem context_11_102219_1409639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102219 ⟨1409639, by decide⟩ :=
  accepted_of_selected 11 102219 ⟨1409639, by decide⟩ ⟨11, 2, 0, 1409639, 102219, 3969, 262144⟩
    (by decide) selected_cut_49734

theorem unmarked_context_10_25554_1409640 : frontier 11 ⟨1409640, by decide⟩
    (prefixCache 10 25554) (prefixPartial 10 25554) = false := by
  decide +kernel

theorem node_context_10_25554_1409640 : EJMOriginalGlobalDAGData.nodes 11 ⟨1409640, by decide⟩ =
    .split (coordinate 10) (![⟨1409427, by decide⟩,⟨1409501, by decide⟩,⟨1409541, by decide⟩,⟨1409639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25554_1409640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25554 ⟨1409640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25554
    ⟨1409640, by decide⟩ (by decide) (![⟨1409427, by decide⟩,⟨1409501, by decide⟩,⟨1409541, by decide⟩,⟨1409639, by decide⟩]) unmarked_context_10_25554_1409640 node_context_10_25554_1409640
  intro a
  fin_cases a
  · exact context_11_102216_1409427
  · exact context_11_102217_1409501
  · exact context_11_102218_1409541
  · exact context_11_102219_1409639

theorem selected_cut_49735 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408880) = some ⟨12, 1, 0, 1108174, 408880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408880_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408880 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408880 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408880, 1, 65536⟩
    (by decide) selected_cut_49735

theorem selected_cut_49736 : selected 9 ⟨1409673, by decide⟩
    (prefixPartial 12 408881) = some ⟨12, 2, 0, 1409673, 408881, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_408881_1409673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408881 ⟨1409673, by decide⟩ :=
  accepted_of_selected 12 408881 ⟨1409673, by decide⟩ ⟨12, 2, 0, 1409673, 408881, 1449, 65536⟩
    (by decide) selected_cut_49736

theorem selected_cut_49737 : selected 9 ⟨1409699, by decide⟩
    (prefixPartial 12 408882) = some ⟨12, 2, 0, 1409699, 408882, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_408882_1409699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408882 ⟨1409699, by decide⟩ :=
  accepted_of_selected 12 408882 ⟨1409699, by decide⟩ ⟨12, 2, 0, 1409699, 408882, 1493, 65536⟩
    (by decide) selected_cut_49737

theorem selected_cut_49738 : selected 9 ⟨1409728, by decide⟩
    (prefixPartial 12 408883) = some ⟨12, 2, 0, 1409728, 408883, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_408883_1409728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408883 ⟨1409728, by decide⟩ :=
  accepted_of_selected 12 408883 ⟨1409728, by decide⟩ ⟨12, 2, 0, 1409728, 408883, 1421, 65536⟩
    (by decide) selected_cut_49738

theorem unmarked_context_11_102220_1409729 : frontier 10 ⟨1409729, by decide⟩
    (prefixCache 11 102220) (prefixPartial 11 102220) = false := by
  decide +kernel

theorem node_context_11_102220_1409729 : EJMOriginalGlobalDAGData.nodes 10 ⟨1409729, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1409673, by decide⟩,⟨1409699, by decide⟩,⟨1409728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102220_1409729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102220 ⟨1409729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102220
    ⟨1409729, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1409673, by decide⟩,⟨1409699, by decide⟩,⟨1409728, by decide⟩]) unmarked_context_11_102220_1409729 node_context_11_102220_1409729
  intro a
  fin_cases a
  · exact context_12_408880_1108174
  · exact context_12_408881_1409673
  · exact context_12_408882_1409699
  · exact context_12_408883_1409728

theorem selected_cut_49739 : selected 10 ⟨1409781, by decide⟩
    (prefixPartial 11 102221) = some ⟨11, 2, 0, 1409781, 102221, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_102221_1409781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102221 ⟨1409781, by decide⟩ :=
  accepted_of_selected 11 102221 ⟨1409781, by decide⟩ ⟨11, 2, 0, 1409781, 102221, 2837, 262144⟩
    (by decide) selected_cut_49739

theorem selected_cut_49740 : selected 10 ⟨1409846, by decide⟩
    (prefixPartial 11 102222) = some ⟨11, 2, 0, 1409846, 102222, 3325, 262144⟩ := by
  decide +kernel

theorem context_11_102222_1409846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102222 ⟨1409846, by decide⟩ :=
  accepted_of_selected 11 102222 ⟨1409846, by decide⟩ ⟨11, 2, 0, 1409846, 102222, 3325, 262144⟩
    (by decide) selected_cut_49740

theorem selected_cut_49741 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102223) = some ⟨11, 1, 0, 977886, 102223, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102223_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102223 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102223 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102223, 1, 262144⟩
    (by decide) selected_cut_49741

theorem unmarked_context_10_25555_1409847 : frontier 11 ⟨1409847, by decide⟩
    (prefixCache 10 25555) (prefixPartial 10 25555) = false := by
  decide +kernel

theorem node_context_10_25555_1409847 : EJMOriginalGlobalDAGData.nodes 11 ⟨1409847, by decide⟩ =
    .split (coordinate 10) (![⟨1409729, by decide⟩,⟨1409781, by decide⟩,⟨1409846, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25555_1409847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25555 ⟨1409847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25555
    ⟨1409847, by decide⟩ (by decide) (![⟨1409729, by decide⟩,⟨1409781, by decide⟩,⟨1409846, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25555_1409847 node_context_10_25555_1409847
  intro a
  fin_cases a
  · exact context_11_102220_1409729
  · exact context_11_102221_1409781
  · exact context_11_102222_1409846
  · exact context_11_102223_977886

theorem unmarked_context_9_6388_1409848 : frontier 12 ⟨1409848, by decide⟩
    (prefixCache 9 6388) (prefixPartial 9 6388) = false := by
  decide +kernel

theorem node_context_9_6388_1409848 : EJMOriginalGlobalDAGData.nodes 12 ⟨1409848, by decide⟩ =
    .split (coordinate 9) (![⟨1408944, by decide⟩,⟨1409260, by decide⟩,⟨1409640, by decide⟩,⟨1409847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6388_1409848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6388 ⟨1409848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6388
    ⟨1409848, by decide⟩ (by decide) (![⟨1408944, by decide⟩,⟨1409260, by decide⟩,⟨1409640, by decide⟩,⟨1409847, by decide⟩]) unmarked_context_9_6388_1409848 node_context_9_6388_1409848
  intro a
  fin_cases a
  · exact context_10_25552_1408944
  · exact context_10_25553_1409260
  · exact context_10_25554_1409640
  · exact context_10_25555_1409847

theorem selected_cut_49742 : selected 10 ⟨1409876, by decide⟩
    (prefixPartial 11 102224) = some ⟨11, 2, 0, 1409876, 102224, 1321, 262144⟩ := by
  decide +kernel

theorem context_11_102224_1409876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102224 ⟨1409876, by decide⟩ :=
  accepted_of_selected 11 102224 ⟨1409876, by decide⟩ ⟨11, 2, 0, 1409876, 102224, 1321, 262144⟩
    (by decide) selected_cut_49742

theorem selected_cut_49743 : selected 10 ⟨1409928, by decide⟩
    (prefixPartial 11 102225) = some ⟨11, 2, 0, 1409928, 102225, 3465, 262144⟩ := by
  decide +kernel

theorem context_11_102225_1409928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102225 ⟨1409928, by decide⟩ :=
  accepted_of_selected 11 102225 ⟨1409928, by decide⟩ ⟨11, 2, 0, 1409928, 102225, 3465, 262144⟩
    (by decide) selected_cut_49743

theorem selected_cut_49744 : selected 10 ⟨1409959, by decide⟩
    (prefixPartial 11 102226) = some ⟨11, 2, 0, 1409959, 102226, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_102226_1409959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102226 ⟨1409959, by decide⟩ :=
  accepted_of_selected 11 102226 ⟨1409959, by decide⟩ ⟨11, 2, 0, 1409959, 102226, 2109, 262144⟩
    (by decide) selected_cut_49744

theorem selected_cut_49745 : selected 10 ⟨1409997, by decide⟩
    (prefixPartial 11 102227) = some ⟨11, 2, 0, 1409997, 102227, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_102227_1409997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102227 ⟨1409997, by decide⟩ :=
  accepted_of_selected 11 102227 ⟨1409997, by decide⟩ ⟨11, 2, 0, 1409997, 102227, 1897, 262144⟩
    (by decide) selected_cut_49745

theorem unmarked_context_10_25556_1409998 : frontier 11 ⟨1409998, by decide⟩
    (prefixCache 10 25556) (prefixPartial 10 25556) = false := by
  decide +kernel

theorem node_context_10_25556_1409998 : EJMOriginalGlobalDAGData.nodes 11 ⟨1409998, by decide⟩ =
    .split (coordinate 10) (![⟨1409876, by decide⟩,⟨1409928, by decide⟩,⟨1409959, by decide⟩,⟨1409997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25556_1409998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25556 ⟨1409998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25556
    ⟨1409998, by decide⟩ (by decide) (![⟨1409876, by decide⟩,⟨1409928, by decide⟩,⟨1409959, by decide⟩,⟨1409997, by decide⟩]) unmarked_context_10_25556_1409998 node_context_10_25556_1409998
  intro a
  fin_cases a
  · exact context_11_102224_1409876
  · exact context_11_102225_1409928
  · exact context_11_102226_1409959
  · exact context_11_102227_1409997

theorem selected_cut_49746 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25557) = some ⟨10, 1, 0, 893098, 25557, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25557_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25557 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25557 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25557, 1, 1048576⟩
    (by decide) selected_cut_49746

theorem selected_cut_49747 : selected 10 ⟨1410066, by decide⟩
    (prefixPartial 11 102232) = some ⟨11, 2, 0, 1410066, 102232, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_102232_1410066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102232 ⟨1410066, by decide⟩ :=
  accepted_of_selected 11 102232 ⟨1410066, by decide⟩ ⟨11, 2, 0, 1410066, 102232, 2569, 262144⟩
    (by decide) selected_cut_49747

theorem selected_cut_49748 : selected 10 ⟨1410124, by decide⟩
    (prefixPartial 11 102233) = some ⟨11, 2, 0, 1410124, 102233, 3185, 262144⟩ := by
  decide +kernel

theorem context_11_102233_1410124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102233 ⟨1410124, by decide⟩ :=
  accepted_of_selected 11 102233 ⟨1410124, by decide⟩ ⟨11, 2, 0, 1410124, 102233, 3185, 262144⟩
    (by decide) selected_cut_49748

theorem selected_cut_49749 : selected 10 ⟨1410142, by decide⟩
    (prefixPartial 11 102234) = some ⟨11, 2, 0, 1410142, 102234, 929, 262144⟩ := by
  decide +kernel

theorem context_11_102234_1410142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102234 ⟨1410142, by decide⟩ :=
  accepted_of_selected 11 102234 ⟨1410142, by decide⟩ ⟨11, 2, 0, 1410142, 102234, 929, 262144⟩
    (by decide) selected_cut_49749

theorem selected_cut_49750 : selected 10 ⟨1410171, by decide⟩
    (prefixPartial 11 102235) = some ⟨11, 2, 0, 1410171, 102235, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_102235_1410171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102235 ⟨1410171, by decide⟩ :=
  accepted_of_selected 11 102235 ⟨1410171, by decide⟩ ⟨11, 2, 0, 1410171, 102235, 1757, 262144⟩
    (by decide) selected_cut_49750

theorem unmarked_context_10_25558_1410172 : frontier 11 ⟨1410172, by decide⟩
    (prefixCache 10 25558) (prefixPartial 10 25558) = false := by
  decide +kernel

theorem node_context_10_25558_1410172 : EJMOriginalGlobalDAGData.nodes 11 ⟨1410172, by decide⟩ =
    .split (coordinate 10) (![⟨1410066, by decide⟩,⟨1410124, by decide⟩,⟨1410142, by decide⟩,⟨1410171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25558_1410172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25558 ⟨1410172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25558
    ⟨1410172, by decide⟩ (by decide) (![⟨1410066, by decide⟩,⟨1410124, by decide⟩,⟨1410142, by decide⟩,⟨1410171, by decide⟩]) unmarked_context_10_25558_1410172 node_context_10_25558_1410172
  intro a
  fin_cases a
  · exact context_11_102232_1410066
  · exact context_11_102233_1410124
  · exact context_11_102234_1410142
  · exact context_11_102235_1410171

theorem selected_cut_49751 : selected 10 ⟨1410203, by decide⟩
    (prefixPartial 11 102236) = some ⟨11, 2, 0, 1410203, 102236, 1865, 262144⟩ := by
  decide +kernel

theorem context_11_102236_1410203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102236 ⟨1410203, by decide⟩ :=
  accepted_of_selected 11 102236 ⟨1410203, by decide⟩ ⟨11, 2, 0, 1410203, 102236, 1865, 262144⟩
    (by decide) selected_cut_49751

theorem selected_cut_49752 : selected 10 ⟨1410244, by decide⟩
    (prefixPartial 11 102237) = some ⟨11, 2, 0, 1410244, 102237, 2465, 262144⟩ := by
  decide +kernel

theorem context_11_102237_1410244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102237 ⟨1410244, by decide⟩ :=
  accepted_of_selected 11 102237 ⟨1410244, by decide⟩ ⟨11, 2, 0, 1410244, 102237, 2465, 262144⟩
    (by decide) selected_cut_49752

theorem selected_cut_49753 : selected 10 ⟨1410271, by decide⟩
    (prefixPartial 11 102238) = some ⟨11, 2, 0, 1410271, 102238, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_102238_1410271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102238 ⟨1410271, by decide⟩ :=
  accepted_of_selected 11 102238 ⟨1410271, by decide⟩ ⟨11, 2, 0, 1410271, 102238, 1449, 262144⟩
    (by decide) selected_cut_49753

theorem selected_cut_49754 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102239) = some ⟨11, 1, 0, 977886, 102239, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102239_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102239 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102239 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102239, 1, 262144⟩
    (by decide) selected_cut_49754

theorem unmarked_context_10_25559_1410272 : frontier 11 ⟨1410272, by decide⟩
    (prefixCache 10 25559) (prefixPartial 10 25559) = false := by
  decide +kernel

theorem node_context_10_25559_1410272 : EJMOriginalGlobalDAGData.nodes 11 ⟨1410272, by decide⟩ =
    .split (coordinate 10) (![⟨1410203, by decide⟩,⟨1410244, by decide⟩,⟨1410271, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25559_1410272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25559 ⟨1410272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25559
    ⟨1410272, by decide⟩ (by decide) (![⟨1410203, by decide⟩,⟨1410244, by decide⟩,⟨1410271, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25559_1410272 node_context_10_25559_1410272
  intro a
  fin_cases a
  · exact context_11_102236_1410203
  · exact context_11_102237_1410244
  · exact context_11_102238_1410271
  · exact context_11_102239_977886

theorem unmarked_context_9_6389_1410273 : frontier 12 ⟨1410273, by decide⟩
    (prefixCache 9 6389) (prefixPartial 9 6389) = false := by
  decide +kernel

theorem node_context_9_6389_1410273 : EJMOriginalGlobalDAGData.nodes 12 ⟨1410273, by decide⟩ =
    .split (coordinate 9) (![⟨1409998, by decide⟩,⟨893098, by decide⟩,⟨1410172, by decide⟩,⟨1410272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6389_1410273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6389 ⟨1410273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6389
    ⟨1410273, by decide⟩ (by decide) (![⟨1409998, by decide⟩,⟨893098, by decide⟩,⟨1410172, by decide⟩,⟨1410272, by decide⟩]) unmarked_context_9_6389_1410273 node_context_9_6389_1410273
  intro a
  fin_cases a
  · exact context_10_25556_1409998
  · exact context_10_25557_893098
  · exact context_10_25558_1410172
  · exact context_10_25559_1410272

theorem selected_cut_49755 : selected 10 ⟨1410294, by decide⟩
    (prefixPartial 11 102240) = some ⟨11, 2, 0, 1410294, 102240, 909, 262144⟩ := by
  decide +kernel

theorem context_11_102240_1410294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102240 ⟨1410294, by decide⟩ :=
  accepted_of_selected 11 102240 ⟨1410294, by decide⟩ ⟨11, 2, 0, 1410294, 102240, 909, 262144⟩
    (by decide) selected_cut_49755

theorem selected_cut_49756 : selected 10 ⟨1410315, by decide⟩
    (prefixPartial 11 102241) = some ⟨11, 2, 0, 1410315, 102241, 1329, 262144⟩ := by
  decide +kernel

theorem context_11_102241_1410315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102241 ⟨1410315, by decide⟩ :=
  accepted_of_selected 11 102241 ⟨1410315, by decide⟩ ⟨11, 2, 0, 1410315, 102241, 1329, 262144⟩
    (by decide) selected_cut_49756

theorem selected_cut_49757 : selected 10 ⟨1410341, by decide⟩
    (prefixPartial 11 102242) = some ⟨11, 2, 0, 1410341, 102242, 1969, 262144⟩ := by
  decide +kernel

theorem context_11_102242_1410341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102242 ⟨1410341, by decide⟩ :=
  accepted_of_selected 11 102242 ⟨1410341, by decide⟩ ⟨11, 2, 0, 1410341, 102242, 1969, 262144⟩
    (by decide) selected_cut_49757

theorem selected_cut_49758 : selected 10 ⟨1410360, by decide⟩
    (prefixPartial 11 102243) = some ⟨11, 2, 0, 1410360, 102243, 1193, 262144⟩ := by
  decide +kernel

theorem context_11_102243_1410360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102243 ⟨1410360, by decide⟩ :=
  accepted_of_selected 11 102243 ⟨1410360, by decide⟩ ⟨11, 2, 0, 1410360, 102243, 1193, 262144⟩
    (by decide) selected_cut_49758

theorem unmarked_context_10_25560_1410361 : frontier 11 ⟨1410361, by decide⟩
    (prefixCache 10 25560) (prefixPartial 10 25560) = false := by
  decide +kernel

theorem node_context_10_25560_1410361 : EJMOriginalGlobalDAGData.nodes 11 ⟨1410361, by decide⟩ =
    .split (coordinate 10) (![⟨1410294, by decide⟩,⟨1410315, by decide⟩,⟨1410341, by decide⟩,⟨1410360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25560_1410361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25560 ⟨1410361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25560
    ⟨1410361, by decide⟩ (by decide) (![⟨1410294, by decide⟩,⟨1410315, by decide⟩,⟨1410341, by decide⟩,⟨1410360, by decide⟩]) unmarked_context_10_25560_1410361 node_context_10_25560_1410361
  intro a
  fin_cases a
  · exact context_11_102240_1410294
  · exact context_11_102241_1410315
  · exact context_11_102242_1410341
  · exact context_11_102243_1410360

theorem selected_cut_49759 : selected 10 ⟨1410394, by decide⟩
    (prefixPartial 11 102244) = some ⟨11, 2, 0, 1410394, 102244, 1529, 262144⟩ := by
  decide +kernel

theorem context_11_102244_1410394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102244 ⟨1410394, by decide⟩ :=
  accepted_of_selected 11 102244 ⟨1410394, by decide⟩ ⟨11, 2, 0, 1410394, 102244, 1529, 262144⟩
    (by decide) selected_cut_49759

theorem selected_cut_49760 : selected 10 ⟨1410395, by decide⟩
    (prefixPartial 11 102245) = some ⟨11, 2, 0, 1410395, 102245, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102245_1410395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102245 ⟨1410395, by decide⟩ :=
  accepted_of_selected 11 102245 ⟨1410395, by decide⟩ ⟨11, 2, 0, 1410395, 102245, 5, 262144⟩
    (by decide) selected_cut_49760

theorem selected_cut_49761 : selected 10 ⟨1410423, by decide⟩
    (prefixPartial 11 102246) = some ⟨11, 2, 0, 1410423, 102246, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_102246_1410423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102246 ⟨1410423, by decide⟩ :=
  accepted_of_selected 11 102246 ⟨1410423, by decide⟩ ⟨11, 2, 0, 1410423, 102246, 1673, 262144⟩
    (by decide) selected_cut_49761

theorem selected_cut_49762 : selected 10 ⟨1410446, by decide⟩
    (prefixPartial 11 102247) = some ⟨11, 2, 0, 1410446, 102247, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_102247_1410446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102247 ⟨1410446, by decide⟩ :=
  accepted_of_selected 11 102247 ⟨1410446, by decide⟩ ⟨11, 2, 0, 1410446, 102247, 1381, 262144⟩
    (by decide) selected_cut_49762

theorem unmarked_context_10_25561_1410447 : frontier 11 ⟨1410447, by decide⟩
    (prefixCache 10 25561) (prefixPartial 10 25561) = false := by
  decide +kernel

theorem node_context_10_25561_1410447 : EJMOriginalGlobalDAGData.nodes 11 ⟨1410447, by decide⟩ =
    .split (coordinate 10) (![⟨1410394, by decide⟩,⟨1410395, by decide⟩,⟨1410423, by decide⟩,⟨1410446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25561_1410447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25561 ⟨1410447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25561
    ⟨1410447, by decide⟩ (by decide) (![⟨1410394, by decide⟩,⟨1410395, by decide⟩,⟨1410423, by decide⟩,⟨1410446, by decide⟩]) unmarked_context_10_25561_1410447 node_context_10_25561_1410447
  intro a
  fin_cases a
  · exact context_11_102244_1410394
  · exact context_11_102245_1410395
  · exact context_11_102246_1410423
  · exact context_11_102247_1410446

theorem selected_cut_49763 : selected 11 ⟨1410470, by decide⟩
    (prefixPartial 10 25562) = some ⟨10, 2, 0, 1410470, 25562, 881, 1048576⟩ := by
  decide +kernel

theorem context_10_25562_1410470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25562 ⟨1410470, by decide⟩ :=
  accepted_of_selected 10 25562 ⟨1410470, by decide⟩ ⟨10, 2, 0, 1410470, 25562, 881, 1048576⟩
    (by decide) selected_cut_49763

theorem selected_cut_49764 : selected 11 ⟨1410527, by decide⟩
    (prefixPartial 10 25563) = some ⟨10, 2, 0, 1410527, 25563, 2769, 1048576⟩ := by
  decide +kernel

theorem context_10_25563_1410527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25563 ⟨1410527, by decide⟩ :=
  accepted_of_selected 10 25563 ⟨1410527, by decide⟩ ⟨10, 2, 0, 1410527, 25563, 2769, 1048576⟩
    (by decide) selected_cut_49764

theorem unmarked_context_9_6390_1410528 : frontier 12 ⟨1410528, by decide⟩
    (prefixCache 9 6390) (prefixPartial 9 6390) = false := by
  decide +kernel

theorem node_context_9_6390_1410528 : EJMOriginalGlobalDAGData.nodes 12 ⟨1410528, by decide⟩ =
    .split (coordinate 9) (![⟨1410361, by decide⟩,⟨1410447, by decide⟩,⟨1410470, by decide⟩,⟨1410527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6390_1410528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6390 ⟨1410528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6390
    ⟨1410528, by decide⟩ (by decide) (![⟨1410361, by decide⟩,⟨1410447, by decide⟩,⟨1410470, by decide⟩,⟨1410527, by decide⟩]) unmarked_context_9_6390_1410528 node_context_9_6390_1410528
  intro a
  fin_cases a
  · exact context_10_25560_1410361
  · exact context_10_25561_1410447
  · exact context_10_25562_1410470
  · exact context_10_25563_1410527

theorem selected_cut_49765 : selected 11 ⟨1410568, by decide⟩
    (prefixPartial 10 25564) = some ⟨10, 2, 0, 1410568, 25564, 1973, 1048576⟩ := by
  decide +kernel

theorem context_10_25564_1410568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25564 ⟨1410568, by decide⟩ :=
  accepted_of_selected 10 25564 ⟨1410568, by decide⟩ ⟨10, 2, 0, 1410568, 25564, 1973, 1048576⟩
    (by decide) selected_cut_49765

theorem selected_cut_49766 : selected 11 ⟨1410609, by decide⟩
    (prefixPartial 10 25565) = some ⟨10, 2, 0, 1410609, 25565, 1557, 1048576⟩ := by
  decide +kernel

theorem context_10_25565_1410609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25565 ⟨1410609, by decide⟩ :=
  accepted_of_selected 10 25565 ⟨1410609, by decide⟩ ⟨10, 2, 0, 1410609, 25565, 1557, 1048576⟩
    (by decide) selected_cut_49766

theorem selected_cut_49767 : selected 11 ⟨1410636, by decide⟩
    (prefixPartial 10 25566) = some ⟨10, 2, 0, 1410636, 25566, 765, 1048576⟩ := by
  decide +kernel

theorem context_10_25566_1410636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25566 ⟨1410636, by decide⟩ :=
  accepted_of_selected 10 25566 ⟨1410636, by decide⟩ ⟨10, 2, 0, 1410636, 25566, 765, 1048576⟩
    (by decide) selected_cut_49767

theorem selected_cut_49768 : selected 11 ⟨1410638, by decide⟩
    (prefixPartial 10 25567) = some ⟨10, 2, 0, 1410638, 25567, 21, 1048576⟩ := by
  decide +kernel

theorem context_10_25567_1410638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25567 ⟨1410638, by decide⟩ :=
  accepted_of_selected 10 25567 ⟨1410638, by decide⟩ ⟨10, 2, 0, 1410638, 25567, 21, 1048576⟩
    (by decide) selected_cut_49768

theorem unmarked_context_9_6391_1410639 : frontier 12 ⟨1410639, by decide⟩
    (prefixCache 9 6391) (prefixPartial 9 6391) = false := by
  decide +kernel

theorem node_context_9_6391_1410639 : EJMOriginalGlobalDAGData.nodes 12 ⟨1410639, by decide⟩ =
    .split (coordinate 9) (![⟨1410568, by decide⟩,⟨1410609, by decide⟩,⟨1410636, by decide⟩,⟨1410638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6391_1410639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6391 ⟨1410639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6391
    ⟨1410639, by decide⟩ (by decide) (![⟨1410568, by decide⟩,⟨1410609, by decide⟩,⟨1410636, by decide⟩,⟨1410638, by decide⟩]) unmarked_context_9_6391_1410639 node_context_9_6391_1410639
  intro a
  fin_cases a
  · exact context_10_25564_1410568
  · exact context_10_25565_1410609
  · exact context_10_25566_1410636
  · exact context_10_25567_1410638

theorem unmarked_context_8_1597_1410640 : frontier 13 ⟨1410640, by decide⟩
    (prefixCache 8 1597) (prefixPartial 8 1597) = false := by
  decide +kernel

theorem node_context_8_1597_1410640 : EJMOriginalGlobalDAGData.nodes 13 ⟨1410640, by decide⟩ =
    .split (coordinate 8) (![⟨1409848, by decide⟩,⟨1410273, by decide⟩,⟨1410528, by decide⟩,⟨1410639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1597_1410640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1597 ⟨1410640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1597
    ⟨1410640, by decide⟩ (by decide) (![⟨1409848, by decide⟩,⟨1410273, by decide⟩,⟨1410528, by decide⟩,⟨1410639, by decide⟩]) unmarked_context_8_1597_1410640 node_context_8_1597_1410640
  intro a
  fin_cases a
  · exact context_9_6388_1409848
  · exact context_9_6389_1410273
  · exact context_9_6390_1410528
  · exact context_9_6391_1410639

theorem selected_cut_49769 : selected 11 ⟨1410705, by decide⟩
    (prefixPartial 10 25568) = some ⟨10, 2, 0, 1410705, 25568, 2345, 1048576⟩ := by
  decide +kernel

theorem context_10_25568_1410705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25568 ⟨1410705, by decide⟩ :=
  accepted_of_selected 10 25568 ⟨1410705, by decide⟩ ⟨10, 2, 0, 1410705, 25568, 2345, 1048576⟩
    (by decide) selected_cut_49769

theorem selected_cut_49770 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409104) = some ⟨12, 1, 0, 1108174, 409104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409104_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409104 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409104 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409104, 1, 65536⟩
    (by decide) selected_cut_49770

theorem selected_cut_49771 : selected 9 ⟨1410792, by decide⟩
    (prefixPartial 12 409105) = some ⟨12, 2, 0, 1410792, 409105, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_409105_1410792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409105 ⟨1410792, by decide⟩ :=
  accepted_of_selected 12 409105 ⟨1410792, by decide⟩ ⟨12, 2, 0, 1410792, 409105, 2861, 65536⟩
    (by decide) selected_cut_49771

theorem selected_cut_49772 : selected 9 ⟨1410863, by decide⟩
    (prefixPartial 12 409106) = some ⟨12, 2, 0, 1410863, 409106, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_409106_1410863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409106 ⟨1410863, by decide⟩ :=
  accepted_of_selected 12 409106 ⟨1410863, by decide⟩ ⟨12, 2, 0, 1410863, 409106, 2685, 65536⟩
    (by decide) selected_cut_49772

theorem selected_cut_49773 : selected 9 ⟨1410924, by decide⟩
    (prefixPartial 12 409107) = some ⟨12, 2, 0, 1410924, 409107, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_409107_1410924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409107 ⟨1410924, by decide⟩ :=
  accepted_of_selected 12 409107 ⟨1410924, by decide⟩ ⟨12, 2, 0, 1410924, 409107, 2605, 65536⟩
    (by decide) selected_cut_49773

theorem unmarked_context_11_102276_1410925 : frontier 10 ⟨1410925, by decide⟩
    (prefixCache 11 102276) (prefixPartial 11 102276) = false := by
  decide +kernel

theorem node_context_11_102276_1410925 : EJMOriginalGlobalDAGData.nodes 10 ⟨1410925, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1410792, by decide⟩,⟨1410863, by decide⟩,⟨1410924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102276_1410925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102276 ⟨1410925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102276
    ⟨1410925, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1410792, by decide⟩,⟨1410863, by decide⟩,⟨1410924, by decide⟩]) unmarked_context_11_102276_1410925 node_context_11_102276_1410925
  intro a
  fin_cases a
  · exact context_12_409104_1108174
  · exact context_12_409105_1410792
  · exact context_12_409106_1410863
  · exact context_12_409107_1410924

theorem selected_cut_49774 : selected 10 ⟨1410994, by decide⟩
    (prefixPartial 11 102277) = some ⟨11, 2, 0, 1410994, 102277, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_102277_1410994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102277 ⟨1410994, by decide⟩ :=
  accepted_of_selected 11 102277 ⟨1410994, by decide⟩ ⟨11, 2, 0, 1410994, 102277, 2233, 262144⟩
    (by decide) selected_cut_49774

theorem selected_cut_49775 : selected 10 ⟨1411075, by decide⟩
    (prefixPartial 11 102278) = some ⟨11, 2, 0, 1411075, 102278, 3861, 262144⟩ := by
  decide +kernel

theorem context_11_102278_1411075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102278 ⟨1411075, by decide⟩ :=
  accepted_of_selected 11 102278 ⟨1411075, by decide⟩ ⟨11, 2, 0, 1411075, 102278, 3861, 262144⟩
    (by decide) selected_cut_49775

theorem selected_cut_49776 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409116) = some ⟨12, 1, 0, 1108174, 409116, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409116_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409116 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409116 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409116, 1, 65536⟩
    (by decide) selected_cut_49776

theorem selected_cut_49777 : selected 9 ⟨1411119, by decide⟩
    (prefixPartial 12 409117) = some ⟨12, 2, 0, 1411119, 409117, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_409117_1411119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409117 ⟨1411119, by decide⟩ :=
  accepted_of_selected 12 409117 ⟨1411119, by decide⟩ ⟨12, 2, 0, 1411119, 409117, 1973, 65536⟩
    (by decide) selected_cut_49777

theorem selected_cut_49778 : selected 9 ⟨1411163, by decide⟩
    (prefixPartial 12 409118) = some ⟨12, 2, 0, 1411163, 409118, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_409118_1411163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409118 ⟨1411163, by decide⟩ :=
  accepted_of_selected 12 409118 ⟨1411163, by decide⟩ ⟨12, 2, 0, 1411163, 409118, 2013, 65536⟩
    (by decide) selected_cut_49778

theorem selected_cut_49779 : selected 9 ⟨1411229, by decide⟩
    (prefixPartial 12 409119) = some ⟨12, 2, 0, 1411229, 409119, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_409119_1411229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409119 ⟨1411229, by decide⟩ :=
  accepted_of_selected 12 409119 ⟨1411229, by decide⟩ ⟨12, 2, 0, 1411229, 409119, 1141, 65536⟩
    (by decide) selected_cut_49779

theorem unmarked_context_11_102279_1411230 : frontier 10 ⟨1411230, by decide⟩
    (prefixCache 11 102279) (prefixPartial 11 102279) = false := by
  decide +kernel

theorem node_context_11_102279_1411230 : EJMOriginalGlobalDAGData.nodes 10 ⟨1411230, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1411119, by decide⟩,⟨1411163, by decide⟩,⟨1411229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102279_1411230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102279 ⟨1411230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102279
    ⟨1411230, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1411119, by decide⟩,⟨1411163, by decide⟩,⟨1411229, by decide⟩]) unmarked_context_11_102279_1411230 node_context_11_102279_1411230
  intro a
  fin_cases a
  · exact context_12_409116_1108174
  · exact context_12_409117_1411119
  · exact context_12_409118_1411163
  · exact context_12_409119_1411229

theorem unmarked_context_10_25569_1411231 : frontier 11 ⟨1411231, by decide⟩
    (prefixCache 10 25569) (prefixPartial 10 25569) = false := by
  decide +kernel

theorem node_context_10_25569_1411231 : EJMOriginalGlobalDAGData.nodes 11 ⟨1411231, by decide⟩ =
    .split (coordinate 10) (![⟨1410925, by decide⟩,⟨1410994, by decide⟩,⟨1411075, by decide⟩,⟨1411230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25569_1411231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25569 ⟨1411231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25569
    ⟨1411231, by decide⟩ (by decide) (![⟨1410925, by decide⟩,⟨1410994, by decide⟩,⟨1411075, by decide⟩,⟨1411230, by decide⟩]) unmarked_context_10_25569_1411231 node_context_10_25569_1411231
  intro a
  fin_cases a
  · exact context_11_102276_1410925
  · exact context_11_102277_1410994
  · exact context_11_102278_1411075
  · exact context_11_102279_1411230

theorem selected_cut_49780 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409120) = some ⟨12, 1, 0, 1108174, 409120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409120_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409120 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409120 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409120, 1, 65536⟩
    (by decide) selected_cut_49780

theorem selected_cut_49781 : selected 9 ⟨1411302, by decide⟩
    (prefixPartial 12 409121) = some ⟨12, 2, 0, 1411302, 409121, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_409121_1411302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409121 ⟨1411302, by decide⟩ :=
  accepted_of_selected 12 409121 ⟨1411302, by decide⟩ ⟨12, 2, 0, 1411302, 409121, 2525, 65536⟩
    (by decide) selected_cut_49781

theorem selected_cut_49782 : selected 9 ⟨1411365, by decide⟩
    (prefixPartial 12 409122) = some ⟨12, 2, 0, 1411365, 409122, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_409122_1411365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409122 ⟨1411365, by decide⟩ :=
  accepted_of_selected 12 409122 ⟨1411365, by decide⟩ ⟨12, 2, 0, 1411365, 409122, 2465, 65536⟩
    (by decide) selected_cut_49782

theorem selected_cut_49783 : selected 9 ⟨1411422, by decide⟩
    (prefixPartial 12 409123) = some ⟨12, 2, 0, 1411422, 409123, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_409123_1411422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409123 ⟨1411422, by decide⟩ :=
  accepted_of_selected 12 409123 ⟨1411422, by decide⟩ ⟨12, 2, 0, 1411422, 409123, 2229, 65536⟩
    (by decide) selected_cut_49783

theorem unmarked_context_11_102280_1411423 : frontier 10 ⟨1411423, by decide⟩
    (prefixCache 11 102280) (prefixPartial 11 102280) = false := by
  decide +kernel

theorem node_context_11_102280_1411423 : EJMOriginalGlobalDAGData.nodes 10 ⟨1411423, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1411302, by decide⟩,⟨1411365, by decide⟩,⟨1411422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102280_1411423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102280 ⟨1411423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102280
    ⟨1411423, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1411302, by decide⟩,⟨1411365, by decide⟩,⟨1411422, by decide⟩]) unmarked_context_11_102280_1411423 node_context_11_102280_1411423
  intro a
  fin_cases a
  · exact context_12_409120_1108174
  · exact context_12_409121_1411302
  · exact context_12_409122_1411365
  · exact context_12_409123_1411422

theorem selected_cut_49784 : selected 10 ⟨1411514, by decide⟩
    (prefixPartial 11 102281) = some ⟨11, 2, 0, 1411514, 102281, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_102281_1411514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102281 ⟨1411514, by decide⟩ :=
  accepted_of_selected 11 102281 ⟨1411514, by decide⟩ ⟨11, 2, 0, 1411514, 102281, 3957, 262144⟩
    (by decide) selected_cut_49784

theorem selected_cut_49785 : selected 10 ⟨1411515, by decide⟩
    (prefixPartial 11 102282) = some ⟨11, 2, 0, 1411515, 102282, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102282_1411515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102282 ⟨1411515, by decide⟩ :=
  accepted_of_selected 11 102282 ⟨1411515, by decide⟩ ⟨11, 2, 0, 1411515, 102282, 5, 262144⟩
    (by decide) selected_cut_49785

theorem selected_cut_49786 : selected 10 ⟨1411591, by decide⟩
    (prefixPartial 11 102283) = some ⟨11, 2, 0, 1411591, 102283, 3381, 262144⟩ := by
  decide +kernel

theorem context_11_102283_1411591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102283 ⟨1411591, by decide⟩ :=
  accepted_of_selected 11 102283 ⟨1411591, by decide⟩ ⟨11, 2, 0, 1411591, 102283, 3381, 262144⟩
    (by decide) selected_cut_49786

theorem unmarked_context_10_25570_1411592 : frontier 11 ⟨1411592, by decide⟩
    (prefixCache 10 25570) (prefixPartial 10 25570) = false := by
  decide +kernel

theorem node_context_10_25570_1411592 : EJMOriginalGlobalDAGData.nodes 11 ⟨1411592, by decide⟩ =
    .split (coordinate 10) (![⟨1411423, by decide⟩,⟨1411514, by decide⟩,⟨1411515, by decide⟩,⟨1411591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25570_1411592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25570 ⟨1411592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25570
    ⟨1411592, by decide⟩ (by decide) (![⟨1411423, by decide⟩,⟨1411514, by decide⟩,⟨1411515, by decide⟩,⟨1411591, by decide⟩]) unmarked_context_10_25570_1411592 node_context_10_25570_1411592
  intro a
  fin_cases a
  · exact context_11_102280_1411423
  · exact context_11_102281_1411514
  · exact context_11_102282_1411515
  · exact context_11_102283_1411591

theorem selected_cut_49787 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409136) = some ⟨12, 1, 0, 1108174, 409136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409136_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409136 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409136 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409136, 1, 65536⟩
    (by decide) selected_cut_49787

theorem selected_cut_49788 : selected 9 ⟨1411625, by decide⟩
    (prefixPartial 12 409137) = some ⟨12, 2, 0, 1411625, 409137, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_409137_1411625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409137 ⟨1411625, by decide⟩ :=
  accepted_of_selected 12 409137 ⟨1411625, by decide⟩ ⟨12, 2, 0, 1411625, 409137, 1525, 65536⟩
    (by decide) selected_cut_49788

theorem selected_cut_49789 : selected 9 ⟨1411663, by decide⟩
    (prefixPartial 12 409138) = some ⟨12, 2, 0, 1411663, 409138, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_409138_1411663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409138 ⟨1411663, by decide⟩ :=
  accepted_of_selected 12 409138 ⟨1411663, by decide⟩ ⟨12, 2, 0, 1411663, 409138, 1585, 65536⟩
    (by decide) selected_cut_49789

theorem selected_cut_49790 : selected 9 ⟨1411695, by decide⟩
    (prefixPartial 12 409139) = some ⟨12, 2, 0, 1411695, 409139, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_409139_1411695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409139 ⟨1411695, by decide⟩ :=
  accepted_of_selected 12 409139 ⟨1411695, by decide⟩ ⟨12, 2, 0, 1411695, 409139, 1485, 65536⟩
    (by decide) selected_cut_49790

theorem unmarked_context_11_102284_1411696 : frontier 10 ⟨1411696, by decide⟩
    (prefixCache 11 102284) (prefixPartial 11 102284) = false := by
  decide +kernel

theorem node_context_11_102284_1411696 : EJMOriginalGlobalDAGData.nodes 10 ⟨1411696, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1411625, by decide⟩,⟨1411663, by decide⟩,⟨1411695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102284_1411696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102284 ⟨1411696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102284
    ⟨1411696, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1411625, by decide⟩,⟨1411663, by decide⟩,⟨1411695, by decide⟩]) unmarked_context_11_102284_1411696 node_context_11_102284_1411696
  intro a
  fin_cases a
  · exact context_12_409136_1108174
  · exact context_12_409137_1411625
  · exact context_12_409138_1411663
  · exact context_12_409139_1411695

theorem selected_cut_49791 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409140) = some ⟨12, 1, 0, 1108174, 409140, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409140_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409140 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409140 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409140, 1, 65536⟩
    (by decide) selected_cut_49791

theorem selected_cut_49792 : selected 9 ⟨1411725, by decide⟩
    (prefixPartial 12 409141) = some ⟨12, 2, 0, 1411725, 409141, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_409141_1411725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409141 ⟨1411725, by decide⟩ :=
  accepted_of_selected 12 409141 ⟨1411725, by decide⟩ ⟨12, 2, 0, 1411725, 409141, 1389, 65536⟩
    (by decide) selected_cut_49792

theorem selected_cut_49793 : selected 9 ⟨1411754, by decide⟩
    (prefixPartial 12 409142) = some ⟨12, 2, 0, 1411754, 409142, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_409142_1411754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409142 ⟨1411754, by decide⟩ :=
  accepted_of_selected 12 409142 ⟨1411754, by decide⟩ ⟨12, 2, 0, 1411754, 409142, 1405, 65536⟩
    (by decide) selected_cut_49793

theorem selected_cut_49794 : selected 9 ⟨1411781, by decide⟩
    (prefixPartial 12 409143) = some ⟨12, 2, 0, 1411781, 409143, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_409143_1411781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409143 ⟨1411781, by decide⟩ :=
  accepted_of_selected 12 409143 ⟨1411781, by decide⟩ ⟨12, 2, 0, 1411781, 409143, 1325, 65536⟩
    (by decide) selected_cut_49794

theorem unmarked_context_11_102285_1411782 : frontier 10 ⟨1411782, by decide⟩
    (prefixCache 11 102285) (prefixPartial 11 102285) = false := by
  decide +kernel

theorem node_context_11_102285_1411782 : EJMOriginalGlobalDAGData.nodes 10 ⟨1411782, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1411725, by decide⟩,⟨1411754, by decide⟩,⟨1411781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102285_1411782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102285 ⟨1411782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102285
    ⟨1411782, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1411725, by decide⟩,⟨1411754, by decide⟩,⟨1411781, by decide⟩]) unmarked_context_11_102285_1411782 node_context_11_102285_1411782
  intro a
  fin_cases a
  · exact context_12_409140_1108174
  · exact context_12_409141_1411725
  · exact context_12_409142_1411754
  · exact context_12_409143_1411781

theorem selected_cut_49795 : selected 10 ⟨1411828, by decide⟩
    (prefixPartial 11 102286) = some ⟨11, 2, 0, 1411828, 102286, 2205, 262144⟩ := by
  decide +kernel

theorem context_11_102286_1411828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102286 ⟨1411828, by decide⟩ :=
  accepted_of_selected 11 102286 ⟨1411828, by decide⟩ ⟨11, 2, 0, 1411828, 102286, 2205, 262144⟩
    (by decide) selected_cut_49795

theorem selected_cut_49796 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102287) = some ⟨11, 1, 0, 977886, 102287, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102287_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102287 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102287 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102287, 1, 262144⟩
    (by decide) selected_cut_49796

theorem unmarked_context_10_25571_1411829 : frontier 11 ⟨1411829, by decide⟩
    (prefixCache 10 25571) (prefixPartial 10 25571) = false := by
  decide +kernel

theorem node_context_10_25571_1411829 : EJMOriginalGlobalDAGData.nodes 11 ⟨1411829, by decide⟩ =
    .split (coordinate 10) (![⟨1411696, by decide⟩,⟨1411782, by decide⟩,⟨1411828, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25571_1411829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25571 ⟨1411829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25571
    ⟨1411829, by decide⟩ (by decide) (![⟨1411696, by decide⟩,⟨1411782, by decide⟩,⟨1411828, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25571_1411829 node_context_10_25571_1411829
  intro a
  fin_cases a
  · exact context_11_102284_1411696
  · exact context_11_102285_1411782
  · exact context_11_102286_1411828
  · exact context_11_102287_977886

theorem unmarked_context_9_6392_1411830 : frontier 12 ⟨1411830, by decide⟩
    (prefixCache 9 6392) (prefixPartial 9 6392) = false := by
  decide +kernel

theorem node_context_9_6392_1411830 : EJMOriginalGlobalDAGData.nodes 12 ⟨1411830, by decide⟩ =
    .split (coordinate 9) (![⟨1410705, by decide⟩,⟨1411231, by decide⟩,⟨1411592, by decide⟩,⟨1411829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6392_1411830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6392 ⟨1411830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6392
    ⟨1411830, by decide⟩ (by decide) (![⟨1410705, by decide⟩,⟨1411231, by decide⟩,⟨1411592, by decide⟩,⟨1411829, by decide⟩]) unmarked_context_9_6392_1411830 node_context_9_6392_1411830
  intro a
  fin_cases a
  · exact context_10_25568_1410705
  · exact context_10_25569_1411231
  · exact context_10_25570_1411592
  · exact context_10_25571_1411829

theorem selected_cut_49797 : selected 10 ⟨1411868, by decide⟩
    (prefixPartial 11 102288) = some ⟨11, 2, 0, 1411868, 102288, 1497, 262144⟩ := by
  decide +kernel

theorem context_11_102288_1411868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102288 ⟨1411868, by decide⟩ :=
  accepted_of_selected 11 102288 ⟨1411868, by decide⟩ ⟨11, 2, 0, 1411868, 102288, 1497, 262144⟩
    (by decide) selected_cut_49797

theorem selected_cut_49798 : selected 10 ⟨1411954, by decide⟩
    (prefixPartial 11 102289) = some ⟨11, 2, 0, 1411954, 102289, 3929, 262144⟩ := by
  decide +kernel

theorem context_11_102289_1411954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102289 ⟨1411954, by decide⟩ :=
  accepted_of_selected 11 102289 ⟨1411954, by decide⟩ ⟨11, 2, 0, 1411954, 102289, 3929, 262144⟩
    (by decide) selected_cut_49798

theorem selected_cut_49799 : selected 10 ⟨1411994, by decide⟩
    (prefixPartial 11 102290) = some ⟨11, 2, 0, 1411994, 102290, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_102290_1411994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102290 ⟨1411994, by decide⟩ :=
  accepted_of_selected 11 102290 ⟨1411994, by decide⟩ ⟨11, 2, 0, 1411994, 102290, 2157, 262144⟩
    (by decide) selected_cut_49799

theorem selected_cut_49800 : selected 10 ⟨1412038, by decide⟩
    (prefixPartial 11 102291) = some ⟨11, 2, 0, 1412038, 102291, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_102291_1412038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102291 ⟨1412038, by decide⟩ :=
  accepted_of_selected 11 102291 ⟨1412038, by decide⟩ ⟨11, 2, 0, 1412038, 102291, 2165, 262144⟩
    (by decide) selected_cut_49800

theorem unmarked_context_10_25572_1412039 : frontier 11 ⟨1412039, by decide⟩
    (prefixCache 10 25572) (prefixPartial 10 25572) = false := by
  decide +kernel

theorem node_context_10_25572_1412039 : EJMOriginalGlobalDAGData.nodes 11 ⟨1412039, by decide⟩ =
    .split (coordinate 10) (![⟨1411868, by decide⟩,⟨1411954, by decide⟩,⟨1411994, by decide⟩,⟨1412038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25572_1412039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25572 ⟨1412039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25572
    ⟨1412039, by decide⟩ (by decide) (![⟨1411868, by decide⟩,⟨1411954, by decide⟩,⟨1411994, by decide⟩,⟨1412038, by decide⟩]) unmarked_context_10_25572_1412039 node_context_10_25572_1412039
  intro a
  fin_cases a
  · exact context_11_102288_1411868
  · exact context_11_102289_1411954
  · exact context_11_102290_1411994
  · exact context_11_102291_1412038

theorem selected_cut_49801 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25573) = some ⟨10, 1, 0, 893098, 25573, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25573_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25573 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25573 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25573, 1, 1048576⟩
    (by decide) selected_cut_49801

theorem selected_cut_49802 : selected 10 ⟨1412107, by decide⟩
    (prefixPartial 11 102296) = some ⟨11, 2, 0, 1412107, 102296, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_102296_1412107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102296 ⟨1412107, by decide⟩ :=
  accepted_of_selected 11 102296 ⟨1412107, by decide⟩ ⟨11, 2, 0, 1412107, 102296, 2625, 262144⟩
    (by decide) selected_cut_49802

theorem selected_cut_49803 : selected 10 ⟨1412186, by decide⟩
    (prefixPartial 11 102297) = some ⟨11, 2, 0, 1412186, 102297, 3589, 262144⟩ := by
  decide +kernel

theorem context_11_102297_1412186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102297 ⟨1412186, by decide⟩ :=
  accepted_of_selected 11 102297 ⟨1412186, by decide⟩ ⟨11, 2, 0, 1412186, 102297, 3589, 262144⟩
    (by decide) selected_cut_49803

theorem selected_cut_49804 : selected 10 ⟨1412210, by decide⟩
    (prefixPartial 11 102298) = some ⟨11, 2, 0, 1412210, 102298, 313, 262144⟩ := by
  decide +kernel

theorem context_11_102298_1412210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102298 ⟨1412210, by decide⟩ :=
  accepted_of_selected 11 102298 ⟨1412210, by decide⟩ ⟨11, 2, 0, 1412210, 102298, 313, 262144⟩
    (by decide) selected_cut_49804

theorem selected_cut_49805 : selected 10 ⟨1412248, by decide⟩
    (prefixPartial 11 102299) = some ⟨11, 2, 0, 1412248, 102299, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_102299_1412248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102299 ⟨1412248, by decide⟩ :=
  accepted_of_selected 11 102299 ⟨1412248, by decide⟩ ⟨11, 2, 0, 1412248, 102299, 1825, 262144⟩
    (by decide) selected_cut_49805

theorem unmarked_context_10_25574_1412249 : frontier 11 ⟨1412249, by decide⟩
    (prefixCache 10 25574) (prefixPartial 10 25574) = false := by
  decide +kernel

theorem node_context_10_25574_1412249 : EJMOriginalGlobalDAGData.nodes 11 ⟨1412249, by decide⟩ =
    .split (coordinate 10) (![⟨1412107, by decide⟩,⟨1412186, by decide⟩,⟨1412210, by decide⟩,⟨1412248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25574_1412249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25574 ⟨1412249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25574
    ⟨1412249, by decide⟩ (by decide) (![⟨1412107, by decide⟩,⟨1412186, by decide⟩,⟨1412210, by decide⟩,⟨1412248, by decide⟩]) unmarked_context_10_25574_1412249 node_context_10_25574_1412249
  intro a
  fin_cases a
  · exact context_11_102296_1412107
  · exact context_11_102297_1412186
  · exact context_11_102298_1412210
  · exact context_11_102299_1412248

theorem selected_cut_49806 : selected 10 ⟨1412300, by decide⟩
    (prefixPartial 11 102300) = some ⟨11, 2, 0, 1412300, 102300, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_102300_1412300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102300 ⟨1412300, by decide⟩ :=
  accepted_of_selected 11 102300 ⟨1412300, by decide⟩ ⟨11, 2, 0, 1412300, 102300, 2073, 262144⟩
    (by decide) selected_cut_49806

theorem selected_cut_49807 : selected 10 ⟨1412350, by decide⟩
    (prefixPartial 11 102301) = some ⟨11, 2, 0, 1412350, 102301, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_102301_1412350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102301 ⟨1412350, by decide⟩ :=
  accepted_of_selected 11 102301 ⟨1412350, by decide⟩ ⟨11, 2, 0, 1412350, 102301, 2321, 262144⟩
    (by decide) selected_cut_49807

theorem selected_cut_49808 : selected 10 ⟨1412378, by decide⟩
    (prefixPartial 11 102302) = some ⟨11, 2, 0, 1412378, 102302, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_102302_1412378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102302 ⟨1412378, by decide⟩ :=
  accepted_of_selected 11 102302 ⟨1412378, by decide⟩ ⟨11, 2, 0, 1412378, 102302, 1461, 262144⟩
    (by decide) selected_cut_49808

theorem selected_cut_49809 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102303) = some ⟨11, 1, 0, 977886, 102303, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102303_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102303 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102303 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102303, 1, 262144⟩
    (by decide) selected_cut_49809

theorem unmarked_context_10_25575_1412379 : frontier 11 ⟨1412379, by decide⟩
    (prefixCache 10 25575) (prefixPartial 10 25575) = false := by
  decide +kernel

theorem node_context_10_25575_1412379 : EJMOriginalGlobalDAGData.nodes 11 ⟨1412379, by decide⟩ =
    .split (coordinate 10) (![⟨1412300, by decide⟩,⟨1412350, by decide⟩,⟨1412378, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25575_1412379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25575 ⟨1412379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25575
    ⟨1412379, by decide⟩ (by decide) (![⟨1412300, by decide⟩,⟨1412350, by decide⟩,⟨1412378, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25575_1412379 node_context_10_25575_1412379
  intro a
  fin_cases a
  · exact context_11_102300_1412300
  · exact context_11_102301_1412350
  · exact context_11_102302_1412378
  · exact context_11_102303_977886

theorem unmarked_context_9_6393_1412380 : frontier 12 ⟨1412380, by decide⟩
    (prefixCache 9 6393) (prefixPartial 9 6393) = false := by
  decide +kernel

theorem node_context_9_6393_1412380 : EJMOriginalGlobalDAGData.nodes 12 ⟨1412380, by decide⟩ =
    .split (coordinate 9) (![⟨1412039, by decide⟩,⟨893098, by decide⟩,⟨1412249, by decide⟩,⟨1412379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6393_1412380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6393 ⟨1412380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6393
    ⟨1412380, by decide⟩ (by decide) (![⟨1412039, by decide⟩,⟨893098, by decide⟩,⟨1412249, by decide⟩,⟨1412379, by decide⟩]) unmarked_context_9_6393_1412380 node_context_9_6393_1412380
  intro a
  fin_cases a
  · exact context_10_25572_1412039
  · exact context_10_25573_893098
  · exact context_10_25574_1412249
  · exact context_10_25575_1412379

theorem selected_cut_49810 : selected 10 ⟨1412407, by decide⟩
    (prefixPartial 11 102304) = some ⟨11, 2, 0, 1412407, 102304, 937, 262144⟩ := by
  decide +kernel

theorem context_11_102304_1412407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102304 ⟨1412407, by decide⟩ :=
  accepted_of_selected 11 102304 ⟨1412407, by decide⟩ ⟨11, 2, 0, 1412407, 102304, 937, 262144⟩
    (by decide) selected_cut_49810

theorem selected_cut_49811 : selected 10 ⟨1412440, by decide⟩
    (prefixPartial 11 102305) = some ⟨11, 2, 0, 1412440, 102305, 1469, 262144⟩ := by
  decide +kernel

theorem context_11_102305_1412440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102305 ⟨1412440, by decide⟩ :=
  accepted_of_selected 11 102305 ⟨1412440, by decide⟩ ⟨11, 2, 0, 1412440, 102305, 1469, 262144⟩
    (by decide) selected_cut_49811

theorem selected_cut_49812 : selected 10 ⟨1412477, by decide⟩
    (prefixPartial 11 102306) = some ⟨11, 2, 0, 1412477, 102306, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_102306_1412477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102306 ⟨1412477, by decide⟩ :=
  accepted_of_selected 11 102306 ⟨1412477, by decide⟩ ⟨11, 2, 0, 1412477, 102306, 1905, 262144⟩
    (by decide) selected_cut_49812

theorem selected_cut_49813 : selected 10 ⟨1412503, by decide⟩
    (prefixPartial 11 102307) = some ⟨11, 2, 0, 1412503, 102307, 1157, 262144⟩ := by
  decide +kernel

theorem context_11_102307_1412503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102307 ⟨1412503, by decide⟩ :=
  accepted_of_selected 11 102307 ⟨1412503, by decide⟩ ⟨11, 2, 0, 1412503, 102307, 1157, 262144⟩
    (by decide) selected_cut_49813

theorem unmarked_context_10_25576_1412504 : frontier 11 ⟨1412504, by decide⟩
    (prefixCache 10 25576) (prefixPartial 10 25576) = false := by
  decide +kernel

theorem node_context_10_25576_1412504 : EJMOriginalGlobalDAGData.nodes 11 ⟨1412504, by decide⟩ =
    .split (coordinate 10) (![⟨1412407, by decide⟩,⟨1412440, by decide⟩,⟨1412477, by decide⟩,⟨1412503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25576_1412504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25576 ⟨1412504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25576
    ⟨1412504, by decide⟩ (by decide) (![⟨1412407, by decide⟩,⟨1412440, by decide⟩,⟨1412477, by decide⟩,⟨1412503, by decide⟩]) unmarked_context_10_25576_1412504 node_context_10_25576_1412504
  intro a
  fin_cases a
  · exact context_11_102304_1412407
  · exact context_11_102305_1412440
  · exact context_11_102306_1412477
  · exact context_11_102307_1412503

theorem selected_cut_49814 : selected 10 ⟨1412546, by decide⟩
    (prefixPartial 11 102308) = some ⟨11, 2, 0, 1412546, 102308, 1681, 262144⟩ := by
  decide +kernel

theorem context_11_102308_1412546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102308 ⟨1412546, by decide⟩ :=
  accepted_of_selected 11 102308 ⟨1412546, by decide⟩ ⟨11, 2, 0, 1412546, 102308, 1681, 262144⟩
    (by decide) selected_cut_49814

theorem selected_cut_49815 : selected 10 ⟨1410395, by decide⟩
    (prefixPartial 11 102309) = some ⟨11, 2, 0, 1410395, 102309, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102309_1410395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102309 ⟨1410395, by decide⟩ :=
  accepted_of_selected 11 102309 ⟨1410395, by decide⟩ ⟨11, 2, 0, 1410395, 102309, 5, 262144⟩
    (by decide) selected_cut_49815

theorem selected_cut_49816 : selected 10 ⟨1412576, by decide⟩
    (prefixPartial 11 102310) = some ⟨11, 2, 0, 1412576, 102310, 1553, 262144⟩ := by
  decide +kernel

theorem context_11_102310_1412576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102310 ⟨1412576, by decide⟩ :=
  accepted_of_selected 11 102310 ⟨1412576, by decide⟩ ⟨11, 2, 0, 1412576, 102310, 1553, 262144⟩
    (by decide) selected_cut_49816

theorem selected_cut_49817 : selected 10 ⟨1412605, by decide⟩
    (prefixPartial 11 102311) = some ⟨11, 2, 0, 1412605, 102311, 1009, 262144⟩ := by
  decide +kernel

theorem context_11_102311_1412605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102311 ⟨1412605, by decide⟩ :=
  accepted_of_selected 11 102311 ⟨1412605, by decide⟩ ⟨11, 2, 0, 1412605, 102311, 1009, 262144⟩
    (by decide) selected_cut_49817

theorem unmarked_context_10_25577_1412606 : frontier 11 ⟨1412606, by decide⟩
    (prefixCache 10 25577) (prefixPartial 10 25577) = false := by
  decide +kernel

theorem node_context_10_25577_1412606 : EJMOriginalGlobalDAGData.nodes 11 ⟨1412606, by decide⟩ =
    .split (coordinate 10) (![⟨1412546, by decide⟩,⟨1410395, by decide⟩,⟨1412576, by decide⟩,⟨1412605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25577_1412606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25577 ⟨1412606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25577
    ⟨1412606, by decide⟩ (by decide) (![⟨1412546, by decide⟩,⟨1410395, by decide⟩,⟨1412576, by decide⟩,⟨1412605, by decide⟩]) unmarked_context_10_25577_1412606 node_context_10_25577_1412606
  intro a
  fin_cases a
  · exact context_11_102308_1412546
  · exact context_11_102309_1410395
  · exact context_11_102310_1412576
  · exact context_11_102311_1412605

theorem selected_cut_49818 : selected 11 ⟨1412634, by decide⟩
    (prefixPartial 10 25578) = some ⟨10, 2, 0, 1412634, 25578, 993, 1048576⟩ := by
  decide +kernel

theorem context_10_25578_1412634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25578 ⟨1412634, by decide⟩ :=
  accepted_of_selected 10 25578 ⟨1412634, by decide⟩ ⟨10, 2, 0, 1412634, 25578, 993, 1048576⟩
    (by decide) selected_cut_49818

theorem selected_cut_49819 : selected 11 ⟨1412697, by decide⟩
    (prefixPartial 10 25579) = some ⟨10, 2, 0, 1412697, 25579, 2669, 1048576⟩ := by
  decide +kernel

theorem context_10_25579_1412697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25579 ⟨1412697, by decide⟩ :=
  accepted_of_selected 10 25579 ⟨1412697, by decide⟩ ⟨10, 2, 0, 1412697, 25579, 2669, 1048576⟩
    (by decide) selected_cut_49819

theorem unmarked_context_9_6394_1412698 : frontier 12 ⟨1412698, by decide⟩
    (prefixCache 9 6394) (prefixPartial 9 6394) = false := by
  decide +kernel

theorem node_context_9_6394_1412698 : EJMOriginalGlobalDAGData.nodes 12 ⟨1412698, by decide⟩ =
    .split (coordinate 9) (![⟨1412504, by decide⟩,⟨1412606, by decide⟩,⟨1412634, by decide⟩,⟨1412697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6394_1412698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6394 ⟨1412698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6394
    ⟨1412698, by decide⟩ (by decide) (![⟨1412504, by decide⟩,⟨1412606, by decide⟩,⟨1412634, by decide⟩,⟨1412697, by decide⟩]) unmarked_context_9_6394_1412698 node_context_9_6394_1412698
  intro a
  fin_cases a
  · exact context_10_25576_1412504
  · exact context_10_25577_1412606
  · exact context_10_25578_1412634
  · exact context_10_25579_1412697

theorem selected_cut_49820 : selected 11 ⟨1412746, by decide⟩
    (prefixPartial 10 25580) = some ⟨10, 2, 0, 1412746, 25580, 2129, 1048576⟩ := by
  decide +kernel

theorem context_10_25580_1412746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25580 ⟨1412746, by decide⟩ :=
  accepted_of_selected 10 25580 ⟨1412746, by decide⟩ ⟨10, 2, 0, 1412746, 25580, 2129, 1048576⟩
    (by decide) selected_cut_49820

theorem selected_cut_49821 : selected 11 ⟨1412795, by decide⟩
    (prefixPartial 10 25581) = some ⟨10, 2, 0, 1412795, 25581, 1437, 1048576⟩ := by
  decide +kernel

theorem context_10_25581_1412795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25581 ⟨1412795, by decide⟩ :=
  accepted_of_selected 10 25581 ⟨1412795, by decide⟩ ⟨10, 2, 0, 1412795, 25581, 1437, 1048576⟩
    (by decide) selected_cut_49821

theorem selected_cut_49822 : selected 11 ⟨1412822, by decide⟩
    (prefixPartial 10 25582) = some ⟨10, 2, 0, 1412822, 25582, 705, 1048576⟩ := by
  decide +kernel

theorem context_10_25582_1412822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25582 ⟨1412822, by decide⟩ :=
  accepted_of_selected 10 25582 ⟨1412822, by decide⟩ ⟨10, 2, 0, 1412822, 25582, 705, 1048576⟩
    (by decide) selected_cut_49822

theorem selected_cut_49823 : selected 11 ⟨1410638, by decide⟩
    (prefixPartial 10 25583) = some ⟨10, 2, 0, 1410638, 25583, 21, 1048576⟩ := by
  decide +kernel

theorem context_10_25583_1410638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25583 ⟨1410638, by decide⟩ :=
  accepted_of_selected 10 25583 ⟨1410638, by decide⟩ ⟨10, 2, 0, 1410638, 25583, 21, 1048576⟩
    (by decide) selected_cut_49823

theorem unmarked_context_9_6395_1412823 : frontier 12 ⟨1412823, by decide⟩
    (prefixCache 9 6395) (prefixPartial 9 6395) = false := by
  decide +kernel

theorem node_context_9_6395_1412823 : EJMOriginalGlobalDAGData.nodes 12 ⟨1412823, by decide⟩ =
    .split (coordinate 9) (![⟨1412746, by decide⟩,⟨1412795, by decide⟩,⟨1412822, by decide⟩,⟨1410638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6395_1412823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6395 ⟨1412823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6395
    ⟨1412823, by decide⟩ (by decide) (![⟨1412746, by decide⟩,⟨1412795, by decide⟩,⟨1412822, by decide⟩,⟨1410638, by decide⟩]) unmarked_context_9_6395_1412823 node_context_9_6395_1412823
  intro a
  fin_cases a
  · exact context_10_25580_1412746
  · exact context_10_25581_1412795
  · exact context_10_25582_1412822
  · exact context_10_25583_1410638

theorem unmarked_context_8_1598_1412824 : frontier 13 ⟨1412824, by decide⟩
    (prefixCache 8 1598) (prefixPartial 8 1598) = false := by
  decide +kernel

theorem node_context_8_1598_1412824 : EJMOriginalGlobalDAGData.nodes 13 ⟨1412824, by decide⟩ =
    .split (coordinate 8) (![⟨1411830, by decide⟩,⟨1412380, by decide⟩,⟨1412698, by decide⟩,⟨1412823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1598_1412824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1598 ⟨1412824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1598
    ⟨1412824, by decide⟩ (by decide) (![⟨1411830, by decide⟩,⟨1412380, by decide⟩,⟨1412698, by decide⟩,⟨1412823, by decide⟩]) unmarked_context_8_1598_1412824 node_context_8_1598_1412824
  intro a
  fin_cases a
  · exact context_9_6392_1411830
  · exact context_9_6393_1412380
  · exact context_9_6394_1412698
  · exact context_9_6395_1412823

theorem selected_cut_49824 : selected 11 ⟨1412900, by decide⟩
    (prefixPartial 10 25584) = some ⟨10, 2, 0, 1412900, 25584, 2405, 1048576⟩ := by
  decide +kernel

theorem context_10_25584_1412900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25584 ⟨1412900, by decide⟩ :=
  accepted_of_selected 10 25584 ⟨1412900, by decide⟩ ⟨10, 2, 0, 1412900, 25584, 2405, 1048576⟩
    (by decide) selected_cut_49824

theorem selected_cut_49825 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409360) = some ⟨12, 1, 0, 1108174, 409360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409360_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409360 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409360 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409360, 1, 65536⟩
    (by decide) selected_cut_49825

theorem selected_cut_49826 : selected 9 ⟨1412980, by decide⟩
    (prefixPartial 12 409361) = some ⟨12, 2, 0, 1412980, 409361, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_409361_1412980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409361 ⟨1412980, by decide⟩ :=
  accepted_of_selected 12 409361 ⟨1412980, by decide⟩ ⟨12, 2, 0, 1412980, 409361, 2741, 65536⟩
    (by decide) selected_cut_49826

theorem selected_cut_49827 : selected 9 ⟨1413048, by decide⟩
    (prefixPartial 12 409362) = some ⟨12, 2, 0, 1413048, 409362, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_409362_1413048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409362 ⟨1413048, by decide⟩ :=
  accepted_of_selected 12 409362 ⟨1413048, by decide⟩ ⟨12, 2, 0, 1413048, 409362, 2889, 65536⟩
    (by decide) selected_cut_49827

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
