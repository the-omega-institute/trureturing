/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover381
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36676 : selected 9 ⟨973842, by decide⟩
    (prefixPartial 12 289678) = some ⟨12, 2, 0, 973842, 289678, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_289678_973842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289678 ⟨973842, by decide⟩ :=
  accepted_of_selected 12 289678 ⟨973842, by decide⟩ ⟨12, 2, 0, 973842, 289678, 1565, 65536⟩
    (by decide) selected_cut_36676

theorem selected_cut_36677 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 289679) = some ⟨12, 1, 0, 903806, 289679, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289679_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289679 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 289679 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 289679, 1, 65536⟩
    (by decide) selected_cut_36677

theorem unmarked_context_11_72419_973843 : frontier 10 ⟨973843, by decide⟩
    (prefixCache 11 72419) (prefixPartial 11 72419) = false := by
  decide +kernel

theorem node_context_11_72419_973843 : EJMOriginalGlobalDAGData.nodes 10 ⟨973843, by decide⟩ =
    .split (coordinate 11) (![⟨973788, by decide⟩,⟨973815, by decide⟩,⟨973842, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72419_973843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72419 ⟨973843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72419
    ⟨973843, by decide⟩ (by decide) (![⟨973788, by decide⟩,⟨973815, by decide⟩,⟨973842, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72419_973843 node_context_11_72419_973843
  intro a
  fin_cases a
  · exact context_12_289676_973788
  · exact context_12_289677_973815
  · exact context_12_289678_973842
  · exact context_12_289679_903806

theorem unmarked_context_10_18104_973844 : frontier 11 ⟨973844, by decide⟩
    (prefixCache 10 18104) (prefixPartial 10 18104) = false := by
  decide +kernel

theorem node_context_10_18104_973844 : EJMOriginalGlobalDAGData.nodes 11 ⟨973844, by decide⟩ =
    .split (coordinate 10) (![⟨973547, by decide⟩,⟨973649, by decide⟩,⟨973757, by decide⟩,⟨973843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18104_973844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18104 ⟨973844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18104
    ⟨973844, by decide⟩ (by decide) (![⟨973547, by decide⟩,⟨973649, by decide⟩,⟨973757, by decide⟩,⟨973843, by decide⟩]) unmarked_context_10_18104_973844 node_context_10_18104_973844
  intro a
  fin_cases a
  · exact context_11_72416_973547
  · exact context_11_72417_973649
  · exact context_11_72418_973757
  · exact context_11_72419_973843

theorem selected_cut_36678 : selected 9 ⟨973866, by decide⟩
    (prefixPartial 12 289680) = some ⟨12, 2, 0, 973866, 289680, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_289680_973866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289680 ⟨973866, by decide⟩ :=
  accepted_of_selected 12 289680 ⟨973866, by decide⟩ ⟨12, 2, 0, 973866, 289680, 1385, 65536⟩
    (by decide) selected_cut_36678

theorem selected_cut_36679 : selected 9 ⟨973889, by decide⟩
    (prefixPartial 12 289681) = some ⟨12, 2, 0, 973889, 289681, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_289681_973889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289681 ⟨973889, by decide⟩ :=
  accepted_of_selected 12 289681 ⟨973889, by decide⟩ ⟨12, 2, 0, 973889, 289681, 1473, 65536⟩
    (by decide) selected_cut_36679

theorem selected_cut_36680 : selected 9 ⟨973912, by decide⟩
    (prefixPartial 12 289682) = some ⟨12, 2, 0, 973912, 289682, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_289682_973912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289682 ⟨973912, by decide⟩ :=
  accepted_of_selected 12 289682 ⟨973912, by decide⟩ ⟨12, 2, 0, 973912, 289682, 1493, 65536⟩
    (by decide) selected_cut_36680

theorem selected_cut_36681 : selected 9 ⟨973931, by decide⟩
    (prefixPartial 12 289683) = some ⟨12, 2, 0, 973931, 289683, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_289683_973931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289683 ⟨973931, by decide⟩ :=
  accepted_of_selected 12 289683 ⟨973931, by decide⟩ ⟨12, 2, 0, 973931, 289683, 1289, 65536⟩
    (by decide) selected_cut_36681

theorem unmarked_context_11_72420_973932 : frontier 10 ⟨973932, by decide⟩
    (prefixCache 11 72420) (prefixPartial 11 72420) = false := by
  decide +kernel

theorem node_context_11_72420_973932 : EJMOriginalGlobalDAGData.nodes 10 ⟨973932, by decide⟩ =
    .split (coordinate 11) (![⟨973866, by decide⟩,⟨973889, by decide⟩,⟨973912, by decide⟩,⟨973931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72420_973932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72420 ⟨973932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72420
    ⟨973932, by decide⟩ (by decide) (![⟨973866, by decide⟩,⟨973889, by decide⟩,⟨973912, by decide⟩,⟨973931, by decide⟩]) unmarked_context_11_72420_973932 node_context_11_72420_973932
  intro a
  fin_cases a
  · exact context_12_289680_973866
  · exact context_12_289681_973889
  · exact context_12_289682_973912
  · exact context_12_289683_973931

theorem selected_cut_36682 : selected 9 ⟨973952, by decide⟩
    (prefixPartial 12 289684) = some ⟨12, 2, 0, 973952, 289684, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_289684_973952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289684 ⟨973952, by decide⟩ :=
  accepted_of_selected 12 289684 ⟨973952, by decide⟩ ⟨12, 2, 0, 973952, 289684, 1361, 65536⟩
    (by decide) selected_cut_36682

theorem selected_cut_36683 : selected 9 ⟨973973, by decide⟩
    (prefixPartial 12 289685) = some ⟨12, 2, 0, 973973, 289685, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_289685_973973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289685 ⟨973973, by decide⟩ :=
  accepted_of_selected 12 289685 ⟨973973, by decide⟩ ⟨12, 2, 0, 973973, 289685, 1277, 65536⟩
    (by decide) selected_cut_36683

theorem selected_cut_36684 : selected 9 ⟨973992, by decide⟩
    (prefixPartial 12 289686) = some ⟨12, 2, 0, 973992, 289686, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_289686_973992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289686 ⟨973992, by decide⟩ :=
  accepted_of_selected 12 289686 ⟨973992, by decide⟩ ⟨12, 2, 0, 973992, 289686, 1281, 65536⟩
    (by decide) selected_cut_36684

theorem selected_cut_36685 : selected 9 ⟨974011, by decide⟩
    (prefixPartial 12 289687) = some ⟨12, 2, 0, 974011, 289687, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_289687_974011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289687 ⟨974011, by decide⟩ :=
  accepted_of_selected 12 289687 ⟨974011, by decide⟩ ⟨12, 2, 0, 974011, 289687, 1261, 65536⟩
    (by decide) selected_cut_36685

theorem unmarked_context_11_72421_974012 : frontier 10 ⟨974012, by decide⟩
    (prefixCache 11 72421) (prefixPartial 11 72421) = false := by
  decide +kernel

theorem node_context_11_72421_974012 : EJMOriginalGlobalDAGData.nodes 10 ⟨974012, by decide⟩ =
    .split (coordinate 11) (![⟨973952, by decide⟩,⟨973973, by decide⟩,⟨973992, by decide⟩,⟨974011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72421_974012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72421 ⟨974012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72421
    ⟨974012, by decide⟩ (by decide) (![⟨973952, by decide⟩,⟨973973, by decide⟩,⟨973992, by decide⟩,⟨974011, by decide⟩]) unmarked_context_11_72421_974012 node_context_11_72421_974012
  intro a
  fin_cases a
  · exact context_12_289684_973952
  · exact context_12_289685_973973
  · exact context_12_289686_973992
  · exact context_12_289687_974011

theorem selected_cut_36686 : selected 9 ⟨974034, by decide⟩
    (prefixPartial 12 289688) = some ⟨12, 2, 0, 974034, 289688, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_289688_974034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289688 ⟨974034, by decide⟩ :=
  accepted_of_selected 12 289688 ⟨974034, by decide⟩ ⟨12, 2, 0, 974034, 289688, 1285, 65536⟩
    (by decide) selected_cut_36686

theorem selected_cut_36687 : selected 9 ⟨974052, by decide⟩
    (prefixPartial 12 289689) = some ⟨12, 2, 0, 974052, 289689, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_289689_974052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289689 ⟨974052, by decide⟩ :=
  accepted_of_selected 12 289689 ⟨974052, by decide⟩ ⟨12, 2, 0, 974052, 289689, 1185, 65536⟩
    (by decide) selected_cut_36687

theorem selected_cut_36688 : selected 9 ⟨974068, by decide⟩
    (prefixPartial 12 289690) = some ⟨12, 2, 0, 974068, 289690, 1061, 65536⟩ := by
  decide +kernel

theorem context_12_289690_974068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289690 ⟨974068, by decide⟩ :=
  accepted_of_selected 12 289690 ⟨974068, by decide⟩ ⟨12, 2, 0, 974068, 289690, 1061, 65536⟩
    (by decide) selected_cut_36688

theorem selected_cut_36689 : selected 9 ⟨974087, by decide⟩
    (prefixPartial 12 289691) = some ⟨12, 2, 0, 974087, 289691, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_289691_974087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289691 ⟨974087, by decide⟩ :=
  accepted_of_selected 12 289691 ⟨974087, by decide⟩ ⟨12, 2, 0, 974087, 289691, 1121, 65536⟩
    (by decide) selected_cut_36689

theorem unmarked_context_11_72422_974088 : frontier 10 ⟨974088, by decide⟩
    (prefixCache 11 72422) (prefixPartial 11 72422) = false := by
  decide +kernel

theorem node_context_11_72422_974088 : EJMOriginalGlobalDAGData.nodes 10 ⟨974088, by decide⟩ =
    .split (coordinate 11) (![⟨974034, by decide⟩,⟨974052, by decide⟩,⟨974068, by decide⟩,⟨974087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72422_974088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72422 ⟨974088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72422
    ⟨974088, by decide⟩ (by decide) (![⟨974034, by decide⟩,⟨974052, by decide⟩,⟨974068, by decide⟩,⟨974087, by decide⟩]) unmarked_context_11_72422_974088 node_context_11_72422_974088
  intro a
  fin_cases a
  · exact context_12_289688_974034
  · exact context_12_289689_974052
  · exact context_12_289690_974068
  · exact context_12_289691_974087

theorem selected_cut_36690 : selected 10 ⟨974136, by decide⟩
    (prefixPartial 11 72423) = some ⟨11, 2, 0, 974136, 72423, 3485, 262144⟩ := by
  decide +kernel

theorem context_11_72423_974136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72423 ⟨974136, by decide⟩ :=
  accepted_of_selected 11 72423 ⟨974136, by decide⟩ ⟨11, 2, 0, 974136, 72423, 3485, 262144⟩
    (by decide) selected_cut_36690

theorem unmarked_context_10_18105_974137 : frontier 11 ⟨974137, by decide⟩
    (prefixCache 10 18105) (prefixPartial 10 18105) = false := by
  decide +kernel

theorem node_context_10_18105_974137 : EJMOriginalGlobalDAGData.nodes 11 ⟨974137, by decide⟩ =
    .split (coordinate 10) (![⟨973932, by decide⟩,⟨974012, by decide⟩,⟨974088, by decide⟩,⟨974136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18105_974137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18105 ⟨974137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18105
    ⟨974137, by decide⟩ (by decide) (![⟨973932, by decide⟩,⟨974012, by decide⟩,⟨974088, by decide⟩,⟨974136, by decide⟩]) unmarked_context_10_18105_974137 node_context_10_18105_974137
  intro a
  fin_cases a
  · exact context_11_72420_973932
  · exact context_11_72421_974012
  · exact context_11_72422_974088
  · exact context_11_72423_974136

theorem selected_cut_36691 : selected 10 ⟨974177, by decide⟩
    (prefixPartial 11 72424) = some ⟨11, 2, 0, 974177, 72424, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_72424_974177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72424 ⟨974177, by decide⟩ :=
  accepted_of_selected 11 72424 ⟨974177, by decide⟩ ⟨11, 2, 0, 974177, 72424, 2897, 262144⟩
    (by decide) selected_cut_36691

theorem selected_cut_36692 : selected 10 ⟨974223, by decide⟩
    (prefixPartial 11 72425) = some ⟨11, 2, 0, 974223, 72425, 3029, 262144⟩ := by
  decide +kernel

theorem context_11_72425_974223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72425 ⟨974223, by decide⟩ :=
  accepted_of_selected 11 72425 ⟨974223, by decide⟩ ⟨11, 2, 0, 974223, 72425, 3029, 262144⟩
    (by decide) selected_cut_36692

theorem selected_cut_36693 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 72426) = some ⟨11, 1, 0, 906566, 72426, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72426_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72426 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 72426 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 72426, 1, 262144⟩
    (by decide) selected_cut_36693

theorem selected_cut_36694 : selected 10 ⟨974259, by decide⟩
    (prefixPartial 11 72427) = some ⟨11, 2, 0, 974259, 72427, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_72427_974259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72427 ⟨974259, by decide⟩ :=
  accepted_of_selected 11 72427 ⟨974259, by decide⟩ ⟨11, 2, 0, 974259, 72427, 2169, 262144⟩
    (by decide) selected_cut_36694

theorem unmarked_context_10_18106_974260 : frontier 11 ⟨974260, by decide⟩
    (prefixCache 10 18106) (prefixPartial 10 18106) = false := by
  decide +kernel

theorem node_context_10_18106_974260 : EJMOriginalGlobalDAGData.nodes 11 ⟨974260, by decide⟩ =
    .split (coordinate 10) (![⟨974177, by decide⟩,⟨974223, by decide⟩,⟨906566, by decide⟩,⟨974259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18106_974260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18106 ⟨974260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18106
    ⟨974260, by decide⟩ (by decide) (![⟨974177, by decide⟩,⟨974223, by decide⟩,⟨906566, by decide⟩,⟨974259, by decide⟩]) unmarked_context_10_18106_974260 node_context_10_18106_974260
  intro a
  fin_cases a
  · exact context_11_72424_974177
  · exact context_11_72425_974223
  · exact context_11_72426_906566
  · exact context_11_72427_974259

theorem selected_cut_36695 : selected 9 ⟨974273, by decide⟩
    (prefixPartial 12 289712) = some ⟨12, 2, 0, 974273, 289712, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_289712_974273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289712 ⟨974273, by decide⟩ :=
  accepted_of_selected 12 289712 ⟨974273, by decide⟩ ⟨12, 2, 0, 974273, 289712, 1085, 65536⟩
    (by decide) selected_cut_36695

theorem selected_cut_36696 : selected 9 ⟨974296, by decide⟩
    (prefixPartial 12 289713) = some ⟨12, 2, 0, 974296, 289713, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_289713_974296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289713 ⟨974296, by decide⟩ :=
  accepted_of_selected 12 289713 ⟨974296, by decide⟩ ⟨12, 2, 0, 974296, 289713, 1281, 65536⟩
    (by decide) selected_cut_36696

theorem selected_cut_36697 : selected 9 ⟨974321, by decide⟩
    (prefixPartial 12 289714) = some ⟨12, 2, 0, 974321, 289714, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_289714_974321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289714 ⟨974321, by decide⟩ :=
  accepted_of_selected 12 289714 ⟨974321, by decide⟩ ⟨12, 2, 0, 974321, 289714, 1197, 65536⟩
    (by decide) selected_cut_36697

theorem selected_cut_36698 : selected 9 ⟨974336, by decide⟩
    (prefixPartial 12 289715) = some ⟨12, 2, 0, 974336, 289715, 985, 65536⟩ := by
  decide +kernel

theorem context_12_289715_974336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289715 ⟨974336, by decide⟩ :=
  accepted_of_selected 12 289715 ⟨974336, by decide⟩ ⟨12, 2, 0, 974336, 289715, 985, 65536⟩
    (by decide) selected_cut_36698

theorem unmarked_context_11_72428_974337 : frontier 10 ⟨974337, by decide⟩
    (prefixCache 11 72428) (prefixPartial 11 72428) = false := by
  decide +kernel

theorem node_context_11_72428_974337 : EJMOriginalGlobalDAGData.nodes 10 ⟨974337, by decide⟩ =
    .split (coordinate 11) (![⟨974273, by decide⟩,⟨974296, by decide⟩,⟨974321, by decide⟩,⟨974336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72428_974337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72428 ⟨974337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72428
    ⟨974337, by decide⟩ (by decide) (![⟨974273, by decide⟩,⟨974296, by decide⟩,⟨974321, by decide⟩,⟨974336, by decide⟩]) unmarked_context_11_72428_974337 node_context_11_72428_974337
  intro a
  fin_cases a
  · exact context_12_289712_974273
  · exact context_12_289713_974296
  · exact context_12_289714_974321
  · exact context_12_289715_974336

theorem selected_cut_36699 : selected 10 ⟨974397, by decide⟩
    (prefixPartial 11 72429) = some ⟨11, 2, 0, 974397, 72429, 3897, 262144⟩ := by
  decide +kernel

theorem context_11_72429_974397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72429 ⟨974397, by decide⟩ :=
  accepted_of_selected 11 72429 ⟨974397, by decide⟩ ⟨11, 2, 0, 974397, 72429, 3897, 262144⟩
    (by decide) selected_cut_36699

theorem selected_cut_36700 : selected 10 ⟨974457, by decide⟩
    (prefixPartial 11 72430) = some ⟨11, 2, 0, 974457, 72430, 4001, 262144⟩ := by
  decide +kernel

theorem context_11_72430_974457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72430 ⟨974457, by decide⟩ :=
  accepted_of_selected 11 72430 ⟨974457, by decide⟩ ⟨11, 2, 0, 974457, 72430, 4001, 262144⟩
    (by decide) selected_cut_36700

theorem selected_cut_36701 : selected 10 ⟨974504, by decide⟩
    (prefixPartial 11 72431) = some ⟨11, 2, 0, 974504, 72431, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_72431_974504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72431 ⟨974504, by decide⟩ :=
  accepted_of_selected 11 72431 ⟨974504, by decide⟩ ⟨11, 2, 0, 974504, 72431, 2817, 262144⟩
    (by decide) selected_cut_36701

theorem unmarked_context_10_18107_974505 : frontier 11 ⟨974505, by decide⟩
    (prefixCache 10 18107) (prefixPartial 10 18107) = false := by
  decide +kernel

theorem node_context_10_18107_974505 : EJMOriginalGlobalDAGData.nodes 11 ⟨974505, by decide⟩ =
    .split (coordinate 10) (![⟨974337, by decide⟩,⟨974397, by decide⟩,⟨974457, by decide⟩,⟨974504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18107_974505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18107 ⟨974505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18107
    ⟨974505, by decide⟩ (by decide) (![⟨974337, by decide⟩,⟨974397, by decide⟩,⟨974457, by decide⟩,⟨974504, by decide⟩]) unmarked_context_10_18107_974505 node_context_10_18107_974505
  intro a
  fin_cases a
  · exact context_11_72428_974337
  · exact context_11_72429_974397
  · exact context_11_72430_974457
  · exact context_11_72431_974504

theorem unmarked_context_9_4526_974506 : frontier 12 ⟨974506, by decide⟩
    (prefixCache 9 4526) (prefixPartial 9 4526) = false := by
  decide +kernel

theorem node_context_9_4526_974506 : EJMOriginalGlobalDAGData.nodes 12 ⟨974506, by decide⟩ =
    .split (coordinate 9) (![⟨973844, by decide⟩,⟨974137, by decide⟩,⟨974260, by decide⟩,⟨974505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4526_974506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4526 ⟨974506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4526
    ⟨974506, by decide⟩ (by decide) (![⟨973844, by decide⟩,⟨974137, by decide⟩,⟨974260, by decide⟩,⟨974505, by decide⟩]) unmarked_context_9_4526_974506 node_context_9_4526_974506
  intro a
  fin_cases a
  · exact context_10_18104_973844
  · exact context_10_18105_974137
  · exact context_10_18106_974260
  · exact context_10_18107_974505

theorem selected_cut_36702 : selected 10 ⟨974541, by decide⟩
    (prefixPartial 11 72432) = some ⟨11, 2, 0, 974541, 72432, 2457, 262144⟩ := by
  decide +kernel

theorem context_11_72432_974541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72432 ⟨974541, by decide⟩ :=
  accepted_of_selected 11 72432 ⟨974541, by decide⟩ ⟨11, 2, 0, 974541, 72432, 2457, 262144⟩
    (by decide) selected_cut_36702

theorem selected_cut_36703 : selected 10 ⟨974572, by decide⟩
    (prefixPartial 11 72433) = some ⟨11, 2, 0, 974572, 72433, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_72433_974572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72433 ⟨974572, by decide⟩ :=
  accepted_of_selected 11 72433 ⟨974572, by decide⟩ ⟨11, 2, 0, 974572, 72433, 2237, 262144⟩
    (by decide) selected_cut_36703

theorem selected_cut_36704 : selected 10 ⟨974612, by decide⟩
    (prefixPartial 11 72434) = some ⟨11, 2, 0, 974612, 72434, 2349, 262144⟩ := by
  decide +kernel

theorem context_11_72434_974612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72434 ⟨974612, by decide⟩ :=
  accepted_of_selected 11 72434 ⟨974612, by decide⟩ ⟨11, 2, 0, 974612, 72434, 2349, 262144⟩
    (by decide) selected_cut_36704

theorem selected_cut_36705 : selected 10 ⟨974656, by decide⟩
    (prefixPartial 11 72435) = some ⟨11, 2, 0, 974656, 72435, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_72435_974656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72435 ⟨974656, by decide⟩ :=
  accepted_of_selected 11 72435 ⟨974656, by decide⟩ ⟨11, 2, 0, 974656, 72435, 1801, 262144⟩
    (by decide) selected_cut_36705

theorem unmarked_context_10_18108_974657 : frontier 11 ⟨974657, by decide⟩
    (prefixCache 10 18108) (prefixPartial 10 18108) = false := by
  decide +kernel

theorem node_context_10_18108_974657 : EJMOriginalGlobalDAGData.nodes 11 ⟨974657, by decide⟩ =
    .split (coordinate 10) (![⟨974541, by decide⟩,⟨974572, by decide⟩,⟨974612, by decide⟩,⟨974656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18108_974657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18108 ⟨974657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18108
    ⟨974657, by decide⟩ (by decide) (![⟨974541, by decide⟩,⟨974572, by decide⟩,⟨974612, by decide⟩,⟨974656, by decide⟩]) unmarked_context_10_18108_974657 node_context_10_18108_974657
  intro a
  fin_cases a
  · exact context_11_72432_974541
  · exact context_11_72433_974572
  · exact context_11_72434_974612
  · exact context_11_72435_974656

theorem selected_cut_36706 : selected 10 ⟨974682, by decide⟩
    (prefixPartial 11 72436) = some ⟨11, 2, 0, 974682, 72436, 1865, 262144⟩ := by
  decide +kernel

theorem context_11_72436_974682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72436 ⟨974682, by decide⟩ :=
  accepted_of_selected 11 72436 ⟨974682, by decide⟩ ⟨11, 2, 0, 974682, 72436, 1865, 262144⟩
    (by decide) selected_cut_36706

theorem selected_cut_36707 : selected 10 ⟨974707, by decide⟩
    (prefixPartial 11 72437) = some ⟨11, 2, 0, 974707, 72437, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_72437_974707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72437 ⟨974707, by decide⟩ :=
  accepted_of_selected 11 72437 ⟨974707, by decide⟩ ⟨11, 2, 0, 974707, 72437, 1673, 262144⟩
    (by decide) selected_cut_36707

theorem selected_cut_36708 : selected 10 ⟨974727, by decide⟩
    (prefixPartial 11 72438) = some ⟨11, 2, 0, 974727, 72438, 1433, 262144⟩ := by
  decide +kernel

theorem context_11_72438_974727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72438 ⟨974727, by decide⟩ :=
  accepted_of_selected 11 72438 ⟨974727, by decide⟩ ⟨11, 2, 0, 974727, 72438, 1433, 262144⟩
    (by decide) selected_cut_36708

theorem selected_cut_36709 : selected 10 ⟨974745, by decide⟩
    (prefixPartial 11 72439) = some ⟨11, 2, 0, 974745, 72439, 1061, 262144⟩ := by
  decide +kernel

theorem context_11_72439_974745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72439 ⟨974745, by decide⟩ :=
  accepted_of_selected 11 72439 ⟨974745, by decide⟩ ⟨11, 2, 0, 974745, 72439, 1061, 262144⟩
    (by decide) selected_cut_36709

theorem unmarked_context_10_18109_974746 : frontier 11 ⟨974746, by decide⟩
    (prefixCache 10 18109) (prefixPartial 10 18109) = false := by
  decide +kernel

theorem node_context_10_18109_974746 : EJMOriginalGlobalDAGData.nodes 11 ⟨974746, by decide⟩ =
    .split (coordinate 10) (![⟨974682, by decide⟩,⟨974707, by decide⟩,⟨974727, by decide⟩,⟨974745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18109_974746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18109 ⟨974746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18109
    ⟨974746, by decide⟩ (by decide) (![⟨974682, by decide⟩,⟨974707, by decide⟩,⟨974727, by decide⟩,⟨974745, by decide⟩]) unmarked_context_10_18109_974746 node_context_10_18109_974746
  intro a
  fin_cases a
  · exact context_11_72436_974682
  · exact context_11_72437_974707
  · exact context_11_72438_974727
  · exact context_11_72439_974745

theorem selected_cut_36710 : selected 11 ⟨974798, by decide⟩
    (prefixPartial 10 18110) = some ⟨10, 2, 0, 974798, 18110, 2637, 1048576⟩ := by
  decide +kernel

theorem context_10_18110_974798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18110 ⟨974798, by decide⟩ :=
  accepted_of_selected 10 18110 ⟨974798, by decide⟩ ⟨10, 2, 0, 974798, 18110, 2637, 1048576⟩
    (by decide) selected_cut_36710

theorem selected_cut_36711 : selected 11 ⟨974842, by decide⟩
    (prefixPartial 10 18111) = some ⟨10, 2, 0, 974842, 18111, 1049, 1048576⟩ := by
  decide +kernel

theorem context_10_18111_974842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18111 ⟨974842, by decide⟩ :=
  accepted_of_selected 10 18111 ⟨974842, by decide⟩ ⟨10, 2, 0, 974842, 18111, 1049, 1048576⟩
    (by decide) selected_cut_36711

theorem unmarked_context_9_4527_974843 : frontier 12 ⟨974843, by decide⟩
    (prefixCache 9 4527) (prefixPartial 9 4527) = false := by
  decide +kernel

theorem node_context_9_4527_974843 : EJMOriginalGlobalDAGData.nodes 12 ⟨974843, by decide⟩ =
    .split (coordinate 9) (![⟨974657, by decide⟩,⟨974746, by decide⟩,⟨974798, by decide⟩,⟨974842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4527_974843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4527 ⟨974843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4527
    ⟨974843, by decide⟩ (by decide) (![⟨974657, by decide⟩,⟨974746, by decide⟩,⟨974798, by decide⟩,⟨974842, by decide⟩]) unmarked_context_9_4527_974843 node_context_9_4527_974843
  intro a
  fin_cases a
  · exact context_10_18108_974657
  · exact context_10_18109_974746
  · exact context_10_18110_974798
  · exact context_10_18111_974842

theorem unmarked_context_8_1131_974844 : frontier 13 ⟨974844, by decide⟩
    (prefixCache 8 1131) (prefixPartial 8 1131) = false := by
  decide +kernel

theorem node_context_8_1131_974844 : EJMOriginalGlobalDAGData.nodes 13 ⟨974844, by decide⟩ =
    .split (coordinate 8) (![⟨972439, by decide⟩,⟨973452, by decide⟩,⟨974506, by decide⟩,⟨974843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1131_974844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1131 ⟨974844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1131
    ⟨974844, by decide⟩ (by decide) (![⟨972439, by decide⟩,⟨973452, by decide⟩,⟨974506, by decide⟩,⟨974843, by decide⟩]) unmarked_context_8_1131_974844 node_context_8_1131_974844
  intro a
  fin_cases a
  · exact context_9_4524_972439
  · exact context_9_4525_973452
  · exact context_9_4526_974506
  · exact context_9_4527_974843

theorem unmarked_context_7_282_974845 : frontier 14 ⟨974845, by decide⟩
    (prefixCache 7 282) (prefixPartial 7 282) = false := by
  decide +kernel

theorem node_context_7_282_974845 : EJMOriginalGlobalDAGData.nodes 14 ⟨974845, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨969559, by decide⟩,⟨974844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_282_974845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 282 ⟨974845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 282
    ⟨974845, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨969559, by decide⟩,⟨974844, by decide⟩]) unmarked_context_7_282_974845 node_context_7_282_974845
  intro a
  fin_cases a
  · exact context_8_1128_14300
  · exact context_8_1129_14300
  · exact context_8_1130_969559
  · exact context_8_1131_974844

theorem selected_cut_36712 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1132) = some ⟨8, 1, 0, 14300, 1132, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1132_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1132 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1132 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1132, 1, 16777216⟩
    (by decide) selected_cut_36712

theorem selected_cut_36713 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1133) = some ⟨8, 1, 0, 14300, 1133, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1133_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1133 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1133 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1133, 1, 16777216⟩
    (by decide) selected_cut_36713

theorem selected_cut_36714 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1134) = some ⟨8, 1, 0, 14300, 1134, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1134_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1134 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1134 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1134, 1, 16777216⟩
    (by decide) selected_cut_36714

theorem selected_cut_36715 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 290560) = some ⟨12, 1, 0, 34034, 290560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290560_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290560 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 290560 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 290560, 1, 65536⟩
    (by decide) selected_cut_36715

theorem selected_cut_36716 : selected 9 ⟨975032, by decide⟩
    (prefixPartial 12 290561) = some ⟨12, 2, 0, 975032, 290561, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_290561_975032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290561 ⟨975032, by decide⟩ :=
  accepted_of_selected 12 290561 ⟨975032, by decide⟩ ⟨12, 2, 0, 975032, 290561, 3893, 65536⟩
    (by decide) selected_cut_36716

theorem selected_cut_36717 : selected 8 ⟨975083, by decide⟩
    (prefixPartial 13 1162248) = some ⟨13, 2, 0, 975083, 1162248, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_1162248_975083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162248 ⟨975083, by decide⟩ :=
  accepted_of_selected 13 1162248 ⟨975083, by decide⟩ ⟨13, 2, 0, 975083, 1162248, 1765, 16384⟩
    (by decide) selected_cut_36717

theorem selected_cut_36718 : selected 8 ⟨975112, by decide⟩
    (prefixPartial 13 1162249) = some ⟨13, 2, 0, 975112, 1162249, 889, 16384⟩ := by
  decide +kernel

theorem context_13_1162249_975112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162249 ⟨975112, by decide⟩ :=
  accepted_of_selected 13 1162249 ⟨975112, by decide⟩ ⟨13, 2, 0, 975112, 1162249, 889, 16384⟩
    (by decide) selected_cut_36718

theorem selected_cut_36719 : selected 8 ⟨975140, by decide⟩
    (prefixPartial 13 1162250) = some ⟨13, 2, 0, 975140, 1162250, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_1162250_975140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162250 ⟨975140, by decide⟩ :=
  accepted_of_selected 13 1162250 ⟨975140, by decide⟩ ⟨13, 2, 0, 975140, 1162250, 1013, 16384⟩
    (by decide) selected_cut_36719

theorem selected_cut_36720 : selected 8 ⟨975164, by decide⟩
    (prefixPartial 13 1162251) = some ⟨13, 2, 0, 975164, 1162251, 545, 16384⟩ := by
  decide +kernel

theorem context_13_1162251_975164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162251 ⟨975164, by decide⟩ :=
  accepted_of_selected 13 1162251 ⟨975164, by decide⟩ ⟨13, 2, 0, 975164, 1162251, 545, 16384⟩
    (by decide) selected_cut_36720

theorem unmarked_context_12_290562_975165 : frontier 9 ⟨975165, by decide⟩
    (prefixCache 12 290562) (prefixPartial 12 290562) = false := by
  decide +kernel

theorem node_context_12_290562_975165 : EJMOriginalGlobalDAGData.nodes 9 ⟨975165, by decide⟩ =
    .split (coordinate 12) (![⟨975083, by decide⟩,⟨975112, by decide⟩,⟨975140, by decide⟩,⟨975164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_290562_975165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290562 ⟨975165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 290562
    ⟨975165, by decide⟩ (by decide) (![⟨975083, by decide⟩,⟨975112, by decide⟩,⟨975140, by decide⟩,⟨975164, by decide⟩]) unmarked_context_12_290562_975165 node_context_12_290562_975165
  intro a
  fin_cases a
  · exact context_13_1162248_975083
  · exact context_13_1162249_975112
  · exact context_13_1162250_975140
  · exact context_13_1162251_975164

theorem selected_cut_36721 : selected 8 ⟨975207, by decide⟩
    (prefixPartial 13 1162252) = some ⟨13, 2, 0, 975207, 1162252, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_1162252_975207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162252 ⟨975207, by decide⟩ :=
  accepted_of_selected 13 1162252 ⟨975207, by decide⟩ ⟨13, 2, 0, 975207, 1162252, 1637, 16384⟩
    (by decide) selected_cut_36721

theorem selected_cut_36722 : selected 8 ⟨975235, by decide⟩
    (prefixPartial 13 1162253) = some ⟨13, 2, 0, 975235, 1162253, 913, 16384⟩ := by
  decide +kernel

theorem context_13_1162253_975235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162253 ⟨975235, by decide⟩ :=
  accepted_of_selected 13 1162253 ⟨975235, by decide⟩ ⟨13, 2, 0, 975235, 1162253, 913, 16384⟩
    (by decide) selected_cut_36722

theorem selected_cut_36723 : selected 8 ⟨975271, by decide⟩
    (prefixPartial 13 1162254) = some ⟨13, 2, 0, 975271, 1162254, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_1162254_975271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162254 ⟨975271, by decide⟩ :=
  accepted_of_selected 13 1162254 ⟨975271, by decide⟩ ⟨13, 2, 0, 975271, 1162254, 1117, 16384⟩
    (by decide) selected_cut_36723

theorem selected_cut_36724 : selected 8 ⟨975286, by decide⟩
    (prefixPartial 13 1162255) = some ⟨13, 2, 0, 975286, 1162255, 561, 16384⟩ := by
  decide +kernel

theorem context_13_1162255_975286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162255 ⟨975286, by decide⟩ :=
  accepted_of_selected 13 1162255 ⟨975286, by decide⟩ ⟨13, 2, 0, 975286, 1162255, 561, 16384⟩
    (by decide) selected_cut_36724

theorem unmarked_context_12_290563_975287 : frontier 9 ⟨975287, by decide⟩
    (prefixCache 12 290563) (prefixPartial 12 290563) = false := by
  decide +kernel

theorem node_context_12_290563_975287 : EJMOriginalGlobalDAGData.nodes 9 ⟨975287, by decide⟩ =
    .split (coordinate 12) (![⟨975207, by decide⟩,⟨975235, by decide⟩,⟨975271, by decide⟩,⟨975286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_290563_975287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290563 ⟨975287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 290563
    ⟨975287, by decide⟩ (by decide) (![⟨975207, by decide⟩,⟨975235, by decide⟩,⟨975271, by decide⟩,⟨975286, by decide⟩]) unmarked_context_12_290563_975287 node_context_12_290563_975287
  intro a
  fin_cases a
  · exact context_13_1162252_975207
  · exact context_13_1162253_975235
  · exact context_13_1162254_975271
  · exact context_13_1162255_975286

theorem unmarked_context_11_72640_975288 : frontier 10 ⟨975288, by decide⟩
    (prefixCache 11 72640) (prefixPartial 11 72640) = false := by
  decide +kernel

theorem node_context_11_72640_975288 : EJMOriginalGlobalDAGData.nodes 10 ⟨975288, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨975032, by decide⟩,⟨975165, by decide⟩,⟨975287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72640_975288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72640 ⟨975288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72640
    ⟨975288, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨975032, by decide⟩,⟨975165, by decide⟩,⟨975287, by decide⟩]) unmarked_context_11_72640_975288 node_context_11_72640_975288
  intro a
  fin_cases a
  · exact context_12_290560_34034
  · exact context_12_290561_975032
  · exact context_12_290562_975165
  · exact context_12_290563_975287

theorem selected_cut_36725 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 290564) = some ⟨12, 1, 0, 34034, 290564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290564_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290564 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 290564 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 290564, 1, 65536⟩
    (by decide) selected_cut_36725

theorem selected_cut_36726 : selected 9 ⟨975421, by decide⟩
    (prefixPartial 12 290565) = some ⟨12, 2, 0, 975421, 290565, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_290565_975421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290565 ⟨975421, by decide⟩ :=
  accepted_of_selected 12 290565 ⟨975421, by decide⟩ ⟨12, 2, 0, 975421, 290565, 4037, 65536⟩
    (by decide) selected_cut_36726

theorem selected_cut_36727 : selected 9 ⟨975538, by decide⟩
    (prefixPartial 12 290566) = some ⟨12, 2, 0, 975538, 290566, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_290566_975538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290566 ⟨975538, by decide⟩ :=
  accepted_of_selected 12 290566 ⟨975538, by decide⟩ ⟨12, 2, 0, 975538, 290566, 4021, 65536⟩
    (by decide) selected_cut_36727

theorem selected_cut_36728 : selected 8 ⟨975580, by decide⟩
    (prefixPartial 13 1162268) = some ⟨13, 2, 0, 975580, 1162268, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_1162268_975580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162268 ⟨975580, by decide⟩ :=
  accepted_of_selected 13 1162268 ⟨975580, by decide⟩ ⟨13, 2, 0, 975580, 1162268, 1633, 16384⟩
    (by decide) selected_cut_36728

theorem selected_cut_36729 : selected 8 ⟨975605, by decide⟩
    (prefixPartial 13 1162269) = some ⟨13, 2, 0, 975605, 1162269, 797, 16384⟩ := by
  decide +kernel

theorem context_13_1162269_975605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162269 ⟨975605, by decide⟩ :=
  accepted_of_selected 13 1162269 ⟨975605, by decide⟩ ⟨13, 2, 0, 975605, 1162269, 797, 16384⟩
    (by decide) selected_cut_36729

theorem selected_cut_36730 : selected 8 ⟨975644, by decide⟩
    (prefixPartial 13 1162270) = some ⟨13, 2, 0, 975644, 1162270, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_1162270_975644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162270 ⟨975644, by decide⟩ :=
  accepted_of_selected 13 1162270 ⟨975644, by decide⟩ ⟨13, 2, 0, 975644, 1162270, 1321, 16384⟩
    (by decide) selected_cut_36730

theorem selected_cut_36731 : selected 8 ⟨975667, by decide⟩
    (prefixPartial 13 1162271) = some ⟨13, 2, 0, 975667, 1162271, 649, 16384⟩ := by
  decide +kernel

theorem context_13_1162271_975667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162271 ⟨975667, by decide⟩ :=
  accepted_of_selected 13 1162271 ⟨975667, by decide⟩ ⟨13, 2, 0, 975667, 1162271, 649, 16384⟩
    (by decide) selected_cut_36731

theorem unmarked_context_12_290567_975668 : frontier 9 ⟨975668, by decide⟩
    (prefixCache 12 290567) (prefixPartial 12 290567) = false := by
  decide +kernel

theorem node_context_12_290567_975668 : EJMOriginalGlobalDAGData.nodes 9 ⟨975668, by decide⟩ =
    .split (coordinate 12) (![⟨975580, by decide⟩,⟨975605, by decide⟩,⟨975644, by decide⟩,⟨975667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_290567_975668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290567 ⟨975668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 290567
    ⟨975668, by decide⟩ (by decide) (![⟨975580, by decide⟩,⟨975605, by decide⟩,⟨975644, by decide⟩,⟨975667, by decide⟩]) unmarked_context_12_290567_975668 node_context_12_290567_975668
  intro a
  fin_cases a
  · exact context_13_1162268_975580
  · exact context_13_1162269_975605
  · exact context_13_1162270_975644
  · exact context_13_1162271_975667

theorem unmarked_context_11_72641_975669 : frontier 10 ⟨975669, by decide⟩
    (prefixCache 11 72641) (prefixPartial 11 72641) = false := by
  decide +kernel

theorem node_context_11_72641_975669 : EJMOriginalGlobalDAGData.nodes 10 ⟨975669, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨975421, by decide⟩,⟨975538, by decide⟩,⟨975668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72641_975669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72641 ⟨975669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72641
    ⟨975669, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨975421, by decide⟩,⟨975538, by decide⟩,⟨975668, by decide⟩]) unmarked_context_11_72641_975669 node_context_11_72641_975669
  intro a
  fin_cases a
  · exact context_12_290564_34034
  · exact context_12_290565_975421
  · exact context_12_290566_975538
  · exact context_12_290567_975668

theorem selected_cut_36732 : selected 9 ⟨975816, by decide⟩
    (prefixPartial 12 290568) = some ⟨12, 2, 0, 975816, 290568, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_290568_975816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290568 ⟨975816, by decide⟩ :=
  accepted_of_selected 12 290568 ⟨975816, by decide⟩ ⟨12, 2, 0, 975816, 290568, 3121, 65536⟩
    (by decide) selected_cut_36732

theorem selected_cut_36733 : selected 9 ⟨975924, by decide⟩
    (prefixPartial 12 290569) = some ⟨12, 2, 0, 975924, 290569, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_290569_975924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290569 ⟨975924, by decide⟩ :=
  accepted_of_selected 12 290569 ⟨975924, by decide⟩ ⟨12, 2, 0, 975924, 290569, 3941, 65536⟩
    (by decide) selected_cut_36733

theorem selected_cut_36734 : selected 9 ⟨976009, by decide⟩
    (prefixPartial 12 290570) = some ⟨12, 2, 0, 976009, 290570, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_290570_976009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290570 ⟨976009, by decide⟩ :=
  accepted_of_selected 12 290570 ⟨976009, by decide⟩ ⟨12, 2, 0, 976009, 290570, 3733, 65536⟩
    (by decide) selected_cut_36734

theorem selected_cut_36735 : selected 8 ⟨976032, by decide⟩
    (prefixPartial 13 1162284) = some ⟨13, 2, 0, 976032, 1162284, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_1162284_976032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162284 ⟨976032, by decide⟩ :=
  accepted_of_selected 13 1162284 ⟨976032, by decide⟩ ⟨13, 2, 0, 976032, 1162284, 1321, 16384⟩
    (by decide) selected_cut_36735

theorem selected_cut_36736 : selected 8 ⟨976066, by decide⟩
    (prefixPartial 13 1162285) = some ⟨13, 2, 0, 976066, 1162285, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_1162285_976066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162285 ⟨976066, by decide⟩ :=
  accepted_of_selected 13 1162285 ⟨976066, by decide⟩ ⟨13, 2, 0, 976066, 1162285, 1065, 16384⟩
    (by decide) selected_cut_36736

theorem selected_cut_36737 : selected 8 ⟨976089, by decide⟩
    (prefixPartial 13 1162286) = some ⟨13, 2, 0, 976089, 1162286, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_1162286_976089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162286 ⟨976089, by decide⟩ :=
  accepted_of_selected 13 1162286 ⟨976089, by decide⟩ ⟨13, 2, 0, 976089, 1162286, 1277, 16384⟩
    (by decide) selected_cut_36737

theorem selected_cut_36738 : selected 8 ⟨976109, by decide⟩
    (prefixPartial 13 1162287) = some ⟨13, 2, 0, 976109, 1162287, 733, 16384⟩ := by
  decide +kernel

theorem context_13_1162287_976109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162287 ⟨976109, by decide⟩ :=
  accepted_of_selected 13 1162287 ⟨976109, by decide⟩ ⟨13, 2, 0, 976109, 1162287, 733, 16384⟩
    (by decide) selected_cut_36738

theorem unmarked_context_12_290571_976110 : frontier 9 ⟨976110, by decide⟩
    (prefixCache 12 290571) (prefixPartial 12 290571) = false := by
  decide +kernel

theorem node_context_12_290571_976110 : EJMOriginalGlobalDAGData.nodes 9 ⟨976110, by decide⟩ =
    .split (coordinate 12) (![⟨976032, by decide⟩,⟨976066, by decide⟩,⟨976089, by decide⟩,⟨976109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_290571_976110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290571 ⟨976110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 290571
    ⟨976110, by decide⟩ (by decide) (![⟨976032, by decide⟩,⟨976066, by decide⟩,⟨976089, by decide⟩,⟨976109, by decide⟩]) unmarked_context_12_290571_976110 node_context_12_290571_976110
  intro a
  fin_cases a
  · exact context_13_1162284_976032
  · exact context_13_1162285_976066
  · exact context_13_1162286_976089
  · exact context_13_1162287_976109

theorem unmarked_context_11_72642_976111 : frontier 10 ⟨976111, by decide⟩
    (prefixCache 11 72642) (prefixPartial 11 72642) = false := by
  decide +kernel

theorem node_context_11_72642_976111 : EJMOriginalGlobalDAGData.nodes 10 ⟨976111, by decide⟩ =
    .split (coordinate 11) (![⟨975816, by decide⟩,⟨975924, by decide⟩,⟨976009, by decide⟩,⟨976110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72642_976111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72642 ⟨976111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72642
    ⟨976111, by decide⟩ (by decide) (![⟨975816, by decide⟩,⟨975924, by decide⟩,⟨976009, by decide⟩,⟨976110, by decide⟩]) unmarked_context_11_72642_976111 node_context_11_72642_976111
  intro a
  fin_cases a
  · exact context_12_290568_975816
  · exact context_12_290569_975924
  · exact context_12_290570_976009
  · exact context_12_290571_976110

theorem selected_cut_36739 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 290572) = some ⟨12, 1, 0, 390434, 290572, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290572_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290572 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 290572 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 290572, 1, 65536⟩
    (by decide) selected_cut_36739

theorem selected_cut_36740 : selected 9 ⟨976186, by decide⟩
    (prefixPartial 12 290573) = some ⟨12, 2, 0, 976186, 290573, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_290573_976186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290573 ⟨976186, by decide⟩ :=
  accepted_of_selected 12 290573 ⟨976186, by decide⟩ ⟨12, 2, 0, 976186, 290573, 3441, 65536⟩
    (by decide) selected_cut_36740

theorem selected_cut_36741 : selected 9 ⟨976271, by decide⟩
    (prefixPartial 12 290574) = some ⟨12, 2, 0, 976271, 290574, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_290574_976271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290574 ⟨976271, by decide⟩ :=
  accepted_of_selected 12 290574 ⟨976271, by decide⟩ ⟨12, 2, 0, 976271, 290574, 3473, 65536⟩
    (by decide) selected_cut_36741

theorem selected_cut_36742 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 290575) = some ⟨12, 1, 0, 903806, 290575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290575_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290575 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 290575 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 290575, 1, 65536⟩
    (by decide) selected_cut_36742

theorem unmarked_context_11_72643_976272 : frontier 10 ⟨976272, by decide⟩
    (prefixCache 11 72643) (prefixPartial 11 72643) = false := by
  decide +kernel

theorem node_context_11_72643_976272 : EJMOriginalGlobalDAGData.nodes 10 ⟨976272, by decide⟩ =
    .split (coordinate 11) (![⟨390434, by decide⟩,⟨976186, by decide⟩,⟨976271, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72643_976272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72643 ⟨976272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72643
    ⟨976272, by decide⟩ (by decide) (![⟨390434, by decide⟩,⟨976186, by decide⟩,⟨976271, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72643_976272 node_context_11_72643_976272
  intro a
  fin_cases a
  · exact context_12_290572_390434
  · exact context_12_290573_976186
  · exact context_12_290574_976271
  · exact context_12_290575_903806

theorem unmarked_context_10_18160_976273 : frontier 11 ⟨976273, by decide⟩
    (prefixCache 10 18160) (prefixPartial 10 18160) = false := by
  decide +kernel

theorem node_context_10_18160_976273 : EJMOriginalGlobalDAGData.nodes 11 ⟨976273, by decide⟩ =
    .split (coordinate 10) (![⟨975288, by decide⟩,⟨975669, by decide⟩,⟨976111, by decide⟩,⟨976272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18160_976273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18160 ⟨976273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18160
    ⟨976273, by decide⟩ (by decide) (![⟨975288, by decide⟩,⟨975669, by decide⟩,⟨976111, by decide⟩,⟨976272, by decide⟩]) unmarked_context_10_18160_976273 node_context_10_18160_976273
  intro a
  fin_cases a
  · exact context_11_72640_975288
  · exact context_11_72641_975669
  · exact context_11_72642_976111
  · exact context_11_72643_976272

theorem selected_cut_36743 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290576) = some ⟨12, 1, 0, 1738, 290576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290576_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290576 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290576 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290576, 1, 65536⟩
    (by decide) selected_cut_36743

theorem selected_cut_36744 : selected 9 ⟨976368, by decide⟩
    (prefixPartial 12 290577) = some ⟨12, 2, 0, 976368, 290577, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_290577_976368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290577 ⟨976368, by decide⟩ :=
  accepted_of_selected 12 290577 ⟨976368, by decide⟩ ⟨12, 2, 0, 976368, 290577, 2489, 65536⟩
    (by decide) selected_cut_36744

theorem selected_cut_36745 : selected 8 ⟨976406, by decide⟩
    (prefixPartial 13 1162312) = some ⟨13, 2, 0, 976406, 1162312, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_1162312_976406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162312 ⟨976406, by decide⟩ :=
  accepted_of_selected 13 1162312 ⟨976406, by decide⟩ ⟨13, 2, 0, 976406, 1162312, 1417, 16384⟩
    (by decide) selected_cut_36745

theorem selected_cut_36746 : selected 8 ⟨976432, by decide⟩
    (prefixPartial 13 1162313) = some ⟨13, 2, 0, 976432, 1162313, 945, 16384⟩ := by
  decide +kernel

theorem context_13_1162313_976432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162313 ⟨976432, by decide⟩ :=
  accepted_of_selected 13 1162313 ⟨976432, by decide⟩ ⟨13, 2, 0, 976432, 1162313, 945, 16384⟩
    (by decide) selected_cut_36746

theorem selected_cut_36747 : selected 8 ⟨976461, by decide⟩
    (prefixPartial 13 1162314) = some ⟨13, 2, 0, 976461, 1162314, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1162314_976461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162314 ⟨976461, by decide⟩ :=
  accepted_of_selected 13 1162314 ⟨976461, by decide⟩ ⟨13, 2, 0, 976461, 1162314, 1113, 16384⟩
    (by decide) selected_cut_36747

theorem selected_cut_36748 : selected 8 ⟨976481, by decide⟩
    (prefixPartial 13 1162315) = some ⟨13, 2, 0, 976481, 1162315, 713, 16384⟩ := by
  decide +kernel

theorem context_13_1162315_976481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1162315 ⟨976481, by decide⟩ :=
  accepted_of_selected 13 1162315 ⟨976481, by decide⟩ ⟨13, 2, 0, 976481, 1162315, 713, 16384⟩
    (by decide) selected_cut_36748

theorem unmarked_context_12_290578_976482 : frontier 9 ⟨976482, by decide⟩
    (prefixCache 12 290578) (prefixPartial 12 290578) = false := by
  decide +kernel

theorem node_context_12_290578_976482 : EJMOriginalGlobalDAGData.nodes 9 ⟨976482, by decide⟩ =
    .split (coordinate 12) (![⟨976406, by decide⟩,⟨976432, by decide⟩,⟨976461, by decide⟩,⟨976481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_290578_976482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290578 ⟨976482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 290578
    ⟨976482, by decide⟩ (by decide) (![⟨976406, by decide⟩,⟨976432, by decide⟩,⟨976461, by decide⟩,⟨976481, by decide⟩]) unmarked_context_12_290578_976482 node_context_12_290578_976482
  intro a
  fin_cases a
  · exact context_13_1162312_976406
  · exact context_13_1162313_976432
  · exact context_13_1162314_976461
  · exact context_13_1162315_976481

theorem selected_cut_36749 : selected 9 ⟨976574, by decide⟩
    (prefixPartial 12 290579) = some ⟨12, 2, 0, 976574, 290579, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_290579_976574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290579 ⟨976574, by decide⟩ :=
  accepted_of_selected 12 290579 ⟨976574, by decide⟩ ⟨12, 2, 0, 976574, 290579, 3961, 65536⟩
    (by decide) selected_cut_36749

theorem unmarked_context_11_72644_976575 : frontier 10 ⟨976575, by decide⟩
    (prefixCache 11 72644) (prefixPartial 11 72644) = false := by
  decide +kernel

theorem node_context_11_72644_976575 : EJMOriginalGlobalDAGData.nodes 10 ⟨976575, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨976368, by decide⟩,⟨976482, by decide⟩,⟨976574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72644_976575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72644 ⟨976575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72644
    ⟨976575, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨976368, by decide⟩,⟨976482, by decide⟩,⟨976574, by decide⟩]) unmarked_context_11_72644_976575 node_context_11_72644_976575
  intro a
  fin_cases a
  · exact context_12_290576_1738
  · exact context_12_290577_976368
  · exact context_12_290578_976482
  · exact context_12_290579_976574

theorem selected_cut_36750 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290580) = some ⟨12, 1, 0, 1738, 290580, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290580_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290580 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290580 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290580, 1, 65536⟩
    (by decide) selected_cut_36750

theorem selected_cut_36751 : selected 9 ⟨976576, by decide⟩
    (prefixPartial 12 290581) = some ⟨12, 1, 0, 976576, 290581, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290581_976576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290581 ⟨976576, by decide⟩ :=
  accepted_of_selected 12 290581 ⟨976576, by decide⟩ ⟨12, 1, 0, 976576, 290581, 1, 65536⟩
    (by decide) selected_cut_36751

theorem selected_cut_36752 : selected 9 ⟨976666, by decide⟩
    (prefixPartial 12 290582) = some ⟨12, 2, 0, 976666, 290582, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_290582_976666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290582 ⟨976666, by decide⟩ :=
  accepted_of_selected 12 290582 ⟨976666, by decide⟩ ⟨12, 2, 0, 976666, 290582, 3669, 65536⟩
    (by decide) selected_cut_36752

theorem selected_cut_36753 : selected 9 ⟨976754, by decide⟩
    (prefixPartial 12 290583) = some ⟨12, 2, 0, 976754, 290583, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_290583_976754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290583 ⟨976754, by decide⟩ :=
  accepted_of_selected 12 290583 ⟨976754, by decide⟩ ⟨12, 2, 0, 976754, 290583, 3841, 65536⟩
    (by decide) selected_cut_36753

theorem unmarked_context_11_72645_976755 : frontier 10 ⟨976755, by decide⟩
    (prefixCache 11 72645) (prefixPartial 11 72645) = false := by
  decide +kernel

theorem node_context_11_72645_976755 : EJMOriginalGlobalDAGData.nodes 10 ⟨976755, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨976576, by decide⟩,⟨976666, by decide⟩,⟨976754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72645_976755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72645 ⟨976755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72645
    ⟨976755, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨976576, by decide⟩,⟨976666, by decide⟩,⟨976754, by decide⟩]) unmarked_context_11_72645_976755 node_context_11_72645_976755
  intro a
  fin_cases a
  · exact context_12_290580_1738
  · exact context_12_290581_976576
  · exact context_12_290582_976666
  · exact context_12_290583_976754

theorem selected_cut_36754 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290584) = some ⟨12, 1, 0, 1738, 290584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290584_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290584 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290584 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290584, 1, 65536⟩
    (by decide) selected_cut_36754

theorem selected_cut_36755 : selected 9 ⟨976837, by decide⟩
    (prefixPartial 12 290585) = some ⟨12, 2, 0, 976837, 290585, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_290585_976837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290585 ⟨976837, by decide⟩ :=
  accepted_of_selected 12 290585 ⟨976837, by decide⟩ ⟨12, 2, 0, 976837, 290585, 2301, 65536⟩
    (by decide) selected_cut_36755

theorem selected_cut_36756 : selected 9 ⟨976907, by decide⟩
    (prefixPartial 12 290586) = some ⟨12, 2, 0, 976907, 290586, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_290586_976907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290586 ⟨976907, by decide⟩ :=
  accepted_of_selected 12 290586 ⟨976907, by decide⟩ ⟨12, 2, 0, 976907, 290586, 3149, 65536⟩
    (by decide) selected_cut_36756

theorem selected_cut_36757 : selected 9 ⟨976998, by decide⟩
    (prefixPartial 12 290587) = some ⟨12, 2, 0, 976998, 290587, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_290587_976998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290587 ⟨976998, by decide⟩ :=
  accepted_of_selected 12 290587 ⟨976998, by decide⟩ ⟨12, 2, 0, 976998, 290587, 3617, 65536⟩
    (by decide) selected_cut_36757

theorem unmarked_context_11_72646_976999 : frontier 10 ⟨976999, by decide⟩
    (prefixCache 11 72646) (prefixPartial 11 72646) = false := by
  decide +kernel

theorem node_context_11_72646_976999 : EJMOriginalGlobalDAGData.nodes 10 ⟨976999, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨976837, by decide⟩,⟨976907, by decide⟩,⟨976998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72646_976999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72646 ⟨976999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72646
    ⟨976999, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨976837, by decide⟩,⟨976907, by decide⟩,⟨976998, by decide⟩]) unmarked_context_11_72646_976999 node_context_11_72646_976999
  intro a
  fin_cases a
  · exact context_12_290584_1738
  · exact context_12_290585_976837
  · exact context_12_290586_976907
  · exact context_12_290587_976998

theorem selected_cut_36758 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290588) = some ⟨12, 1, 0, 1738, 290588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290588_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290588 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290588 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290588, 1, 65536⟩
    (by decide) selected_cut_36758

theorem selected_cut_36759 : selected 9 ⟨977060, by decide⟩
    (prefixPartial 12 290589) = some ⟨12, 2, 0, 977060, 290589, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_290589_977060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290589 ⟨977060, by decide⟩ :=
  accepted_of_selected 12 290589 ⟨977060, by decide⟩ ⟨12, 2, 0, 977060, 290589, 2057, 65536⟩
    (by decide) selected_cut_36759

theorem selected_cut_36760 : selected 9 ⟨977136, by decide⟩
    (prefixPartial 12 290590) = some ⟨12, 2, 0, 977136, 290590, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_290590_977136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290590 ⟨977136, by decide⟩ :=
  accepted_of_selected 12 290590 ⟨977136, by decide⟩ ⟨12, 2, 0, 977136, 290590, 3001, 65536⟩
    (by decide) selected_cut_36760

theorem selected_cut_36761 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 290591) = some ⟨12, 1, 0, 903806, 290591, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290591_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290591 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 290591 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 290591, 1, 65536⟩
    (by decide) selected_cut_36761

theorem unmarked_context_11_72647_977137 : frontier 10 ⟨977137, by decide⟩
    (prefixCache 11 72647) (prefixPartial 11 72647) = false := by
  decide +kernel

theorem node_context_11_72647_977137 : EJMOriginalGlobalDAGData.nodes 10 ⟨977137, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨977060, by decide⟩,⟨977136, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72647_977137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72647 ⟨977137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72647
    ⟨977137, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨977060, by decide⟩,⟨977136, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72647_977137 node_context_11_72647_977137
  intro a
  fin_cases a
  · exact context_12_290588_1738
  · exact context_12_290589_977060
  · exact context_12_290590_977136
  · exact context_12_290591_903806

theorem unmarked_context_10_18161_977138 : frontier 11 ⟨977138, by decide⟩
    (prefixCache 10 18161) (prefixPartial 10 18161) = false := by
  decide +kernel

theorem node_context_10_18161_977138 : EJMOriginalGlobalDAGData.nodes 11 ⟨977138, by decide⟩ =
    .split (coordinate 10) (![⟨976575, by decide⟩,⟨976755, by decide⟩,⟨976999, by decide⟩,⟨977137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18161_977138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18161 ⟨977138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18161
    ⟨977138, by decide⟩ (by decide) (![⟨976575, by decide⟩,⟨976755, by decide⟩,⟨976999, by decide⟩,⟨977137, by decide⟩]) unmarked_context_10_18161_977138 node_context_10_18161_977138
  intro a
  fin_cases a
  · exact context_11_72644_976575
  · exact context_11_72645_976755
  · exact context_11_72646_976999
  · exact context_11_72647_977137

theorem selected_cut_36762 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290592) = some ⟨12, 1, 0, 1738, 290592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290592_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290592 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290592 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290592, 1, 65536⟩
    (by decide) selected_cut_36762

theorem selected_cut_36763 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290593) = some ⟨12, 1, 0, 1738, 290593, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290593_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290593 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290593 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290593, 1, 65536⟩
    (by decide) selected_cut_36763

theorem selected_cut_36764 : selected 9 ⟨977222, by decide⟩
    (prefixPartial 12 290594) = some ⟨12, 2, 0, 977222, 290594, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_290594_977222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290594 ⟨977222, by decide⟩ :=
  accepted_of_selected 12 290594 ⟨977222, by decide⟩ ⟨12, 2, 0, 977222, 290594, 2461, 65536⟩
    (by decide) selected_cut_36764

theorem selected_cut_36765 : selected 9 ⟨977306, by decide⟩
    (prefixPartial 12 290595) = some ⟨12, 2, 0, 977306, 290595, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_290595_977306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290595 ⟨977306, by decide⟩ :=
  accepted_of_selected 12 290595 ⟨977306, by decide⟩ ⟨12, 2, 0, 977306, 290595, 3333, 65536⟩
    (by decide) selected_cut_36765

theorem unmarked_context_11_72648_977307 : frontier 10 ⟨977307, by decide⟩
    (prefixCache 11 72648) (prefixPartial 11 72648) = false := by
  decide +kernel

theorem node_context_11_72648_977307 : EJMOriginalGlobalDAGData.nodes 10 ⟨977307, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨977222, by decide⟩,⟨977306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72648_977307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72648 ⟨977307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72648
    ⟨977307, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨977222, by decide⟩,⟨977306, by decide⟩]) unmarked_context_11_72648_977307 node_context_11_72648_977307
  intro a
  fin_cases a
  · exact context_12_290592_1738
  · exact context_12_290593_1738
  · exact context_12_290594_977222
  · exact context_12_290595_977306

theorem selected_cut_36766 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290596) = some ⟨12, 1, 0, 1738, 290596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290596_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290596 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290596 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290596, 1, 65536⟩
    (by decide) selected_cut_36766

theorem selected_cut_36767 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 290597) = some ⟨12, 1, 0, 1738, 290597, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290597_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290597 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 290597 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 290597, 1, 65536⟩
    (by decide) selected_cut_36767

theorem selected_cut_36768 : selected 9 ⟨977370, by decide⟩
    (prefixPartial 12 290598) = some ⟨12, 2, 0, 977370, 290598, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_290598_977370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290598 ⟨977370, by decide⟩ :=
  accepted_of_selected 12 290598 ⟨977370, by decide⟩ ⟨12, 2, 0, 977370, 290598, 2089, 65536⟩
    (by decide) selected_cut_36768

theorem selected_cut_36769 : selected 9 ⟨977442, by decide⟩
    (prefixPartial 12 290599) = some ⟨12, 2, 0, 977442, 290599, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_290599_977442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290599 ⟨977442, by decide⟩ :=
  accepted_of_selected 12 290599 ⟨977442, by decide⟩ ⟨12, 2, 0, 977442, 290599, 3005, 65536⟩
    (by decide) selected_cut_36769

theorem unmarked_context_11_72649_977443 : frontier 10 ⟨977443, by decide⟩
    (prefixCache 11 72649) (prefixPartial 11 72649) = false := by
  decide +kernel

theorem node_context_11_72649_977443 : EJMOriginalGlobalDAGData.nodes 10 ⟨977443, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨977370, by decide⟩,⟨977442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72649_977443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72649 ⟨977443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72649
    ⟨977443, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨977370, by decide⟩,⟨977442, by decide⟩]) unmarked_context_11_72649_977443 node_context_11_72649_977443
  intro a
  fin_cases a
  · exact context_12_290596_1738
  · exact context_12_290597_1738
  · exact context_12_290598_977370
  · exact context_12_290599_977442

theorem selected_cut_36770 : selected 10 ⟨977612, by decide⟩
    (prefixPartial 11 72650) = some ⟨11, 2, 0, 977612, 72650, 3953, 262144⟩ := by
  decide +kernel

theorem context_11_72650_977612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72650 ⟨977612, by decide⟩ :=
  accepted_of_selected 11 72650 ⟨977612, by decide⟩ ⟨11, 2, 0, 977612, 72650, 3953, 262144⟩
    (by decide) selected_cut_36770

theorem selected_cut_36771 : selected 10 ⟨977678, by decide⟩
    (prefixPartial 11 72651) = some ⟨11, 2, 0, 977678, 72651, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_72651_977678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72651 ⟨977678, by decide⟩ :=
  accepted_of_selected 11 72651 ⟨977678, by decide⟩ ⟨11, 2, 0, 977678, 72651, 2225, 262144⟩
    (by decide) selected_cut_36771

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
