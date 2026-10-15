/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover473
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_45508 : selected 8 ⟨1262975, by decide⟩
    (prefixPartial 13 1472566) = some ⟨13, 2, 0, 1262975, 1472566, 769, 16384⟩ := by
  decide +kernel

theorem context_13_1472566_1262975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472566 ⟨1262975, by decide⟩ :=
  accepted_of_selected 13 1472566 ⟨1262975, by decide⟩ ⟨13, 2, 0, 1262975, 1472566, 769, 16384⟩
    (by decide) selected_cut_45508

theorem selected_cut_45509 : selected 8 ⟨1262991, by decide⟩
    (prefixPartial 13 1472567) = some ⟨13, 2, 0, 1262991, 1472567, 621, 16384⟩ := by
  decide +kernel

theorem context_13_1472567_1262991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472567 ⟨1262991, by decide⟩ :=
  accepted_of_selected 13 1472567 ⟨1262991, by decide⟩ ⟨13, 2, 0, 1262991, 1472567, 621, 16384⟩
    (by decide) selected_cut_45509

theorem unmarked_context_12_368141_1262992 : frontier 9 ⟨1262992, by decide⟩
    (prefixCache 12 368141) (prefixPartial 12 368141) = false := by
  decide +kernel

theorem node_context_12_368141_1262992 : EJMOriginalGlobalDAGData.nodes 9 ⟨1262992, by decide⟩ =
    .split (coordinate 12) (![⟨1262933, by decide⟩,⟨1262955, by decide⟩,⟨1262975, by decide⟩,⟨1262991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_368141_1262992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368141 ⟨1262992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 368141
    ⟨1262992, by decide⟩ (by decide) (![⟨1262933, by decide⟩,⟨1262955, by decide⟩,⟨1262975, by decide⟩,⟨1262991, by decide⟩]) unmarked_context_12_368141_1262992 node_context_12_368141_1262992
  intro a
  fin_cases a
  · exact context_13_1472564_1262933
  · exact context_13_1472565_1262955
  · exact context_13_1472566_1262975
  · exact context_13_1472567_1262991

theorem selected_cut_45510 : selected 9 ⟨1263069, by decide⟩
    (prefixPartial 12 368142) = some ⟨12, 2, 0, 1263069, 368142, 4013, 65536⟩ := by
  decide +kernel

theorem context_12_368142_1263069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368142 ⟨1263069, by decide⟩ :=
  accepted_of_selected 12 368142 ⟨1263069, by decide⟩ ⟨12, 2, 0, 1263069, 368142, 4013, 65536⟩
    (by decide) selected_cut_45510

theorem selected_cut_45511 : selected 9 ⟨1263153, by decide⟩
    (prefixPartial 12 368143) = some ⟨12, 2, 0, 1263153, 368143, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_368143_1263153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368143 ⟨1263153, by decide⟩ :=
  accepted_of_selected 12 368143 ⟨1263153, by decide⟩ ⟨12, 2, 0, 1263153, 368143, 3909, 65536⟩
    (by decide) selected_cut_45511

theorem unmarked_context_11_92035_1263154 : frontier 10 ⟨1263154, by decide⟩
    (prefixCache 11 92035) (prefixPartial 11 92035) = false := by
  decide +kernel

theorem node_context_11_92035_1263154 : EJMOriginalGlobalDAGData.nodes 10 ⟨1263154, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1262992, by decide⟩,⟨1263069, by decide⟩,⟨1263153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92035_1263154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92035 ⟨1263154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92035
    ⟨1263154, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1262992, by decide⟩,⟨1263069, by decide⟩,⟨1263153, by decide⟩]) unmarked_context_11_92035_1263154 node_context_11_92035_1263154
  intro a
  fin_cases a
  · exact context_12_368140_448748
  · exact context_12_368141_1262992
  · exact context_12_368142_1263069
  · exact context_12_368143_1263153

theorem unmarked_context_10_23008_1263155 : frontier 11 ⟨1263155, by decide⟩
    (prefixCache 10 23008) (prefixPartial 10 23008) = false := by
  decide +kernel

theorem node_context_10_23008_1263155 : EJMOriginalGlobalDAGData.nodes 11 ⟨1263155, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1262726, by decide⟩,⟨1262898, by decide⟩,⟨1263154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23008_1263155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23008 ⟨1263155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23008
    ⟨1263155, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1262726, by decide⟩,⟨1262898, by decide⟩,⟨1263154, by decide⟩]) unmarked_context_10_23008_1263155 node_context_10_23008_1263155
  intro a
  fin_cases a
  · exact context_11_92032_434745
  · exact context_11_92033_1262726
  · exact context_11_92034_1262898
  · exact context_11_92035_1263154

theorem selected_cut_45512 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 368144) = some ⟨12, 1, 0, 1255011, 368144, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368144_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368144 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 368144 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 368144, 1, 65536⟩
    (by decide) selected_cut_45512

theorem selected_cut_45513 : selected 9 ⟨1263231, by decide⟩
    (prefixPartial 12 368145) = some ⟨12, 2, 0, 1263231, 368145, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_368145_1263231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368145 ⟨1263231, by decide⟩ :=
  accepted_of_selected 12 368145 ⟨1263231, by decide⟩ ⟨12, 2, 0, 1263231, 368145, 3777, 65536⟩
    (by decide) selected_cut_45513

theorem selected_cut_45514 : selected 9 ⟨1263312, by decide⟩
    (prefixPartial 12 368146) = some ⟨12, 2, 0, 1263312, 368146, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_368146_1263312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368146 ⟨1263312, by decide⟩ :=
  accepted_of_selected 12 368146 ⟨1263312, by decide⟩ ⟨12, 2, 0, 1263312, 368146, 3625, 65536⟩
    (by decide) selected_cut_45514

theorem selected_cut_45515 : selected 9 ⟨1263392, by decide⟩
    (prefixPartial 12 368147) = some ⟨12, 2, 0, 1263392, 368147, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_368147_1263392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368147 ⟨1263392, by decide⟩ :=
  accepted_of_selected 12 368147 ⟨1263392, by decide⟩ ⟨12, 2, 0, 1263392, 368147, 4053, 65536⟩
    (by decide) selected_cut_45515

theorem unmarked_context_11_92036_1263393 : frontier 10 ⟨1263393, by decide⟩
    (prefixCache 11 92036) (prefixPartial 11 92036) = false := by
  decide +kernel

theorem node_context_11_92036_1263393 : EJMOriginalGlobalDAGData.nodes 10 ⟨1263393, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1263231, by decide⟩,⟨1263312, by decide⟩,⟨1263392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92036_1263393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92036 ⟨1263393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92036
    ⟨1263393, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1263231, by decide⟩,⟨1263312, by decide⟩,⟨1263392, by decide⟩]) unmarked_context_11_92036_1263393 node_context_11_92036_1263393
  intro a
  fin_cases a
  · exact context_12_368144_1255011
  · exact context_12_368145_1263231
  · exact context_12_368146_1263312
  · exact context_12_368147_1263392

theorem selected_cut_45516 : selected 9 ⟨1263473, by decide⟩
    (prefixPartial 12 368148) = some ⟨12, 2, 0, 1263473, 368148, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_368148_1263473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368148 ⟨1263473, by decide⟩ :=
  accepted_of_selected 12 368148 ⟨1263473, by decide⟩ ⟨12, 2, 0, 1263473, 368148, 3421, 65536⟩
    (by decide) selected_cut_45516

theorem selected_cut_45517 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 368149) = some ⟨12, 1, 0, 1172003, 368149, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368149_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368149 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 368149 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 368149, 1, 65536⟩
    (by decide) selected_cut_45517

theorem selected_cut_45518 : selected 9 ⟨1263541, by decide⟩
    (prefixPartial 12 368150) = some ⟨12, 2, 0, 1263541, 368150, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_368150_1263541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368150 ⟨1263541, by decide⟩ :=
  accepted_of_selected 12 368150 ⟨1263541, by decide⟩ ⟨12, 2, 0, 1263541, 368150, 3509, 65536⟩
    (by decide) selected_cut_45518

theorem selected_cut_45519 : selected 9 ⟨1263613, by decide⟩
    (prefixPartial 12 368151) = some ⟨12, 2, 0, 1263613, 368151, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_368151_1263613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368151 ⟨1263613, by decide⟩ :=
  accepted_of_selected 12 368151 ⟨1263613, by decide⟩ ⟨12, 2, 0, 1263613, 368151, 3821, 65536⟩
    (by decide) selected_cut_45519

theorem unmarked_context_11_92037_1263614 : frontier 10 ⟨1263614, by decide⟩
    (prefixCache 11 92037) (prefixPartial 11 92037) = false := by
  decide +kernel

theorem node_context_11_92037_1263614 : EJMOriginalGlobalDAGData.nodes 10 ⟨1263614, by decide⟩ =
    .split (coordinate 11) (![⟨1263473, by decide⟩,⟨1172003, by decide⟩,⟨1263541, by decide⟩,⟨1263613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92037_1263614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92037 ⟨1263614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92037
    ⟨1263614, by decide⟩ (by decide) (![⟨1263473, by decide⟩,⟨1172003, by decide⟩,⟨1263541, by decide⟩,⟨1263613, by decide⟩]) unmarked_context_11_92037_1263614 node_context_11_92037_1263614
  intro a
  fin_cases a
  · exact context_12_368148_1263473
  · exact context_12_368149_1172003
  · exact context_12_368150_1263541
  · exact context_12_368151_1263613

theorem selected_cut_45520 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 368152) = some ⟨12, 1, 0, 994572, 368152, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368152_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368152 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 368152 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 368152, 1, 65536⟩
    (by decide) selected_cut_45520

theorem selected_cut_45521 : selected 9 ⟨1263675, by decide⟩
    (prefixPartial 12 368153) = some ⟨12, 2, 0, 1263675, 368153, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_368153_1263675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368153 ⟨1263675, by decide⟩ :=
  accepted_of_selected 12 368153 ⟨1263675, by decide⟩ ⟨12, 2, 0, 1263675, 368153, 3525, 65536⟩
    (by decide) selected_cut_45521

theorem selected_cut_45522 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 368154) = some ⟨12, 1, 0, 893903, 368154, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368154_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368154 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 368154 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 368154, 1, 65536⟩
    (by decide) selected_cut_45522

theorem selected_cut_45523 : selected 9 ⟨1263745, by decide⟩
    (prefixPartial 12 368155) = some ⟨12, 2, 0, 1263745, 368155, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_368155_1263745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368155 ⟨1263745, by decide⟩ :=
  accepted_of_selected 12 368155 ⟨1263745, by decide⟩ ⟨12, 2, 0, 1263745, 368155, 3817, 65536⟩
    (by decide) selected_cut_45523

theorem unmarked_context_11_92038_1263746 : frontier 10 ⟨1263746, by decide⟩
    (prefixCache 11 92038) (prefixPartial 11 92038) = false := by
  decide +kernel

theorem node_context_11_92038_1263746 : EJMOriginalGlobalDAGData.nodes 10 ⟨1263746, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1263675, by decide⟩,⟨893903, by decide⟩,⟨1263745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92038_1263746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92038 ⟨1263746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92038
    ⟨1263746, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1263675, by decide⟩,⟨893903, by decide⟩,⟨1263745, by decide⟩]) unmarked_context_11_92038_1263746 node_context_11_92038_1263746
  intro a
  fin_cases a
  · exact context_12_368152_994572
  · exact context_12_368153_1263675
  · exact context_12_368154_893903
  · exact context_12_368155_1263745

theorem selected_cut_45524 : selected 9 ⟨1263819, by decide⟩
    (prefixPartial 12 368156) = some ⟨12, 2, 0, 1263819, 368156, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_368156_1263819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368156 ⟨1263819, by decide⟩ :=
  accepted_of_selected 12 368156 ⟨1263819, by decide⟩ ⟨12, 2, 0, 1263819, 368156, 3329, 65536⟩
    (by decide) selected_cut_45524

theorem selected_cut_45525 : selected 9 ⟨1263872, by decide⟩
    (prefixPartial 12 368157) = some ⟨12, 2, 0, 1263872, 368157, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_368157_1263872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368157 ⟨1263872, by decide⟩ :=
  accepted_of_selected 12 368157 ⟨1263872, by decide⟩ ⟨12, 2, 0, 1263872, 368157, 3245, 65536⟩
    (by decide) selected_cut_45525

theorem selected_cut_45526 : selected 9 ⟨1263931, by decide⟩
    (prefixPartial 12 368158) = some ⟨12, 2, 0, 1263931, 368158, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_368158_1263931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368158 ⟨1263931, by decide⟩ :=
  accepted_of_selected 12 368158 ⟨1263931, by decide⟩ ⟨12, 2, 0, 1263931, 368158, 3285, 65536⟩
    (by decide) selected_cut_45526

theorem selected_cut_45527 : selected 9 ⟨1263987, by decide⟩
    (prefixPartial 12 368159) = some ⟨12, 2, 0, 1263987, 368159, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_368159_1263987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368159 ⟨1263987, by decide⟩ :=
  accepted_of_selected 12 368159 ⟨1263987, by decide⟩ ⟨12, 2, 0, 1263987, 368159, 3117, 65536⟩
    (by decide) selected_cut_45527

theorem unmarked_context_11_92039_1263988 : frontier 10 ⟨1263988, by decide⟩
    (prefixCache 11 92039) (prefixPartial 11 92039) = false := by
  decide +kernel

theorem node_context_11_92039_1263988 : EJMOriginalGlobalDAGData.nodes 10 ⟨1263988, by decide⟩ =
    .split (coordinate 11) (![⟨1263819, by decide⟩,⟨1263872, by decide⟩,⟨1263931, by decide⟩,⟨1263987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92039_1263988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92039 ⟨1263988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92039
    ⟨1263988, by decide⟩ (by decide) (![⟨1263819, by decide⟩,⟨1263872, by decide⟩,⟨1263931, by decide⟩,⟨1263987, by decide⟩]) unmarked_context_11_92039_1263988 node_context_11_92039_1263988
  intro a
  fin_cases a
  · exact context_12_368156_1263819
  · exact context_12_368157_1263872
  · exact context_12_368158_1263931
  · exact context_12_368159_1263987

theorem unmarked_context_10_23009_1263989 : frontier 11 ⟨1263989, by decide⟩
    (prefixCache 10 23009) (prefixPartial 10 23009) = false := by
  decide +kernel

theorem node_context_10_23009_1263989 : EJMOriginalGlobalDAGData.nodes 11 ⟨1263989, by decide⟩ =
    .split (coordinate 10) (![⟨1263393, by decide⟩,⟨1263614, by decide⟩,⟨1263746, by decide⟩,⟨1263988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23009_1263989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23009 ⟨1263989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23009
    ⟨1263989, by decide⟩ (by decide) (![⟨1263393, by decide⟩,⟨1263614, by decide⟩,⟨1263746, by decide⟩,⟨1263988, by decide⟩]) unmarked_context_10_23009_1263989 node_context_10_23009_1263989
  intro a
  fin_cases a
  · exact context_11_92036_1263393
  · exact context_11_92037_1263614
  · exact context_11_92038_1263746
  · exact context_11_92039_1263988

theorem selected_cut_45528 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 368160) = some ⟨12, 1, 0, 435790, 368160, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368160_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368160 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 368160 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 368160, 1, 65536⟩
    (by decide) selected_cut_45528

theorem selected_cut_45529 : selected 9 ⟨1264049, by decide⟩
    (prefixPartial 12 368161) = some ⟨12, 2, 0, 1264049, 368161, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_368161_1264049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368161 ⟨1264049, by decide⟩ :=
  accepted_of_selected 12 368161 ⟨1264049, by decide⟩ ⟨12, 2, 0, 1264049, 368161, 3149, 65536⟩
    (by decide) selected_cut_45529

theorem selected_cut_45530 : selected 9 ⟨1264106, by decide⟩
    (prefixPartial 12 368162) = some ⟨12, 2, 0, 1264106, 368162, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_368162_1264106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368162 ⟨1264106, by decide⟩ :=
  accepted_of_selected 12 368162 ⟨1264106, by decide⟩ ⟨12, 2, 0, 1264106, 368162, 2745, 65536⟩
    (by decide) selected_cut_45530

theorem selected_cut_45531 : selected 9 ⟨1264158, by decide⟩
    (prefixPartial 12 368163) = some ⟨12, 2, 0, 1264158, 368163, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_368163_1264158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368163 ⟨1264158, by decide⟩ :=
  accepted_of_selected 12 368163 ⟨1264158, by decide⟩ ⟨12, 2, 0, 1264158, 368163, 3277, 65536⟩
    (by decide) selected_cut_45531

theorem unmarked_context_11_92040_1264159 : frontier 10 ⟨1264159, by decide⟩
    (prefixCache 11 92040) (prefixPartial 11 92040) = false := by
  decide +kernel

theorem node_context_11_92040_1264159 : EJMOriginalGlobalDAGData.nodes 10 ⟨1264159, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1264049, by decide⟩,⟨1264106, by decide⟩,⟨1264158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92040_1264159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92040 ⟨1264159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92040
    ⟨1264159, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1264049, by decide⟩,⟨1264106, by decide⟩,⟨1264158, by decide⟩]) unmarked_context_11_92040_1264159 node_context_11_92040_1264159
  intro a
  fin_cases a
  · exact context_12_368160_435790
  · exact context_12_368161_1264049
  · exact context_12_368162_1264106
  · exact context_12_368163_1264158

theorem selected_cut_45532 : selected 9 ⟨1264210, by decide⟩
    (prefixPartial 12 368164) = some ⟨12, 2, 0, 1264210, 368164, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_368164_1264210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368164 ⟨1264210, by decide⟩ :=
  accepted_of_selected 12 368164 ⟨1264210, by decide⟩ ⟨12, 2, 0, 1264210, 368164, 2881, 65536⟩
    (by decide) selected_cut_45532

theorem selected_cut_45533 : selected 9 ⟨1264276, by decide⟩
    (prefixPartial 12 368165) = some ⟨12, 2, 0, 1264276, 368165, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_368165_1264276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368165 ⟨1264276, by decide⟩ :=
  accepted_of_selected 12 368165 ⟨1264276, by decide⟩ ⟨12, 2, 0, 1264276, 368165, 3637, 65536⟩
    (by decide) selected_cut_45533

theorem selected_cut_45534 : selected 9 ⟨1264326, by decide⟩
    (prefixPartial 12 368166) = some ⟨12, 2, 0, 1264326, 368166, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_368166_1264326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368166 ⟨1264326, by decide⟩ :=
  accepted_of_selected 12 368166 ⟨1264326, by decide⟩ ⟨12, 2, 0, 1264326, 368166, 2773, 65536⟩
    (by decide) selected_cut_45534

theorem selected_cut_45535 : selected 9 ⟨1264377, by decide⟩
    (prefixPartial 12 368167) = some ⟨12, 2, 0, 1264377, 368167, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_368167_1264377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368167 ⟨1264377, by decide⟩ :=
  accepted_of_selected 12 368167 ⟨1264377, by decide⟩ ⟨12, 2, 0, 1264377, 368167, 3061, 65536⟩
    (by decide) selected_cut_45535

theorem unmarked_context_11_92041_1264378 : frontier 10 ⟨1264378, by decide⟩
    (prefixCache 11 92041) (prefixPartial 11 92041) = false := by
  decide +kernel

theorem node_context_11_92041_1264378 : EJMOriginalGlobalDAGData.nodes 10 ⟨1264378, by decide⟩ =
    .split (coordinate 11) (![⟨1264210, by decide⟩,⟨1264276, by decide⟩,⟨1264326, by decide⟩,⟨1264377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92041_1264378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92041 ⟨1264378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92041
    ⟨1264378, by decide⟩ (by decide) (![⟨1264210, by decide⟩,⟨1264276, by decide⟩,⟨1264326, by decide⟩,⟨1264377, by decide⟩]) unmarked_context_11_92041_1264378 node_context_11_92041_1264378
  intro a
  fin_cases a
  · exact context_12_368164_1264210
  · exact context_12_368165_1264276
  · exact context_12_368166_1264326
  · exact context_12_368167_1264377

theorem selected_cut_45536 : selected 10 ⟨1264421, by decide⟩
    (prefixPartial 11 92042) = some ⟨11, 2, 0, 1264421, 92042, 2865, 262144⟩ := by
  decide +kernel

theorem context_11_92042_1264421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92042 ⟨1264421, by decide⟩ :=
  accepted_of_selected 11 92042 ⟨1264421, by decide⟩ ⟨11, 2, 0, 1264421, 92042, 2865, 262144⟩
    (by decide) selected_cut_45536

theorem selected_cut_45537 : selected 9 ⟨1264468, by decide⟩
    (prefixPartial 12 368172) = some ⟨12, 2, 0, 1264468, 368172, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_368172_1264468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368172 ⟨1264468, by decide⟩ :=
  accepted_of_selected 12 368172 ⟨1264468, by decide⟩ ⟨12, 2, 0, 1264468, 368172, 2625, 65536⟩
    (by decide) selected_cut_45537

theorem selected_cut_45538 : selected 9 ⟨1264520, by decide⟩
    (prefixPartial 12 368173) = some ⟨12, 2, 0, 1264520, 368173, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_368173_1264520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368173 ⟨1264520, by decide⟩ :=
  accepted_of_selected 12 368173 ⟨1264520, by decide⟩ ⟨12, 2, 0, 1264520, 368173, 2789, 65536⟩
    (by decide) selected_cut_45538

theorem selected_cut_45539 : selected 9 ⟨1264561, by decide⟩
    (prefixPartial 12 368174) = some ⟨12, 2, 0, 1264561, 368174, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_368174_1264561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368174 ⟨1264561, by decide⟩ :=
  accepted_of_selected 12 368174 ⟨1264561, by decide⟩ ⟨12, 2, 0, 1264561, 368174, 2601, 65536⟩
    (by decide) selected_cut_45539

theorem selected_cut_45540 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 368175) = some ⟨12, 1, 0, 758968, 368175, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368175_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368175 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 368175 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 368175, 1, 65536⟩
    (by decide) selected_cut_45540

theorem unmarked_context_11_92043_1264562 : frontier 10 ⟨1264562, by decide⟩
    (prefixCache 11 92043) (prefixPartial 11 92043) = false := by
  decide +kernel

theorem node_context_11_92043_1264562 : EJMOriginalGlobalDAGData.nodes 10 ⟨1264562, by decide⟩ =
    .split (coordinate 11) (![⟨1264468, by decide⟩,⟨1264520, by decide⟩,⟨1264561, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92043_1264562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92043 ⟨1264562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92043
    ⟨1264562, by decide⟩ (by decide) (![⟨1264468, by decide⟩,⟨1264520, by decide⟩,⟨1264561, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_92043_1264562 node_context_11_92043_1264562
  intro a
  fin_cases a
  · exact context_12_368172_1264468
  · exact context_12_368173_1264520
  · exact context_12_368174_1264561
  · exact context_12_368175_758968

theorem unmarked_context_10_23010_1264563 : frontier 11 ⟨1264563, by decide⟩
    (prefixCache 10 23010) (prefixPartial 10 23010) = false := by
  decide +kernel

theorem node_context_10_23010_1264563 : EJMOriginalGlobalDAGData.nodes 11 ⟨1264563, by decide⟩ =
    .split (coordinate 10) (![⟨1264159, by decide⟩,⟨1264378, by decide⟩,⟨1264421, by decide⟩,⟨1264562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23010_1264563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23010 ⟨1264563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23010
    ⟨1264563, by decide⟩ (by decide) (![⟨1264159, by decide⟩,⟨1264378, by decide⟩,⟨1264421, by decide⟩,⟨1264562, by decide⟩]) unmarked_context_10_23010_1264563 node_context_10_23010_1264563
  intro a
  fin_cases a
  · exact context_11_92040_1264159
  · exact context_11_92041_1264378
  · exact context_11_92042_1264421
  · exact context_11_92043_1264562

theorem selected_cut_45541 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 368176) = some ⟨12, 1, 0, 1255011, 368176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368176_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368176 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 368176 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 368176, 1, 65536⟩
    (by decide) selected_cut_45541

theorem selected_cut_45542 : selected 9 ⟨1264609, by decide⟩
    (prefixPartial 12 368177) = some ⟨12, 2, 0, 1264609, 368177, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_368177_1264609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368177 ⟨1264609, by decide⟩ :=
  accepted_of_selected 12 368177 ⟨1264609, by decide⟩ ⟨12, 2, 0, 1264609, 368177, 2845, 65536⟩
    (by decide) selected_cut_45542

theorem selected_cut_45543 : selected 9 ⟨1264667, by decide⟩
    (prefixPartial 12 368178) = some ⟨12, 2, 0, 1264667, 368178, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_368178_1264667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368178 ⟨1264667, by decide⟩ :=
  accepted_of_selected 12 368178 ⟨1264667, by decide⟩ ⟨12, 2, 0, 1264667, 368178, 2741, 65536⟩
    (by decide) selected_cut_45543

theorem selected_cut_45544 : selected 9 ⟨1264718, by decide⟩
    (prefixPartial 12 368179) = some ⟨12, 2, 0, 1264718, 368179, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_368179_1264718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368179 ⟨1264718, by decide⟩ :=
  accepted_of_selected 12 368179 ⟨1264718, by decide⟩ ⟨12, 2, 0, 1264718, 368179, 3157, 65536⟩
    (by decide) selected_cut_45544

theorem unmarked_context_11_92044_1264719 : frontier 10 ⟨1264719, by decide⟩
    (prefixCache 11 92044) (prefixPartial 11 92044) = false := by
  decide +kernel

theorem node_context_11_92044_1264719 : EJMOriginalGlobalDAGData.nodes 10 ⟨1264719, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1264609, by decide⟩,⟨1264667, by decide⟩,⟨1264718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92044_1264719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92044 ⟨1264719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92044
    ⟨1264719, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1264609, by decide⟩,⟨1264667, by decide⟩,⟨1264718, by decide⟩]) unmarked_context_11_92044_1264719 node_context_11_92044_1264719
  intro a
  fin_cases a
  · exact context_12_368176_1255011
  · exact context_12_368177_1264609
  · exact context_12_368178_1264667
  · exact context_12_368179_1264718

theorem selected_cut_45545 : selected 9 ⟨1264782, by decide⟩
    (prefixPartial 12 368180) = some ⟨12, 2, 0, 1264782, 368180, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_368180_1264782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368180 ⟨1264782, by decide⟩ :=
  accepted_of_selected 12 368180 ⟨1264782, by decide⟩ ⟨12, 2, 0, 1264782, 368180, 2721, 65536⟩
    (by decide) selected_cut_45545

theorem selected_cut_45546 : selected 9 ⟨1264844, by decide⟩
    (prefixPartial 12 368181) = some ⟨12, 2, 0, 1264844, 368181, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_368181_1264844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368181 ⟨1264844, by decide⟩ :=
  accepted_of_selected 12 368181 ⟨1264844, by decide⟩ ⟨12, 2, 0, 1264844, 368181, 3129, 65536⟩
    (by decide) selected_cut_45546

theorem selected_cut_45547 : selected 9 ⟨1264895, by decide⟩
    (prefixPartial 12 368182) = some ⟨12, 2, 0, 1264895, 368182, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_368182_1264895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368182 ⟨1264895, by decide⟩ :=
  accepted_of_selected 12 368182 ⟨1264895, by decide⟩ ⟨12, 2, 0, 1264895, 368182, 2529, 65536⟩
    (by decide) selected_cut_45547

theorem selected_cut_45548 : selected 9 ⟨1264946, by decide⟩
    (prefixPartial 12 368183) = some ⟨12, 2, 0, 1264946, 368183, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_368183_1264946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368183 ⟨1264946, by decide⟩ :=
  accepted_of_selected 12 368183 ⟨1264946, by decide⟩ ⟨12, 2, 0, 1264946, 368183, 2749, 65536⟩
    (by decide) selected_cut_45548

theorem unmarked_context_11_92045_1264947 : frontier 10 ⟨1264947, by decide⟩
    (prefixCache 11 92045) (prefixPartial 11 92045) = false := by
  decide +kernel

theorem node_context_11_92045_1264947 : EJMOriginalGlobalDAGData.nodes 10 ⟨1264947, by decide⟩ =
    .split (coordinate 11) (![⟨1264782, by decide⟩,⟨1264844, by decide⟩,⟨1264895, by decide⟩,⟨1264946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92045_1264947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92045 ⟨1264947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92045
    ⟨1264947, by decide⟩ (by decide) (![⟨1264782, by decide⟩,⟨1264844, by decide⟩,⟨1264895, by decide⟩,⟨1264946, by decide⟩]) unmarked_context_11_92045_1264947 node_context_11_92045_1264947
  intro a
  fin_cases a
  · exact context_12_368180_1264782
  · exact context_12_368181_1264844
  · exact context_12_368182_1264895
  · exact context_12_368183_1264946

theorem selected_cut_45549 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 368184) = some ⟨12, 1, 0, 994572, 368184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368184_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368184 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 368184 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 368184, 1, 65536⟩
    (by decide) selected_cut_45549

theorem selected_cut_45550 : selected 9 ⟨1264986, by decide⟩
    (prefixPartial 12 368185) = some ⟨12, 2, 0, 1264986, 368185, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_368185_1264986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368185 ⟨1264986, by decide⟩ :=
  accepted_of_selected 12 368185 ⟨1264986, by decide⟩ ⟨12, 2, 0, 1264986, 368185, 2413, 65536⟩
    (by decide) selected_cut_45550

theorem selected_cut_45551 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 368186) = some ⟨12, 1, 0, 893903, 368186, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368186_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368186 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 368186 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 368186, 1, 65536⟩
    (by decide) selected_cut_45551

theorem selected_cut_45552 : selected 9 ⟨1265047, by decide⟩
    (prefixPartial 12 368187) = some ⟨12, 2, 0, 1265047, 368187, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_368187_1265047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368187 ⟨1265047, by decide⟩ :=
  accepted_of_selected 12 368187 ⟨1265047, by decide⟩ ⟨12, 2, 0, 1265047, 368187, 2861, 65536⟩
    (by decide) selected_cut_45552

theorem unmarked_context_11_92046_1265048 : frontier 10 ⟨1265048, by decide⟩
    (prefixCache 11 92046) (prefixPartial 11 92046) = false := by
  decide +kernel

theorem node_context_11_92046_1265048 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265048, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1264986, by decide⟩,⟨893903, by decide⟩,⟨1265047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92046_1265048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92046 ⟨1265048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92046
    ⟨1265048, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1264986, by decide⟩,⟨893903, by decide⟩,⟨1265047, by decide⟩]) unmarked_context_11_92046_1265048 node_context_11_92046_1265048
  intro a
  fin_cases a
  · exact context_12_368184_994572
  · exact context_12_368185_1264986
  · exact context_12_368186_893903
  · exact context_12_368187_1265047

theorem selected_cut_45553 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 92047) = some ⟨11, 1, 0, 977886, 92047, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92047_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92047 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 92047 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 92047, 1, 262144⟩
    (by decide) selected_cut_45553

theorem unmarked_context_10_23011_1265049 : frontier 11 ⟨1265049, by decide⟩
    (prefixCache 10 23011) (prefixPartial 10 23011) = false := by
  decide +kernel

theorem node_context_10_23011_1265049 : EJMOriginalGlobalDAGData.nodes 11 ⟨1265049, by decide⟩ =
    .split (coordinate 10) (![⟨1264719, by decide⟩,⟨1264947, by decide⟩,⟨1265048, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23011_1265049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23011 ⟨1265049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23011
    ⟨1265049, by decide⟩ (by decide) (![⟨1264719, by decide⟩,⟨1264947, by decide⟩,⟨1265048, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23011_1265049 node_context_10_23011_1265049
  intro a
  fin_cases a
  · exact context_11_92044_1264719
  · exact context_11_92045_1264947
  · exact context_11_92046_1265048
  · exact context_11_92047_977886

theorem unmarked_context_9_5752_1265050 : frontier 12 ⟨1265050, by decide⟩
    (prefixCache 9 5752) (prefixPartial 9 5752) = false := by
  decide +kernel

theorem node_context_9_5752_1265050 : EJMOriginalGlobalDAGData.nodes 12 ⟨1265050, by decide⟩ =
    .split (coordinate 9) (![⟨1263155, by decide⟩,⟨1263989, by decide⟩,⟨1264563, by decide⟩,⟨1265049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5752_1265050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5752 ⟨1265050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5752
    ⟨1265050, by decide⟩ (by decide) (![⟨1263155, by decide⟩,⟨1263989, by decide⟩,⟨1264563, by decide⟩,⟨1265049, by decide⟩]) unmarked_context_9_5752_1265050 node_context_9_5752_1265050
  intro a
  fin_cases a
  · exact context_10_23008_1263155
  · exact context_10_23009_1263989
  · exact context_10_23010_1264563
  · exact context_10_23011_1265049

theorem selected_cut_45554 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 368192) = some ⟨12, 1, 0, 1173556, 368192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368192_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368192 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 368192 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 368192, 1, 65536⟩
    (by decide) selected_cut_45554

theorem selected_cut_45555 : selected 9 ⟨1265093, by decide⟩
    (prefixPartial 12 368193) = some ⟨12, 2, 0, 1265093, 368193, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_368193_1265093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368193 ⟨1265093, by decide⟩ :=
  accepted_of_selected 12 368193 ⟨1265093, by decide⟩ ⟨12, 2, 0, 1265093, 368193, 2153, 65536⟩
    (by decide) selected_cut_45555

theorem selected_cut_45556 : selected 9 ⟨1265139, by decide⟩
    (prefixPartial 12 368194) = some ⟨12, 2, 0, 1265139, 368194, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_368194_1265139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368194 ⟨1265139, by decide⟩ :=
  accepted_of_selected 12 368194 ⟨1265139, by decide⟩ ⟨12, 2, 0, 1265139, 368194, 2053, 65536⟩
    (by decide) selected_cut_45556

theorem selected_cut_45557 : selected 9 ⟨1265181, by decide⟩
    (prefixPartial 12 368195) = some ⟨12, 2, 0, 1265181, 368195, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_368195_1265181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368195 ⟨1265181, by decide⟩ :=
  accepted_of_selected 12 368195 ⟨1265181, by decide⟩ ⟨12, 2, 0, 1265181, 368195, 2341, 65536⟩
    (by decide) selected_cut_45557

theorem unmarked_context_11_92048_1265182 : frontier 10 ⟨1265182, by decide⟩
    (prefixCache 11 92048) (prefixPartial 11 92048) = false := by
  decide +kernel

theorem node_context_11_92048_1265182 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265182, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨1265093, by decide⟩,⟨1265139, by decide⟩,⟨1265181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92048_1265182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92048 ⟨1265182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92048
    ⟨1265182, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨1265093, by decide⟩,⟨1265139, by decide⟩,⟨1265181, by decide⟩]) unmarked_context_11_92048_1265182 node_context_11_92048_1265182
  intro a
  fin_cases a
  · exact context_12_368192_1173556
  · exact context_12_368193_1265093
  · exact context_12_368194_1265139
  · exact context_12_368195_1265181

theorem selected_cut_45558 : selected 9 ⟨1265228, by decide⟩
    (prefixPartial 12 368196) = some ⟨12, 2, 0, 1265228, 368196, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_368196_1265228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368196 ⟨1265228, by decide⟩ :=
  accepted_of_selected 12 368196 ⟨1265228, by decide⟩ ⟨12, 2, 0, 1265228, 368196, 2281, 65536⟩
    (by decide) selected_cut_45558

theorem selected_cut_45559 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 368197) = some ⟨12, 1, 0, 1257136, 368197, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368197_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368197 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 368197 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 368197, 1, 65536⟩
    (by decide) selected_cut_45559

theorem selected_cut_45560 : selected 9 ⟨1265272, by decide⟩
    (prefixPartial 12 368198) = some ⟨12, 2, 0, 1265272, 368198, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_368198_1265272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368198 ⟨1265272, by decide⟩ :=
  accepted_of_selected 12 368198 ⟨1265272, by decide⟩ ⟨12, 2, 0, 1265272, 368198, 2077, 65536⟩
    (by decide) selected_cut_45560

theorem selected_cut_45561 : selected 9 ⟨1265311, by decide⟩
    (prefixPartial 12 368199) = some ⟨12, 2, 0, 1265311, 368199, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_368199_1265311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368199 ⟨1265311, by decide⟩ :=
  accepted_of_selected 12 368199 ⟨1265311, by decide⟩ ⟨12, 2, 0, 1265311, 368199, 2169, 65536⟩
    (by decide) selected_cut_45561

theorem unmarked_context_11_92049_1265312 : frontier 10 ⟨1265312, by decide⟩
    (prefixCache 11 92049) (prefixPartial 11 92049) = false := by
  decide +kernel

theorem node_context_11_92049_1265312 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265312, by decide⟩ =
    .split (coordinate 11) (![⟨1265228, by decide⟩,⟨1257136, by decide⟩,⟨1265272, by decide⟩,⟨1265311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92049_1265312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92049 ⟨1265312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92049
    ⟨1265312, by decide⟩ (by decide) (![⟨1265228, by decide⟩,⟨1257136, by decide⟩,⟨1265272, by decide⟩,⟨1265311, by decide⟩]) unmarked_context_11_92049_1265312 node_context_11_92049_1265312
  intro a
  fin_cases a
  · exact context_12_368196_1265228
  · exact context_12_368197_1257136
  · exact context_12_368198_1265272
  · exact context_12_368199_1265311

theorem selected_cut_45562 : selected 9 ⟨1265357, by decide⟩
    (prefixPartial 12 368200) = some ⟨12, 2, 0, 1265357, 368200, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_368200_1265357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368200 ⟨1265357, by decide⟩ :=
  accepted_of_selected 12 368200 ⟨1265357, by decide⟩ ⟨12, 2, 0, 1265357, 368200, 2173, 65536⟩
    (by decide) selected_cut_45562

theorem selected_cut_45563 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 368201) = some ⟨12, 1, 0, 691709, 368201, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368201_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368201 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 368201 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 368201, 1, 65536⟩
    (by decide) selected_cut_45563

theorem selected_cut_45564 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 368202) = some ⟨12, 1, 0, 893903, 368202, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368202_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368202 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 368202 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 368202, 1, 65536⟩
    (by decide) selected_cut_45564

theorem selected_cut_45565 : selected 9 ⟨1265394, by decide⟩
    (prefixPartial 12 368203) = some ⟨12, 2, 0, 1265394, 368203, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_368203_1265394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368203 ⟨1265394, by decide⟩ :=
  accepted_of_selected 12 368203 ⟨1265394, by decide⟩ ⟨12, 2, 0, 1265394, 368203, 2297, 65536⟩
    (by decide) selected_cut_45565

theorem unmarked_context_11_92050_1265395 : frontier 10 ⟨1265395, by decide⟩
    (prefixCache 11 92050) (prefixPartial 11 92050) = false := by
  decide +kernel

theorem node_context_11_92050_1265395 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265395, by decide⟩ =
    .split (coordinate 11) (![⟨1265357, by decide⟩,⟨691709, by decide⟩,⟨893903, by decide⟩,⟨1265394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92050_1265395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92050 ⟨1265395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92050
    ⟨1265395, by decide⟩ (by decide) (![⟨1265357, by decide⟩,⟨691709, by decide⟩,⟨893903, by decide⟩,⟨1265394, by decide⟩]) unmarked_context_11_92050_1265395 node_context_11_92050_1265395
  intro a
  fin_cases a
  · exact context_12_368200_1265357
  · exact context_12_368201_691709
  · exact context_12_368202_893903
  · exact context_12_368203_1265394

theorem selected_cut_45566 : selected 9 ⟨1265433, by decide⟩
    (prefixPartial 12 368204) = some ⟨12, 2, 0, 1265433, 368204, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_368204_1265433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368204 ⟨1265433, by decide⟩ :=
  accepted_of_selected 12 368204 ⟨1265433, by decide⟩ ⟨12, 2, 0, 1265433, 368204, 2141, 65536⟩
    (by decide) selected_cut_45566

theorem selected_cut_45567 : selected 9 ⟨1265469, by decide⟩
    (prefixPartial 12 368205) = some ⟨12, 2, 0, 1265469, 368205, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_368205_1265469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368205 ⟨1265469, by decide⟩ :=
  accepted_of_selected 12 368205 ⟨1265469, by decide⟩ ⟨12, 2, 0, 1265469, 368205, 1877, 65536⟩
    (by decide) selected_cut_45567

theorem selected_cut_45568 : selected 9 ⟨1265508, by decide⟩
    (prefixPartial 12 368206) = some ⟨12, 2, 0, 1265508, 368206, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_368206_1265508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368206 ⟨1265508, by decide⟩ :=
  accepted_of_selected 12 368206 ⟨1265508, by decide⟩ ⟨12, 2, 0, 1265508, 368206, 1917, 65536⟩
    (by decide) selected_cut_45568

theorem selected_cut_45569 : selected 9 ⟨1265541, by decide⟩
    (prefixPartial 12 368207) = some ⟨12, 2, 0, 1265541, 368207, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_368207_1265541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368207 ⟨1265541, by decide⟩ :=
  accepted_of_selected 12 368207 ⟨1265541, by decide⟩ ⟨12, 2, 0, 1265541, 368207, 1789, 65536⟩
    (by decide) selected_cut_45569

theorem unmarked_context_11_92051_1265542 : frontier 10 ⟨1265542, by decide⟩
    (prefixCache 11 92051) (prefixPartial 11 92051) = false := by
  decide +kernel

theorem node_context_11_92051_1265542 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265542, by decide⟩ =
    .split (coordinate 11) (![⟨1265433, by decide⟩,⟨1265469, by decide⟩,⟨1265508, by decide⟩,⟨1265541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92051_1265542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92051 ⟨1265542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92051
    ⟨1265542, by decide⟩ (by decide) (![⟨1265433, by decide⟩,⟨1265469, by decide⟩,⟨1265508, by decide⟩,⟨1265541, by decide⟩]) unmarked_context_11_92051_1265542 node_context_11_92051_1265542
  intro a
  fin_cases a
  · exact context_12_368204_1265433
  · exact context_12_368205_1265469
  · exact context_12_368206_1265508
  · exact context_12_368207_1265541

theorem unmarked_context_10_23012_1265543 : frontier 11 ⟨1265543, by decide⟩
    (prefixCache 10 23012) (prefixPartial 10 23012) = false := by
  decide +kernel

theorem node_context_10_23012_1265543 : EJMOriginalGlobalDAGData.nodes 11 ⟨1265543, by decide⟩ =
    .split (coordinate 10) (![⟨1265182, by decide⟩,⟨1265312, by decide⟩,⟨1265395, by decide⟩,⟨1265542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23012_1265543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23012 ⟨1265543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23012
    ⟨1265543, by decide⟩ (by decide) (![⟨1265182, by decide⟩,⟨1265312, by decide⟩,⟨1265395, by decide⟩,⟨1265542, by decide⟩]) unmarked_context_10_23012_1265543 node_context_10_23012_1265543
  intro a
  fin_cases a
  · exact context_11_92048_1265182
  · exact context_11_92049_1265312
  · exact context_11_92050_1265395
  · exact context_11_92051_1265542

theorem selected_cut_45570 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23013) = some ⟨10, 1, 0, 893098, 23013, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23013_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23013 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23013 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23013, 1, 1048576⟩
    (by decide) selected_cut_45570

theorem selected_cut_45571 : selected 9 ⟨1265576, by decide⟩
    (prefixPartial 12 368224) = some ⟨12, 2, 0, 1265576, 368224, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_368224_1265576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368224 ⟨1265576, by decide⟩ :=
  accepted_of_selected 12 368224 ⟨1265576, by decide⟩ ⟨12, 2, 0, 1265576, 368224, 1545, 65536⟩
    (by decide) selected_cut_45571

theorem selected_cut_45572 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 368225) = some ⟨12, 1, 0, 1256866, 368225, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368225_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368225 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 368225 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 368225, 1, 65536⟩
    (by decide) selected_cut_45572

theorem selected_cut_45573 : selected 9 ⟨1265607, by decide⟩
    (prefixPartial 12 368226) = some ⟨12, 2, 0, 1265607, 368226, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_368226_1265607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368226 ⟨1265607, by decide⟩ :=
  accepted_of_selected 12 368226 ⟨1265607, by decide⟩ ⟨12, 2, 0, 1265607, 368226, 1457, 65536⟩
    (by decide) selected_cut_45573

theorem selected_cut_45574 : selected 9 ⟨1265641, by decide⟩
    (prefixPartial 12 368227) = some ⟨12, 2, 0, 1265641, 368227, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_368227_1265641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368227 ⟨1265641, by decide⟩ :=
  accepted_of_selected 12 368227 ⟨1265641, by decide⟩ ⟨12, 2, 0, 1265641, 368227, 1773, 65536⟩
    (by decide) selected_cut_45574

theorem unmarked_context_11_92056_1265642 : frontier 10 ⟨1265642, by decide⟩
    (prefixCache 11 92056) (prefixPartial 11 92056) = false := by
  decide +kernel

theorem node_context_11_92056_1265642 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265642, by decide⟩ =
    .split (coordinate 11) (![⟨1265576, by decide⟩,⟨1256866, by decide⟩,⟨1265607, by decide⟩,⟨1265641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92056_1265642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92056 ⟨1265642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92056
    ⟨1265642, by decide⟩ (by decide) (![⟨1265576, by decide⟩,⟨1256866, by decide⟩,⟨1265607, by decide⟩,⟨1265641, by decide⟩]) unmarked_context_11_92056_1265642 node_context_11_92056_1265642
  intro a
  fin_cases a
  · exact context_12_368224_1265576
  · exact context_12_368225_1256866
  · exact context_12_368226_1265607
  · exact context_12_368227_1265641

theorem selected_cut_45575 : selected 9 ⟨1265673, by decide⟩
    (prefixPartial 12 368228) = some ⟨12, 2, 0, 1265673, 368228, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_368228_1265673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368228 ⟨1265673, by decide⟩ :=
  accepted_of_selected 12 368228 ⟨1265673, by decide⟩ ⟨12, 2, 0, 1265673, 368228, 1621, 65536⟩
    (by decide) selected_cut_45575

theorem selected_cut_45576 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 368229) = some ⟨12, 1, 0, 1256866, 368229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368229_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368229 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 368229 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 368229, 1, 65536⟩
    (by decide) selected_cut_45576

theorem selected_cut_45577 : selected 9 ⟨1265694, by decide⟩
    (prefixPartial 12 368230) = some ⟨12, 2, 0, 1265694, 368230, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_368230_1265694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368230 ⟨1265694, by decide⟩ :=
  accepted_of_selected 12 368230 ⟨1265694, by decide⟩ ⟨12, 2, 0, 1265694, 368230, 1417, 65536⟩
    (by decide) selected_cut_45577

theorem selected_cut_45578 : selected 9 ⟨1265722, by decide⟩
    (prefixPartial 12 368231) = some ⟨12, 2, 0, 1265722, 368231, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_368231_1265722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368231 ⟨1265722, by decide⟩ :=
  accepted_of_selected 12 368231 ⟨1265722, by decide⟩ ⟨12, 2, 0, 1265722, 368231, 1513, 65536⟩
    (by decide) selected_cut_45578

theorem unmarked_context_11_92057_1265723 : frontier 10 ⟨1265723, by decide⟩
    (prefixCache 11 92057) (prefixPartial 11 92057) = false := by
  decide +kernel

theorem node_context_11_92057_1265723 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265723, by decide⟩ =
    .split (coordinate 11) (![⟨1265673, by decide⟩,⟨1256866, by decide⟩,⟨1265694, by decide⟩,⟨1265722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92057_1265723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92057 ⟨1265723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92057
    ⟨1265723, by decide⟩ (by decide) (![⟨1265673, by decide⟩,⟨1256866, by decide⟩,⟨1265694, by decide⟩,⟨1265722, by decide⟩]) unmarked_context_11_92057_1265723 node_context_11_92057_1265723
  intro a
  fin_cases a
  · exact context_12_368228_1265673
  · exact context_12_368229_1256866
  · exact context_12_368230_1265694
  · exact context_12_368231_1265722

theorem selected_cut_45579 : selected 10 ⟨1265754, by decide⟩
    (prefixPartial 11 92058) = some ⟨11, 2, 0, 1265754, 92058, 1533, 262144⟩ := by
  decide +kernel

theorem context_11_92058_1265754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92058 ⟨1265754, by decide⟩ :=
  accepted_of_selected 11 92058 ⟨1265754, by decide⟩ ⟨11, 2, 0, 1265754, 92058, 1533, 262144⟩
    (by decide) selected_cut_45579

theorem selected_cut_45580 : selected 10 ⟨1265807, by decide⟩
    (prefixPartial 11 92059) = some ⟨11, 2, 0, 1265807, 92059, 2901, 262144⟩ := by
  decide +kernel

theorem context_11_92059_1265807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92059 ⟨1265807, by decide⟩ :=
  accepted_of_selected 11 92059 ⟨1265807, by decide⟩ ⟨11, 2, 0, 1265807, 92059, 2901, 262144⟩
    (by decide) selected_cut_45580

theorem unmarked_context_10_23014_1265808 : frontier 11 ⟨1265808, by decide⟩
    (prefixCache 10 23014) (prefixPartial 10 23014) = false := by
  decide +kernel

theorem node_context_10_23014_1265808 : EJMOriginalGlobalDAGData.nodes 11 ⟨1265808, by decide⟩ =
    .split (coordinate 10) (![⟨1265642, by decide⟩,⟨1265723, by decide⟩,⟨1265754, by decide⟩,⟨1265807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23014_1265808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23014 ⟨1265808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23014
    ⟨1265808, by decide⟩ (by decide) (![⟨1265642, by decide⟩,⟨1265723, by decide⟩,⟨1265754, by decide⟩,⟨1265807, by decide⟩]) unmarked_context_10_23014_1265808 node_context_10_23014_1265808
  intro a
  fin_cases a
  · exact context_11_92056_1265642
  · exact context_11_92057_1265723
  · exact context_11_92058_1265754
  · exact context_11_92059_1265807

theorem selected_cut_45581 : selected 9 ⟨1265843, by decide⟩
    (prefixPartial 12 368240) = some ⟨12, 2, 0, 1265843, 368240, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_368240_1265843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368240 ⟨1265843, by decide⟩ :=
  accepted_of_selected 12 368240 ⟨1265843, by decide⟩ ⟨12, 2, 0, 1265843, 368240, 1421, 65536⟩
    (by decide) selected_cut_45581

theorem selected_cut_45582 : selected 9 ⟨1265873, by decide⟩
    (prefixPartial 12 368241) = some ⟨12, 2, 0, 1265873, 368241, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_368241_1265873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368241 ⟨1265873, by decide⟩ :=
  accepted_of_selected 12 368241 ⟨1265873, by decide⟩ ⟨12, 2, 0, 1265873, 368241, 1413, 65536⟩
    (by decide) selected_cut_45582

theorem selected_cut_45583 : selected 9 ⟨1265892, by decide⟩
    (prefixPartial 12 368242) = some ⟨12, 2, 0, 1265892, 368242, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_368242_1265892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368242 ⟨1265892, by decide⟩ :=
  accepted_of_selected 12 368242 ⟨1265892, by decide⟩ ⟨12, 2, 0, 1265892, 368242, 1193, 65536⟩
    (by decide) selected_cut_45583

theorem selected_cut_45584 : selected 9 ⟨1265916, by decide⟩
    (prefixPartial 12 368243) = some ⟨12, 2, 0, 1265916, 368243, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_368243_1265916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368243 ⟨1265916, by decide⟩ :=
  accepted_of_selected 12 368243 ⟨1265916, by decide⟩ ⟨12, 2, 0, 1265916, 368243, 1557, 65536⟩
    (by decide) selected_cut_45584

theorem unmarked_context_11_92060_1265917 : frontier 10 ⟨1265917, by decide⟩
    (prefixCache 11 92060) (prefixPartial 11 92060) = false := by
  decide +kernel

theorem node_context_11_92060_1265917 : EJMOriginalGlobalDAGData.nodes 10 ⟨1265917, by decide⟩ =
    .split (coordinate 11) (![⟨1265843, by decide⟩,⟨1265873, by decide⟩,⟨1265892, by decide⟩,⟨1265916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92060_1265917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92060 ⟨1265917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92060
    ⟨1265917, by decide⟩ (by decide) (![⟨1265843, by decide⟩,⟨1265873, by decide⟩,⟨1265892, by decide⟩,⟨1265916, by decide⟩]) unmarked_context_11_92060_1265917 node_context_11_92060_1265917
  intro a
  fin_cases a
  · exact context_12_368240_1265843
  · exact context_12_368241_1265873
  · exact context_12_368242_1265892
  · exact context_12_368243_1265916

theorem selected_cut_45585 : selected 10 ⟨1265997, by decide⟩
    (prefixPartial 11 92061) = some ⟨11, 2, 0, 1265997, 92061, 3649, 262144⟩ := by
  decide +kernel

theorem context_11_92061_1265997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92061 ⟨1265997, by decide⟩ :=
  accepted_of_selected 11 92061 ⟨1265997, by decide⟩ ⟨11, 2, 0, 1265997, 92061, 3649, 262144⟩
    (by decide) selected_cut_45585

theorem selected_cut_45586 : selected 10 ⟨1266050, by decide⟩
    (prefixPartial 11 92062) = some ⟨11, 2, 0, 1266050, 92062, 2577, 262144⟩ := by
  decide +kernel

theorem context_11_92062_1266050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92062 ⟨1266050, by decide⟩ :=
  accepted_of_selected 11 92062 ⟨1266050, by decide⟩ ⟨11, 2, 0, 1266050, 92062, 2577, 262144⟩
    (by decide) selected_cut_45586

theorem selected_cut_45587 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 92063) = some ⟨11, 1, 0, 977886, 92063, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92063_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92063 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 92063 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 92063, 1, 262144⟩
    (by decide) selected_cut_45587

theorem unmarked_context_10_23015_1266051 : frontier 11 ⟨1266051, by decide⟩
    (prefixCache 10 23015) (prefixPartial 10 23015) = false := by
  decide +kernel

theorem node_context_10_23015_1266051 : EJMOriginalGlobalDAGData.nodes 11 ⟨1266051, by decide⟩ =
    .split (coordinate 10) (![⟨1265917, by decide⟩,⟨1265997, by decide⟩,⟨1266050, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23015_1266051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23015 ⟨1266051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23015
    ⟨1266051, by decide⟩ (by decide) (![⟨1265917, by decide⟩,⟨1265997, by decide⟩,⟨1266050, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23015_1266051 node_context_10_23015_1266051
  intro a
  fin_cases a
  · exact context_11_92060_1265917
  · exact context_11_92061_1265997
  · exact context_11_92062_1266050
  · exact context_11_92063_977886

theorem unmarked_context_9_5753_1266052 : frontier 12 ⟨1266052, by decide⟩
    (prefixCache 9 5753) (prefixPartial 9 5753) = false := by
  decide +kernel

theorem node_context_9_5753_1266052 : EJMOriginalGlobalDAGData.nodes 12 ⟨1266052, by decide⟩ =
    .split (coordinate 9) (![⟨1265543, by decide⟩,⟨893098, by decide⟩,⟨1265808, by decide⟩,⟨1266051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5753_1266052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5753 ⟨1266052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5753
    ⟨1266052, by decide⟩ (by decide) (![⟨1265543, by decide⟩,⟨893098, by decide⟩,⟨1265808, by decide⟩,⟨1266051, by decide⟩]) unmarked_context_9_5753_1266052 node_context_9_5753_1266052
  intro a
  fin_cases a
  · exact context_10_23012_1265543
  · exact context_10_23013_893098
  · exact context_10_23014_1265808
  · exact context_10_23015_1266051

theorem selected_cut_45588 : selected 10 ⟨1266092, by decide⟩
    (prefixPartial 11 92064) = some ⟨11, 2, 0, 1266092, 92064, 2469, 262144⟩ := by
  decide +kernel

theorem context_11_92064_1266092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92064 ⟨1266092, by decide⟩ :=
  accepted_of_selected 11 92064 ⟨1266092, by decide⟩ ⟨11, 2, 0, 1266092, 92064, 2469, 262144⟩
    (by decide) selected_cut_45588

theorem selected_cut_45589 : selected 10 ⟨1266140, by decide⟩
    (prefixPartial 11 92065) = some ⟨11, 2, 0, 1266140, 92065, 2473, 262144⟩ := by
  decide +kernel

theorem context_11_92065_1266140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92065 ⟨1266140, by decide⟩ :=
  accepted_of_selected 11 92065 ⟨1266140, by decide⟩ ⟨11, 2, 0, 1266140, 92065, 2473, 262144⟩
    (by decide) selected_cut_45589

theorem selected_cut_45590 : selected 10 ⟨1266199, by decide⟩
    (prefixPartial 11 92066) = some ⟨11, 2, 0, 1266199, 92066, 3321, 262144⟩ := by
  decide +kernel

theorem context_11_92066_1266199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92066 ⟨1266199, by decide⟩ :=
  accepted_of_selected 11 92066 ⟨1266199, by decide⟩ ⟨11, 2, 0, 1266199, 92066, 3321, 262144⟩
    (by decide) selected_cut_45590

theorem selected_cut_45591 : selected 10 ⟨1266235, by decide⟩
    (prefixPartial 11 92067) = some ⟨11, 2, 0, 1266235, 92067, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_92067_1266235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92067 ⟨1266235, by decide⟩ :=
  accepted_of_selected 11 92067 ⟨1266235, by decide⟩ ⟨11, 2, 0, 1266235, 92067, 2109, 262144⟩
    (by decide) selected_cut_45591

theorem unmarked_context_10_23016_1266236 : frontier 11 ⟨1266236, by decide⟩
    (prefixCache 10 23016) (prefixPartial 10 23016) = false := by
  decide +kernel

theorem node_context_10_23016_1266236 : EJMOriginalGlobalDAGData.nodes 11 ⟨1266236, by decide⟩ =
    .split (coordinate 10) (![⟨1266092, by decide⟩,⟨1266140, by decide⟩,⟨1266199, by decide⟩,⟨1266235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23016_1266236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23016 ⟨1266236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23016
    ⟨1266236, by decide⟩ (by decide) (![⟨1266092, by decide⟩,⟨1266140, by decide⟩,⟨1266199, by decide⟩,⟨1266235, by decide⟩]) unmarked_context_10_23016_1266236 node_context_10_23016_1266236
  intro a
  fin_cases a
  · exact context_11_92064_1266092
  · exact context_11_92065_1266140
  · exact context_11_92066_1266199
  · exact context_11_92067_1266235

theorem selected_cut_45592 : selected 10 ⟨1266276, by decide⟩
    (prefixPartial 11 92068) = some ⟨11, 2, 0, 1266276, 92068, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_92068_1266276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92068 ⟨1266276, by decide⟩ :=
  accepted_of_selected 11 92068 ⟨1266276, by decide⟩ ⟨11, 2, 0, 1266276, 92068, 2233, 262144⟩
    (by decide) selected_cut_45592

theorem selected_cut_45593 : selected 10 ⟨1266314, by decide⟩
    (prefixPartial 11 92069) = some ⟨11, 2, 0, 1266314, 92069, 1869, 262144⟩ := by
  decide +kernel

theorem context_11_92069_1266314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92069 ⟨1266314, by decide⟩ :=
  accepted_of_selected 11 92069 ⟨1266314, by decide⟩ ⟨11, 2, 0, 1266314, 92069, 1869, 262144⟩
    (by decide) selected_cut_45593

theorem selected_cut_45594 : selected 10 ⟨1266365, by decide⟩
    (prefixPartial 11 92070) = some ⟨11, 2, 0, 1266365, 92070, 2529, 262144⟩ := by
  decide +kernel

theorem context_11_92070_1266365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92070 ⟨1266365, by decide⟩ :=
  accepted_of_selected 11 92070 ⟨1266365, by decide⟩ ⟨11, 2, 0, 1266365, 92070, 2529, 262144⟩
    (by decide) selected_cut_45594

theorem selected_cut_45595 : selected 10 ⟨1266395, by decide⟩
    (prefixPartial 11 92071) = some ⟨11, 2, 0, 1266395, 92071, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_92071_1266395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92071 ⟨1266395, by decide⟩ :=
  accepted_of_selected 11 92071 ⟨1266395, by decide⟩ ⟨11, 2, 0, 1266395, 92071, 1641, 262144⟩
    (by decide) selected_cut_45595

theorem unmarked_context_10_23017_1266396 : frontier 11 ⟨1266396, by decide⟩
    (prefixCache 10 23017) (prefixPartial 10 23017) = false := by
  decide +kernel

theorem node_context_10_23017_1266396 : EJMOriginalGlobalDAGData.nodes 11 ⟨1266396, by decide⟩ =
    .split (coordinate 10) (![⟨1266276, by decide⟩,⟨1266314, by decide⟩,⟨1266365, by decide⟩,⟨1266395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23017_1266396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23017 ⟨1266396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23017
    ⟨1266396, by decide⟩ (by decide) (![⟨1266276, by decide⟩,⟨1266314, by decide⟩,⟨1266365, by decide⟩,⟨1266395, by decide⟩]) unmarked_context_10_23017_1266396 node_context_10_23017_1266396
  intro a
  fin_cases a
  · exact context_11_92068_1266276
  · exact context_11_92069_1266314
  · exact context_11_92070_1266365
  · exact context_11_92071_1266395

theorem selected_cut_45596 : selected 11 ⟨1266450, by decide⟩
    (prefixPartial 10 23018) = some ⟨10, 2, 0, 1266450, 23018, 2773, 1048576⟩ := by
  decide +kernel

theorem context_10_23018_1266450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23018 ⟨1266450, by decide⟩ :=
  accepted_of_selected 10 23018 ⟨1266450, by decide⟩ ⟨10, 2, 0, 1266450, 23018, 2773, 1048576⟩
    (by decide) selected_cut_45596

theorem selected_cut_45597 : selected 10 ⟨1266470, by decide⟩
    (prefixPartial 11 92076) = some ⟨11, 2, 0, 1266470, 92076, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_92076_1266470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92076 ⟨1266470, by decide⟩ :=
  accepted_of_selected 11 92076 ⟨1266470, by decide⟩ ⟨11, 2, 0, 1266470, 92076, 1429, 262144⟩
    (by decide) selected_cut_45597

theorem selected_cut_45598 : selected 10 ⟨1266493, by decide⟩
    (prefixPartial 11 92077) = some ⟨11, 2, 0, 1266493, 92077, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_92077_1266493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92077 ⟨1266493, by decide⟩ :=
  accepted_of_selected 11 92077 ⟨1266493, by decide⟩ ⟨11, 2, 0, 1266493, 92077, 1101, 262144⟩
    (by decide) selected_cut_45598

theorem selected_cut_45599 : selected 10 ⟨1266523, by decide⟩
    (prefixPartial 11 92078) = some ⟨11, 2, 0, 1266523, 92078, 1617, 262144⟩ := by
  decide +kernel

theorem context_11_92078_1266523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92078 ⟨1266523, by decide⟩ :=
  accepted_of_selected 11 92078 ⟨1266523, by decide⟩ ⟨11, 2, 0, 1266523, 92078, 1617, 262144⟩
    (by decide) selected_cut_45599

theorem selected_cut_45600 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 92079) = some ⟨11, 1, 0, 977886, 92079, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92079_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92079 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 92079 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 92079, 1, 262144⟩
    (by decide) selected_cut_45600

theorem unmarked_context_10_23019_1266524 : frontier 11 ⟨1266524, by decide⟩
    (prefixCache 10 23019) (prefixPartial 10 23019) = false := by
  decide +kernel

theorem node_context_10_23019_1266524 : EJMOriginalGlobalDAGData.nodes 11 ⟨1266524, by decide⟩ =
    .split (coordinate 10) (![⟨1266470, by decide⟩,⟨1266493, by decide⟩,⟨1266523, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23019_1266524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23019 ⟨1266524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23019
    ⟨1266524, by decide⟩ (by decide) (![⟨1266470, by decide⟩,⟨1266493, by decide⟩,⟨1266523, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23019_1266524 node_context_10_23019_1266524
  intro a
  fin_cases a
  · exact context_11_92076_1266470
  · exact context_11_92077_1266493
  · exact context_11_92078_1266523
  · exact context_11_92079_977886

theorem unmarked_context_9_5754_1266525 : frontier 12 ⟨1266525, by decide⟩
    (prefixCache 9 5754) (prefixPartial 9 5754) = false := by
  decide +kernel

theorem node_context_9_5754_1266525 : EJMOriginalGlobalDAGData.nodes 12 ⟨1266525, by decide⟩ =
    .split (coordinate 9) (![⟨1266236, by decide⟩,⟨1266396, by decide⟩,⟨1266450, by decide⟩,⟨1266524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5754_1266525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5754 ⟨1266525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5754
    ⟨1266525, by decide⟩ (by decide) (![⟨1266236, by decide⟩,⟨1266396, by decide⟩,⟨1266450, by decide⟩,⟨1266524, by decide⟩]) unmarked_context_9_5754_1266525 node_context_9_5754_1266525
  intro a
  fin_cases a
  · exact context_10_23016_1266236
  · exact context_10_23017_1266396
  · exact context_10_23018_1266450
  · exact context_10_23019_1266524

theorem selected_cut_45601 : selected 10 ⟨1266556, by decide⟩
    (prefixPartial 11 92080) = some ⟨11, 2, 0, 1266556, 92080, 1173, 262144⟩ := by
  decide +kernel

theorem context_11_92080_1266556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92080 ⟨1266556, by decide⟩ :=
  accepted_of_selected 11 92080 ⟨1266556, by decide⟩ ⟨11, 2, 0, 1266556, 92080, 1173, 262144⟩
    (by decide) selected_cut_45601

theorem selected_cut_45602 : selected 10 ⟨1266588, by decide⟩
    (prefixPartial 11 92081) = some ⟨11, 2, 0, 1266588, 92081, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_92081_1266588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92081 ⟨1266588, by decide⟩ :=
  accepted_of_selected 11 92081 ⟨1266588, by decide⟩ ⟨11, 2, 0, 1266588, 92081, 2253, 262144⟩
    (by decide) selected_cut_45602

theorem selected_cut_45603 : selected 10 ⟨1266599, by decide⟩
    (prefixPartial 11 92082) = some ⟨11, 2, 0, 1266599, 92082, 709, 262144⟩ := by
  decide +kernel

theorem context_11_92082_1266599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92082 ⟨1266599, by decide⟩ :=
  accepted_of_selected 11 92082 ⟨1266599, by decide⟩ ⟨11, 2, 0, 1266599, 92082, 709, 262144⟩
    (by decide) selected_cut_45603

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
