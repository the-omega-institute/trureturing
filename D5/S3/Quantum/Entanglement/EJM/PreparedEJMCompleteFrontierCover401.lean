/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover400
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38499 : selected 8 ⟨1038030, by decide⟩
    (prefixPartial 13 1206324) = some ⟨13, 2, 0, 1038030, 1206324, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_1206324_1038030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206324 ⟨1038030, by decide⟩ :=
  accepted_of_selected 13 1206324 ⟨1038030, by decide⟩ ⟨13, 2, 0, 1038030, 1206324, 1737, 16384⟩
    (by decide) selected_cut_38499

theorem selected_cut_38500 : selected 8 ⟨1038053, by decide⟩
    (prefixPartial 13 1206325) = some ⟨13, 2, 0, 1038053, 1206325, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_1206325_1038053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206325 ⟨1038053, by decide⟩ :=
  accepted_of_selected 13 1206325 ⟨1038053, by decide⟩ ⟨13, 2, 0, 1038053, 1206325, 1205, 16384⟩
    (by decide) selected_cut_38500

theorem selected_cut_38501 : selected 8 ⟨1038074, by decide⟩
    (prefixPartial 13 1206326) = some ⟨13, 2, 0, 1038074, 1206326, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_1206326_1038074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206326 ⟨1038074, by decide⟩ :=
  accepted_of_selected 13 1206326 ⟨1038074, by decide⟩ ⟨13, 2, 0, 1038074, 1206326, 1121, 16384⟩
    (by decide) selected_cut_38501

theorem selected_cut_38502 : selected 8 ⟨1038089, by decide⟩
    (prefixPartial 13 1206327) = some ⟨13, 2, 0, 1038089, 1206327, 725, 16384⟩ := by
  decide +kernel

theorem context_13_1206327_1038089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206327 ⟨1038089, by decide⟩ :=
  accepted_of_selected 13 1206327 ⟨1038089, by decide⟩ ⟨13, 2, 0, 1038089, 1206327, 725, 16384⟩
    (by decide) selected_cut_38502

theorem unmarked_context_12_301581_1038090 : frontier 9 ⟨1038090, by decide⟩
    (prefixCache 12 301581) (prefixPartial 12 301581) = false := by
  decide +kernel

theorem node_context_12_301581_1038090 : EJMOriginalGlobalDAGData.nodes 9 ⟨1038090, by decide⟩ =
    .split (coordinate 12) (![⟨1038030, by decide⟩,⟨1038053, by decide⟩,⟨1038074, by decide⟩,⟨1038089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301581_1038090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301581 ⟨1038090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301581
    ⟨1038090, by decide⟩ (by decide) (![⟨1038030, by decide⟩,⟨1038053, by decide⟩,⟨1038074, by decide⟩,⟨1038089, by decide⟩]) unmarked_context_12_301581_1038090 node_context_12_301581_1038090
  intro a
  fin_cases a
  · exact context_13_1206324_1038030
  · exact context_13_1206325_1038053
  · exact context_13_1206326_1038074
  · exact context_13_1206327_1038089

theorem selected_cut_38503 : selected 8 ⟨1038118, by decide⟩
    (prefixPartial 13 1206328) = some ⟨13, 2, 0, 1038118, 1206328, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_1206328_1038118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206328 ⟨1038118, by decide⟩ :=
  accepted_of_selected 13 1206328 ⟨1038118, by decide⟩ ⟨13, 2, 0, 1038118, 1206328, 1489, 16384⟩
    (by decide) selected_cut_38503

theorem selected_cut_38504 : selected 8 ⟨1038142, by decide⟩
    (prefixPartial 13 1206329) = some ⟨13, 2, 0, 1038142, 1206329, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_1206329_1038142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206329 ⟨1038142, by decide⟩ :=
  accepted_of_selected 13 1206329 ⟨1038142, by decide⟩ ⟨13, 2, 0, 1038142, 1206329, 1205, 16384⟩
    (by decide) selected_cut_38504

theorem selected_cut_38505 : selected 8 ⟨1038160, by decide⟩
    (prefixPartial 13 1206330) = some ⟨13, 2, 0, 1038160, 1206330, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_1206330_1038160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206330 ⟨1038160, by decide⟩ :=
  accepted_of_selected 13 1206330 ⟨1038160, by decide⟩ ⟨13, 2, 0, 1038160, 1206330, 1097, 16384⟩
    (by decide) selected_cut_38505

theorem selected_cut_38506 : selected 8 ⟨1038170, by decide⟩
    (prefixPartial 13 1206331) = some ⟨13, 2, 0, 1038170, 1206331, 601, 16384⟩ := by
  decide +kernel

theorem context_13_1206331_1038170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206331 ⟨1038170, by decide⟩ :=
  accepted_of_selected 13 1206331 ⟨1038170, by decide⟩ ⟨13, 2, 0, 1038170, 1206331, 601, 16384⟩
    (by decide) selected_cut_38506

theorem unmarked_context_12_301582_1038171 : frontier 9 ⟨1038171, by decide⟩
    (prefixCache 12 301582) (prefixPartial 12 301582) = false := by
  decide +kernel

theorem node_context_12_301582_1038171 : EJMOriginalGlobalDAGData.nodes 9 ⟨1038171, by decide⟩ =
    .split (coordinate 12) (![⟨1038118, by decide⟩,⟨1038142, by decide⟩,⟨1038160, by decide⟩,⟨1038170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301582_1038171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301582 ⟨1038171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301582
    ⟨1038171, by decide⟩ (by decide) (![⟨1038118, by decide⟩,⟨1038142, by decide⟩,⟨1038160, by decide⟩,⟨1038170, by decide⟩]) unmarked_context_12_301582_1038171 node_context_12_301582_1038171
  intro a
  fin_cases a
  · exact context_13_1206328_1038118
  · exact context_13_1206329_1038142
  · exact context_13_1206330_1038160
  · exact context_13_1206331_1038170

theorem selected_cut_38507 : selected 8 ⟨1038204, by decide⟩
    (prefixPartial 13 1206332) = some ⟨13, 2, 0, 1038204, 1206332, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_1206332_1038204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206332 ⟨1038204, by decide⟩ :=
  accepted_of_selected 13 1206332 ⟨1038204, by decide⟩ ⟨13, 2, 0, 1038204, 1206332, 1441, 16384⟩
    (by decide) selected_cut_38507

theorem selected_cut_38508 : selected 8 ⟨1038225, by decide⟩
    (prefixPartial 13 1206333) = some ⟨13, 2, 0, 1038225, 1206333, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_1206333_1038225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206333 ⟨1038225, by decide⟩ :=
  accepted_of_selected 13 1206333 ⟨1038225, by decide⟩ ⟨13, 2, 0, 1038225, 1206333, 1085, 16384⟩
    (by decide) selected_cut_38508

theorem selected_cut_38509 : selected 8 ⟨1038244, by decide⟩
    (prefixPartial 13 1206334) = some ⟨13, 2, 0, 1038244, 1206334, 973, 16384⟩ := by
  decide +kernel

theorem context_13_1206334_1038244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206334 ⟨1038244, by decide⟩ :=
  accepted_of_selected 13 1206334 ⟨1038244, by decide⟩ ⟨13, 2, 0, 1038244, 1206334, 973, 16384⟩
    (by decide) selected_cut_38509

theorem selected_cut_38510 : selected 8 ⟨1038253, by decide⟩
    (prefixPartial 13 1206335) = some ⟨13, 2, 0, 1038253, 1206335, 701, 16384⟩ := by
  decide +kernel

theorem context_13_1206335_1038253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206335 ⟨1038253, by decide⟩ :=
  accepted_of_selected 13 1206335 ⟨1038253, by decide⟩ ⟨13, 2, 0, 1038253, 1206335, 701, 16384⟩
    (by decide) selected_cut_38510

theorem unmarked_context_12_301583_1038254 : frontier 9 ⟨1038254, by decide⟩
    (prefixCache 12 301583) (prefixPartial 12 301583) = false := by
  decide +kernel

theorem node_context_12_301583_1038254 : EJMOriginalGlobalDAGData.nodes 9 ⟨1038254, by decide⟩ =
    .split (coordinate 12) (![⟨1038204, by decide⟩,⟨1038225, by decide⟩,⟨1038244, by decide⟩,⟨1038253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301583_1038254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301583 ⟨1038254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301583
    ⟨1038254, by decide⟩ (by decide) (![⟨1038204, by decide⟩,⟨1038225, by decide⟩,⟨1038244, by decide⟩,⟨1038253, by decide⟩]) unmarked_context_12_301583_1038254 node_context_12_301583_1038254
  intro a
  fin_cases a
  · exact context_13_1206332_1038204
  · exact context_13_1206333_1038225
  · exact context_13_1206334_1038244
  · exact context_13_1206335_1038253

theorem unmarked_context_11_75395_1038255 : frontier 10 ⟨1038255, by decide⟩
    (prefixCache 11 75395) (prefixPartial 11 75395) = false := by
  decide +kernel

theorem node_context_11_75395_1038255 : EJMOriginalGlobalDAGData.nodes 10 ⟨1038255, by decide⟩ =
    .split (coordinate 11) (![⟨1037994, by decide⟩,⟨1038090, by decide⟩,⟨1038171, by decide⟩,⟨1038254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75395_1038255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75395 ⟨1038255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75395
    ⟨1038255, by decide⟩ (by decide) (![⟨1037994, by decide⟩,⟨1038090, by decide⟩,⟨1038171, by decide⟩,⟨1038254, by decide⟩]) unmarked_context_11_75395_1038255 node_context_11_75395_1038255
  intro a
  fin_cases a
  · exact context_12_301580_1037994
  · exact context_12_301581_1038090
  · exact context_12_301582_1038171
  · exact context_12_301583_1038254

theorem unmarked_context_10_18848_1038256 : frontier 11 ⟨1038256, by decide⟩
    (prefixCache 10 18848) (prefixPartial 10 18848) = false := by
  decide +kernel

theorem node_context_10_18848_1038256 : EJMOriginalGlobalDAGData.nodes 11 ⟨1038256, by decide⟩ =
    .split (coordinate 10) (![⟨1037357, by decide⟩,⟨1037723, by decide⟩,⟨1037896, by decide⟩,⟨1038255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18848_1038256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18848 ⟨1038256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18848
    ⟨1038256, by decide⟩ (by decide) (![⟨1037357, by decide⟩,⟨1037723, by decide⟩,⟨1037896, by decide⟩,⟨1038255, by decide⟩]) unmarked_context_10_18848_1038256 node_context_10_18848_1038256
  intro a
  fin_cases a
  · exact context_11_75392_1037357
  · exact context_11_75393_1037723
  · exact context_11_75394_1037896
  · exact context_11_75395_1038255

theorem selected_cut_38511 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 301584) = some ⟨12, 1, 0, 994572, 301584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301584_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301584 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 301584 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 301584, 1, 65536⟩
    (by decide) selected_cut_38511

theorem selected_cut_38512 : selected 9 ⟨1038326, by decide⟩
    (prefixPartial 12 301585) = some ⟨12, 2, 0, 1038326, 301585, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_301585_1038326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301585 ⟨1038326, by decide⟩ :=
  accepted_of_selected 12 301585 ⟨1038326, by decide⟩ ⟨12, 2, 0, 1038326, 301585, 3537, 65536⟩
    (by decide) selected_cut_38512

theorem selected_cut_38513 : selected 9 ⟨1038377, by decide⟩
    (prefixPartial 12 301586) = some ⟨12, 2, 0, 1038377, 301586, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_301586_1038377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301586 ⟨1038377, by decide⟩ :=
  accepted_of_selected 12 301586 ⟨1038377, by decide⟩ ⟨12, 2, 0, 1038377, 301586, 2965, 65536⟩
    (by decide) selected_cut_38513

theorem selected_cut_38514 : selected 9 ⟨1038438, by decide⟩
    (prefixPartial 12 301587) = some ⟨12, 2, 0, 1038438, 301587, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_301587_1038438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301587 ⟨1038438, by decide⟩ :=
  accepted_of_selected 12 301587 ⟨1038438, by decide⟩ ⟨12, 2, 0, 1038438, 301587, 3529, 65536⟩
    (by decide) selected_cut_38514

theorem unmarked_context_11_75396_1038439 : frontier 10 ⟨1038439, by decide⟩
    (prefixCache 11 75396) (prefixPartial 11 75396) = false := by
  decide +kernel

theorem node_context_11_75396_1038439 : EJMOriginalGlobalDAGData.nodes 10 ⟨1038439, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1038326, by decide⟩,⟨1038377, by decide⟩,⟨1038438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75396_1038439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75396 ⟨1038439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75396
    ⟨1038439, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1038326, by decide⟩,⟨1038377, by decide⟩,⟨1038438, by decide⟩]) unmarked_context_11_75396_1038439 node_context_11_75396_1038439
  intro a
  fin_cases a
  · exact context_12_301584_994572
  · exact context_12_301585_1038326
  · exact context_12_301586_1038377
  · exact context_12_301587_1038438

theorem selected_cut_38515 : selected 9 ⟨1038501, by decide⟩
    (prefixPartial 12 301588) = some ⟨12, 2, 0, 1038501, 301588, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_301588_1038501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301588 ⟨1038501, by decide⟩ :=
  accepted_of_selected 12 301588 ⟨1038501, by decide⟩ ⟨12, 2, 0, 1038501, 301588, 3237, 65536⟩
    (by decide) selected_cut_38515

theorem selected_cut_38516 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 301589) = some ⟨12, 1, 0, 692793, 301589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301589_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301589 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 301589 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 301589, 1, 65536⟩
    (by decide) selected_cut_38516

theorem selected_cut_38517 : selected 9 ⟨1038559, by decide⟩
    (prefixPartial 12 301590) = some ⟨12, 2, 0, 1038559, 301590, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_301590_1038559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301590 ⟨1038559, by decide⟩ :=
  accepted_of_selected 12 301590 ⟨1038559, by decide⟩ ⟨12, 2, 0, 1038559, 301590, 3061, 65536⟩
    (by decide) selected_cut_38517

theorem selected_cut_38518 : selected 9 ⟨1038635, by decide⟩
    (prefixPartial 12 301591) = some ⟨12, 2, 0, 1038635, 301591, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_301591_1038635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301591 ⟨1038635, by decide⟩ :=
  accepted_of_selected 12 301591 ⟨1038635, by decide⟩ ⟨12, 2, 0, 1038635, 301591, 3721, 65536⟩
    (by decide) selected_cut_38518

theorem unmarked_context_11_75397_1038636 : frontier 10 ⟨1038636, by decide⟩
    (prefixCache 11 75397) (prefixPartial 11 75397) = false := by
  decide +kernel

theorem node_context_11_75397_1038636 : EJMOriginalGlobalDAGData.nodes 10 ⟨1038636, by decide⟩ =
    .split (coordinate 11) (![⟨1038501, by decide⟩,⟨692793, by decide⟩,⟨1038559, by decide⟩,⟨1038635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75397_1038636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75397 ⟨1038636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75397
    ⟨1038636, by decide⟩ (by decide) (![⟨1038501, by decide⟩,⟨692793, by decide⟩,⟨1038559, by decide⟩,⟨1038635, by decide⟩]) unmarked_context_11_75397_1038636 node_context_11_75397_1038636
  intro a
  fin_cases a
  · exact context_12_301588_1038501
  · exact context_12_301589_692793
  · exact context_12_301590_1038559
  · exact context_12_301591_1038635

theorem selected_cut_38519 : selected 9 ⟨1038687, by decide⟩
    (prefixPartial 12 301592) = some ⟨12, 2, 0, 1038687, 301592, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_301592_1038687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301592 ⟨1038687, by decide⟩ :=
  accepted_of_selected 12 301592 ⟨1038687, by decide⟩ ⟨12, 2, 0, 1038687, 301592, 2957, 65536⟩
    (by decide) selected_cut_38519

theorem selected_cut_38520 : selected 9 ⟨1038759, by decide⟩
    (prefixPartial 12 301593) = some ⟨12, 2, 0, 1038759, 301593, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_301593_1038759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301593 ⟨1038759, by decide⟩ :=
  accepted_of_selected 12 301593 ⟨1038759, by decide⟩ ⟨12, 2, 0, 1038759, 301593, 3601, 65536⟩
    (by decide) selected_cut_38520

theorem selected_cut_38521 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 301594) = some ⟨12, 1, 0, 893903, 301594, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301594_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301594 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 301594 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 301594, 1, 65536⟩
    (by decide) selected_cut_38521

theorem selected_cut_38522 : selected 9 ⟨1038824, by decide⟩
    (prefixPartial 12 301595) = some ⟨12, 2, 0, 1038824, 301595, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_301595_1038824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301595 ⟨1038824, by decide⟩ :=
  accepted_of_selected 12 301595 ⟨1038824, by decide⟩ ⟨12, 2, 0, 1038824, 301595, 3629, 65536⟩
    (by decide) selected_cut_38522

theorem unmarked_context_11_75398_1038825 : frontier 10 ⟨1038825, by decide⟩
    (prefixCache 11 75398) (prefixPartial 11 75398) = false := by
  decide +kernel

theorem node_context_11_75398_1038825 : EJMOriginalGlobalDAGData.nodes 10 ⟨1038825, by decide⟩ =
    .split (coordinate 11) (![⟨1038687, by decide⟩,⟨1038759, by decide⟩,⟨893903, by decide⟩,⟨1038824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75398_1038825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75398 ⟨1038825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75398
    ⟨1038825, by decide⟩ (by decide) (![⟨1038687, by decide⟩,⟨1038759, by decide⟩,⟨893903, by decide⟩,⟨1038824, by decide⟩]) unmarked_context_11_75398_1038825 node_context_11_75398_1038825
  intro a
  fin_cases a
  · exact context_12_301592_1038687
  · exact context_12_301593_1038759
  · exact context_12_301594_893903
  · exact context_12_301595_1038824

theorem selected_cut_38523 : selected 9 ⟨1038889, by decide⟩
    (prefixPartial 12 301596) = some ⟨12, 2, 0, 1038889, 301596, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_301596_1038889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301596 ⟨1038889, by decide⟩ :=
  accepted_of_selected 12 301596 ⟨1038889, by decide⟩ ⟨12, 2, 0, 1038889, 301596, 3461, 65536⟩
    (by decide) selected_cut_38523

theorem selected_cut_38524 : selected 9 ⟨1038969, by decide⟩
    (prefixPartial 12 301597) = some ⟨12, 2, 0, 1038969, 301597, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_301597_1038969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301597 ⟨1038969, by decide⟩ :=
  accepted_of_selected 12 301597 ⟨1038969, by decide⟩ ⟨12, 2, 0, 1038969, 301597, 3937, 65536⟩
    (by decide) selected_cut_38524

theorem selected_cut_38525 : selected 9 ⟨1039031, by decide⟩
    (prefixPartial 12 301598) = some ⟨12, 2, 0, 1039031, 301598, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_301598_1039031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301598 ⟨1039031, by decide⟩ :=
  accepted_of_selected 12 301598 ⟨1039031, by decide⟩ ⟨12, 2, 0, 1039031, 301598, 3513, 65536⟩
    (by decide) selected_cut_38525

theorem selected_cut_38526 : selected 9 ⟨1039100, by decide⟩
    (prefixPartial 12 301599) = some ⟨12, 2, 0, 1039100, 301599, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_301599_1039100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301599 ⟨1039100, by decide⟩ :=
  accepted_of_selected 12 301599 ⟨1039100, by decide⟩ ⟨12, 2, 0, 1039100, 301599, 3637, 65536⟩
    (by decide) selected_cut_38526

theorem unmarked_context_11_75399_1039101 : frontier 10 ⟨1039101, by decide⟩
    (prefixCache 11 75399) (prefixPartial 11 75399) = false := by
  decide +kernel

theorem node_context_11_75399_1039101 : EJMOriginalGlobalDAGData.nodes 10 ⟨1039101, by decide⟩ =
    .split (coordinate 11) (![⟨1038889, by decide⟩,⟨1038969, by decide⟩,⟨1039031, by decide⟩,⟨1039100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75399_1039101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75399 ⟨1039101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75399
    ⟨1039101, by decide⟩ (by decide) (![⟨1038889, by decide⟩,⟨1038969, by decide⟩,⟨1039031, by decide⟩,⟨1039100, by decide⟩]) unmarked_context_11_75399_1039101 node_context_11_75399_1039101
  intro a
  fin_cases a
  · exact context_12_301596_1038889
  · exact context_12_301597_1038969
  · exact context_12_301598_1039031
  · exact context_12_301599_1039100

theorem unmarked_context_10_18849_1039102 : frontier 11 ⟨1039102, by decide⟩
    (prefixCache 10 18849) (prefixPartial 10 18849) = false := by
  decide +kernel

theorem node_context_10_18849_1039102 : EJMOriginalGlobalDAGData.nodes 11 ⟨1039102, by decide⟩ =
    .split (coordinate 10) (![⟨1038439, by decide⟩,⟨1038636, by decide⟩,⟨1038825, by decide⟩,⟨1039101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18849_1039102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18849 ⟨1039102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18849
    ⟨1039102, by decide⟩ (by decide) (![⟨1038439, by decide⟩,⟨1038636, by decide⟩,⟨1038825, by decide⟩,⟨1039101, by decide⟩]) unmarked_context_10_18849_1039102 node_context_10_18849_1039102
  intro a
  fin_cases a
  · exact context_11_75396_1038439
  · exact context_11_75397_1038636
  · exact context_11_75398_1038825
  · exact context_11_75399_1039101

theorem selected_cut_38527 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 301600) = some ⟨12, 1, 0, 994572, 301600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301600_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301600 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 301600 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 301600, 1, 65536⟩
    (by decide) selected_cut_38527

theorem selected_cut_38528 : selected 9 ⟨1039158, by decide⟩
    (prefixPartial 12 301601) = some ⟨12, 2, 0, 1039158, 301601, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_301601_1039158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301601 ⟨1039158, by decide⟩ :=
  accepted_of_selected 12 301601 ⟨1039158, by decide⟩ ⟨12, 2, 0, 1039158, 301601, 3101, 65536⟩
    (by decide) selected_cut_38528

theorem selected_cut_38529 : selected 9 ⟨1039207, by decide⟩
    (prefixPartial 12 301602) = some ⟨12, 2, 0, 1039207, 301602, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_301602_1039207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301602 ⟨1039207, by decide⟩ :=
  accepted_of_selected 12 301602 ⟨1039207, by decide⟩ ⟨12, 2, 0, 1039207, 301602, 2405, 65536⟩
    (by decide) selected_cut_38529

theorem selected_cut_38530 : selected 9 ⟨1039255, by decide⟩
    (prefixPartial 12 301603) = some ⟨12, 2, 0, 1039255, 301603, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_301603_1039255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301603 ⟨1039255, by decide⟩ :=
  accepted_of_selected 12 301603 ⟨1039255, by decide⟩ ⟨12, 2, 0, 1039255, 301603, 2945, 65536⟩
    (by decide) selected_cut_38530

theorem unmarked_context_11_75400_1039256 : frontier 10 ⟨1039256, by decide⟩
    (prefixCache 11 75400) (prefixPartial 11 75400) = false := by
  decide +kernel

theorem node_context_11_75400_1039256 : EJMOriginalGlobalDAGData.nodes 10 ⟨1039256, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1039158, by decide⟩,⟨1039207, by decide⟩,⟨1039255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75400_1039256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75400 ⟨1039256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75400
    ⟨1039256, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1039158, by decide⟩,⟨1039207, by decide⟩,⟨1039255, by decide⟩]) unmarked_context_11_75400_1039256 node_context_11_75400_1039256
  intro a
  fin_cases a
  · exact context_12_301600_994572
  · exact context_12_301601_1039158
  · exact context_12_301602_1039207
  · exact context_12_301603_1039255

theorem selected_cut_38531 : selected 9 ⟨1039313, by decide⟩
    (prefixPartial 12 301604) = some ⟨12, 2, 0, 1039313, 301604, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_301604_1039313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301604 ⟨1039313, by decide⟩ :=
  accepted_of_selected 12 301604 ⟨1039313, by decide⟩ ⟨12, 2, 0, 1039313, 301604, 3061, 65536⟩
    (by decide) selected_cut_38531

theorem selected_cut_38532 : selected 9 ⟨1039380, by decide⟩
    (prefixPartial 12 301605) = some ⟨12, 2, 0, 1039380, 301605, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_301605_1039380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301605 ⟨1039380, by decide⟩ :=
  accepted_of_selected 12 301605 ⟨1039380, by decide⟩ ⟨12, 2, 0, 1039380, 301605, 3397, 65536⟩
    (by decide) selected_cut_38532

theorem selected_cut_38533 : selected 9 ⟨1039428, by decide⟩
    (prefixPartial 12 301606) = some ⟨12, 2, 0, 1039428, 301606, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_301606_1039428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301606 ⟨1039428, by decide⟩ :=
  accepted_of_selected 12 301606 ⟨1039428, by decide⟩ ⟨12, 2, 0, 1039428, 301606, 2569, 65536⟩
    (by decide) selected_cut_38533

theorem selected_cut_38534 : selected 9 ⟨1039487, by decide⟩
    (prefixPartial 12 301607) = some ⟨12, 2, 0, 1039487, 301607, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_301607_1039487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301607 ⟨1039487, by decide⟩ :=
  accepted_of_selected 12 301607 ⟨1039487, by decide⟩ ⟨12, 2, 0, 1039487, 301607, 3169, 65536⟩
    (by decide) selected_cut_38534

theorem unmarked_context_11_75401_1039488 : frontier 10 ⟨1039488, by decide⟩
    (prefixCache 11 75401) (prefixPartial 11 75401) = false := by
  decide +kernel

theorem node_context_11_75401_1039488 : EJMOriginalGlobalDAGData.nodes 10 ⟨1039488, by decide⟩ =
    .split (coordinate 11) (![⟨1039313, by decide⟩,⟨1039380, by decide⟩,⟨1039428, by decide⟩,⟨1039487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75401_1039488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75401 ⟨1039488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75401
    ⟨1039488, by decide⟩ (by decide) (![⟨1039313, by decide⟩,⟨1039380, by decide⟩,⟨1039428, by decide⟩,⟨1039487, by decide⟩]) unmarked_context_11_75401_1039488 node_context_11_75401_1039488
  intro a
  fin_cases a
  · exact context_12_301604_1039313
  · exact context_12_301605_1039380
  · exact context_12_301606_1039428
  · exact context_12_301607_1039487

theorem selected_cut_38535 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75402) = some ⟨11, 1, 0, 900587, 75402, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75402_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75402 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75402 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75402, 1, 262144⟩
    (by decide) selected_cut_38535

theorem selected_cut_38536 : selected 9 ⟨1039542, by decide⟩
    (prefixPartial 12 301612) = some ⟨12, 2, 0, 1039542, 301612, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_301612_1039542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301612 ⟨1039542, by decide⟩ :=
  accepted_of_selected 12 301612 ⟨1039542, by decide⟩ ⟨12, 2, 0, 1039542, 301612, 2925, 65536⟩
    (by decide) selected_cut_38536

theorem selected_cut_38537 : selected 9 ⟨1039612, by decide⟩
    (prefixPartial 12 301613) = some ⟨12, 2, 0, 1039612, 301613, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_301613_1039612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301613 ⟨1039612, by decide⟩ :=
  accepted_of_selected 12 301613 ⟨1039612, by decide⟩ ⟨12, 2, 0, 1039612, 301613, 3481, 65536⟩
    (by decide) selected_cut_38537

theorem selected_cut_38538 : selected 9 ⟨1039661, by decide⟩
    (prefixPartial 12 301614) = some ⟨12, 2, 0, 1039661, 301614, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_301614_1039661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301614 ⟨1039661, by decide⟩ :=
  accepted_of_selected 12 301614 ⟨1039661, by decide⟩ ⟨12, 2, 0, 1039661, 301614, 2785, 65536⟩
    (by decide) selected_cut_38538

theorem selected_cut_38539 : selected 9 ⟨1039720, by decide⟩
    (prefixPartial 12 301615) = some ⟨12, 2, 0, 1039720, 301615, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_301615_1039720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301615 ⟨1039720, by decide⟩ :=
  accepted_of_selected 12 301615 ⟨1039720, by decide⟩ ⟨12, 2, 0, 1039720, 301615, 3001, 65536⟩
    (by decide) selected_cut_38539

theorem unmarked_context_11_75403_1039721 : frontier 10 ⟨1039721, by decide⟩
    (prefixCache 11 75403) (prefixPartial 11 75403) = false := by
  decide +kernel

theorem node_context_11_75403_1039721 : EJMOriginalGlobalDAGData.nodes 10 ⟨1039721, by decide⟩ =
    .split (coordinate 11) (![⟨1039542, by decide⟩,⟨1039612, by decide⟩,⟨1039661, by decide⟩,⟨1039720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75403_1039721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75403 ⟨1039721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75403
    ⟨1039721, by decide⟩ (by decide) (![⟨1039542, by decide⟩,⟨1039612, by decide⟩,⟨1039661, by decide⟩,⟨1039720, by decide⟩]) unmarked_context_11_75403_1039721 node_context_11_75403_1039721
  intro a
  fin_cases a
  · exact context_12_301612_1039542
  · exact context_12_301613_1039612
  · exact context_12_301614_1039661
  · exact context_12_301615_1039720

theorem unmarked_context_10_18850_1039722 : frontier 11 ⟨1039722, by decide⟩
    (prefixCache 10 18850) (prefixPartial 10 18850) = false := by
  decide +kernel

theorem node_context_10_18850_1039722 : EJMOriginalGlobalDAGData.nodes 11 ⟨1039722, by decide⟩ =
    .split (coordinate 10) (![⟨1039256, by decide⟩,⟨1039488, by decide⟩,⟨900587, by decide⟩,⟨1039721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18850_1039722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18850 ⟨1039722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18850
    ⟨1039722, by decide⟩ (by decide) (![⟨1039256, by decide⟩,⟨1039488, by decide⟩,⟨900587, by decide⟩,⟨1039721, by decide⟩]) unmarked_context_10_18850_1039722 node_context_10_18850_1039722
  intro a
  fin_cases a
  · exact context_11_75400_1039256
  · exact context_11_75401_1039488
  · exact context_11_75402_900587
  · exact context_11_75403_1039721

theorem selected_cut_38540 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 301616) = some ⟨12, 1, 0, 994572, 301616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301616_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301616 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 301616 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 301616, 1, 65536⟩
    (by decide) selected_cut_38540

theorem selected_cut_38541 : selected 9 ⟨1039789, by decide⟩
    (prefixPartial 12 301617) = some ⟨12, 2, 0, 1039789, 301617, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_301617_1039789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301617 ⟨1039789, by decide⟩ :=
  accepted_of_selected 12 301617 ⟨1039789, by decide⟩ ⟨12, 2, 0, 1039789, 301617, 3461, 65536⟩
    (by decide) selected_cut_38541

theorem selected_cut_38542 : selected 9 ⟨1039837, by decide⟩
    (prefixPartial 12 301618) = some ⟨12, 2, 0, 1039837, 301618, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_301618_1039837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301618 ⟨1039837, by decide⟩ :=
  accepted_of_selected 12 301618 ⟨1039837, by decide⟩ ⟨12, 2, 0, 1039837, 301618, 2869, 65536⟩
    (by decide) selected_cut_38542

theorem selected_cut_38543 : selected 9 ⟨1039897, by decide⟩
    (prefixPartial 12 301619) = some ⟨12, 2, 0, 1039897, 301619, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_301619_1039897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301619 ⟨1039897, by decide⟩ :=
  accepted_of_selected 12 301619 ⟨1039897, by decide⟩ ⟨12, 2, 0, 1039897, 301619, 3353, 65536⟩
    (by decide) selected_cut_38543

theorem unmarked_context_11_75404_1039898 : frontier 10 ⟨1039898, by decide⟩
    (prefixCache 11 75404) (prefixPartial 11 75404) = false := by
  decide +kernel

theorem node_context_11_75404_1039898 : EJMOriginalGlobalDAGData.nodes 10 ⟨1039898, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1039789, by decide⟩,⟨1039837, by decide⟩,⟨1039897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75404_1039898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75404 ⟨1039898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75404
    ⟨1039898, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1039789, by decide⟩,⟨1039837, by decide⟩,⟨1039897, by decide⟩]) unmarked_context_11_75404_1039898 node_context_11_75404_1039898
  intro a
  fin_cases a
  · exact context_12_301616_994572
  · exact context_12_301617_1039789
  · exact context_12_301618_1039837
  · exact context_12_301619_1039897

theorem selected_cut_38544 : selected 9 ⟨1039954, by decide⟩
    (prefixPartial 12 301620) = some ⟨12, 2, 0, 1039954, 301620, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_301620_1039954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301620 ⟨1039954, by decide⟩ :=
  accepted_of_selected 12 301620 ⟨1039954, by decide⟩ ⟨12, 2, 0, 1039954, 301620, 3121, 65536⟩
    (by decide) selected_cut_38544

theorem selected_cut_38545 : selected 9 ⟨1040026, by decide⟩
    (prefixPartial 12 301621) = some ⟨12, 2, 0, 1040026, 301621, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_301621_1040026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301621 ⟨1040026, by decide⟩ :=
  accepted_of_selected 12 301621 ⟨1040026, by decide⟩ ⟨12, 2, 0, 1040026, 301621, 3613, 65536⟩
    (by decide) selected_cut_38545

theorem selected_cut_38546 : selected 9 ⟨1040077, by decide⟩
    (prefixPartial 12 301622) = some ⟨12, 2, 0, 1040077, 301622, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_301622_1040077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301622 ⟨1040077, by decide⟩ :=
  accepted_of_selected 12 301622 ⟨1040077, by decide⟩ ⟨12, 2, 0, 1040077, 301622, 2993, 65536⟩
    (by decide) selected_cut_38546

theorem selected_cut_38547 : selected 9 ⟨1040142, by decide⟩
    (prefixPartial 12 301623) = some ⟨12, 2, 0, 1040142, 301623, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_301623_1040142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301623 ⟨1040142, by decide⟩ :=
  accepted_of_selected 12 301623 ⟨1040142, by decide⟩ ⟨12, 2, 0, 1040142, 301623, 3301, 65536⟩
    (by decide) selected_cut_38547

theorem unmarked_context_11_75405_1040143 : frontier 10 ⟨1040143, by decide⟩
    (prefixCache 11 75405) (prefixPartial 11 75405) = false := by
  decide +kernel

theorem node_context_11_75405_1040143 : EJMOriginalGlobalDAGData.nodes 10 ⟨1040143, by decide⟩ =
    .split (coordinate 11) (![⟨1039954, by decide⟩,⟨1040026, by decide⟩,⟨1040077, by decide⟩,⟨1040142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75405_1040143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75405 ⟨1040143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75405
    ⟨1040143, by decide⟩ (by decide) (![⟨1039954, by decide⟩,⟨1040026, by decide⟩,⟨1040077, by decide⟩,⟨1040142, by decide⟩]) unmarked_context_11_75405_1040143 node_context_11_75405_1040143
  intro a
  fin_cases a
  · exact context_12_301620_1039954
  · exact context_12_301621_1040026
  · exact context_12_301622_1040077
  · exact context_12_301623_1040142

theorem selected_cut_38548 : selected 9 ⟨1040189, by decide⟩
    (prefixPartial 12 301624) = some ⟨12, 2, 0, 1040189, 301624, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_301624_1040189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301624 ⟨1040189, by decide⟩ :=
  accepted_of_selected 12 301624 ⟨1040189, by decide⟩ ⟨12, 2, 0, 1040189, 301624, 2749, 65536⟩
    (by decide) selected_cut_38548

theorem selected_cut_38549 : selected 9 ⟨1040252, by decide⟩
    (prefixPartial 12 301625) = some ⟨12, 2, 0, 1040252, 301625, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_301625_1040252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301625 ⟨1040252, by decide⟩ :=
  accepted_of_selected 12 301625 ⟨1040252, by decide⟩ ⟨12, 2, 0, 1040252, 301625, 3269, 65536⟩
    (by decide) selected_cut_38549

theorem selected_cut_38550 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 301626) = some ⟨12, 1, 0, 893903, 301626, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301626_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301626 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 301626 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 301626, 1, 65536⟩
    (by decide) selected_cut_38550

theorem selected_cut_38551 : selected 9 ⟨1040312, by decide⟩
    (prefixPartial 12 301627) = some ⟨12, 2, 0, 1040312, 301627, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_301627_1040312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301627 ⟨1040312, by decide⟩ :=
  accepted_of_selected 12 301627 ⟨1040312, by decide⟩ ⟨12, 2, 0, 1040312, 301627, 3253, 65536⟩
    (by decide) selected_cut_38551

theorem unmarked_context_11_75406_1040313 : frontier 10 ⟨1040313, by decide⟩
    (prefixCache 11 75406) (prefixPartial 11 75406) = false := by
  decide +kernel

theorem node_context_11_75406_1040313 : EJMOriginalGlobalDAGData.nodes 10 ⟨1040313, by decide⟩ =
    .split (coordinate 11) (![⟨1040189, by decide⟩,⟨1040252, by decide⟩,⟨893903, by decide⟩,⟨1040312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75406_1040313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75406 ⟨1040313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75406
    ⟨1040313, by decide⟩ (by decide) (![⟨1040189, by decide⟩,⟨1040252, by decide⟩,⟨893903, by decide⟩,⟨1040312, by decide⟩]) unmarked_context_11_75406_1040313 node_context_11_75406_1040313
  intro a
  fin_cases a
  · exact context_12_301624_1040189
  · exact context_12_301625_1040252
  · exact context_12_301626_893903
  · exact context_12_301627_1040312

theorem selected_cut_38552 : selected 9 ⟨1040362, by decide⟩
    (prefixPartial 12 301628) = some ⟨12, 2, 0, 1040362, 301628, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_301628_1040362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301628 ⟨1040362, by decide⟩ :=
  accepted_of_selected 12 301628 ⟨1040362, by decide⟩ ⟨12, 2, 0, 1040362, 301628, 2821, 65536⟩
    (by decide) selected_cut_38552

theorem selected_cut_38553 : selected 9 ⟨1040418, by decide⟩
    (prefixPartial 12 301629) = some ⟨12, 2, 0, 1040418, 301629, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_301629_1040418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301629 ⟨1040418, by decide⟩ :=
  accepted_of_selected 12 301629 ⟨1040418, by decide⟩ ⟨12, 2, 0, 1040418, 301629, 3249, 65536⟩
    (by decide) selected_cut_38553

theorem selected_cut_38554 : selected 9 ⟨1040461, by decide⟩
    (prefixPartial 12 301630) = some ⟨12, 2, 0, 1040461, 301630, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_301630_1040461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301630 ⟨1040461, by decide⟩ :=
  accepted_of_selected 12 301630 ⟨1040461, by decide⟩ ⟨12, 2, 0, 1040461, 301630, 2721, 65536⟩
    (by decide) selected_cut_38554

theorem selected_cut_38555 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 301631) = some ⟨12, 1, 0, 762109, 301631, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301631_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301631 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 301631 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 301631, 1, 65536⟩
    (by decide) selected_cut_38555

theorem unmarked_context_11_75407_1040462 : frontier 10 ⟨1040462, by decide⟩
    (prefixCache 11 75407) (prefixPartial 11 75407) = false := by
  decide +kernel

theorem node_context_11_75407_1040462 : EJMOriginalGlobalDAGData.nodes 10 ⟨1040462, by decide⟩ =
    .split (coordinate 11) (![⟨1040362, by decide⟩,⟨1040418, by decide⟩,⟨1040461, by decide⟩,⟨762109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75407_1040462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75407 ⟨1040462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75407
    ⟨1040462, by decide⟩ (by decide) (![⟨1040362, by decide⟩,⟨1040418, by decide⟩,⟨1040461, by decide⟩,⟨762109, by decide⟩]) unmarked_context_11_75407_1040462 node_context_11_75407_1040462
  intro a
  fin_cases a
  · exact context_12_301628_1040362
  · exact context_12_301629_1040418
  · exact context_12_301630_1040461
  · exact context_12_301631_762109

theorem unmarked_context_10_18851_1040463 : frontier 11 ⟨1040463, by decide⟩
    (prefixCache 10 18851) (prefixPartial 10 18851) = false := by
  decide +kernel

theorem node_context_10_18851_1040463 : EJMOriginalGlobalDAGData.nodes 11 ⟨1040463, by decide⟩ =
    .split (coordinate 10) (![⟨1039898, by decide⟩,⟨1040143, by decide⟩,⟨1040313, by decide⟩,⟨1040462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18851_1040463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18851 ⟨1040463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18851
    ⟨1040463, by decide⟩ (by decide) (![⟨1039898, by decide⟩,⟨1040143, by decide⟩,⟨1040313, by decide⟩,⟨1040462, by decide⟩]) unmarked_context_10_18851_1040463 node_context_10_18851_1040463
  intro a
  fin_cases a
  · exact context_11_75404_1039898
  · exact context_11_75405_1040143
  · exact context_11_75406_1040313
  · exact context_11_75407_1040462

theorem unmarked_context_9_4712_1040464 : frontier 12 ⟨1040464, by decide⟩
    (prefixCache 9 4712) (prefixPartial 9 4712) = false := by
  decide +kernel

theorem node_context_9_4712_1040464 : EJMOriginalGlobalDAGData.nodes 12 ⟨1040464, by decide⟩ =
    .split (coordinate 9) (![⟨1038256, by decide⟩,⟨1039102, by decide⟩,⟨1039722, by decide⟩,⟨1040463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4712_1040464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4712 ⟨1040464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4712
    ⟨1040464, by decide⟩ (by decide) (![⟨1038256, by decide⟩,⟨1039102, by decide⟩,⟨1039722, by decide⟩,⟨1040463, by decide⟩]) unmarked_context_9_4712_1040464 node_context_9_4712_1040464
  intro a
  fin_cases a
  · exact context_10_18848_1038256
  · exact context_10_18849_1039102
  · exact context_10_18850_1039722
  · exact context_10_18851_1040463

theorem selected_cut_38556 : selected 9 ⟨1030245, by decide⟩
    (prefixPartial 12 301632) = some ⟨12, 1, 0, 1030245, 301632, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301632_1030245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301632 ⟨1030245, by decide⟩ :=
  accepted_of_selected 12 301632 ⟨1030245, by decide⟩ ⟨12, 1, 0, 1030245, 301632, 1, 65536⟩
    (by decide) selected_cut_38556

theorem selected_cut_38557 : selected 9 ⟨1040523, by decide⟩
    (prefixPartial 12 301633) = some ⟨12, 2, 0, 1040523, 301633, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_301633_1040523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301633 ⟨1040523, by decide⟩ :=
  accepted_of_selected 12 301633 ⟨1040523, by decide⟩ ⟨12, 2, 0, 1040523, 301633, 2861, 65536⟩
    (by decide) selected_cut_38557

theorem selected_cut_38558 : selected 9 ⟨1040565, by decide⟩
    (prefixPartial 12 301634) = some ⟨12, 2, 0, 1040565, 301634, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_301634_1040565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301634 ⟨1040565, by decide⟩ :=
  accepted_of_selected 12 301634 ⟨1040565, by decide⟩ ⟨12, 2, 0, 1040565, 301634, 2493, 65536⟩
    (by decide) selected_cut_38558

theorem selected_cut_38559 : selected 9 ⟨1040617, by decide⟩
    (prefixPartial 12 301635) = some ⟨12, 2, 0, 1040617, 301635, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_301635_1040617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301635 ⟨1040617, by decide⟩ :=
  accepted_of_selected 12 301635 ⟨1040617, by decide⟩ ⟨12, 2, 0, 1040617, 301635, 2609, 65536⟩
    (by decide) selected_cut_38559

theorem unmarked_context_11_75408_1040618 : frontier 10 ⟨1040618, by decide⟩
    (prefixCache 11 75408) (prefixPartial 11 75408) = false := by
  decide +kernel

theorem node_context_11_75408_1040618 : EJMOriginalGlobalDAGData.nodes 10 ⟨1040618, by decide⟩ =
    .split (coordinate 11) (![⟨1030245, by decide⟩,⟨1040523, by decide⟩,⟨1040565, by decide⟩,⟨1040617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75408_1040618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75408 ⟨1040618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75408
    ⟨1040618, by decide⟩ (by decide) (![⟨1030245, by decide⟩,⟨1040523, by decide⟩,⟨1040565, by decide⟩,⟨1040617, by decide⟩]) unmarked_context_11_75408_1040618 node_context_11_75408_1040618
  intro a
  fin_cases a
  · exact context_12_301632_1030245
  · exact context_12_301633_1040523
  · exact context_12_301634_1040565
  · exact context_12_301635_1040617

theorem selected_cut_38560 : selected 9 ⟨1040680, by decide⟩
    (prefixPartial 12 301636) = some ⟨12, 2, 0, 1040680, 301636, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_301636_1040680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301636 ⟨1040680, by decide⟩ :=
  accepted_of_selected 12 301636 ⟨1040680, by decide⟩ ⟨12, 2, 0, 1040680, 301636, 3237, 65536⟩
    (by decide) selected_cut_38560

theorem selected_cut_38561 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 301637) = some ⟨12, 1, 0, 691709, 301637, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301637_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301637 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 301637 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 301637, 1, 65536⟩
    (by decide) selected_cut_38561

theorem selected_cut_38562 : selected 9 ⟨1040721, by decide⟩
    (prefixPartial 12 301638) = some ⟨12, 2, 0, 1040721, 301638, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_301638_1040721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301638 ⟨1040721, by decide⟩ :=
  accepted_of_selected 12 301638 ⟨1040721, by decide⟩ ⟨12, 2, 0, 1040721, 301638, 2601, 65536⟩
    (by decide) selected_cut_38562

theorem selected_cut_38563 : selected 9 ⟨1040770, by decide⟩
    (prefixPartial 12 301639) = some ⟨12, 2, 0, 1040770, 301639, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_301639_1040770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301639 ⟨1040770, by decide⟩ :=
  accepted_of_selected 12 301639 ⟨1040770, by decide⟩ ⟨12, 2, 0, 1040770, 301639, 2585, 65536⟩
    (by decide) selected_cut_38563

theorem unmarked_context_11_75409_1040771 : frontier 10 ⟨1040771, by decide⟩
    (prefixCache 11 75409) (prefixPartial 11 75409) = false := by
  decide +kernel

theorem node_context_11_75409_1040771 : EJMOriginalGlobalDAGData.nodes 10 ⟨1040771, by decide⟩ =
    .split (coordinate 11) (![⟨1040680, by decide⟩,⟨691709, by decide⟩,⟨1040721, by decide⟩,⟨1040770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75409_1040771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75409 ⟨1040771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75409
    ⟨1040771, by decide⟩ (by decide) (![⟨1040680, by decide⟩,⟨691709, by decide⟩,⟨1040721, by decide⟩,⟨1040770, by decide⟩]) unmarked_context_11_75409_1040771 node_context_11_75409_1040771
  intro a
  fin_cases a
  · exact context_12_301636_1040680
  · exact context_12_301637_691709
  · exact context_12_301638_1040721
  · exact context_12_301639_1040770

theorem selected_cut_38564 : selected 9 ⟨1040834, by decide⟩
    (prefixPartial 12 301640) = some ⟨12, 2, 0, 1040834, 301640, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_301640_1040834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301640 ⟨1040834, by decide⟩ :=
  accepted_of_selected 12 301640 ⟨1040834, by decide⟩ ⟨12, 2, 0, 1040834, 301640, 3093, 65536⟩
    (by decide) selected_cut_38564

theorem selected_cut_38565 : selected 9 ⟨1040893, by decide⟩
    (prefixPartial 12 301641) = some ⟨12, 2, 0, 1040893, 301641, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_301641_1040893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301641 ⟨1040893, by decide⟩ :=
  accepted_of_selected 12 301641 ⟨1040893, by decide⟩ ⟨12, 2, 0, 1040893, 301641, 2797, 65536⟩
    (by decide) selected_cut_38565

theorem selected_cut_38566 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 301642) = some ⟨12, 1, 0, 893903, 301642, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301642_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301642 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 301642 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 301642, 1, 65536⟩
    (by decide) selected_cut_38566

theorem selected_cut_38567 : selected 9 ⟨1040942, by decide⟩
    (prefixPartial 12 301643) = some ⟨12, 2, 0, 1040942, 301643, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_301643_1040942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301643 ⟨1040942, by decide⟩ :=
  accepted_of_selected 12 301643 ⟨1040942, by decide⟩ ⟨12, 2, 0, 1040942, 301643, 2693, 65536⟩
    (by decide) selected_cut_38567

theorem unmarked_context_11_75410_1040943 : frontier 10 ⟨1040943, by decide⟩
    (prefixCache 11 75410) (prefixPartial 11 75410) = false := by
  decide +kernel

theorem node_context_11_75410_1040943 : EJMOriginalGlobalDAGData.nodes 10 ⟨1040943, by decide⟩ =
    .split (coordinate 11) (![⟨1040834, by decide⟩,⟨1040893, by decide⟩,⟨893903, by decide⟩,⟨1040942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75410_1040943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75410 ⟨1040943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75410
    ⟨1040943, by decide⟩ (by decide) (![⟨1040834, by decide⟩,⟨1040893, by decide⟩,⟨893903, by decide⟩,⟨1040942, by decide⟩]) unmarked_context_11_75410_1040943 node_context_11_75410_1040943
  intro a
  fin_cases a
  · exact context_12_301640_1040834
  · exact context_12_301641_1040893
  · exact context_12_301642_893903
  · exact context_12_301643_1040942

theorem selected_cut_38568 : selected 9 ⟨1041017, by decide⟩
    (prefixPartial 12 301644) = some ⟨12, 2, 0, 1041017, 301644, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_301644_1041017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301644 ⟨1041017, by decide⟩ :=
  accepted_of_selected 12 301644 ⟨1041017, by decide⟩ ⟨12, 2, 0, 1041017, 301644, 3437, 65536⟩
    (by decide) selected_cut_38568

theorem selected_cut_38569 : selected 9 ⟨1041060, by decide⟩
    (prefixPartial 12 301645) = some ⟨12, 2, 0, 1041060, 301645, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_301645_1041060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301645 ⟨1041060, by decide⟩ :=
  accepted_of_selected 12 301645 ⟨1041060, by decide⟩ ⟨12, 2, 0, 1041060, 301645, 2841, 65536⟩
    (by decide) selected_cut_38569

theorem selected_cut_38570 : selected 9 ⟨1041108, by decide⟩
    (prefixPartial 12 301646) = some ⟨12, 2, 0, 1041108, 301646, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_301646_1041108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301646 ⟨1041108, by decide⟩ :=
  accepted_of_selected 12 301646 ⟨1041108, by decide⟩ ⟨12, 2, 0, 1041108, 301646, 2749, 65536⟩
    (by decide) selected_cut_38570

theorem selected_cut_38571 : selected 9 ⟨1041149, by decide⟩
    (prefixPartial 12 301647) = some ⟨12, 2, 0, 1041149, 301647, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_301647_1041149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301647 ⟨1041149, by decide⟩ :=
  accepted_of_selected 12 301647 ⟨1041149, by decide⟩ ⟨12, 2, 0, 1041149, 301647, 2457, 65536⟩
    (by decide) selected_cut_38571

theorem unmarked_context_11_75411_1041150 : frontier 10 ⟨1041150, by decide⟩
    (prefixCache 11 75411) (prefixPartial 11 75411) = false := by
  decide +kernel

theorem node_context_11_75411_1041150 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041150, by decide⟩ =
    .split (coordinate 11) (![⟨1041017, by decide⟩,⟨1041060, by decide⟩,⟨1041108, by decide⟩,⟨1041149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75411_1041150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75411 ⟨1041150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75411
    ⟨1041150, by decide⟩ (by decide) (![⟨1041017, by decide⟩,⟨1041060, by decide⟩,⟨1041108, by decide⟩,⟨1041149, by decide⟩]) unmarked_context_11_75411_1041150 node_context_11_75411_1041150
  intro a
  fin_cases a
  · exact context_12_301644_1041017
  · exact context_12_301645_1041060
  · exact context_12_301646_1041108
  · exact context_12_301647_1041149

theorem unmarked_context_10_18852_1041151 : frontier 11 ⟨1041151, by decide⟩
    (prefixCache 10 18852) (prefixPartial 10 18852) = false := by
  decide +kernel

theorem node_context_10_18852_1041151 : EJMOriginalGlobalDAGData.nodes 11 ⟨1041151, by decide⟩ =
    .split (coordinate 10) (![⟨1040618, by decide⟩,⟨1040771, by decide⟩,⟨1040943, by decide⟩,⟨1041150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18852_1041151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18852 ⟨1041151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18852
    ⟨1041151, by decide⟩ (by decide) (![⟨1040618, by decide⟩,⟨1040771, by decide⟩,⟨1040943, by decide⟩,⟨1041150, by decide⟩]) unmarked_context_10_18852_1041151 node_context_10_18852_1041151
  intro a
  fin_cases a
  · exact context_11_75408_1040618
  · exact context_11_75409_1040771
  · exact context_11_75410_1040943
  · exact context_11_75411_1041150

theorem selected_cut_38572 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18853) = some ⟨10, 1, 0, 893098, 18853, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18853_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18853 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18853 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18853, 1, 1048576⟩
    (by decide) selected_cut_38572

theorem selected_cut_38573 : selected 9 ⟨1041176, by decide⟩
    (prefixPartial 12 301664) = some ⟨12, 2, 0, 1041176, 301664, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_301664_1041176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301664 ⟨1041176, by decide⟩ :=
  accepted_of_selected 12 301664 ⟨1041176, by decide⟩ ⟨12, 2, 0, 1041176, 301664, 1709, 65536⟩
    (by decide) selected_cut_38573

theorem selected_cut_38574 : selected 9 ⟨1041201, by decide⟩
    (prefixPartial 12 301665) = some ⟨12, 2, 0, 1041201, 301665, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_301665_1041201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301665 ⟨1041201, by decide⟩ :=
  accepted_of_selected 12 301665 ⟨1041201, by decide⟩ ⟨12, 2, 0, 1041201, 301665, 1793, 65536⟩
    (by decide) selected_cut_38574

theorem selected_cut_38575 : selected 9 ⟨1041223, by decide⟩
    (prefixPartial 12 301666) = some ⟨12, 2, 0, 1041223, 301666, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_301666_1041223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301666 ⟨1041223, by decide⟩ :=
  accepted_of_selected 12 301666 ⟨1041223, by decide⟩ ⟨12, 2, 0, 1041223, 301666, 1297, 65536⟩
    (by decide) selected_cut_38575

theorem selected_cut_38576 : selected 9 ⟨1041242, by decide⟩
    (prefixPartial 12 301667) = some ⟨12, 2, 0, 1041242, 301667, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_301667_1041242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301667 ⟨1041242, by decide⟩ :=
  accepted_of_selected 12 301667 ⟨1041242, by decide⟩ ⟨12, 2, 0, 1041242, 301667, 1601, 65536⟩
    (by decide) selected_cut_38576

theorem unmarked_context_11_75416_1041243 : frontier 10 ⟨1041243, by decide⟩
    (prefixCache 11 75416) (prefixPartial 11 75416) = false := by
  decide +kernel

theorem node_context_11_75416_1041243 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041243, by decide⟩ =
    .split (coordinate 11) (![⟨1041176, by decide⟩,⟨1041201, by decide⟩,⟨1041223, by decide⟩,⟨1041242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75416_1041243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75416 ⟨1041243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75416
    ⟨1041243, by decide⟩ (by decide) (![⟨1041176, by decide⟩,⟨1041201, by decide⟩,⟨1041223, by decide⟩,⟨1041242, by decide⟩]) unmarked_context_11_75416_1041243 node_context_11_75416_1041243
  intro a
  fin_cases a
  · exact context_12_301664_1041176
  · exact context_12_301665_1041201
  · exact context_12_301666_1041223
  · exact context_12_301667_1041242

theorem selected_cut_38577 : selected 9 ⟨1041268, by decide⟩
    (prefixPartial 12 301668) = some ⟨12, 2, 0, 1041268, 301668, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_301668_1041268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301668 ⟨1041268, by decide⟩ :=
  accepted_of_selected 12 301668 ⟨1041268, by decide⟩ ⟨12, 2, 0, 1041268, 301668, 1753, 65536⟩
    (by decide) selected_cut_38577

theorem selected_cut_38578 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 301669) = some ⟨12, 1, 0, 691709, 301669, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301669_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301669 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 301669 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 301669, 1, 65536⟩
    (by decide) selected_cut_38578

theorem selected_cut_38579 : selected 9 ⟨1041288, by decide⟩
    (prefixPartial 12 301670) = some ⟨12, 2, 0, 1041288, 301670, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_301670_1041288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301670 ⟨1041288, by decide⟩ :=
  accepted_of_selected 12 301670 ⟨1041288, by decide⟩ ⟨12, 2, 0, 1041288, 301670, 1317, 65536⟩
    (by decide) selected_cut_38579

theorem selected_cut_38580 : selected 9 ⟨1041315, by decide⟩
    (prefixPartial 12 301671) = some ⟨12, 2, 0, 1041315, 301671, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_301671_1041315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301671 ⟨1041315, by decide⟩ :=
  accepted_of_selected 12 301671 ⟨1041315, by decide⟩ ⟨12, 2, 0, 1041315, 301671, 1633, 65536⟩
    (by decide) selected_cut_38580

theorem unmarked_context_11_75417_1041316 : frontier 10 ⟨1041316, by decide⟩
    (prefixCache 11 75417) (prefixPartial 11 75417) = false := by
  decide +kernel

theorem node_context_11_75417_1041316 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041316, by decide⟩ =
    .split (coordinate 11) (![⟨1041268, by decide⟩,⟨691709, by decide⟩,⟨1041288, by decide⟩,⟨1041315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75417_1041316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75417 ⟨1041316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75417
    ⟨1041316, by decide⟩ (by decide) (![⟨1041268, by decide⟩,⟨691709, by decide⟩,⟨1041288, by decide⟩,⟨1041315, by decide⟩]) unmarked_context_11_75417_1041316 node_context_11_75417_1041316
  intro a
  fin_cases a
  · exact context_12_301668_1041268
  · exact context_12_301669_691709
  · exact context_12_301670_1041288
  · exact context_12_301671_1041315

theorem selected_cut_38581 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75418) = some ⟨11, 1, 0, 900587, 75418, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75418_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75418 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75418 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75418, 1, 262144⟩
    (by decide) selected_cut_38581

theorem selected_cut_38582 : selected 9 ⟨1041355, by decide⟩
    (prefixPartial 12 301676) = some ⟨12, 2, 0, 1041355, 301676, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_301676_1041355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301676 ⟨1041355, by decide⟩ :=
  accepted_of_selected 12 301676 ⟨1041355, by decide⟩ ⟨12, 2, 0, 1041355, 301676, 1949, 65536⟩
    (by decide) selected_cut_38582

theorem selected_cut_38583 : selected 9 ⟨1041387, by decide⟩
    (prefixPartial 12 301677) = some ⟨12, 2, 0, 1041387, 301677, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_301677_1041387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301677 ⟨1041387, by decide⟩ :=
  accepted_of_selected 12 301677 ⟨1041387, by decide⟩ ⟨12, 2, 0, 1041387, 301677, 1925, 65536⟩
    (by decide) selected_cut_38583

theorem selected_cut_38584 : selected 9 ⟨1041414, by decide⟩
    (prefixPartial 12 301678) = some ⟨12, 2, 0, 1041414, 301678, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_301678_1041414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301678 ⟨1041414, by decide⟩ :=
  accepted_of_selected 12 301678 ⟨1041414, by decide⟩ ⟨12, 2, 0, 1041414, 301678, 1521, 65536⟩
    (by decide) selected_cut_38584

theorem selected_cut_38585 : selected 9 ⟨1041437, by decide⟩
    (prefixPartial 12 301679) = some ⟨12, 2, 0, 1041437, 301679, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_301679_1041437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301679 ⟨1041437, by decide⟩ :=
  accepted_of_selected 12 301679 ⟨1041437, by decide⟩ ⟨12, 2, 0, 1041437, 301679, 1709, 65536⟩
    (by decide) selected_cut_38585

theorem unmarked_context_11_75419_1041438 : frontier 10 ⟨1041438, by decide⟩
    (prefixCache 11 75419) (prefixPartial 11 75419) = false := by
  decide +kernel

theorem node_context_11_75419_1041438 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041438, by decide⟩ =
    .split (coordinate 11) (![⟨1041355, by decide⟩,⟨1041387, by decide⟩,⟨1041414, by decide⟩,⟨1041437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75419_1041438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75419 ⟨1041438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75419
    ⟨1041438, by decide⟩ (by decide) (![⟨1041355, by decide⟩,⟨1041387, by decide⟩,⟨1041414, by decide⟩,⟨1041437, by decide⟩]) unmarked_context_11_75419_1041438 node_context_11_75419_1041438
  intro a
  fin_cases a
  · exact context_12_301676_1041355
  · exact context_12_301677_1041387
  · exact context_12_301678_1041414
  · exact context_12_301679_1041437

theorem unmarked_context_10_18854_1041439 : frontier 11 ⟨1041439, by decide⟩
    (prefixCache 10 18854) (prefixPartial 10 18854) = false := by
  decide +kernel

theorem node_context_10_18854_1041439 : EJMOriginalGlobalDAGData.nodes 11 ⟨1041439, by decide⟩ =
    .split (coordinate 10) (![⟨1041243, by decide⟩,⟨1041316, by decide⟩,⟨900587, by decide⟩,⟨1041438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18854_1041439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18854 ⟨1041439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18854
    ⟨1041439, by decide⟩ (by decide) (![⟨1041243, by decide⟩,⟨1041316, by decide⟩,⟨900587, by decide⟩,⟨1041438, by decide⟩]) unmarked_context_10_18854_1041439 node_context_10_18854_1041439
  intro a
  fin_cases a
  · exact context_11_75416_1041243
  · exact context_11_75417_1041316
  · exact context_11_75418_900587
  · exact context_11_75419_1041438

theorem selected_cut_38586 : selected 9 ⟨1041469, by decide⟩
    (prefixPartial 12 301680) = some ⟨12, 2, 0, 1041469, 301680, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_301680_1041469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301680 ⟨1041469, by decide⟩ :=
  accepted_of_selected 12 301680 ⟨1041469, by decide⟩ ⟨12, 2, 0, 1041469, 301680, 1753, 65536⟩
    (by decide) selected_cut_38586

theorem selected_cut_38587 : selected 9 ⟨1041504, by decide⟩
    (prefixPartial 12 301681) = some ⟨12, 2, 0, 1041504, 301681, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_301681_1041504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301681 ⟨1041504, by decide⟩ :=
  accepted_of_selected 12 301681 ⟨1041504, by decide⟩ ⟨12, 2, 0, 1041504, 301681, 1873, 65536⟩
    (by decide) selected_cut_38587

theorem selected_cut_38588 : selected 9 ⟨1041524, by decide⟩
    (prefixPartial 12 301682) = some ⟨12, 2, 0, 1041524, 301682, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_301682_1041524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301682 ⟨1041524, by decide⟩ :=
  accepted_of_selected 12 301682 ⟨1041524, by decide⟩ ⟨12, 2, 0, 1041524, 301682, 1529, 65536⟩
    (by decide) selected_cut_38588

theorem selected_cut_38589 : selected 9 ⟨1041553, by decide⟩
    (prefixPartial 12 301683) = some ⟨12, 2, 0, 1041553, 301683, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_301683_1041553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301683 ⟨1041553, by decide⟩ :=
  accepted_of_selected 12 301683 ⟨1041553, by decide⟩ ⟨12, 2, 0, 1041553, 301683, 1709, 65536⟩
    (by decide) selected_cut_38589

theorem unmarked_context_11_75420_1041554 : frontier 10 ⟨1041554, by decide⟩
    (prefixCache 11 75420) (prefixPartial 11 75420) = false := by
  decide +kernel

theorem node_context_11_75420_1041554 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041554, by decide⟩ =
    .split (coordinate 11) (![⟨1041469, by decide⟩,⟨1041504, by decide⟩,⟨1041524, by decide⟩,⟨1041553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75420_1041554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75420 ⟨1041554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75420
    ⟨1041554, by decide⟩ (by decide) (![⟨1041469, by decide⟩,⟨1041504, by decide⟩,⟨1041524, by decide⟩,⟨1041553, by decide⟩]) unmarked_context_11_75420_1041554 node_context_11_75420_1041554
  intro a
  fin_cases a
  · exact context_12_301680_1041469
  · exact context_12_301681_1041504
  · exact context_12_301682_1041524
  · exact context_12_301683_1041553

theorem selected_cut_38590 : selected 9 ⟨1041580, by decide⟩
    (prefixPartial 12 301684) = some ⟨12, 2, 0, 1041580, 301684, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_301684_1041580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301684 ⟨1041580, by decide⟩ :=
  accepted_of_selected 12 301684 ⟨1041580, by decide⟩ ⟨12, 2, 0, 1041580, 301684, 1757, 65536⟩
    (by decide) selected_cut_38590

theorem selected_cut_38591 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 301685) = some ⟨12, 1, 0, 691709, 301685, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301685_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301685 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 301685 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 301685, 1, 65536⟩
    (by decide) selected_cut_38591

theorem selected_cut_38592 : selected 9 ⟨1041600, by decide⟩
    (prefixPartial 12 301686) = some ⟨12, 2, 0, 1041600, 301686, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_301686_1041600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301686 ⟨1041600, by decide⟩ :=
  accepted_of_selected 12 301686 ⟨1041600, by decide⟩ ⟨12, 2, 0, 1041600, 301686, 1557, 65536⟩
    (by decide) selected_cut_38592

theorem selected_cut_38593 : selected 9 ⟨1041631, by decide⟩
    (prefixPartial 12 301687) = some ⟨12, 2, 0, 1041631, 301687, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_301687_1041631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301687 ⟨1041631, by decide⟩ :=
  accepted_of_selected 12 301687 ⟨1041631, by decide⟩ ⟨12, 2, 0, 1041631, 301687, 1717, 65536⟩
    (by decide) selected_cut_38593

theorem unmarked_context_11_75421_1041632 : frontier 10 ⟨1041632, by decide⟩
    (prefixCache 11 75421) (prefixPartial 11 75421) = false := by
  decide +kernel

theorem node_context_11_75421_1041632 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041632, by decide⟩ =
    .split (coordinate 11) (![⟨1041580, by decide⟩,⟨691709, by decide⟩,⟨1041600, by decide⟩,⟨1041631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75421_1041632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75421 ⟨1041632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75421
    ⟨1041632, by decide⟩ (by decide) (![⟨1041580, by decide⟩,⟨691709, by decide⟩,⟨1041600, by decide⟩,⟨1041631, by decide⟩]) unmarked_context_11_75421_1041632 node_context_11_75421_1041632
  intro a
  fin_cases a
  · exact context_12_301684_1041580
  · exact context_12_301685_691709
  · exact context_12_301686_1041600
  · exact context_12_301687_1041631

theorem selected_cut_38594 : selected 9 ⟨1041660, by decide⟩
    (prefixPartial 12 301688) = some ⟨12, 2, 0, 1041660, 301688, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_301688_1041660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301688 ⟨1041660, by decide⟩ :=
  accepted_of_selected 12 301688 ⟨1041660, by decide⟩ ⟨12, 2, 0, 1041660, 301688, 1721, 65536⟩
    (by decide) selected_cut_38594

theorem selected_cut_38595 : selected 9 ⟨1041696, by decide⟩
    (prefixPartial 12 301689) = some ⟨12, 2, 0, 1041696, 301689, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_301689_1041696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301689 ⟨1041696, by decide⟩ :=
  accepted_of_selected 12 301689 ⟨1041696, by decide⟩ ⟨12, 2, 0, 1041696, 301689, 1789, 65536⟩
    (by decide) selected_cut_38595

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
