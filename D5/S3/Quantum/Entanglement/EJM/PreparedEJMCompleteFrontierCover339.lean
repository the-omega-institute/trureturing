/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover338
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32547 : selected 8 ⟨837606, by decide⟩
    (prefixPartial 13 438372) = some ⟨13, 2, 0, 837606, 438372, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_438372_837606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438372 ⟨837606, by decide⟩ :=
  accepted_of_selected 13 438372 ⟨837606, by decide⟩ ⟨13, 2, 0, 837606, 438372, 2141, 16384⟩
    (by decide) selected_cut_32547

theorem selected_cut_32548 : selected 8 ⟨837643, by decide⟩
    (prefixPartial 13 438373) = some ⟨13, 2, 0, 837643, 438373, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_438373_837643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438373 ⟨837643, by decide⟩ :=
  accepted_of_selected 13 438373 ⟨837643, by decide⟩ ⟨13, 2, 0, 837643, 438373, 2537, 16384⟩
    (by decide) selected_cut_32548

theorem selected_cut_32549 : selected 8 ⟨837699, by decide⟩
    (prefixPartial 13 438374) = some ⟨13, 2, 0, 837699, 438374, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_438374_837699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438374 ⟨837699, by decide⟩ :=
  accepted_of_selected 13 438374 ⟨837699, by decide⟩ ⟨13, 2, 0, 837699, 438374, 1997, 16384⟩
    (by decide) selected_cut_32549

theorem selected_cut_32550 : selected 8 ⟨837707, by decide⟩
    (prefixPartial 13 438375) = some ⟨13, 2, 0, 837707, 438375, 665, 16384⟩ := by
  decide +kernel

theorem context_13_438375_837707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438375 ⟨837707, by decide⟩ :=
  accepted_of_selected 13 438375 ⟨837707, by decide⟩ ⟨13, 2, 0, 837707, 438375, 665, 16384⟩
    (by decide) selected_cut_32550

theorem unmarked_context_12_109593_837708 : frontier 9 ⟨837708, by decide⟩
    (prefixCache 12 109593) (prefixPartial 12 109593) = false := by
  decide +kernel

theorem node_context_12_109593_837708 : EJMOriginalGlobalDAGData.nodes 9 ⟨837708, by decide⟩ =
    .split (coordinate 12) (![⟨837606, by decide⟩,⟨837643, by decide⟩,⟨837699, by decide⟩,⟨837707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109593_837708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109593 ⟨837708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109593
    ⟨837708, by decide⟩ (by decide) (![⟨837606, by decide⟩,⟨837643, by decide⟩,⟨837699, by decide⟩,⟨837707, by decide⟩]) unmarked_context_12_109593_837708 node_context_12_109593_837708
  intro a
  fin_cases a
  · exact context_13_438372_837606
  · exact context_13_438373_837643
  · exact context_13_438374_837699
  · exact context_13_438375_837707

theorem selected_cut_32551 : selected 8 ⟨837734, by decide⟩
    (prefixPartial 13 438376) = some ⟨13, 2, 0, 837734, 438376, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_438376_837734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438376 ⟨837734, by decide⟩ :=
  accepted_of_selected 13 438376 ⟨837734, by decide⟩ ⟨13, 2, 0, 837734, 438376, 1393, 16384⟩
    (by decide) selected_cut_32551

theorem selected_cut_32552 : selected 8 ⟨837759, by decide⟩
    (prefixPartial 13 438377) = some ⟨13, 2, 0, 837759, 438377, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_438377_837759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438377 ⟨837759, by decide⟩ :=
  accepted_of_selected 13 438377 ⟨837759, by decide⟩ ⟨13, 2, 0, 837759, 438377, 2069, 16384⟩
    (by decide) selected_cut_32552

theorem selected_cut_32553 : selected 8 ⟨837787, by decide⟩
    (prefixPartial 13 438378) = some ⟨13, 2, 0, 837787, 438378, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_438378_837787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438378 ⟨837787, by decide⟩ :=
  accepted_of_selected 13 438378 ⟨837787, by decide⟩ ⟨13, 2, 0, 837787, 438378, 1133, 16384⟩
    (by decide) selected_cut_32553

theorem selected_cut_32554 : selected 8 ⟨837790, by decide⟩
    (prefixPartial 13 438379) = some ⟨13, 2, 0, 837790, 438379, 625, 16384⟩ := by
  decide +kernel

theorem context_13_438379_837790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438379 ⟨837790, by decide⟩ :=
  accepted_of_selected 13 438379 ⟨837790, by decide⟩ ⟨13, 2, 0, 837790, 438379, 625, 16384⟩
    (by decide) selected_cut_32554

theorem unmarked_context_12_109594_837791 : frontier 9 ⟨837791, by decide⟩
    (prefixCache 12 109594) (prefixPartial 12 109594) = false := by
  decide +kernel

theorem node_context_12_109594_837791 : EJMOriginalGlobalDAGData.nodes 9 ⟨837791, by decide⟩ =
    .split (coordinate 12) (![⟨837734, by decide⟩,⟨837759, by decide⟩,⟨837787, by decide⟩,⟨837790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109594_837791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109594 ⟨837791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109594
    ⟨837791, by decide⟩ (by decide) (![⟨837734, by decide⟩,⟨837759, by decide⟩,⟨837787, by decide⟩,⟨837790, by decide⟩]) unmarked_context_12_109594_837791 node_context_12_109594_837791
  intro a
  fin_cases a
  · exact context_13_438376_837734
  · exact context_13_438377_837759
  · exact context_13_438378_837787
  · exact context_13_438379_837790

theorem selected_cut_32555 : selected 8 ⟨837819, by decide⟩
    (prefixPartial 13 438380) = some ⟨13, 2, 0, 837819, 438380, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_438380_837819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438380 ⟨837819, by decide⟩ :=
  accepted_of_selected 13 438380 ⟨837819, by decide⟩ ⟨13, 2, 0, 837819, 438380, 1833, 16384⟩
    (by decide) selected_cut_32555

theorem selected_cut_32556 : selected 8 ⟨837858, by decide⟩
    (prefixPartial 13 438381) = some ⟨13, 2, 0, 837858, 438381, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_438381_837858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438381 ⟨837858, by decide⟩ :=
  accepted_of_selected 13 438381 ⟨837858, by decide⟩ ⟨13, 2, 0, 837858, 438381, 2629, 16384⟩
    (by decide) selected_cut_32556

theorem selected_cut_32557 : selected 8 ⟨837899, by decide⟩
    (prefixPartial 13 438382) = some ⟨13, 2, 0, 837899, 438382, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_438382_837899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438382 ⟨837899, by decide⟩ :=
  accepted_of_selected 13 438382 ⟨837899, by decide⟩ ⟨13, 2, 0, 837899, 438382, 1801, 16384⟩
    (by decide) selected_cut_32557

theorem selected_cut_32558 : selected 8 ⟨837906, by decide⟩
    (prefixPartial 13 438383) = some ⟨13, 2, 0, 837906, 438383, 649, 16384⟩ := by
  decide +kernel

theorem context_13_438383_837906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438383 ⟨837906, by decide⟩ :=
  accepted_of_selected 13 438383 ⟨837906, by decide⟩ ⟨13, 2, 0, 837906, 438383, 649, 16384⟩
    (by decide) selected_cut_32558

theorem unmarked_context_12_109595_837907 : frontier 9 ⟨837907, by decide⟩
    (prefixCache 12 109595) (prefixPartial 12 109595) = false := by
  decide +kernel

theorem node_context_12_109595_837907 : EJMOriginalGlobalDAGData.nodes 9 ⟨837907, by decide⟩ =
    .split (coordinate 12) (![⟨837819, by decide⟩,⟨837858, by decide⟩,⟨837899, by decide⟩,⟨837906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109595_837907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109595 ⟨837907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109595
    ⟨837907, by decide⟩ (by decide) (![⟨837819, by decide⟩,⟨837858, by decide⟩,⟨837899, by decide⟩,⟨837906, by decide⟩]) unmarked_context_12_109595_837907 node_context_12_109595_837907
  intro a
  fin_cases a
  · exact context_13_438380_837819
  · exact context_13_438381_837858
  · exact context_13_438382_837899
  · exact context_13_438383_837906

theorem unmarked_context_11_27398_837908 : frontier 10 ⟨837908, by decide⟩
    (prefixCache 11 27398) (prefixPartial 11 27398) = false := by
  decide +kernel

theorem node_context_11_27398_837908 : EJMOriginalGlobalDAGData.nodes 10 ⟨837908, by decide⟩ =
    .split (coordinate 11) (![⟨837566, by decide⟩,⟨837708, by decide⟩,⟨837791, by decide⟩,⟨837907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27398_837908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27398 ⟨837908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27398
    ⟨837908, by decide⟩ (by decide) (![⟨837566, by decide⟩,⟨837708, by decide⟩,⟨837791, by decide⟩,⟨837907, by decide⟩]) unmarked_context_11_27398_837908 node_context_11_27398_837908
  intro a
  fin_cases a
  · exact context_12_109592_837566
  · exact context_12_109593_837708
  · exact context_12_109594_837791
  · exact context_12_109595_837907

theorem selected_cut_32559 : selected 8 ⟨837929, by decide⟩
    (prefixPartial 13 438384) = some ⟨13, 2, 0, 837929, 438384, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_438384_837929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438384 ⟨837929, by decide⟩ :=
  accepted_of_selected 13 438384 ⟨837929, by decide⟩ ⟨13, 2, 0, 837929, 438384, 1029, 16384⟩
    (by decide) selected_cut_32559

theorem selected_cut_32560 : selected 8 ⟨837966, by decide⟩
    (prefixPartial 13 438385) = some ⟨13, 2, 0, 837966, 438385, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_438385_837966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438385 ⟨837966, by decide⟩ :=
  accepted_of_selected 13 438385 ⟨837966, by decide⟩ ⟨13, 2, 0, 837966, 438385, 2361, 16384⟩
    (by decide) selected_cut_32560

theorem selected_cut_32561 : selected 8 ⟨837986, by decide⟩
    (prefixPartial 13 438386) = some ⟨13, 2, 0, 837986, 438386, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_438386_837986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438386 ⟨837986, by decide⟩ :=
  accepted_of_selected 13 438386 ⟨837986, by decide⟩ ⟨13, 2, 0, 837986, 438386, 1321, 16384⟩
    (by decide) selected_cut_32561

theorem selected_cut_32562 : selected 8 ⟨837995, by decide⟩
    (prefixPartial 13 438387) = some ⟨13, 2, 0, 837995, 438387, 689, 16384⟩ := by
  decide +kernel

theorem context_13_438387_837995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438387 ⟨837995, by decide⟩ :=
  accepted_of_selected 13 438387 ⟨837995, by decide⟩ ⟨13, 2, 0, 837995, 438387, 689, 16384⟩
    (by decide) selected_cut_32562

theorem unmarked_context_12_109596_837996 : frontier 9 ⟨837996, by decide⟩
    (prefixCache 12 109596) (prefixPartial 12 109596) = false := by
  decide +kernel

theorem node_context_12_109596_837996 : EJMOriginalGlobalDAGData.nodes 9 ⟨837996, by decide⟩ =
    .split (coordinate 12) (![⟨837929, by decide⟩,⟨837966, by decide⟩,⟨837986, by decide⟩,⟨837995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109596_837996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109596 ⟨837996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109596
    ⟨837996, by decide⟩ (by decide) (![⟨837929, by decide⟩,⟨837966, by decide⟩,⟨837986, by decide⟩,⟨837995, by decide⟩]) unmarked_context_12_109596_837996 node_context_12_109596_837996
  intro a
  fin_cases a
  · exact context_13_438384_837929
  · exact context_13_438385_837966
  · exact context_13_438386_837986
  · exact context_13_438387_837995

theorem selected_cut_32563 : selected 8 ⟨838032, by decide⟩
    (prefixPartial 13 438388) = some ⟨13, 2, 0, 838032, 438388, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_438388_838032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438388 ⟨838032, by decide⟩ :=
  accepted_of_selected 13 438388 ⟨838032, by decide⟩ ⟨13, 2, 0, 838032, 438388, 1753, 16384⟩
    (by decide) selected_cut_32563

theorem selected_cut_32564 : selected 8 ⟨838080, by decide⟩
    (prefixPartial 13 438389) = some ⟨13, 2, 0, 838080, 438389, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_438389_838080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438389 ⟨838080, by decide⟩ :=
  accepted_of_selected 13 438389 ⟨838080, by decide⟩ ⟨13, 2, 0, 838080, 438389, 2777, 16384⟩
    (by decide) selected_cut_32564

theorem selected_cut_32565 : selected 8 ⟨838130, by decide⟩
    (prefixPartial 13 438390) = some ⟨13, 2, 0, 838130, 438390, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_438390_838130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438390 ⟨838130, by decide⟩ :=
  accepted_of_selected 13 438390 ⟨838130, by decide⟩ ⟨13, 2, 0, 838130, 438390, 1893, 16384⟩
    (by decide) selected_cut_32565

theorem selected_cut_32566 : selected 8 ⟨838138, by decide⟩
    (prefixPartial 13 438391) = some ⟨13, 2, 0, 838138, 438391, 745, 16384⟩ := by
  decide +kernel

theorem context_13_438391_838138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438391 ⟨838138, by decide⟩ :=
  accepted_of_selected 13 438391 ⟨838138, by decide⟩ ⟨13, 2, 0, 838138, 438391, 745, 16384⟩
    (by decide) selected_cut_32566

theorem unmarked_context_12_109597_838139 : frontier 9 ⟨838139, by decide⟩
    (prefixCache 12 109597) (prefixPartial 12 109597) = false := by
  decide +kernel

theorem node_context_12_109597_838139 : EJMOriginalGlobalDAGData.nodes 9 ⟨838139, by decide⟩ =
    .split (coordinate 12) (![⟨838032, by decide⟩,⟨838080, by decide⟩,⟨838130, by decide⟩,⟨838138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109597_838139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109597 ⟨838139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109597
    ⟨838139, by decide⟩ (by decide) (![⟨838032, by decide⟩,⟨838080, by decide⟩,⟨838130, by decide⟩,⟨838138, by decide⟩]) unmarked_context_12_109597_838139 node_context_12_109597_838139
  intro a
  fin_cases a
  · exact context_13_438388_838032
  · exact context_13_438389_838080
  · exact context_13_438390_838130
  · exact context_13_438391_838138

theorem selected_cut_32567 : selected 8 ⟨838161, by decide⟩
    (prefixPartial 13 438392) = some ⟨13, 2, 0, 838161, 438392, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_438392_838161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438392 ⟨838161, by decide⟩ :=
  accepted_of_selected 13 438392 ⟨838161, by decide⟩ ⟨13, 2, 0, 838161, 438392, 1221, 16384⟩
    (by decide) selected_cut_32567

theorem selected_cut_32568 : selected 8 ⟨838192, by decide⟩
    (prefixPartial 13 438393) = some ⟨13, 2, 0, 838192, 438393, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_438393_838192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438393 ⟨838192, by decide⟩ :=
  accepted_of_selected 13 438393 ⟨838192, by decide⟩ ⟨13, 2, 0, 838192, 438393, 2453, 16384⟩
    (by decide) selected_cut_32568

theorem selected_cut_32569 : selected 8 ⟨838211, by decide⟩
    (prefixPartial 13 438394) = some ⟨13, 2, 0, 838211, 438394, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_438394_838211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438394 ⟨838211, by decide⟩ :=
  accepted_of_selected 13 438394 ⟨838211, by decide⟩ ⟨13, 2, 0, 838211, 438394, 1121, 16384⟩
    (by decide) selected_cut_32569

theorem selected_cut_32570 : selected 8 ⟨838220, by decide⟩
    (prefixPartial 13 438395) = some ⟨13, 2, 0, 838220, 438395, 785, 16384⟩ := by
  decide +kernel

theorem context_13_438395_838220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438395 ⟨838220, by decide⟩ :=
  accepted_of_selected 13 438395 ⟨838220, by decide⟩ ⟨13, 2, 0, 838220, 438395, 785, 16384⟩
    (by decide) selected_cut_32570

theorem unmarked_context_12_109598_838221 : frontier 9 ⟨838221, by decide⟩
    (prefixCache 12 109598) (prefixPartial 12 109598) = false := by
  decide +kernel

theorem node_context_12_109598_838221 : EJMOriginalGlobalDAGData.nodes 9 ⟨838221, by decide⟩ =
    .split (coordinate 12) (![⟨838161, by decide⟩,⟨838192, by decide⟩,⟨838211, by decide⟩,⟨838220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109598_838221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109598 ⟨838221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109598
    ⟨838221, by decide⟩ (by decide) (![⟨838161, by decide⟩,⟨838192, by decide⟩,⟨838211, by decide⟩,⟨838220, by decide⟩]) unmarked_context_12_109598_838221 node_context_12_109598_838221
  intro a
  fin_cases a
  · exact context_13_438392_838161
  · exact context_13_438393_838192
  · exact context_13_438394_838211
  · exact context_13_438395_838220

theorem selected_cut_32571 : selected 8 ⟨838253, by decide⟩
    (prefixPartial 13 438396) = some ⟨13, 2, 0, 838253, 438396, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_438396_838253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438396 ⟨838253, by decide⟩ :=
  accepted_of_selected 13 438396 ⟨838253, by decide⟩ ⟨13, 2, 0, 838253, 438396, 1341, 16384⟩
    (by decide) selected_cut_32571

theorem selected_cut_32572 : selected 8 ⟨838281, by decide⟩
    (prefixPartial 13 438397) = some ⟨13, 2, 0, 838281, 438397, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_438397_838281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438397 ⟨838281, by decide⟩ :=
  accepted_of_selected 13 438397 ⟨838281, by decide⟩ ⟨13, 2, 0, 838281, 438397, 2421, 16384⟩
    (by decide) selected_cut_32572

theorem selected_cut_32573 : selected 8 ⟨838304, by decide⟩
    (prefixPartial 13 438398) = some ⟨13, 2, 0, 838304, 438398, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_438398_838304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438398 ⟨838304, by decide⟩ :=
  accepted_of_selected 13 438398 ⟨838304, by decide⟩ ⟨13, 2, 0, 838304, 438398, 1505, 16384⟩
    (by decide) selected_cut_32573

theorem selected_cut_32574 : selected 8 ⟨838310, by decide⟩
    (prefixPartial 13 438399) = some ⟨13, 2, 0, 838310, 438399, 713, 16384⟩ := by
  decide +kernel

theorem context_13_438399_838310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438399 ⟨838310, by decide⟩ :=
  accepted_of_selected 13 438399 ⟨838310, by decide⟩ ⟨13, 2, 0, 838310, 438399, 713, 16384⟩
    (by decide) selected_cut_32574

theorem unmarked_context_12_109599_838311 : frontier 9 ⟨838311, by decide⟩
    (prefixCache 12 109599) (prefixPartial 12 109599) = false := by
  decide +kernel

theorem node_context_12_109599_838311 : EJMOriginalGlobalDAGData.nodes 9 ⟨838311, by decide⟩ =
    .split (coordinate 12) (![⟨838253, by decide⟩,⟨838281, by decide⟩,⟨838304, by decide⟩,⟨838310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109599_838311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109599 ⟨838311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109599
    ⟨838311, by decide⟩ (by decide) (![⟨838253, by decide⟩,⟨838281, by decide⟩,⟨838304, by decide⟩,⟨838310, by decide⟩]) unmarked_context_12_109599_838311 node_context_12_109599_838311
  intro a
  fin_cases a
  · exact context_13_438396_838253
  · exact context_13_438397_838281
  · exact context_13_438398_838304
  · exact context_13_438399_838310

theorem unmarked_context_11_27399_838312 : frontier 10 ⟨838312, by decide⟩
    (prefixCache 11 27399) (prefixPartial 11 27399) = false := by
  decide +kernel

theorem node_context_11_27399_838312 : EJMOriginalGlobalDAGData.nodes 10 ⟨838312, by decide⟩ =
    .split (coordinate 11) (![⟨837996, by decide⟩,⟨838139, by decide⟩,⟨838221, by decide⟩,⟨838311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27399_838312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27399 ⟨838312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27399
    ⟨838312, by decide⟩ (by decide) (![⟨837996, by decide⟩,⟨838139, by decide⟩,⟨838221, by decide⟩,⟨838311, by decide⟩]) unmarked_context_11_27399_838312 node_context_11_27399_838312
  intro a
  fin_cases a
  · exact context_12_109596_837996
  · exact context_12_109597_838139
  · exact context_12_109598_838221
  · exact context_12_109599_838311

theorem unmarked_context_10_6849_838313 : frontier 11 ⟨838313, by decide⟩
    (prefixCache 10 6849) (prefixPartial 10 6849) = false := by
  decide +kernel

theorem node_context_10_6849_838313 : EJMOriginalGlobalDAGData.nodes 11 ⟨838313, by decide⟩ =
    .split (coordinate 10) (![⟨837038, by decide⟩,⟨837464, by decide⟩,⟨837908, by decide⟩,⟨838312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6849_838313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6849 ⟨838313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6849
    ⟨838313, by decide⟩ (by decide) (![⟨837038, by decide⟩,⟨837464, by decide⟩,⟨837908, by decide⟩,⟨838312, by decide⟩]) unmarked_context_10_6849_838313 node_context_10_6849_838313
  intro a
  fin_cases a
  · exact context_11_27396_837038
  · exact context_11_27397_837464
  · exact context_11_27398_837908
  · exact context_11_27399_838312

theorem selected_cut_32575 : selected 9 ⟨790888, by decide⟩
    (prefixPartial 12 109600) = some ⟨12, 1, 0, 790888, 109600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109600_790888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109600 ⟨790888, by decide⟩ :=
  accepted_of_selected 12 109600 ⟨790888, by decide⟩ ⟨12, 1, 0, 790888, 109600, 1, 65536⟩
    (by decide) selected_cut_32575

theorem selected_cut_32576 : selected 8 ⟨838341, by decide⟩
    (prefixPartial 13 438404) = some ⟨13, 2, 0, 838341, 438404, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_438404_838341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438404 ⟨838341, by decide⟩ :=
  accepted_of_selected 13 438404 ⟨838341, by decide⟩ ⟨13, 2, 0, 838341, 438404, 1593, 16384⟩
    (by decide) selected_cut_32576

theorem selected_cut_32577 : selected 8 ⟨838380, by decide⟩
    (prefixPartial 13 438405) = some ⟨13, 2, 0, 838380, 438405, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_438405_838380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438405 ⟨838380, by decide⟩ :=
  accepted_of_selected 13 438405 ⟨838380, by decide⟩ ⟨13, 2, 0, 838380, 438405, 2573, 16384⟩
    (by decide) selected_cut_32577

theorem selected_cut_32578 : selected 8 ⟨838412, by decide⟩
    (prefixPartial 13 438406) = some ⟨13, 2, 0, 838412, 438406, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_438406_838412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438406 ⟨838412, by decide⟩ :=
  accepted_of_selected 13 438406 ⟨838412, by decide⟩ ⟨13, 2, 0, 838412, 438406, 1389, 16384⟩
    (by decide) selected_cut_32578

theorem selected_cut_32579 : selected 8 ⟨838420, by decide⟩
    (prefixPartial 13 438407) = some ⟨13, 2, 0, 838420, 438407, 669, 16384⟩ := by
  decide +kernel

theorem context_13_438407_838420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438407 ⟨838420, by decide⟩ :=
  accepted_of_selected 13 438407 ⟨838420, by decide⟩ ⟨13, 2, 0, 838420, 438407, 669, 16384⟩
    (by decide) selected_cut_32579

theorem unmarked_context_12_109601_838421 : frontier 9 ⟨838421, by decide⟩
    (prefixCache 12 109601) (prefixPartial 12 109601) = false := by
  decide +kernel

theorem node_context_12_109601_838421 : EJMOriginalGlobalDAGData.nodes 9 ⟨838421, by decide⟩ =
    .split (coordinate 12) (![⟨838341, by decide⟩,⟨838380, by decide⟩,⟨838412, by decide⟩,⟨838420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109601_838421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109601 ⟨838421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109601
    ⟨838421, by decide⟩ (by decide) (![⟨838341, by decide⟩,⟨838380, by decide⟩,⟨838412, by decide⟩,⟨838420, by decide⟩]) unmarked_context_12_109601_838421 node_context_12_109601_838421
  intro a
  fin_cases a
  · exact context_13_438404_838341
  · exact context_13_438405_838380
  · exact context_13_438406_838412
  · exact context_13_438407_838420

theorem selected_cut_32580 : selected 8 ⟨838446, by decide⟩
    (prefixPartial 13 438408) = some ⟨13, 2, 0, 838446, 438408, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_438408_838446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438408 ⟨838446, by decide⟩ :=
  accepted_of_selected 13 438408 ⟨838446, by decide⟩ ⟨13, 2, 0, 838446, 438408, 1209, 16384⟩
    (by decide) selected_cut_32580

theorem selected_cut_32581 : selected 8 ⟨838476, by decide⟩
    (prefixPartial 13 438409) = some ⟨13, 2, 0, 838476, 438409, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_438409_838476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438409 ⟨838476, by decide⟩ :=
  accepted_of_selected 13 438409 ⟨838476, by decide⟩ ⟨13, 2, 0, 838476, 438409, 2497, 16384⟩
    (by decide) selected_cut_32581

theorem selected_cut_32582 : selected 8 ⟨838494, by decide⟩
    (prefixPartial 13 438410) = some ⟨13, 2, 0, 838494, 438410, 925, 16384⟩ := by
  decide +kernel

theorem context_13_438410_838494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438410 ⟨838494, by decide⟩ :=
  accepted_of_selected 13 438410 ⟨838494, by decide⟩ ⟨13, 2, 0, 838494, 438410, 925, 16384⟩
    (by decide) selected_cut_32582

theorem selected_cut_32583 : selected 8 ⟨838504, by decide⟩
    (prefixPartial 13 438411) = some ⟨13, 2, 0, 838504, 438411, 749, 16384⟩ := by
  decide +kernel

theorem context_13_438411_838504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438411 ⟨838504, by decide⟩ :=
  accepted_of_selected 13 438411 ⟨838504, by decide⟩ ⟨13, 2, 0, 838504, 438411, 749, 16384⟩
    (by decide) selected_cut_32583

theorem unmarked_context_12_109602_838505 : frontier 9 ⟨838505, by decide⟩
    (prefixCache 12 109602) (prefixPartial 12 109602) = false := by
  decide +kernel

theorem node_context_12_109602_838505 : EJMOriginalGlobalDAGData.nodes 9 ⟨838505, by decide⟩ =
    .split (coordinate 12) (![⟨838446, by decide⟩,⟨838476, by decide⟩,⟨838494, by decide⟩,⟨838504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109602_838505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109602 ⟨838505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109602
    ⟨838505, by decide⟩ (by decide) (![⟨838446, by decide⟩,⟨838476, by decide⟩,⟨838494, by decide⟩,⟨838504, by decide⟩]) unmarked_context_12_109602_838505 node_context_12_109602_838505
  intro a
  fin_cases a
  · exact context_13_438408_838446
  · exact context_13_438409_838476
  · exact context_13_438410_838494
  · exact context_13_438411_838504

theorem selected_cut_32584 : selected 8 ⟨838528, by decide⟩
    (prefixPartial 13 438412) = some ⟨13, 2, 0, 838528, 438412, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_438412_838528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438412 ⟨838528, by decide⟩ :=
  accepted_of_selected 13 438412 ⟨838528, by decide⟩ ⟨13, 2, 0, 838528, 438412, 1349, 16384⟩
    (by decide) selected_cut_32584

theorem selected_cut_32585 : selected 8 ⟨838555, by decide⟩
    (prefixPartial 13 438413) = some ⟨13, 2, 0, 838555, 438413, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_438413_838555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438413 ⟨838555, by decide⟩ :=
  accepted_of_selected 13 438413 ⟨838555, by decide⟩ ⟨13, 2, 0, 838555, 438413, 2677, 16384⟩
    (by decide) selected_cut_32585

theorem selected_cut_32586 : selected 8 ⟨838579, by decide⟩
    (prefixPartial 13 438414) = some ⟨13, 2, 0, 838579, 438414, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_438414_838579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438414 ⟨838579, by decide⟩ :=
  accepted_of_selected 13 438414 ⟨838579, by decide⟩ ⟨13, 2, 0, 838579, 438414, 1265, 16384⟩
    (by decide) selected_cut_32586

theorem selected_cut_32587 : selected 8 ⟨838588, by decide⟩
    (prefixPartial 13 438415) = some ⟨13, 2, 0, 838588, 438415, 701, 16384⟩ := by
  decide +kernel

theorem context_13_438415_838588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438415 ⟨838588, by decide⟩ :=
  accepted_of_selected 13 438415 ⟨838588, by decide⟩ ⟨13, 2, 0, 838588, 438415, 701, 16384⟩
    (by decide) selected_cut_32587

theorem unmarked_context_12_109603_838589 : frontier 9 ⟨838589, by decide⟩
    (prefixCache 12 109603) (prefixPartial 12 109603) = false := by
  decide +kernel

theorem node_context_12_109603_838589 : EJMOriginalGlobalDAGData.nodes 9 ⟨838589, by decide⟩ =
    .split (coordinate 12) (![⟨838528, by decide⟩,⟨838555, by decide⟩,⟨838579, by decide⟩,⟨838588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109603_838589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109603 ⟨838589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109603
    ⟨838589, by decide⟩ (by decide) (![⟨838528, by decide⟩,⟨838555, by decide⟩,⟨838579, by decide⟩,⟨838588, by decide⟩]) unmarked_context_12_109603_838589 node_context_12_109603_838589
  intro a
  fin_cases a
  · exact context_13_438412_838528
  · exact context_13_438413_838555
  · exact context_13_438414_838579
  · exact context_13_438415_838588

theorem unmarked_context_11_27400_838590 : frontier 10 ⟨838590, by decide⟩
    (prefixCache 11 27400) (prefixPartial 11 27400) = false := by
  decide +kernel

theorem node_context_11_27400_838590 : EJMOriginalGlobalDAGData.nodes 10 ⟨838590, by decide⟩ =
    .split (coordinate 11) (![⟨790888, by decide⟩,⟨838421, by decide⟩,⟨838505, by decide⟩,⟨838589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27400_838590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27400 ⟨838590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27400
    ⟨838590, by decide⟩ (by decide) (![⟨790888, by decide⟩,⟨838421, by decide⟩,⟨838505, by decide⟩,⟨838589, by decide⟩]) unmarked_context_11_27400_838590 node_context_11_27400_838590
  intro a
  fin_cases a
  · exact context_12_109600_790888
  · exact context_12_109601_838421
  · exact context_12_109602_838505
  · exact context_12_109603_838589

theorem selected_cut_32588 : selected 8 ⟨838615, by decide⟩
    (prefixPartial 13 438416) = some ⟨13, 2, 0, 838615, 438416, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_438416_838615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438416 ⟨838615, by decide⟩ :=
  accepted_of_selected 13 438416 ⟨838615, by decide⟩ ⟨13, 2, 0, 838615, 438416, 1089, 16384⟩
    (by decide) selected_cut_32588

theorem selected_cut_32589 : selected 8 ⟨838652, by decide⟩
    (prefixPartial 13 438417) = some ⟨13, 2, 0, 838652, 438417, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_438417_838652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438417 ⟨838652, by decide⟩ :=
  accepted_of_selected 13 438417 ⟨838652, by decide⟩ ⟨13, 2, 0, 838652, 438417, 2605, 16384⟩
    (by decide) selected_cut_32589

theorem selected_cut_32590 : selected 8 ⟨838671, by decide⟩
    (prefixPartial 13 438418) = some ⟨13, 2, 0, 838671, 438418, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_438418_838671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438418 ⟨838671, by decide⟩ :=
  accepted_of_selected 13 438418 ⟨838671, by decide⟩ ⟨13, 2, 0, 838671, 438418, 1449, 16384⟩
    (by decide) selected_cut_32590

theorem selected_cut_32591 : selected 8 ⟨838680, by decide⟩
    (prefixPartial 13 438419) = some ⟨13, 2, 0, 838680, 438419, 869, 16384⟩ := by
  decide +kernel

theorem context_13_438419_838680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438419 ⟨838680, by decide⟩ :=
  accepted_of_selected 13 438419 ⟨838680, by decide⟩ ⟨13, 2, 0, 838680, 438419, 869, 16384⟩
    (by decide) selected_cut_32591

theorem unmarked_context_12_109604_838681 : frontier 9 ⟨838681, by decide⟩
    (prefixCache 12 109604) (prefixPartial 12 109604) = false := by
  decide +kernel

theorem node_context_12_109604_838681 : EJMOriginalGlobalDAGData.nodes 9 ⟨838681, by decide⟩ =
    .split (coordinate 12) (![⟨838615, by decide⟩,⟨838652, by decide⟩,⟨838671, by decide⟩,⟨838680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109604_838681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109604 ⟨838681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109604
    ⟨838681, by decide⟩ (by decide) (![⟨838615, by decide⟩,⟨838652, by decide⟩,⟨838671, by decide⟩,⟨838680, by decide⟩]) unmarked_context_12_109604_838681 node_context_12_109604_838681
  intro a
  fin_cases a
  · exact context_13_438416_838615
  · exact context_13_438417_838652
  · exact context_13_438418_838671
  · exact context_13_438419_838680

theorem selected_cut_32592 : selected 8 ⟨838713, by decide⟩
    (prefixPartial 13 438420) = some ⟨13, 2, 0, 838713, 438420, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_438420_838713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438420 ⟨838713, by decide⟩ :=
  accepted_of_selected 13 438420 ⟨838713, by decide⟩ ⟨13, 2, 0, 838713, 438420, 1401, 16384⟩
    (by decide) selected_cut_32592

theorem selected_cut_32593 : selected 8 ⟨838753, by decide⟩
    (prefixPartial 13 438421) = some ⟨13, 2, 0, 838753, 438421, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_438421_838753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438421 ⟨838753, by decide⟩ :=
  accepted_of_selected 13 438421 ⟨838753, by decide⟩ ⟨13, 2, 0, 838753, 438421, 2601, 16384⟩
    (by decide) selected_cut_32593

theorem selected_cut_32594 : selected 8 ⟨838788, by decide⟩
    (prefixPartial 13 438422) = some ⟨13, 2, 0, 838788, 438422, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_438422_838788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438422 ⟨838788, by decide⟩ :=
  accepted_of_selected 13 438422 ⟨838788, by decide⟩ ⟨13, 2, 0, 838788, 438422, 1725, 16384⟩
    (by decide) selected_cut_32594

theorem selected_cut_32595 : selected 8 ⟨838796, by decide⟩
    (prefixPartial 13 438423) = some ⟨13, 2, 0, 838796, 438423, 833, 16384⟩ := by
  decide +kernel

theorem context_13_438423_838796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438423 ⟨838796, by decide⟩ :=
  accepted_of_selected 13 438423 ⟨838796, by decide⟩ ⟨13, 2, 0, 838796, 438423, 833, 16384⟩
    (by decide) selected_cut_32595

theorem unmarked_context_12_109605_838797 : frontier 9 ⟨838797, by decide⟩
    (prefixCache 12 109605) (prefixPartial 12 109605) = false := by
  decide +kernel

theorem node_context_12_109605_838797 : EJMOriginalGlobalDAGData.nodes 9 ⟨838797, by decide⟩ =
    .split (coordinate 12) (![⟨838713, by decide⟩,⟨838753, by decide⟩,⟨838788, by decide⟩,⟨838796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109605_838797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109605 ⟨838797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109605
    ⟨838797, by decide⟩ (by decide) (![⟨838713, by decide⟩,⟨838753, by decide⟩,⟨838788, by decide⟩,⟨838796, by decide⟩]) unmarked_context_12_109605_838797 node_context_12_109605_838797
  intro a
  fin_cases a
  · exact context_13_438420_838713
  · exact context_13_438421_838753
  · exact context_13_438422_838788
  · exact context_13_438423_838796

theorem selected_cut_32596 : selected 8 ⟨838819, by decide⟩
    (prefixPartial 13 438424) = some ⟨13, 2, 0, 838819, 438424, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_438424_838819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438424 ⟨838819, by decide⟩ :=
  accepted_of_selected 13 438424 ⟨838819, by decide⟩ ⟨13, 2, 0, 838819, 438424, 1157, 16384⟩
    (by decide) selected_cut_32596

theorem selected_cut_32597 : selected 8 ⟨838860, by decide⟩
    (prefixPartial 13 438425) = some ⟨13, 2, 0, 838860, 438425, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_438425_838860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438425 ⟨838860, by decide⟩ :=
  accepted_of_selected 13 438425 ⟨838860, by decide⟩ ⟨13, 2, 0, 838860, 438425, 2901, 16384⟩
    (by decide) selected_cut_32597

theorem selected_cut_32598 : selected 8 ⟨838881, by decide⟩
    (prefixPartial 13 438426) = some ⟨13, 2, 0, 838881, 438426, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_438426_838881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438426 ⟨838881, by decide⟩ :=
  accepted_of_selected 13 438426 ⟨838881, by decide⟩ ⟨13, 2, 0, 838881, 438426, 1253, 16384⟩
    (by decide) selected_cut_32598

theorem selected_cut_32599 : selected 8 ⟨838890, by decide⟩
    (prefixPartial 13 438427) = some ⟨13, 2, 0, 838890, 438427, 933, 16384⟩ := by
  decide +kernel

theorem context_13_438427_838890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438427 ⟨838890, by decide⟩ :=
  accepted_of_selected 13 438427 ⟨838890, by decide⟩ ⟨13, 2, 0, 838890, 438427, 933, 16384⟩
    (by decide) selected_cut_32599

theorem unmarked_context_12_109606_838891 : frontier 9 ⟨838891, by decide⟩
    (prefixCache 12 109606) (prefixPartial 12 109606) = false := by
  decide +kernel

theorem node_context_12_109606_838891 : EJMOriginalGlobalDAGData.nodes 9 ⟨838891, by decide⟩ =
    .split (coordinate 12) (![⟨838819, by decide⟩,⟨838860, by decide⟩,⟨838881, by decide⟩,⟨838890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109606_838891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109606 ⟨838891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109606
    ⟨838891, by decide⟩ (by decide) (![⟨838819, by decide⟩,⟨838860, by decide⟩,⟨838881, by decide⟩,⟨838890, by decide⟩]) unmarked_context_12_109606_838891 node_context_12_109606_838891
  intro a
  fin_cases a
  · exact context_13_438424_838819
  · exact context_13_438425_838860
  · exact context_13_438426_838881
  · exact context_13_438427_838890

theorem selected_cut_32600 : selected 8 ⟨838915, by decide⟩
    (prefixPartial 13 438428) = some ⟨13, 2, 0, 838915, 438428, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_438428_838915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438428 ⟨838915, by decide⟩ :=
  accepted_of_selected 13 438428 ⟨838915, by decide⟩ ⟨13, 2, 0, 838915, 438428, 1301, 16384⟩
    (by decide) selected_cut_32600

theorem selected_cut_32601 : selected 8 ⟨838967, by decide⟩
    (prefixPartial 13 438429) = some ⟨13, 2, 0, 838967, 438429, 3081, 16384⟩ := by
  decide +kernel

theorem context_13_438429_838967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438429 ⟨838967, by decide⟩ :=
  accepted_of_selected 13 438429 ⟨838967, by decide⟩ ⟨13, 2, 0, 838967, 438429, 3081, 16384⟩
    (by decide) selected_cut_32601

theorem selected_cut_32602 : selected 8 ⟨839004, by decide⟩
    (prefixPartial 13 438430) = some ⟨13, 2, 0, 839004, 438430, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_438430_839004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438430 ⟨839004, by decide⟩ :=
  accepted_of_selected 13 438430 ⟨839004, by decide⟩ ⟨13, 2, 0, 839004, 438430, 1737, 16384⟩
    (by decide) selected_cut_32602

theorem selected_cut_32603 : selected 8 ⟨839013, by decide⟩
    (prefixPartial 13 438431) = some ⟨13, 2, 0, 839013, 438431, 917, 16384⟩ := by
  decide +kernel

theorem context_13_438431_839013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438431 ⟨839013, by decide⟩ :=
  accepted_of_selected 13 438431 ⟨839013, by decide⟩ ⟨13, 2, 0, 839013, 438431, 917, 16384⟩
    (by decide) selected_cut_32603

theorem unmarked_context_12_109607_839014 : frontier 9 ⟨839014, by decide⟩
    (prefixCache 12 109607) (prefixPartial 12 109607) = false := by
  decide +kernel

theorem node_context_12_109607_839014 : EJMOriginalGlobalDAGData.nodes 9 ⟨839014, by decide⟩ =
    .split (coordinate 12) (![⟨838915, by decide⟩,⟨838967, by decide⟩,⟨839004, by decide⟩,⟨839013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109607_839014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109607 ⟨839014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109607
    ⟨839014, by decide⟩ (by decide) (![⟨838915, by decide⟩,⟨838967, by decide⟩,⟨839004, by decide⟩,⟨839013, by decide⟩]) unmarked_context_12_109607_839014 node_context_12_109607_839014
  intro a
  fin_cases a
  · exact context_13_438428_838915
  · exact context_13_438429_838967
  · exact context_13_438430_839004
  · exact context_13_438431_839013

theorem unmarked_context_11_27401_839015 : frontier 10 ⟨839015, by decide⟩
    (prefixCache 11 27401) (prefixPartial 11 27401) = false := by
  decide +kernel

theorem node_context_11_27401_839015 : EJMOriginalGlobalDAGData.nodes 10 ⟨839015, by decide⟩ =
    .split (coordinate 11) (![⟨838681, by decide⟩,⟨838797, by decide⟩,⟨838891, by decide⟩,⟨839014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27401_839015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27401 ⟨839015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27401
    ⟨839015, by decide⟩ (by decide) (![⟨838681, by decide⟩,⟨838797, by decide⟩,⟨838891, by decide⟩,⟨839014, by decide⟩]) unmarked_context_11_27401_839015 node_context_11_27401_839015
  intro a
  fin_cases a
  · exact context_12_109604_838681
  · exact context_12_109605_838797
  · exact context_12_109606_838891
  · exact context_12_109607_839014

theorem selected_cut_32604 : selected 8 ⟨839027, by decide⟩
    (prefixPartial 13 438432) = some ⟨13, 2, 0, 839027, 438432, 821, 16384⟩ := by
  decide +kernel

theorem context_13_438432_839027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438432 ⟨839027, by decide⟩ :=
  accepted_of_selected 13 438432 ⟨839027, by decide⟩ ⟨13, 2, 0, 839027, 438432, 821, 16384⟩
    (by decide) selected_cut_32604

theorem selected_cut_32605 : selected 8 ⟨839071, by decide⟩
    (prefixPartial 13 438433) = some ⟨13, 2, 0, 839071, 438433, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_438433_839071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438433 ⟨839071, by decide⟩ :=
  accepted_of_selected 13 438433 ⟨839071, by decide⟩ ⟨13, 2, 0, 839071, 438433, 2833, 16384⟩
    (by decide) selected_cut_32605

theorem selected_cut_32606 : selected 8 ⟨839094, by decide⟩
    (prefixPartial 13 438434) = some ⟨13, 2, 0, 839094, 438434, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_438434_839094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438434 ⟨839094, by decide⟩ :=
  accepted_of_selected 13 438434 ⟨839094, by decide⟩ ⟨13, 2, 0, 839094, 438434, 1445, 16384⟩
    (by decide) selected_cut_32606

theorem selected_cut_32607 : selected 8 ⟨839099, by decide⟩
    (prefixPartial 13 438435) = some ⟨13, 2, 0, 839099, 438435, 705, 16384⟩ := by
  decide +kernel

theorem context_13_438435_839099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438435 ⟨839099, by decide⟩ :=
  accepted_of_selected 13 438435 ⟨839099, by decide⟩ ⟨13, 2, 0, 839099, 438435, 705, 16384⟩
    (by decide) selected_cut_32607

theorem unmarked_context_12_109608_839100 : frontier 9 ⟨839100, by decide⟩
    (prefixCache 12 109608) (prefixPartial 12 109608) = false := by
  decide +kernel

theorem node_context_12_109608_839100 : EJMOriginalGlobalDAGData.nodes 9 ⟨839100, by decide⟩ =
    .split (coordinate 12) (![⟨839027, by decide⟩,⟨839071, by decide⟩,⟨839094, by decide⟩,⟨839099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109608_839100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109608 ⟨839100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109608
    ⟨839100, by decide⟩ (by decide) (![⟨839027, by decide⟩,⟨839071, by decide⟩,⟨839094, by decide⟩,⟨839099, by decide⟩]) unmarked_context_12_109608_839100 node_context_12_109608_839100
  intro a
  fin_cases a
  · exact context_13_438432_839027
  · exact context_13_438433_839071
  · exact context_13_438434_839094
  · exact context_13_438435_839099

theorem selected_cut_32608 : selected 8 ⟨839123, by decide⟩
    (prefixPartial 13 438436) = some ⟨13, 2, 0, 839123, 438436, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_438436_839123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438436 ⟨839123, by decide⟩ :=
  accepted_of_selected 13 438436 ⟨839123, by decide⟩ ⟨13, 2, 0, 839123, 438436, 1241, 16384⟩
    (by decide) selected_cut_32608

theorem selected_cut_32609 : selected 8 ⟨839159, by decide⟩
    (prefixPartial 13 438437) = some ⟨13, 2, 0, 839159, 438437, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_438437_839159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438437 ⟨839159, by decide⟩ :=
  accepted_of_selected 13 438437 ⟨839159, by decide⟩ ⟨13, 2, 0, 839159, 438437, 2981, 16384⟩
    (by decide) selected_cut_32609

theorem selected_cut_32610 : selected 8 ⟨839196, by decide⟩
    (prefixPartial 13 438438) = some ⟨13, 2, 0, 839196, 438438, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_438438_839196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438438 ⟨839196, by decide⟩ :=
  accepted_of_selected 13 438438 ⟨839196, by decide⟩ ⟨13, 2, 0, 839196, 438438, 1793, 16384⟩
    (by decide) selected_cut_32610

theorem selected_cut_32611 : selected 8 ⟨839204, by decide⟩
    (prefixPartial 13 438439) = some ⟨13, 2, 0, 839204, 438439, 717, 16384⟩ := by
  decide +kernel

theorem context_13_438439_839204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438439 ⟨839204, by decide⟩ :=
  accepted_of_selected 13 438439 ⟨839204, by decide⟩ ⟨13, 2, 0, 839204, 438439, 717, 16384⟩
    (by decide) selected_cut_32611

theorem unmarked_context_12_109609_839205 : frontier 9 ⟨839205, by decide⟩
    (prefixCache 12 109609) (prefixPartial 12 109609) = false := by
  decide +kernel

theorem node_context_12_109609_839205 : EJMOriginalGlobalDAGData.nodes 9 ⟨839205, by decide⟩ =
    .split (coordinate 12) (![⟨839123, by decide⟩,⟨839159, by decide⟩,⟨839196, by decide⟩,⟨839204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109609_839205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109609 ⟨839205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109609
    ⟨839205, by decide⟩ (by decide) (![⟨839123, by decide⟩,⟨839159, by decide⟩,⟨839196, by decide⟩,⟨839204, by decide⟩]) unmarked_context_12_109609_839205 node_context_12_109609_839205
  intro a
  fin_cases a
  · exact context_13_438436_839123
  · exact context_13_438437_839159
  · exact context_13_438438_839196
  · exact context_13_438439_839204

theorem selected_cut_32612 : selected 8 ⟨839220, by decide⟩
    (prefixPartial 13 438440) = some ⟨13, 2, 0, 839220, 438440, 781, 16384⟩ := by
  decide +kernel

theorem context_13_438440_839220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438440 ⟨839220, by decide⟩ :=
  accepted_of_selected 13 438440 ⟨839220, by decide⟩ ⟨13, 2, 0, 839220, 438440, 781, 16384⟩
    (by decide) selected_cut_32612

theorem selected_cut_32613 : selected 8 ⟨839248, by decide⟩
    (prefixPartial 13 438441) = some ⟨13, 2, 0, 839248, 438441, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_438441_839248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438441 ⟨839248, by decide⟩ :=
  accepted_of_selected 13 438441 ⟨839248, by decide⟩ ⟨13, 2, 0, 839248, 438441, 2705, 16384⟩
    (by decide) selected_cut_32613

theorem selected_cut_32614 : selected 8 ⟨839269, by decide⟩
    (prefixPartial 13 438442) = some ⟨13, 2, 0, 839269, 438442, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_438442_839269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438442 ⟨839269, by decide⟩ :=
  accepted_of_selected 13 438442 ⟨839269, by decide⟩ ⟨13, 2, 0, 839269, 438442, 1141, 16384⟩
    (by decide) selected_cut_32614

theorem selected_cut_32615 : selected 8 ⟨839276, by decide⟩
    (prefixPartial 13 438443) = some ⟨13, 2, 0, 839276, 438443, 709, 16384⟩ := by
  decide +kernel

theorem context_13_438443_839276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438443 ⟨839276, by decide⟩ :=
  accepted_of_selected 13 438443 ⟨839276, by decide⟩ ⟨13, 2, 0, 839276, 438443, 709, 16384⟩
    (by decide) selected_cut_32615

theorem unmarked_context_12_109610_839277 : frontier 9 ⟨839277, by decide⟩
    (prefixCache 12 109610) (prefixPartial 12 109610) = false := by
  decide +kernel

theorem node_context_12_109610_839277 : EJMOriginalGlobalDAGData.nodes 9 ⟨839277, by decide⟩ =
    .split (coordinate 12) (![⟨839220, by decide⟩,⟨839248, by decide⟩,⟨839269, by decide⟩,⟨839276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109610_839277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109610 ⟨839277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109610
    ⟨839277, by decide⟩ (by decide) (![⟨839220, by decide⟩,⟨839248, by decide⟩,⟨839269, by decide⟩,⟨839276, by decide⟩]) unmarked_context_12_109610_839277 node_context_12_109610_839277
  intro a
  fin_cases a
  · exact context_13_438440_839220
  · exact context_13_438441_839248
  · exact context_13_438442_839269
  · exact context_13_438443_839276

theorem selected_cut_32616 : selected 8 ⟨839290, by decide⟩
    (prefixPartial 13 438444) = some ⟨13, 2, 0, 839290, 438444, 961, 16384⟩ := by
  decide +kernel

theorem context_13_438444_839290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438444 ⟨839290, by decide⟩ :=
  accepted_of_selected 13 438444 ⟨839290, by decide⟩ ⟨13, 2, 0, 839290, 438444, 961, 16384⟩
    (by decide) selected_cut_32616

theorem selected_cut_32617 : selected 8 ⟨839328, by decide⟩
    (prefixPartial 13 438445) = some ⟨13, 2, 0, 839328, 438445, 3105, 16384⟩ := by
  decide +kernel

theorem context_13_438445_839328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438445 ⟨839328, by decide⟩ :=
  accepted_of_selected 13 438445 ⟨839328, by decide⟩ ⟨13, 2, 0, 839328, 438445, 3105, 16384⟩
    (by decide) selected_cut_32617

theorem selected_cut_32618 : selected 8 ⟨839360, by decide⟩
    (prefixPartial 13 438446) = some ⟨13, 2, 0, 839360, 438446, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_438446_839360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438446 ⟨839360, by decide⟩ :=
  accepted_of_selected 13 438446 ⟨839360, by decide⟩ ⟨13, 2, 0, 839360, 438446, 1629, 16384⟩
    (by decide) selected_cut_32618

theorem selected_cut_32619 : selected 8 ⟨839368, by decide⟩
    (prefixPartial 13 438447) = some ⟨13, 2, 0, 839368, 438447, 741, 16384⟩ := by
  decide +kernel

theorem context_13_438447_839368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438447 ⟨839368, by decide⟩ :=
  accepted_of_selected 13 438447 ⟨839368, by decide⟩ ⟨13, 2, 0, 839368, 438447, 741, 16384⟩
    (by decide) selected_cut_32619

theorem unmarked_context_12_109611_839369 : frontier 9 ⟨839369, by decide⟩
    (prefixCache 12 109611) (prefixPartial 12 109611) = false := by
  decide +kernel

theorem node_context_12_109611_839369 : EJMOriginalGlobalDAGData.nodes 9 ⟨839369, by decide⟩ =
    .split (coordinate 12) (![⟨839290, by decide⟩,⟨839328, by decide⟩,⟨839360, by decide⟩,⟨839368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109611_839369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109611 ⟨839369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109611
    ⟨839369, by decide⟩ (by decide) (![⟨839290, by decide⟩,⟨839328, by decide⟩,⟨839360, by decide⟩,⟨839368, by decide⟩]) unmarked_context_12_109611_839369 node_context_12_109611_839369
  intro a
  fin_cases a
  · exact context_13_438444_839290
  · exact context_13_438445_839328
  · exact context_13_438446_839360
  · exact context_13_438447_839368

theorem unmarked_context_11_27402_839370 : frontier 10 ⟨839370, by decide⟩
    (prefixCache 11 27402) (prefixPartial 11 27402) = false := by
  decide +kernel

theorem node_context_11_27402_839370 : EJMOriginalGlobalDAGData.nodes 10 ⟨839370, by decide⟩ =
    .split (coordinate 11) (![⟨839100, by decide⟩,⟨839205, by decide⟩,⟨839277, by decide⟩,⟨839369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27402_839370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27402 ⟨839370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27402
    ⟨839370, by decide⟩ (by decide) (![⟨839100, by decide⟩,⟨839205, by decide⟩,⟨839277, by decide⟩,⟨839369, by decide⟩]) unmarked_context_11_27402_839370 node_context_11_27402_839370
  intro a
  fin_cases a
  · exact context_12_109608_839100
  · exact context_12_109609_839205
  · exact context_12_109610_839277
  · exact context_12_109611_839369

theorem selected_cut_32620 : selected 8 ⟨839382, by decide⟩
    (prefixPartial 13 438448) = some ⟨13, 2, 0, 839382, 438448, 521, 16384⟩ := by
  decide +kernel

theorem context_13_438448_839382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438448 ⟨839382, by decide⟩ :=
  accepted_of_selected 13 438448 ⟨839382, by decide⟩ ⟨13, 2, 0, 839382, 438448, 521, 16384⟩
    (by decide) selected_cut_32620

theorem selected_cut_32621 : selected 8 ⟨839414, by decide⟩
    (prefixPartial 13 438449) = some ⟨13, 2, 0, 839414, 438449, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_438449_839414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438449 ⟨839414, by decide⟩ :=
  accepted_of_selected 13 438449 ⟨839414, by decide⟩ ⟨13, 2, 0, 839414, 438449, 2769, 16384⟩
    (by decide) selected_cut_32621

theorem selected_cut_32622 : selected 8 ⟨839437, by decide⟩
    (prefixPartial 13 438450) = some ⟨13, 2, 0, 839437, 438450, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_438450_839437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438450 ⟨839437, by decide⟩ :=
  accepted_of_selected 13 438450 ⟨839437, by decide⟩ ⟨13, 2, 0, 839437, 438450, 1389, 16384⟩
    (by decide) selected_cut_32622

theorem selected_cut_32623 : selected 8 ⟨839446, by decide⟩
    (prefixPartial 13 438451) = some ⟨13, 2, 0, 839446, 438451, 885, 16384⟩ := by
  decide +kernel

theorem context_13_438451_839446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438451 ⟨839446, by decide⟩ :=
  accepted_of_selected 13 438451 ⟨839446, by decide⟩ ⟨13, 2, 0, 839446, 438451, 885, 16384⟩
    (by decide) selected_cut_32623

theorem unmarked_context_12_109612_839447 : frontier 9 ⟨839447, by decide⟩
    (prefixCache 12 109612) (prefixPartial 12 109612) = false := by
  decide +kernel

theorem node_context_12_109612_839447 : EJMOriginalGlobalDAGData.nodes 9 ⟨839447, by decide⟩ =
    .split (coordinate 12) (![⟨839382, by decide⟩,⟨839414, by decide⟩,⟨839437, by decide⟩,⟨839446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109612_839447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109612 ⟨839447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109612
    ⟨839447, by decide⟩ (by decide) (![⟨839382, by decide⟩,⟨839414, by decide⟩,⟨839437, by decide⟩,⟨839446, by decide⟩]) unmarked_context_12_109612_839447 node_context_12_109612_839447
  intro a
  fin_cases a
  · exact context_13_438448_839382
  · exact context_13_438449_839414
  · exact context_13_438450_839437
  · exact context_13_438451_839446

theorem selected_cut_32624 : selected 8 ⟨839463, by decide⟩
    (prefixPartial 13 438452) = some ⟨13, 2, 0, 839463, 438452, 789, 16384⟩ := by
  decide +kernel

theorem context_13_438452_839463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438452 ⟨839463, by decide⟩ :=
  accepted_of_selected 13 438452 ⟨839463, by decide⟩ ⟨13, 2, 0, 839463, 438452, 789, 16384⟩
    (by decide) selected_cut_32624

theorem selected_cut_32625 : selected 8 ⟨839505, by decide⟩
    (prefixPartial 13 438453) = some ⟨13, 2, 0, 839505, 438453, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_438453_839505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438453 ⟨839505, by decide⟩ :=
  accepted_of_selected 13 438453 ⟨839505, by decide⟩ ⟨13, 2, 0, 839505, 438453, 3193, 16384⟩
    (by decide) selected_cut_32625

theorem selected_cut_32626 : selected 8 ⟨839540, by decide⟩
    (prefixPartial 13 438454) = some ⟨13, 2, 0, 839540, 438454, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_438454_839540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438454 ⟨839540, by decide⟩ :=
  accepted_of_selected 13 438454 ⟨839540, by decide⟩ ⟨13, 2, 0, 839540, 438454, 1805, 16384⟩
    (by decide) selected_cut_32626

theorem selected_cut_32627 : selected 8 ⟨839549, by decide⟩
    (prefixPartial 13 438455) = some ⟨13, 2, 0, 839549, 438455, 881, 16384⟩ := by
  decide +kernel

theorem context_13_438455_839549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438455 ⟨839549, by decide⟩ :=
  accepted_of_selected 13 438455 ⟨839549, by decide⟩ ⟨13, 2, 0, 839549, 438455, 881, 16384⟩
    (by decide) selected_cut_32627

theorem unmarked_context_12_109613_839550 : frontier 9 ⟨839550, by decide⟩
    (prefixCache 12 109613) (prefixPartial 12 109613) = false := by
  decide +kernel

theorem node_context_12_109613_839550 : EJMOriginalGlobalDAGData.nodes 9 ⟨839550, by decide⟩ =
    .split (coordinate 12) (![⟨839463, by decide⟩,⟨839505, by decide⟩,⟨839540, by decide⟩,⟨839549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109613_839550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109613 ⟨839550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109613
    ⟨839550, by decide⟩ (by decide) (![⟨839463, by decide⟩,⟨839505, by decide⟩,⟨839540, by decide⟩,⟨839549, by decide⟩]) unmarked_context_12_109613_839550 node_context_12_109613_839550
  intro a
  fin_cases a
  · exact context_13_438452_839463
  · exact context_13_438453_839505
  · exact context_13_438454_839540
  · exact context_13_438455_839549

theorem selected_cut_32628 : selected 8 ⟨839562, by decide⟩
    (prefixPartial 13 438456) = some ⟨13, 2, 0, 839562, 438456, 521, 16384⟩ := by
  decide +kernel

theorem context_13_438456_839562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438456 ⟨839562, by decide⟩ :=
  accepted_of_selected 13 438456 ⟨839562, by decide⟩ ⟨13, 2, 0, 839562, 438456, 521, 16384⟩
    (by decide) selected_cut_32628

theorem selected_cut_32629 : selected 8 ⟨839596, by decide⟩
    (prefixPartial 13 438457) = some ⟨13, 2, 0, 839596, 438457, 2945, 16384⟩ := by
  decide +kernel

theorem context_13_438457_839596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438457 ⟨839596, by decide⟩ :=
  accepted_of_selected 13 438457 ⟨839596, by decide⟩ ⟨13, 2, 0, 839596, 438457, 2945, 16384⟩
    (by decide) selected_cut_32629

theorem selected_cut_32630 : selected 8 ⟨839615, by decide⟩
    (prefixPartial 13 438458) = some ⟨13, 2, 0, 839615, 438458, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_438458_839615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438458 ⟨839615, by decide⟩ :=
  accepted_of_selected 13 438458 ⟨839615, by decide⟩ ⟨13, 2, 0, 839615, 438458, 1145, 16384⟩
    (by decide) selected_cut_32630

theorem selected_cut_32631 : selected 8 ⟨839626, by decide⟩
    (prefixPartial 13 438459) = some ⟨13, 2, 0, 839626, 438459, 925, 16384⟩ := by
  decide +kernel

theorem context_13_438459_839626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438459 ⟨839626, by decide⟩ :=
  accepted_of_selected 13 438459 ⟨839626, by decide⟩ ⟨13, 2, 0, 839626, 438459, 925, 16384⟩
    (by decide) selected_cut_32631

theorem unmarked_context_12_109614_839627 : frontier 9 ⟨839627, by decide⟩
    (prefixCache 12 109614) (prefixPartial 12 109614) = false := by
  decide +kernel

theorem node_context_12_109614_839627 : EJMOriginalGlobalDAGData.nodes 9 ⟨839627, by decide⟩ =
    .split (coordinate 12) (![⟨839562, by decide⟩,⟨839596, by decide⟩,⟨839615, by decide⟩,⟨839626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109614_839627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109614 ⟨839627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109614
    ⟨839627, by decide⟩ (by decide) (![⟨839562, by decide⟩,⟨839596, by decide⟩,⟨839615, by decide⟩,⟨839626, by decide⟩]) unmarked_context_12_109614_839627 node_context_12_109614_839627
  intro a
  fin_cases a
  · exact context_13_438456_839562
  · exact context_13_438457_839596
  · exact context_13_438458_839615
  · exact context_13_438459_839626

theorem selected_cut_32632 : selected 8 ⟨839644, by decide⟩
    (prefixPartial 13 438460) = some ⟨13, 2, 0, 839644, 438460, 509, 16384⟩ := by
  decide +kernel

theorem context_13_438460_839644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438460 ⟨839644, by decide⟩ :=
  accepted_of_selected 13 438460 ⟨839644, by decide⟩ ⟨13, 2, 0, 839644, 438460, 509, 16384⟩
    (by decide) selected_cut_32632

theorem selected_cut_32633 : selected 8 ⟨839683, by decide⟩
    (prefixPartial 13 438461) = some ⟨13, 2, 0, 839683, 438461, 3045, 16384⟩ := by
  decide +kernel

theorem context_13_438461_839683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438461 ⟨839683, by decide⟩ :=
  accepted_of_selected 13 438461 ⟨839683, by decide⟩ ⟨13, 2, 0, 839683, 438461, 3045, 16384⟩
    (by decide) selected_cut_32633

theorem selected_cut_32634 : selected 8 ⟨839708, by decide⟩
    (prefixPartial 13 438462) = some ⟨13, 2, 0, 839708, 438462, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_438462_839708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438462 ⟨839708, by decide⟩ :=
  accepted_of_selected 13 438462 ⟨839708, by decide⟩ ⟨13, 2, 0, 839708, 438462, 1453, 16384⟩
    (by decide) selected_cut_32634

theorem selected_cut_32635 : selected 8 ⟨839720, by decide⟩
    (prefixPartial 13 438463) = some ⟨13, 2, 0, 839720, 438463, 889, 16384⟩ := by
  decide +kernel

theorem context_13_438463_839720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438463 ⟨839720, by decide⟩ :=
  accepted_of_selected 13 438463 ⟨839720, by decide⟩ ⟨13, 2, 0, 839720, 438463, 889, 16384⟩
    (by decide) selected_cut_32635

theorem unmarked_context_12_109615_839721 : frontier 9 ⟨839721, by decide⟩
    (prefixCache 12 109615) (prefixPartial 12 109615) = false := by
  decide +kernel

theorem node_context_12_109615_839721 : EJMOriginalGlobalDAGData.nodes 9 ⟨839721, by decide⟩ =
    .split (coordinate 12) (![⟨839644, by decide⟩,⟨839683, by decide⟩,⟨839708, by decide⟩,⟨839720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109615_839721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109615 ⟨839721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109615
    ⟨839721, by decide⟩ (by decide) (![⟨839644, by decide⟩,⟨839683, by decide⟩,⟨839708, by decide⟩,⟨839720, by decide⟩]) unmarked_context_12_109615_839721 node_context_12_109615_839721
  intro a
  fin_cases a
  · exact context_13_438460_839644
  · exact context_13_438461_839683
  · exact context_13_438462_839708
  · exact context_13_438463_839720

theorem unmarked_context_11_27403_839722 : frontier 10 ⟨839722, by decide⟩
    (prefixCache 11 27403) (prefixPartial 11 27403) = false := by
  decide +kernel

theorem node_context_11_27403_839722 : EJMOriginalGlobalDAGData.nodes 10 ⟨839722, by decide⟩ =
    .split (coordinate 11) (![⟨839447, by decide⟩,⟨839550, by decide⟩,⟨839627, by decide⟩,⟨839721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27403_839722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27403 ⟨839722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27403
    ⟨839722, by decide⟩ (by decide) (![⟨839447, by decide⟩,⟨839550, by decide⟩,⟨839627, by decide⟩,⟨839721, by decide⟩]) unmarked_context_11_27403_839722 node_context_11_27403_839722
  intro a
  fin_cases a
  · exact context_12_109612_839447
  · exact context_12_109613_839550
  · exact context_12_109614_839627
  · exact context_12_109615_839721

theorem unmarked_context_10_6850_839723 : frontier 11 ⟨839723, by decide⟩
    (prefixCache 10 6850) (prefixPartial 10 6850) = false := by
  decide +kernel

theorem node_context_10_6850_839723 : EJMOriginalGlobalDAGData.nodes 11 ⟨839723, by decide⟩ =
    .split (coordinate 10) (![⟨838590, by decide⟩,⟨839015, by decide⟩,⟨839370, by decide⟩,⟨839722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6850_839723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6850 ⟨839723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6850
    ⟨839723, by decide⟩ (by decide) (![⟨838590, by decide⟩,⟨839015, by decide⟩,⟨839370, by decide⟩,⟨839722, by decide⟩]) unmarked_context_10_6850_839723 node_context_10_6850_839723
  intro a
  fin_cases a
  · exact context_11_27400_838590
  · exact context_11_27401_839015
  · exact context_11_27402_839370
  · exact context_11_27403_839722

theorem selected_cut_32636 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 109616) = some ⟨12, 1, 0, 792260, 109616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109616_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109616 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 109616 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 109616, 1, 65536⟩
    (by decide) selected_cut_32636

theorem selected_cut_32637 : selected 8 ⟨839734, by decide⟩
    (prefixPartial 13 438468) = some ⟨13, 2, 0, 839734, 438468, 557, 16384⟩ := by
  decide +kernel

theorem context_13_438468_839734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438468 ⟨839734, by decide⟩ :=
  accepted_of_selected 13 438468 ⟨839734, by decide⟩ ⟨13, 2, 0, 839734, 438468, 557, 16384⟩
    (by decide) selected_cut_32637

theorem selected_cut_32638 : selected 8 ⟨839762, by decide⟩
    (prefixPartial 13 438469) = some ⟨13, 2, 0, 839762, 438469, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_438469_839762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438469 ⟨839762, by decide⟩ :=
  accepted_of_selected 13 438469 ⟨839762, by decide⟩ ⟨13, 2, 0, 839762, 438469, 2217, 16384⟩
    (by decide) selected_cut_32638

theorem selected_cut_32639 : selected 8 ⟨839784, by decide⟩
    (prefixPartial 13 438470) = some ⟨13, 2, 0, 839784, 438470, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_438470_839784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438470 ⟨839784, by decide⟩ :=
  accepted_of_selected 13 438470 ⟨839784, by decide⟩ ⟨13, 2, 0, 839784, 438470, 1273, 16384⟩
    (by decide) selected_cut_32639

theorem selected_cut_32640 : selected 8 ⟨839790, by decide⟩
    (prefixPartial 13 438471) = some ⟨13, 2, 0, 839790, 438471, 645, 16384⟩ := by
  decide +kernel

theorem context_13_438471_839790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438471 ⟨839790, by decide⟩ :=
  accepted_of_selected 13 438471 ⟨839790, by decide⟩ ⟨13, 2, 0, 839790, 438471, 645, 16384⟩
    (by decide) selected_cut_32640

theorem unmarked_context_12_109617_839791 : frontier 9 ⟨839791, by decide⟩
    (prefixCache 12 109617) (prefixPartial 12 109617) = false := by
  decide +kernel

theorem node_context_12_109617_839791 : EJMOriginalGlobalDAGData.nodes 9 ⟨839791, by decide⟩ =
    .split (coordinate 12) (![⟨839734, by decide⟩,⟨839762, by decide⟩,⟨839784, by decide⟩,⟨839790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109617_839791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109617 ⟨839791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109617
    ⟨839791, by decide⟩ (by decide) (![⟨839734, by decide⟩,⟨839762, by decide⟩,⟨839784, by decide⟩,⟨839790, by decide⟩]) unmarked_context_12_109617_839791 node_context_12_109617_839791
  intro a
  fin_cases a
  · exact context_13_438468_839734
  · exact context_13_438469_839762
  · exact context_13_438470_839784
  · exact context_13_438471_839790

theorem selected_cut_32641 : selected 8 ⟨839800, by decide⟩
    (prefixPartial 13 438472) = some ⟨13, 2, 0, 839800, 438472, 457, 16384⟩ := by
  decide +kernel

theorem context_13_438472_839800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438472 ⟨839800, by decide⟩ :=
  accepted_of_selected 13 438472 ⟨839800, by decide⟩ ⟨13, 2, 0, 839800, 438472, 457, 16384⟩
    (by decide) selected_cut_32641

theorem selected_cut_32642 : selected 8 ⟨839829, by decide⟩
    (prefixPartial 13 438473) = some ⟨13, 2, 0, 839829, 438473, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_438473_839829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438473 ⟨839829, by decide⟩ :=
  accepted_of_selected 13 438473 ⟨839829, by decide⟩ ⟨13, 2, 0, 839829, 438473, 2197, 16384⟩
    (by decide) selected_cut_32642

theorem selected_cut_32643 : selected 8 ⟨839844, by decide⟩
    (prefixPartial 13 438474) = some ⟨13, 2, 0, 839844, 438474, 825, 16384⟩ := by
  decide +kernel

theorem context_13_438474_839844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 438474 ⟨839844, by decide⟩ :=
  accepted_of_selected 13 438474 ⟨839844, by decide⟩ ⟨13, 2, 0, 839844, 438474, 825, 16384⟩
    (by decide) selected_cut_32643

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
