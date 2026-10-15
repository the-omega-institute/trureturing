/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover426
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_40994 : selected 9 ⟨1118571, by decide⟩
    (prefixPartial 12 333833) = some ⟨12, 2, 0, 1118571, 333833, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_333833_1118571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333833 ⟨1118571, by decide⟩ :=
  accepted_of_selected 12 333833 ⟨1118571, by decide⟩ ⟨12, 2, 0, 1118571, 333833, 2953, 65536⟩
    (by decide) selected_cut_40994

theorem selected_cut_40995 : selected 9 ⟨592223, by decide⟩
    (prefixPartial 12 333834) = some ⟨12, 1, 0, 592223, 333834, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333834_592223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333834 ⟨592223, by decide⟩ :=
  accepted_of_selected 12 333834 ⟨592223, by decide⟩ ⟨12, 1, 0, 592223, 333834, 1, 65536⟩
    (by decide) selected_cut_40995

theorem selected_cut_40996 : selected 9 ⟨1118623, by decide⟩
    (prefixPartial 12 333835) = some ⟨12, 2, 0, 1118623, 333835, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_333835_1118623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333835 ⟨1118623, by decide⟩ :=
  accepted_of_selected 12 333835 ⟨1118623, by decide⟩ ⟨12, 2, 0, 1118623, 333835, 2909, 65536⟩
    (by decide) selected_cut_40996

theorem unmarked_context_11_83458_1118624 : frontier 10 ⟨1118624, by decide⟩
    (prefixCache 11 83458) (prefixPartial 11 83458) = false := by
  decide +kernel

theorem node_context_11_83458_1118624 : EJMOriginalGlobalDAGData.nodes 10 ⟨1118624, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1118571, by decide⟩,⟨592223, by decide⟩,⟨1118623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83458_1118624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83458 ⟨1118624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83458
    ⟨1118624, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1118571, by decide⟩,⟨592223, by decide⟩,⟨1118623, by decide⟩]) unmarked_context_11_83458_1118624 node_context_11_83458_1118624
  intro a
  fin_cases a
  · exact context_12_333832_448748
  · exact context_12_333833_1118571
  · exact context_12_333834_592223
  · exact context_12_333835_1118623

theorem selected_cut_40997 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 333836) = some ⟨12, 1, 0, 448748, 333836, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333836_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333836 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 333836 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 333836, 1, 65536⟩
    (by decide) selected_cut_40997

theorem selected_cut_40998 : selected 9 ⟨1118689, by decide⟩
    (prefixPartial 12 333837) = some ⟨12, 2, 0, 1118689, 333837, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_333837_1118689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333837 ⟨1118689, by decide⟩ :=
  accepted_of_selected 12 333837 ⟨1118689, by decide⟩ ⟨12, 2, 0, 1118689, 333837, 2985, 65536⟩
    (by decide) selected_cut_40998

theorem selected_cut_40999 : selected 9 ⟨1118746, by decide⟩
    (prefixPartial 12 333838) = some ⟨12, 2, 0, 1118746, 333838, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_333838_1118746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333838 ⟨1118746, by decide⟩ :=
  accepted_of_selected 12 333838 ⟨1118746, by decide⟩ ⟨12, 2, 0, 1118746, 333838, 3021, 65536⟩
    (by decide) selected_cut_40999

theorem selected_cut_41000 : selected 9 ⟨1118789, by decide⟩
    (prefixPartial 12 333839) = some ⟨12, 2, 0, 1118789, 333839, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_333839_1118789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333839 ⟨1118789, by decide⟩ :=
  accepted_of_selected 12 333839 ⟨1118789, by decide⟩ ⟨12, 2, 0, 1118789, 333839, 2665, 65536⟩
    (by decide) selected_cut_41000

theorem unmarked_context_11_83459_1118790 : frontier 10 ⟨1118790, by decide⟩
    (prefixCache 11 83459) (prefixPartial 11 83459) = false := by
  decide +kernel

theorem node_context_11_83459_1118790 : EJMOriginalGlobalDAGData.nodes 10 ⟨1118790, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1118689, by decide⟩,⟨1118746, by decide⟩,⟨1118789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83459_1118790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83459 ⟨1118790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83459
    ⟨1118790, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1118689, by decide⟩,⟨1118746, by decide⟩,⟨1118789, by decide⟩]) unmarked_context_11_83459_1118790 node_context_11_83459_1118790
  intro a
  fin_cases a
  · exact context_12_333836_448748
  · exact context_12_333837_1118689
  · exact context_12_333838_1118746
  · exact context_12_333839_1118789

theorem unmarked_context_10_20864_1118791 : frontier 11 ⟨1118791, by decide⟩
    (prefixCache 10 20864) (prefixPartial 10 20864) = false := by
  decide +kernel

theorem node_context_10_20864_1118791 : EJMOriginalGlobalDAGData.nodes 11 ⟨1118791, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1118508, by decide⟩,⟨1118624, by decide⟩,⟨1118790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20864_1118791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20864 ⟨1118791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20864
    ⟨1118791, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1118508, by decide⟩,⟨1118624, by decide⟩,⟨1118790, by decide⟩]) unmarked_context_10_20864_1118791 node_context_10_20864_1118791
  intro a
  fin_cases a
  · exact context_11_83456_434745
  · exact context_11_83457_1118508
  · exact context_11_83458_1118624
  · exact context_11_83459_1118790

theorem selected_cut_41001 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333840) = some ⟨12, 1, 0, 1108174, 333840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333840_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333840 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333840 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333840, 1, 65536⟩
    (by decide) selected_cut_41001

theorem selected_cut_41002 : selected 9 ⟨1118853, by decide⟩
    (prefixPartial 12 333841) = some ⟨12, 2, 0, 1118853, 333841, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_333841_1118853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333841 ⟨1118853, by decide⟩ :=
  accepted_of_selected 12 333841 ⟨1118853, by decide⟩ ⟨12, 2, 0, 1118853, 333841, 2889, 65536⟩
    (by decide) selected_cut_41002

theorem selected_cut_41003 : selected 9 ⟨1118912, by decide⟩
    (prefixPartial 12 333842) = some ⟨12, 2, 0, 1118912, 333842, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_333842_1118912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333842 ⟨1118912, by decide⟩ :=
  accepted_of_selected 12 333842 ⟨1118912, by decide⟩ ⟨12, 2, 0, 1118912, 333842, 2985, 65536⟩
    (by decide) selected_cut_41003

theorem selected_cut_41004 : selected 9 ⟨1118963, by decide⟩
    (prefixPartial 12 333843) = some ⟨12, 2, 0, 1118963, 333843, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_333843_1118963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333843 ⟨1118963, by decide⟩ :=
  accepted_of_selected 12 333843 ⟨1118963, by decide⟩ ⟨12, 2, 0, 1118963, 333843, 2773, 65536⟩
    (by decide) selected_cut_41004

theorem unmarked_context_11_83460_1118964 : frontier 10 ⟨1118964, by decide⟩
    (prefixCache 11 83460) (prefixPartial 11 83460) = false := by
  decide +kernel

theorem node_context_11_83460_1118964 : EJMOriginalGlobalDAGData.nodes 10 ⟨1118964, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1118853, by decide⟩,⟨1118912, by decide⟩,⟨1118963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83460_1118964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83460 ⟨1118964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83460
    ⟨1118964, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1118853, by decide⟩,⟨1118912, by decide⟩,⟨1118963, by decide⟩]) unmarked_context_11_83460_1118964 node_context_11_83460_1118964
  intro a
  fin_cases a
  · exact context_12_333840_1108174
  · exact context_12_333841_1118853
  · exact context_12_333842_1118912
  · exact context_12_333843_1118963

theorem selected_cut_41005 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333844) = some ⟨12, 1, 0, 1108174, 333844, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333844_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333844 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333844 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333844, 1, 65536⟩
    (by decide) selected_cut_41005

theorem selected_cut_41006 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 333845) = some ⟨12, 1, 0, 1118965, 333845, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333845_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333845 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 333845 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 333845, 1, 65536⟩
    (by decide) selected_cut_41006

theorem selected_cut_41007 : selected 9 ⟨1119032, by decide⟩
    (prefixPartial 12 333846) = some ⟨12, 2, 0, 1119032, 333846, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_333846_1119032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333846 ⟨1119032, by decide⟩ :=
  accepted_of_selected 12 333846 ⟨1119032, by decide⟩ ⟨12, 2, 0, 1119032, 333846, 3021, 65536⟩
    (by decide) selected_cut_41007

theorem selected_cut_41008 : selected 9 ⟨1119090, by decide⟩
    (prefixPartial 12 333847) = some ⟨12, 2, 0, 1119090, 333847, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_333847_1119090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333847 ⟨1119090, by decide⟩ :=
  accepted_of_selected 12 333847 ⟨1119090, by decide⟩ ⟨12, 2, 0, 1119090, 333847, 2969, 65536⟩
    (by decide) selected_cut_41008

theorem unmarked_context_11_83461_1119091 : frontier 10 ⟨1119091, by decide⟩
    (prefixCache 11 83461) (prefixPartial 11 83461) = false := by
  decide +kernel

theorem node_context_11_83461_1119091 : EJMOriginalGlobalDAGData.nodes 10 ⟨1119091, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1119032, by decide⟩,⟨1119090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83461_1119091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83461 ⟨1119091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83461
    ⟨1119091, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1119032, by decide⟩,⟨1119090, by decide⟩]) unmarked_context_11_83461_1119091 node_context_11_83461_1119091
  intro a
  fin_cases a
  · exact context_12_333844_1108174
  · exact context_12_333845_1118965
  · exact context_12_333846_1119032
  · exact context_12_333847_1119090

theorem selected_cut_41009 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333848) = some ⟨12, 1, 0, 1108174, 333848, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333848_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333848 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333848 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333848, 1, 65536⟩
    (by decide) selected_cut_41009

theorem selected_cut_41010 : selected 9 ⟨1119157, by decide⟩
    (prefixPartial 12 333849) = some ⟨12, 2, 0, 1119157, 333849, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_333849_1119157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333849 ⟨1119157, by decide⟩ :=
  accepted_of_selected 12 333849 ⟨1119157, by decide⟩ ⟨12, 2, 0, 1119157, 333849, 2969, 65536⟩
    (by decide) selected_cut_41010

theorem selected_cut_41011 : selected 9 ⟨1119213, by decide⟩
    (prefixPartial 12 333850) = some ⟨12, 2, 0, 1119213, 333850, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_333850_1119213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333850 ⟨1119213, by decide⟩ :=
  accepted_of_selected 12 333850 ⟨1119213, by decide⟩ ⟨12, 2, 0, 1119213, 333850, 2973, 65536⟩
    (by decide) selected_cut_41011

theorem selected_cut_41012 : selected 9 ⟨1119288, by decide⟩
    (prefixPartial 12 333851) = some ⟨12, 2, 0, 1119288, 333851, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_333851_1119288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333851 ⟨1119288, by decide⟩ :=
  accepted_of_selected 12 333851 ⟨1119288, by decide⟩ ⟨12, 2, 0, 1119288, 333851, 3245, 65536⟩
    (by decide) selected_cut_41012

theorem unmarked_context_11_83462_1119289 : frontier 10 ⟨1119289, by decide⟩
    (prefixCache 11 83462) (prefixPartial 11 83462) = false := by
  decide +kernel

theorem node_context_11_83462_1119289 : EJMOriginalGlobalDAGData.nodes 10 ⟨1119289, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1119157, by decide⟩,⟨1119213, by decide⟩,⟨1119288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83462_1119289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83462 ⟨1119289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83462
    ⟨1119289, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1119157, by decide⟩,⟨1119213, by decide⟩,⟨1119288, by decide⟩]) unmarked_context_11_83462_1119289 node_context_11_83462_1119289
  intro a
  fin_cases a
  · exact context_12_333848_1108174
  · exact context_12_333849_1119157
  · exact context_12_333850_1119213
  · exact context_12_333851_1119288

theorem selected_cut_41013 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333852) = some ⟨12, 1, 0, 1108174, 333852, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333852_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333852 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333852 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333852, 1, 65536⟩
    (by decide) selected_cut_41013

theorem selected_cut_41014 : selected 9 ⟨1119346, by decide⟩
    (prefixPartial 12 333853) = some ⟨12, 2, 0, 1119346, 333853, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_333853_1119346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333853 ⟨1119346, by decide⟩ :=
  accepted_of_selected 12 333853 ⟨1119346, by decide⟩ ⟨12, 2, 0, 1119346, 333853, 2997, 65536⟩
    (by decide) selected_cut_41014

theorem selected_cut_41015 : selected 9 ⟨1119417, by decide⟩
    (prefixPartial 12 333854) = some ⟨12, 2, 0, 1119417, 333854, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_333854_1119417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333854 ⟨1119417, by decide⟩ :=
  accepted_of_selected 12 333854 ⟨1119417, by decide⟩ ⟨12, 2, 0, 1119417, 333854, 3397, 65536⟩
    (by decide) selected_cut_41015

theorem selected_cut_41016 : selected 9 ⟨1119463, by decide⟩
    (prefixPartial 12 333855) = some ⟨12, 2, 0, 1119463, 333855, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_333855_1119463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333855 ⟨1119463, by decide⟩ :=
  accepted_of_selected 12 333855 ⟨1119463, by decide⟩ ⟨12, 2, 0, 1119463, 333855, 2797, 65536⟩
    (by decide) selected_cut_41016

theorem unmarked_context_11_83463_1119464 : frontier 10 ⟨1119464, by decide⟩
    (prefixCache 11 83463) (prefixPartial 11 83463) = false := by
  decide +kernel

theorem node_context_11_83463_1119464 : EJMOriginalGlobalDAGData.nodes 10 ⟨1119464, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1119346, by decide⟩,⟨1119417, by decide⟩,⟨1119463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83463_1119464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83463 ⟨1119464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83463
    ⟨1119464, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1119346, by decide⟩,⟨1119417, by decide⟩,⟨1119463, by decide⟩]) unmarked_context_11_83463_1119464 node_context_11_83463_1119464
  intro a
  fin_cases a
  · exact context_12_333852_1108174
  · exact context_12_333853_1119346
  · exact context_12_333854_1119417
  · exact context_12_333855_1119463

theorem unmarked_context_10_20865_1119465 : frontier 11 ⟨1119465, by decide⟩
    (prefixCache 10 20865) (prefixPartial 10 20865) = false := by
  decide +kernel

theorem node_context_10_20865_1119465 : EJMOriginalGlobalDAGData.nodes 11 ⟨1119465, by decide⟩ =
    .split (coordinate 10) (![⟨1118964, by decide⟩,⟨1119091, by decide⟩,⟨1119289, by decide⟩,⟨1119464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20865_1119465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20865 ⟨1119465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20865
    ⟨1119465, by decide⟩ (by decide) (![⟨1118964, by decide⟩,⟨1119091, by decide⟩,⟨1119289, by decide⟩,⟨1119464, by decide⟩]) unmarked_context_10_20865_1119465 node_context_10_20865_1119465
  intro a
  fin_cases a
  · exact context_11_83460_1118964
  · exact context_11_83461_1119091
  · exact context_11_83462_1119289
  · exact context_11_83463_1119464

theorem selected_cut_41017 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333856) = some ⟨12, 1, 0, 1108174, 333856, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333856_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333856 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333856 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333856, 1, 65536⟩
    (by decide) selected_cut_41017

theorem selected_cut_41018 : selected 9 ⟨1119530, by decide⟩
    (prefixPartial 12 333857) = some ⟨12, 2, 0, 1119530, 333857, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_333857_1119530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333857 ⟨1119530, by decide⟩ :=
  accepted_of_selected 12 333857 ⟨1119530, by decide⟩ ⟨12, 2, 0, 1119530, 333857, 2893, 65536⟩
    (by decide) selected_cut_41018

theorem selected_cut_41019 : selected 9 ⟨1119584, by decide⟩
    (prefixPartial 12 333858) = some ⟨12, 2, 0, 1119584, 333858, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_333858_1119584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333858 ⟨1119584, by decide⟩ :=
  accepted_of_selected 12 333858 ⟨1119584, by decide⟩ ⟨12, 2, 0, 1119584, 333858, 2965, 65536⟩
    (by decide) selected_cut_41019

theorem selected_cut_41020 : selected 9 ⟨1119640, by decide⟩
    (prefixPartial 12 333859) = some ⟨12, 2, 0, 1119640, 333859, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_333859_1119640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333859 ⟨1119640, by decide⟩ :=
  accepted_of_selected 12 333859 ⟨1119640, by decide⟩ ⟨12, 2, 0, 1119640, 333859, 2693, 65536⟩
    (by decide) selected_cut_41020

theorem unmarked_context_11_83464_1119641 : frontier 10 ⟨1119641, by decide⟩
    (prefixCache 11 83464) (prefixPartial 11 83464) = false := by
  decide +kernel

theorem node_context_11_83464_1119641 : EJMOriginalGlobalDAGData.nodes 10 ⟨1119641, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1119530, by decide⟩,⟨1119584, by decide⟩,⟨1119640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83464_1119641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83464 ⟨1119641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83464
    ⟨1119641, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1119530, by decide⟩,⟨1119584, by decide⟩,⟨1119640, by decide⟩]) unmarked_context_11_83464_1119641 node_context_11_83464_1119641
  intro a
  fin_cases a
  · exact context_12_333856_1108174
  · exact context_12_333857_1119530
  · exact context_12_333858_1119584
  · exact context_12_333859_1119640

theorem selected_cut_41021 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333860) = some ⟨12, 1, 0, 1108174, 333860, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333860_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333860 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333860 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333860, 1, 65536⟩
    (by decide) selected_cut_41021

theorem selected_cut_41022 : selected 9 ⟨1119722, by decide⟩
    (prefixPartial 12 333861) = some ⟨12, 2, 0, 1119722, 333861, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_333861_1119722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333861 ⟨1119722, by decide⟩ :=
  accepted_of_selected 12 333861 ⟨1119722, by decide⟩ ⟨12, 2, 0, 1119722, 333861, 3233, 65536⟩
    (by decide) selected_cut_41022

theorem selected_cut_41023 : selected 9 ⟨1119778, by decide⟩
    (prefixPartial 12 333862) = some ⟨12, 2, 0, 1119778, 333862, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_333862_1119778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333862 ⟨1119778, by decide⟩ :=
  accepted_of_selected 12 333862 ⟨1119778, by decide⟩ ⟨12, 2, 0, 1119778, 333862, 2873, 65536⟩
    (by decide) selected_cut_41023

theorem selected_cut_41024 : selected 9 ⟨1119829, by decide⟩
    (prefixPartial 12 333863) = some ⟨12, 2, 0, 1119829, 333863, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_333863_1119829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333863 ⟨1119829, by decide⟩ :=
  accepted_of_selected 12 333863 ⟨1119829, by decide⟩ ⟨12, 2, 0, 1119829, 333863, 2761, 65536⟩
    (by decide) selected_cut_41024

theorem unmarked_context_11_83465_1119830 : frontier 10 ⟨1119830, by decide⟩
    (prefixCache 11 83465) (prefixPartial 11 83465) = false := by
  decide +kernel

theorem node_context_11_83465_1119830 : EJMOriginalGlobalDAGData.nodes 10 ⟨1119830, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1119722, by decide⟩,⟨1119778, by decide⟩,⟨1119829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83465_1119830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83465 ⟨1119830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83465
    ⟨1119830, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1119722, by decide⟩,⟨1119778, by decide⟩,⟨1119829, by decide⟩]) unmarked_context_11_83465_1119830 node_context_11_83465_1119830
  intro a
  fin_cases a
  · exact context_12_333860_1108174
  · exact context_12_333861_1119722
  · exact context_12_333862_1119778
  · exact context_12_333863_1119829

theorem selected_cut_41025 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 83466) = some ⟨11, 1, 0, 900587, 83466, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83466_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83466 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 83466 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 83466, 1, 262144⟩
    (by decide) selected_cut_41025

theorem selected_cut_41026 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333868) = some ⟨12, 1, 0, 1108174, 333868, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333868_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333868 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333868 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333868, 1, 65536⟩
    (by decide) selected_cut_41026

theorem selected_cut_41027 : selected 9 ⟨1119886, by decide⟩
    (prefixPartial 12 333869) = some ⟨12, 2, 0, 1119886, 333869, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_333869_1119886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333869 ⟨1119886, by decide⟩ :=
  accepted_of_selected 12 333869 ⟨1119886, by decide⟩ ⟨12, 2, 0, 1119886, 333869, 2961, 65536⟩
    (by decide) selected_cut_41027

theorem selected_cut_41028 : selected 9 ⟨1119958, by decide⟩
    (prefixPartial 12 333870) = some ⟨12, 2, 0, 1119958, 333870, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_333870_1119958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333870 ⟨1119958, by decide⟩ :=
  accepted_of_selected 12 333870 ⟨1119958, by decide⟩ ⟨12, 2, 0, 1119958, 333870, 3465, 65536⟩
    (by decide) selected_cut_41028

theorem selected_cut_41029 : selected 9 ⟨1120013, by decide⟩
    (prefixPartial 12 333871) = some ⟨12, 2, 0, 1120013, 333871, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_333871_1120013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333871 ⟨1120013, by decide⟩ :=
  accepted_of_selected 12 333871 ⟨1120013, by decide⟩ ⟨12, 2, 0, 1120013, 333871, 2729, 65536⟩
    (by decide) selected_cut_41029

theorem unmarked_context_11_83467_1120014 : frontier 10 ⟨1120014, by decide⟩
    (prefixCache 11 83467) (prefixPartial 11 83467) = false := by
  decide +kernel

theorem node_context_11_83467_1120014 : EJMOriginalGlobalDAGData.nodes 10 ⟨1120014, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1119886, by decide⟩,⟨1119958, by decide⟩,⟨1120013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83467_1120014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83467 ⟨1120014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83467
    ⟨1120014, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1119886, by decide⟩,⟨1119958, by decide⟩,⟨1120013, by decide⟩]) unmarked_context_11_83467_1120014 node_context_11_83467_1120014
  intro a
  fin_cases a
  · exact context_12_333868_1108174
  · exact context_12_333869_1119886
  · exact context_12_333870_1119958
  · exact context_12_333871_1120013

theorem unmarked_context_10_20866_1120015 : frontier 11 ⟨1120015, by decide⟩
    (prefixCache 10 20866) (prefixPartial 10 20866) = false := by
  decide +kernel

theorem node_context_10_20866_1120015 : EJMOriginalGlobalDAGData.nodes 11 ⟨1120015, by decide⟩ =
    .split (coordinate 10) (![⟨1119641, by decide⟩,⟨1119830, by decide⟩,⟨900587, by decide⟩,⟨1120014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20866_1120015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20866 ⟨1120015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20866
    ⟨1120015, by decide⟩ (by decide) (![⟨1119641, by decide⟩,⟨1119830, by decide⟩,⟨900587, by decide⟩,⟨1120014, by decide⟩]) unmarked_context_10_20866_1120015 node_context_10_20866_1120015
  intro a
  fin_cases a
  · exact context_11_83464_1119641
  · exact context_11_83465_1119830
  · exact context_11_83466_900587
  · exact context_11_83467_1120014

theorem selected_cut_41030 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333872) = some ⟨12, 1, 0, 1108174, 333872, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333872_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333872 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333872 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333872, 1, 65536⟩
    (by decide) selected_cut_41030

theorem selected_cut_41031 : selected 9 ⟨1120073, by decide⟩
    (prefixPartial 12 333873) = some ⟨12, 2, 0, 1120073, 333873, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_333873_1120073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333873 ⟨1120073, by decide⟩ :=
  accepted_of_selected 12 333873 ⟨1120073, by decide⟩ ⟨12, 2, 0, 1120073, 333873, 2713, 65536⟩
    (by decide) selected_cut_41031

theorem selected_cut_41032 : selected 9 ⟨1120122, by decide⟩
    (prefixPartial 12 333874) = some ⟨12, 2, 0, 1120122, 333874, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_333874_1120122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333874 ⟨1120122, by decide⟩ :=
  accepted_of_selected 12 333874 ⟨1120122, by decide⟩ ⟨12, 2, 0, 1120122, 333874, 2789, 65536⟩
    (by decide) selected_cut_41032

theorem selected_cut_41033 : selected 9 ⟨1120174, by decide⟩
    (prefixPartial 12 333875) = some ⟨12, 2, 0, 1120174, 333875, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_333875_1120174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333875 ⟨1120174, by decide⟩ :=
  accepted_of_selected 12 333875 ⟨1120174, by decide⟩ ⟨12, 2, 0, 1120174, 333875, 2689, 65536⟩
    (by decide) selected_cut_41033

theorem unmarked_context_11_83468_1120175 : frontier 10 ⟨1120175, by decide⟩
    (prefixCache 11 83468) (prefixPartial 11 83468) = false := by
  decide +kernel

theorem node_context_11_83468_1120175 : EJMOriginalGlobalDAGData.nodes 10 ⟨1120175, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1120073, by decide⟩,⟨1120122, by decide⟩,⟨1120174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83468_1120175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83468 ⟨1120175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83468
    ⟨1120175, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1120073, by decide⟩,⟨1120122, by decide⟩,⟨1120174, by decide⟩]) unmarked_context_11_83468_1120175 node_context_11_83468_1120175
  intro a
  fin_cases a
  · exact context_12_333872_1108174
  · exact context_12_333873_1120073
  · exact context_12_333874_1120122
  · exact context_12_333875_1120174

theorem selected_cut_41034 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333876) = some ⟨12, 1, 0, 1108174, 333876, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333876_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333876 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333876 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333876, 1, 65536⟩
    (by decide) selected_cut_41034

theorem selected_cut_41035 : selected 9 ⟨1120227, by decide⟩
    (prefixPartial 12 333877) = some ⟨12, 2, 0, 1120227, 333877, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_333877_1120227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333877 ⟨1120227, by decide⟩ :=
  accepted_of_selected 12 333877 ⟨1120227, by decide⟩ ⟨12, 2, 0, 1120227, 333877, 3105, 65536⟩
    (by decide) selected_cut_41035

theorem selected_cut_41036 : selected 9 ⟨1120278, by decide⟩
    (prefixPartial 12 333878) = some ⟨12, 2, 0, 1120278, 333878, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_333878_1120278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333878 ⟨1120278, by decide⟩ :=
  accepted_of_selected 12 333878 ⟨1120278, by decide⟩ ⟨12, 2, 0, 1120278, 333878, 2801, 65536⟩
    (by decide) selected_cut_41036

theorem selected_cut_41037 : selected 9 ⟨1120330, by decide⟩
    (prefixPartial 12 333879) = some ⟨12, 2, 0, 1120330, 333879, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_333879_1120330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333879 ⟨1120330, by decide⟩ :=
  accepted_of_selected 12 333879 ⟨1120330, by decide⟩ ⟨12, 2, 0, 1120330, 333879, 2825, 65536⟩
    (by decide) selected_cut_41037

theorem unmarked_context_11_83469_1120331 : frontier 10 ⟨1120331, by decide⟩
    (prefixCache 11 83469) (prefixPartial 11 83469) = false := by
  decide +kernel

theorem node_context_11_83469_1120331 : EJMOriginalGlobalDAGData.nodes 10 ⟨1120331, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1120227, by decide⟩,⟨1120278, by decide⟩,⟨1120330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83469_1120331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83469 ⟨1120331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83469
    ⟨1120331, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1120227, by decide⟩,⟨1120278, by decide⟩,⟨1120330, by decide⟩]) unmarked_context_11_83469_1120331 node_context_11_83469_1120331
  intro a
  fin_cases a
  · exact context_12_333876_1108174
  · exact context_12_333877_1120227
  · exact context_12_333878_1120278
  · exact context_12_333879_1120330

theorem selected_cut_41038 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333880) = some ⟨12, 1, 0, 1108174, 333880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333880_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333880 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333880 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333880, 1, 65536⟩
    (by decide) selected_cut_41038

theorem selected_cut_41039 : selected 9 ⟨1120375, by decide⟩
    (prefixPartial 12 333881) = some ⟨12, 2, 0, 1120375, 333881, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_333881_1120375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333881 ⟨1120375, by decide⟩ :=
  accepted_of_selected 12 333881 ⟨1120375, by decide⟩ ⟨12, 2, 0, 1120375, 333881, 2533, 65536⟩
    (by decide) selected_cut_41039

theorem selected_cut_41040 : selected 9 ⟨1120418, by decide⟩
    (prefixPartial 12 333882) = some ⟨12, 2, 0, 1120418, 333882, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_333882_1120418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333882 ⟨1120418, by decide⟩ :=
  accepted_of_selected 12 333882 ⟨1120418, by decide⟩ ⟨12, 2, 0, 1120418, 333882, 2769, 65536⟩
    (by decide) selected_cut_41040

theorem selected_cut_41041 : selected 9 ⟨1120477, by decide⟩
    (prefixPartial 12 333883) = some ⟨12, 2, 0, 1120477, 333883, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_333883_1120477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333883 ⟨1120477, by decide⟩ :=
  accepted_of_selected 12 333883 ⟨1120477, by decide⟩ ⟨12, 2, 0, 1120477, 333883, 3065, 65536⟩
    (by decide) selected_cut_41041

theorem unmarked_context_11_83470_1120478 : frontier 10 ⟨1120478, by decide⟩
    (prefixCache 11 83470) (prefixPartial 11 83470) = false := by
  decide +kernel

theorem node_context_11_83470_1120478 : EJMOriginalGlobalDAGData.nodes 10 ⟨1120478, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1120375, by decide⟩,⟨1120418, by decide⟩,⟨1120477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83470_1120478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83470 ⟨1120478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83470
    ⟨1120478, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1120375, by decide⟩,⟨1120418, by decide⟩,⟨1120477, by decide⟩]) unmarked_context_11_83470_1120478 node_context_11_83470_1120478
  intro a
  fin_cases a
  · exact context_12_333880_1108174
  · exact context_12_333881_1120375
  · exact context_12_333882_1120418
  · exact context_12_333883_1120477

theorem selected_cut_41042 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333884) = some ⟨12, 1, 0, 1108174, 333884, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333884_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333884 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333884 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333884, 1, 65536⟩
    (by decide) selected_cut_41042

theorem selected_cut_41043 : selected 9 ⟨1120518, by decide⟩
    (prefixPartial 12 333885) = some ⟨12, 2, 0, 1120518, 333885, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_333885_1120518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333885 ⟨1120518, by decide⟩ :=
  accepted_of_selected 12 333885 ⟨1120518, by decide⟩ ⟨12, 2, 0, 1120518, 333885, 2509, 65536⟩
    (by decide) selected_cut_41043

theorem selected_cut_41044 : selected 9 ⟨1120581, by decide⟩
    (prefixPartial 12 333886) = some ⟨12, 2, 0, 1120581, 333886, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_333886_1120581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333886 ⟨1120581, by decide⟩ :=
  accepted_of_selected 12 333886 ⟨1120581, by decide⟩ ⟨12, 2, 0, 1120581, 333886, 3029, 65536⟩
    (by decide) selected_cut_41044

theorem selected_cut_41045 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 333887) = some ⟨12, 1, 0, 1120582, 333887, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333887_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333887 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 333887 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 333887, 1, 65536⟩
    (by decide) selected_cut_41045

theorem unmarked_context_11_83471_1120583 : frontier 10 ⟨1120583, by decide⟩
    (prefixCache 11 83471) (prefixPartial 11 83471) = false := by
  decide +kernel

theorem node_context_11_83471_1120583 : EJMOriginalGlobalDAGData.nodes 10 ⟨1120583, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1120518, by decide⟩,⟨1120581, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83471_1120583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83471 ⟨1120583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83471
    ⟨1120583, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1120518, by decide⟩,⟨1120581, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_83471_1120583 node_context_11_83471_1120583
  intro a
  fin_cases a
  · exact context_12_333884_1108174
  · exact context_12_333885_1120518
  · exact context_12_333886_1120581
  · exact context_12_333887_1120582

theorem unmarked_context_10_20867_1120584 : frontier 11 ⟨1120584, by decide⟩
    (prefixCache 10 20867) (prefixPartial 10 20867) = false := by
  decide +kernel

theorem node_context_10_20867_1120584 : EJMOriginalGlobalDAGData.nodes 11 ⟨1120584, by decide⟩ =
    .split (coordinate 10) (![⟨1120175, by decide⟩,⟨1120331, by decide⟩,⟨1120478, by decide⟩,⟨1120583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20867_1120584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20867 ⟨1120584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20867
    ⟨1120584, by decide⟩ (by decide) (![⟨1120175, by decide⟩,⟨1120331, by decide⟩,⟨1120478, by decide⟩,⟨1120583, by decide⟩]) unmarked_context_10_20867_1120584 node_context_10_20867_1120584
  intro a
  fin_cases a
  · exact context_11_83468_1120175
  · exact context_11_83469_1120331
  · exact context_11_83470_1120478
  · exact context_11_83471_1120583

theorem unmarked_context_9_5216_1120585 : frontier 12 ⟨1120585, by decide⟩
    (prefixCache 9 5216) (prefixPartial 9 5216) = false := by
  decide +kernel

theorem node_context_9_5216_1120585 : EJMOriginalGlobalDAGData.nodes 12 ⟨1120585, by decide⟩ =
    .split (coordinate 9) (![⟨1118791, by decide⟩,⟨1119465, by decide⟩,⟨1120015, by decide⟩,⟨1120584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5216_1120585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5216 ⟨1120585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5216
    ⟨1120585, by decide⟩ (by decide) (![⟨1118791, by decide⟩,⟨1119465, by decide⟩,⟨1120015, by decide⟩,⟨1120584, by decide⟩]) unmarked_context_9_5216_1120585 node_context_9_5216_1120585
  intro a
  fin_cases a
  · exact context_10_20864_1118791
  · exact context_10_20865_1119465
  · exact context_10_20866_1120015
  · exact context_10_20867_1120584

theorem selected_cut_41046 : selected 10 ⟨1120655, by decide⟩
    (prefixPartial 11 83472) = some ⟨11, 2, 0, 1120655, 83472, 4053, 262144⟩ := by
  decide +kernel

theorem context_11_83472_1120655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83472 ⟨1120655, by decide⟩ :=
  accepted_of_selected 11 83472 ⟨1120655, by decide⟩ ⟨11, 2, 0, 1120655, 83472, 4053, 262144⟩
    (by decide) selected_cut_41046

theorem selected_cut_41047 : selected 9 ⟨1120689, by decide⟩
    (prefixPartial 12 333892) = some ⟨12, 2, 0, 1120689, 333892, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_333892_1120689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333892 ⟨1120689, by decide⟩ :=
  accepted_of_selected 12 333892 ⟨1120689, by decide⟩ ⟨12, 2, 0, 1120689, 333892, 1841, 65536⟩
    (by decide) selected_cut_41047

theorem selected_cut_41048 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 333893) = some ⟨12, 1, 0, 170504, 333893, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333893_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333893 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 333893 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 333893, 1, 65536⟩
    (by decide) selected_cut_41048

theorem selected_cut_41049 : selected 9 ⟨1120724, by decide⟩
    (prefixPartial 12 333894) = some ⟨12, 2, 0, 1120724, 333894, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_333894_1120724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333894 ⟨1120724, by decide⟩ :=
  accepted_of_selected 12 333894 ⟨1120724, by decide⟩ ⟨12, 2, 0, 1120724, 333894, 2157, 65536⟩
    (by decide) selected_cut_41049

theorem selected_cut_41050 : selected 9 ⟨1120758, by decide⟩
    (prefixPartial 12 333895) = some ⟨12, 2, 0, 1120758, 333895, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_333895_1120758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333895 ⟨1120758, by decide⟩ :=
  accepted_of_selected 12 333895 ⟨1120758, by decide⟩ ⟨12, 2, 0, 1120758, 333895, 2249, 65536⟩
    (by decide) selected_cut_41050

theorem unmarked_context_11_83473_1120759 : frontier 10 ⟨1120759, by decide⟩
    (prefixCache 11 83473) (prefixPartial 11 83473) = false := by
  decide +kernel

theorem node_context_11_83473_1120759 : EJMOriginalGlobalDAGData.nodes 10 ⟨1120759, by decide⟩ =
    .split (coordinate 11) (![⟨1120689, by decide⟩,⟨170504, by decide⟩,⟨1120724, by decide⟩,⟨1120758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83473_1120759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83473 ⟨1120759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83473
    ⟨1120759, by decide⟩ (by decide) (![⟨1120689, by decide⟩,⟨170504, by decide⟩,⟨1120724, by decide⟩,⟨1120758, by decide⟩]) unmarked_context_11_83473_1120759 node_context_11_83473_1120759
  intro a
  fin_cases a
  · exact context_12_333892_1120689
  · exact context_12_333893_170504
  · exact context_12_333894_1120724
  · exact context_12_333895_1120758

theorem selected_cut_41051 : selected 9 ⟨1120783, by decide⟩
    (prefixPartial 12 333896) = some ⟨12, 2, 0, 1120783, 333896, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_333896_1120783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333896 ⟨1120783, by decide⟩ :=
  accepted_of_selected 12 333896 ⟨1120783, by decide⟩ ⟨12, 2, 0, 1120783, 333896, 1673, 65536⟩
    (by decide) selected_cut_41051

theorem selected_cut_41052 : selected 9 ⟨1120817, by decide⟩
    (prefixPartial 12 333897) = some ⟨12, 2, 0, 1120817, 333897, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_333897_1120817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333897 ⟨1120817, by decide⟩ :=
  accepted_of_selected 12 333897 ⟨1120817, by decide⟩ ⟨12, 2, 0, 1120817, 333897, 1809, 65536⟩
    (by decide) selected_cut_41052

theorem selected_cut_41053 : selected 9 ⟨1120843, by decide⟩
    (prefixPartial 12 333898) = some ⟨12, 2, 0, 1120843, 333898, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_333898_1120843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333898 ⟨1120843, by decide⟩ :=
  accepted_of_selected 12 333898 ⟨1120843, by decide⟩ ⟨12, 2, 0, 1120843, 333898, 1913, 65536⟩
    (by decide) selected_cut_41053

theorem selected_cut_41054 : selected 9 ⟨1120875, by decide⟩
    (prefixPartial 12 333899) = some ⟨12, 2, 0, 1120875, 333899, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_333899_1120875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333899 ⟨1120875, by decide⟩ :=
  accepted_of_selected 12 333899 ⟨1120875, by decide⟩ ⟨12, 2, 0, 1120875, 333899, 2069, 65536⟩
    (by decide) selected_cut_41054

theorem unmarked_context_11_83474_1120876 : frontier 10 ⟨1120876, by decide⟩
    (prefixCache 11 83474) (prefixPartial 11 83474) = false := by
  decide +kernel

theorem node_context_11_83474_1120876 : EJMOriginalGlobalDAGData.nodes 10 ⟨1120876, by decide⟩ =
    .split (coordinate 11) (![⟨1120783, by decide⟩,⟨1120817, by decide⟩,⟨1120843, by decide⟩,⟨1120875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83474_1120876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83474 ⟨1120876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83474
    ⟨1120876, by decide⟩ (by decide) (![⟨1120783, by decide⟩,⟨1120817, by decide⟩,⟨1120843, by decide⟩,⟨1120875, by decide⟩]) unmarked_context_11_83474_1120876 node_context_11_83474_1120876
  intro a
  fin_cases a
  · exact context_12_333896_1120783
  · exact context_12_333897_1120817
  · exact context_12_333898_1120843
  · exact context_12_333899_1120875

theorem selected_cut_41055 : selected 9 ⟨1120906, by decide⟩
    (prefixPartial 12 333900) = some ⟨12, 2, 0, 1120906, 333900, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_333900_1120906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333900 ⟨1120906, by decide⟩ :=
  accepted_of_selected 12 333900 ⟨1120906, by decide⟩ ⟨12, 2, 0, 1120906, 333900, 1733, 65536⟩
    (by decide) selected_cut_41055

theorem selected_cut_41056 : selected 9 ⟨1120931, by decide⟩
    (prefixPartial 12 333901) = some ⟨12, 2, 0, 1120931, 333901, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_333901_1120931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333901 ⟨1120931, by decide⟩ :=
  accepted_of_selected 12 333901 ⟨1120931, by decide⟩ ⟨12, 2, 0, 1120931, 333901, 1913, 65536⟩
    (by decide) selected_cut_41056

theorem selected_cut_41057 : selected 9 ⟨1120973, by decide⟩
    (prefixPartial 12 333902) = some ⟨12, 2, 0, 1120973, 333902, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_333902_1120973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333902 ⟨1120973, by decide⟩ :=
  accepted_of_selected 12 333902 ⟨1120973, by decide⟩ ⟨12, 2, 0, 1120973, 333902, 2189, 65536⟩
    (by decide) selected_cut_41057

theorem selected_cut_41058 : selected 9 ⟨1121001, by decide⟩
    (prefixPartial 12 333903) = some ⟨12, 2, 0, 1121001, 333903, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_333903_1121001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333903 ⟨1121001, by decide⟩ :=
  accepted_of_selected 12 333903 ⟨1121001, by decide⟩ ⟨12, 2, 0, 1121001, 333903, 1913, 65536⟩
    (by decide) selected_cut_41058

theorem unmarked_context_11_83475_1121002 : frontier 10 ⟨1121002, by decide⟩
    (prefixCache 11 83475) (prefixPartial 11 83475) = false := by
  decide +kernel

theorem node_context_11_83475_1121002 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121002, by decide⟩ =
    .split (coordinate 11) (![⟨1120906, by decide⟩,⟨1120931, by decide⟩,⟨1120973, by decide⟩,⟨1121001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83475_1121002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83475 ⟨1121002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83475
    ⟨1121002, by decide⟩ (by decide) (![⟨1120906, by decide⟩,⟨1120931, by decide⟩,⟨1120973, by decide⟩,⟨1121001, by decide⟩]) unmarked_context_11_83475_1121002 node_context_11_83475_1121002
  intro a
  fin_cases a
  · exact context_12_333900_1120906
  · exact context_12_333901_1120931
  · exact context_12_333902_1120973
  · exact context_12_333903_1121001

theorem unmarked_context_10_20868_1121003 : frontier 11 ⟨1121003, by decide⟩
    (prefixCache 10 20868) (prefixPartial 10 20868) = false := by
  decide +kernel

theorem node_context_10_20868_1121003 : EJMOriginalGlobalDAGData.nodes 11 ⟨1121003, by decide⟩ =
    .split (coordinate 10) (![⟨1120655, by decide⟩,⟨1120759, by decide⟩,⟨1120876, by decide⟩,⟨1121002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20868_1121003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20868 ⟨1121003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20868
    ⟨1121003, by decide⟩ (by decide) (![⟨1120655, by decide⟩,⟨1120759, by decide⟩,⟨1120876, by decide⟩,⟨1121002, by decide⟩]) unmarked_context_10_20868_1121003 node_context_10_20868_1121003
  intro a
  fin_cases a
  · exact context_11_83472_1120655
  · exact context_11_83473_1120759
  · exact context_11_83474_1120876
  · exact context_11_83475_1121002

theorem selected_cut_41059 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 20869) = some ⟨10, 1, 0, 893098, 20869, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20869_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20869 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 20869 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 20869, 1, 1048576⟩
    (by decide) selected_cut_41059

theorem selected_cut_41060 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 333920) = some ⟨12, 1, 0, 985390, 333920, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333920_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333920 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 333920 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 333920, 1, 65536⟩
    (by decide) selected_cut_41060

theorem selected_cut_41061 : selected 9 ⟨1121033, by decide⟩
    (prefixPartial 12 333921) = some ⟨12, 2, 0, 1121033, 333921, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_333921_1121033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333921 ⟨1121033, by decide⟩ :=
  accepted_of_selected 12 333921 ⟨1121033, by decide⟩ ⟨12, 2, 0, 1121033, 333921, 1893, 65536⟩
    (by decide) selected_cut_41061

theorem selected_cut_41062 : selected 9 ⟨1121069, by decide⟩
    (prefixPartial 12 333922) = some ⟨12, 2, 0, 1121069, 333922, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_333922_1121069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333922 ⟨1121069, by decide⟩ :=
  accepted_of_selected 12 333922 ⟨1121069, by decide⟩ ⟨12, 2, 0, 1121069, 333922, 2085, 65536⟩
    (by decide) selected_cut_41062

theorem selected_cut_41063 : selected 9 ⟨1121102, by decide⟩
    (prefixPartial 12 333923) = some ⟨12, 2, 0, 1121102, 333923, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_333923_1121102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333923 ⟨1121102, by decide⟩ :=
  accepted_of_selected 12 333923 ⟨1121102, by decide⟩ ⟨12, 2, 0, 1121102, 333923, 1821, 65536⟩
    (by decide) selected_cut_41063

theorem unmarked_context_11_83480_1121103 : frontier 10 ⟨1121103, by decide⟩
    (prefixCache 11 83480) (prefixPartial 11 83480) = false := by
  decide +kernel

theorem node_context_11_83480_1121103 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121103, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1121033, by decide⟩,⟨1121069, by decide⟩,⟨1121102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83480_1121103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83480 ⟨1121103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83480
    ⟨1121103, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1121033, by decide⟩,⟨1121069, by decide⟩,⟨1121102, by decide⟩]) unmarked_context_11_83480_1121103 node_context_11_83480_1121103
  intro a
  fin_cases a
  · exact context_12_333920_985390
  · exact context_12_333921_1121033
  · exact context_12_333922_1121069
  · exact context_12_333923_1121102

theorem selected_cut_41064 : selected 9 ⟨1121136, by decide⟩
    (prefixPartial 12 333924) = some ⟨12, 2, 0, 1121136, 333924, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_333924_1121136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333924 ⟨1121136, by decide⟩ :=
  accepted_of_selected 12 333924 ⟨1121136, by decide⟩ ⟨12, 2, 0, 1121136, 333924, 1701, 65536⟩
    (by decide) selected_cut_41064

theorem selected_cut_41065 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 333925) = some ⟨12, 1, 0, 642794, 333925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333925_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333925 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 333925 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 333925, 1, 65536⟩
    (by decide) selected_cut_41065

theorem selected_cut_41066 : selected 9 ⟨1121172, by decide⟩
    (prefixPartial 12 333926) = some ⟨12, 2, 0, 1121172, 333926, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_333926_1121172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333926 ⟨1121172, by decide⟩ :=
  accepted_of_selected 12 333926 ⟨1121172, by decide⟩ ⟨12, 2, 0, 1121172, 333926, 1953, 65536⟩
    (by decide) selected_cut_41066

theorem selected_cut_41067 : selected 9 ⟨1121211, by decide⟩
    (prefixPartial 12 333927) = some ⟨12, 2, 0, 1121211, 333927, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_333927_1121211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333927 ⟨1121211, by decide⟩ :=
  accepted_of_selected 12 333927 ⟨1121211, by decide⟩ ⟨12, 2, 0, 1121211, 333927, 1885, 65536⟩
    (by decide) selected_cut_41067

theorem unmarked_context_11_83481_1121212 : frontier 10 ⟨1121212, by decide⟩
    (prefixCache 11 83481) (prefixPartial 11 83481) = false := by
  decide +kernel

theorem node_context_11_83481_1121212 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121212, by decide⟩ =
    .split (coordinate 11) (![⟨1121136, by decide⟩,⟨642794, by decide⟩,⟨1121172, by decide⟩,⟨1121211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83481_1121212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83481 ⟨1121212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83481
    ⟨1121212, by decide⟩ (by decide) (![⟨1121136, by decide⟩,⟨642794, by decide⟩,⟨1121172, by decide⟩,⟨1121211, by decide⟩]) unmarked_context_11_83481_1121212 node_context_11_83481_1121212
  intro a
  fin_cases a
  · exact context_12_333924_1121136
  · exact context_12_333925_642794
  · exact context_12_333926_1121172
  · exact context_12_333927_1121211

theorem selected_cut_41068 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 83482) = some ⟨11, 1, 0, 900587, 83482, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83482_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83482 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 83482 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 83482, 1, 262144⟩
    (by decide) selected_cut_41068

theorem selected_cut_41069 : selected 9 ⟨1121247, by decide⟩
    (prefixPartial 12 333932) = some ⟨12, 2, 0, 1121247, 333932, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_333932_1121247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333932 ⟨1121247, by decide⟩ :=
  accepted_of_selected 12 333932 ⟨1121247, by decide⟩ ⟨12, 2, 0, 1121247, 333932, 1653, 65536⟩
    (by decide) selected_cut_41069

theorem selected_cut_41070 : selected 9 ⟨1121272, by decide⟩
    (prefixPartial 12 333933) = some ⟨12, 2, 0, 1121272, 333933, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_333933_1121272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333933 ⟨1121272, by decide⟩ :=
  accepted_of_selected 12 333933 ⟨1121272, by decide⟩ ⟨12, 2, 0, 1121272, 333933, 1713, 65536⟩
    (by decide) selected_cut_41070

theorem selected_cut_41071 : selected 9 ⟨1121310, by decide⟩
    (prefixPartial 12 333934) = some ⟨12, 2, 0, 1121310, 333934, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_333934_1121310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333934 ⟨1121310, by decide⟩ :=
  accepted_of_selected 12 333934 ⟨1121310, by decide⟩ ⟨12, 2, 0, 1121310, 333934, 2197, 65536⟩
    (by decide) selected_cut_41071

theorem selected_cut_41072 : selected 9 ⟨1121337, by decide⟩
    (prefixPartial 12 333935) = some ⟨12, 2, 0, 1121337, 333935, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_333935_1121337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333935 ⟨1121337, by decide⟩ :=
  accepted_of_selected 12 333935 ⟨1121337, by decide⟩ ⟨12, 2, 0, 1121337, 333935, 1661, 65536⟩
    (by decide) selected_cut_41072

theorem unmarked_context_11_83483_1121338 : frontier 10 ⟨1121338, by decide⟩
    (prefixCache 11 83483) (prefixPartial 11 83483) = false := by
  decide +kernel

theorem node_context_11_83483_1121338 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121338, by decide⟩ =
    .split (coordinate 11) (![⟨1121247, by decide⟩,⟨1121272, by decide⟩,⟨1121310, by decide⟩,⟨1121337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83483_1121338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83483 ⟨1121338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83483
    ⟨1121338, by decide⟩ (by decide) (![⟨1121247, by decide⟩,⟨1121272, by decide⟩,⟨1121310, by decide⟩,⟨1121337, by decide⟩]) unmarked_context_11_83483_1121338 node_context_11_83483_1121338
  intro a
  fin_cases a
  · exact context_12_333932_1121247
  · exact context_12_333933_1121272
  · exact context_12_333934_1121310
  · exact context_12_333935_1121337

theorem unmarked_context_10_20870_1121339 : frontier 11 ⟨1121339, by decide⟩
    (prefixCache 10 20870) (prefixPartial 10 20870) = false := by
  decide +kernel

theorem node_context_10_20870_1121339 : EJMOriginalGlobalDAGData.nodes 11 ⟨1121339, by decide⟩ =
    .split (coordinate 10) (![⟨1121103, by decide⟩,⟨1121212, by decide⟩,⟨900587, by decide⟩,⟨1121338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20870_1121339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20870 ⟨1121339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20870
    ⟨1121339, by decide⟩ (by decide) (![⟨1121103, by decide⟩,⟨1121212, by decide⟩,⟨900587, by decide⟩,⟨1121338, by decide⟩]) unmarked_context_10_20870_1121339 node_context_10_20870_1121339
  intro a
  fin_cases a
  · exact context_11_83480_1121103
  · exact context_11_83481_1121212
  · exact context_11_83482_900587
  · exact context_11_83483_1121338

theorem selected_cut_41073 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 333936) = some ⟨12, 1, 0, 985390, 333936, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333936_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333936 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 333936 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 333936, 1, 65536⟩
    (by decide) selected_cut_41073

theorem selected_cut_41074 : selected 9 ⟨1121363, by decide⟩
    (prefixPartial 12 333937) = some ⟨12, 2, 0, 1121363, 333937, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_333937_1121363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333937 ⟨1121363, by decide⟩ :=
  accepted_of_selected 12 333937 ⟨1121363, by decide⟩ ⟨12, 2, 0, 1121363, 333937, 1753, 65536⟩
    (by decide) selected_cut_41074

theorem selected_cut_41075 : selected 9 ⟨1121395, by decide⟩
    (prefixPartial 12 333938) = some ⟨12, 2, 0, 1121395, 333938, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_333938_1121395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333938 ⟨1121395, by decide⟩ :=
  accepted_of_selected 12 333938 ⟨1121395, by decide⟩ ⟨12, 2, 0, 1121395, 333938, 1805, 65536⟩
    (by decide) selected_cut_41075

theorem selected_cut_41076 : selected 9 ⟨1121421, by decide⟩
    (prefixPartial 12 333939) = some ⟨12, 2, 0, 1121421, 333939, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_333939_1121421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333939 ⟨1121421, by decide⟩ :=
  accepted_of_selected 12 333939 ⟨1121421, by decide⟩ ⟨12, 2, 0, 1121421, 333939, 1741, 65536⟩
    (by decide) selected_cut_41076

theorem unmarked_context_11_83484_1121422 : frontier 10 ⟨1121422, by decide⟩
    (prefixCache 11 83484) (prefixPartial 11 83484) = false := by
  decide +kernel

theorem node_context_11_83484_1121422 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121422, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1121363, by decide⟩,⟨1121395, by decide⟩,⟨1121421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83484_1121422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83484 ⟨1121422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83484
    ⟨1121422, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1121363, by decide⟩,⟨1121395, by decide⟩,⟨1121421, by decide⟩]) unmarked_context_11_83484_1121422 node_context_11_83484_1121422
  intro a
  fin_cases a
  · exact context_12_333936_985390
  · exact context_12_333937_1121363
  · exact context_12_333938_1121395
  · exact context_12_333939_1121421

theorem selected_cut_41077 : selected 9 ⟨1121449, by decide⟩
    (prefixPartial 12 333940) = some ⟨12, 2, 0, 1121449, 333940, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_333940_1121449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333940 ⟨1121449, by decide⟩ :=
  accepted_of_selected 12 333940 ⟨1121449, by decide⟩ ⟨12, 2, 0, 1121449, 333940, 1669, 65536⟩
    (by decide) selected_cut_41077

theorem selected_cut_41078 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 333941) = some ⟨12, 1, 0, 642794, 333941, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333941_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333941 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 333941 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 333941, 1, 65536⟩
    (by decide) selected_cut_41078

theorem selected_cut_41079 : selected 9 ⟨1121476, by decide⟩
    (prefixPartial 12 333942) = some ⟨12, 2, 0, 1121476, 333942, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_333942_1121476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333942 ⟨1121476, by decide⟩ :=
  accepted_of_selected 12 333942 ⟨1121476, by decide⟩ ⟨12, 2, 0, 1121476, 333942, 1821, 65536⟩
    (by decide) selected_cut_41079

theorem selected_cut_41080 : selected 9 ⟨1121511, by decide⟩
    (prefixPartial 12 333943) = some ⟨12, 2, 0, 1121511, 333943, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_333943_1121511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333943 ⟨1121511, by decide⟩ :=
  accepted_of_selected 12 333943 ⟨1121511, by decide⟩ ⟨12, 2, 0, 1121511, 333943, 1829, 65536⟩
    (by decide) selected_cut_41080

theorem unmarked_context_11_83485_1121512 : frontier 10 ⟨1121512, by decide⟩
    (prefixCache 11 83485) (prefixPartial 11 83485) = false := by
  decide +kernel

theorem node_context_11_83485_1121512 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121512, by decide⟩ =
    .split (coordinate 11) (![⟨1121449, by decide⟩,⟨642794, by decide⟩,⟨1121476, by decide⟩,⟨1121511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83485_1121512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83485 ⟨1121512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83485
    ⟨1121512, by decide⟩ (by decide) (![⟨1121449, by decide⟩,⟨642794, by decide⟩,⟨1121476, by decide⟩,⟨1121511, by decide⟩]) unmarked_context_11_83485_1121512 node_context_11_83485_1121512
  intro a
  fin_cases a
  · exact context_12_333940_1121449
  · exact context_12_333941_642794
  · exact context_12_333942_1121476
  · exact context_12_333943_1121511

theorem selected_cut_41081 : selected 9 ⟨1121535, by decide⟩
    (prefixPartial 12 333944) = some ⟨12, 2, 0, 1121535, 333944, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_333944_1121535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333944 ⟨1121535, by decide⟩ :=
  accepted_of_selected 12 333944 ⟨1121535, by decide⟩ ⟨12, 2, 0, 1121535, 333944, 1493, 65536⟩
    (by decide) selected_cut_41081

theorem selected_cut_41082 : selected 9 ⟨1121559, by decide⟩
    (prefixPartial 12 333945) = some ⟨12, 2, 0, 1121559, 333945, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_333945_1121559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333945 ⟨1121559, by decide⟩ :=
  accepted_of_selected 12 333945 ⟨1121559, by decide⟩ ⟨12, 2, 0, 1121559, 333945, 1569, 65536⟩
    (by decide) selected_cut_41082

theorem selected_cut_41083 : selected 9 ⟨1121583, by decide⟩
    (prefixPartial 12 333946) = some ⟨12, 2, 0, 1121583, 333946, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_333946_1121583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333946 ⟨1121583, by decide⟩ :=
  accepted_of_selected 12 333946 ⟨1121583, by decide⟩ ⟨12, 2, 0, 1121583, 333946, 1589, 65536⟩
    (by decide) selected_cut_41083

theorem selected_cut_41084 : selected 9 ⟨1121618, by decide⟩
    (prefixPartial 12 333947) = some ⟨12, 2, 0, 1121618, 333947, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_333947_1121618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333947 ⟨1121618, by decide⟩ :=
  accepted_of_selected 12 333947 ⟨1121618, by decide⟩ ⟨12, 2, 0, 1121618, 333947, 1885, 65536⟩
    (by decide) selected_cut_41084

theorem unmarked_context_11_83486_1121619 : frontier 10 ⟨1121619, by decide⟩
    (prefixCache 11 83486) (prefixPartial 11 83486) = false := by
  decide +kernel

theorem node_context_11_83486_1121619 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121619, by decide⟩ =
    .split (coordinate 11) (![⟨1121535, by decide⟩,⟨1121559, by decide⟩,⟨1121583, by decide⟩,⟨1121618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83486_1121619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83486 ⟨1121619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83486
    ⟨1121619, by decide⟩ (by decide) (![⟨1121535, by decide⟩,⟨1121559, by decide⟩,⟨1121583, by decide⟩,⟨1121618, by decide⟩]) unmarked_context_11_83486_1121619 node_context_11_83486_1121619
  intro a
  fin_cases a
  · exact context_12_333944_1121535
  · exact context_12_333945_1121559
  · exact context_12_333946_1121583
  · exact context_12_333947_1121618

theorem selected_cut_41085 : selected 9 ⟨1121642, by decide⟩
    (prefixPartial 12 333948) = some ⟨12, 2, 0, 1121642, 333948, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_333948_1121642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333948 ⟨1121642, by decide⟩ :=
  accepted_of_selected 12 333948 ⟨1121642, by decide⟩ ⟨12, 2, 0, 1121642, 333948, 1425, 65536⟩
    (by decide) selected_cut_41085

theorem selected_cut_41086 : selected 9 ⟨1121656, by decide⟩
    (prefixPartial 12 333949) = some ⟨12, 2, 0, 1121656, 333949, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_333949_1121656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333949 ⟨1121656, by decide⟩ :=
  accepted_of_selected 12 333949 ⟨1121656, by decide⟩ ⟨12, 2, 0, 1121656, 333949, 1453, 65536⟩
    (by decide) selected_cut_41086

theorem selected_cut_41087 : selected 9 ⟨1121686, by decide⟩
    (prefixPartial 12 333950) = some ⟨12, 2, 0, 1121686, 333950, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_333950_1121686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333950 ⟨1121686, by decide⟩ :=
  accepted_of_selected 12 333950 ⟨1121686, by decide⟩ ⟨12, 2, 0, 1121686, 333950, 1729, 65536⟩
    (by decide) selected_cut_41087

theorem selected_cut_41088 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 333951) = some ⟨12, 1, 0, 1120582, 333951, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333951_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333951 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 333951 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 333951, 1, 65536⟩
    (by decide) selected_cut_41088

theorem unmarked_context_11_83487_1121687 : frontier 10 ⟨1121687, by decide⟩
    (prefixCache 11 83487) (prefixPartial 11 83487) = false := by
  decide +kernel

theorem node_context_11_83487_1121687 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121687, by decide⟩ =
    .split (coordinate 11) (![⟨1121642, by decide⟩,⟨1121656, by decide⟩,⟨1121686, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83487_1121687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83487 ⟨1121687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83487
    ⟨1121687, by decide⟩ (by decide) (![⟨1121642, by decide⟩,⟨1121656, by decide⟩,⟨1121686, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_83487_1121687 node_context_11_83487_1121687
  intro a
  fin_cases a
  · exact context_12_333948_1121642
  · exact context_12_333949_1121656
  · exact context_12_333950_1121686
  · exact context_12_333951_1120582

theorem unmarked_context_10_20871_1121688 : frontier 11 ⟨1121688, by decide⟩
    (prefixCache 10 20871) (prefixPartial 10 20871) = false := by
  decide +kernel

theorem node_context_10_20871_1121688 : EJMOriginalGlobalDAGData.nodes 11 ⟨1121688, by decide⟩ =
    .split (coordinate 10) (![⟨1121422, by decide⟩,⟨1121512, by decide⟩,⟨1121619, by decide⟩,⟨1121687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20871_1121688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20871 ⟨1121688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20871
    ⟨1121688, by decide⟩ (by decide) (![⟨1121422, by decide⟩,⟨1121512, by decide⟩,⟨1121619, by decide⟩,⟨1121687, by decide⟩]) unmarked_context_10_20871_1121688 node_context_10_20871_1121688
  intro a
  fin_cases a
  · exact context_11_83484_1121422
  · exact context_11_83485_1121512
  · exact context_11_83486_1121619
  · exact context_11_83487_1121687

theorem unmarked_context_9_5217_1121689 : frontier 12 ⟨1121689, by decide⟩
    (prefixCache 9 5217) (prefixPartial 9 5217) = false := by
  decide +kernel

theorem node_context_9_5217_1121689 : EJMOriginalGlobalDAGData.nodes 12 ⟨1121689, by decide⟩ =
    .split (coordinate 9) (![⟨1121003, by decide⟩,⟨893098, by decide⟩,⟨1121339, by decide⟩,⟨1121688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5217_1121689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5217 ⟨1121689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5217
    ⟨1121689, by decide⟩ (by decide) (![⟨1121003, by decide⟩,⟨893098, by decide⟩,⟨1121339, by decide⟩,⟨1121688, by decide⟩]) unmarked_context_9_5217_1121689 node_context_9_5217_1121689
  intro a
  fin_cases a
  · exact context_10_20868_1121003
  · exact context_10_20869_893098
  · exact context_10_20870_1121339
  · exact context_10_20871_1121688

theorem selected_cut_41089 : selected 10 ⟨1121776, by decide⟩
    (prefixPartial 11 83488) = some ⟨11, 2, 0, 1121776, 83488, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_83488_1121776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83488 ⟨1121776, by decide⟩ :=
  accepted_of_selected 11 83488 ⟨1121776, by decide⟩ ⟨11, 2, 0, 1121776, 83488, 3537, 262144⟩
    (by decide) selected_cut_41089

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
