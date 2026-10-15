/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover393
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_37827 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 300405) = some ⟨12, 1, 0, 891951, 300405, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300405_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300405 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 300405 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 300405, 1, 65536⟩
    (by decide) selected_cut_37827

theorem selected_cut_37828 : selected 9 ⟨1014388, by decide⟩
    (prefixPartial 12 300406) = some ⟨12, 2, 0, 1014388, 300406, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_300406_1014388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300406 ⟨1014388, by decide⟩ :=
  accepted_of_selected 12 300406 ⟨1014388, by decide⟩ ⟨12, 2, 0, 1014388, 300406, 1457, 65536⟩
    (by decide) selected_cut_37828

theorem selected_cut_37829 : selected 9 ⟨1014405, by decide⟩
    (prefixPartial 12 300407) = some ⟨12, 2, 0, 1014405, 300407, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_300407_1014405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300407 ⟨1014405, by decide⟩ :=
  accepted_of_selected 12 300407 ⟨1014405, by decide⟩ ⟨12, 2, 0, 1014405, 300407, 1397, 65536⟩
    (by decide) selected_cut_37829

theorem unmarked_context_11_75101_1014406 : frontier 10 ⟨1014406, by decide⟩
    (prefixCache 11 75101) (prefixPartial 11 75101) = false := by
  decide +kernel

theorem node_context_11_75101_1014406 : EJMOriginalGlobalDAGData.nodes 10 ⟨1014406, by decide⟩ =
    .split (coordinate 11) (![⟨1014369, by decide⟩,⟨891951, by decide⟩,⟨1014388, by decide⟩,⟨1014405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75101_1014406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75101 ⟨1014406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75101
    ⟨1014406, by decide⟩ (by decide) (![⟨1014369, by decide⟩,⟨891951, by decide⟩,⟨1014388, by decide⟩,⟨1014405, by decide⟩]) unmarked_context_11_75101_1014406 node_context_11_75101_1014406
  intro a
  fin_cases a
  · exact context_12_300404_1014369
  · exact context_12_300405_891951
  · exact context_12_300406_1014388
  · exact context_12_300407_1014405

theorem selected_cut_37830 : selected 9 ⟨1014429, by decide⟩
    (prefixPartial 12 300408) = some ⟨12, 2, 0, 1014429, 300408, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_300408_1014429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300408 ⟨1014429, by decide⟩ :=
  accepted_of_selected 12 300408 ⟨1014429, by decide⟩ ⟨12, 2, 0, 1014429, 300408, 1613, 65536⟩
    (by decide) selected_cut_37830

theorem selected_cut_37831 : selected 9 ⟨1014449, by decide⟩
    (prefixPartial 12 300409) = some ⟨12, 2, 0, 1014449, 300409, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_300409_1014449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300409 ⟨1014449, by decide⟩ :=
  accepted_of_selected 12 300409 ⟨1014449, by decide⟩ ⟨12, 2, 0, 1014449, 300409, 1333, 65536⟩
    (by decide) selected_cut_37831

theorem selected_cut_37832 : selected 9 ⟨1014475, by decide⟩
    (prefixPartial 12 300410) = some ⟨12, 2, 0, 1014475, 300410, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_300410_1014475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300410 ⟨1014475, by decide⟩ :=
  accepted_of_selected 12 300410 ⟨1014475, by decide⟩ ⟨12, 2, 0, 1014475, 300410, 1553, 65536⟩
    (by decide) selected_cut_37832

theorem selected_cut_37833 : selected 9 ⟨1014500, by decide⟩
    (prefixPartial 12 300411) = some ⟨12, 2, 0, 1014500, 300411, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_300411_1014500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300411 ⟨1014500, by decide⟩ :=
  accepted_of_selected 12 300411 ⟨1014500, by decide⟩ ⟨12, 2, 0, 1014500, 300411, 1429, 65536⟩
    (by decide) selected_cut_37833

theorem unmarked_context_11_75102_1014501 : frontier 10 ⟨1014501, by decide⟩
    (prefixCache 11 75102) (prefixPartial 11 75102) = false := by
  decide +kernel

theorem node_context_11_75102_1014501 : EJMOriginalGlobalDAGData.nodes 10 ⟨1014501, by decide⟩ =
    .split (coordinate 11) (![⟨1014429, by decide⟩,⟨1014449, by decide⟩,⟨1014475, by decide⟩,⟨1014500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75102_1014501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75102 ⟨1014501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75102
    ⟨1014501, by decide⟩ (by decide) (![⟨1014429, by decide⟩,⟨1014449, by decide⟩,⟨1014475, by decide⟩,⟨1014500, by decide⟩]) unmarked_context_11_75102_1014501 node_context_11_75102_1014501
  intro a
  fin_cases a
  · exact context_12_300408_1014429
  · exact context_12_300409_1014449
  · exact context_12_300410_1014475
  · exact context_12_300411_1014500

theorem selected_cut_37834 : selected 9 ⟨1014528, by decide⟩
    (prefixPartial 12 300412) = some ⟨12, 2, 0, 1014528, 300412, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_300412_1014528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300412 ⟨1014528, by decide⟩ :=
  accepted_of_selected 12 300412 ⟨1014528, by decide⟩ ⟨12, 2, 0, 1014528, 300412, 1589, 65536⟩
    (by decide) selected_cut_37834

theorem selected_cut_37835 : selected 9 ⟨1014553, by decide⟩
    (prefixPartial 12 300413) = some ⟨12, 2, 0, 1014553, 300413, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_300413_1014553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300413 ⟨1014553, by decide⟩ :=
  accepted_of_selected 12 300413 ⟨1014553, by decide⟩ ⟨12, 2, 0, 1014553, 300413, 1389, 65536⟩
    (by decide) selected_cut_37835

theorem selected_cut_37836 : selected 9 ⟨1014580, by decide⟩
    (prefixPartial 12 300414) = some ⟨12, 2, 0, 1014580, 300414, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_300414_1014580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300414 ⟨1014580, by decide⟩ :=
  accepted_of_selected 12 300414 ⟨1014580, by decide⟩ ⟨12, 2, 0, 1014580, 300414, 1489, 65536⟩
    (by decide) selected_cut_37836

theorem selected_cut_37837 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 300415) = some ⟨12, 1, 0, 762108, 300415, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300415_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300415 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 300415 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 300415, 1, 65536⟩
    (by decide) selected_cut_37837

theorem unmarked_context_11_75103_1014581 : frontier 10 ⟨1014581, by decide⟩
    (prefixCache 11 75103) (prefixPartial 11 75103) = false := by
  decide +kernel

theorem node_context_11_75103_1014581 : EJMOriginalGlobalDAGData.nodes 10 ⟨1014581, by decide⟩ =
    .split (coordinate 11) (![⟨1014528, by decide⟩,⟨1014553, by decide⟩,⟨1014580, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75103_1014581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75103 ⟨1014581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75103
    ⟨1014581, by decide⟩ (by decide) (![⟨1014528, by decide⟩,⟨1014553, by decide⟩,⟨1014580, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_75103_1014581 node_context_11_75103_1014581
  intro a
  fin_cases a
  · exact context_12_300412_1014528
  · exact context_12_300413_1014553
  · exact context_12_300414_1014580
  · exact context_12_300415_762108

theorem unmarked_context_10_18775_1014582 : frontier 11 ⟨1014582, by decide⟩
    (prefixCache 10 18775) (prefixPartial 10 18775) = false := by
  decide +kernel

theorem node_context_10_18775_1014582 : EJMOriginalGlobalDAGData.nodes 11 ⟨1014582, by decide⟩ =
    .split (coordinate 10) (![⟨1014335, by decide⟩,⟨1014406, by decide⟩,⟨1014501, by decide⟩,⟨1014581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18775_1014582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18775 ⟨1014582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18775
    ⟨1014582, by decide⟩ (by decide) (![⟨1014335, by decide⟩,⟨1014406, by decide⟩,⟨1014501, by decide⟩,⟨1014581, by decide⟩]) unmarked_context_10_18775_1014582 node_context_10_18775_1014582
  intro a
  fin_cases a
  · exact context_11_75100_1014335
  · exact context_11_75101_1014406
  · exact context_11_75102_1014501
  · exact context_11_75103_1014581

theorem unmarked_context_9_4693_1014583 : frontier 12 ⟨1014583, by decide⟩
    (prefixCache 9 4693) (prefixPartial 9 4693) = false := by
  decide +kernel

theorem node_context_9_4693_1014583 : EJMOriginalGlobalDAGData.nodes 12 ⟨1014583, by decide⟩ =
    .split (coordinate 9) (![⟨1013789, by decide⟩,⟨893098, by decide⟩,⟨1014244, by decide⟩,⟨1014582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4693_1014583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4693 ⟨1014583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4693
    ⟨1014583, by decide⟩ (by decide) (![⟨1013789, by decide⟩,⟨893098, by decide⟩,⟨1014244, by decide⟩,⟨1014582, by decide⟩]) unmarked_context_9_4693_1014583 node_context_9_4693_1014583
  intro a
  fin_cases a
  · exact context_10_18772_1013789
  · exact context_10_18773_893098
  · exact context_10_18774_1014244
  · exact context_10_18775_1014582

theorem selected_cut_37838 : selected 10 ⟨1014625, by decide⟩
    (prefixPartial 11 75104) = some ⟨11, 2, 0, 1014625, 75104, 2597, 262144⟩ := by
  decide +kernel

theorem context_11_75104_1014625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75104 ⟨1014625, by decide⟩ :=
  accepted_of_selected 11 75104 ⟨1014625, by decide⟩ ⟨11, 2, 0, 1014625, 75104, 2597, 262144⟩
    (by decide) selected_cut_37838

theorem selected_cut_37839 : selected 10 ⟨1014684, by decide⟩
    (prefixPartial 11 75105) = some ⟨11, 2, 0, 1014684, 75105, 3081, 262144⟩ := by
  decide +kernel

theorem context_11_75105_1014684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75105 ⟨1014684, by decide⟩ :=
  accepted_of_selected 11 75105 ⟨1014684, by decide⟩ ⟨11, 2, 0, 1014684, 75105, 3081, 262144⟩
    (by decide) selected_cut_37839

theorem selected_cut_37840 : selected 10 ⟨1014751, by decide⟩
    (prefixPartial 11 75106) = some ⟨11, 2, 0, 1014751, 75106, 3993, 262144⟩ := by
  decide +kernel

theorem context_11_75106_1014751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75106 ⟨1014751, by decide⟩ :=
  accepted_of_selected 11 75106 ⟨1014751, by decide⟩ ⟨11, 2, 0, 1014751, 75106, 3993, 262144⟩
    (by decide) selected_cut_37840

theorem selected_cut_37841 : selected 10 ⟨1014829, by decide⟩
    (prefixPartial 11 75107) = some ⟨11, 2, 0, 1014829, 75107, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_75107_1014829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75107 ⟨1014829, by decide⟩ :=
  accepted_of_selected 11 75107 ⟨1014829, by decide⟩ ⟨11, 2, 0, 1014829, 75107, 3785, 262144⟩
    (by decide) selected_cut_37841

theorem unmarked_context_10_18776_1014830 : frontier 11 ⟨1014830, by decide⟩
    (prefixCache 10 18776) (prefixPartial 10 18776) = false := by
  decide +kernel

theorem node_context_10_18776_1014830 : EJMOriginalGlobalDAGData.nodes 11 ⟨1014830, by decide⟩ =
    .split (coordinate 10) (![⟨1014625, by decide⟩,⟨1014684, by decide⟩,⟨1014751, by decide⟩,⟨1014829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18776_1014830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18776 ⟨1014830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18776
    ⟨1014830, by decide⟩ (by decide) (![⟨1014625, by decide⟩,⟨1014684, by decide⟩,⟨1014751, by decide⟩,⟨1014829, by decide⟩]) unmarked_context_10_18776_1014830 node_context_10_18776_1014830
  intro a
  fin_cases a
  · exact context_11_75104_1014625
  · exact context_11_75105_1014684
  · exact context_11_75106_1014751
  · exact context_11_75107_1014829

theorem selected_cut_37842 : selected 10 ⟨1014864, by decide⟩
    (prefixPartial 11 75108) = some ⟨11, 2, 0, 1014864, 75108, 2577, 262144⟩ := by
  decide +kernel

theorem context_11_75108_1014864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75108 ⟨1014864, by decide⟩ :=
  accepted_of_selected 11 75108 ⟨1014864, by decide⟩ ⟨11, 2, 0, 1014864, 75108, 2577, 262144⟩
    (by decide) selected_cut_37842

theorem selected_cut_37843 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75109) = some ⟨11, 1, 0, 892405, 75109, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75109_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75109 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75109 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75109, 1, 262144⟩
    (by decide) selected_cut_37843

theorem selected_cut_37844 : selected 10 ⟨1014889, by decide⟩
    (prefixPartial 11 75110) = some ⟨11, 2, 0, 1014889, 75110, 2497, 262144⟩ := by
  decide +kernel

theorem context_11_75110_1014889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75110 ⟨1014889, by decide⟩ :=
  accepted_of_selected 11 75110 ⟨1014889, by decide⟩ ⟨11, 2, 0, 1014889, 75110, 2497, 262144⟩
    (by decide) selected_cut_37844

theorem selected_cut_37845 : selected 10 ⟨1014928, by decide⟩
    (prefixPartial 11 75111) = some ⟨11, 2, 0, 1014928, 75111, 2469, 262144⟩ := by
  decide +kernel

theorem context_11_75111_1014928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75111 ⟨1014928, by decide⟩ :=
  accepted_of_selected 11 75111 ⟨1014928, by decide⟩ ⟨11, 2, 0, 1014928, 75111, 2469, 262144⟩
    (by decide) selected_cut_37845

theorem unmarked_context_10_18777_1014929 : frontier 11 ⟨1014929, by decide⟩
    (prefixCache 10 18777) (prefixPartial 10 18777) = false := by
  decide +kernel

theorem node_context_10_18777_1014929 : EJMOriginalGlobalDAGData.nodes 11 ⟨1014929, by decide⟩ =
    .split (coordinate 10) (![⟨1014864, by decide⟩,⟨892405, by decide⟩,⟨1014889, by decide⟩,⟨1014928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18777_1014929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18777 ⟨1014929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18777
    ⟨1014929, by decide⟩ (by decide) (![⟨1014864, by decide⟩,⟨892405, by decide⟩,⟨1014889, by decide⟩,⟨1014928, by decide⟩]) unmarked_context_10_18777_1014929 node_context_10_18777_1014929
  intro a
  fin_cases a
  · exact context_11_75108_1014864
  · exact context_11_75109_892405
  · exact context_11_75110_1014889
  · exact context_11_75111_1014928

theorem selected_cut_37846 : selected 10 ⟨1014965, by decide⟩
    (prefixPartial 11 75112) = some ⟨11, 2, 0, 1014965, 75112, 2517, 262144⟩ := by
  decide +kernel

theorem context_11_75112_1014965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75112 ⟨1014965, by decide⟩ :=
  accepted_of_selected 11 75112 ⟨1014965, by decide⟩ ⟨11, 2, 0, 1014965, 75112, 2517, 262144⟩
    (by decide) selected_cut_37846

theorem selected_cut_37847 : selected 10 ⟨1014988, by decide⟩
    (prefixPartial 11 75113) = some ⟨11, 2, 0, 1014988, 75113, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_75113_1014988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75113 ⟨1014988, by decide⟩ :=
  accepted_of_selected 11 75113 ⟨1014988, by decide⟩ ⟨11, 2, 0, 1014988, 75113, 1597, 262144⟩
    (by decide) selected_cut_37847

theorem selected_cut_37848 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75114) = some ⟨11, 1, 0, 906566, 75114, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75114_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75114 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75114 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75114, 1, 262144⟩
    (by decide) selected_cut_37848

theorem selected_cut_37849 : selected 10 ⟨1015022, by decide⟩
    (prefixPartial 11 75115) = some ⟨11, 2, 0, 1015022, 75115, 2289, 262144⟩ := by
  decide +kernel

theorem context_11_75115_1015022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75115 ⟨1015022, by decide⟩ :=
  accepted_of_selected 11 75115 ⟨1015022, by decide⟩ ⟨11, 2, 0, 1015022, 75115, 2289, 262144⟩
    (by decide) selected_cut_37849

theorem unmarked_context_10_18778_1015023 : frontier 11 ⟨1015023, by decide⟩
    (prefixCache 10 18778) (prefixPartial 10 18778) = false := by
  decide +kernel

theorem node_context_10_18778_1015023 : EJMOriginalGlobalDAGData.nodes 11 ⟨1015023, by decide⟩ =
    .split (coordinate 10) (![⟨1014965, by decide⟩,⟨1014988, by decide⟩,⟨906566, by decide⟩,⟨1015022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18778_1015023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18778 ⟨1015023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18778
    ⟨1015023, by decide⟩ (by decide) (![⟨1014965, by decide⟩,⟨1014988, by decide⟩,⟨906566, by decide⟩,⟨1015022, by decide⟩]) unmarked_context_10_18778_1015023 node_context_10_18778_1015023
  intro a
  fin_cases a
  · exact context_11_75112_1014965
  · exact context_11_75113_1014988
  · exact context_11_75114_906566
  · exact context_11_75115_1015022

theorem selected_cut_37850 : selected 10 ⟨1015052, by decide⟩
    (prefixPartial 11 75116) = some ⟨11, 2, 0, 1015052, 75116, 2045, 262144⟩ := by
  decide +kernel

theorem context_11_75116_1015052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75116 ⟨1015052, by decide⟩ :=
  accepted_of_selected 11 75116 ⟨1015052, by decide⟩ ⟨11, 2, 0, 1015052, 75116, 2045, 262144⟩
    (by decide) selected_cut_37850

theorem selected_cut_37851 : selected 10 ⟨1015072, by decide⟩
    (prefixPartial 11 75117) = some ⟨11, 2, 0, 1015072, 75117, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_75117_1015072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75117 ⟨1015072, by decide⟩ :=
  accepted_of_selected 11 75117 ⟨1015072, by decide⟩ ⟨11, 2, 0, 1015072, 75117, 1429, 262144⟩
    (by decide) selected_cut_37851

theorem selected_cut_37852 : selected 10 ⟨1015094, by decide⟩
    (prefixPartial 11 75118) = some ⟨11, 2, 0, 1015094, 75118, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_75118_1015094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75118 ⟨1015094, by decide⟩ :=
  accepted_of_selected 11 75118 ⟨1015094, by decide⟩ ⟨11, 2, 0, 1015094, 75118, 1753, 262144⟩
    (by decide) selected_cut_37852

theorem selected_cut_37853 : selected 10 ⟨1015112, by decide⟩
    (prefixPartial 11 75119) = some ⟨11, 2, 0, 1015112, 75119, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_75119_1015112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75119 ⟨1015112, by decide⟩ :=
  accepted_of_selected 11 75119 ⟨1015112, by decide⟩ ⟨11, 2, 0, 1015112, 75119, 1149, 262144⟩
    (by decide) selected_cut_37853

theorem unmarked_context_10_18779_1015113 : frontier 11 ⟨1015113, by decide⟩
    (prefixCache 10 18779) (prefixPartial 10 18779) = false := by
  decide +kernel

theorem node_context_10_18779_1015113 : EJMOriginalGlobalDAGData.nodes 11 ⟨1015113, by decide⟩ =
    .split (coordinate 10) (![⟨1015052, by decide⟩,⟨1015072, by decide⟩,⟨1015094, by decide⟩,⟨1015112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18779_1015113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18779 ⟨1015113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18779
    ⟨1015113, by decide⟩ (by decide) (![⟨1015052, by decide⟩,⟨1015072, by decide⟩,⟨1015094, by decide⟩,⟨1015112, by decide⟩]) unmarked_context_10_18779_1015113 node_context_10_18779_1015113
  intro a
  fin_cases a
  · exact context_11_75116_1015052
  · exact context_11_75117_1015072
  · exact context_11_75118_1015094
  · exact context_11_75119_1015112

theorem unmarked_context_9_4694_1015114 : frontier 12 ⟨1015114, by decide⟩
    (prefixCache 9 4694) (prefixPartial 9 4694) = false := by
  decide +kernel

theorem node_context_9_4694_1015114 : EJMOriginalGlobalDAGData.nodes 12 ⟨1015114, by decide⟩ =
    .split (coordinate 9) (![⟨1014830, by decide⟩,⟨1014929, by decide⟩,⟨1015023, by decide⟩,⟨1015113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4694_1015114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4694 ⟨1015114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4694
    ⟨1015114, by decide⟩ (by decide) (![⟨1014830, by decide⟩,⟨1014929, by decide⟩,⟨1015023, by decide⟩,⟨1015113, by decide⟩]) unmarked_context_9_4694_1015114 node_context_9_4694_1015114
  intro a
  fin_cases a
  · exact context_10_18776_1014830
  · exact context_10_18777_1014929
  · exact context_10_18778_1015023
  · exact context_10_18779_1015113

theorem selected_cut_37854 : selected 10 ⟨1015142, by decide⟩
    (prefixPartial 11 75120) = some ⟨11, 2, 0, 1015142, 75120, 1813, 262144⟩ := by
  decide +kernel

theorem context_11_75120_1015142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75120 ⟨1015142, by decide⟩ :=
  accepted_of_selected 11 75120 ⟨1015142, by decide⟩ ⟨11, 2, 0, 1015142, 75120, 1813, 262144⟩
    (by decide) selected_cut_37854

theorem selected_cut_37855 : selected 10 ⟨1015179, by decide⟩
    (prefixPartial 11 75121) = some ⟨11, 2, 0, 1015179, 75121, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_75121_1015179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75121 ⟨1015179, by decide⟩ :=
  accepted_of_selected 11 75121 ⟨1015179, by decide⟩ ⟨11, 2, 0, 1015179, 75121, 1949, 262144⟩
    (by decide) selected_cut_37855

theorem selected_cut_37856 : selected 10 ⟨1015223, by decide⟩
    (prefixPartial 11 75122) = some ⟨11, 2, 0, 1015223, 75122, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_75122_1015223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75122 ⟨1015223, by decide⟩ :=
  accepted_of_selected 11 75122 ⟨1015223, by decide⟩ ⟨11, 2, 0, 1015223, 75122, 2233, 262144⟩
    (by decide) selected_cut_37856

theorem selected_cut_37857 : selected 10 ⟨1015271, by decide⟩
    (prefixPartial 11 75123) = some ⟨11, 2, 0, 1015271, 75123, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_75123_1015271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75123 ⟨1015271, by decide⟩ :=
  accepted_of_selected 11 75123 ⟨1015271, by decide⟩ ⟨11, 2, 0, 1015271, 75123, 2233, 262144⟩
    (by decide) selected_cut_37857

theorem unmarked_context_10_18780_1015272 : frontier 11 ⟨1015272, by decide⟩
    (prefixCache 10 18780) (prefixPartial 10 18780) = false := by
  decide +kernel

theorem node_context_10_18780_1015272 : EJMOriginalGlobalDAGData.nodes 11 ⟨1015272, by decide⟩ =
    .split (coordinate 10) (![⟨1015142, by decide⟩,⟨1015179, by decide⟩,⟨1015223, by decide⟩,⟨1015271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18780_1015272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18780 ⟨1015272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18780
    ⟨1015272, by decide⟩ (by decide) (![⟨1015142, by decide⟩,⟨1015179, by decide⟩,⟨1015223, by decide⟩,⟨1015271, by decide⟩]) unmarked_context_10_18780_1015272 node_context_10_18780_1015272
  intro a
  fin_cases a
  · exact context_11_75120_1015142
  · exact context_11_75121_1015179
  · exact context_11_75122_1015223
  · exact context_11_75123_1015271

theorem selected_cut_37858 : selected 11 ⟨1015346, by decide⟩
    (prefixPartial 10 18781) = some ⟨10, 2, 0, 1015346, 18781, 3953, 1048576⟩ := by
  decide +kernel

theorem context_10_18781_1015346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18781 ⟨1015346, by decide⟩ :=
  accepted_of_selected 10 18781 ⟨1015346, by decide⟩ ⟨10, 2, 0, 1015346, 18781, 3953, 1048576⟩
    (by decide) selected_cut_37858

theorem selected_cut_37859 : selected 11 ⟨1015403, by decide⟩
    (prefixPartial 10 18782) = some ⟨10, 2, 0, 1015403, 18782, 2941, 1048576⟩ := by
  decide +kernel

theorem context_10_18782_1015403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18782 ⟨1015403, by decide⟩ :=
  accepted_of_selected 10 18782 ⟨1015403, by decide⟩ ⟨10, 2, 0, 1015403, 18782, 2941, 1048576⟩
    (by decide) selected_cut_37859

theorem selected_cut_37860 : selected 11 ⟨1015424, by decide⟩
    (prefixPartial 10 18783) = some ⟨10, 2, 0, 1015424, 18783, 665, 1048576⟩ := by
  decide +kernel

theorem context_10_18783_1015424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18783 ⟨1015424, by decide⟩ :=
  accepted_of_selected 10 18783 ⟨1015424, by decide⟩ ⟨10, 2, 0, 1015424, 18783, 665, 1048576⟩
    (by decide) selected_cut_37860

theorem unmarked_context_9_4695_1015425 : frontier 12 ⟨1015425, by decide⟩
    (prefixCache 9 4695) (prefixPartial 9 4695) = false := by
  decide +kernel

theorem node_context_9_4695_1015425 : EJMOriginalGlobalDAGData.nodes 12 ⟨1015425, by decide⟩ =
    .split (coordinate 9) (![⟨1015272, by decide⟩,⟨1015346, by decide⟩,⟨1015403, by decide⟩,⟨1015424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4695_1015425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4695 ⟨1015425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4695
    ⟨1015425, by decide⟩ (by decide) (![⟨1015272, by decide⟩,⟨1015346, by decide⟩,⟨1015403, by decide⟩,⟨1015424, by decide⟩]) unmarked_context_9_4695_1015425 node_context_9_4695_1015425
  intro a
  fin_cases a
  · exact context_10_18780_1015272
  · exact context_10_18781_1015346
  · exact context_10_18782_1015403
  · exact context_10_18783_1015424

theorem unmarked_context_8_1173_1015426 : frontier 13 ⟨1015426, by decide⟩
    (prefixCache 8 1173) (prefixPartial 8 1173) = false := by
  decide +kernel

theorem node_context_8_1173_1015426 : EJMOriginalGlobalDAGData.nodes 13 ⟨1015426, by decide⟩ =
    .split (coordinate 8) (![⟨1013240, by decide⟩,⟨1014583, by decide⟩,⟨1015114, by decide⟩,⟨1015425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1173_1015426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1173 ⟨1015426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1173
    ⟨1015426, by decide⟩ (by decide) (![⟨1013240, by decide⟩,⟨1014583, by decide⟩,⟨1015114, by decide⟩,⟨1015425, by decide⟩]) unmarked_context_8_1173_1015426 node_context_8_1173_1015426
  intro a
  fin_cases a
  · exact context_9_4692_1013240
  · exact context_9_4693_1014583
  · exact context_9_4694_1015114
  · exact context_9_4695_1015425

theorem selected_cut_37861 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 75136) = some ⟨11, 1, 0, 167448, 75136, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75136_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75136 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 75136 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 75136, 1, 262144⟩
    (by decide) selected_cut_37861

theorem selected_cut_37862 : selected 8 ⟨1015447, by decide⟩
    (prefixPartial 13 1202192) = some ⟨13, 2, 0, 1015447, 1202192, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_1202192_1015447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202192 ⟨1015447, by decide⟩ :=
  accepted_of_selected 13 1202192 ⟨1015447, by decide⟩ ⟨13, 2, 0, 1015447, 1202192, 1305, 16384⟩
    (by decide) selected_cut_37862

theorem selected_cut_37863 : selected 8 ⟨1015475, by decide⟩
    (prefixPartial 13 1202193) = some ⟨13, 2, 0, 1015475, 1202193, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_1202193_1015475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202193 ⟨1015475, by decide⟩ :=
  accepted_of_selected 13 1202193 ⟨1015475, by decide⟩ ⟨13, 2, 0, 1015475, 1202193, 1357, 16384⟩
    (by decide) selected_cut_37863

theorem selected_cut_37864 : selected 8 ⟨1015507, by decide⟩
    (prefixPartial 13 1202194) = some ⟨13, 2, 0, 1015507, 1202194, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_1202194_1015507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202194 ⟨1015507, by decide⟩ :=
  accepted_of_selected 13 1202194 ⟨1015507, by decide⟩ ⟨13, 2, 0, 1015507, 1202194, 1229, 16384⟩
    (by decide) selected_cut_37864

theorem selected_cut_37865 : selected 8 ⟨1015527, by decide⟩
    (prefixPartial 13 1202195) = some ⟨13, 2, 0, 1015527, 1202195, 717, 16384⟩ := by
  decide +kernel

theorem context_13_1202195_1015527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202195 ⟨1015527, by decide⟩ :=
  accepted_of_selected 13 1202195 ⟨1015527, by decide⟩ ⟨13, 2, 0, 1015527, 1202195, 717, 16384⟩
    (by decide) selected_cut_37865

theorem unmarked_context_12_300548_1015528 : frontier 9 ⟨1015528, by decide⟩
    (prefixCache 12 300548) (prefixPartial 12 300548) = false := by
  decide +kernel

theorem node_context_12_300548_1015528 : EJMOriginalGlobalDAGData.nodes 9 ⟨1015528, by decide⟩ =
    .split (coordinate 12) (![⟨1015447, by decide⟩,⟨1015475, by decide⟩,⟨1015507, by decide⟩,⟨1015527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300548_1015528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300548 ⟨1015528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300548
    ⟨1015528, by decide⟩ (by decide) (![⟨1015447, by decide⟩,⟨1015475, by decide⟩,⟨1015507, by decide⟩,⟨1015527, by decide⟩]) unmarked_context_12_300548_1015528 node_context_12_300548_1015528
  intro a
  fin_cases a
  · exact context_13_1202192_1015447
  · exact context_13_1202193_1015475
  · exact context_13_1202194_1015507
  · exact context_13_1202195_1015527

theorem selected_cut_37866 : selected 9 ⟨1015611, by decide⟩
    (prefixPartial 12 300549) = some ⟨12, 2, 0, 1015611, 300549, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_300549_1015611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300549 ⟨1015611, by decide⟩ :=
  accepted_of_selected 12 300549 ⟨1015611, by decide⟩ ⟨12, 2, 0, 1015611, 300549, 4005, 65536⟩
    (by decide) selected_cut_37866

theorem selected_cut_37867 : selected 9 ⟨1015684, by decide⟩
    (prefixPartial 12 300550) = some ⟨12, 2, 0, 1015684, 300550, 3865, 65536⟩ := by
  decide +kernel

theorem context_12_300550_1015684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300550 ⟨1015684, by decide⟩ :=
  accepted_of_selected 12 300550 ⟨1015684, by decide⟩ ⟨12, 2, 0, 1015684, 300550, 3865, 65536⟩
    (by decide) selected_cut_37867

theorem selected_cut_37868 : selected 8 ⟨1015709, by decide⟩
    (prefixPartial 13 1202204) = some ⟨13, 2, 0, 1015709, 1202204, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_1202204_1015709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202204 ⟨1015709, by decide⟩ :=
  accepted_of_selected 13 1202204 ⟨1015709, by decide⟩ ⟨13, 2, 0, 1015709, 1202204, 1369, 16384⟩
    (by decide) selected_cut_37868

theorem selected_cut_37869 : selected 8 ⟨1015728, by decide⟩
    (prefixPartial 13 1202205) = some ⟨13, 2, 0, 1015728, 1202205, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_1202205_1015728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202205 ⟨1015728, by decide⟩ :=
  accepted_of_selected 13 1202205 ⟨1015728, by decide⟩ ⟨13, 2, 0, 1015728, 1202205, 1153, 16384⟩
    (by decide) selected_cut_37869

theorem selected_cut_37870 : selected 8 ⟨1015754, by decide⟩
    (prefixPartial 13 1202206) = some ⟨13, 2, 0, 1015754, 1202206, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_1202206_1015754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202206 ⟨1015754, by decide⟩ :=
  accepted_of_selected 13 1202206 ⟨1015754, by decide⟩ ⟨13, 2, 0, 1015754, 1202206, 1149, 16384⟩
    (by decide) selected_cut_37870

theorem selected_cut_37871 : selected 8 ⟨1015765, by decide⟩
    (prefixPartial 13 1202207) = some ⟨13, 2, 0, 1015765, 1202207, 581, 16384⟩ := by
  decide +kernel

theorem context_13_1202207_1015765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202207 ⟨1015765, by decide⟩ :=
  accepted_of_selected 13 1202207 ⟨1015765, by decide⟩ ⟨13, 2, 0, 1015765, 1202207, 581, 16384⟩
    (by decide) selected_cut_37871

theorem unmarked_context_12_300551_1015766 : frontier 9 ⟨1015766, by decide⟩
    (prefixCache 12 300551) (prefixPartial 12 300551) = false := by
  decide +kernel

theorem node_context_12_300551_1015766 : EJMOriginalGlobalDAGData.nodes 9 ⟨1015766, by decide⟩ =
    .split (coordinate 12) (![⟨1015709, by decide⟩,⟨1015728, by decide⟩,⟨1015754, by decide⟩,⟨1015765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300551_1015766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300551 ⟨1015766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300551
    ⟨1015766, by decide⟩ (by decide) (![⟨1015709, by decide⟩,⟨1015728, by decide⟩,⟨1015754, by decide⟩,⟨1015765, by decide⟩]) unmarked_context_12_300551_1015766 node_context_12_300551_1015766
  intro a
  fin_cases a
  · exact context_13_1202204_1015709
  · exact context_13_1202205_1015728
  · exact context_13_1202206_1015754
  · exact context_13_1202207_1015765

theorem unmarked_context_11_75137_1015767 : frontier 10 ⟨1015767, by decide⟩
    (prefixCache 11 75137) (prefixPartial 11 75137) = false := by
  decide +kernel

theorem node_context_11_75137_1015767 : EJMOriginalGlobalDAGData.nodes 10 ⟨1015767, by decide⟩ =
    .split (coordinate 11) (![⟨1015528, by decide⟩,⟨1015611, by decide⟩,⟨1015684, by decide⟩,⟨1015766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75137_1015767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75137 ⟨1015767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75137
    ⟨1015767, by decide⟩ (by decide) (![⟨1015528, by decide⟩,⟨1015611, by decide⟩,⟨1015684, by decide⟩,⟨1015766, by decide⟩]) unmarked_context_11_75137_1015767 node_context_11_75137_1015767
  intro a
  fin_cases a
  · exact context_12_300548_1015528
  · exact context_12_300549_1015611
  · exact context_12_300550_1015684
  · exact context_12_300551_1015766

theorem selected_cut_37872 : selected 9 ⟨1015834, by decide⟩
    (prefixPartial 12 300552) = some ⟨12, 2, 0, 1015834, 300552, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_300552_1015834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300552 ⟨1015834, by decide⟩ :=
  accepted_of_selected 12 300552 ⟨1015834, by decide⟩ ⟨12, 2, 0, 1015834, 300552, 2605, 65536⟩
    (by decide) selected_cut_37872

theorem selected_cut_37873 : selected 8 ⟨1015858, by decide⟩
    (prefixPartial 13 1202212) = some ⟨13, 2, 0, 1015858, 1202212, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_1202212_1015858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202212 ⟨1015858, by decide⟩ :=
  accepted_of_selected 13 1202212 ⟨1015858, by decide⟩ ⟨13, 2, 0, 1015858, 1202212, 1341, 16384⟩
    (by decide) selected_cut_37873

theorem selected_cut_37874 : selected 8 ⟨1015885, by decide⟩
    (prefixPartial 13 1202213) = some ⟨13, 2, 0, 1015885, 1202213, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_1202213_1015885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202213 ⟨1015885, by decide⟩ :=
  accepted_of_selected 13 1202213 ⟨1015885, by decide⟩ ⟨13, 2, 0, 1015885, 1202213, 1501, 16384⟩
    (by decide) selected_cut_37874

theorem selected_cut_37875 : selected 8 ⟨1015907, by decide⟩
    (prefixPartial 13 1202214) = some ⟨13, 2, 0, 1015907, 1202214, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_1202214_1015907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202214 ⟨1015907, by decide⟩ :=
  accepted_of_selected 13 1202214 ⟨1015907, by decide⟩ ⟨13, 2, 0, 1015907, 1202214, 1033, 16384⟩
    (by decide) selected_cut_37875

theorem selected_cut_37876 : selected 8 ⟨1015917, by decide⟩
    (prefixPartial 13 1202215) = some ⟨13, 2, 0, 1015917, 1202215, 605, 16384⟩ := by
  decide +kernel

theorem context_13_1202215_1015917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202215 ⟨1015917, by decide⟩ :=
  accepted_of_selected 13 1202215 ⟨1015917, by decide⟩ ⟨13, 2, 0, 1015917, 1202215, 605, 16384⟩
    (by decide) selected_cut_37876

theorem unmarked_context_12_300553_1015918 : frontier 9 ⟨1015918, by decide⟩
    (prefixCache 12 300553) (prefixPartial 12 300553) = false := by
  decide +kernel

theorem node_context_12_300553_1015918 : EJMOriginalGlobalDAGData.nodes 9 ⟨1015918, by decide⟩ =
    .split (coordinate 12) (![⟨1015858, by decide⟩,⟨1015885, by decide⟩,⟨1015907, by decide⟩,⟨1015917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300553_1015918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300553 ⟨1015918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300553
    ⟨1015918, by decide⟩ (by decide) (![⟨1015858, by decide⟩,⟨1015885, by decide⟩,⟨1015907, by decide⟩,⟨1015917, by decide⟩]) unmarked_context_12_300553_1015918 node_context_12_300553_1015918
  intro a
  fin_cases a
  · exact context_13_1202212_1015858
  · exact context_13_1202213_1015885
  · exact context_13_1202214_1015907
  · exact context_13_1202215_1015917

theorem selected_cut_37877 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 300554) = some ⟨12, 1, 0, 893903, 300554, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300554_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300554 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 300554 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 300554, 1, 65536⟩
    (by decide) selected_cut_37877

theorem selected_cut_37878 : selected 8 ⟨1015939, by decide⟩
    (prefixPartial 13 1202220) = some ⟨13, 2, 0, 1015939, 1202220, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_1202220_1015939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202220 ⟨1015939, by decide⟩ :=
  accepted_of_selected 13 1202220 ⟨1015939, by decide⟩ ⟨13, 2, 0, 1015939, 1202220, 1413, 16384⟩
    (by decide) selected_cut_37878

theorem selected_cut_37879 : selected 8 ⟨1015971, by decide⟩
    (prefixPartial 13 1202221) = some ⟨13, 2, 0, 1015971, 1202221, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_1202221_1015971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202221 ⟨1015971, by decide⟩ :=
  accepted_of_selected 13 1202221 ⟨1015971, by decide⟩ ⟨13, 2, 0, 1015971, 1202221, 1601, 16384⟩
    (by decide) selected_cut_37879

theorem selected_cut_37880 : selected 8 ⟨1015997, by decide⟩
    (prefixPartial 13 1202222) = some ⟨13, 2, 0, 1015997, 1202222, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_1202222_1015997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202222 ⟨1015997, by decide⟩ :=
  accepted_of_selected 13 1202222 ⟨1015997, by decide⟩ ⟨13, 2, 0, 1015997, 1202222, 1169, 16384⟩
    (by decide) selected_cut_37880

theorem selected_cut_37881 : selected 8 ⟨1016009, by decide⟩
    (prefixPartial 13 1202223) = some ⟨13, 2, 0, 1016009, 1202223, 637, 16384⟩ := by
  decide +kernel

theorem context_13_1202223_1016009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202223 ⟨1016009, by decide⟩ :=
  accepted_of_selected 13 1202223 ⟨1016009, by decide⟩ ⟨13, 2, 0, 1016009, 1202223, 637, 16384⟩
    (by decide) selected_cut_37881

theorem unmarked_context_12_300555_1016010 : frontier 9 ⟨1016010, by decide⟩
    (prefixCache 12 300555) (prefixPartial 12 300555) = false := by
  decide +kernel

theorem node_context_12_300555_1016010 : EJMOriginalGlobalDAGData.nodes 9 ⟨1016010, by decide⟩ =
    .split (coordinate 12) (![⟨1015939, by decide⟩,⟨1015971, by decide⟩,⟨1015997, by decide⟩,⟨1016009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300555_1016010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300555 ⟨1016010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300555
    ⟨1016010, by decide⟩ (by decide) (![⟨1015939, by decide⟩,⟨1015971, by decide⟩,⟨1015997, by decide⟩,⟨1016009, by decide⟩]) unmarked_context_12_300555_1016010 node_context_12_300555_1016010
  intro a
  fin_cases a
  · exact context_13_1202220_1015939
  · exact context_13_1202221_1015971
  · exact context_13_1202222_1015997
  · exact context_13_1202223_1016009

theorem unmarked_context_11_75138_1016011 : frontier 10 ⟨1016011, by decide⟩
    (prefixCache 11 75138) (prefixPartial 11 75138) = false := by
  decide +kernel

theorem node_context_11_75138_1016011 : EJMOriginalGlobalDAGData.nodes 10 ⟨1016011, by decide⟩ =
    .split (coordinate 11) (![⟨1015834, by decide⟩,⟨1015918, by decide⟩,⟨893903, by decide⟩,⟨1016010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75138_1016011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75138 ⟨1016011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75138
    ⟨1016011, by decide⟩ (by decide) (![⟨1015834, by decide⟩,⟨1015918, by decide⟩,⟨893903, by decide⟩,⟨1016010, by decide⟩]) unmarked_context_11_75138_1016011 node_context_11_75138_1016011
  intro a
  fin_cases a
  · exact context_12_300552_1015834
  · exact context_12_300553_1015918
  · exact context_12_300554_893903
  · exact context_12_300555_1016010

theorem selected_cut_37882 : selected 8 ⟨1016034, by decide⟩
    (prefixPartial 13 1202224) = some ⟨13, 2, 0, 1016034, 1202224, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_1202224_1016034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202224 ⟨1016034, by decide⟩ :=
  accepted_of_selected 13 1202224 ⟨1016034, by decide⟩ ⟨13, 2, 0, 1016034, 1202224, 1369, 16384⟩
    (by decide) selected_cut_37882

theorem selected_cut_37883 : selected 8 ⟨1016066, by decide⟩
    (prefixPartial 13 1202225) = some ⟨13, 2, 0, 1016066, 1202225, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_1202225_1016066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202225 ⟨1016066, by decide⟩ :=
  accepted_of_selected 13 1202225 ⟨1016066, by decide⟩ ⟨13, 2, 0, 1016066, 1202225, 1609, 16384⟩
    (by decide) selected_cut_37883

theorem selected_cut_37884 : selected 8 ⟨1016085, by decide⟩
    (prefixPartial 13 1202226) = some ⟨13, 2, 0, 1016085, 1202226, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_1202226_1016085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202226 ⟨1016085, by decide⟩ :=
  accepted_of_selected 13 1202226 ⟨1016085, by decide⟩ ⟨13, 2, 0, 1016085, 1202226, 1337, 16384⟩
    (by decide) selected_cut_37884

theorem selected_cut_37885 : selected 8 ⟨1016105, by decide⟩
    (prefixPartial 13 1202227) = some ⟨13, 2, 0, 1016105, 1202227, 861, 16384⟩ := by
  decide +kernel

theorem context_13_1202227_1016105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202227 ⟨1016105, by decide⟩ :=
  accepted_of_selected 13 1202227 ⟨1016105, by decide⟩ ⟨13, 2, 0, 1016105, 1202227, 861, 16384⟩
    (by decide) selected_cut_37885

theorem unmarked_context_12_300556_1016106 : frontier 9 ⟨1016106, by decide⟩
    (prefixCache 12 300556) (prefixPartial 12 300556) = false := by
  decide +kernel

theorem node_context_12_300556_1016106 : EJMOriginalGlobalDAGData.nodes 9 ⟨1016106, by decide⟩ =
    .split (coordinate 12) (![⟨1016034, by decide⟩,⟨1016066, by decide⟩,⟨1016085, by decide⟩,⟨1016105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300556_1016106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300556 ⟨1016106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300556
    ⟨1016106, by decide⟩ (by decide) (![⟨1016034, by decide⟩,⟨1016066, by decide⟩,⟨1016085, by decide⟩,⟨1016105, by decide⟩]) unmarked_context_12_300556_1016106 node_context_12_300556_1016106
  intro a
  fin_cases a
  · exact context_13_1202224_1016034
  · exact context_13_1202225_1016066
  · exact context_13_1202226_1016085
  · exact context_13_1202227_1016105

theorem selected_cut_37886 : selected 8 ⟨1016140, by decide⟩
    (prefixPartial 13 1202228) = some ⟨13, 2, 0, 1016140, 1202228, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_1202228_1016140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202228 ⟨1016140, by decide⟩ :=
  accepted_of_selected 13 1202228 ⟨1016140, by decide⟩ ⟨13, 2, 0, 1016140, 1202228, 1525, 16384⟩
    (by decide) selected_cut_37886

theorem selected_cut_37887 : selected 8 ⟨1016169, by decide⟩
    (prefixPartial 13 1202229) = some ⟨13, 2, 0, 1016169, 1202229, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_1202229_1016169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202229 ⟨1016169, by decide⟩ :=
  accepted_of_selected 13 1202229 ⟨1016169, by decide⟩ ⟨13, 2, 0, 1016169, 1202229, 1517, 16384⟩
    (by decide) selected_cut_37887

theorem selected_cut_37888 : selected 8 ⟨1016186, by decide⟩
    (prefixPartial 13 1202230) = some ⟨13, 2, 0, 1016186, 1202230, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_1202230_1016186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202230 ⟨1016186, by decide⟩ :=
  accepted_of_selected 13 1202230 ⟨1016186, by decide⟩ ⟨13, 2, 0, 1016186, 1202230, 1073, 16384⟩
    (by decide) selected_cut_37888

theorem selected_cut_37889 : selected 8 ⟨1016198, by decide⟩
    (prefixPartial 13 1202231) = some ⟨13, 2, 0, 1016198, 1202231, 709, 16384⟩ := by
  decide +kernel

theorem context_13_1202231_1016198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202231 ⟨1016198, by decide⟩ :=
  accepted_of_selected 13 1202231 ⟨1016198, by decide⟩ ⟨13, 2, 0, 1016198, 1202231, 709, 16384⟩
    (by decide) selected_cut_37889

theorem unmarked_context_12_300557_1016199 : frontier 9 ⟨1016199, by decide⟩
    (prefixCache 12 300557) (prefixPartial 12 300557) = false := by
  decide +kernel

theorem node_context_12_300557_1016199 : EJMOriginalGlobalDAGData.nodes 9 ⟨1016199, by decide⟩ =
    .split (coordinate 12) (![⟨1016140, by decide⟩,⟨1016169, by decide⟩,⟨1016186, by decide⟩,⟨1016198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300557_1016199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300557 ⟨1016199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300557
    ⟨1016199, by decide⟩ (by decide) (![⟨1016140, by decide⟩,⟨1016169, by decide⟩,⟨1016186, by decide⟩,⟨1016198, by decide⟩]) unmarked_context_12_300557_1016199 node_context_12_300557_1016199
  intro a
  fin_cases a
  · exact context_13_1202228_1016140
  · exact context_13_1202229_1016169
  · exact context_13_1202230_1016186
  · exact context_13_1202231_1016198

theorem selected_cut_37890 : selected 8 ⟨1016221, by decide⟩
    (prefixPartial 13 1202232) = some ⟨13, 2, 0, 1016221, 1202232, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_1202232_1016221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202232 ⟨1016221, by decide⟩ :=
  accepted_of_selected 13 1202232 ⟨1016221, by decide⟩ ⟨13, 2, 0, 1016221, 1202232, 1461, 16384⟩
    (by decide) selected_cut_37890

theorem selected_cut_37891 : selected 8 ⟨1016248, by decide⟩
    (prefixPartial 13 1202233) = some ⟨13, 2, 0, 1016248, 1202233, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_1202233_1016248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202233 ⟨1016248, by decide⟩ :=
  accepted_of_selected 13 1202233 ⟨1016248, by decide⟩ ⟨13, 2, 0, 1016248, 1202233, 1581, 16384⟩
    (by decide) selected_cut_37891

theorem selected_cut_37892 : selected 8 ⟨1016268, by decide⟩
    (prefixPartial 13 1202234) = some ⟨13, 2, 0, 1016268, 1202234, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_1202234_1016268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202234 ⟨1016268, by decide⟩ :=
  accepted_of_selected 13 1202234 ⟨1016268, by decide⟩ ⟨13, 2, 0, 1016268, 1202234, 1037, 16384⟩
    (by decide) selected_cut_37892

theorem selected_cut_37893 : selected 8 ⟨1016280, by decide⟩
    (prefixPartial 13 1202235) = some ⟨13, 2, 0, 1016280, 1202235, 749, 16384⟩ := by
  decide +kernel

theorem context_13_1202235_1016280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202235 ⟨1016280, by decide⟩ :=
  accepted_of_selected 13 1202235 ⟨1016280, by decide⟩ ⟨13, 2, 0, 1016280, 1202235, 749, 16384⟩
    (by decide) selected_cut_37893

theorem unmarked_context_12_300558_1016281 : frontier 9 ⟨1016281, by decide⟩
    (prefixCache 12 300558) (prefixPartial 12 300558) = false := by
  decide +kernel

theorem node_context_12_300558_1016281 : EJMOriginalGlobalDAGData.nodes 9 ⟨1016281, by decide⟩ =
    .split (coordinate 12) (![⟨1016221, by decide⟩,⟨1016248, by decide⟩,⟨1016268, by decide⟩,⟨1016280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300558_1016281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300558 ⟨1016281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300558
    ⟨1016281, by decide⟩ (by decide) (![⟨1016221, by decide⟩,⟨1016248, by decide⟩,⟨1016268, by decide⟩,⟨1016280, by decide⟩]) unmarked_context_12_300558_1016281 node_context_12_300558_1016281
  intro a
  fin_cases a
  · exact context_13_1202232_1016221
  · exact context_13_1202233_1016248
  · exact context_13_1202234_1016268
  · exact context_13_1202235_1016280

theorem selected_cut_37894 : selected 8 ⟨1016309, by decide⟩
    (prefixPartial 13 1202236) = some ⟨13, 2, 0, 1016309, 1202236, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_1202236_1016309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202236 ⟨1016309, by decide⟩ :=
  accepted_of_selected 13 1202236 ⟨1016309, by decide⟩ ⟨13, 2, 0, 1016309, 1202236, 1477, 16384⟩
    (by decide) selected_cut_37894

theorem selected_cut_37895 : selected 8 ⟨1016345, by decide⟩
    (prefixPartial 13 1202237) = some ⟨13, 2, 0, 1016345, 1202237, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_1202237_1016345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202237 ⟨1016345, by decide⟩ :=
  accepted_of_selected 13 1202237 ⟨1016345, by decide⟩ ⟨13, 2, 0, 1016345, 1202237, 1601, 16384⟩
    (by decide) selected_cut_37895

theorem selected_cut_37896 : selected 8 ⟨1016374, by decide⟩
    (prefixPartial 13 1202238) = some ⟨13, 2, 0, 1016374, 1202238, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_1202238_1016374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202238 ⟨1016374, by decide⟩ :=
  accepted_of_selected 13 1202238 ⟨1016374, by decide⟩ ⟨13, 2, 0, 1016374, 1202238, 1081, 16384⟩
    (by decide) selected_cut_37896

theorem selected_cut_37897 : selected 8 ⟨1016387, by decide⟩
    (prefixPartial 13 1202239) = some ⟨13, 2, 0, 1016387, 1202239, 733, 16384⟩ := by
  decide +kernel

theorem context_13_1202239_1016387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202239 ⟨1016387, by decide⟩ :=
  accepted_of_selected 13 1202239 ⟨1016387, by decide⟩ ⟨13, 2, 0, 1016387, 1202239, 733, 16384⟩
    (by decide) selected_cut_37897

theorem unmarked_context_12_300559_1016388 : frontier 9 ⟨1016388, by decide⟩
    (prefixCache 12 300559) (prefixPartial 12 300559) = false := by
  decide +kernel

theorem node_context_12_300559_1016388 : EJMOriginalGlobalDAGData.nodes 9 ⟨1016388, by decide⟩ =
    .split (coordinate 12) (![⟨1016309, by decide⟩,⟨1016345, by decide⟩,⟨1016374, by decide⟩,⟨1016387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300559_1016388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300559 ⟨1016388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300559
    ⟨1016388, by decide⟩ (by decide) (![⟨1016309, by decide⟩,⟨1016345, by decide⟩,⟨1016374, by decide⟩,⟨1016387, by decide⟩]) unmarked_context_12_300559_1016388 node_context_12_300559_1016388
  intro a
  fin_cases a
  · exact context_13_1202236_1016309
  · exact context_13_1202237_1016345
  · exact context_13_1202238_1016374
  · exact context_13_1202239_1016387

theorem unmarked_context_11_75139_1016389 : frontier 10 ⟨1016389, by decide⟩
    (prefixCache 11 75139) (prefixPartial 11 75139) = false := by
  decide +kernel

theorem node_context_11_75139_1016389 : EJMOriginalGlobalDAGData.nodes 10 ⟨1016389, by decide⟩ =
    .split (coordinate 11) (![⟨1016106, by decide⟩,⟨1016199, by decide⟩,⟨1016281, by decide⟩,⟨1016388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75139_1016389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75139 ⟨1016389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75139
    ⟨1016389, by decide⟩ (by decide) (![⟨1016106, by decide⟩,⟨1016199, by decide⟩,⟨1016281, by decide⟩,⟨1016388, by decide⟩]) unmarked_context_11_75139_1016389 node_context_11_75139_1016389
  intro a
  fin_cases a
  · exact context_12_300556_1016106
  · exact context_12_300557_1016199
  · exact context_12_300558_1016281
  · exact context_12_300559_1016388

theorem unmarked_context_10_18784_1016390 : frontier 11 ⟨1016390, by decide⟩
    (prefixCache 10 18784) (prefixPartial 10 18784) = false := by
  decide +kernel

theorem node_context_10_18784_1016390 : EJMOriginalGlobalDAGData.nodes 11 ⟨1016390, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1015767, by decide⟩,⟨1016011, by decide⟩,⟨1016389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18784_1016390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18784 ⟨1016390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18784
    ⟨1016390, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1015767, by decide⟩,⟨1016011, by decide⟩,⟨1016389, by decide⟩]) unmarked_context_10_18784_1016390 node_context_10_18784_1016390
  intro a
  fin_cases a
  · exact context_11_75136_167448
  · exact context_11_75137_1015767
  · exact context_11_75138_1016011
  · exact context_11_75139_1016389

theorem selected_cut_37898 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 300560) = some ⟨12, 1, 0, 994572, 300560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300560_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300560 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 300560 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 300560, 1, 65536⟩
    (by decide) selected_cut_37898

theorem selected_cut_37899 : selected 9 ⟨1016442, by decide⟩
    (prefixPartial 12 300561) = some ⟨12, 2, 0, 1016442, 300561, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_300561_1016442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300561 ⟨1016442, by decide⟩ :=
  accepted_of_selected 12 300561 ⟨1016442, by decide⟩ ⟨12, 2, 0, 1016442, 300561, 3249, 65536⟩
    (by decide) selected_cut_37899

theorem selected_cut_37900 : selected 9 ⟨1016492, by decide⟩
    (prefixPartial 12 300562) = some ⟨12, 2, 0, 1016492, 300562, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_300562_1016492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300562 ⟨1016492, by decide⟩ :=
  accepted_of_selected 12 300562 ⟨1016492, by decide⟩ ⟨12, 2, 0, 1016492, 300562, 3221, 65536⟩
    (by decide) selected_cut_37900

theorem selected_cut_37901 : selected 9 ⟨1016548, by decide⟩
    (prefixPartial 12 300563) = some ⟨12, 2, 0, 1016548, 300563, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_300563_1016548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300563 ⟨1016548, by decide⟩ :=
  accepted_of_selected 12 300563 ⟨1016548, by decide⟩ ⟨12, 2, 0, 1016548, 300563, 3785, 65536⟩
    (by decide) selected_cut_37901

theorem unmarked_context_11_75140_1016549 : frontier 10 ⟨1016549, by decide⟩
    (prefixCache 11 75140) (prefixPartial 11 75140) = false := by
  decide +kernel

theorem node_context_11_75140_1016549 : EJMOriginalGlobalDAGData.nodes 10 ⟨1016549, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1016442, by decide⟩,⟨1016492, by decide⟩,⟨1016548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75140_1016549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75140 ⟨1016549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75140
    ⟨1016549, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1016442, by decide⟩,⟨1016492, by decide⟩,⟨1016548, by decide⟩]) unmarked_context_11_75140_1016549 node_context_11_75140_1016549
  intro a
  fin_cases a
  · exact context_12_300560_994572
  · exact context_12_300561_1016442
  · exact context_12_300562_1016492
  · exact context_12_300563_1016548

theorem selected_cut_37902 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75141) = some ⟨11, 1, 0, 892405, 75141, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75141_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75141 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75141 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75141, 1, 262144⟩
    (by decide) selected_cut_37902

theorem selected_cut_37903 : selected 9 ⟨1016608, by decide⟩
    (prefixPartial 12 300568) = some ⟨12, 2, 0, 1016608, 300568, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_300568_1016608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300568 ⟨1016608, by decide⟩ :=
  accepted_of_selected 12 300568 ⟨1016608, by decide⟩ ⟨12, 2, 0, 1016608, 300568, 3825, 65536⟩
    (by decide) selected_cut_37903

theorem selected_cut_37904 : selected 9 ⟨1016659, by decide⟩
    (prefixPartial 12 300569) = some ⟨12, 2, 0, 1016659, 300569, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_300569_1016659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300569 ⟨1016659, by decide⟩ :=
  accepted_of_selected 12 300569 ⟨1016659, by decide⟩ ⟨12, 2, 0, 1016659, 300569, 3517, 65536⟩
    (by decide) selected_cut_37904

theorem selected_cut_37905 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 300570) = some ⟨12, 1, 0, 893903, 300570, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300570_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300570 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 300570 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 300570, 1, 65536⟩
    (by decide) selected_cut_37905

theorem selected_cut_37906 : selected 9 ⟨1016724, by decide⟩
    (prefixPartial 12 300571) = some ⟨12, 2, 0, 1016724, 300571, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_300571_1016724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300571 ⟨1016724, by decide⟩ :=
  accepted_of_selected 12 300571 ⟨1016724, by decide⟩ ⟨12, 2, 0, 1016724, 300571, 4057, 65536⟩
    (by decide) selected_cut_37906

theorem unmarked_context_11_75142_1016725 : frontier 10 ⟨1016725, by decide⟩
    (prefixCache 11 75142) (prefixPartial 11 75142) = false := by
  decide +kernel

theorem node_context_11_75142_1016725 : EJMOriginalGlobalDAGData.nodes 10 ⟨1016725, by decide⟩ =
    .split (coordinate 11) (![⟨1016608, by decide⟩,⟨1016659, by decide⟩,⟨893903, by decide⟩,⟨1016724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75142_1016725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75142 ⟨1016725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75142
    ⟨1016725, by decide⟩ (by decide) (![⟨1016608, by decide⟩,⟨1016659, by decide⟩,⟨893903, by decide⟩,⟨1016724, by decide⟩]) unmarked_context_11_75142_1016725 node_context_11_75142_1016725
  intro a
  fin_cases a
  · exact context_12_300568_1016608
  · exact context_12_300569_1016659
  · exact context_12_300570_893903
  · exact context_12_300571_1016724

theorem selected_cut_37907 : selected 8 ⟨1016743, by decide⟩
    (prefixPartial 13 1202288) = some ⟨13, 2, 0, 1016743, 1202288, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_1202288_1016743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202288 ⟨1016743, by decide⟩ :=
  accepted_of_selected 13 1202288 ⟨1016743, by decide⟩ ⟨13, 2, 0, 1016743, 1202288, 1117, 16384⟩
    (by decide) selected_cut_37907

theorem selected_cut_37908 : selected 8 ⟨1016762, by decide⟩
    (prefixPartial 13 1202289) = some ⟨13, 2, 0, 1016762, 1202289, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_1202289_1016762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202289 ⟨1016762, by decide⟩ :=
  accepted_of_selected 13 1202289 ⟨1016762, by decide⟩ ⟨13, 2, 0, 1016762, 1202289, 1293, 16384⟩
    (by decide) selected_cut_37908

theorem selected_cut_37909 : selected 8 ⟨1016784, by decide⟩
    (prefixPartial 13 1202290) = some ⟨13, 2, 0, 1016784, 1202290, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_1202290_1016784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202290 ⟨1016784, by decide⟩ :=
  accepted_of_selected 13 1202290 ⟨1016784, by decide⟩ ⟨13, 2, 0, 1016784, 1202290, 1305, 16384⟩
    (by decide) selected_cut_37909

theorem selected_cut_37910 : selected 8 ⟨1016797, by decide⟩
    (prefixPartial 13 1202291) = some ⟨13, 2, 0, 1016797, 1202291, 725, 16384⟩ := by
  decide +kernel

theorem context_13_1202291_1016797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1202291 ⟨1016797, by decide⟩ :=
  accepted_of_selected 13 1202291 ⟨1016797, by decide⟩ ⟨13, 2, 0, 1016797, 1202291, 725, 16384⟩
    (by decide) selected_cut_37910

theorem unmarked_context_12_300572_1016798 : frontier 9 ⟨1016798, by decide⟩
    (prefixCache 12 300572) (prefixPartial 12 300572) = false := by
  decide +kernel

theorem node_context_12_300572_1016798 : EJMOriginalGlobalDAGData.nodes 9 ⟨1016798, by decide⟩ =
    .split (coordinate 12) (![⟨1016743, by decide⟩,⟨1016762, by decide⟩,⟨1016784, by decide⟩,⟨1016797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300572_1016798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300572 ⟨1016798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300572
    ⟨1016798, by decide⟩ (by decide) (![⟨1016743, by decide⟩,⟨1016762, by decide⟩,⟨1016784, by decide⟩,⟨1016797, by decide⟩]) unmarked_context_12_300572_1016798 node_context_12_300572_1016798
  intro a
  fin_cases a
  · exact context_13_1202288_1016743
  · exact context_13_1202289_1016762
  · exact context_13_1202290_1016784
  · exact context_13_1202291_1016797

theorem selected_cut_37911 : selected 9 ⟨1016860, by decide⟩
    (prefixPartial 12 300573) = some ⟨12, 2, 0, 1016860, 300573, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_300573_1016860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300573 ⟨1016860, by decide⟩ :=
  accepted_of_selected 12 300573 ⟨1016860, by decide⟩ ⟨12, 2, 0, 1016860, 300573, 3769, 65536⟩
    (by decide) selected_cut_37911

theorem selected_cut_37912 : selected 9 ⟨1016921, by decide⟩
    (prefixPartial 12 300574) = some ⟨12, 2, 0, 1016921, 300574, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_300574_1016921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300574 ⟨1016921, by decide⟩ :=
  accepted_of_selected 12 300574 ⟨1016921, by decide⟩ ⟨12, 2, 0, 1016921, 300574, 3813, 65536⟩
    (by decide) selected_cut_37912

theorem selected_cut_37913 : selected 9 ⟨1016994, by decide⟩
    (prefixPartial 12 300575) = some ⟨12, 2, 0, 1016994, 300575, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_300575_1016994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300575 ⟨1016994, by decide⟩ :=
  accepted_of_selected 12 300575 ⟨1016994, by decide⟩ ⟨12, 2, 0, 1016994, 300575, 4069, 65536⟩
    (by decide) selected_cut_37913

theorem unmarked_context_11_75143_1016995 : frontier 10 ⟨1016995, by decide⟩
    (prefixCache 11 75143) (prefixPartial 11 75143) = false := by
  decide +kernel

theorem node_context_11_75143_1016995 : EJMOriginalGlobalDAGData.nodes 10 ⟨1016995, by decide⟩ =
    .split (coordinate 11) (![⟨1016798, by decide⟩,⟨1016860, by decide⟩,⟨1016921, by decide⟩,⟨1016994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75143_1016995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75143 ⟨1016995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75143
    ⟨1016995, by decide⟩ (by decide) (![⟨1016798, by decide⟩,⟨1016860, by decide⟩,⟨1016921, by decide⟩,⟨1016994, by decide⟩]) unmarked_context_11_75143_1016995 node_context_11_75143_1016995
  intro a
  fin_cases a
  · exact context_12_300572_1016798
  · exact context_12_300573_1016860
  · exact context_12_300574_1016921
  · exact context_12_300575_1016994

theorem unmarked_context_10_18785_1016996 : frontier 11 ⟨1016996, by decide⟩
    (prefixCache 10 18785) (prefixPartial 10 18785) = false := by
  decide +kernel

theorem node_context_10_18785_1016996 : EJMOriginalGlobalDAGData.nodes 11 ⟨1016996, by decide⟩ =
    .split (coordinate 10) (![⟨1016549, by decide⟩,⟨892405, by decide⟩,⟨1016725, by decide⟩,⟨1016995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18785_1016996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18785 ⟨1016996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18785
    ⟨1016996, by decide⟩ (by decide) (![⟨1016549, by decide⟩,⟨892405, by decide⟩,⟨1016725, by decide⟩,⟨1016995, by decide⟩]) unmarked_context_10_18785_1016996 node_context_10_18785_1016996
  intro a
  fin_cases a
  · exact context_11_75140_1016549
  · exact context_11_75141_892405
  · exact context_11_75142_1016725
  · exact context_11_75143_1016995

theorem selected_cut_37914 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 300576) = some ⟨12, 1, 0, 994572, 300576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300576_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300576 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 300576 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 300576, 1, 65536⟩
    (by decide) selected_cut_37914

theorem selected_cut_37915 : selected 9 ⟨1017068, by decide⟩
    (prefixPartial 12 300577) = some ⟨12, 2, 0, 1017068, 300577, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_300577_1017068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300577 ⟨1017068, by decide⟩ :=
  accepted_of_selected 12 300577 ⟨1017068, by decide⟩ ⟨12, 2, 0, 1017068, 300577, 3661, 65536⟩
    (by decide) selected_cut_37915

theorem selected_cut_37916 : selected 9 ⟨1017119, by decide⟩
    (prefixPartial 12 300578) = some ⟨12, 2, 0, 1017119, 300578, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_300578_1017119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300578 ⟨1017119, by decide⟩ :=
  accepted_of_selected 12 300578 ⟨1017119, by decide⟩ ⟨12, 2, 0, 1017119, 300578, 3293, 65536⟩
    (by decide) selected_cut_37916

theorem selected_cut_37917 : selected 9 ⟨1017192, by decide⟩
    (prefixPartial 12 300579) = some ⟨12, 2, 0, 1017192, 300579, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_300579_1017192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300579 ⟨1017192, by decide⟩ :=
  accepted_of_selected 12 300579 ⟨1017192, by decide⟩ ⟨12, 2, 0, 1017192, 300579, 3829, 65536⟩
    (by decide) selected_cut_37917

theorem unmarked_context_11_75144_1017193 : frontier 10 ⟨1017193, by decide⟩
    (prefixCache 11 75144) (prefixPartial 11 75144) = false := by
  decide +kernel

theorem node_context_11_75144_1017193 : EJMOriginalGlobalDAGData.nodes 10 ⟨1017193, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1017068, by decide⟩,⟨1017119, by decide⟩,⟨1017192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75144_1017193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75144 ⟨1017193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75144
    ⟨1017193, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1017068, by decide⟩,⟨1017119, by decide⟩,⟨1017192, by decide⟩]) unmarked_context_11_75144_1017193 node_context_11_75144_1017193
  intro a
  fin_cases a
  · exact context_12_300576_994572
  · exact context_12_300577_1017068
  · exact context_12_300578_1017119
  · exact context_12_300579_1017192

theorem selected_cut_37918 : selected 9 ⟨1017253, by decide⟩
    (prefixPartial 12 300580) = some ⟨12, 2, 0, 1017253, 300580, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_300580_1017253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300580 ⟨1017253, by decide⟩ :=
  accepted_of_selected 12 300580 ⟨1017253, by decide⟩ ⟨12, 2, 0, 1017253, 300580, 3597, 65536⟩
    (by decide) selected_cut_37918

theorem selected_cut_37919 : selected 9 ⟨1017310, by decide⟩
    (prefixPartial 12 300581) = some ⟨12, 2, 0, 1017310, 300581, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_300581_1017310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300581 ⟨1017310, by decide⟩ :=
  accepted_of_selected 12 300581 ⟨1017310, by decide⟩ ⟨12, 2, 0, 1017310, 300581, 3501, 65536⟩
    (by decide) selected_cut_37919

theorem selected_cut_37920 : selected 9 ⟨1017354, by decide⟩
    (prefixPartial 12 300582) = some ⟨12, 2, 0, 1017354, 300582, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_300582_1017354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300582 ⟨1017354, by decide⟩ :=
  accepted_of_selected 12 300582 ⟨1017354, by decide⟩ ⟨12, 2, 0, 1017354, 300582, 3017, 65536⟩
    (by decide) selected_cut_37920

theorem selected_cut_37921 : selected 9 ⟨1017410, by decide⟩
    (prefixPartial 12 300583) = some ⟨12, 2, 0, 1017410, 300583, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_300583_1017410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300583 ⟨1017410, by decide⟩ :=
  accepted_of_selected 12 300583 ⟨1017410, by decide⟩ ⟨12, 2, 0, 1017410, 300583, 3521, 65536⟩
    (by decide) selected_cut_37921

theorem unmarked_context_11_75145_1017411 : frontier 10 ⟨1017411, by decide⟩
    (prefixCache 11 75145) (prefixPartial 11 75145) = false := by
  decide +kernel

theorem node_context_11_75145_1017411 : EJMOriginalGlobalDAGData.nodes 10 ⟨1017411, by decide⟩ =
    .split (coordinate 11) (![⟨1017253, by decide⟩,⟨1017310, by decide⟩,⟨1017354, by decide⟩,⟨1017410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75145_1017411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75145 ⟨1017411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75145
    ⟨1017411, by decide⟩ (by decide) (![⟨1017253, by decide⟩,⟨1017310, by decide⟩,⟨1017354, by decide⟩,⟨1017410, by decide⟩]) unmarked_context_11_75145_1017411 node_context_11_75145_1017411
  intro a
  fin_cases a
  · exact context_12_300580_1017253
  · exact context_12_300581_1017310
  · exact context_12_300582_1017354
  · exact context_12_300583_1017410

theorem selected_cut_37922 : selected 9 ⟨1017467, by decide⟩
    (prefixPartial 12 300584) = some ⟨12, 2, 0, 1017467, 300584, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_300584_1017467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300584 ⟨1017467, by decide⟩ :=
  accepted_of_selected 12 300584 ⟨1017467, by decide⟩ ⟨12, 2, 0, 1017467, 300584, 3849, 65536⟩
    (by decide) selected_cut_37922

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
