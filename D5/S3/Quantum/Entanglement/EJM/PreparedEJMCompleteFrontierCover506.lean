/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover505
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48580 : selected 9 ⟨1363666, by decide⟩
    (prefixPartial 12 376648) = some ⟨12, 2, 0, 1363666, 376648, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_376648_1363666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376648 ⟨1363666, by decide⟩ :=
  accepted_of_selected 12 376648 ⟨1363666, by decide⟩ ⟨12, 2, 0, 1363666, 376648, 1757, 65536⟩
    (by decide) selected_cut_48580

theorem selected_cut_48581 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 376649) = some ⟨12, 1, 0, 1025817, 376649, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376649_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376649 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 376649 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 376649, 1, 65536⟩
    (by decide) selected_cut_48581

theorem selected_cut_48582 : selected 9 ⟨1363695, by decide⟩
    (prefixPartial 12 376650) = some ⟨12, 2, 0, 1363695, 376650, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_376650_1363695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376650 ⟨1363695, by decide⟩ :=
  accepted_of_selected 12 376650 ⟨1363695, by decide⟩ ⟨12, 2, 0, 1363695, 376650, 1561, 65536⟩
    (by decide) selected_cut_48582

theorem selected_cut_48583 : selected 9 ⟨1363723, by decide⟩
    (prefixPartial 12 376651) = some ⟨12, 2, 0, 1363723, 376651, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_376651_1363723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376651 ⟨1363723, by decide⟩ :=
  accepted_of_selected 12 376651 ⟨1363723, by decide⟩ ⟨12, 2, 0, 1363723, 376651, 1605, 65536⟩
    (by decide) selected_cut_48583

theorem unmarked_context_11_94162_1363724 : frontier 10 ⟨1363724, by decide⟩
    (prefixCache 11 94162) (prefixPartial 11 94162) = false := by
  decide +kernel

theorem node_context_11_94162_1363724 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363724, by decide⟩ =
    .split (coordinate 11) (![⟨1363666, by decide⟩,⟨1025817, by decide⟩,⟨1363695, by decide⟩,⟨1363723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94162_1363724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94162 ⟨1363724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94162
    ⟨1363724, by decide⟩ (by decide) (![⟨1363666, by decide⟩,⟨1025817, by decide⟩,⟨1363695, by decide⟩,⟨1363723, by decide⟩]) unmarked_context_11_94162_1363724 node_context_11_94162_1363724
  intro a
  fin_cases a
  · exact context_12_376648_1363666
  · exact context_12_376649_1025817
  · exact context_12_376650_1363695
  · exact context_12_376651_1363723

theorem selected_cut_48584 : selected 9 ⟨1363748, by decide⟩
    (prefixPartial 12 376652) = some ⟨12, 2, 0, 1363748, 376652, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_376652_1363748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376652 ⟨1363748, by decide⟩ :=
  accepted_of_selected 12 376652 ⟨1363748, by decide⟩ ⟨12, 2, 0, 1363748, 376652, 1697, 65536⟩
    (by decide) selected_cut_48584

theorem selected_cut_48585 : selected 9 ⟨1363773, by decide⟩
    (prefixPartial 12 376653) = some ⟨12, 2, 0, 1363773, 376653, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_376653_1363773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376653 ⟨1363773, by decide⟩ :=
  accepted_of_selected 12 376653 ⟨1363773, by decide⟩ ⟨12, 2, 0, 1363773, 376653, 1489, 65536⟩
    (by decide) selected_cut_48585

theorem selected_cut_48586 : selected 9 ⟨1363796, by decide⟩
    (prefixPartial 12 376654) = some ⟨12, 2, 0, 1363796, 376654, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_376654_1363796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376654 ⟨1363796, by decide⟩ :=
  accepted_of_selected 12 376654 ⟨1363796, by decide⟩ ⟨12, 2, 0, 1363796, 376654, 1573, 65536⟩
    (by decide) selected_cut_48586

theorem selected_cut_48587 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 376655) = some ⟨12, 1, 0, 903806, 376655, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376655_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376655 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 376655 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 376655, 1, 65536⟩
    (by decide) selected_cut_48587

theorem unmarked_context_11_94163_1363797 : frontier 10 ⟨1363797, by decide⟩
    (prefixCache 11 94163) (prefixPartial 11 94163) = false := by
  decide +kernel

theorem node_context_11_94163_1363797 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363797, by decide⟩ =
    .split (coordinate 11) (![⟨1363748, by decide⟩,⟨1363773, by decide⟩,⟨1363796, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94163_1363797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94163 ⟨1363797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94163
    ⟨1363797, by decide⟩ (by decide) (![⟨1363748, by decide⟩,⟨1363773, by decide⟩,⟨1363796, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_94163_1363797 node_context_11_94163_1363797
  intro a
  fin_cases a
  · exact context_12_376652_1363748
  · exact context_12_376653_1363773
  · exact context_12_376654_1363796
  · exact context_12_376655_903806

theorem unmarked_context_10_23540_1363798 : frontier 11 ⟨1363798, by decide⟩
    (prefixCache 10 23540) (prefixPartial 10 23540) = false := by
  decide +kernel

theorem node_context_10_23540_1363798 : EJMOriginalGlobalDAGData.nodes 11 ⟨1363798, by decide⟩ =
    .split (coordinate 10) (![⟨1363523, by decide⟩,⟨1363640, by decide⟩,⟨1363724, by decide⟩,⟨1363797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23540_1363798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23540 ⟨1363798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23540
    ⟨1363798, by decide⟩ (by decide) (![⟨1363523, by decide⟩,⟨1363640, by decide⟩,⟨1363724, by decide⟩,⟨1363797, by decide⟩]) unmarked_context_10_23540_1363798 node_context_10_23540_1363798
  intro a
  fin_cases a
  · exact context_11_94160_1363523
  · exact context_11_94161_1363640
  · exact context_11_94162_1363724
  · exact context_11_94163_1363797

theorem selected_cut_48588 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23541) = some ⟨10, 1, 0, 893098, 23541, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23541_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23541 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23541 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23541, 1, 1048576⟩
    (by decide) selected_cut_48588

theorem selected_cut_48589 : selected 9 ⟨1363825, by decide⟩
    (prefixPartial 12 376672) = some ⟨12, 2, 0, 1363825, 376672, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_376672_1363825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376672 ⟨1363825, by decide⟩ :=
  accepted_of_selected 12 376672 ⟨1363825, by decide⟩ ⟨12, 2, 0, 1363825, 376672, 1497, 65536⟩
    (by decide) selected_cut_48589

theorem selected_cut_48590 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 376673) = some ⟨12, 1, 0, 1256866, 376673, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376673_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376673 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 376673 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 376673, 1, 65536⟩
    (by decide) selected_cut_48590

theorem selected_cut_48591 : selected 9 ⟨1363851, by decide⟩
    (prefixPartial 12 376674) = some ⟨12, 2, 0, 1363851, 376674, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_376674_1363851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376674 ⟨1363851, by decide⟩ :=
  accepted_of_selected 12 376674 ⟨1363851, by decide⟩ ⟨12, 2, 0, 1363851, 376674, 1421, 65536⟩
    (by decide) selected_cut_48591

theorem selected_cut_48592 : selected 9 ⟨1363873, by decide⟩
    (prefixPartial 12 376675) = some ⟨12, 2, 0, 1363873, 376675, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_376675_1363873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376675 ⟨1363873, by decide⟩ :=
  accepted_of_selected 12 376675 ⟨1363873, by decide⟩ ⟨12, 2, 0, 1363873, 376675, 1329, 65536⟩
    (by decide) selected_cut_48592

theorem unmarked_context_11_94168_1363874 : frontier 10 ⟨1363874, by decide⟩
    (prefixCache 11 94168) (prefixPartial 11 94168) = false := by
  decide +kernel

theorem node_context_11_94168_1363874 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363874, by decide⟩ =
    .split (coordinate 11) (![⟨1363825, by decide⟩,⟨1256866, by decide⟩,⟨1363851, by decide⟩,⟨1363873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94168_1363874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94168 ⟨1363874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94168
    ⟨1363874, by decide⟩ (by decide) (![⟨1363825, by decide⟩,⟨1256866, by decide⟩,⟨1363851, by decide⟩,⟨1363873, by decide⟩]) unmarked_context_11_94168_1363874 node_context_11_94168_1363874
  intro a
  fin_cases a
  · exact context_12_376672_1363825
  · exact context_12_376673_1256866
  · exact context_12_376674_1363851
  · exact context_12_376675_1363873

theorem selected_cut_48593 : selected 9 ⟨1363908, by decide⟩
    (prefixPartial 12 376676) = some ⟨12, 2, 0, 1363908, 376676, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_376676_1363908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376676 ⟨1363908, by decide⟩ :=
  accepted_of_selected 12 376676 ⟨1363908, by decide⟩ ⟨12, 2, 0, 1363908, 376676, 1577, 65536⟩
    (by decide) selected_cut_48593

theorem selected_cut_48594 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 376677) = some ⟨12, 1, 0, 1256866, 376677, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376677_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376677 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 376677 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 376677, 1, 65536⟩
    (by decide) selected_cut_48594

theorem selected_cut_48595 : selected 9 ⟨1363933, by decide⟩
    (prefixPartial 12 376678) = some ⟨12, 2, 0, 1363933, 376678, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_376678_1363933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376678 ⟨1363933, by decide⟩ :=
  accepted_of_selected 12 376678 ⟨1363933, by decide⟩ ⟨12, 2, 0, 1363933, 376678, 1485, 65536⟩
    (by decide) selected_cut_48595

theorem selected_cut_48596 : selected 9 ⟨1363955, by decide⟩
    (prefixPartial 12 376679) = some ⟨12, 2, 0, 1363955, 376679, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_376679_1363955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376679 ⟨1363955, by decide⟩ :=
  accepted_of_selected 12 376679 ⟨1363955, by decide⟩ ⟨12, 2, 0, 1363955, 376679, 1405, 65536⟩
    (by decide) selected_cut_48596

theorem unmarked_context_11_94169_1363956 : frontier 10 ⟨1363956, by decide⟩
    (prefixCache 11 94169) (prefixPartial 11 94169) = false := by
  decide +kernel

theorem node_context_11_94169_1363956 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363956, by decide⟩ =
    .split (coordinate 11) (![⟨1363908, by decide⟩,⟨1256866, by decide⟩,⟨1363933, by decide⟩,⟨1363955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94169_1363956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94169 ⟨1363956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94169
    ⟨1363956, by decide⟩ (by decide) (![⟨1363908, by decide⟩,⟨1256866, by decide⟩,⟨1363933, by decide⟩,⟨1363955, by decide⟩]) unmarked_context_11_94169_1363956 node_context_11_94169_1363956
  intro a
  fin_cases a
  · exact context_12_376676_1363908
  · exact context_12_376677_1256866
  · exact context_12_376678_1363933
  · exact context_12_376679_1363955

theorem selected_cut_48597 : selected 10 ⟨1363977, by decide⟩
    (prefixPartial 11 94170) = some ⟨11, 2, 0, 1363977, 94170, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_94170_1363977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94170 ⟨1363977, by decide⟩ :=
  accepted_of_selected 11 94170 ⟨1363977, by decide⟩ ⟨11, 2, 0, 1363977, 94170, 1149, 262144⟩
    (by decide) selected_cut_48597

theorem selected_cut_48598 : selected 10 ⟨1364014, by decide⟩
    (prefixPartial 11 94171) = some ⟨11, 2, 0, 1364014, 94171, 2281, 262144⟩ := by
  decide +kernel

theorem context_11_94171_1364014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94171 ⟨1364014, by decide⟩ :=
  accepted_of_selected 11 94171 ⟨1364014, by decide⟩ ⟨11, 2, 0, 1364014, 94171, 2281, 262144⟩
    (by decide) selected_cut_48598

theorem unmarked_context_10_23542_1364015 : frontier 11 ⟨1364015, by decide⟩
    (prefixCache 10 23542) (prefixPartial 10 23542) = false := by
  decide +kernel

theorem node_context_10_23542_1364015 : EJMOriginalGlobalDAGData.nodes 11 ⟨1364015, by decide⟩ =
    .split (coordinate 10) (![⟨1363874, by decide⟩,⟨1363956, by decide⟩,⟨1363977, by decide⟩,⟨1364014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23542_1364015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23542 ⟨1364015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23542
    ⟨1364015, by decide⟩ (by decide) (![⟨1363874, by decide⟩,⟨1363956, by decide⟩,⟨1363977, by decide⟩,⟨1364014, by decide⟩]) unmarked_context_10_23542_1364015 node_context_10_23542_1364015
  intro a
  fin_cases a
  · exact context_11_94168_1363874
  · exact context_11_94169_1363956
  · exact context_11_94170_1363977
  · exact context_11_94171_1364014

theorem selected_cut_48599 : selected 10 ⟨1364072, by decide⟩
    (prefixPartial 11 94172) = some ⟨11, 2, 0, 1364072, 94172, 2869, 262144⟩ := by
  decide +kernel

theorem context_11_94172_1364072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94172 ⟨1364072, by decide⟩ :=
  accepted_of_selected 11 94172 ⟨1364072, by decide⟩ ⟨11, 2, 0, 1364072, 94172, 2869, 262144⟩
    (by decide) selected_cut_48599

theorem selected_cut_48600 : selected 10 ⟨1364135, by decide⟩
    (prefixPartial 11 94173) = some ⟨11, 2, 0, 1364135, 94173, 3161, 262144⟩ := by
  decide +kernel

theorem context_11_94173_1364135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94173 ⟨1364135, by decide⟩ :=
  accepted_of_selected 11 94173 ⟨1364135, by decide⟩ ⟨11, 2, 0, 1364135, 94173, 3161, 262144⟩
    (by decide) selected_cut_48600

theorem selected_cut_48601 : selected 10 ⟨1364163, by decide⟩
    (prefixPartial 11 94174) = some ⟨11, 2, 0, 1364163, 94174, 1565, 262144⟩ := by
  decide +kernel

theorem context_11_94174_1364163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94174 ⟨1364163, by decide⟩ :=
  accepted_of_selected 11 94174 ⟨1364163, by decide⟩ ⟨11, 2, 0, 1364163, 94174, 1565, 262144⟩
    (by decide) selected_cut_48601

theorem selected_cut_48602 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 94175) = some ⟨11, 1, 0, 977886, 94175, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94175_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94175 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 94175 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 94175, 1, 262144⟩
    (by decide) selected_cut_48602

theorem unmarked_context_10_23543_1364164 : frontier 11 ⟨1364164, by decide⟩
    (prefixCache 10 23543) (prefixPartial 10 23543) = false := by
  decide +kernel

theorem node_context_10_23543_1364164 : EJMOriginalGlobalDAGData.nodes 11 ⟨1364164, by decide⟩ =
    .split (coordinate 10) (![⟨1364072, by decide⟩,⟨1364135, by decide⟩,⟨1364163, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23543_1364164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23543 ⟨1364164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23543
    ⟨1364164, by decide⟩ (by decide) (![⟨1364072, by decide⟩,⟨1364135, by decide⟩,⟨1364163, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23543_1364164 node_context_10_23543_1364164
  intro a
  fin_cases a
  · exact context_11_94172_1364072
  · exact context_11_94173_1364135
  · exact context_11_94174_1364163
  · exact context_11_94175_977886

theorem unmarked_context_9_5885_1364165 : frontier 12 ⟨1364165, by decide⟩
    (prefixCache 9 5885) (prefixPartial 9 5885) = false := by
  decide +kernel

theorem node_context_9_5885_1364165 : EJMOriginalGlobalDAGData.nodes 12 ⟨1364165, by decide⟩ =
    .split (coordinate 9) (![⟨1363798, by decide⟩,⟨893098, by decide⟩,⟨1364015, by decide⟩,⟨1364164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5885_1364165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5885 ⟨1364165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5885
    ⟨1364165, by decide⟩ (by decide) (![⟨1363798, by decide⟩,⟨893098, by decide⟩,⟨1364015, by decide⟩,⟨1364164, by decide⟩]) unmarked_context_9_5885_1364165 node_context_9_5885_1364165
  intro a
  fin_cases a
  · exact context_10_23540_1363798
  · exact context_10_23541_893098
  · exact context_10_23542_1364015
  · exact context_10_23543_1364164

theorem selected_cut_48603 : selected 10 ⟨1364177, by decide⟩
    (prefixPartial 11 94176) = some ⟨11, 2, 0, 1364177, 94176, 997, 262144⟩ := by
  decide +kernel

theorem context_11_94176_1364177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94176 ⟨1364177, by decide⟩ :=
  accepted_of_selected 11 94176 ⟨1364177, by decide⟩ ⟨11, 2, 0, 1364177, 94176, 997, 262144⟩
    (by decide) selected_cut_48603

theorem selected_cut_48604 : selected 10 ⟨1364230, by decide⟩
    (prefixPartial 11 94177) = some ⟨11, 2, 0, 1364230, 94177, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_94177_1364230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94177 ⟨1364230, by decide⟩ :=
  accepted_of_selected 11 94177 ⟨1364230, by decide⟩ ⟨11, 2, 0, 1364230, 94177, 3113, 262144⟩
    (by decide) selected_cut_48604

theorem selected_cut_48605 : selected 10 ⟨1364265, by decide⟩
    (prefixPartial 11 94178) = some ⟨11, 2, 0, 1364265, 94178, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_94178_1364265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94178 ⟨1364265, by decide⟩ :=
  accepted_of_selected 11 94178 ⟨1364265, by decide⟩ ⟨11, 2, 0, 1364265, 94178, 2645, 262144⟩
    (by decide) selected_cut_48605

theorem selected_cut_48606 : selected 10 ⟨1364289, by decide⟩
    (prefixPartial 11 94179) = some ⟨11, 2, 0, 1364289, 94179, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_94179_1364289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94179 ⟨1364289, by decide⟩ :=
  accepted_of_selected 11 94179 ⟨1364289, by decide⟩ ⟨11, 2, 0, 1364289, 94179, 1517, 262144⟩
    (by decide) selected_cut_48606

theorem unmarked_context_10_23544_1364290 : frontier 11 ⟨1364290, by decide⟩
    (prefixCache 10 23544) (prefixPartial 10 23544) = false := by
  decide +kernel

theorem node_context_10_23544_1364290 : EJMOriginalGlobalDAGData.nodes 11 ⟨1364290, by decide⟩ =
    .split (coordinate 10) (![⟨1364177, by decide⟩,⟨1364230, by decide⟩,⟨1364265, by decide⟩,⟨1364289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23544_1364290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23544 ⟨1364290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23544
    ⟨1364290, by decide⟩ (by decide) (![⟨1364177, by decide⟩,⟨1364230, by decide⟩,⟨1364265, by decide⟩,⟨1364289, by decide⟩]) unmarked_context_10_23544_1364290 node_context_10_23544_1364290
  intro a
  fin_cases a
  · exact context_11_94176_1364177
  · exact context_11_94177_1364230
  · exact context_11_94178_1364265
  · exact context_11_94179_1364289

theorem selected_cut_48607 : selected 10 ⟨1364318, by decide⟩
    (prefixPartial 11 94180) = some ⟨11, 2, 0, 1364318, 94180, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_94180_1364318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94180 ⟨1364318, by decide⟩ :=
  accepted_of_selected 11 94180 ⟨1364318, by decide⟩ ⟨11, 2, 0, 1364318, 94180, 2085, 262144⟩
    (by decide) selected_cut_48607

theorem selected_cut_48608 : selected 10 ⟨1364331, by decide⟩
    (prefixPartial 11 94181) = some ⟨11, 2, 0, 1364331, 94181, 777, 262144⟩ := by
  decide +kernel

theorem context_11_94181_1364331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94181 ⟨1364331, by decide⟩ :=
  accepted_of_selected 11 94181 ⟨1364331, by decide⟩ ⟨11, 2, 0, 1364331, 94181, 777, 262144⟩
    (by decide) selected_cut_48608

theorem selected_cut_48609 : selected 10 ⟨1364360, by decide⟩
    (prefixPartial 11 94182) = some ⟨11, 2, 0, 1364360, 94182, 1813, 262144⟩ := by
  decide +kernel

theorem context_11_94182_1364360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94182 ⟨1364360, by decide⟩ :=
  accepted_of_selected 11 94182 ⟨1364360, by decide⟩ ⟨11, 2, 0, 1364360, 94182, 1813, 262144⟩
    (by decide) selected_cut_48609

theorem selected_cut_48610 : selected 10 ⟨1364378, by decide⟩
    (prefixPartial 11 94183) = some ⟨11, 2, 0, 1364378, 94183, 957, 262144⟩ := by
  decide +kernel

theorem context_11_94183_1364378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94183 ⟨1364378, by decide⟩ :=
  accepted_of_selected 11 94183 ⟨1364378, by decide⟩ ⟨11, 2, 0, 1364378, 94183, 957, 262144⟩
    (by decide) selected_cut_48610

theorem unmarked_context_10_23545_1364379 : frontier 11 ⟨1364379, by decide⟩
    (prefixCache 10 23545) (prefixPartial 10 23545) = false := by
  decide +kernel

theorem node_context_10_23545_1364379 : EJMOriginalGlobalDAGData.nodes 11 ⟨1364379, by decide⟩ =
    .split (coordinate 10) (![⟨1364318, by decide⟩,⟨1364331, by decide⟩,⟨1364360, by decide⟩,⟨1364378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23545_1364379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23545 ⟨1364379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23545
    ⟨1364379, by decide⟩ (by decide) (![⟨1364318, by decide⟩,⟨1364331, by decide⟩,⟨1364360, by decide⟩,⟨1364378, by decide⟩]) unmarked_context_10_23545_1364379 node_context_10_23545_1364379
  intro a
  fin_cases a
  · exact context_11_94180_1364318
  · exact context_11_94181_1364331
  · exact context_11_94182_1364360
  · exact context_11_94183_1364378

theorem selected_cut_48611 : selected 11 ⟨1364401, by decide⟩
    (prefixPartial 10 23546) = some ⟨10, 2, 0, 1364401, 23546, 1277, 1048576⟩ := by
  decide +kernel

theorem context_10_23546_1364401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23546 ⟨1364401, by decide⟩ :=
  accepted_of_selected 10 23546 ⟨1364401, by decide⟩ ⟨10, 2, 0, 1364401, 23546, 1277, 1048576⟩
    (by decide) selected_cut_48611

theorem selected_cut_48612 : selected 11 ⟨1364451, by decide⟩
    (prefixPartial 10 23547) = some ⟨10, 2, 0, 1364451, 23547, 2537, 1048576⟩ := by
  decide +kernel

theorem context_10_23547_1364451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23547 ⟨1364451, by decide⟩ :=
  accepted_of_selected 10 23547 ⟨1364451, by decide⟩ ⟨10, 2, 0, 1364451, 23547, 2537, 1048576⟩
    (by decide) selected_cut_48612

theorem unmarked_context_9_5886_1364452 : frontier 12 ⟨1364452, by decide⟩
    (prefixCache 9 5886) (prefixPartial 9 5886) = false := by
  decide +kernel

theorem node_context_9_5886_1364452 : EJMOriginalGlobalDAGData.nodes 12 ⟨1364452, by decide⟩ =
    .split (coordinate 9) (![⟨1364290, by decide⟩,⟨1364379, by decide⟩,⟨1364401, by decide⟩,⟨1364451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5886_1364452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5886 ⟨1364452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5886
    ⟨1364452, by decide⟩ (by decide) (![⟨1364290, by decide⟩,⟨1364379, by decide⟩,⟨1364401, by decide⟩,⟨1364451, by decide⟩]) unmarked_context_9_5886_1364452 node_context_9_5886_1364452
  intro a
  fin_cases a
  · exact context_10_23544_1364290
  · exact context_10_23545_1364379
  · exact context_10_23546_1364401
  · exact context_10_23547_1364451

theorem selected_cut_48613 : selected 12 ⟨1364549, by decide⟩
    (prefixPartial 9 5887) = some ⟨9, 2, 0, 1364549, 5887, 3505, 4194304⟩ := by
  decide +kernel

theorem context_9_5887_1364549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5887 ⟨1364549, by decide⟩ :=
  accepted_of_selected 9 5887 ⟨1364549, by decide⟩ ⟨9, 2, 0, 1364549, 5887, 3505, 4194304⟩
    (by decide) selected_cut_48613

theorem unmarked_context_8_1471_1364550 : frontier 13 ⟨1364550, by decide⟩
    (prefixCache 8 1471) (prefixPartial 8 1471) = false := by
  decide +kernel

theorem node_context_8_1471_1364550 : EJMOriginalGlobalDAGData.nodes 13 ⟨1364550, by decide⟩ =
    .split (coordinate 8) (![⟨1363463, by decide⟩,⟨1364165, by decide⟩,⟨1364452, by decide⟩,⟨1364549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1471_1364550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1471 ⟨1364550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1471
    ⟨1364550, by decide⟩ (by decide) (![⟨1363463, by decide⟩,⟨1364165, by decide⟩,⟨1364452, by decide⟩,⟨1364549, by decide⟩]) unmarked_context_8_1471_1364550 node_context_8_1471_1364550
  intro a
  fin_cases a
  · exact context_9_5884_1363463
  · exact context_9_5885_1364165
  · exact context_9_5886_1364452
  · exact context_9_5887_1364549

theorem unmarked_context_7_367_1364551 : frontier 14 ⟨1364551, by decide⟩
    (prefixCache 7 367) (prefixPartial 7 367) = false := by
  decide +kernel

theorem node_context_7_367_1364551 : EJMOriginalGlobalDAGData.nodes 14 ⟨1364551, by decide⟩ =
    .split (coordinate 7) (![⟨1356725, by decide⟩,⟨1359147, by decide⟩,⟨1361945, by decide⟩,⟨1364550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_367_1364551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 367 ⟨1364551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 367
    ⟨1364551, by decide⟩ (by decide) (![⟨1356725, by decide⟩,⟨1359147, by decide⟩,⟨1361945, by decide⟩,⟨1364550, by decide⟩]) unmarked_context_7_367_1364551 node_context_7_367_1364551
  intro a
  fin_cases a
  · exact context_8_1468_1356725
  · exact context_8_1469_1359147
  · exact context_8_1470_1361945
  · exact context_8_1471_1364550

theorem unmarked_context_6_91_1364552 : frontier 15 ⟨1364552, by decide⟩
    (prefixCache 6 91) (prefixPartial 6 91) = false := by
  decide +kernel

theorem node_context_6_91_1364552 : EJMOriginalGlobalDAGData.nodes 15 ⟨1364552, by decide⟩ =
    .split (coordinate 6) (![⟨1332113, by decide⟩,⟨1342372, by decide⟩,⟨1353813, by decide⟩,⟨1364551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_91_1364552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 91 ⟨1364552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 91
    ⟨1364552, by decide⟩ (by decide) (![⟨1332113, by decide⟩,⟨1342372, by decide⟩,⟨1353813, by decide⟩,⟨1364551, by decide⟩]) unmarked_context_6_91_1364552 node_context_6_91_1364552
  intro a
  fin_cases a
  · exact context_7_364_1332113
  · exact context_7_365_1342372
  · exact context_7_366_1353813
  · exact context_7_367_1364551

theorem unmarked_context_5_22_1364553 : frontier 16 ⟨1364553, by decide⟩
    (prefixCache 5 22) (prefixPartial 5 22) = false := by
  decide +kernel

theorem node_context_5_22_1364553 : EJMOriginalGlobalDAGData.nodes 16 ⟨1364553, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨1266738, by decide⟩,⟨1321174, by decide⟩,⟨1364552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_22_1364553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 22 ⟨1364553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 22
    ⟨1364553, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨1266738, by decide⟩,⟨1321174, by decide⟩,⟨1364552, by decide⟩]) unmarked_context_5_22_1364553 node_context_5_22_1364553
  intro a
  fin_cases a
  · exact context_6_88_434744
  · exact context_6_89_1266738
  · exact context_6_90_1321174
  · exact context_6_91_1364552

theorem selected_cut_48614 : selected 16 ⟨434742, by decide⟩
    (prefixPartial 5 23) = some ⟨5, 1, 0, 434742, 23, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_23_434742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 23 ⟨434742, by decide⟩ :=
  accepted_of_selected 5 23 ⟨434742, by decide⟩ ⟨5, 1, 0, 434742, 23, 1, 1073741824⟩
    (by decide) selected_cut_48614

theorem unmarked_context_4_5_1364554 : frontier 17 ⟨1364554, by decide⟩
    (prefixCache 4 5) (prefixPartial 4 5) = false := by
  decide +kernel

theorem node_context_4_5_1364554 : EJMOriginalGlobalDAGData.nodes 17 ⟨1364554, by decide⟩ =
    .split (coordinate 4) (![⟨1186975, by decide⟩,⟨1252302, by decide⟩,⟨1364553, by decide⟩,⟨434742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_5_1364554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 5 ⟨1364554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 5
    ⟨1364554, by decide⟩ (by decide) (![⟨1186975, by decide⟩,⟨1252302, by decide⟩,⟨1364553, by decide⟩,⟨434742, by decide⟩]) unmarked_context_4_5_1364554 node_context_4_5_1364554
  intro a
  fin_cases a
  · exact context_5_20_1186975
  · exact context_5_21_1252302
  · exact context_5_22_1364553
  · exact context_5_23_434742

theorem selected_cut_48615 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 96) = some ⟨6, 1, 0, 434744, 96, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_96_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 96 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 96 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 96, 1, 268435456⟩
    (by decide) selected_cut_48615

theorem selected_cut_48616 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 97) = some ⟨6, 1, 0, 434744, 97, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_97_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 97 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 97 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 97, 1, 268435456⟩
    (by decide) selected_cut_48616

theorem selected_cut_48617 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 1568) = some ⟨8, 1, 0, 1364555, 1568, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1568_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1568 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 1568 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 1568, 1, 16777216⟩
    (by decide) selected_cut_48617

theorem selected_cut_48618 : selected 11 ⟨1364693, by decide⟩
    (prefixPartial 10 25104) = some ⟨10, 2, 0, 1364693, 25104, 2921, 1048576⟩ := by
  decide +kernel

theorem context_10_25104_1364693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25104 ⟨1364693, by decide⟩ :=
  accepted_of_selected 10 25104 ⟨1364693, by decide⟩ ⟨10, 2, 0, 1364693, 25104, 2921, 1048576⟩
    (by decide) selected_cut_48618

theorem selected_cut_48619 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 401680) = some ⟨12, 1, 0, 1108174, 401680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_401680_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401680 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 401680 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 401680, 1, 65536⟩
    (by decide) selected_cut_48619

theorem selected_cut_48620 : selected 9 ⟨1364760, by decide⟩
    (prefixPartial 12 401681) = some ⟨12, 2, 0, 1364760, 401681, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_401681_1364760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401681 ⟨1364760, by decide⟩ :=
  accepted_of_selected 12 401681 ⟨1364760, by decide⟩ ⟨12, 2, 0, 1364760, 401681, 1713, 65536⟩
    (by decide) selected_cut_48620

theorem selected_cut_48621 : selected 9 ⟨1364812, by decide⟩
    (prefixPartial 12 401682) = some ⟨12, 2, 0, 1364812, 401682, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_401682_1364812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401682 ⟨1364812, by decide⟩ :=
  accepted_of_selected 12 401682 ⟨1364812, by decide⟩ ⟨12, 2, 0, 1364812, 401682, 1769, 65536⟩
    (by decide) selected_cut_48621

theorem selected_cut_48622 : selected 9 ⟨1364849, by decide⟩
    (prefixPartial 12 401683) = some ⟨12, 2, 0, 1364849, 401683, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_401683_1364849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401683 ⟨1364849, by decide⟩ :=
  accepted_of_selected 12 401683 ⟨1364849, by decide⟩ ⟨12, 2, 0, 1364849, 401683, 1665, 65536⟩
    (by decide) selected_cut_48622

theorem unmarked_context_11_100420_1364850 : frontier 10 ⟨1364850, by decide⟩
    (prefixCache 11 100420) (prefixPartial 11 100420) = false := by
  decide +kernel

theorem node_context_11_100420_1364850 : EJMOriginalGlobalDAGData.nodes 10 ⟨1364850, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1364760, by decide⟩,⟨1364812, by decide⟩,⟨1364849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100420_1364850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100420 ⟨1364850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100420
    ⟨1364850, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1364760, by decide⟩,⟨1364812, by decide⟩,⟨1364849, by decide⟩]) unmarked_context_11_100420_1364850 node_context_11_100420_1364850
  intro a
  fin_cases a
  · exact context_12_401680_1108174
  · exact context_12_401681_1364760
  · exact context_12_401682_1364812
  · exact context_12_401683_1364849

theorem selected_cut_48623 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 100421) = some ⟨11, 1, 0, 451541, 100421, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100421_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100421 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 100421 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 100421, 1, 262144⟩
    (by decide) selected_cut_48623

theorem selected_cut_48624 : selected 10 ⟨1364934, by decide⟩
    (prefixPartial 11 100422) = some ⟨11, 2, 0, 1364934, 100422, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_100422_1364934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100422 ⟨1364934, by decide⟩ :=
  accepted_of_selected 11 100422 ⟨1364934, by decide⟩ ⟨11, 2, 0, 1364934, 100422, 3137, 262144⟩
    (by decide) selected_cut_48624

theorem selected_cut_48625 : selected 10 ⟨1365012, by decide⟩
    (prefixPartial 11 100423) = some ⟨11, 2, 0, 1365012, 100423, 3049, 262144⟩ := by
  decide +kernel

theorem context_11_100423_1365012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100423 ⟨1365012, by decide⟩ :=
  accepted_of_selected 11 100423 ⟨1365012, by decide⟩ ⟨11, 2, 0, 1365012, 100423, 3049, 262144⟩
    (by decide) selected_cut_48625

theorem unmarked_context_10_25105_1365013 : frontier 11 ⟨1365013, by decide⟩
    (prefixCache 10 25105) (prefixPartial 10 25105) = false := by
  decide +kernel

theorem node_context_10_25105_1365013 : EJMOriginalGlobalDAGData.nodes 11 ⟨1365013, by decide⟩ =
    .split (coordinate 10) (![⟨1364850, by decide⟩,⟨451541, by decide⟩,⟨1364934, by decide⟩,⟨1365012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25105_1365013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25105 ⟨1365013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25105
    ⟨1365013, by decide⟩ (by decide) (![⟨1364850, by decide⟩,⟨451541, by decide⟩,⟨1364934, by decide⟩,⟨1365012, by decide⟩]) unmarked_context_10_25105_1365013 node_context_10_25105_1365013
  intro a
  fin_cases a
  · exact context_11_100420_1364850
  · exact context_11_100421_451541
  · exact context_11_100422_1364934
  · exact context_11_100423_1365012

theorem selected_cut_48626 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 401696) = some ⟨12, 1, 0, 1108174, 401696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_401696_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401696 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 401696 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 401696, 1, 65536⟩
    (by decide) selected_cut_48626

theorem selected_cut_48627 : selected 9 ⟨1365066, by decide⟩
    (prefixPartial 12 401697) = some ⟨12, 2, 0, 1365066, 401697, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_401697_1365066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401697 ⟨1365066, by decide⟩ :=
  accepted_of_selected 12 401697 ⟨1365066, by decide⟩ ⟨12, 2, 0, 1365066, 401697, 1537, 65536⟩
    (by decide) selected_cut_48627

theorem selected_cut_48628 : selected 9 ⟨1365118, by decide⟩
    (prefixPartial 12 401698) = some ⟨12, 2, 0, 1365118, 401698, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_401698_1365118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401698 ⟨1365118, by decide⟩ :=
  accepted_of_selected 12 401698 ⟨1365118, by decide⟩ ⟨12, 2, 0, 1365118, 401698, 1477, 65536⟩
    (by decide) selected_cut_48628

theorem selected_cut_48629 : selected 9 ⟨1365156, by decide⟩
    (prefixPartial 12 401699) = some ⟨12, 2, 0, 1365156, 401699, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_401699_1365156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 401699 ⟨1365156, by decide⟩ :=
  accepted_of_selected 12 401699 ⟨1365156, by decide⟩ ⟨12, 2, 0, 1365156, 401699, 1429, 65536⟩
    (by decide) selected_cut_48629

theorem unmarked_context_11_100424_1365157 : frontier 10 ⟨1365157, by decide⟩
    (prefixCache 11 100424) (prefixPartial 11 100424) = false := by
  decide +kernel

theorem node_context_11_100424_1365157 : EJMOriginalGlobalDAGData.nodes 10 ⟨1365157, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1365066, by decide⟩,⟨1365118, by decide⟩,⟨1365156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100424_1365157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100424 ⟨1365157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100424
    ⟨1365157, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1365066, by decide⟩,⟨1365118, by decide⟩,⟨1365156, by decide⟩]) unmarked_context_11_100424_1365157 node_context_11_100424_1365157
  intro a
  fin_cases a
  · exact context_12_401696_1108174
  · exact context_12_401697_1365066
  · exact context_12_401698_1365118
  · exact context_12_401699_1365156

theorem selected_cut_48630 : selected 10 ⟨1365239, by decide⟩
    (prefixPartial 11 100425) = some ⟨11, 2, 0, 1365239, 100425, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_100425_1365239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100425 ⟨1365239, by decide⟩ :=
  accepted_of_selected 11 100425 ⟨1365239, by decide⟩ ⟨11, 2, 0, 1365239, 100425, 2873, 262144⟩
    (by decide) selected_cut_48630

theorem selected_cut_48631 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 100426) = some ⟨11, 1, 0, 479708, 100426, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100426_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100426 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 100426 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 100426, 1, 262144⟩
    (by decide) selected_cut_48631

theorem selected_cut_48632 : selected 10 ⟨1365331, by decide⟩
    (prefixPartial 11 100427) = some ⟨11, 2, 0, 1365331, 100427, 3905, 262144⟩ := by
  decide +kernel

theorem context_11_100427_1365331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100427 ⟨1365331, by decide⟩ :=
  accepted_of_selected 11 100427 ⟨1365331, by decide⟩ ⟨11, 2, 0, 1365331, 100427, 3905, 262144⟩
    (by decide) selected_cut_48632

theorem unmarked_context_10_25106_1365332 : frontier 11 ⟨1365332, by decide⟩
    (prefixCache 10 25106) (prefixPartial 10 25106) = false := by
  decide +kernel

theorem node_context_10_25106_1365332 : EJMOriginalGlobalDAGData.nodes 11 ⟨1365332, by decide⟩ =
    .split (coordinate 10) (![⟨1365157, by decide⟩,⟨1365239, by decide⟩,⟨479708, by decide⟩,⟨1365331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25106_1365332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25106 ⟨1365332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25106
    ⟨1365332, by decide⟩ (by decide) (![⟨1365157, by decide⟩,⟨1365239, by decide⟩,⟨479708, by decide⟩,⟨1365331, by decide⟩]) unmarked_context_10_25106_1365332 node_context_10_25106_1365332
  intro a
  fin_cases a
  · exact context_11_100424_1365157
  · exact context_11_100425_1365239
  · exact context_11_100426_479708
  · exact context_11_100427_1365331

theorem selected_cut_48633 : selected 10 ⟨1365447, by decide⟩
    (prefixPartial 11 100428) = some ⟨11, 2, 0, 1365447, 100428, 3781, 262144⟩ := by
  decide +kernel

theorem context_11_100428_1365447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100428 ⟨1365447, by decide⟩ :=
  accepted_of_selected 11 100428 ⟨1365447, by decide⟩ ⟨11, 2, 0, 1365447, 100428, 3781, 262144⟩
    (by decide) selected_cut_48633

theorem selected_cut_48634 : selected 10 ⟨1365519, by decide⟩
    (prefixPartial 11 100429) = some ⟨11, 2, 0, 1365519, 100429, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_100429_1365519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100429 ⟨1365519, by decide⟩ :=
  accepted_of_selected 11 100429 ⟨1365519, by decide⟩ ⟨11, 2, 0, 1365519, 100429, 2449, 262144⟩
    (by decide) selected_cut_48634

theorem selected_cut_48635 : selected 10 ⟨1365602, by decide⟩
    (prefixPartial 11 100430) = some ⟨11, 2, 0, 1365602, 100430, 3189, 262144⟩ := by
  decide +kernel

theorem context_11_100430_1365602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100430 ⟨1365602, by decide⟩ :=
  accepted_of_selected 11 100430 ⟨1365602, by decide⟩ ⟨11, 2, 0, 1365602, 100430, 3189, 262144⟩
    (by decide) selected_cut_48635

theorem selected_cut_48636 : selected 10 ⟨612961, by decide⟩
    (prefixPartial 11 100431) = some ⟨11, 1, 0, 612961, 100431, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100431_612961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100431 ⟨612961, by decide⟩ :=
  accepted_of_selected 11 100431 ⟨612961, by decide⟩ ⟨11, 1, 0, 612961, 100431, 1, 262144⟩
    (by decide) selected_cut_48636

theorem unmarked_context_10_25107_1365603 : frontier 11 ⟨1365603, by decide⟩
    (prefixCache 10 25107) (prefixPartial 10 25107) = false := by
  decide +kernel

theorem node_context_10_25107_1365603 : EJMOriginalGlobalDAGData.nodes 11 ⟨1365603, by decide⟩ =
    .split (coordinate 10) (![⟨1365447, by decide⟩,⟨1365519, by decide⟩,⟨1365602, by decide⟩,⟨612961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25107_1365603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25107 ⟨1365603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25107
    ⟨1365603, by decide⟩ (by decide) (![⟨1365447, by decide⟩,⟨1365519, by decide⟩,⟨1365602, by decide⟩,⟨612961, by decide⟩]) unmarked_context_10_25107_1365603 node_context_10_25107_1365603
  intro a
  fin_cases a
  · exact context_11_100428_1365447
  · exact context_11_100429_1365519
  · exact context_11_100430_1365602
  · exact context_11_100431_612961

theorem unmarked_context_9_6276_1365604 : frontier 12 ⟨1365604, by decide⟩
    (prefixCache 9 6276) (prefixPartial 9 6276) = false := by
  decide +kernel

theorem node_context_9_6276_1365604 : EJMOriginalGlobalDAGData.nodes 12 ⟨1365604, by decide⟩ =
    .split (coordinate 9) (![⟨1364693, by decide⟩,⟨1365013, by decide⟩,⟨1365332, by decide⟩,⟨1365603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6276_1365604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6276 ⟨1365604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6276
    ⟨1365604, by decide⟩ (by decide) (![⟨1364693, by decide⟩,⟨1365013, by decide⟩,⟨1365332, by decide⟩,⟨1365603, by decide⟩]) unmarked_context_9_6276_1365604 node_context_9_6276_1365604
  intro a
  fin_cases a
  · exact context_10_25104_1364693
  · exact context_10_25105_1365013
  · exact context_10_25106_1365332
  · exact context_10_25107_1365603

theorem selected_cut_48637 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 25108) = some ⟨10, 1, 0, 3442, 25108, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25108_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25108 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 25108 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 25108, 1, 1048576⟩
    (by decide) selected_cut_48637

theorem selected_cut_48638 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25109) = some ⟨10, 1, 0, 893098, 25109, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25109_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25109 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25109 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25109, 1, 1048576⟩
    (by decide) selected_cut_48638

theorem selected_cut_48639 : selected 10 ⟨1365677, by decide⟩
    (prefixPartial 11 100440) = some ⟨11, 2, 0, 1365677, 100440, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_100440_1365677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100440 ⟨1365677, by decide⟩ :=
  accepted_of_selected 11 100440 ⟨1365677, by decide⟩ ⟨11, 2, 0, 1365677, 100440, 1929, 262144⟩
    (by decide) selected_cut_48639

theorem selected_cut_48640 : selected 10 ⟨1365758, by decide⟩
    (prefixPartial 11 100441) = some ⟨11, 2, 0, 1365758, 100441, 2689, 262144⟩ := by
  decide +kernel

theorem context_11_100441_1365758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100441 ⟨1365758, by decide⟩ :=
  accepted_of_selected 11 100441 ⟨1365758, by decide⟩ ⟨11, 2, 0, 1365758, 100441, 2689, 262144⟩
    (by decide) selected_cut_48640

theorem selected_cut_48641 : selected 10 ⟨1365819, by decide⟩
    (prefixPartial 11 100442) = some ⟨11, 2, 0, 1365819, 100442, 1305, 262144⟩ := by
  decide +kernel

theorem context_11_100442_1365819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100442 ⟨1365819, by decide⟩ :=
  accepted_of_selected 11 100442 ⟨1365819, by decide⟩ ⟨11, 2, 0, 1365819, 100442, 1305, 262144⟩
    (by decide) selected_cut_48641

theorem selected_cut_48642 : selected 10 ⟨1365905, by decide⟩
    (prefixPartial 11 100443) = some ⟨11, 2, 0, 1365905, 100443, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_100443_1365905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100443 ⟨1365905, by decide⟩ :=
  accepted_of_selected 11 100443 ⟨1365905, by decide⟩ ⟨11, 2, 0, 1365905, 100443, 2385, 262144⟩
    (by decide) selected_cut_48642

theorem unmarked_context_10_25110_1365906 : frontier 11 ⟨1365906, by decide⟩
    (prefixCache 10 25110) (prefixPartial 10 25110) = false := by
  decide +kernel

theorem node_context_10_25110_1365906 : EJMOriginalGlobalDAGData.nodes 11 ⟨1365906, by decide⟩ =
    .split (coordinate 10) (![⟨1365677, by decide⟩,⟨1365758, by decide⟩,⟨1365819, by decide⟩,⟨1365905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25110_1365906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25110 ⟨1365906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25110
    ⟨1365906, by decide⟩ (by decide) (![⟨1365677, by decide⟩,⟨1365758, by decide⟩,⟨1365819, by decide⟩,⟨1365905, by decide⟩]) unmarked_context_10_25110_1365906 node_context_10_25110_1365906
  intro a
  fin_cases a
  · exact context_11_100440_1365677
  · exact context_11_100441_1365758
  · exact context_11_100442_1365819
  · exact context_11_100443_1365905

theorem selected_cut_48643 : selected 10 ⟨1365945, by decide⟩
    (prefixPartial 11 100444) = some ⟨11, 2, 0, 1365945, 100444, 1341, 262144⟩ := by
  decide +kernel

theorem context_11_100444_1365945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100444 ⟨1365945, by decide⟩ :=
  accepted_of_selected 11 100444 ⟨1365945, by decide⟩ ⟨11, 2, 0, 1365945, 100444, 1341, 262144⟩
    (by decide) selected_cut_48643

theorem selected_cut_48644 : selected 10 ⟨1366009, by decide⟩
    (prefixPartial 11 100445) = some ⟨11, 2, 0, 1366009, 100445, 1853, 262144⟩ := by
  decide +kernel

theorem context_11_100445_1366009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100445 ⟨1366009, by decide⟩ :=
  accepted_of_selected 11 100445 ⟨1366009, by decide⟩ ⟨11, 2, 0, 1366009, 100445, 1853, 262144⟩
    (by decide) selected_cut_48644

theorem selected_cut_48645 : selected 10 ⟨1366069, by decide⟩
    (prefixPartial 11 100446) = some ⟨11, 2, 0, 1366069, 100446, 1649, 262144⟩ := by
  decide +kernel

theorem context_11_100446_1366069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100446 ⟨1366069, by decide⟩ :=
  accepted_of_selected 11 100446 ⟨1366069, by decide⟩ ⟨11, 2, 0, 1366069, 100446, 1649, 262144⟩
    (by decide) selected_cut_48645

theorem selected_cut_48646 : selected 10 ⟨1366090, by decide⟩
    (prefixPartial 11 100447) = some ⟨11, 2, 0, 1366090, 100447, 625, 262144⟩ := by
  decide +kernel

theorem context_11_100447_1366090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100447 ⟨1366090, by decide⟩ :=
  accepted_of_selected 11 100447 ⟨1366090, by decide⟩ ⟨11, 2, 0, 1366090, 100447, 625, 262144⟩
    (by decide) selected_cut_48646

theorem unmarked_context_10_25111_1366091 : frontier 11 ⟨1366091, by decide⟩
    (prefixCache 10 25111) (prefixPartial 10 25111) = false := by
  decide +kernel

theorem node_context_10_25111_1366091 : EJMOriginalGlobalDAGData.nodes 11 ⟨1366091, by decide⟩ =
    .split (coordinate 10) (![⟨1365945, by decide⟩,⟨1366009, by decide⟩,⟨1366069, by decide⟩,⟨1366090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25111_1366091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25111 ⟨1366091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25111
    ⟨1366091, by decide⟩ (by decide) (![⟨1365945, by decide⟩,⟨1366009, by decide⟩,⟨1366069, by decide⟩,⟨1366090, by decide⟩]) unmarked_context_10_25111_1366091 node_context_10_25111_1366091
  intro a
  fin_cases a
  · exact context_11_100444_1365945
  · exact context_11_100445_1366009
  · exact context_11_100446_1366069
  · exact context_11_100447_1366090

theorem unmarked_context_9_6277_1366092 : frontier 12 ⟨1366092, by decide⟩
    (prefixCache 9 6277) (prefixPartial 9 6277) = false := by
  decide +kernel

theorem node_context_9_6277_1366092 : EJMOriginalGlobalDAGData.nodes 12 ⟨1366092, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1365906, by decide⟩,⟨1366091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6277_1366092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6277 ⟨1366092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6277
    ⟨1366092, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1365906, by decide⟩,⟨1366091, by decide⟩]) unmarked_context_9_6277_1366092 node_context_9_6277_1366092
  intro a
  fin_cases a
  · exact context_10_25108_3442
  · exact context_10_25109_893098
  · exact context_10_25110_1365906
  · exact context_10_25111_1366091

theorem selected_cut_48647 : selected 12 ⟨1366222, by decide⟩
    (prefixPartial 9 6278) = some ⟨9, 2, 0, 1366222, 6278, 3053, 4194304⟩ := by
  decide +kernel

theorem context_9_6278_1366222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6278 ⟨1366222, by decide⟩ :=
  accepted_of_selected 9 6278 ⟨1366222, by decide⟩ ⟨9, 2, 0, 1366222, 6278, 3053, 4194304⟩
    (by decide) selected_cut_48647

theorem selected_cut_48648 : selected 12 ⟨1366233, by decide⟩
    (prefixPartial 9 6279) = some ⟨9, 2, 0, 1366233, 6279, 109, 4194304⟩ := by
  decide +kernel

theorem context_9_6279_1366233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6279 ⟨1366233, by decide⟩ :=
  accepted_of_selected 9 6279 ⟨1366233, by decide⟩ ⟨9, 2, 0, 1366233, 6279, 109, 4194304⟩
    (by decide) selected_cut_48648

theorem unmarked_context_8_1569_1366234 : frontier 13 ⟨1366234, by decide⟩
    (prefixCache 8 1569) (prefixPartial 8 1569) = false := by
  decide +kernel

theorem node_context_8_1569_1366234 : EJMOriginalGlobalDAGData.nodes 13 ⟨1366234, by decide⟩ =
    .split (coordinate 8) (![⟨1365604, by decide⟩,⟨1366092, by decide⟩,⟨1366222, by decide⟩,⟨1366233, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1569_1366234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1569 ⟨1366234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1569
    ⟨1366234, by decide⟩ (by decide) (![⟨1365604, by decide⟩,⟨1366092, by decide⟩,⟨1366222, by decide⟩,⟨1366233, by decide⟩]) unmarked_context_8_1569_1366234 node_context_8_1569_1366234
  intro a
  fin_cases a
  · exact context_9_6276_1365604
  · exact context_9_6277_1366092
  · exact context_9_6278_1366222
  · exact context_9_6279_1366233

theorem selected_cut_48649 : selected 13 ⟨1366235, by decide⟩
    (prefixPartial 8 1570) = some ⟨8, 1, 0, 1366235, 1570, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1570_1366235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1570 ⟨1366235, by decide⟩ :=
  accepted_of_selected 8 1570 ⟨1366235, by decide⟩ ⟨8, 1, 0, 1366235, 1570, 1, 16777216⟩
    (by decide) selected_cut_48649

theorem selected_cut_48650 : selected 11 ⟨1366335, by decide⟩
    (prefixPartial 10 25136) = some ⟨10, 2, 0, 1366335, 25136, 2725, 1048576⟩ := by
  decide +kernel

theorem context_10_25136_1366335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25136 ⟨1366335, by decide⟩ :=
  accepted_of_selected 10 25136 ⟨1366335, by decide⟩ ⟨10, 2, 0, 1366335, 25136, 2725, 1048576⟩
    (by decide) selected_cut_48650

theorem selected_cut_48651 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402192) = some ⟨12, 1, 0, 1108174, 402192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402192_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402192 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402192 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402192, 1, 65536⟩
    (by decide) selected_cut_48651

theorem selected_cut_48652 : selected 9 ⟨1366386, by decide⟩
    (prefixPartial 12 402193) = some ⟨12, 2, 0, 1366386, 402193, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_402193_1366386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402193 ⟨1366386, by decide⟩ :=
  accepted_of_selected 12 402193 ⟨1366386, by decide⟩ ⟨12, 2, 0, 1366386, 402193, 2085, 65536⟩
    (by decide) selected_cut_48652

theorem selected_cut_48653 : selected 9 ⟨1366450, by decide⟩
    (prefixPartial 12 402194) = some ⟨12, 2, 0, 1366450, 402194, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_402194_1366450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402194 ⟨1366450, by decide⟩ :=
  accepted_of_selected 12 402194 ⟨1366450, by decide⟩ ⟨12, 2, 0, 1366450, 402194, 1997, 65536⟩
    (by decide) selected_cut_48653

theorem selected_cut_48654 : selected 9 ⟨1366492, by decide⟩
    (prefixPartial 12 402195) = some ⟨12, 2, 0, 1366492, 402195, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_402195_1366492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402195 ⟨1366492, by decide⟩ :=
  accepted_of_selected 12 402195 ⟨1366492, by decide⟩ ⟨12, 2, 0, 1366492, 402195, 1873, 65536⟩
    (by decide) selected_cut_48654

theorem unmarked_context_11_100548_1366493 : frontier 10 ⟨1366493, by decide⟩
    (prefixCache 11 100548) (prefixPartial 11 100548) = false := by
  decide +kernel

theorem node_context_11_100548_1366493 : EJMOriginalGlobalDAGData.nodes 10 ⟨1366493, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1366386, by decide⟩,⟨1366450, by decide⟩,⟨1366492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100548_1366493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100548 ⟨1366493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100548
    ⟨1366493, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1366386, by decide⟩,⟨1366450, by decide⟩,⟨1366492, by decide⟩]) unmarked_context_11_100548_1366493 node_context_11_100548_1366493
  intro a
  fin_cases a
  · exact context_12_402192_1108174
  · exact context_12_402193_1366386
  · exact context_12_402194_1366450
  · exact context_12_402195_1366492

theorem selected_cut_48655 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 100549) = some ⟨11, 1, 0, 451541, 100549, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100549_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100549 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 100549 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 100549, 1, 262144⟩
    (by decide) selected_cut_48655

theorem selected_cut_48656 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402200) = some ⟨12, 1, 0, 1108174, 402200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402200_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402200 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402200 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402200, 1, 65536⟩
    (by decide) selected_cut_48656

theorem selected_cut_48657 : selected 9 ⟨1366539, by decide⟩
    (prefixPartial 12 402201) = some ⟨12, 2, 0, 1366539, 402201, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_402201_1366539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402201 ⟨1366539, by decide⟩ :=
  accepted_of_selected 12 402201 ⟨1366539, by decide⟩ ⟨12, 2, 0, 1366539, 402201, 1905, 65536⟩
    (by decide) selected_cut_48657

theorem selected_cut_48658 : selected 9 ⟨1366579, by decide⟩
    (prefixPartial 12 402202) = some ⟨12, 2, 0, 1366579, 402202, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_402202_1366579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402202 ⟨1366579, by decide⟩ :=
  accepted_of_selected 12 402202 ⟨1366579, by decide⟩ ⟨12, 2, 0, 1366579, 402202, 1769, 65536⟩
    (by decide) selected_cut_48658

theorem selected_cut_48659 : selected 9 ⟨1366615, by decide⟩
    (prefixPartial 12 402203) = some ⟨12, 2, 0, 1366615, 402203, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_402203_1366615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402203 ⟨1366615, by decide⟩ :=
  accepted_of_selected 12 402203 ⟨1366615, by decide⟩ ⟨12, 2, 0, 1366615, 402203, 1745, 65536⟩
    (by decide) selected_cut_48659

theorem unmarked_context_11_100550_1366616 : frontier 10 ⟨1366616, by decide⟩
    (prefixCache 11 100550) (prefixPartial 11 100550) = false := by
  decide +kernel

theorem node_context_11_100550_1366616 : EJMOriginalGlobalDAGData.nodes 10 ⟨1366616, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1366539, by decide⟩,⟨1366579, by decide⟩,⟨1366615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100550_1366616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100550 ⟨1366616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100550
    ⟨1366616, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1366539, by decide⟩,⟨1366579, by decide⟩,⟨1366615, by decide⟩]) unmarked_context_11_100550_1366616 node_context_11_100550_1366616
  intro a
  fin_cases a
  · exact context_12_402200_1108174
  · exact context_12_402201_1366539
  · exact context_12_402202_1366579
  · exact context_12_402203_1366615

theorem selected_cut_48660 : selected 10 ⟨1366708, by decide⟩
    (prefixPartial 11 100551) = some ⟨11, 2, 0, 1366708, 100551, 3597, 262144⟩ := by
  decide +kernel

theorem context_11_100551_1366708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100551 ⟨1366708, by decide⟩ :=
  accepted_of_selected 11 100551 ⟨1366708, by decide⟩ ⟨11, 2, 0, 1366708, 100551, 3597, 262144⟩
    (by decide) selected_cut_48660

theorem unmarked_context_10_25137_1366709 : frontier 11 ⟨1366709, by decide⟩
    (prefixCache 10 25137) (prefixPartial 10 25137) = false := by
  decide +kernel

theorem node_context_10_25137_1366709 : EJMOriginalGlobalDAGData.nodes 11 ⟨1366709, by decide⟩ =
    .split (coordinate 10) (![⟨1366493, by decide⟩,⟨451541, by decide⟩,⟨1366616, by decide⟩,⟨1366708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25137_1366709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25137 ⟨1366709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25137
    ⟨1366709, by decide⟩ (by decide) (![⟨1366493, by decide⟩,⟨451541, by decide⟩,⟨1366616, by decide⟩,⟨1366708, by decide⟩]) unmarked_context_10_25137_1366709 node_context_10_25137_1366709
  intro a
  fin_cases a
  · exact context_11_100548_1366493
  · exact context_11_100549_451541
  · exact context_11_100550_1366616
  · exact context_11_100551_1366708

theorem selected_cut_48661 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402208) = some ⟨12, 1, 0, 1108174, 402208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402208_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402208 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402208 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402208, 1, 65536⟩
    (by decide) selected_cut_48661

theorem selected_cut_48662 : selected 9 ⟨1366743, by decide⟩
    (prefixPartial 12 402209) = some ⟨12, 2, 0, 1366743, 402209, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_402209_1366743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402209 ⟨1366743, by decide⟩ :=
  accepted_of_selected 12 402209 ⟨1366743, by decide⟩ ⟨12, 2, 0, 1366743, 402209, 1653, 65536⟩
    (by decide) selected_cut_48662

theorem selected_cut_48663 : selected 9 ⟨1366776, by decide⟩
    (prefixPartial 12 402210) = some ⟨12, 2, 0, 1366776, 402210, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_402210_1366776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402210 ⟨1366776, by decide⟩ :=
  accepted_of_selected 12 402210 ⟨1366776, by decide⟩ ⟨12, 2, 0, 1366776, 402210, 1517, 65536⟩
    (by decide) selected_cut_48663

theorem selected_cut_48664 : selected 9 ⟨1366811, by decide⟩
    (prefixPartial 12 402211) = some ⟨12, 2, 0, 1366811, 402211, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_402211_1366811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402211 ⟨1366811, by decide⟩ :=
  accepted_of_selected 12 402211 ⟨1366811, by decide⟩ ⟨12, 2, 0, 1366811, 402211, 1465, 65536⟩
    (by decide) selected_cut_48664

theorem unmarked_context_11_100552_1366812 : frontier 10 ⟨1366812, by decide⟩
    (prefixCache 11 100552) (prefixPartial 11 100552) = false := by
  decide +kernel

theorem node_context_11_100552_1366812 : EJMOriginalGlobalDAGData.nodes 10 ⟨1366812, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1366743, by decide⟩,⟨1366776, by decide⟩,⟨1366811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100552_1366812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100552 ⟨1366812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100552
    ⟨1366812, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1366743, by decide⟩,⟨1366776, by decide⟩,⟨1366811, by decide⟩]) unmarked_context_11_100552_1366812 node_context_11_100552_1366812
  intro a
  fin_cases a
  · exact context_12_402208_1108174
  · exact context_12_402209_1366743
  · exact context_12_402210_1366776
  · exact context_12_402211_1366811

theorem selected_cut_48665 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402212) = some ⟨12, 1, 0, 1108174, 402212, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402212_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402212 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402212 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402212, 1, 65536⟩
    (by decide) selected_cut_48665

theorem selected_cut_48666 : selected 9 ⟨1366848, by decide⟩
    (prefixPartial 12 402213) = some ⟨12, 2, 0, 1366848, 402213, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_402213_1366848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402213 ⟨1366848, by decide⟩ :=
  accepted_of_selected 12 402213 ⟨1366848, by decide⟩ ⟨12, 2, 0, 1366848, 402213, 1433, 65536⟩
    (by decide) selected_cut_48666

theorem selected_cut_48667 : selected 9 ⟨1366876, by decide⟩
    (prefixPartial 12 402214) = some ⟨12, 2, 0, 1366876, 402214, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_402214_1366876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402214 ⟨1366876, by decide⟩ :=
  accepted_of_selected 12 402214 ⟨1366876, by decide⟩ ⟨12, 2, 0, 1366876, 402214, 1357, 65536⟩
    (by decide) selected_cut_48667

theorem selected_cut_48668 : selected 9 ⟨1366901, by decide⟩
    (prefixPartial 12 402215) = some ⟨12, 2, 0, 1366901, 402215, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_402215_1366901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402215 ⟨1366901, by decide⟩ :=
  accepted_of_selected 12 402215 ⟨1366901, by decide⟩ ⟨12, 2, 0, 1366901, 402215, 1309, 65536⟩
    (by decide) selected_cut_48668

theorem unmarked_context_11_100553_1366902 : frontier 10 ⟨1366902, by decide⟩
    (prefixCache 11 100553) (prefixPartial 11 100553) = false := by
  decide +kernel

theorem node_context_11_100553_1366902 : EJMOriginalGlobalDAGData.nodes 10 ⟨1366902, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1366848, by decide⟩,⟨1366876, by decide⟩,⟨1366901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100553_1366902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100553 ⟨1366902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100553
    ⟨1366902, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1366848, by decide⟩,⟨1366876, by decide⟩,⟨1366901, by decide⟩]) unmarked_context_11_100553_1366902 node_context_11_100553_1366902
  intro a
  fin_cases a
  · exact context_12_402212_1108174
  · exact context_12_402213_1366848
  · exact context_12_402214_1366876
  · exact context_12_402215_1366901

theorem selected_cut_48669 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 100554) = some ⟨11, 1, 0, 479708, 100554, 1, 262144⟩ := by
  decide +kernel

theorem context_11_100554_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100554 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 100554 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 100554, 1, 262144⟩
    (by decide) selected_cut_48669

theorem selected_cut_48670 : selected 10 ⟨1366959, by decide⟩
    (prefixPartial 11 100555) = some ⟨11, 2, 0, 1366959, 100555, 2661, 262144⟩ := by
  decide +kernel

theorem context_11_100555_1366959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100555 ⟨1366959, by decide⟩ :=
  accepted_of_selected 11 100555 ⟨1366959, by decide⟩ ⟨11, 2, 0, 1366959, 100555, 2661, 262144⟩
    (by decide) selected_cut_48670

theorem unmarked_context_10_25138_1366960 : frontier 11 ⟨1366960, by decide⟩
    (prefixCache 10 25138) (prefixPartial 10 25138) = false := by
  decide +kernel

theorem node_context_10_25138_1366960 : EJMOriginalGlobalDAGData.nodes 11 ⟨1366960, by decide⟩ =
    .split (coordinate 10) (![⟨1366812, by decide⟩,⟨1366902, by decide⟩,⟨479708, by decide⟩,⟨1366959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25138_1366960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25138 ⟨1366960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25138
    ⟨1366960, by decide⟩ (by decide) (![⟨1366812, by decide⟩,⟨1366902, by decide⟩,⟨479708, by decide⟩,⟨1366959, by decide⟩]) unmarked_context_10_25138_1366960 node_context_10_25138_1366960
  intro a
  fin_cases a
  · exact context_11_100552_1366812
  · exact context_11_100553_1366902
  · exact context_11_100554_479708
  · exact context_11_100555_1366959

theorem selected_cut_48671 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 402224) = some ⟨12, 1, 0, 1108174, 402224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_402224_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402224 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 402224 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 402224, 1, 65536⟩
    (by decide) selected_cut_48671

theorem selected_cut_48672 : selected 9 ⟨1367004, by decide⟩
    (prefixPartial 12 402225) = some ⟨12, 2, 0, 1367004, 402225, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_402225_1367004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402225 ⟨1367004, by decide⟩ :=
  accepted_of_selected 12 402225 ⟨1367004, by decide⟩ ⟨12, 2, 0, 1367004, 402225, 1501, 65536⟩
    (by decide) selected_cut_48672

theorem selected_cut_48673 : selected 9 ⟨1367038, by decide⟩
    (prefixPartial 12 402226) = some ⟨12, 2, 0, 1367038, 402226, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_402226_1367038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402226 ⟨1367038, by decide⟩ :=
  accepted_of_selected 12 402226 ⟨1367038, by decide⟩ ⟨12, 2, 0, 1367038, 402226, 1349, 65536⟩
    (by decide) selected_cut_48673

theorem selected_cut_48674 : selected 9 ⟨1367068, by decide⟩
    (prefixPartial 12 402227) = some ⟨12, 2, 0, 1367068, 402227, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_402227_1367068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 402227 ⟨1367068, by decide⟩ :=
  accepted_of_selected 12 402227 ⟨1367068, by decide⟩ ⟨12, 2, 0, 1367068, 402227, 1245, 65536⟩
    (by decide) selected_cut_48674

theorem unmarked_context_11_100556_1367069 : frontier 10 ⟨1367069, by decide⟩
    (prefixCache 11 100556) (prefixPartial 11 100556) = false := by
  decide +kernel

theorem node_context_11_100556_1367069 : EJMOriginalGlobalDAGData.nodes 10 ⟨1367069, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1367004, by decide⟩,⟨1367038, by decide⟩,⟨1367068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_100556_1367069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 100556 ⟨1367069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 100556
    ⟨1367069, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1367004, by decide⟩,⟨1367038, by decide⟩,⟨1367068, by decide⟩]) unmarked_context_11_100556_1367069 node_context_11_100556_1367069
  intro a
  fin_cases a
  · exact context_12_402224_1108174
  · exact context_12_402225_1367004
  · exact context_12_402226_1367038
  · exact context_12_402227_1367068

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
