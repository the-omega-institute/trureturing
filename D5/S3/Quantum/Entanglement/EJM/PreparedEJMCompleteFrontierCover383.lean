/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover382
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_18162_977679 : frontier 11 ⟨977679, by decide⟩
    (prefixCache 10 18162) (prefixPartial 10 18162) = false := by
  decide +kernel

theorem node_context_10_18162_977679 : EJMOriginalGlobalDAGData.nodes 11 ⟨977679, by decide⟩ =
    .split (coordinate 10) (![⟨977307, by decide⟩,⟨977443, by decide⟩,⟨977612, by decide⟩,⟨977678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18162_977679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18162 ⟨977679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18162
    ⟨977679, by decide⟩ (by decide) (![⟨977307, by decide⟩,⟨977443, by decide⟩,⟨977612, by decide⟩,⟨977678, by decide⟩]) unmarked_context_10_18162_977679 node_context_10_18162_977679
  intro a
  fin_cases a
  · exact context_11_72648_977307
  · exact context_11_72649_977443
  · exact context_11_72650_977612
  · exact context_11_72651_977678

theorem selected_cut_36772 : selected 10 ⟨977758, by decide⟩
    (prefixPartial 11 72652) = some ⟨11, 2, 0, 977758, 72652, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_72652_977758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72652 ⟨977758, by decide⟩ :=
  accepted_of_selected 11 72652 ⟨977758, by decide⟩ ⟨11, 2, 0, 977758, 72652, 2057, 262144⟩
    (by decide) selected_cut_36772

theorem selected_cut_36773 : selected 10 ⟨977817, by decide⟩
    (prefixPartial 11 72653) = some ⟨11, 2, 0, 977817, 72653, 1909, 262144⟩ := by
  decide +kernel

theorem context_11_72653_977817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72653 ⟨977817, by decide⟩ :=
  accepted_of_selected 11 72653 ⟨977817, by decide⟩ ⟨11, 2, 0, 977817, 72653, 1909, 262144⟩
    (by decide) selected_cut_36773

theorem selected_cut_36774 : selected 10 ⟨977885, by decide⟩
    (prefixPartial 11 72654) = some ⟨11, 2, 0, 977885, 72654, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_72654_977885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72654 ⟨977885, by decide⟩ :=
  accepted_of_selected 11 72654 ⟨977885, by decide⟩ ⟨11, 2, 0, 977885, 72654, 2149, 262144⟩
    (by decide) selected_cut_36774

theorem selected_cut_36775 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 72655) = some ⟨11, 1, 0, 977886, 72655, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72655_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72655 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 72655 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 72655, 1, 262144⟩
    (by decide) selected_cut_36775

theorem unmarked_context_10_18163_977887 : frontier 11 ⟨977887, by decide⟩
    (prefixCache 10 18163) (prefixPartial 10 18163) = false := by
  decide +kernel

theorem node_context_10_18163_977887 : EJMOriginalGlobalDAGData.nodes 11 ⟨977887, by decide⟩ =
    .split (coordinate 10) (![⟨977758, by decide⟩,⟨977817, by decide⟩,⟨977885, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18163_977887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18163 ⟨977887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18163
    ⟨977887, by decide⟩ (by decide) (![⟨977758, by decide⟩,⟨977817, by decide⟩,⟨977885, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18163_977887 node_context_10_18163_977887
  intro a
  fin_cases a
  · exact context_11_72652_977758
  · exact context_11_72653_977817
  · exact context_11_72654_977885
  · exact context_11_72655_977886

theorem unmarked_context_9_4540_977888 : frontier 12 ⟨977888, by decide⟩
    (prefixCache 9 4540) (prefixPartial 9 4540) = false := by
  decide +kernel

theorem node_context_9_4540_977888 : EJMOriginalGlobalDAGData.nodes 12 ⟨977888, by decide⟩ =
    .split (coordinate 9) (![⟨976273, by decide⟩,⟨977138, by decide⟩,⟨977679, by decide⟩,⟨977887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4540_977888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4540 ⟨977888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4540
    ⟨977888, by decide⟩ (by decide) (![⟨976273, by decide⟩,⟨977138, by decide⟩,⟨977679, by decide⟩,⟨977887, by decide⟩]) unmarked_context_9_4540_977888 node_context_9_4540_977888
  intro a
  fin_cases a
  · exact context_10_18160_976273
  · exact context_10_18161_977138
  · exact context_10_18162_977679
  · exact context_10_18163_977887

theorem selected_cut_36776 : selected 9 ⟨977889, by decide⟩
    (prefixPartial 12 290624) = some ⟨12, 1, 0, 977889, 290624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290624_977889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290624 ⟨977889, by decide⟩ :=
  accepted_of_selected 12 290624 ⟨977889, by decide⟩ ⟨12, 1, 0, 977889, 290624, 1, 65536⟩
    (by decide) selected_cut_36776

theorem selected_cut_36777 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 290625) = some ⟨12, 1, 0, 896706, 290625, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290625_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290625 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 290625 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 290625, 1, 65536⟩
    (by decide) selected_cut_36777

theorem selected_cut_36778 : selected 9 ⟨977951, by decide⟩
    (prefixPartial 12 290626) = some ⟨12, 2, 0, 977951, 290626, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_290626_977951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290626 ⟨977951, by decide⟩ :=
  accepted_of_selected 12 290626 ⟨977951, by decide⟩ ⟨12, 2, 0, 977951, 290626, 2785, 65536⟩
    (by decide) selected_cut_36778

theorem selected_cut_36779 : selected 9 ⟨978008, by decide⟩
    (prefixPartial 12 290627) = some ⟨12, 2, 0, 978008, 290627, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_290627_978008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290627 ⟨978008, by decide⟩ :=
  accepted_of_selected 12 290627 ⟨978008, by decide⟩ ⟨12, 2, 0, 978008, 290627, 2789, 65536⟩
    (by decide) selected_cut_36779

theorem unmarked_context_11_72656_978009 : frontier 10 ⟨978009, by decide⟩
    (prefixCache 11 72656) (prefixPartial 11 72656) = false := by
  decide +kernel

theorem node_context_11_72656_978009 : EJMOriginalGlobalDAGData.nodes 10 ⟨978009, by decide⟩ =
    .split (coordinate 11) (![⟨977889, by decide⟩,⟨896706, by decide⟩,⟨977951, by decide⟩,⟨978008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72656_978009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72656 ⟨978009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72656
    ⟨978009, by decide⟩ (by decide) (![⟨977889, by decide⟩,⟨896706, by decide⟩,⟨977951, by decide⟩,⟨978008, by decide⟩]) unmarked_context_11_72656_978009 node_context_11_72656_978009
  intro a
  fin_cases a
  · exact context_12_290624_977889
  · exact context_12_290625_896706
  · exact context_12_290626_977951
  · exact context_12_290627_978008

theorem selected_cut_36780 : selected 9 ⟨978071, by decide⟩
    (prefixPartial 12 290628) = some ⟨12, 2, 0, 978071, 290628, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_290628_978071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290628 ⟨978071, by decide⟩ :=
  accepted_of_selected 12 290628 ⟨978071, by decide⟩ ⟨12, 2, 0, 978071, 290628, 2005, 65536⟩
    (by decide) selected_cut_36780

theorem selected_cut_36781 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 290629) = some ⟨12, 1, 0, 896706, 290629, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290629_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290629 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 290629 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 290629, 1, 65536⟩
    (by decide) selected_cut_36781

theorem selected_cut_36782 : selected 9 ⟨978122, by decide⟩
    (prefixPartial 12 290630) = some ⟨12, 2, 0, 978122, 290630, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_290630_978122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290630 ⟨978122, by decide⟩ :=
  accepted_of_selected 12 290630 ⟨978122, by decide⟩ ⟨12, 2, 0, 978122, 290630, 2297, 65536⟩
    (by decide) selected_cut_36782

theorem selected_cut_36783 : selected 9 ⟨978173, by decide⟩
    (prefixPartial 12 290631) = some ⟨12, 2, 0, 978173, 290631, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_290631_978173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290631 ⟨978173, by decide⟩ :=
  accepted_of_selected 12 290631 ⟨978173, by decide⟩ ⟨12, 2, 0, 978173, 290631, 2361, 65536⟩
    (by decide) selected_cut_36783

theorem unmarked_context_11_72657_978174 : frontier 10 ⟨978174, by decide⟩
    (prefixCache 11 72657) (prefixPartial 11 72657) = false := by
  decide +kernel

theorem node_context_11_72657_978174 : EJMOriginalGlobalDAGData.nodes 10 ⟨978174, by decide⟩ =
    .split (coordinate 11) (![⟨978071, by decide⟩,⟨896706, by decide⟩,⟨978122, by decide⟩,⟨978173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72657_978174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72657 ⟨978174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72657
    ⟨978174, by decide⟩ (by decide) (![⟨978071, by decide⟩,⟨896706, by decide⟩,⟨978122, by decide⟩,⟨978173, by decide⟩]) unmarked_context_11_72657_978174 node_context_11_72657_978174
  intro a
  fin_cases a
  · exact context_12_290628_978071
  · exact context_12_290629_896706
  · exact context_12_290630_978122
  · exact context_12_290631_978173

theorem selected_cut_36784 : selected 9 ⟨978241, by decide⟩
    (prefixPartial 12 290632) = some ⟨12, 2, 0, 978241, 290632, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_290632_978241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290632 ⟨978241, by decide⟩ :=
  accepted_of_selected 12 290632 ⟨978241, by decide⟩ ⟨12, 2, 0, 978241, 290632, 2157, 65536⟩
    (by decide) selected_cut_36784

theorem selected_cut_36785 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 290633) = some ⟨12, 1, 0, 896706, 290633, 1, 65536⟩ := by
  decide +kernel

theorem context_12_290633_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290633 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 290633 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 290633, 1, 65536⟩
    (by decide) selected_cut_36785

theorem selected_cut_36786 : selected 9 ⟨978297, by decide⟩
    (prefixPartial 12 290634) = some ⟨12, 2, 0, 978297, 290634, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_290634_978297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290634 ⟨978297, by decide⟩ :=
  accepted_of_selected 12 290634 ⟨978297, by decide⟩ ⟨12, 2, 0, 978297, 290634, 2349, 65536⟩
    (by decide) selected_cut_36786

theorem selected_cut_36787 : selected 9 ⟨978358, by decide⟩
    (prefixPartial 12 290635) = some ⟨12, 2, 0, 978358, 290635, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_290635_978358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290635 ⟨978358, by decide⟩ :=
  accepted_of_selected 12 290635 ⟨978358, by decide⟩ ⟨12, 2, 0, 978358, 290635, 2521, 65536⟩
    (by decide) selected_cut_36787

theorem unmarked_context_11_72658_978359 : frontier 10 ⟨978359, by decide⟩
    (prefixCache 11 72658) (prefixPartial 11 72658) = false := by
  decide +kernel

theorem node_context_11_72658_978359 : EJMOriginalGlobalDAGData.nodes 10 ⟨978359, by decide⟩ =
    .split (coordinate 11) (![⟨978241, by decide⟩,⟨896706, by decide⟩,⟨978297, by decide⟩,⟨978358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72658_978359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72658 ⟨978359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72658
    ⟨978359, by decide⟩ (by decide) (![⟨978241, by decide⟩,⟨896706, by decide⟩,⟨978297, by decide⟩,⟨978358, by decide⟩]) unmarked_context_11_72658_978359 node_context_11_72658_978359
  intro a
  fin_cases a
  · exact context_12_290632_978241
  · exact context_12_290633_896706
  · exact context_12_290634_978297
  · exact context_12_290635_978358

theorem selected_cut_36788 : selected 10 ⟨978462, by decide⟩
    (prefixPartial 11 72659) = some ⟨11, 2, 0, 978462, 72659, 3685, 262144⟩ := by
  decide +kernel

theorem context_11_72659_978462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72659 ⟨978462, by decide⟩ :=
  accepted_of_selected 11 72659 ⟨978462, by decide⟩ ⟨11, 2, 0, 978462, 72659, 3685, 262144⟩
    (by decide) selected_cut_36788

theorem unmarked_context_10_18164_978463 : frontier 11 ⟨978463, by decide⟩
    (prefixCache 10 18164) (prefixPartial 10 18164) = false := by
  decide +kernel

theorem node_context_10_18164_978463 : EJMOriginalGlobalDAGData.nodes 11 ⟨978463, by decide⟩ =
    .split (coordinate 10) (![⟨978009, by decide⟩,⟨978174, by decide⟩,⟨978359, by decide⟩,⟨978462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18164_978463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18164 ⟨978463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18164
    ⟨978463, by decide⟩ (by decide) (![⟨978009, by decide⟩,⟨978174, by decide⟩,⟨978359, by decide⟩,⟨978462, by decide⟩]) unmarked_context_10_18164_978463 node_context_10_18164_978463
  intro a
  fin_cases a
  · exact context_11_72656_978009
  · exact context_11_72657_978174
  · exact context_11_72658_978359
  · exact context_11_72659_978462

theorem selected_cut_36789 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18165) = some ⟨10, 1, 0, 893098, 18165, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18165_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18165 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18165 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18165, 1, 1048576⟩
    (by decide) selected_cut_36789

theorem selected_cut_36790 : selected 10 ⟨978569, by decide⟩
    (prefixPartial 11 72664) = some ⟨11, 2, 0, 978569, 72664, 3569, 262144⟩ := by
  decide +kernel

theorem context_11_72664_978569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72664 ⟨978569, by decide⟩ :=
  accepted_of_selected 11 72664 ⟨978569, by decide⟩ ⟨11, 2, 0, 978569, 72664, 3569, 262144⟩
    (by decide) selected_cut_36790

theorem selected_cut_36791 : selected 10 ⟨978637, by decide⟩
    (prefixPartial 11 72665) = some ⟨11, 2, 0, 978637, 72665, 2865, 262144⟩ := by
  decide +kernel

theorem context_11_72665_978637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72665 ⟨978637, by decide⟩ :=
  accepted_of_selected 11 72665 ⟨978637, by decide⟩ ⟨11, 2, 0, 978637, 72665, 2865, 262144⟩
    (by decide) selected_cut_36791

theorem selected_cut_36792 : selected 10 ⟨978675, by decide⟩
    (prefixPartial 11 72666) = some ⟨11, 2, 0, 978675, 72666, 1777, 262144⟩ := by
  decide +kernel

theorem context_11_72666_978675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72666 ⟨978675, by decide⟩ :=
  accepted_of_selected 11 72666 ⟨978675, by decide⟩ ⟨11, 2, 0, 978675, 72666, 1777, 262144⟩
    (by decide) selected_cut_36792

theorem selected_cut_36793 : selected 10 ⟨978706, by decide⟩
    (prefixPartial 11 72667) = some ⟨11, 2, 0, 978706, 72667, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_72667_978706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72667 ⟨978706, by decide⟩ :=
  accepted_of_selected 11 72667 ⟨978706, by decide⟩ ⟨11, 2, 0, 978706, 72667, 1281, 262144⟩
    (by decide) selected_cut_36793

theorem unmarked_context_10_18166_978707 : frontier 11 ⟨978707, by decide⟩
    (prefixCache 10 18166) (prefixPartial 10 18166) = false := by
  decide +kernel

theorem node_context_10_18166_978707 : EJMOriginalGlobalDAGData.nodes 11 ⟨978707, by decide⟩ =
    .split (coordinate 10) (![⟨978569, by decide⟩,⟨978637, by decide⟩,⟨978675, by decide⟩,⟨978706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18166_978707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18166 ⟨978707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18166
    ⟨978707, by decide⟩ (by decide) (![⟨978569, by decide⟩,⟨978637, by decide⟩,⟨978675, by decide⟩,⟨978706, by decide⟩]) unmarked_context_10_18166_978707 node_context_10_18166_978707
  intro a
  fin_cases a
  · exact context_11_72664_978569
  · exact context_11_72665_978637
  · exact context_11_72666_978675
  · exact context_11_72667_978706

theorem selected_cut_36794 : selected 11 ⟨978806, by decide⟩
    (prefixPartial 10 18167) = some ⟨10, 2, 0, 978806, 18167, 3437, 1048576⟩ := by
  decide +kernel

theorem context_10_18167_978806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18167 ⟨978806, by decide⟩ :=
  accepted_of_selected 10 18167 ⟨978806, by decide⟩ ⟨10, 2, 0, 978806, 18167, 3437, 1048576⟩
    (by decide) selected_cut_36794

theorem unmarked_context_9_4541_978807 : frontier 12 ⟨978807, by decide⟩
    (prefixCache 9 4541) (prefixPartial 9 4541) = false := by
  decide +kernel

theorem node_context_9_4541_978807 : EJMOriginalGlobalDAGData.nodes 12 ⟨978807, by decide⟩ =
    .split (coordinate 9) (![⟨978463, by decide⟩,⟨893098, by decide⟩,⟨978707, by decide⟩,⟨978806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4541_978807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4541 ⟨978807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4541
    ⟨978807, by decide⟩ (by decide) (![⟨978463, by decide⟩,⟨893098, by decide⟩,⟨978707, by decide⟩,⟨978806, by decide⟩]) unmarked_context_9_4541_978807 node_context_9_4541_978807
  intro a
  fin_cases a
  · exact context_10_18164_978463
  · exact context_10_18165_893098
  · exact context_10_18166_978707
  · exact context_10_18167_978806

theorem selected_cut_36795 : selected 9 ⟨978856, by decide⟩
    (prefixPartial 12 290688) = some ⟨12, 2, 0, 978856, 290688, 557, 65536⟩ := by
  decide +kernel

theorem context_12_290688_978856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290688 ⟨978856, by decide⟩ :=
  accepted_of_selected 12 290688 ⟨978856, by decide⟩ ⟨12, 2, 0, 978856, 290688, 557, 65536⟩
    (by decide) selected_cut_36795

theorem selected_cut_36796 : selected 9 ⟨978883, by decide⟩
    (prefixPartial 12 290689) = some ⟨12, 2, 0, 978883, 290689, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_290689_978883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290689 ⟨978883, by decide⟩ :=
  accepted_of_selected 12 290689 ⟨978883, by decide⟩ ⟨12, 2, 0, 978883, 290689, 1781, 65536⟩
    (by decide) selected_cut_36796

theorem selected_cut_36797 : selected 9 ⟨978914, by decide⟩
    (prefixPartial 12 290690) = some ⟨12, 2, 0, 978914, 290690, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_290690_978914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290690 ⟨978914, by decide⟩ :=
  accepted_of_selected 12 290690 ⟨978914, by decide⟩ ⟨12, 2, 0, 978914, 290690, 1797, 65536⟩
    (by decide) selected_cut_36797

theorem selected_cut_36798 : selected 9 ⟨978947, by decide⟩
    (prefixPartial 12 290691) = some ⟨12, 2, 0, 978947, 290691, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_290691_978947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290691 ⟨978947, by decide⟩ :=
  accepted_of_selected 12 290691 ⟨978947, by decide⟩ ⟨12, 2, 0, 978947, 290691, 1861, 65536⟩
    (by decide) selected_cut_36798

theorem unmarked_context_11_72672_978948 : frontier 10 ⟨978948, by decide⟩
    (prefixCache 11 72672) (prefixPartial 11 72672) = false := by
  decide +kernel

theorem node_context_11_72672_978948 : EJMOriginalGlobalDAGData.nodes 10 ⟨978948, by decide⟩ =
    .split (coordinate 11) (![⟨978856, by decide⟩,⟨978883, by decide⟩,⟨978914, by decide⟩,⟨978947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72672_978948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72672 ⟨978948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72672
    ⟨978948, by decide⟩ (by decide) (![⟨978856, by decide⟩,⟨978883, by decide⟩,⟨978914, by decide⟩,⟨978947, by decide⟩]) unmarked_context_11_72672_978948 node_context_11_72672_978948
  intro a
  fin_cases a
  · exact context_12_290688_978856
  · exact context_12_290689_978883
  · exact context_12_290690_978914
  · exact context_12_290691_978947

theorem selected_cut_36799 : selected 9 ⟨978979, by decide⟩
    (prefixPartial 12 290692) = some ⟨12, 2, 0, 978979, 290692, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_290692_978979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290692 ⟨978979, by decide⟩ :=
  accepted_of_selected 12 290692 ⟨978979, by decide⟩ ⟨12, 2, 0, 978979, 290692, 1361, 65536⟩
    (by decide) selected_cut_36799

theorem selected_cut_36800 : selected 9 ⟨979012, by decide⟩
    (prefixPartial 12 290693) = some ⟨12, 2, 0, 979012, 290693, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_290693_979012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290693 ⟨979012, by decide⟩ :=
  accepted_of_selected 12 290693 ⟨979012, by decide⟩ ⟨12, 2, 0, 979012, 290693, 1649, 65536⟩
    (by decide) selected_cut_36800

theorem selected_cut_36801 : selected 9 ⟨979040, by decide⟩
    (prefixPartial 12 290694) = some ⟨12, 2, 0, 979040, 290694, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_290694_979040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290694 ⟨979040, by decide⟩ :=
  accepted_of_selected 12 290694 ⟨979040, by decide⟩ ⟨12, 2, 0, 979040, 290694, 1649, 65536⟩
    (by decide) selected_cut_36801

theorem selected_cut_36802 : selected 9 ⟨979075, by decide⟩
    (prefixPartial 12 290695) = some ⟨12, 2, 0, 979075, 290695, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_290695_979075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290695 ⟨979075, by decide⟩ :=
  accepted_of_selected 12 290695 ⟨979075, by decide⟩ ⟨12, 2, 0, 979075, 290695, 1773, 65536⟩
    (by decide) selected_cut_36802

theorem unmarked_context_11_72673_979076 : frontier 10 ⟨979076, by decide⟩
    (prefixCache 11 72673) (prefixPartial 11 72673) = false := by
  decide +kernel

theorem node_context_11_72673_979076 : EJMOriginalGlobalDAGData.nodes 10 ⟨979076, by decide⟩ =
    .split (coordinate 11) (![⟨978979, by decide⟩,⟨979012, by decide⟩,⟨979040, by decide⟩,⟨979075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72673_979076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72673 ⟨979076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72673
    ⟨979076, by decide⟩ (by decide) (![⟨978979, by decide⟩,⟨979012, by decide⟩,⟨979040, by decide⟩,⟨979075, by decide⟩]) unmarked_context_11_72673_979076 node_context_11_72673_979076
  intro a
  fin_cases a
  · exact context_12_290692_978979
  · exact context_12_290693_979012
  · exact context_12_290694_979040
  · exact context_12_290695_979075

theorem selected_cut_36803 : selected 9 ⟨979115, by decide⟩
    (prefixPartial 12 290696) = some ⟨12, 2, 0, 979115, 290696, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_290696_979115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290696 ⟨979115, by decide⟩ :=
  accepted_of_selected 12 290696 ⟨979115, by decide⟩ ⟨12, 2, 0, 979115, 290696, 1493, 65536⟩
    (by decide) selected_cut_36803

theorem selected_cut_36804 : selected 9 ⟨979149, by decide⟩
    (prefixPartial 12 290697) = some ⟨12, 2, 0, 979149, 290697, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_290697_979149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290697 ⟨979149, by decide⟩ :=
  accepted_of_selected 12 290697 ⟨979149, by decide⟩ ⟨12, 2, 0, 979149, 290697, 1601, 65536⟩
    (by decide) selected_cut_36804

theorem selected_cut_36805 : selected 9 ⟨979175, by decide⟩
    (prefixPartial 12 290698) = some ⟨12, 2, 0, 979175, 290698, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_290698_979175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290698 ⟨979175, by decide⟩ :=
  accepted_of_selected 12 290698 ⟨979175, by decide⟩ ⟨12, 2, 0, 979175, 290698, 1577, 65536⟩
    (by decide) selected_cut_36805

theorem selected_cut_36806 : selected 9 ⟨979208, by decide⟩
    (prefixPartial 12 290699) = some ⟨12, 2, 0, 979208, 290699, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_290699_979208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 290699 ⟨979208, by decide⟩ :=
  accepted_of_selected 12 290699 ⟨979208, by decide⟩ ⟨12, 2, 0, 979208, 290699, 1769, 65536⟩
    (by decide) selected_cut_36806

theorem unmarked_context_11_72674_979209 : frontier 10 ⟨979209, by decide⟩
    (prefixCache 11 72674) (prefixPartial 11 72674) = false := by
  decide +kernel

theorem node_context_11_72674_979209 : EJMOriginalGlobalDAGData.nodes 10 ⟨979209, by decide⟩ =
    .split (coordinate 11) (![⟨979115, by decide⟩,⟨979149, by decide⟩,⟨979175, by decide⟩,⟨979208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72674_979209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72674 ⟨979209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72674
    ⟨979209, by decide⟩ (by decide) (![⟨979115, by decide⟩,⟨979149, by decide⟩,⟨979175, by decide⟩,⟨979208, by decide⟩]) unmarked_context_11_72674_979209 node_context_11_72674_979209
  intro a
  fin_cases a
  · exact context_12_290696_979115
  · exact context_12_290697_979149
  · exact context_12_290698_979175
  · exact context_12_290699_979208

theorem selected_cut_36807 : selected 10 ⟨979289, by decide⟩
    (prefixPartial 11 72675) = some ⟨11, 2, 0, 979289, 72675, 3685, 262144⟩ := by
  decide +kernel

theorem context_11_72675_979289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72675 ⟨979289, by decide⟩ :=
  accepted_of_selected 11 72675 ⟨979289, by decide⟩ ⟨11, 2, 0, 979289, 72675, 3685, 262144⟩
    (by decide) selected_cut_36807

theorem unmarked_context_10_18168_979290 : frontier 11 ⟨979290, by decide⟩
    (prefixCache 10 18168) (prefixPartial 10 18168) = false := by
  decide +kernel

theorem node_context_10_18168_979290 : EJMOriginalGlobalDAGData.nodes 11 ⟨979290, by decide⟩ =
    .split (coordinate 10) (![⟨978948, by decide⟩,⟨979076, by decide⟩,⟨979209, by decide⟩,⟨979289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18168_979290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18168 ⟨979290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18168
    ⟨979290, by decide⟩ (by decide) (![⟨978948, by decide⟩,⟨979076, by decide⟩,⟨979209, by decide⟩,⟨979289, by decide⟩]) unmarked_context_10_18168_979290 node_context_10_18168_979290
  intro a
  fin_cases a
  · exact context_11_72672_978948
  · exact context_11_72673_979076
  · exact context_11_72674_979209
  · exact context_11_72675_979289

theorem selected_cut_36808 : selected 10 ⟨979366, by decide⟩
    (prefixPartial 11 72676) = some ⟨11, 2, 0, 979366, 72676, 3345, 262144⟩ := by
  decide +kernel

theorem context_11_72676_979366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72676 ⟨979366, by decide⟩ :=
  accepted_of_selected 11 72676 ⟨979366, by decide⟩ ⟨11, 2, 0, 979366, 72676, 3345, 262144⟩
    (by decide) selected_cut_36808

theorem selected_cut_36809 : selected 10 ⟨979409, by decide⟩
    (prefixPartial 11 72677) = some ⟨11, 2, 0, 979409, 72677, 2025, 262144⟩ := by
  decide +kernel

theorem context_11_72677_979409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72677 ⟨979409, by decide⟩ :=
  accepted_of_selected 11 72677 ⟨979409, by decide⟩ ⟨11, 2, 0, 979409, 72677, 2025, 262144⟩
    (by decide) selected_cut_36809

theorem selected_cut_36810 : selected 10 ⟨979467, by decide⟩
    (prefixPartial 11 72678) = some ⟨11, 2, 0, 979467, 72678, 2517, 262144⟩ := by
  decide +kernel

theorem context_11_72678_979467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72678 ⟨979467, by decide⟩ :=
  accepted_of_selected 11 72678 ⟨979467, by decide⟩ ⟨11, 2, 0, 979467, 72678, 2517, 262144⟩
    (by decide) selected_cut_36810

theorem selected_cut_36811 : selected 10 ⟨979496, by decide⟩
    (prefixPartial 11 72679) = some ⟨11, 2, 0, 979496, 72679, 1373, 262144⟩ := by
  decide +kernel

theorem context_11_72679_979496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72679 ⟨979496, by decide⟩ :=
  accepted_of_selected 11 72679 ⟨979496, by decide⟩ ⟨11, 2, 0, 979496, 72679, 1373, 262144⟩
    (by decide) selected_cut_36811

theorem unmarked_context_10_18169_979497 : frontier 11 ⟨979497, by decide⟩
    (prefixCache 10 18169) (prefixPartial 10 18169) = false := by
  decide +kernel

theorem node_context_10_18169_979497 : EJMOriginalGlobalDAGData.nodes 11 ⟨979497, by decide⟩ =
    .split (coordinate 10) (![⟨979366, by decide⟩,⟨979409, by decide⟩,⟨979467, by decide⟩,⟨979496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18169_979497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18169 ⟨979497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18169
    ⟨979497, by decide⟩ (by decide) (![⟨979366, by decide⟩,⟨979409, by decide⟩,⟨979467, by decide⟩,⟨979496, by decide⟩]) unmarked_context_10_18169_979497 node_context_10_18169_979497
  intro a
  fin_cases a
  · exact context_11_72676_979366
  · exact context_11_72677_979409
  · exact context_11_72678_979467
  · exact context_11_72679_979496

theorem selected_cut_36812 : selected 11 ⟨979577, by decide⟩
    (prefixPartial 10 18170) = some ⟨10, 2, 0, 979577, 18170, 2741, 1048576⟩ := by
  decide +kernel

theorem context_10_18170_979577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18170 ⟨979577, by decide⟩ :=
  accepted_of_selected 10 18170 ⟨979577, by decide⟩ ⟨10, 2, 0, 979577, 18170, 2741, 1048576⟩
    (by decide) selected_cut_36812

theorem selected_cut_36813 : selected 11 ⟨979619, by decide⟩
    (prefixPartial 10 18171) = some ⟨10, 2, 0, 979619, 18171, 1517, 1048576⟩ := by
  decide +kernel

theorem context_10_18171_979619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18171 ⟨979619, by decide⟩ :=
  accepted_of_selected 10 18171 ⟨979619, by decide⟩ ⟨10, 2, 0, 979619, 18171, 1517, 1048576⟩
    (by decide) selected_cut_36813

theorem unmarked_context_9_4542_979620 : frontier 12 ⟨979620, by decide⟩
    (prefixCache 9 4542) (prefixPartial 9 4542) = false := by
  decide +kernel

theorem node_context_9_4542_979620 : EJMOriginalGlobalDAGData.nodes 12 ⟨979620, by decide⟩ =
    .split (coordinate 9) (![⟨979290, by decide⟩,⟨979497, by decide⟩,⟨979577, by decide⟩,⟨979619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4542_979620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4542 ⟨979620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4542
    ⟨979620, by decide⟩ (by decide) (![⟨979290, by decide⟩,⟨979497, by decide⟩,⟨979577, by decide⟩,⟨979619, by decide⟩]) unmarked_context_9_4542_979620 node_context_9_4542_979620
  intro a
  fin_cases a
  · exact context_10_18168_979290
  · exact context_10_18169_979497
  · exact context_10_18170_979577
  · exact context_10_18171_979619

theorem selected_cut_36814 : selected 10 ⟨979642, by decide⟩
    (prefixPartial 11 72688) = some ⟨11, 2, 0, 979642, 72688, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_72688_979642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72688 ⟨979642, by decide⟩ :=
  accepted_of_selected 11 72688 ⟨979642, by decide⟩ ⟨11, 2, 0, 979642, 72688, 1537, 262144⟩
    (by decide) selected_cut_36814

theorem selected_cut_36815 : selected 10 ⟨979683, by decide⟩
    (prefixPartial 11 72689) = some ⟨11, 2, 0, 979683, 72689, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_72689_979683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72689 ⟨979683, by decide⟩ :=
  accepted_of_selected 11 72689 ⟨979683, by decide⟩ ⟨11, 2, 0, 979683, 72689, 1929, 262144⟩
    (by decide) selected_cut_36815

theorem selected_cut_36816 : selected 10 ⟨979732, by decide⟩
    (prefixPartial 11 72690) = some ⟨11, 2, 0, 979732, 72690, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_72690_979732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72690 ⟨979732, by decide⟩ :=
  accepted_of_selected 11 72690 ⟨979732, by decide⟩ ⟨11, 2, 0, 979732, 72690, 1929, 262144⟩
    (by decide) selected_cut_36816

theorem selected_cut_36817 : selected 10 ⟨979761, by decide⟩
    (prefixPartial 11 72691) = some ⟨11, 2, 0, 979761, 72691, 1033, 262144⟩ := by
  decide +kernel

theorem context_11_72691_979761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72691 ⟨979761, by decide⟩ :=
  accepted_of_selected 11 72691 ⟨979761, by decide⟩ ⟨11, 2, 0, 979761, 72691, 1033, 262144⟩
    (by decide) selected_cut_36817

theorem unmarked_context_10_18172_979762 : frontier 11 ⟨979762, by decide⟩
    (prefixCache 10 18172) (prefixPartial 10 18172) = false := by
  decide +kernel

theorem node_context_10_18172_979762 : EJMOriginalGlobalDAGData.nodes 11 ⟨979762, by decide⟩ =
    .split (coordinate 10) (![⟨979642, by decide⟩,⟨979683, by decide⟩,⟨979732, by decide⟩,⟨979761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18172_979762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18172 ⟨979762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18172
    ⟨979762, by decide⟩ (by decide) (![⟨979642, by decide⟩,⟨979683, by decide⟩,⟨979732, by decide⟩,⟨979761, by decide⟩]) unmarked_context_10_18172_979762 node_context_10_18172_979762
  intro a
  fin_cases a
  · exact context_11_72688_979642
  · exact context_11_72689_979683
  · exact context_11_72690_979732
  · exact context_11_72691_979761

theorem selected_cut_36818 : selected 11 ⟨979844, by decide⟩
    (prefixPartial 10 18173) = some ⟨10, 2, 0, 979844, 18173, 2245, 1048576⟩ := by
  decide +kernel

theorem context_10_18173_979844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18173 ⟨979844, by decide⟩ :=
  accepted_of_selected 10 18173 ⟨979844, by decide⟩ ⟨10, 2, 0, 979844, 18173, 2245, 1048576⟩
    (by decide) selected_cut_36818

theorem selected_cut_36819 : selected 11 ⟨979885, by decide⟩
    (prefixPartial 10 18174) = some ⟨10, 2, 0, 979885, 18174, 617, 1048576⟩ := by
  decide +kernel

theorem context_10_18174_979885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18174 ⟨979885, by decide⟩ :=
  accepted_of_selected 10 18174 ⟨979885, by decide⟩ ⟨10, 2, 0, 979885, 18174, 617, 1048576⟩
    (by decide) selected_cut_36819

theorem selected_cut_36820 : selected 11 ⟨979891, by decide⟩
    (prefixPartial 10 18175) = some ⟨10, 2, 0, 979891, 18175, 17, 1048576⟩ := by
  decide +kernel

theorem context_10_18175_979891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18175 ⟨979891, by decide⟩ :=
  accepted_of_selected 10 18175 ⟨979891, by decide⟩ ⟨10, 2, 0, 979891, 18175, 17, 1048576⟩
    (by decide) selected_cut_36820

theorem unmarked_context_9_4543_979892 : frontier 12 ⟨979892, by decide⟩
    (prefixCache 9 4543) (prefixPartial 9 4543) = false := by
  decide +kernel

theorem node_context_9_4543_979892 : EJMOriginalGlobalDAGData.nodes 12 ⟨979892, by decide⟩ =
    .split (coordinate 9) (![⟨979762, by decide⟩,⟨979844, by decide⟩,⟨979885, by decide⟩,⟨979891, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4543_979892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4543 ⟨979892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4543
    ⟨979892, by decide⟩ (by decide) (![⟨979762, by decide⟩,⟨979844, by decide⟩,⟨979885, by decide⟩,⟨979891, by decide⟩]) unmarked_context_9_4543_979892 node_context_9_4543_979892
  intro a
  fin_cases a
  · exact context_10_18172_979762
  · exact context_10_18173_979844
  · exact context_10_18174_979885
  · exact context_10_18175_979891

theorem unmarked_context_8_1135_979893 : frontier 13 ⟨979893, by decide⟩
    (prefixCache 8 1135) (prefixPartial 8 1135) = false := by
  decide +kernel

theorem node_context_8_1135_979893 : EJMOriginalGlobalDAGData.nodes 13 ⟨979893, by decide⟩ =
    .split (coordinate 8) (![⟨977888, by decide⟩,⟨978807, by decide⟩,⟨979620, by decide⟩,⟨979892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1135_979893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1135 ⟨979893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1135
    ⟨979893, by decide⟩ (by decide) (![⟨977888, by decide⟩,⟨978807, by decide⟩,⟨979620, by decide⟩,⟨979892, by decide⟩]) unmarked_context_8_1135_979893 node_context_8_1135_979893
  intro a
  fin_cases a
  · exact context_9_4540_977888
  · exact context_9_4541_978807
  · exact context_9_4542_979620
  · exact context_9_4543_979892

theorem unmarked_context_7_283_979894 : frontier 14 ⟨979894, by decide⟩
    (prefixCache 7 283) (prefixPartial 7 283) = false := by
  decide +kernel

theorem node_context_7_283_979894 : EJMOriginalGlobalDAGData.nodes 14 ⟨979894, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨14300, by decide⟩,⟨979893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_283_979894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 283 ⟨979894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 283
    ⟨979894, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨14300, by decide⟩,⟨979893, by decide⟩]) unmarked_context_7_283_979894 node_context_7_283_979894
  intro a
  fin_cases a
  · exact context_8_1132_14300
  · exact context_8_1133_14300
  · exact context_8_1134_14300
  · exact context_8_1135_979893

theorem unmarked_context_6_70_979895 : frontier 15 ⟨979895, by decide⟩
    (prefixCache 6 70) (prefixPartial 6 70) = false := by
  decide +kernel

theorem node_context_6_70_979895 : EJMOriginalGlobalDAGData.nodes 15 ⟨979895, by decide⟩ =
    .split (coordinate 6) (![⟨949751, by decide⟩,⟨965537, by decide⟩,⟨974845, by decide⟩,⟨979894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_70_979895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 70 ⟨979895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 70
    ⟨979895, by decide⟩ (by decide) (![⟨949751, by decide⟩,⟨965537, by decide⟩,⟨974845, by decide⟩,⟨979894, by decide⟩]) unmarked_context_6_70_979895 node_context_6_70_979895
  intro a
  fin_cases a
  · exact context_7_280_949751
  · exact context_7_281_965537
  · exact context_7_282_974845
  · exact context_7_283_979894

theorem selected_cut_36821 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 71) = some ⟨6, 1, 0, 116314, 71, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_71_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 71 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 71 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 71, 1, 268435456⟩
    (by decide) selected_cut_36821

theorem unmarked_context_5_17_979896 : frontier 16 ⟨979896, by decide⟩
    (prefixCache 5 17) (prefixPartial 5 17) = false := by
  decide +kernel

theorem node_context_5_17_979896 : EJMOriginalGlobalDAGData.nodes 16 ⟨979896, by decide⟩ =
    .split (coordinate 5) (![⟨906779, by decide⟩,⟨931809, by decide⟩,⟨979895, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_17_979896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 17 ⟨979896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 17
    ⟨979896, by decide⟩ (by decide) (![⟨906779, by decide⟩,⟨931809, by decide⟩,⟨979895, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_17_979896 node_context_5_17_979896
  intro a
  fin_cases a
  · exact context_6_68_906779
  · exact context_6_69_931809
  · exact context_6_70_979895
  · exact context_6_71_116314

theorem selected_cut_36822 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 288) = some ⟨7, 1, 0, 116316, 288, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_288_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 288 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 288 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 288, 1, 67108864⟩
    (by decide) selected_cut_36822

theorem selected_cut_36823 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 289) = some ⟨7, 1, 0, 116316, 289, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_289_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 289 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 289 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 289, 1, 67108864⟩
    (by decide) selected_cut_36823

theorem selected_cut_36824 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1160) = some ⟨8, 1, 0, 979897, 1160, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1160_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1160 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1160 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1160, 1, 16777216⟩
    (by decide) selected_cut_36824

theorem selected_cut_36825 : selected 9 ⟨979950, by decide⟩
    (prefixPartial 12 297216) = some ⟨12, 2, 0, 979950, 297216, 549, 65536⟩ := by
  decide +kernel

theorem context_12_297216_979950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297216 ⟨979950, by decide⟩ :=
  accepted_of_selected 12 297216 ⟨979950, by decide⟩ ⟨12, 2, 0, 979950, 297216, 549, 65536⟩
    (by decide) selected_cut_36825

theorem selected_cut_36826 : selected 9 ⟨980018, by decide⟩
    (prefixPartial 12 297217) = some ⟨12, 2, 0, 980018, 297217, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_297217_980018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297217 ⟨980018, by decide⟩ :=
  accepted_of_selected 12 297217 ⟨980018, by decide⟩ ⟨12, 2, 0, 980018, 297217, 2873, 65536⟩
    (by decide) selected_cut_36826

theorem selected_cut_36827 : selected 9 ⟨898007, by decide⟩
    (prefixPartial 12 297218) = some ⟨12, 1, 0, 898007, 297218, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297218_898007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297218 ⟨898007, by decide⟩ :=
  accepted_of_selected 12 297218 ⟨898007, by decide⟩ ⟨12, 1, 0, 898007, 297218, 1, 65536⟩
    (by decide) selected_cut_36827

theorem selected_cut_36828 : selected 9 ⟨980095, by decide⟩
    (prefixPartial 12 297219) = some ⟨12, 2, 0, 980095, 297219, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_297219_980095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297219 ⟨980095, by decide⟩ :=
  accepted_of_selected 12 297219 ⟨980095, by decide⟩ ⟨12, 2, 0, 980095, 297219, 1885, 65536⟩
    (by decide) selected_cut_36828

theorem unmarked_context_11_74304_980096 : frontier 10 ⟨980096, by decide⟩
    (prefixCache 11 74304) (prefixPartial 11 74304) = false := by
  decide +kernel

theorem node_context_11_74304_980096 : EJMOriginalGlobalDAGData.nodes 10 ⟨980096, by decide⟩ =
    .split (coordinate 11) (![⟨979950, by decide⟩,⟨980018, by decide⟩,⟨898007, by decide⟩,⟨980095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74304_980096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74304 ⟨980096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74304
    ⟨980096, by decide⟩ (by decide) (![⟨979950, by decide⟩,⟨980018, by decide⟩,⟨898007, by decide⟩,⟨980095, by decide⟩]) unmarked_context_11_74304_980096 node_context_11_74304_980096
  intro a
  fin_cases a
  · exact context_12_297216_979950
  · exact context_12_297217_980018
  · exact context_12_297218_898007
  · exact context_12_297219_980095

theorem selected_cut_36829 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 297220) = some ⟨12, 1, 0, 895, 297220, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297220_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297220 ⟨895, by decide⟩ :=
  accepted_of_selected 12 297220 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 297220, 1, 65536⟩
    (by decide) selected_cut_36829

theorem selected_cut_36830 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 297221) = some ⟨12, 1, 0, 891951, 297221, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297221_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297221 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 297221 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 297221, 1, 65536⟩
    (by decide) selected_cut_36830

theorem selected_cut_36831 : selected 9 ⟨980161, by decide⟩
    (prefixPartial 12 297222) = some ⟨12, 2, 0, 980161, 297222, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_297222_980161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297222 ⟨980161, by decide⟩ :=
  accepted_of_selected 12 297222 ⟨980161, by decide⟩ ⟨12, 2, 0, 980161, 297222, 2789, 65536⟩
    (by decide) selected_cut_36831

theorem selected_cut_36832 : selected 9 ⟨980230, by decide⟩
    (prefixPartial 12 297223) = some ⟨12, 2, 0, 980230, 297223, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_297223_980230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297223 ⟨980230, by decide⟩ :=
  accepted_of_selected 12 297223 ⟨980230, by decide⟩ ⟨12, 2, 0, 980230, 297223, 3025, 65536⟩
    (by decide) selected_cut_36832

theorem unmarked_context_11_74305_980231 : frontier 10 ⟨980231, by decide⟩
    (prefixCache 11 74305) (prefixPartial 11 74305) = false := by
  decide +kernel

theorem node_context_11_74305_980231 : EJMOriginalGlobalDAGData.nodes 10 ⟨980231, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨891951, by decide⟩,⟨980161, by decide⟩,⟨980230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74305_980231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74305 ⟨980231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74305
    ⟨980231, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨891951, by decide⟩,⟨980161, by decide⟩,⟨980230, by decide⟩]) unmarked_context_11_74305_980231 node_context_11_74305_980231
  intro a
  fin_cases a
  · exact context_12_297220_895
  · exact context_12_297221_891951
  · exact context_12_297222_980161
  · exact context_12_297223_980230

theorem selected_cut_36833 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 297224) = some ⟨12, 1, 0, 3161, 297224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297224_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297224 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 297224 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 297224, 1, 65536⟩
    (by decide) selected_cut_36833

theorem selected_cut_36834 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 297225) = some ⟨12, 1, 0, 895, 297225, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297225_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297225 ⟨895, by decide⟩ :=
  accepted_of_selected 12 297225 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 297225, 1, 65536⟩
    (by decide) selected_cut_36834

theorem selected_cut_36835 : selected 9 ⟨980277, by decide⟩
    (prefixPartial 12 297226) = some ⟨12, 2, 0, 980277, 297226, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_297226_980277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297226 ⟨980277, by decide⟩ :=
  accepted_of_selected 12 297226 ⟨980277, by decide⟩ ⟨12, 2, 0, 980277, 297226, 1569, 65536⟩
    (by decide) selected_cut_36835

theorem selected_cut_36836 : selected 9 ⟨980336, by decide⟩
    (prefixPartial 12 297227) = some ⟨12, 2, 0, 980336, 297227, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_297227_980336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297227 ⟨980336, by decide⟩ :=
  accepted_of_selected 12 297227 ⟨980336, by decide⟩ ⟨12, 2, 0, 980336, 297227, 2625, 65536⟩
    (by decide) selected_cut_36836

theorem unmarked_context_11_74306_980337 : frontier 10 ⟨980337, by decide⟩
    (prefixCache 11 74306) (prefixPartial 11 74306) = false := by
  decide +kernel

theorem node_context_11_74306_980337 : EJMOriginalGlobalDAGData.nodes 10 ⟨980337, by decide⟩ =
    .split (coordinate 11) (![⟨3161, by decide⟩,⟨895, by decide⟩,⟨980277, by decide⟩,⟨980336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74306_980337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74306 ⟨980337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74306
    ⟨980337, by decide⟩ (by decide) (![⟨3161, by decide⟩,⟨895, by decide⟩,⟨980277, by decide⟩,⟨980336, by decide⟩]) unmarked_context_11_74306_980337 node_context_11_74306_980337
  intro a
  fin_cases a
  · exact context_12_297224_3161
  · exact context_12_297225_895
  · exact context_12_297226_980277
  · exact context_12_297227_980336

theorem selected_cut_36837 : selected 10 ⟨980394, by decide⟩
    (prefixPartial 11 74307) = some ⟨11, 2, 0, 980394, 74307, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_74307_980394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74307 ⟨980394, by decide⟩ :=
  accepted_of_selected 11 74307 ⟨980394, by decide⟩ ⟨11, 2, 0, 980394, 74307, 1609, 262144⟩
    (by decide) selected_cut_36837

theorem unmarked_context_10_18576_980395 : frontier 11 ⟨980395, by decide⟩
    (prefixCache 10 18576) (prefixPartial 10 18576) = false := by
  decide +kernel

theorem node_context_10_18576_980395 : EJMOriginalGlobalDAGData.nodes 11 ⟨980395, by decide⟩ =
    .split (coordinate 10) (![⟨980096, by decide⟩,⟨980231, by decide⟩,⟨980337, by decide⟩,⟨980394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18576_980395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18576 ⟨980395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18576
    ⟨980395, by decide⟩ (by decide) (![⟨980096, by decide⟩,⟨980231, by decide⟩,⟨980337, by decide⟩,⟨980394, by decide⟩]) unmarked_context_10_18576_980395 node_context_10_18576_980395
  intro a
  fin_cases a
  · exact context_11_74304_980096
  · exact context_11_74305_980231
  · exact context_11_74306_980337
  · exact context_11_74307_980394

theorem selected_cut_36838 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 297232) = some ⟨12, 1, 0, 26677, 297232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297232_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297232 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 297232 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 297232, 1, 65536⟩
    (by decide) selected_cut_36838

theorem selected_cut_36839 : selected 9 ⟨980481, by decide⟩
    (prefixPartial 12 297233) = some ⟨12, 2, 0, 980481, 297233, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_297233_980481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297233 ⟨980481, by decide⟩ :=
  accepted_of_selected 12 297233 ⟨980481, by decide⟩ ⟨12, 2, 0, 980481, 297233, 1741, 65536⟩
    (by decide) selected_cut_36839

theorem selected_cut_36840 : selected 9 ⟨980533, by decide⟩
    (prefixPartial 12 297234) = some ⟨12, 2, 0, 980533, 297234, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_297234_980533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297234 ⟨980533, by decide⟩ :=
  accepted_of_selected 12 297234 ⟨980533, by decide⟩ ⟨12, 2, 0, 980533, 297234, 1425, 65536⟩
    (by decide) selected_cut_36840

theorem selected_cut_36841 : selected 9 ⟨980611, by decide⟩
    (prefixPartial 12 297235) = some ⟨12, 2, 0, 980611, 297235, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_297235_980611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297235 ⟨980611, by decide⟩ :=
  accepted_of_selected 12 297235 ⟨980611, by decide⟩ ⟨12, 2, 0, 980611, 297235, 2473, 65536⟩
    (by decide) selected_cut_36841

theorem unmarked_context_11_74308_980612 : frontier 10 ⟨980612, by decide⟩
    (prefixCache 11 74308) (prefixPartial 11 74308) = false := by
  decide +kernel

theorem node_context_11_74308_980612 : EJMOriginalGlobalDAGData.nodes 10 ⟨980612, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨980481, by decide⟩,⟨980533, by decide⟩,⟨980611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74308_980612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74308 ⟨980612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74308
    ⟨980612, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨980481, by decide⟩,⟨980533, by decide⟩,⟨980611, by decide⟩]) unmarked_context_11_74308_980612 node_context_11_74308_980612
  intro a
  fin_cases a
  · exact context_12_297232_26677
  · exact context_12_297233_980481
  · exact context_12_297234_980533
  · exact context_12_297235_980611

theorem selected_cut_36842 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 297236) = some ⟨12, 1, 0, 26677, 297236, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297236_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297236 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 297236 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 297236, 1, 65536⟩
    (by decide) selected_cut_36842

theorem selected_cut_36843 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 297237) = some ⟨12, 1, 0, 692793, 297237, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297237_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297237 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 297237 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 297237, 1, 65536⟩
    (by decide) selected_cut_36843

theorem selected_cut_36844 : selected 9 ⟨980671, by decide⟩
    (prefixPartial 12 297238) = some ⟨12, 2, 0, 980671, 297238, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_297238_980671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297238 ⟨980671, by decide⟩ :=
  accepted_of_selected 12 297238 ⟨980671, by decide⟩ ⟨12, 2, 0, 980671, 297238, 2017, 65536⟩
    (by decide) selected_cut_36844

theorem selected_cut_36845 : selected 9 ⟨980731, by decide⟩
    (prefixPartial 12 297239) = some ⟨12, 2, 0, 980731, 297239, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_297239_980731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297239 ⟨980731, by decide⟩ :=
  accepted_of_selected 12 297239 ⟨980731, by decide⟩ ⟨12, 2, 0, 980731, 297239, 2221, 65536⟩
    (by decide) selected_cut_36845

theorem unmarked_context_11_74309_980732 : frontier 10 ⟨980732, by decide⟩
    (prefixCache 11 74309) (prefixPartial 11 74309) = false := by
  decide +kernel

theorem node_context_11_74309_980732 : EJMOriginalGlobalDAGData.nodes 10 ⟨980732, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨692793, by decide⟩,⟨980671, by decide⟩,⟨980731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74309_980732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74309 ⟨980732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74309
    ⟨980732, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨692793, by decide⟩,⟨980671, by decide⟩,⟨980731, by decide⟩]) unmarked_context_11_74309_980732 node_context_11_74309_980732
  intro a
  fin_cases a
  · exact context_12_297236_26677
  · exact context_12_297237_692793
  · exact context_12_297238_980671
  · exact context_12_297239_980731

theorem selected_cut_36846 : selected 10 ⟨980878, by decide⟩
    (prefixPartial 11 74310) = some ⟨11, 2, 0, 980878, 74310, 3893, 262144⟩ := by
  decide +kernel

theorem context_11_74310_980878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74310 ⟨980878, by decide⟩ :=
  accepted_of_selected 11 74310 ⟨980878, by decide⟩ ⟨11, 2, 0, 980878, 74310, 3893, 262144⟩
    (by decide) selected_cut_36846

theorem selected_cut_36847 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 297244) = some ⟨12, 1, 0, 26677, 297244, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297244_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297244 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 297244 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 297244, 1, 65536⟩
    (by decide) selected_cut_36847

theorem selected_cut_36848 : selected 9 ⟨980940, by decide⟩
    (prefixPartial 12 297245) = some ⟨12, 2, 0, 980940, 297245, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_297245_980940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297245 ⟨980940, by decide⟩ :=
  accepted_of_selected 12 297245 ⟨980940, by decide⟩ ⟨12, 2, 0, 980940, 297245, 1733, 65536⟩
    (by decide) selected_cut_36848

theorem selected_cut_36849 : selected 9 ⟨980978, by decide⟩
    (prefixPartial 12 297246) = some ⟨12, 2, 0, 980978, 297246, 905, 65536⟩ := by
  decide +kernel

theorem context_12_297246_980978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297246 ⟨980978, by decide⟩ :=
  accepted_of_selected 12 297246 ⟨980978, by decide⟩ ⟨12, 2, 0, 980978, 297246, 905, 65536⟩
    (by decide) selected_cut_36849

theorem selected_cut_36850 : selected 9 ⟨981042, by decide⟩
    (prefixPartial 12 297247) = some ⟨12, 2, 0, 981042, 297247, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_297247_981042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297247 ⟨981042, by decide⟩ :=
  accepted_of_selected 12 297247 ⟨981042, by decide⟩ ⟨12, 2, 0, 981042, 297247, 1609, 65536⟩
    (by decide) selected_cut_36850

theorem unmarked_context_11_74311_981043 : frontier 10 ⟨981043, by decide⟩
    (prefixCache 11 74311) (prefixPartial 11 74311) = false := by
  decide +kernel

theorem node_context_11_74311_981043 : EJMOriginalGlobalDAGData.nodes 10 ⟨981043, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨980940, by decide⟩,⟨980978, by decide⟩,⟨981042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74311_981043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74311 ⟨981043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74311
    ⟨981043, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨980940, by decide⟩,⟨980978, by decide⟩,⟨981042, by decide⟩]) unmarked_context_11_74311_981043 node_context_11_74311_981043
  intro a
  fin_cases a
  · exact context_12_297244_26677
  · exact context_12_297245_980940
  · exact context_12_297246_980978
  · exact context_12_297247_981042

theorem unmarked_context_10_18577_981044 : frontier 11 ⟨981044, by decide⟩
    (prefixCache 10 18577) (prefixPartial 10 18577) = false := by
  decide +kernel

theorem node_context_10_18577_981044 : EJMOriginalGlobalDAGData.nodes 11 ⟨981044, by decide⟩ =
    .split (coordinate 10) (![⟨980612, by decide⟩,⟨980732, by decide⟩,⟨980878, by decide⟩,⟨981043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18577_981044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18577 ⟨981044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18577
    ⟨981044, by decide⟩ (by decide) (![⟨980612, by decide⟩,⟨980732, by decide⟩,⟨980878, by decide⟩,⟨981043, by decide⟩]) unmarked_context_10_18577_981044 node_context_10_18577_981044
  intro a
  fin_cases a
  · exact context_11_74308_980612
  · exact context_11_74309_980732
  · exact context_11_74310_980878
  · exact context_11_74311_981043

theorem selected_cut_36851 : selected 11 ⟨981224, by decide⟩
    (prefixPartial 10 18578) = some ⟨10, 2, 0, 981224, 18578, 3865, 1048576⟩ := by
  decide +kernel

theorem context_10_18578_981224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18578 ⟨981224, by decide⟩ :=
  accepted_of_selected 10 18578 ⟨981224, by decide⟩ ⟨10, 2, 0, 981224, 18578, 3865, 1048576⟩
    (by decide) selected_cut_36851

theorem selected_cut_36852 : selected 11 ⟨981396, by decide⟩
    (prefixPartial 10 18579) = some ⟨10, 2, 0, 981396, 18579, 2389, 1048576⟩ := by
  decide +kernel

theorem context_10_18579_981396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18579 ⟨981396, by decide⟩ :=
  accepted_of_selected 10 18579 ⟨981396, by decide⟩ ⟨10, 2, 0, 981396, 18579, 2389, 1048576⟩
    (by decide) selected_cut_36852

theorem unmarked_context_9_4644_981397 : frontier 12 ⟨981397, by decide⟩
    (prefixCache 9 4644) (prefixPartial 9 4644) = false := by
  decide +kernel

theorem node_context_9_4644_981397 : EJMOriginalGlobalDAGData.nodes 12 ⟨981397, by decide⟩ =
    .split (coordinate 9) (![⟨980395, by decide⟩,⟨981044, by decide⟩,⟨981224, by decide⟩,⟨981396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4644_981397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4644 ⟨981397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4644
    ⟨981397, by decide⟩ (by decide) (![⟨980395, by decide⟩,⟨981044, by decide⟩,⟨981224, by decide⟩,⟨981396, by decide⟩]) unmarked_context_9_4644_981397 node_context_9_4644_981397
  intro a
  fin_cases a
  · exact context_10_18576_980395
  · exact context_10_18577_981044
  · exact context_10_18578_981224
  · exact context_10_18579_981396

theorem selected_cut_36853 : selected 12 ⟨981758, by decide⟩
    (prefixPartial 9 4645) = some ⟨9, 2, 0, 981758, 4645, 3669, 4194304⟩ := by
  decide +kernel

theorem context_9_4645_981758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4645 ⟨981758, by decide⟩ :=
  accepted_of_selected 9 4645 ⟨981758, by decide⟩ ⟨9, 2, 0, 981758, 4645, 3669, 4194304⟩
    (by decide) selected_cut_36853

theorem selected_cut_36854 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 4646) = some ⟨9, 1, 0, 33466, 4646, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4646_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4646 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 4646 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 4646, 1, 4194304⟩
    (by decide) selected_cut_36854

theorem selected_cut_36855 : selected 12 ⟨981761, by decide⟩
    (prefixPartial 9 4647) = some ⟨9, 2, 0, 981761, 4647, 17, 4194304⟩ := by
  decide +kernel

theorem context_9_4647_981761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4647 ⟨981761, by decide⟩ :=
  accepted_of_selected 9 4647 ⟨981761, by decide⟩ ⟨9, 2, 0, 981761, 4647, 17, 4194304⟩
    (by decide) selected_cut_36855

theorem unmarked_context_8_1161_981762 : frontier 13 ⟨981762, by decide⟩
    (prefixCache 8 1161) (prefixPartial 8 1161) = false := by
  decide +kernel

theorem node_context_8_1161_981762 : EJMOriginalGlobalDAGData.nodes 13 ⟨981762, by decide⟩ =
    .split (coordinate 8) (![⟨981397, by decide⟩,⟨981758, by decide⟩,⟨33466, by decide⟩,⟨981761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1161_981762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1161 ⟨981762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1161
    ⟨981762, by decide⟩ (by decide) (![⟨981397, by decide⟩,⟨981758, by decide⟩,⟨33466, by decide⟩,⟨981761, by decide⟩]) unmarked_context_8_1161_981762 node_context_8_1161_981762
  intro a
  fin_cases a
  · exact context_9_4644_981397
  · exact context_9_4645_981758
  · exact context_9_4646_33466
  · exact context_9_4647_981761

theorem selected_cut_36856 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1162) = some ⟨8, 1, 0, 979897, 1162, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1162_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1162 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1162 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1162, 1, 16777216⟩
    (by decide) selected_cut_36856

theorem selected_cut_36857 : selected 9 ⟨981828, by decide⟩
    (prefixPartial 12 297728) = some ⟨12, 2, 0, 981828, 297728, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_297728_981828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297728 ⟨981828, by decide⟩ :=
  accepted_of_selected 12 297728 ⟨981828, by decide⟩ ⟨12, 2, 0, 981828, 297728, 1141, 65536⟩
    (by decide) selected_cut_36857

theorem selected_cut_36858 : selected 9 ⟨981897, by decide⟩
    (prefixPartial 12 297729) = some ⟨12, 2, 0, 981897, 297729, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_297729_981897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297729 ⟨981897, by decide⟩ :=
  accepted_of_selected 12 297729 ⟨981897, by decide⟩ ⟨12, 2, 0, 981897, 297729, 3469, 65536⟩
    (by decide) selected_cut_36858

theorem selected_cut_36859 : selected 9 ⟨981964, by decide⟩
    (prefixPartial 12 297730) = some ⟨12, 2, 0, 981964, 297730, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_297730_981964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297730 ⟨981964, by decide⟩ :=
  accepted_of_selected 12 297730 ⟨981964, by decide⟩ ⟨12, 2, 0, 981964, 297730, 3173, 65536⟩
    (by decide) selected_cut_36859

theorem selected_cut_36860 : selected 9 ⟨982028, by decide⟩
    (prefixPartial 12 297731) = some ⟨12, 2, 0, 982028, 297731, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_297731_982028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297731 ⟨982028, by decide⟩ :=
  accepted_of_selected 12 297731 ⟨982028, by decide⟩ ⟨12, 2, 0, 982028, 297731, 3213, 65536⟩
    (by decide) selected_cut_36860

theorem unmarked_context_11_74432_982029 : frontier 10 ⟨982029, by decide⟩
    (prefixCache 11 74432) (prefixPartial 11 74432) = false := by
  decide +kernel

theorem node_context_11_74432_982029 : EJMOriginalGlobalDAGData.nodes 10 ⟨982029, by decide⟩ =
    .split (coordinate 11) (![⟨981828, by decide⟩,⟨981897, by decide⟩,⟨981964, by decide⟩,⟨982028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74432_982029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74432 ⟨982029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74432
    ⟨982029, by decide⟩ (by decide) (![⟨981828, by decide⟩,⟨981897, by decide⟩,⟨981964, by decide⟩,⟨982028, by decide⟩]) unmarked_context_11_74432_982029 node_context_11_74432_982029
  intro a
  fin_cases a
  · exact context_12_297728_981828
  · exact context_12_297729_981897
  · exact context_12_297730_981964
  · exact context_12_297731_982028

theorem selected_cut_36861 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 297732) = some ⟨12, 1, 0, 895, 297732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297732_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297732 ⟨895, by decide⟩ :=
  accepted_of_selected 12 297732 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 297732, 1, 65536⟩
    (by decide) selected_cut_36861

theorem selected_cut_36862 : selected 9 ⟨982086, by decide⟩
    (prefixPartial 12 297733) = some ⟨12, 2, 0, 982086, 297733, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_297733_982086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297733 ⟨982086, by decide⟩ :=
  accepted_of_selected 12 297733 ⟨982086, by decide⟩ ⟨12, 2, 0, 982086, 297733, 2037, 65536⟩
    (by decide) selected_cut_36862

theorem selected_cut_36863 : selected 9 ⟨982147, by decide⟩
    (prefixPartial 12 297734) = some ⟨12, 2, 0, 982147, 297734, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_297734_982147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297734 ⟨982147, by decide⟩ :=
  accepted_of_selected 12 297734 ⟨982147, by decide⟩ ⟨12, 2, 0, 982147, 297734, 3193, 65536⟩
    (by decide) selected_cut_36863

theorem selected_cut_36864 : selected 9 ⟨982210, by decide⟩
    (prefixPartial 12 297735) = some ⟨12, 2, 0, 982210, 297735, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_297735_982210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297735 ⟨982210, by decide⟩ :=
  accepted_of_selected 12 297735 ⟨982210, by decide⟩ ⟨12, 2, 0, 982210, 297735, 3321, 65536⟩
    (by decide) selected_cut_36864

theorem unmarked_context_11_74433_982211 : frontier 10 ⟨982211, by decide⟩
    (prefixCache 11 74433) (prefixPartial 11 74433) = false := by
  decide +kernel

theorem node_context_11_74433_982211 : EJMOriginalGlobalDAGData.nodes 10 ⟨982211, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨982086, by decide⟩,⟨982147, by decide⟩,⟨982210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74433_982211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74433 ⟨982211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74433
    ⟨982211, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨982086, by decide⟩,⟨982147, by decide⟩,⟨982210, by decide⟩]) unmarked_context_11_74433_982211 node_context_11_74433_982211
  intro a
  fin_cases a
  · exact context_12_297732_895
  · exact context_12_297733_982086
  · exact context_12_297734_982147
  · exact context_12_297735_982210

theorem selected_cut_36865 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 297736) = some ⟨12, 1, 0, 895, 297736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297736_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297736 ⟨895, by decide⟩ :=
  accepted_of_selected 12 297736 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 297736, 1, 65536⟩
    (by decide) selected_cut_36865

theorem selected_cut_36866 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 297737) = some ⟨12, 1, 0, 895, 297737, 1, 65536⟩ := by
  decide +kernel

theorem context_12_297737_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 297737 ⟨895, by decide⟩ :=
  accepted_of_selected 12 297737 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 297737, 1, 65536⟩
    (by decide) selected_cut_36866

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
