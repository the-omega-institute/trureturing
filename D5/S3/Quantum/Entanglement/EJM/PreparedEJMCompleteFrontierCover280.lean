/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover279
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26883 : selected 8 ⟨679954, by decide⟩
    (prefixPartial 13 364686) = some ⟨13, 2, 0, 679954, 364686, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_364686_679954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364686 ⟨679954, by decide⟩ :=
  accepted_of_selected 13 364686 ⟨679954, by decide⟩ ⟨13, 2, 0, 679954, 364686, 1349, 16384⟩
    (by decide) selected_cut_26883

theorem selected_cut_26884 : selected 8 ⟨679962, by decide⟩
    (prefixPartial 13 364687) = some ⟨13, 2, 0, 679962, 364687, 713, 16384⟩ := by
  decide +kernel

theorem context_13_364687_679962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364687 ⟨679962, by decide⟩ :=
  accepted_of_selected 13 364687 ⟨679962, by decide⟩ ⟨13, 2, 0, 679962, 364687, 713, 16384⟩
    (by decide) selected_cut_26884

theorem unmarked_context_12_91171_679963 : frontier 9 ⟨679963, by decide⟩
    (prefixCache 12 91171) (prefixPartial 12 91171) = false := by
  decide +kernel

theorem node_context_12_91171_679963 : EJMOriginalGlobalDAGData.nodes 9 ⟨679963, by decide⟩ =
    .split (coordinate 12) (![⟨679905, by decide⟩,⟨679937, by decide⟩,⟨679954, by decide⟩,⟨679962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91171_679963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91171 ⟨679963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91171
    ⟨679963, by decide⟩ (by decide) (![⟨679905, by decide⟩,⟨679937, by decide⟩,⟨679954, by decide⟩,⟨679962, by decide⟩]) unmarked_context_12_91171_679963 node_context_12_91171_679963
  intro a
  fin_cases a
  · exact context_13_364684_679905
  · exact context_13_364685_679937
  · exact context_13_364686_679954
  · exact context_13_364687_679962

theorem unmarked_context_11_22792_679964 : frontier 10 ⟨679964, by decide⟩
    (prefixCache 11 22792) (prefixPartial 11 22792) = false := by
  decide +kernel

theorem node_context_11_22792_679964 : EJMOriginalGlobalDAGData.nodes 10 ⟨679964, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨679817, by decide⟩,⟨679884, by decide⟩,⟨679963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22792_679964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22792 ⟨679964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22792
    ⟨679964, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨679817, by decide⟩,⟨679884, by decide⟩,⟨679963, by decide⟩]) unmarked_context_11_22792_679964 node_context_11_22792_679964
  intro a
  fin_cases a
  · exact context_12_91168_641337
  · exact context_12_91169_679817
  · exact context_12_91170_679884
  · exact context_12_91171_679963

theorem selected_cut_26885 : selected 9 ⟨680030, by decide⟩
    (prefixPartial 12 91172) = some ⟨12, 2, 0, 680030, 91172, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_91172_680030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91172 ⟨680030, by decide⟩ :=
  accepted_of_selected 12 91172 ⟨680030, by decide⟩ ⟨12, 2, 0, 680030, 91172, 4005, 65536⟩
    (by decide) selected_cut_26885

theorem selected_cut_26886 : selected 8 ⟨680044, by decide⟩
    (prefixPartial 13 364692) = some ⟨13, 2, 0, 680044, 364692, 849, 16384⟩ := by
  decide +kernel

theorem context_13_364692_680044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364692 ⟨680044, by decide⟩ :=
  accepted_of_selected 13 364692 ⟨680044, by decide⟩ ⟨13, 2, 0, 680044, 364692, 849, 16384⟩
    (by decide) selected_cut_26886

theorem selected_cut_26887 : selected 8 ⟨680073, by decide⟩
    (prefixPartial 13 364693) = some ⟨13, 2, 0, 680073, 364693, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_364693_680073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364693 ⟨680073, by decide⟩ :=
  accepted_of_selected 13 364693 ⟨680073, by decide⟩ ⟨13, 2, 0, 680073, 364693, 1469, 16384⟩
    (by decide) selected_cut_26887

theorem selected_cut_26888 : selected 8 ⟨680090, by decide⟩
    (prefixPartial 13 364694) = some ⟨13, 2, 0, 680090, 364694, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_364694_680090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364694 ⟨680090, by decide⟩ :=
  accepted_of_selected 13 364694 ⟨680090, by decide⟩ ⟨13, 2, 0, 680090, 364694, 1273, 16384⟩
    (by decide) selected_cut_26888

theorem selected_cut_26889 : selected 8 ⟨680095, by decide⟩
    (prefixPartial 13 364695) = some ⟨13, 2, 0, 680095, 364695, 725, 16384⟩ := by
  decide +kernel

theorem context_13_364695_680095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364695 ⟨680095, by decide⟩ :=
  accepted_of_selected 13 364695 ⟨680095, by decide⟩ ⟨13, 2, 0, 680095, 364695, 725, 16384⟩
    (by decide) selected_cut_26889

theorem unmarked_context_12_91173_680096 : frontier 9 ⟨680096, by decide⟩
    (prefixCache 12 91173) (prefixPartial 12 91173) = false := by
  decide +kernel

theorem node_context_12_91173_680096 : EJMOriginalGlobalDAGData.nodes 9 ⟨680096, by decide⟩ =
    .split (coordinate 12) (![⟨680044, by decide⟩,⟨680073, by decide⟩,⟨680090, by decide⟩,⟨680095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91173_680096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91173 ⟨680096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91173
    ⟨680096, by decide⟩ (by decide) (![⟨680044, by decide⟩,⟨680073, by decide⟩,⟨680090, by decide⟩,⟨680095, by decide⟩]) unmarked_context_12_91173_680096 node_context_12_91173_680096
  intro a
  fin_cases a
  · exact context_13_364692_680044
  · exact context_13_364693_680073
  · exact context_13_364694_680090
  · exact context_13_364695_680095

theorem selected_cut_26890 : selected 8 ⟨680107, by decide⟩
    (prefixPartial 13 364696) = some ⟨13, 2, 0, 680107, 364696, 825, 16384⟩ := by
  decide +kernel

theorem context_13_364696_680107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364696 ⟨680107, by decide⟩ :=
  accepted_of_selected 13 364696 ⟨680107, by decide⟩ ⟨13, 2, 0, 680107, 364696, 825, 16384⟩
    (by decide) selected_cut_26890

theorem selected_cut_26891 : selected 8 ⟨680134, by decide⟩
    (prefixPartial 13 364697) = some ⟨13, 2, 0, 680134, 364697, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_364697_680134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364697 ⟨680134, by decide⟩ :=
  accepted_of_selected 13 364697 ⟨680134, by decide⟩ ⟨13, 2, 0, 680134, 364697, 1733, 16384⟩
    (by decide) selected_cut_26891

theorem selected_cut_26892 : selected 8 ⟨680151, by decide⟩
    (prefixPartial 13 364698) = some ⟨13, 2, 0, 680151, 364698, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_364698_680151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364698 ⟨680151, by decide⟩ :=
  accepted_of_selected 13 364698 ⟨680151, by decide⟩ ⟨13, 2, 0, 680151, 364698, 1245, 16384⟩
    (by decide) selected_cut_26892

theorem selected_cut_26893 : selected 8 ⟨680156, by decide⟩
    (prefixPartial 13 364699) = some ⟨13, 2, 0, 680156, 364699, 797, 16384⟩ := by
  decide +kernel

theorem context_13_364699_680156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364699 ⟨680156, by decide⟩ :=
  accepted_of_selected 13 364699 ⟨680156, by decide⟩ ⟨13, 2, 0, 680156, 364699, 797, 16384⟩
    (by decide) selected_cut_26893

theorem unmarked_context_12_91174_680157 : frontier 9 ⟨680157, by decide⟩
    (prefixCache 12 91174) (prefixPartial 12 91174) = false := by
  decide +kernel

theorem node_context_12_91174_680157 : EJMOriginalGlobalDAGData.nodes 9 ⟨680157, by decide⟩ =
    .split (coordinate 12) (![⟨680107, by decide⟩,⟨680134, by decide⟩,⟨680151, by decide⟩,⟨680156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91174_680157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91174 ⟨680157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91174
    ⟨680157, by decide⟩ (by decide) (![⟨680107, by decide⟩,⟨680134, by decide⟩,⟨680151, by decide⟩,⟨680156, by decide⟩]) unmarked_context_12_91174_680157 node_context_12_91174_680157
  intro a
  fin_cases a
  · exact context_13_364696_680107
  · exact context_13_364697_680134
  · exact context_13_364698_680151
  · exact context_13_364699_680156

theorem selected_cut_26894 : selected 8 ⟨680173, by decide⟩
    (prefixPartial 13 364700) = some ⟨13, 2, 0, 680173, 364700, 873, 16384⟩ := by
  decide +kernel

theorem context_13_364700_680173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364700 ⟨680173, by decide⟩ :=
  accepted_of_selected 13 364700 ⟨680173, by decide⟩ ⟨13, 2, 0, 680173, 364700, 873, 16384⟩
    (by decide) selected_cut_26894

theorem selected_cut_26895 : selected 8 ⟨680209, by decide⟩
    (prefixPartial 13 364701) = some ⟨13, 2, 0, 680209, 364701, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_364701_680209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364701 ⟨680209, by decide⟩ :=
  accepted_of_selected 13 364701 ⟨680209, by decide⟩ ⟨13, 2, 0, 680209, 364701, 1985, 16384⟩
    (by decide) selected_cut_26895

theorem selected_cut_26896 : selected 8 ⟨680226, by decide⟩
    (prefixPartial 13 364702) = some ⟨13, 2, 0, 680226, 364702, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_364702_680226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364702 ⟨680226, by decide⟩ :=
  accepted_of_selected 13 364702 ⟨680226, by decide⟩ ⟨13, 2, 0, 680226, 364702, 1425, 16384⟩
    (by decide) selected_cut_26896

theorem selected_cut_26897 : selected 8 ⟨680231, by decide⟩
    (prefixPartial 13 364703) = some ⟨13, 2, 0, 680231, 364703, 737, 16384⟩ := by
  decide +kernel

theorem context_13_364703_680231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364703 ⟨680231, by decide⟩ :=
  accepted_of_selected 13 364703 ⟨680231, by decide⟩ ⟨13, 2, 0, 680231, 364703, 737, 16384⟩
    (by decide) selected_cut_26897

theorem unmarked_context_12_91175_680232 : frontier 9 ⟨680232, by decide⟩
    (prefixCache 12 91175) (prefixPartial 12 91175) = false := by
  decide +kernel

theorem node_context_12_91175_680232 : EJMOriginalGlobalDAGData.nodes 9 ⟨680232, by decide⟩ =
    .split (coordinate 12) (![⟨680173, by decide⟩,⟨680209, by decide⟩,⟨680226, by decide⟩,⟨680231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91175_680232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91175 ⟨680232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91175
    ⟨680232, by decide⟩ (by decide) (![⟨680173, by decide⟩,⟨680209, by decide⟩,⟨680226, by decide⟩,⟨680231, by decide⟩]) unmarked_context_12_91175_680232 node_context_12_91175_680232
  intro a
  fin_cases a
  · exact context_13_364700_680173
  · exact context_13_364701_680209
  · exact context_13_364702_680226
  · exact context_13_364703_680231

theorem unmarked_context_11_22793_680233 : frontier 10 ⟨680233, by decide⟩
    (prefixCache 11 22793) (prefixPartial 11 22793) = false := by
  decide +kernel

theorem node_context_11_22793_680233 : EJMOriginalGlobalDAGData.nodes 10 ⟨680233, by decide⟩ =
    .split (coordinate 11) (![⟨680030, by decide⟩,⟨680096, by decide⟩,⟨680157, by decide⟩,⟨680232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22793_680233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22793 ⟨680233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22793
    ⟨680233, by decide⟩ (by decide) (![⟨680030, by decide⟩,⟨680096, by decide⟩,⟨680157, by decide⟩,⟨680232, by decide⟩]) unmarked_context_11_22793_680233 node_context_11_22793_680233
  intro a
  fin_cases a
  · exact context_12_91172_680030
  · exact context_12_91173_680096
  · exact context_12_91174_680157
  · exact context_12_91175_680232

theorem selected_cut_26898 : selected 8 ⟨680243, by decide⟩
    (prefixPartial 13 364704) = some ⟨13, 2, 0, 680243, 364704, 625, 16384⟩ := by
  decide +kernel

theorem context_13_364704_680243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364704 ⟨680243, by decide⟩ :=
  accepted_of_selected 13 364704 ⟨680243, by decide⟩ ⟨13, 2, 0, 680243, 364704, 625, 16384⟩
    (by decide) selected_cut_26898

theorem selected_cut_26899 : selected 8 ⟨680296, by decide⟩
    (prefixPartial 13 364705) = some ⟨13, 2, 0, 680296, 364705, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_364705_680296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364705 ⟨680296, by decide⟩ :=
  accepted_of_selected 13 364705 ⟨680296, by decide⟩ ⟨13, 2, 0, 680296, 364705, 1937, 16384⟩
    (by decide) selected_cut_26899

theorem selected_cut_26900 : selected 8 ⟨680310, by decide⟩
    (prefixPartial 13 364706) = some ⟨13, 2, 0, 680310, 364706, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_364706_680310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364706 ⟨680310, by decide⟩ :=
  accepted_of_selected 13 364706 ⟨680310, by decide⟩ ⟨13, 2, 0, 680310, 364706, 1193, 16384⟩
    (by decide) selected_cut_26900

theorem selected_cut_26901 : selected 8 ⟨680316, by decide⟩
    (prefixPartial 13 364707) = some ⟨13, 2, 0, 680316, 364707, 833, 16384⟩ := by
  decide +kernel

theorem context_13_364707_680316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364707 ⟨680316, by decide⟩ :=
  accepted_of_selected 13 364707 ⟨680316, by decide⟩ ⟨13, 2, 0, 680316, 364707, 833, 16384⟩
    (by decide) selected_cut_26901

theorem unmarked_context_12_91176_680317 : frontier 9 ⟨680317, by decide⟩
    (prefixCache 12 91176) (prefixPartial 12 91176) = false := by
  decide +kernel

theorem node_context_12_91176_680317 : EJMOriginalGlobalDAGData.nodes 9 ⟨680317, by decide⟩ =
    .split (coordinate 12) (![⟨680243, by decide⟩,⟨680296, by decide⟩,⟨680310, by decide⟩,⟨680316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91176_680317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91176 ⟨680317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91176
    ⟨680317, by decide⟩ (by decide) (![⟨680243, by decide⟩,⟨680296, by decide⟩,⟨680310, by decide⟩,⟨680316, by decide⟩]) unmarked_context_12_91176_680317 node_context_12_91176_680317
  intro a
  fin_cases a
  · exact context_13_364704_680243
  · exact context_13_364705_680296
  · exact context_13_364706_680310
  · exact context_13_364707_680316

theorem selected_cut_26902 : selected 8 ⟨680336, by decide⟩
    (prefixPartial 13 364708) = some ⟨13, 2, 0, 680336, 364708, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_364708_680336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364708 ⟨680336, by decide⟩ :=
  accepted_of_selected 13 364708 ⟨680336, by decide⟩ ⟨13, 2, 0, 680336, 364708, 1001, 16384⟩
    (by decide) selected_cut_26902

theorem selected_cut_26903 : selected 8 ⟨680379, by decide⟩
    (prefixPartial 13 364709) = some ⟨13, 2, 0, 680379, 364709, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_364709_680379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364709 ⟨680379, by decide⟩ :=
  accepted_of_selected 13 364709 ⟨680379, by decide⟩ ⟨13, 2, 0, 680379, 364709, 2125, 16384⟩
    (by decide) selected_cut_26903

theorem selected_cut_26904 : selected 8 ⟨680402, by decide⟩
    (prefixPartial 13 364710) = some ⟨13, 2, 0, 680402, 364710, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_364710_680402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364710 ⟨680402, by decide⟩ :=
  accepted_of_selected 13 364710 ⟨680402, by decide⟩ ⟨13, 2, 0, 680402, 364710, 1553, 16384⟩
    (by decide) selected_cut_26904

theorem selected_cut_26905 : selected 8 ⟨680413, by decide⟩
    (prefixPartial 13 364711) = some ⟨13, 2, 0, 680413, 364711, 925, 16384⟩ := by
  decide +kernel

theorem context_13_364711_680413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364711 ⟨680413, by decide⟩ :=
  accepted_of_selected 13 364711 ⟨680413, by decide⟩ ⟨13, 2, 0, 680413, 364711, 925, 16384⟩
    (by decide) selected_cut_26905

theorem unmarked_context_12_91177_680414 : frontier 9 ⟨680414, by decide⟩
    (prefixCache 12 91177) (prefixPartial 12 91177) = false := by
  decide +kernel

theorem node_context_12_91177_680414 : EJMOriginalGlobalDAGData.nodes 9 ⟨680414, by decide⟩ =
    .split (coordinate 12) (![⟨680336, by decide⟩,⟨680379, by decide⟩,⟨680402, by decide⟩,⟨680413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91177_680414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91177 ⟨680414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91177
    ⟨680414, by decide⟩ (by decide) (![⟨680336, by decide⟩,⟨680379, by decide⟩,⟨680402, by decide⟩,⟨680413, by decide⟩]) unmarked_context_12_91177_680414 node_context_12_91177_680414
  intro a
  fin_cases a
  · exact context_13_364708_680336
  · exact context_13_364709_680379
  · exact context_13_364710_680402
  · exact context_13_364711_680413

theorem selected_cut_26906 : selected 8 ⟨680425, by decide⟩
    (prefixPartial 13 364712) = some ⟨13, 2, 0, 680425, 364712, 777, 16384⟩ := by
  decide +kernel

theorem context_13_364712_680425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364712 ⟨680425, by decide⟩ :=
  accepted_of_selected 13 364712 ⟨680425, by decide⟩ ⟨13, 2, 0, 680425, 364712, 777, 16384⟩
    (by decide) selected_cut_26906

theorem selected_cut_26907 : selected 8 ⟨680462, by decide⟩
    (prefixPartial 13 364713) = some ⟨13, 2, 0, 680462, 364713, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_364713_680462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364713 ⟨680462, by decide⟩ :=
  accepted_of_selected 13 364713 ⟨680462, by decide⟩ ⟨13, 2, 0, 680462, 364713, 1721, 16384⟩
    (by decide) selected_cut_26907

theorem selected_cut_26908 : selected 8 ⟨680476, by decide⟩
    (prefixPartial 13 364714) = some ⟨13, 2, 0, 680476, 364714, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_364714_680476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364714 ⟨680476, by decide⟩ :=
  accepted_of_selected 13 364714 ⟨680476, by decide⟩ ⟨13, 2, 0, 680476, 364714, 1241, 16384⟩
    (by decide) selected_cut_26908

theorem selected_cut_26909 : selected 8 ⟨680482, by decide⟩
    (prefixPartial 13 364715) = some ⟨13, 2, 0, 680482, 364715, 853, 16384⟩ := by
  decide +kernel

theorem context_13_364715_680482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364715 ⟨680482, by decide⟩ :=
  accepted_of_selected 13 364715 ⟨680482, by decide⟩ ⟨13, 2, 0, 680482, 364715, 853, 16384⟩
    (by decide) selected_cut_26909

theorem unmarked_context_12_91178_680483 : frontier 9 ⟨680483, by decide⟩
    (prefixCache 12 91178) (prefixPartial 12 91178) = false := by
  decide +kernel

theorem node_context_12_91178_680483 : EJMOriginalGlobalDAGData.nodes 9 ⟨680483, by decide⟩ =
    .split (coordinate 12) (![⟨680425, by decide⟩,⟨680462, by decide⟩,⟨680476, by decide⟩,⟨680482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91178_680483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91178 ⟨680483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91178
    ⟨680483, by decide⟩ (by decide) (![⟨680425, by decide⟩,⟨680462, by decide⟩,⟨680476, by decide⟩,⟨680482, by decide⟩]) unmarked_context_12_91178_680483 node_context_12_91178_680483
  intro a
  fin_cases a
  · exact context_13_364712_680425
  · exact context_13_364713_680462
  · exact context_13_364714_680476
  · exact context_13_364715_680482

theorem selected_cut_26910 : selected 8 ⟨680499, by decide⟩
    (prefixPartial 13 364716) = some ⟨13, 2, 0, 680499, 364716, 801, 16384⟩ := by
  decide +kernel

theorem context_13_364716_680499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364716 ⟨680499, by decide⟩ :=
  accepted_of_selected 13 364716 ⟨680499, by decide⟩ ⟨13, 2, 0, 680499, 364716, 801, 16384⟩
    (by decide) selected_cut_26910

theorem selected_cut_26911 : selected 8 ⟨680544, by decide⟩
    (prefixPartial 13 364717) = some ⟨13, 2, 0, 680544, 364717, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_364717_680544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364717 ⟨680544, by decide⟩ :=
  accepted_of_selected 13 364717 ⟨680544, by decide⟩ ⟨13, 2, 0, 680544, 364717, 2345, 16384⟩
    (by decide) selected_cut_26911

theorem selected_cut_26912 : selected 8 ⟨680560, by decide⟩
    (prefixPartial 13 364718) = some ⟨13, 2, 0, 680560, 364718, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_364718_680560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364718 ⟨680560, by decide⟩ :=
  accepted_of_selected 13 364718 ⟨680560, by decide⟩ ⟨13, 2, 0, 680560, 364718, 1445, 16384⟩
    (by decide) selected_cut_26912

theorem selected_cut_26913 : selected 8 ⟨680568, by decide⟩
    (prefixPartial 13 364719) = some ⟨13, 2, 0, 680568, 364719, 793, 16384⟩ := by
  decide +kernel

theorem context_13_364719_680568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364719 ⟨680568, by decide⟩ :=
  accepted_of_selected 13 364719 ⟨680568, by decide⟩ ⟨13, 2, 0, 680568, 364719, 793, 16384⟩
    (by decide) selected_cut_26913

theorem unmarked_context_12_91179_680569 : frontier 9 ⟨680569, by decide⟩
    (prefixCache 12 91179) (prefixPartial 12 91179) = false := by
  decide +kernel

theorem node_context_12_91179_680569 : EJMOriginalGlobalDAGData.nodes 9 ⟨680569, by decide⟩ =
    .split (coordinate 12) (![⟨680499, by decide⟩,⟨680544, by decide⟩,⟨680560, by decide⟩,⟨680568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91179_680569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91179 ⟨680569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91179
    ⟨680569, by decide⟩ (by decide) (![⟨680499, by decide⟩,⟨680544, by decide⟩,⟨680560, by decide⟩,⟨680568, by decide⟩]) unmarked_context_12_91179_680569 node_context_12_91179_680569
  intro a
  fin_cases a
  · exact context_13_364716_680499
  · exact context_13_364717_680544
  · exact context_13_364718_680560
  · exact context_13_364719_680568

theorem unmarked_context_11_22794_680570 : frontier 10 ⟨680570, by decide⟩
    (prefixCache 11 22794) (prefixPartial 11 22794) = false := by
  decide +kernel

theorem node_context_11_22794_680570 : EJMOriginalGlobalDAGData.nodes 10 ⟨680570, by decide⟩ =
    .split (coordinate 11) (![⟨680317, by decide⟩,⟨680414, by decide⟩,⟨680483, by decide⟩,⟨680569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22794_680570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22794 ⟨680570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22794
    ⟨680570, by decide⟩ (by decide) (![⟨680317, by decide⟩,⟨680414, by decide⟩,⟨680483, by decide⟩,⟨680569, by decide⟩]) unmarked_context_11_22794_680570 node_context_11_22794_680570
  intro a
  fin_cases a
  · exact context_12_91176_680317
  · exact context_12_91177_680414
  · exact context_12_91178_680483
  · exact context_12_91179_680569

theorem selected_cut_26914 : selected 8 ⟨680581, by decide⟩
    (prefixPartial 13 364720) = some ⟨13, 2, 0, 680581, 364720, 577, 16384⟩ := by
  decide +kernel

theorem context_13_364720_680581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364720 ⟨680581, by decide⟩ :=
  accepted_of_selected 13 364720 ⟨680581, by decide⟩ ⟨13, 2, 0, 680581, 364720, 577, 16384⟩
    (by decide) selected_cut_26914

theorem selected_cut_26915 : selected 8 ⟨680627, by decide⟩
    (prefixPartial 13 364721) = some ⟨13, 2, 0, 680627, 364721, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_364721_680627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364721 ⟨680627, by decide⟩ :=
  accepted_of_selected 13 364721 ⟨680627, by decide⟩ ⟨13, 2, 0, 680627, 364721, 1941, 16384⟩
    (by decide) selected_cut_26915

theorem selected_cut_26916 : selected 8 ⟨680641, by decide⟩
    (prefixPartial 13 364722) = some ⟨13, 2, 0, 680641, 364722, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_364722_680641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364722 ⟨680641, by decide⟩ :=
  accepted_of_selected 13 364722 ⟨680641, by decide⟩ ⟨13, 2, 0, 680641, 364722, 1101, 16384⟩
    (by decide) selected_cut_26916

theorem selected_cut_26917 : selected 8 ⟨680646, by decide⟩
    (prefixPartial 13 364723) = some ⟨13, 2, 0, 680646, 364723, 785, 16384⟩ := by
  decide +kernel

theorem context_13_364723_680646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364723 ⟨680646, by decide⟩ :=
  accepted_of_selected 13 364723 ⟨680646, by decide⟩ ⟨13, 2, 0, 680646, 364723, 785, 16384⟩
    (by decide) selected_cut_26917

theorem unmarked_context_12_91180_680647 : frontier 9 ⟨680647, by decide⟩
    (prefixCache 12 91180) (prefixPartial 12 91180) = false := by
  decide +kernel

theorem node_context_12_91180_680647 : EJMOriginalGlobalDAGData.nodes 9 ⟨680647, by decide⟩ =
    .split (coordinate 12) (![⟨680581, by decide⟩,⟨680627, by decide⟩,⟨680641, by decide⟩,⟨680646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91180_680647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91180 ⟨680647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91180
    ⟨680647, by decide⟩ (by decide) (![⟨680581, by decide⟩,⟨680627, by decide⟩,⟨680641, by decide⟩,⟨680646, by decide⟩]) unmarked_context_12_91180_680647 node_context_12_91180_680647
  intro a
  fin_cases a
  · exact context_13_364720_680581
  · exact context_13_364721_680627
  · exact context_13_364722_680641
  · exact context_13_364723_680646

theorem selected_cut_26918 : selected 8 ⟨680667, by decide⟩
    (prefixPartial 13 364724) = some ⟨13, 2, 0, 680667, 364724, 809, 16384⟩ := by
  decide +kernel

theorem context_13_364724_680667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364724 ⟨680667, by decide⟩ :=
  accepted_of_selected 13 364724 ⟨680667, by decide⟩ ⟨13, 2, 0, 680667, 364724, 809, 16384⟩
    (by decide) selected_cut_26918

theorem selected_cut_26919 : selected 8 ⟨680711, by decide⟩
    (prefixPartial 13 364725) = some ⟨13, 2, 0, 680711, 364725, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_364725_680711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364725 ⟨680711, by decide⟩ :=
  accepted_of_selected 13 364725 ⟨680711, by decide⟩ ⟨13, 2, 0, 680711, 364725, 2241, 16384⟩
    (by decide) selected_cut_26919

theorem selected_cut_26920 : selected 8 ⟨680728, by decide⟩
    (prefixPartial 13 364726) = some ⟨13, 2, 0, 680728, 364726, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_364726_680728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364726 ⟨680728, by decide⟩ :=
  accepted_of_selected 13 364726 ⟨680728, by decide⟩ ⟨13, 2, 0, 680728, 364726, 1389, 16384⟩
    (by decide) selected_cut_26920

theorem selected_cut_26921 : selected 8 ⟨680733, by decide⟩
    (prefixPartial 13 364727) = some ⟨13, 2, 0, 680733, 364727, 801, 16384⟩ := by
  decide +kernel

theorem context_13_364727_680733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364727 ⟨680733, by decide⟩ :=
  accepted_of_selected 13 364727 ⟨680733, by decide⟩ ⟨13, 2, 0, 680733, 364727, 801, 16384⟩
    (by decide) selected_cut_26921

theorem unmarked_context_12_91181_680734 : frontier 9 ⟨680734, by decide⟩
    (prefixCache 12 91181) (prefixPartial 12 91181) = false := by
  decide +kernel

theorem node_context_12_91181_680734 : EJMOriginalGlobalDAGData.nodes 9 ⟨680734, by decide⟩ =
    .split (coordinate 12) (![⟨680667, by decide⟩,⟨680711, by decide⟩,⟨680728, by decide⟩,⟨680733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91181_680734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91181 ⟨680734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91181
    ⟨680734, by decide⟩ (by decide) (![⟨680667, by decide⟩,⟨680711, by decide⟩,⟨680728, by decide⟩,⟨680733, by decide⟩]) unmarked_context_12_91181_680734 node_context_12_91181_680734
  intro a
  fin_cases a
  · exact context_13_364724_680667
  · exact context_13_364725_680711
  · exact context_13_364726_680728
  · exact context_13_364727_680733

theorem selected_cut_26922 : selected 8 ⟨680744, by decide⟩
    (prefixPartial 13 364728) = some ⟨13, 2, 0, 680744, 364728, 649, 16384⟩ := by
  decide +kernel

theorem context_13_364728_680744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364728 ⟨680744, by decide⟩ :=
  accepted_of_selected 13 364728 ⟨680744, by decide⟩ ⟨13, 2, 0, 680744, 364728, 649, 16384⟩
    (by decide) selected_cut_26922

theorem selected_cut_26923 : selected 8 ⟨680781, by decide⟩
    (prefixPartial 13 364729) = some ⟨13, 2, 0, 680781, 364729, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_364729_680781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364729 ⟨680781, by decide⟩ :=
  accepted_of_selected 13 364729 ⟨680781, by decide⟩ ⟨13, 2, 0, 680781, 364729, 2073, 16384⟩
    (by decide) selected_cut_26923

theorem selected_cut_26924 : selected 8 ⟨680797, by decide⟩
    (prefixPartial 13 364730) = some ⟨13, 2, 0, 680797, 364730, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_364730_680797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364730 ⟨680797, by decide⟩ :=
  accepted_of_selected 13 364730 ⟨680797, by decide⟩ ⟨13, 2, 0, 680797, 364730, 1313, 16384⟩
    (by decide) selected_cut_26924

theorem selected_cut_26925 : selected 8 ⟨680802, by decide⟩
    (prefixPartial 13 364731) = some ⟨13, 2, 0, 680802, 364731, 865, 16384⟩ := by
  decide +kernel

theorem context_13_364731_680802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364731 ⟨680802, by decide⟩ :=
  accepted_of_selected 13 364731 ⟨680802, by decide⟩ ⟨13, 2, 0, 680802, 364731, 865, 16384⟩
    (by decide) selected_cut_26925

theorem unmarked_context_12_91182_680803 : frontier 9 ⟨680803, by decide⟩
    (prefixCache 12 91182) (prefixPartial 12 91182) = false := by
  decide +kernel

theorem node_context_12_91182_680803 : EJMOriginalGlobalDAGData.nodes 9 ⟨680803, by decide⟩ =
    .split (coordinate 12) (![⟨680744, by decide⟩,⟨680781, by decide⟩,⟨680797, by decide⟩,⟨680802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91182_680803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91182 ⟨680803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91182
    ⟨680803, by decide⟩ (by decide) (![⟨680744, by decide⟩,⟨680781, by decide⟩,⟨680797, by decide⟩,⟨680802, by decide⟩]) unmarked_context_12_91182_680803 node_context_12_91182_680803
  intro a
  fin_cases a
  · exact context_13_364728_680744
  · exact context_13_364729_680781
  · exact context_13_364730_680797
  · exact context_13_364731_680802

theorem selected_cut_26926 : selected 8 ⟨680815, by decide⟩
    (prefixPartial 13 364732) = some ⟨13, 2, 0, 680815, 364732, 585, 16384⟩ := by
  decide +kernel

theorem context_13_364732_680815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364732 ⟨680815, by decide⟩ :=
  accepted_of_selected 13 364732 ⟨680815, by decide⟩ ⟨13, 2, 0, 680815, 364732, 585, 16384⟩
    (by decide) selected_cut_26926

theorem selected_cut_26927 : selected 8 ⟨680852, by decide⟩
    (prefixPartial 13 364733) = some ⟨13, 2, 0, 680852, 364733, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_364733_680852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364733 ⟨680852, by decide⟩ :=
  accepted_of_selected 13 364733 ⟨680852, by decide⟩ ⟨13, 2, 0, 680852, 364733, 2229, 16384⟩
    (by decide) selected_cut_26927

theorem selected_cut_26928 : selected 8 ⟨680869, by decide⟩
    (prefixPartial 13 364734) = some ⟨13, 2, 0, 680869, 364734, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_364734_680869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364734 ⟨680869, by decide⟩ :=
  accepted_of_selected 13 364734 ⟨680869, by decide⟩ ⟨13, 2, 0, 680869, 364734, 1309, 16384⟩
    (by decide) selected_cut_26928

theorem selected_cut_26929 : selected 8 ⟨680874, by decide⟩
    (prefixPartial 13 364735) = some ⟨13, 2, 0, 680874, 364735, 701, 16384⟩ := by
  decide +kernel

theorem context_13_364735_680874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364735 ⟨680874, by decide⟩ :=
  accepted_of_selected 13 364735 ⟨680874, by decide⟩ ⟨13, 2, 0, 680874, 364735, 701, 16384⟩
    (by decide) selected_cut_26929

theorem unmarked_context_12_91183_680875 : frontier 9 ⟨680875, by decide⟩
    (prefixCache 12 91183) (prefixPartial 12 91183) = false := by
  decide +kernel

theorem node_context_12_91183_680875 : EJMOriginalGlobalDAGData.nodes 9 ⟨680875, by decide⟩ =
    .split (coordinate 12) (![⟨680815, by decide⟩,⟨680852, by decide⟩,⟨680869, by decide⟩,⟨680874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91183_680875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91183 ⟨680875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91183
    ⟨680875, by decide⟩ (by decide) (![⟨680815, by decide⟩,⟨680852, by decide⟩,⟨680869, by decide⟩,⟨680874, by decide⟩]) unmarked_context_12_91183_680875 node_context_12_91183_680875
  intro a
  fin_cases a
  · exact context_13_364732_680815
  · exact context_13_364733_680852
  · exact context_13_364734_680869
  · exact context_13_364735_680874

theorem unmarked_context_11_22795_680876 : frontier 10 ⟨680876, by decide⟩
    (prefixCache 11 22795) (prefixPartial 11 22795) = false := by
  decide +kernel

theorem node_context_11_22795_680876 : EJMOriginalGlobalDAGData.nodes 10 ⟨680876, by decide⟩ =
    .split (coordinate 11) (![⟨680647, by decide⟩,⟨680734, by decide⟩,⟨680803, by decide⟩,⟨680875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22795_680876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22795 ⟨680876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22795
    ⟨680876, by decide⟩ (by decide) (![⟨680647, by decide⟩,⟨680734, by decide⟩,⟨680803, by decide⟩,⟨680875, by decide⟩]) unmarked_context_11_22795_680876 node_context_11_22795_680876
  intro a
  fin_cases a
  · exact context_12_91180_680647
  · exact context_12_91181_680734
  · exact context_12_91182_680803
  · exact context_12_91183_680875

theorem unmarked_context_10_5698_680877 : frontier 11 ⟨680877, by decide⟩
    (prefixCache 10 5698) (prefixPartial 10 5698) = false := by
  decide +kernel

theorem node_context_10_5698_680877 : EJMOriginalGlobalDAGData.nodes 11 ⟨680877, by decide⟩ =
    .split (coordinate 10) (![⟨679964, by decide⟩,⟨680233, by decide⟩,⟨680570, by decide⟩,⟨680876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5698_680877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5698 ⟨680877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5698
    ⟨680877, by decide⟩ (by decide) (![⟨679964, by decide⟩,⟨680233, by decide⟩,⟨680570, by decide⟩,⟨680876, by decide⟩]) unmarked_context_10_5698_680877 node_context_10_5698_680877
  intro a
  fin_cases a
  · exact context_11_22792_679964
  · exact context_11_22793_680233
  · exact context_11_22794_680570
  · exact context_11_22795_680876

theorem selected_cut_26930 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 91184) = some ⟨12, 1, 0, 641337, 91184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91184_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91184 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 91184 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 91184, 1, 65536⟩
    (by decide) selected_cut_26930

theorem selected_cut_26931 : selected 8 ⟨680896, by decide⟩
    (prefixPartial 13 364740) = some ⟨13, 2, 0, 680896, 364740, 733, 16384⟩ := by
  decide +kernel

theorem context_13_364740_680896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364740 ⟨680896, by decide⟩ :=
  accepted_of_selected 13 364740 ⟨680896, by decide⟩ ⟨13, 2, 0, 680896, 364740, 733, 16384⟩
    (by decide) selected_cut_26931

theorem selected_cut_26932 : selected 8 ⟨680922, by decide⟩
    (prefixPartial 13 364741) = some ⟨13, 2, 0, 680922, 364741, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_364741_680922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364741 ⟨680922, by decide⟩ :=
  accepted_of_selected 13 364741 ⟨680922, by decide⟩ ⟨13, 2, 0, 680922, 364741, 1757, 16384⟩
    (by decide) selected_cut_26932

theorem selected_cut_26933 : selected 8 ⟨680944, by decide⟩
    (prefixPartial 13 364742) = some ⟨13, 2, 0, 680944, 364742, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_364742_680944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364742 ⟨680944, by decide⟩ :=
  accepted_of_selected 13 364742 ⟨680944, by decide⟩ ⟨13, 2, 0, 680944, 364742, 1465, 16384⟩
    (by decide) selected_cut_26933

theorem selected_cut_26934 : selected 8 ⟨680951, by decide⟩
    (prefixPartial 13 364743) = some ⟨13, 2, 0, 680951, 364743, 681, 16384⟩ := by
  decide +kernel

theorem context_13_364743_680951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364743 ⟨680951, by decide⟩ :=
  accepted_of_selected 13 364743 ⟨680951, by decide⟩ ⟨13, 2, 0, 680951, 364743, 681, 16384⟩
    (by decide) selected_cut_26934

theorem unmarked_context_12_91185_680952 : frontier 9 ⟨680952, by decide⟩
    (prefixCache 12 91185) (prefixPartial 12 91185) = false := by
  decide +kernel

theorem node_context_12_91185_680952 : EJMOriginalGlobalDAGData.nodes 9 ⟨680952, by decide⟩ =
    .split (coordinate 12) (![⟨680896, by decide⟩,⟨680922, by decide⟩,⟨680944, by decide⟩,⟨680951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91185_680952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91185 ⟨680952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91185
    ⟨680952, by decide⟩ (by decide) (![⟨680896, by decide⟩,⟨680922, by decide⟩,⟨680944, by decide⟩,⟨680951, by decide⟩]) unmarked_context_12_91185_680952 node_context_12_91185_680952
  intro a
  fin_cases a
  · exact context_13_364740_680896
  · exact context_13_364741_680922
  · exact context_13_364742_680944
  · exact context_13_364743_680951

theorem selected_cut_26935 : selected 8 ⟨680959, by decide⟩
    (prefixPartial 13 364744) = some ⟨13, 2, 0, 680959, 364744, 673, 16384⟩ := by
  decide +kernel

theorem context_13_364744_680959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364744 ⟨680959, by decide⟩ :=
  accepted_of_selected 13 364744 ⟨680959, by decide⟩ ⟨13, 2, 0, 680959, 364744, 673, 16384⟩
    (by decide) selected_cut_26935

theorem selected_cut_26936 : selected 8 ⟨680983, by decide⟩
    (prefixPartial 13 364745) = some ⟨13, 2, 0, 680983, 364745, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_364745_680983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364745 ⟨680983, by decide⟩ :=
  accepted_of_selected 13 364745 ⟨680983, by decide⟩ ⟨13, 2, 0, 680983, 364745, 1717, 16384⟩
    (by decide) selected_cut_26936

theorem selected_cut_26937 : selected 8 ⟨680997, by decide⟩
    (prefixPartial 13 364746) = some ⟨13, 2, 0, 680997, 364746, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_364746_680997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364746 ⟨680997, by decide⟩ :=
  accepted_of_selected 13 364746 ⟨680997, by decide⟩ ⟨13, 2, 0, 680997, 364746, 1181, 16384⟩
    (by decide) selected_cut_26937

theorem selected_cut_26938 : selected 8 ⟨681007, by decide⟩
    (prefixPartial 13 364747) = some ⟨13, 2, 0, 681007, 364747, 861, 16384⟩ := by
  decide +kernel

theorem context_13_364747_681007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364747 ⟨681007, by decide⟩ :=
  accepted_of_selected 13 364747 ⟨681007, by decide⟩ ⟨13, 2, 0, 681007, 364747, 861, 16384⟩
    (by decide) selected_cut_26938

theorem unmarked_context_12_91186_681008 : frontier 9 ⟨681008, by decide⟩
    (prefixCache 12 91186) (prefixPartial 12 91186) = false := by
  decide +kernel

theorem node_context_12_91186_681008 : EJMOriginalGlobalDAGData.nodes 9 ⟨681008, by decide⟩ =
    .split (coordinate 12) (![⟨680959, by decide⟩,⟨680983, by decide⟩,⟨680997, by decide⟩,⟨681007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91186_681008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91186 ⟨681008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91186
    ⟨681008, by decide⟩ (by decide) (![⟨680959, by decide⟩,⟨680983, by decide⟩,⟨680997, by decide⟩,⟨681007, by decide⟩]) unmarked_context_12_91186_681008 node_context_12_91186_681008
  intro a
  fin_cases a
  · exact context_13_364744_680959
  · exact context_13_364745_680983
  · exact context_13_364746_680997
  · exact context_13_364747_681007

theorem selected_cut_26939 : selected 8 ⟨681019, by decide⟩
    (prefixPartial 13 364748) = some ⟨13, 2, 0, 681019, 364748, 653, 16384⟩ := by
  decide +kernel

theorem context_13_364748_681019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364748 ⟨681019, by decide⟩ :=
  accepted_of_selected 13 364748 ⟨681019, by decide⟩ ⟨13, 2, 0, 681019, 364748, 653, 16384⟩
    (by decide) selected_cut_26939

theorem selected_cut_26940 : selected 8 ⟨681056, by decide⟩
    (prefixPartial 13 364749) = some ⟨13, 2, 0, 681056, 364749, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_364749_681056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364749 ⟨681056, by decide⟩ :=
  accepted_of_selected 13 364749 ⟨681056, by decide⟩ ⟨13, 2, 0, 681056, 364749, 2197, 16384⟩
    (by decide) selected_cut_26940

theorem selected_cut_26941 : selected 8 ⟨681078, by decide⟩
    (prefixPartial 13 364750) = some ⟨13, 2, 0, 681078, 364750, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_364750_681078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364750 ⟨681078, by decide⟩ :=
  accepted_of_selected 13 364750 ⟨681078, by decide⟩ ⟨13, 2, 0, 681078, 364750, 1561, 16384⟩
    (by decide) selected_cut_26941

theorem selected_cut_26942 : selected 8 ⟨681084, by decide⟩
    (prefixPartial 13 364751) = some ⟨13, 2, 0, 681084, 364751, 753, 16384⟩ := by
  decide +kernel

theorem context_13_364751_681084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364751 ⟨681084, by decide⟩ :=
  accepted_of_selected 13 364751 ⟨681084, by decide⟩ ⟨13, 2, 0, 681084, 364751, 753, 16384⟩
    (by decide) selected_cut_26942

theorem unmarked_context_12_91187_681085 : frontier 9 ⟨681085, by decide⟩
    (prefixCache 12 91187) (prefixPartial 12 91187) = false := by
  decide +kernel

theorem node_context_12_91187_681085 : EJMOriginalGlobalDAGData.nodes 9 ⟨681085, by decide⟩ =
    .split (coordinate 12) (![⟨681019, by decide⟩,⟨681056, by decide⟩,⟨681078, by decide⟩,⟨681084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91187_681085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91187 ⟨681085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91187
    ⟨681085, by decide⟩ (by decide) (![⟨681019, by decide⟩,⟨681056, by decide⟩,⟨681078, by decide⟩,⟨681084, by decide⟩]) unmarked_context_12_91187_681085 node_context_12_91187_681085
  intro a
  fin_cases a
  · exact context_13_364748_681019
  · exact context_13_364749_681056
  · exact context_13_364750_681078
  · exact context_13_364751_681084

theorem unmarked_context_11_22796_681086 : frontier 10 ⟨681086, by decide⟩
    (prefixCache 11 22796) (prefixPartial 11 22796) = false := by
  decide +kernel

theorem node_context_11_22796_681086 : EJMOriginalGlobalDAGData.nodes 10 ⟨681086, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨680952, by decide⟩,⟨681008, by decide⟩,⟨681085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22796_681086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22796 ⟨681086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22796
    ⟨681086, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨680952, by decide⟩,⟨681008, by decide⟩,⟨681085, by decide⟩]) unmarked_context_11_22796_681086 node_context_11_22796_681086
  intro a
  fin_cases a
  · exact context_12_91184_641337
  · exact context_12_91185_680952
  · exact context_12_91186_681008
  · exact context_12_91187_681085

theorem selected_cut_26943 : selected 9 ⟨681157, by decide⟩
    (prefixPartial 12 91188) = some ⟨12, 2, 0, 681157, 91188, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_91188_681157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91188 ⟨681157, by decide⟩ :=
  accepted_of_selected 12 91188 ⟨681157, by decide⟩ ⟨12, 2, 0, 681157, 91188, 4081, 65536⟩
    (by decide) selected_cut_26943

theorem selected_cut_26944 : selected 8 ⟨681169, by decide⟩
    (prefixPartial 13 364756) = some ⟨13, 2, 0, 681169, 364756, 465, 16384⟩ := by
  decide +kernel

theorem context_13_364756_681169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364756 ⟨681169, by decide⟩ :=
  accepted_of_selected 13 364756 ⟨681169, by decide⟩ ⟨13, 2, 0, 681169, 364756, 465, 16384⟩
    (by decide) selected_cut_26944

theorem selected_cut_26945 : selected 8 ⟨681197, by decide⟩
    (prefixPartial 13 364757) = some ⟨13, 2, 0, 681197, 364757, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_364757_681197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364757 ⟨681197, by decide⟩ :=
  accepted_of_selected 13 364757 ⟨681197, by decide⟩ ⟨13, 2, 0, 681197, 364757, 1689, 16384⟩
    (by decide) selected_cut_26945

theorem selected_cut_26946 : selected 8 ⟨681217, by decide⟩
    (prefixPartial 13 364758) = some ⟨13, 2, 0, 681217, 364758, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_364758_681217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364758 ⟨681217, by decide⟩ :=
  accepted_of_selected 13 364758 ⟨681217, by decide⟩ ⟨13, 2, 0, 681217, 364758, 1397, 16384⟩
    (by decide) selected_cut_26946

theorem selected_cut_26947 : selected 8 ⟨681224, by decide⟩
    (prefixPartial 13 364759) = some ⟨13, 2, 0, 681224, 364759, 621, 16384⟩ := by
  decide +kernel

theorem context_13_364759_681224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364759 ⟨681224, by decide⟩ :=
  accepted_of_selected 13 364759 ⟨681224, by decide⟩ ⟨13, 2, 0, 681224, 364759, 621, 16384⟩
    (by decide) selected_cut_26947

theorem unmarked_context_12_91189_681225 : frontier 9 ⟨681225, by decide⟩
    (prefixCache 12 91189) (prefixPartial 12 91189) = false := by
  decide +kernel

theorem node_context_12_91189_681225 : EJMOriginalGlobalDAGData.nodes 9 ⟨681225, by decide⟩ =
    .split (coordinate 12) (![⟨681169, by decide⟩,⟨681197, by decide⟩,⟨681217, by decide⟩,⟨681224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91189_681225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91189 ⟨681225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91189
    ⟨681225, by decide⟩ (by decide) (![⟨681169, by decide⟩,⟨681197, by decide⟩,⟨681217, by decide⟩,⟨681224, by decide⟩]) unmarked_context_12_91189_681225 node_context_12_91189_681225
  intro a
  fin_cases a
  · exact context_13_364756_681169
  · exact context_13_364757_681197
  · exact context_13_364758_681217
  · exact context_13_364759_681224

theorem selected_cut_26948 : selected 8 ⟨681233, by decide⟩
    (prefixPartial 13 364760) = some ⟨13, 2, 0, 681233, 364760, 509, 16384⟩ := by
  decide +kernel

theorem context_13_364760_681233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364760 ⟨681233, by decide⟩ :=
  accepted_of_selected 13 364760 ⟨681233, by decide⟩ ⟨13, 2, 0, 681233, 364760, 509, 16384⟩
    (by decide) selected_cut_26948

theorem selected_cut_26949 : selected 8 ⟨681262, by decide⟩
    (prefixPartial 13 364761) = some ⟨13, 2, 0, 681262, 364761, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_364761_681262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364761 ⟨681262, by decide⟩ :=
  accepted_of_selected 13 364761 ⟨681262, by decide⟩ ⟨13, 2, 0, 681262, 364761, 1969, 16384⟩
    (by decide) selected_cut_26949

theorem selected_cut_26950 : selected 8 ⟨681280, by decide⟩
    (prefixPartial 13 364762) = some ⟨13, 2, 0, 681280, 364762, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_364762_681280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364762 ⟨681280, by decide⟩ :=
  accepted_of_selected 13 364762 ⟨681280, by decide⟩ ⟨13, 2, 0, 681280, 364762, 1301, 16384⟩
    (by decide) selected_cut_26950

theorem selected_cut_26951 : selected 8 ⟨681286, by decide⟩
    (prefixPartial 13 364763) = some ⟨13, 2, 0, 681286, 364763, 749, 16384⟩ := by
  decide +kernel

theorem context_13_364763_681286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364763 ⟨681286, by decide⟩ :=
  accepted_of_selected 13 364763 ⟨681286, by decide⟩ ⟨13, 2, 0, 681286, 364763, 749, 16384⟩
    (by decide) selected_cut_26951

theorem unmarked_context_12_91190_681287 : frontier 9 ⟨681287, by decide⟩
    (prefixCache 12 91190) (prefixPartial 12 91190) = false := by
  decide +kernel

theorem node_context_12_91190_681287 : EJMOriginalGlobalDAGData.nodes 9 ⟨681287, by decide⟩ =
    .split (coordinate 12) (![⟨681233, by decide⟩,⟨681262, by decide⟩,⟨681280, by decide⟩,⟨681286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91190_681287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91190 ⟨681287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91190
    ⟨681287, by decide⟩ (by decide) (![⟨681233, by decide⟩,⟨681262, by decide⟩,⟨681280, by decide⟩,⟨681286, by decide⟩]) unmarked_context_12_91190_681287 node_context_12_91190_681287
  intro a
  fin_cases a
  · exact context_13_364760_681233
  · exact context_13_364761_681262
  · exact context_13_364762_681280
  · exact context_13_364763_681286

theorem selected_cut_26952 : selected 8 ⟨681294, by decide⟩
    (prefixPartial 13 364764) = some ⟨13, 2, 0, 681294, 364764, 485, 16384⟩ := by
  decide +kernel

theorem context_13_364764_681294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364764 ⟨681294, by decide⟩ :=
  accepted_of_selected 13 364764 ⟨681294, by decide⟩ ⟨13, 2, 0, 681294, 364764, 485, 16384⟩
    (by decide) selected_cut_26952

theorem selected_cut_26953 : selected 8 ⟨681343, by decide⟩
    (prefixPartial 13 364765) = some ⟨13, 2, 0, 681343, 364765, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_364765_681343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364765 ⟨681343, by decide⟩ :=
  accepted_of_selected 13 364765 ⟨681343, by decide⟩ ⟨13, 2, 0, 681343, 364765, 2377, 16384⟩
    (by decide) selected_cut_26953

theorem selected_cut_26954 : selected 8 ⟨681365, by decide⟩
    (prefixPartial 13 364766) = some ⟨13, 2, 0, 681365, 364766, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_364766_681365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364766 ⟨681365, by decide⟩ :=
  accepted_of_selected 13 364766 ⟨681365, by decide⟩ ⟨13, 2, 0, 681365, 364766, 1653, 16384⟩
    (by decide) selected_cut_26954

theorem selected_cut_26955 : selected 8 ⟨681371, by decide⟩
    (prefixPartial 13 364767) = some ⟨13, 2, 0, 681371, 364767, 737, 16384⟩ := by
  decide +kernel

theorem context_13_364767_681371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364767 ⟨681371, by decide⟩ :=
  accepted_of_selected 13 364767 ⟨681371, by decide⟩ ⟨13, 2, 0, 681371, 364767, 737, 16384⟩
    (by decide) selected_cut_26955

theorem unmarked_context_12_91191_681372 : frontier 9 ⟨681372, by decide⟩
    (prefixCache 12 91191) (prefixPartial 12 91191) = false := by
  decide +kernel

theorem node_context_12_91191_681372 : EJMOriginalGlobalDAGData.nodes 9 ⟨681372, by decide⟩ =
    .split (coordinate 12) (![⟨681294, by decide⟩,⟨681343, by decide⟩,⟨681365, by decide⟩,⟨681371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91191_681372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91191 ⟨681372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91191
    ⟨681372, by decide⟩ (by decide) (![⟨681294, by decide⟩,⟨681343, by decide⟩,⟨681365, by decide⟩,⟨681371, by decide⟩]) unmarked_context_12_91191_681372 node_context_12_91191_681372
  intro a
  fin_cases a
  · exact context_13_364764_681294
  · exact context_13_364765_681343
  · exact context_13_364766_681365
  · exact context_13_364767_681371

theorem unmarked_context_11_22797_681373 : frontier 10 ⟨681373, by decide⟩
    (prefixCache 11 22797) (prefixPartial 11 22797) = false := by
  decide +kernel

theorem node_context_11_22797_681373 : EJMOriginalGlobalDAGData.nodes 10 ⟨681373, by decide⟩ =
    .split (coordinate 11) (![⟨681157, by decide⟩,⟨681225, by decide⟩,⟨681287, by decide⟩,⟨681372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22797_681373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22797 ⟨681373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22797
    ⟨681373, by decide⟩ (by decide) (![⟨681157, by decide⟩,⟨681225, by decide⟩,⟨681287, by decide⟩,⟨681372, by decide⟩]) unmarked_context_11_22797_681373 node_context_11_22797_681373
  intro a
  fin_cases a
  · exact context_12_91188_681157
  · exact context_12_91189_681225
  · exact context_12_91190_681287
  · exact context_12_91191_681372

theorem selected_cut_26956 : selected 8 ⟨681383, by decide⟩
    (prefixPartial 13 364768) = some ⟨13, 2, 0, 681383, 364768, 385, 16384⟩ := by
  decide +kernel

theorem context_13_364768_681383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364768 ⟨681383, by decide⟩ :=
  accepted_of_selected 13 364768 ⟨681383, by decide⟩ ⟨13, 2, 0, 681383, 364768, 385, 16384⟩
    (by decide) selected_cut_26956

theorem selected_cut_26957 : selected 8 ⟨681435, by decide⟩
    (prefixPartial 13 364769) = some ⟨13, 2, 0, 681435, 364769, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_364769_681435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364769 ⟨681435, by decide⟩ :=
  accepted_of_selected 13 364769 ⟨681435, by decide⟩ ⟨13, 2, 0, 681435, 364769, 2385, 16384⟩
    (by decide) selected_cut_26957

theorem selected_cut_26958 : selected 8 ⟨681456, by decide⟩
    (prefixPartial 13 364770) = some ⟨13, 2, 0, 681456, 364770, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_364770_681456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364770 ⟨681456, by decide⟩ :=
  accepted_of_selected 13 364770 ⟨681456, by decide⟩ ⟨13, 2, 0, 681456, 364770, 1433, 16384⟩
    (by decide) selected_cut_26958

theorem selected_cut_26959 : selected 8 ⟨681463, by decide⟩
    (prefixPartial 13 364771) = some ⟨13, 2, 0, 681463, 364771, 789, 16384⟩ := by
  decide +kernel

theorem context_13_364771_681463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364771 ⟨681463, by decide⟩ :=
  accepted_of_selected 13 364771 ⟨681463, by decide⟩ ⟨13, 2, 0, 681463, 364771, 789, 16384⟩
    (by decide) selected_cut_26959

theorem unmarked_context_12_91192_681464 : frontier 9 ⟨681464, by decide⟩
    (prefixCache 12 91192) (prefixPartial 12 91192) = false := by
  decide +kernel

theorem node_context_12_91192_681464 : EJMOriginalGlobalDAGData.nodes 9 ⟨681464, by decide⟩ =
    .split (coordinate 12) (![⟨681383, by decide⟩,⟨681435, by decide⟩,⟨681456, by decide⟩,⟨681463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91192_681464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91192 ⟨681464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91192
    ⟨681464, by decide⟩ (by decide) (![⟨681383, by decide⟩,⟨681435, by decide⟩,⟨681456, by decide⟩,⟨681463, by decide⟩]) unmarked_context_12_91192_681464 node_context_12_91192_681464
  intro a
  fin_cases a
  · exact context_13_364768_681383
  · exact context_13_364769_681435
  · exact context_13_364770_681456
  · exact context_13_364771_681463

theorem selected_cut_26960 : selected 8 ⟨681477, by decide⟩
    (prefixPartial 13 364772) = some ⟨13, 2, 0, 681477, 364772, 541, 16384⟩ := by
  decide +kernel

theorem context_13_364772_681477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364772 ⟨681477, by decide⟩ :=
  accepted_of_selected 13 364772 ⟨681477, by decide⟩ ⟨13, 2, 0, 681477, 364772, 541, 16384⟩
    (by decide) selected_cut_26960

theorem selected_cut_26961 : selected 8 ⟨681537, by decide⟩
    (prefixPartial 13 364773) = some ⟨13, 2, 0, 681537, 364773, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_364773_681537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364773 ⟨681537, by decide⟩ :=
  accepted_of_selected 13 364773 ⟨681537, by decide⟩ ⟨13, 2, 0, 681537, 364773, 2553, 16384⟩
    (by decide) selected_cut_26961

theorem selected_cut_26962 : selected 8 ⟨681567, by decide⟩
    (prefixPartial 13 364774) = some ⟨13, 2, 0, 681567, 364774, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_364774_681567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364774 ⟨681567, by decide⟩ :=
  accepted_of_selected 13 364774 ⟨681567, by decide⟩ ⟨13, 2, 0, 681567, 364774, 1741, 16384⟩
    (by decide) selected_cut_26962

theorem selected_cut_26963 : selected 8 ⟨681573, by decide⟩
    (prefixPartial 13 364775) = some ⟨13, 2, 0, 681573, 364775, 785, 16384⟩ := by
  decide +kernel

theorem context_13_364775_681573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364775 ⟨681573, by decide⟩ :=
  accepted_of_selected 13 364775 ⟨681573, by decide⟩ ⟨13, 2, 0, 681573, 364775, 785, 16384⟩
    (by decide) selected_cut_26963

theorem unmarked_context_12_91193_681574 : frontier 9 ⟨681574, by decide⟩
    (prefixCache 12 91193) (prefixPartial 12 91193) = false := by
  decide +kernel

theorem node_context_12_91193_681574 : EJMOriginalGlobalDAGData.nodes 9 ⟨681574, by decide⟩ =
    .split (coordinate 12) (![⟨681477, by decide⟩,⟨681537, by decide⟩,⟨681567, by decide⟩,⟨681573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91193_681574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91193 ⟨681574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91193
    ⟨681574, by decide⟩ (by decide) (![⟨681477, by decide⟩,⟨681537, by decide⟩,⟨681567, by decide⟩,⟨681573, by decide⟩]) unmarked_context_12_91193_681574 node_context_12_91193_681574
  intro a
  fin_cases a
  · exact context_13_364772_681477
  · exact context_13_364773_681537
  · exact context_13_364774_681567
  · exact context_13_364775_681573

theorem selected_cut_26964 : selected 8 ⟨681584, by decide⟩
    (prefixPartial 13 364776) = some ⟨13, 2, 0, 681584, 364776, 353, 16384⟩ := by
  decide +kernel

theorem context_13_364776_681584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364776 ⟨681584, by decide⟩ :=
  accepted_of_selected 13 364776 ⟨681584, by decide⟩ ⟨13, 2, 0, 681584, 364776, 353, 16384⟩
    (by decide) selected_cut_26964

theorem selected_cut_26965 : selected 8 ⟨681623, by decide⟩
    (prefixPartial 13 364777) = some ⟨13, 2, 0, 681623, 364777, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_364777_681623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364777 ⟨681623, by decide⟩ :=
  accepted_of_selected 13 364777 ⟨681623, by decide⟩ ⟨13, 2, 0, 681623, 364777, 2193, 16384⟩
    (by decide) selected_cut_26965

theorem selected_cut_26966 : selected 8 ⟨681641, by decide⟩
    (prefixPartial 13 364778) = some ⟨13, 2, 0, 681641, 364778, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_364778_681641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364778 ⟨681641, by decide⟩ :=
  accepted_of_selected 13 364778 ⟨681641, by decide⟩ ⟨13, 2, 0, 681641, 364778, 1253, 16384⟩
    (by decide) selected_cut_26966

theorem selected_cut_26967 : selected 8 ⟨681649, by decide⟩
    (prefixPartial 13 364779) = some ⟨13, 2, 0, 681649, 364779, 825, 16384⟩ := by
  decide +kernel

theorem context_13_364779_681649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364779 ⟨681649, by decide⟩ :=
  accepted_of_selected 13 364779 ⟨681649, by decide⟩ ⟨13, 2, 0, 681649, 364779, 825, 16384⟩
    (by decide) selected_cut_26967

theorem unmarked_context_12_91194_681650 : frontier 9 ⟨681650, by decide⟩
    (prefixCache 12 91194) (prefixPartial 12 91194) = false := by
  decide +kernel

theorem node_context_12_91194_681650 : EJMOriginalGlobalDAGData.nodes 9 ⟨681650, by decide⟩ =
    .split (coordinate 12) (![⟨681584, by decide⟩,⟨681623, by decide⟩,⟨681641, by decide⟩,⟨681649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91194_681650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91194 ⟨681650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91194
    ⟨681650, by decide⟩ (by decide) (![⟨681584, by decide⟩,⟨681623, by decide⟩,⟨681641, by decide⟩,⟨681649, by decide⟩]) unmarked_context_12_91194_681650 node_context_12_91194_681650
  intro a
  fin_cases a
  · exact context_13_364776_681584
  · exact context_13_364777_681623
  · exact context_13_364778_681641
  · exact context_13_364779_681649

theorem selected_cut_26968 : selected 8 ⟨681656, by decide⟩
    (prefixPartial 13 364780) = some ⟨13, 2, 0, 681656, 364780, 321, 16384⟩ := by
  decide +kernel

theorem context_13_364780_681656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364780 ⟨681656, by decide⟩ :=
  accepted_of_selected 13 364780 ⟨681656, by decide⟩ ⟨13, 2, 0, 681656, 364780, 321, 16384⟩
    (by decide) selected_cut_26968

theorem selected_cut_26969 : selected 8 ⟨681727, by decide⟩
    (prefixPartial 13 364781) = some ⟨13, 2, 0, 681727, 364781, 3057, 16384⟩ := by
  decide +kernel

theorem context_13_364781_681727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364781 ⟨681727, by decide⟩ :=
  accepted_of_selected 13 364781 ⟨681727, by decide⟩ ⟨13, 2, 0, 681727, 364781, 3057, 16384⟩
    (by decide) selected_cut_26969

theorem selected_cut_26970 : selected 8 ⟨681751, by decide⟩
    (prefixPartial 13 364782) = some ⟨13, 2, 0, 681751, 364782, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_364782_681751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364782 ⟨681751, by decide⟩ :=
  accepted_of_selected 13 364782 ⟨681751, by decide⟩ ⟨13, 2, 0, 681751, 364782, 1713, 16384⟩
    (by decide) selected_cut_26970

theorem selected_cut_26971 : selected 8 ⟨681760, by decide⟩
    (prefixPartial 13 364783) = some ⟨13, 2, 0, 681760, 364783, 853, 16384⟩ := by
  decide +kernel

theorem context_13_364783_681760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364783 ⟨681760, by decide⟩ :=
  accepted_of_selected 13 364783 ⟨681760, by decide⟩ ⟨13, 2, 0, 681760, 364783, 853, 16384⟩
    (by decide) selected_cut_26971

theorem unmarked_context_12_91195_681761 : frontier 9 ⟨681761, by decide⟩
    (prefixCache 12 91195) (prefixPartial 12 91195) = false := by
  decide +kernel

theorem node_context_12_91195_681761 : EJMOriginalGlobalDAGData.nodes 9 ⟨681761, by decide⟩ =
    .split (coordinate 12) (![⟨681656, by decide⟩,⟨681727, by decide⟩,⟨681751, by decide⟩,⟨681760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91195_681761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91195 ⟨681761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91195
    ⟨681761, by decide⟩ (by decide) (![⟨681656, by decide⟩,⟨681727, by decide⟩,⟨681751, by decide⟩,⟨681760, by decide⟩]) unmarked_context_12_91195_681761 node_context_12_91195_681761
  intro a
  fin_cases a
  · exact context_13_364780_681656
  · exact context_13_364781_681727
  · exact context_13_364782_681751
  · exact context_13_364783_681760

theorem unmarked_context_11_22798_681762 : frontier 10 ⟨681762, by decide⟩
    (prefixCache 11 22798) (prefixPartial 11 22798) = false := by
  decide +kernel

theorem node_context_11_22798_681762 : EJMOriginalGlobalDAGData.nodes 10 ⟨681762, by decide⟩ =
    .split (coordinate 11) (![⟨681464, by decide⟩,⟨681574, by decide⟩,⟨681650, by decide⟩,⟨681761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22798_681762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22798 ⟨681762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22798
    ⟨681762, by decide⟩ (by decide) (![⟨681464, by decide⟩,⟨681574, by decide⟩,⟨681650, by decide⟩,⟨681761, by decide⟩]) unmarked_context_11_22798_681762 node_context_11_22798_681762
  intro a
  fin_cases a
  · exact context_12_91192_681464
  · exact context_12_91193_681574
  · exact context_12_91194_681650
  · exact context_12_91195_681761

theorem selected_cut_26972 : selected 9 ⟨681827, by decide⟩
    (prefixPartial 12 91196) = some ⟨12, 2, 0, 681827, 91196, 4033, 65536⟩ := by
  decide +kernel

theorem context_12_91196_681827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91196 ⟨681827, by decide⟩ :=
  accepted_of_selected 12 91196 ⟨681827, by decide⟩ ⟨12, 2, 0, 681827, 91196, 4033, 65536⟩
    (by decide) selected_cut_26972

theorem selected_cut_26973 : selected 8 ⟨681832, by decide⟩
    (prefixPartial 13 364788) = some ⟨13, 2, 0, 681832, 364788, 157, 16384⟩ := by
  decide +kernel

theorem context_13_364788_681832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364788 ⟨681832, by decide⟩ :=
  accepted_of_selected 13 364788 ⟨681832, by decide⟩ ⟨13, 2, 0, 681832, 364788, 157, 16384⟩
    (by decide) selected_cut_26973

theorem selected_cut_26974 : selected 8 ⟨681882, by decide⟩
    (prefixPartial 13 364789) = some ⟨13, 2, 0, 681882, 364789, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_364789_681882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364789 ⟨681882, by decide⟩ :=
  accepted_of_selected 13 364789 ⟨681882, by decide⟩ ⟨13, 2, 0, 681882, 364789, 2305, 16384⟩
    (by decide) selected_cut_26974

theorem selected_cut_26975 : selected 8 ⟨681905, by decide⟩
    (prefixPartial 13 364790) = some ⟨13, 2, 0, 681905, 364790, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_364790_681905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364790 ⟨681905, by decide⟩ :=
  accepted_of_selected 13 364790 ⟨681905, by decide⟩ ⟨13, 2, 0, 681905, 364790, 1565, 16384⟩
    (by decide) selected_cut_26975

theorem selected_cut_26976 : selected 8 ⟨681911, by decide⟩
    (prefixPartial 13 364791) = some ⟨13, 2, 0, 681911, 364791, 645, 16384⟩ := by
  decide +kernel

theorem context_13_364791_681911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364791 ⟨681911, by decide⟩ :=
  accepted_of_selected 13 364791 ⟨681911, by decide⟩ ⟨13, 2, 0, 681911, 364791, 645, 16384⟩
    (by decide) selected_cut_26976

theorem unmarked_context_12_91197_681912 : frontier 9 ⟨681912, by decide⟩
    (prefixCache 12 91197) (prefixPartial 12 91197) = false := by
  decide +kernel

theorem node_context_12_91197_681912 : EJMOriginalGlobalDAGData.nodes 9 ⟨681912, by decide⟩ =
    .split (coordinate 12) (![⟨681832, by decide⟩,⟨681882, by decide⟩,⟨681905, by decide⟩,⟨681911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91197_681912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91197 ⟨681912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91197
    ⟨681912, by decide⟩ (by decide) (![⟨681832, by decide⟩,⟨681882, by decide⟩,⟨681905, by decide⟩,⟨681911, by decide⟩]) unmarked_context_12_91197_681912 node_context_12_91197_681912
  intro a
  fin_cases a
  · exact context_13_364788_681832
  · exact context_13_364789_681882
  · exact context_13_364790_681905
  · exact context_13_364791_681911

theorem selected_cut_26977 : selected 8 ⟨681915, by decide⟩
    (prefixPartial 13 364792) = some ⟨13, 2, 0, 681915, 364792, 93, 16384⟩ := by
  decide +kernel

theorem context_13_364792_681915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364792 ⟨681915, by decide⟩ :=
  accepted_of_selected 13 364792 ⟨681915, by decide⟩ ⟨13, 2, 0, 681915, 364792, 93, 16384⟩
    (by decide) selected_cut_26977

theorem selected_cut_26978 : selected 8 ⟨681947, by decide⟩
    (prefixPartial 13 364793) = some ⟨13, 2, 0, 681947, 364793, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_364793_681947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364793 ⟨681947, by decide⟩ :=
  accepted_of_selected 13 364793 ⟨681947, by decide⟩ ⟨13, 2, 0, 681947, 364793, 2109, 16384⟩
    (by decide) selected_cut_26978

theorem selected_cut_26979 : selected 8 ⟨681964, by decide⟩
    (prefixPartial 13 364794) = some ⟨13, 2, 0, 681964, 364794, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_364794_681964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364794 ⟨681964, by decide⟩ :=
  accepted_of_selected 13 364794 ⟨681964, by decide⟩ ⟨13, 2, 0, 681964, 364794, 1257, 16384⟩
    (by decide) selected_cut_26979

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
