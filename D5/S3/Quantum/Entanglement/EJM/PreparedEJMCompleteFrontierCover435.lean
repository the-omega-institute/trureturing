/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover434
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41763 : selected 9 ⟨1141853, by decide⟩
    (prefixPartial 12 336663) = some ⟨12, 2, 0, 1141853, 336663, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_336663_1141853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336663 ⟨1141853, by decide⟩ :=
  accepted_of_selected 12 336663 ⟨1141853, by decide⟩ ⟨12, 2, 0, 1141853, 336663, 3069, 65536⟩
    (by decide) selected_cut_41763

theorem unmarked_context_11_84165_1141854 : frontier 10 ⟨1141854, by decide⟩
    (prefixCache 11 84165) (prefixPartial 11 84165) = false := by
  decide +kernel

theorem node_context_11_84165_1141854 : EJMOriginalGlobalDAGData.nodes 10 ⟨1141854, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1141795, by decide⟩,⟨1141853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84165_1141854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84165 ⟨1141854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84165
    ⟨1141854, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1141795, by decide⟩,⟨1141853, by decide⟩]) unmarked_context_11_84165_1141854 node_context_11_84165_1141854
  intro a
  fin_cases a
  · exact context_12_336660_1108174
  · exact context_12_336661_308705
  · exact context_12_336662_1141795
  · exact context_12_336663_1141853

theorem selected_cut_41764 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336664) = some ⟨12, 1, 0, 1108174, 336664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336664_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336664 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336664 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336664, 1, 65536⟩
    (by decide) selected_cut_41764

theorem selected_cut_41765 : selected 9 ⟨1141906, by decide⟩
    (prefixPartial 12 336665) = some ⟨12, 2, 0, 1141906, 336665, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_336665_1141906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336665 ⟨1141906, by decide⟩ :=
  accepted_of_selected 12 336665 ⟨1141906, by decide⟩ ⟨12, 2, 0, 1141906, 336665, 2913, 65536⟩
    (by decide) selected_cut_41765

theorem selected_cut_41766 : selected 9 ⟨1141944, by decide⟩
    (prefixPartial 12 336666) = some ⟨12, 2, 0, 1141944, 336666, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_336666_1141944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336666 ⟨1141944, by decide⟩ :=
  accepted_of_selected 12 336666 ⟨1141944, by decide⟩ ⟨12, 2, 0, 1141944, 336666, 2481, 65536⟩
    (by decide) selected_cut_41766

theorem selected_cut_41767 : selected 9 ⟨1141986, by decide⟩
    (prefixPartial 12 336667) = some ⟨12, 2, 0, 1141986, 336667, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_336667_1141986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336667 ⟨1141986, by decide⟩ :=
  accepted_of_selected 12 336667 ⟨1141986, by decide⟩ ⟨12, 2, 0, 1141986, 336667, 2677, 65536⟩
    (by decide) selected_cut_41767

theorem unmarked_context_11_84166_1141987 : frontier 10 ⟨1141987, by decide⟩
    (prefixCache 11 84166) (prefixPartial 11 84166) = false := by
  decide +kernel

theorem node_context_11_84166_1141987 : EJMOriginalGlobalDAGData.nodes 10 ⟨1141987, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1141906, by decide⟩,⟨1141944, by decide⟩,⟨1141986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84166_1141987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84166 ⟨1141987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84166
    ⟨1141987, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1141906, by decide⟩,⟨1141944, by decide⟩,⟨1141986, by decide⟩]) unmarked_context_11_84166_1141987 node_context_11_84166_1141987
  intro a
  fin_cases a
  · exact context_12_336664_1108174
  · exact context_12_336665_1141906
  · exact context_12_336666_1141944
  · exact context_12_336667_1141986

theorem selected_cut_41768 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336668) = some ⟨12, 1, 0, 1108174, 336668, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336668_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336668 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336668 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336668, 1, 65536⟩
    (by decide) selected_cut_41768

theorem selected_cut_41769 : selected 9 ⟨1142026, by decide⟩
    (prefixPartial 12 336669) = some ⟨12, 2, 0, 1142026, 336669, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_336669_1142026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336669 ⟨1142026, by decide⟩ :=
  accepted_of_selected 12 336669 ⟨1142026, by decide⟩ ⟨12, 2, 0, 1142026, 336669, 2453, 65536⟩
    (by decide) selected_cut_41769

theorem selected_cut_41770 : selected 9 ⟨1142059, by decide⟩
    (prefixPartial 12 336670) = some ⟨12, 2, 0, 1142059, 336670, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_336670_1142059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336670 ⟨1142059, by decide⟩ :=
  accepted_of_selected 12 336670 ⟨1142059, by decide⟩ ⟨12, 2, 0, 1142059, 336670, 2477, 65536⟩
    (by decide) selected_cut_41770

theorem selected_cut_41771 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 336671) = some ⟨12, 1, 0, 903806, 336671, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336671_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336671 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 336671 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 336671, 1, 65536⟩
    (by decide) selected_cut_41771

theorem unmarked_context_11_84167_1142060 : frontier 10 ⟨1142060, by decide⟩
    (prefixCache 11 84167) (prefixPartial 11 84167) = false := by
  decide +kernel

theorem node_context_11_84167_1142060 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142060, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142026, by decide⟩,⟨1142059, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84167_1142060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84167 ⟨1142060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84167
    ⟨1142060, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142026, by decide⟩,⟨1142059, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84167_1142060 node_context_11_84167_1142060
  intro a
  fin_cases a
  · exact context_12_336668_1108174
  · exact context_12_336669_1142026
  · exact context_12_336670_1142059
  · exact context_12_336671_903806

theorem unmarked_context_10_21041_1142061 : frontier 11 ⟨1142061, by decide⟩
    (prefixCache 10 21041) (prefixPartial 10 21041) = false := by
  decide +kernel

theorem node_context_10_21041_1142061 : EJMOriginalGlobalDAGData.nodes 11 ⟨1142061, by decide⟩ =
    .split (coordinate 10) (![⟨1141738, by decide⟩,⟨1141854, by decide⟩,⟨1141987, by decide⟩,⟨1142060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21041_1142061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21041 ⟨1142061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21041
    ⟨1142061, by decide⟩ (by decide) (![⟨1141738, by decide⟩,⟨1141854, by decide⟩,⟨1141987, by decide⟩,⟨1142060, by decide⟩]) unmarked_context_10_21041_1142061 node_context_10_21041_1142061
  intro a
  fin_cases a
  · exact context_11_84164_1141738
  · exact context_11_84165_1141854
  · exact context_11_84166_1141987
  · exact context_11_84167_1142060

theorem selected_cut_41772 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336672) = some ⟨12, 1, 0, 1108174, 336672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336672_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336672 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336672 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336672, 1, 65536⟩
    (by decide) selected_cut_41772

theorem selected_cut_41773 : selected 9 ⟨1142104, by decide⟩
    (prefixPartial 12 336673) = some ⟨12, 2, 0, 1142104, 336673, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_336673_1142104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336673 ⟨1142104, by decide⟩ :=
  accepted_of_selected 12 336673 ⟨1142104, by decide⟩ ⟨12, 2, 0, 1142104, 336673, 2725, 65536⟩
    (by decide) selected_cut_41773

theorem selected_cut_41774 : selected 9 ⟨1142139, by decide⟩
    (prefixPartial 12 336674) = some ⟨12, 2, 0, 1142139, 336674, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_336674_1142139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336674 ⟨1142139, by decide⟩ :=
  accepted_of_selected 12 336674 ⟨1142139, by decide⟩ ⟨12, 2, 0, 1142139, 336674, 2421, 65536⟩
    (by decide) selected_cut_41774

theorem selected_cut_41775 : selected 9 ⟨1142176, by decide⟩
    (prefixPartial 12 336675) = some ⟨12, 2, 0, 1142176, 336675, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_336675_1142176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336675 ⟨1142176, by decide⟩ :=
  accepted_of_selected 12 336675 ⟨1142176, by decide⟩ ⟨12, 2, 0, 1142176, 336675, 2405, 65536⟩
    (by decide) selected_cut_41775

theorem unmarked_context_11_84168_1142177 : frontier 10 ⟨1142177, by decide⟩
    (prefixCache 11 84168) (prefixPartial 11 84168) = false := by
  decide +kernel

theorem node_context_11_84168_1142177 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142177, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142104, by decide⟩,⟨1142139, by decide⟩,⟨1142176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84168_1142177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84168 ⟨1142177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84168
    ⟨1142177, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142104, by decide⟩,⟨1142139, by decide⟩,⟨1142176, by decide⟩]) unmarked_context_11_84168_1142177 node_context_11_84168_1142177
  intro a
  fin_cases a
  · exact context_12_336672_1108174
  · exact context_12_336673_1142104
  · exact context_12_336674_1142139
  · exact context_12_336675_1142176

theorem selected_cut_41776 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336676) = some ⟨12, 1, 0, 1108174, 336676, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336676_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336676 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336676 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336676, 1, 65536⟩
    (by decide) selected_cut_41776

theorem selected_cut_41777 : selected 9 ⟨1142223, by decide⟩
    (prefixPartial 12 336677) = some ⟨12, 2, 0, 1142223, 336677, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_336677_1142223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336677 ⟨1142223, by decide⟩ :=
  accepted_of_selected 12 336677 ⟨1142223, by decide⟩ ⟨12, 2, 0, 1142223, 336677, 2709, 65536⟩
    (by decide) selected_cut_41777

theorem selected_cut_41778 : selected 9 ⟨1142258, by decide⟩
    (prefixPartial 12 336678) = some ⟨12, 2, 0, 1142258, 336678, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_336678_1142258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336678 ⟨1142258, by decide⟩ :=
  accepted_of_selected 12 336678 ⟨1142258, by decide⟩ ⟨12, 2, 0, 1142258, 336678, 2305, 65536⟩
    (by decide) selected_cut_41778

theorem selected_cut_41779 : selected 9 ⟨1142299, by decide⟩
    (prefixPartial 12 336679) = some ⟨12, 2, 0, 1142299, 336679, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_336679_1142299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336679 ⟨1142299, by decide⟩ :=
  accepted_of_selected 12 336679 ⟨1142299, by decide⟩ ⟨12, 2, 0, 1142299, 336679, 2397, 65536⟩
    (by decide) selected_cut_41779

theorem unmarked_context_11_84169_1142300 : frontier 10 ⟨1142300, by decide⟩
    (prefixCache 11 84169) (prefixPartial 11 84169) = false := by
  decide +kernel

theorem node_context_11_84169_1142300 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142300, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142223, by decide⟩,⟨1142258, by decide⟩,⟨1142299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84169_1142300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84169 ⟨1142300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84169
    ⟨1142300, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142223, by decide⟩,⟨1142258, by decide⟩,⟨1142299, by decide⟩]) unmarked_context_11_84169_1142300 node_context_11_84169_1142300
  intro a
  fin_cases a
  · exact context_12_336676_1108174
  · exact context_12_336677_1142223
  · exact context_12_336678_1142258
  · exact context_12_336679_1142299

theorem selected_cut_41780 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336680) = some ⟨12, 1, 0, 1108174, 336680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336680_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336680 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336680 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336680, 1, 65536⟩
    (by decide) selected_cut_41780

theorem selected_cut_41781 : selected 9 ⟨1142345, by decide⟩
    (prefixPartial 12 336681) = some ⟨12, 2, 0, 1142345, 336681, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_336681_1142345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336681 ⟨1142345, by decide⟩ :=
  accepted_of_selected 12 336681 ⟨1142345, by decide⟩ ⟨12, 2, 0, 1142345, 336681, 2645, 65536⟩
    (by decide) selected_cut_41781

theorem selected_cut_41782 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 336682) = some ⟨12, 1, 0, 474208, 336682, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336682_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336682 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 336682 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 336682, 1, 65536⟩
    (by decide) selected_cut_41782

theorem selected_cut_41783 : selected 9 ⟨1142377, by decide⟩
    (prefixPartial 12 336683) = some ⟨12, 2, 0, 1142377, 336683, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_336683_1142377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336683 ⟨1142377, by decide⟩ :=
  accepted_of_selected 12 336683 ⟨1142377, by decide⟩ ⟨12, 2, 0, 1142377, 336683, 2361, 65536⟩
    (by decide) selected_cut_41783

theorem unmarked_context_11_84170_1142378 : frontier 10 ⟨1142378, by decide⟩
    (prefixCache 11 84170) (prefixPartial 11 84170) = false := by
  decide +kernel

theorem node_context_11_84170_1142378 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142378, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142345, by decide⟩,⟨474208, by decide⟩,⟨1142377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84170_1142378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84170 ⟨1142378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84170
    ⟨1142378, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142345, by decide⟩,⟨474208, by decide⟩,⟨1142377, by decide⟩]) unmarked_context_11_84170_1142378 node_context_11_84170_1142378
  intro a
  fin_cases a
  · exact context_12_336680_1108174
  · exact context_12_336681_1142345
  · exact context_12_336682_474208
  · exact context_12_336683_1142377

theorem selected_cut_41784 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336684) = some ⟨12, 1, 0, 1108174, 336684, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336684_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336684 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336684 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336684, 1, 65536⟩
    (by decide) selected_cut_41784

theorem selected_cut_41785 : selected 9 ⟨1142411, by decide⟩
    (prefixPartial 12 336685) = some ⟨12, 2, 0, 1142411, 336685, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_336685_1142411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336685 ⟨1142411, by decide⟩ :=
  accepted_of_selected 12 336685 ⟨1142411, by decide⟩ ⟨12, 2, 0, 1142411, 336685, 2285, 65536⟩
    (by decide) selected_cut_41785

theorem selected_cut_41786 : selected 9 ⟨1142436, by decide⟩
    (prefixPartial 12 336686) = some ⟨12, 2, 0, 1142436, 336686, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_336686_1142436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336686 ⟨1142436, by decide⟩ :=
  accepted_of_selected 12 336686 ⟨1142436, by decide⟩ ⟨12, 2, 0, 1142436, 336686, 2109, 65536⟩
    (by decide) selected_cut_41786

theorem selected_cut_41787 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 336687) = some ⟨12, 1, 0, 903806, 336687, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336687_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336687 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 336687 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 336687, 1, 65536⟩
    (by decide) selected_cut_41787

theorem unmarked_context_11_84171_1142437 : frontier 10 ⟨1142437, by decide⟩
    (prefixCache 11 84171) (prefixPartial 11 84171) = false := by
  decide +kernel

theorem node_context_11_84171_1142437 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142437, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142411, by decide⟩,⟨1142436, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84171_1142437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84171 ⟨1142437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84171
    ⟨1142437, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142411, by decide⟩,⟨1142436, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84171_1142437 node_context_11_84171_1142437
  intro a
  fin_cases a
  · exact context_12_336684_1108174
  · exact context_12_336685_1142411
  · exact context_12_336686_1142436
  · exact context_12_336687_903806

theorem unmarked_context_10_21042_1142438 : frontier 11 ⟨1142438, by decide⟩
    (prefixCache 10 21042) (prefixPartial 10 21042) = false := by
  decide +kernel

theorem node_context_10_21042_1142438 : EJMOriginalGlobalDAGData.nodes 11 ⟨1142438, by decide⟩ =
    .split (coordinate 10) (![⟨1142177, by decide⟩,⟨1142300, by decide⟩,⟨1142378, by decide⟩,⟨1142437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21042_1142438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21042 ⟨1142438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21042
    ⟨1142438, by decide⟩ (by decide) (![⟨1142177, by decide⟩,⟨1142300, by decide⟩,⟨1142378, by decide⟩,⟨1142437, by decide⟩]) unmarked_context_10_21042_1142438 node_context_10_21042_1142438
  intro a
  fin_cases a
  · exact context_11_84168_1142177
  · exact context_11_84169_1142300
  · exact context_11_84170_1142378
  · exact context_11_84171_1142437

theorem selected_cut_41788 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336688) = some ⟨12, 1, 0, 1108174, 336688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336688_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336688 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336688 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336688, 1, 65536⟩
    (by decide) selected_cut_41788

theorem selected_cut_41789 : selected 9 ⟨1142483, by decide⟩
    (prefixPartial 12 336689) = some ⟨12, 2, 0, 1142483, 336689, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_336689_1142483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336689 ⟨1142483, by decide⟩ :=
  accepted_of_selected 12 336689 ⟨1142483, by decide⟩ ⟨12, 2, 0, 1142483, 336689, 2637, 65536⟩
    (by decide) selected_cut_41789

theorem selected_cut_41790 : selected 9 ⟨1142523, by decide⟩
    (prefixPartial 12 336690) = some ⟨12, 2, 0, 1142523, 336690, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_336690_1142523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336690 ⟨1142523, by decide⟩ :=
  accepted_of_selected 12 336690 ⟨1142523, by decide⟩ ⟨12, 2, 0, 1142523, 336690, 2317, 65536⟩
    (by decide) selected_cut_41790

theorem selected_cut_41791 : selected 9 ⟨1142556, by decide⟩
    (prefixPartial 12 336691) = some ⟨12, 2, 0, 1142556, 336691, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_336691_1142556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336691 ⟨1142556, by decide⟩ :=
  accepted_of_selected 12 336691 ⟨1142556, by decide⟩ ⟨12, 2, 0, 1142556, 336691, 2293, 65536⟩
    (by decide) selected_cut_41791

theorem unmarked_context_11_84172_1142557 : frontier 10 ⟨1142557, by decide⟩
    (prefixCache 11 84172) (prefixPartial 11 84172) = false := by
  decide +kernel

theorem node_context_11_84172_1142557 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142557, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142483, by decide⟩,⟨1142523, by decide⟩,⟨1142556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84172_1142557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84172 ⟨1142557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84172
    ⟨1142557, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142483, by decide⟩,⟨1142523, by decide⟩,⟨1142556, by decide⟩]) unmarked_context_11_84172_1142557 node_context_11_84172_1142557
  intro a
  fin_cases a
  · exact context_12_336688_1108174
  · exact context_12_336689_1142483
  · exact context_12_336690_1142523
  · exact context_12_336691_1142556

theorem selected_cut_41792 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336692) = some ⟨12, 1, 0, 1108174, 336692, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336692_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336692 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336692 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336692, 1, 65536⟩
    (by decide) selected_cut_41792

theorem selected_cut_41793 : selected 9 ⟨1142600, by decide⟩
    (prefixPartial 12 336693) = some ⟨12, 2, 0, 1142600, 336693, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_336693_1142600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336693 ⟨1142600, by decide⟩ :=
  accepted_of_selected 12 336693 ⟨1142600, by decide⟩ ⟨12, 2, 0, 1142600, 336693, 2489, 65536⟩
    (by decide) selected_cut_41793

theorem selected_cut_41794 : selected 9 ⟨1142632, by decide⟩
    (prefixPartial 12 336694) = some ⟨12, 2, 0, 1142632, 336694, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_336694_1142632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336694 ⟨1142632, by decide⟩ :=
  accepted_of_selected 12 336694 ⟨1142632, by decide⟩ ⟨12, 2, 0, 1142632, 336694, 2261, 65536⟩
    (by decide) selected_cut_41794

theorem selected_cut_41795 : selected 9 ⟨1142674, by decide⟩
    (prefixPartial 12 336695) = some ⟨12, 2, 0, 1142674, 336695, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_336695_1142674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336695 ⟨1142674, by decide⟩ :=
  accepted_of_selected 12 336695 ⟨1142674, by decide⟩ ⟨12, 2, 0, 1142674, 336695, 2393, 65536⟩
    (by decide) selected_cut_41795

theorem unmarked_context_11_84173_1142675 : frontier 10 ⟨1142675, by decide⟩
    (prefixCache 11 84173) (prefixPartial 11 84173) = false := by
  decide +kernel

theorem node_context_11_84173_1142675 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142675, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142600, by decide⟩,⟨1142632, by decide⟩,⟨1142674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84173_1142675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84173 ⟨1142675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84173
    ⟨1142675, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142600, by decide⟩,⟨1142632, by decide⟩,⟨1142674, by decide⟩]) unmarked_context_11_84173_1142675 node_context_11_84173_1142675
  intro a
  fin_cases a
  · exact context_12_336692_1108174
  · exact context_12_336693_1142600
  · exact context_12_336694_1142632
  · exact context_12_336695_1142674

theorem selected_cut_41796 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336696) = some ⟨12, 1, 0, 1108174, 336696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336696_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336696 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336696 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336696, 1, 65536⟩
    (by decide) selected_cut_41796

theorem selected_cut_41797 : selected 9 ⟨1142725, by decide⟩
    (prefixPartial 12 336697) = some ⟨12, 2, 0, 1142725, 336697, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_336697_1142725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336697 ⟨1142725, by decide⟩ :=
  accepted_of_selected 12 336697 ⟨1142725, by decide⟩ ⟨12, 2, 0, 1142725, 336697, 2561, 65536⟩
    (by decide) selected_cut_41797

theorem selected_cut_41798 : selected 9 ⟨1142755, by decide⟩
    (prefixPartial 12 336698) = some ⟨12, 2, 0, 1142755, 336698, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_336698_1142755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336698 ⟨1142755, by decide⟩ :=
  accepted_of_selected 12 336698 ⟨1142755, by decide⟩ ⟨12, 2, 0, 1142755, 336698, 2093, 65536⟩
    (by decide) selected_cut_41798

theorem selected_cut_41799 : selected 9 ⟨1142793, by decide⟩
    (prefixPartial 12 336699) = some ⟨12, 2, 0, 1142793, 336699, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_336699_1142793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336699 ⟨1142793, by decide⟩ :=
  accepted_of_selected 12 336699 ⟨1142793, by decide⟩ ⟨12, 2, 0, 1142793, 336699, 2273, 65536⟩
    (by decide) selected_cut_41799

theorem unmarked_context_11_84174_1142794 : frontier 10 ⟨1142794, by decide⟩
    (prefixCache 11 84174) (prefixPartial 11 84174) = false := by
  decide +kernel

theorem node_context_11_84174_1142794 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142794, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142725, by decide⟩,⟨1142755, by decide⟩,⟨1142793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84174_1142794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84174 ⟨1142794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84174
    ⟨1142794, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142725, by decide⟩,⟨1142755, by decide⟩,⟨1142793, by decide⟩]) unmarked_context_11_84174_1142794 node_context_11_84174_1142794
  intro a
  fin_cases a
  · exact context_12_336696_1108174
  · exact context_12_336697_1142725
  · exact context_12_336698_1142755
  · exact context_12_336699_1142793

theorem selected_cut_41800 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336700) = some ⟨12, 1, 0, 1108174, 336700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336700_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336700 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336700 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336700, 1, 65536⟩
    (by decide) selected_cut_41800

theorem selected_cut_41801 : selected 9 ⟨1142834, by decide⟩
    (prefixPartial 12 336701) = some ⟨12, 2, 0, 1142834, 336701, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_336701_1142834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336701 ⟨1142834, by decide⟩ :=
  accepted_of_selected 12 336701 ⟨1142834, by decide⟩ ⟨12, 2, 0, 1142834, 336701, 2325, 65536⟩
    (by decide) selected_cut_41801

theorem selected_cut_41802 : selected 9 ⟨1142867, by decide⟩
    (prefixPartial 12 336702) = some ⟨12, 2, 0, 1142867, 336702, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_336702_1142867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336702 ⟨1142867, by decide⟩ :=
  accepted_of_selected 12 336702 ⟨1142867, by decide⟩ ⟨12, 2, 0, 1142867, 336702, 2233, 65536⟩
    (by decide) selected_cut_41802

theorem selected_cut_41803 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 336703) = some ⟨12, 1, 0, 607719, 336703, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336703_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336703 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 336703 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 336703, 1, 65536⟩
    (by decide) selected_cut_41803

theorem unmarked_context_11_84175_1142868 : frontier 10 ⟨1142868, by decide⟩
    (prefixCache 11 84175) (prefixPartial 11 84175) = false := by
  decide +kernel

theorem node_context_11_84175_1142868 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142868, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1142834, by decide⟩,⟨1142867, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84175_1142868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84175 ⟨1142868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84175
    ⟨1142868, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1142834, by decide⟩,⟨1142867, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_84175_1142868 node_context_11_84175_1142868
  intro a
  fin_cases a
  · exact context_12_336700_1108174
  · exact context_12_336701_1142834
  · exact context_12_336702_1142867
  · exact context_12_336703_607719

theorem unmarked_context_10_21043_1142869 : frontier 11 ⟨1142869, by decide⟩
    (prefixCache 10 21043) (prefixPartial 10 21043) = false := by
  decide +kernel

theorem node_context_10_21043_1142869 : EJMOriginalGlobalDAGData.nodes 11 ⟨1142869, by decide⟩ =
    .split (coordinate 10) (![⟨1142557, by decide⟩,⟨1142675, by decide⟩,⟨1142794, by decide⟩,⟨1142868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21043_1142869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21043 ⟨1142869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21043
    ⟨1142869, by decide⟩ (by decide) (![⟨1142557, by decide⟩,⟨1142675, by decide⟩,⟨1142794, by decide⟩,⟨1142868, by decide⟩]) unmarked_context_10_21043_1142869 node_context_10_21043_1142869
  intro a
  fin_cases a
  · exact context_11_84172_1142557
  · exact context_11_84173_1142675
  · exact context_11_84174_1142794
  · exact context_11_84175_1142868

theorem unmarked_context_9_5260_1142870 : frontier 12 ⟨1142870, by decide⟩
    (prefixCache 9 5260) (prefixPartial 9 5260) = false := by
  decide +kernel

theorem node_context_9_5260_1142870 : EJMOriginalGlobalDAGData.nodes 12 ⟨1142870, by decide⟩ =
    .split (coordinate 9) (![⟨1141592, by decide⟩,⟨1142061, by decide⟩,⟨1142438, by decide⟩,⟨1142869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5260_1142870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5260 ⟨1142870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5260
    ⟨1142870, by decide⟩ (by decide) (![⟨1141592, by decide⟩,⟨1142061, by decide⟩,⟨1142438, by decide⟩,⟨1142869, by decide⟩]) unmarked_context_9_5260_1142870 node_context_9_5260_1142870
  intro a
  fin_cases a
  · exact context_10_21040_1141592
  · exact context_10_21041_1142061
  · exact context_10_21042_1142438
  · exact context_10_21043_1142869

theorem selected_cut_41804 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 84176) = some ⟨11, 1, 0, 907917, 84176, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84176_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84176 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 84176 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 84176, 1, 262144⟩
    (by decide) selected_cut_41804

theorem selected_cut_41805 : selected 9 ⟨1142898, by decide⟩
    (prefixPartial 12 336708) = some ⟨12, 2, 0, 1142898, 336708, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_336708_1142898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336708 ⟨1142898, by decide⟩ :=
  accepted_of_selected 12 336708 ⟨1142898, by decide⟩ ⟨12, 2, 0, 1142898, 336708, 1789, 65536⟩
    (by decide) selected_cut_41805

theorem selected_cut_41806 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 336709) = some ⟨12, 1, 0, 170504, 336709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336709_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336709 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 336709 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 336709, 1, 65536⟩
    (by decide) selected_cut_41806

theorem selected_cut_41807 : selected 9 ⟨1142923, by decide⟩
    (prefixPartial 12 336710) = some ⟨12, 2, 0, 1142923, 336710, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_336710_1142923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336710 ⟨1142923, by decide⟩ :=
  accepted_of_selected 12 336710 ⟨1142923, by decide⟩ ⟨12, 2, 0, 1142923, 336710, 1729, 65536⟩
    (by decide) selected_cut_41807

theorem selected_cut_41808 : selected 9 ⟨1142953, by decide⟩
    (prefixPartial 12 336711) = some ⟨12, 2, 0, 1142953, 336711, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_336711_1142953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336711 ⟨1142953, by decide⟩ :=
  accepted_of_selected 12 336711 ⟨1142953, by decide⟩ ⟨12, 2, 0, 1142953, 336711, 1905, 65536⟩
    (by decide) selected_cut_41808

theorem unmarked_context_11_84177_1142954 : frontier 10 ⟨1142954, by decide⟩
    (prefixCache 11 84177) (prefixPartial 11 84177) = false := by
  decide +kernel

theorem node_context_11_84177_1142954 : EJMOriginalGlobalDAGData.nodes 10 ⟨1142954, by decide⟩ =
    .split (coordinate 11) (![⟨1142898, by decide⟩,⟨170504, by decide⟩,⟨1142923, by decide⟩,⟨1142953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84177_1142954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84177 ⟨1142954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84177
    ⟨1142954, by decide⟩ (by decide) (![⟨1142898, by decide⟩,⟨170504, by decide⟩,⟨1142923, by decide⟩,⟨1142953, by decide⟩]) unmarked_context_11_84177_1142954 node_context_11_84177_1142954
  intro a
  fin_cases a
  · exact context_12_336708_1142898
  · exact context_12_336709_170504
  · exact context_12_336710_1142923
  · exact context_12_336711_1142953

theorem selected_cut_41809 : selected 9 ⟨1142992, by decide⟩
    (prefixPartial 12 336712) = some ⟨12, 2, 0, 1142992, 336712, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_336712_1142992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336712 ⟨1142992, by decide⟩ :=
  accepted_of_selected 12 336712 ⟨1142992, by decide⟩ ⟨12, 2, 0, 1142992, 336712, 1869, 65536⟩
    (by decide) selected_cut_41809

theorem selected_cut_41810 : selected 9 ⟨1143030, by decide⟩
    (prefixPartial 12 336713) = some ⟨12, 2, 0, 1143030, 336713, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_336713_1143030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336713 ⟨1143030, by decide⟩ :=
  accepted_of_selected 12 336713 ⟨1143030, by decide⟩ ⟨12, 2, 0, 1143030, 336713, 2041, 65536⟩
    (by decide) selected_cut_41810

theorem selected_cut_41811 : selected 9 ⟨1143061, by decide⟩
    (prefixPartial 12 336714) = some ⟨12, 2, 0, 1143061, 336714, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_336714_1143061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336714 ⟨1143061, by decide⟩ :=
  accepted_of_selected 12 336714 ⟨1143061, by decide⟩ ⟨12, 2, 0, 1143061, 336714, 1781, 65536⟩
    (by decide) selected_cut_41811

theorem selected_cut_41812 : selected 9 ⟨1143098, by decide⟩
    (prefixPartial 12 336715) = some ⟨12, 2, 0, 1143098, 336715, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_336715_1143098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336715 ⟨1143098, by decide⟩ :=
  accepted_of_selected 12 336715 ⟨1143098, by decide⟩ ⟨12, 2, 0, 1143098, 336715, 1981, 65536⟩
    (by decide) selected_cut_41812

theorem unmarked_context_11_84178_1143099 : frontier 10 ⟨1143099, by decide⟩
    (prefixCache 11 84178) (prefixPartial 11 84178) = false := by
  decide +kernel

theorem node_context_11_84178_1143099 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143099, by decide⟩ =
    .split (coordinate 11) (![⟨1142992, by decide⟩,⟨1143030, by decide⟩,⟨1143061, by decide⟩,⟨1143098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84178_1143099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84178 ⟨1143099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84178
    ⟨1143099, by decide⟩ (by decide) (![⟨1142992, by decide⟩,⟨1143030, by decide⟩,⟨1143061, by decide⟩,⟨1143098, by decide⟩]) unmarked_context_11_84178_1143099 node_context_11_84178_1143099
  intro a
  fin_cases a
  · exact context_12_336712_1142992
  · exact context_12_336713_1143030
  · exact context_12_336714_1143061
  · exact context_12_336715_1143098

theorem selected_cut_41813 : selected 9 ⟨1143123, by decide⟩
    (prefixPartial 12 336716) = some ⟨12, 2, 0, 1143123, 336716, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_336716_1143123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336716 ⟨1143123, by decide⟩ :=
  accepted_of_selected 12 336716 ⟨1143123, by decide⟩ ⟨12, 2, 0, 1143123, 336716, 1625, 65536⟩
    (by decide) selected_cut_41813

theorem selected_cut_41814 : selected 9 ⟨1143145, by decide⟩
    (prefixPartial 12 336717) = some ⟨12, 2, 0, 1143145, 336717, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_336717_1143145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336717 ⟨1143145, by decide⟩ :=
  accepted_of_selected 12 336717 ⟨1143145, by decide⟩ ⟨12, 2, 0, 1143145, 336717, 1693, 65536⟩
    (by decide) selected_cut_41814

theorem selected_cut_41815 : selected 9 ⟨1143169, by decide⟩
    (prefixPartial 12 336718) = some ⟨12, 2, 0, 1143169, 336718, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_336718_1143169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336718 ⟨1143169, by decide⟩ :=
  accepted_of_selected 12 336718 ⟨1143169, by decide⟩ ⟨12, 2, 0, 1143169, 336718, 1661, 65536⟩
    (by decide) selected_cut_41815

theorem selected_cut_41816 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 336719) = some ⟨12, 1, 0, 903806, 336719, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336719_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336719 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 336719 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 336719, 1, 65536⟩
    (by decide) selected_cut_41816

theorem unmarked_context_11_84179_1143170 : frontier 10 ⟨1143170, by decide⟩
    (prefixCache 11 84179) (prefixPartial 11 84179) = false := by
  decide +kernel

theorem node_context_11_84179_1143170 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143170, by decide⟩ =
    .split (coordinate 11) (![⟨1143123, by decide⟩,⟨1143145, by decide⟩,⟨1143169, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84179_1143170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84179 ⟨1143170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84179
    ⟨1143170, by decide⟩ (by decide) (![⟨1143123, by decide⟩,⟨1143145, by decide⟩,⟨1143169, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84179_1143170 node_context_11_84179_1143170
  intro a
  fin_cases a
  · exact context_12_336716_1143123
  · exact context_12_336717_1143145
  · exact context_12_336718_1143169
  · exact context_12_336719_903806

theorem unmarked_context_10_21044_1143171 : frontier 11 ⟨1143171, by decide⟩
    (prefixCache 10 21044) (prefixPartial 10 21044) = false := by
  decide +kernel

theorem node_context_10_21044_1143171 : EJMOriginalGlobalDAGData.nodes 11 ⟨1143171, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1142954, by decide⟩,⟨1143099, by decide⟩,⟨1143170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21044_1143171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21044 ⟨1143171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21044
    ⟨1143171, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1142954, by decide⟩,⟨1143099, by decide⟩,⟨1143170, by decide⟩]) unmarked_context_10_21044_1143171 node_context_10_21044_1143171
  intro a
  fin_cases a
  · exact context_11_84176_907917
  · exact context_11_84177_1142954
  · exact context_11_84178_1143099
  · exact context_11_84179_1143170

theorem selected_cut_41817 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21045) = some ⟨10, 1, 0, 893098, 21045, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21045_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21045 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21045 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21045, 1, 1048576⟩
    (by decide) selected_cut_41817

theorem selected_cut_41818 : selected 9 ⟨1143200, by decide⟩
    (prefixPartial 12 336736) = some ⟨12, 2, 0, 1143200, 336736, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_336736_1143200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336736 ⟨1143200, by decide⟩ :=
  accepted_of_selected 12 336736 ⟨1143200, by decide⟩ ⟨12, 2, 0, 1143200, 336736, 1725, 65536⟩
    (by decide) selected_cut_41818

theorem selected_cut_41819 : selected 9 ⟨1143221, by decide⟩
    (prefixPartial 12 336737) = some ⟨12, 2, 0, 1143221, 336737, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_336737_1143221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336737 ⟨1143221, by decide⟩ :=
  accepted_of_selected 12 336737 ⟨1143221, by decide⟩ ⟨12, 2, 0, 1143221, 336737, 1657, 65536⟩
    (by decide) selected_cut_41819

theorem selected_cut_41820 : selected 9 ⟨1143248, by decide⟩
    (prefixPartial 12 336738) = some ⟨12, 2, 0, 1143248, 336738, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_336738_1143248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336738 ⟨1143248, by decide⟩ :=
  accepted_of_selected 12 336738 ⟨1143248, by decide⟩ ⟨12, 2, 0, 1143248, 336738, 1697, 65536⟩
    (by decide) selected_cut_41820

theorem selected_cut_41821 : selected 9 ⟨1143270, by decide⟩
    (prefixPartial 12 336739) = some ⟨12, 2, 0, 1143270, 336739, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_336739_1143270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336739 ⟨1143270, by decide⟩ :=
  accepted_of_selected 12 336739 ⟨1143270, by decide⟩ ⟨12, 2, 0, 1143270, 336739, 1585, 65536⟩
    (by decide) selected_cut_41821

theorem unmarked_context_11_84184_1143271 : frontier 10 ⟨1143271, by decide⟩
    (prefixCache 11 84184) (prefixPartial 11 84184) = false := by
  decide +kernel

theorem node_context_11_84184_1143271 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143271, by decide⟩ =
    .split (coordinate 11) (![⟨1143200, by decide⟩,⟨1143221, by decide⟩,⟨1143248, by decide⟩,⟨1143270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84184_1143271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84184 ⟨1143271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84184
    ⟨1143271, by decide⟩ (by decide) (![⟨1143200, by decide⟩,⟨1143221, by decide⟩,⟨1143248, by decide⟩,⟨1143270, by decide⟩]) unmarked_context_11_84184_1143271 node_context_11_84184_1143271
  intro a
  fin_cases a
  · exact context_12_336736_1143200
  · exact context_12_336737_1143221
  · exact context_12_336738_1143248
  · exact context_12_336739_1143270

theorem selected_cut_41822 : selected 9 ⟨1143300, by decide⟩
    (prefixPartial 12 336740) = some ⟨12, 2, 0, 1143300, 336740, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_336740_1143300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336740 ⟨1143300, by decide⟩ :=
  accepted_of_selected 12 336740 ⟨1143300, by decide⟩ ⟨12, 2, 0, 1143300, 336740, 1693, 65536⟩
    (by decide) selected_cut_41822

theorem selected_cut_41823 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 336741) = some ⟨12, 1, 0, 642794, 336741, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336741_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336741 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 336741 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 336741, 1, 65536⟩
    (by decide) selected_cut_41823

theorem selected_cut_41824 : selected 9 ⟨1143319, by decide⟩
    (prefixPartial 12 336742) = some ⟨12, 2, 0, 1143319, 336742, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_336742_1143319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336742 ⟨1143319, by decide⟩ :=
  accepted_of_selected 12 336742 ⟨1143319, by decide⟩ ⟨12, 2, 0, 1143319, 336742, 1613, 65536⟩
    (by decide) selected_cut_41824

theorem selected_cut_41825 : selected 9 ⟨1143338, by decide⟩
    (prefixPartial 12 336743) = some ⟨12, 2, 0, 1143338, 336743, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_336743_1143338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336743 ⟨1143338, by decide⟩ :=
  accepted_of_selected 12 336743 ⟨1143338, by decide⟩ ⟨12, 2, 0, 1143338, 336743, 1581, 65536⟩
    (by decide) selected_cut_41825

theorem unmarked_context_11_84185_1143339 : frontier 10 ⟨1143339, by decide⟩
    (prefixCache 11 84185) (prefixPartial 11 84185) = false := by
  decide +kernel

theorem node_context_11_84185_1143339 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143339, by decide⟩ =
    .split (coordinate 11) (![⟨1143300, by decide⟩,⟨642794, by decide⟩,⟨1143319, by decide⟩,⟨1143338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84185_1143339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84185 ⟨1143339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84185
    ⟨1143339, by decide⟩ (by decide) (![⟨1143300, by decide⟩,⟨642794, by decide⟩,⟨1143319, by decide⟩,⟨1143338, by decide⟩]) unmarked_context_11_84185_1143339 node_context_11_84185_1143339
  intro a
  fin_cases a
  · exact context_12_336740_1143300
  · exact context_12_336741_642794
  · exact context_12_336742_1143319
  · exact context_12_336743_1143338

theorem selected_cut_41826 : selected 9 ⟨1143365, by decide⟩
    (prefixPartial 12 336744) = some ⟨12, 2, 0, 1143365, 336744, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_336744_1143365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336744 ⟨1143365, by decide⟩ :=
  accepted_of_selected 12 336744 ⟨1143365, by decide⟩ ⟨12, 2, 0, 1143365, 336744, 1725, 65536⟩
    (by decide) selected_cut_41826

theorem selected_cut_41827 : selected 9 ⟨1143392, by decide⟩
    (prefixPartial 12 336745) = some ⟨12, 2, 0, 1143392, 336745, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_336745_1143392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336745 ⟨1143392, by decide⟩ :=
  accepted_of_selected 12 336745 ⟨1143392, by decide⟩ ⟨12, 2, 0, 1143392, 336745, 1669, 65536⟩
    (by decide) selected_cut_41827

theorem selected_cut_41828 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 336746) = some ⟨12, 1, 0, 474208, 336746, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336746_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336746 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 336746 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 336746, 1, 65536⟩
    (by decide) selected_cut_41828

theorem selected_cut_41829 : selected 9 ⟨1143417, by decide⟩
    (prefixPartial 12 336747) = some ⟨12, 2, 0, 1143417, 336747, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_336747_1143417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336747 ⟨1143417, by decide⟩ :=
  accepted_of_selected 12 336747 ⟨1143417, by decide⟩ ⟨12, 2, 0, 1143417, 336747, 1585, 65536⟩
    (by decide) selected_cut_41829

theorem unmarked_context_11_84186_1143418 : frontier 10 ⟨1143418, by decide⟩
    (prefixCache 11 84186) (prefixPartial 11 84186) = false := by
  decide +kernel

theorem node_context_11_84186_1143418 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143418, by decide⟩ =
    .split (coordinate 11) (![⟨1143365, by decide⟩,⟨1143392, by decide⟩,⟨474208, by decide⟩,⟨1143417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84186_1143418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84186 ⟨1143418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84186
    ⟨1143418, by decide⟩ (by decide) (![⟨1143365, by decide⟩,⟨1143392, by decide⟩,⟨474208, by decide⟩,⟨1143417, by decide⟩]) unmarked_context_11_84186_1143418 node_context_11_84186_1143418
  intro a
  fin_cases a
  · exact context_12_336744_1143365
  · exact context_12_336745_1143392
  · exact context_12_336746_474208
  · exact context_12_336747_1143417

theorem selected_cut_41830 : selected 9 ⟨1143442, by decide⟩
    (prefixPartial 12 336748) = some ⟨12, 2, 0, 1143442, 336748, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_336748_1143442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336748 ⟨1143442, by decide⟩ :=
  accepted_of_selected 12 336748 ⟨1143442, by decide⟩ ⟨12, 2, 0, 1143442, 336748, 1465, 65536⟩
    (by decide) selected_cut_41830

theorem selected_cut_41831 : selected 9 ⟨1143465, by decide⟩
    (prefixPartial 12 336749) = some ⟨12, 2, 0, 1143465, 336749, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_336749_1143465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336749 ⟨1143465, by decide⟩ :=
  accepted_of_selected 12 336749 ⟨1143465, by decide⟩ ⟨12, 2, 0, 1143465, 336749, 1481, 65536⟩
    (by decide) selected_cut_41831

theorem selected_cut_41832 : selected 9 ⟨1143484, by decide⟩
    (prefixPartial 12 336750) = some ⟨12, 2, 0, 1143484, 336750, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_336750_1143484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336750 ⟨1143484, by decide⟩ :=
  accepted_of_selected 12 336750 ⟨1143484, by decide⟩ ⟨12, 2, 0, 1143484, 336750, 1453, 65536⟩
    (by decide) selected_cut_41832

theorem selected_cut_41833 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 336751) = some ⟨12, 1, 0, 903806, 336751, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336751_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336751 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 336751 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 336751, 1, 65536⟩
    (by decide) selected_cut_41833

theorem unmarked_context_11_84187_1143485 : frontier 10 ⟨1143485, by decide⟩
    (prefixCache 11 84187) (prefixPartial 11 84187) = false := by
  decide +kernel

theorem node_context_11_84187_1143485 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143485, by decide⟩ =
    .split (coordinate 11) (![⟨1143442, by decide⟩,⟨1143465, by decide⟩,⟨1143484, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84187_1143485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84187 ⟨1143485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84187
    ⟨1143485, by decide⟩ (by decide) (![⟨1143442, by decide⟩,⟨1143465, by decide⟩,⟨1143484, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84187_1143485 node_context_11_84187_1143485
  intro a
  fin_cases a
  · exact context_12_336748_1143442
  · exact context_12_336749_1143465
  · exact context_12_336750_1143484
  · exact context_12_336751_903806

theorem unmarked_context_10_21046_1143486 : frontier 11 ⟨1143486, by decide⟩
    (prefixCache 10 21046) (prefixPartial 10 21046) = false := by
  decide +kernel

theorem node_context_10_21046_1143486 : EJMOriginalGlobalDAGData.nodes 11 ⟨1143486, by decide⟩ =
    .split (coordinate 10) (![⟨1143271, by decide⟩,⟨1143339, by decide⟩,⟨1143418, by decide⟩,⟨1143485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21046_1143486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21046 ⟨1143486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21046
    ⟨1143486, by decide⟩ (by decide) (![⟨1143271, by decide⟩,⟨1143339, by decide⟩,⟨1143418, by decide⟩,⟨1143485, by decide⟩]) unmarked_context_10_21046_1143486 node_context_10_21046_1143486
  intro a
  fin_cases a
  · exact context_11_84184_1143271
  · exact context_11_84185_1143339
  · exact context_11_84186_1143418
  · exact context_11_84187_1143485

theorem selected_cut_41834 : selected 9 ⟨1143487, by decide⟩
    (prefixPartial 12 336752) = some ⟨12, 1, 0, 1143487, 336752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336752_1143487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336752 ⟨1143487, by decide⟩ :=
  accepted_of_selected 12 336752 ⟨1143487, by decide⟩ ⟨12, 1, 0, 1143487, 336752, 1, 65536⟩
    (by decide) selected_cut_41834

theorem selected_cut_41835 : selected 9 ⟨1143515, by decide⟩
    (prefixPartial 12 336753) = some ⟨12, 2, 0, 1143515, 336753, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_336753_1143515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336753 ⟨1143515, by decide⟩ :=
  accepted_of_selected 12 336753 ⟨1143515, by decide⟩ ⟨12, 2, 0, 1143515, 336753, 1785, 65536⟩
    (by decide) selected_cut_41835

theorem selected_cut_41836 : selected 9 ⟨1143544, by decide⟩
    (prefixPartial 12 336754) = some ⟨12, 2, 0, 1143544, 336754, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_336754_1143544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336754 ⟨1143544, by decide⟩ :=
  accepted_of_selected 12 336754 ⟨1143544, by decide⟩ ⟨12, 2, 0, 1143544, 336754, 1761, 65536⟩
    (by decide) selected_cut_41836

theorem selected_cut_41837 : selected 9 ⟨1143572, by decide⟩
    (prefixPartial 12 336755) = some ⟨12, 2, 0, 1143572, 336755, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_336755_1143572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336755 ⟨1143572, by decide⟩ :=
  accepted_of_selected 12 336755 ⟨1143572, by decide⟩ ⟨12, 2, 0, 1143572, 336755, 1617, 65536⟩
    (by decide) selected_cut_41837

theorem unmarked_context_11_84188_1143573 : frontier 10 ⟨1143573, by decide⟩
    (prefixCache 11 84188) (prefixPartial 11 84188) = false := by
  decide +kernel

theorem node_context_11_84188_1143573 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143573, by decide⟩ =
    .split (coordinate 11) (![⟨1143487, by decide⟩,⟨1143515, by decide⟩,⟨1143544, by decide⟩,⟨1143572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84188_1143573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84188 ⟨1143573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84188
    ⟨1143573, by decide⟩ (by decide) (![⟨1143487, by decide⟩,⟨1143515, by decide⟩,⟨1143544, by decide⟩,⟨1143572, by decide⟩]) unmarked_context_11_84188_1143573 node_context_11_84188_1143573
  intro a
  fin_cases a
  · exact context_12_336752_1143487
  · exact context_12_336753_1143515
  · exact context_12_336754_1143544
  · exact context_12_336755_1143572

theorem selected_cut_41838 : selected 9 ⟨1143602, by decide⟩
    (prefixPartial 12 336756) = some ⟨12, 2, 0, 1143602, 336756, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_336756_1143602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336756 ⟨1143602, by decide⟩ :=
  accepted_of_selected 12 336756 ⟨1143602, by decide⟩ ⟨12, 2, 0, 1143602, 336756, 1601, 65536⟩
    (by decide) selected_cut_41838

theorem selected_cut_41839 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 336757) = some ⟨12, 1, 0, 642794, 336757, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336757_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336757 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 336757 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 336757, 1, 65536⟩
    (by decide) selected_cut_41839

theorem selected_cut_41840 : selected 9 ⟨1143629, by decide⟩
    (prefixPartial 12 336758) = some ⟨12, 2, 0, 1143629, 336758, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_336758_1143629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336758 ⟨1143629, by decide⟩ :=
  accepted_of_selected 12 336758 ⟨1143629, by decide⟩ ⟨12, 2, 0, 1143629, 336758, 1593, 65536⟩
    (by decide) selected_cut_41840

theorem selected_cut_41841 : selected 9 ⟨1143661, by decide⟩
    (prefixPartial 12 336759) = some ⟨12, 2, 0, 1143661, 336759, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_336759_1143661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336759 ⟨1143661, by decide⟩ :=
  accepted_of_selected 12 336759 ⟨1143661, by decide⟩ ⟨12, 2, 0, 1143661, 336759, 1589, 65536⟩
    (by decide) selected_cut_41841

theorem unmarked_context_11_84189_1143662 : frontier 10 ⟨1143662, by decide⟩
    (prefixCache 11 84189) (prefixPartial 11 84189) = false := by
  decide +kernel

theorem node_context_11_84189_1143662 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143662, by decide⟩ =
    .split (coordinate 11) (![⟨1143602, by decide⟩,⟨642794, by decide⟩,⟨1143629, by decide⟩,⟨1143661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84189_1143662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84189 ⟨1143662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84189
    ⟨1143662, by decide⟩ (by decide) (![⟨1143602, by decide⟩,⟨642794, by decide⟩,⟨1143629, by decide⟩,⟨1143661, by decide⟩]) unmarked_context_11_84189_1143662 node_context_11_84189_1143662
  intro a
  fin_cases a
  · exact context_12_336756_1143602
  · exact context_12_336757_642794
  · exact context_12_336758_1143629
  · exact context_12_336759_1143661

theorem selected_cut_41842 : selected 9 ⟨1143691, by decide⟩
    (prefixPartial 12 336760) = some ⟨12, 2, 0, 1143691, 336760, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_336760_1143691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336760 ⟨1143691, by decide⟩ :=
  accepted_of_selected 12 336760 ⟨1143691, by decide⟩ ⟨12, 2, 0, 1143691, 336760, 1649, 65536⟩
    (by decide) selected_cut_41842

theorem selected_cut_41843 : selected 9 ⟨1143720, by decide⟩
    (prefixPartial 12 336761) = some ⟨12, 2, 0, 1143720, 336761, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_336761_1143720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336761 ⟨1143720, by decide⟩ :=
  accepted_of_selected 12 336761 ⟨1143720, by decide⟩ ⟨12, 2, 0, 1143720, 336761, 1673, 65536⟩
    (by decide) selected_cut_41843

theorem selected_cut_41844 : selected 9 ⟨1143748, by decide⟩
    (prefixPartial 12 336762) = some ⟨12, 2, 0, 1143748, 336762, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_336762_1143748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336762 ⟨1143748, by decide⟩ :=
  accepted_of_selected 12 336762 ⟨1143748, by decide⟩ ⟨12, 2, 0, 1143748, 336762, 1529, 65536⟩
    (by decide) selected_cut_41844

theorem selected_cut_41845 : selected 9 ⟨1143777, by decide⟩
    (prefixPartial 12 336763) = some ⟨12, 2, 0, 1143777, 336763, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_336763_1143777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336763 ⟨1143777, by decide⟩ :=
  accepted_of_selected 12 336763 ⟨1143777, by decide⟩ ⟨12, 2, 0, 1143777, 336763, 1481, 65536⟩
    (by decide) selected_cut_41845

theorem unmarked_context_11_84190_1143778 : frontier 10 ⟨1143778, by decide⟩
    (prefixCache 11 84190) (prefixPartial 11 84190) = false := by
  decide +kernel

theorem node_context_11_84190_1143778 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143778, by decide⟩ =
    .split (coordinate 11) (![⟨1143691, by decide⟩,⟨1143720, by decide⟩,⟨1143748, by decide⟩,⟨1143777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84190_1143778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84190 ⟨1143778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84190
    ⟨1143778, by decide⟩ (by decide) (![⟨1143691, by decide⟩,⟨1143720, by decide⟩,⟨1143748, by decide⟩,⟨1143777, by decide⟩]) unmarked_context_11_84190_1143778 node_context_11_84190_1143778
  intro a
  fin_cases a
  · exact context_12_336760_1143691
  · exact context_12_336761_1143720
  · exact context_12_336762_1143748
  · exact context_12_336763_1143777

theorem selected_cut_41846 : selected 9 ⟨1143802, by decide⟩
    (prefixPartial 12 336764) = some ⟨12, 2, 0, 1143802, 336764, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_336764_1143802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336764 ⟨1143802, by decide⟩ :=
  accepted_of_selected 12 336764 ⟨1143802, by decide⟩ ⟨12, 2, 0, 1143802, 336764, 1457, 65536⟩
    (by decide) selected_cut_41846

theorem selected_cut_41847 : selected 9 ⟨1143828, by decide⟩
    (prefixPartial 12 336765) = some ⟨12, 2, 0, 1143828, 336765, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_336765_1143828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336765 ⟨1143828, by decide⟩ :=
  accepted_of_selected 12 336765 ⟨1143828, by decide⟩ ⟨12, 2, 0, 1143828, 336765, 1477, 65536⟩
    (by decide) selected_cut_41847

theorem selected_cut_41848 : selected 9 ⟨1143855, by decide⟩
    (prefixPartial 12 336766) = some ⟨12, 2, 0, 1143855, 336766, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_336766_1143855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336766 ⟨1143855, by decide⟩ :=
  accepted_of_selected 12 336766 ⟨1143855, by decide⟩ ⟨12, 2, 0, 1143855, 336766, 1537, 65536⟩
    (by decide) selected_cut_41848

theorem selected_cut_41849 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 336767) = some ⟨12, 1, 0, 607719, 336767, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336767_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336767 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 336767 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 336767, 1, 65536⟩
    (by decide) selected_cut_41849

theorem unmarked_context_11_84191_1143856 : frontier 10 ⟨1143856, by decide⟩
    (prefixCache 11 84191) (prefixPartial 11 84191) = false := by
  decide +kernel

theorem node_context_11_84191_1143856 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143856, by decide⟩ =
    .split (coordinate 11) (![⟨1143802, by decide⟩,⟨1143828, by decide⟩,⟨1143855, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84191_1143856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84191 ⟨1143856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84191
    ⟨1143856, by decide⟩ (by decide) (![⟨1143802, by decide⟩,⟨1143828, by decide⟩,⟨1143855, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_84191_1143856 node_context_11_84191_1143856
  intro a
  fin_cases a
  · exact context_12_336764_1143802
  · exact context_12_336765_1143828
  · exact context_12_336766_1143855
  · exact context_12_336767_607719

theorem unmarked_context_10_21047_1143857 : frontier 11 ⟨1143857, by decide⟩
    (prefixCache 10 21047) (prefixPartial 10 21047) = false := by
  decide +kernel

theorem node_context_10_21047_1143857 : EJMOriginalGlobalDAGData.nodes 11 ⟨1143857, by decide⟩ =
    .split (coordinate 10) (![⟨1143573, by decide⟩,⟨1143662, by decide⟩,⟨1143778, by decide⟩,⟨1143856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21047_1143857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21047 ⟨1143857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21047
    ⟨1143857, by decide⟩ (by decide) (![⟨1143573, by decide⟩,⟨1143662, by decide⟩,⟨1143778, by decide⟩,⟨1143856, by decide⟩]) unmarked_context_10_21047_1143857 node_context_10_21047_1143857
  intro a
  fin_cases a
  · exact context_11_84188_1143573
  · exact context_11_84189_1143662
  · exact context_11_84190_1143778
  · exact context_11_84191_1143856

theorem unmarked_context_9_5261_1143858 : frontier 12 ⟨1143858, by decide⟩
    (prefixCache 9 5261) (prefixPartial 9 5261) = false := by
  decide +kernel

theorem node_context_9_5261_1143858 : EJMOriginalGlobalDAGData.nodes 12 ⟨1143858, by decide⟩ =
    .split (coordinate 9) (![⟨1143171, by decide⟩,⟨893098, by decide⟩,⟨1143486, by decide⟩,⟨1143857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5261_1143858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5261 ⟨1143858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5261
    ⟨1143858, by decide⟩ (by decide) (![⟨1143171, by decide⟩,⟨893098, by decide⟩,⟨1143486, by decide⟩,⟨1143857, by decide⟩]) unmarked_context_9_5261_1143858 node_context_9_5261_1143858
  intro a
  fin_cases a
  · exact context_10_21044_1143171
  · exact context_10_21045_893098
  · exact context_10_21046_1143486
  · exact context_10_21047_1143857

theorem selected_cut_41850 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 84192) = some ⟨11, 1, 0, 907917, 84192, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84192_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84192 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 84192 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 84192, 1, 262144⟩
    (by decide) selected_cut_41850

theorem selected_cut_41851 : selected 9 ⟨1143877, by decide⟩
    (prefixPartial 12 336772) = some ⟨12, 2, 0, 1143877, 336772, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_336772_1143877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336772 ⟨1143877, by decide⟩ :=
  accepted_of_selected 12 336772 ⟨1143877, by decide⟩ ⟨12, 2, 0, 1143877, 336772, 1129, 65536⟩
    (by decide) selected_cut_41851

theorem selected_cut_41852 : selected 9 ⟨1143892, by decide⟩
    (prefixPartial 12 336773) = some ⟨12, 2, 0, 1143892, 336773, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_336773_1143892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336773 ⟨1143892, by decide⟩ :=
  accepted_of_selected 12 336773 ⟨1143892, by decide⟩ ⟨12, 2, 0, 1143892, 336773, 1165, 65536⟩
    (by decide) selected_cut_41852

theorem selected_cut_41853 : selected 9 ⟨1143911, by decide⟩
    (prefixPartial 12 336774) = some ⟨12, 2, 0, 1143911, 336774, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_336774_1143911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336774 ⟨1143911, by decide⟩ :=
  accepted_of_selected 12 336774 ⟨1143911, by decide⟩ ⟨12, 2, 0, 1143911, 336774, 1129, 65536⟩
    (by decide) selected_cut_41853

theorem selected_cut_41854 : selected 9 ⟨1143932, by decide⟩
    (prefixPartial 12 336775) = some ⟨12, 2, 0, 1143932, 336775, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_336775_1143932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336775 ⟨1143932, by decide⟩ :=
  accepted_of_selected 12 336775 ⟨1143932, by decide⟩ ⟨12, 2, 0, 1143932, 336775, 1201, 65536⟩
    (by decide) selected_cut_41854

theorem unmarked_context_11_84193_1143933 : frontier 10 ⟨1143933, by decide⟩
    (prefixCache 11 84193) (prefixPartial 11 84193) = false := by
  decide +kernel

theorem node_context_11_84193_1143933 : EJMOriginalGlobalDAGData.nodes 10 ⟨1143933, by decide⟩ =
    .split (coordinate 11) (![⟨1143877, by decide⟩,⟨1143892, by decide⟩,⟨1143911, by decide⟩,⟨1143932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84193_1143933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84193 ⟨1143933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84193
    ⟨1143933, by decide⟩ (by decide) (![⟨1143877, by decide⟩,⟨1143892, by decide⟩,⟨1143911, by decide⟩,⟨1143932, by decide⟩]) unmarked_context_11_84193_1143933 node_context_11_84193_1143933
  intro a
  fin_cases a
  · exact context_12_336772_1143877
  · exact context_12_336773_1143892
  · exact context_12_336774_1143911
  · exact context_12_336775_1143932

theorem selected_cut_41855 : selected 10 ⟨1143994, by decide⟩
    (prefixPartial 11 84194) = some ⟨11, 2, 0, 1143994, 84194, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_84194_1143994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84194 ⟨1143994, by decide⟩ :=
  accepted_of_selected 11 84194 ⟨1143994, by decide⟩ ⟨11, 2, 0, 1143994, 84194, 3785, 262144⟩
    (by decide) selected_cut_41855

theorem selected_cut_41856 : selected 10 ⟨1144037, by decide⟩
    (prefixPartial 11 84195) = some ⟨11, 2, 0, 1144037, 84195, 3077, 262144⟩ := by
  decide +kernel

theorem context_11_84195_1144037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84195 ⟨1144037, by decide⟩ :=
  accepted_of_selected 11 84195 ⟨1144037, by decide⟩ ⟨11, 2, 0, 1144037, 84195, 3077, 262144⟩
    (by decide) selected_cut_41856

theorem unmarked_context_10_21048_1144038 : frontier 11 ⟨1144038, by decide⟩
    (prefixCache 10 21048) (prefixPartial 10 21048) = false := by
  decide +kernel

theorem node_context_10_21048_1144038 : EJMOriginalGlobalDAGData.nodes 11 ⟨1144038, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1143933, by decide⟩,⟨1143994, by decide⟩,⟨1144037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21048_1144038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21048 ⟨1144038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21048
    ⟨1144038, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1143933, by decide⟩,⟨1143994, by decide⟩,⟨1144037, by decide⟩]) unmarked_context_10_21048_1144038 node_context_10_21048_1144038
  intro a
  fin_cases a
  · exact context_11_84192_907917
  · exact context_11_84193_1143933
  · exact context_11_84194_1143994
  · exact context_11_84195_1144037

theorem selected_cut_41857 : selected 9 ⟨1144061, by decide⟩
    (prefixPartial 12 336784) = some ⟨12, 2, 0, 1144061, 336784, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_336784_1144061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336784 ⟨1144061, by decide⟩ :=
  accepted_of_selected 12 336784 ⟨1144061, by decide⟩ ⟨12, 2, 0, 1144061, 336784, 1197, 65536⟩
    (by decide) selected_cut_41857

theorem selected_cut_41858 : selected 9 ⟨1144083, by decide⟩
    (prefixPartial 12 336785) = some ⟨12, 2, 0, 1144083, 336785, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_336785_1144083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336785 ⟨1144083, by decide⟩ :=
  accepted_of_selected 12 336785 ⟨1144083, by decide⟩ ⟨12, 2, 0, 1144083, 336785, 1273, 65536⟩
    (by decide) selected_cut_41858

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
