/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover179
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17282 : selected 8 ⟨439709, by decide⟩
    (prefixPartial 13 279686) = some ⟨13, 2, 0, 439709, 279686, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_279686_439709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279686 ⟨439709, by decide⟩ :=
  accepted_of_selected 13 279686 ⟨439709, by decide⟩ ⟨13, 2, 0, 439709, 279686, 1825, 16384⟩
    (by decide) selected_cut_17282

theorem selected_cut_17283 : selected 8 ⟨439720, by decide⟩
    (prefixPartial 13 279687) = some ⟨13, 2, 0, 439720, 279687, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_279687_439720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279687 ⟨439720, by decide⟩ :=
  accepted_of_selected 13 279687 ⟨439720, by decide⟩ ⟨13, 2, 0, 439720, 279687, 1029, 16384⟩
    (by decide) selected_cut_17283

theorem unmarked_context_12_69921_439721 : frontier 9 ⟨439721, by decide⟩
    (prefixCache 12 69921) (prefixPartial 12 69921) = false := by
  decide +kernel

theorem node_context_12_69921_439721 : EJMOriginalGlobalDAGData.nodes 9 ⟨439721, by decide⟩ =
    .split (coordinate 12) (![⟨439665, by decide⟩,⟨439685, by decide⟩,⟨439709, by decide⟩,⟨439720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69921_439721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69921 ⟨439721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69921
    ⟨439721, by decide⟩ (by decide) (![⟨439665, by decide⟩,⟨439685, by decide⟩,⟨439709, by decide⟩,⟨439720, by decide⟩]) unmarked_context_12_69921_439721 node_context_12_69921_439721
  intro a
  fin_cases a
  · exact context_13_279684_439665
  · exact context_13_279685_439685
  · exact context_13_279686_439709
  · exact context_13_279687_439720

theorem selected_cut_17284 : selected 8 ⟨439761, by decide⟩
    (prefixPartial 13 279688) = some ⟨13, 2, 0, 439761, 279688, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_279688_439761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279688 ⟨439761, by decide⟩ :=
  accepted_of_selected 13 279688 ⟨439761, by decide⟩ ⟨13, 2, 0, 439761, 279688, 1601, 16384⟩
    (by decide) selected_cut_17284

theorem selected_cut_17285 : selected 8 ⟨439785, by decide⟩
    (prefixPartial 13 279689) = some ⟨13, 2, 0, 439785, 279689, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_279689_439785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279689 ⟨439785, by decide⟩ :=
  accepted_of_selected 13 279689 ⟨439785, by decide⟩ ⟨13, 2, 0, 439785, 279689, 1773, 16384⟩
    (by decide) selected_cut_17285

theorem selected_cut_17286 : selected 8 ⟨439805, by decide⟩
    (prefixPartial 13 279690) = some ⟨13, 2, 0, 439805, 279690, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_279690_439805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279690 ⟨439805, by decide⟩ :=
  accepted_of_selected 13 279690 ⟨439805, by decide⟩ ⟨13, 2, 0, 439805, 279690, 1353, 16384⟩
    (by decide) selected_cut_17286

theorem selected_cut_17287 : selected 8 ⟨439813, by decide⟩
    (prefixPartial 13 279691) = some ⟨13, 2, 0, 439813, 279691, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_279691_439813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279691 ⟨439813, by decide⟩ :=
  accepted_of_selected 13 279691 ⟨439813, by decide⟩ ⟨13, 2, 0, 439813, 279691, 1069, 16384⟩
    (by decide) selected_cut_17287

theorem unmarked_context_12_69922_439814 : frontier 9 ⟨439814, by decide⟩
    (prefixCache 12 69922) (prefixPartial 12 69922) = false := by
  decide +kernel

theorem node_context_12_69922_439814 : EJMOriginalGlobalDAGData.nodes 9 ⟨439814, by decide⟩ =
    .split (coordinate 12) (![⟨439761, by decide⟩,⟨439785, by decide⟩,⟨439805, by decide⟩,⟨439813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69922_439814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69922 ⟨439814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69922
    ⟨439814, by decide⟩ (by decide) (![⟨439761, by decide⟩,⟨439785, by decide⟩,⟨439805, by decide⟩,⟨439813, by decide⟩]) unmarked_context_12_69922_439814 node_context_12_69922_439814
  intro a
  fin_cases a
  · exact context_13_279688_439761
  · exact context_13_279689_439785
  · exact context_13_279690_439805
  · exact context_13_279691_439813

theorem selected_cut_17288 : selected 8 ⟨439850, by decide⟩
    (prefixPartial 13 279692) = some ⟨13, 2, 0, 439850, 279692, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_279692_439850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279692 ⟨439850, by decide⟩ :=
  accepted_of_selected 13 279692 ⟨439850, by decide⟩ ⟨13, 2, 0, 439850, 279692, 1581, 16384⟩
    (by decide) selected_cut_17288

theorem selected_cut_17289 : selected 8 ⟨439875, by decide⟩
    (prefixPartial 13 279693) = some ⟨13, 2, 0, 439875, 279693, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_279693_439875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279693 ⟨439875, by decide⟩ :=
  accepted_of_selected 13 279693 ⟨439875, by decide⟩ ⟨13, 2, 0, 439875, 279693, 1941, 16384⟩
    (by decide) selected_cut_17289

theorem selected_cut_17290 : selected 8 ⟨439898, by decide⟩
    (prefixPartial 13 279694) = some ⟨13, 2, 0, 439898, 279694, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_279694_439898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279694 ⟨439898, by decide⟩ :=
  accepted_of_selected 13 279694 ⟨439898, by decide⟩ ⟨13, 2, 0, 439898, 279694, 1657, 16384⟩
    (by decide) selected_cut_17290

theorem selected_cut_17291 : selected 8 ⟨439906, by decide⟩
    (prefixPartial 13 279695) = some ⟨13, 2, 0, 439906, 279695, 841, 16384⟩ := by
  decide +kernel

theorem context_13_279695_439906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279695 ⟨439906, by decide⟩ :=
  accepted_of_selected 13 279695 ⟨439906, by decide⟩ ⟨13, 2, 0, 439906, 279695, 841, 16384⟩
    (by decide) selected_cut_17291

theorem unmarked_context_12_69923_439907 : frontier 9 ⟨439907, by decide⟩
    (prefixCache 12 69923) (prefixPartial 12 69923) = false := by
  decide +kernel

theorem node_context_12_69923_439907 : EJMOriginalGlobalDAGData.nodes 9 ⟨439907, by decide⟩ =
    .split (coordinate 12) (![⟨439850, by decide⟩,⟨439875, by decide⟩,⟨439898, by decide⟩,⟨439906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69923_439907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69923 ⟨439907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69923
    ⟨439907, by decide⟩ (by decide) (![⟨439850, by decide⟩,⟨439875, by decide⟩,⟨439898, by decide⟩,⟨439906, by decide⟩]) unmarked_context_12_69923_439907 node_context_12_69923_439907
  intro a
  fin_cases a
  · exact context_13_279692_439850
  · exact context_13_279693_439875
  · exact context_13_279694_439898
  · exact context_13_279695_439906

theorem unmarked_context_11_17480_439908 : frontier 10 ⟨439908, by decide⟩
    (prefixCache 11 17480) (prefixPartial 11 17480) = false := by
  decide +kernel

theorem node_context_11_17480_439908 : EJMOriginalGlobalDAGData.nodes 10 ⟨439908, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨439721, by decide⟩,⟨439814, by decide⟩,⟨439907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17480_439908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17480 ⟨439908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17480
    ⟨439908, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨439721, by decide⟩,⟨439814, by decide⟩,⟨439907, by decide⟩]) unmarked_context_11_17480_439908 node_context_11_17480_439908
  intro a
  fin_cases a
  · exact context_12_69920_435790
  · exact context_12_69921_439721
  · exact context_12_69922_439814
  · exact context_12_69923_439907

theorem selected_cut_17292 : selected 8 ⟨439945, by decide⟩
    (prefixPartial 13 279696) = some ⟨13, 2, 0, 439945, 279696, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_279696_439945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279696 ⟨439945, by decide⟩ :=
  accepted_of_selected 13 279696 ⟨439945, by decide⟩ ⟨13, 2, 0, 439945, 279696, 1777, 16384⟩
    (by decide) selected_cut_17292

theorem selected_cut_17293 : selected 8 ⟨439976, by decide⟩
    (prefixPartial 13 279697) = some ⟨13, 2, 0, 439976, 279697, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_279697_439976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279697 ⟨439976, by decide⟩ :=
  accepted_of_selected 13 279697 ⟨439976, by decide⟩ ⟨13, 2, 0, 439976, 279697, 2613, 16384⟩
    (by decide) selected_cut_17293

theorem selected_cut_17294 : selected 8 ⟨440002, by decide⟩
    (prefixPartial 13 279698) = some ⟨13, 2, 0, 440002, 279698, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_279698_440002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279698 ⟨440002, by decide⟩ :=
  accepted_of_selected 13 279698 ⟨440002, by decide⟩ ⟨13, 2, 0, 440002, 279698, 2185, 16384⟩
    (by decide) selected_cut_17294

theorem selected_cut_17295 : selected 8 ⟨440013, by decide⟩
    (prefixPartial 13 279699) = some ⟨13, 2, 0, 440013, 279699, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_279699_440013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279699 ⟨440013, by decide⟩ :=
  accepted_of_selected 13 279699 ⟨440013, by decide⟩ ⟨13, 2, 0, 440013, 279699, 1089, 16384⟩
    (by decide) selected_cut_17295

theorem unmarked_context_12_69924_440014 : frontier 9 ⟨440014, by decide⟩
    (prefixCache 12 69924) (prefixPartial 12 69924) = false := by
  decide +kernel

theorem node_context_12_69924_440014 : EJMOriginalGlobalDAGData.nodes 9 ⟨440014, by decide⟩ =
    .split (coordinate 12) (![⟨439945, by decide⟩,⟨439976, by decide⟩,⟨440002, by decide⟩,⟨440013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69924_440014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69924 ⟨440014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69924
    ⟨440014, by decide⟩ (by decide) (![⟨439945, by decide⟩,⟨439976, by decide⟩,⟨440002, by decide⟩,⟨440013, by decide⟩]) unmarked_context_12_69924_440014 node_context_12_69924_440014
  intro a
  fin_cases a
  · exact context_13_279696_439945
  · exact context_13_279697_439976
  · exact context_13_279698_440002
  · exact context_13_279699_440013

theorem selected_cut_17296 : selected 8 ⟨440070, by decide⟩
    (prefixPartial 13 279700) = some ⟨13, 2, 0, 440070, 279700, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_279700_440070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279700 ⟨440070, by decide⟩ :=
  accepted_of_selected 13 279700 ⟨440070, by decide⟩ ⟨13, 2, 0, 440070, 279700, 2301, 16384⟩
    (by decide) selected_cut_17296

theorem selected_cut_17297 : selected 8 ⟨440129, by decide⟩
    (prefixPartial 13 279701) = some ⟨13, 2, 0, 440129, 279701, 3213, 16384⟩ := by
  decide +kernel

theorem context_13_279701_440129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279701 ⟨440129, by decide⟩ :=
  accepted_of_selected 13 279701 ⟨440129, by decide⟩ ⟨13, 2, 0, 440129, 279701, 3213, 16384⟩
    (by decide) selected_cut_17297

theorem selected_cut_17298 : selected 8 ⟨440183, by decide⟩
    (prefixPartial 13 279702) = some ⟨13, 2, 0, 440183, 279702, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_279702_440183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279702 ⟨440183, by decide⟩ :=
  accepted_of_selected 13 279702 ⟨440183, by decide⟩ ⟨13, 2, 0, 440183, 279702, 2889, 16384⟩
    (by decide) selected_cut_17298

theorem selected_cut_17299 : selected 8 ⟨440206, by decide⟩
    (prefixPartial 13 279703) = some ⟨13, 2, 0, 440206, 279703, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_279703_440206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279703 ⟨440206, by decide⟩ :=
  accepted_of_selected 13 279703 ⟨440206, by decide⟩ ⟨13, 2, 0, 440206, 279703, 1353, 16384⟩
    (by decide) selected_cut_17299

theorem unmarked_context_12_69925_440207 : frontier 9 ⟨440207, by decide⟩
    (prefixCache 12 69925) (prefixPartial 12 69925) = false := by
  decide +kernel

theorem node_context_12_69925_440207 : EJMOriginalGlobalDAGData.nodes 9 ⟨440207, by decide⟩ =
    .split (coordinate 12) (![⟨440070, by decide⟩,⟨440129, by decide⟩,⟨440183, by decide⟩,⟨440206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69925_440207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69925 ⟨440207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69925
    ⟨440207, by decide⟩ (by decide) (![⟨440070, by decide⟩,⟨440129, by decide⟩,⟨440183, by decide⟩,⟨440206, by decide⟩]) unmarked_context_12_69925_440207 node_context_12_69925_440207
  intro a
  fin_cases a
  · exact context_13_279700_440070
  · exact context_13_279701_440129
  · exact context_13_279702_440183
  · exact context_13_279703_440206

theorem selected_cut_17300 : selected 8 ⟨440240, by decide⟩
    (prefixPartial 13 279704) = some ⟨13, 2, 0, 440240, 279704, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_279704_440240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279704 ⟨440240, by decide⟩ :=
  accepted_of_selected 13 279704 ⟨440240, by decide⟩ ⟨13, 2, 0, 440240, 279704, 1357, 16384⟩
    (by decide) selected_cut_17300

theorem selected_cut_17301 : selected 8 ⟨440263, by decide⟩
    (prefixPartial 13 279705) = some ⟨13, 2, 0, 440263, 279705, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_279705_440263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279705 ⟨440263, by decide⟩ :=
  accepted_of_selected 13 279705 ⟨440263, by decide⟩ ⟨13, 2, 0, 440263, 279705, 1985, 16384⟩
    (by decide) selected_cut_17301

theorem selected_cut_17302 : selected 8 ⟨440283, by decide⟩
    (prefixPartial 13 279706) = some ⟨13, 2, 0, 440283, 279706, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_279706_440283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279706 ⟨440283, by decide⟩ :=
  accepted_of_selected 13 279706 ⟨440283, by decide⟩ ⟨13, 2, 0, 440283, 279706, 1309, 16384⟩
    (by decide) selected_cut_17302

theorem selected_cut_17303 : selected 8 ⟨440293, by decide⟩
    (prefixPartial 13 279707) = some ⟨13, 2, 0, 440293, 279707, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_279707_440293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279707 ⟨440293, by decide⟩ :=
  accepted_of_selected 13 279707 ⟨440293, by decide⟩ ⟨13, 2, 0, 440293, 279707, 1029, 16384⟩
    (by decide) selected_cut_17303

theorem unmarked_context_12_69926_440294 : frontier 9 ⟨440294, by decide⟩
    (prefixCache 12 69926) (prefixPartial 12 69926) = false := by
  decide +kernel

theorem node_context_12_69926_440294 : EJMOriginalGlobalDAGData.nodes 9 ⟨440294, by decide⟩ =
    .split (coordinate 12) (![⟨440240, by decide⟩,⟨440263, by decide⟩,⟨440283, by decide⟩,⟨440293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69926_440294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69926 ⟨440294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69926
    ⟨440294, by decide⟩ (by decide) (![⟨440240, by decide⟩,⟨440263, by decide⟩,⟨440283, by decide⟩,⟨440293, by decide⟩]) unmarked_context_12_69926_440294 node_context_12_69926_440294
  intro a
  fin_cases a
  · exact context_13_279704_440240
  · exact context_13_279705_440263
  · exact context_13_279706_440283
  · exact context_13_279707_440293

theorem selected_cut_17304 : selected 8 ⟨440323, by decide⟩
    (prefixPartial 13 279708) = some ⟨13, 2, 0, 440323, 279708, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_279708_440323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279708 ⟨440323, by decide⟩ :=
  accepted_of_selected 13 279708 ⟨440323, by decide⟩ ⟨13, 2, 0, 440323, 279708, 1201, 16384⟩
    (by decide) selected_cut_17304

theorem selected_cut_17305 : selected 8 ⟨440344, by decide⟩
    (prefixPartial 13 279709) = some ⟨13, 2, 0, 440344, 279709, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_279709_440344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279709 ⟨440344, by decide⟩ :=
  accepted_of_selected 13 279709 ⟨440344, by decide⟩ ⟨13, 2, 0, 440344, 279709, 2189, 16384⟩
    (by decide) selected_cut_17305

theorem selected_cut_17306 : selected 8 ⟨440363, by decide⟩
    (prefixPartial 13 279710) = some ⟨13, 2, 0, 440363, 279710, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_279710_440363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279710 ⟨440363, by decide⟩ :=
  accepted_of_selected 13 279710 ⟨440363, by decide⟩ ⟨13, 2, 0, 440363, 279710, 1709, 16384⟩
    (by decide) selected_cut_17306

theorem selected_cut_17307 : selected 8 ⟨440371, by decide⟩
    (prefixPartial 13 279711) = some ⟨13, 2, 0, 440371, 279711, 649, 16384⟩ := by
  decide +kernel

theorem context_13_279711_440371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279711 ⟨440371, by decide⟩ :=
  accepted_of_selected 13 279711 ⟨440371, by decide⟩ ⟨13, 2, 0, 440371, 279711, 649, 16384⟩
    (by decide) selected_cut_17307

theorem unmarked_context_12_69927_440372 : frontier 9 ⟨440372, by decide⟩
    (prefixCache 12 69927) (prefixPartial 12 69927) = false := by
  decide +kernel

theorem node_context_12_69927_440372 : EJMOriginalGlobalDAGData.nodes 9 ⟨440372, by decide⟩ =
    .split (coordinate 12) (![⟨440323, by decide⟩,⟨440344, by decide⟩,⟨440363, by decide⟩,⟨440371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69927_440372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69927 ⟨440372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69927
    ⟨440372, by decide⟩ (by decide) (![⟨440323, by decide⟩,⟨440344, by decide⟩,⟨440363, by decide⟩,⟨440371, by decide⟩]) unmarked_context_12_69927_440372 node_context_12_69927_440372
  intro a
  fin_cases a
  · exact context_13_279708_440323
  · exact context_13_279709_440344
  · exact context_13_279710_440363
  · exact context_13_279711_440371

theorem unmarked_context_11_17481_440373 : frontier 10 ⟨440373, by decide⟩
    (prefixCache 11 17481) (prefixPartial 11 17481) = false := by
  decide +kernel

theorem node_context_11_17481_440373 : EJMOriginalGlobalDAGData.nodes 10 ⟨440373, by decide⟩ =
    .split (coordinate 11) (![⟨440014, by decide⟩,⟨440207, by decide⟩,⟨440294, by decide⟩,⟨440372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17481_440373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17481 ⟨440373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17481
    ⟨440373, by decide⟩ (by decide) (![⟨440014, by decide⟩,⟨440207, by decide⟩,⟨440294, by decide⟩,⟨440372, by decide⟩]) unmarked_context_11_17481_440373 node_context_11_17481_440373
  intro a
  fin_cases a
  · exact context_12_69924_440014
  · exact context_12_69925_440207
  · exact context_12_69926_440294
  · exact context_12_69927_440372

theorem selected_cut_17308 : selected 8 ⟨440392, by decide⟩
    (prefixPartial 13 279712) = some ⟨13, 2, 0, 440392, 279712, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_279712_440392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279712 ⟨440392, by decide⟩ :=
  accepted_of_selected 13 279712 ⟨440392, by decide⟩ ⟨13, 2, 0, 440392, 279712, 1045, 16384⟩
    (by decide) selected_cut_17308

theorem selected_cut_17309 : selected 8 ⟨440434, by decide⟩
    (prefixPartial 13 279713) = some ⟨13, 2, 0, 440434, 279713, 2897, 16384⟩ := by
  decide +kernel

theorem context_13_279713_440434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279713 ⟨440434, by decide⟩ :=
  accepted_of_selected 13 279713 ⟨440434, by decide⟩ ⟨13, 2, 0, 440434, 279713, 2897, 16384⟩
    (by decide) selected_cut_17309

theorem selected_cut_17310 : selected 8 ⟨440462, by decide⟩
    (prefixPartial 13 279714) = some ⟨13, 2, 0, 440462, 279714, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_279714_440462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279714 ⟨440462, by decide⟩ :=
  accepted_of_selected 13 279714 ⟨440462, by decide⟩ ⟨13, 2, 0, 440462, 279714, 2253, 16384⟩
    (by decide) selected_cut_17310

theorem selected_cut_17311 : selected 8 ⟨440480, by decide⟩
    (prefixPartial 13 279715) = some ⟨13, 2, 0, 440480, 279715, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_279715_440480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279715 ⟨440480, by decide⟩ :=
  accepted_of_selected 13 279715 ⟨440480, by decide⟩ ⟨13, 2, 0, 440480, 279715, 1101, 16384⟩
    (by decide) selected_cut_17311

theorem unmarked_context_12_69928_440481 : frontier 9 ⟨440481, by decide⟩
    (prefixCache 12 69928) (prefixPartial 12 69928) = false := by
  decide +kernel

theorem node_context_12_69928_440481 : EJMOriginalGlobalDAGData.nodes 9 ⟨440481, by decide⟩ =
    .split (coordinate 12) (![⟨440392, by decide⟩,⟨440434, by decide⟩,⟨440462, by decide⟩,⟨440480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69928_440481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69928 ⟨440481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69928
    ⟨440481, by decide⟩ (by decide) (![⟨440392, by decide⟩,⟨440434, by decide⟩,⟨440462, by decide⟩,⟨440480, by decide⟩]) unmarked_context_12_69928_440481 node_context_12_69928_440481
  intro a
  fin_cases a
  · exact context_13_279712_440392
  · exact context_13_279713_440434
  · exact context_13_279714_440462
  · exact context_13_279715_440480

theorem selected_cut_17312 : selected 8 ⟨440500, by decide⟩
    (prefixPartial 13 279716) = some ⟨13, 2, 0, 440500, 279716, 801, 16384⟩ := by
  decide +kernel

theorem context_13_279716_440500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279716 ⟨440500, by decide⟩ :=
  accepted_of_selected 13 279716 ⟨440500, by decide⟩ ⟨13, 2, 0, 440500, 279716, 801, 16384⟩
    (by decide) selected_cut_17312

theorem selected_cut_17313 : selected 8 ⟨440518, by decide⟩
    (prefixPartial 13 279717) = some ⟨13, 2, 0, 440518, 279717, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_279717_440518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279717 ⟨440518, by decide⟩ :=
  accepted_of_selected 13 279717 ⟨440518, by decide⟩ ⟨13, 2, 0, 440518, 279717, 1789, 16384⟩
    (by decide) selected_cut_17313

theorem selected_cut_17314 : selected 8 ⟨440540, by decide⟩
    (prefixPartial 13 279718) = some ⟨13, 2, 0, 440540, 279718, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_279718_440540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279718 ⟨440540, by decide⟩ :=
  accepted_of_selected 13 279718 ⟨440540, by decide⟩ ⟨13, 2, 0, 440540, 279718, 2045, 16384⟩
    (by decide) selected_cut_17314

theorem selected_cut_17315 : selected 8 ⟨440551, by decide⟩
    (prefixPartial 13 279719) = some ⟨13, 2, 0, 440551, 279719, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_279719_440551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279719 ⟨440551, by decide⟩ :=
  accepted_of_selected 13 279719 ⟨440551, by decide⟩ ⟨13, 2, 0, 440551, 279719, 1017, 16384⟩
    (by decide) selected_cut_17315

theorem unmarked_context_12_69929_440552 : frontier 9 ⟨440552, by decide⟩
    (prefixCache 12 69929) (prefixPartial 12 69929) = false := by
  decide +kernel

theorem node_context_12_69929_440552 : EJMOriginalGlobalDAGData.nodes 9 ⟨440552, by decide⟩ =
    .split (coordinate 12) (![⟨440500, by decide⟩,⟨440518, by decide⟩,⟨440540, by decide⟩,⟨440551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69929_440552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69929 ⟨440552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69929
    ⟨440552, by decide⟩ (by decide) (![⟨440500, by decide⟩,⟨440518, by decide⟩,⟨440540, by decide⟩,⟨440551, by decide⟩]) unmarked_context_12_69929_440552 node_context_12_69929_440552
  intro a
  fin_cases a
  · exact context_13_279716_440500
  · exact context_13_279717_440518
  · exact context_13_279718_440540
  · exact context_13_279719_440551

theorem selected_cut_17316 : selected 8 ⟨440569, by decide⟩
    (prefixPartial 13 279720) = some ⟨13, 2, 0, 440569, 279720, 641, 16384⟩ := by
  decide +kernel

theorem context_13_279720_440569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279720 ⟨440569, by decide⟩ :=
  accepted_of_selected 13 279720 ⟨440569, by decide⟩ ⟨13, 2, 0, 440569, 279720, 641, 16384⟩
    (by decide) selected_cut_17316

theorem selected_cut_17317 : selected 8 ⟨440594, by decide⟩
    (prefixPartial 13 279721) = some ⟨13, 2, 0, 440594, 279721, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_279721_440594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279721 ⟨440594, by decide⟩ :=
  accepted_of_selected 13 279721 ⟨440594, by decide⟩ ⟨13, 2, 0, 440594, 279721, 2061, 16384⟩
    (by decide) selected_cut_17317

theorem selected_cut_17318 : selected 8 ⟨440615, by decide⟩
    (prefixPartial 13 279722) = some ⟨13, 2, 0, 440615, 279722, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_279722_440615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279722 ⟨440615, by decide⟩ :=
  accepted_of_selected 13 279722 ⟨440615, by decide⟩ ⟨13, 2, 0, 440615, 279722, 1457, 16384⟩
    (by decide) selected_cut_17318

theorem selected_cut_17319 : selected 8 ⟨440624, by decide⟩
    (prefixPartial 13 279723) = some ⟨13, 2, 0, 440624, 279723, 941, 16384⟩ := by
  decide +kernel

theorem context_13_279723_440624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279723 ⟨440624, by decide⟩ :=
  accepted_of_selected 13 279723 ⟨440624, by decide⟩ ⟨13, 2, 0, 440624, 279723, 941, 16384⟩
    (by decide) selected_cut_17319

theorem unmarked_context_12_69930_440625 : frontier 9 ⟨440625, by decide⟩
    (prefixCache 12 69930) (prefixPartial 12 69930) = false := by
  decide +kernel

theorem node_context_12_69930_440625 : EJMOriginalGlobalDAGData.nodes 9 ⟨440625, by decide⟩ =
    .split (coordinate 12) (![⟨440569, by decide⟩,⟨440594, by decide⟩,⟨440615, by decide⟩,⟨440624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69930_440625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69930 ⟨440625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69930
    ⟨440625, by decide⟩ (by decide) (![⟨440569, by decide⟩,⟨440594, by decide⟩,⟨440615, by decide⟩,⟨440624, by decide⟩]) unmarked_context_12_69930_440625 node_context_12_69930_440625
  intro a
  fin_cases a
  · exact context_13_279720_440569
  · exact context_13_279721_440594
  · exact context_13_279722_440615
  · exact context_13_279723_440624

theorem selected_cut_17320 : selected 8 ⟨440639, by decide⟩
    (prefixPartial 13 279724) = some ⟨13, 2, 0, 440639, 279724, 577, 16384⟩ := by
  decide +kernel

theorem context_13_279724_440639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279724 ⟨440639, by decide⟩ :=
  accepted_of_selected 13 279724 ⟨440639, by decide⟩ ⟨13, 2, 0, 440639, 279724, 577, 16384⟩
    (by decide) selected_cut_17320

theorem selected_cut_17321 : selected 8 ⟨440662, by decide⟩
    (prefixPartial 13 279725) = some ⟨13, 2, 0, 440662, 279725, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_279725_440662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279725 ⟨440662, by decide⟩ :=
  accepted_of_selected 13 279725 ⟨440662, by decide⟩ ⟨13, 2, 0, 440662, 279725, 2281, 16384⟩
    (by decide) selected_cut_17321

theorem selected_cut_17322 : selected 8 ⟨440681, by decide⟩
    (prefixPartial 13 279726) = some ⟨13, 2, 0, 440681, 279726, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_279726_440681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279726 ⟨440681, by decide⟩ :=
  accepted_of_selected 13 279726 ⟨440681, by decide⟩ ⟨13, 2, 0, 440681, 279726, 1753, 16384⟩
    (by decide) selected_cut_17322

theorem selected_cut_17323 : selected 8 ⟨440691, by decide⟩
    (prefixPartial 13 279727) = some ⟨13, 2, 0, 440691, 279727, 773, 16384⟩ := by
  decide +kernel

theorem context_13_279727_440691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279727 ⟨440691, by decide⟩ :=
  accepted_of_selected 13 279727 ⟨440691, by decide⟩ ⟨13, 2, 0, 440691, 279727, 773, 16384⟩
    (by decide) selected_cut_17323

theorem unmarked_context_12_69931_440692 : frontier 9 ⟨440692, by decide⟩
    (prefixCache 12 69931) (prefixPartial 12 69931) = false := by
  decide +kernel

theorem node_context_12_69931_440692 : EJMOriginalGlobalDAGData.nodes 9 ⟨440692, by decide⟩ =
    .split (coordinate 12) (![⟨440639, by decide⟩,⟨440662, by decide⟩,⟨440681, by decide⟩,⟨440691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69931_440692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69931 ⟨440692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69931
    ⟨440692, by decide⟩ (by decide) (![⟨440639, by decide⟩,⟨440662, by decide⟩,⟨440681, by decide⟩,⟨440691, by decide⟩]) unmarked_context_12_69931_440692 node_context_12_69931_440692
  intro a
  fin_cases a
  · exact context_13_279724_440639
  · exact context_13_279725_440662
  · exact context_13_279726_440681
  · exact context_13_279727_440691

theorem unmarked_context_11_17482_440693 : frontier 10 ⟨440693, by decide⟩
    (prefixCache 11 17482) (prefixPartial 11 17482) = false := by
  decide +kernel

theorem node_context_11_17482_440693 : EJMOriginalGlobalDAGData.nodes 10 ⟨440693, by decide⟩ =
    .split (coordinate 11) (![⟨440481, by decide⟩,⟨440552, by decide⟩,⟨440625, by decide⟩,⟨440692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17482_440693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17482 ⟨440693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17482
    ⟨440693, by decide⟩ (by decide) (![⟨440481, by decide⟩,⟨440552, by decide⟩,⟨440625, by decide⟩,⟨440692, by decide⟩]) unmarked_context_11_17482_440693 node_context_11_17482_440693
  intro a
  fin_cases a
  · exact context_12_69928_440481
  · exact context_12_69929_440552
  · exact context_12_69930_440625
  · exact context_12_69931_440692

theorem selected_cut_17324 : selected 8 ⟨440709, by decide⟩
    (prefixPartial 13 279728) = some ⟨13, 2, 0, 440709, 279728, 557, 16384⟩ := by
  decide +kernel

theorem context_13_279728_440709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279728 ⟨440709, by decide⟩ :=
  accepted_of_selected 13 279728 ⟨440709, by decide⟩ ⟨13, 2, 0, 440709, 279728, 557, 16384⟩
    (by decide) selected_cut_17324

theorem selected_cut_17325 : selected 8 ⟨440753, by decide⟩
    (prefixPartial 13 279729) = some ⟨13, 2, 0, 440753, 279729, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_279729_440753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279729 ⟨440753, by decide⟩ :=
  accepted_of_selected 13 279729 ⟨440753, by decide⟩ ⟨13, 2, 0, 440753, 279729, 2969, 16384⟩
    (by decide) selected_cut_17325

theorem selected_cut_17326 : selected 8 ⟨440792, by decide⟩
    (prefixPartial 13 279730) = some ⟨13, 2, 0, 440792, 279730, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_279730_440792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279730 ⟨440792, by decide⟩ :=
  accepted_of_selected 13 279730 ⟨440792, by decide⟩ ⟨13, 2, 0, 440792, 279730, 2205, 16384⟩
    (by decide) selected_cut_17326

theorem selected_cut_17327 : selected 8 ⟨440801, by decide⟩
    (prefixPartial 13 279731) = some ⟨13, 2, 0, 440801, 279731, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_279731_440801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279731 ⟨440801, by decide⟩ :=
  accepted_of_selected 13 279731 ⟨440801, by decide⟩ ⟨13, 2, 0, 440801, 279731, 1005, 16384⟩
    (by decide) selected_cut_17327

theorem unmarked_context_12_69932_440802 : frontier 9 ⟨440802, by decide⟩
    (prefixCache 12 69932) (prefixPartial 12 69932) = false := by
  decide +kernel

theorem node_context_12_69932_440802 : EJMOriginalGlobalDAGData.nodes 9 ⟨440802, by decide⟩ =
    .split (coordinate 12) (![⟨440709, by decide⟩,⟨440753, by decide⟩,⟨440792, by decide⟩,⟨440801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69932_440802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69932 ⟨440802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69932
    ⟨440802, by decide⟩ (by decide) (![⟨440709, by decide⟩,⟨440753, by decide⟩,⟨440792, by decide⟩,⟨440801, by decide⟩]) unmarked_context_12_69932_440802 node_context_12_69932_440802
  intro a
  fin_cases a
  · exact context_13_279728_440709
  · exact context_13_279729_440753
  · exact context_13_279730_440792
  · exact context_13_279731_440801

theorem selected_cut_17328 : selected 8 ⟨440813, by decide⟩
    (prefixPartial 13 279732) = some ⟨13, 2, 0, 440813, 279732, 385, 16384⟩ := by
  decide +kernel

theorem context_13_279732_440813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279732 ⟨440813, by decide⟩ :=
  accepted_of_selected 13 279732 ⟨440813, by decide⟩ ⟨13, 2, 0, 440813, 279732, 385, 16384⟩
    (by decide) selected_cut_17328

theorem selected_cut_17329 : selected 8 ⟨440836, by decide⟩
    (prefixPartial 13 279733) = some ⟨13, 2, 0, 440836, 279733, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_279733_440836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279733 ⟨440836, by decide⟩ :=
  accepted_of_selected 13 279733 ⟨440836, by decide⟩ ⟨13, 2, 0, 440836, 279733, 1793, 16384⟩
    (by decide) selected_cut_17329

theorem selected_cut_17330 : selected 8 ⟨440864, by decide⟩
    (prefixPartial 13 279734) = some ⟨13, 2, 0, 440864, 279734, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_279734_440864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279734 ⟨440864, by decide⟩ :=
  accepted_of_selected 13 279734 ⟨440864, by decide⟩ ⟨13, 2, 0, 440864, 279734, 2061, 16384⟩
    (by decide) selected_cut_17330

theorem selected_cut_17331 : selected 8 ⟨440870, by decide⟩
    (prefixPartial 13 279735) = some ⟨13, 2, 0, 440870, 279735, 893, 16384⟩ := by
  decide +kernel

theorem context_13_279735_440870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279735 ⟨440870, by decide⟩ :=
  accepted_of_selected 13 279735 ⟨440870, by decide⟩ ⟨13, 2, 0, 440870, 279735, 893, 16384⟩
    (by decide) selected_cut_17331

theorem unmarked_context_12_69933_440871 : frontier 9 ⟨440871, by decide⟩
    (prefixCache 12 69933) (prefixPartial 12 69933) = false := by
  decide +kernel

theorem node_context_12_69933_440871 : EJMOriginalGlobalDAGData.nodes 9 ⟨440871, by decide⟩ =
    .split (coordinate 12) (![⟨440813, by decide⟩,⟨440836, by decide⟩,⟨440864, by decide⟩,⟨440870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69933_440871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69933 ⟨440871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69933
    ⟨440871, by decide⟩ (by decide) (![⟨440813, by decide⟩,⟨440836, by decide⟩,⟨440864, by decide⟩,⟨440870, by decide⟩]) unmarked_context_12_69933_440871 node_context_12_69933_440871
  intro a
  fin_cases a
  · exact context_13_279732_440813
  · exact context_13_279733_440836
  · exact context_13_279734_440864
  · exact context_13_279735_440870

theorem selected_cut_17332 : selected 8 ⟨440882, by decide⟩
    (prefixPartial 13 279736) = some ⟨13, 2, 0, 440882, 279736, 229, 16384⟩ := by
  decide +kernel

theorem context_13_279736_440882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279736 ⟨440882, by decide⟩ :=
  accepted_of_selected 13 279736 ⟨440882, by decide⟩ ⟨13, 2, 0, 440882, 279736, 229, 16384⟩
    (by decide) selected_cut_17332

theorem selected_cut_17333 : selected 8 ⟨440905, by decide⟩
    (prefixPartial 13 279737) = some ⟨13, 2, 0, 440905, 279737, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_279737_440905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279737 ⟨440905, by decide⟩ :=
  accepted_of_selected 13 279737 ⟨440905, by decide⟩ ⟨13, 2, 0, 440905, 279737, 2161, 16384⟩
    (by decide) selected_cut_17333

theorem selected_cut_17334 : selected 8 ⟨440926, by decide⟩
    (prefixPartial 13 279738) = some ⟨13, 2, 0, 440926, 279738, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_279738_440926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279738 ⟨440926, by decide⟩ :=
  accepted_of_selected 13 279738 ⟨440926, by decide⟩ ⟨13, 2, 0, 440926, 279738, 1437, 16384⟩
    (by decide) selected_cut_17334

theorem selected_cut_17335 : selected 8 ⟨440932, by decide⟩
    (prefixPartial 13 279739) = some ⟨13, 2, 0, 440932, 279739, 825, 16384⟩ := by
  decide +kernel

theorem context_13_279739_440932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279739 ⟨440932, by decide⟩ :=
  accepted_of_selected 13 279739 ⟨440932, by decide⟩ ⟨13, 2, 0, 440932, 279739, 825, 16384⟩
    (by decide) selected_cut_17335

theorem unmarked_context_12_69934_440933 : frontier 9 ⟨440933, by decide⟩
    (prefixCache 12 69934) (prefixPartial 12 69934) = false := by
  decide +kernel

theorem node_context_12_69934_440933 : EJMOriginalGlobalDAGData.nodes 9 ⟨440933, by decide⟩ =
    .split (coordinate 12) (![⟨440882, by decide⟩,⟨440905, by decide⟩,⟨440926, by decide⟩,⟨440932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69934_440933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69934 ⟨440933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69934
    ⟨440933, by decide⟩ (by decide) (![⟨440882, by decide⟩,⟨440905, by decide⟩,⟨440926, by decide⟩,⟨440932, by decide⟩]) unmarked_context_12_69934_440933 node_context_12_69934_440933
  intro a
  fin_cases a
  · exact context_13_279736_440882
  · exact context_13_279737_440905
  · exact context_13_279738_440926
  · exact context_13_279739_440932

theorem selected_cut_17336 : selected 8 ⟨440937, by decide⟩
    (prefixPartial 13 279740) = some ⟨13, 2, 0, 440937, 279740, 117, 16384⟩ := by
  decide +kernel

theorem context_13_279740_440937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279740 ⟨440937, by decide⟩ :=
  accepted_of_selected 13 279740 ⟨440937, by decide⟩ ⟨13, 2, 0, 440937, 279740, 117, 16384⟩
    (by decide) selected_cut_17336

theorem selected_cut_17337 : selected 8 ⟨440961, by decide⟩
    (prefixPartial 13 279741) = some ⟨13, 2, 0, 440961, 279741, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_279741_440961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279741 ⟨440961, by decide⟩ :=
  accepted_of_selected 13 279741 ⟨440961, by decide⟩ ⟨13, 2, 0, 440961, 279741, 2249, 16384⟩
    (by decide) selected_cut_17337

theorem selected_cut_17338 : selected 8 ⟨440980, by decide⟩
    (prefixPartial 13 279742) = some ⟨13, 2, 0, 440980, 279742, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_279742_440980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279742 ⟨440980, by decide⟩ :=
  accepted_of_selected 13 279742 ⟨440980, by decide⟩ ⟨13, 2, 0, 440980, 279742, 1605, 16384⟩
    (by decide) selected_cut_17338

theorem selected_cut_17339 : selected 8 ⟨440986, by decide⟩
    (prefixPartial 13 279743) = some ⟨13, 2, 0, 440986, 279743, 717, 16384⟩ := by
  decide +kernel

theorem context_13_279743_440986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279743 ⟨440986, by decide⟩ :=
  accepted_of_selected 13 279743 ⟨440986, by decide⟩ ⟨13, 2, 0, 440986, 279743, 717, 16384⟩
    (by decide) selected_cut_17339

theorem unmarked_context_12_69935_440987 : frontier 9 ⟨440987, by decide⟩
    (prefixCache 12 69935) (prefixPartial 12 69935) = false := by
  decide +kernel

theorem node_context_12_69935_440987 : EJMOriginalGlobalDAGData.nodes 9 ⟨440987, by decide⟩ =
    .split (coordinate 12) (![⟨440937, by decide⟩,⟨440961, by decide⟩,⟨440980, by decide⟩,⟨440986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69935_440987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69935 ⟨440987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69935
    ⟨440987, by decide⟩ (by decide) (![⟨440937, by decide⟩,⟨440961, by decide⟩,⟨440980, by decide⟩,⟨440986, by decide⟩]) unmarked_context_12_69935_440987 node_context_12_69935_440987
  intro a
  fin_cases a
  · exact context_13_279740_440937
  · exact context_13_279741_440961
  · exact context_13_279742_440980
  · exact context_13_279743_440986

theorem unmarked_context_11_17483_440988 : frontier 10 ⟨440988, by decide⟩
    (prefixCache 11 17483) (prefixPartial 11 17483) = false := by
  decide +kernel

theorem node_context_11_17483_440988 : EJMOriginalGlobalDAGData.nodes 10 ⟨440988, by decide⟩ =
    .split (coordinate 11) (![⟨440802, by decide⟩,⟨440871, by decide⟩,⟨440933, by decide⟩,⟨440987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17483_440988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17483 ⟨440988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17483
    ⟨440988, by decide⟩ (by decide) (![⟨440802, by decide⟩,⟨440871, by decide⟩,⟨440933, by decide⟩,⟨440987, by decide⟩]) unmarked_context_11_17483_440988 node_context_11_17483_440988
  intro a
  fin_cases a
  · exact context_12_69932_440802
  · exact context_12_69933_440871
  · exact context_12_69934_440933
  · exact context_12_69935_440987

theorem unmarked_context_10_4370_440989 : frontier 11 ⟨440989, by decide⟩
    (prefixCache 10 4370) (prefixPartial 10 4370) = false := by
  decide +kernel

theorem node_context_10_4370_440989 : EJMOriginalGlobalDAGData.nodes 11 ⟨440989, by decide⟩ =
    .split (coordinate 10) (![⟨439908, by decide⟩,⟨440373, by decide⟩,⟨440693, by decide⟩,⟨440988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4370_440989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4370 ⟨440989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4370
    ⟨440989, by decide⟩ (by decide) (![⟨439908, by decide⟩,⟨440373, by decide⟩,⟨440693, by decide⟩,⟨440988, by decide⟩]) unmarked_context_10_4370_440989 node_context_10_4370_440989
  intro a
  fin_cases a
  · exact context_11_17480_439908
  · exact context_11_17481_440373
  · exact context_11_17482_440693
  · exact context_11_17483_440988

theorem selected_cut_17340 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4371) = some ⟨10, 1, 0, 3440, 4371, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4371_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4371 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4371 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4371, 1, 1048576⟩
    (by decide) selected_cut_17340

theorem unmarked_context_9_1092_440990 : frontier 12 ⟨440990, by decide⟩
    (prefixCache 9 1092) (prefixPartial 9 1092) = false := by
  decide +kernel

theorem node_context_9_1092_440990 : EJMOriginalGlobalDAGData.nodes 12 ⟨440990, by decide⟩ =
    .split (coordinate 9) (![⟨438840, by decide⟩,⟨439627, by decide⟩,⟨440989, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1092_440990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1092 ⟨440990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1092
    ⟨440990, by decide⟩ (by decide) (![⟨438840, by decide⟩,⟨439627, by decide⟩,⟨440989, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1092_440990 node_context_9_1092_440990
  intro a
  fin_cases a
  · exact context_10_4368_438840
  · exact context_10_4369_439627
  · exact context_10_4370_440989
  · exact context_10_4371_3440

theorem selected_cut_17341 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4372) = some ⟨10, 1, 0, 3442, 4372, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4372_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4372 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4372 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4372, 1, 1048576⟩
    (by decide) selected_cut_17341

theorem selected_cut_17342 : selected 9 ⟨441018, by decide⟩
    (prefixPartial 12 69968) = some ⟨12, 2, 0, 441018, 69968, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_69968_441018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69968 ⟨441018, by decide⟩ :=
  accepted_of_selected 12 69968 ⟨441018, by decide⟩ ⟨12, 2, 0, 441018, 69968, 1077, 65536⟩
    (by decide) selected_cut_17342

theorem selected_cut_17343 : selected 9 ⟨441053, by decide⟩
    (prefixPartial 12 69969) = some ⟨12, 2, 0, 441053, 69969, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_69969_441053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69969 ⟨441053, by decide⟩ :=
  accepted_of_selected 12 69969 ⟨441053, by decide⟩ ⟨12, 2, 0, 441053, 69969, 2065, 65536⟩
    (by decide) selected_cut_17343

theorem selected_cut_17344 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 279880) = some ⟨13, 1, 0, 3444, 279880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_279880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 279880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 279880, 1, 16384⟩
    (by decide) selected_cut_17344

theorem selected_cut_17345 : selected 8 ⟨441094, by decide⟩
    (prefixPartial 13 279881) = some ⟨13, 2, 0, 441094, 279881, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_279881_441094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279881 ⟨441094, by decide⟩ :=
  accepted_of_selected 13 279881 ⟨441094, by decide⟩ ⟨13, 2, 0, 441094, 279881, 1781, 16384⟩
    (by decide) selected_cut_17345

theorem selected_cut_17346 : selected 8 ⟨441118, by decide⟩
    (prefixPartial 13 279882) = some ⟨13, 2, 0, 441118, 279882, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_279882_441118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279882 ⟨441118, by decide⟩ :=
  accepted_of_selected 13 279882 ⟨441118, by decide⟩ ⟨13, 2, 0, 441118, 279882, 1597, 16384⟩
    (by decide) selected_cut_17346

theorem selected_cut_17347 : selected 8 ⟨441124, by decide⟩
    (prefixPartial 13 279883) = some ⟨13, 2, 0, 441124, 279883, 865, 16384⟩ := by
  decide +kernel

theorem context_13_279883_441124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279883 ⟨441124, by decide⟩ :=
  accepted_of_selected 13 279883 ⟨441124, by decide⟩ ⟨13, 2, 0, 441124, 279883, 865, 16384⟩
    (by decide) selected_cut_17347

theorem unmarked_context_12_69970_441125 : frontier 9 ⟨441125, by decide⟩
    (prefixCache 12 69970) (prefixPartial 12 69970) = false := by
  decide +kernel

theorem node_context_12_69970_441125 : EJMOriginalGlobalDAGData.nodes 9 ⟨441125, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨441094, by decide⟩,⟨441118, by decide⟩,⟨441124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69970_441125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69970 ⟨441125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69970
    ⟨441125, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨441094, by decide⟩,⟨441118, by decide⟩,⟨441124, by decide⟩]) unmarked_context_12_69970_441125 node_context_12_69970_441125
  intro a
  fin_cases a
  · exact context_13_279880_3444
  · exact context_13_279881_441094
  · exact context_13_279882_441118
  · exact context_13_279883_441124

theorem selected_cut_17348 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69971) = some ⟨12, 1, 0, 893, 69971, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69971_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69971 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69971 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69971, 1, 65536⟩
    (by decide) selected_cut_17348

theorem unmarked_context_11_17492_441126 : frontier 10 ⟨441126, by decide⟩
    (prefixCache 11 17492) (prefixPartial 11 17492) = false := by
  decide +kernel

theorem node_context_11_17492_441126 : EJMOriginalGlobalDAGData.nodes 10 ⟨441126, by decide⟩ =
    .split (coordinate 11) (![⟨441018, by decide⟩,⟨441053, by decide⟩,⟨441125, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17492_441126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17492 ⟨441126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17492
    ⟨441126, by decide⟩ (by decide) (![⟨441018, by decide⟩,⟨441053, by decide⟩,⟨441125, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17492_441126 node_context_11_17492_441126
  intro a
  fin_cases a
  · exact context_12_69968_441018
  · exact context_12_69969_441053
  · exact context_12_69970_441125
  · exact context_12_69971_893

theorem selected_cut_17349 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69972) = some ⟨12, 1, 0, 895, 69972, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69972_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69972 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69972 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69972, 1, 65536⟩
    (by decide) selected_cut_17349

theorem selected_cut_17350 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 69973) = some ⟨12, 1, 0, 439069, 69973, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69973_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69973 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 69973 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 69973, 1, 65536⟩
    (by decide) selected_cut_17350

theorem selected_cut_17351 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 279896) = some ⟨13, 1, 0, 3444, 279896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_279896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 279896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 279896, 1, 16384⟩
    (by decide) selected_cut_17351

theorem selected_cut_17352 : selected 8 ⟨441161, by decide⟩
    (prefixPartial 13 279897) = some ⟨13, 2, 0, 441161, 279897, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_279897_441161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279897 ⟨441161, by decide⟩ :=
  accepted_of_selected 13 279897 ⟨441161, by decide⟩ ⟨13, 2, 0, 441161, 279897, 1781, 16384⟩
    (by decide) selected_cut_17352

theorem selected_cut_17353 : selected 8 ⟨441187, by decide⟩
    (prefixPartial 13 279898) = some ⟨13, 2, 0, 441187, 279898, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_279898_441187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279898 ⟨441187, by decide⟩ :=
  accepted_of_selected 13 279898 ⟨441187, by decide⟩ ⟨13, 2, 0, 441187, 279898, 1477, 16384⟩
    (by decide) selected_cut_17353

theorem selected_cut_17354 : selected 8 ⟨441197, by decide⟩
    (prefixPartial 13 279899) = some ⟨13, 2, 0, 441197, 279899, 889, 16384⟩ := by
  decide +kernel

theorem context_13_279899_441197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279899 ⟨441197, by decide⟩ :=
  accepted_of_selected 13 279899 ⟨441197, by decide⟩ ⟨13, 2, 0, 441197, 279899, 889, 16384⟩
    (by decide) selected_cut_17354

theorem unmarked_context_12_69974_441198 : frontier 9 ⟨441198, by decide⟩
    (prefixCache 12 69974) (prefixPartial 12 69974) = false := by
  decide +kernel

theorem node_context_12_69974_441198 : EJMOriginalGlobalDAGData.nodes 9 ⟨441198, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨441161, by decide⟩,⟨441187, by decide⟩,⟨441197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69974_441198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69974 ⟨441198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69974
    ⟨441198, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨441161, by decide⟩,⟨441187, by decide⟩,⟨441197, by decide⟩]) unmarked_context_12_69974_441198 node_context_12_69974_441198
  intro a
  fin_cases a
  · exact context_13_279896_3444
  · exact context_13_279897_441161
  · exact context_13_279898_441187
  · exact context_13_279899_441197

theorem selected_cut_17355 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69975) = some ⟨12, 1, 0, 893, 69975, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69975_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69975 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69975 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69975, 1, 65536⟩
    (by decide) selected_cut_17355

theorem unmarked_context_11_17493_441199 : frontier 10 ⟨441199, by decide⟩
    (prefixCache 11 17493) (prefixPartial 11 17493) = false := by
  decide +kernel

theorem node_context_11_17493_441199 : EJMOriginalGlobalDAGData.nodes 10 ⟨441199, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨439069, by decide⟩,⟨441198, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17493_441199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17493 ⟨441199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17493
    ⟨441199, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨439069, by decide⟩,⟨441198, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17493_441199 node_context_11_17493_441199
  intro a
  fin_cases a
  · exact context_12_69972_895
  · exact context_12_69973_439069
  · exact context_12_69974_441198
  · exact context_12_69975_893

theorem selected_cut_17356 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69976) = some ⟨12, 1, 0, 895, 69976, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69976_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69976 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69976 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69976, 1, 65536⟩
    (by decide) selected_cut_17356

theorem selected_cut_17357 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69977) = some ⟨12, 1, 0, 895, 69977, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69977_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69977 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69977 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69977, 1, 65536⟩
    (by decide) selected_cut_17357

theorem selected_cut_17358 : selected 9 ⟨441259, by decide⟩
    (prefixPartial 12 69978) = some ⟨12, 2, 0, 441259, 69978, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_69978_441259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69978 ⟨441259, by decide⟩ :=
  accepted_of_selected 12 69978 ⟨441259, by decide⟩ ⟨12, 2, 0, 441259, 69978, 2545, 65536⟩
    (by decide) selected_cut_17358

theorem selected_cut_17359 : selected 9 ⟨441325, by decide⟩
    (prefixPartial 12 69979) = some ⟨12, 2, 0, 441325, 69979, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_69979_441325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69979 ⟨441325, by decide⟩ :=
  accepted_of_selected 12 69979 ⟨441325, by decide⟩ ⟨12, 2, 0, 441325, 69979, 2533, 65536⟩
    (by decide) selected_cut_17359

theorem unmarked_context_11_17494_441326 : frontier 10 ⟨441326, by decide⟩
    (prefixCache 11 17494) (prefixPartial 11 17494) = false := by
  decide +kernel

theorem node_context_11_17494_441326 : EJMOriginalGlobalDAGData.nodes 10 ⟨441326, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨441259, by decide⟩,⟨441325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17494_441326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17494 ⟨441326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17494
    ⟨441326, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨441259, by decide⟩,⟨441325, by decide⟩]) unmarked_context_11_17494_441326 node_context_11_17494_441326
  intro a
  fin_cases a
  · exact context_12_69976_895
  · exact context_12_69977_895
  · exact context_12_69978_441259
  · exact context_12_69979_441325

theorem selected_cut_17360 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17495) = some ⟨11, 1, 0, 1736, 17495, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17495_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17495 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17495 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17495, 1, 262144⟩
    (by decide) selected_cut_17360

theorem unmarked_context_10_4373_441327 : frontier 11 ⟨441327, by decide⟩
    (prefixCache 10 4373) (prefixPartial 10 4373) = false := by
  decide +kernel

theorem node_context_10_4373_441327 : EJMOriginalGlobalDAGData.nodes 11 ⟨441327, by decide⟩ =
    .split (coordinate 10) (![⟨441126, by decide⟩,⟨441199, by decide⟩,⟨441326, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4373_441327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4373 ⟨441327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4373
    ⟨441327, by decide⟩ (by decide) (![⟨441126, by decide⟩,⟨441199, by decide⟩,⟨441326, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4373_441327 node_context_10_4373_441327
  intro a
  fin_cases a
  · exact context_11_17492_441126
  · exact context_11_17493_441199
  · exact context_11_17494_441326
  · exact context_11_17495_1736

theorem selected_cut_17361 : selected 9 ⟨441378, by decide⟩
    (prefixPartial 12 69984) = some ⟨12, 2, 0, 441378, 69984, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_69984_441378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69984 ⟨441378, by decide⟩ :=
  accepted_of_selected 12 69984 ⟨441378, by decide⟩ ⟨12, 2, 0, 441378, 69984, 2993, 65536⟩
    (by decide) selected_cut_17361

theorem selected_cut_17362 : selected 9 ⟨441460, by decide⟩
    (prefixPartial 12 69985) = some ⟨12, 2, 0, 441460, 69985, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_69985_441460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69985 ⟨441460, by decide⟩ :=
  accepted_of_selected 12 69985 ⟨441460, by decide⟩ ⟨12, 2, 0, 441460, 69985, 3665, 65536⟩
    (by decide) selected_cut_17362

theorem selected_cut_17363 : selected 9 ⟨441555, by decide⟩
    (prefixPartial 12 69986) = some ⟨12, 2, 0, 441555, 69986, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_69986_441555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69986 ⟨441555, by decide⟩ :=
  accepted_of_selected 12 69986 ⟨441555, by decide⟩ ⟨12, 2, 0, 441555, 69986, 3661, 65536⟩
    (by decide) selected_cut_17363

theorem selected_cut_17364 : selected 9 ⟨441626, by decide⟩
    (prefixPartial 12 69987) = some ⟨12, 2, 0, 441626, 69987, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_69987_441626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69987 ⟨441626, by decide⟩ :=
  accepted_of_selected 12 69987 ⟨441626, by decide⟩ ⟨12, 2, 0, 441626, 69987, 3545, 65536⟩
    (by decide) selected_cut_17364

theorem unmarked_context_11_17496_441627 : frontier 10 ⟨441627, by decide⟩
    (prefixCache 11 17496) (prefixPartial 11 17496) = false := by
  decide +kernel

theorem node_context_11_17496_441627 : EJMOriginalGlobalDAGData.nodes 10 ⟨441627, by decide⟩ =
    .split (coordinate 11) (![⟨441378, by decide⟩,⟨441460, by decide⟩,⟨441555, by decide⟩,⟨441626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17496_441627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17496 ⟨441627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17496
    ⟨441627, by decide⟩ (by decide) (![⟨441378, by decide⟩,⟨441460, by decide⟩,⟨441555, by decide⟩,⟨441626, by decide⟩]) unmarked_context_11_17496_441627 node_context_11_17496_441627
  intro a
  fin_cases a
  · exact context_12_69984_441378
  · exact context_12_69985_441460
  · exact context_12_69986_441555
  · exact context_12_69987_441626

theorem selected_cut_17365 : selected 9 ⟨441671, by decide⟩
    (prefixPartial 12 69988) = some ⟨12, 2, 0, 441671, 69988, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_69988_441671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69988 ⟨441671, by decide⟩ :=
  accepted_of_selected 12 69988 ⟨441671, by decide⟩ ⟨12, 2, 0, 441671, 69988, 2929, 65536⟩
    (by decide) selected_cut_17365

theorem selected_cut_17366 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 69989) = some ⟨12, 1, 0, 441672, 69989, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69989_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69989 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 69989 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 69989, 1, 65536⟩
    (by decide) selected_cut_17366

theorem selected_cut_17367 : selected 9 ⟨441734, by decide⟩
    (prefixPartial 12 69990) = some ⟨12, 2, 0, 441734, 69990, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_69990_441734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69990 ⟨441734, by decide⟩ :=
  accepted_of_selected 12 69990 ⟨441734, by decide⟩ ⟨12, 2, 0, 441734, 69990, 3117, 65536⟩
    (by decide) selected_cut_17367

theorem selected_cut_17368 : selected 9 ⟨441789, by decide⟩
    (prefixPartial 12 69991) = some ⟨12, 2, 0, 441789, 69991, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_69991_441789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69991 ⟨441789, by decide⟩ :=
  accepted_of_selected 12 69991 ⟨441789, by decide⟩ ⟨12, 2, 0, 441789, 69991, 3057, 65536⟩
    (by decide) selected_cut_17368

theorem unmarked_context_11_17497_441790 : frontier 10 ⟨441790, by decide⟩
    (prefixCache 11 17497) (prefixPartial 11 17497) = false := by
  decide +kernel

theorem node_context_11_17497_441790 : EJMOriginalGlobalDAGData.nodes 10 ⟨441790, by decide⟩ =
    .split (coordinate 11) (![⟨441671, by decide⟩,⟨441672, by decide⟩,⟨441734, by decide⟩,⟨441789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17497_441790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17497 ⟨441790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17497
    ⟨441790, by decide⟩ (by decide) (![⟨441671, by decide⟩,⟨441672, by decide⟩,⟨441734, by decide⟩,⟨441789, by decide⟩]) unmarked_context_11_17497_441790 node_context_11_17497_441790
  intro a
  fin_cases a
  · exact context_12_69988_441671
  · exact context_12_69989_441672
  · exact context_12_69990_441734
  · exact context_12_69991_441789

theorem selected_cut_17369 : selected 9 ⟨441854, by decide⟩
    (prefixPartial 12 69992) = some ⟨12, 2, 0, 441854, 69992, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_69992_441854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69992 ⟨441854, by decide⟩ :=
  accepted_of_selected 12 69992 ⟨441854, by decide⟩ ⟨12, 2, 0, 441854, 69992, 2889, 65536⟩
    (by decide) selected_cut_17369

theorem selected_cut_17370 : selected 9 ⟨441932, by decide⟩
    (prefixPartial 12 69993) = some ⟨12, 2, 0, 441932, 69993, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_69993_441932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69993 ⟨441932, by decide⟩ :=
  accepted_of_selected 12 69993 ⟨441932, by decide⟩ ⟨12, 2, 0, 441932, 69993, 3017, 65536⟩
    (by decide) selected_cut_17370

theorem selected_cut_17371 : selected 9 ⟨441988, by decide⟩
    (prefixPartial 12 69994) = some ⟨12, 2, 0, 441988, 69994, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_69994_441988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69994 ⟨441988, by decide⟩ :=
  accepted_of_selected 12 69994 ⟨441988, by decide⟩ ⟨12, 2, 0, 441988, 69994, 2581, 65536⟩
    (by decide) selected_cut_17371

theorem selected_cut_17372 : selected 9 ⟨442041, by decide⟩
    (prefixPartial 12 69995) = some ⟨12, 2, 0, 442041, 69995, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_69995_442041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69995 ⟨442041, by decide⟩ :=
  accepted_of_selected 12 69995 ⟨442041, by decide⟩ ⟨12, 2, 0, 442041, 69995, 2533, 65536⟩
    (by decide) selected_cut_17372

theorem unmarked_context_11_17498_442042 : frontier 10 ⟨442042, by decide⟩
    (prefixCache 11 17498) (prefixPartial 11 17498) = false := by
  decide +kernel

theorem node_context_11_17498_442042 : EJMOriginalGlobalDAGData.nodes 10 ⟨442042, by decide⟩ =
    .split (coordinate 11) (![⟨441854, by decide⟩,⟨441932, by decide⟩,⟨441988, by decide⟩,⟨442041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17498_442042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17498 ⟨442042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17498
    ⟨442042, by decide⟩ (by decide) (![⟨441854, by decide⟩,⟨441932, by decide⟩,⟨441988, by decide⟩,⟨442041, by decide⟩]) unmarked_context_11_17498_442042 node_context_11_17498_442042
  intro a
  fin_cases a
  · exact context_12_69992_441854
  · exact context_12_69993_441932
  · exact context_12_69994_441988
  · exact context_12_69995_442041

theorem selected_cut_17373 : selected 9 ⟨442100, by decide⟩
    (prefixPartial 12 69996) = some ⟨12, 2, 0, 442100, 69996, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_69996_442100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69996 ⟨442100, by decide⟩ :=
  accepted_of_selected 12 69996 ⟨442100, by decide⟩ ⟨12, 2, 0, 442100, 69996, 2289, 65536⟩
    (by decide) selected_cut_17373

theorem selected_cut_17374 : selected 9 ⟨442151, by decide⟩
    (prefixPartial 12 69997) = some ⟨12, 2, 0, 442151, 69997, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_69997_442151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69997 ⟨442151, by decide⟩ :=
  accepted_of_selected 12 69997 ⟨442151, by decide⟩ ⟨12, 2, 0, 442151, 69997, 2365, 65536⟩
    (by decide) selected_cut_17374

theorem selected_cut_17375 : selected 9 ⟨442200, by decide⟩
    (prefixPartial 12 69998) = some ⟨12, 2, 0, 442200, 69998, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_69998_442200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69998 ⟨442200, by decide⟩ :=
  accepted_of_selected 12 69998 ⟨442200, by decide⟩ ⟨12, 2, 0, 442200, 69998, 1973, 65536⟩
    (by decide) selected_cut_17375

theorem selected_cut_17376 : selected 9 ⟨442238, by decide⟩
    (prefixPartial 12 69999) = some ⟨12, 2, 0, 442238, 69999, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_69999_442238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69999 ⟨442238, by decide⟩ :=
  accepted_of_selected 12 69999 ⟨442238, by decide⟩ ⟨12, 2, 0, 442238, 69999, 1849, 65536⟩
    (by decide) selected_cut_17376

theorem unmarked_context_11_17499_442239 : frontier 10 ⟨442239, by decide⟩
    (prefixCache 11 17499) (prefixPartial 11 17499) = false := by
  decide +kernel

theorem node_context_11_17499_442239 : EJMOriginalGlobalDAGData.nodes 10 ⟨442239, by decide⟩ =
    .split (coordinate 11) (![⟨442100, by decide⟩,⟨442151, by decide⟩,⟨442200, by decide⟩,⟨442238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17499_442239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17499 ⟨442239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17499
    ⟨442239, by decide⟩ (by decide) (![⟨442100, by decide⟩,⟨442151, by decide⟩,⟨442200, by decide⟩,⟨442238, by decide⟩]) unmarked_context_11_17499_442239 node_context_11_17499_442239
  intro a
  fin_cases a
  · exact context_12_69996_442100
  · exact context_12_69997_442151
  · exact context_12_69998_442200
  · exact context_12_69999_442238

theorem unmarked_context_10_4374_442240 : frontier 11 ⟨442240, by decide⟩
    (prefixCache 10 4374) (prefixPartial 10 4374) = false := by
  decide +kernel

theorem node_context_10_4374_442240 : EJMOriginalGlobalDAGData.nodes 11 ⟨442240, by decide⟩ =
    .split (coordinate 10) (![⟨441627, by decide⟩,⟨441790, by decide⟩,⟨442042, by decide⟩,⟨442239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4374_442240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4374 ⟨442240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4374
    ⟨442240, by decide⟩ (by decide) (![⟨441627, by decide⟩,⟨441790, by decide⟩,⟨442042, by decide⟩,⟨442239, by decide⟩]) unmarked_context_10_4374_442240 node_context_10_4374_442240
  intro a
  fin_cases a
  · exact context_11_17496_441627
  · exact context_11_17497_441790
  · exact context_11_17498_442042
  · exact context_11_17499_442239

theorem selected_cut_17377 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4375) = some ⟨10, 1, 0, 3440, 4375, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4375_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4375 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4375 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4375, 1, 1048576⟩
    (by decide) selected_cut_17377

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
