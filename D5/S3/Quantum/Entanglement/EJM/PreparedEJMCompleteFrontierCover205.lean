/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover204
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19683 : selected 8 ⟨503243, by decide⟩
    (prefixPartial 13 289137) = some ⟨13, 2, 0, 503243, 289137, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_289137_503243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289137 ⟨503243, by decide⟩ :=
  accepted_of_selected 13 289137 ⟨503243, by decide⟩ ⟨13, 2, 0, 503243, 289137, 1817, 16384⟩
    (by decide) selected_cut_19683

theorem selected_cut_19684 : selected 8 ⟨503264, by decide⟩
    (prefixPartial 13 289138) = some ⟨13, 2, 0, 503264, 289138, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_289138_503264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289138 ⟨503264, by decide⟩ :=
  accepted_of_selected 13 289138 ⟨503264, by decide⟩ ⟨13, 2, 0, 503264, 289138, 1721, 16384⟩
    (by decide) selected_cut_19684

theorem selected_cut_19685 : selected 8 ⟨503279, by decide⟩
    (prefixPartial 13 289139) = some ⟨13, 2, 0, 503279, 289139, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_289139_503279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289139 ⟨503279, by decide⟩ :=
  accepted_of_selected 13 289139 ⟨503279, by decide⟩ ⟨13, 2, 0, 503279, 289139, 1133, 16384⟩
    (by decide) selected_cut_19685

theorem unmarked_context_12_72284_503280 : frontier 9 ⟨503280, by decide⟩
    (prefixCache 12 72284) (prefixPartial 12 72284) = false := by
  decide +kernel

theorem node_context_12_72284_503280 : EJMOriginalGlobalDAGData.nodes 9 ⟨503280, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503243, by decide⟩,⟨503264, by decide⟩,⟨503279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72284_503280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72284 ⟨503280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72284
    ⟨503280, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503243, by decide⟩,⟨503264, by decide⟩,⟨503279, by decide⟩]) unmarked_context_12_72284_503280 node_context_12_72284_503280
  intro a
  fin_cases a
  · exact context_13_289136_3444
  · exact context_13_289137_503243
  · exact context_13_289138_503264
  · exact context_13_289139_503279

theorem selected_cut_19686 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289140) = some ⟨13, 1, 0, 3444, 289140, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289140_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289140 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289140 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289140, 1, 16384⟩
    (by decide) selected_cut_19686

theorem selected_cut_19687 : selected 8 ⟨503300, by decide⟩
    (prefixPartial 13 289141) = some ⟨13, 2, 0, 503300, 289141, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_289141_503300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289141 ⟨503300, by decide⟩ :=
  accepted_of_selected 13 289141 ⟨503300, by decide⟩ ⟨13, 2, 0, 503300, 289141, 1521, 16384⟩
    (by decide) selected_cut_19687

theorem selected_cut_19688 : selected 8 ⟨503322, by decide⟩
    (prefixPartial 13 289142) = some ⟨13, 2, 0, 503322, 289142, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_289142_503322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289142 ⟨503322, by decide⟩ :=
  accepted_of_selected 13 289142 ⟨503322, by decide⟩ ⟨13, 2, 0, 503322, 289142, 1521, 16384⟩
    (by decide) selected_cut_19688

theorem selected_cut_19689 : selected 8 ⟨503342, by decide⟩
    (prefixPartial 13 289143) = some ⟨13, 2, 0, 503342, 289143, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_289143_503342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289143 ⟨503342, by decide⟩ :=
  accepted_of_selected 13 289143 ⟨503342, by decide⟩ ⟨13, 2, 0, 503342, 289143, 1237, 16384⟩
    (by decide) selected_cut_19689

theorem unmarked_context_12_72285_503343 : frontier 9 ⟨503343, by decide⟩
    (prefixCache 12 72285) (prefixPartial 12 72285) = false := by
  decide +kernel

theorem node_context_12_72285_503343 : EJMOriginalGlobalDAGData.nodes 9 ⟨503343, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503300, by decide⟩,⟨503322, by decide⟩,⟨503342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72285_503343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72285 ⟨503343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72285
    ⟨503343, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503300, by decide⟩,⟨503322, by decide⟩,⟨503342, by decide⟩]) unmarked_context_12_72285_503343 node_context_12_72285_503343
  intro a
  fin_cases a
  · exact context_13_289140_3444
  · exact context_13_289141_503300
  · exact context_13_289142_503322
  · exact context_13_289143_503342

theorem selected_cut_19690 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289144) = some ⟨13, 1, 0, 3444, 289144, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289144_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289144 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289144 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289144, 1, 16384⟩
    (by decide) selected_cut_19690

theorem selected_cut_19691 : selected 8 ⟨503373, by decide⟩
    (prefixPartial 13 289145) = some ⟨13, 2, 0, 503373, 289145, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_289145_503373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289145 ⟨503373, by decide⟩ :=
  accepted_of_selected 13 289145 ⟨503373, by decide⟩ ⟨13, 2, 0, 503373, 289145, 1829, 16384⟩
    (by decide) selected_cut_19691

theorem selected_cut_19692 : selected 8 ⟨503400, by decide⟩
    (prefixPartial 13 289146) = some ⟨13, 2, 0, 503400, 289146, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_289146_503400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289146 ⟨503400, by decide⟩ :=
  accepted_of_selected 13 289146 ⟨503400, by decide⟩ ⟨13, 2, 0, 503400, 289146, 1809, 16384⟩
    (by decide) selected_cut_19692

theorem selected_cut_19693 : selected 8 ⟨503417, by decide⟩
    (prefixPartial 13 289147) = some ⟨13, 2, 0, 503417, 289147, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_289147_503417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289147 ⟨503417, by decide⟩ :=
  accepted_of_selected 13 289147 ⟨503417, by decide⟩ ⟨13, 2, 0, 503417, 289147, 1129, 16384⟩
    (by decide) selected_cut_19693

theorem unmarked_context_12_72286_503418 : frontier 9 ⟨503418, by decide⟩
    (prefixCache 12 72286) (prefixPartial 12 72286) = false := by
  decide +kernel

theorem node_context_12_72286_503418 : EJMOriginalGlobalDAGData.nodes 9 ⟨503418, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503373, by decide⟩,⟨503400, by decide⟩,⟨503417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72286_503418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72286 ⟨503418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72286
    ⟨503418, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503373, by decide⟩,⟨503400, by decide⟩,⟨503417, by decide⟩]) unmarked_context_12_72286_503418 node_context_12_72286_503418
  intro a
  fin_cases a
  · exact context_13_289144_3444
  · exact context_13_289145_503373
  · exact context_13_289146_503400
  · exact context_13_289147_503417

theorem selected_cut_19694 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289148) = some ⟨13, 1, 0, 3444, 289148, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289148_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289148 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289148 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289148, 1, 16384⟩
    (by decide) selected_cut_19694

theorem selected_cut_19695 : selected 8 ⟨503442, by decide⟩
    (prefixPartial 13 289149) = some ⟨13, 2, 0, 503442, 289149, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_289149_503442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289149 ⟨503442, by decide⟩ :=
  accepted_of_selected 13 289149 ⟨503442, by decide⟩ ⟨13, 2, 0, 503442, 289149, 1717, 16384⟩
    (by decide) selected_cut_19695

theorem selected_cut_19696 : selected 8 ⟨503469, by decide⟩
    (prefixPartial 13 289150) = some ⟨13, 2, 0, 503469, 289150, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_289150_503469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289150 ⟨503469, by decide⟩ :=
  accepted_of_selected 13 289150 ⟨503469, by decide⟩ ⟨13, 2, 0, 503469, 289150, 2049, 16384⟩
    (by decide) selected_cut_19696

theorem selected_cut_19697 : selected 8 ⟨503490, by decide⟩
    (prefixPartial 13 289151) = some ⟨13, 2, 0, 503490, 289151, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_289151_503490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289151 ⟨503490, by decide⟩ :=
  accepted_of_selected 13 289151 ⟨503490, by decide⟩ ⟨13, 2, 0, 503490, 289151, 1157, 16384⟩
    (by decide) selected_cut_19697

theorem unmarked_context_12_72287_503491 : frontier 9 ⟨503491, by decide⟩
    (prefixCache 12 72287) (prefixPartial 12 72287) = false := by
  decide +kernel

theorem node_context_12_72287_503491 : EJMOriginalGlobalDAGData.nodes 9 ⟨503491, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503442, by decide⟩,⟨503469, by decide⟩,⟨503490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72287_503491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72287 ⟨503491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72287
    ⟨503491, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503442, by decide⟩,⟨503469, by decide⟩,⟨503490, by decide⟩]) unmarked_context_12_72287_503491 node_context_12_72287_503491
  intro a
  fin_cases a
  · exact context_13_289148_3444
  · exact context_13_289149_503442
  · exact context_13_289150_503469
  · exact context_13_289151_503490

theorem unmarked_context_11_18071_503492 : frontier 10 ⟨503492, by decide⟩
    (prefixCache 11 18071) (prefixPartial 11 18071) = false := by
  decide +kernel

theorem node_context_11_18071_503492 : EJMOriginalGlobalDAGData.nodes 10 ⟨503492, by decide⟩ =
    .split (coordinate 11) (![⟨503280, by decide⟩,⟨503343, by decide⟩,⟨503418, by decide⟩,⟨503491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18071_503492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18071 ⟨503492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18071
    ⟨503492, by decide⟩ (by decide) (![⟨503280, by decide⟩,⟨503343, by decide⟩,⟨503418, by decide⟩,⟨503491, by decide⟩]) unmarked_context_11_18071_503492 node_context_11_18071_503492
  intro a
  fin_cases a
  · exact context_12_72284_503280
  · exact context_12_72285_503343
  · exact context_12_72286_503418
  · exact context_12_72287_503491

theorem unmarked_context_10_4517_503493 : frontier 11 ⟨503493, by decide⟩
    (prefixCache 10 4517) (prefixPartial 10 4517) = false := by
  decide +kernel

theorem node_context_10_4517_503493 : EJMOriginalGlobalDAGData.nodes 11 ⟨503493, by decide⟩ =
    .split (coordinate 10) (![⟨502681, by decide⟩,⟨502927, by decide⟩,⟨503220, by decide⟩,⟨503492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4517_503493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4517 ⟨503493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4517
    ⟨503493, by decide⟩ (by decide) (![⟨502681, by decide⟩,⟨502927, by decide⟩,⟨503220, by decide⟩,⟨503492, by decide⟩]) unmarked_context_10_4517_503493 node_context_10_4517_503493
  intro a
  fin_cases a
  · exact context_11_18068_502681
  · exact context_11_18069_502927
  · exact context_11_18070_503220
  · exact context_11_18071_503492

theorem selected_cut_19698 : selected 9 ⟨503547, by decide⟩
    (prefixPartial 12 72288) = some ⟨12, 2, 0, 503547, 72288, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_72288_503547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72288 ⟨503547, by decide⟩ :=
  accepted_of_selected 12 72288 ⟨503547, by decide⟩ ⟨12, 2, 0, 503547, 72288, 3737, 65536⟩
    (by decide) selected_cut_19698

theorem selected_cut_19699 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289156) = some ⟨13, 1, 0, 3444, 289156, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289156_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289156 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289156 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289156, 1, 16384⟩
    (by decide) selected_cut_19699

theorem selected_cut_19700 : selected 8 ⟨503568, by decide⟩
    (prefixPartial 13 289157) = some ⟨13, 2, 0, 503568, 289157, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_289157_503568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289157 ⟨503568, by decide⟩ :=
  accepted_of_selected 13 289157 ⟨503568, by decide⟩ ⟨13, 2, 0, 503568, 289157, 1521, 16384⟩
    (by decide) selected_cut_19700

theorem selected_cut_19701 : selected 8 ⟨503585, by decide⟩
    (prefixPartial 13 289158) = some ⟨13, 2, 0, 503585, 289158, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_289158_503585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289158 ⟨503585, by decide⟩ :=
  accepted_of_selected 13 289158 ⟨503585, by decide⟩ ⟨13, 2, 0, 503585, 289158, 1541, 16384⟩
    (by decide) selected_cut_19701

theorem selected_cut_19702 : selected 8 ⟨503598, by decide⟩
    (prefixPartial 13 289159) = some ⟨13, 2, 0, 503598, 289159, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_289159_503598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289159 ⟨503598, by decide⟩ :=
  accepted_of_selected 13 289159 ⟨503598, by decide⟩ ⟨13, 2, 0, 503598, 289159, 1065, 16384⟩
    (by decide) selected_cut_19702

theorem unmarked_context_12_72289_503599 : frontier 9 ⟨503599, by decide⟩
    (prefixCache 12 72289) (prefixPartial 12 72289) = false := by
  decide +kernel

theorem node_context_12_72289_503599 : EJMOriginalGlobalDAGData.nodes 9 ⟨503599, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503568, by decide⟩,⟨503585, by decide⟩,⟨503598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72289_503599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72289 ⟨503599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72289
    ⟨503599, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503568, by decide⟩,⟨503585, by decide⟩,⟨503598, by decide⟩]) unmarked_context_12_72289_503599 node_context_12_72289_503599
  intro a
  fin_cases a
  · exact context_13_289156_3444
  · exact context_13_289157_503568
  · exact context_13_289158_503585
  · exact context_13_289159_503598

theorem selected_cut_19703 : selected 9 ⟨503639, by decide⟩
    (prefixPartial 12 72290) = some ⟨12, 2, 0, 503639, 72290, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_72290_503639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72290 ⟨503639, by decide⟩ :=
  accepted_of_selected 12 72290 ⟨503639, by decide⟩ ⟨12, 2, 0, 503639, 72290, 3685, 65536⟩
    (by decide) selected_cut_19703

theorem selected_cut_19704 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289164) = some ⟨13, 1, 0, 3444, 289164, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289164_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289164 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289164 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289164, 1, 16384⟩
    (by decide) selected_cut_19704

theorem selected_cut_19705 : selected 8 ⟨503662, by decide⟩
    (prefixPartial 13 289165) = some ⟨13, 2, 0, 503662, 289165, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_289165_503662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289165 ⟨503662, by decide⟩ :=
  accepted_of_selected 13 289165 ⟨503662, by decide⟩ ⟨13, 2, 0, 503662, 289165, 1589, 16384⟩
    (by decide) selected_cut_19705

theorem selected_cut_19706 : selected 8 ⟨503688, by decide⟩
    (prefixPartial 13 289166) = some ⟨13, 2, 0, 503688, 289166, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_289166_503688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289166 ⟨503688, by decide⟩ :=
  accepted_of_selected 13 289166 ⟨503688, by decide⟩ ⟨13, 2, 0, 503688, 289166, 2009, 16384⟩
    (by decide) selected_cut_19706

theorem selected_cut_19707 : selected 8 ⟨503700, by decide⟩
    (prefixPartial 13 289167) = some ⟨13, 2, 0, 503700, 289167, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_289167_503700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289167 ⟨503700, by decide⟩ :=
  accepted_of_selected 13 289167 ⟨503700, by decide⟩ ⟨13, 2, 0, 503700, 289167, 1001, 16384⟩
    (by decide) selected_cut_19707

theorem unmarked_context_12_72291_503701 : frontier 9 ⟨503701, by decide⟩
    (prefixCache 12 72291) (prefixPartial 12 72291) = false := by
  decide +kernel

theorem node_context_12_72291_503701 : EJMOriginalGlobalDAGData.nodes 9 ⟨503701, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503662, by decide⟩,⟨503688, by decide⟩,⟨503700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72291_503701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72291 ⟨503701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72291
    ⟨503701, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503662, by decide⟩,⟨503688, by decide⟩,⟨503700, by decide⟩]) unmarked_context_12_72291_503701 node_context_12_72291_503701
  intro a
  fin_cases a
  · exact context_13_289164_3444
  · exact context_13_289165_503662
  · exact context_13_289166_503688
  · exact context_13_289167_503700

theorem unmarked_context_11_18072_503702 : frontier 10 ⟨503702, by decide⟩
    (prefixCache 11 18072) (prefixPartial 11 18072) = false := by
  decide +kernel

theorem node_context_11_18072_503702 : EJMOriginalGlobalDAGData.nodes 10 ⟨503702, by decide⟩ =
    .split (coordinate 11) (![⟨503547, by decide⟩,⟨503599, by decide⟩,⟨503639, by decide⟩,⟨503701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18072_503702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18072 ⟨503702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18072
    ⟨503702, by decide⟩ (by decide) (![⟨503547, by decide⟩,⟨503599, by decide⟩,⟨503639, by decide⟩,⟨503701, by decide⟩]) unmarked_context_11_18072_503702 node_context_11_18072_503702
  intro a
  fin_cases a
  · exact context_12_72288_503547
  · exact context_12_72289_503599
  · exact context_12_72290_503639
  · exact context_12_72291_503701

theorem selected_cut_19708 : selected 9 ⟨503759, by decide⟩
    (prefixPartial 12 72292) = some ⟨12, 2, 0, 503759, 72292, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_72292_503759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72292 ⟨503759, by decide⟩ :=
  accepted_of_selected 12 72292 ⟨503759, by decide⟩ ⟨12, 2, 0, 503759, 72292, 4081, 65536⟩
    (by decide) selected_cut_19708

theorem selected_cut_19709 : selected 9 ⟨503805, by decide⟩
    (prefixPartial 12 72293) = some ⟨12, 2, 0, 503805, 72293, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_72293_503805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72293 ⟨503805, by decide⟩ :=
  accepted_of_selected 12 72293 ⟨503805, by decide⟩ ⟨12, 2, 0, 503805, 72293, 3689, 65536⟩
    (by decide) selected_cut_19709

theorem selected_cut_19710 : selected 9 ⟨503848, by decide⟩
    (prefixPartial 12 72294) = some ⟨12, 2, 0, 503848, 72294, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_72294_503848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72294 ⟨503848, by decide⟩ :=
  accepted_of_selected 12 72294 ⟨503848, by decide⟩ ⟨12, 2, 0, 503848, 72294, 3721, 65536⟩
    (by decide) selected_cut_19710

theorem selected_cut_19711 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289180) = some ⟨13, 1, 0, 3444, 289180, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289180_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289180 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289180 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289180, 1, 16384⟩
    (by decide) selected_cut_19711

theorem selected_cut_19712 : selected 8 ⟨503865, by decide⟩
    (prefixPartial 13 289181) = some ⟨13, 2, 0, 503865, 289181, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_289181_503865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289181 ⟨503865, by decide⟩ :=
  accepted_of_selected 13 289181 ⟨503865, by decide⟩ ⟨13, 2, 0, 503865, 289181, 1273, 16384⟩
    (by decide) selected_cut_19712

theorem selected_cut_19713 : selected 8 ⟨503896, by decide⟩
    (prefixPartial 13 289182) = some ⟨13, 2, 0, 503896, 289182, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_289182_503896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289182 ⟨503896, by decide⟩ :=
  accepted_of_selected 13 289182 ⟨503896, by decide⟩ ⟨13, 2, 0, 503896, 289182, 2085, 16384⟩
    (by decide) selected_cut_19713

theorem selected_cut_19714 : selected 8 ⟨503902, by decide⟩
    (prefixPartial 13 289183) = some ⟨13, 2, 0, 503902, 289183, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_289183_503902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289183 ⟨503902, by decide⟩ :=
  accepted_of_selected 13 289183 ⟨503902, by decide⟩ ⟨13, 2, 0, 503902, 289183, 1069, 16384⟩
    (by decide) selected_cut_19714

theorem unmarked_context_12_72295_503903 : frontier 9 ⟨503903, by decide⟩
    (prefixCache 12 72295) (prefixPartial 12 72295) = false := by
  decide +kernel

theorem node_context_12_72295_503903 : EJMOriginalGlobalDAGData.nodes 9 ⟨503903, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503865, by decide⟩,⟨503896, by decide⟩,⟨503902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72295_503903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72295 ⟨503903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72295
    ⟨503903, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503865, by decide⟩,⟨503896, by decide⟩,⟨503902, by decide⟩]) unmarked_context_12_72295_503903 node_context_12_72295_503903
  intro a
  fin_cases a
  · exact context_13_289180_3444
  · exact context_13_289181_503865
  · exact context_13_289182_503896
  · exact context_13_289183_503902

theorem unmarked_context_11_18073_503904 : frontier 10 ⟨503904, by decide⟩
    (prefixCache 11 18073) (prefixPartial 11 18073) = false := by
  decide +kernel

theorem node_context_11_18073_503904 : EJMOriginalGlobalDAGData.nodes 10 ⟨503904, by decide⟩ =
    .split (coordinate 11) (![⟨503759, by decide⟩,⟨503805, by decide⟩,⟨503848, by decide⟩,⟨503903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18073_503904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18073 ⟨503904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18073
    ⟨503904, by decide⟩ (by decide) (![⟨503759, by decide⟩,⟨503805, by decide⟩,⟨503848, by decide⟩,⟨503903, by decide⟩]) unmarked_context_11_18073_503904 node_context_11_18073_503904
  intro a
  fin_cases a
  · exact context_12_72292_503759
  · exact context_12_72293_503805
  · exact context_12_72294_503848
  · exact context_12_72295_503903

theorem selected_cut_19715 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289184) = some ⟨13, 1, 0, 3444, 289184, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289184_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289184 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289184 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289184, 1, 16384⟩
    (by decide) selected_cut_19715

theorem selected_cut_19716 : selected 8 ⟨503928, by decide⟩
    (prefixPartial 13 289185) = some ⟨13, 2, 0, 503928, 289185, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_289185_503928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289185 ⟨503928, by decide⟩ :=
  accepted_of_selected 13 289185 ⟨503928, by decide⟩ ⟨13, 2, 0, 503928, 289185, 1273, 16384⟩
    (by decide) selected_cut_19716

theorem selected_cut_19717 : selected 8 ⟨503985, by decide⟩
    (prefixPartial 13 289186) = some ⟨13, 2, 0, 503985, 289186, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_289186_503985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289186 ⟨503985, by decide⟩ :=
  accepted_of_selected 13 289186 ⟨503985, by decide⟩ ⟨13, 2, 0, 503985, 289186, 2297, 16384⟩
    (by decide) selected_cut_19717

theorem selected_cut_19718 : selected 8 ⟨504010, by decide⟩
    (prefixPartial 13 289187) = some ⟨13, 2, 0, 504010, 289187, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_289187_504010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289187 ⟨504010, by decide⟩ :=
  accepted_of_selected 13 289187 ⟨504010, by decide⟩ ⟨13, 2, 0, 504010, 289187, 1225, 16384⟩
    (by decide) selected_cut_19718

theorem unmarked_context_12_72296_504011 : frontier 9 ⟨504011, by decide⟩
    (prefixCache 12 72296) (prefixPartial 12 72296) = false := by
  decide +kernel

theorem node_context_12_72296_504011 : EJMOriginalGlobalDAGData.nodes 9 ⟨504011, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨503928, by decide⟩,⟨503985, by decide⟩,⟨504010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72296_504011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72296 ⟨504011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72296
    ⟨504011, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨503928, by decide⟩,⟨503985, by decide⟩,⟨504010, by decide⟩]) unmarked_context_12_72296_504011 node_context_12_72296_504011
  intro a
  fin_cases a
  · exact context_13_289184_3444
  · exact context_13_289185_503928
  · exact context_13_289186_503985
  · exact context_13_289187_504010

theorem selected_cut_19719 : selected 9 ⟨504068, by decide⟩
    (prefixPartial 12 72297) = some ⟨12, 2, 0, 504068, 72297, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_72297_504068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72297 ⟨504068, by decide⟩ :=
  accepted_of_selected 12 72297 ⟨504068, by decide⟩ ⟨12, 2, 0, 504068, 72297, 1857, 65536⟩
    (by decide) selected_cut_19719

theorem selected_cut_19720 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 72298) = some ⟨12, 1, 0, 474208, 72298, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72298_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72298 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 72298 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 72298, 1, 65536⟩
    (by decide) selected_cut_19720

theorem selected_cut_19721 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289196) = some ⟨13, 1, 0, 3444, 289196, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289196_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289196 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289196 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289196, 1, 16384⟩
    (by decide) selected_cut_19721

theorem selected_cut_19722 : selected 8 ⟨504089, by decide⟩
    (prefixPartial 13 289197) = some ⟨13, 2, 0, 504089, 289197, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_289197_504089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289197 ⟨504089, by decide⟩ :=
  accepted_of_selected 13 289197 ⟨504089, by decide⟩ ⟨13, 2, 0, 504089, 289197, 1337, 16384⟩
    (by decide) selected_cut_19722

theorem selected_cut_19723 : selected 8 ⟨504136, by decide⟩
    (prefixPartial 13 289198) = some ⟨13, 2, 0, 504136, 289198, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_289198_504136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289198 ⟨504136, by decide⟩ :=
  accepted_of_selected 13 289198 ⟨504136, by decide⟩ ⟨13, 2, 0, 504136, 289198, 2441, 16384⟩
    (by decide) selected_cut_19723

theorem selected_cut_19724 : selected 8 ⟨504154, by decide⟩
    (prefixPartial 13 289199) = some ⟨13, 2, 0, 504154, 289199, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_289199_504154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289199 ⟨504154, by decide⟩ :=
  accepted_of_selected 13 289199 ⟨504154, by decide⟩ ⟨13, 2, 0, 504154, 289199, 1201, 16384⟩
    (by decide) selected_cut_19724

theorem unmarked_context_12_72299_504155 : frontier 9 ⟨504155, by decide⟩
    (prefixCache 12 72299) (prefixPartial 12 72299) = false := by
  decide +kernel

theorem node_context_12_72299_504155 : EJMOriginalGlobalDAGData.nodes 9 ⟨504155, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨504089, by decide⟩,⟨504136, by decide⟩,⟨504154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72299_504155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72299 ⟨504155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72299
    ⟨504155, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨504089, by decide⟩,⟨504136, by decide⟩,⟨504154, by decide⟩]) unmarked_context_12_72299_504155 node_context_12_72299_504155
  intro a
  fin_cases a
  · exact context_13_289196_3444
  · exact context_13_289197_504089
  · exact context_13_289198_504136
  · exact context_13_289199_504154

theorem unmarked_context_11_18074_504156 : frontier 10 ⟨504156, by decide⟩
    (prefixCache 11 18074) (prefixPartial 11 18074) = false := by
  decide +kernel

theorem node_context_11_18074_504156 : EJMOriginalGlobalDAGData.nodes 10 ⟨504156, by decide⟩ =
    .split (coordinate 11) (![⟨504011, by decide⟩,⟨504068, by decide⟩,⟨474208, by decide⟩,⟨504155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18074_504156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18074 ⟨504156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18074
    ⟨504156, by decide⟩ (by decide) (![⟨504011, by decide⟩,⟨504068, by decide⟩,⟨474208, by decide⟩,⟨504155, by decide⟩]) unmarked_context_11_18074_504156 node_context_11_18074_504156
  intro a
  fin_cases a
  · exact context_12_72296_504011
  · exact context_12_72297_504068
  · exact context_12_72298_474208
  · exact context_12_72299_504155

theorem selected_cut_19725 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289200) = some ⟨13, 1, 0, 3444, 289200, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289200_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289200 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289200 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289200, 1, 16384⟩
    (by decide) selected_cut_19725

theorem selected_cut_19726 : selected 8 ⟨504170, by decide⟩
    (prefixPartial 13 289201) = some ⟨13, 2, 0, 504170, 289201, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_289201_504170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289201 ⟨504170, by decide⟩ :=
  accepted_of_selected 13 289201 ⟨504170, by decide⟩ ⟨13, 2, 0, 504170, 289201, 1021, 16384⟩
    (by decide) selected_cut_19726

theorem selected_cut_19727 : selected 8 ⟨504209, by decide⟩
    (prefixPartial 13 289202) = some ⟨13, 2, 0, 504209, 289202, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_289202_504209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289202 ⟨504209, by decide⟩ :=
  accepted_of_selected 13 289202 ⟨504209, by decide⟩ ⟨13, 2, 0, 504209, 289202, 2021, 16384⟩
    (by decide) selected_cut_19727

theorem selected_cut_19728 : selected 8 ⟨504225, by decide⟩
    (prefixPartial 13 289203) = some ⟨13, 2, 0, 504225, 289203, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_289203_504225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289203 ⟨504225, by decide⟩ :=
  accepted_of_selected 13 289203 ⟨504225, by decide⟩ ⟨13, 2, 0, 504225, 289203, 1129, 16384⟩
    (by decide) selected_cut_19728

theorem unmarked_context_12_72300_504226 : frontier 9 ⟨504226, by decide⟩
    (prefixCache 12 72300) (prefixPartial 12 72300) = false := by
  decide +kernel

theorem node_context_12_72300_504226 : EJMOriginalGlobalDAGData.nodes 9 ⟨504226, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨504170, by decide⟩,⟨504209, by decide⟩,⟨504225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72300_504226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72300 ⟨504226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72300
    ⟨504226, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨504170, by decide⟩,⟨504209, by decide⟩,⟨504225, by decide⟩]) unmarked_context_12_72300_504226 node_context_12_72300_504226
  intro a
  fin_cases a
  · exact context_13_289200_3444
  · exact context_13_289201_504170
  · exact context_13_289202_504209
  · exact context_13_289203_504225

theorem selected_cut_19729 : selected 9 ⟨504287, by decide⟩
    (prefixPartial 12 72301) = some ⟨12, 2, 0, 504287, 72301, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_72301_504287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72301 ⟨504287, by decide⟩ :=
  accepted_of_selected 12 72301 ⟨504287, by decide⟩ ⟨12, 2, 0, 504287, 72301, 3913, 65536⟩
    (by decide) selected_cut_19729

theorem selected_cut_19730 : selected 9 ⟨504334, by decide⟩
    (prefixPartial 12 72302) = some ⟨12, 2, 0, 504334, 72302, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_72302_504334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72302 ⟨504334, by decide⟩ :=
  accepted_of_selected 12 72302 ⟨504334, by decide⟩ ⟨12, 2, 0, 504334, 72302, 3757, 65536⟩
    (by decide) selected_cut_19730

theorem selected_cut_19731 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289212) = some ⟨13, 1, 0, 3444, 289212, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289212_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289212 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289212 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289212, 1, 16384⟩
    (by decide) selected_cut_19731

theorem selected_cut_19732 : selected 8 ⟨504342, by decide⟩
    (prefixPartial 13 289213) = some ⟨13, 2, 0, 504342, 289213, 849, 16384⟩ := by
  decide +kernel

theorem context_13_289213_504342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289213 ⟨504342, by decide⟩ :=
  accepted_of_selected 13 289213 ⟨504342, by decide⟩ ⟨13, 2, 0, 504342, 289213, 849, 16384⟩
    (by decide) selected_cut_19732

theorem selected_cut_19733 : selected 8 ⟨504364, by decide⟩
    (prefixPartial 13 289214) = some ⟨13, 2, 0, 504364, 289214, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_289214_504364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289214 ⟨504364, by decide⟩ :=
  accepted_of_selected 13 289214 ⟨504364, by decide⟩ ⟨13, 2, 0, 504364, 289214, 2285, 16384⟩
    (by decide) selected_cut_19733

theorem selected_cut_19734 : selected 8 ⟨504377, by decide⟩
    (prefixPartial 13 289215) = some ⟨13, 2, 0, 504377, 289215, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_289215_504377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289215 ⟨504377, by decide⟩ :=
  accepted_of_selected 13 289215 ⟨504377, by decide⟩ ⟨13, 2, 0, 504377, 289215, 1117, 16384⟩
    (by decide) selected_cut_19734

theorem unmarked_context_12_72303_504378 : frontier 9 ⟨504378, by decide⟩
    (prefixCache 12 72303) (prefixPartial 12 72303) = false := by
  decide +kernel

theorem node_context_12_72303_504378 : EJMOriginalGlobalDAGData.nodes 9 ⟨504378, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨504342, by decide⟩,⟨504364, by decide⟩,⟨504377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72303_504378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72303 ⟨504378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72303
    ⟨504378, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨504342, by decide⟩,⟨504364, by decide⟩,⟨504377, by decide⟩]) unmarked_context_12_72303_504378 node_context_12_72303_504378
  intro a
  fin_cases a
  · exact context_13_289212_3444
  · exact context_13_289213_504342
  · exact context_13_289214_504364
  · exact context_13_289215_504377

theorem unmarked_context_11_18075_504379 : frontier 10 ⟨504379, by decide⟩
    (prefixCache 11 18075) (prefixPartial 11 18075) = false := by
  decide +kernel

theorem node_context_11_18075_504379 : EJMOriginalGlobalDAGData.nodes 10 ⟨504379, by decide⟩ =
    .split (coordinate 11) (![⟨504226, by decide⟩,⟨504287, by decide⟩,⟨504334, by decide⟩,⟨504378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18075_504379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18075 ⟨504379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18075
    ⟨504379, by decide⟩ (by decide) (![⟨504226, by decide⟩,⟨504287, by decide⟩,⟨504334, by decide⟩,⟨504378, by decide⟩]) unmarked_context_11_18075_504379 node_context_11_18075_504379
  intro a
  fin_cases a
  · exact context_12_72300_504226
  · exact context_12_72301_504287
  · exact context_12_72302_504334
  · exact context_12_72303_504378

theorem unmarked_context_10_4518_504380 : frontier 11 ⟨504380, by decide⟩
    (prefixCache 10 4518) (prefixPartial 10 4518) = false := by
  decide +kernel

theorem node_context_10_4518_504380 : EJMOriginalGlobalDAGData.nodes 11 ⟨504380, by decide⟩ =
    .split (coordinate 10) (![⟨503702, by decide⟩,⟨503904, by decide⟩,⟨504156, by decide⟩,⟨504379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4518_504380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4518 ⟨504380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4518
    ⟨504380, by decide⟩ (by decide) (![⟨503702, by decide⟩,⟨503904, by decide⟩,⟨504156, by decide⟩,⟨504379, by decide⟩]) unmarked_context_10_4518_504380 node_context_10_4518_504380
  intro a
  fin_cases a
  · exact context_11_18072_503702
  · exact context_11_18073_503904
  · exact context_11_18074_504156
  · exact context_11_18075_504379

theorem selected_cut_19735 : selected 9 ⟨504428, by decide⟩
    (prefixPartial 12 72304) = some ⟨12, 2, 0, 504428, 72304, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_72304_504428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72304 ⟨504428, by decide⟩ :=
  accepted_of_selected 12 72304 ⟨504428, by decide⟩ ⟨12, 2, 0, 504428, 72304, 2821, 65536⟩
    (by decide) selected_cut_19735

theorem selected_cut_19736 : selected 9 ⟨504484, by decide⟩
    (prefixPartial 12 72305) = some ⟨12, 2, 0, 504484, 72305, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_72305_504484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72305 ⟨504484, by decide⟩ :=
  accepted_of_selected 12 72305 ⟨504484, by decide⟩ ⟨12, 2, 0, 504484, 72305, 3185, 65536⟩
    (by decide) selected_cut_19736

theorem selected_cut_19737 : selected 9 ⟨504526, by decide⟩
    (prefixPartial 12 72306) = some ⟨12, 2, 0, 504526, 72306, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_72306_504526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72306 ⟨504526, by decide⟩ :=
  accepted_of_selected 12 72306 ⟨504526, by decide⟩ ⟨12, 2, 0, 504526, 72306, 3261, 65536⟩
    (by decide) selected_cut_19737

theorem selected_cut_19738 : selected 9 ⟨504572, by decide⟩
    (prefixPartial 12 72307) = some ⟨12, 2, 0, 504572, 72307, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_72307_504572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72307 ⟨504572, by decide⟩ :=
  accepted_of_selected 12 72307 ⟨504572, by decide⟩ ⟨12, 2, 0, 504572, 72307, 3569, 65536⟩
    (by decide) selected_cut_19738

theorem unmarked_context_11_18076_504573 : frontier 10 ⟨504573, by decide⟩
    (prefixCache 11 18076) (prefixPartial 11 18076) = false := by
  decide +kernel

theorem node_context_11_18076_504573 : EJMOriginalGlobalDAGData.nodes 10 ⟨504573, by decide⟩ =
    .split (coordinate 11) (![⟨504428, by decide⟩,⟨504484, by decide⟩,⟨504526, by decide⟩,⟨504572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18076_504573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18076 ⟨504573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18076
    ⟨504573, by decide⟩ (by decide) (![⟨504428, by decide⟩,⟨504484, by decide⟩,⟨504526, by decide⟩,⟨504572, by decide⟩]) unmarked_context_11_18076_504573 node_context_11_18076_504573
  intro a
  fin_cases a
  · exact context_12_72304_504428
  · exact context_12_72305_504484
  · exact context_12_72306_504526
  · exact context_12_72307_504572

theorem selected_cut_19739 : selected 9 ⟨504614, by decide⟩
    (prefixPartial 12 72308) = some ⟨12, 2, 0, 504614, 72308, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_72308_504614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72308 ⟨504614, by decide⟩ :=
  accepted_of_selected 12 72308 ⟨504614, by decide⟩ ⟨12, 2, 0, 504614, 72308, 3389, 65536⟩
    (by decide) selected_cut_19739

theorem selected_cut_19740 : selected 9 ⟨504660, by decide⟩
    (prefixPartial 12 72309) = some ⟨12, 2, 0, 504660, 72309, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_72309_504660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72309 ⟨504660, by decide⟩ :=
  accepted_of_selected 12 72309 ⟨504660, by decide⟩ ⟨12, 2, 0, 504660, 72309, 3081, 65536⟩
    (by decide) selected_cut_19740

theorem selected_cut_19741 : selected 9 ⟨504702, by decide⟩
    (prefixPartial 12 72310) = some ⟨12, 2, 0, 504702, 72310, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_72310_504702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72310 ⟨504702, by decide⟩ :=
  accepted_of_selected 12 72310 ⟨504702, by decide⟩ ⟨12, 2, 0, 504702, 72310, 3529, 65536⟩
    (by decide) selected_cut_19741

theorem selected_cut_19742 : selected 9 ⟨504759, by decide⟩
    (prefixPartial 12 72311) = some ⟨12, 2, 0, 504759, 72311, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_72311_504759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72311 ⟨504759, by decide⟩ :=
  accepted_of_selected 12 72311 ⟨504759, by decide⟩ ⟨12, 2, 0, 504759, 72311, 3781, 65536⟩
    (by decide) selected_cut_19742

theorem unmarked_context_11_18077_504760 : frontier 10 ⟨504760, by decide⟩
    (prefixCache 11 18077) (prefixPartial 11 18077) = false := by
  decide +kernel

theorem node_context_11_18077_504760 : EJMOriginalGlobalDAGData.nodes 10 ⟨504760, by decide⟩ =
    .split (coordinate 11) (![⟨504614, by decide⟩,⟨504660, by decide⟩,⟨504702, by decide⟩,⟨504759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18077_504760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18077 ⟨504760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18077
    ⟨504760, by decide⟩ (by decide) (![⟨504614, by decide⟩,⟨504660, by decide⟩,⟨504702, by decide⟩,⟨504759, by decide⟩]) unmarked_context_11_18077_504760 node_context_11_18077_504760
  intro a
  fin_cases a
  · exact context_12_72308_504614
  · exact context_12_72309_504660
  · exact context_12_72310_504702
  · exact context_12_72311_504759

theorem selected_cut_19743 : selected 9 ⟨504805, by decide⟩
    (prefixPartial 12 72312) = some ⟨12, 2, 0, 504805, 72312, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_72312_504805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72312 ⟨504805, by decide⟩ :=
  accepted_of_selected 12 72312 ⟨504805, by decide⟩ ⟨12, 2, 0, 504805, 72312, 3073, 65536⟩
    (by decide) selected_cut_19743

theorem selected_cut_19744 : selected 9 ⟨504858, by decide⟩
    (prefixPartial 12 72313) = some ⟨12, 2, 0, 504858, 72313, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_72313_504858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72313 ⟨504858, by decide⟩ :=
  accepted_of_selected 12 72313 ⟨504858, by decide⟩ ⟨12, 2, 0, 504858, 72313, 2913, 65536⟩
    (by decide) selected_cut_19744

theorem selected_cut_19745 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 289256) = some ⟨13, 1, 0, 3444, 289256, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289256_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289256 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 289256 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 289256, 1, 16384⟩
    (by decide) selected_cut_19745

theorem selected_cut_19746 : selected 8 ⟨504868, by decide⟩
    (prefixPartial 13 289257) = some ⟨13, 2, 0, 504868, 289257, 449, 16384⟩ := by
  decide +kernel

theorem context_13_289257_504868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289257 ⟨504868, by decide⟩ :=
  accepted_of_selected 13 289257 ⟨504868, by decide⟩ ⟨13, 2, 0, 504868, 289257, 449, 16384⟩
    (by decide) selected_cut_19746

theorem selected_cut_19747 : selected 8 ⟨504956, by decide⟩
    (prefixPartial 13 289258) = some ⟨13, 2, 0, 504956, 289258, 2825, 16384⟩ := by
  decide +kernel

theorem context_13_289258_504956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289258 ⟨504956, by decide⟩ :=
  accepted_of_selected 13 289258 ⟨504956, by decide⟩ ⟨13, 2, 0, 504956, 289258, 2825, 16384⟩
    (by decide) selected_cut_19747

theorem selected_cut_19748 : selected 8 ⟨504994, by decide⟩
    (prefixPartial 13 289259) = some ⟨13, 2, 0, 504994, 289259, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_289259_504994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289259 ⟨504994, by decide⟩ :=
  accepted_of_selected 13 289259 ⟨504994, by decide⟩ ⟨13, 2, 0, 504994, 289259, 1413, 16384⟩
    (by decide) selected_cut_19748

theorem unmarked_context_12_72314_504995 : frontier 9 ⟨504995, by decide⟩
    (prefixCache 12 72314) (prefixPartial 12 72314) = false := by
  decide +kernel

theorem node_context_12_72314_504995 : EJMOriginalGlobalDAGData.nodes 9 ⟨504995, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨504868, by decide⟩,⟨504956, by decide⟩,⟨504994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72314_504995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72314 ⟨504995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72314
    ⟨504995, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨504868, by decide⟩,⟨504956, by decide⟩,⟨504994, by decide⟩]) unmarked_context_12_72314_504995 node_context_12_72314_504995
  intro a
  fin_cases a
  · exact context_13_289256_3444
  · exact context_13_289257_504868
  · exact context_13_289258_504956
  · exact context_13_289259_504994

theorem selected_cut_19749 : selected 9 ⟨505029, by decide⟩
    (prefixPartial 12 72315) = some ⟨12, 2, 0, 505029, 72315, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_72315_505029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72315 ⟨505029, by decide⟩ :=
  accepted_of_selected 12 72315 ⟨505029, by decide⟩ ⟨12, 2, 0, 505029, 72315, 3221, 65536⟩
    (by decide) selected_cut_19749

theorem unmarked_context_11_18078_505030 : frontier 10 ⟨505030, by decide⟩
    (prefixCache 11 18078) (prefixPartial 11 18078) = false := by
  decide +kernel

theorem node_context_11_18078_505030 : EJMOriginalGlobalDAGData.nodes 10 ⟨505030, by decide⟩ =
    .split (coordinate 11) (![⟨504805, by decide⟩,⟨504858, by decide⟩,⟨504995, by decide⟩,⟨505029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18078_505030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18078 ⟨505030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18078
    ⟨505030, by decide⟩ (by decide) (![⟨504805, by decide⟩,⟨504858, by decide⟩,⟨504995, by decide⟩,⟨505029, by decide⟩]) unmarked_context_11_18078_505030 node_context_11_18078_505030
  intro a
  fin_cases a
  · exact context_12_72312_504805
  · exact context_12_72313_504858
  · exact context_12_72314_504995
  · exact context_12_72315_505029

theorem selected_cut_19750 : selected 9 ⟨505065, by decide⟩
    (prefixPartial 12 72316) = some ⟨12, 2, 0, 505065, 72316, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_72316_505065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72316 ⟨505065, by decide⟩ :=
  accepted_of_selected 12 72316 ⟨505065, by decide⟩ ⟨12, 2, 0, 505065, 72316, 3105, 65536⟩
    (by decide) selected_cut_19750

theorem selected_cut_19751 : selected 9 ⟨505127, by decide⟩
    (prefixPartial 12 72317) = some ⟨12, 2, 0, 505127, 72317, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_72317_505127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72317 ⟨505127, by decide⟩ :=
  accepted_of_selected 12 72317 ⟨505127, by decide⟩ ⟨12, 2, 0, 505127, 72317, 2893, 65536⟩
    (by decide) selected_cut_19751

theorem selected_cut_19752 : selected 9 ⟨505168, by decide⟩
    (prefixPartial 12 72318) = some ⟨12, 2, 0, 505168, 72318, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_72318_505168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72318 ⟨505168, by decide⟩ :=
  accepted_of_selected 12 72318 ⟨505168, by decide⟩ ⟨12, 2, 0, 505168, 72318, 3101, 65536⟩
    (by decide) selected_cut_19752

theorem selected_cut_19753 : selected 9 ⟨505210, by decide⟩
    (prefixPartial 12 72319) = some ⟨12, 2, 0, 505210, 72319, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_72319_505210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72319 ⟨505210, by decide⟩ :=
  accepted_of_selected 12 72319 ⟨505210, by decide⟩ ⟨12, 2, 0, 505210, 72319, 3265, 65536⟩
    (by decide) selected_cut_19753

theorem unmarked_context_11_18079_505211 : frontier 10 ⟨505211, by decide⟩
    (prefixCache 11 18079) (prefixPartial 11 18079) = false := by
  decide +kernel

theorem node_context_11_18079_505211 : EJMOriginalGlobalDAGData.nodes 10 ⟨505211, by decide⟩ =
    .split (coordinate 11) (![⟨505065, by decide⟩,⟨505127, by decide⟩,⟨505168, by decide⟩,⟨505210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18079_505211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18079 ⟨505211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18079
    ⟨505211, by decide⟩ (by decide) (![⟨505065, by decide⟩,⟨505127, by decide⟩,⟨505168, by decide⟩,⟨505210, by decide⟩]) unmarked_context_11_18079_505211 node_context_11_18079_505211
  intro a
  fin_cases a
  · exact context_12_72316_505065
  · exact context_12_72317_505127
  · exact context_12_72318_505168
  · exact context_12_72319_505210

theorem unmarked_context_10_4519_505212 : frontier 11 ⟨505212, by decide⟩
    (prefixCache 10 4519) (prefixPartial 10 4519) = false := by
  decide +kernel

theorem node_context_10_4519_505212 : EJMOriginalGlobalDAGData.nodes 11 ⟨505212, by decide⟩ =
    .split (coordinate 10) (![⟨504573, by decide⟩,⟨504760, by decide⟩,⟨505030, by decide⟩,⟨505211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4519_505212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4519 ⟨505212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4519
    ⟨505212, by decide⟩ (by decide) (![⟨504573, by decide⟩,⟨504760, by decide⟩,⟨505030, by decide⟩,⟨505211, by decide⟩]) unmarked_context_10_4519_505212 node_context_10_4519_505212
  intro a
  fin_cases a
  · exact context_11_18076_504573
  · exact context_11_18077_504760
  · exact context_11_18078_505030
  · exact context_11_18079_505211

theorem unmarked_context_9_1129_505213 : frontier 12 ⟨505213, by decide⟩
    (prefixCache 9 1129) (prefixPartial 9 1129) = false := by
  decide +kernel

theorem node_context_9_1129_505213 : EJMOriginalGlobalDAGData.nodes 12 ⟨505213, by decide⟩ =
    .split (coordinate 9) (![⟨502431, by decide⟩,⟨503493, by decide⟩,⟨504380, by decide⟩,⟨505212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1129_505213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1129 ⟨505213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1129
    ⟨505213, by decide⟩ (by decide) (![⟨502431, by decide⟩,⟨503493, by decide⟩,⟨504380, by decide⟩,⟨505212, by decide⟩]) unmarked_context_9_1129_505213 node_context_9_1129_505213
  intro a
  fin_cases a
  · exact context_10_4516_502431
  · exact context_10_4517_503493
  · exact context_10_4518_504380
  · exact context_10_4519_505212

theorem selected_cut_19754 : selected 9 ⟨505236, by decide⟩
    (prefixPartial 12 72320) = some ⟨12, 2, 0, 505236, 72320, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_72320_505236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72320 ⟨505236, by decide⟩ :=
  accepted_of_selected 12 72320 ⟨505236, by decide⟩ ⟨12, 2, 0, 505236, 72320, 1689, 65536⟩
    (by decide) selected_cut_19754

theorem selected_cut_19755 : selected 9 ⟨505268, by decide⟩
    (prefixPartial 12 72321) = some ⟨12, 2, 0, 505268, 72321, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_72321_505268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72321 ⟨505268, by decide⟩ :=
  accepted_of_selected 12 72321 ⟨505268, by decide⟩ ⟨12, 2, 0, 505268, 72321, 2165, 65536⟩
    (by decide) selected_cut_19755

theorem selected_cut_19756 : selected 9 ⟨505288, by decide⟩
    (prefixPartial 12 72322) = some ⟨12, 2, 0, 505288, 72322, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_72322_505288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72322 ⟨505288, by decide⟩ :=
  accepted_of_selected 12 72322 ⟨505288, by decide⟩ ⟨12, 2, 0, 505288, 72322, 1969, 65536⟩
    (by decide) selected_cut_19756

theorem selected_cut_19757 : selected 9 ⟨505310, by decide⟩
    (prefixPartial 12 72323) = some ⟨12, 2, 0, 505310, 72323, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_72323_505310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72323 ⟨505310, by decide⟩ :=
  accepted_of_selected 12 72323 ⟨505310, by decide⟩ ⟨12, 2, 0, 505310, 72323, 2025, 65536⟩
    (by decide) selected_cut_19757

theorem unmarked_context_11_18080_505311 : frontier 10 ⟨505311, by decide⟩
    (prefixCache 11 18080) (prefixPartial 11 18080) = false := by
  decide +kernel

theorem node_context_11_18080_505311 : EJMOriginalGlobalDAGData.nodes 10 ⟨505311, by decide⟩ =
    .split (coordinate 11) (![⟨505236, by decide⟩,⟨505268, by decide⟩,⟨505288, by decide⟩,⟨505310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18080_505311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18080 ⟨505311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18080
    ⟨505311, by decide⟩ (by decide) (![⟨505236, by decide⟩,⟨505268, by decide⟩,⟨505288, by decide⟩,⟨505310, by decide⟩]) unmarked_context_11_18080_505311 node_context_11_18080_505311
  intro a
  fin_cases a
  · exact context_12_72320_505236
  · exact context_12_72321_505268
  · exact context_12_72322_505288
  · exact context_12_72323_505310

theorem selected_cut_19758 : selected 9 ⟨505331, by decide⟩
    (prefixPartial 12 72324) = some ⟨12, 2, 0, 505331, 72324, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_72324_505331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72324 ⟨505331, by decide⟩ :=
  accepted_of_selected 12 72324 ⟨505331, by decide⟩ ⟨12, 2, 0, 505331, 72324, 1833, 65536⟩
    (by decide) selected_cut_19758

theorem selected_cut_19759 : selected 9 ⟨505354, by decide⟩
    (prefixPartial 12 72325) = some ⟨12, 2, 0, 505354, 72325, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_72325_505354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72325 ⟨505354, by decide⟩ :=
  accepted_of_selected 12 72325 ⟨505354, by decide⟩ ⟨12, 2, 0, 505354, 72325, 1989, 65536⟩
    (by decide) selected_cut_19759

theorem selected_cut_19760 : selected 9 ⟨505375, by decide⟩
    (prefixPartial 12 72326) = some ⟨12, 2, 0, 505375, 72326, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_72326_505375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72326 ⟨505375, by decide⟩ :=
  accepted_of_selected 12 72326 ⟨505375, by decide⟩ ⟨12, 2, 0, 505375, 72326, 2057, 65536⟩
    (by decide) selected_cut_19760

theorem selected_cut_19761 : selected 9 ⟨505400, by decide⟩
    (prefixPartial 12 72327) = some ⟨12, 2, 0, 505400, 72327, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_72327_505400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72327 ⟨505400, by decide⟩ :=
  accepted_of_selected 12 72327 ⟨505400, by decide⟩ ⟨12, 2, 0, 505400, 72327, 2077, 65536⟩
    (by decide) selected_cut_19761

theorem unmarked_context_11_18081_505401 : frontier 10 ⟨505401, by decide⟩
    (prefixCache 11 18081) (prefixPartial 11 18081) = false := by
  decide +kernel

theorem node_context_11_18081_505401 : EJMOriginalGlobalDAGData.nodes 10 ⟨505401, by decide⟩ =
    .split (coordinate 11) (![⟨505331, by decide⟩,⟨505354, by decide⟩,⟨505375, by decide⟩,⟨505400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18081_505401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18081 ⟨505401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18081
    ⟨505401, by decide⟩ (by decide) (![⟨505331, by decide⟩,⟨505354, by decide⟩,⟨505375, by decide⟩,⟨505400, by decide⟩]) unmarked_context_11_18081_505401 node_context_11_18081_505401
  intro a
  fin_cases a
  · exact context_12_72324_505331
  · exact context_12_72325_505354
  · exact context_12_72326_505375
  · exact context_12_72327_505400

theorem selected_cut_19762 : selected 9 ⟨505419, by decide⟩
    (prefixPartial 12 72328) = some ⟨12, 2, 0, 505419, 72328, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_72328_505419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72328 ⟨505419, by decide⟩ :=
  accepted_of_selected 12 72328 ⟨505419, by decide⟩ ⟨12, 2, 0, 505419, 72328, 1425, 65536⟩
    (by decide) selected_cut_19762

theorem selected_cut_19763 : selected 9 ⟨505438, by decide⟩
    (prefixPartial 12 72329) = some ⟨12, 2, 0, 505438, 72329, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_72329_505438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72329 ⟨505438, by decide⟩ :=
  accepted_of_selected 12 72329 ⟨505438, by decide⟩ ⟨12, 2, 0, 505438, 72329, 1753, 65536⟩
    (by decide) selected_cut_19763

theorem selected_cut_19764 : selected 9 ⟨188189, by decide⟩
    (prefixPartial 12 72330) = some ⟨12, 1, 0, 188189, 72330, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72330_188189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72330 ⟨188189, by decide⟩ :=
  accepted_of_selected 12 72330 ⟨188189, by decide⟩ ⟨12, 1, 0, 188189, 72330, 1, 65536⟩
    (by decide) selected_cut_19764

theorem selected_cut_19765 : selected 9 ⟨505456, by decide⟩
    (prefixPartial 12 72331) = some ⟨12, 2, 0, 505456, 72331, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_72331_505456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72331 ⟨505456, by decide⟩ :=
  accepted_of_selected 12 72331 ⟨505456, by decide⟩ ⟨12, 2, 0, 505456, 72331, 1625, 65536⟩
    (by decide) selected_cut_19765

theorem unmarked_context_11_18082_505457 : frontier 10 ⟨505457, by decide⟩
    (prefixCache 11 18082) (prefixPartial 11 18082) = false := by
  decide +kernel

theorem node_context_11_18082_505457 : EJMOriginalGlobalDAGData.nodes 10 ⟨505457, by decide⟩ =
    .split (coordinate 11) (![⟨505419, by decide⟩,⟨505438, by decide⟩,⟨188189, by decide⟩,⟨505456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18082_505457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18082 ⟨505457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18082
    ⟨505457, by decide⟩ (by decide) (![⟨505419, by decide⟩,⟨505438, by decide⟩,⟨188189, by decide⟩,⟨505456, by decide⟩]) unmarked_context_11_18082_505457 node_context_11_18082_505457
  intro a
  fin_cases a
  · exact context_12_72328_505419
  · exact context_12_72329_505438
  · exact context_12_72330_188189
  · exact context_12_72331_505456

theorem selected_cut_19766 : selected 9 ⟨505479, by decide⟩
    (prefixPartial 12 72332) = some ⟨12, 2, 0, 505479, 72332, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_72332_505479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72332 ⟨505479, by decide⟩ :=
  accepted_of_selected 12 72332 ⟨505479, by decide⟩ ⟨12, 2, 0, 505479, 72332, 1849, 65536⟩
    (by decide) selected_cut_19766

theorem selected_cut_19767 : selected 9 ⟨505520, by decide⟩
    (prefixPartial 12 72333) = some ⟨12, 2, 0, 505520, 72333, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_72333_505520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72333 ⟨505520, by decide⟩ :=
  accepted_of_selected 12 72333 ⟨505520, by decide⟩ ⟨12, 2, 0, 505520, 72333, 2069, 65536⟩
    (by decide) selected_cut_19767

theorem selected_cut_19768 : selected 9 ⟨505545, by decide⟩
    (prefixPartial 12 72334) = some ⟨12, 2, 0, 505545, 72334, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_72334_505545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72334 ⟨505545, by decide⟩ :=
  accepted_of_selected 12 72334 ⟨505545, by decide⟩ ⟨12, 2, 0, 505545, 72334, 1969, 65536⟩
    (by decide) selected_cut_19768

theorem selected_cut_19769 : selected 9 ⟨505568, by decide⟩
    (prefixPartial 12 72335) = some ⟨12, 2, 0, 505568, 72335, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_72335_505568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72335 ⟨505568, by decide⟩ :=
  accepted_of_selected 12 72335 ⟨505568, by decide⟩ ⟨12, 2, 0, 505568, 72335, 2009, 65536⟩
    (by decide) selected_cut_19769

theorem unmarked_context_11_18083_505569 : frontier 10 ⟨505569, by decide⟩
    (prefixCache 11 18083) (prefixPartial 11 18083) = false := by
  decide +kernel

theorem node_context_11_18083_505569 : EJMOriginalGlobalDAGData.nodes 10 ⟨505569, by decide⟩ =
    .split (coordinate 11) (![⟨505479, by decide⟩,⟨505520, by decide⟩,⟨505545, by decide⟩,⟨505568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18083_505569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18083 ⟨505569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18083
    ⟨505569, by decide⟩ (by decide) (![⟨505479, by decide⟩,⟨505520, by decide⟩,⟨505545, by decide⟩,⟨505568, by decide⟩]) unmarked_context_11_18083_505569 node_context_11_18083_505569
  intro a
  fin_cases a
  · exact context_12_72332_505479
  · exact context_12_72333_505520
  · exact context_12_72334_505545
  · exact context_12_72335_505568

theorem unmarked_context_10_4520_505570 : frontier 11 ⟨505570, by decide⟩
    (prefixCache 10 4520) (prefixPartial 10 4520) = false := by
  decide +kernel

theorem node_context_10_4520_505570 : EJMOriginalGlobalDAGData.nodes 11 ⟨505570, by decide⟩ =
    .split (coordinate 10) (![⟨505311, by decide⟩,⟨505401, by decide⟩,⟨505457, by decide⟩,⟨505569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4520_505570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4520 ⟨505570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4520
    ⟨505570, by decide⟩ (by decide) (![⟨505311, by decide⟩,⟨505401, by decide⟩,⟨505457, by decide⟩,⟨505569, by decide⟩]) unmarked_context_10_4520_505570 node_context_10_4520_505570
  intro a
  fin_cases a
  · exact context_11_18080_505311
  · exact context_11_18081_505401
  · exact context_11_18082_505457
  · exact context_11_18083_505569

theorem selected_cut_19770 : selected 9 ⟨505595, by decide⟩
    (prefixPartial 12 72336) = some ⟨12, 2, 0, 505595, 72336, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_72336_505595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72336 ⟨505595, by decide⟩ :=
  accepted_of_selected 12 72336 ⟨505595, by decide⟩ ⟨12, 2, 0, 505595, 72336, 1793, 65536⟩
    (by decide) selected_cut_19770

theorem selected_cut_19771 : selected 9 ⟨505642, by decide⟩
    (prefixPartial 12 72337) = some ⟨12, 2, 0, 505642, 72337, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_72337_505642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72337 ⟨505642, by decide⟩ :=
  accepted_of_selected 12 72337 ⟨505642, by decide⟩ ⟨12, 2, 0, 505642, 72337, 2273, 65536⟩
    (by decide) selected_cut_19771

theorem selected_cut_19772 : selected 9 ⟨505675, by decide⟩
    (prefixPartial 12 72338) = some ⟨12, 2, 0, 505675, 72338, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_72338_505675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72338 ⟨505675, by decide⟩ :=
  accepted_of_selected 12 72338 ⟨505675, by decide⟩ ⟨12, 2, 0, 505675, 72338, 2037, 65536⟩
    (by decide) selected_cut_19772

theorem selected_cut_19773 : selected 9 ⟨505703, by decide⟩
    (prefixPartial 12 72339) = some ⟨12, 2, 0, 505703, 72339, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_72339_505703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72339 ⟨505703, by decide⟩ :=
  accepted_of_selected 12 72339 ⟨505703, by decide⟩ ⟨12, 2, 0, 505703, 72339, 2065, 65536⟩
    (by decide) selected_cut_19773

theorem unmarked_context_11_18084_505704 : frontier 10 ⟨505704, by decide⟩
    (prefixCache 11 18084) (prefixPartial 11 18084) = false := by
  decide +kernel

theorem node_context_11_18084_505704 : EJMOriginalGlobalDAGData.nodes 10 ⟨505704, by decide⟩ =
    .split (coordinate 11) (![⟨505595, by decide⟩,⟨505642, by decide⟩,⟨505675, by decide⟩,⟨505703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18084_505704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18084 ⟨505704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18084
    ⟨505704, by decide⟩ (by decide) (![⟨505595, by decide⟩,⟨505642, by decide⟩,⟨505675, by decide⟩,⟨505703, by decide⟩]) unmarked_context_11_18084_505704 node_context_11_18084_505704
  intro a
  fin_cases a
  · exact context_12_72336_505595
  · exact context_12_72337_505642
  · exact context_12_72338_505675
  · exact context_12_72339_505703

theorem selected_cut_19774 : selected 9 ⟨505735, by decide⟩
    (prefixPartial 12 72340) = some ⟨12, 2, 0, 505735, 72340, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_72340_505735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72340 ⟨505735, by decide⟩ :=
  accepted_of_selected 12 72340 ⟨505735, by decide⟩ ⟨12, 2, 0, 505735, 72340, 1997, 65536⟩
    (by decide) selected_cut_19774

theorem selected_cut_19775 : selected 9 ⟨505761, by decide⟩
    (prefixPartial 12 72341) = some ⟨12, 2, 0, 505761, 72341, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_72341_505761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72341 ⟨505761, by decide⟩ :=
  accepted_of_selected 12 72341 ⟨505761, by decide⟩ ⟨12, 2, 0, 505761, 72341, 2029, 65536⟩
    (by decide) selected_cut_19775

theorem selected_cut_19776 : selected 9 ⟨505795, by decide⟩
    (prefixPartial 12 72342) = some ⟨12, 2, 0, 505795, 72342, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_72342_505795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72342 ⟨505795, by decide⟩ :=
  accepted_of_selected 12 72342 ⟨505795, by decide⟩ ⟨12, 2, 0, 505795, 72342, 2129, 65536⟩
    (by decide) selected_cut_19776

theorem selected_cut_19777 : selected 9 ⟨505822, by decide⟩
    (prefixPartial 12 72343) = some ⟨12, 2, 0, 505822, 72343, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_72343_505822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72343 ⟨505822, by decide⟩ :=
  accepted_of_selected 12 72343 ⟨505822, by decide⟩ ⟨12, 2, 0, 505822, 72343, 2093, 65536⟩
    (by decide) selected_cut_19777

theorem unmarked_context_11_18085_505823 : frontier 10 ⟨505823, by decide⟩
    (prefixCache 11 18085) (prefixPartial 11 18085) = false := by
  decide +kernel

theorem node_context_11_18085_505823 : EJMOriginalGlobalDAGData.nodes 10 ⟨505823, by decide⟩ =
    .split (coordinate 11) (![⟨505735, by decide⟩,⟨505761, by decide⟩,⟨505795, by decide⟩,⟨505822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18085_505823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18085 ⟨505823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18085
    ⟨505823, by decide⟩ (by decide) (![⟨505735, by decide⟩,⟨505761, by decide⟩,⟨505795, by decide⟩,⟨505822, by decide⟩]) unmarked_context_11_18085_505823 node_context_11_18085_505823
  intro a
  fin_cases a
  · exact context_12_72340_505735
  · exact context_12_72341_505761
  · exact context_12_72342_505795
  · exact context_12_72343_505822

theorem selected_cut_19778 : selected 9 ⟨505840, by decide⟩
    (prefixPartial 12 72344) = some ⟨12, 2, 0, 505840, 72344, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_72344_505840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72344 ⟨505840, by decide⟩ :=
  accepted_of_selected 12 72344 ⟨505840, by decide⟩ ⟨12, 2, 0, 505840, 72344, 1625, 65536⟩
    (by decide) selected_cut_19778

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
