/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover356
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34276 : selected 8 ⟨886011, by decide⟩
    (prefixPartial 13 452695) = some ⟨13, 2, 0, 886011, 452695, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_452695_886011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452695 ⟨886011, by decide⟩ :=
  accepted_of_selected 13 452695 ⟨886011, by decide⟩ ⟨13, 2, 0, 886011, 452695, 1105, 16384⟩
    (by decide) selected_cut_34276

theorem unmarked_context_12_113173_886012 : frontier 9 ⟨886012, by decide⟩
    (prefixCache 12 113173) (prefixPartial 12 113173) = false := by
  decide +kernel

theorem node_context_12_113173_886012 : EJMOriginalGlobalDAGData.nodes 9 ⟨886012, by decide⟩ =
    .split (coordinate 12) (![⟨885937, by decide⟩,⟨885965, by decide⟩,⟨885987, by decide⟩,⟨886011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113173_886012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113173 ⟨886012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113173
    ⟨886012, by decide⟩ (by decide) (![⟨885937, by decide⟩,⟨885965, by decide⟩,⟨885987, by decide⟩,⟨886011, by decide⟩]) unmarked_context_12_113173_886012 node_context_12_113173_886012
  intro a
  fin_cases a
  · exact context_13_452692_885937
  · exact context_13_452693_885965
  · exact context_13_452694_885987
  · exact context_13_452695_886011

theorem selected_cut_34277 : selected 8 ⟨886044, by decide⟩
    (prefixPartial 13 452696) = some ⟨13, 2, 0, 886044, 452696, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_452696_886044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452696 ⟨886044, by decide⟩ :=
  accepted_of_selected 13 452696 ⟨886044, by decide⟩ ⟨13, 2, 0, 886044, 452696, 2085, 16384⟩
    (by decide) selected_cut_34277

theorem selected_cut_34278 : selected 8 ⟨886070, by decide⟩
    (prefixPartial 13 452697) = some ⟨13, 2, 0, 886070, 452697, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_452697_886070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452697 ⟨886070, by decide⟩ :=
  accepted_of_selected 13 452697 ⟨886070, by decide⟩ ⟨13, 2, 0, 886070, 452697, 2045, 16384⟩
    (by decide) selected_cut_34278

theorem selected_cut_34279 : selected 8 ⟨886088, by decide⟩
    (prefixPartial 13 452698) = some ⟨13, 2, 0, 886088, 452698, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_452698_886088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452698 ⟨886088, by decide⟩ :=
  accepted_of_selected 13 452698 ⟨886088, by decide⟩ ⟨13, 2, 0, 886088, 452698, 1157, 16384⟩
    (by decide) selected_cut_34279

theorem selected_cut_34280 : selected 8 ⟨886104, by decide⟩
    (prefixPartial 13 452699) = some ⟨13, 2, 0, 886104, 452699, 993, 16384⟩ := by
  decide +kernel

theorem context_13_452699_886104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452699 ⟨886104, by decide⟩ :=
  accepted_of_selected 13 452699 ⟨886104, by decide⟩ ⟨13, 2, 0, 886104, 452699, 993, 16384⟩
    (by decide) selected_cut_34280

theorem unmarked_context_12_113174_886105 : frontier 9 ⟨886105, by decide⟩
    (prefixCache 12 113174) (prefixPartial 12 113174) = false := by
  decide +kernel

theorem node_context_12_113174_886105 : EJMOriginalGlobalDAGData.nodes 9 ⟨886105, by decide⟩ =
    .split (coordinate 12) (![⟨886044, by decide⟩,⟨886070, by decide⟩,⟨886088, by decide⟩,⟨886104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113174_886105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113174 ⟨886105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113174
    ⟨886105, by decide⟩ (by decide) (![⟨886044, by decide⟩,⟨886070, by decide⟩,⟨886088, by decide⟩,⟨886104, by decide⟩]) unmarked_context_12_113174_886105 node_context_12_113174_886105
  intro a
  fin_cases a
  · exact context_13_452696_886044
  · exact context_13_452697_886070
  · exact context_13_452698_886088
  · exact context_13_452699_886104

theorem selected_cut_34281 : selected 8 ⟨886152, by decide⟩
    (prefixPartial 13 452700) = some ⟨13, 2, 0, 886152, 452700, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_452700_886152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452700 ⟨886152, by decide⟩ :=
  accepted_of_selected 13 452700 ⟨886152, by decide⟩ ⟨13, 2, 0, 886152, 452700, 2461, 16384⟩
    (by decide) selected_cut_34281

theorem selected_cut_34282 : selected 8 ⟨886194, by decide⟩
    (prefixPartial 13 452701) = some ⟨13, 2, 0, 886194, 452701, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_452701_886194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452701 ⟨886194, by decide⟩ :=
  accepted_of_selected 13 452701 ⟨886194, by decide⟩ ⟨13, 2, 0, 886194, 452701, 2573, 16384⟩
    (by decide) selected_cut_34282

theorem selected_cut_34283 : selected 8 ⟨886218, by decide⟩
    (prefixPartial 13 452702) = some ⟨13, 2, 0, 886218, 452702, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_452702_886218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452702 ⟨886218, by decide⟩ :=
  accepted_of_selected 13 452702 ⟨886218, by decide⟩ ⟨13, 2, 0, 886218, 452702, 1253, 16384⟩
    (by decide) selected_cut_34283

theorem selected_cut_34284 : selected 8 ⟨886238, by decide⟩
    (prefixPartial 13 452703) = some ⟨13, 2, 0, 886238, 452703, 909, 16384⟩ := by
  decide +kernel

theorem context_13_452703_886238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452703 ⟨886238, by decide⟩ :=
  accepted_of_selected 13 452703 ⟨886238, by decide⟩ ⟨13, 2, 0, 886238, 452703, 909, 16384⟩
    (by decide) selected_cut_34284

theorem unmarked_context_12_113175_886239 : frontier 9 ⟨886239, by decide⟩
    (prefixCache 12 113175) (prefixPartial 12 113175) = false := by
  decide +kernel

theorem node_context_12_113175_886239 : EJMOriginalGlobalDAGData.nodes 9 ⟨886239, by decide⟩ =
    .split (coordinate 12) (![⟨886152, by decide⟩,⟨886194, by decide⟩,⟨886218, by decide⟩,⟨886238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113175_886239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113175 ⟨886239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113175
    ⟨886239, by decide⟩ (by decide) (![⟨886152, by decide⟩,⟨886194, by decide⟩,⟨886218, by decide⟩,⟨886238, by decide⟩]) unmarked_context_12_113175_886239 node_context_12_113175_886239
  intro a
  fin_cases a
  · exact context_13_452700_886152
  · exact context_13_452701_886194
  · exact context_13_452702_886218
  · exact context_13_452703_886238

theorem unmarked_context_11_28293_886240 : frontier 10 ⟨886240, by decide⟩
    (prefixCache 11 28293) (prefixPartial 11 28293) = false := by
  decide +kernel

theorem node_context_11_28293_886240 : EJMOriginalGlobalDAGData.nodes 10 ⟨886240, by decide⟩ =
    .split (coordinate 11) (![⟨885886, by decide⟩,⟨886012, by decide⟩,⟨886105, by decide⟩,⟨886239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28293_886240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28293 ⟨886240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28293
    ⟨886240, by decide⟩ (by decide) (![⟨885886, by decide⟩,⟨886012, by decide⟩,⟨886105, by decide⟩,⟨886239, by decide⟩]) unmarked_context_11_28293_886240 node_context_11_28293_886240
  intro a
  fin_cases a
  · exact context_12_113172_885886
  · exact context_12_113173_886012
  · exact context_12_113174_886105
  · exact context_12_113175_886239

theorem selected_cut_34285 : selected 8 ⟨886260, by decide⟩
    (prefixPartial 13 452704) = some ⟨13, 2, 0, 886260, 452704, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_452704_886260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452704 ⟨886260, by decide⟩ :=
  accepted_of_selected 13 452704 ⟨886260, by decide⟩ ⟨13, 2, 0, 886260, 452704, 1421, 16384⟩
    (by decide) selected_cut_34285

theorem selected_cut_34286 : selected 8 ⟨886283, by decide⟩
    (prefixPartial 13 452705) = some ⟨13, 2, 0, 886283, 452705, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_452705_886283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452705 ⟨886283, by decide⟩ :=
  accepted_of_selected 13 452705 ⟨886283, by decide⟩ ⟨13, 2, 0, 886283, 452705, 2233, 16384⟩
    (by decide) selected_cut_34286

theorem selected_cut_34287 : selected 8 ⟨886304, by decide⟩
    (prefixPartial 13 452706) = some ⟨13, 2, 0, 886304, 452706, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_452706_886304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452706 ⟨886304, by decide⟩ :=
  accepted_of_selected 13 452706 ⟨886304, by decide⟩ ⟨13, 2, 0, 886304, 452706, 1193, 16384⟩
    (by decide) selected_cut_34287

theorem selected_cut_34288 : selected 8 ⟨886315, by decide⟩
    (prefixPartial 13 452707) = some ⟨13, 2, 0, 886315, 452707, 701, 16384⟩ := by
  decide +kernel

theorem context_13_452707_886315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452707 ⟨886315, by decide⟩ :=
  accepted_of_selected 13 452707 ⟨886315, by decide⟩ ⟨13, 2, 0, 886315, 452707, 701, 16384⟩
    (by decide) selected_cut_34288

theorem unmarked_context_12_113176_886316 : frontier 9 ⟨886316, by decide⟩
    (prefixCache 12 113176) (prefixPartial 12 113176) = false := by
  decide +kernel

theorem node_context_12_113176_886316 : EJMOriginalGlobalDAGData.nodes 9 ⟨886316, by decide⟩ =
    .split (coordinate 12) (![⟨886260, by decide⟩,⟨886283, by decide⟩,⟨886304, by decide⟩,⟨886315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113176_886316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113176 ⟨886316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113176
    ⟨886316, by decide⟩ (by decide) (![⟨886260, by decide⟩,⟨886283, by decide⟩,⟨886304, by decide⟩,⟨886315, by decide⟩]) unmarked_context_12_113176_886316 node_context_12_113176_886316
  intro a
  fin_cases a
  · exact context_13_452704_886260
  · exact context_13_452705_886283
  · exact context_13_452706_886304
  · exact context_13_452707_886315

theorem selected_cut_34289 : selected 8 ⟨886349, by decide⟩
    (prefixPartial 13 452708) = some ⟨13, 2, 0, 886349, 452708, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_452708_886349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452708 ⟨886349, by decide⟩ :=
  accepted_of_selected 13 452708 ⟨886349, by decide⟩ ⟨13, 2, 0, 886349, 452708, 1933, 16384⟩
    (by decide) selected_cut_34289

theorem selected_cut_34290 : selected 8 ⟨886384, by decide⟩
    (prefixPartial 13 452709) = some ⟨13, 2, 0, 886384, 452709, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_452709_886384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452709 ⟨886384, by decide⟩ :=
  accepted_of_selected 13 452709 ⟨886384, by decide⟩ ⟨13, 2, 0, 886384, 452709, 2573, 16384⟩
    (by decide) selected_cut_34290

theorem selected_cut_34291 : selected 8 ⟨886412, by decide⟩
    (prefixPartial 13 452710) = some ⟨13, 2, 0, 886412, 452710, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_452710_886412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452710 ⟨886412, by decide⟩ :=
  accepted_of_selected 13 452710 ⟨886412, by decide⟩ ⟨13, 2, 0, 886412, 452710, 1541, 16384⟩
    (by decide) selected_cut_34291

theorem selected_cut_34292 : selected 8 ⟨886431, by decide⟩
    (prefixPartial 13 452711) = some ⟨13, 2, 0, 886431, 452711, 921, 16384⟩ := by
  decide +kernel

theorem context_13_452711_886431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452711 ⟨886431, by decide⟩ :=
  accepted_of_selected 13 452711 ⟨886431, by decide⟩ ⟨13, 2, 0, 886431, 452711, 921, 16384⟩
    (by decide) selected_cut_34292

theorem unmarked_context_12_113177_886432 : frontier 9 ⟨886432, by decide⟩
    (prefixCache 12 113177) (prefixPartial 12 113177) = false := by
  decide +kernel

theorem node_context_12_113177_886432 : EJMOriginalGlobalDAGData.nodes 9 ⟨886432, by decide⟩ =
    .split (coordinate 12) (![⟨886349, by decide⟩,⟨886384, by decide⟩,⟨886412, by decide⟩,⟨886431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113177_886432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113177 ⟨886432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113177
    ⟨886432, by decide⟩ (by decide) (![⟨886349, by decide⟩,⟨886384, by decide⟩,⟨886412, by decide⟩,⟨886431, by decide⟩]) unmarked_context_12_113177_886432 node_context_12_113177_886432
  intro a
  fin_cases a
  · exact context_13_452708_886349
  · exact context_13_452709_886384
  · exact context_13_452710_886412
  · exact context_13_452711_886431

theorem selected_cut_34293 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 113178) = some ⟨12, 1, 0, 660636, 113178, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113178_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113178 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 113178 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 113178, 1, 65536⟩
    (by decide) selected_cut_34293

theorem selected_cut_34294 : selected 8 ⟨886460, by decide⟩
    (prefixPartial 13 452716) = some ⟨13, 2, 0, 886460, 452716, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_452716_886460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452716 ⟨886460, by decide⟩ :=
  accepted_of_selected 13 452716 ⟨886460, by decide⟩ ⟨13, 2, 0, 886460, 452716, 1613, 16384⟩
    (by decide) selected_cut_34294

theorem selected_cut_34295 : selected 8 ⟨886496, by decide⟩
    (prefixPartial 13 452717) = some ⟨13, 2, 0, 886496, 452717, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_452717_886496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452717 ⟨886496, by decide⟩ :=
  accepted_of_selected 13 452717 ⟨886496, by decide⟩ ⟨13, 2, 0, 886496, 452717, 2533, 16384⟩
    (by decide) selected_cut_34295

theorem selected_cut_34296 : selected 8 ⟨886517, by decide⟩
    (prefixPartial 13 452718) = some ⟨13, 2, 0, 886517, 452718, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_452718_886517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452718 ⟨886517, by decide⟩ :=
  accepted_of_selected 13 452718 ⟨886517, by decide⟩ ⟨13, 2, 0, 886517, 452718, 1197, 16384⟩
    (by decide) selected_cut_34296

theorem selected_cut_34297 : selected 8 ⟨886530, by decide⟩
    (prefixPartial 13 452719) = some ⟨13, 2, 0, 886530, 452719, 737, 16384⟩ := by
  decide +kernel

theorem context_13_452719_886530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452719 ⟨886530, by decide⟩ :=
  accepted_of_selected 13 452719 ⟨886530, by decide⟩ ⟨13, 2, 0, 886530, 452719, 737, 16384⟩
    (by decide) selected_cut_34297

theorem unmarked_context_12_113179_886531 : frontier 9 ⟨886531, by decide⟩
    (prefixCache 12 113179) (prefixPartial 12 113179) = false := by
  decide +kernel

theorem node_context_12_113179_886531 : EJMOriginalGlobalDAGData.nodes 9 ⟨886531, by decide⟩ =
    .split (coordinate 12) (![⟨886460, by decide⟩,⟨886496, by decide⟩,⟨886517, by decide⟩,⟨886530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113179_886531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113179 ⟨886531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113179
    ⟨886531, by decide⟩ (by decide) (![⟨886460, by decide⟩,⟨886496, by decide⟩,⟨886517, by decide⟩,⟨886530, by decide⟩]) unmarked_context_12_113179_886531 node_context_12_113179_886531
  intro a
  fin_cases a
  · exact context_13_452716_886460
  · exact context_13_452717_886496
  · exact context_13_452718_886517
  · exact context_13_452719_886530

theorem unmarked_context_11_28294_886532 : frontier 10 ⟨886532, by decide⟩
    (prefixCache 11 28294) (prefixPartial 11 28294) = false := by
  decide +kernel

theorem node_context_11_28294_886532 : EJMOriginalGlobalDAGData.nodes 10 ⟨886532, by decide⟩ =
    .split (coordinate 11) (![⟨886316, by decide⟩,⟨886432, by decide⟩,⟨660636, by decide⟩,⟨886531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28294_886532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28294 ⟨886532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28294
    ⟨886532, by decide⟩ (by decide) (![⟨886316, by decide⟩,⟨886432, by decide⟩,⟨660636, by decide⟩,⟨886531, by decide⟩]) unmarked_context_11_28294_886532 node_context_11_28294_886532
  intro a
  fin_cases a
  · exact context_12_113176_886316
  · exact context_12_113177_886432
  · exact context_12_113178_660636
  · exact context_12_113179_886531

theorem selected_cut_34298 : selected 8 ⟨886554, by decide⟩
    (prefixPartial 13 452720) = some ⟨13, 2, 0, 886554, 452720, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_452720_886554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452720 ⟨886554, by decide⟩ :=
  accepted_of_selected 13 452720 ⟨886554, by decide⟩ ⟨13, 2, 0, 886554, 452720, 1521, 16384⟩
    (by decide) selected_cut_34298

theorem selected_cut_34299 : selected 8 ⟨886582, by decide⟩
    (prefixPartial 13 452721) = some ⟨13, 2, 0, 886582, 452721, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_452721_886582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452721 ⟨886582, by decide⟩ :=
  accepted_of_selected 13 452721 ⟨886582, by decide⟩ ⟨13, 2, 0, 886582, 452721, 2633, 16384⟩
    (by decide) selected_cut_34299

theorem selected_cut_34300 : selected 8 ⟨886606, by decide⟩
    (prefixPartial 13 452722) = some ⟨13, 2, 0, 886606, 452722, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_452722_886606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452722 ⟨886606, by decide⟩ :=
  accepted_of_selected 13 452722 ⟨886606, by decide⟩ ⟨13, 2, 0, 886606, 452722, 1553, 16384⟩
    (by decide) selected_cut_34300

theorem selected_cut_34301 : selected 8 ⟨886616, by decide⟩
    (prefixPartial 13 452723) = some ⟨13, 2, 0, 886616, 452723, 801, 16384⟩ := by
  decide +kernel

theorem context_13_452723_886616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452723 ⟨886616, by decide⟩ :=
  accepted_of_selected 13 452723 ⟨886616, by decide⟩ ⟨13, 2, 0, 886616, 452723, 801, 16384⟩
    (by decide) selected_cut_34301

theorem unmarked_context_12_113180_886617 : frontier 9 ⟨886617, by decide⟩
    (prefixCache 12 113180) (prefixPartial 12 113180) = false := by
  decide +kernel

theorem node_context_12_113180_886617 : EJMOriginalGlobalDAGData.nodes 9 ⟨886617, by decide⟩ =
    .split (coordinate 12) (![⟨886554, by decide⟩,⟨886582, by decide⟩,⟨886606, by decide⟩,⟨886616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113180_886617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113180 ⟨886617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113180
    ⟨886617, by decide⟩ (by decide) (![⟨886554, by decide⟩,⟨886582, by decide⟩,⟨886606, by decide⟩,⟨886616, by decide⟩]) unmarked_context_12_113180_886617 node_context_12_113180_886617
  intro a
  fin_cases a
  · exact context_13_452720_886554
  · exact context_13_452721_886582
  · exact context_13_452722_886606
  · exact context_13_452723_886616

theorem selected_cut_34302 : selected 8 ⟨886656, by decide⟩
    (prefixPartial 13 452724) = some ⟨13, 2, 0, 886656, 452724, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_452724_886656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452724 ⟨886656, by decide⟩ :=
  accepted_of_selected 13 452724 ⟨886656, by decide⟩ ⟨13, 2, 0, 886656, 452724, 2173, 16384⟩
    (by decide) selected_cut_34302

theorem selected_cut_34303 : selected 8 ⟨886704, by decide⟩
    (prefixPartial 13 452725) = some ⟨13, 2, 0, 886704, 452725, 2897, 16384⟩ := by
  decide +kernel

theorem context_13_452725_886704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452725 ⟨886704, by decide⟩ :=
  accepted_of_selected 13 452725 ⟨886704, by decide⟩ ⟨13, 2, 0, 886704, 452725, 2897, 16384⟩
    (by decide) selected_cut_34303

theorem selected_cut_34304 : selected 8 ⟨886752, by decide⟩
    (prefixPartial 13 452726) = some ⟨13, 2, 0, 886752, 452726, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_452726_886752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452726 ⟨886752, by decide⟩ :=
  accepted_of_selected 13 452726 ⟨886752, by decide⟩ ⟨13, 2, 0, 886752, 452726, 1869, 16384⟩
    (by decide) selected_cut_34304

theorem selected_cut_34305 : selected 8 ⟨886777, by decide⟩
    (prefixPartial 13 452727) = some ⟨13, 2, 0, 886777, 452727, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_452727_886777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452727 ⟨886777, by decide⟩ :=
  accepted_of_selected 13 452727 ⟨886777, by decide⟩ ⟨13, 2, 0, 886777, 452727, 1025, 16384⟩
    (by decide) selected_cut_34305

theorem unmarked_context_12_113181_886778 : frontier 9 ⟨886778, by decide⟩
    (prefixCache 12 113181) (prefixPartial 12 113181) = false := by
  decide +kernel

theorem node_context_12_113181_886778 : EJMOriginalGlobalDAGData.nodes 9 ⟨886778, by decide⟩ =
    .split (coordinate 12) (![⟨886656, by decide⟩,⟨886704, by decide⟩,⟨886752, by decide⟩,⟨886777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113181_886778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113181 ⟨886778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113181
    ⟨886778, by decide⟩ (by decide) (![⟨886656, by decide⟩,⟨886704, by decide⟩,⟨886752, by decide⟩,⟨886777, by decide⟩]) unmarked_context_12_113181_886778 node_context_12_113181_886778
  intro a
  fin_cases a
  · exact context_13_452724_886656
  · exact context_13_452725_886704
  · exact context_13_452726_886752
  · exact context_13_452727_886777

theorem selected_cut_34306 : selected 8 ⟨886801, by decide⟩
    (prefixPartial 13 452728) = some ⟨13, 2, 0, 886801, 452728, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_452728_886801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452728 ⟨886801, by decide⟩ :=
  accepted_of_selected 13 452728 ⟨886801, by decide⟩ ⟨13, 2, 0, 886801, 452728, 1429, 16384⟩
    (by decide) selected_cut_34306

theorem selected_cut_34307 : selected 8 ⟨886828, by decide⟩
    (prefixPartial 13 452729) = some ⟨13, 2, 0, 886828, 452729, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_452729_886828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452729 ⟨886828, by decide⟩ :=
  accepted_of_selected 13 452729 ⟨886828, by decide⟩ ⟨13, 2, 0, 886828, 452729, 2441, 16384⟩
    (by decide) selected_cut_34307

theorem selected_cut_34308 : selected 8 ⟨886852, by decide⟩
    (prefixPartial 13 452730) = some ⟨13, 2, 0, 886852, 452730, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_452730_886852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452730 ⟨886852, by decide⟩ :=
  accepted_of_selected 13 452730 ⟨886852, by decide⟩ ⟨13, 2, 0, 886852, 452730, 1393, 16384⟩
    (by decide) selected_cut_34308

theorem selected_cut_34309 : selected 8 ⟨886859, by decide⟩
    (prefixPartial 13 452731) = some ⟨13, 2, 0, 886859, 452731, 833, 16384⟩ := by
  decide +kernel

theorem context_13_452731_886859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452731 ⟨886859, by decide⟩ :=
  accepted_of_selected 13 452731 ⟨886859, by decide⟩ ⟨13, 2, 0, 886859, 452731, 833, 16384⟩
    (by decide) selected_cut_34309

theorem unmarked_context_12_113182_886860 : frontier 9 ⟨886860, by decide⟩
    (prefixCache 12 113182) (prefixPartial 12 113182) = false := by
  decide +kernel

theorem node_context_12_113182_886860 : EJMOriginalGlobalDAGData.nodes 9 ⟨886860, by decide⟩ =
    .split (coordinate 12) (![⟨886801, by decide⟩,⟨886828, by decide⟩,⟨886852, by decide⟩,⟨886859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113182_886860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113182 ⟨886860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113182
    ⟨886860, by decide⟩ (by decide) (![⟨886801, by decide⟩,⟨886828, by decide⟩,⟨886852, by decide⟩,⟨886859, by decide⟩]) unmarked_context_12_113182_886860 node_context_12_113182_886860
  intro a
  fin_cases a
  · exact context_13_452728_886801
  · exact context_13_452729_886828
  · exact context_13_452730_886852
  · exact context_13_452731_886859

theorem selected_cut_34310 : selected 8 ⟨886883, by decide⟩
    (prefixPartial 13 452732) = some ⟨13, 2, 0, 886883, 452732, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_452732_886883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452732 ⟨886883, by decide⟩ :=
  accepted_of_selected 13 452732 ⟨886883, by decide⟩ ⟨13, 2, 0, 886883, 452732, 1421, 16384⟩
    (by decide) selected_cut_34310

theorem selected_cut_34311 : selected 8 ⟨886924, by decide⟩
    (prefixPartial 13 452733) = some ⟨13, 2, 0, 886924, 452733, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_452733_886924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452733 ⟨886924, by decide⟩ :=
  accepted_of_selected 13 452733 ⟨886924, by decide⟩ ⟨13, 2, 0, 886924, 452733, 2693, 16384⟩
    (by decide) selected_cut_34311

theorem selected_cut_34312 : selected 8 ⟨886953, by decide⟩
    (prefixPartial 13 452734) = some ⟨13, 2, 0, 886953, 452734, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_452734_886953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452734 ⟨886953, by decide⟩ :=
  accepted_of_selected 13 452734 ⟨886953, by decide⟩ ⟨13, 2, 0, 886953, 452734, 1497, 16384⟩
    (by decide) selected_cut_34312

theorem selected_cut_34313 : selected 8 ⟨886967, by decide⟩
    (prefixPartial 13 452735) = some ⟨13, 2, 0, 886967, 452735, 817, 16384⟩ := by
  decide +kernel

theorem context_13_452735_886967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452735 ⟨886967, by decide⟩ :=
  accepted_of_selected 13 452735 ⟨886967, by decide⟩ ⟨13, 2, 0, 886967, 452735, 817, 16384⟩
    (by decide) selected_cut_34313

theorem unmarked_context_12_113183_886968 : frontier 9 ⟨886968, by decide⟩
    (prefixCache 12 113183) (prefixPartial 12 113183) = false := by
  decide +kernel

theorem node_context_12_113183_886968 : EJMOriginalGlobalDAGData.nodes 9 ⟨886968, by decide⟩ =
    .split (coordinate 12) (![⟨886883, by decide⟩,⟨886924, by decide⟩,⟨886953, by decide⟩,⟨886967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113183_886968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113183 ⟨886968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113183
    ⟨886968, by decide⟩ (by decide) (![⟨886883, by decide⟩,⟨886924, by decide⟩,⟨886953, by decide⟩,⟨886967, by decide⟩]) unmarked_context_12_113183_886968 node_context_12_113183_886968
  intro a
  fin_cases a
  · exact context_13_452732_886883
  · exact context_13_452733_886924
  · exact context_13_452734_886953
  · exact context_13_452735_886967

theorem unmarked_context_11_28295_886969 : frontier 10 ⟨886969, by decide⟩
    (prefixCache 11 28295) (prefixPartial 11 28295) = false := by
  decide +kernel

theorem node_context_11_28295_886969 : EJMOriginalGlobalDAGData.nodes 10 ⟨886969, by decide⟩ =
    .split (coordinate 11) (![⟨886617, by decide⟩,⟨886778, by decide⟩,⟨886860, by decide⟩,⟨886968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28295_886969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28295 ⟨886969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28295
    ⟨886969, by decide⟩ (by decide) (![⟨886617, by decide⟩,⟨886778, by decide⟩,⟨886860, by decide⟩,⟨886968, by decide⟩]) unmarked_context_11_28295_886969 node_context_11_28295_886969
  intro a
  fin_cases a
  · exact context_12_113180_886617
  · exact context_12_113181_886778
  · exact context_12_113182_886860
  · exact context_12_113183_886968

theorem unmarked_context_10_7073_886970 : frontier 11 ⟨886970, by decide⟩
    (prefixCache 10 7073) (prefixPartial 10 7073) = false := by
  decide +kernel

theorem node_context_10_7073_886970 : EJMOriginalGlobalDAGData.nodes 11 ⟨886970, by decide⟩ =
    .split (coordinate 10) (![⟨885792, by decide⟩,⟨886240, by decide⟩,⟨886532, by decide⟩,⟨886969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7073_886970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7073 ⟨886970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7073
    ⟨886970, by decide⟩ (by decide) (![⟨885792, by decide⟩,⟨886240, by decide⟩,⟨886532, by decide⟩,⟨886969, by decide⟩]) unmarked_context_10_7073_886970 node_context_10_7073_886970
  intro a
  fin_cases a
  · exact context_11_28292_885792
  · exact context_11_28293_886240
  · exact context_11_28294_886532
  · exact context_11_28295_886969

theorem selected_cut_34314 : selected 8 ⟨887000, by decide⟩
    (prefixPartial 13 452736) = some ⟨13, 2, 0, 887000, 452736, 981, 16384⟩ := by
  decide +kernel

theorem context_13_452736_887000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452736 ⟨887000, by decide⟩ :=
  accepted_of_selected 13 452736 ⟨887000, by decide⟩ ⟨13, 2, 0, 887000, 452736, 981, 16384⟩
    (by decide) selected_cut_34314

theorem selected_cut_34315 : selected 8 ⟨887066, by decide⟩
    (prefixPartial 13 452737) = some ⟨13, 2, 0, 887066, 452737, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_452737_887066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452737 ⟨887066, by decide⟩ :=
  accepted_of_selected 13 452737 ⟨887066, by decide⟩ ⟨13, 2, 0, 887066, 452737, 2213, 16384⟩
    (by decide) selected_cut_34315

theorem selected_cut_34316 : selected 8 ⟨887100, by decide⟩
    (prefixPartial 13 452738) = some ⟨13, 2, 0, 887100, 452738, 893, 16384⟩ := by
  decide +kernel

theorem context_13_452738_887100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452738 ⟨887100, by decide⟩ :=
  accepted_of_selected 13 452738 ⟨887100, by decide⟩ ⟨13, 2, 0, 887100, 452738, 893, 16384⟩
    (by decide) selected_cut_34316

theorem selected_cut_34317 : selected 8 ⟨887105, by decide⟩
    (prefixPartial 13 452739) = some ⟨13, 2, 0, 887105, 452739, 517, 16384⟩ := by
  decide +kernel

theorem context_13_452739_887105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452739 ⟨887105, by decide⟩ :=
  accepted_of_selected 13 452739 ⟨887105, by decide⟩ ⟨13, 2, 0, 887105, 452739, 517, 16384⟩
    (by decide) selected_cut_34317

theorem unmarked_context_12_113184_887106 : frontier 9 ⟨887106, by decide⟩
    (prefixCache 12 113184) (prefixPartial 12 113184) = false := by
  decide +kernel

theorem node_context_12_113184_887106 : EJMOriginalGlobalDAGData.nodes 9 ⟨887106, by decide⟩ =
    .split (coordinate 12) (![⟨887000, by decide⟩,⟨887066, by decide⟩,⟨887100, by decide⟩,⟨887105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113184_887106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113184 ⟨887106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113184
    ⟨887106, by decide⟩ (by decide) (![⟨887000, by decide⟩,⟨887066, by decide⟩,⟨887100, by decide⟩,⟨887105, by decide⟩]) unmarked_context_12_113184_887106 node_context_12_113184_887106
  intro a
  fin_cases a
  · exact context_13_452736_887000
  · exact context_13_452737_887066
  · exact context_13_452738_887100
  · exact context_13_452739_887105

theorem selected_cut_34318 : selected 8 ⟨887142, by decide⟩
    (prefixPartial 13 452740) = some ⟨13, 2, 0, 887142, 452740, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_452740_887142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452740 ⟨887142, by decide⟩ :=
  accepted_of_selected 13 452740 ⟨887142, by decide⟩ ⟨13, 2, 0, 887142, 452740, 1241, 16384⟩
    (by decide) selected_cut_34318

theorem selected_cut_34319 : selected 8 ⟨887207, by decide⟩
    (prefixPartial 13 452741) = some ⟨13, 2, 0, 887207, 452741, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_452741_887207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452741 ⟨887207, by decide⟩ :=
  accepted_of_selected 13 452741 ⟨887207, by decide⟩ ⟨13, 2, 0, 887207, 452741, 2549, 16384⟩
    (by decide) selected_cut_34319

theorem selected_cut_34320 : selected 8 ⟨887233, by decide⟩
    (prefixPartial 13 452742) = some ⟨13, 2, 0, 887233, 452742, 937, 16384⟩ := by
  decide +kernel

theorem context_13_452742_887233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452742 ⟨887233, by decide⟩ :=
  accepted_of_selected 13 452742 ⟨887233, by decide⟩ ⟨13, 2, 0, 887233, 452742, 937, 16384⟩
    (by decide) selected_cut_34320

theorem selected_cut_34321 : selected 8 ⟨887241, by decide⟩
    (prefixPartial 13 452743) = some ⟨13, 2, 0, 887241, 452743, 701, 16384⟩ := by
  decide +kernel

theorem context_13_452743_887241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452743 ⟨887241, by decide⟩ :=
  accepted_of_selected 13 452743 ⟨887241, by decide⟩ ⟨13, 2, 0, 887241, 452743, 701, 16384⟩
    (by decide) selected_cut_34321

theorem unmarked_context_12_113185_887242 : frontier 9 ⟨887242, by decide⟩
    (prefixCache 12 113185) (prefixPartial 12 113185) = false := by
  decide +kernel

theorem node_context_12_113185_887242 : EJMOriginalGlobalDAGData.nodes 9 ⟨887242, by decide⟩ =
    .split (coordinate 12) (![⟨887142, by decide⟩,⟨887207, by decide⟩,⟨887233, by decide⟩,⟨887241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113185_887242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113185 ⟨887242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113185
    ⟨887242, by decide⟩ (by decide) (![⟨887142, by decide⟩,⟨887207, by decide⟩,⟨887233, by decide⟩,⟨887241, by decide⟩]) unmarked_context_12_113185_887242 node_context_12_113185_887242
  intro a
  fin_cases a
  · exact context_13_452740_887142
  · exact context_13_452741_887207
  · exact context_13_452742_887233
  · exact context_13_452743_887241

theorem selected_cut_34322 : selected 9 ⟨887342, by decide⟩
    (prefixPartial 12 113186) = some ⟨12, 2, 0, 887342, 113186, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_113186_887342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113186 ⟨887342, by decide⟩ :=
  accepted_of_selected 12 113186 ⟨887342, by decide⟩ ⟨12, 2, 0, 887342, 113186, 3973, 65536⟩
    (by decide) selected_cut_34322

theorem selected_cut_34323 : selected 8 ⟨887368, by decide⟩
    (prefixPartial 13 452748) = some ⟨13, 2, 0, 887368, 452748, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_452748_887368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452748 ⟨887368, by decide⟩ :=
  accepted_of_selected 13 452748 ⟨887368, by decide⟩ ⟨13, 2, 0, 887368, 452748, 1061, 16384⟩
    (by decide) selected_cut_34323

theorem selected_cut_34324 : selected 8 ⟨887426, by decide⟩
    (prefixPartial 13 452749) = some ⟨13, 2, 0, 887426, 452749, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_452749_887426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452749 ⟨887426, by decide⟩ :=
  accepted_of_selected 13 452749 ⟨887426, by decide⟩ ⟨13, 2, 0, 887426, 452749, 2261, 16384⟩
    (by decide) selected_cut_34324

theorem selected_cut_34325 : selected 8 ⟨887444, by decide⟩
    (prefixPartial 13 452750) = some ⟨13, 2, 0, 887444, 452750, 833, 16384⟩ := by
  decide +kernel

theorem context_13_452750_887444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452750 ⟨887444, by decide⟩ :=
  accepted_of_selected 13 452750 ⟨887444, by decide⟩ ⟨13, 2, 0, 887444, 452750, 833, 16384⟩
    (by decide) selected_cut_34325

theorem selected_cut_34326 : selected 8 ⟨887451, by decide⟩
    (prefixPartial 13 452751) = some ⟨13, 2, 0, 887451, 452751, 677, 16384⟩ := by
  decide +kernel

theorem context_13_452751_887451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452751 ⟨887451, by decide⟩ :=
  accepted_of_selected 13 452751 ⟨887451, by decide⟩ ⟨13, 2, 0, 887451, 452751, 677, 16384⟩
    (by decide) selected_cut_34326

theorem unmarked_context_12_113187_887452 : frontier 9 ⟨887452, by decide⟩
    (prefixCache 12 113187) (prefixPartial 12 113187) = false := by
  decide +kernel

theorem node_context_12_113187_887452 : EJMOriginalGlobalDAGData.nodes 9 ⟨887452, by decide⟩ =
    .split (coordinate 12) (![⟨887368, by decide⟩,⟨887426, by decide⟩,⟨887444, by decide⟩,⟨887451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113187_887452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113187 ⟨887452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113187
    ⟨887452, by decide⟩ (by decide) (![⟨887368, by decide⟩,⟨887426, by decide⟩,⟨887444, by decide⟩,⟨887451, by decide⟩]) unmarked_context_12_113187_887452 node_context_12_113187_887452
  intro a
  fin_cases a
  · exact context_13_452748_887368
  · exact context_13_452749_887426
  · exact context_13_452750_887444
  · exact context_13_452751_887451

theorem unmarked_context_11_28296_887453 : frontier 10 ⟨887453, by decide⟩
    (prefixCache 11 28296) (prefixPartial 11 28296) = false := by
  decide +kernel

theorem node_context_11_28296_887453 : EJMOriginalGlobalDAGData.nodes 10 ⟨887453, by decide⟩ =
    .split (coordinate 11) (![⟨887106, by decide⟩,⟨887242, by decide⟩,⟨887342, by decide⟩,⟨887452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28296_887453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28296 ⟨887453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28296
    ⟨887453, by decide⟩ (by decide) (![⟨887106, by decide⟩,⟨887242, by decide⟩,⟨887342, by decide⟩,⟨887452, by decide⟩]) unmarked_context_11_28296_887453 node_context_11_28296_887453
  intro a
  fin_cases a
  · exact context_12_113184_887106
  · exact context_12_113185_887242
  · exact context_12_113186_887342
  · exact context_12_113187_887452

theorem selected_cut_34327 : selected 8 ⟨887478, by decide⟩
    (prefixPartial 13 452752) = some ⟨13, 2, 0, 887478, 452752, 805, 16384⟩ := by
  decide +kernel

theorem context_13_452752_887478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452752 ⟨887478, by decide⟩ :=
  accepted_of_selected 13 452752 ⟨887478, by decide⟩ ⟨13, 2, 0, 887478, 452752, 805, 16384⟩
    (by decide) selected_cut_34327

theorem selected_cut_34328 : selected 8 ⟨887540, by decide⟩
    (prefixPartial 13 452753) = some ⟨13, 2, 0, 887540, 452753, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_452753_887540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452753 ⟨887540, by decide⟩ :=
  accepted_of_selected 13 452753 ⟨887540, by decide⟩ ⟨13, 2, 0, 887540, 452753, 2317, 16384⟩
    (by decide) selected_cut_34328

theorem selected_cut_34329 : selected 8 ⟨887574, by decide⟩
    (prefixPartial 13 452754) = some ⟨13, 2, 0, 887574, 452754, 937, 16384⟩ := by
  decide +kernel

theorem context_13_452754_887574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452754 ⟨887574, by decide⟩ :=
  accepted_of_selected 13 452754 ⟨887574, by decide⟩ ⟨13, 2, 0, 887574, 452754, 937, 16384⟩
    (by decide) selected_cut_34329

theorem selected_cut_34330 : selected 8 ⟨887577, by decide⟩
    (prefixPartial 13 452755) = some ⟨13, 2, 0, 887577, 452755, 517, 16384⟩ := by
  decide +kernel

theorem context_13_452755_887577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452755 ⟨887577, by decide⟩ :=
  accepted_of_selected 13 452755 ⟨887577, by decide⟩ ⟨13, 2, 0, 887577, 452755, 517, 16384⟩
    (by decide) selected_cut_34330

theorem unmarked_context_12_113188_887578 : frontier 9 ⟨887578, by decide⟩
    (prefixCache 12 113188) (prefixPartial 12 113188) = false := by
  decide +kernel

theorem node_context_12_113188_887578 : EJMOriginalGlobalDAGData.nodes 9 ⟨887578, by decide⟩ =
    .split (coordinate 12) (![⟨887478, by decide⟩,⟨887540, by decide⟩,⟨887574, by decide⟩,⟨887577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113188_887578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113188 ⟨887578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113188
    ⟨887578, by decide⟩ (by decide) (![⟨887478, by decide⟩,⟨887540, by decide⟩,⟨887574, by decide⟩,⟨887577, by decide⟩]) unmarked_context_12_113188_887578 node_context_12_113188_887578
  intro a
  fin_cases a
  · exact context_13_452752_887478
  · exact context_13_452753_887540
  · exact context_13_452754_887574
  · exact context_13_452755_887577

theorem selected_cut_34331 : selected 8 ⟨887604, by decide⟩
    (prefixPartial 13 452756) = some ⟨13, 2, 0, 887604, 452756, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_452756_887604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452756 ⟨887604, by decide⟩ :=
  accepted_of_selected 13 452756 ⟨887604, by decide⟩ ⟨13, 2, 0, 887604, 452756, 1209, 16384⟩
    (by decide) selected_cut_34331

theorem selected_cut_34332 : selected 8 ⟨887662, by decide⟩
    (prefixPartial 13 452757) = some ⟨13, 2, 0, 887662, 452757, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_452757_887662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452757 ⟨887662, by decide⟩ :=
  accepted_of_selected 13 452757 ⟨887662, by decide⟩ ⟨13, 2, 0, 887662, 452757, 2305, 16384⟩
    (by decide) selected_cut_34332

theorem selected_cut_34333 : selected 8 ⟨887685, by decide⟩
    (prefixPartial 13 452758) = some ⟨13, 2, 0, 887685, 452758, 841, 16384⟩ := by
  decide +kernel

theorem context_13_452758_887685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452758 ⟨887685, by decide⟩ :=
  accepted_of_selected 13 452758 ⟨887685, by decide⟩ ⟨13, 2, 0, 887685, 452758, 841, 16384⟩
    (by decide) selected_cut_34333

theorem selected_cut_34334 : selected 8 ⟨887694, by decide⟩
    (prefixPartial 13 452759) = some ⟨13, 2, 0, 887694, 452759, 645, 16384⟩ := by
  decide +kernel

theorem context_13_452759_887694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452759 ⟨887694, by decide⟩ :=
  accepted_of_selected 13 452759 ⟨887694, by decide⟩ ⟨13, 2, 0, 887694, 452759, 645, 16384⟩
    (by decide) selected_cut_34334

theorem unmarked_context_12_113189_887695 : frontier 9 ⟨887695, by decide⟩
    (prefixCache 12 113189) (prefixPartial 12 113189) = false := by
  decide +kernel

theorem node_context_12_113189_887695 : EJMOriginalGlobalDAGData.nodes 9 ⟨887695, by decide⟩ =
    .split (coordinate 12) (![⟨887604, by decide⟩,⟨887662, by decide⟩,⟨887685, by decide⟩,⟨887694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113189_887695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113189 ⟨887695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113189
    ⟨887695, by decide⟩ (by decide) (![⟨887604, by decide⟩,⟨887662, by decide⟩,⟨887685, by decide⟩,⟨887694, by decide⟩]) unmarked_context_12_113189_887695 node_context_12_113189_887695
  intro a
  fin_cases a
  · exact context_13_452756_887604
  · exact context_13_452757_887662
  · exact context_13_452758_887685
  · exact context_13_452759_887694

theorem selected_cut_34335 : selected 9 ⟨887782, by decide⟩
    (prefixPartial 12 113190) = some ⟨12, 2, 0, 887782, 113190, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_113190_887782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113190 ⟨887782, by decide⟩ :=
  accepted_of_selected 12 113190 ⟨887782, by decide⟩ ⟨12, 2, 0, 887782, 113190, 3893, 65536⟩
    (by decide) selected_cut_34335

theorem selected_cut_34336 : selected 8 ⟨887809, by decide⟩
    (prefixPartial 13 452764) = some ⟨13, 2, 0, 887809, 452764, 965, 16384⟩ := by
  decide +kernel

theorem context_13_452764_887809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452764 ⟨887809, by decide⟩ :=
  accepted_of_selected 13 452764 ⟨887809, by decide⟩ ⟨13, 2, 0, 887809, 452764, 965, 16384⟩
    (by decide) selected_cut_34336

theorem selected_cut_34337 : selected 8 ⟨887866, by decide⟩
    (prefixPartial 13 452765) = some ⟨13, 2, 0, 887866, 452765, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_452765_887866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452765 ⟨887866, by decide⟩ :=
  accepted_of_selected 13 452765 ⟨887866, by decide⟩ ⟨13, 2, 0, 887866, 452765, 2129, 16384⟩
    (by decide) selected_cut_34337

theorem selected_cut_34338 : selected 8 ⟨887886, by decide⟩
    (prefixPartial 13 452766) = some ⟨13, 2, 0, 887886, 452766, 861, 16384⟩ := by
  decide +kernel

theorem context_13_452766_887886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452766 ⟨887886, by decide⟩ :=
  accepted_of_selected 13 452766 ⟨887886, by decide⟩ ⟨13, 2, 0, 887886, 452766, 861, 16384⟩
    (by decide) selected_cut_34338

theorem selected_cut_34339 : selected 8 ⟨887892, by decide⟩
    (prefixPartial 13 452767) = some ⟨13, 2, 0, 887892, 452767, 553, 16384⟩ := by
  decide +kernel

theorem context_13_452767_887892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452767 ⟨887892, by decide⟩ :=
  accepted_of_selected 13 452767 ⟨887892, by decide⟩ ⟨13, 2, 0, 887892, 452767, 553, 16384⟩
    (by decide) selected_cut_34339

theorem unmarked_context_12_113191_887893 : frontier 9 ⟨887893, by decide⟩
    (prefixCache 12 113191) (prefixPartial 12 113191) = false := by
  decide +kernel

theorem node_context_12_113191_887893 : EJMOriginalGlobalDAGData.nodes 9 ⟨887893, by decide⟩ =
    .split (coordinate 12) (![⟨887809, by decide⟩,⟨887866, by decide⟩,⟨887886, by decide⟩,⟨887892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113191_887893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113191 ⟨887893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113191
    ⟨887893, by decide⟩ (by decide) (![⟨887809, by decide⟩,⟨887866, by decide⟩,⟨887886, by decide⟩,⟨887892, by decide⟩]) unmarked_context_12_113191_887893 node_context_12_113191_887893
  intro a
  fin_cases a
  · exact context_13_452764_887809
  · exact context_13_452765_887866
  · exact context_13_452766_887886
  · exact context_13_452767_887892

theorem unmarked_context_11_28297_887894 : frontier 10 ⟨887894, by decide⟩
    (prefixCache 11 28297) (prefixPartial 11 28297) = false := by
  decide +kernel

theorem node_context_11_28297_887894 : EJMOriginalGlobalDAGData.nodes 10 ⟨887894, by decide⟩ =
    .split (coordinate 11) (![⟨887578, by decide⟩,⟨887695, by decide⟩,⟨887782, by decide⟩,⟨887893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28297_887894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28297 ⟨887894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28297
    ⟨887894, by decide⟩ (by decide) (![⟨887578, by decide⟩,⟨887695, by decide⟩,⟨887782, by decide⟩,⟨887893, by decide⟩]) unmarked_context_11_28297_887894 node_context_11_28297_887894
  intro a
  fin_cases a
  · exact context_12_113188_887578
  · exact context_12_113189_887695
  · exact context_12_113190_887782
  · exact context_12_113191_887893

theorem selected_cut_34340 : selected 10 ⟨766338, by decide⟩
    (prefixPartial 11 28298) = some ⟨11, 1, 0, 766338, 28298, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28298_766338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28298 ⟨766338, by decide⟩ :=
  accepted_of_selected 11 28298 ⟨766338, by decide⟩ ⟨11, 1, 0, 766338, 28298, 1, 262144⟩
    (by decide) selected_cut_34340

theorem selected_cut_34341 : selected 8 ⟨887909, by decide⟩
    (prefixPartial 13 452784) = some ⟨13, 2, 0, 887909, 452784, 689, 16384⟩ := by
  decide +kernel

theorem context_13_452784_887909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452784 ⟨887909, by decide⟩ :=
  accepted_of_selected 13 452784 ⟨887909, by decide⟩ ⟨13, 2, 0, 887909, 452784, 689, 16384⟩
    (by decide) selected_cut_34341

theorem selected_cut_34342 : selected 8 ⟨887961, by decide⟩
    (prefixPartial 13 452785) = some ⟨13, 2, 0, 887961, 452785, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_452785_887961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452785 ⟨887961, by decide⟩ :=
  accepted_of_selected 13 452785 ⟨887961, by decide⟩ ⟨13, 2, 0, 887961, 452785, 2457, 16384⟩
    (by decide) selected_cut_34342

theorem selected_cut_34343 : selected 8 ⟨887987, by decide⟩
    (prefixPartial 13 452786) = some ⟨13, 2, 0, 887987, 452786, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_452786_887987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452786 ⟨887987, by decide⟩ :=
  accepted_of_selected 13 452786 ⟨887987, by decide⟩ ⟨13, 2, 0, 887987, 452786, 1001, 16384⟩
    (by decide) selected_cut_34343

theorem selected_cut_34344 : selected 8 ⟨887991, by decide⟩
    (prefixPartial 13 452787) = some ⟨13, 2, 0, 887991, 452787, 605, 16384⟩ := by
  decide +kernel

theorem context_13_452787_887991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452787 ⟨887991, by decide⟩ :=
  accepted_of_selected 13 452787 ⟨887991, by decide⟩ ⟨13, 2, 0, 887991, 452787, 605, 16384⟩
    (by decide) selected_cut_34344

theorem unmarked_context_12_113196_887992 : frontier 9 ⟨887992, by decide⟩
    (prefixCache 12 113196) (prefixPartial 12 113196) = false := by
  decide +kernel

theorem node_context_12_113196_887992 : EJMOriginalGlobalDAGData.nodes 9 ⟨887992, by decide⟩ =
    .split (coordinate 12) (![⟨887909, by decide⟩,⟨887961, by decide⟩,⟨887987, by decide⟩,⟨887991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113196_887992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113196 ⟨887992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113196
    ⟨887992, by decide⟩ (by decide) (![⟨887909, by decide⟩,⟨887961, by decide⟩,⟨887987, by decide⟩,⟨887991, by decide⟩]) unmarked_context_12_113196_887992 node_context_12_113196_887992
  intro a
  fin_cases a
  · exact context_13_452784_887909
  · exact context_13_452785_887961
  · exact context_13_452786_887987
  · exact context_13_452787_887991

theorem selected_cut_34345 : selected 8 ⟨888018, by decide⟩
    (prefixPartial 13 452788) = some ⟨13, 2, 0, 888018, 452788, 837, 16384⟩ := by
  decide +kernel

theorem context_13_452788_888018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452788 ⟨888018, by decide⟩ :=
  accepted_of_selected 13 452788 ⟨888018, by decide⟩ ⟨13, 2, 0, 888018, 452788, 837, 16384⟩
    (by decide) selected_cut_34345

theorem selected_cut_34346 : selected 8 ⟨888067, by decide⟩
    (prefixPartial 13 452789) = some ⟨13, 2, 0, 888067, 452789, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_452789_888067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452789 ⟨888067, by decide⟩ :=
  accepted_of_selected 13 452789 ⟨888067, by decide⟩ ⟨13, 2, 0, 888067, 452789, 2425, 16384⟩
    (by decide) selected_cut_34346

theorem selected_cut_34347 : selected 8 ⟨888096, by decide⟩
    (prefixPartial 13 452790) = some ⟨13, 2, 0, 888096, 452790, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_452790_888096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452790 ⟨888096, by decide⟩ :=
  accepted_of_selected 13 452790 ⟨888096, by decide⟩ ⟨13, 2, 0, 888096, 452790, 1021, 16384⟩
    (by decide) selected_cut_34347

theorem selected_cut_34348 : selected 8 ⟨888106, by decide⟩
    (prefixPartial 13 452791) = some ⟨13, 2, 0, 888106, 452791, 733, 16384⟩ := by
  decide +kernel

theorem context_13_452791_888106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452791 ⟨888106, by decide⟩ :=
  accepted_of_selected 13 452791 ⟨888106, by decide⟩ ⟨13, 2, 0, 888106, 452791, 733, 16384⟩
    (by decide) selected_cut_34348

theorem unmarked_context_12_113197_888107 : frontier 9 ⟨888107, by decide⟩
    (prefixCache 12 113197) (prefixPartial 12 113197) = false := by
  decide +kernel

theorem node_context_12_113197_888107 : EJMOriginalGlobalDAGData.nodes 9 ⟨888107, by decide⟩ =
    .split (coordinate 12) (![⟨888018, by decide⟩,⟨888067, by decide⟩,⟨888096, by decide⟩,⟨888106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113197_888107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113197 ⟨888107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113197
    ⟨888107, by decide⟩ (by decide) (![⟨888018, by decide⟩,⟨888067, by decide⟩,⟨888096, by decide⟩,⟨888106, by decide⟩]) unmarked_context_12_113197_888107 node_context_12_113197_888107
  intro a
  fin_cases a
  · exact context_13_452788_888018
  · exact context_13_452789_888067
  · exact context_13_452790_888096
  · exact context_13_452791_888106

theorem selected_cut_34349 : selected 9 ⟨888192, by decide⟩
    (prefixPartial 12 113198) = some ⟨12, 2, 0, 888192, 113198, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_113198_888192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113198 ⟨888192, by decide⟩ :=
  accepted_of_selected 12 113198 ⟨888192, by decide⟩ ⟨12, 2, 0, 888192, 113198, 3837, 65536⟩
    (by decide) selected_cut_34349

theorem selected_cut_34350 : selected 8 ⟨888207, by decide⟩
    (prefixPartial 13 452796) = some ⟨13, 2, 0, 888207, 452796, 601, 16384⟩ := by
  decide +kernel

theorem context_13_452796_888207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452796 ⟨888207, by decide⟩ :=
  accepted_of_selected 13 452796 ⟨888207, by decide⟩ ⟨13, 2, 0, 888207, 452796, 601, 16384⟩
    (by decide) selected_cut_34350

theorem selected_cut_34351 : selected 8 ⟨888256, by decide⟩
    (prefixPartial 13 452797) = some ⟨13, 2, 0, 888256, 452797, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_452797_888256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452797 ⟨888256, by decide⟩ :=
  accepted_of_selected 13 452797 ⟨888256, by decide⟩ ⟨13, 2, 0, 888256, 452797, 2357, 16384⟩
    (by decide) selected_cut_34351

theorem selected_cut_34352 : selected 8 ⟨888274, by decide⟩
    (prefixPartial 13 452798) = some ⟨13, 2, 0, 888274, 452798, 837, 16384⟩ := by
  decide +kernel

theorem context_13_452798_888274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452798 ⟨888274, by decide⟩ :=
  accepted_of_selected 13 452798 ⟨888274, by decide⟩ ⟨13, 2, 0, 888274, 452798, 837, 16384⟩
    (by decide) selected_cut_34352

theorem selected_cut_34353 : selected 8 ⟨888281, by decide⟩
    (prefixPartial 13 452799) = some ⟨13, 2, 0, 888281, 452799, 645, 16384⟩ := by
  decide +kernel

theorem context_13_452799_888281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452799 ⟨888281, by decide⟩ :=
  accepted_of_selected 13 452799 ⟨888281, by decide⟩ ⟨13, 2, 0, 888281, 452799, 645, 16384⟩
    (by decide) selected_cut_34353

theorem unmarked_context_12_113199_888282 : frontier 9 ⟨888282, by decide⟩
    (prefixCache 12 113199) (prefixPartial 12 113199) = false := by
  decide +kernel

theorem node_context_12_113199_888282 : EJMOriginalGlobalDAGData.nodes 9 ⟨888282, by decide⟩ =
    .split (coordinate 12) (![⟨888207, by decide⟩,⟨888256, by decide⟩,⟨888274, by decide⟩,⟨888281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113199_888282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113199 ⟨888282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113199
    ⟨888282, by decide⟩ (by decide) (![⟨888207, by decide⟩,⟨888256, by decide⟩,⟨888274, by decide⟩,⟨888281, by decide⟩]) unmarked_context_12_113199_888282 node_context_12_113199_888282
  intro a
  fin_cases a
  · exact context_13_452796_888207
  · exact context_13_452797_888256
  · exact context_13_452798_888274
  · exact context_13_452799_888281

theorem unmarked_context_11_28299_888283 : frontier 10 ⟨888283, by decide⟩
    (prefixCache 11 28299) (prefixPartial 11 28299) = false := by
  decide +kernel

theorem node_context_11_28299_888283 : EJMOriginalGlobalDAGData.nodes 10 ⟨888283, by decide⟩ =
    .split (coordinate 11) (![⟨887992, by decide⟩,⟨888107, by decide⟩,⟨888192, by decide⟩,⟨888282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28299_888283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28299 ⟨888283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28299
    ⟨888283, by decide⟩ (by decide) (![⟨887992, by decide⟩,⟨888107, by decide⟩,⟨888192, by decide⟩,⟨888282, by decide⟩]) unmarked_context_11_28299_888283 node_context_11_28299_888283
  intro a
  fin_cases a
  · exact context_12_113196_887992
  · exact context_12_113197_888107
  · exact context_12_113198_888192
  · exact context_12_113199_888282

theorem unmarked_context_10_7074_888284 : frontier 11 ⟨888284, by decide⟩
    (prefixCache 10 7074) (prefixPartial 10 7074) = false := by
  decide +kernel

theorem node_context_10_7074_888284 : EJMOriginalGlobalDAGData.nodes 11 ⟨888284, by decide⟩ =
    .split (coordinate 10) (![⟨887453, by decide⟩,⟨887894, by decide⟩,⟨766338, by decide⟩,⟨888283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7074_888284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7074 ⟨888284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7074
    ⟨888284, by decide⟩ (by decide) (![⟨887453, by decide⟩,⟨887894, by decide⟩,⟨766338, by decide⟩,⟨888283, by decide⟩]) unmarked_context_10_7074_888284 node_context_10_7074_888284
  intro a
  fin_cases a
  · exact context_11_28296_887453
  · exact context_11_28297_887894
  · exact context_11_28298_766338
  · exact context_11_28299_888283

theorem selected_cut_34354 : selected 8 ⟨888303, by decide⟩
    (prefixPartial 13 452800) = some ⟨13, 2, 0, 888303, 452800, 833, 16384⟩ := by
  decide +kernel

theorem context_13_452800_888303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452800 ⟨888303, by decide⟩ :=
  accepted_of_selected 13 452800 ⟨888303, by decide⟩ ⟨13, 2, 0, 888303, 452800, 833, 16384⟩
    (by decide) selected_cut_34354

theorem selected_cut_34355 : selected 8 ⟨888357, by decide⟩
    (prefixPartial 13 452801) = some ⟨13, 2, 0, 888357, 452801, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_452801_888357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452801 ⟨888357, by decide⟩ :=
  accepted_of_selected 13 452801 ⟨888357, by decide⟩ ⟨13, 2, 0, 888357, 452801, 2377, 16384⟩
    (by decide) selected_cut_34355

theorem selected_cut_34356 : selected 8 ⟨888378, by decide⟩
    (prefixPartial 13 452802) = some ⟨13, 2, 0, 888378, 452802, 765, 16384⟩ := by
  decide +kernel

theorem context_13_452802_888378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452802 ⟨888378, by decide⟩ :=
  accepted_of_selected 13 452802 ⟨888378, by decide⟩ ⟨13, 2, 0, 888378, 452802, 765, 16384⟩
    (by decide) selected_cut_34356

theorem selected_cut_34357 : selected 8 ⟨888381, by decide⟩
    (prefixPartial 13 452803) = some ⟨13, 2, 0, 888381, 452803, 541, 16384⟩ := by
  decide +kernel

theorem context_13_452803_888381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452803 ⟨888381, by decide⟩ :=
  accepted_of_selected 13 452803 ⟨888381, by decide⟩ ⟨13, 2, 0, 888381, 452803, 541, 16384⟩
    (by decide) selected_cut_34357

theorem unmarked_context_12_113200_888382 : frontier 9 ⟨888382, by decide⟩
    (prefixCache 12 113200) (prefixPartial 12 113200) = false := by
  decide +kernel

theorem node_context_12_113200_888382 : EJMOriginalGlobalDAGData.nodes 9 ⟨888382, by decide⟩ =
    .split (coordinate 12) (![⟨888303, by decide⟩,⟨888357, by decide⟩,⟨888378, by decide⟩,⟨888381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113200_888382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113200 ⟨888382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113200
    ⟨888382, by decide⟩ (by decide) (![⟨888303, by decide⟩,⟨888357, by decide⟩,⟨888378, by decide⟩,⟨888381, by decide⟩]) unmarked_context_12_113200_888382 node_context_12_113200_888382
  intro a
  fin_cases a
  · exact context_13_452800_888303
  · exact context_13_452801_888357
  · exact context_13_452802_888378
  · exact context_13_452803_888381

theorem selected_cut_34358 : selected 8 ⟨888403, by decide⟩
    (prefixPartial 13 452804) = some ⟨13, 2, 0, 888403, 452804, 961, 16384⟩ := by
  decide +kernel

theorem context_13_452804_888403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452804 ⟨888403, by decide⟩ :=
  accepted_of_selected 13 452804 ⟨888403, by decide⟩ ⟨13, 2, 0, 888403, 452804, 961, 16384⟩
    (by decide) selected_cut_34358

theorem selected_cut_34359 : selected 8 ⟨888460, by decide⟩
    (prefixPartial 13 452805) = some ⟨13, 2, 0, 888460, 452805, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_452805_888460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452805 ⟨888460, by decide⟩ :=
  accepted_of_selected 13 452805 ⟨888460, by decide⟩ ⟨13, 2, 0, 888460, 452805, 2769, 16384⟩
    (by decide) selected_cut_34359

theorem selected_cut_34360 : selected 8 ⟨888480, by decide⟩
    (prefixPartial 13 452806) = some ⟨13, 2, 0, 888480, 452806, 809, 16384⟩ := by
  decide +kernel

theorem context_13_452806_888480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452806 ⟨888480, by decide⟩ :=
  accepted_of_selected 13 452806 ⟨888480, by decide⟩ ⟨13, 2, 0, 888480, 452806, 809, 16384⟩
    (by decide) selected_cut_34360

theorem selected_cut_34361 : selected 8 ⟨888487, by decide⟩
    (prefixPartial 13 452807) = some ⟨13, 2, 0, 888487, 452807, 765, 16384⟩ := by
  decide +kernel

theorem context_13_452807_888487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452807 ⟨888487, by decide⟩ :=
  accepted_of_selected 13 452807 ⟨888487, by decide⟩ ⟨13, 2, 0, 888487, 452807, 765, 16384⟩
    (by decide) selected_cut_34361

theorem unmarked_context_12_113201_888488 : frontier 9 ⟨888488, by decide⟩
    (prefixCache 12 113201) (prefixPartial 12 113201) = false := by
  decide +kernel

theorem node_context_12_113201_888488 : EJMOriginalGlobalDAGData.nodes 9 ⟨888488, by decide⟩ =
    .split (coordinate 12) (![⟨888403, by decide⟩,⟨888460, by decide⟩,⟨888480, by decide⟩,⟨888487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113201_888488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113201 ⟨888488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113201
    ⟨888488, by decide⟩ (by decide) (![⟨888403, by decide⟩,⟨888460, by decide⟩,⟨888480, by decide⟩,⟨888487, by decide⟩]) unmarked_context_12_113201_888488 node_context_12_113201_888488
  intro a
  fin_cases a
  · exact context_13_452804_888403
  · exact context_13_452805_888460
  · exact context_13_452806_888480
  · exact context_13_452807_888487

theorem selected_cut_34362 : selected 9 ⟨888566, by decide⟩
    (prefixPartial 12 113202) = some ⟨12, 2, 0, 888566, 113202, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_113202_888566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113202 ⟨888566, by decide⟩ :=
  accepted_of_selected 12 113202 ⟨888566, by decide⟩ ⟨12, 2, 0, 888566, 113202, 4037, 65536⟩
    (by decide) selected_cut_34362

theorem selected_cut_34363 : selected 8 ⟨888581, by decide⟩
    (prefixPartial 13 452812) = some ⟨13, 2, 0, 888581, 452812, 677, 16384⟩ := by
  decide +kernel

theorem context_13_452812_888581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452812 ⟨888581, by decide⟩ :=
  accepted_of_selected 13 452812 ⟨888581, by decide⟩ ⟨13, 2, 0, 888581, 452812, 677, 16384⟩
    (by decide) selected_cut_34363

theorem selected_cut_34364 : selected 8 ⟨888636, by decide⟩
    (prefixPartial 13 452813) = some ⟨13, 2, 0, 888636, 452813, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_452813_888636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452813 ⟨888636, by decide⟩ :=
  accepted_of_selected 13 452813 ⟨888636, by decide⟩ ⟨13, 2, 0, 888636, 452813, 2369, 16384⟩
    (by decide) selected_cut_34364

theorem selected_cut_34365 : selected 8 ⟨888656, by decide⟩
    (prefixPartial 13 452814) = some ⟨13, 2, 0, 888656, 452814, 809, 16384⟩ := by
  decide +kernel

theorem context_13_452814_888656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452814 ⟨888656, by decide⟩ :=
  accepted_of_selected 13 452814 ⟨888656, by decide⟩ ⟨13, 2, 0, 888656, 452814, 809, 16384⟩
    (by decide) selected_cut_34365

theorem selected_cut_34366 : selected 8 ⟨888662, by decide⟩
    (prefixPartial 13 452815) = some ⟨13, 2, 0, 888662, 452815, 657, 16384⟩ := by
  decide +kernel

theorem context_13_452815_888662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452815 ⟨888662, by decide⟩ :=
  accepted_of_selected 13 452815 ⟨888662, by decide⟩ ⟨13, 2, 0, 888662, 452815, 657, 16384⟩
    (by decide) selected_cut_34366

theorem unmarked_context_12_113203_888663 : frontier 9 ⟨888663, by decide⟩
    (prefixCache 12 113203) (prefixPartial 12 113203) = false := by
  decide +kernel

theorem node_context_12_113203_888663 : EJMOriginalGlobalDAGData.nodes 9 ⟨888663, by decide⟩ =
    .split (coordinate 12) (![⟨888581, by decide⟩,⟨888636, by decide⟩,⟨888656, by decide⟩,⟨888662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113203_888663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113203 ⟨888663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113203
    ⟨888663, by decide⟩ (by decide) (![⟨888581, by decide⟩,⟨888636, by decide⟩,⟨888656, by decide⟩,⟨888662, by decide⟩]) unmarked_context_12_113203_888663 node_context_12_113203_888663
  intro a
  fin_cases a
  · exact context_13_452812_888581
  · exact context_13_452813_888636
  · exact context_13_452814_888656
  · exact context_13_452815_888662

theorem unmarked_context_11_28300_888664 : frontier 10 ⟨888664, by decide⟩
    (prefixCache 11 28300) (prefixPartial 11 28300) = false := by
  decide +kernel

theorem node_context_11_28300_888664 : EJMOriginalGlobalDAGData.nodes 10 ⟨888664, by decide⟩ =
    .split (coordinate 11) (![⟨888382, by decide⟩,⟨888488, by decide⟩,⟨888566, by decide⟩,⟨888663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28300_888664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28300 ⟨888664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28300
    ⟨888664, by decide⟩ (by decide) (![⟨888382, by decide⟩,⟨888488, by decide⟩,⟨888566, by decide⟩,⟨888663, by decide⟩]) unmarked_context_11_28300_888664 node_context_11_28300_888664
  intro a
  fin_cases a
  · exact context_12_113200_888382
  · exact context_12_113201_888488
  · exact context_12_113202_888566
  · exact context_12_113203_888663

theorem selected_cut_34367 : selected 8 ⟨888677, by decide⟩
    (prefixPartial 13 452816) = some ⟨13, 2, 0, 888677, 452816, 617, 16384⟩ := by
  decide +kernel

theorem context_13_452816_888677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452816 ⟨888677, by decide⟩ :=
  accepted_of_selected 13 452816 ⟨888677, by decide⟩ ⟨13, 2, 0, 888677, 452816, 617, 16384⟩
    (by decide) selected_cut_34367

theorem selected_cut_34368 : selected 8 ⟨888740, by decide⟩
    (prefixPartial 13 452817) = some ⟨13, 2, 0, 888740, 452817, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_452817_888740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452817 ⟨888740, by decide⟩ :=
  accepted_of_selected 13 452817 ⟨888740, by decide⟩ ⟨13, 2, 0, 888740, 452817, 2185, 16384⟩
    (by decide) selected_cut_34368

theorem selected_cut_34369 : selected 8 ⟨888759, by decide⟩
    (prefixPartial 13 452818) = some ⟨13, 2, 0, 888759, 452818, 769, 16384⟩ := by
  decide +kernel

theorem context_13_452818_888759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452818 ⟨888759, by decide⟩ :=
  accepted_of_selected 13 452818 ⟨888759, by decide⟩ ⟨13, 2, 0, 888759, 452818, 769, 16384⟩
    (by decide) selected_cut_34369

theorem selected_cut_34370 : selected 8 ⟨888764, by decide⟩
    (prefixPartial 13 452819) = some ⟨13, 2, 0, 888764, 452819, 529, 16384⟩ := by
  decide +kernel

theorem context_13_452819_888764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452819 ⟨888764, by decide⟩ :=
  accepted_of_selected 13 452819 ⟨888764, by decide⟩ ⟨13, 2, 0, 888764, 452819, 529, 16384⟩
    (by decide) selected_cut_34370

theorem unmarked_context_12_113204_888765 : frontier 9 ⟨888765, by decide⟩
    (prefixCache 12 113204) (prefixPartial 12 113204) = false := by
  decide +kernel

theorem node_context_12_113204_888765 : EJMOriginalGlobalDAGData.nodes 9 ⟨888765, by decide⟩ =
    .split (coordinate 12) (![⟨888677, by decide⟩,⟨888740, by decide⟩,⟨888759, by decide⟩,⟨888764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113204_888765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113204 ⟨888765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113204
    ⟨888765, by decide⟩ (by decide) (![⟨888677, by decide⟩,⟨888740, by decide⟩,⟨888759, by decide⟩,⟨888764, by decide⟩]) unmarked_context_12_113204_888765 node_context_12_113204_888765
  intro a
  fin_cases a
  · exact context_13_452816_888677
  · exact context_13_452817_888740
  · exact context_13_452818_888759
  · exact context_13_452819_888764

theorem selected_cut_34371 : selected 8 ⟨888783, by decide⟩
    (prefixPartial 13 452820) = some ⟨13, 2, 0, 888783, 452820, 733, 16384⟩ := by
  decide +kernel

theorem context_13_452820_888783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452820 ⟨888783, by decide⟩ :=
  accepted_of_selected 13 452820 ⟨888783, by decide⟩ ⟨13, 2, 0, 888783, 452820, 733, 16384⟩
    (by decide) selected_cut_34371

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
