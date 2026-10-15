/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover497
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_47811 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23397) = some ⟨10, 1, 0, 893098, 23397, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23397_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23397 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23397 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23397, 1, 1048576⟩
    (by decide) selected_cut_47811

theorem selected_cut_47812 : selected 10 ⟨1339111, by decide⟩
    (prefixPartial 11 93592) = some ⟨11, 2, 0, 1339111, 93592, 3189, 262144⟩ := by
  decide +kernel

theorem context_11_93592_1339111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93592 ⟨1339111, by decide⟩ :=
  accepted_of_selected 11 93592 ⟨1339111, by decide⟩ ⟨11, 2, 0, 1339111, 93592, 3189, 262144⟩
    (by decide) selected_cut_47812

theorem selected_cut_47813 : selected 9 ⟨1339143, by decide⟩
    (prefixPartial 12 374372) = some ⟨12, 2, 0, 1339143, 374372, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_374372_1339143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374372 ⟨1339143, by decide⟩ :=
  accepted_of_selected 12 374372 ⟨1339143, by decide⟩ ⟨12, 2, 0, 1339143, 374372, 1465, 65536⟩
    (by decide) selected_cut_47813

theorem selected_cut_47814 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 374373) = some ⟨12, 1, 0, 1256866, 374373, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374373_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374373 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 374373 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 374373, 1, 65536⟩
    (by decide) selected_cut_47814

theorem selected_cut_47815 : selected 9 ⟨1339167, by decide⟩
    (prefixPartial 12 374374) = some ⟨12, 2, 0, 1339167, 374374, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_374374_1339167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374374 ⟨1339167, by decide⟩ :=
  accepted_of_selected 12 374374 ⟨1339167, by decide⟩ ⟨12, 2, 0, 1339167, 374374, 1361, 65536⟩
    (by decide) selected_cut_47815

theorem selected_cut_47816 : selected 9 ⟨1339187, by decide⟩
    (prefixPartial 12 374375) = some ⟨12, 2, 0, 1339187, 374375, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_374375_1339187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374375 ⟨1339187, by decide⟩ :=
  accepted_of_selected 12 374375 ⟨1339187, by decide⟩ ⟨12, 2, 0, 1339187, 374375, 1377, 65536⟩
    (by decide) selected_cut_47816

theorem unmarked_context_11_93593_1339188 : frontier 10 ⟨1339188, by decide⟩
    (prefixCache 11 93593) (prefixPartial 11 93593) = false := by
  decide +kernel

theorem node_context_11_93593_1339188 : EJMOriginalGlobalDAGData.nodes 10 ⟨1339188, by decide⟩ =
    .split (coordinate 11) (![⟨1339143, by decide⟩,⟨1256866, by decide⟩,⟨1339167, by decide⟩,⟨1339187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93593_1339188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93593 ⟨1339188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93593
    ⟨1339188, by decide⟩ (by decide) (![⟨1339143, by decide⟩,⟨1256866, by decide⟩,⟨1339167, by decide⟩,⟨1339187, by decide⟩]) unmarked_context_11_93593_1339188 node_context_11_93593_1339188
  intro a
  fin_cases a
  · exact context_12_374372_1339143
  · exact context_12_374373_1256866
  · exact context_12_374374_1339167
  · exact context_12_374375_1339187

theorem selected_cut_47817 : selected 10 ⟨1283737, by decide⟩
    (prefixPartial 11 93594) = some ⟨11, 1, 0, 1283737, 93594, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93594_1283737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93594 ⟨1283737, by decide⟩ :=
  accepted_of_selected 11 93594 ⟨1283737, by decide⟩ ⟨11, 1, 0, 1283737, 93594, 1, 262144⟩
    (by decide) selected_cut_47817

theorem selected_cut_47818 : selected 10 ⟨1339248, by decide⟩
    (prefixPartial 11 93595) = some ⟨11, 2, 0, 1339248, 93595, 2949, 262144⟩ := by
  decide +kernel

theorem context_11_93595_1339248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93595 ⟨1339248, by decide⟩ :=
  accepted_of_selected 11 93595 ⟨1339248, by decide⟩ ⟨11, 2, 0, 1339248, 93595, 2949, 262144⟩
    (by decide) selected_cut_47818

theorem unmarked_context_10_23398_1339249 : frontier 11 ⟨1339249, by decide⟩
    (prefixCache 10 23398) (prefixPartial 10 23398) = false := by
  decide +kernel

theorem node_context_10_23398_1339249 : EJMOriginalGlobalDAGData.nodes 11 ⟨1339249, by decide⟩ =
    .split (coordinate 10) (![⟨1339111, by decide⟩,⟨1339188, by decide⟩,⟨1283737, by decide⟩,⟨1339248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23398_1339249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23398 ⟨1339249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23398
    ⟨1339249, by decide⟩ (by decide) (![⟨1339111, by decide⟩,⟨1339188, by decide⟩,⟨1283737, by decide⟩,⟨1339248, by decide⟩]) unmarked_context_10_23398_1339249 node_context_10_23398_1339249
  intro a
  fin_cases a
  · exact context_11_93592_1339111
  · exact context_11_93593_1339188
  · exact context_11_93594_1283737
  · exact context_11_93595_1339248

theorem selected_cut_47819 : selected 9 ⟨1339269, by decide⟩
    (prefixPartial 12 374384) = some ⟨12, 2, 0, 1339269, 374384, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_374384_1339269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374384 ⟨1339269, by decide⟩ :=
  accepted_of_selected 12 374384 ⟨1339269, by decide⟩ ⟨12, 2, 0, 1339269, 374384, 1209, 65536⟩
    (by decide) selected_cut_47819

theorem selected_cut_47820 : selected 9 ⟨1339284, by decide⟩
    (prefixPartial 12 374385) = some ⟨12, 2, 0, 1339284, 374385, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_374385_1339284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374385 ⟨1339284, by decide⟩ :=
  accepted_of_selected 12 374385 ⟨1339284, by decide⟩ ⟨12, 2, 0, 1339284, 374385, 1065, 65536⟩
    (by decide) selected_cut_47820

theorem selected_cut_47821 : selected 9 ⟨1339302, by decide⟩
    (prefixPartial 12 374386) = some ⟨12, 2, 0, 1339302, 374386, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_374386_1339302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374386 ⟨1339302, by decide⟩ :=
  accepted_of_selected 12 374386 ⟨1339302, by decide⟩ ⟨12, 2, 0, 1339302, 374386, 1085, 65536⟩
    (by decide) selected_cut_47821

theorem selected_cut_47822 : selected 9 ⟨1339331, by decide⟩
    (prefixPartial 12 374387) = some ⟨12, 2, 0, 1339331, 374387, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_374387_1339331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374387 ⟨1339331, by decide⟩ :=
  accepted_of_selected 12 374387 ⟨1339331, by decide⟩ ⟨12, 2, 0, 1339331, 374387, 1233, 65536⟩
    (by decide) selected_cut_47822

theorem unmarked_context_11_93596_1339332 : frontier 10 ⟨1339332, by decide⟩
    (prefixCache 11 93596) (prefixPartial 11 93596) = false := by
  decide +kernel

theorem node_context_11_93596_1339332 : EJMOriginalGlobalDAGData.nodes 10 ⟨1339332, by decide⟩ =
    .split (coordinate 11) (![⟨1339269, by decide⟩,⟨1339284, by decide⟩,⟨1339302, by decide⟩,⟨1339331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93596_1339332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93596 ⟨1339332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93596
    ⟨1339332, by decide⟩ (by decide) (![⟨1339269, by decide⟩,⟨1339284, by decide⟩,⟨1339302, by decide⟩,⟨1339331, by decide⟩]) unmarked_context_11_93596_1339332 node_context_11_93596_1339332
  intro a
  fin_cases a
  · exact context_12_374384_1339269
  · exact context_12_374385_1339284
  · exact context_12_374386_1339302
  · exact context_12_374387_1339331

theorem selected_cut_47823 : selected 10 ⟨1339377, by decide⟩
    (prefixPartial 11 93597) = some ⟨11, 2, 0, 1339377, 93597, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_93597_1339377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93597 ⟨1339377, by decide⟩ :=
  accepted_of_selected 11 93597 ⟨1339377, by decide⟩ ⟨11, 2, 0, 1339377, 93597, 2825, 262144⟩
    (by decide) selected_cut_47823

theorem selected_cut_47824 : selected 10 ⟨1339412, by decide⟩
    (prefixPartial 11 93598) = some ⟨11, 2, 0, 1339412, 93598, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_93598_1339412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93598 ⟨1339412, by decide⟩ :=
  accepted_of_selected 11 93598 ⟨1339412, by decide⟩ ⟨11, 2, 0, 1339412, 93598, 2085, 262144⟩
    (by decide) selected_cut_47824

theorem selected_cut_47825 : selected 10 ⟨1284138, by decide⟩
    (prefixPartial 11 93599) = some ⟨11, 1, 0, 1284138, 93599, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93599_1284138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93599 ⟨1284138, by decide⟩ :=
  accepted_of_selected 11 93599 ⟨1284138, by decide⟩ ⟨11, 1, 0, 1284138, 93599, 1, 262144⟩
    (by decide) selected_cut_47825

theorem unmarked_context_10_23399_1339413 : frontier 11 ⟨1339413, by decide⟩
    (prefixCache 10 23399) (prefixPartial 10 23399) = false := by
  decide +kernel

theorem node_context_10_23399_1339413 : EJMOriginalGlobalDAGData.nodes 11 ⟨1339413, by decide⟩ =
    .split (coordinate 10) (![⟨1339332, by decide⟩,⟨1339377, by decide⟩,⟨1339412, by decide⟩,⟨1284138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23399_1339413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23399 ⟨1339413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23399
    ⟨1339413, by decide⟩ (by decide) (![⟨1339332, by decide⟩,⟨1339377, by decide⟩,⟨1339412, by decide⟩,⟨1284138, by decide⟩]) unmarked_context_10_23399_1339413 node_context_10_23399_1339413
  intro a
  fin_cases a
  · exact context_11_93596_1339332
  · exact context_11_93597_1339377
  · exact context_11_93598_1339412
  · exact context_11_93599_1284138

theorem unmarked_context_9_5849_1339414 : frontier 12 ⟨1339414, by decide⟩
    (prefixCache 9 5849) (prefixPartial 9 5849) = false := by
  decide +kernel

theorem node_context_9_5849_1339414 : EJMOriginalGlobalDAGData.nodes 12 ⟨1339414, by decide⟩ =
    .split (coordinate 9) (![⟨1339051, by decide⟩,⟨893098, by decide⟩,⟨1339249, by decide⟩,⟨1339413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5849_1339414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5849 ⟨1339414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5849
    ⟨1339414, by decide⟩ (by decide) (![⟨1339051, by decide⟩,⟨893098, by decide⟩,⟨1339249, by decide⟩,⟨1339413, by decide⟩]) unmarked_context_9_5849_1339414 node_context_9_5849_1339414
  intro a
  fin_cases a
  · exact context_10_23396_1339051
  · exact context_10_23397_893098
  · exact context_10_23398_1339249
  · exact context_10_23399_1339413

theorem selected_cut_47826 : selected 10 ⟨1339434, by decide⟩
    (prefixPartial 11 93600) = some ⟨11, 2, 0, 1339434, 93600, 1001, 262144⟩ := by
  decide +kernel

theorem context_11_93600_1339434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93600 ⟨1339434, by decide⟩ :=
  accepted_of_selected 11 93600 ⟨1339434, by decide⟩ ⟨11, 2, 0, 1339434, 93600, 1001, 262144⟩
    (by decide) selected_cut_47826

theorem selected_cut_47827 : selected 10 ⟨1339474, by decide⟩
    (prefixPartial 11 93601) = some ⟨11, 2, 0, 1339474, 93601, 1997, 262144⟩ := by
  decide +kernel

theorem context_11_93601_1339474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93601 ⟨1339474, by decide⟩ :=
  accepted_of_selected 11 93601 ⟨1339474, by decide⟩ ⟨11, 2, 0, 1339474, 93601, 1997, 262144⟩
    (by decide) selected_cut_47827

theorem selected_cut_47828 : selected 10 ⟨1339514, by decide⟩
    (prefixPartial 11 93602) = some ⟨11, 2, 0, 1339514, 93602, 2573, 262144⟩ := by
  decide +kernel

theorem context_11_93602_1339514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93602 ⟨1339514, by decide⟩ :=
  accepted_of_selected 11 93602 ⟨1339514, by decide⟩ ⟨11, 2, 0, 1339514, 93602, 2573, 262144⟩
    (by decide) selected_cut_47828

theorem selected_cut_47829 : selected 10 ⟨1339551, by decide⟩
    (prefixPartial 11 93603) = some ⟨11, 2, 0, 1339551, 93603, 1813, 262144⟩ := by
  decide +kernel

theorem context_11_93603_1339551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93603 ⟨1339551, by decide⟩ :=
  accepted_of_selected 11 93603 ⟨1339551, by decide⟩ ⟨11, 2, 0, 1339551, 93603, 1813, 262144⟩
    (by decide) selected_cut_47829

theorem unmarked_context_10_23400_1339552 : frontier 11 ⟨1339552, by decide⟩
    (prefixCache 10 23400) (prefixPartial 10 23400) = false := by
  decide +kernel

theorem node_context_10_23400_1339552 : EJMOriginalGlobalDAGData.nodes 11 ⟨1339552, by decide⟩ =
    .split (coordinate 10) (![⟨1339434, by decide⟩,⟨1339474, by decide⟩,⟨1339514, by decide⟩,⟨1339551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23400_1339552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23400 ⟨1339552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23400
    ⟨1339552, by decide⟩ (by decide) (![⟨1339434, by decide⟩,⟨1339474, by decide⟩,⟨1339514, by decide⟩,⟨1339551, by decide⟩]) unmarked_context_10_23400_1339552 node_context_10_23400_1339552
  intro a
  fin_cases a
  · exact context_11_93600_1339434
  · exact context_11_93601_1339474
  · exact context_11_93602_1339514
  · exact context_11_93603_1339551

theorem selected_cut_47830 : selected 10 ⟨1339581, by decide⟩
    (prefixPartial 11 93604) = some ⟨11, 2, 0, 1339581, 93604, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_93604_1339581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93604 ⟨1339581, by decide⟩ :=
  accepted_of_selected 11 93604 ⟨1339581, by decide⟩ ⟨11, 2, 0, 1339581, 93604, 1517, 262144⟩
    (by decide) selected_cut_47830

theorem selected_cut_47831 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93605) = some ⟨11, 1, 0, 892405, 93605, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93605_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93605 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93605 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93605, 1, 262144⟩
    (by decide) selected_cut_47831

theorem selected_cut_47832 : selected 10 ⟨1339615, by decide⟩
    (prefixPartial 11 93606) = some ⟨11, 2, 0, 1339615, 93606, 1989, 262144⟩ := by
  decide +kernel

theorem context_11_93606_1339615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93606 ⟨1339615, by decide⟩ :=
  accepted_of_selected 11 93606 ⟨1339615, by decide⟩ ⟨11, 2, 0, 1339615, 93606, 1989, 262144⟩
    (by decide) selected_cut_47832

theorem selected_cut_47833 : selected 10 ⟨1339641, by decide⟩
    (prefixPartial 11 93607) = some ⟨11, 2, 0, 1339641, 93607, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_93607_1339641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93607 ⟨1339641, by decide⟩ :=
  accepted_of_selected 11 93607 ⟨1339641, by decide⟩ ⟨11, 2, 0, 1339641, 93607, 1401, 262144⟩
    (by decide) selected_cut_47833

theorem unmarked_context_10_23401_1339642 : frontier 11 ⟨1339642, by decide⟩
    (prefixCache 10 23401) (prefixPartial 10 23401) = false := by
  decide +kernel

theorem node_context_10_23401_1339642 : EJMOriginalGlobalDAGData.nodes 11 ⟨1339642, by decide⟩ =
    .split (coordinate 10) (![⟨1339581, by decide⟩,⟨892405, by decide⟩,⟨1339615, by decide⟩,⟨1339641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23401_1339642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23401 ⟨1339642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23401
    ⟨1339642, by decide⟩ (by decide) (![⟨1339581, by decide⟩,⟨892405, by decide⟩,⟨1339615, by decide⟩,⟨1339641, by decide⟩]) unmarked_context_10_23401_1339642 node_context_10_23401_1339642
  intro a
  fin_cases a
  · exact context_11_93604_1339581
  · exact context_11_93605_892405
  · exact context_11_93606_1339615
  · exact context_11_93607_1339641

theorem selected_cut_47834 : selected 11 ⟨1339664, by decide⟩
    (prefixPartial 10 23402) = some ⟨10, 2, 0, 1339664, 23402, 1249, 1048576⟩ := by
  decide +kernel

theorem context_10_23402_1339664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23402 ⟨1339664, by decide⟩ :=
  accepted_of_selected 10 23402 ⟨1339664, by decide⟩ ⟨10, 2, 0, 1339664, 23402, 1249, 1048576⟩
    (by decide) selected_cut_47834

theorem selected_cut_47835 : selected 11 ⟨1339725, by decide⟩
    (prefixPartial 10 23403) = some ⟨10, 2, 0, 1339725, 23403, 3749, 1048576⟩ := by
  decide +kernel

theorem context_10_23403_1339725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23403 ⟨1339725, by decide⟩ :=
  accepted_of_selected 10 23403 ⟨1339725, by decide⟩ ⟨10, 2, 0, 1339725, 23403, 3749, 1048576⟩
    (by decide) selected_cut_47835

theorem unmarked_context_9_5850_1339726 : frontier 12 ⟨1339726, by decide⟩
    (prefixCache 9 5850) (prefixPartial 9 5850) = false := by
  decide +kernel

theorem node_context_9_5850_1339726 : EJMOriginalGlobalDAGData.nodes 12 ⟨1339726, by decide⟩ =
    .split (coordinate 9) (![⟨1339552, by decide⟩,⟨1339642, by decide⟩,⟨1339664, by decide⟩,⟨1339725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5850_1339726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5850 ⟨1339726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5850
    ⟨1339726, by decide⟩ (by decide) (![⟨1339552, by decide⟩,⟨1339642, by decide⟩,⟨1339664, by decide⟩,⟨1339725, by decide⟩]) unmarked_context_9_5850_1339726 node_context_9_5850_1339726
  intro a
  fin_cases a
  · exact context_10_23400_1339552
  · exact context_10_23401_1339642
  · exact context_10_23402_1339664
  · exact context_10_23403_1339725

theorem selected_cut_47836 : selected 10 ⟨1339753, by decide⟩
    (prefixPartial 11 93616) = some ⟨11, 2, 0, 1339753, 93616, 1057, 262144⟩ := by
  decide +kernel

theorem context_11_93616_1339753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93616 ⟨1339753, by decide⟩ :=
  accepted_of_selected 11 93616 ⟨1339753, by decide⟩ ⟨11, 2, 0, 1339753, 93616, 1057, 262144⟩
    (by decide) selected_cut_47836

theorem selected_cut_47837 : selected 10 ⟨1339782, by decide⟩
    (prefixPartial 11 93617) = some ⟨11, 2, 0, 1339782, 93617, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_93617_1339782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93617 ⟨1339782, by decide⟩ :=
  accepted_of_selected 11 93617 ⟨1339782, by decide⟩ ⟨11, 2, 0, 1339782, 93617, 1705, 262144⟩
    (by decide) selected_cut_47837

theorem selected_cut_47838 : selected 10 ⟨1339792, by decide⟩
    (prefixPartial 11 93618) = some ⟨11, 2, 0, 1339792, 93618, 701, 262144⟩ := by
  decide +kernel

theorem context_11_93618_1339792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93618 ⟨1339792, by decide⟩ :=
  accepted_of_selected 11 93618 ⟨1339792, by decide⟩ ⟨11, 2, 0, 1339792, 93618, 701, 262144⟩
    (by decide) selected_cut_47838

theorem selected_cut_47839 : selected 10 ⟨1339819, by decide⟩
    (prefixPartial 11 93619) = some ⟨11, 2, 0, 1339819, 93619, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_93619_1339819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93619 ⟨1339819, by decide⟩ :=
  accepted_of_selected 11 93619 ⟨1339819, by decide⟩ ⟨11, 2, 0, 1339819, 93619, 1093, 262144⟩
    (by decide) selected_cut_47839

theorem unmarked_context_10_23404_1339820 : frontier 11 ⟨1339820, by decide⟩
    (prefixCache 10 23404) (prefixPartial 10 23404) = false := by
  decide +kernel

theorem node_context_10_23404_1339820 : EJMOriginalGlobalDAGData.nodes 11 ⟨1339820, by decide⟩ =
    .split (coordinate 10) (![⟨1339753, by decide⟩,⟨1339782, by decide⟩,⟨1339792, by decide⟩,⟨1339819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23404_1339820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23404 ⟨1339820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23404
    ⟨1339820, by decide⟩ (by decide) (![⟨1339753, by decide⟩,⟨1339782, by decide⟩,⟨1339792, by decide⟩,⟨1339819, by decide⟩]) unmarked_context_10_23404_1339820 node_context_10_23404_1339820
  intro a
  fin_cases a
  · exact context_11_93616_1339753
  · exact context_11_93617_1339782
  · exact context_11_93618_1339792
  · exact context_11_93619_1339819

theorem selected_cut_47840 : selected 11 ⟨1339859, by decide⟩
    (prefixPartial 10 23405) = some ⟨10, 2, 0, 1339859, 23405, 1977, 1048576⟩ := by
  decide +kernel

theorem context_10_23405_1339859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23405 ⟨1339859, by decide⟩ :=
  accepted_of_selected 10 23405 ⟨1339859, by decide⟩ ⟨10, 2, 0, 1339859, 23405, 1977, 1048576⟩
    (by decide) selected_cut_47840

theorem selected_cut_47841 : selected 11 ⟨1339886, by decide⟩
    (prefixPartial 10 23406) = some ⟨10, 2, 0, 1339886, 23406, 809, 1048576⟩ := by
  decide +kernel

theorem context_10_23406_1339886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23406 ⟨1339886, by decide⟩ :=
  accepted_of_selected 10 23406 ⟨1339886, by decide⟩ ⟨10, 2, 0, 1339886, 23406, 809, 1048576⟩
    (by decide) selected_cut_47841

theorem selected_cut_47842 : selected 11 ⟨1339894, by decide⟩
    (prefixPartial 10 23407) = some ⟨10, 2, 0, 1339894, 23407, 113, 1048576⟩ := by
  decide +kernel

theorem context_10_23407_1339894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23407 ⟨1339894, by decide⟩ :=
  accepted_of_selected 10 23407 ⟨1339894, by decide⟩ ⟨10, 2, 0, 1339894, 23407, 113, 1048576⟩
    (by decide) selected_cut_47842

theorem unmarked_context_9_5851_1339895 : frontier 12 ⟨1339895, by decide⟩
    (prefixCache 9 5851) (prefixPartial 9 5851) = false := by
  decide +kernel

theorem node_context_9_5851_1339895 : EJMOriginalGlobalDAGData.nodes 12 ⟨1339895, by decide⟩ =
    .split (coordinate 9) (![⟨1339820, by decide⟩,⟨1339859, by decide⟩,⟨1339886, by decide⟩,⟨1339894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5851_1339895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5851 ⟨1339895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5851
    ⟨1339895, by decide⟩ (by decide) (![⟨1339820, by decide⟩,⟨1339859, by decide⟩,⟨1339886, by decide⟩,⟨1339894, by decide⟩]) unmarked_context_9_5851_1339895 node_context_9_5851_1339895
  intro a
  fin_cases a
  · exact context_10_23404_1339820
  · exact context_10_23405_1339859
  · exact context_10_23406_1339886
  · exact context_10_23407_1339894

theorem unmarked_context_8_1462_1339896 : frontier 13 ⟨1339896, by decide⟩
    (prefixCache 8 1462) (prefixPartial 8 1462) = false := by
  decide +kernel

theorem node_context_8_1462_1339896 : EJMOriginalGlobalDAGData.nodes 13 ⟨1339896, by decide⟩ =
    .split (coordinate 8) (![⟨1338683, by decide⟩,⟨1339414, by decide⟩,⟨1339726, by decide⟩,⟨1339895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1462_1339896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1462 ⟨1339896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1462
    ⟨1339896, by decide⟩ (by decide) (![⟨1338683, by decide⟩,⟨1339414, by decide⟩,⟨1339726, by decide⟩,⟨1339895, by decide⟩]) unmarked_context_8_1462_1339896 node_context_8_1462_1339896
  intro a
  fin_cases a
  · exact context_9_5848_1338683
  · exact context_9_5849_1339414
  · exact context_9_5850_1339726
  · exact context_9_5851_1339895

theorem selected_cut_47843 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93632) = some ⟨11, 1, 0, 434745, 93632, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93632_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93632 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93632 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93632, 1, 262144⟩
    (by decide) selected_cut_47843

theorem selected_cut_47844 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 93633) = some ⟨11, 1, 0, 167448, 93633, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93633_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93633 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 93633 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 93633, 1, 262144⟩
    (by decide) selected_cut_47844

theorem selected_cut_47845 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 374536) = some ⟨12, 1, 0, 448748, 374536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374536_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374536 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 374536 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 374536, 1, 65536⟩
    (by decide) selected_cut_47845

theorem selected_cut_47846 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 374537) = some ⟨12, 1, 0, 34034, 374537, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374537_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374537 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 374537 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 374537, 1, 65536⟩
    (by decide) selected_cut_47846

theorem selected_cut_47847 : selected 9 ⟨1339962, by decide⟩
    (prefixPartial 12 374538) = some ⟨12, 2, 0, 1339962, 374538, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_374538_1339962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374538 ⟨1339962, by decide⟩ :=
  accepted_of_selected 12 374538 ⟨1339962, by decide⟩ ⟨12, 2, 0, 1339962, 374538, 2941, 65536⟩
    (by decide) selected_cut_47847

theorem selected_cut_47848 : selected 9 ⟨1340013, by decide⟩
    (prefixPartial 12 374539) = some ⟨12, 2, 0, 1340013, 374539, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_374539_1340013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374539 ⟨1340013, by decide⟩ :=
  accepted_of_selected 12 374539 ⟨1340013, by decide⟩ ⟨12, 2, 0, 1340013, 374539, 2869, 65536⟩
    (by decide) selected_cut_47848

theorem unmarked_context_11_93634_1340014 : frontier 10 ⟨1340014, by decide⟩
    (prefixCache 11 93634) (prefixPartial 11 93634) = false := by
  decide +kernel

theorem node_context_11_93634_1340014 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340014, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1339962, by decide⟩,⟨1340013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93634_1340014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93634 ⟨1340014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93634
    ⟨1340014, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1339962, by decide⟩,⟨1340013, by decide⟩]) unmarked_context_11_93634_1340014 node_context_11_93634_1340014
  intro a
  fin_cases a
  · exact context_12_374536_448748
  · exact context_12_374537_34034
  · exact context_12_374538_1339962
  · exact context_12_374539_1340013

theorem selected_cut_47849 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 374540) = some ⟨12, 1, 0, 448748, 374540, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374540_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374540 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 374540 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 374540, 1, 65536⟩
    (by decide) selected_cut_47849

theorem selected_cut_47850 : selected 9 ⟨1340068, by decide⟩
    (prefixPartial 12 374541) = some ⟨12, 2, 0, 1340068, 374541, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_374541_1340068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374541 ⟨1340068, by decide⟩ :=
  accepted_of_selected 12 374541 ⟨1340068, by decide⟩ ⟨12, 2, 0, 1340068, 374541, 2605, 65536⟩
    (by decide) selected_cut_47850

theorem selected_cut_47851 : selected 9 ⟨1340130, by decide⟩
    (prefixPartial 12 374542) = some ⟨12, 2, 0, 1340130, 374542, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_374542_1340130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374542 ⟨1340130, by decide⟩ :=
  accepted_of_selected 12 374542 ⟨1340130, by decide⟩ ⟨12, 2, 0, 1340130, 374542, 2929, 65536⟩
    (by decide) selected_cut_47851

theorem selected_cut_47852 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 374543) = some ⟨12, 1, 0, 903806, 374543, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374543_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374543 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 374543 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 374543, 1, 65536⟩
    (by decide) selected_cut_47852

theorem unmarked_context_11_93635_1340131 : frontier 10 ⟨1340131, by decide⟩
    (prefixCache 11 93635) (prefixPartial 11 93635) = false := by
  decide +kernel

theorem node_context_11_93635_1340131 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340131, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1340068, by decide⟩,⟨1340130, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93635_1340131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93635 ⟨1340131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93635
    ⟨1340131, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1340068, by decide⟩,⟨1340130, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93635_1340131 node_context_11_93635_1340131
  intro a
  fin_cases a
  · exact context_12_374540_448748
  · exact context_12_374541_1340068
  · exact context_12_374542_1340130
  · exact context_12_374543_903806

theorem unmarked_context_10_23408_1340132 : frontier 11 ⟨1340132, by decide⟩
    (prefixCache 10 23408) (prefixPartial 10 23408) = false := by
  decide +kernel

theorem node_context_10_23408_1340132 : EJMOriginalGlobalDAGData.nodes 11 ⟨1340132, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1340014, by decide⟩,⟨1340131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23408_1340132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23408 ⟨1340132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23408
    ⟨1340132, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1340014, by decide⟩,⟨1340131, by decide⟩]) unmarked_context_10_23408_1340132 node_context_10_23408_1340132
  intro a
  fin_cases a
  · exact context_11_93632_434745
  · exact context_11_93633_167448
  · exact context_11_93634_1340014
  · exact context_11_93635_1340131

theorem selected_cut_47853 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 374544) = some ⟨12, 1, 0, 1255011, 374544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374544_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374544 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 374544 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 374544, 1, 65536⟩
    (by decide) selected_cut_47853

theorem selected_cut_47854 : selected 9 ⟨1340167, by decide⟩
    (prefixPartial 12 374545) = some ⟨12, 2, 0, 1340167, 374545, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_374545_1340167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374545 ⟨1340167, by decide⟩ :=
  accepted_of_selected 12 374545 ⟨1340167, by decide⟩ ⟨12, 2, 0, 1340167, 374545, 2157, 65536⟩
    (by decide) selected_cut_47854

theorem selected_cut_47855 : selected 9 ⟨1340213, by decide⟩
    (prefixPartial 12 374546) = some ⟨12, 2, 0, 1340213, 374546, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_374546_1340213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374546 ⟨1340213, by decide⟩ :=
  accepted_of_selected 12 374546 ⟨1340213, by decide⟩ ⟨12, 2, 0, 1340213, 374546, 2489, 65536⟩
    (by decide) selected_cut_47855

theorem selected_cut_47856 : selected 9 ⟨1340255, by decide⟩
    (prefixPartial 12 374547) = some ⟨12, 2, 0, 1340255, 374547, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_374547_1340255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374547 ⟨1340255, by decide⟩ :=
  accepted_of_selected 12 374547 ⟨1340255, by decide⟩ ⟨12, 2, 0, 1340255, 374547, 2377, 65536⟩
    (by decide) selected_cut_47856

theorem unmarked_context_11_93636_1340256 : frontier 10 ⟨1340256, by decide⟩
    (prefixCache 11 93636) (prefixPartial 11 93636) = false := by
  decide +kernel

theorem node_context_11_93636_1340256 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340256, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1340167, by decide⟩,⟨1340213, by decide⟩,⟨1340255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93636_1340256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93636 ⟨1340256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93636
    ⟨1340256, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1340167, by decide⟩,⟨1340213, by decide⟩,⟨1340255, by decide⟩]) unmarked_context_11_93636_1340256 node_context_11_93636_1340256
  intro a
  fin_cases a
  · exact context_12_374544_1255011
  · exact context_12_374545_1340167
  · exact context_12_374546_1340213
  · exact context_12_374547_1340255

theorem selected_cut_47857 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93637) = some ⟨11, 1, 0, 892405, 93637, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93637_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93637 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93637 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93637, 1, 262144⟩
    (by decide) selected_cut_47857

theorem selected_cut_47858 : selected 9 ⟨1340308, by decide⟩
    (prefixPartial 12 374552) = some ⟨12, 2, 0, 1340308, 374552, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_374552_1340308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374552 ⟨1340308, by decide⟩ :=
  accepted_of_selected 12 374552 ⟨1340308, by decide⟩ ⟨12, 2, 0, 1340308, 374552, 2705, 65536⟩
    (by decide) selected_cut_47858

theorem selected_cut_47859 : selected 9 ⟨1340338, by decide⟩
    (prefixPartial 12 374553) = some ⟨12, 2, 0, 1340338, 374553, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_374553_1340338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374553 ⟨1340338, by decide⟩ :=
  accepted_of_selected 12 374553 ⟨1340338, by decide⟩ ⟨12, 2, 0, 1340338, 374553, 2073, 65536⟩
    (by decide) selected_cut_47859

theorem selected_cut_47860 : selected 9 ⟨1340379, by decide⟩
    (prefixPartial 12 374554) = some ⟨12, 2, 0, 1340379, 374554, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_374554_1340379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374554 ⟨1340379, by decide⟩ :=
  accepted_of_selected 12 374554 ⟨1340379, by decide⟩ ⟨12, 2, 0, 1340379, 374554, 2397, 65536⟩
    (by decide) selected_cut_47860

theorem selected_cut_47861 : selected 9 ⟨1340425, by decide⟩
    (prefixPartial 12 374555) = some ⟨12, 2, 0, 1340425, 374555, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_374555_1340425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374555 ⟨1340425, by decide⟩ :=
  accepted_of_selected 12 374555 ⟨1340425, by decide⟩ ⟨12, 2, 0, 1340425, 374555, 2497, 65536⟩
    (by decide) selected_cut_47861

theorem unmarked_context_11_93638_1340426 : frontier 10 ⟨1340426, by decide⟩
    (prefixCache 11 93638) (prefixPartial 11 93638) = false := by
  decide +kernel

theorem node_context_11_93638_1340426 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340426, by decide⟩ =
    .split (coordinate 11) (![⟨1340308, by decide⟩,⟨1340338, by decide⟩,⟨1340379, by decide⟩,⟨1340425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93638_1340426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93638 ⟨1340426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93638
    ⟨1340426, by decide⟩ (by decide) (![⟨1340308, by decide⟩,⟨1340338, by decide⟩,⟨1340379, by decide⟩,⟨1340425, by decide⟩]) unmarked_context_11_93638_1340426 node_context_11_93638_1340426
  intro a
  fin_cases a
  · exact context_12_374552_1340308
  · exact context_12_374553_1340338
  · exact context_12_374554_1340379
  · exact context_12_374555_1340425

theorem selected_cut_47862 : selected 9 ⟨1340471, by decide⟩
    (prefixPartial 12 374556) = some ⟨12, 2, 0, 1340471, 374556, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_374556_1340471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374556 ⟨1340471, by decide⟩ :=
  accepted_of_selected 12 374556 ⟨1340471, by decide⟩ ⟨12, 2, 0, 1340471, 374556, 2577, 65536⟩
    (by decide) selected_cut_47862

theorem selected_cut_47863 : selected 9 ⟨1340508, by decide⟩
    (prefixPartial 12 374557) = some ⟨12, 2, 0, 1340508, 374557, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_374557_1340508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374557 ⟨1340508, by decide⟩ :=
  accepted_of_selected 12 374557 ⟨1340508, by decide⟩ ⟨12, 2, 0, 1340508, 374557, 2037, 65536⟩
    (by decide) selected_cut_47863

theorem selected_cut_47864 : selected 9 ⟨1340548, by decide⟩
    (prefixPartial 12 374558) = some ⟨12, 2, 0, 1340548, 374558, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_374558_1340548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374558 ⟨1340548, by decide⟩ :=
  accepted_of_selected 12 374558 ⟨1340548, by decide⟩ ⟨12, 2, 0, 1340548, 374558, 2305, 65536⟩
    (by decide) selected_cut_47864

theorem selected_cut_47865 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 374559) = some ⟨12, 1, 0, 903806, 374559, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374559_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374559 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 374559 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 374559, 1, 65536⟩
    (by decide) selected_cut_47865

theorem unmarked_context_11_93639_1340549 : frontier 10 ⟨1340549, by decide⟩
    (prefixCache 11 93639) (prefixPartial 11 93639) = false := by
  decide +kernel

theorem node_context_11_93639_1340549 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340549, by decide⟩ =
    .split (coordinate 11) (![⟨1340471, by decide⟩,⟨1340508, by decide⟩,⟨1340548, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93639_1340549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93639 ⟨1340549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93639
    ⟨1340549, by decide⟩ (by decide) (![⟨1340471, by decide⟩,⟨1340508, by decide⟩,⟨1340548, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93639_1340549 node_context_11_93639_1340549
  intro a
  fin_cases a
  · exact context_12_374556_1340471
  · exact context_12_374557_1340508
  · exact context_12_374558_1340548
  · exact context_12_374559_903806

theorem unmarked_context_10_23409_1340550 : frontier 11 ⟨1340550, by decide⟩
    (prefixCache 10 23409) (prefixPartial 10 23409) = false := by
  decide +kernel

theorem node_context_10_23409_1340550 : EJMOriginalGlobalDAGData.nodes 11 ⟨1340550, by decide⟩ =
    .split (coordinate 10) (![⟨1340256, by decide⟩,⟨892405, by decide⟩,⟨1340426, by decide⟩,⟨1340549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23409_1340550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23409 ⟨1340550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23409
    ⟨1340550, by decide⟩ (by decide) (![⟨1340256, by decide⟩,⟨892405, by decide⟩,⟨1340426, by decide⟩,⟨1340549, by decide⟩]) unmarked_context_10_23409_1340550 node_context_10_23409_1340550
  intro a
  fin_cases a
  · exact context_11_93636_1340256
  · exact context_11_93637_892405
  · exact context_11_93638_1340426
  · exact context_11_93639_1340549

theorem selected_cut_47866 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374560) = some ⟨12, 1, 0, 435790, 374560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374560_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374560 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374560 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374560, 1, 65536⟩
    (by decide) selected_cut_47866

theorem selected_cut_47867 : selected 9 ⟨1340581, by decide⟩
    (prefixPartial 12 374561) = some ⟨12, 2, 0, 1340581, 374561, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_374561_1340581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374561 ⟨1340581, by decide⟩ :=
  accepted_of_selected 12 374561 ⟨1340581, by decide⟩ ⟨12, 2, 0, 1340581, 374561, 2037, 65536⟩
    (by decide) selected_cut_47867

theorem selected_cut_47868 : selected 9 ⟨1340626, by decide⟩
    (prefixPartial 12 374562) = some ⟨12, 2, 0, 1340626, 374562, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_374562_1340626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374562 ⟨1340626, by decide⟩ :=
  accepted_of_selected 12 374562 ⟨1340626, by decide⟩ ⟨12, 2, 0, 1340626, 374562, 2429, 65536⟩
    (by decide) selected_cut_47868

theorem selected_cut_47869 : selected 9 ⟨1340663, by decide⟩
    (prefixPartial 12 374563) = some ⟨12, 2, 0, 1340663, 374563, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_374563_1340663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374563 ⟨1340663, by decide⟩ :=
  accepted_of_selected 12 374563 ⟨1340663, by decide⟩ ⟨12, 2, 0, 1340663, 374563, 2273, 65536⟩
    (by decide) selected_cut_47869

theorem unmarked_context_11_93640_1340664 : frontier 10 ⟨1340664, by decide⟩
    (prefixCache 11 93640) (prefixPartial 11 93640) = false := by
  decide +kernel

theorem node_context_11_93640_1340664 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340664, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1340581, by decide⟩,⟨1340626, by decide⟩,⟨1340663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93640_1340664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93640 ⟨1340664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93640
    ⟨1340664, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1340581, by decide⟩,⟨1340626, by decide⟩,⟨1340663, by decide⟩]) unmarked_context_11_93640_1340664 node_context_11_93640_1340664
  intro a
  fin_cases a
  · exact context_12_374560_435790
  · exact context_12_374561_1340581
  · exact context_12_374562_1340626
  · exact context_12_374563_1340663

theorem selected_cut_47870 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374564) = some ⟨12, 1, 0, 435790, 374564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374564_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374564 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374564 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374564, 1, 65536⟩
    (by decide) selected_cut_47870

theorem selected_cut_47871 : selected 9 ⟨1340696, by decide⟩
    (prefixPartial 12 374565) = some ⟨12, 2, 0, 1340696, 374565, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_374565_1340696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374565 ⟨1340696, by decide⟩ :=
  accepted_of_selected 12 374565 ⟨1340696, by decide⟩ ⟨12, 2, 0, 1340696, 374565, 2121, 65536⟩
    (by decide) selected_cut_47871

theorem selected_cut_47872 : selected 9 ⟨1340741, by decide⟩
    (prefixPartial 12 374566) = some ⟨12, 2, 0, 1340741, 374566, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_374566_1340741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374566 ⟨1340741, by decide⟩ :=
  accepted_of_selected 12 374566 ⟨1340741, by decide⟩ ⟨12, 2, 0, 1340741, 374566, 2505, 65536⟩
    (by decide) selected_cut_47872

theorem selected_cut_47873 : selected 9 ⟨1340776, by decide⟩
    (prefixPartial 12 374567) = some ⟨12, 2, 0, 1340776, 374567, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_374567_1340776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374567 ⟨1340776, by decide⟩ :=
  accepted_of_selected 12 374567 ⟨1340776, by decide⟩ ⟨12, 2, 0, 1340776, 374567, 2157, 65536⟩
    (by decide) selected_cut_47873

theorem unmarked_context_11_93641_1340777 : frontier 10 ⟨1340777, by decide⟩
    (prefixCache 11 93641) (prefixPartial 11 93641) = false := by
  decide +kernel

theorem node_context_11_93641_1340777 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340777, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1340696, by decide⟩,⟨1340741, by decide⟩,⟨1340776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93641_1340777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93641 ⟨1340777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93641
    ⟨1340777, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1340696, by decide⟩,⟨1340741, by decide⟩,⟨1340776, by decide⟩]) unmarked_context_11_93641_1340777 node_context_11_93641_1340777
  intro a
  fin_cases a
  · exact context_12_374564_435790
  · exact context_12_374565_1340696
  · exact context_12_374566_1340741
  · exact context_12_374567_1340776

theorem selected_cut_47874 : selected 10 ⟨1340816, by decide⟩
    (prefixPartial 11 93642) = some ⟨11, 2, 0, 1340816, 93642, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_93642_1340816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93642 ⟨1340816, by decide⟩ :=
  accepted_of_selected 11 93642 ⟨1340816, by decide⟩ ⟨11, 2, 0, 1340816, 93642, 2165, 262144⟩
    (by decide) selected_cut_47874

theorem selected_cut_47875 : selected 9 ⟨1340866, by decide⟩
    (prefixPartial 12 374572) = some ⟨12, 2, 0, 1340866, 374572, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_374572_1340866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374572 ⟨1340866, by decide⟩ :=
  accepted_of_selected 12 374572 ⟨1340866, by decide⟩ ⟨12, 2, 0, 1340866, 374572, 2361, 65536⟩
    (by decide) selected_cut_47875

theorem selected_cut_47876 : selected 9 ⟨1340904, by decide⟩
    (prefixPartial 12 374573) = some ⟨12, 2, 0, 1340904, 374573, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_374573_1340904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374573 ⟨1340904, by decide⟩ :=
  accepted_of_selected 12 374573 ⟨1340904, by decide⟩ ⟨12, 2, 0, 1340904, 374573, 1965, 65536⟩
    (by decide) selected_cut_47876

theorem selected_cut_47877 : selected 9 ⟨1340952, by decide⟩
    (prefixPartial 12 374574) = some ⟨12, 2, 0, 1340952, 374574, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_374574_1340952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374574 ⟨1340952, by decide⟩ :=
  accepted_of_selected 12 374574 ⟨1340952, by decide⟩ ⟨12, 2, 0, 1340952, 374574, 2261, 65536⟩
    (by decide) selected_cut_47877

theorem selected_cut_47878 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 374575) = some ⟨12, 1, 0, 903806, 374575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374575_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374575 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 374575 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 374575, 1, 65536⟩
    (by decide) selected_cut_47878

theorem unmarked_context_11_93643_1340953 : frontier 10 ⟨1340953, by decide⟩
    (prefixCache 11 93643) (prefixPartial 11 93643) = false := by
  decide +kernel

theorem node_context_11_93643_1340953 : EJMOriginalGlobalDAGData.nodes 10 ⟨1340953, by decide⟩ =
    .split (coordinate 11) (![⟨1340866, by decide⟩,⟨1340904, by decide⟩,⟨1340952, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93643_1340953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93643 ⟨1340953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93643
    ⟨1340953, by decide⟩ (by decide) (![⟨1340866, by decide⟩,⟨1340904, by decide⟩,⟨1340952, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93643_1340953 node_context_11_93643_1340953
  intro a
  fin_cases a
  · exact context_12_374572_1340866
  · exact context_12_374573_1340904
  · exact context_12_374574_1340952
  · exact context_12_374575_903806

theorem unmarked_context_10_23410_1340954 : frontier 11 ⟨1340954, by decide⟩
    (prefixCache 10 23410) (prefixPartial 10 23410) = false := by
  decide +kernel

theorem node_context_10_23410_1340954 : EJMOriginalGlobalDAGData.nodes 11 ⟨1340954, by decide⟩ =
    .split (coordinate 10) (![⟨1340664, by decide⟩,⟨1340777, by decide⟩,⟨1340816, by decide⟩,⟨1340953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23410_1340954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23410 ⟨1340954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23410
    ⟨1340954, by decide⟩ (by decide) (![⟨1340664, by decide⟩,⟨1340777, by decide⟩,⟨1340816, by decide⟩,⟨1340953, by decide⟩]) unmarked_context_10_23410_1340954 node_context_10_23410_1340954
  intro a
  fin_cases a
  · exact context_11_93640_1340664
  · exact context_11_93641_1340777
  · exact context_11_93642_1340816
  · exact context_11_93643_1340953

theorem selected_cut_47879 : selected 9 ⟨399079, by decide⟩
    (prefixPartial 12 374576) = some ⟨12, 1, 0, 399079, 374576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374576_399079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374576 ⟨399079, by decide⟩ :=
  accepted_of_selected 12 374576 ⟨399079, by decide⟩ ⟨12, 1, 0, 399079, 374576, 1, 65536⟩
    (by decide) selected_cut_47879

theorem selected_cut_47880 : selected 9 ⟨1340980, by decide⟩
    (prefixPartial 12 374577) = some ⟨12, 2, 0, 1340980, 374577, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_374577_1340980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374577 ⟨1340980, by decide⟩ :=
  accepted_of_selected 12 374577 ⟨1340980, by decide⟩ ⟨12, 2, 0, 1340980, 374577, 1849, 65536⟩
    (by decide) selected_cut_47880

theorem selected_cut_47881 : selected 9 ⟨1341018, by decide⟩
    (prefixPartial 12 374578) = some ⟨12, 2, 0, 1341018, 374578, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_374578_1341018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374578 ⟨1341018, by decide⟩ :=
  accepted_of_selected 12 374578 ⟨1341018, by decide⟩ ⟨12, 2, 0, 1341018, 374578, 2161, 65536⟩
    (by decide) selected_cut_47881

theorem selected_cut_47882 : selected 9 ⟨1341050, by decide⟩
    (prefixPartial 12 374579) = some ⟨12, 2, 0, 1341050, 374579, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_374579_1341050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374579 ⟨1341050, by decide⟩ :=
  accepted_of_selected 12 374579 ⟨1341050, by decide⟩ ⟨12, 2, 0, 1341050, 374579, 1989, 65536⟩
    (by decide) selected_cut_47882

theorem unmarked_context_11_93644_1341051 : frontier 10 ⟨1341051, by decide⟩
    (prefixCache 11 93644) (prefixPartial 11 93644) = false := by
  decide +kernel

theorem node_context_11_93644_1341051 : EJMOriginalGlobalDAGData.nodes 10 ⟨1341051, by decide⟩ =
    .split (coordinate 11) (![⟨399079, by decide⟩,⟨1340980, by decide⟩,⟨1341018, by decide⟩,⟨1341050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93644_1341051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93644 ⟨1341051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93644
    ⟨1341051, by decide⟩ (by decide) (![⟨399079, by decide⟩,⟨1340980, by decide⟩,⟨1341018, by decide⟩,⟨1341050, by decide⟩]) unmarked_context_11_93644_1341051 node_context_11_93644_1341051
  intro a
  fin_cases a
  · exact context_12_374576_399079
  · exact context_12_374577_1340980
  · exact context_12_374578_1341018
  · exact context_12_374579_1341050

theorem selected_cut_47883 : selected 9 ⟨1341091, by decide⟩
    (prefixPartial 12 374580) = some ⟨12, 2, 0, 1341091, 374580, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_374580_1341091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374580 ⟨1341091, by decide⟩ :=
  accepted_of_selected 12 374580 ⟨1341091, by decide⟩ ⟨12, 2, 0, 1341091, 374580, 2177, 65536⟩
    (by decide) selected_cut_47883

theorem selected_cut_47884 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 374581) = some ⟨12, 1, 0, 689956, 374581, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374581_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374581 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 374581 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 374581, 1, 65536⟩
    (by decide) selected_cut_47884

theorem selected_cut_47885 : selected 9 ⟨1341131, by decide⟩
    (prefixPartial 12 374582) = some ⟨12, 2, 0, 1341131, 374582, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_374582_1341131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374582 ⟨1341131, by decide⟩ :=
  accepted_of_selected 12 374582 ⟨1341131, by decide⟩ ⟨12, 2, 0, 1341131, 374582, 2013, 65536⟩
    (by decide) selected_cut_47885

theorem selected_cut_47886 : selected 9 ⟨1341169, by decide⟩
    (prefixPartial 12 374583) = some ⟨12, 2, 0, 1341169, 374583, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_374583_1341169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374583 ⟨1341169, by decide⟩ :=
  accepted_of_selected 12 374583 ⟨1341169, by decide⟩ ⟨12, 2, 0, 1341169, 374583, 1821, 65536⟩
    (by decide) selected_cut_47886

theorem unmarked_context_11_93645_1341170 : frontier 10 ⟨1341170, by decide⟩
    (prefixCache 11 93645) (prefixPartial 11 93645) = false := by
  decide +kernel

theorem node_context_11_93645_1341170 : EJMOriginalGlobalDAGData.nodes 10 ⟨1341170, by decide⟩ =
    .split (coordinate 11) (![⟨1341091, by decide⟩,⟨689956, by decide⟩,⟨1341131, by decide⟩,⟨1341169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93645_1341170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93645 ⟨1341170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93645
    ⟨1341170, by decide⟩ (by decide) (![⟨1341091, by decide⟩,⟨689956, by decide⟩,⟨1341131, by decide⟩,⟨1341169, by decide⟩]) unmarked_context_11_93645_1341170 node_context_11_93645_1341170
  intro a
  fin_cases a
  · exact context_12_374580_1341091
  · exact context_12_374581_689956
  · exact context_12_374582_1341131
  · exact context_12_374583_1341169

theorem selected_cut_47887 : selected 10 ⟨1341232, by decide⟩
    (prefixPartial 11 93646) = some ⟨11, 2, 0, 1341232, 93646, 3697, 262144⟩ := by
  decide +kernel

theorem context_11_93646_1341232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93646 ⟨1341232, by decide⟩ :=
  accepted_of_selected 11 93646 ⟨1341232, by decide⟩ ⟨11, 2, 0, 1341232, 93646, 3697, 262144⟩
    (by decide) selected_cut_47887

theorem selected_cut_47888 : selected 10 ⟨1341301, by decide⟩
    (prefixPartial 11 93647) = some ⟨11, 2, 0, 1341301, 93647, 3733, 262144⟩ := by
  decide +kernel

theorem context_11_93647_1341301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93647 ⟨1341301, by decide⟩ :=
  accepted_of_selected 11 93647 ⟨1341301, by decide⟩ ⟨11, 2, 0, 1341301, 93647, 3733, 262144⟩
    (by decide) selected_cut_47888

theorem unmarked_context_10_23411_1341302 : frontier 11 ⟨1341302, by decide⟩
    (prefixCache 10 23411) (prefixPartial 10 23411) = false := by
  decide +kernel

theorem node_context_10_23411_1341302 : EJMOriginalGlobalDAGData.nodes 11 ⟨1341302, by decide⟩ =
    .split (coordinate 10) (![⟨1341051, by decide⟩,⟨1341170, by decide⟩,⟨1341232, by decide⟩,⟨1341301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23411_1341302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23411 ⟨1341302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23411
    ⟨1341302, by decide⟩ (by decide) (![⟨1341051, by decide⟩,⟨1341170, by decide⟩,⟨1341232, by decide⟩,⟨1341301, by decide⟩]) unmarked_context_10_23411_1341302 node_context_10_23411_1341302
  intro a
  fin_cases a
  · exact context_11_93644_1341051
  · exact context_11_93645_1341170
  · exact context_11_93646_1341232
  · exact context_11_93647_1341301

theorem unmarked_context_9_5852_1341303 : frontier 12 ⟨1341303, by decide⟩
    (prefixCache 9 5852) (prefixPartial 9 5852) = false := by
  decide +kernel

theorem node_context_9_5852_1341303 : EJMOriginalGlobalDAGData.nodes 12 ⟨1341303, by decide⟩ =
    .split (coordinate 9) (![⟨1340132, by decide⟩,⟨1340550, by decide⟩,⟨1340954, by decide⟩,⟨1341302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5852_1341303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5852 ⟨1341303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5852
    ⟨1341303, by decide⟩ (by decide) (![⟨1340132, by decide⟩,⟨1340550, by decide⟩,⟨1340954, by decide⟩,⟨1341302, by decide⟩]) unmarked_context_9_5852_1341303 node_context_9_5852_1341303
  intro a
  fin_cases a
  · exact context_10_23408_1340132
  · exact context_10_23409_1340550
  · exact context_10_23410_1340954
  · exact context_10_23411_1341302

theorem selected_cut_47889 : selected 10 ⟨1283168, by decide⟩
    (prefixPartial 11 93648) = some ⟨11, 1, 0, 1283168, 93648, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93648_1283168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93648 ⟨1283168, by decide⟩ :=
  accepted_of_selected 11 93648 ⟨1283168, by decide⟩ ⟨11, 1, 0, 1283168, 93648, 1, 262144⟩
    (by decide) selected_cut_47889

theorem selected_cut_47890 : selected 9 ⟨1341355, by decide⟩
    (prefixPartial 12 374596) = some ⟨12, 2, 0, 1341355, 374596, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_374596_1341355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374596 ⟨1341355, by decide⟩ :=
  accepted_of_selected 12 374596 ⟨1341355, by decide⟩ ⟨12, 2, 0, 1341355, 374596, 2017, 65536⟩
    (by decide) selected_cut_47890

theorem selected_cut_47891 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 374597) = some ⟨12, 1, 0, 1257136, 374597, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374597_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374597 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 374597 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 374597, 1, 65536⟩
    (by decide) selected_cut_47891

theorem selected_cut_47892 : selected 9 ⟨1341391, by decide⟩
    (prefixPartial 12 374598) = some ⟨12, 2, 0, 1341391, 374598, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_374598_1341391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374598 ⟨1341391, by decide⟩ :=
  accepted_of_selected 12 374598 ⟨1341391, by decide⟩ ⟨12, 2, 0, 1341391, 374598, 1817, 65536⟩
    (by decide) selected_cut_47892

theorem selected_cut_47893 : selected 9 ⟨1341425, by decide⟩
    (prefixPartial 12 374599) = some ⟨12, 2, 0, 1341425, 374599, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_374599_1341425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374599 ⟨1341425, by decide⟩ :=
  accepted_of_selected 12 374599 ⟨1341425, by decide⟩ ⟨12, 2, 0, 1341425, 374599, 1825, 65536⟩
    (by decide) selected_cut_47893

theorem unmarked_context_11_93649_1341426 : frontier 10 ⟨1341426, by decide⟩
    (prefixCache 11 93649) (prefixPartial 11 93649) = false := by
  decide +kernel

theorem node_context_11_93649_1341426 : EJMOriginalGlobalDAGData.nodes 10 ⟨1341426, by decide⟩ =
    .split (coordinate 11) (![⟨1341355, by decide⟩,⟨1257136, by decide⟩,⟨1341391, by decide⟩,⟨1341425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93649_1341426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93649 ⟨1341426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93649
    ⟨1341426, by decide⟩ (by decide) (![⟨1341355, by decide⟩,⟨1257136, by decide⟩,⟨1341391, by decide⟩,⟨1341425, by decide⟩]) unmarked_context_11_93649_1341426 node_context_11_93649_1341426
  intro a
  fin_cases a
  · exact context_12_374596_1341355
  · exact context_12_374597_1257136
  · exact context_12_374598_1341391
  · exact context_12_374599_1341425

theorem selected_cut_47894 : selected 9 ⟨1341469, by decide⟩
    (prefixPartial 12 374600) = some ⟨12, 2, 0, 1341469, 374600, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_374600_1341469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374600 ⟨1341469, by decide⟩ :=
  accepted_of_selected 12 374600 ⟨1341469, by decide⟩ ⟨12, 2, 0, 1341469, 374600, 2005, 65536⟩
    (by decide) selected_cut_47894

theorem selected_cut_47895 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 374601) = some ⟨12, 1, 0, 1025817, 374601, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374601_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374601 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 374601 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 374601, 1, 65536⟩
    (by decide) selected_cut_47895

theorem selected_cut_47896 : selected 9 ⟨1341506, by decide⟩
    (prefixPartial 12 374602) = some ⟨12, 2, 0, 1341506, 374602, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_374602_1341506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374602 ⟨1341506, by decide⟩ :=
  accepted_of_selected 12 374602 ⟨1341506, by decide⟩ ⟨12, 2, 0, 1341506, 374602, 1837, 65536⟩
    (by decide) selected_cut_47896

theorem selected_cut_47897 : selected 9 ⟨1341543, by decide⟩
    (prefixPartial 12 374603) = some ⟨12, 2, 0, 1341543, 374603, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_374603_1341543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374603 ⟨1341543, by decide⟩ :=
  accepted_of_selected 12 374603 ⟨1341543, by decide⟩ ⟨12, 2, 0, 1341543, 374603, 1921, 65536⟩
    (by decide) selected_cut_47897

theorem unmarked_context_11_93650_1341544 : frontier 10 ⟨1341544, by decide⟩
    (prefixCache 11 93650) (prefixPartial 11 93650) = false := by
  decide +kernel

theorem node_context_11_93650_1341544 : EJMOriginalGlobalDAGData.nodes 10 ⟨1341544, by decide⟩ =
    .split (coordinate 11) (![⟨1341469, by decide⟩,⟨1025817, by decide⟩,⟨1341506, by decide⟩,⟨1341543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93650_1341544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93650 ⟨1341544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93650
    ⟨1341544, by decide⟩ (by decide) (![⟨1341469, by decide⟩,⟨1025817, by decide⟩,⟨1341506, by decide⟩,⟨1341543, by decide⟩]) unmarked_context_11_93650_1341544 node_context_11_93650_1341544
  intro a
  fin_cases a
  · exact context_12_374600_1341469
  · exact context_12_374601_1025817
  · exact context_12_374602_1341506
  · exact context_12_374603_1341543

theorem selected_cut_47898 : selected 9 ⟨1341572, by decide⟩
    (prefixPartial 12 374604) = some ⟨12, 2, 0, 1341572, 374604, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_374604_1341572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374604 ⟨1341572, by decide⟩ :=
  accepted_of_selected 12 374604 ⟨1341572, by decide⟩ ⟨12, 2, 0, 1341572, 374604, 1761, 65536⟩
    (by decide) selected_cut_47898

theorem selected_cut_47899 : selected 9 ⟨1341599, by decide⟩
    (prefixPartial 12 374605) = some ⟨12, 2, 0, 1341599, 374605, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_374605_1341599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374605 ⟨1341599, by decide⟩ :=
  accepted_of_selected 12 374605 ⟨1341599, by decide⟩ ⟨12, 2, 0, 1341599, 374605, 1433, 65536⟩
    (by decide) selected_cut_47899

theorem selected_cut_47900 : selected 9 ⟨1341629, by decide⟩
    (prefixPartial 12 374606) = some ⟨12, 2, 0, 1341629, 374606, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_374606_1341629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374606 ⟨1341629, by decide⟩ :=
  accepted_of_selected 12 374606 ⟨1341629, by decide⟩ ⟨12, 2, 0, 1341629, 374606, 1725, 65536⟩
    (by decide) selected_cut_47900

theorem selected_cut_47901 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 374607) = some ⟨12, 1, 0, 903806, 374607, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374607_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374607 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 374607 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 374607, 1, 65536⟩
    (by decide) selected_cut_47901

theorem unmarked_context_11_93651_1341630 : frontier 10 ⟨1341630, by decide⟩
    (prefixCache 11 93651) (prefixPartial 11 93651) = false := by
  decide +kernel

theorem node_context_11_93651_1341630 : EJMOriginalGlobalDAGData.nodes 10 ⟨1341630, by decide⟩ =
    .split (coordinate 11) (![⟨1341572, by decide⟩,⟨1341599, by decide⟩,⟨1341629, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93651_1341630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93651 ⟨1341630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93651
    ⟨1341630, by decide⟩ (by decide) (![⟨1341572, by decide⟩,⟨1341599, by decide⟩,⟨1341629, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93651_1341630 node_context_11_93651_1341630
  intro a
  fin_cases a
  · exact context_12_374604_1341572
  · exact context_12_374605_1341599
  · exact context_12_374606_1341629
  · exact context_12_374607_903806

theorem unmarked_context_10_23412_1341631 : frontier 11 ⟨1341631, by decide⟩
    (prefixCache 10 23412) (prefixPartial 10 23412) = false := by
  decide +kernel

theorem node_context_10_23412_1341631 : EJMOriginalGlobalDAGData.nodes 11 ⟨1341631, by decide⟩ =
    .split (coordinate 10) (![⟨1283168, by decide⟩,⟨1341426, by decide⟩,⟨1341544, by decide⟩,⟨1341630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23412_1341631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23412 ⟨1341631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23412
    ⟨1341631, by decide⟩ (by decide) (![⟨1283168, by decide⟩,⟨1341426, by decide⟩,⟨1341544, by decide⟩,⟨1341630, by decide⟩]) unmarked_context_10_23412_1341631 node_context_10_23412_1341631
  intro a
  fin_cases a
  · exact context_11_93648_1283168
  · exact context_11_93649_1341426
  · exact context_11_93650_1341544
  · exact context_11_93651_1341630

theorem selected_cut_47902 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23413) = some ⟨10, 1, 0, 893098, 23413, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23413_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23413 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23413 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23413, 1, 1048576⟩
    (by decide) selected_cut_47902

theorem selected_cut_47903 : selected 9 ⟨1341653, by decide⟩
    (prefixPartial 12 374624) = some ⟨12, 2, 0, 1341653, 374624, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_374624_1341653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374624 ⟨1341653, by decide⟩ :=
  accepted_of_selected 12 374624 ⟨1341653, by decide⟩ ⟨12, 2, 0, 1341653, 374624, 1433, 65536⟩
    (by decide) selected_cut_47903

theorem selected_cut_47904 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 374625) = some ⟨12, 1, 0, 1256866, 374625, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374625_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374625 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 374625 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 374625, 1, 65536⟩
    (by decide) selected_cut_47904

theorem selected_cut_47905 : selected 9 ⟨1341680, by decide⟩
    (prefixPartial 12 374626) = some ⟨12, 2, 0, 1341680, 374626, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_374626_1341680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374626 ⟨1341680, by decide⟩ :=
  accepted_of_selected 12 374626 ⟨1341680, by decide⟩ ⟨12, 2, 0, 1341680, 374626, 1457, 65536⟩
    (by decide) selected_cut_47905

theorem selected_cut_47906 : selected 9 ⟨1341699, by decide⟩
    (prefixPartial 12 374627) = some ⟨12, 2, 0, 1341699, 374627, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_374627_1341699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374627 ⟨1341699, by decide⟩ :=
  accepted_of_selected 12 374627 ⟨1341699, by decide⟩ ⟨12, 2, 0, 1341699, 374627, 1309, 65536⟩
    (by decide) selected_cut_47906

theorem unmarked_context_11_93656_1341700 : frontier 10 ⟨1341700, by decide⟩
    (prefixCache 11 93656) (prefixPartial 11 93656) = false := by
  decide +kernel

theorem node_context_11_93656_1341700 : EJMOriginalGlobalDAGData.nodes 10 ⟨1341700, by decide⟩ =
    .split (coordinate 11) (![⟨1341653, by decide⟩,⟨1256866, by decide⟩,⟨1341680, by decide⟩,⟨1341699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93656_1341700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93656 ⟨1341700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93656
    ⟨1341700, by decide⟩ (by decide) (![⟨1341653, by decide⟩,⟨1256866, by decide⟩,⟨1341680, by decide⟩,⟨1341699, by decide⟩]) unmarked_context_11_93656_1341700 node_context_11_93656_1341700
  intro a
  fin_cases a
  · exact context_12_374624_1341653
  · exact context_12_374625_1256866
  · exact context_12_374626_1341680
  · exact context_12_374627_1341699

theorem selected_cut_47907 : selected 10 ⟨1341760, by decide⟩
    (prefixPartial 11 93657) = some ⟨11, 2, 0, 1341760, 93657, 3717, 262144⟩ := by
  decide +kernel

theorem context_11_93657_1341760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93657 ⟨1341760, by decide⟩ :=
  accepted_of_selected 11 93657 ⟨1341760, by decide⟩ ⟨11, 2, 0, 1341760, 93657, 3717, 262144⟩
    (by decide) selected_cut_47907

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
