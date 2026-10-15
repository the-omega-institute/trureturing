/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover282
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_27170 : selected 8 ⟨687768, by decide⟩
    (prefixPartial 13 365636) = some ⟨13, 2, 0, 687768, 365636, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_365636_687768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365636 ⟨687768, by decide⟩ :=
  accepted_of_selected 13 365636 ⟨687768, by decide⟩ ⟨13, 2, 0, 687768, 365636, 1449, 16384⟩
    (by decide) selected_cut_27170

theorem selected_cut_27171 : selected 8 ⟨687789, by decide⟩
    (prefixPartial 13 365637) = some ⟨13, 2, 0, 687789, 365637, 945, 16384⟩ := by
  decide +kernel

theorem context_13_365637_687789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365637 ⟨687789, by decide⟩ :=
  accepted_of_selected 13 365637 ⟨687789, by decide⟩ ⟨13, 2, 0, 687789, 365637, 945, 16384⟩
    (by decide) selected_cut_27171

theorem selected_cut_27172 : selected 8 ⟨687805, by decide⟩
    (prefixPartial 13 365638) = some ⟨13, 2, 0, 687805, 365638, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_365638_687805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365638 ⟨687805, by decide⟩ :=
  accepted_of_selected 13 365638 ⟨687805, by decide⟩ ⟨13, 2, 0, 687805, 365638, 1125, 16384⟩
    (by decide) selected_cut_27172

theorem selected_cut_27173 : selected 8 ⟨687812, by decide⟩
    (prefixPartial 13 365639) = some ⟨13, 2, 0, 687812, 365639, 617, 16384⟩ := by
  decide +kernel

theorem context_13_365639_687812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365639 ⟨687812, by decide⟩ :=
  accepted_of_selected 13 365639 ⟨687812, by decide⟩ ⟨13, 2, 0, 687812, 365639, 617, 16384⟩
    (by decide) selected_cut_27173

theorem unmarked_context_12_91409_687813 : frontier 9 ⟨687813, by decide⟩
    (prefixCache 12 91409) (prefixPartial 12 91409) = false := by
  decide +kernel

theorem node_context_12_91409_687813 : EJMOriginalGlobalDAGData.nodes 9 ⟨687813, by decide⟩ =
    .split (coordinate 12) (![⟨687768, by decide⟩,⟨687789, by decide⟩,⟨687805, by decide⟩,⟨687812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91409_687813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91409 ⟨687813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91409
    ⟨687813, by decide⟩ (by decide) (![⟨687768, by decide⟩,⟨687789, by decide⟩,⟨687805, by decide⟩,⟨687812, by decide⟩]) unmarked_context_12_91409_687813 node_context_12_91409_687813
  intro a
  fin_cases a
  · exact context_13_365636_687768
  · exact context_13_365637_687789
  · exact context_13_365638_687805
  · exact context_13_365639_687812

theorem selected_cut_27174 : selected 8 ⟨687840, by decide⟩
    (prefixPartial 13 365640) = some ⟨13, 2, 0, 687840, 365640, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_365640_687840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365640 ⟨687840, by decide⟩ :=
  accepted_of_selected 13 365640 ⟨687840, by decide⟩ ⟨13, 2, 0, 687840, 365640, 1537, 16384⟩
    (by decide) selected_cut_27174

theorem selected_cut_27175 : selected 8 ⟨687860, by decide⟩
    (prefixPartial 13 365641) = some ⟨13, 2, 0, 687860, 365641, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_365641_687860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365641 ⟨687860, by decide⟩ :=
  accepted_of_selected 13 365641 ⟨687860, by decide⟩ ⟨13, 2, 0, 687860, 365641, 1273, 16384⟩
    (by decide) selected_cut_27175

theorem selected_cut_27176 : selected 8 ⟨687875, by decide⟩
    (prefixPartial 13 365642) = some ⟨13, 2, 0, 687875, 365642, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_365642_687875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365642 ⟨687875, by decide⟩ :=
  accepted_of_selected 13 365642 ⟨687875, by decide⟩ ⟨13, 2, 0, 687875, 365642, 1345, 16384⟩
    (by decide) selected_cut_27176

theorem selected_cut_27177 : selected 8 ⟨687884, by decide⟩
    (prefixPartial 13 365643) = some ⟨13, 2, 0, 687884, 365643, 781, 16384⟩ := by
  decide +kernel

theorem context_13_365643_687884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365643 ⟨687884, by decide⟩ :=
  accepted_of_selected 13 365643 ⟨687884, by decide⟩ ⟨13, 2, 0, 687884, 365643, 781, 16384⟩
    (by decide) selected_cut_27177

theorem unmarked_context_12_91410_687885 : frontier 9 ⟨687885, by decide⟩
    (prefixCache 12 91410) (prefixPartial 12 91410) = false := by
  decide +kernel

theorem node_context_12_91410_687885 : EJMOriginalGlobalDAGData.nodes 9 ⟨687885, by decide⟩ =
    .split (coordinate 12) (![⟨687840, by decide⟩,⟨687860, by decide⟩,⟨687875, by decide⟩,⟨687884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91410_687885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91410 ⟨687885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91410
    ⟨687885, by decide⟩ (by decide) (![⟨687840, by decide⟩,⟨687860, by decide⟩,⟨687875, by decide⟩,⟨687884, by decide⟩]) unmarked_context_12_91410_687885 node_context_12_91410_687885
  intro a
  fin_cases a
  · exact context_13_365640_687840
  · exact context_13_365641_687860
  · exact context_13_365642_687875
  · exact context_13_365643_687884

theorem selected_cut_27178 : selected 8 ⟨687918, by decide⟩
    (prefixPartial 13 365644) = some ⟨13, 2, 0, 687918, 365644, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_365644_687918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365644 ⟨687918, by decide⟩ :=
  accepted_of_selected 13 365644 ⟨687918, by decide⟩ ⟨13, 2, 0, 687918, 365644, 1601, 16384⟩
    (by decide) selected_cut_27178

theorem selected_cut_27179 : selected 8 ⟨687937, by decide⟩
    (prefixPartial 13 365645) = some ⟨13, 2, 0, 687937, 365645, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_365645_687937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365645 ⟨687937, by decide⟩ :=
  accepted_of_selected 13 365645 ⟨687937, by decide⟩ ⟨13, 2, 0, 687937, 365645, 1381, 16384⟩
    (by decide) selected_cut_27179

theorem selected_cut_27180 : selected 8 ⟨687955, by decide⟩
    (prefixPartial 13 365646) = some ⟨13, 2, 0, 687955, 365646, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_365646_687955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365646 ⟨687955, by decide⟩ :=
  accepted_of_selected 13 365646 ⟨687955, by decide⟩ ⟨13, 2, 0, 687955, 365646, 1557, 16384⟩
    (by decide) selected_cut_27180

theorem selected_cut_27181 : selected 8 ⟨687960, by decide⟩
    (prefixPartial 13 365647) = some ⟨13, 2, 0, 687960, 365647, 781, 16384⟩ := by
  decide +kernel

theorem context_13_365647_687960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365647 ⟨687960, by decide⟩ :=
  accepted_of_selected 13 365647 ⟨687960, by decide⟩ ⟨13, 2, 0, 687960, 365647, 781, 16384⟩
    (by decide) selected_cut_27181

theorem unmarked_context_12_91411_687961 : frontier 9 ⟨687961, by decide⟩
    (prefixCache 12 91411) (prefixPartial 12 91411) = false := by
  decide +kernel

theorem node_context_12_91411_687961 : EJMOriginalGlobalDAGData.nodes 9 ⟨687961, by decide⟩ =
    .split (coordinate 12) (![⟨687918, by decide⟩,⟨687937, by decide⟩,⟨687955, by decide⟩,⟨687960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91411_687961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91411 ⟨687961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91411
    ⟨687961, by decide⟩ (by decide) (![⟨687918, by decide⟩,⟨687937, by decide⟩,⟨687955, by decide⟩,⟨687960, by decide⟩]) unmarked_context_12_91411_687961 node_context_12_91411_687961
  intro a
  fin_cases a
  · exact context_13_365644_687918
  · exact context_13_365645_687937
  · exact context_13_365646_687955
  · exact context_13_365647_687960

theorem unmarked_context_11_22852_687962 : frontier 10 ⟨687962, by decide⟩
    (prefixCache 11 22852) (prefixPartial 11 22852) = false := by
  decide +kernel

theorem node_context_11_22852_687962 : EJMOriginalGlobalDAGData.nodes 10 ⟨687962, by decide⟩ =
    .split (coordinate 11) (![⟨687746, by decide⟩,⟨687813, by decide⟩,⟨687885, by decide⟩,⟨687961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22852_687962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22852 ⟨687962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22852
    ⟨687962, by decide⟩ (by decide) (![⟨687746, by decide⟩,⟨687813, by decide⟩,⟨687885, by decide⟩,⟨687961, by decide⟩]) unmarked_context_11_22852_687962 node_context_11_22852_687962
  intro a
  fin_cases a
  · exact context_12_91408_687746
  · exact context_12_91409_687813
  · exact context_12_91410_687885
  · exact context_12_91411_687961

theorem selected_cut_27182 : selected 10 ⟨687963, by decide⟩
    (prefixPartial 11 22853) = some ⟨11, 2, 0, 687963, 22853, 5, 262144⟩ := by
  decide +kernel

theorem context_11_22853_687963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22853 ⟨687963, by decide⟩ :=
  accepted_of_selected 11 22853 ⟨687963, by decide⟩ ⟨11, 2, 0, 687963, 22853, 5, 262144⟩
    (by decide) selected_cut_27182

theorem selected_cut_27183 : selected 8 ⟨687982, by decide⟩
    (prefixPartial 13 365664) = some ⟨13, 2, 0, 687982, 365664, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_365664_687982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365664 ⟨687982, by decide⟩ :=
  accepted_of_selected 13 365664 ⟨687982, by decide⟩ ⟨13, 2, 0, 687982, 365664, 1217, 16384⟩
    (by decide) selected_cut_27183

theorem selected_cut_27184 : selected 8 ⟨688005, by decide⟩
    (prefixPartial 13 365665) = some ⟨13, 2, 0, 688005, 365665, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_365665_688005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365665 ⟨688005, by decide⟩ :=
  accepted_of_selected 13 365665 ⟨688005, by decide⟩ ⟨13, 2, 0, 688005, 365665, 1141, 16384⟩
    (by decide) selected_cut_27184

theorem selected_cut_27185 : selected 8 ⟨688024, by decide⟩
    (prefixPartial 13 365666) = some ⟨13, 2, 0, 688024, 365666, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_365666_688024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365666 ⟨688024, by decide⟩ :=
  accepted_of_selected 13 365666 ⟨688024, by decide⟩ ⟨13, 2, 0, 688024, 365666, 1401, 16384⟩
    (by decide) selected_cut_27185

theorem selected_cut_27186 : selected 8 ⟨688032, by decide⟩
    (prefixPartial 13 365667) = some ⟨13, 2, 0, 688032, 365667, 817, 16384⟩ := by
  decide +kernel

theorem context_13_365667_688032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365667 ⟨688032, by decide⟩ :=
  accepted_of_selected 13 365667 ⟨688032, by decide⟩ ⟨13, 2, 0, 688032, 365667, 817, 16384⟩
    (by decide) selected_cut_27186

theorem unmarked_context_12_91416_688033 : frontier 9 ⟨688033, by decide⟩
    (prefixCache 12 91416) (prefixPartial 12 91416) = false := by
  decide +kernel

theorem node_context_12_91416_688033 : EJMOriginalGlobalDAGData.nodes 9 ⟨688033, by decide⟩ =
    .split (coordinate 12) (![⟨687982, by decide⟩,⟨688005, by decide⟩,⟨688024, by decide⟩,⟨688032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91416_688033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91416 ⟨688033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91416
    ⟨688033, by decide⟩ (by decide) (![⟨687982, by decide⟩,⟨688005, by decide⟩,⟨688024, by decide⟩,⟨688032, by decide⟩]) unmarked_context_12_91416_688033 node_context_12_91416_688033
  intro a
  fin_cases a
  · exact context_13_365664_687982
  · exact context_13_365665_688005
  · exact context_13_365666_688024
  · exact context_13_365667_688032

theorem selected_cut_27187 : selected 8 ⟨688062, by decide⟩
    (prefixPartial 13 365668) = some ⟨13, 2, 0, 688062, 365668, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_365668_688062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365668 ⟨688062, by decide⟩ :=
  accepted_of_selected 13 365668 ⟨688062, by decide⟩ ⟨13, 2, 0, 688062, 365668, 1501, 16384⟩
    (by decide) selected_cut_27187

theorem selected_cut_27188 : selected 8 ⟨688080, by decide⟩
    (prefixPartial 13 365669) = some ⟨13, 2, 0, 688080, 365669, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_365669_688080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365669 ⟨688080, by decide⟩ :=
  accepted_of_selected 13 365669 ⟨688080, by decide⟩ ⟨13, 2, 0, 688080, 365669, 1065, 16384⟩
    (by decide) selected_cut_27188

theorem selected_cut_27189 : selected 8 ⟨688099, by decide⟩
    (prefixPartial 13 365670) = some ⟨13, 2, 0, 688099, 365670, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_365670_688099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365670 ⟨688099, by decide⟩ :=
  accepted_of_selected 13 365670 ⟨688099, by decide⟩ ⟨13, 2, 0, 688099, 365670, 1357, 16384⟩
    (by decide) selected_cut_27189

theorem selected_cut_27190 : selected 8 ⟨688106, by decide⟩
    (prefixPartial 13 365671) = some ⟨13, 2, 0, 688106, 365671, 637, 16384⟩ := by
  decide +kernel

theorem context_13_365671_688106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365671 ⟨688106, by decide⟩ :=
  accepted_of_selected 13 365671 ⟨688106, by decide⟩ ⟨13, 2, 0, 688106, 365671, 637, 16384⟩
    (by decide) selected_cut_27190

theorem unmarked_context_12_91417_688107 : frontier 9 ⟨688107, by decide⟩
    (prefixCache 12 91417) (prefixPartial 12 91417) = false := by
  decide +kernel

theorem node_context_12_91417_688107 : EJMOriginalGlobalDAGData.nodes 9 ⟨688107, by decide⟩ =
    .split (coordinate 12) (![⟨688062, by decide⟩,⟨688080, by decide⟩,⟨688099, by decide⟩,⟨688106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91417_688107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91417 ⟨688107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91417
    ⟨688107, by decide⟩ (by decide) (![⟨688062, by decide⟩,⟨688080, by decide⟩,⟨688099, by decide⟩,⟨688106, by decide⟩]) unmarked_context_12_91417_688107 node_context_12_91417_688107
  intro a
  fin_cases a
  · exact context_13_365668_688062
  · exact context_13_365669_688080
  · exact context_13_365670_688099
  · exact context_13_365671_688106

theorem selected_cut_27191 : selected 8 ⟨688130, by decide⟩
    (prefixPartial 13 365672) = some ⟨13, 2, 0, 688130, 365672, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_365672_688130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365672 ⟨688130, by decide⟩ :=
  accepted_of_selected 13 365672 ⟨688130, by decide⟩ ⟨13, 2, 0, 688130, 365672, 1397, 16384⟩
    (by decide) selected_cut_27191

theorem selected_cut_27192 : selected 8 ⟨688151, by decide⟩
    (prefixPartial 13 365673) = some ⟨13, 2, 0, 688151, 365673, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_365673_688151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365673 ⟨688151, by decide⟩ :=
  accepted_of_selected 13 365673 ⟨688151, by decide⟩ ⟨13, 2, 0, 688151, 365673, 1233, 16384⟩
    (by decide) selected_cut_27192

theorem selected_cut_27193 : selected 8 ⟨688169, by decide⟩
    (prefixPartial 13 365674) = some ⟨13, 2, 0, 688169, 365674, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_365674_688169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365674 ⟨688169, by decide⟩ :=
  accepted_of_selected 13 365674 ⟨688169, by decide⟩ ⟨13, 2, 0, 688169, 365674, 1293, 16384⟩
    (by decide) selected_cut_27193

theorem selected_cut_27194 : selected 8 ⟨688176, by decide⟩
    (prefixPartial 13 365675) = some ⟨13, 2, 0, 688176, 365675, 789, 16384⟩ := by
  decide +kernel

theorem context_13_365675_688176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365675 ⟨688176, by decide⟩ :=
  accepted_of_selected 13 365675 ⟨688176, by decide⟩ ⟨13, 2, 0, 688176, 365675, 789, 16384⟩
    (by decide) selected_cut_27194

theorem unmarked_context_12_91418_688177 : frontier 9 ⟨688177, by decide⟩
    (prefixCache 12 91418) (prefixPartial 12 91418) = false := by
  decide +kernel

theorem node_context_12_91418_688177 : EJMOriginalGlobalDAGData.nodes 9 ⟨688177, by decide⟩ =
    .split (coordinate 12) (![⟨688130, by decide⟩,⟨688151, by decide⟩,⟨688169, by decide⟩,⟨688176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91418_688177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91418 ⟨688177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91418
    ⟨688177, by decide⟩ (by decide) (![⟨688130, by decide⟩,⟨688151, by decide⟩,⟨688169, by decide⟩,⟨688176, by decide⟩]) unmarked_context_12_91418_688177 node_context_12_91418_688177
  intro a
  fin_cases a
  · exact context_13_365672_688130
  · exact context_13_365673_688151
  · exact context_13_365674_688169
  · exact context_13_365675_688176

theorem selected_cut_27195 : selected 8 ⟨688203, by decide⟩
    (prefixPartial 13 365676) = some ⟨13, 2, 0, 688203, 365676, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_365676_688203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365676 ⟨688203, by decide⟩ :=
  accepted_of_selected 13 365676 ⟨688203, by decide⟩ ⟨13, 2, 0, 688203, 365676, 1461, 16384⟩
    (by decide) selected_cut_27195

theorem selected_cut_27196 : selected 8 ⟨688227, by decide⟩
    (prefixPartial 13 365677) = some ⟨13, 2, 0, 688227, 365677, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_365677_688227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365677 ⟨688227, by decide⟩ :=
  accepted_of_selected 13 365677 ⟨688227, by decide⟩ ⟨13, 2, 0, 688227, 365677, 1505, 16384⟩
    (by decide) selected_cut_27196

theorem selected_cut_27197 : selected 8 ⟨688247, by decide⟩
    (prefixPartial 13 365678) = some ⟨13, 2, 0, 688247, 365678, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_365678_688247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365678 ⟨688247, by decide⟩ :=
  accepted_of_selected 13 365678 ⟨688247, by decide⟩ ⟨13, 2, 0, 688247, 365678, 1581, 16384⟩
    (by decide) selected_cut_27197

theorem selected_cut_27198 : selected 8 ⟨688254, by decide⟩
    (prefixPartial 13 365679) = some ⟨13, 2, 0, 688254, 365679, 733, 16384⟩ := by
  decide +kernel

theorem context_13_365679_688254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365679 ⟨688254, by decide⟩ :=
  accepted_of_selected 13 365679 ⟨688254, by decide⟩ ⟨13, 2, 0, 688254, 365679, 733, 16384⟩
    (by decide) selected_cut_27198

theorem unmarked_context_12_91419_688255 : frontier 9 ⟨688255, by decide⟩
    (prefixCache 12 91419) (prefixPartial 12 91419) = false := by
  decide +kernel

theorem node_context_12_91419_688255 : EJMOriginalGlobalDAGData.nodes 9 ⟨688255, by decide⟩ =
    .split (coordinate 12) (![⟨688203, by decide⟩,⟨688227, by decide⟩,⟨688247, by decide⟩,⟨688254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91419_688255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91419 ⟨688255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91419
    ⟨688255, by decide⟩ (by decide) (![⟨688203, by decide⟩,⟨688227, by decide⟩,⟨688247, by decide⟩,⟨688254, by decide⟩]) unmarked_context_12_91419_688255 node_context_12_91419_688255
  intro a
  fin_cases a
  · exact context_13_365676_688203
  · exact context_13_365677_688227
  · exact context_13_365678_688247
  · exact context_13_365679_688254

theorem unmarked_context_11_22854_688256 : frontier 10 ⟨688256, by decide⟩
    (prefixCache 11 22854) (prefixPartial 11 22854) = false := by
  decide +kernel

theorem node_context_11_22854_688256 : EJMOriginalGlobalDAGData.nodes 10 ⟨688256, by decide⟩ =
    .split (coordinate 11) (![⟨688033, by decide⟩,⟨688107, by decide⟩,⟨688177, by decide⟩,⟨688255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22854_688256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22854 ⟨688256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22854
    ⟨688256, by decide⟩ (by decide) (![⟨688033, by decide⟩,⟨688107, by decide⟩,⟨688177, by decide⟩,⟨688255, by decide⟩]) unmarked_context_11_22854_688256 node_context_11_22854_688256
  intro a
  fin_cases a
  · exact context_12_91416_688033
  · exact context_12_91417_688107
  · exact context_12_91418_688177
  · exact context_12_91419_688255

theorem selected_cut_27199 : selected 8 ⟨688273, by decide⟩
    (prefixPartial 13 365680) = some ⟨13, 2, 0, 688273, 365680, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_365680_688273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365680 ⟨688273, by decide⟩ :=
  accepted_of_selected 13 365680 ⟨688273, by decide⟩ ⟨13, 2, 0, 688273, 365680, 1053, 16384⟩
    (by decide) selected_cut_27199

theorem selected_cut_27200 : selected 8 ⟨688296, by decide⟩
    (prefixPartial 13 365681) = some ⟨13, 2, 0, 688296, 365681, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_365681_688296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365681 ⟨688296, by decide⟩ :=
  accepted_of_selected 13 365681 ⟨688296, by decide⟩ ⟨13, 2, 0, 688296, 365681, 1357, 16384⟩
    (by decide) selected_cut_27200

theorem selected_cut_27201 : selected 8 ⟨688313, by decide⟩
    (prefixPartial 13 365682) = some ⟨13, 2, 0, 688313, 365682, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_365682_688313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365682 ⟨688313, by decide⟩ :=
  accepted_of_selected 13 365682 ⟨688313, by decide⟩ ⟨13, 2, 0, 688313, 365682, 1245, 16384⟩
    (by decide) selected_cut_27201

theorem selected_cut_27202 : selected 8 ⟨688320, by decide⟩
    (prefixPartial 13 365683) = some ⟨13, 2, 0, 688320, 365683, 869, 16384⟩ := by
  decide +kernel

theorem context_13_365683_688320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365683 ⟨688320, by decide⟩ :=
  accepted_of_selected 13 365683 ⟨688320, by decide⟩ ⟨13, 2, 0, 688320, 365683, 869, 16384⟩
    (by decide) selected_cut_27202

theorem unmarked_context_12_91420_688321 : frontier 9 ⟨688321, by decide⟩
    (prefixCache 12 91420) (prefixPartial 12 91420) = false := by
  decide +kernel

theorem node_context_12_91420_688321 : EJMOriginalGlobalDAGData.nodes 9 ⟨688321, by decide⟩ =
    .split (coordinate 12) (![⟨688273, by decide⟩,⟨688296, by decide⟩,⟨688313, by decide⟩,⟨688320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91420_688321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91420 ⟨688321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91420
    ⟨688321, by decide⟩ (by decide) (![⟨688273, by decide⟩,⟨688296, by decide⟩,⟨688313, by decide⟩,⟨688320, by decide⟩]) unmarked_context_12_91420_688321 node_context_12_91420_688321
  intro a
  fin_cases a
  · exact context_13_365680_688273
  · exact context_13_365681_688296
  · exact context_13_365682_688313
  · exact context_13_365683_688320

theorem selected_cut_27203 : selected 9 ⟨688385, by decide⟩
    (prefixPartial 12 91421) = some ⟨12, 2, 0, 688385, 91421, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_91421_688385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91421 ⟨688385, by decide⟩ :=
  accepted_of_selected 12 91421 ⟨688385, by decide⟩ ⟨12, 2, 0, 688385, 91421, 4041, 65536⟩
    (by decide) selected_cut_27203

theorem selected_cut_27204 : selected 8 ⟨688403, by decide⟩
    (prefixPartial 13 365688) = some ⟨13, 2, 0, 688403, 365688, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_365688_688403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365688 ⟨688403, by decide⟩ :=
  accepted_of_selected 13 365688 ⟨688403, by decide⟩ ⟨13, 2, 0, 688403, 365688, 1249, 16384⟩
    (by decide) selected_cut_27204

theorem selected_cut_27205 : selected 8 ⟨688421, by decide⟩
    (prefixPartial 13 365689) = some ⟨13, 2, 0, 688421, 365689, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_365689_688421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365689 ⟨688421, by decide⟩ :=
  accepted_of_selected 13 365689 ⟨688421, by decide⟩ ⟨13, 2, 0, 688421, 365689, 1313, 16384⟩
    (by decide) selected_cut_27205

theorem selected_cut_27206 : selected 8 ⟨688434, by decide⟩
    (prefixPartial 13 365690) = some ⟨13, 2, 0, 688434, 365690, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_365690_688434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365690 ⟨688434, by decide⟩ :=
  accepted_of_selected 13 365690 ⟨688434, by decide⟩ ⟨13, 2, 0, 688434, 365690, 1085, 16384⟩
    (by decide) selected_cut_27206

theorem selected_cut_27207 : selected 8 ⟨688440, by decide⟩
    (prefixPartial 13 365691) = some ⟨13, 2, 0, 688440, 365691, 849, 16384⟩ := by
  decide +kernel

theorem context_13_365691_688440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365691 ⟨688440, by decide⟩ :=
  accepted_of_selected 13 365691 ⟨688440, by decide⟩ ⟨13, 2, 0, 688440, 365691, 849, 16384⟩
    (by decide) selected_cut_27207

theorem unmarked_context_12_91422_688441 : frontier 9 ⟨688441, by decide⟩
    (prefixCache 12 91422) (prefixPartial 12 91422) = false := by
  decide +kernel

theorem node_context_12_91422_688441 : EJMOriginalGlobalDAGData.nodes 9 ⟨688441, by decide⟩ =
    .split (coordinate 12) (![⟨688403, by decide⟩,⟨688421, by decide⟩,⟨688434, by decide⟩,⟨688440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91422_688441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91422 ⟨688441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91422
    ⟨688441, by decide⟩ (by decide) (![⟨688403, by decide⟩,⟨688421, by decide⟩,⟨688434, by decide⟩,⟨688440, by decide⟩]) unmarked_context_12_91422_688441 node_context_12_91422_688441
  intro a
  fin_cases a
  · exact context_13_365688_688403
  · exact context_13_365689_688421
  · exact context_13_365690_688434
  · exact context_13_365691_688440

theorem selected_cut_27208 : selected 8 ⟨688467, by decide⟩
    (prefixPartial 13 365692) = some ⟨13, 2, 0, 688467, 365692, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_365692_688467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365692 ⟨688467, by decide⟩ :=
  accepted_of_selected 13 365692 ⟨688467, by decide⟩ ⟨13, 2, 0, 688467, 365692, 1421, 16384⟩
    (by decide) selected_cut_27208

theorem selected_cut_27209 : selected 8 ⟨688489, by decide⟩
    (prefixPartial 13 365693) = some ⟨13, 2, 0, 688489, 365693, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_365693_688489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365693 ⟨688489, by decide⟩ :=
  accepted_of_selected 13 365693 ⟨688489, by decide⟩ ⟨13, 2, 0, 688489, 365693, 1541, 16384⟩
    (by decide) selected_cut_27209

theorem selected_cut_27210 : selected 8 ⟨688509, by decide⟩
    (prefixPartial 13 365694) = some ⟨13, 2, 0, 688509, 365694, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_365694_688509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365694 ⟨688509, by decide⟩ :=
  accepted_of_selected 13 365694 ⟨688509, by decide⟩ ⟨13, 2, 0, 688509, 365694, 1397, 16384⟩
    (by decide) selected_cut_27210

theorem selected_cut_27211 : selected 8 ⟨688519, by decide⟩
    (prefixPartial 13 365695) = some ⟨13, 2, 0, 688519, 365695, 837, 16384⟩ := by
  decide +kernel

theorem context_13_365695_688519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365695 ⟨688519, by decide⟩ :=
  accepted_of_selected 13 365695 ⟨688519, by decide⟩ ⟨13, 2, 0, 688519, 365695, 837, 16384⟩
    (by decide) selected_cut_27211

theorem unmarked_context_12_91423_688520 : frontier 9 ⟨688520, by decide⟩
    (prefixCache 12 91423) (prefixPartial 12 91423) = false := by
  decide +kernel

theorem node_context_12_91423_688520 : EJMOriginalGlobalDAGData.nodes 9 ⟨688520, by decide⟩ =
    .split (coordinate 12) (![⟨688467, by decide⟩,⟨688489, by decide⟩,⟨688509, by decide⟩,⟨688519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91423_688520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91423 ⟨688520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91423
    ⟨688520, by decide⟩ (by decide) (![⟨688467, by decide⟩,⟨688489, by decide⟩,⟨688509, by decide⟩,⟨688519, by decide⟩]) unmarked_context_12_91423_688520 node_context_12_91423_688520
  intro a
  fin_cases a
  · exact context_13_365692_688467
  · exact context_13_365693_688489
  · exact context_13_365694_688509
  · exact context_13_365695_688519

theorem unmarked_context_11_22855_688521 : frontier 10 ⟨688521, by decide⟩
    (prefixCache 11 22855) (prefixPartial 11 22855) = false := by
  decide +kernel

theorem node_context_11_22855_688521 : EJMOriginalGlobalDAGData.nodes 10 ⟨688521, by decide⟩ =
    .split (coordinate 11) (![⟨688321, by decide⟩,⟨688385, by decide⟩,⟨688441, by decide⟩,⟨688520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22855_688521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22855 ⟨688521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22855
    ⟨688521, by decide⟩ (by decide) (![⟨688321, by decide⟩,⟨688385, by decide⟩,⟨688441, by decide⟩,⟨688520, by decide⟩]) unmarked_context_11_22855_688521 node_context_11_22855_688521
  intro a
  fin_cases a
  · exact context_12_91420_688321
  · exact context_12_91421_688385
  · exact context_12_91422_688441
  · exact context_12_91423_688520

theorem unmarked_context_10_5713_688522 : frontier 11 ⟨688522, by decide⟩
    (prefixCache 10 5713) (prefixPartial 10 5713) = false := by
  decide +kernel

theorem node_context_10_5713_688522 : EJMOriginalGlobalDAGData.nodes 11 ⟨688522, by decide⟩ =
    .split (coordinate 10) (![⟨687962, by decide⟩,⟨687963, by decide⟩,⟨688256, by decide⟩,⟨688521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5713_688522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5713 ⟨688522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5713
    ⟨688522, by decide⟩ (by decide) (![⟨687962, by decide⟩,⟨687963, by decide⟩,⟨688256, by decide⟩,⟨688521, by decide⟩]) unmarked_context_10_5713_688522 node_context_10_5713_688522
  intro a
  fin_cases a
  · exact context_11_22852_687962
  · exact context_11_22853_687963
  · exact context_11_22854_688256
  · exact context_11_22855_688521

theorem selected_cut_27212 : selected 8 ⟨688546, by decide⟩
    (prefixPartial 13 365696) = some ⟨13, 2, 0, 688546, 365696, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_365696_688546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365696 ⟨688546, by decide⟩ :=
  accepted_of_selected 13 365696 ⟨688546, by decide⟩ ⟨13, 2, 0, 688546, 365696, 1357, 16384⟩
    (by decide) selected_cut_27212

theorem selected_cut_27213 : selected 8 ⟨688567, by decide⟩
    (prefixPartial 13 365697) = some ⟨13, 2, 0, 688567, 365697, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_365697_688567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365697 ⟨688567, by decide⟩ :=
  accepted_of_selected 13 365697 ⟨688567, by decide⟩ ⟨13, 2, 0, 688567, 365697, 1337, 16384⟩
    (by decide) selected_cut_27213

theorem selected_cut_27214 : selected 8 ⟨688584, by decide⟩
    (prefixPartial 13 365698) = some ⟨13, 2, 0, 688584, 365698, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_365698_688584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365698 ⟨688584, by decide⟩ :=
  accepted_of_selected 13 365698 ⟨688584, by decide⟩ ⟨13, 2, 0, 688584, 365698, 1437, 16384⟩
    (by decide) selected_cut_27214

theorem selected_cut_27215 : selected 8 ⟨688593, by decide⟩
    (prefixPartial 13 365699) = some ⟨13, 2, 0, 688593, 365699, 897, 16384⟩ := by
  decide +kernel

theorem context_13_365699_688593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365699 ⟨688593, by decide⟩ :=
  accepted_of_selected 13 365699 ⟨688593, by decide⟩ ⟨13, 2, 0, 688593, 365699, 897, 16384⟩
    (by decide) selected_cut_27215

theorem unmarked_context_12_91424_688594 : frontier 9 ⟨688594, by decide⟩
    (prefixCache 12 91424) (prefixPartial 12 91424) = false := by
  decide +kernel

theorem node_context_12_91424_688594 : EJMOriginalGlobalDAGData.nodes 9 ⟨688594, by decide⟩ =
    .split (coordinate 12) (![⟨688546, by decide⟩,⟨688567, by decide⟩,⟨688584, by decide⟩,⟨688593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91424_688594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91424 ⟨688594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91424
    ⟨688594, by decide⟩ (by decide) (![⟨688546, by decide⟩,⟨688567, by decide⟩,⟨688584, by decide⟩,⟨688593, by decide⟩]) unmarked_context_12_91424_688594 node_context_12_91424_688594
  intro a
  fin_cases a
  · exact context_13_365696_688546
  · exact context_13_365697_688567
  · exact context_13_365698_688584
  · exact context_13_365699_688593

theorem selected_cut_27216 : selected 8 ⟨688619, by decide⟩
    (prefixPartial 13 365700) = some ⟨13, 2, 0, 688619, 365700, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_365700_688619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365700 ⟨688619, by decide⟩ :=
  accepted_of_selected 13 365700 ⟨688619, by decide⟩ ⟨13, 2, 0, 688619, 365700, 1469, 16384⟩
    (by decide) selected_cut_27216

theorem selected_cut_27217 : selected 8 ⟨688643, by decide⟩
    (prefixPartial 13 365701) = some ⟨13, 2, 0, 688643, 365701, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_365701_688643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365701 ⟨688643, by decide⟩ :=
  accepted_of_selected 13 365701 ⟨688643, by decide⟩ ⟨13, 2, 0, 688643, 365701, 1389, 16384⟩
    (by decide) selected_cut_27217

theorem selected_cut_27218 : selected 8 ⟨688661, by decide⟩
    (prefixPartial 13 365702) = some ⟨13, 2, 0, 688661, 365702, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_365702_688661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365702 ⟨688661, by decide⟩ :=
  accepted_of_selected 13 365702 ⟨688661, by decide⟩ ⟨13, 2, 0, 688661, 365702, 1441, 16384⟩
    (by decide) selected_cut_27218

theorem selected_cut_27219 : selected 8 ⟨688666, by decide⟩
    (prefixPartial 13 365703) = some ⟨13, 2, 0, 688666, 365703, 729, 16384⟩ := by
  decide +kernel

theorem context_13_365703_688666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365703 ⟨688666, by decide⟩ :=
  accepted_of_selected 13 365703 ⟨688666, by decide⟩ ⟨13, 2, 0, 688666, 365703, 729, 16384⟩
    (by decide) selected_cut_27219

theorem unmarked_context_12_91425_688667 : frontier 9 ⟨688667, by decide⟩
    (prefixCache 12 91425) (prefixPartial 12 91425) = false := by
  decide +kernel

theorem node_context_12_91425_688667 : EJMOriginalGlobalDAGData.nodes 9 ⟨688667, by decide⟩ =
    .split (coordinate 12) (![⟨688619, by decide⟩,⟨688643, by decide⟩,⟨688661, by decide⟩,⟨688666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91425_688667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91425 ⟨688667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91425
    ⟨688667, by decide⟩ (by decide) (![⟨688619, by decide⟩,⟨688643, by decide⟩,⟨688661, by decide⟩,⟨688666, by decide⟩]) unmarked_context_12_91425_688667 node_context_12_91425_688667
  intro a
  fin_cases a
  · exact context_13_365700_688619
  · exact context_13_365701_688643
  · exact context_13_365702_688661
  · exact context_13_365703_688666

theorem selected_cut_27220 : selected 8 ⟨688693, by decide⟩
    (prefixPartial 13 365704) = some ⟨13, 2, 0, 688693, 365704, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_365704_688693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365704 ⟨688693, by decide⟩ :=
  accepted_of_selected 13 365704 ⟨688693, by decide⟩ ⟨13, 2, 0, 688693, 365704, 1401, 16384⟩
    (by decide) selected_cut_27220

theorem selected_cut_27221 : selected 8 ⟨688718, by decide⟩
    (prefixPartial 13 365705) = some ⟨13, 2, 0, 688718, 365705, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_365705_688718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365705 ⟨688718, by decide⟩ :=
  accepted_of_selected 13 365705 ⟨688718, by decide⟩ ⟨13, 2, 0, 688718, 365705, 1561, 16384⟩
    (by decide) selected_cut_27221

theorem selected_cut_27222 : selected 8 ⟨688735, by decide⟩
    (prefixPartial 13 365706) = some ⟨13, 2, 0, 688735, 365706, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_365706_688735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365706 ⟨688735, by decide⟩ :=
  accepted_of_selected 13 365706 ⟨688735, by decide⟩ ⟨13, 2, 0, 688735, 365706, 1325, 16384⟩
    (by decide) selected_cut_27222

theorem selected_cut_27223 : selected 8 ⟨688743, by decide⟩
    (prefixPartial 13 365707) = some ⟨13, 2, 0, 688743, 365707, 881, 16384⟩ := by
  decide +kernel

theorem context_13_365707_688743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365707 ⟨688743, by decide⟩ :=
  accepted_of_selected 13 365707 ⟨688743, by decide⟩ ⟨13, 2, 0, 688743, 365707, 881, 16384⟩
    (by decide) selected_cut_27223

theorem unmarked_context_12_91426_688744 : frontier 9 ⟨688744, by decide⟩
    (prefixCache 12 91426) (prefixPartial 12 91426) = false := by
  decide +kernel

theorem node_context_12_91426_688744 : EJMOriginalGlobalDAGData.nodes 9 ⟨688744, by decide⟩ =
    .split (coordinate 12) (![⟨688693, by decide⟩,⟨688718, by decide⟩,⟨688735, by decide⟩,⟨688743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91426_688744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91426 ⟨688744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91426
    ⟨688744, by decide⟩ (by decide) (![⟨688693, by decide⟩,⟨688718, by decide⟩,⟨688735, by decide⟩,⟨688743, by decide⟩]) unmarked_context_12_91426_688744 node_context_12_91426_688744
  intro a
  fin_cases a
  · exact context_13_365704_688693
  · exact context_13_365705_688718
  · exact context_13_365706_688735
  · exact context_13_365707_688743

theorem selected_cut_27224 : selected 8 ⟨688775, by decide⟩
    (prefixPartial 13 365708) = some ⟨13, 2, 0, 688775, 365708, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_365708_688775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365708 ⟨688775, by decide⟩ :=
  accepted_of_selected 13 365708 ⟨688775, by decide⟩ ⟨13, 2, 0, 688775, 365708, 1581, 16384⟩
    (by decide) selected_cut_27224

theorem selected_cut_27225 : selected 8 ⟨688808, by decide⟩
    (prefixPartial 13 365709) = some ⟨13, 2, 0, 688808, 365709, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_365709_688808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365709 ⟨688808, by decide⟩ :=
  accepted_of_selected 13 365709 ⟨688808, by decide⟩ ⟨13, 2, 0, 688808, 365709, 1765, 16384⟩
    (by decide) selected_cut_27225

theorem selected_cut_27226 : selected 8 ⟨688832, by decide⟩
    (prefixPartial 13 365710) = some ⟨13, 2, 0, 688832, 365710, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_365710_688832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365710 ⟨688832, by decide⟩ :=
  accepted_of_selected 13 365710 ⟨688832, by decide⟩ ⟨13, 2, 0, 688832, 365710, 1621, 16384⟩
    (by decide) selected_cut_27226

theorem selected_cut_27227 : selected 8 ⟨688838, by decide⟩
    (prefixPartial 13 365711) = some ⟨13, 2, 0, 688838, 365711, 889, 16384⟩ := by
  decide +kernel

theorem context_13_365711_688838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365711 ⟨688838, by decide⟩ :=
  accepted_of_selected 13 365711 ⟨688838, by decide⟩ ⟨13, 2, 0, 688838, 365711, 889, 16384⟩
    (by decide) selected_cut_27227

theorem unmarked_context_12_91427_688839 : frontier 9 ⟨688839, by decide⟩
    (prefixCache 12 91427) (prefixPartial 12 91427) = false := by
  decide +kernel

theorem node_context_12_91427_688839 : EJMOriginalGlobalDAGData.nodes 9 ⟨688839, by decide⟩ =
    .split (coordinate 12) (![⟨688775, by decide⟩,⟨688808, by decide⟩,⟨688832, by decide⟩,⟨688838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91427_688839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91427 ⟨688839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91427
    ⟨688839, by decide⟩ (by decide) (![⟨688775, by decide⟩,⟨688808, by decide⟩,⟨688832, by decide⟩,⟨688838, by decide⟩]) unmarked_context_12_91427_688839 node_context_12_91427_688839
  intro a
  fin_cases a
  · exact context_13_365708_688775
  · exact context_13_365709_688808
  · exact context_13_365710_688832
  · exact context_13_365711_688838

theorem unmarked_context_11_22856_688840 : frontier 10 ⟨688840, by decide⟩
    (prefixCache 11 22856) (prefixPartial 11 22856) = false := by
  decide +kernel

theorem node_context_11_22856_688840 : EJMOriginalGlobalDAGData.nodes 10 ⟨688840, by decide⟩ =
    .split (coordinate 11) (![⟨688594, by decide⟩,⟨688667, by decide⟩,⟨688744, by decide⟩,⟨688839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22856_688840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22856 ⟨688840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22856
    ⟨688840, by decide⟩ (by decide) (![⟨688594, by decide⟩,⟨688667, by decide⟩,⟨688744, by decide⟩,⟨688839, by decide⟩]) unmarked_context_11_22856_688840 node_context_11_22856_688840
  intro a
  fin_cases a
  · exact context_12_91424_688594
  · exact context_12_91425_688667
  · exact context_12_91426_688744
  · exact context_12_91427_688839

theorem selected_cut_27228 : selected 9 ⟨688902, by decide⟩
    (prefixPartial 12 91428) = some ⟨12, 2, 0, 688902, 91428, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_91428_688902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91428 ⟨688902, by decide⟩ :=
  accepted_of_selected 12 91428 ⟨688902, by decide⟩ ⟨12, 2, 0, 688902, 91428, 3901, 65536⟩
    (by decide) selected_cut_27228

theorem selected_cut_27229 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 91429) = some ⟨12, 1, 0, 688903, 91429, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91429_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91429 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 91429 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 91429, 1, 65536⟩
    (by decide) selected_cut_27229

theorem selected_cut_27230 : selected 9 ⟨688965, by decide⟩
    (prefixPartial 12 91430) = some ⟨12, 2, 0, 688965, 91430, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_91430_688965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91430 ⟨688965, by decide⟩ :=
  accepted_of_selected 12 91430 ⟨688965, by decide⟩ ⟨12, 2, 0, 688965, 91430, 3881, 65536⟩
    (by decide) selected_cut_27230

theorem selected_cut_27231 : selected 8 ⟨688985, by decide⟩
    (prefixPartial 13 365724) = some ⟨13, 2, 0, 688985, 365724, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_365724_688985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365724 ⟨688985, by decide⟩ :=
  accepted_of_selected 13 365724 ⟨688985, by decide⟩ ⟨13, 2, 0, 688985, 365724, 1069, 16384⟩
    (by decide) selected_cut_27231

theorem selected_cut_27232 : selected 8 ⟨689007, by decide⟩
    (prefixPartial 13 365725) = some ⟨13, 2, 0, 689007, 365725, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_365725_689007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365725 ⟨689007, by decide⟩ :=
  accepted_of_selected 13 365725 ⟨689007, by decide⟩ ⟨13, 2, 0, 689007, 365725, 1405, 16384⟩
    (by decide) selected_cut_27232

theorem selected_cut_27233 : selected 8 ⟨689026, by decide⟩
    (prefixPartial 13 365726) = some ⟨13, 2, 0, 689026, 365726, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_365726_689026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365726 ⟨689026, by decide⟩ :=
  accepted_of_selected 13 365726 ⟨689026, by decide⟩ ⟨13, 2, 0, 689026, 365726, 1301, 16384⟩
    (by decide) selected_cut_27233

theorem selected_cut_27234 : selected 8 ⟨689031, by decide⟩
    (prefixPartial 13 365727) = some ⟨13, 2, 0, 689031, 365727, 749, 16384⟩ := by
  decide +kernel

theorem context_13_365727_689031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365727 ⟨689031, by decide⟩ :=
  accepted_of_selected 13 365727 ⟨689031, by decide⟩ ⟨13, 2, 0, 689031, 365727, 749, 16384⟩
    (by decide) selected_cut_27234

theorem unmarked_context_12_91431_689032 : frontier 9 ⟨689032, by decide⟩
    (prefixCache 12 91431) (prefixPartial 12 91431) = false := by
  decide +kernel

theorem node_context_12_91431_689032 : EJMOriginalGlobalDAGData.nodes 9 ⟨689032, by decide⟩ =
    .split (coordinate 12) (![⟨688985, by decide⟩,⟨689007, by decide⟩,⟨689026, by decide⟩,⟨689031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91431_689032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91431 ⟨689032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91431
    ⟨689032, by decide⟩ (by decide) (![⟨688985, by decide⟩,⟨689007, by decide⟩,⟨689026, by decide⟩,⟨689031, by decide⟩]) unmarked_context_12_91431_689032 node_context_12_91431_689032
  intro a
  fin_cases a
  · exact context_13_365724_688985
  · exact context_13_365725_689007
  · exact context_13_365726_689026
  · exact context_13_365727_689031

theorem unmarked_context_11_22857_689033 : frontier 10 ⟨689033, by decide⟩
    (prefixCache 11 22857) (prefixPartial 11 22857) = false := by
  decide +kernel

theorem node_context_11_22857_689033 : EJMOriginalGlobalDAGData.nodes 10 ⟨689033, by decide⟩ =
    .split (coordinate 11) (![⟨688902, by decide⟩,⟨688903, by decide⟩,⟨688965, by decide⟩,⟨689032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22857_689033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22857 ⟨689033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22857
    ⟨689033, by decide⟩ (by decide) (![⟨688902, by decide⟩,⟨688903, by decide⟩,⟨688965, by decide⟩,⟨689032, by decide⟩]) unmarked_context_11_22857_689033 node_context_11_22857_689033
  intro a
  fin_cases a
  · exact context_12_91428_688902
  · exact context_12_91429_688903
  · exact context_12_91430_688965
  · exact context_12_91431_689032

theorem selected_cut_27235 : selected 8 ⟨689047, by decide⟩
    (prefixPartial 13 365728) = some ⟨13, 2, 0, 689047, 365728, 929, 16384⟩ := by
  decide +kernel

theorem context_13_365728_689047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365728 ⟨689047, by decide⟩ :=
  accepted_of_selected 13 365728 ⟨689047, by decide⟩ ⟨13, 2, 0, 689047, 365728, 929, 16384⟩
    (by decide) selected_cut_27235

theorem selected_cut_27236 : selected 8 ⟨689068, by decide⟩
    (prefixPartial 13 365729) = some ⟨13, 2, 0, 689068, 365729, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_365729_689068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365729 ⟨689068, by decide⟩ :=
  accepted_of_selected 13 365729 ⟨689068, by decide⟩ ⟨13, 2, 0, 689068, 365729, 1481, 16384⟩
    (by decide) selected_cut_27236

theorem selected_cut_27237 : selected 8 ⟨689088, by decide⟩
    (prefixPartial 13 365730) = some ⟨13, 2, 0, 689088, 365730, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_365730_689088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365730 ⟨689088, by decide⟩ :=
  accepted_of_selected 13 365730 ⟨689088, by decide⟩ ⟨13, 2, 0, 689088, 365730, 1481, 16384⟩
    (by decide) selected_cut_27237

theorem selected_cut_27238 : selected 8 ⟨689095, by decide⟩
    (prefixPartial 13 365731) = some ⟨13, 2, 0, 689095, 365731, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_365731_689095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365731 ⟨689095, by decide⟩ :=
  accepted_of_selected 13 365731 ⟨689095, by decide⟩ ⟨13, 2, 0, 689095, 365731, 1033, 16384⟩
    (by decide) selected_cut_27238

theorem unmarked_context_12_91432_689096 : frontier 9 ⟨689096, by decide⟩
    (prefixCache 12 91432) (prefixPartial 12 91432) = false := by
  decide +kernel

theorem node_context_12_91432_689096 : EJMOriginalGlobalDAGData.nodes 9 ⟨689096, by decide⟩ =
    .split (coordinate 12) (![⟨689047, by decide⟩,⟨689068, by decide⟩,⟨689088, by decide⟩,⟨689095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91432_689096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91432 ⟨689096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91432
    ⟨689096, by decide⟩ (by decide) (![⟨689047, by decide⟩,⟨689068, by decide⟩,⟨689088, by decide⟩,⟨689095, by decide⟩]) unmarked_context_12_91432_689096 node_context_12_91432_689096
  intro a
  fin_cases a
  · exact context_13_365728_689047
  · exact context_13_365729_689068
  · exact context_13_365730_689088
  · exact context_13_365731_689095

theorem selected_cut_27239 : selected 8 ⟨689117, by decide⟩
    (prefixPartial 13 365732) = some ⟨13, 2, 0, 689117, 365732, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_365732_689117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365732 ⟨689117, by decide⟩ :=
  accepted_of_selected 13 365732 ⟨689117, by decide⟩ ⟨13, 2, 0, 689117, 365732, 1185, 16384⟩
    (by decide) selected_cut_27239

theorem selected_cut_27240 : selected 8 ⟨689138, by decide⟩
    (prefixPartial 13 365733) = some ⟨13, 2, 0, 689138, 365733, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_365733_689138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365733 ⟨689138, by decide⟩ :=
  accepted_of_selected 13 365733 ⟨689138, by decide⟩ ⟨13, 2, 0, 689138, 365733, 1445, 16384⟩
    (by decide) selected_cut_27240

theorem selected_cut_27241 : selected 8 ⟨689162, by decide⟩
    (prefixPartial 13 365734) = some ⟨13, 2, 0, 689162, 365734, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_365734_689162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365734 ⟨689162, by decide⟩ :=
  accepted_of_selected 13 365734 ⟨689162, by decide⟩ ⟨13, 2, 0, 689162, 365734, 1541, 16384⟩
    (by decide) selected_cut_27241

theorem selected_cut_27242 : selected 8 ⟨689169, by decide⟩
    (prefixPartial 13 365735) = some ⟨13, 2, 0, 689169, 365735, 753, 16384⟩ := by
  decide +kernel

theorem context_13_365735_689169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365735 ⟨689169, by decide⟩ :=
  accepted_of_selected 13 365735 ⟨689169, by decide⟩ ⟨13, 2, 0, 689169, 365735, 753, 16384⟩
    (by decide) selected_cut_27242

theorem unmarked_context_12_91433_689170 : frontier 9 ⟨689170, by decide⟩
    (prefixCache 12 91433) (prefixPartial 12 91433) = false := by
  decide +kernel

theorem node_context_12_91433_689170 : EJMOriginalGlobalDAGData.nodes 9 ⟨689170, by decide⟩ =
    .split (coordinate 12) (![⟨689117, by decide⟩,⟨689138, by decide⟩,⟨689162, by decide⟩,⟨689169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91433_689170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91433 ⟨689170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91433
    ⟨689170, by decide⟩ (by decide) (![⟨689117, by decide⟩,⟨689138, by decide⟩,⟨689162, by decide⟩,⟨689169, by decide⟩]) unmarked_context_12_91433_689170 node_context_12_91433_689170
  intro a
  fin_cases a
  · exact context_13_365732_689117
  · exact context_13_365733_689138
  · exact context_13_365734_689162
  · exact context_13_365735_689169

theorem selected_cut_27243 : selected 8 ⟨689187, by decide⟩
    (prefixPartial 13 365736) = some ⟨13, 2, 0, 689187, 365736, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_365736_689187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365736 ⟨689187, by decide⟩ :=
  accepted_of_selected 13 365736 ⟨689187, by decide⟩ ⟨13, 2, 0, 689187, 365736, 1017, 16384⟩
    (by decide) selected_cut_27243

theorem selected_cut_27244 : selected 8 ⟨689207, by decide⟩
    (prefixPartial 13 365737) = some ⟨13, 2, 0, 689207, 365737, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_365737_689207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365737 ⟨689207, by decide⟩ :=
  accepted_of_selected 13 365737 ⟨689207, by decide⟩ ⟨13, 2, 0, 689207, 365737, 1501, 16384⟩
    (by decide) selected_cut_27244

theorem selected_cut_27245 : selected 8 ⟨689221, by decide⟩
    (prefixPartial 13 365738) = some ⟨13, 2, 0, 689221, 365738, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_365738_689221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365738 ⟨689221, by decide⟩ :=
  accepted_of_selected 13 365738 ⟨689221, by decide⟩ ⟨13, 2, 0, 689221, 365738, 1261, 16384⟩
    (by decide) selected_cut_27245

theorem selected_cut_27246 : selected 8 ⟨689230, by decide⟩
    (prefixPartial 13 365739) = some ⟨13, 2, 0, 689230, 365739, 881, 16384⟩ := by
  decide +kernel

theorem context_13_365739_689230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365739 ⟨689230, by decide⟩ :=
  accepted_of_selected 13 365739 ⟨689230, by decide⟩ ⟨13, 2, 0, 689230, 365739, 881, 16384⟩
    (by decide) selected_cut_27246

theorem unmarked_context_12_91434_689231 : frontier 9 ⟨689231, by decide⟩
    (prefixCache 12 91434) (prefixPartial 12 91434) = false := by
  decide +kernel

theorem node_context_12_91434_689231 : EJMOriginalGlobalDAGData.nodes 9 ⟨689231, by decide⟩ =
    .split (coordinate 12) (![⟨689187, by decide⟩,⟨689207, by decide⟩,⟨689221, by decide⟩,⟨689230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91434_689231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91434 ⟨689231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91434
    ⟨689231, by decide⟩ (by decide) (![⟨689187, by decide⟩,⟨689207, by decide⟩,⟨689221, by decide⟩,⟨689230, by decide⟩]) unmarked_context_12_91434_689231 node_context_12_91434_689231
  intro a
  fin_cases a
  · exact context_13_365736_689187
  · exact context_13_365737_689207
  · exact context_13_365738_689221
  · exact context_13_365739_689230

theorem selected_cut_27247 : selected 8 ⟨689253, by decide⟩
    (prefixPartial 13 365740) = some ⟨13, 2, 0, 689253, 365740, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_365740_689253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365740 ⟨689253, by decide⟩ :=
  accepted_of_selected 13 365740 ⟨689253, by decide⟩ ⟨13, 2, 0, 689253, 365740, 1125, 16384⟩
    (by decide) selected_cut_27247

theorem selected_cut_27248 : selected 8 ⟨689275, by decide⟩
    (prefixPartial 13 365741) = some ⟨13, 2, 0, 689275, 365741, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_365741_689275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365741 ⟨689275, by decide⟩ :=
  accepted_of_selected 13 365741 ⟨689275, by decide⟩ ⟨13, 2, 0, 689275, 365741, 1781, 16384⟩
    (by decide) selected_cut_27248

theorem selected_cut_27249 : selected 8 ⟨689297, by decide⟩
    (prefixPartial 13 365742) = some ⟨13, 2, 0, 689297, 365742, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_365742_689297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365742 ⟨689297, by decide⟩ :=
  accepted_of_selected 13 365742 ⟨689297, by decide⟩ ⟨13, 2, 0, 689297, 365742, 1657, 16384⟩
    (by decide) selected_cut_27249

theorem selected_cut_27250 : selected 8 ⟨689308, by decide⟩
    (prefixPartial 13 365743) = some ⟨13, 2, 0, 689308, 365743, 845, 16384⟩ := by
  decide +kernel

theorem context_13_365743_689308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365743 ⟨689308, by decide⟩ :=
  accepted_of_selected 13 365743 ⟨689308, by decide⟩ ⟨13, 2, 0, 689308, 365743, 845, 16384⟩
    (by decide) selected_cut_27250

theorem unmarked_context_12_91435_689309 : frontier 9 ⟨689309, by decide⟩
    (prefixCache 12 91435) (prefixPartial 12 91435) = false := by
  decide +kernel

theorem node_context_12_91435_689309 : EJMOriginalGlobalDAGData.nodes 9 ⟨689309, by decide⟩ =
    .split (coordinate 12) (![⟨689253, by decide⟩,⟨689275, by decide⟩,⟨689297, by decide⟩,⟨689308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91435_689309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91435 ⟨689309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91435
    ⟨689309, by decide⟩ (by decide) (![⟨689253, by decide⟩,⟨689275, by decide⟩,⟨689297, by decide⟩,⟨689308, by decide⟩]) unmarked_context_12_91435_689309 node_context_12_91435_689309
  intro a
  fin_cases a
  · exact context_13_365740_689253
  · exact context_13_365741_689275
  · exact context_13_365742_689297
  · exact context_13_365743_689308

theorem unmarked_context_11_22858_689310 : frontier 10 ⟨689310, by decide⟩
    (prefixCache 11 22858) (prefixPartial 11 22858) = false := by
  decide +kernel

theorem node_context_11_22858_689310 : EJMOriginalGlobalDAGData.nodes 10 ⟨689310, by decide⟩ =
    .split (coordinate 11) (![⟨689096, by decide⟩,⟨689170, by decide⟩,⟨689231, by decide⟩,⟨689309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22858_689310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22858 ⟨689310, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22858
    ⟨689310, by decide⟩ (by decide) (![⟨689096, by decide⟩,⟨689170, by decide⟩,⟨689231, by decide⟩,⟨689309, by decide⟩]) unmarked_context_11_22858_689310 node_context_11_22858_689310
  intro a
  fin_cases a
  · exact context_12_91432_689096
  · exact context_12_91433_689170
  · exact context_12_91434_689231
  · exact context_12_91435_689309

theorem selected_cut_27251 : selected 8 ⟨689327, by decide⟩
    (prefixPartial 13 365744) = some ⟨13, 2, 0, 689327, 365744, 873, 16384⟩ := by
  decide +kernel

theorem context_13_365744_689327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365744 ⟨689327, by decide⟩ :=
  accepted_of_selected 13 365744 ⟨689327, by decide⟩ ⟨13, 2, 0, 689327, 365744, 873, 16384⟩
    (by decide) selected_cut_27251

theorem selected_cut_27252 : selected 8 ⟨689350, by decide⟩
    (prefixPartial 13 365745) = some ⟨13, 2, 0, 689350, 365745, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_365745_689350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365745 ⟨689350, by decide⟩ :=
  accepted_of_selected 13 365745 ⟨689350, by decide⟩ ⟨13, 2, 0, 689350, 365745, 1641, 16384⟩
    (by decide) selected_cut_27252

theorem selected_cut_27253 : selected 8 ⟨689366, by decide⟩
    (prefixPartial 13 365746) = some ⟨13, 2, 0, 689366, 365746, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_365746_689366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365746 ⟨689366, by decide⟩ :=
  accepted_of_selected 13 365746 ⟨689366, by decide⟩ ⟨13, 2, 0, 689366, 365746, 1353, 16384⟩
    (by decide) selected_cut_27253

theorem selected_cut_27254 : selected 8 ⟨689373, by decide⟩
    (prefixPartial 13 365747) = some ⟨13, 2, 0, 689373, 365747, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_365747_689373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365747 ⟨689373, by decide⟩ :=
  accepted_of_selected 13 365747 ⟨689373, by decide⟩ ⟨13, 2, 0, 689373, 365747, 1053, 16384⟩
    (by decide) selected_cut_27254

theorem unmarked_context_12_91436_689374 : frontier 9 ⟨689374, by decide⟩
    (prefixCache 12 91436) (prefixPartial 12 91436) = false := by
  decide +kernel

theorem node_context_12_91436_689374 : EJMOriginalGlobalDAGData.nodes 9 ⟨689374, by decide⟩ =
    .split (coordinate 12) (![⟨689327, by decide⟩,⟨689350, by decide⟩,⟨689366, by decide⟩,⟨689373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91436_689374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91436 ⟨689374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91436
    ⟨689374, by decide⟩ (by decide) (![⟨689327, by decide⟩,⟨689350, by decide⟩,⟨689366, by decide⟩,⟨689373, by decide⟩]) unmarked_context_12_91436_689374 node_context_12_91436_689374
  intro a
  fin_cases a
  · exact context_13_365744_689327
  · exact context_13_365745_689350
  · exact context_13_365746_689366
  · exact context_13_365747_689373

theorem selected_cut_27255 : selected 8 ⟨689394, by decide⟩
    (prefixPartial 13 365748) = some ⟨13, 2, 0, 689394, 365748, 925, 16384⟩ := by
  decide +kernel

theorem context_13_365748_689394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365748 ⟨689394, by decide⟩ :=
  accepted_of_selected 13 365748 ⟨689394, by decide⟩ ⟨13, 2, 0, 689394, 365748, 925, 16384⟩
    (by decide) selected_cut_27255

theorem selected_cut_27256 : selected 8 ⟨689416, by decide⟩
    (prefixPartial 13 365749) = some ⟨13, 2, 0, 689416, 365749, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_365749_689416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365749 ⟨689416, by decide⟩ :=
  accepted_of_selected 13 365749 ⟨689416, by decide⟩ ⟨13, 2, 0, 689416, 365749, 1469, 16384⟩
    (by decide) selected_cut_27256

theorem selected_cut_27257 : selected 8 ⟨689429, by decide⟩
    (prefixPartial 13 365750) = some ⟨13, 2, 0, 689429, 365750, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_365750_689429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365750 ⟨689429, by decide⟩ :=
  accepted_of_selected 13 365750 ⟨689429, by decide⟩ ⟨13, 2, 0, 689429, 365750, 1265, 16384⟩
    (by decide) selected_cut_27257

theorem selected_cut_27258 : selected 8 ⟨689436, by decide⟩
    (prefixPartial 13 365751) = some ⟨13, 2, 0, 689436, 365751, 773, 16384⟩ := by
  decide +kernel

theorem context_13_365751_689436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365751 ⟨689436, by decide⟩ :=
  accepted_of_selected 13 365751 ⟨689436, by decide⟩ ⟨13, 2, 0, 689436, 365751, 773, 16384⟩
    (by decide) selected_cut_27258

theorem unmarked_context_12_91437_689437 : frontier 9 ⟨689437, by decide⟩
    (prefixCache 12 91437) (prefixPartial 12 91437) = false := by
  decide +kernel

theorem node_context_12_91437_689437 : EJMOriginalGlobalDAGData.nodes 9 ⟨689437, by decide⟩ =
    .split (coordinate 12) (![⟨689394, by decide⟩,⟨689416, by decide⟩,⟨689429, by decide⟩,⟨689436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91437_689437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91437 ⟨689437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91437
    ⟨689437, by decide⟩ (by decide) (![⟨689394, by decide⟩,⟨689416, by decide⟩,⟨689429, by decide⟩,⟨689436, by decide⟩]) unmarked_context_12_91437_689437 node_context_12_91437_689437
  intro a
  fin_cases a
  · exact context_13_365748_689394
  · exact context_13_365749_689416
  · exact context_13_365750_689429
  · exact context_13_365751_689436

theorem selected_cut_27259 : selected 8 ⟨689455, by decide⟩
    (prefixPartial 13 365752) = some ⟨13, 2, 0, 689455, 365752, 933, 16384⟩ := by
  decide +kernel

theorem context_13_365752_689455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365752 ⟨689455, by decide⟩ :=
  accepted_of_selected 13 365752 ⟨689455, by decide⟩ ⟨13, 2, 0, 689455, 365752, 933, 16384⟩
    (by decide) selected_cut_27259

theorem selected_cut_27260 : selected 8 ⟨689479, by decide⟩
    (prefixPartial 13 365753) = some ⟨13, 2, 0, 689479, 365753, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_365753_689479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365753 ⟨689479, by decide⟩ :=
  accepted_of_selected 13 365753 ⟨689479, by decide⟩ ⟨13, 2, 0, 689479, 365753, 1665, 16384⟩
    (by decide) selected_cut_27260

theorem selected_cut_27261 : selected 8 ⟨689494, by decide⟩
    (prefixPartial 13 365754) = some ⟨13, 2, 0, 689494, 365754, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_365754_689494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365754 ⟨689494, by decide⟩ :=
  accepted_of_selected 13 365754 ⟨689494, by decide⟩ ⟨13, 2, 0, 689494, 365754, 1161, 16384⟩
    (by decide) selected_cut_27261

theorem selected_cut_27262 : selected 8 ⟨689502, by decide⟩
    (prefixPartial 13 365755) = some ⟨13, 2, 0, 689502, 365755, 981, 16384⟩ := by
  decide +kernel

theorem context_13_365755_689502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365755 ⟨689502, by decide⟩ :=
  accepted_of_selected 13 365755 ⟨689502, by decide⟩ ⟨13, 2, 0, 689502, 365755, 981, 16384⟩
    (by decide) selected_cut_27262

theorem unmarked_context_12_91438_689503 : frontier 9 ⟨689503, by decide⟩
    (prefixCache 12 91438) (prefixPartial 12 91438) = false := by
  decide +kernel

theorem node_context_12_91438_689503 : EJMOriginalGlobalDAGData.nodes 9 ⟨689503, by decide⟩ =
    .split (coordinate 12) (![⟨689455, by decide⟩,⟨689479, by decide⟩,⟨689494, by decide⟩,⟨689502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91438_689503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91438 ⟨689503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91438
    ⟨689503, by decide⟩ (by decide) (![⟨689455, by decide⟩,⟨689479, by decide⟩,⟨689494, by decide⟩,⟨689502, by decide⟩]) unmarked_context_12_91438_689503 node_context_12_91438_689503
  intro a
  fin_cases a
  · exact context_13_365752_689455
  · exact context_13_365753_689479
  · exact context_13_365754_689494
  · exact context_13_365755_689502

theorem selected_cut_27263 : selected 8 ⟨689520, by decide⟩
    (prefixPartial 13 365756) = some ⟨13, 2, 0, 689520, 365756, 901, 16384⟩ := by
  decide +kernel

theorem context_13_365756_689520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365756 ⟨689520, by decide⟩ :=
  accepted_of_selected 13 365756 ⟨689520, by decide⟩ ⟨13, 2, 0, 689520, 365756, 901, 16384⟩
    (by decide) selected_cut_27263

theorem selected_cut_27264 : selected 8 ⟨689546, by decide⟩
    (prefixPartial 13 365757) = some ⟨13, 2, 0, 689546, 365757, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_365757_689546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365757 ⟨689546, by decide⟩ :=
  accepted_of_selected 13 365757 ⟨689546, by decide⟩ ⟨13, 2, 0, 689546, 365757, 1849, 16384⟩
    (by decide) selected_cut_27264

theorem selected_cut_27265 : selected 8 ⟨689569, by decide⟩
    (prefixPartial 13 365758) = some ⟨13, 2, 0, 689569, 365758, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_365758_689569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365758 ⟨689569, by decide⟩ :=
  accepted_of_selected 13 365758 ⟨689569, by decide⟩ ⟨13, 2, 0, 689569, 365758, 1453, 16384⟩
    (by decide) selected_cut_27265

theorem selected_cut_27266 : selected 8 ⟨689580, by decide⟩
    (prefixPartial 13 365759) = some ⟨13, 2, 0, 689580, 365759, 949, 16384⟩ := by
  decide +kernel

theorem context_13_365759_689580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365759 ⟨689580, by decide⟩ :=
  accepted_of_selected 13 365759 ⟨689580, by decide⟩ ⟨13, 2, 0, 689580, 365759, 949, 16384⟩
    (by decide) selected_cut_27266

theorem unmarked_context_12_91439_689581 : frontier 9 ⟨689581, by decide⟩
    (prefixCache 12 91439) (prefixPartial 12 91439) = false := by
  decide +kernel

theorem node_context_12_91439_689581 : EJMOriginalGlobalDAGData.nodes 9 ⟨689581, by decide⟩ =
    .split (coordinate 12) (![⟨689520, by decide⟩,⟨689546, by decide⟩,⟨689569, by decide⟩,⟨689580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91439_689581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91439 ⟨689581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91439
    ⟨689581, by decide⟩ (by decide) (![⟨689520, by decide⟩,⟨689546, by decide⟩,⟨689569, by decide⟩,⟨689580, by decide⟩]) unmarked_context_12_91439_689581 node_context_12_91439_689581
  intro a
  fin_cases a
  · exact context_13_365756_689520
  · exact context_13_365757_689546
  · exact context_13_365758_689569
  · exact context_13_365759_689580

theorem unmarked_context_11_22859_689582 : frontier 10 ⟨689582, by decide⟩
    (prefixCache 11 22859) (prefixPartial 11 22859) = false := by
  decide +kernel

theorem node_context_11_22859_689582 : EJMOriginalGlobalDAGData.nodes 10 ⟨689582, by decide⟩ =
    .split (coordinate 11) (![⟨689374, by decide⟩,⟨689437, by decide⟩,⟨689503, by decide⟩,⟨689581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22859_689582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22859 ⟨689582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22859
    ⟨689582, by decide⟩ (by decide) (![⟨689374, by decide⟩,⟨689437, by decide⟩,⟨689503, by decide⟩,⟨689581, by decide⟩]) unmarked_context_11_22859_689582 node_context_11_22859_689582
  intro a
  fin_cases a
  · exact context_12_91436_689374
  · exact context_12_91437_689437
  · exact context_12_91438_689503
  · exact context_12_91439_689581

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
