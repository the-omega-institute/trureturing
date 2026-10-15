/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover302
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29091 : selected 9 ⟨734533, by decide⟩
    (prefixPartial 12 93270) = some ⟨12, 2, 0, 734533, 93270, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_93270_734533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93270 ⟨734533, by decide⟩ :=
  accepted_of_selected 12 93270 ⟨734533, by decide⟩ ⟨12, 2, 0, 734533, 93270, 3705, 65536⟩
    (by decide) selected_cut_29091

theorem selected_cut_29092 : selected 9 ⟨734584, by decide⟩
    (prefixPartial 12 93271) = some ⟨12, 2, 0, 734584, 93271, 4029, 65536⟩ := by
  decide +kernel

theorem context_12_93271_734584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93271 ⟨734584, by decide⟩ :=
  accepted_of_selected 12 93271 ⟨734584, by decide⟩ ⟨12, 2, 0, 734584, 93271, 4029, 65536⟩
    (by decide) selected_cut_29092

theorem unmarked_context_11_23317_734585 : frontier 10 ⟨734585, by decide⟩
    (prefixCache 11 23317) (prefixPartial 11 23317) = false := by
  decide +kernel

theorem node_context_11_23317_734585 : EJMOriginalGlobalDAGData.nodes 10 ⟨734585, by decide⟩ =
    .split (coordinate 11) (![⟨734487, by decide⟩,⟨642341, by decide⟩,⟨734533, by decide⟩,⟨734584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23317_734585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23317 ⟨734585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23317
    ⟨734585, by decide⟩ (by decide) (![⟨734487, by decide⟩,⟨642341, by decide⟩,⟨734533, by decide⟩,⟨734584, by decide⟩]) unmarked_context_11_23317_734585 node_context_11_23317_734585
  intro a
  fin_cases a
  · exact context_12_93268_734487
  · exact context_12_93269_642341
  · exact context_12_93270_734533
  · exact context_12_93271_734584

theorem selected_cut_29093 : selected 9 ⟨734635, by decide⟩
    (prefixPartial 12 93272) = some ⟨12, 2, 0, 734635, 93272, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_93272_734635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93272 ⟨734635, by decide⟩ :=
  accepted_of_selected 12 93272 ⟨734635, by decide⟩ ⟨12, 2, 0, 734635, 93272, 3025, 65536⟩
    (by decide) selected_cut_29093

theorem selected_cut_29094 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93273) = some ⟨12, 1, 0, 642341, 93273, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93273_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93273 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93273 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93273, 1, 65536⟩
    (by decide) selected_cut_29094

theorem selected_cut_29095 : selected 9 ⟨734676, by decide⟩
    (prefixPartial 12 93274) = some ⟨12, 2, 0, 734676, 93274, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_93274_734676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93274 ⟨734676, by decide⟩ :=
  accepted_of_selected 12 93274 ⟨734676, by decide⟩ ⟨12, 2, 0, 734676, 93274, 3041, 65536⟩
    (by decide) selected_cut_29095

theorem selected_cut_29096 : selected 9 ⟨734723, by decide⟩
    (prefixPartial 12 93275) = some ⟨12, 2, 0, 734723, 93275, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_93275_734723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93275 ⟨734723, by decide⟩ :=
  accepted_of_selected 12 93275 ⟨734723, by decide⟩ ⟨12, 2, 0, 734723, 93275, 3569, 65536⟩
    (by decide) selected_cut_29096

theorem unmarked_context_11_23318_734724 : frontier 10 ⟨734724, by decide⟩
    (prefixCache 11 23318) (prefixPartial 11 23318) = false := by
  decide +kernel

theorem node_context_11_23318_734724 : EJMOriginalGlobalDAGData.nodes 10 ⟨734724, by decide⟩ =
    .split (coordinate 11) (![⟨734635, by decide⟩,⟨642341, by decide⟩,⟨734676, by decide⟩,⟨734723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23318_734724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23318 ⟨734724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23318
    ⟨734724, by decide⟩ (by decide) (![⟨734635, by decide⟩,⟨642341, by decide⟩,⟨734676, by decide⟩,⟨734723, by decide⟩]) unmarked_context_11_23318_734724 node_context_11_23318_734724
  intro a
  fin_cases a
  · exact context_12_93272_734635
  · exact context_12_93273_642341
  · exact context_12_93274_734676
  · exact context_12_93275_734723

theorem selected_cut_29097 : selected 9 ⟨734765, by decide⟩
    (prefixPartial 12 93276) = some ⟨12, 2, 0, 734765, 93276, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_93276_734765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93276 ⟨734765, by decide⟩ :=
  accepted_of_selected 12 93276 ⟨734765, by decide⟩ ⟨12, 2, 0, 734765, 93276, 2829, 65536⟩
    (by decide) selected_cut_29097

theorem selected_cut_29098 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93277) = some ⟨12, 1, 0, 642341, 93277, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93277_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93277 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93277 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93277, 1, 65536⟩
    (by decide) selected_cut_29098

theorem selected_cut_29099 : selected 9 ⟨734808, by decide⟩
    (prefixPartial 12 93278) = some ⟨12, 2, 0, 734808, 93278, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_93278_734808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93278 ⟨734808, by decide⟩ :=
  accepted_of_selected 12 93278 ⟨734808, by decide⟩ ⟨12, 2, 0, 734808, 93278, 3229, 65536⟩
    (by decide) selected_cut_29099

theorem selected_cut_29100 : selected 9 ⟨734853, by decide⟩
    (prefixPartial 12 93279) = some ⟨12, 2, 0, 734853, 93279, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_93279_734853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93279 ⟨734853, by decide⟩ :=
  accepted_of_selected 12 93279 ⟨734853, by decide⟩ ⟨12, 2, 0, 734853, 93279, 3233, 65536⟩
    (by decide) selected_cut_29100

theorem unmarked_context_11_23319_734854 : frontier 10 ⟨734854, by decide⟩
    (prefixCache 11 23319) (prefixPartial 11 23319) = false := by
  decide +kernel

theorem node_context_11_23319_734854 : EJMOriginalGlobalDAGData.nodes 10 ⟨734854, by decide⟩ =
    .split (coordinate 11) (![⟨734765, by decide⟩,⟨642341, by decide⟩,⟨734808, by decide⟩,⟨734853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23319_734854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23319 ⟨734854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23319
    ⟨734854, by decide⟩ (by decide) (![⟨734765, by decide⟩,⟨642341, by decide⟩,⟨734808, by decide⟩,⟨734853, by decide⟩]) unmarked_context_11_23319_734854 node_context_11_23319_734854
  intro a
  fin_cases a
  · exact context_12_93276_734765
  · exact context_12_93277_642341
  · exact context_12_93278_734808
  · exact context_12_93279_734853

theorem unmarked_context_10_5829_734855 : frontier 11 ⟨734855, by decide⟩
    (prefixCache 10 5829) (prefixPartial 10 5829) = false := by
  decide +kernel

theorem node_context_10_5829_734855 : EJMOriginalGlobalDAGData.nodes 11 ⟨734855, by decide⟩ =
    .split (coordinate 10) (![⟨734437, by decide⟩,⟨734585, by decide⟩,⟨734724, by decide⟩,⟨734854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5829_734855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5829 ⟨734855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5829
    ⟨734855, by decide⟩ (by decide) (![⟨734437, by decide⟩,⟨734585, by decide⟩,⟨734724, by decide⟩,⟨734854, by decide⟩]) unmarked_context_10_5829_734855 node_context_10_5829_734855
  intro a
  fin_cases a
  · exact context_11_23316_734437
  · exact context_11_23317_734585
  · exact context_11_23318_734724
  · exact context_11_23319_734854

theorem selected_cut_29101 : selected 9 ⟨734944, by decide⟩
    (prefixPartial 12 93280) = some ⟨12, 2, 0, 734944, 93280, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_93280_734944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93280 ⟨734944, by decide⟩ :=
  accepted_of_selected 12 93280 ⟨734944, by decide⟩ ⟨12, 2, 0, 734944, 93280, 2489, 65536⟩
    (by decide) selected_cut_29101

theorem selected_cut_29102 : selected 9 ⟨219808, by decide⟩
    (prefixPartial 12 93281) = some ⟨12, 1, 0, 219808, 93281, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93281_219808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93281 ⟨219808, by decide⟩ :=
  accepted_of_selected 12 93281 ⟨219808, by decide⟩ ⟨12, 1, 0, 219808, 93281, 1, 65536⟩
    (by decide) selected_cut_29102

theorem selected_cut_29103 : selected 9 ⟨734980, by decide⟩
    (prefixPartial 12 93282) = some ⟨12, 2, 0, 734980, 93282, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_93282_734980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93282 ⟨734980, by decide⟩ :=
  accepted_of_selected 12 93282 ⟨734980, by decide⟩ ⟨12, 2, 0, 734980, 93282, 2901, 65536⟩
    (by decide) selected_cut_29103

theorem selected_cut_29104 : selected 9 ⟨735022, by decide⟩
    (prefixPartial 12 93283) = some ⟨12, 2, 0, 735022, 93283, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_93283_735022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93283 ⟨735022, by decide⟩ :=
  accepted_of_selected 12 93283 ⟨735022, by decide⟩ ⟨12, 2, 0, 735022, 93283, 3097, 65536⟩
    (by decide) selected_cut_29104

theorem unmarked_context_11_23320_735023 : frontier 10 ⟨735023, by decide⟩
    (prefixCache 11 23320) (prefixPartial 11 23320) = false := by
  decide +kernel

theorem node_context_11_23320_735023 : EJMOriginalGlobalDAGData.nodes 10 ⟨735023, by decide⟩ =
    .split (coordinate 11) (![⟨734944, by decide⟩,⟨219808, by decide⟩,⟨734980, by decide⟩,⟨735022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23320_735023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23320 ⟨735023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23320
    ⟨735023, by decide⟩ (by decide) (![⟨734944, by decide⟩,⟨219808, by decide⟩,⟨734980, by decide⟩,⟨735022, by decide⟩]) unmarked_context_11_23320_735023 node_context_11_23320_735023
  intro a
  fin_cases a
  · exact context_12_93280_734944
  · exact context_12_93281_219808
  · exact context_12_93282_734980
  · exact context_12_93283_735022

theorem selected_cut_29105 : selected 9 ⟨735063, by decide⟩
    (prefixPartial 12 93284) = some ⟨12, 2, 0, 735063, 93284, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_93284_735063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93284 ⟨735063, by decide⟩ :=
  accepted_of_selected 12 93284 ⟨735063, by decide⟩ ⟨12, 2, 0, 735063, 93284, 3097, 65536⟩
    (by decide) selected_cut_29105

theorem selected_cut_29106 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 93285) = some ⟨12, 1, 0, 642794, 93285, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93285_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93285 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 93285 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 93285, 1, 65536⟩
    (by decide) selected_cut_29106

theorem selected_cut_29107 : selected 9 ⟨735107, by decide⟩
    (prefixPartial 12 93286) = some ⟨12, 2, 0, 735107, 93286, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_93286_735107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93286 ⟨735107, by decide⟩ :=
  accepted_of_selected 12 93286 ⟨735107, by decide⟩ ⟨12, 2, 0, 735107, 93286, 3137, 65536⟩
    (by decide) selected_cut_29107

theorem selected_cut_29108 : selected 9 ⟨735148, by decide⟩
    (prefixPartial 12 93287) = some ⟨12, 2, 0, 735148, 93287, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_93287_735148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93287 ⟨735148, by decide⟩ :=
  accepted_of_selected 12 93287 ⟨735148, by decide⟩ ⟨12, 2, 0, 735148, 93287, 3417, 65536⟩
    (by decide) selected_cut_29108

theorem unmarked_context_11_23321_735149 : frontier 10 ⟨735149, by decide⟩
    (prefixCache 11 23321) (prefixPartial 11 23321) = false := by
  decide +kernel

theorem node_context_11_23321_735149 : EJMOriginalGlobalDAGData.nodes 10 ⟨735149, by decide⟩ =
    .split (coordinate 11) (![⟨735063, by decide⟩,⟨642794, by decide⟩,⟨735107, by decide⟩,⟨735148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23321_735149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23321 ⟨735149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23321
    ⟨735149, by decide⟩ (by decide) (![⟨735063, by decide⟩,⟨642794, by decide⟩,⟨735107, by decide⟩,⟨735148, by decide⟩]) unmarked_context_11_23321_735149 node_context_11_23321_735149
  intro a
  fin_cases a
  · exact context_12_93284_735063
  · exact context_12_93285_642794
  · exact context_12_93286_735107
  · exact context_12_93287_735148

theorem selected_cut_29109 : selected 9 ⟨735187, by decide⟩
    (prefixPartial 12 93288) = some ⟨12, 2, 0, 735187, 93288, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_93288_735187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93288 ⟨735187, by decide⟩ :=
  accepted_of_selected 12 93288 ⟨735187, by decide⟩ ⟨12, 2, 0, 735187, 93288, 2821, 65536⟩
    (by decide) selected_cut_29109

theorem selected_cut_29110 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 373156) = some ⟨13, 1, 0, 3444, 373156, 1, 16384⟩ := by
  decide +kernel

theorem context_13_373156_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373156 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 373156 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 373156, 1, 16384⟩
    (by decide) selected_cut_29110

theorem selected_cut_29111 : selected 8 ⟨735202, by decide⟩
    (prefixPartial 13 373157) = some ⟨13, 2, 0, 735202, 373157, 973, 16384⟩ := by
  decide +kernel

theorem context_13_373157_735202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373157 ⟨735202, by decide⟩ :=
  accepted_of_selected 13 373157 ⟨735202, by decide⟩ ⟨13, 2, 0, 735202, 373157, 973, 16384⟩
    (by decide) selected_cut_29111

theorem selected_cut_29112 : selected 8 ⟨735252, by decide⟩
    (prefixPartial 13 373158) = some ⟨13, 2, 0, 735252, 373158, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_373158_735252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373158 ⟨735252, by decide⟩ :=
  accepted_of_selected 13 373158 ⟨735252, by decide⟩ ⟨13, 2, 0, 735252, 373158, 2369, 16384⟩
    (by decide) selected_cut_29112

theorem selected_cut_29113 : selected 8 ⟨735260, by decide⟩
    (prefixPartial 13 373159) = some ⟨13, 2, 0, 735260, 373159, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_373159_735260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373159 ⟨735260, by decide⟩ :=
  accepted_of_selected 13 373159 ⟨735260, by decide⟩ ⟨13, 2, 0, 735260, 373159, 1057, 16384⟩
    (by decide) selected_cut_29113

theorem unmarked_context_12_93289_735261 : frontier 9 ⟨735261, by decide⟩
    (prefixCache 12 93289) (prefixPartial 12 93289) = false := by
  decide +kernel

theorem node_context_12_93289_735261 : EJMOriginalGlobalDAGData.nodes 9 ⟨735261, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨735202, by decide⟩,⟨735252, by decide⟩,⟨735260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93289_735261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93289 ⟨735261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93289
    ⟨735261, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨735202, by decide⟩,⟨735252, by decide⟩,⟨735260, by decide⟩]) unmarked_context_12_93289_735261 node_context_12_93289_735261
  intro a
  fin_cases a
  · exact context_13_373156_3444
  · exact context_13_373157_735202
  · exact context_13_373158_735252
  · exact context_13_373159_735260

theorem selected_cut_29114 : selected 9 ⟨735304, by decide⟩
    (prefixPartial 12 93290) = some ⟨12, 2, 0, 735304, 93290, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_93290_735304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93290 ⟨735304, by decide⟩ :=
  accepted_of_selected 12 93290 ⟨735304, by decide⟩ ⟨12, 2, 0, 735304, 93290, 2657, 65536⟩
    (by decide) selected_cut_29114

theorem selected_cut_29115 : selected 9 ⟨735348, by decide⟩
    (prefixPartial 12 93291) = some ⟨12, 2, 0, 735348, 93291, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_93291_735348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93291 ⟨735348, by decide⟩ :=
  accepted_of_selected 12 93291 ⟨735348, by decide⟩ ⟨12, 2, 0, 735348, 93291, 3025, 65536⟩
    (by decide) selected_cut_29115

theorem unmarked_context_11_23322_735349 : frontier 10 ⟨735349, by decide⟩
    (prefixCache 11 23322) (prefixPartial 11 23322) = false := by
  decide +kernel

theorem node_context_11_23322_735349 : EJMOriginalGlobalDAGData.nodes 10 ⟨735349, by decide⟩ =
    .split (coordinate 11) (![⟨735187, by decide⟩,⟨735261, by decide⟩,⟨735304, by decide⟩,⟨735348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23322_735349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23322 ⟨735349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23322
    ⟨735349, by decide⟩ (by decide) (![⟨735187, by decide⟩,⟨735261, by decide⟩,⟨735304, by decide⟩,⟨735348, by decide⟩]) unmarked_context_11_23322_735349 node_context_11_23322_735349
  intro a
  fin_cases a
  · exact context_12_93288_735187
  · exact context_12_93289_735261
  · exact context_12_93290_735304
  · exact context_12_93291_735348

theorem selected_cut_29116 : selected 9 ⟨735379, by decide⟩
    (prefixPartial 12 93292) = some ⟨12, 2, 0, 735379, 93292, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_93292_735379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93292 ⟨735379, by decide⟩ :=
  accepted_of_selected 12 93292 ⟨735379, by decide⟩ ⟨12, 2, 0, 735379, 93292, 2569, 65536⟩
    (by decide) selected_cut_29116

theorem selected_cut_29117 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 373172) = some ⟨13, 1, 0, 3444, 373172, 1, 16384⟩ := by
  decide +kernel

theorem context_13_373172_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373172 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 373172 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 373172, 1, 16384⟩
    (by decide) selected_cut_29117

theorem selected_cut_29118 : selected 8 ⟨735394, by decide⟩
    (prefixPartial 13 373173) = some ⟨13, 2, 0, 735394, 373173, 857, 16384⟩ := by
  decide +kernel

theorem context_13_373173_735394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373173 ⟨735394, by decide⟩ :=
  accepted_of_selected 13 373173 ⟨735394, by decide⟩ ⟨13, 2, 0, 735394, 373173, 857, 16384⟩
    (by decide) selected_cut_29118

theorem selected_cut_29119 : selected 8 ⟨735428, by decide⟩
    (prefixPartial 13 373174) = some ⟨13, 2, 0, 735428, 373174, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_373174_735428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373174 ⟨735428, by decide⟩ :=
  accepted_of_selected 13 373174 ⟨735428, by decide⟩ ⟨13, 2, 0, 735428, 373174, 2277, 16384⟩
    (by decide) selected_cut_29119

theorem selected_cut_29120 : selected 8 ⟨735437, by decide⟩
    (prefixPartial 13 373175) = some ⟨13, 2, 0, 735437, 373175, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_373175_735437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373175 ⟨735437, by decide⟩ :=
  accepted_of_selected 13 373175 ⟨735437, by decide⟩ ⟨13, 2, 0, 735437, 373175, 1021, 16384⟩
    (by decide) selected_cut_29120

theorem unmarked_context_12_93293_735438 : frontier 9 ⟨735438, by decide⟩
    (prefixCache 12 93293) (prefixPartial 12 93293) = false := by
  decide +kernel

theorem node_context_12_93293_735438 : EJMOriginalGlobalDAGData.nodes 9 ⟨735438, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨735394, by decide⟩,⟨735428, by decide⟩,⟨735437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93293_735438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93293 ⟨735438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93293
    ⟨735438, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨735394, by decide⟩,⟨735428, by decide⟩,⟨735437, by decide⟩]) unmarked_context_12_93293_735438 node_context_12_93293_735438
  intro a
  fin_cases a
  · exact context_13_373172_3444
  · exact context_13_373173_735394
  · exact context_13_373174_735428
  · exact context_13_373175_735437

theorem selected_cut_29121 : selected 9 ⟨735479, by decide⟩
    (prefixPartial 12 93294) = some ⟨12, 2, 0, 735479, 93294, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_93294_735479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93294 ⟨735479, by decide⟩ :=
  accepted_of_selected 12 93294 ⟨735479, by decide⟩ ⟨12, 2, 0, 735479, 93294, 2805, 65536⟩
    (by decide) selected_cut_29121

theorem selected_cut_29122 : selected 9 ⟨735516, by decide⟩
    (prefixPartial 12 93295) = some ⟨12, 2, 0, 735516, 93295, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_93295_735516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93295 ⟨735516, by decide⟩ :=
  accepted_of_selected 12 93295 ⟨735516, by decide⟩ ⟨12, 2, 0, 735516, 93295, 2621, 65536⟩
    (by decide) selected_cut_29122

theorem unmarked_context_11_23323_735517 : frontier 10 ⟨735517, by decide⟩
    (prefixCache 11 23323) (prefixPartial 11 23323) = false := by
  decide +kernel

theorem node_context_11_23323_735517 : EJMOriginalGlobalDAGData.nodes 10 ⟨735517, by decide⟩ =
    .split (coordinate 11) (![⟨735379, by decide⟩,⟨735438, by decide⟩,⟨735479, by decide⟩,⟨735516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23323_735517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23323 ⟨735517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23323
    ⟨735517, by decide⟩ (by decide) (![⟨735379, by decide⟩,⟨735438, by decide⟩,⟨735479, by decide⟩,⟨735516, by decide⟩]) unmarked_context_11_23323_735517 node_context_11_23323_735517
  intro a
  fin_cases a
  · exact context_12_93292_735379
  · exact context_12_93293_735438
  · exact context_12_93294_735479
  · exact context_12_93295_735516

theorem unmarked_context_10_5830_735518 : frontier 11 ⟨735518, by decide⟩
    (prefixCache 10 5830) (prefixPartial 10 5830) = false := by
  decide +kernel

theorem node_context_10_5830_735518 : EJMOriginalGlobalDAGData.nodes 11 ⟨735518, by decide⟩ =
    .split (coordinate 10) (![⟨735023, by decide⟩,⟨735149, by decide⟩,⟨735349, by decide⟩,⟨735517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5830_735518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5830 ⟨735518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5830
    ⟨735518, by decide⟩ (by decide) (![⟨735023, by decide⟩,⟨735149, by decide⟩,⟨735349, by decide⟩,⟨735517, by decide⟩]) unmarked_context_10_5830_735518 node_context_10_5830_735518
  intro a
  fin_cases a
  · exact context_11_23320_735023
  · exact context_11_23321_735149
  · exact context_11_23322_735349
  · exact context_11_23323_735517

theorem selected_cut_29123 : selected 9 ⟨394179, by decide⟩
    (prefixPartial 12 93296) = some ⟨12, 1, 0, 394179, 93296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93296_394179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93296 ⟨394179, by decide⟩ :=
  accepted_of_selected 12 93296 ⟨394179, by decide⟩ ⟨12, 1, 0, 394179, 93296, 1, 65536⟩
    (by decide) selected_cut_29123

theorem selected_cut_29124 : selected 9 ⟨355230, by decide⟩
    (prefixPartial 12 93297) = some ⟨12, 1, 0, 355230, 93297, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93297_355230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93297 ⟨355230, by decide⟩ :=
  accepted_of_selected 12 93297 ⟨355230, by decide⟩ ⟨12, 1, 0, 355230, 93297, 1, 65536⟩
    (by decide) selected_cut_29124

theorem selected_cut_29125 : selected 9 ⟨735553, by decide⟩
    (prefixPartial 12 93298) = some ⟨12, 2, 0, 735553, 93298, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_93298_735553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93298 ⟨735553, by decide⟩ :=
  accepted_of_selected 12 93298 ⟨735553, by decide⟩ ⟨12, 2, 0, 735553, 93298, 2717, 65536⟩
    (by decide) selected_cut_29125

theorem selected_cut_29126 : selected 9 ⟨735592, by decide⟩
    (prefixPartial 12 93299) = some ⟨12, 2, 0, 735592, 93299, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_93299_735592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93299 ⟨735592, by decide⟩ :=
  accepted_of_selected 12 93299 ⟨735592, by decide⟩ ⟨12, 2, 0, 735592, 93299, 3265, 65536⟩
    (by decide) selected_cut_29126

theorem unmarked_context_11_23324_735593 : frontier 10 ⟨735593, by decide⟩
    (prefixCache 11 23324) (prefixPartial 11 23324) = false := by
  decide +kernel

theorem node_context_11_23324_735593 : EJMOriginalGlobalDAGData.nodes 10 ⟨735593, by decide⟩ =
    .split (coordinate 11) (![⟨394179, by decide⟩,⟨355230, by decide⟩,⟨735553, by decide⟩,⟨735592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23324_735593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23324 ⟨735593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23324
    ⟨735593, by decide⟩ (by decide) (![⟨394179, by decide⟩,⟨355230, by decide⟩,⟨735553, by decide⟩,⟨735592, by decide⟩]) unmarked_context_11_23324_735593 node_context_11_23324_735593
  intro a
  fin_cases a
  · exact context_12_93296_394179
  · exact context_12_93297_355230
  · exact context_12_93298_735553
  · exact context_12_93299_735592

theorem selected_cut_29127 : selected 9 ⟨735631, by decide⟩
    (prefixPartial 12 93300) = some ⟨12, 2, 0, 735631, 93300, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_93300_735631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93300 ⟨735631, by decide⟩ :=
  accepted_of_selected 12 93300 ⟨735631, by decide⟩ ⟨12, 2, 0, 735631, 93300, 2933, 65536⟩
    (by decide) selected_cut_29127

theorem selected_cut_29128 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 93301) = some ⟨12, 1, 0, 642794, 93301, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93301_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93301 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 93301 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 93301, 1, 65536⟩
    (by decide) selected_cut_29128

theorem selected_cut_29129 : selected 9 ⟨735675, by decide⟩
    (prefixPartial 12 93302) = some ⟨12, 2, 0, 735675, 93302, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_93302_735675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93302 ⟨735675, by decide⟩ :=
  accepted_of_selected 12 93302 ⟨735675, by decide⟩ ⟨12, 2, 0, 735675, 93302, 2829, 65536⟩
    (by decide) selected_cut_29129

theorem selected_cut_29130 : selected 9 ⟨735714, by decide⟩
    (prefixPartial 12 93303) = some ⟨12, 2, 0, 735714, 93303, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_93303_735714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93303 ⟨735714, by decide⟩ :=
  accepted_of_selected 12 93303 ⟨735714, by decide⟩ ⟨12, 2, 0, 735714, 93303, 3365, 65536⟩
    (by decide) selected_cut_29130

theorem unmarked_context_11_23325_735715 : frontier 10 ⟨735715, by decide⟩
    (prefixCache 11 23325) (prefixPartial 11 23325) = false := by
  decide +kernel

theorem node_context_11_23325_735715 : EJMOriginalGlobalDAGData.nodes 10 ⟨735715, by decide⟩ =
    .split (coordinate 11) (![⟨735631, by decide⟩,⟨642794, by decide⟩,⟨735675, by decide⟩,⟨735714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23325_735715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23325 ⟨735715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23325
    ⟨735715, by decide⟩ (by decide) (![⟨735631, by decide⟩,⟨642794, by decide⟩,⟨735675, by decide⟩,⟨735714, by decide⟩]) unmarked_context_11_23325_735715 node_context_11_23325_735715
  intro a
  fin_cases a
  · exact context_12_93300_735631
  · exact context_12_93301_642794
  · exact context_12_93302_735675
  · exact context_12_93303_735714

theorem selected_cut_29131 : selected 9 ⟨735751, by decide⟩
    (prefixPartial 12 93304) = some ⟨12, 2, 0, 735751, 93304, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_93304_735751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93304 ⟨735751, by decide⟩ :=
  accepted_of_selected 12 93304 ⟨735751, by decide⟩ ⟨12, 2, 0, 735751, 93304, 2717, 65536⟩
    (by decide) selected_cut_29131

theorem selected_cut_29132 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 373220) = some ⟨13, 1, 0, 3444, 373220, 1, 16384⟩ := by
  decide +kernel

theorem context_13_373220_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373220 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 373220 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 373220, 1, 16384⟩
    (by decide) selected_cut_29132

theorem selected_cut_29133 : selected 8 ⟨735761, by decide⟩
    (prefixPartial 13 373221) = some ⟨13, 2, 0, 735761, 373221, 409, 16384⟩ := by
  decide +kernel

theorem context_13_373221_735761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373221 ⟨735761, by decide⟩ :=
  accepted_of_selected 13 373221 ⟨735761, by decide⟩ ⟨13, 2, 0, 735761, 373221, 409, 16384⟩
    (by decide) selected_cut_29133

theorem selected_cut_29134 : selected 8 ⟨735825, by decide⟩
    (prefixPartial 13 373222) = some ⟨13, 2, 0, 735825, 373222, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_373222_735825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373222 ⟨735825, by decide⟩ :=
  accepted_of_selected 13 373222 ⟨735825, by decide⟩ ⟨13, 2, 0, 735825, 373222, 2701, 16384⟩
    (by decide) selected_cut_29134

theorem selected_cut_29135 : selected 8 ⟨735833, by decide⟩
    (prefixPartial 13 373223) = some ⟨13, 2, 0, 735833, 373223, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_373223_735833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373223 ⟨735833, by decide⟩ :=
  accepted_of_selected 13 373223 ⟨735833, by decide⟩ ⟨13, 2, 0, 735833, 373223, 1117, 16384⟩
    (by decide) selected_cut_29135

theorem unmarked_context_12_93305_735834 : frontier 9 ⟨735834, by decide⟩
    (prefixCache 12 93305) (prefixPartial 12 93305) = false := by
  decide +kernel

theorem node_context_12_93305_735834 : EJMOriginalGlobalDAGData.nodes 9 ⟨735834, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨735761, by decide⟩,⟨735825, by decide⟩,⟨735833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93305_735834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93305 ⟨735834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93305
    ⟨735834, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨735761, by decide⟩,⟨735825, by decide⟩,⟨735833, by decide⟩]) unmarked_context_12_93305_735834 node_context_12_93305_735834
  intro a
  fin_cases a
  · exact context_13_373220_3444
  · exact context_13_373221_735761
  · exact context_13_373222_735825
  · exact context_13_373223_735833

theorem selected_cut_29136 : selected 9 ⟨735864, by decide⟩
    (prefixPartial 12 93306) = some ⟨12, 2, 0, 735864, 93306, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_93306_735864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93306 ⟨735864, by decide⟩ :=
  accepted_of_selected 12 93306 ⟨735864, by decide⟩ ⟨12, 2, 0, 735864, 93306, 2381, 65536⟩
    (by decide) selected_cut_29136

theorem selected_cut_29137 : selected 9 ⟨735898, by decide⟩
    (prefixPartial 12 93307) = some ⟨12, 2, 0, 735898, 93307, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_93307_735898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93307 ⟨735898, by decide⟩ :=
  accepted_of_selected 12 93307 ⟨735898, by decide⟩ ⟨12, 2, 0, 735898, 93307, 3029, 65536⟩
    (by decide) selected_cut_29137

theorem unmarked_context_11_23326_735899 : frontier 10 ⟨735899, by decide⟩
    (prefixCache 11 23326) (prefixPartial 11 23326) = false := by
  decide +kernel

theorem node_context_11_23326_735899 : EJMOriginalGlobalDAGData.nodes 10 ⟨735899, by decide⟩ =
    .split (coordinate 11) (![⟨735751, by decide⟩,⟨735834, by decide⟩,⟨735864, by decide⟩,⟨735898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23326_735899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23326 ⟨735899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23326
    ⟨735899, by decide⟩ (by decide) (![⟨735751, by decide⟩,⟨735834, by decide⟩,⟨735864, by decide⟩,⟨735898, by decide⟩]) unmarked_context_11_23326_735899 node_context_11_23326_735899
  intro a
  fin_cases a
  · exact context_12_93304_735751
  · exact context_12_93305_735834
  · exact context_12_93306_735864
  · exact context_12_93307_735898

theorem selected_cut_29138 : selected 9 ⟨397570, by decide⟩
    (prefixPartial 12 93308) = some ⟨12, 1, 0, 397570, 93308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93308_397570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93308 ⟨397570, by decide⟩ :=
  accepted_of_selected 12 93308 ⟨397570, by decide⟩ ⟨12, 1, 0, 397570, 93308, 1, 65536⟩
    (by decide) selected_cut_29138

theorem selected_cut_29139 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 373236) = some ⟨13, 1, 0, 3444, 373236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_373236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 373236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 373236, 1, 16384⟩
    (by decide) selected_cut_29139

theorem selected_cut_29140 : selected 8 ⟨735907, by decide⟩
    (prefixPartial 13 373237) = some ⟨13, 2, 0, 735907, 373237, 253, 16384⟩ := by
  decide +kernel

theorem context_13_373237_735907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373237 ⟨735907, by decide⟩ :=
  accepted_of_selected 13 373237 ⟨735907, by decide⟩ ⟨13, 2, 0, 735907, 373237, 253, 16384⟩
    (by decide) selected_cut_29140

theorem selected_cut_29141 : selected 8 ⟨735992, by decide⟩
    (prefixPartial 13 373238) = some ⟨13, 2, 0, 735992, 373238, 3273, 16384⟩ := by
  decide +kernel

theorem context_13_373238_735992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373238 ⟨735992, by decide⟩ :=
  accepted_of_selected 13 373238 ⟨735992, by decide⟩ ⟨13, 2, 0, 735992, 373238, 3273, 16384⟩
    (by decide) selected_cut_29141

theorem selected_cut_29142 : selected 8 ⟨736016, by decide⟩
    (prefixPartial 13 373239) = some ⟨13, 2, 0, 736016, 373239, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_373239_736016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373239 ⟨736016, by decide⟩ :=
  accepted_of_selected 13 373239 ⟨736016, by decide⟩ ⟨13, 2, 0, 736016, 373239, 1221, 16384⟩
    (by decide) selected_cut_29142

theorem unmarked_context_12_93309_736017 : frontier 9 ⟨736017, by decide⟩
    (prefixCache 12 93309) (prefixPartial 12 93309) = false := by
  decide +kernel

theorem node_context_12_93309_736017 : EJMOriginalGlobalDAGData.nodes 9 ⟨736017, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨735907, by decide⟩,⟨735992, by decide⟩,⟨736016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93309_736017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93309 ⟨736017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93309
    ⟨736017, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨735907, by decide⟩,⟨735992, by decide⟩,⟨736016, by decide⟩]) unmarked_context_12_93309_736017 node_context_12_93309_736017
  intro a
  fin_cases a
  · exact context_13_373236_3444
  · exact context_13_373237_735907
  · exact context_13_373238_735992
  · exact context_13_373239_736016

theorem selected_cut_29143 : selected 9 ⟨736064, by decide⟩
    (prefixPartial 12 93310) = some ⟨12, 2, 0, 736064, 93310, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_93310_736064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93310 ⟨736064, by decide⟩ :=
  accepted_of_selected 12 93310 ⟨736064, by decide⟩ ⟨12, 2, 0, 736064, 93310, 2933, 65536⟩
    (by decide) selected_cut_29143

theorem selected_cut_29144 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 93311) = some ⟨12, 1, 0, 607719, 93311, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93311_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93311 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 93311 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 93311, 1, 65536⟩
    (by decide) selected_cut_29144

theorem unmarked_context_11_23327_736065 : frontier 10 ⟨736065, by decide⟩
    (prefixCache 11 23327) (prefixPartial 11 23327) = false := by
  decide +kernel

theorem node_context_11_23327_736065 : EJMOriginalGlobalDAGData.nodes 10 ⟨736065, by decide⟩ =
    .split (coordinate 11) (![⟨397570, by decide⟩,⟨736017, by decide⟩,⟨736064, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23327_736065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23327 ⟨736065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23327
    ⟨736065, by decide⟩ (by decide) (![⟨397570, by decide⟩,⟨736017, by decide⟩,⟨736064, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_23327_736065 node_context_11_23327_736065
  intro a
  fin_cases a
  · exact context_12_93308_397570
  · exact context_12_93309_736017
  · exact context_12_93310_736064
  · exact context_12_93311_607719

theorem unmarked_context_10_5831_736066 : frontier 11 ⟨736066, by decide⟩
    (prefixCache 10 5831) (prefixPartial 10 5831) = false := by
  decide +kernel

theorem node_context_10_5831_736066 : EJMOriginalGlobalDAGData.nodes 11 ⟨736066, by decide⟩ =
    .split (coordinate 10) (![⟨735593, by decide⟩,⟨735715, by decide⟩,⟨735899, by decide⟩,⟨736065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5831_736066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5831 ⟨736066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5831
    ⟨736066, by decide⟩ (by decide) (![⟨735593, by decide⟩,⟨735715, by decide⟩,⟨735899, by decide⟩,⟨736065, by decide⟩]) unmarked_context_10_5831_736066 node_context_10_5831_736066
  intro a
  fin_cases a
  · exact context_11_23324_735593
  · exact context_11_23325_735715
  · exact context_11_23326_735899
  · exact context_11_23327_736065

theorem unmarked_context_9_1457_736067 : frontier 12 ⟨736067, by decide⟩
    (prefixCache 9 1457) (prefixPartial 9 1457) = false := by
  decide +kernel

theorem node_context_9_1457_736067 : EJMOriginalGlobalDAGData.nodes 12 ⟨736067, by decide⟩ =
    .split (coordinate 9) (![⟨734345, by decide⟩,⟨734855, by decide⟩,⟨735518, by decide⟩,⟨736066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1457_736067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1457 ⟨736067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1457
    ⟨736067, by decide⟩ (by decide) (![⟨734345, by decide⟩,⟨734855, by decide⟩,⟨735518, by decide⟩,⟨736066, by decide⟩]) unmarked_context_9_1457_736067 node_context_9_1457_736067
  intro a
  fin_cases a
  · exact context_10_5828_734345
  · exact context_10_5829_734855
  · exact context_10_5830_735518
  · exact context_10_5831_736066

theorem selected_cut_29145 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 93312) = some ⟨12, 1, 0, 450982, 93312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93312_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93312 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 93312 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 93312, 1, 65536⟩
    (by decide) selected_cut_29145

theorem selected_cut_29146 : selected 9 ⟨736093, by decide⟩
    (prefixPartial 12 93313) = some ⟨12, 2, 0, 736093, 93313, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_93313_736093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93313 ⟨736093, by decide⟩ :=
  accepted_of_selected 12 93313 ⟨736093, by decide⟩ ⟨12, 2, 0, 736093, 93313, 2281, 65536⟩
    (by decide) selected_cut_29146

theorem selected_cut_29147 : selected 9 ⟨736126, by decide⟩
    (prefixPartial 12 93314) = some ⟨12, 2, 0, 736126, 93314, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_93314_736126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93314 ⟨736126, by decide⟩ :=
  accepted_of_selected 12 93314 ⟨736126, by decide⟩ ⟨12, 2, 0, 736126, 93314, 2157, 65536⟩
    (by decide) selected_cut_29147

theorem selected_cut_29148 : selected 9 ⟨736166, by decide⟩
    (prefixPartial 12 93315) = some ⟨12, 2, 0, 736166, 93315, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_93315_736166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93315 ⟨736166, by decide⟩ :=
  accepted_of_selected 12 93315 ⟨736166, by decide⟩ ⟨12, 2, 0, 736166, 93315, 2425, 65536⟩
    (by decide) selected_cut_29148

theorem unmarked_context_11_23328_736167 : frontier 10 ⟨736167, by decide⟩
    (prefixCache 11 23328) (prefixPartial 11 23328) = false := by
  decide +kernel

theorem node_context_11_23328_736167 : EJMOriginalGlobalDAGData.nodes 10 ⟨736167, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨736093, by decide⟩,⟨736126, by decide⟩,⟨736166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23328_736167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23328 ⟨736167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23328
    ⟨736167, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨736093, by decide⟩,⟨736126, by decide⟩,⟨736166, by decide⟩]) unmarked_context_11_23328_736167 node_context_11_23328_736167
  intro a
  fin_cases a
  · exact context_12_93312_450982
  · exact context_12_93313_736093
  · exact context_12_93314_736126
  · exact context_12_93315_736166

theorem selected_cut_29149 : selected 9 ⟨736201, by decide⟩
    (prefixPartial 12 93316) = some ⟨12, 2, 0, 736201, 93316, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_93316_736201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93316 ⟨736201, by decide⟩ :=
  accepted_of_selected 12 93316 ⟨736201, by decide⟩ ⟨12, 2, 0, 736201, 93316, 2177, 65536⟩
    (by decide) selected_cut_29149

theorem selected_cut_29150 : selected 9 ⟨736233, by decide⟩
    (prefixPartial 12 93317) = some ⟨12, 2, 0, 736233, 93317, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_93317_736233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93317 ⟨736233, by decide⟩ :=
  accepted_of_selected 12 93317 ⟨736233, by decide⟩ ⟨12, 2, 0, 736233, 93317, 2253, 65536⟩
    (by decide) selected_cut_29150

theorem selected_cut_29151 : selected 9 ⟨736266, by decide⟩
    (prefixPartial 12 93318) = some ⟨12, 2, 0, 736266, 93318, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_93318_736266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93318 ⟨736266, by decide⟩ :=
  accepted_of_selected 12 93318 ⟨736266, by decide⟩ ⟨12, 2, 0, 736266, 93318, 2341, 65536⟩
    (by decide) selected_cut_29151

theorem selected_cut_29152 : selected 9 ⟨736298, by decide⟩
    (prefixPartial 12 93319) = some ⟨12, 2, 0, 736298, 93319, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_93319_736298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93319 ⟨736298, by decide⟩ :=
  accepted_of_selected 12 93319 ⟨736298, by decide⟩ ⟨12, 2, 0, 736298, 93319, 2561, 65536⟩
    (by decide) selected_cut_29152

theorem unmarked_context_11_23329_736299 : frontier 10 ⟨736299, by decide⟩
    (prefixCache 11 23329) (prefixPartial 11 23329) = false := by
  decide +kernel

theorem node_context_11_23329_736299 : EJMOriginalGlobalDAGData.nodes 10 ⟨736299, by decide⟩ =
    .split (coordinate 11) (![⟨736201, by decide⟩,⟨736233, by decide⟩,⟨736266, by decide⟩,⟨736298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23329_736299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23329 ⟨736299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23329
    ⟨736299, by decide⟩ (by decide) (![⟨736201, by decide⟩,⟨736233, by decide⟩,⟨736266, by decide⟩,⟨736298, by decide⟩]) unmarked_context_11_23329_736299 node_context_11_23329_736299
  intro a
  fin_cases a
  · exact context_12_93316_736201
  · exact context_12_93317_736233
  · exact context_12_93318_736266
  · exact context_12_93319_736298

theorem selected_cut_29153 : selected 9 ⟨736331, by decide⟩
    (prefixPartial 12 93320) = some ⟨12, 2, 0, 736331, 93320, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_93320_736331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93320 ⟨736331, by decide⟩ :=
  accepted_of_selected 12 93320 ⟨736331, by decide⟩ ⟨12, 2, 0, 736331, 93320, 2337, 65536⟩
    (by decide) selected_cut_29153

theorem selected_cut_29154 : selected 9 ⟨736370, by decide⟩
    (prefixPartial 12 93321) = some ⟨12, 2, 0, 736370, 93321, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_93321_736370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93321 ⟨736370, by decide⟩ :=
  accepted_of_selected 12 93321 ⟨736370, by decide⟩ ⟨12, 2, 0, 736370, 93321, 2701, 65536⟩
    (by decide) selected_cut_29154

theorem selected_cut_29155 : selected 9 ⟨736402, by decide⟩
    (prefixPartial 12 93322) = some ⟨12, 2, 0, 736402, 93322, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_93322_736402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93322 ⟨736402, by decide⟩ :=
  accepted_of_selected 12 93322 ⟨736402, by decide⟩ ⟨12, 2, 0, 736402, 93322, 2417, 65536⟩
    (by decide) selected_cut_29155

theorem selected_cut_29156 : selected 9 ⟨736446, by decide⟩
    (prefixPartial 12 93323) = some ⟨12, 2, 0, 736446, 93323, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_93323_736446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93323 ⟨736446, by decide⟩ :=
  accepted_of_selected 12 93323 ⟨736446, by decide⟩ ⟨12, 2, 0, 736446, 93323, 2705, 65536⟩
    (by decide) selected_cut_29156

theorem unmarked_context_11_23330_736447 : frontier 10 ⟨736447, by decide⟩
    (prefixCache 11 23330) (prefixPartial 11 23330) = false := by
  decide +kernel

theorem node_context_11_23330_736447 : EJMOriginalGlobalDAGData.nodes 10 ⟨736447, by decide⟩ =
    .split (coordinate 11) (![⟨736331, by decide⟩,⟨736370, by decide⟩,⟨736402, by decide⟩,⟨736446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23330_736447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23330 ⟨736447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23330
    ⟨736447, by decide⟩ (by decide) (![⟨736331, by decide⟩,⟨736370, by decide⟩,⟨736402, by decide⟩,⟨736446, by decide⟩]) unmarked_context_11_23330_736447 node_context_11_23330_736447
  intro a
  fin_cases a
  · exact context_12_93320_736331
  · exact context_12_93321_736370
  · exact context_12_93322_736402
  · exact context_12_93323_736446

theorem selected_cut_29157 : selected 9 ⟨736480, by decide⟩
    (prefixPartial 12 93324) = some ⟨12, 2, 0, 736480, 93324, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_93324_736480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93324 ⟨736480, by decide⟩ :=
  accepted_of_selected 12 93324 ⟨736480, by decide⟩ ⟨12, 2, 0, 736480, 93324, 1765, 65536⟩
    (by decide) selected_cut_29157

theorem selected_cut_29158 : selected 9 ⟨736508, by decide⟩
    (prefixPartial 12 93325) = some ⟨12, 2, 0, 736508, 93325, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_93325_736508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93325 ⟨736508, by decide⟩ :=
  accepted_of_selected 12 93325 ⟨736508, by decide⟩ ⟨12, 2, 0, 736508, 93325, 1925, 65536⟩
    (by decide) selected_cut_29158

theorem selected_cut_29159 : selected 9 ⟨736536, by decide⟩
    (prefixPartial 12 93326) = some ⟨12, 2, 0, 736536, 93326, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_93326_736536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93326 ⟨736536, by decide⟩ :=
  accepted_of_selected 12 93326 ⟨736536, by decide⟩ ⟨12, 2, 0, 736536, 93326, 1985, 65536⟩
    (by decide) selected_cut_29159

theorem selected_cut_29160 : selected 9 ⟨736563, by decide⟩
    (prefixPartial 12 93327) = some ⟨12, 2, 0, 736563, 93327, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_93327_736563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93327 ⟨736563, by decide⟩ :=
  accepted_of_selected 12 93327 ⟨736563, by decide⟩ ⟨12, 2, 0, 736563, 93327, 2085, 65536⟩
    (by decide) selected_cut_29160

theorem unmarked_context_11_23331_736564 : frontier 10 ⟨736564, by decide⟩
    (prefixCache 11 23331) (prefixPartial 11 23331) = false := by
  decide +kernel

theorem node_context_11_23331_736564 : EJMOriginalGlobalDAGData.nodes 10 ⟨736564, by decide⟩ =
    .split (coordinate 11) (![⟨736480, by decide⟩,⟨736508, by decide⟩,⟨736536, by decide⟩,⟨736563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23331_736564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23331 ⟨736564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23331
    ⟨736564, by decide⟩ (by decide) (![⟨736480, by decide⟩,⟨736508, by decide⟩,⟨736536, by decide⟩,⟨736563, by decide⟩]) unmarked_context_11_23331_736564 node_context_11_23331_736564
  intro a
  fin_cases a
  · exact context_12_93324_736480
  · exact context_12_93325_736508
  · exact context_12_93326_736536
  · exact context_12_93327_736563

theorem unmarked_context_10_5832_736565 : frontier 11 ⟨736565, by decide⟩
    (prefixCache 10 5832) (prefixPartial 10 5832) = false := by
  decide +kernel

theorem node_context_10_5832_736565 : EJMOriginalGlobalDAGData.nodes 11 ⟨736565, by decide⟩ =
    .split (coordinate 10) (![⟨736167, by decide⟩,⟨736299, by decide⟩,⟨736447, by decide⟩,⟨736564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5832_736565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5832 ⟨736565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5832
    ⟨736565, by decide⟩ (by decide) (![⟨736167, by decide⟩,⟨736299, by decide⟩,⟨736447, by decide⟩,⟨736564, by decide⟩]) unmarked_context_10_5832_736565 node_context_10_5832_736565
  intro a
  fin_cases a
  · exact context_11_23328_736167
  · exact context_11_23329_736299
  · exact context_11_23330_736447
  · exact context_11_23331_736564

theorem selected_cut_29161 : selected 9 ⟨736712, by decide⟩
    (prefixPartial 12 93328) = some ⟨12, 2, 0, 736712, 93328, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_93328_736712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93328 ⟨736712, by decide⟩ :=
  accepted_of_selected 12 93328 ⟨736712, by decide⟩ ⟨12, 2, 0, 736712, 93328, 3697, 65536⟩
    (by decide) selected_cut_29161

theorem selected_cut_29162 : selected 9 ⟨736757, by decide⟩
    (prefixPartial 12 93329) = some ⟨12, 2, 0, 736757, 93329, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_93329_736757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93329 ⟨736757, by decide⟩ :=
  accepted_of_selected 12 93329 ⟨736757, by decide⟩ ⟨12, 2, 0, 736757, 93329, 2733, 65536⟩
    (by decide) selected_cut_29162

theorem selected_cut_29163 : selected 9 ⟨736794, by decide⟩
    (prefixPartial 12 93330) = some ⟨12, 2, 0, 736794, 93330, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_93330_736794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93330 ⟨736794, by decide⟩ :=
  accepted_of_selected 12 93330 ⟨736794, by decide⟩ ⟨12, 2, 0, 736794, 93330, 2453, 65536⟩
    (by decide) selected_cut_29163

theorem selected_cut_29164 : selected 9 ⟨736842, by decide⟩
    (prefixPartial 12 93331) = some ⟨12, 2, 0, 736842, 93331, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_93331_736842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93331 ⟨736842, by decide⟩ :=
  accepted_of_selected 12 93331 ⟨736842, by decide⟩ ⟨12, 2, 0, 736842, 93331, 2633, 65536⟩
    (by decide) selected_cut_29164

theorem unmarked_context_11_23332_736843 : frontier 10 ⟨736843, by decide⟩
    (prefixCache 11 23332) (prefixPartial 11 23332) = false := by
  decide +kernel

theorem node_context_11_23332_736843 : EJMOriginalGlobalDAGData.nodes 10 ⟨736843, by decide⟩ =
    .split (coordinate 11) (![⟨736712, by decide⟩,⟨736757, by decide⟩,⟨736794, by decide⟩,⟨736842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23332_736843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23332 ⟨736843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23332
    ⟨736843, by decide⟩ (by decide) (![⟨736712, by decide⟩,⟨736757, by decide⟩,⟨736794, by decide⟩,⟨736842, by decide⟩]) unmarked_context_11_23332_736843 node_context_11_23332_736843
  intro a
  fin_cases a
  · exact context_12_93328_736712
  · exact context_12_93329_736757
  · exact context_12_93330_736794
  · exact context_12_93331_736842

theorem selected_cut_29165 : selected 9 ⟨736869, by decide⟩
    (prefixPartial 12 93332) = some ⟨12, 2, 0, 736869, 93332, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_93332_736869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93332 ⟨736869, by decide⟩ :=
  accepted_of_selected 12 93332 ⟨736869, by decide⟩ ⟨12, 2, 0, 736869, 93332, 2309, 65536⟩
    (by decide) selected_cut_29165

theorem selected_cut_29166 : selected 9 ⟨736905, by decide⟩
    (prefixPartial 12 93333) = some ⟨12, 2, 0, 736905, 93333, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_93333_736905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93333 ⟨736905, by decide⟩ :=
  accepted_of_selected 12 93333 ⟨736905, by decide⟩ ⟨12, 2, 0, 736905, 93333, 2573, 65536⟩
    (by decide) selected_cut_29166

theorem selected_cut_29167 : selected 9 ⟨736928, by decide⟩
    (prefixPartial 12 93334) = some ⟨12, 2, 0, 736928, 93334, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_93334_736928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93334 ⟨736928, by decide⟩ :=
  accepted_of_selected 12 93334 ⟨736928, by decide⟩ ⟨12, 2, 0, 736928, 93334, 2357, 65536⟩
    (by decide) selected_cut_29167

theorem selected_cut_29168 : selected 9 ⟨736964, by decide⟩
    (prefixPartial 12 93335) = some ⟨12, 2, 0, 736964, 93335, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_93335_736964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93335 ⟨736964, by decide⟩ :=
  accepted_of_selected 12 93335 ⟨736964, by decide⟩ ⟨12, 2, 0, 736964, 93335, 2613, 65536⟩
    (by decide) selected_cut_29168

theorem unmarked_context_11_23333_736965 : frontier 10 ⟨736965, by decide⟩
    (prefixCache 11 23333) (prefixPartial 11 23333) = false := by
  decide +kernel

theorem node_context_11_23333_736965 : EJMOriginalGlobalDAGData.nodes 10 ⟨736965, by decide⟩ =
    .split (coordinate 11) (![⟨736869, by decide⟩,⟨736905, by decide⟩,⟨736928, by decide⟩,⟨736964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23333_736965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23333 ⟨736965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23333
    ⟨736965, by decide⟩ (by decide) (![⟨736869, by decide⟩,⟨736905, by decide⟩,⟨736928, by decide⟩,⟨736964, by decide⟩]) unmarked_context_11_23333_736965 node_context_11_23333_736965
  intro a
  fin_cases a
  · exact context_12_93332_736869
  · exact context_12_93333_736905
  · exact context_12_93334_736928
  · exact context_12_93335_736964

theorem selected_cut_29169 : selected 9 ⟨736993, by decide⟩
    (prefixPartial 12 93336) = some ⟨12, 2, 0, 736993, 93336, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_93336_736993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93336 ⟨736993, by decide⟩ :=
  accepted_of_selected 12 93336 ⟨736993, by decide⟩ ⟨12, 2, 0, 736993, 93336, 2245, 65536⟩
    (by decide) selected_cut_29169

theorem selected_cut_29170 : selected 9 ⟨737033, by decide⟩
    (prefixPartial 12 93337) = some ⟨12, 2, 0, 737033, 93337, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_93337_737033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93337 ⟨737033, by decide⟩ :=
  accepted_of_selected 12 93337 ⟨737033, by decide⟩ ⟨12, 2, 0, 737033, 93337, 2641, 65536⟩
    (by decide) selected_cut_29170

theorem selected_cut_29171 : selected 9 ⟨737059, by decide⟩
    (prefixPartial 12 93338) = some ⟨12, 2, 0, 737059, 93338, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_93338_737059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93338 ⟨737059, by decide⟩ :=
  accepted_of_selected 12 93338 ⟨737059, by decide⟩ ⟨12, 2, 0, 737059, 93338, 2169, 65536⟩
    (by decide) selected_cut_29171

theorem selected_cut_29172 : selected 9 ⟨737097, by decide⟩
    (prefixPartial 12 93339) = some ⟨12, 2, 0, 737097, 93339, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_93339_737097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93339 ⟨737097, by decide⟩ :=
  accepted_of_selected 12 93339 ⟨737097, by decide⟩ ⟨12, 2, 0, 737097, 93339, 2465, 65536⟩
    (by decide) selected_cut_29172

theorem unmarked_context_11_23334_737098 : frontier 10 ⟨737098, by decide⟩
    (prefixCache 11 23334) (prefixPartial 11 23334) = false := by
  decide +kernel

theorem node_context_11_23334_737098 : EJMOriginalGlobalDAGData.nodes 10 ⟨737098, by decide⟩ =
    .split (coordinate 11) (![⟨736993, by decide⟩,⟨737033, by decide⟩,⟨737059, by decide⟩,⟨737097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23334_737098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23334 ⟨737098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23334
    ⟨737098, by decide⟩ (by decide) (![⟨736993, by decide⟩,⟨737033, by decide⟩,⟨737059, by decide⟩,⟨737097, by decide⟩]) unmarked_context_11_23334_737098 node_context_11_23334_737098
  intro a
  fin_cases a
  · exact context_12_93336_736993
  · exact context_12_93337_737033
  · exact context_12_93338_737059
  · exact context_12_93339_737097

theorem selected_cut_29173 : selected 9 ⟨737120, by decide⟩
    (prefixPartial 12 93340) = some ⟨12, 2, 0, 737120, 93340, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_93340_737120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93340 ⟨737120, by decide⟩ :=
  accepted_of_selected 12 93340 ⟨737120, by decide⟩ ⟨12, 2, 0, 737120, 93340, 1821, 65536⟩
    (by decide) selected_cut_29173

theorem selected_cut_29174 : selected 9 ⟨737150, by decide⟩
    (prefixPartial 12 93341) = some ⟨12, 2, 0, 737150, 93341, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_93341_737150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93341 ⟨737150, by decide⟩ :=
  accepted_of_selected 12 93341 ⟨737150, by decide⟩ ⟨12, 2, 0, 737150, 93341, 2081, 65536⟩
    (by decide) selected_cut_29174

theorem selected_cut_29175 : selected 9 ⟨737175, by decide⟩
    (prefixPartial 12 93342) = some ⟨12, 2, 0, 737175, 93342, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_93342_737175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93342 ⟨737175, by decide⟩ :=
  accepted_of_selected 12 93342 ⟨737175, by decide⟩ ⟨12, 2, 0, 737175, 93342, 1937, 65536⟩
    (by decide) selected_cut_29175

theorem selected_cut_29176 : selected 9 ⟨737197, by decide⟩
    (prefixPartial 12 93343) = some ⟨12, 2, 0, 737197, 93343, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_93343_737197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93343 ⟨737197, by decide⟩ :=
  accepted_of_selected 12 93343 ⟨737197, by decide⟩ ⟨12, 2, 0, 737197, 93343, 1953, 65536⟩
    (by decide) selected_cut_29176

theorem unmarked_context_11_23335_737198 : frontier 10 ⟨737198, by decide⟩
    (prefixCache 11 23335) (prefixPartial 11 23335) = false := by
  decide +kernel

theorem node_context_11_23335_737198 : EJMOriginalGlobalDAGData.nodes 10 ⟨737198, by decide⟩ =
    .split (coordinate 11) (![⟨737120, by decide⟩,⟨737150, by decide⟩,⟨737175, by decide⟩,⟨737197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23335_737198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23335 ⟨737198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23335
    ⟨737198, by decide⟩ (by decide) (![⟨737120, by decide⟩,⟨737150, by decide⟩,⟨737175, by decide⟩,⟨737197, by decide⟩]) unmarked_context_11_23335_737198 node_context_11_23335_737198
  intro a
  fin_cases a
  · exact context_12_93340_737120
  · exact context_12_93341_737150
  · exact context_12_93342_737175
  · exact context_12_93343_737197

theorem unmarked_context_10_5833_737199 : frontier 11 ⟨737199, by decide⟩
    (prefixCache 10 5833) (prefixPartial 10 5833) = false := by
  decide +kernel

theorem node_context_10_5833_737199 : EJMOriginalGlobalDAGData.nodes 11 ⟨737199, by decide⟩ =
    .split (coordinate 10) (![⟨736843, by decide⟩,⟨736965, by decide⟩,⟨737098, by decide⟩,⟨737198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5833_737199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5833 ⟨737199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5833
    ⟨737199, by decide⟩ (by decide) (![⟨736843, by decide⟩,⟨736965, by decide⟩,⟨737098, by decide⟩,⟨737198, by decide⟩]) unmarked_context_10_5833_737199 node_context_10_5833_737199
  intro a
  fin_cases a
  · exact context_11_23332_736843
  · exact context_11_23333_736965
  · exact context_11_23334_737098
  · exact context_11_23335_737198

theorem selected_cut_29177 : selected 9 ⟨737261, by decide⟩
    (prefixPartial 12 93344) = some ⟨12, 2, 0, 737261, 93344, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_93344_737261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93344 ⟨737261, by decide⟩ :=
  accepted_of_selected 12 93344 ⟨737261, by decide⟩ ⟨12, 2, 0, 737261, 93344, 2505, 65536⟩
    (by decide) selected_cut_29177

theorem selected_cut_29178 : selected 9 ⟨737281, by decide⟩
    (prefixPartial 12 93345) = some ⟨12, 2, 0, 737281, 93345, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_93345_737281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93345 ⟨737281, by decide⟩ :=
  accepted_of_selected 12 93345 ⟨737281, by decide⟩ ⟨12, 2, 0, 737281, 93345, 1557, 65536⟩
    (by decide) selected_cut_29178

theorem selected_cut_29179 : selected 9 ⟨737303, by decide⟩
    (prefixPartial 12 93346) = some ⟨12, 2, 0, 737303, 93346, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_93346_737303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93346 ⟨737303, by decide⟩ :=
  accepted_of_selected 12 93346 ⟨737303, by decide⟩ ⟨12, 2, 0, 737303, 93346, 1525, 65536⟩
    (by decide) selected_cut_29179

theorem selected_cut_29180 : selected 9 ⟨737329, by decide⟩
    (prefixPartial 12 93347) = some ⟨12, 2, 0, 737329, 93347, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_93347_737329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93347 ⟨737329, by decide⟩ :=
  accepted_of_selected 12 93347 ⟨737329, by decide⟩ ⟨12, 2, 0, 737329, 93347, 1697, 65536⟩
    (by decide) selected_cut_29180

theorem unmarked_context_11_23336_737330 : frontier 10 ⟨737330, by decide⟩
    (prefixCache 11 23336) (prefixPartial 11 23336) = false := by
  decide +kernel

theorem node_context_11_23336_737330 : EJMOriginalGlobalDAGData.nodes 10 ⟨737330, by decide⟩ =
    .split (coordinate 11) (![⟨737261, by decide⟩,⟨737281, by decide⟩,⟨737303, by decide⟩,⟨737329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23336_737330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23336 ⟨737330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23336
    ⟨737330, by decide⟩ (by decide) (![⟨737261, by decide⟩,⟨737281, by decide⟩,⟨737303, by decide⟩,⟨737329, by decide⟩]) unmarked_context_11_23336_737330 node_context_11_23336_737330
  intro a
  fin_cases a
  · exact context_12_93344_737261
  · exact context_12_93345_737281
  · exact context_12_93346_737303
  · exact context_12_93347_737329

theorem selected_cut_29181 : selected 9 ⟨737351, by decide⟩
    (prefixPartial 12 93348) = some ⟨12, 2, 0, 737351, 93348, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_93348_737351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93348 ⟨737351, by decide⟩ :=
  accepted_of_selected 12 93348 ⟨737351, by decide⟩ ⟨12, 2, 0, 737351, 93348, 1601, 65536⟩
    (by decide) selected_cut_29181

theorem selected_cut_29182 : selected 9 ⟨737373, by decide⟩
    (prefixPartial 12 93349) = some ⟨12, 2, 0, 737373, 93349, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_93349_737373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93349 ⟨737373, by decide⟩ :=
  accepted_of_selected 12 93349 ⟨737373, by decide⟩ ⟨12, 2, 0, 737373, 93349, 1517, 65536⟩
    (by decide) selected_cut_29182

theorem selected_cut_29183 : selected 9 ⟨737400, by decide⟩
    (prefixPartial 12 93350) = some ⟨12, 2, 0, 737400, 93350, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_93350_737400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93350 ⟨737400, by decide⟩ :=
  accepted_of_selected 12 93350 ⟨737400, by decide⟩ ⟨12, 2, 0, 737400, 93350, 1573, 65536⟩
    (by decide) selected_cut_29183

theorem selected_cut_29184 : selected 9 ⟨737418, by decide⟩
    (prefixPartial 12 93351) = some ⟨12, 2, 0, 737418, 93351, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_93351_737418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93351 ⟨737418, by decide⟩ :=
  accepted_of_selected 12 93351 ⟨737418, by decide⟩ ⟨12, 2, 0, 737418, 93351, 1685, 65536⟩
    (by decide) selected_cut_29184

theorem unmarked_context_11_23337_737419 : frontier 10 ⟨737419, by decide⟩
    (prefixCache 11 23337) (prefixPartial 11 23337) = false := by
  decide +kernel

theorem node_context_11_23337_737419 : EJMOriginalGlobalDAGData.nodes 10 ⟨737419, by decide⟩ =
    .split (coordinate 11) (![⟨737351, by decide⟩,⟨737373, by decide⟩,⟨737400, by decide⟩,⟨737418, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23337_737419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23337 ⟨737419, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23337
    ⟨737419, by decide⟩ (by decide) (![⟨737351, by decide⟩,⟨737373, by decide⟩,⟨737400, by decide⟩,⟨737418, by decide⟩]) unmarked_context_11_23337_737419 node_context_11_23337_737419
  intro a
  fin_cases a
  · exact context_12_93348_737351
  · exact context_12_93349_737373
  · exact context_12_93350_737400
  · exact context_12_93351_737418

theorem selected_cut_29185 : selected 9 ⟨737433, by decide⟩
    (prefixPartial 12 93352) = some ⟨12, 2, 0, 737433, 93352, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_93352_737433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93352 ⟨737433, by decide⟩ :=
  accepted_of_selected 12 93352 ⟨737433, by decide⟩ ⟨12, 2, 0, 737433, 93352, 1617, 65536⟩
    (by decide) selected_cut_29185

theorem selected_cut_29186 : selected 9 ⟨737453, by decide⟩
    (prefixPartial 12 93353) = some ⟨12, 2, 0, 737453, 93353, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_93353_737453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93353 ⟨737453, by decide⟩ :=
  accepted_of_selected 12 93353 ⟨737453, by decide⟩ ⟨12, 2, 0, 737453, 93353, 1669, 65536⟩
    (by decide) selected_cut_29186

theorem selected_cut_29187 : selected 9 ⟨737472, by decide⟩
    (prefixPartial 12 93354) = some ⟨12, 2, 0, 737472, 93354, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_93354_737472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93354 ⟨737472, by decide⟩ :=
  accepted_of_selected 12 93354 ⟨737472, by decide⟩ ⟨12, 2, 0, 737472, 93354, 1441, 65536⟩
    (by decide) selected_cut_29187

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
