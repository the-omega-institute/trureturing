/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover073
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_07107 : selected 8 ⟨207928, by decide⟩
    (prefixPartial 13 88347) = some ⟨13, 2, 0, 207928, 88347, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_88347_207928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88347 ⟨207928, by decide⟩ :=
  accepted_of_selected 13 88347 ⟨207928, by decide⟩ ⟨13, 2, 0, 207928, 88347, 1009, 16384⟩
    (by decide) selected_cut_07107

theorem unmarked_context_12_22086_207929 : frontier 9 ⟨207929, by decide⟩
    (prefixCache 12 22086) (prefixPartial 12 22086) = false := by
  decide +kernel

theorem node_context_12_22086_207929 : EJMOriginalGlobalDAGData.nodes 9 ⟨207929, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207900, by decide⟩,⟨207920, by decide⟩,⟨207928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22086_207929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22086 ⟨207929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22086
    ⟨207929, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207900, by decide⟩,⟨207920, by decide⟩,⟨207928, by decide⟩]) unmarked_context_12_22086_207929 node_context_12_22086_207929
  intro a
  fin_cases a
  · exact context_13_88344_3444
  · exact context_13_88345_207900
  · exact context_13_88346_207920
  · exact context_13_88347_207928

theorem selected_cut_07108 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88348) = some ⟨13, 1, 0, 3444, 88348, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88348_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88348 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88348 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88348, 1, 16384⟩
    (by decide) selected_cut_07108

theorem selected_cut_07109 : selected 8 ⟨207965, by decide⟩
    (prefixPartial 13 88349) = some ⟨13, 2, 0, 207965, 88349, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_88349_207965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88349 ⟨207965, by decide⟩ :=
  accepted_of_selected 13 88349 ⟨207965, by decide⟩ ⟨13, 2, 0, 207965, 88349, 2901, 16384⟩
    (by decide) selected_cut_07109

theorem selected_cut_07110 : selected 8 ⟨207984, by decide⟩
    (prefixPartial 13 88350) = some ⟨13, 2, 0, 207984, 88350, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_88350_207984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88350 ⟨207984, by decide⟩ :=
  accepted_of_selected 13 88350 ⟨207984, by decide⟩ ⟨13, 2, 0, 207984, 88350, 1757, 16384⟩
    (by decide) selected_cut_07110

theorem selected_cut_07111 : selected 8 ⟨207995, by decide⟩
    (prefixPartial 13 88351) = some ⟨13, 2, 0, 207995, 88351, 949, 16384⟩ := by
  decide +kernel

theorem context_13_88351_207995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88351 ⟨207995, by decide⟩ :=
  accepted_of_selected 13 88351 ⟨207995, by decide⟩ ⟨13, 2, 0, 207995, 88351, 949, 16384⟩
    (by decide) selected_cut_07111

theorem unmarked_context_12_22087_207996 : frontier 9 ⟨207996, by decide⟩
    (prefixCache 12 22087) (prefixPartial 12 22087) = false := by
  decide +kernel

theorem node_context_12_22087_207996 : EJMOriginalGlobalDAGData.nodes 9 ⟨207996, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨207965, by decide⟩,⟨207984, by decide⟩,⟨207995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22087_207996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22087 ⟨207996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22087
    ⟨207996, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨207965, by decide⟩,⟨207984, by decide⟩,⟨207995, by decide⟩]) unmarked_context_12_22087_207996 node_context_12_22087_207996
  intro a
  fin_cases a
  · exact context_13_88348_3444
  · exact context_13_88349_207965
  · exact context_13_88350_207984
  · exact context_13_88351_207995

theorem unmarked_context_11_5521_207997 : frontier 10 ⟨207997, by decide⟩
    (prefixCache 11 5521) (prefixPartial 11 5521) = false := by
  decide +kernel

theorem node_context_11_5521_207997 : EJMOriginalGlobalDAGData.nodes 10 ⟨207997, by decide⟩ =
    .split (coordinate 11) (![⟨207751, by decide⟩,⟨207865, by decide⟩,⟨207929, by decide⟩,⟨207996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5521_207997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5521 ⟨207997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5521
    ⟨207997, by decide⟩ (by decide) (![⟨207751, by decide⟩,⟨207865, by decide⟩,⟨207929, by decide⟩,⟨207996, by decide⟩]) unmarked_context_11_5521_207997 node_context_11_5521_207997
  intro a
  fin_cases a
  · exact context_12_22084_207751
  · exact context_12_22085_207865
  · exact context_12_22086_207929
  · exact context_12_22087_207996

theorem selected_cut_07112 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88352) = some ⟨13, 1, 0, 3444, 88352, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88352_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88352 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88352 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88352, 1, 16384⟩
    (by decide) selected_cut_07112

theorem selected_cut_07113 : selected 8 ⟨208023, by decide⟩
    (prefixPartial 13 88353) = some ⟨13, 2, 0, 208023, 88353, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_88353_208023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88353 ⟨208023, by decide⟩ :=
  accepted_of_selected 13 88353 ⟨208023, by decide⟩ ⟨13, 2, 0, 208023, 88353, 2277, 16384⟩
    (by decide) selected_cut_07113

theorem selected_cut_07114 : selected 8 ⟨208045, by decide⟩
    (prefixPartial 13 88354) = some ⟨13, 2, 0, 208045, 88354, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_88354_208045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88354 ⟨208045, by decide⟩ :=
  accepted_of_selected 13 88354 ⟨208045, by decide⟩ ⟨13, 2, 0, 208045, 88354, 1401, 16384⟩
    (by decide) selected_cut_07114

theorem selected_cut_07115 : selected 8 ⟨208053, by decide⟩
    (prefixPartial 13 88355) = some ⟨13, 2, 0, 208053, 88355, 801, 16384⟩ := by
  decide +kernel

theorem context_13_88355_208053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88355 ⟨208053, by decide⟩ :=
  accepted_of_selected 13 88355 ⟨208053, by decide⟩ ⟨13, 2, 0, 208053, 88355, 801, 16384⟩
    (by decide) selected_cut_07115

theorem unmarked_context_12_22088_208054 : frontier 9 ⟨208054, by decide⟩
    (prefixCache 12 22088) (prefixPartial 12 22088) = false := by
  decide +kernel

theorem node_context_12_22088_208054 : EJMOriginalGlobalDAGData.nodes 9 ⟨208054, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208023, by decide⟩,⟨208045, by decide⟩,⟨208053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22088_208054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22088 ⟨208054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22088
    ⟨208054, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208023, by decide⟩,⟨208045, by decide⟩,⟨208053, by decide⟩]) unmarked_context_12_22088_208054 node_context_12_22088_208054
  intro a
  fin_cases a
  · exact context_13_88352_3444
  · exact context_13_88353_208023
  · exact context_13_88354_208045
  · exact context_13_88355_208053

theorem selected_cut_07116 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88356) = some ⟨13, 1, 0, 3444, 88356, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88356_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88356 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88356 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88356, 1, 16384⟩
    (by decide) selected_cut_07116

theorem selected_cut_07117 : selected 8 ⟨208102, by decide⟩
    (prefixPartial 13 88357) = some ⟨13, 2, 0, 208102, 88357, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_88357_208102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88357 ⟨208102, by decide⟩ :=
  accepted_of_selected 13 88357 ⟨208102, by decide⟩ ⟨13, 2, 0, 208102, 88357, 3077, 16384⟩
    (by decide) selected_cut_07117

theorem selected_cut_07118 : selected 8 ⟨208132, by decide⟩
    (prefixPartial 13 88358) = some ⟨13, 2, 0, 208132, 88358, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_88358_208132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88358 ⟨208132, by decide⟩ :=
  accepted_of_selected 13 88358 ⟨208132, by decide⟩ ⟨13, 2, 0, 208132, 88358, 1997, 16384⟩
    (by decide) selected_cut_07118

theorem selected_cut_07119 : selected 8 ⟨208142, by decide⟩
    (prefixPartial 13 88359) = some ⟨13, 2, 0, 208142, 88359, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_88359_208142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88359 ⟨208142, by decide⟩ :=
  accepted_of_selected 13 88359 ⟨208142, by decide⟩ ⟨13, 2, 0, 208142, 88359, 1181, 16384⟩
    (by decide) selected_cut_07119

theorem unmarked_context_12_22089_208143 : frontier 9 ⟨208143, by decide⟩
    (prefixCache 12 22089) (prefixPartial 12 22089) = false := by
  decide +kernel

theorem node_context_12_22089_208143 : EJMOriginalGlobalDAGData.nodes 9 ⟨208143, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208102, by decide⟩,⟨208132, by decide⟩,⟨208142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22089_208143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22089 ⟨208143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22089
    ⟨208143, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208102, by decide⟩,⟨208132, by decide⟩,⟨208142, by decide⟩]) unmarked_context_12_22089_208143 node_context_12_22089_208143
  intro a
  fin_cases a
  · exact context_13_88356_3444
  · exact context_13_88357_208102
  · exact context_13_88358_208132
  · exact context_13_88359_208142

theorem selected_cut_07120 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88360) = some ⟨13, 1, 0, 3444, 88360, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88360_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88360 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88360 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88360, 1, 16384⟩
    (by decide) selected_cut_07120

theorem selected_cut_07121 : selected 8 ⟨208200, by decide⟩
    (prefixPartial 13 88361) = some ⟨13, 2, 0, 208200, 88361, 3649, 16384⟩ := by
  decide +kernel

theorem context_13_88361_208200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88361 ⟨208200, by decide⟩ :=
  accepted_of_selected 13 88361 ⟨208200, by decide⟩ ⟨13, 2, 0, 208200, 88361, 3649, 16384⟩
    (by decide) selected_cut_07121

theorem selected_cut_07122 : selected 8 ⟨208232, by decide⟩
    (prefixPartial 13 88362) = some ⟨13, 2, 0, 208232, 88362, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_88362_208232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88362 ⟨208232, by decide⟩ :=
  accepted_of_selected 13 88362 ⟨208232, by decide⟩ ⟨13, 2, 0, 208232, 88362, 2385, 16384⟩
    (by decide) selected_cut_07122

theorem selected_cut_07123 : selected 8 ⟨208243, by decide⟩
    (prefixPartial 13 88363) = some ⟨13, 2, 0, 208243, 88363, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_88363_208243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88363 ⟨208243, by decide⟩ :=
  accepted_of_selected 13 88363 ⟨208243, by decide⟩ ⟨13, 2, 0, 208243, 88363, 1277, 16384⟩
    (by decide) selected_cut_07123

theorem unmarked_context_12_22090_208244 : frontier 9 ⟨208244, by decide⟩
    (prefixCache 12 22090) (prefixPartial 12 22090) = false := by
  decide +kernel

theorem node_context_12_22090_208244 : EJMOriginalGlobalDAGData.nodes 9 ⟨208244, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208200, by decide⟩,⟨208232, by decide⟩,⟨208243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22090_208244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22090 ⟨208244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22090
    ⟨208244, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208200, by decide⟩,⟨208232, by decide⟩,⟨208243, by decide⟩]) unmarked_context_12_22090_208244 node_context_12_22090_208244
  intro a
  fin_cases a
  · exact context_13_88360_3444
  · exact context_13_88361_208200
  · exact context_13_88362_208232
  · exact context_13_88363_208243

theorem selected_cut_07124 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88364) = some ⟨13, 1, 0, 3444, 88364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88364, 1, 16384⟩
    (by decide) selected_cut_07124

theorem selected_cut_07125 : selected 8 ⟨208278, by decide⟩
    (prefixPartial 13 88365) = some ⟨13, 2, 0, 208278, 88365, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_88365_208278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88365 ⟨208278, by decide⟩ :=
  accepted_of_selected 13 88365 ⟨208278, by decide⟩ ⟨13, 2, 0, 208278, 88365, 2433, 16384⟩
    (by decide) selected_cut_07125

theorem selected_cut_07126 : selected 8 ⟨208299, by decide⟩
    (prefixPartial 13 88366) = some ⟨13, 2, 0, 208299, 88366, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_88366_208299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88366 ⟨208299, by decide⟩ :=
  accepted_of_selected 13 88366 ⟨208299, by decide⟩ ⟨13, 2, 0, 208299, 88366, 1377, 16384⟩
    (by decide) selected_cut_07126

theorem selected_cut_07127 : selected 8 ⟨208307, by decide⟩
    (prefixPartial 13 88367) = some ⟨13, 2, 0, 208307, 88367, 849, 16384⟩ := by
  decide +kernel

theorem context_13_88367_208307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88367 ⟨208307, by decide⟩ :=
  accepted_of_selected 13 88367 ⟨208307, by decide⟩ ⟨13, 2, 0, 208307, 88367, 849, 16384⟩
    (by decide) selected_cut_07127

theorem unmarked_context_12_22091_208308 : frontier 9 ⟨208308, by decide⟩
    (prefixCache 12 22091) (prefixPartial 12 22091) = false := by
  decide +kernel

theorem node_context_12_22091_208308 : EJMOriginalGlobalDAGData.nodes 9 ⟨208308, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208278, by decide⟩,⟨208299, by decide⟩,⟨208307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22091_208308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22091 ⟨208308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22091
    ⟨208308, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208278, by decide⟩,⟨208299, by decide⟩,⟨208307, by decide⟩]) unmarked_context_12_22091_208308 node_context_12_22091_208308
  intro a
  fin_cases a
  · exact context_13_88364_3444
  · exact context_13_88365_208278
  · exact context_13_88366_208299
  · exact context_13_88367_208307

theorem unmarked_context_11_5522_208309 : frontier 10 ⟨208309, by decide⟩
    (prefixCache 11 5522) (prefixPartial 11 5522) = false := by
  decide +kernel

theorem node_context_11_5522_208309 : EJMOriginalGlobalDAGData.nodes 10 ⟨208309, by decide⟩ =
    .split (coordinate 11) (![⟨208054, by decide⟩,⟨208143, by decide⟩,⟨208244, by decide⟩,⟨208308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5522_208309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5522 ⟨208309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5522
    ⟨208309, by decide⟩ (by decide) (![⟨208054, by decide⟩,⟨208143, by decide⟩,⟨208244, by decide⟩,⟨208308, by decide⟩]) unmarked_context_11_5522_208309 node_context_11_5522_208309
  intro a
  fin_cases a
  · exact context_12_22088_208054
  · exact context_12_22089_208143
  · exact context_12_22090_208244
  · exact context_12_22091_208308

theorem selected_cut_07128 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88368) = some ⟨13, 1, 0, 3444, 88368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88368, 1, 16384⟩
    (by decide) selected_cut_07128

theorem selected_cut_07129 : selected 8 ⟨208337, by decide⟩
    (prefixPartial 13 88369) = some ⟨13, 2, 0, 208337, 88369, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_88369_208337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88369 ⟨208337, by decide⟩ :=
  accepted_of_selected 13 88369 ⟨208337, by decide⟩ ⟨13, 2, 0, 208337, 88369, 2413, 16384⟩
    (by decide) selected_cut_07129

theorem selected_cut_07130 : selected 8 ⟨208356, by decide⟩
    (prefixPartial 13 88370) = some ⟨13, 2, 0, 208356, 88370, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_88370_208356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88370 ⟨208356, by decide⟩ :=
  accepted_of_selected 13 88370 ⟨208356, by decide⟩ ⟨13, 2, 0, 208356, 88370, 1809, 16384⟩
    (by decide) selected_cut_07130

theorem selected_cut_07131 : selected 8 ⟨208360, by decide⟩
    (prefixPartial 13 88371) = some ⟨13, 2, 0, 208360, 88371, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_88371_208360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88371 ⟨208360, by decide⟩ :=
  accepted_of_selected 13 88371 ⟨208360, by decide⟩ ⟨13, 2, 0, 208360, 88371, 1013, 16384⟩
    (by decide) selected_cut_07131

theorem unmarked_context_12_22092_208361 : frontier 9 ⟨208361, by decide⟩
    (prefixCache 12 22092) (prefixPartial 12 22092) = false := by
  decide +kernel

theorem node_context_12_22092_208361 : EJMOriginalGlobalDAGData.nodes 9 ⟨208361, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208337, by decide⟩,⟨208356, by decide⟩,⟨208360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22092_208361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22092 ⟨208361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22092
    ⟨208361, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208337, by decide⟩,⟨208356, by decide⟩,⟨208360, by decide⟩]) unmarked_context_12_22092_208361 node_context_12_22092_208361
  intro a
  fin_cases a
  · exact context_13_88368_3444
  · exact context_13_88369_208337
  · exact context_13_88370_208356
  · exact context_13_88371_208360

theorem selected_cut_07132 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88372) = some ⟨13, 1, 0, 3444, 88372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88372, 1, 16384⟩
    (by decide) selected_cut_07132

theorem selected_cut_07133 : selected 8 ⟨208414, by decide⟩
    (prefixPartial 13 88373) = some ⟨13, 2, 0, 208414, 88373, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_88373_208414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88373 ⟨208414, by decide⟩ :=
  accepted_of_selected 13 88373 ⟨208414, by decide⟩ ⟨13, 2, 0, 208414, 88373, 3217, 16384⟩
    (by decide) selected_cut_07133

theorem selected_cut_07134 : selected 8 ⟨208454, by decide⟩
    (prefixPartial 13 88374) = some ⟨13, 2, 0, 208454, 88374, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_88374_208454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88374 ⟨208454, by decide⟩ :=
  accepted_of_selected 13 88374 ⟨208454, by decide⟩ ⟨13, 2, 0, 208454, 88374, 2405, 16384⟩
    (by decide) selected_cut_07134

theorem selected_cut_07135 : selected 8 ⟨208463, by decide⟩
    (prefixPartial 13 88375) = some ⟨13, 2, 0, 208463, 88375, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_88375_208463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88375 ⟨208463, by decide⟩ :=
  accepted_of_selected 13 88375 ⟨208463, by decide⟩ ⟨13, 2, 0, 208463, 88375, 1289, 16384⟩
    (by decide) selected_cut_07135

theorem unmarked_context_12_22093_208464 : frontier 9 ⟨208464, by decide⟩
    (prefixCache 12 22093) (prefixPartial 12 22093) = false := by
  decide +kernel

theorem node_context_12_22093_208464 : EJMOriginalGlobalDAGData.nodes 9 ⟨208464, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208414, by decide⟩,⟨208454, by decide⟩,⟨208463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22093_208464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22093 ⟨208464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22093
    ⟨208464, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208414, by decide⟩,⟨208454, by decide⟩,⟨208463, by decide⟩]) unmarked_context_12_22093_208464 node_context_12_22093_208464
  intro a
  fin_cases a
  · exact context_13_88372_3444
  · exact context_13_88373_208414
  · exact context_13_88374_208454
  · exact context_13_88375_208463

theorem selected_cut_07136 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88376) = some ⟨13, 1, 0, 3444, 88376, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88376_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88376 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88376 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88376, 1, 16384⟩
    (by decide) selected_cut_07136

theorem selected_cut_07137 : selected 8 ⟨208497, by decide⟩
    (prefixPartial 13 88377) = some ⟨13, 2, 0, 208497, 88377, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_88377_208497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88377 ⟨208497, by decide⟩ :=
  accepted_of_selected 13 88377 ⟨208497, by decide⟩ ⟨13, 2, 0, 208497, 88377, 2449, 16384⟩
    (by decide) selected_cut_07137

theorem selected_cut_07138 : selected 8 ⟨208519, by decide⟩
    (prefixPartial 13 88378) = some ⟨13, 2, 0, 208519, 88378, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_88378_208519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88378 ⟨208519, by decide⟩ :=
  accepted_of_selected 13 88378 ⟨208519, by decide⟩ ⟨13, 2, 0, 208519, 88378, 1497, 16384⟩
    (by decide) selected_cut_07138

theorem selected_cut_07139 : selected 8 ⟨208529, by decide⟩
    (prefixPartial 13 88379) = some ⟨13, 2, 0, 208529, 88379, 981, 16384⟩ := by
  decide +kernel

theorem context_13_88379_208529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88379 ⟨208529, by decide⟩ :=
  accepted_of_selected 13 88379 ⟨208529, by decide⟩ ⟨13, 2, 0, 208529, 88379, 981, 16384⟩
    (by decide) selected_cut_07139

theorem unmarked_context_12_22094_208530 : frontier 9 ⟨208530, by decide⟩
    (prefixCache 12 22094) (prefixPartial 12 22094) = false := by
  decide +kernel

theorem node_context_12_22094_208530 : EJMOriginalGlobalDAGData.nodes 9 ⟨208530, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208497, by decide⟩,⟨208519, by decide⟩,⟨208529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22094_208530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22094 ⟨208530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22094
    ⟨208530, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208497, by decide⟩,⟨208519, by decide⟩,⟨208529, by decide⟩]) unmarked_context_12_22094_208530 node_context_12_22094_208530
  intro a
  fin_cases a
  · exact context_13_88376_3444
  · exact context_13_88377_208497
  · exact context_13_88378_208519
  · exact context_13_88379_208529

theorem selected_cut_07140 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88380) = some ⟨13, 1, 0, 3444, 88380, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88380_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88380 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88380 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88380, 1, 16384⟩
    (by decide) selected_cut_07140

theorem selected_cut_07141 : selected 8 ⟨208561, by decide⟩
    (prefixPartial 13 88381) = some ⟨13, 2, 0, 208561, 88381, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_88381_208561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88381 ⟨208561, by decide⟩ :=
  accepted_of_selected 13 88381 ⟨208561, by decide⟩ ⟨13, 2, 0, 208561, 88381, 2345, 16384⟩
    (by decide) selected_cut_07141

theorem selected_cut_07142 : selected 8 ⟨208580, by decide⟩
    (prefixPartial 13 88382) = some ⟨13, 2, 0, 208580, 88382, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_88382_208580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88382 ⟨208580, by decide⟩ :=
  accepted_of_selected 13 88382 ⟨208580, by decide⟩ ⟨13, 2, 0, 208580, 88382, 1693, 16384⟩
    (by decide) selected_cut_07142

theorem selected_cut_07143 : selected 8 ⟨208589, by decide⟩
    (prefixPartial 13 88383) = some ⟨13, 2, 0, 208589, 88383, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_88383_208589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88383 ⟨208589, by decide⟩ :=
  accepted_of_selected 13 88383 ⟨208589, by decide⟩ ⟨13, 2, 0, 208589, 88383, 1033, 16384⟩
    (by decide) selected_cut_07143

theorem unmarked_context_12_22095_208590 : frontier 9 ⟨208590, by decide⟩
    (prefixCache 12 22095) (prefixPartial 12 22095) = false := by
  decide +kernel

theorem node_context_12_22095_208590 : EJMOriginalGlobalDAGData.nodes 9 ⟨208590, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208561, by decide⟩,⟨208580, by decide⟩,⟨208589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22095_208590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22095 ⟨208590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22095
    ⟨208590, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208561, by decide⟩,⟨208580, by decide⟩,⟨208589, by decide⟩]) unmarked_context_12_22095_208590 node_context_12_22095_208590
  intro a
  fin_cases a
  · exact context_13_88380_3444
  · exact context_13_88381_208561
  · exact context_13_88382_208580
  · exact context_13_88383_208589

theorem unmarked_context_11_5523_208591 : frontier 10 ⟨208591, by decide⟩
    (prefixCache 11 5523) (prefixPartial 11 5523) = false := by
  decide +kernel

theorem node_context_11_5523_208591 : EJMOriginalGlobalDAGData.nodes 10 ⟨208591, by decide⟩ =
    .split (coordinate 11) (![⟨208361, by decide⟩,⟨208464, by decide⟩,⟨208530, by decide⟩,⟨208590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5523_208591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5523 ⟨208591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5523
    ⟨208591, by decide⟩ (by decide) (![⟨208361, by decide⟩,⟨208464, by decide⟩,⟨208530, by decide⟩,⟨208590, by decide⟩]) unmarked_context_11_5523_208591 node_context_11_5523_208591
  intro a
  fin_cases a
  · exact context_12_22092_208361
  · exact context_12_22093_208464
  · exact context_12_22094_208530
  · exact context_12_22095_208590

theorem unmarked_context_10_1380_208592 : frontier 11 ⟨208592, by decide⟩
    (prefixCache 10 1380) (prefixPartial 10 1380) = false := by
  decide +kernel

theorem node_context_10_1380_208592 : EJMOriginalGlobalDAGData.nodes 11 ⟨208592, by decide⟩ =
    .split (coordinate 10) (![⟨207679, by decide⟩,⟨207997, by decide⟩,⟨208309, by decide⟩,⟨208591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1380_208592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1380 ⟨208592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1380
    ⟨208592, by decide⟩ (by decide) (![⟨207679, by decide⟩,⟨207997, by decide⟩,⟨208309, by decide⟩,⟨208591, by decide⟩]) unmarked_context_10_1380_208592 node_context_10_1380_208592
  intro a
  fin_cases a
  · exact context_11_5520_207679
  · exact context_11_5521_207997
  · exact context_11_5522_208309
  · exact context_11_5523_208591

theorem selected_cut_07144 : selected 9 ⟨208637, by decide⟩
    (prefixPartial 12 22096) = some ⟨12, 2, 0, 208637, 22096, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_22096_208637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22096 ⟨208637, by decide⟩ :=
  accepted_of_selected 12 22096 ⟨208637, by decide⟩ ⟨12, 2, 0, 208637, 22096, 3965, 65536⟩
    (by decide) selected_cut_07144

theorem selected_cut_07145 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88388) = some ⟨13, 1, 0, 3444, 88388, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88388_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88388 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88388 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88388, 1, 16384⟩
    (by decide) selected_cut_07145

theorem selected_cut_07146 : selected 8 ⟨208664, by decide⟩
    (prefixPartial 13 88389) = some ⟨13, 2, 0, 208664, 88389, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_88389_208664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88389 ⟨208664, by decide⟩ :=
  accepted_of_selected 13 88389 ⟨208664, by decide⟩ ⟨13, 2, 0, 208664, 88389, 2101, 16384⟩
    (by decide) selected_cut_07146

theorem selected_cut_07147 : selected 8 ⟨208687, by decide⟩
    (prefixPartial 13 88390) = some ⟨13, 2, 0, 208687, 88390, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_88390_208687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88390 ⟨208687, by decide⟩ :=
  accepted_of_selected 13 88390 ⟨208687, by decide⟩ ⟨13, 2, 0, 208687, 88390, 1997, 16384⟩
    (by decide) selected_cut_07147

theorem selected_cut_07148 : selected 8 ⟨208698, by decide⟩
    (prefixPartial 13 88391) = some ⟨13, 2, 0, 208698, 88391, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_88391_208698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88391 ⟨208698, by decide⟩ :=
  accepted_of_selected 13 88391 ⟨208698, by decide⟩ ⟨13, 2, 0, 208698, 88391, 1153, 16384⟩
    (by decide) selected_cut_07148

theorem unmarked_context_12_22097_208699 : frontier 9 ⟨208699, by decide⟩
    (prefixCache 12 22097) (prefixPartial 12 22097) = false := by
  decide +kernel

theorem node_context_12_22097_208699 : EJMOriginalGlobalDAGData.nodes 9 ⟨208699, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208664, by decide⟩,⟨208687, by decide⟩,⟨208698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22097_208699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22097 ⟨208699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22097
    ⟨208699, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208664, by decide⟩,⟨208687, by decide⟩,⟨208698, by decide⟩]) unmarked_context_12_22097_208699 node_context_12_22097_208699
  intro a
  fin_cases a
  · exact context_13_88388_3444
  · exact context_13_88389_208664
  · exact context_13_88390_208687
  · exact context_13_88391_208698

theorem selected_cut_07149 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88392) = some ⟨13, 1, 0, 3444, 88392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88392, 1, 16384⟩
    (by decide) selected_cut_07149

theorem selected_cut_07150 : selected 8 ⟨208718, by decide⟩
    (prefixPartial 13 88393) = some ⟨13, 2, 0, 208718, 88393, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_88393_208718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88393 ⟨208718, by decide⟩ :=
  accepted_of_selected 13 88393 ⟨208718, by decide⟩ ⟨13, 2, 0, 208718, 88393, 1813, 16384⟩
    (by decide) selected_cut_07150

theorem selected_cut_07151 : selected 8 ⟨208736, by decide⟩
    (prefixPartial 13 88394) = some ⟨13, 2, 0, 208736, 88394, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_88394_208736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88394 ⟨208736, by decide⟩ :=
  accepted_of_selected 13 88394 ⟨208736, by decide⟩ ⟨13, 2, 0, 208736, 88394, 1445, 16384⟩
    (by decide) selected_cut_07151

theorem selected_cut_07152 : selected 8 ⟨208742, by decide⟩
    (prefixPartial 13 88395) = some ⟨13, 2, 0, 208742, 88395, 937, 16384⟩ := by
  decide +kernel

theorem context_13_88395_208742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88395 ⟨208742, by decide⟩ :=
  accepted_of_selected 13 88395 ⟨208742, by decide⟩ ⟨13, 2, 0, 208742, 88395, 937, 16384⟩
    (by decide) selected_cut_07152

theorem unmarked_context_12_22098_208743 : frontier 9 ⟨208743, by decide⟩
    (prefixCache 12 22098) (prefixPartial 12 22098) = false := by
  decide +kernel

theorem node_context_12_22098_208743 : EJMOriginalGlobalDAGData.nodes 9 ⟨208743, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208718, by decide⟩,⟨208736, by decide⟩,⟨208742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22098_208743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22098 ⟨208743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22098
    ⟨208743, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208718, by decide⟩,⟨208736, by decide⟩,⟨208742, by decide⟩]) unmarked_context_12_22098_208743 node_context_12_22098_208743
  intro a
  fin_cases a
  · exact context_13_88392_3444
  · exact context_13_88393_208718
  · exact context_13_88394_208736
  · exact context_13_88395_208742

theorem selected_cut_07153 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88396) = some ⟨13, 1, 0, 3444, 88396, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88396_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88396 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88396 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88396, 1, 16384⟩
    (by decide) selected_cut_07153

theorem selected_cut_07154 : selected 8 ⟨208768, by decide⟩
    (prefixPartial 13 88397) = some ⟨13, 2, 0, 208768, 88397, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_88397_208768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88397 ⟨208768, by decide⟩ :=
  accepted_of_selected 13 88397 ⟨208768, by decide⟩ ⟨13, 2, 0, 208768, 88397, 1953, 16384⟩
    (by decide) selected_cut_07154

theorem selected_cut_07155 : selected 8 ⟨208788, by decide⟩
    (prefixPartial 13 88398) = some ⟨13, 2, 0, 208788, 88398, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_88398_208788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88398 ⟨208788, by decide⟩ :=
  accepted_of_selected 13 88398 ⟨208788, by decide⟩ ⟨13, 2, 0, 208788, 88398, 1681, 16384⟩
    (by decide) selected_cut_07155

theorem selected_cut_07156 : selected 8 ⟨208800, by decide⟩
    (prefixPartial 13 88399) = some ⟨13, 2, 0, 208800, 88399, 989, 16384⟩ := by
  decide +kernel

theorem context_13_88399_208800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88399 ⟨208800, by decide⟩ :=
  accepted_of_selected 13 88399 ⟨208800, by decide⟩ ⟨13, 2, 0, 208800, 88399, 989, 16384⟩
    (by decide) selected_cut_07156

theorem unmarked_context_12_22099_208801 : frontier 9 ⟨208801, by decide⟩
    (prefixCache 12 22099) (prefixPartial 12 22099) = false := by
  decide +kernel

theorem node_context_12_22099_208801 : EJMOriginalGlobalDAGData.nodes 9 ⟨208801, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208768, by decide⟩,⟨208788, by decide⟩,⟨208800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22099_208801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22099 ⟨208801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22099
    ⟨208801, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208768, by decide⟩,⟨208788, by decide⟩,⟨208800, by decide⟩]) unmarked_context_12_22099_208801 node_context_12_22099_208801
  intro a
  fin_cases a
  · exact context_13_88396_3444
  · exact context_13_88397_208768
  · exact context_13_88398_208788
  · exact context_13_88399_208800

theorem unmarked_context_11_5524_208802 : frontier 10 ⟨208802, by decide⟩
    (prefixCache 11 5524) (prefixPartial 11 5524) = false := by
  decide +kernel

theorem node_context_11_5524_208802 : EJMOriginalGlobalDAGData.nodes 10 ⟨208802, by decide⟩ =
    .split (coordinate 11) (![⟨208637, by decide⟩,⟨208699, by decide⟩,⟨208743, by decide⟩,⟨208801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5524_208802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5524 ⟨208802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5524
    ⟨208802, by decide⟩ (by decide) (![⟨208637, by decide⟩,⟨208699, by decide⟩,⟨208743, by decide⟩,⟨208801, by decide⟩]) unmarked_context_11_5524_208802 node_context_11_5524_208802
  intro a
  fin_cases a
  · exact context_12_22096_208637
  · exact context_12_22097_208699
  · exact context_12_22098_208743
  · exact context_12_22099_208801

theorem selected_cut_07157 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88400) = some ⟨13, 1, 0, 3444, 88400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88400, 1, 16384⟩
    (by decide) selected_cut_07157

theorem selected_cut_07158 : selected 8 ⟨208845, by decide⟩
    (prefixPartial 13 88401) = some ⟨13, 2, 0, 208845, 88401, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_88401_208845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88401 ⟨208845, by decide⟩ :=
  accepted_of_selected 13 88401 ⟨208845, by decide⟩ ⟨13, 2, 0, 208845, 88401, 2381, 16384⟩
    (by decide) selected_cut_07158

theorem selected_cut_07159 : selected 8 ⟨208868, by decide⟩
    (prefixPartial 13 88402) = some ⟨13, 2, 0, 208868, 88402, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_88402_208868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88402 ⟨208868, by decide⟩ :=
  accepted_of_selected 13 88402 ⟨208868, by decide⟩ ⟨13, 2, 0, 208868, 88402, 1937, 16384⟩
    (by decide) selected_cut_07159

theorem selected_cut_07160 : selected 8 ⟨208879, by decide⟩
    (prefixPartial 13 88403) = some ⟨13, 2, 0, 208879, 88403, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_88403_208879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88403 ⟨208879, by decide⟩ :=
  accepted_of_selected 13 88403 ⟨208879, by decide⟩ ⟨13, 2, 0, 208879, 88403, 1005, 16384⟩
    (by decide) selected_cut_07160

theorem unmarked_context_12_22100_208880 : frontier 9 ⟨208880, by decide⟩
    (prefixCache 12 22100) (prefixPartial 12 22100) = false := by
  decide +kernel

theorem node_context_12_22100_208880 : EJMOriginalGlobalDAGData.nodes 9 ⟨208880, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208845, by decide⟩,⟨208868, by decide⟩,⟨208879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22100_208880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22100 ⟨208880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22100
    ⟨208880, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208845, by decide⟩,⟨208868, by decide⟩,⟨208879, by decide⟩]) unmarked_context_12_22100_208880 node_context_12_22100_208880
  intro a
  fin_cases a
  · exact context_13_88400_3444
  · exact context_13_88401_208845
  · exact context_13_88402_208868
  · exact context_13_88403_208879

theorem selected_cut_07161 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 22101) = some ⟨12, 1, 0, 170504, 22101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22101_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22101 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 22101 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 22101, 1, 65536⟩
    (by decide) selected_cut_07161

theorem selected_cut_07162 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88408) = some ⟨13, 1, 0, 3444, 88408, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88408_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88408 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88408 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88408, 1, 16384⟩
    (by decide) selected_cut_07162

theorem selected_cut_07163 : selected 8 ⟨208916, by decide⟩
    (prefixPartial 13 88409) = some ⟨13, 2, 0, 208916, 88409, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_88409_208916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88409 ⟨208916, by decide⟩ :=
  accepted_of_selected 13 88409 ⟨208916, by decide⟩ ⟨13, 2, 0, 208916, 88409, 2393, 16384⟩
    (by decide) selected_cut_07163

theorem selected_cut_07164 : selected 8 ⟨208935, by decide⟩
    (prefixPartial 13 88410) = some ⟨13, 2, 0, 208935, 88410, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_88410_208935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88410 ⟨208935, by decide⟩ :=
  accepted_of_selected 13 88410 ⟨208935, by decide⟩ ⟨13, 2, 0, 208935, 88410, 1833, 16384⟩
    (by decide) selected_cut_07164

theorem selected_cut_07165 : selected 8 ⟨208945, by decide⟩
    (prefixPartial 13 88411) = some ⟨13, 2, 0, 208945, 88411, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_88411_208945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88411 ⟨208945, by decide⟩ :=
  accepted_of_selected 13 88411 ⟨208945, by decide⟩ ⟨13, 2, 0, 208945, 88411, 1105, 16384⟩
    (by decide) selected_cut_07165

theorem unmarked_context_12_22102_208946 : frontier 9 ⟨208946, by decide⟩
    (prefixCache 12 22102) (prefixPartial 12 22102) = false := by
  decide +kernel

theorem node_context_12_22102_208946 : EJMOriginalGlobalDAGData.nodes 9 ⟨208946, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208916, by decide⟩,⟨208935, by decide⟩,⟨208945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22102_208946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22102 ⟨208946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22102
    ⟨208946, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208916, by decide⟩,⟨208935, by decide⟩,⟨208945, by decide⟩]) unmarked_context_12_22102_208946 node_context_12_22102_208946
  intro a
  fin_cases a
  · exact context_13_88408_3444
  · exact context_13_88409_208916
  · exact context_13_88410_208935
  · exact context_13_88411_208945

theorem selected_cut_07166 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88412) = some ⟨13, 1, 0, 3444, 88412, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88412_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88412 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88412 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88412, 1, 16384⟩
    (by decide) selected_cut_07166

theorem selected_cut_07167 : selected 8 ⟨208990, by decide⟩
    (prefixPartial 13 88413) = some ⟨13, 2, 0, 208990, 88413, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_88413_208990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88413 ⟨208990, by decide⟩ :=
  accepted_of_selected 13 88413 ⟨208990, by decide⟩ ⟨13, 2, 0, 208990, 88413, 2661, 16384⟩
    (by decide) selected_cut_07167

theorem selected_cut_07168 : selected 8 ⟨209018, by decide⟩
    (prefixPartial 13 88414) = some ⟨13, 2, 0, 209018, 88414, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_88414_209018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88414 ⟨209018, by decide⟩ :=
  accepted_of_selected 13 88414 ⟨209018, by decide⟩ ⟨13, 2, 0, 209018, 88414, 2213, 16384⟩
    (by decide) selected_cut_07168

theorem selected_cut_07169 : selected 8 ⟨209029, by decide⟩
    (prefixPartial 13 88415) = some ⟨13, 2, 0, 209029, 88415, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_88415_209029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88415 ⟨209029, by decide⟩ :=
  accepted_of_selected 13 88415 ⟨209029, by decide⟩ ⟨13, 2, 0, 209029, 88415, 1125, 16384⟩
    (by decide) selected_cut_07169

theorem unmarked_context_12_22103_209030 : frontier 9 ⟨209030, by decide⟩
    (prefixCache 12 22103) (prefixPartial 12 22103) = false := by
  decide +kernel

theorem node_context_12_22103_209030 : EJMOriginalGlobalDAGData.nodes 9 ⟨209030, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨208990, by decide⟩,⟨209018, by decide⟩,⟨209029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22103_209030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22103 ⟨209030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22103
    ⟨209030, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨208990, by decide⟩,⟨209018, by decide⟩,⟨209029, by decide⟩]) unmarked_context_12_22103_209030 node_context_12_22103_209030
  intro a
  fin_cases a
  · exact context_13_88412_3444
  · exact context_13_88413_208990
  · exact context_13_88414_209018
  · exact context_13_88415_209029

theorem unmarked_context_11_5525_209031 : frontier 10 ⟨209031, by decide⟩
    (prefixCache 11 5525) (prefixPartial 11 5525) = false := by
  decide +kernel

theorem node_context_11_5525_209031 : EJMOriginalGlobalDAGData.nodes 10 ⟨209031, by decide⟩ =
    .split (coordinate 11) (![⟨208880, by decide⟩,⟨170504, by decide⟩,⟨208946, by decide⟩,⟨209030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5525_209031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5525 ⟨209031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5525
    ⟨209031, by decide⟩ (by decide) (![⟨208880, by decide⟩,⟨170504, by decide⟩,⟨208946, by decide⟩,⟨209030, by decide⟩]) unmarked_context_11_5525_209031 node_context_11_5525_209031
  intro a
  fin_cases a
  · exact context_12_22100_208880
  · exact context_12_22101_170504
  · exact context_12_22102_208946
  · exact context_12_22103_209030

theorem selected_cut_07170 : selected 9 ⟨209071, by decide⟩
    (prefixPartial 12 22104) = some ⟨12, 2, 0, 209071, 22104, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_22104_209071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22104 ⟨209071, by decide⟩ :=
  accepted_of_selected 12 22104 ⟨209071, by decide⟩ ⟨12, 2, 0, 209071, 22104, 3501, 65536⟩
    (by decide) selected_cut_07170

theorem selected_cut_07171 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88420) = some ⟨13, 1, 0, 3444, 88420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88420, 1, 16384⟩
    (by decide) selected_cut_07171

theorem selected_cut_07172 : selected 8 ⟨209096, by decide⟩
    (prefixPartial 13 88421) = some ⟨13, 2, 0, 209096, 88421, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_88421_209096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88421 ⟨209096, by decide⟩ :=
  accepted_of_selected 13 88421 ⟨209096, by decide⟩ ⟨13, 2, 0, 209096, 88421, 1553, 16384⟩
    (by decide) selected_cut_07172

theorem selected_cut_07173 : selected 8 ⟨209123, by decide⟩
    (prefixPartial 13 88422) = some ⟨13, 2, 0, 209123, 88422, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_88422_209123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88422 ⟨209123, by decide⟩ :=
  accepted_of_selected 13 88422 ⟨209123, by decide⟩ ⟨13, 2, 0, 209123, 88422, 1985, 16384⟩
    (by decide) selected_cut_07173

theorem selected_cut_07174 : selected 8 ⟨209139, by decide⟩
    (prefixPartial 13 88423) = some ⟨13, 2, 0, 209139, 88423, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_88423_209139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88423 ⟨209139, by decide⟩ :=
  accepted_of_selected 13 88423 ⟨209139, by decide⟩ ⟨13, 2, 0, 209139, 88423, 1165, 16384⟩
    (by decide) selected_cut_07174

theorem unmarked_context_12_22105_209140 : frontier 9 ⟨209140, by decide⟩
    (prefixCache 12 22105) (prefixPartial 12 22105) = false := by
  decide +kernel

theorem node_context_12_22105_209140 : EJMOriginalGlobalDAGData.nodes 9 ⟨209140, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209096, by decide⟩,⟨209123, by decide⟩,⟨209139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22105_209140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22105 ⟨209140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22105
    ⟨209140, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209096, by decide⟩,⟨209123, by decide⟩,⟨209139, by decide⟩]) unmarked_context_12_22105_209140 node_context_12_22105_209140
  intro a
  fin_cases a
  · exact context_13_88420_3444
  · exact context_13_88421_209096
  · exact context_13_88422_209123
  · exact context_13_88423_209139

theorem selected_cut_07175 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88424) = some ⟨13, 1, 0, 3444, 88424, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88424_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88424 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88424 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88424, 1, 16384⟩
    (by decide) selected_cut_07175

theorem selected_cut_07176 : selected 8 ⟨209171, by decide⟩
    (prefixPartial 13 88425) = some ⟨13, 2, 0, 209171, 88425, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_88425_209171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88425 ⟨209171, by decide⟩ :=
  accepted_of_selected 13 88425 ⟨209171, by decide⟩ ⟨13, 2, 0, 209171, 88425, 2177, 16384⟩
    (by decide) selected_cut_07176

theorem selected_cut_07177 : selected 8 ⟨209201, by decide⟩
    (prefixPartial 13 88426) = some ⟨13, 2, 0, 209201, 88426, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_88426_209201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88426 ⟨209201, by decide⟩ :=
  accepted_of_selected 13 88426 ⟨209201, by decide⟩ ⟨13, 2, 0, 209201, 88426, 2481, 16384⟩
    (by decide) selected_cut_07177

theorem selected_cut_07178 : selected 8 ⟨209213, by decide⟩
    (prefixPartial 13 88427) = some ⟨13, 2, 0, 209213, 88427, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_88427_209213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88427 ⟨209213, by decide⟩ :=
  accepted_of_selected 13 88427 ⟨209213, by decide⟩ ⟨13, 2, 0, 209213, 88427, 1317, 16384⟩
    (by decide) selected_cut_07178

theorem unmarked_context_12_22106_209214 : frontier 9 ⟨209214, by decide⟩
    (prefixCache 12 22106) (prefixPartial 12 22106) = false := by
  decide +kernel

theorem node_context_12_22106_209214 : EJMOriginalGlobalDAGData.nodes 9 ⟨209214, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209171, by decide⟩,⟨209201, by decide⟩,⟨209213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22106_209214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22106 ⟨209214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22106
    ⟨209214, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209171, by decide⟩,⟨209201, by decide⟩,⟨209213, by decide⟩]) unmarked_context_12_22106_209214 node_context_12_22106_209214
  intro a
  fin_cases a
  · exact context_13_88424_3444
  · exact context_13_88425_209171
  · exact context_13_88426_209201
  · exact context_13_88427_209213

theorem selected_cut_07179 : selected 9 ⟨209260, by decide⟩
    (prefixPartial 12 22107) = some ⟨12, 2, 0, 209260, 22107, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_22107_209260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22107 ⟨209260, by decide⟩ :=
  accepted_of_selected 12 22107 ⟨209260, by decide⟩ ⟨12, 2, 0, 209260, 22107, 3765, 65536⟩
    (by decide) selected_cut_07179

theorem unmarked_context_11_5526_209261 : frontier 10 ⟨209261, by decide⟩
    (prefixCache 11 5526) (prefixPartial 11 5526) = false := by
  decide +kernel

theorem node_context_11_5526_209261 : EJMOriginalGlobalDAGData.nodes 10 ⟨209261, by decide⟩ =
    .split (coordinate 11) (![⟨209071, by decide⟩,⟨209140, by decide⟩,⟨209214, by decide⟩,⟨209260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5526_209261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5526 ⟨209261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5526
    ⟨209261, by decide⟩ (by decide) (![⟨209071, by decide⟩,⟨209140, by decide⟩,⟨209214, by decide⟩,⟨209260, by decide⟩]) unmarked_context_11_5526_209261 node_context_11_5526_209261
  intro a
  fin_cases a
  · exact context_12_22104_209071
  · exact context_12_22105_209140
  · exact context_12_22106_209214
  · exact context_12_22107_209260

theorem selected_cut_07180 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88432) = some ⟨13, 1, 0, 3444, 88432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88432, 1, 16384⟩
    (by decide) selected_cut_07180

theorem selected_cut_07181 : selected 8 ⟨209277, by decide⟩
    (prefixPartial 13 88433) = some ⟨13, 2, 0, 209277, 88433, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_88433_209277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88433 ⟨209277, by decide⟩ :=
  accepted_of_selected 13 88433 ⟨209277, by decide⟩ ⟨13, 2, 0, 209277, 88433, 1309, 16384⟩
    (by decide) selected_cut_07181

theorem selected_cut_07182 : selected 8 ⟨209298, by decide⟩
    (prefixPartial 13 88434) = some ⟨13, 2, 0, 209298, 88434, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_88434_209298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88434 ⟨209298, by decide⟩ :=
  accepted_of_selected 13 88434 ⟨209298, by decide⟩ ⟨13, 2, 0, 209298, 88434, 1881, 16384⟩
    (by decide) selected_cut_07182

theorem selected_cut_07183 : selected 8 ⟨209306, by decide⟩
    (prefixPartial 13 88435) = some ⟨13, 2, 0, 209306, 88435, 997, 16384⟩ := by
  decide +kernel

theorem context_13_88435_209306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88435 ⟨209306, by decide⟩ :=
  accepted_of_selected 13 88435 ⟨209306, by decide⟩ ⟨13, 2, 0, 209306, 88435, 997, 16384⟩
    (by decide) selected_cut_07183

theorem unmarked_context_12_22108_209307 : frontier 9 ⟨209307, by decide⟩
    (prefixCache 12 22108) (prefixPartial 12 22108) = false := by
  decide +kernel

theorem node_context_12_22108_209307 : EJMOriginalGlobalDAGData.nodes 9 ⟨209307, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209277, by decide⟩,⟨209298, by decide⟩,⟨209306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22108_209307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22108 ⟨209307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22108
    ⟨209307, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209277, by decide⟩,⟨209298, by decide⟩,⟨209306, by decide⟩]) unmarked_context_12_22108_209307 node_context_12_22108_209307
  intro a
  fin_cases a
  · exact context_13_88432_3444
  · exact context_13_88433_209277
  · exact context_13_88434_209298
  · exact context_13_88435_209306

theorem selected_cut_07184 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88436) = some ⟨13, 1, 0, 3444, 88436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88436, 1, 16384⟩
    (by decide) selected_cut_07184

theorem selected_cut_07185 : selected 8 ⟨209333, by decide⟩
    (prefixPartial 13 88437) = some ⟨13, 2, 0, 209333, 88437, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_88437_209333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88437 ⟨209333, by decide⟩ :=
  accepted_of_selected 13 88437 ⟨209333, by decide⟩ ⟨13, 2, 0, 209333, 88437, 1589, 16384⟩
    (by decide) selected_cut_07185

theorem selected_cut_07186 : selected 8 ⟨209378, by decide⟩
    (prefixPartial 13 88438) = some ⟨13, 2, 0, 209378, 88438, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_88438_209378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88438 ⟨209378, by decide⟩ :=
  accepted_of_selected 13 88438 ⟨209378, by decide⟩ ⟨13, 2, 0, 209378, 88438, 2537, 16384⟩
    (by decide) selected_cut_07186

theorem selected_cut_07187 : selected 8 ⟨209389, by decide⟩
    (prefixPartial 13 88439) = some ⟨13, 2, 0, 209389, 88439, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_88439_209389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88439 ⟨209389, by decide⟩ :=
  accepted_of_selected 13 88439 ⟨209389, by decide⟩ ⟨13, 2, 0, 209389, 88439, 1193, 16384⟩
    (by decide) selected_cut_07187

theorem unmarked_context_12_22109_209390 : frontier 9 ⟨209390, by decide⟩
    (prefixCache 12 22109) (prefixPartial 12 22109) = false := by
  decide +kernel

theorem node_context_12_22109_209390 : EJMOriginalGlobalDAGData.nodes 9 ⟨209390, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209333, by decide⟩,⟨209378, by decide⟩,⟨209389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22109_209390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22109 ⟨209390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22109
    ⟨209390, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209333, by decide⟩,⟨209378, by decide⟩,⟨209389, by decide⟩]) unmarked_context_12_22109_209390 node_context_12_22109_209390
  intro a
  fin_cases a
  · exact context_13_88436_3444
  · exact context_13_88437_209333
  · exact context_13_88438_209378
  · exact context_13_88439_209389

theorem selected_cut_07188 : selected 9 ⟨209438, by decide⟩
    (prefixPartial 12 22110) = some ⟨12, 2, 0, 209438, 22110, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_22110_209438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22110 ⟨209438, by decide⟩ :=
  accepted_of_selected 12 22110 ⟨209438, by decide⟩ ⟨12, 2, 0, 209438, 22110, 4021, 65536⟩
    (by decide) selected_cut_07188

theorem selected_cut_07189 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88444) = some ⟨13, 1, 0, 3444, 88444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88444, 1, 16384⟩
    (by decide) selected_cut_07189

theorem selected_cut_07190 : selected 8 ⟨209454, by decide⟩
    (prefixPartial 13 88445) = some ⟨13, 2, 0, 209454, 88445, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_88445_209454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88445 ⟨209454, by decide⟩ :=
  accepted_of_selected 13 88445 ⟨209454, by decide⟩ ⟨13, 2, 0, 209454, 88445, 1325, 16384⟩
    (by decide) selected_cut_07190

theorem selected_cut_07191 : selected 8 ⟨209475, by decide⟩
    (prefixPartial 13 88446) = some ⟨13, 2, 0, 209475, 88446, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_88446_209475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88446 ⟨209475, by decide⟩ :=
  accepted_of_selected 13 88446 ⟨209475, by decide⟩ ⟨13, 2, 0, 209475, 88446, 1929, 16384⟩
    (by decide) selected_cut_07191

theorem selected_cut_07192 : selected 8 ⟨209485, by decide⟩
    (prefixPartial 13 88447) = some ⟨13, 2, 0, 209485, 88447, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_88447_209485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88447 ⟨209485, by decide⟩ :=
  accepted_of_selected 13 88447 ⟨209485, by decide⟩ ⟨13, 2, 0, 209485, 88447, 1045, 16384⟩
    (by decide) selected_cut_07192

theorem unmarked_context_12_22111_209486 : frontier 9 ⟨209486, by decide⟩
    (prefixCache 12 22111) (prefixPartial 12 22111) = false := by
  decide +kernel

theorem node_context_12_22111_209486 : EJMOriginalGlobalDAGData.nodes 9 ⟨209486, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209454, by decide⟩,⟨209475, by decide⟩,⟨209485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22111_209486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22111 ⟨209486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22111
    ⟨209486, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209454, by decide⟩,⟨209475, by decide⟩,⟨209485, by decide⟩]) unmarked_context_12_22111_209486 node_context_12_22111_209486
  intro a
  fin_cases a
  · exact context_13_88444_3444
  · exact context_13_88445_209454
  · exact context_13_88446_209475
  · exact context_13_88447_209485

theorem unmarked_context_11_5527_209487 : frontier 10 ⟨209487, by decide⟩
    (prefixCache 11 5527) (prefixPartial 11 5527) = false := by
  decide +kernel

theorem node_context_11_5527_209487 : EJMOriginalGlobalDAGData.nodes 10 ⟨209487, by decide⟩ =
    .split (coordinate 11) (![⟨209307, by decide⟩,⟨209390, by decide⟩,⟨209438, by decide⟩,⟨209486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5527_209487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5527 ⟨209487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5527
    ⟨209487, by decide⟩ (by decide) (![⟨209307, by decide⟩,⟨209390, by decide⟩,⟨209438, by decide⟩,⟨209486, by decide⟩]) unmarked_context_11_5527_209487 node_context_11_5527_209487
  intro a
  fin_cases a
  · exact context_12_22108_209307
  · exact context_12_22109_209390
  · exact context_12_22110_209438
  · exact context_12_22111_209486

theorem unmarked_context_10_1381_209488 : frontier 11 ⟨209488, by decide⟩
    (prefixCache 10 1381) (prefixPartial 10 1381) = false := by
  decide +kernel

theorem node_context_10_1381_209488 : EJMOriginalGlobalDAGData.nodes 11 ⟨209488, by decide⟩ =
    .split (coordinate 10) (![⟨208802, by decide⟩,⟨209031, by decide⟩,⟨209261, by decide⟩,⟨209487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1381_209488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1381 ⟨209488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1381
    ⟨209488, by decide⟩ (by decide) (![⟨208802, by decide⟩,⟨209031, by decide⟩,⟨209261, by decide⟩,⟨209487, by decide⟩]) unmarked_context_10_1381_209488 node_context_10_1381_209488
  intro a
  fin_cases a
  · exact context_11_5524_208802
  · exact context_11_5525_209031
  · exact context_11_5526_209261
  · exact context_11_5527_209487

theorem selected_cut_07193 : selected 9 ⟨209530, by decide⟩
    (prefixPartial 12 22112) = some ⟨12, 2, 0, 209530, 22112, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_22112_209530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22112 ⟨209530, by decide⟩ :=
  accepted_of_selected 12 22112 ⟨209530, by decide⟩ ⟨12, 2, 0, 209530, 22112, 3785, 65536⟩
    (by decide) selected_cut_07193

theorem selected_cut_07194 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88452) = some ⟨13, 1, 0, 3444, 88452, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88452_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88452 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88452 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88452, 1, 16384⟩
    (by decide) selected_cut_07194

theorem selected_cut_07195 : selected 8 ⟨209560, by decide⟩
    (prefixPartial 13 88453) = some ⟨13, 2, 0, 209560, 88453, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_88453_209560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88453 ⟨209560, by decide⟩ :=
  accepted_of_selected 13 88453 ⟨209560, by decide⟩ ⟨13, 2, 0, 209560, 88453, 1853, 16384⟩
    (by decide) selected_cut_07195

theorem selected_cut_07196 : selected 8 ⟨209589, by decide⟩
    (prefixPartial 13 88454) = some ⟨13, 2, 0, 209589, 88454, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_88454_209589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88454 ⟨209589, by decide⟩ :=
  accepted_of_selected 13 88454 ⟨209589, by decide⟩ ⟨13, 2, 0, 209589, 88454, 2081, 16384⟩
    (by decide) selected_cut_07196

theorem selected_cut_07197 : selected 8 ⟨209605, by decide⟩
    (prefixPartial 13 88455) = some ⟨13, 2, 0, 209605, 88455, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_88455_209605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88455 ⟨209605, by decide⟩ :=
  accepted_of_selected 13 88455 ⟨209605, by decide⟩ ⟨13, 2, 0, 209605, 88455, 1185, 16384⟩
    (by decide) selected_cut_07197

theorem unmarked_context_12_22113_209606 : frontier 9 ⟨209606, by decide⟩
    (prefixCache 12 22113) (prefixPartial 12 22113) = false := by
  decide +kernel

theorem node_context_12_22113_209606 : EJMOriginalGlobalDAGData.nodes 9 ⟨209606, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨209560, by decide⟩,⟨209589, by decide⟩,⟨209605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22113_209606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22113 ⟨209606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22113
    ⟨209606, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨209560, by decide⟩,⟨209589, by decide⟩,⟨209605, by decide⟩]) unmarked_context_12_22113_209606 node_context_12_22113_209606
  intro a
  fin_cases a
  · exact context_13_88452_3444
  · exact context_13_88453_209560
  · exact context_13_88454_209589
  · exact context_13_88455_209605

theorem selected_cut_07198 : selected 9 ⟨209648, by decide⟩
    (prefixPartial 12 22114) = some ⟨12, 2, 0, 209648, 22114, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_22114_209648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22114 ⟨209648, by decide⟩ :=
  accepted_of_selected 12 22114 ⟨209648, by decide⟩ ⟨12, 2, 0, 209648, 22114, 3717, 65536⟩
    (by decide) selected_cut_07198

theorem selected_cut_07199 : selected 9 ⟨209695, by decide⟩
    (prefixPartial 12 22115) = some ⟨12, 2, 0, 209695, 22115, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_22115_209695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22115 ⟨209695, by decide⟩ :=
  accepted_of_selected 12 22115 ⟨209695, by decide⟩ ⟨12, 2, 0, 209695, 22115, 4037, 65536⟩
    (by decide) selected_cut_07199

theorem unmarked_context_11_5528_209696 : frontier 10 ⟨209696, by decide⟩
    (prefixCache 11 5528) (prefixPartial 11 5528) = false := by
  decide +kernel

theorem node_context_11_5528_209696 : EJMOriginalGlobalDAGData.nodes 10 ⟨209696, by decide⟩ =
    .split (coordinate 11) (![⟨209530, by decide⟩,⟨209606, by decide⟩,⟨209648, by decide⟩,⟨209695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5528_209696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5528 ⟨209696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5528
    ⟨209696, by decide⟩ (by decide) (![⟨209530, by decide⟩,⟨209606, by decide⟩,⟨209648, by decide⟩,⟨209695, by decide⟩]) unmarked_context_11_5528_209696 node_context_11_5528_209696
  intro a
  fin_cases a
  · exact context_12_22112_209530
  · exact context_12_22113_209606
  · exact context_12_22114_209648
  · exact context_12_22115_209695

theorem selected_cut_07200 : selected 9 ⟨209743, by decide⟩
    (prefixPartial 12 22116) = some ⟨12, 2, 0, 209743, 22116, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_22116_209743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22116 ⟨209743, by decide⟩ :=
  accepted_of_selected 12 22116 ⟨209743, by decide⟩ ⟨12, 2, 0, 209743, 22116, 3617, 65536⟩
    (by decide) selected_cut_07200

theorem selected_cut_07201 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 88468) = some ⟨13, 1, 0, 3444, 88468, 1, 16384⟩ := by
  decide +kernel

theorem context_13_88468_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88468 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 88468 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 88468, 1, 16384⟩
    (by decide) selected_cut_07201

theorem selected_cut_07202 : selected 8 ⟨209762, by decide⟩
    (prefixPartial 13 88469) = some ⟨13, 2, 0, 209762, 88469, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_88469_209762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88469 ⟨209762, by decide⟩ :=
  accepted_of_selected 13 88469 ⟨209762, by decide⟩ ⟨13, 2, 0, 209762, 88469, 1529, 16384⟩
    (by decide) selected_cut_07202

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
