/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover065
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_5380_190260 : frontier 10 ⟨190260, by decide⟩
    (prefixCache 11 5380) (prefixPartial 11 5380) = false := by
  decide +kernel

theorem node_context_11_5380_190260 : EJMOriginalGlobalDAGData.nodes 10 ⟨190260, by decide⟩ =
    .split (coordinate 11) (![⟨190141, by decide⟩,⟨190185, by decide⟩,⟨190259, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5380_190260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5380 ⟨190260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5380
    ⟨190260, by decide⟩ (by decide) (![⟨190141, by decide⟩,⟨190185, by decide⟩,⟨190259, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5380_190260 node_context_11_5380_190260
  intro a
  fin_cases a
  · exact context_12_21520_190141
  · exact context_12_21521_190185
  · exact context_12_21522_190259
  · exact context_12_21523_893

theorem selected_cut_06338 : selected 9 ⟨190348, by decide⟩
    (prefixPartial 12 21524) = some ⟨12, 2, 0, 190348, 21524, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_21524_190348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21524 ⟨190348, by decide⟩ :=
  accepted_of_selected 12 21524 ⟨190348, by decide⟩ ⟨12, 2, 0, 190348, 21524, 3961, 65536⟩
    (by decide) selected_cut_06338

theorem selected_cut_06339 : selected 9 ⟨190481, by decide⟩
    (prefixPartial 12 21525) = some ⟨12, 2, 0, 190481, 21525, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_21525_190481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21525 ⟨190481, by decide⟩ :=
  accepted_of_selected 12 21525 ⟨190481, by decide⟩ ⟨12, 2, 0, 190481, 21525, 1993, 65536⟩
    (by decide) selected_cut_06339

theorem selected_cut_06340 : selected 8 ⟨190511, by decide⟩
    (prefixPartial 13 86104) = some ⟨13, 2, 0, 190511, 86104, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_86104_190511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86104 ⟨190511, by decide⟩ :=
  accepted_of_selected 13 86104 ⟨190511, by decide⟩ ⟨13, 2, 0, 190511, 86104, 1949, 16384⟩
    (by decide) selected_cut_06340

theorem selected_cut_06341 : selected 8 ⟨190579, by decide⟩
    (prefixPartial 13 86105) = some ⟨13, 2, 0, 190579, 86105, 3473, 16384⟩ := by
  decide +kernel

theorem context_13_86105_190579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86105 ⟨190579, by decide⟩ :=
  accepted_of_selected 13 86105 ⟨190579, by decide⟩ ⟨13, 2, 0, 190579, 86105, 3473, 16384⟩
    (by decide) selected_cut_06341

theorem selected_cut_06342 : selected 8 ⟨190604, by decide⟩
    (prefixPartial 13 86106) = some ⟨13, 2, 0, 190604, 86106, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_86106_190604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86106 ⟨190604, by decide⟩ :=
  accepted_of_selected 13 86106 ⟨190604, by decide⟩ ⟨13, 2, 0, 190604, 86106, 1933, 16384⟩
    (by decide) selected_cut_06342

theorem selected_cut_06343 : selected 8 ⟨190614, by decide⟩
    (prefixPartial 13 86107) = some ⟨13, 2, 0, 190614, 86107, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_86107_190614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86107 ⟨190614, by decide⟩ :=
  accepted_of_selected 13 86107 ⟨190614, by decide⟩ ⟨13, 2, 0, 190614, 86107, 1061, 16384⟩
    (by decide) selected_cut_06343

theorem unmarked_context_12_21526_190615 : frontier 9 ⟨190615, by decide⟩
    (prefixCache 12 21526) (prefixPartial 12 21526) = false := by
  decide +kernel

theorem node_context_12_21526_190615 : EJMOriginalGlobalDAGData.nodes 9 ⟨190615, by decide⟩ =
    .split (coordinate 12) (![⟨190511, by decide⟩,⟨190579, by decide⟩,⟨190604, by decide⟩,⟨190614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21526_190615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21526 ⟨190615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21526
    ⟨190615, by decide⟩ (by decide) (![⟨190511, by decide⟩,⟨190579, by decide⟩,⟨190604, by decide⟩,⟨190614, by decide⟩]) unmarked_context_12_21526_190615 node_context_12_21526_190615
  intro a
  fin_cases a
  · exact context_13_86104_190511
  · exact context_13_86105_190579
  · exact context_13_86106_190604
  · exact context_13_86107_190614

theorem selected_cut_06344 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21527) = some ⟨12, 1, 0, 893, 21527, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21527_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21527 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21527 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21527, 1, 65536⟩
    (by decide) selected_cut_06344

theorem unmarked_context_11_5381_190616 : frontier 10 ⟨190616, by decide⟩
    (prefixCache 11 5381) (prefixPartial 11 5381) = false := by
  decide +kernel

theorem node_context_11_5381_190616 : EJMOriginalGlobalDAGData.nodes 10 ⟨190616, by decide⟩ =
    .split (coordinate 11) (![⟨190348, by decide⟩,⟨190481, by decide⟩,⟨190615, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5381_190616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5381 ⟨190616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5381
    ⟨190616, by decide⟩ (by decide) (![⟨190348, by decide⟩,⟨190481, by decide⟩,⟨190615, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5381_190616 node_context_11_5381_190616
  intro a
  fin_cases a
  · exact context_12_21524_190348
  · exact context_12_21525_190481
  · exact context_12_21526_190615
  · exact context_12_21527_893

theorem selected_cut_06345 : selected 8 ⟨190629, by decide⟩
    (prefixPartial 13 86112) = some ⟨13, 2, 0, 190629, 86112, 825, 16384⟩ := by
  decide +kernel

theorem context_13_86112_190629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86112 ⟨190629, by decide⟩ :=
  accepted_of_selected 13 86112 ⟨190629, by decide⟩ ⟨13, 2, 0, 190629, 86112, 825, 16384⟩
    (by decide) selected_cut_06345

theorem selected_cut_06346 : selected 8 ⟨190653, by decide⟩
    (prefixPartial 13 86113) = some ⟨13, 2, 0, 190653, 86113, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_86113_190653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86113 ⟨190653, by decide⟩ :=
  accepted_of_selected 13 86113 ⟨190653, by decide⟩ ⟨13, 2, 0, 190653, 86113, 1885, 16384⟩
    (by decide) selected_cut_06346

theorem selected_cut_06347 : selected 8 ⟨190672, by decide⟩
    (prefixPartial 13 86114) = some ⟨13, 2, 0, 190672, 86114, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_86114_190672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86114 ⟨190672, by decide⟩ :=
  accepted_of_selected 13 86114 ⟨190672, by decide⟩ ⟨13, 2, 0, 190672, 86114, 1337, 16384⟩
    (by decide) selected_cut_06347

theorem selected_cut_06348 : selected 8 ⟨190682, by decide⟩
    (prefixPartial 13 86115) = some ⟨13, 2, 0, 190682, 86115, 801, 16384⟩ := by
  decide +kernel

theorem context_13_86115_190682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86115 ⟨190682, by decide⟩ :=
  accepted_of_selected 13 86115 ⟨190682, by decide⟩ ⟨13, 2, 0, 190682, 86115, 801, 16384⟩
    (by decide) selected_cut_06348

theorem unmarked_context_12_21528_190683 : frontier 9 ⟨190683, by decide⟩
    (prefixCache 12 21528) (prefixPartial 12 21528) = false := by
  decide +kernel

theorem node_context_12_21528_190683 : EJMOriginalGlobalDAGData.nodes 9 ⟨190683, by decide⟩ =
    .split (coordinate 12) (![⟨190629, by decide⟩,⟨190653, by decide⟩,⟨190672, by decide⟩,⟨190682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21528_190683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21528 ⟨190683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21528
    ⟨190683, by decide⟩ (by decide) (![⟨190629, by decide⟩,⟨190653, by decide⟩,⟨190672, by decide⟩,⟨190682, by decide⟩]) unmarked_context_12_21528_190683 node_context_12_21528_190683
  intro a
  fin_cases a
  · exact context_13_86112_190629
  · exact context_13_86113_190653
  · exact context_13_86114_190672
  · exact context_13_86115_190682

theorem selected_cut_06349 : selected 8 ⟨190696, by decide⟩
    (prefixPartial 13 86116) = some ⟨13, 2, 0, 190696, 86116, 865, 16384⟩ := by
  decide +kernel

theorem context_13_86116_190696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86116 ⟨190696, by decide⟩ :=
  accepted_of_selected 13 86116 ⟨190696, by decide⟩ ⟨13, 2, 0, 190696, 86116, 865, 16384⟩
    (by decide) selected_cut_06349

theorem selected_cut_06350 : selected 8 ⟨190718, by decide⟩
    (prefixPartial 13 86117) = some ⟨13, 2, 0, 190718, 86117, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_86117_190718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86117 ⟨190718, by decide⟩ :=
  accepted_of_selected 13 86117 ⟨190718, by decide⟩ ⟨13, 2, 0, 190718, 86117, 1269, 16384⟩
    (by decide) selected_cut_06350

theorem selected_cut_06351 : selected 8 ⟨190735, by decide⟩
    (prefixPartial 13 86118) = some ⟨13, 2, 0, 190735, 86118, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_86118_190735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86118 ⟨190735, by decide⟩ :=
  accepted_of_selected 13 86118 ⟨190735, by decide⟩ ⟨13, 2, 0, 190735, 86118, 1249, 16384⟩
    (by decide) selected_cut_06351

theorem selected_cut_06352 : selected 8 ⟨190747, by decide⟩
    (prefixPartial 13 86119) = some ⟨13, 2, 0, 190747, 86119, 809, 16384⟩ := by
  decide +kernel

theorem context_13_86119_190747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86119 ⟨190747, by decide⟩ :=
  accepted_of_selected 13 86119 ⟨190747, by decide⟩ ⟨13, 2, 0, 190747, 86119, 809, 16384⟩
    (by decide) selected_cut_06352

theorem unmarked_context_12_21529_190748 : frontier 9 ⟨190748, by decide⟩
    (prefixCache 12 21529) (prefixPartial 12 21529) = false := by
  decide +kernel

theorem node_context_12_21529_190748 : EJMOriginalGlobalDAGData.nodes 9 ⟨190748, by decide⟩ =
    .split (coordinate 12) (![⟨190696, by decide⟩,⟨190718, by decide⟩,⟨190735, by decide⟩,⟨190747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21529_190748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21529 ⟨190748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21529
    ⟨190748, by decide⟩ (by decide) (![⟨190696, by decide⟩,⟨190718, by decide⟩,⟨190735, by decide⟩,⟨190747, by decide⟩]) unmarked_context_12_21529_190748 node_context_12_21529_190748
  intro a
  fin_cases a
  · exact context_13_86116_190696
  · exact context_13_86117_190718
  · exact context_13_86118_190735
  · exact context_13_86119_190747

theorem selected_cut_06353 : selected 8 ⟨190768, by decide⟩
    (prefixPartial 13 86120) = some ⟨13, 2, 0, 190768, 86120, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_86120_190768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86120 ⟨190768, by decide⟩ :=
  accepted_of_selected 13 86120 ⟨190768, by decide⟩ ⟨13, 2, 0, 190768, 86120, 1089, 16384⟩
    (by decide) selected_cut_06353

theorem selected_cut_06354 : selected 8 ⟨190798, by decide⟩
    (prefixPartial 13 86121) = some ⟨13, 2, 0, 190798, 86121, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_86121_190798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86121 ⟨190798, by decide⟩ :=
  accepted_of_selected 13 86121 ⟨190798, by decide⟩ ⟨13, 2, 0, 190798, 86121, 2061, 16384⟩
    (by decide) selected_cut_06354

theorem selected_cut_06355 : selected 8 ⟨190812, by decide⟩
    (prefixPartial 13 86122) = some ⟨13, 2, 0, 190812, 86122, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_86122_190812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86122 ⟨190812, by decide⟩ :=
  accepted_of_selected 13 86122 ⟨190812, by decide⟩ ⟨13, 2, 0, 190812, 86122, 1137, 16384⟩
    (by decide) selected_cut_06355

theorem selected_cut_06356 : selected 8 ⟨190820, by decide⟩
    (prefixPartial 13 86123) = some ⟨13, 2, 0, 190820, 86123, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_86123_190820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86123 ⟨190820, by decide⟩ :=
  accepted_of_selected 13 86123 ⟨190820, by decide⟩ ⟨13, 2, 0, 190820, 86123, 1005, 16384⟩
    (by decide) selected_cut_06356

theorem unmarked_context_12_21530_190821 : frontier 9 ⟨190821, by decide⟩
    (prefixCache 12 21530) (prefixPartial 12 21530) = false := by
  decide +kernel

theorem node_context_12_21530_190821 : EJMOriginalGlobalDAGData.nodes 9 ⟨190821, by decide⟩ =
    .split (coordinate 12) (![⟨190768, by decide⟩,⟨190798, by decide⟩,⟨190812, by decide⟩,⟨190820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21530_190821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21530 ⟨190821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21530
    ⟨190821, by decide⟩ (by decide) (![⟨190768, by decide⟩,⟨190798, by decide⟩,⟨190812, by decide⟩,⟨190820, by decide⟩]) unmarked_context_12_21530_190821 node_context_12_21530_190821
  intro a
  fin_cases a
  · exact context_13_86120_190768
  · exact context_13_86121_190798
  · exact context_13_86122_190812
  · exact context_13_86123_190820

theorem selected_cut_06357 : selected 8 ⟨190840, by decide⟩
    (prefixPartial 13 86124) = some ⟨13, 2, 0, 190840, 86124, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_86124_190840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86124 ⟨190840, by decide⟩ :=
  accepted_of_selected 13 86124 ⟨190840, by decide⟩ ⟨13, 2, 0, 190840, 86124, 1065, 16384⟩
    (by decide) selected_cut_06357

theorem selected_cut_06358 : selected 8 ⟨190869, by decide⟩
    (prefixPartial 13 86125) = some ⟨13, 2, 0, 190869, 86125, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_86125_190869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86125 ⟨190869, by decide⟩ :=
  accepted_of_selected 13 86125 ⟨190869, by decide⟩ ⟨13, 2, 0, 190869, 86125, 2109, 16384⟩
    (by decide) selected_cut_06358

theorem selected_cut_06359 : selected 8 ⟨190890, by decide⟩
    (prefixPartial 13 86126) = some ⟨13, 2, 0, 190890, 86126, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_86126_190890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86126 ⟨190890, by decide⟩ :=
  accepted_of_selected 13 86126 ⟨190890, by decide⟩ ⟨13, 2, 0, 190890, 86126, 1441, 16384⟩
    (by decide) selected_cut_06359

theorem selected_cut_06360 : selected 8 ⟨190899, by decide⟩
    (prefixPartial 13 86127) = some ⟨13, 2, 0, 190899, 86127, 849, 16384⟩ := by
  decide +kernel

theorem context_13_86127_190899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86127 ⟨190899, by decide⟩ :=
  accepted_of_selected 13 86127 ⟨190899, by decide⟩ ⟨13, 2, 0, 190899, 86127, 849, 16384⟩
    (by decide) selected_cut_06360

theorem unmarked_context_12_21531_190900 : frontier 9 ⟨190900, by decide⟩
    (prefixCache 12 21531) (prefixPartial 12 21531) = false := by
  decide +kernel

theorem node_context_12_21531_190900 : EJMOriginalGlobalDAGData.nodes 9 ⟨190900, by decide⟩ =
    .split (coordinate 12) (![⟨190840, by decide⟩,⟨190869, by decide⟩,⟨190890, by decide⟩,⟨190899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21531_190900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21531 ⟨190900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21531
    ⟨190900, by decide⟩ (by decide) (![⟨190840, by decide⟩,⟨190869, by decide⟩,⟨190890, by decide⟩,⟨190899, by decide⟩]) unmarked_context_12_21531_190900 node_context_12_21531_190900
  intro a
  fin_cases a
  · exact context_13_86124_190840
  · exact context_13_86125_190869
  · exact context_13_86126_190890
  · exact context_13_86127_190899

theorem unmarked_context_11_5382_190901 : frontier 10 ⟨190901, by decide⟩
    (prefixCache 11 5382) (prefixPartial 11 5382) = false := by
  decide +kernel

theorem node_context_11_5382_190901 : EJMOriginalGlobalDAGData.nodes 10 ⟨190901, by decide⟩ =
    .split (coordinate 11) (![⟨190683, by decide⟩,⟨190748, by decide⟩,⟨190821, by decide⟩,⟨190900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5382_190901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5382 ⟨190901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5382
    ⟨190901, by decide⟩ (by decide) (![⟨190683, by decide⟩,⟨190748, by decide⟩,⟨190821, by decide⟩,⟨190900, by decide⟩]) unmarked_context_11_5382_190901 node_context_11_5382_190901
  intro a
  fin_cases a
  · exact context_12_21528_190683
  · exact context_12_21529_190748
  · exact context_12_21530_190821
  · exact context_12_21531_190900

theorem selected_cut_06361 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5383) = some ⟨11, 1, 0, 1736, 5383, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5383_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5383 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5383 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5383, 1, 262144⟩
    (by decide) selected_cut_06361

theorem unmarked_context_10_1345_190902 : frontier 11 ⟨190902, by decide⟩
    (prefixCache 10 1345) (prefixPartial 10 1345) = false := by
  decide +kernel

theorem node_context_10_1345_190902 : EJMOriginalGlobalDAGData.nodes 11 ⟨190902, by decide⟩ =
    .split (coordinate 10) (![⟨190260, by decide⟩,⟨190616, by decide⟩,⟨190901, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1345_190902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1345 ⟨190902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1345
    ⟨190902, by decide⟩ (by decide) (![⟨190260, by decide⟩,⟨190616, by decide⟩,⟨190901, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1345_190902 node_context_10_1345_190902
  intro a
  fin_cases a
  · exact context_11_5380_190260
  · exact context_11_5381_190616
  · exact context_11_5382_190901
  · exact context_11_5383_1736

theorem selected_cut_06362 : selected 8 ⟨190940, by decide⟩
    (prefixPartial 13 86144) = some ⟨13, 2, 0, 190940, 86144, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_86144_190940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86144 ⟨190940, by decide⟩ :=
  accepted_of_selected 13 86144 ⟨190940, by decide⟩ ⟨13, 2, 0, 190940, 86144, 1361, 16384⟩
    (by decide) selected_cut_06362

theorem selected_cut_06363 : selected 8 ⟨190998, by decide⟩
    (prefixPartial 13 86145) = some ⟨13, 2, 0, 190998, 86145, 3269, 16384⟩ := by
  decide +kernel

theorem context_13_86145_190998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86145 ⟨190998, by decide⟩ :=
  accepted_of_selected 13 86145 ⟨190998, by decide⟩ ⟨13, 2, 0, 190998, 86145, 3269, 16384⟩
    (by decide) selected_cut_06363

theorem selected_cut_06364 : selected 8 ⟨191026, by decide⟩
    (prefixPartial 13 86146) = some ⟨13, 2, 0, 191026, 86146, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_86146_191026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86146 ⟨191026, by decide⟩ :=
  accepted_of_selected 13 86146 ⟨191026, by decide⟩ ⟨13, 2, 0, 191026, 86146, 1941, 16384⟩
    (by decide) selected_cut_06364

theorem selected_cut_06365 : selected 8 ⟨191044, by decide⟩
    (prefixPartial 13 86147) = some ⟨13, 2, 0, 191044, 86147, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_86147_191044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86147 ⟨191044, by decide⟩ :=
  accepted_of_selected 13 86147 ⟨191044, by decide⟩ ⟨13, 2, 0, 191044, 86147, 1181, 16384⟩
    (by decide) selected_cut_06365

theorem unmarked_context_12_21536_191045 : frontier 9 ⟨191045, by decide⟩
    (prefixCache 12 21536) (prefixPartial 12 21536) = false := by
  decide +kernel

theorem node_context_12_21536_191045 : EJMOriginalGlobalDAGData.nodes 9 ⟨191045, by decide⟩ =
    .split (coordinate 12) (![⟨190940, by decide⟩,⟨190998, by decide⟩,⟨191026, by decide⟩,⟨191044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21536_191045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21536 ⟨191045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21536
    ⟨191045, by decide⟩ (by decide) (![⟨190940, by decide⟩,⟨190998, by decide⟩,⟨191026, by decide⟩,⟨191044, by decide⟩]) unmarked_context_12_21536_191045 node_context_12_21536_191045
  intro a
  fin_cases a
  · exact context_13_86144_190940
  · exact context_13_86145_190998
  · exact context_13_86146_191026
  · exact context_13_86147_191044

theorem selected_cut_06366 : selected 9 ⟨191109, by decide⟩
    (prefixPartial 12 21537) = some ⟨12, 2, 0, 191109, 21537, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_21537_191109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21537 ⟨191109, by decide⟩ :=
  accepted_of_selected 12 21537 ⟨191109, by decide⟩ ⟨12, 2, 0, 191109, 21537, 3769, 65536⟩
    (by decide) selected_cut_06366

theorem selected_cut_06367 : selected 8 ⟨191127, by decide⟩
    (prefixPartial 13 86152) = some ⟨13, 2, 0, 191127, 86152, 885, 16384⟩ := by
  decide +kernel

theorem context_13_86152_191127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86152 ⟨191127, by decide⟩ :=
  accepted_of_selected 13 86152 ⟨191127, by decide⟩ ⟨13, 2, 0, 191127, 86152, 885, 16384⟩
    (by decide) selected_cut_06367

theorem selected_cut_06368 : selected 8 ⟨191164, by decide⟩
    (prefixPartial 13 86153) = some ⟨13, 2, 0, 191164, 86153, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_86153_191164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86153 ⟨191164, by decide⟩ :=
  accepted_of_selected 13 86153 ⟨191164, by decide⟩ ⟨13, 2, 0, 191164, 86153, 1901, 16384⟩
    (by decide) selected_cut_06368

theorem selected_cut_06369 : selected 8 ⟨191174, by decide⟩
    (prefixPartial 13 86154) = some ⟨13, 2, 0, 191174, 86154, 881, 16384⟩ := by
  decide +kernel

theorem context_13_86154_191174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86154 ⟨191174, by decide⟩ :=
  accepted_of_selected 13 86154 ⟨191174, by decide⟩ ⟨13, 2, 0, 191174, 86154, 881, 16384⟩
    (by decide) selected_cut_06369

theorem selected_cut_06370 : selected 8 ⟨191183, by decide⟩
    (prefixPartial 13 86155) = some ⟨13, 2, 0, 191183, 86155, 905, 16384⟩ := by
  decide +kernel

theorem context_13_86155_191183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86155 ⟨191183, by decide⟩ :=
  accepted_of_selected 13 86155 ⟨191183, by decide⟩ ⟨13, 2, 0, 191183, 86155, 905, 16384⟩
    (by decide) selected_cut_06370

theorem unmarked_context_12_21538_191184 : frontier 9 ⟨191184, by decide⟩
    (prefixCache 12 21538) (prefixPartial 12 21538) = false := by
  decide +kernel

theorem node_context_12_21538_191184 : EJMOriginalGlobalDAGData.nodes 9 ⟨191184, by decide⟩ =
    .split (coordinate 12) (![⟨191127, by decide⟩,⟨191164, by decide⟩,⟨191174, by decide⟩,⟨191183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21538_191184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21538 ⟨191184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21538
    ⟨191184, by decide⟩ (by decide) (![⟨191127, by decide⟩,⟨191164, by decide⟩,⟨191174, by decide⟩,⟨191183, by decide⟩]) unmarked_context_12_21538_191184 node_context_12_21538_191184
  intro a
  fin_cases a
  · exact context_13_86152_191127
  · exact context_13_86153_191164
  · exact context_13_86154_191174
  · exact context_13_86155_191183

theorem selected_cut_06371 : selected 8 ⟨191198, by decide⟩
    (prefixPartial 13 86156) = some ⟨13, 2, 0, 191198, 86156, 809, 16384⟩ := by
  decide +kernel

theorem context_13_86156_191198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86156 ⟨191198, by decide⟩ :=
  accepted_of_selected 13 86156 ⟨191198, by decide⟩ ⟨13, 2, 0, 191198, 86156, 809, 16384⟩
    (by decide) selected_cut_06371

theorem selected_cut_06372 : selected 8 ⟨191232, by decide⟩
    (prefixPartial 13 86157) = some ⟨13, 2, 0, 191232, 86157, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_86157_191232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86157 ⟨191232, by decide⟩ :=
  accepted_of_selected 13 86157 ⟨191232, by decide⟩ ⟨13, 2, 0, 191232, 86157, 1801, 16384⟩
    (by decide) selected_cut_06372

theorem selected_cut_06373 : selected 8 ⟨191246, by decide⟩
    (prefixPartial 13 86158) = some ⟨13, 2, 0, 191246, 86158, 989, 16384⟩ := by
  decide +kernel

theorem context_13_86158_191246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86158 ⟨191246, by decide⟩ :=
  accepted_of_selected 13 86158 ⟨191246, by decide⟩ ⟨13, 2, 0, 191246, 86158, 989, 16384⟩
    (by decide) selected_cut_06373

theorem selected_cut_06374 : selected 8 ⟨191252, by decide⟩
    (prefixPartial 13 86159) = some ⟨13, 2, 0, 191252, 86159, 665, 16384⟩ := by
  decide +kernel

theorem context_13_86159_191252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86159 ⟨191252, by decide⟩ :=
  accepted_of_selected 13 86159 ⟨191252, by decide⟩ ⟨13, 2, 0, 191252, 86159, 665, 16384⟩
    (by decide) selected_cut_06374

theorem unmarked_context_12_21539_191253 : frontier 9 ⟨191253, by decide⟩
    (prefixCache 12 21539) (prefixPartial 12 21539) = false := by
  decide +kernel

theorem node_context_12_21539_191253 : EJMOriginalGlobalDAGData.nodes 9 ⟨191253, by decide⟩ =
    .split (coordinate 12) (![⟨191198, by decide⟩,⟨191232, by decide⟩,⟨191246, by decide⟩,⟨191252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21539_191253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21539 ⟨191253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21539
    ⟨191253, by decide⟩ (by decide) (![⟨191198, by decide⟩,⟨191232, by decide⟩,⟨191246, by decide⟩,⟨191252, by decide⟩]) unmarked_context_12_21539_191253 node_context_12_21539_191253
  intro a
  fin_cases a
  · exact context_13_86156_191198
  · exact context_13_86157_191232
  · exact context_13_86158_191246
  · exact context_13_86159_191252

theorem unmarked_context_11_5384_191254 : frontier 10 ⟨191254, by decide⟩
    (prefixCache 11 5384) (prefixPartial 11 5384) = false := by
  decide +kernel

theorem node_context_11_5384_191254 : EJMOriginalGlobalDAGData.nodes 10 ⟨191254, by decide⟩ =
    .split (coordinate 11) (![⟨191045, by decide⟩,⟨191109, by decide⟩,⟨191184, by decide⟩,⟨191253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5384_191254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5384 ⟨191254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5384
    ⟨191254, by decide⟩ (by decide) (![⟨191045, by decide⟩,⟨191109, by decide⟩,⟨191184, by decide⟩,⟨191253, by decide⟩]) unmarked_context_11_5384_191254 node_context_11_5384_191254
  intro a
  fin_cases a
  · exact context_12_21536_191045
  · exact context_12_21537_191109
  · exact context_12_21538_191184
  · exact context_12_21539_191253

theorem selected_cut_06375 : selected 8 ⟨191263, by decide⟩
    (prefixPartial 13 86160) = some ⟨13, 2, 0, 191263, 86160, 549, 16384⟩ := by
  decide +kernel

theorem context_13_86160_191263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86160 ⟨191263, by decide⟩ :=
  accepted_of_selected 13 86160 ⟨191263, by decide⟩ ⟨13, 2, 0, 191263, 86160, 549, 16384⟩
    (by decide) selected_cut_06375

theorem selected_cut_06376 : selected 8 ⟨191297, by decide⟩
    (prefixPartial 13 86161) = some ⟨13, 2, 0, 191297, 86161, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_86161_191297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86161 ⟨191297, by decide⟩ :=
  accepted_of_selected 13 86161 ⟨191297, by decide⟩ ⟨13, 2, 0, 191297, 86161, 2513, 16384⟩
    (by decide) selected_cut_06376

theorem selected_cut_06377 : selected 8 ⟨191315, by decide⟩
    (prefixPartial 13 86162) = some ⟨13, 2, 0, 191315, 86162, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_86162_191315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86162 ⟨191315, by decide⟩ :=
  accepted_of_selected 13 86162 ⟨191315, by decide⟩ ⟨13, 2, 0, 191315, 86162, 1317, 16384⟩
    (by decide) selected_cut_06377

theorem selected_cut_06378 : selected 8 ⟨191327, by decide⟩
    (prefixPartial 13 86163) = some ⟨13, 2, 0, 191327, 86163, 817, 16384⟩ := by
  decide +kernel

theorem context_13_86163_191327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86163 ⟨191327, by decide⟩ :=
  accepted_of_selected 13 86163 ⟨191327, by decide⟩ ⟨13, 2, 0, 191327, 86163, 817, 16384⟩
    (by decide) selected_cut_06378

theorem unmarked_context_12_21540_191328 : frontier 9 ⟨191328, by decide⟩
    (prefixCache 12 21540) (prefixPartial 12 21540) = false := by
  decide +kernel

theorem node_context_12_21540_191328 : EJMOriginalGlobalDAGData.nodes 9 ⟨191328, by decide⟩ =
    .split (coordinate 12) (![⟨191263, by decide⟩,⟨191297, by decide⟩,⟨191315, by decide⟩,⟨191327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21540_191328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21540 ⟨191328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21540
    ⟨191328, by decide⟩ (by decide) (![⟨191263, by decide⟩,⟨191297, by decide⟩,⟨191315, by decide⟩,⟨191327, by decide⟩]) unmarked_context_12_21540_191328 node_context_12_21540_191328
  intro a
  fin_cases a
  · exact context_13_86160_191263
  · exact context_13_86161_191297
  · exact context_13_86162_191315
  · exact context_13_86163_191327

theorem selected_cut_06379 : selected 8 ⟨191338, by decide⟩
    (prefixPartial 13 86164) = some ⟨13, 2, 0, 191338, 86164, 553, 16384⟩ := by
  decide +kernel

theorem context_13_86164_191338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86164 ⟨191338, by decide⟩ :=
  accepted_of_selected 13 86164 ⟨191338, by decide⟩ ⟨13, 2, 0, 191338, 86164, 553, 16384⟩
    (by decide) selected_cut_06379

theorem selected_cut_06380 : selected 8 ⟨191362, by decide⟩
    (prefixPartial 13 86165) = some ⟨13, 2, 0, 191362, 86165, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_86165_191362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86165 ⟨191362, by decide⟩ :=
  accepted_of_selected 13 86165 ⟨191362, by decide⟩ ⟨13, 2, 0, 191362, 86165, 1677, 16384⟩
    (by decide) selected_cut_06380

theorem selected_cut_06381 : selected 8 ⟨191378, by decide⟩
    (prefixPartial 13 86166) = some ⟨13, 2, 0, 191378, 86166, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_86166_191378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86166 ⟨191378, by decide⟩ :=
  accepted_of_selected 13 86166 ⟨191378, by decide⟩ ⟨13, 2, 0, 191378, 86166, 1145, 16384⟩
    (by decide) selected_cut_06381

theorem selected_cut_06382 : selected 8 ⟨191387, by decide⟩
    (prefixPartial 13 86167) = some ⟨13, 2, 0, 191387, 86167, 789, 16384⟩ := by
  decide +kernel

theorem context_13_86167_191387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86167 ⟨191387, by decide⟩ :=
  accepted_of_selected 13 86167 ⟨191387, by decide⟩ ⟨13, 2, 0, 191387, 86167, 789, 16384⟩
    (by decide) selected_cut_06382

theorem unmarked_context_12_21541_191388 : frontier 9 ⟨191388, by decide⟩
    (prefixCache 12 21541) (prefixPartial 12 21541) = false := by
  decide +kernel

theorem node_context_12_21541_191388 : EJMOriginalGlobalDAGData.nodes 9 ⟨191388, by decide⟩ =
    .split (coordinate 12) (![⟨191338, by decide⟩,⟨191362, by decide⟩,⟨191378, by decide⟩,⟨191387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21541_191388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21541 ⟨191388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21541
    ⟨191388, by decide⟩ (by decide) (![⟨191338, by decide⟩,⟨191362, by decide⟩,⟨191378, by decide⟩,⟨191387, by decide⟩]) unmarked_context_12_21541_191388 node_context_12_21541_191388
  intro a
  fin_cases a
  · exact context_13_86164_191338
  · exact context_13_86165_191362
  · exact context_13_86166_191378
  · exact context_13_86167_191387

theorem selected_cut_06383 : selected 8 ⟨191401, by decide⟩
    (prefixPartial 13 86168) = some ⟨13, 2, 0, 191401, 86168, 701, 16384⟩ := by
  decide +kernel

theorem context_13_86168_191401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86168 ⟨191401, by decide⟩ :=
  accepted_of_selected 13 86168 ⟨191401, by decide⟩ ⟨13, 2, 0, 191401, 86168, 701, 16384⟩
    (by decide) selected_cut_06383

theorem selected_cut_06384 : selected 8 ⟨191438, by decide⟩
    (prefixPartial 13 86169) = some ⟨13, 2, 0, 191438, 86169, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_86169_191438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86169 ⟨191438, by decide⟩ :=
  accepted_of_selected 13 86169 ⟨191438, by decide⟩ ⟨13, 2, 0, 191438, 86169, 2601, 16384⟩
    (by decide) selected_cut_06384

theorem selected_cut_06385 : selected 8 ⟨191452, by decide⟩
    (prefixPartial 13 86170) = some ⟨13, 2, 0, 191452, 86170, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_86170_191452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86170 ⟨191452, by decide⟩ :=
  accepted_of_selected 13 86170 ⟨191452, by decide⟩ ⟨13, 2, 0, 191452, 86170, 1205, 16384⟩
    (by decide) selected_cut_06385

theorem selected_cut_06386 : selected 8 ⟨191462, by decide⟩
    (prefixPartial 13 86171) = some ⟨13, 2, 0, 191462, 86171, 889, 16384⟩ := by
  decide +kernel

theorem context_13_86171_191462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86171 ⟨191462, by decide⟩ :=
  accepted_of_selected 13 86171 ⟨191462, by decide⟩ ⟨13, 2, 0, 191462, 86171, 889, 16384⟩
    (by decide) selected_cut_06386

theorem unmarked_context_12_21542_191463 : frontier 9 ⟨191463, by decide⟩
    (prefixCache 12 21542) (prefixPartial 12 21542) = false := by
  decide +kernel

theorem node_context_12_21542_191463 : EJMOriginalGlobalDAGData.nodes 9 ⟨191463, by decide⟩ =
    .split (coordinate 12) (![⟨191401, by decide⟩,⟨191438, by decide⟩,⟨191452, by decide⟩,⟨191462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21542_191463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21542 ⟨191463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21542
    ⟨191463, by decide⟩ (by decide) (![⟨191401, by decide⟩,⟨191438, by decide⟩,⟨191452, by decide⟩,⟨191462, by decide⟩]) unmarked_context_12_21542_191463 node_context_12_21542_191463
  intro a
  fin_cases a
  · exact context_13_86168_191401
  · exact context_13_86169_191438
  · exact context_13_86170_191452
  · exact context_13_86171_191462

theorem selected_cut_06387 : selected 8 ⟨191476, by decide⟩
    (prefixPartial 13 86172) = some ⟨13, 2, 0, 191476, 86172, 605, 16384⟩ := by
  decide +kernel

theorem context_13_86172_191476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86172 ⟨191476, by decide⟩ :=
  accepted_of_selected 13 86172 ⟨191476, by decide⟩ ⟨13, 2, 0, 191476, 86172, 605, 16384⟩
    (by decide) selected_cut_06387

theorem selected_cut_06388 : selected 8 ⟨191519, by decide⟩
    (prefixPartial 13 86173) = some ⟨13, 2, 0, 191519, 86173, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_86173_191519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86173 ⟨191519, by decide⟩ :=
  accepted_of_selected 13 86173 ⟨191519, by decide⟩ ⟨13, 2, 0, 191519, 86173, 2433, 16384⟩
    (by decide) selected_cut_06388

theorem selected_cut_06389 : selected 8 ⟨191531, by decide⟩
    (prefixPartial 13 86174) = some ⟨13, 2, 0, 191531, 86174, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_86174_191531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86174 ⟨191531, by decide⟩ :=
  accepted_of_selected 13 86174 ⟨191531, by decide⟩ ⟨13, 2, 0, 191531, 86174, 1225, 16384⟩
    (by decide) selected_cut_06389

theorem selected_cut_06390 : selected 8 ⟨191539, by decide⟩
    (prefixPartial 13 86175) = some ⟨13, 2, 0, 191539, 86175, 717, 16384⟩ := by
  decide +kernel

theorem context_13_86175_191539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86175 ⟨191539, by decide⟩ :=
  accepted_of_selected 13 86175 ⟨191539, by decide⟩ ⟨13, 2, 0, 191539, 86175, 717, 16384⟩
    (by decide) selected_cut_06390

theorem unmarked_context_12_21543_191540 : frontier 9 ⟨191540, by decide⟩
    (prefixCache 12 21543) (prefixPartial 12 21543) = false := by
  decide +kernel

theorem node_context_12_21543_191540 : EJMOriginalGlobalDAGData.nodes 9 ⟨191540, by decide⟩ =
    .split (coordinate 12) (![⟨191476, by decide⟩,⟨191519, by decide⟩,⟨191531, by decide⟩,⟨191539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21543_191540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21543 ⟨191540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21543
    ⟨191540, by decide⟩ (by decide) (![⟨191476, by decide⟩,⟨191519, by decide⟩,⟨191531, by decide⟩,⟨191539, by decide⟩]) unmarked_context_12_21543_191540 node_context_12_21543_191540
  intro a
  fin_cases a
  · exact context_13_86172_191476
  · exact context_13_86173_191519
  · exact context_13_86174_191531
  · exact context_13_86175_191539

theorem unmarked_context_11_5385_191541 : frontier 10 ⟨191541, by decide⟩
    (prefixCache 11 5385) (prefixPartial 11 5385) = false := by
  decide +kernel

theorem node_context_11_5385_191541 : EJMOriginalGlobalDAGData.nodes 10 ⟨191541, by decide⟩ =
    .split (coordinate 11) (![⟨191328, by decide⟩,⟨191388, by decide⟩,⟨191463, by decide⟩,⟨191540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5385_191541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5385 ⟨191541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5385
    ⟨191541, by decide⟩ (by decide) (![⟨191328, by decide⟩,⟨191388, by decide⟩,⟨191463, by decide⟩,⟨191540, by decide⟩]) unmarked_context_11_5385_191541 node_context_11_5385_191541
  intro a
  fin_cases a
  · exact context_12_21540_191328
  · exact context_12_21541_191388
  · exact context_12_21542_191463
  · exact context_12_21543_191540

theorem selected_cut_06391 : selected 8 ⟨191549, by decide⟩
    (prefixPartial 13 86176) = some ⟨13, 2, 0, 191549, 86176, 397, 16384⟩ := by
  decide +kernel

theorem context_13_86176_191549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86176 ⟨191549, by decide⟩ :=
  accepted_of_selected 13 86176 ⟨191549, by decide⟩ ⟨13, 2, 0, 191549, 86176, 397, 16384⟩
    (by decide) selected_cut_06391

theorem selected_cut_06392 : selected 8 ⟨191580, by decide⟩
    (prefixPartial 13 86177) = some ⟨13, 2, 0, 191580, 86177, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_86177_191580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86177 ⟨191580, by decide⟩ :=
  accepted_of_selected 13 86177 ⟨191580, by decide⟩ ⟨13, 2, 0, 191580, 86177, 2189, 16384⟩
    (by decide) selected_cut_06392

theorem selected_cut_06393 : selected 8 ⟨191594, by decide⟩
    (prefixPartial 13 86178) = some ⟨13, 2, 0, 191594, 86178, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_86178_191594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86178 ⟨191594, by decide⟩ :=
  accepted_of_selected 13 86178 ⟨191594, by decide⟩ ⟨13, 2, 0, 191594, 86178, 1257, 16384⟩
    (by decide) selected_cut_06393

theorem selected_cut_06394 : selected 8 ⟨191604, by decide⟩
    (prefixPartial 13 86179) = some ⟨13, 2, 0, 191604, 86179, 873, 16384⟩ := by
  decide +kernel

theorem context_13_86179_191604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86179 ⟨191604, by decide⟩ :=
  accepted_of_selected 13 86179 ⟨191604, by decide⟩ ⟨13, 2, 0, 191604, 86179, 873, 16384⟩
    (by decide) selected_cut_06394

theorem unmarked_context_12_21544_191605 : frontier 9 ⟨191605, by decide⟩
    (prefixCache 12 21544) (prefixPartial 12 21544) = false := by
  decide +kernel

theorem node_context_12_21544_191605 : EJMOriginalGlobalDAGData.nodes 9 ⟨191605, by decide⟩ =
    .split (coordinate 12) (![⟨191549, by decide⟩,⟨191580, by decide⟩,⟨191594, by decide⟩,⟨191604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21544_191605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21544 ⟨191605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21544
    ⟨191605, by decide⟩ (by decide) (![⟨191549, by decide⟩,⟨191580, by decide⟩,⟨191594, by decide⟩,⟨191604, by decide⟩]) unmarked_context_12_21544_191605 node_context_12_21544_191605
  intro a
  fin_cases a
  · exact context_13_86176_191549
  · exact context_13_86177_191580
  · exact context_13_86178_191594
  · exact context_13_86179_191604

theorem selected_cut_06395 : selected 8 ⟨191613, by decide⟩
    (prefixPartial 13 86180) = some ⟨13, 2, 0, 191613, 86180, 385, 16384⟩ := by
  decide +kernel

theorem context_13_86180_191613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86180 ⟨191613, by decide⟩ :=
  accepted_of_selected 13 86180 ⟨191613, by decide⟩ ⟨13, 2, 0, 191613, 86180, 385, 16384⟩
    (by decide) selected_cut_06395

theorem selected_cut_06396 : selected 8 ⟨191639, by decide⟩
    (prefixPartial 13 86181) = some ⟨13, 2, 0, 191639, 86181, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_86181_191639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86181 ⟨191639, by decide⟩ :=
  accepted_of_selected 13 86181 ⟨191639, by decide⟩ ⟨13, 2, 0, 191639, 86181, 1809, 16384⟩
    (by decide) selected_cut_06396

theorem selected_cut_06397 : selected 8 ⟨191657, by decide⟩
    (prefixPartial 13 86182) = some ⟨13, 2, 0, 191657, 86182, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_86182_191657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86182 ⟨191657, by decide⟩ :=
  accepted_of_selected 13 86182 ⟨191657, by decide⟩ ⟨13, 2, 0, 191657, 86182, 1069, 16384⟩
    (by decide) selected_cut_06397

theorem selected_cut_06398 : selected 8 ⟨191667, by decide⟩
    (prefixPartial 13 86183) = some ⟨13, 2, 0, 191667, 86183, 937, 16384⟩ := by
  decide +kernel

theorem context_13_86183_191667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86183 ⟨191667, by decide⟩ :=
  accepted_of_selected 13 86183 ⟨191667, by decide⟩ ⟨13, 2, 0, 191667, 86183, 937, 16384⟩
    (by decide) selected_cut_06398

theorem unmarked_context_12_21545_191668 : frontier 9 ⟨191668, by decide⟩
    (prefixCache 12 21545) (prefixPartial 12 21545) = false := by
  decide +kernel

theorem node_context_12_21545_191668 : EJMOriginalGlobalDAGData.nodes 9 ⟨191668, by decide⟩ =
    .split (coordinate 12) (![⟨191613, by decide⟩,⟨191639, by decide⟩,⟨191657, by decide⟩,⟨191667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21545_191668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21545 ⟨191668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21545
    ⟨191668, by decide⟩ (by decide) (![⟨191613, by decide⟩,⟨191639, by decide⟩,⟨191657, by decide⟩,⟨191667, by decide⟩]) unmarked_context_12_21545_191668 node_context_12_21545_191668
  intro a
  fin_cases a
  · exact context_13_86180_191613
  · exact context_13_86181_191639
  · exact context_13_86182_191657
  · exact context_13_86183_191667

theorem selected_cut_06399 : selected 8 ⟨191680, by decide⟩
    (prefixPartial 13 86184) = some ⟨13, 2, 0, 191680, 86184, 385, 16384⟩ := by
  decide +kernel

theorem context_13_86184_191680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86184 ⟨191680, by decide⟩ :=
  accepted_of_selected 13 86184 ⟨191680, by decide⟩ ⟨13, 2, 0, 191680, 86184, 385, 16384⟩
    (by decide) selected_cut_06399

theorem selected_cut_06400 : selected 8 ⟨191730, by decide⟩
    (prefixPartial 13 86185) = some ⟨13, 2, 0, 191730, 86185, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_86185_191730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86185 ⟨191730, by decide⟩ :=
  accepted_of_selected 13 86185 ⟨191730, by decide⟩ ⟨13, 2, 0, 191730, 86185, 2533, 16384⟩
    (by decide) selected_cut_06400

theorem selected_cut_06401 : selected 8 ⟨191744, by decide⟩
    (prefixPartial 13 86186) = some ⟨13, 2, 0, 191744, 86186, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_86186_191744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86186 ⟨191744, by decide⟩ :=
  accepted_of_selected 13 86186 ⟨191744, by decide⟩ ⟨13, 2, 0, 191744, 86186, 1033, 16384⟩
    (by decide) selected_cut_06401

theorem selected_cut_06402 : selected 8 ⟨191754, by decide⟩
    (prefixPartial 13 86187) = some ⟨13, 2, 0, 191754, 86187, 989, 16384⟩ := by
  decide +kernel

theorem context_13_86187_191754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86187 ⟨191754, by decide⟩ :=
  accepted_of_selected 13 86187 ⟨191754, by decide⟩ ⟨13, 2, 0, 191754, 86187, 989, 16384⟩
    (by decide) selected_cut_06402

theorem unmarked_context_12_21546_191755 : frontier 9 ⟨191755, by decide⟩
    (prefixCache 12 21546) (prefixPartial 12 21546) = false := by
  decide +kernel

theorem node_context_12_21546_191755 : EJMOriginalGlobalDAGData.nodes 9 ⟨191755, by decide⟩ =
    .split (coordinate 12) (![⟨191680, by decide⟩,⟨191730, by decide⟩,⟨191744, by decide⟩,⟨191754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21546_191755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21546 ⟨191755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21546
    ⟨191755, by decide⟩ (by decide) (![⟨191680, by decide⟩,⟨191730, by decide⟩,⟨191744, by decide⟩,⟨191754, by decide⟩]) unmarked_context_12_21546_191755 node_context_12_21546_191755
  intro a
  fin_cases a
  · exact context_13_86184_191680
  · exact context_13_86185_191730
  · exact context_13_86186_191744
  · exact context_13_86187_191754

theorem selected_cut_06403 : selected 8 ⟨191765, by decide⟩
    (prefixPartial 13 86188) = some ⟨13, 2, 0, 191765, 86188, 329, 16384⟩ := by
  decide +kernel

theorem context_13_86188_191765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86188 ⟨191765, by decide⟩ :=
  accepted_of_selected 13 86188 ⟨191765, by decide⟩ ⟨13, 2, 0, 191765, 86188, 329, 16384⟩
    (by decide) selected_cut_06403

theorem selected_cut_06404 : selected 8 ⟨191824, by decide⟩
    (prefixPartial 13 86189) = some ⟨13, 2, 0, 191824, 86189, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_86189_191824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86189 ⟨191824, by decide⟩ :=
  accepted_of_selected 13 86189 ⟨191824, by decide⟩ ⟨13, 2, 0, 191824, 86189, 2529, 16384⟩
    (by decide) selected_cut_06404

theorem selected_cut_06405 : selected 8 ⟨191838, by decide⟩
    (prefixPartial 13 86190) = some ⟨13, 2, 0, 191838, 86190, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_86190_191838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86190 ⟨191838, by decide⟩ :=
  accepted_of_selected 13 86190 ⟨191838, by decide⟩ ⟨13, 2, 0, 191838, 86190, 1145, 16384⟩
    (by decide) selected_cut_06405

theorem selected_cut_06406 : selected 8 ⟨191846, by decide⟩
    (prefixPartial 13 86191) = some ⟨13, 2, 0, 191846, 86191, 857, 16384⟩ := by
  decide +kernel

theorem context_13_86191_191846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86191 ⟨191846, by decide⟩ :=
  accepted_of_selected 13 86191 ⟨191846, by decide⟩ ⟨13, 2, 0, 191846, 86191, 857, 16384⟩
    (by decide) selected_cut_06406

theorem unmarked_context_12_21547_191847 : frontier 9 ⟨191847, by decide⟩
    (prefixCache 12 21547) (prefixPartial 12 21547) = false := by
  decide +kernel

theorem node_context_12_21547_191847 : EJMOriginalGlobalDAGData.nodes 9 ⟨191847, by decide⟩ =
    .split (coordinate 12) (![⟨191765, by decide⟩,⟨191824, by decide⟩,⟨191838, by decide⟩,⟨191846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21547_191847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21547 ⟨191847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21547
    ⟨191847, by decide⟩ (by decide) (![⟨191765, by decide⟩,⟨191824, by decide⟩,⟨191838, by decide⟩,⟨191846, by decide⟩]) unmarked_context_12_21547_191847 node_context_12_21547_191847
  intro a
  fin_cases a
  · exact context_13_86188_191765
  · exact context_13_86189_191824
  · exact context_13_86190_191838
  · exact context_13_86191_191846

theorem unmarked_context_11_5386_191848 : frontier 10 ⟨191848, by decide⟩
    (prefixCache 11 5386) (prefixPartial 11 5386) = false := by
  decide +kernel

theorem node_context_11_5386_191848 : EJMOriginalGlobalDAGData.nodes 10 ⟨191848, by decide⟩ =
    .split (coordinate 11) (![⟨191605, by decide⟩,⟨191668, by decide⟩,⟨191755, by decide⟩,⟨191847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5386_191848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5386 ⟨191848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5386
    ⟨191848, by decide⟩ (by decide) (![⟨191605, by decide⟩,⟨191668, by decide⟩,⟨191755, by decide⟩,⟨191847, by decide⟩]) unmarked_context_11_5386_191848 node_context_11_5386_191848
  intro a
  fin_cases a
  · exact context_12_21544_191605
  · exact context_12_21545_191668
  · exact context_12_21546_191755
  · exact context_12_21547_191847

theorem selected_cut_06407 : selected 8 ⟨191855, by decide⟩
    (prefixPartial 13 86192) = some ⟨13, 2, 0, 191855, 86192, 181, 16384⟩ := by
  decide +kernel

theorem context_13_86192_191855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86192 ⟨191855, by decide⟩ :=
  accepted_of_selected 13 86192 ⟨191855, by decide⟩ ⟨13, 2, 0, 191855, 86192, 181, 16384⟩
    (by decide) selected_cut_06407

theorem selected_cut_06408 : selected 8 ⟨191891, by decide⟩
    (prefixPartial 13 86193) = some ⟨13, 2, 0, 191891, 86193, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_86193_191891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86193 ⟨191891, by decide⟩ :=
  accepted_of_selected 13 86193 ⟨191891, by decide⟩ ⟨13, 2, 0, 191891, 86193, 2233, 16384⟩
    (by decide) selected_cut_06408

theorem selected_cut_06409 : selected 8 ⟨191911, by decide⟩
    (prefixPartial 13 86194) = some ⟨13, 2, 0, 191911, 86194, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_86194_191911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86194 ⟨191911, by decide⟩ :=
  accepted_of_selected 13 86194 ⟨191911, by decide⟩ ⟨13, 2, 0, 191911, 86194, 1245, 16384⟩
    (by decide) selected_cut_06409

theorem selected_cut_06410 : selected 8 ⟨191920, by decide⟩
    (prefixPartial 13 86195) = some ⟨13, 2, 0, 191920, 86195, 741, 16384⟩ := by
  decide +kernel

theorem context_13_86195_191920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86195 ⟨191920, by decide⟩ :=
  accepted_of_selected 13 86195 ⟨191920, by decide⟩ ⟨13, 2, 0, 191920, 86195, 741, 16384⟩
    (by decide) selected_cut_06410

theorem unmarked_context_12_21548_191921 : frontier 9 ⟨191921, by decide⟩
    (prefixCache 12 21548) (prefixPartial 12 21548) = false := by
  decide +kernel

theorem node_context_12_21548_191921 : EJMOriginalGlobalDAGData.nodes 9 ⟨191921, by decide⟩ =
    .split (coordinate 12) (![⟨191855, by decide⟩,⟨191891, by decide⟩,⟨191911, by decide⟩,⟨191920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21548_191921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21548 ⟨191921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21548
    ⟨191921, by decide⟩ (by decide) (![⟨191855, by decide⟩,⟨191891, by decide⟩,⟨191911, by decide⟩,⟨191920, by decide⟩]) unmarked_context_12_21548_191921 node_context_12_21548_191921
  intro a
  fin_cases a
  · exact context_13_86192_191855
  · exact context_13_86193_191891
  · exact context_13_86194_191911
  · exact context_13_86195_191920

theorem selected_cut_06411 : selected 9 ⟨191984, by decide⟩
    (prefixPartial 12 21549) = some ⟨12, 2, 0, 191984, 21549, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_21549_191984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21549 ⟨191984, by decide⟩ :=
  accepted_of_selected 12 21549 ⟨191984, by decide⟩ ⟨12, 2, 0, 191984, 21549, 3817, 65536⟩
    (by decide) selected_cut_06411

theorem selected_cut_06412 : selected 8 ⟨191992, by decide⟩
    (prefixPartial 13 86200) = some ⟨13, 2, 0, 191992, 86200, 201, 16384⟩ := by
  decide +kernel

theorem context_13_86200_191992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86200 ⟨191992, by decide⟩ :=
  accepted_of_selected 13 86200 ⟨191992, by decide⟩ ⟨13, 2, 0, 191992, 86200, 201, 16384⟩
    (by decide) selected_cut_06412

theorem selected_cut_06413 : selected 8 ⟨192028, by decide⟩
    (prefixPartial 13 86201) = some ⟨13, 2, 0, 192028, 86201, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_86201_192028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86201 ⟨192028, by decide⟩ :=
  accepted_of_selected 13 86201 ⟨192028, by decide⟩ ⟨13, 2, 0, 192028, 86201, 2645, 16384⟩
    (by decide) selected_cut_06413

theorem selected_cut_06414 : selected 8 ⟨192045, by decide⟩
    (prefixPartial 13 86202) = some ⟨13, 2, 0, 192045, 86202, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_86202_192045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86202 ⟨192045, by decide⟩ :=
  accepted_of_selected 13 86202 ⟨192045, by decide⟩ ⟨13, 2, 0, 192045, 86202, 1161, 16384⟩
    (by decide) selected_cut_06414

theorem selected_cut_06415 : selected 8 ⟨192054, by decide⟩
    (prefixPartial 13 86203) = some ⟨13, 2, 0, 192054, 86203, 849, 16384⟩ := by
  decide +kernel

theorem context_13_86203_192054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86203 ⟨192054, by decide⟩ :=
  accepted_of_selected 13 86203 ⟨192054, by decide⟩ ⟨13, 2, 0, 192054, 86203, 849, 16384⟩
    (by decide) selected_cut_06415

theorem unmarked_context_12_21550_192055 : frontier 9 ⟨192055, by decide⟩
    (prefixCache 12 21550) (prefixPartial 12 21550) = false := by
  decide +kernel

theorem node_context_12_21550_192055 : EJMOriginalGlobalDAGData.nodes 9 ⟨192055, by decide⟩ =
    .split (coordinate 12) (![⟨191992, by decide⟩,⟨192028, by decide⟩,⟨192045, by decide⟩,⟨192054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21550_192055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21550 ⟨192055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21550
    ⟨192055, by decide⟩ (by decide) (![⟨191992, by decide⟩,⟨192028, by decide⟩,⟨192045, by decide⟩,⟨192054, by decide⟩]) unmarked_context_12_21550_192055 node_context_12_21550_192055
  intro a
  fin_cases a
  · exact context_13_86200_191992
  · exact context_13_86201_192028
  · exact context_13_86202_192045
  · exact context_13_86203_192054

theorem selected_cut_06416 : selected 8 ⟨192060, by decide⟩
    (prefixPartial 13 86204) = some ⟨13, 2, 0, 192060, 86204, 93, 16384⟩ := by
  decide +kernel

theorem context_13_86204_192060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86204 ⟨192060, by decide⟩ :=
  accepted_of_selected 13 86204 ⟨192060, by decide⟩ ⟨13, 2, 0, 192060, 86204, 93, 16384⟩
    (by decide) selected_cut_06416

theorem selected_cut_06417 : selected 8 ⟨192104, by decide⟩
    (prefixPartial 13 86205) = some ⟨13, 2, 0, 192104, 86205, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_86205_192104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86205 ⟨192104, by decide⟩ :=
  accepted_of_selected 13 86205 ⟨192104, by decide⟩ ⟨13, 2, 0, 192104, 86205, 2401, 16384⟩
    (by decide) selected_cut_06417

theorem selected_cut_06418 : selected 8 ⟨192117, by decide⟩
    (prefixPartial 13 86206) = some ⟨13, 2, 0, 192117, 86206, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_86206_192117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86206 ⟨192117, by decide⟩ :=
  accepted_of_selected 13 86206 ⟨192117, by decide⟩ ⟨13, 2, 0, 192117, 86206, 1117, 16384⟩
    (by decide) selected_cut_06418

theorem selected_cut_06419 : selected 8 ⟨192123, by decide⟩
    (prefixPartial 13 86207) = some ⟨13, 2, 0, 192123, 86207, 653, 16384⟩ := by
  decide +kernel

theorem context_13_86207_192123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86207 ⟨192123, by decide⟩ :=
  accepted_of_selected 13 86207 ⟨192123, by decide⟩ ⟨13, 2, 0, 192123, 86207, 653, 16384⟩
    (by decide) selected_cut_06419

theorem unmarked_context_12_21551_192124 : frontier 9 ⟨192124, by decide⟩
    (prefixCache 12 21551) (prefixPartial 12 21551) = false := by
  decide +kernel

theorem node_context_12_21551_192124 : EJMOriginalGlobalDAGData.nodes 9 ⟨192124, by decide⟩ =
    .split (coordinate 12) (![⟨192060, by decide⟩,⟨192104, by decide⟩,⟨192117, by decide⟩,⟨192123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21551_192124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21551 ⟨192124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21551
    ⟨192124, by decide⟩ (by decide) (![⟨192060, by decide⟩,⟨192104, by decide⟩,⟨192117, by decide⟩,⟨192123, by decide⟩]) unmarked_context_12_21551_192124 node_context_12_21551_192124
  intro a
  fin_cases a
  · exact context_13_86204_192060
  · exact context_13_86205_192104
  · exact context_13_86206_192117
  · exact context_13_86207_192123

theorem unmarked_context_11_5387_192125 : frontier 10 ⟨192125, by decide⟩
    (prefixCache 11 5387) (prefixPartial 11 5387) = false := by
  decide +kernel

theorem node_context_11_5387_192125 : EJMOriginalGlobalDAGData.nodes 10 ⟨192125, by decide⟩ =
    .split (coordinate 11) (![⟨191921, by decide⟩,⟨191984, by decide⟩,⟨192055, by decide⟩,⟨192124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5387_192125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5387 ⟨192125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5387
    ⟨192125, by decide⟩ (by decide) (![⟨191921, by decide⟩,⟨191984, by decide⟩,⟨192055, by decide⟩,⟨192124, by decide⟩]) unmarked_context_11_5387_192125 node_context_11_5387_192125
  intro a
  fin_cases a
  · exact context_12_21548_191921
  · exact context_12_21549_191984
  · exact context_12_21550_192055
  · exact context_12_21551_192124

theorem unmarked_context_10_1346_192126 : frontier 11 ⟨192126, by decide⟩
    (prefixCache 10 1346) (prefixPartial 10 1346) = false := by
  decide +kernel

theorem node_context_10_1346_192126 : EJMOriginalGlobalDAGData.nodes 11 ⟨192126, by decide⟩ =
    .split (coordinate 10) (![⟨191254, by decide⟩,⟨191541, by decide⟩,⟨191848, by decide⟩,⟨192125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1346_192126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1346 ⟨192126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1346
    ⟨192126, by decide⟩ (by decide) (![⟨191254, by decide⟩,⟨191541, by decide⟩,⟨191848, by decide⟩,⟨192125, by decide⟩]) unmarked_context_10_1346_192126 node_context_10_1346_192126
  intro a
  fin_cases a
  · exact context_11_5384_191254
  · exact context_11_5385_191541
  · exact context_11_5386_191848
  · exact context_11_5387_192125

theorem selected_cut_06420 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1347) = some ⟨10, 1, 0, 3440, 1347, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1347_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1347 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1347 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1347, 1, 1048576⟩
    (by decide) selected_cut_06420

theorem unmarked_context_9_336_192127 : frontier 12 ⟨192127, by decide⟩
    (prefixCache 9 336) (prefixPartial 9 336) = false := by
  decide +kernel

theorem node_context_9_336_192127 : EJMOriginalGlobalDAGData.nodes 12 ⟨192127, by decide⟩ =
    .split (coordinate 9) (![⟨190044, by decide⟩,⟨190902, by decide⟩,⟨192126, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_336_192127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 336 ⟨192127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 336
    ⟨192127, by decide⟩ (by decide) (![⟨190044, by decide⟩,⟨190902, by decide⟩,⟨192126, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_336_192127 node_context_9_336_192127
  intro a
  fin_cases a
  · exact context_10_1344_190044
  · exact context_10_1345_190902
  · exact context_10_1346_192126
  · exact context_10_1347_3440

theorem selected_cut_06421 : selected 9 ⟨192261, by decide⟩
    (prefixPartial 12 21568) = some ⟨12, 2, 0, 192261, 21568, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_21568_192261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21568 ⟨192261, by decide⟩ :=
  accepted_of_selected 12 21568 ⟨192261, by decide⟩ ⟨12, 2, 0, 192261, 21568, 2029, 65536⟩
    (by decide) selected_cut_06421

theorem selected_cut_06422 : selected 9 ⟨192323, by decide⟩
    (prefixPartial 12 21569) = some ⟨12, 2, 0, 192323, 21569, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_21569_192323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21569 ⟨192323, by decide⟩ :=
  accepted_of_selected 12 21569 ⟨192323, by decide⟩ ⟨12, 2, 0, 192323, 21569, 3073, 65536⟩
    (by decide) selected_cut_06422

theorem selected_cut_06423 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86280) = some ⟨13, 1, 0, 3444, 86280, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86280_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86280 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86280 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86280, 1, 16384⟩
    (by decide) selected_cut_06423

theorem selected_cut_06424 : selected 8 ⟨192352, by decide⟩
    (prefixPartial 13 86281) = some ⟨13, 2, 0, 192352, 86281, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_86281_192352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86281 ⟨192352, by decide⟩ :=
  accepted_of_selected 13 86281 ⟨192352, by decide⟩ ⟨13, 2, 0, 192352, 86281, 2085, 16384⟩
    (by decide) selected_cut_06424

theorem selected_cut_06425 : selected 8 ⟨192376, by decide⟩
    (prefixPartial 13 86282) = some ⟨13, 2, 0, 192376, 86282, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_86282_192376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86282 ⟨192376, by decide⟩ :=
  accepted_of_selected 13 86282 ⟨192376, by decide⟩ ⟨13, 2, 0, 192376, 86282, 1417, 16384⟩
    (by decide) selected_cut_06425

theorem selected_cut_06426 : selected 8 ⟨192391, by decide⟩
    (prefixPartial 13 86283) = some ⟨13, 2, 0, 192391, 86283, 885, 16384⟩ := by
  decide +kernel

theorem context_13_86283_192391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86283 ⟨192391, by decide⟩ :=
  accepted_of_selected 13 86283 ⟨192391, by decide⟩ ⟨13, 2, 0, 192391, 86283, 885, 16384⟩
    (by decide) selected_cut_06426

theorem unmarked_context_12_21570_192392 : frontier 9 ⟨192392, by decide⟩
    (prefixCache 12 21570) (prefixPartial 12 21570) = false := by
  decide +kernel

theorem node_context_12_21570_192392 : EJMOriginalGlobalDAGData.nodes 9 ⟨192392, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨192352, by decide⟩,⟨192376, by decide⟩,⟨192391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21570_192392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21570 ⟨192392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21570
    ⟨192392, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨192352, by decide⟩,⟨192376, by decide⟩,⟨192391, by decide⟩]) unmarked_context_12_21570_192392 node_context_12_21570_192392
  intro a
  fin_cases a
  · exact context_13_86280_3444
  · exact context_13_86281_192352
  · exact context_13_86282_192376
  · exact context_13_86283_192391

theorem selected_cut_06427 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21571) = some ⟨12, 1, 0, 893, 21571, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21571_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21571 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21571 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21571, 1, 65536⟩
    (by decide) selected_cut_06427

theorem unmarked_context_11_5392_192393 : frontier 10 ⟨192393, by decide⟩
    (prefixCache 11 5392) (prefixPartial 11 5392) = false := by
  decide +kernel

theorem node_context_11_5392_192393 : EJMOriginalGlobalDAGData.nodes 10 ⟨192393, by decide⟩ =
    .split (coordinate 11) (![⟨192261, by decide⟩,⟨192323, by decide⟩,⟨192392, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5392_192393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5392 ⟨192393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5392
    ⟨192393, by decide⟩ (by decide) (![⟨192261, by decide⟩,⟨192323, by decide⟩,⟨192392, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5392_192393 node_context_11_5392_192393
  intro a
  fin_cases a
  · exact context_12_21568_192261
  · exact context_12_21569_192323
  · exact context_12_21570_192392
  · exact context_12_21571_893

theorem selected_cut_06428 : selected 9 ⟨192456, by decide⟩
    (prefixPartial 12 21572) = some ⟨12, 2, 0, 192456, 21572, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_21572_192456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21572 ⟨192456, by decide⟩ :=
  accepted_of_selected 12 21572 ⟨192456, by decide⟩ ⟨12, 2, 0, 192456, 21572, 2745, 65536⟩
    (by decide) selected_cut_06428

theorem selected_cut_06429 : selected 9 ⟨192544, by decide⟩
    (prefixPartial 12 21573) = some ⟨12, 2, 0, 192544, 21573, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_21573_192544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21573 ⟨192544, by decide⟩ :=
  accepted_of_selected 12 21573 ⟨192544, by decide⟩ ⟨12, 2, 0, 192544, 21573, 2373, 65536⟩
    (by decide) selected_cut_06429

theorem selected_cut_06430 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86296) = some ⟨13, 1, 0, 3444, 86296, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86296_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86296 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86296 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86296, 1, 16384⟩
    (by decide) selected_cut_06430

theorem selected_cut_06431 : selected 8 ⟨192578, by decide⟩
    (prefixPartial 13 86297) = some ⟨13, 2, 0, 192578, 86297, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_86297_192578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86297 ⟨192578, by decide⟩ :=
  accepted_of_selected 13 86297 ⟨192578, by decide⟩ ⟨13, 2, 0, 192578, 86297, 2273, 16384⟩
    (by decide) selected_cut_06431

theorem selected_cut_06432 : selected 8 ⟨192599, by decide⟩
    (prefixPartial 13 86298) = some ⟨13, 2, 0, 192599, 86298, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_86298_192599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86298 ⟨192599, by decide⟩ :=
  accepted_of_selected 13 86298 ⟨192599, by decide⟩ ⟨13, 2, 0, 192599, 86298, 1545, 16384⟩
    (by decide) selected_cut_06432

theorem selected_cut_06433 : selected 8 ⟨192611, by decide⟩
    (prefixPartial 13 86299) = some ⟨13, 2, 0, 192611, 86299, 821, 16384⟩ := by
  decide +kernel

theorem context_13_86299_192611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86299 ⟨192611, by decide⟩ :=
  accepted_of_selected 13 86299 ⟨192611, by decide⟩ ⟨13, 2, 0, 192611, 86299, 821, 16384⟩
    (by decide) selected_cut_06433

theorem unmarked_context_12_21574_192612 : frontier 9 ⟨192612, by decide⟩
    (prefixCache 12 21574) (prefixPartial 12 21574) = false := by
  decide +kernel

theorem node_context_12_21574_192612 : EJMOriginalGlobalDAGData.nodes 9 ⟨192612, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨192578, by decide⟩,⟨192599, by decide⟩,⟨192611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21574_192612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21574 ⟨192612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21574
    ⟨192612, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨192578, by decide⟩,⟨192599, by decide⟩,⟨192611, by decide⟩]) unmarked_context_12_21574_192612 node_context_12_21574_192612
  intro a
  fin_cases a
  · exact context_13_86296_3444
  · exact context_13_86297_192578
  · exact context_13_86298_192599
  · exact context_13_86299_192611

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
