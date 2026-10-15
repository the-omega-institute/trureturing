/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover271
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_5537_661150 : frontier 11 ⟨661150, by decide⟩
    (prefixCache 10 5537) (prefixPartial 10 5537) = false := by
  decide +kernel

theorem node_context_10_5537_661150 : EJMOriginalGlobalDAGData.nodes 11 ⟨661150, by decide⟩ =
    .split (coordinate 10) (![⟨660087, by decide⟩,⟨660488, by decide⟩,⟨660741, by decide⟩,⟨661149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5537_661150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5537 ⟨661150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5537
    ⟨661150, by decide⟩ (by decide) (![⟨660087, by decide⟩,⟨660488, by decide⟩,⟨660741, by decide⟩,⟨661149, by decide⟩]) unmarked_context_10_5537_661150 node_context_10_5537_661150
  intro a
  fin_cases a
  · exact context_11_22148_660087
  · exact context_11_22149_660488
  · exact context_11_22150_660741
  · exact context_11_22151_661149

theorem selected_cut_26115 : selected 8 ⟨661162, by decide⟩
    (prefixPartial 13 354432) = some ⟨13, 2, 0, 661162, 354432, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_354432_661162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354432 ⟨661162, by decide⟩ :=
  accepted_of_selected 13 354432 ⟨661162, by decide⟩ ⟨13, 2, 0, 661162, 354432, 1061, 16384⟩
    (by decide) selected_cut_26115

theorem selected_cut_26116 : selected 8 ⟨661190, by decide⟩
    (prefixPartial 13 354433) = some ⟨13, 2, 0, 661190, 354433, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_354433_661190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354433 ⟨661190, by decide⟩ :=
  accepted_of_selected 13 354433 ⟨661190, by decide⟩ ⟨13, 2, 0, 661190, 354433, 1597, 16384⟩
    (by decide) selected_cut_26116

theorem selected_cut_26117 : selected 8 ⟨661209, by decide⟩
    (prefixPartial 13 354434) = some ⟨13, 2, 0, 661209, 354434, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_354434_661209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354434 ⟨661209, by decide⟩ :=
  accepted_of_selected 13 354434 ⟨661209, by decide⟩ ⟨13, 2, 0, 661209, 354434, 1381, 16384⟩
    (by decide) selected_cut_26117

theorem selected_cut_26118 : selected 8 ⟨661217, by decide⟩
    (prefixPartial 13 354435) = some ⟨13, 2, 0, 661217, 354435, 749, 16384⟩ := by
  decide +kernel

theorem context_13_354435_661217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354435 ⟨661217, by decide⟩ :=
  accepted_of_selected 13 354435 ⟨661217, by decide⟩ ⟨13, 2, 0, 661217, 354435, 749, 16384⟩
    (by decide) selected_cut_26118

theorem unmarked_context_12_88608_661218 : frontier 9 ⟨661218, by decide⟩
    (prefixCache 12 88608) (prefixPartial 12 88608) = false := by
  decide +kernel

theorem node_context_12_88608_661218 : EJMOriginalGlobalDAGData.nodes 9 ⟨661218, by decide⟩ =
    .split (coordinate 12) (![⟨661162, by decide⟩,⟨661190, by decide⟩,⟨661209, by decide⟩,⟨661217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88608_661218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88608 ⟨661218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88608
    ⟨661218, by decide⟩ (by decide) (![⟨661162, by decide⟩,⟨661190, by decide⟩,⟨661209, by decide⟩,⟨661217, by decide⟩]) unmarked_context_12_88608_661218 node_context_12_88608_661218
  intro a
  fin_cases a
  · exact context_13_354432_661162
  · exact context_13_354433_661190
  · exact context_13_354434_661209
  · exact context_13_354435_661217

theorem selected_cut_26119 : selected 8 ⟨661231, by decide⟩
    (prefixPartial 13 354436) = some ⟨13, 2, 0, 661231, 354436, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_354436_661231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354436 ⟨661231, by decide⟩ :=
  accepted_of_selected 13 354436 ⟨661231, by decide⟩ ⟨13, 2, 0, 661231, 354436, 1069, 16384⟩
    (by decide) selected_cut_26119

theorem selected_cut_26120 : selected 8 ⟨661252, by decide⟩
    (prefixPartial 13 354437) = some ⟨13, 2, 0, 661252, 354437, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_354437_661252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354437 ⟨661252, by decide⟩ :=
  accepted_of_selected 13 354437 ⟨661252, by decide⟩ ⟨13, 2, 0, 661252, 354437, 1573, 16384⟩
    (by decide) selected_cut_26120

theorem selected_cut_26121 : selected 8 ⟨661265, by decide⟩
    (prefixPartial 13 354438) = some ⟨13, 2, 0, 661265, 354438, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_354438_661265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354438 ⟨661265, by decide⟩ :=
  accepted_of_selected 13 354438 ⟨661265, by decide⟩ ⟨13, 2, 0, 661265, 354438, 1333, 16384⟩
    (by decide) selected_cut_26121

theorem selected_cut_26122 : selected 8 ⟨661274, by decide⟩
    (prefixPartial 13 354439) = some ⟨13, 2, 0, 661274, 354439, 793, 16384⟩ := by
  decide +kernel

theorem context_13_354439_661274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354439 ⟨661274, by decide⟩ :=
  accepted_of_selected 13 354439 ⟨661274, by decide⟩ ⟨13, 2, 0, 661274, 354439, 793, 16384⟩
    (by decide) selected_cut_26122

theorem unmarked_context_12_88609_661275 : frontier 9 ⟨661275, by decide⟩
    (prefixCache 12 88609) (prefixPartial 12 88609) = false := by
  decide +kernel

theorem node_context_12_88609_661275 : EJMOriginalGlobalDAGData.nodes 9 ⟨661275, by decide⟩ =
    .split (coordinate 12) (![⟨661231, by decide⟩,⟨661252, by decide⟩,⟨661265, by decide⟩,⟨661274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88609_661275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88609 ⟨661275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88609
    ⟨661275, by decide⟩ (by decide) (![⟨661231, by decide⟩,⟨661252, by decide⟩,⟨661265, by decide⟩,⟨661274, by decide⟩]) unmarked_context_12_88609_661275 node_context_12_88609_661275
  intro a
  fin_cases a
  · exact context_13_354436_661231
  · exact context_13_354437_661252
  · exact context_13_354438_661265
  · exact context_13_354439_661274

theorem selected_cut_26123 : selected 8 ⟨661289, by decide⟩
    (prefixPartial 13 354440) = some ⟨13, 2, 0, 661289, 354440, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_354440_661289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354440 ⟨661289, by decide⟩ :=
  accepted_of_selected 13 354440 ⟨661289, by decide⟩ ⟨13, 2, 0, 661289, 354440, 1137, 16384⟩
    (by decide) selected_cut_26123

theorem selected_cut_26124 : selected 8 ⟨661311, by decide⟩
    (prefixPartial 13 354441) = some ⟨13, 2, 0, 661311, 354441, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_354441_661311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354441 ⟨661311, by decide⟩ :=
  accepted_of_selected 13 354441 ⟨661311, by decide⟩ ⟨13, 2, 0, 661311, 354441, 1749, 16384⟩
    (by decide) selected_cut_26124

theorem selected_cut_26125 : selected 8 ⟨661322, by decide⟩
    (prefixPartial 13 354442) = some ⟨13, 2, 0, 661322, 354442, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_354442_661322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354442 ⟨661322, by decide⟩ :=
  accepted_of_selected 13 354442 ⟨661322, by decide⟩ ⟨13, 2, 0, 661322, 354442, 1345, 16384⟩
    (by decide) selected_cut_26125

theorem selected_cut_26126 : selected 8 ⟨661330, by decide⟩
    (prefixPartial 13 354443) = some ⟨13, 2, 0, 661330, 354443, 757, 16384⟩ := by
  decide +kernel

theorem context_13_354443_661330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354443 ⟨661330, by decide⟩ :=
  accepted_of_selected 13 354443 ⟨661330, by decide⟩ ⟨13, 2, 0, 661330, 354443, 757, 16384⟩
    (by decide) selected_cut_26126

theorem unmarked_context_12_88610_661331 : frontier 9 ⟨661331, by decide⟩
    (prefixCache 12 88610) (prefixPartial 12 88610) = false := by
  decide +kernel

theorem node_context_12_88610_661331 : EJMOriginalGlobalDAGData.nodes 9 ⟨661331, by decide⟩ =
    .split (coordinate 12) (![⟨661289, by decide⟩,⟨661311, by decide⟩,⟨661322, by decide⟩,⟨661330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88610_661331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88610 ⟨661331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88610
    ⟨661331, by decide⟩ (by decide) (![⟨661289, by decide⟩,⟨661311, by decide⟩,⟨661322, by decide⟩,⟨661330, by decide⟩]) unmarked_context_12_88610_661331 node_context_12_88610_661331
  intro a
  fin_cases a
  · exact context_13_354440_661289
  · exact context_13_354441_661311
  · exact context_13_354442_661322
  · exact context_13_354443_661330

theorem selected_cut_26127 : selected 8 ⟨661346, by decide⟩
    (prefixPartial 13 354444) = some ⟨13, 2, 0, 661346, 354444, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_354444_661346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354444 ⟨661346, by decide⟩ :=
  accepted_of_selected 13 354444 ⟨661346, by decide⟩ ⟨13, 2, 0, 661346, 354444, 1221, 16384⟩
    (by decide) selected_cut_26127

theorem selected_cut_26128 : selected 8 ⟨661373, by decide⟩
    (prefixPartial 13 354445) = some ⟨13, 2, 0, 661373, 354445, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_354445_661373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354445 ⟨661373, by decide⟩ :=
  accepted_of_selected 13 354445 ⟨661373, by decide⟩ ⟨13, 2, 0, 661373, 354445, 2005, 16384⟩
    (by decide) selected_cut_26128

theorem selected_cut_26129 : selected 8 ⟨661387, by decide⟩
    (prefixPartial 13 354446) = some ⟨13, 2, 0, 661387, 354446, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_354446_661387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354446 ⟨661387, by decide⟩ :=
  accepted_of_selected 13 354446 ⟨661387, by decide⟩ ⟨13, 2, 0, 661387, 354446, 1581, 16384⟩
    (by decide) selected_cut_26129

theorem selected_cut_26130 : selected 8 ⟨661394, by decide⟩
    (prefixPartial 13 354447) = some ⟨13, 2, 0, 661394, 354447, 833, 16384⟩ := by
  decide +kernel

theorem context_13_354447_661394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354447 ⟨661394, by decide⟩ :=
  accepted_of_selected 13 354447 ⟨661394, by decide⟩ ⟨13, 2, 0, 661394, 354447, 833, 16384⟩
    (by decide) selected_cut_26130

theorem unmarked_context_12_88611_661395 : frontier 9 ⟨661395, by decide⟩
    (prefixCache 12 88611) (prefixPartial 12 88611) = false := by
  decide +kernel

theorem node_context_12_88611_661395 : EJMOriginalGlobalDAGData.nodes 9 ⟨661395, by decide⟩ =
    .split (coordinate 12) (![⟨661346, by decide⟩,⟨661373, by decide⟩,⟨661387, by decide⟩,⟨661394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88611_661395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88611 ⟨661395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88611
    ⟨661395, by decide⟩ (by decide) (![⟨661346, by decide⟩,⟨661373, by decide⟩,⟨661387, by decide⟩,⟨661394, by decide⟩]) unmarked_context_12_88611_661395 node_context_12_88611_661395
  intro a
  fin_cases a
  · exact context_13_354444_661346
  · exact context_13_354445_661373
  · exact context_13_354446_661387
  · exact context_13_354447_661394

theorem unmarked_context_11_22152_661396 : frontier 10 ⟨661396, by decide⟩
    (prefixCache 11 22152) (prefixPartial 11 22152) = false := by
  decide +kernel

theorem node_context_11_22152_661396 : EJMOriginalGlobalDAGData.nodes 10 ⟨661396, by decide⟩ =
    .split (coordinate 11) (![⟨661218, by decide⟩,⟨661275, by decide⟩,⟨661331, by decide⟩,⟨661395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22152_661396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22152 ⟨661396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22152
    ⟨661396, by decide⟩ (by decide) (![⟨661218, by decide⟩,⟨661275, by decide⟩,⟨661331, by decide⟩,⟨661395, by decide⟩]) unmarked_context_11_22152_661396 node_context_11_22152_661396
  intro a
  fin_cases a
  · exact context_12_88608_661218
  · exact context_12_88609_661275
  · exact context_12_88610_661331
  · exact context_12_88611_661395

theorem selected_cut_26131 : selected 8 ⟨661408, by decide⟩
    (prefixPartial 13 354448) = some ⟨13, 2, 0, 661408, 354448, 857, 16384⟩ := by
  decide +kernel

theorem context_13_354448_661408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354448 ⟨661408, by decide⟩ :=
  accepted_of_selected 13 354448 ⟨661408, by decide⟩ ⟨13, 2, 0, 661408, 354448, 857, 16384⟩
    (by decide) selected_cut_26131

theorem selected_cut_26132 : selected 8 ⟨661448, by decide⟩
    (prefixPartial 13 354449) = some ⟨13, 2, 0, 661448, 354449, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_354449_661448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354449 ⟨661448, by decide⟩ :=
  accepted_of_selected 13 354449 ⟨661448, by decide⟩ ⟨13, 2, 0, 661448, 354449, 2109, 16384⟩
    (by decide) selected_cut_26132

theorem selected_cut_26133 : selected 8 ⟨661458, by decide⟩
    (prefixPartial 13 354450) = some ⟨13, 2, 0, 661458, 354450, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_354450_661458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354450 ⟨661458, by decide⟩ :=
  accepted_of_selected 13 354450 ⟨661458, by decide⟩ ⟨13, 2, 0, 661458, 354450, 1257, 16384⟩
    (by decide) selected_cut_26133

theorem selected_cut_26134 : selected 8 ⟨661468, by decide⟩
    (prefixPartial 13 354451) = some ⟨13, 2, 0, 661468, 354451, 893, 16384⟩ := by
  decide +kernel

theorem context_13_354451_661468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354451 ⟨661468, by decide⟩ :=
  accepted_of_selected 13 354451 ⟨661468, by decide⟩ ⟨13, 2, 0, 661468, 354451, 893, 16384⟩
    (by decide) selected_cut_26134

theorem unmarked_context_12_88612_661469 : frontier 9 ⟨661469, by decide⟩
    (prefixCache 12 88612) (prefixPartial 12 88612) = false := by
  decide +kernel

theorem node_context_12_88612_661469 : EJMOriginalGlobalDAGData.nodes 9 ⟨661469, by decide⟩ =
    .split (coordinate 12) (![⟨661408, by decide⟩,⟨661448, by decide⟩,⟨661458, by decide⟩,⟨661468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88612_661469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88612 ⟨661469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88612
    ⟨661469, by decide⟩ (by decide) (![⟨661408, by decide⟩,⟨661448, by decide⟩,⟨661458, by decide⟩,⟨661468, by decide⟩]) unmarked_context_12_88612_661469 node_context_12_88612_661469
  intro a
  fin_cases a
  · exact context_13_354448_661408
  · exact context_13_354449_661448
  · exact context_13_354450_661458
  · exact context_13_354451_661468

theorem selected_cut_26135 : selected 9 ⟨661525, by decide⟩
    (prefixPartial 12 88613) = some ⟨12, 2, 0, 661525, 88613, 4049, 65536⟩ := by
  decide +kernel

theorem context_12_88613_661525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88613 ⟨661525, by decide⟩ :=
  accepted_of_selected 12 88613 ⟨661525, by decide⟩ ⟨12, 2, 0, 661525, 88613, 4049, 65536⟩
    (by decide) selected_cut_26135

theorem selected_cut_26136 : selected 8 ⟨661535, by decide⟩
    (prefixPartial 13 354456) = some ⟨13, 2, 0, 661535, 354456, 869, 16384⟩ := by
  decide +kernel

theorem context_13_354456_661535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354456 ⟨661535, by decide⟩ :=
  accepted_of_selected 13 354456 ⟨661535, by decide⟩ ⟨13, 2, 0, 661535, 354456, 869, 16384⟩
    (by decide) selected_cut_26136

theorem selected_cut_26137 : selected 8 ⟨661562, by decide⟩
    (prefixPartial 13 354457) = some ⟨13, 2, 0, 661562, 354457, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_354457_661562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354457 ⟨661562, by decide⟩ :=
  accepted_of_selected 13 354457 ⟨661562, by decide⟩ ⟨13, 2, 0, 661562, 354457, 1881, 16384⟩
    (by decide) selected_cut_26137

theorem selected_cut_26138 : selected 8 ⟨661577, by decide⟩
    (prefixPartial 13 354458) = some ⟨13, 2, 0, 661577, 354458, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_354458_661577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354458 ⟨661577, by decide⟩ :=
  accepted_of_selected 13 354458 ⟨661577, by decide⟩ ⟨13, 2, 0, 661577, 354458, 1105, 16384⟩
    (by decide) selected_cut_26138

theorem selected_cut_26139 : selected 8 ⟨661586, by decide⟩
    (prefixPartial 13 354459) = some ⟨13, 2, 0, 661586, 354459, 781, 16384⟩ := by
  decide +kernel

theorem context_13_354459_661586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354459 ⟨661586, by decide⟩ :=
  accepted_of_selected 13 354459 ⟨661586, by decide⟩ ⟨13, 2, 0, 661586, 354459, 781, 16384⟩
    (by decide) selected_cut_26139

theorem unmarked_context_12_88614_661587 : frontier 9 ⟨661587, by decide⟩
    (prefixCache 12 88614) (prefixPartial 12 88614) = false := by
  decide +kernel

theorem node_context_12_88614_661587 : EJMOriginalGlobalDAGData.nodes 9 ⟨661587, by decide⟩ =
    .split (coordinate 12) (![⟨661535, by decide⟩,⟨661562, by decide⟩,⟨661577, by decide⟩,⟨661586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88614_661587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88614 ⟨661587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88614
    ⟨661587, by decide⟩ (by decide) (![⟨661535, by decide⟩,⟨661562, by decide⟩,⟨661577, by decide⟩,⟨661586, by decide⟩]) unmarked_context_12_88614_661587 node_context_12_88614_661587
  intro a
  fin_cases a
  · exact context_13_354456_661535
  · exact context_13_354457_661562
  · exact context_13_354458_661577
  · exact context_13_354459_661586

theorem selected_cut_26140 : selected 8 ⟨661602, by decide⟩
    (prefixPartial 13 354460) = some ⟨13, 2, 0, 661602, 354460, 877, 16384⟩ := by
  decide +kernel

theorem context_13_354460_661602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354460 ⟨661602, by decide⟩ :=
  accepted_of_selected 13 354460 ⟨661602, by decide⟩ ⟨13, 2, 0, 661602, 354460, 877, 16384⟩
    (by decide) selected_cut_26140

theorem selected_cut_26141 : selected 8 ⟨661639, by decide⟩
    (prefixPartial 13 354461) = some ⟨13, 2, 0, 661639, 354461, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_354461_661639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354461 ⟨661639, by decide⟩ :=
  accepted_of_selected 13 354461 ⟨661639, by decide⟩ ⟨13, 2, 0, 661639, 354461, 1945, 16384⟩
    (by decide) selected_cut_26141

theorem selected_cut_26142 : selected 8 ⟨661658, by decide⟩
    (prefixPartial 13 354462) = some ⟨13, 2, 0, 661658, 354462, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_354462_661658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354462 ⟨661658, by decide⟩ :=
  accepted_of_selected 13 354462 ⟨661658, by decide⟩ ⟨13, 2, 0, 661658, 354462, 1281, 16384⟩
    (by decide) selected_cut_26142

theorem selected_cut_26143 : selected 8 ⟨661668, by decide⟩
    (prefixPartial 13 354463) = some ⟨13, 2, 0, 661668, 354463, 853, 16384⟩ := by
  decide +kernel

theorem context_13_354463_661668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354463 ⟨661668, by decide⟩ :=
  accepted_of_selected 13 354463 ⟨661668, by decide⟩ ⟨13, 2, 0, 661668, 354463, 853, 16384⟩
    (by decide) selected_cut_26143

theorem unmarked_context_12_88615_661669 : frontier 9 ⟨661669, by decide⟩
    (prefixCache 12 88615) (prefixPartial 12 88615) = false := by
  decide +kernel

theorem node_context_12_88615_661669 : EJMOriginalGlobalDAGData.nodes 9 ⟨661669, by decide⟩ =
    .split (coordinate 12) (![⟨661602, by decide⟩,⟨661639, by decide⟩,⟨661658, by decide⟩,⟨661668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88615_661669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88615 ⟨661669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88615
    ⟨661669, by decide⟩ (by decide) (![⟨661602, by decide⟩,⟨661639, by decide⟩,⟨661658, by decide⟩,⟨661668, by decide⟩]) unmarked_context_12_88615_661669 node_context_12_88615_661669
  intro a
  fin_cases a
  · exact context_13_354460_661602
  · exact context_13_354461_661639
  · exact context_13_354462_661658
  · exact context_13_354463_661668

theorem unmarked_context_11_22153_661670 : frontier 10 ⟨661670, by decide⟩
    (prefixCache 11 22153) (prefixPartial 11 22153) = false := by
  decide +kernel

theorem node_context_11_22153_661670 : EJMOriginalGlobalDAGData.nodes 10 ⟨661670, by decide⟩ =
    .split (coordinate 11) (![⟨661469, by decide⟩,⟨661525, by decide⟩,⟨661587, by decide⟩,⟨661669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22153_661670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22153 ⟨661670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22153
    ⟨661670, by decide⟩ (by decide) (![⟨661469, by decide⟩,⟨661525, by decide⟩,⟨661587, by decide⟩,⟨661669, by decide⟩]) unmarked_context_11_22153_661670 node_context_11_22153_661670
  intro a
  fin_cases a
  · exact context_12_88612_661469
  · exact context_12_88613_661525
  · exact context_12_88614_661587
  · exact context_12_88615_661669

theorem selected_cut_26144 : selected 10 ⟨661673, by decide⟩
    (prefixPartial 11 22154) = some ⟨11, 2, 0, 661673, 22154, 5, 262144⟩ := by
  decide +kernel

theorem context_11_22154_661673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22154 ⟨661673, by decide⟩ :=
  accepted_of_selected 11 22154 ⟨661673, by decide⟩ ⟨11, 2, 0, 661673, 22154, 5, 262144⟩
    (by decide) selected_cut_26144

theorem selected_cut_26145 : selected 8 ⟨661684, by decide⟩
    (prefixPartial 13 354480) = some ⟨13, 2, 0, 661684, 354480, 737, 16384⟩ := by
  decide +kernel

theorem context_13_354480_661684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354480 ⟨661684, by decide⟩ :=
  accepted_of_selected 13 354480 ⟨661684, by decide⟩ ⟨13, 2, 0, 661684, 354480, 737, 16384⟩
    (by decide) selected_cut_26145

theorem selected_cut_26146 : selected 8 ⟨661715, by decide⟩
    (prefixPartial 13 354481) = some ⟨13, 2, 0, 661715, 354481, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_354481_661715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354481 ⟨661715, by decide⟩ :=
  accepted_of_selected 13 354481 ⟨661715, by decide⟩ ⟨13, 2, 0, 661715, 354481, 2069, 16384⟩
    (by decide) selected_cut_26146

theorem selected_cut_26147 : selected 8 ⟨661735, by decide⟩
    (prefixPartial 13 354482) = some ⟨13, 2, 0, 661735, 354482, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_354482_661735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354482 ⟨661735, by decide⟩ :=
  accepted_of_selected 13 354482 ⟨661735, by decide⟩ ⟨13, 2, 0, 661735, 354482, 1721, 16384⟩
    (by decide) selected_cut_26147

theorem selected_cut_26148 : selected 8 ⟨661745, by decide⟩
    (prefixPartial 13 354483) = some ⟨13, 2, 0, 661745, 354483, 945, 16384⟩ := by
  decide +kernel

theorem context_13_354483_661745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354483 ⟨661745, by decide⟩ :=
  accepted_of_selected 13 354483 ⟨661745, by decide⟩ ⟨13, 2, 0, 661745, 354483, 945, 16384⟩
    (by decide) selected_cut_26148

theorem unmarked_context_12_88620_661746 : frontier 9 ⟨661746, by decide⟩
    (prefixCache 12 88620) (prefixPartial 12 88620) = false := by
  decide +kernel

theorem node_context_12_88620_661746 : EJMOriginalGlobalDAGData.nodes 9 ⟨661746, by decide⟩ =
    .split (coordinate 12) (![⟨661684, by decide⟩,⟨661715, by decide⟩,⟨661735, by decide⟩,⟨661745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88620_661746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88620 ⟨661746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88620
    ⟨661746, by decide⟩ (by decide) (![⟨661684, by decide⟩,⟨661715, by decide⟩,⟨661735, by decide⟩,⟨661745, by decide⟩]) unmarked_context_12_88620_661746 node_context_12_88620_661746
  intro a
  fin_cases a
  · exact context_13_354480_661684
  · exact context_13_354481_661715
  · exact context_13_354482_661735
  · exact context_13_354483_661745

theorem selected_cut_26149 : selected 8 ⟨661755, by decide⟩
    (prefixPartial 13 354484) = some ⟨13, 2, 0, 661755, 354484, 725, 16384⟩ := by
  decide +kernel

theorem context_13_354484_661755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354484 ⟨661755, by decide⟩ :=
  accepted_of_selected 13 354484 ⟨661755, by decide⟩ ⟨13, 2, 0, 661755, 354484, 725, 16384⟩
    (by decide) selected_cut_26149

theorem selected_cut_26150 : selected 8 ⟨661774, by decide⟩
    (prefixPartial 13 354485) = some ⟨13, 2, 0, 661774, 354485, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_354485_661774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354485 ⟨661774, by decide⟩ :=
  accepted_of_selected 13 354485 ⟨661774, by decide⟩ ⟨13, 2, 0, 661774, 354485, 1565, 16384⟩
    (by decide) selected_cut_26150

theorem selected_cut_26151 : selected 8 ⟨661793, by decide⟩
    (prefixPartial 13 354486) = some ⟨13, 2, 0, 661793, 354486, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_354486_661793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354486 ⟨661793, by decide⟩ :=
  accepted_of_selected 13 354486 ⟨661793, by decide⟩ ⟨13, 2, 0, 661793, 354486, 1413, 16384⟩
    (by decide) selected_cut_26151

theorem selected_cut_26152 : selected 8 ⟨661800, by decide⟩
    (prefixPartial 13 354487) = some ⟨13, 2, 0, 661800, 354487, 833, 16384⟩ := by
  decide +kernel

theorem context_13_354487_661800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354487 ⟨661800, by decide⟩ :=
  accepted_of_selected 13 354487 ⟨661800, by decide⟩ ⟨13, 2, 0, 661800, 354487, 833, 16384⟩
    (by decide) selected_cut_26152

theorem unmarked_context_12_88621_661801 : frontier 9 ⟨661801, by decide⟩
    (prefixCache 12 88621) (prefixPartial 12 88621) = false := by
  decide +kernel

theorem node_context_12_88621_661801 : EJMOriginalGlobalDAGData.nodes 9 ⟨661801, by decide⟩ =
    .split (coordinate 12) (![⟨661755, by decide⟩,⟨661774, by decide⟩,⟨661793, by decide⟩,⟨661800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88621_661801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88621 ⟨661801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88621
    ⟨661801, by decide⟩ (by decide) (![⟨661755, by decide⟩,⟨661774, by decide⟩,⟨661793, by decide⟩,⟨661800, by decide⟩]) unmarked_context_12_88621_661801 node_context_12_88621_661801
  intro a
  fin_cases a
  · exact context_13_354484_661755
  · exact context_13_354485_661774
  · exact context_13_354486_661793
  · exact context_13_354487_661800

theorem selected_cut_26153 : selected 8 ⟨661811, by decide⟩
    (prefixPartial 13 354488) = some ⟨13, 2, 0, 661811, 354488, 709, 16384⟩ := by
  decide +kernel

theorem context_13_354488_661811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354488 ⟨661811, by decide⟩ :=
  accepted_of_selected 13 354488 ⟨661811, by decide⟩ ⟨13, 2, 0, 661811, 354488, 709, 16384⟩
    (by decide) selected_cut_26153

theorem selected_cut_26154 : selected 8 ⟨661849, by decide⟩
    (prefixPartial 13 354489) = some ⟨13, 2, 0, 661849, 354489, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_354489_661849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354489 ⟨661849, by decide⟩ :=
  accepted_of_selected 13 354489 ⟨661849, by decide⟩ ⟨13, 2, 0, 661849, 354489, 2093, 16384⟩
    (by decide) selected_cut_26154

theorem selected_cut_26155 : selected 8 ⟨661869, by decide⟩
    (prefixPartial 13 354490) = some ⟨13, 2, 0, 661869, 354490, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_354490_661869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354490 ⟨661869, by decide⟩ :=
  accepted_of_selected 13 354490 ⟨661869, by decide⟩ ⟨13, 2, 0, 661869, 354490, 1509, 16384⟩
    (by decide) selected_cut_26155

theorem selected_cut_26156 : selected 8 ⟨661878, by decide⟩
    (prefixPartial 13 354491) = some ⟨13, 2, 0, 661878, 354491, 809, 16384⟩ := by
  decide +kernel

theorem context_13_354491_661878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354491 ⟨661878, by decide⟩ :=
  accepted_of_selected 13 354491 ⟨661878, by decide⟩ ⟨13, 2, 0, 661878, 354491, 809, 16384⟩
    (by decide) selected_cut_26156

theorem unmarked_context_12_88622_661879 : frontier 9 ⟨661879, by decide⟩
    (prefixCache 12 88622) (prefixPartial 12 88622) = false := by
  decide +kernel

theorem node_context_12_88622_661879 : EJMOriginalGlobalDAGData.nodes 9 ⟨661879, by decide⟩ =
    .split (coordinate 12) (![⟨661811, by decide⟩,⟨661849, by decide⟩,⟨661869, by decide⟩,⟨661878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88622_661879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88622 ⟨661879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88622
    ⟨661879, by decide⟩ (by decide) (![⟨661811, by decide⟩,⟨661849, by decide⟩,⟨661869, by decide⟩,⟨661878, by decide⟩]) unmarked_context_12_88622_661879 node_context_12_88622_661879
  intro a
  fin_cases a
  · exact context_13_354488_661811
  · exact context_13_354489_661849
  · exact context_13_354490_661869
  · exact context_13_354491_661878

theorem selected_cut_26157 : selected 8 ⟨661889, by decide⟩
    (prefixPartial 13 354492) = some ⟨13, 2, 0, 661889, 354492, 801, 16384⟩ := by
  decide +kernel

theorem context_13_354492_661889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354492 ⟨661889, by decide⟩ :=
  accepted_of_selected 13 354492 ⟨661889, by decide⟩ ⟨13, 2, 0, 661889, 354492, 801, 16384⟩
    (by decide) selected_cut_26157

theorem selected_cut_26158 : selected 8 ⟨661918, by decide⟩
    (prefixPartial 13 354493) = some ⟨13, 2, 0, 661918, 354493, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_354493_661918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354493 ⟨661918, by decide⟩ :=
  accepted_of_selected 13 354493 ⟨661918, by decide⟩ ⟨13, 2, 0, 661918, 354493, 2153, 16384⟩
    (by decide) selected_cut_26158

theorem selected_cut_26159 : selected 8 ⟨661935, by decide⟩
    (prefixPartial 13 354494) = some ⟨13, 2, 0, 661935, 354494, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_354494_661935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354494 ⟨661935, by decide⟩ :=
  accepted_of_selected 13 354494 ⟨661935, by decide⟩ ⟨13, 2, 0, 661935, 354494, 1813, 16384⟩
    (by decide) selected_cut_26159

theorem selected_cut_26160 : selected 8 ⟨661942, by decide⟩
    (prefixPartial 13 354495) = some ⟨13, 2, 0, 661942, 354495, 909, 16384⟩ := by
  decide +kernel

theorem context_13_354495_661942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354495 ⟨661942, by decide⟩ :=
  accepted_of_selected 13 354495 ⟨661942, by decide⟩ ⟨13, 2, 0, 661942, 354495, 909, 16384⟩
    (by decide) selected_cut_26160

theorem unmarked_context_12_88623_661943 : frontier 9 ⟨661943, by decide⟩
    (prefixCache 12 88623) (prefixPartial 12 88623) = false := by
  decide +kernel

theorem node_context_12_88623_661943 : EJMOriginalGlobalDAGData.nodes 9 ⟨661943, by decide⟩ =
    .split (coordinate 12) (![⟨661889, by decide⟩,⟨661918, by decide⟩,⟨661935, by decide⟩,⟨661942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88623_661943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88623 ⟨661943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88623
    ⟨661943, by decide⟩ (by decide) (![⟨661889, by decide⟩,⟨661918, by decide⟩,⟨661935, by decide⟩,⟨661942, by decide⟩]) unmarked_context_12_88623_661943 node_context_12_88623_661943
  intro a
  fin_cases a
  · exact context_13_354492_661889
  · exact context_13_354493_661918
  · exact context_13_354494_661935
  · exact context_13_354495_661942

theorem unmarked_context_11_22155_661944 : frontier 10 ⟨661944, by decide⟩
    (prefixCache 11 22155) (prefixPartial 11 22155) = false := by
  decide +kernel

theorem node_context_11_22155_661944 : EJMOriginalGlobalDAGData.nodes 10 ⟨661944, by decide⟩ =
    .split (coordinate 11) (![⟨661746, by decide⟩,⟨661801, by decide⟩,⟨661879, by decide⟩,⟨661943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22155_661944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22155 ⟨661944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22155
    ⟨661944, by decide⟩ (by decide) (![⟨661746, by decide⟩,⟨661801, by decide⟩,⟨661879, by decide⟩,⟨661943, by decide⟩]) unmarked_context_11_22155_661944 node_context_11_22155_661944
  intro a
  fin_cases a
  · exact context_12_88620_661746
  · exact context_12_88621_661801
  · exact context_12_88622_661879
  · exact context_12_88623_661943

theorem unmarked_context_10_5538_661945 : frontier 11 ⟨661945, by decide⟩
    (prefixCache 10 5538) (prefixPartial 10 5538) = false := by
  decide +kernel

theorem node_context_10_5538_661945 : EJMOriginalGlobalDAGData.nodes 11 ⟨661945, by decide⟩ =
    .split (coordinate 10) (![⟨661396, by decide⟩,⟨661670, by decide⟩,⟨661673, by decide⟩,⟨661944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5538_661945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5538 ⟨661945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5538
    ⟨661945, by decide⟩ (by decide) (![⟨661396, by decide⟩,⟨661670, by decide⟩,⟨661673, by decide⟩,⟨661944, by decide⟩]) unmarked_context_10_5538_661945 node_context_10_5538_661945
  intro a
  fin_cases a
  · exact context_11_22152_661396
  · exact context_11_22153_661670
  · exact context_11_22154_661673
  · exact context_11_22155_661944

theorem selected_cut_26161 : selected 8 ⟨661954, by decide⟩
    (prefixPartial 13 354496) = some ⟨13, 2, 0, 661954, 354496, 845, 16384⟩ := by
  decide +kernel

theorem context_13_354496_661954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354496 ⟨661954, by decide⟩ :=
  accepted_of_selected 13 354496 ⟨661954, by decide⟩ ⟨13, 2, 0, 661954, 354496, 845, 16384⟩
    (by decide) selected_cut_26161

theorem selected_cut_26162 : selected 8 ⟨661988, by decide⟩
    (prefixPartial 13 354497) = some ⟨13, 2, 0, 661988, 354497, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_354497_661988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354497 ⟨661988, by decide⟩ :=
  accepted_of_selected 13 354497 ⟨661988, by decide⟩ ⟨13, 2, 0, 661988, 354497, 1993, 16384⟩
    (by decide) selected_cut_26162

theorem selected_cut_26163 : selected 8 ⟨662006, by decide⟩
    (prefixPartial 13 354498) = some ⟨13, 2, 0, 662006, 354498, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_354498_662006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354498 ⟨662006, by decide⟩ :=
  accepted_of_selected 13 354498 ⟨662006, by decide⟩ ⟨13, 2, 0, 662006, 354498, 1297, 16384⟩
    (by decide) selected_cut_26163

theorem selected_cut_26164 : selected 8 ⟨662014, by decide⟩
    (prefixPartial 13 354499) = some ⟨13, 2, 0, 662014, 354499, 777, 16384⟩ := by
  decide +kernel

theorem context_13_354499_662014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354499 ⟨662014, by decide⟩ :=
  accepted_of_selected 13 354499 ⟨662014, by decide⟩ ⟨13, 2, 0, 662014, 354499, 777, 16384⟩
    (by decide) selected_cut_26164

theorem unmarked_context_12_88624_662015 : frontier 9 ⟨662015, by decide⟩
    (prefixCache 12 88624) (prefixPartial 12 88624) = false := by
  decide +kernel

theorem node_context_12_88624_662015 : EJMOriginalGlobalDAGData.nodes 9 ⟨662015, by decide⟩ =
    .split (coordinate 12) (![⟨661954, by decide⟩,⟨661988, by decide⟩,⟨662006, by decide⟩,⟨662014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88624_662015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88624 ⟨662015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88624
    ⟨662015, by decide⟩ (by decide) (![⟨661954, by decide⟩,⟨661988, by decide⟩,⟨662006, by decide⟩,⟨662014, by decide⟩]) unmarked_context_12_88624_662015 node_context_12_88624_662015
  intro a
  fin_cases a
  · exact context_13_354496_661954
  · exact context_13_354497_661988
  · exact context_13_354498_662006
  · exact context_13_354499_662014

theorem selected_cut_26165 : selected 8 ⟨662035, by decide⟩
    (prefixPartial 13 354500) = some ⟨13, 2, 0, 662035, 354500, 881, 16384⟩ := by
  decide +kernel

theorem context_13_354500_662035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354500 ⟨662035, by decide⟩ :=
  accepted_of_selected 13 354500 ⟨662035, by decide⟩ ⟨13, 2, 0, 662035, 354500, 881, 16384⟩
    (by decide) selected_cut_26165

theorem selected_cut_26166 : selected 8 ⟨662067, by decide⟩
    (prefixPartial 13 354501) = some ⟨13, 2, 0, 662067, 354501, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_354501_662067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354501 ⟨662067, by decide⟩ :=
  accepted_of_selected 13 354501 ⟨662067, by decide⟩ ⟨13, 2, 0, 662067, 354501, 1957, 16384⟩
    (by decide) selected_cut_26166

theorem selected_cut_26167 : selected 8 ⟨662079, by decide⟩
    (prefixPartial 13 354502) = some ⟨13, 2, 0, 662079, 354502, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_354502_662079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354502 ⟨662079, by decide⟩ :=
  accepted_of_selected 13 354502 ⟨662079, by decide⟩ ⟨13, 2, 0, 662079, 354502, 1289, 16384⟩
    (by decide) selected_cut_26167

theorem selected_cut_26168 : selected 8 ⟨662088, by decide⟩
    (prefixPartial 13 354503) = some ⟨13, 2, 0, 662088, 354503, 909, 16384⟩ := by
  decide +kernel

theorem context_13_354503_662088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354503 ⟨662088, by decide⟩ :=
  accepted_of_selected 13 354503 ⟨662088, by decide⟩ ⟨13, 2, 0, 662088, 354503, 909, 16384⟩
    (by decide) selected_cut_26168

theorem unmarked_context_12_88625_662089 : frontier 9 ⟨662089, by decide⟩
    (prefixCache 12 88625) (prefixPartial 12 88625) = false := by
  decide +kernel

theorem node_context_12_88625_662089 : EJMOriginalGlobalDAGData.nodes 9 ⟨662089, by decide⟩ =
    .split (coordinate 12) (![⟨662035, by decide⟩,⟨662067, by decide⟩,⟨662079, by decide⟩,⟨662088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88625_662089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88625 ⟨662089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88625
    ⟨662089, by decide⟩ (by decide) (![⟨662035, by decide⟩,⟨662067, by decide⟩,⟨662079, by decide⟩,⟨662088, by decide⟩]) unmarked_context_12_88625_662089 node_context_12_88625_662089
  intro a
  fin_cases a
  · exact context_13_354500_662035
  · exact context_13_354501_662067
  · exact context_13_354502_662079
  · exact context_13_354503_662088

theorem selected_cut_26169 : selected 8 ⟨662098, by decide⟩
    (prefixPartial 13 354504) = some ⟨13, 2, 0, 662098, 354504, 813, 16384⟩ := by
  decide +kernel

theorem context_13_354504_662098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354504 ⟨662098, by decide⟩ :=
  accepted_of_selected 13 354504 ⟨662098, by decide⟩ ⟨13, 2, 0, 662098, 354504, 813, 16384⟩
    (by decide) selected_cut_26169

theorem selected_cut_26170 : selected 8 ⟨662126, by decide⟩
    (prefixPartial 13 354505) = some ⟨13, 2, 0, 662126, 354505, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_354505_662126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354505 ⟨662126, by decide⟩ :=
  accepted_of_selected 13 354505 ⟨662126, by decide⟩ ⟨13, 2, 0, 662126, 354505, 2213, 16384⟩
    (by decide) selected_cut_26170

theorem selected_cut_26171 : selected 8 ⟨662142, by decide⟩
    (prefixPartial 13 354506) = some ⟨13, 2, 0, 662142, 354506, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_354506_662142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354506 ⟨662142, by decide⟩ :=
  accepted_of_selected 13 354506 ⟨662142, by decide⟩ ⟨13, 2, 0, 662142, 354506, 1413, 16384⟩
    (by decide) selected_cut_26171

theorem selected_cut_26172 : selected 8 ⟨662151, by decide⟩
    (prefixPartial 13 354507) = some ⟨13, 2, 0, 662151, 354507, 885, 16384⟩ := by
  decide +kernel

theorem context_13_354507_662151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354507 ⟨662151, by decide⟩ :=
  accepted_of_selected 13 354507 ⟨662151, by decide⟩ ⟨13, 2, 0, 662151, 354507, 885, 16384⟩
    (by decide) selected_cut_26172

theorem unmarked_context_12_88626_662152 : frontier 9 ⟨662152, by decide⟩
    (prefixCache 12 88626) (prefixPartial 12 88626) = false := by
  decide +kernel

theorem node_context_12_88626_662152 : EJMOriginalGlobalDAGData.nodes 9 ⟨662152, by decide⟩ =
    .split (coordinate 12) (![⟨662098, by decide⟩,⟨662126, by decide⟩,⟨662142, by decide⟩,⟨662151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88626_662152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88626 ⟨662152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88626
    ⟨662152, by decide⟩ (by decide) (![⟨662098, by decide⟩,⟨662126, by decide⟩,⟨662142, by decide⟩,⟨662151, by decide⟩]) unmarked_context_12_88626_662152 node_context_12_88626_662152
  intro a
  fin_cases a
  · exact context_13_354504_662098
  · exact context_13_354505_662126
  · exact context_13_354506_662142
  · exact context_13_354507_662151

theorem selected_cut_26173 : selected 8 ⟨662171, by decide⟩
    (prefixPartial 13 354508) = some ⟨13, 2, 0, 662171, 354508, 937, 16384⟩ := by
  decide +kernel

theorem context_13_354508_662171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354508 ⟨662171, by decide⟩ :=
  accepted_of_selected 13 354508 ⟨662171, by decide⟩ ⟨13, 2, 0, 662171, 354508, 937, 16384⟩
    (by decide) selected_cut_26173

theorem selected_cut_26174 : selected 8 ⟨662214, by decide⟩
    (prefixPartial 13 354509) = some ⟨13, 2, 0, 662214, 354509, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_354509_662214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354509 ⟨662214, by decide⟩ :=
  accepted_of_selected 13 354509 ⟨662214, by decide⟩ ⟨13, 2, 0, 662214, 354509, 2457, 16384⟩
    (by decide) selected_cut_26174

theorem selected_cut_26175 : selected 8 ⟨662233, by decide⟩
    (prefixPartial 13 354510) = some ⟨13, 2, 0, 662233, 354510, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_354510_662233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354510 ⟨662233, by decide⟩ :=
  accepted_of_selected 13 354510 ⟨662233, by decide⟩ ⟨13, 2, 0, 662233, 354510, 1609, 16384⟩
    (by decide) selected_cut_26175

theorem selected_cut_26176 : selected 8 ⟨662240, by decide⟩
    (prefixPartial 13 354511) = some ⟨13, 2, 0, 662240, 354511, 889, 16384⟩ := by
  decide +kernel

theorem context_13_354511_662240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354511 ⟨662240, by decide⟩ :=
  accepted_of_selected 13 354511 ⟨662240, by decide⟩ ⟨13, 2, 0, 662240, 354511, 889, 16384⟩
    (by decide) selected_cut_26176

theorem unmarked_context_12_88627_662241 : frontier 9 ⟨662241, by decide⟩
    (prefixCache 12 88627) (prefixPartial 12 88627) = false := by
  decide +kernel

theorem node_context_12_88627_662241 : EJMOriginalGlobalDAGData.nodes 9 ⟨662241, by decide⟩ =
    .split (coordinate 12) (![⟨662171, by decide⟩,⟨662214, by decide⟩,⟨662233, by decide⟩,⟨662240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88627_662241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88627 ⟨662241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88627
    ⟨662241, by decide⟩ (by decide) (![⟨662171, by decide⟩,⟨662214, by decide⟩,⟨662233, by decide⟩,⟨662240, by decide⟩]) unmarked_context_12_88627_662241 node_context_12_88627_662241
  intro a
  fin_cases a
  · exact context_13_354508_662171
  · exact context_13_354509_662214
  · exact context_13_354510_662233
  · exact context_13_354511_662240

theorem unmarked_context_11_22156_662242 : frontier 10 ⟨662242, by decide⟩
    (prefixCache 11 22156) (prefixPartial 11 22156) = false := by
  decide +kernel

theorem node_context_11_22156_662242 : EJMOriginalGlobalDAGData.nodes 10 ⟨662242, by decide⟩ =
    .split (coordinate 11) (![⟨662015, by decide⟩,⟨662089, by decide⟩,⟨662152, by decide⟩,⟨662241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22156_662242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22156 ⟨662242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22156
    ⟨662242, by decide⟩ (by decide) (![⟨662015, by decide⟩,⟨662089, by decide⟩,⟨662152, by decide⟩,⟨662241, by decide⟩]) unmarked_context_11_22156_662242 node_context_11_22156_662242
  intro a
  fin_cases a
  · exact context_12_88624_662015
  · exact context_12_88625_662089
  · exact context_12_88626_662152
  · exact context_12_88627_662241

theorem selected_cut_26177 : selected 8 ⟨662251, by decide⟩
    (prefixPartial 13 354512) = some ⟨13, 2, 0, 662251, 354512, 609, 16384⟩ := by
  decide +kernel

theorem context_13_354512_662251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354512 ⟨662251, by decide⟩ :=
  accepted_of_selected 13 354512 ⟨662251, by decide⟩ ⟨13, 2, 0, 662251, 354512, 609, 16384⟩
    (by decide) selected_cut_26177

theorem selected_cut_26178 : selected 8 ⟨662291, by decide⟩
    (prefixPartial 13 354513) = some ⟨13, 2, 0, 662291, 354513, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_354513_662291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354513 ⟨662291, by decide⟩ :=
  accepted_of_selected 13 354513 ⟨662291, by decide⟩ ⟨13, 2, 0, 662291, 354513, 2425, 16384⟩
    (by decide) selected_cut_26178

theorem selected_cut_26179 : selected 8 ⟨662313, by decide⟩
    (prefixPartial 13 354514) = some ⟨13, 2, 0, 662313, 354514, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_354514_662313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354514 ⟨662313, by decide⟩ :=
  accepted_of_selected 13 354514 ⟨662313, by decide⟩ ⟨13, 2, 0, 662313, 354514, 1273, 16384⟩
    (by decide) selected_cut_26179

theorem selected_cut_26180 : selected 8 ⟨662322, by decide⟩
    (prefixPartial 13 354515) = some ⟨13, 2, 0, 662322, 354515, 877, 16384⟩ := by
  decide +kernel

theorem context_13_354515_662322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354515 ⟨662322, by decide⟩ :=
  accepted_of_selected 13 354515 ⟨662322, by decide⟩ ⟨13, 2, 0, 662322, 354515, 877, 16384⟩
    (by decide) selected_cut_26180

theorem unmarked_context_12_88628_662323 : frontier 9 ⟨662323, by decide⟩
    (prefixCache 12 88628) (prefixPartial 12 88628) = false := by
  decide +kernel

theorem node_context_12_88628_662323 : EJMOriginalGlobalDAGData.nodes 9 ⟨662323, by decide⟩ =
    .split (coordinate 12) (![⟨662251, by decide⟩,⟨662291, by decide⟩,⟨662313, by decide⟩,⟨662322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88628_662323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88628 ⟨662323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88628
    ⟨662323, by decide⟩ (by decide) (![⟨662251, by decide⟩,⟨662291, by decide⟩,⟨662313, by decide⟩,⟨662322, by decide⟩]) unmarked_context_12_88628_662323 node_context_12_88628_662323
  intro a
  fin_cases a
  · exact context_13_354512_662251
  · exact context_13_354513_662291
  · exact context_13_354514_662313
  · exact context_13_354515_662322

theorem selected_cut_26181 : selected 8 ⟨662330, by decide⟩
    (prefixPartial 13 354516) = some ⟨13, 2, 0, 662330, 354516, 537, 16384⟩ := by
  decide +kernel

theorem context_13_354516_662330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354516 ⟨662330, by decide⟩ :=
  accepted_of_selected 13 354516 ⟨662330, by decide⟩ ⟨13, 2, 0, 662330, 354516, 537, 16384⟩
    (by decide) selected_cut_26181

theorem selected_cut_26182 : selected 8 ⟨662361, by decide⟩
    (prefixPartial 13 354517) = some ⟨13, 2, 0, 662361, 354517, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_354517_662361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354517 ⟨662361, by decide⟩ :=
  accepted_of_selected 13 354517 ⟨662361, by decide⟩ ⟨13, 2, 0, 662361, 354517, 1909, 16384⟩
    (by decide) selected_cut_26182

theorem selected_cut_26183 : selected 8 ⟨662379, by decide⟩
    (prefixPartial 13 354518) = some ⟨13, 2, 0, 662379, 354518, 937, 16384⟩ := by
  decide +kernel

theorem context_13_354518_662379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354518 ⟨662379, by decide⟩ :=
  accepted_of_selected 13 354518 ⟨662379, by decide⟩ ⟨13, 2, 0, 662379, 354518, 937, 16384⟩
    (by decide) selected_cut_26183

theorem selected_cut_26184 : selected 8 ⟨662385, by decide⟩
    (prefixPartial 13 354519) = some ⟨13, 2, 0, 662385, 354519, 849, 16384⟩ := by
  decide +kernel

theorem context_13_354519_662385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354519 ⟨662385, by decide⟩ :=
  accepted_of_selected 13 354519 ⟨662385, by decide⟩ ⟨13, 2, 0, 662385, 354519, 849, 16384⟩
    (by decide) selected_cut_26184

theorem unmarked_context_12_88629_662386 : frontier 9 ⟨662386, by decide⟩
    (prefixCache 12 88629) (prefixPartial 12 88629) = false := by
  decide +kernel

theorem node_context_12_88629_662386 : EJMOriginalGlobalDAGData.nodes 9 ⟨662386, by decide⟩ =
    .split (coordinate 12) (![⟨662330, by decide⟩,⟨662361, by decide⟩,⟨662379, by decide⟩,⟨662385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88629_662386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88629 ⟨662386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88629
    ⟨662386, by decide⟩ (by decide) (![⟨662330, by decide⟩,⟨662361, by decide⟩,⟨662379, by decide⟩,⟨662385, by decide⟩]) unmarked_context_12_88629_662386 node_context_12_88629_662386
  intro a
  fin_cases a
  · exact context_13_354516_662330
  · exact context_13_354517_662361
  · exact context_13_354518_662379
  · exact context_13_354519_662385

theorem selected_cut_26185 : selected 8 ⟨662395, by decide⟩
    (prefixPartial 13 354520) = some ⟨13, 2, 0, 662395, 354520, 565, 16384⟩ := by
  decide +kernel

theorem context_13_354520_662395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354520 ⟨662395, by decide⟩ :=
  accepted_of_selected 13 354520 ⟨662395, by decide⟩ ⟨13, 2, 0, 662395, 354520, 565, 16384⟩
    (by decide) selected_cut_26185

theorem selected_cut_26186 : selected 8 ⟨662423, by decide⟩
    (prefixPartial 13 354521) = some ⟨13, 2, 0, 662423, 354521, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_354521_662423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354521 ⟨662423, by decide⟩ :=
  accepted_of_selected 13 354521 ⟨662423, by decide⟩ ⟨13, 2, 0, 662423, 354521, 2249, 16384⟩
    (by decide) selected_cut_26186

theorem selected_cut_26187 : selected 8 ⟨662438, by decide⟩
    (prefixPartial 13 354522) = some ⟨13, 2, 0, 662438, 354522, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_354522_662438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354522 ⟨662438, by decide⟩ :=
  accepted_of_selected 13 354522 ⟨662438, by decide⟩ ⟨13, 2, 0, 662438, 354522, 1257, 16384⟩
    (by decide) selected_cut_26187

theorem selected_cut_26188 : selected 8 ⟨662449, by decide⟩
    (prefixPartial 13 354523) = some ⟨13, 2, 0, 662449, 354523, 889, 16384⟩ := by
  decide +kernel

theorem context_13_354523_662449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354523 ⟨662449, by decide⟩ :=
  accepted_of_selected 13 354523 ⟨662449, by decide⟩ ⟨13, 2, 0, 662449, 354523, 889, 16384⟩
    (by decide) selected_cut_26188

theorem unmarked_context_12_88630_662450 : frontier 9 ⟨662450, by decide⟩
    (prefixCache 12 88630) (prefixPartial 12 88630) = false := by
  decide +kernel

theorem node_context_12_88630_662450 : EJMOriginalGlobalDAGData.nodes 9 ⟨662450, by decide⟩ =
    .split (coordinate 12) (![⟨662395, by decide⟩,⟨662423, by decide⟩,⟨662438, by decide⟩,⟨662449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88630_662450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88630 ⟨662450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88630
    ⟨662450, by decide⟩ (by decide) (![⟨662395, by decide⟩,⟨662423, by decide⟩,⟨662438, by decide⟩,⟨662449, by decide⟩]) unmarked_context_12_88630_662450 node_context_12_88630_662450
  intro a
  fin_cases a
  · exact context_13_354520_662395
  · exact context_13_354521_662423
  · exact context_13_354522_662438
  · exact context_13_354523_662449

theorem selected_cut_26189 : selected 8 ⟨662461, by decide⟩
    (prefixPartial 13 354524) = some ⟨13, 2, 0, 662461, 354524, 541, 16384⟩ := by
  decide +kernel

theorem context_13_354524_662461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354524 ⟨662461, by decide⟩ :=
  accepted_of_selected 13 354524 ⟨662461, by decide⟩ ⟨13, 2, 0, 662461, 354524, 541, 16384⟩
    (by decide) selected_cut_26189

theorem selected_cut_26190 : selected 8 ⟨662499, by decide⟩
    (prefixPartial 13 354525) = some ⟨13, 2, 0, 662499, 354525, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_354525_662499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354525 ⟨662499, by decide⟩ :=
  accepted_of_selected 13 354525 ⟨662499, by decide⟩ ⟨13, 2, 0, 662499, 354525, 2361, 16384⟩
    (by decide) selected_cut_26190

theorem selected_cut_26191 : selected 8 ⟨662519, by decide⟩
    (prefixPartial 13 354526) = some ⟨13, 2, 0, 662519, 354526, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_354526_662519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354526 ⟨662519, by decide⟩ :=
  accepted_of_selected 13 354526 ⟨662519, by decide⟩ ⟨13, 2, 0, 662519, 354526, 1357, 16384⟩
    (by decide) selected_cut_26191

theorem selected_cut_26192 : selected 8 ⟨662532, by decide⟩
    (prefixPartial 13 354527) = some ⟨13, 2, 0, 662532, 354527, 901, 16384⟩ := by
  decide +kernel

theorem context_13_354527_662532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354527 ⟨662532, by decide⟩ :=
  accepted_of_selected 13 354527 ⟨662532, by decide⟩ ⟨13, 2, 0, 662532, 354527, 901, 16384⟩
    (by decide) selected_cut_26192

theorem unmarked_context_12_88631_662533 : frontier 9 ⟨662533, by decide⟩
    (prefixCache 12 88631) (prefixPartial 12 88631) = false := by
  decide +kernel

theorem node_context_12_88631_662533 : EJMOriginalGlobalDAGData.nodes 9 ⟨662533, by decide⟩ =
    .split (coordinate 12) (![⟨662461, by decide⟩,⟨662499, by decide⟩,⟨662519, by decide⟩,⟨662532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88631_662533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88631 ⟨662533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88631
    ⟨662533, by decide⟩ (by decide) (![⟨662461, by decide⟩,⟨662499, by decide⟩,⟨662519, by decide⟩,⟨662532, by decide⟩]) unmarked_context_12_88631_662533 node_context_12_88631_662533
  intro a
  fin_cases a
  · exact context_13_354524_662461
  · exact context_13_354525_662499
  · exact context_13_354526_662519
  · exact context_13_354527_662532

theorem unmarked_context_11_22157_662534 : frontier 10 ⟨662534, by decide⟩
    (prefixCache 11 22157) (prefixPartial 11 22157) = false := by
  decide +kernel

theorem node_context_11_22157_662534 : EJMOriginalGlobalDAGData.nodes 10 ⟨662534, by decide⟩ =
    .split (coordinate 11) (![⟨662323, by decide⟩,⟨662386, by decide⟩,⟨662450, by decide⟩,⟨662533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22157_662534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22157 ⟨662534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22157
    ⟨662534, by decide⟩ (by decide) (![⟨662323, by decide⟩,⟨662386, by decide⟩,⟨662450, by decide⟩,⟨662533, by decide⟩]) unmarked_context_11_22157_662534 node_context_11_22157_662534
  intro a
  fin_cases a
  · exact context_12_88628_662323
  · exact context_12_88629_662386
  · exact context_12_88630_662450
  · exact context_12_88631_662533

theorem selected_cut_26193 : selected 8 ⟨662543, by decide⟩
    (prefixPartial 13 354528) = some ⟨13, 2, 0, 662543, 354528, 365, 16384⟩ := by
  decide +kernel

theorem context_13_354528_662543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354528 ⟨662543, by decide⟩ :=
  accepted_of_selected 13 354528 ⟨662543, by decide⟩ ⟨13, 2, 0, 662543, 354528, 365, 16384⟩
    (by decide) selected_cut_26193

theorem selected_cut_26194 : selected 8 ⟨662571, by decide⟩
    (prefixPartial 13 354529) = some ⟨13, 2, 0, 662571, 354529, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_354529_662571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354529 ⟨662571, by decide⟩ :=
  accepted_of_selected 13 354529 ⟨662571, by decide⟩ ⟨13, 2, 0, 662571, 354529, 1957, 16384⟩
    (by decide) selected_cut_26194

theorem selected_cut_26195 : selected 8 ⟨662587, by decide⟩
    (prefixPartial 13 354530) = some ⟨13, 2, 0, 662587, 354530, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_354530_662587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354530 ⟨662587, by decide⟩ :=
  accepted_of_selected 13 354530 ⟨662587, by decide⟩ ⟨13, 2, 0, 662587, 354530, 1489, 16384⟩
    (by decide) selected_cut_26195

theorem selected_cut_26196 : selected 8 ⟨662595, by decide⟩
    (prefixPartial 13 354531) = some ⟨13, 2, 0, 662595, 354531, 785, 16384⟩ := by
  decide +kernel

theorem context_13_354531_662595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354531 ⟨662595, by decide⟩ :=
  accepted_of_selected 13 354531 ⟨662595, by decide⟩ ⟨13, 2, 0, 662595, 354531, 785, 16384⟩
    (by decide) selected_cut_26196

theorem unmarked_context_12_88632_662596 : frontier 9 ⟨662596, by decide⟩
    (prefixCache 12 88632) (prefixPartial 12 88632) = false := by
  decide +kernel

theorem node_context_12_88632_662596 : EJMOriginalGlobalDAGData.nodes 9 ⟨662596, by decide⟩ =
    .split (coordinate 12) (![⟨662543, by decide⟩,⟨662571, by decide⟩,⟨662587, by decide⟩,⟨662595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88632_662596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88632 ⟨662596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88632
    ⟨662596, by decide⟩ (by decide) (![⟨662543, by decide⟩,⟨662571, by decide⟩,⟨662587, by decide⟩,⟨662595, by decide⟩]) unmarked_context_12_88632_662596 node_context_12_88632_662596
  intro a
  fin_cases a
  · exact context_13_354528_662543
  · exact context_13_354529_662571
  · exact context_13_354530_662587
  · exact context_13_354531_662595

theorem selected_cut_26197 : selected 9 ⟨662654, by decide⟩
    (prefixPartial 12 88633) = some ⟨12, 2, 0, 662654, 88633, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_88633_662654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88633 ⟨662654, by decide⟩ :=
  accepted_of_selected 12 88633 ⟨662654, by decide⟩ ⟨12, 2, 0, 662654, 88633, 4093, 65536⟩
    (by decide) selected_cut_26197

theorem selected_cut_26198 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 88634) = some ⟨12, 1, 0, 662655, 88634, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88634_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88634 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 88634 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 88634, 1, 65536⟩
    (by decide) selected_cut_26198

theorem selected_cut_26199 : selected 8 ⟨662664, by decide⟩
    (prefixPartial 13 354540) = some ⟨13, 2, 0, 662664, 354540, 317, 16384⟩ := by
  decide +kernel

theorem context_13_354540_662664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354540 ⟨662664, by decide⟩ :=
  accepted_of_selected 13 354540 ⟨662664, by decide⟩ ⟨13, 2, 0, 662664, 354540, 317, 16384⟩
    (by decide) selected_cut_26199

theorem selected_cut_26200 : selected 8 ⟨662706, by decide⟩
    (prefixPartial 13 354541) = some ⟨13, 2, 0, 662706, 354541, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_354541_662706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354541 ⟨662706, by decide⟩ :=
  accepted_of_selected 13 354541 ⟨662706, by decide⟩ ⟨13, 2, 0, 662706, 354541, 2469, 16384⟩
    (by decide) selected_cut_26200

theorem selected_cut_26201 : selected 8 ⟨662725, by decide⟩
    (prefixPartial 13 354542) = some ⟨13, 2, 0, 662725, 354542, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_354542_662725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354542 ⟨662725, by decide⟩ :=
  accepted_of_selected 13 354542 ⟨662725, by decide⟩ ⟨13, 2, 0, 662725, 354542, 1577, 16384⟩
    (by decide) selected_cut_26201

theorem selected_cut_26202 : selected 8 ⟨662732, by decide⟩
    (prefixPartial 13 354543) = some ⟨13, 2, 0, 662732, 354543, 845, 16384⟩ := by
  decide +kernel

theorem context_13_354543_662732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354543 ⟨662732, by decide⟩ :=
  accepted_of_selected 13 354543 ⟨662732, by decide⟩ ⟨13, 2, 0, 662732, 354543, 845, 16384⟩
    (by decide) selected_cut_26202

theorem unmarked_context_12_88635_662733 : frontier 9 ⟨662733, by decide⟩
    (prefixCache 12 88635) (prefixPartial 12 88635) = false := by
  decide +kernel

theorem node_context_12_88635_662733 : EJMOriginalGlobalDAGData.nodes 9 ⟨662733, by decide⟩ =
    .split (coordinate 12) (![⟨662664, by decide⟩,⟨662706, by decide⟩,⟨662725, by decide⟩,⟨662732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88635_662733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88635 ⟨662733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88635
    ⟨662733, by decide⟩ (by decide) (![⟨662664, by decide⟩,⟨662706, by decide⟩,⟨662725, by decide⟩,⟨662732, by decide⟩]) unmarked_context_12_88635_662733 node_context_12_88635_662733
  intro a
  fin_cases a
  · exact context_13_354540_662664
  · exact context_13_354541_662706
  · exact context_13_354542_662725
  · exact context_13_354543_662732

theorem unmarked_context_11_22158_662734 : frontier 10 ⟨662734, by decide⟩
    (prefixCache 11 22158) (prefixPartial 11 22158) = false := by
  decide +kernel

theorem node_context_11_22158_662734 : EJMOriginalGlobalDAGData.nodes 10 ⟨662734, by decide⟩ =
    .split (coordinate 11) (![⟨662596, by decide⟩,⟨662654, by decide⟩,⟨662655, by decide⟩,⟨662733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22158_662734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22158 ⟨662734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22158
    ⟨662734, by decide⟩ (by decide) (![⟨662596, by decide⟩,⟨662654, by decide⟩,⟨662655, by decide⟩,⟨662733, by decide⟩]) unmarked_context_11_22158_662734 node_context_11_22158_662734
  intro a
  fin_cases a
  · exact context_12_88632_662596
  · exact context_12_88633_662654
  · exact context_12_88634_662655
  · exact context_12_88635_662733

theorem selected_cut_26203 : selected 8 ⟨662739, by decide⟩
    (prefixPartial 13 354544) = some ⟨13, 2, 0, 662739, 354544, 205, 16384⟩ := by
  decide +kernel

theorem context_13_354544_662739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354544 ⟨662739, by decide⟩ :=
  accepted_of_selected 13 354544 ⟨662739, by decide⟩ ⟨13, 2, 0, 662739, 354544, 205, 16384⟩
    (by decide) selected_cut_26203

theorem selected_cut_26204 : selected 8 ⟨662780, by decide⟩
    (prefixPartial 13 354545) = some ⟨13, 2, 0, 662780, 354545, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_354545_662780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354545 ⟨662780, by decide⟩ :=
  accepted_of_selected 13 354545 ⟨662780, by decide⟩ ⟨13, 2, 0, 662780, 354545, 2449, 16384⟩
    (by decide) selected_cut_26204

theorem selected_cut_26205 : selected 8 ⟨662805, by decide⟩
    (prefixPartial 13 354546) = some ⟨13, 2, 0, 662805, 354546, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_354546_662805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354546 ⟨662805, by decide⟩ :=
  accepted_of_selected 13 354546 ⟨662805, by decide⟩ ⟨13, 2, 0, 662805, 354546, 1673, 16384⟩
    (by decide) selected_cut_26205

theorem selected_cut_26206 : selected 8 ⟨662813, by decide⟩
    (prefixPartial 13 354547) = some ⟨13, 2, 0, 662813, 354547, 885, 16384⟩ := by
  decide +kernel

theorem context_13_354547_662813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354547 ⟨662813, by decide⟩ :=
  accepted_of_selected 13 354547 ⟨662813, by decide⟩ ⟨13, 2, 0, 662813, 354547, 885, 16384⟩
    (by decide) selected_cut_26206

theorem unmarked_context_12_88636_662814 : frontier 9 ⟨662814, by decide⟩
    (prefixCache 12 88636) (prefixPartial 12 88636) = false := by
  decide +kernel

theorem node_context_12_88636_662814 : EJMOriginalGlobalDAGData.nodes 9 ⟨662814, by decide⟩ =
    .split (coordinate 12) (![⟨662739, by decide⟩,⟨662780, by decide⟩,⟨662805, by decide⟩,⟨662813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88636_662814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88636 ⟨662814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88636
    ⟨662814, by decide⟩ (by decide) (![⟨662739, by decide⟩,⟨662780, by decide⟩,⟨662805, by decide⟩,⟨662813, by decide⟩]) unmarked_context_12_88636_662814 node_context_12_88636_662814
  intro a
  fin_cases a
  · exact context_13_354544_662739
  · exact context_13_354545_662780
  · exact context_13_354546_662805
  · exact context_13_354547_662813

theorem selected_cut_26207 : selected 8 ⟨662820, by decide⟩
    (prefixPartial 13 354548) = some ⟨13, 2, 0, 662820, 354548, 209, 16384⟩ := by
  decide +kernel

theorem context_13_354548_662820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354548 ⟨662820, by decide⟩ :=
  accepted_of_selected 13 354548 ⟨662820, by decide⟩ ⟨13, 2, 0, 662820, 354548, 209, 16384⟩
    (by decide) selected_cut_26207

theorem selected_cut_26208 : selected 8 ⟨662849, by decide⟩
    (prefixPartial 13 354549) = some ⟨13, 2, 0, 662849, 354549, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_354549_662849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354549 ⟨662849, by decide⟩ :=
  accepted_of_selected 13 354549 ⟨662849, by decide⟩ ⟨13, 2, 0, 662849, 354549, 2045, 16384⟩
    (by decide) selected_cut_26208

theorem selected_cut_26209 : selected 8 ⟨662867, by decide⟩
    (prefixPartial 13 354550) = some ⟨13, 2, 0, 662867, 354550, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_354550_662867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354550 ⟨662867, by decide⟩ :=
  accepted_of_selected 13 354550 ⟨662867, by decide⟩ ⟨13, 2, 0, 662867, 354550, 1301, 16384⟩
    (by decide) selected_cut_26209

theorem selected_cut_26210 : selected 8 ⟨662874, by decide⟩
    (prefixPartial 13 354551) = some ⟨13, 2, 0, 662874, 354551, 905, 16384⟩ := by
  decide +kernel

theorem context_13_354551_662874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354551 ⟨662874, by decide⟩ :=
  accepted_of_selected 13 354551 ⟨662874, by decide⟩ ⟨13, 2, 0, 662874, 354551, 905, 16384⟩
    (by decide) selected_cut_26210

theorem unmarked_context_12_88637_662875 : frontier 9 ⟨662875, by decide⟩
    (prefixCache 12 88637) (prefixPartial 12 88637) = false := by
  decide +kernel

theorem node_context_12_88637_662875 : EJMOriginalGlobalDAGData.nodes 9 ⟨662875, by decide⟩ =
    .split (coordinate 12) (![⟨662820, by decide⟩,⟨662849, by decide⟩,⟨662867, by decide⟩,⟨662874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88637_662875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88637 ⟨662875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88637
    ⟨662875, by decide⟩ (by decide) (![⟨662820, by decide⟩,⟨662849, by decide⟩,⟨662867, by decide⟩,⟨662874, by decide⟩]) unmarked_context_12_88637_662875 node_context_12_88637_662875
  intro a
  fin_cases a
  · exact context_13_354548_662820
  · exact context_13_354549_662849
  · exact context_13_354550_662867
  · exact context_13_354551_662874

theorem selected_cut_26211 : selected 8 ⟨662880, by decide⟩
    (prefixPartial 13 354552) = some ⟨13, 2, 0, 662880, 354552, 93, 16384⟩ := by
  decide +kernel

theorem context_13_354552_662880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354552 ⟨662880, by decide⟩ :=
  accepted_of_selected 13 354552 ⟨662880, by decide⟩ ⟨13, 2, 0, 662880, 354552, 93, 16384⟩
    (by decide) selected_cut_26211

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
