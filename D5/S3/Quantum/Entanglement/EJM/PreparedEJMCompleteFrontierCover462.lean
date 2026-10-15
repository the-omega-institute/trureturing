/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover461
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_44355 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353889) = some ⟨12, 1, 0, 896706, 353889, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353889_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353889 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353889 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353889, 1, 65536⟩
    (by decide) selected_cut_44355

theorem selected_cut_44356 : selected 9 ⟨1219901, by decide⟩
    (prefixPartial 12 353890) = some ⟨12, 2, 0, 1219901, 353890, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_353890_1219901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353890 ⟨1219901, by decide⟩ :=
  accepted_of_selected 12 353890 ⟨1219901, by decide⟩ ⟨12, 2, 0, 1219901, 353890, 1301, 65536⟩
    (by decide) selected_cut_44356

theorem selected_cut_44357 : selected 9 ⟨1219920, by decide⟩
    (prefixPartial 12 353891) = some ⟨12, 2, 0, 1219920, 353891, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_353891_1219920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353891 ⟨1219920, by decide⟩ :=
  accepted_of_selected 12 353891 ⟨1219920, by decide⟩ ⟨12, 2, 0, 1219920, 353891, 1537, 65536⟩
    (by decide) selected_cut_44357

theorem unmarked_context_11_88472_1219921 : frontier 10 ⟨1219921, by decide⟩
    (prefixCache 11 88472) (prefixPartial 11 88472) = false := by
  decide +kernel

theorem node_context_11_88472_1219921 : EJMOriginalGlobalDAGData.nodes 10 ⟨1219921, by decide⟩ =
    .split (coordinate 11) (![⟨1219884, by decide⟩,⟨896706, by decide⟩,⟨1219901, by decide⟩,⟨1219920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88472_1219921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88472 ⟨1219921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88472
    ⟨1219921, by decide⟩ (by decide) (![⟨1219884, by decide⟩,⟨896706, by decide⟩,⟨1219901, by decide⟩,⟨1219920, by decide⟩]) unmarked_context_11_88472_1219921 node_context_11_88472_1219921
  intro a
  fin_cases a
  · exact context_12_353888_1219884
  · exact context_12_353889_896706
  · exact context_12_353890_1219901
  · exact context_12_353891_1219920

theorem selected_cut_44358 : selected 10 ⟨1219972, by decide⟩
    (prefixPartial 11 88473) = some ⟨11, 2, 0, 1219972, 88473, 3297, 262144⟩ := by
  decide +kernel

theorem context_11_88473_1219972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88473 ⟨1219972, by decide⟩ :=
  accepted_of_selected 11 88473 ⟨1219972, by decide⟩ ⟨11, 2, 0, 1219972, 88473, 3297, 262144⟩
    (by decide) selected_cut_44358

theorem selected_cut_44359 : selected 10 ⟨1219974, by decide⟩
    (prefixPartial 11 88474) = some ⟨11, 2, 0, 1219974, 88474, 5, 262144⟩ := by
  decide +kernel

theorem context_11_88474_1219974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88474 ⟨1219974, by decide⟩ :=
  accepted_of_selected 11 88474 ⟨1219974, by decide⟩ ⟨11, 2, 0, 1219974, 88474, 5, 262144⟩
    (by decide) selected_cut_44359

theorem selected_cut_44360 : selected 10 ⟨1220035, by decide⟩
    (prefixPartial 11 88475) = some ⟨11, 2, 0, 1220035, 88475, 4037, 262144⟩ := by
  decide +kernel

theorem context_11_88475_1220035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88475 ⟨1220035, by decide⟩ :=
  accepted_of_selected 11 88475 ⟨1220035, by decide⟩ ⟨11, 2, 0, 1220035, 88475, 4037, 262144⟩
    (by decide) selected_cut_44360

theorem unmarked_context_10_22118_1220036 : frontier 11 ⟨1220036, by decide⟩
    (prefixCache 10 22118) (prefixPartial 10 22118) = false := by
  decide +kernel

theorem node_context_10_22118_1220036 : EJMOriginalGlobalDAGData.nodes 11 ⟨1220036, by decide⟩ =
    .split (coordinate 10) (![⟨1219921, by decide⟩,⟨1219972, by decide⟩,⟨1219974, by decide⟩,⟨1220035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22118_1220036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22118 ⟨1220036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22118
    ⟨1220036, by decide⟩ (by decide) (![⟨1219921, by decide⟩,⟨1219972, by decide⟩,⟨1219974, by decide⟩,⟨1220035, by decide⟩]) unmarked_context_10_22118_1220036 node_context_10_22118_1220036
  intro a
  fin_cases a
  · exact context_11_88472_1219921
  · exact context_11_88473_1219972
  · exact context_11_88474_1219974
  · exact context_11_88475_1220035

theorem selected_cut_44361 : selected 10 ⟨1220090, by decide⟩
    (prefixPartial 11 88476) = some ⟨11, 2, 0, 1220090, 88476, 3665, 262144⟩ := by
  decide +kernel

theorem context_11_88476_1220090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88476 ⟨1220090, by decide⟩ :=
  accepted_of_selected 11 88476 ⟨1220090, by decide⟩ ⟨11, 2, 0, 1220090, 88476, 3665, 262144⟩
    (by decide) selected_cut_44361

theorem selected_cut_44362 : selected 10 ⟨1220136, by decide⟩
    (prefixPartial 11 88477) = some ⟨11, 2, 0, 1220136, 88477, 2573, 262144⟩ := by
  decide +kernel

theorem context_11_88477_1220136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88477 ⟨1220136, by decide⟩ :=
  accepted_of_selected 11 88477 ⟨1220136, by decide⟩ ⟨11, 2, 0, 1220136, 88477, 2573, 262144⟩
    (by decide) selected_cut_44362

theorem selected_cut_44363 : selected 10 ⟨1220169, by decide⟩
    (prefixPartial 11 88478) = some ⟨11, 2, 0, 1220169, 88478, 2121, 262144⟩ := by
  decide +kernel

theorem context_11_88478_1220169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88478 ⟨1220169, by decide⟩ :=
  accepted_of_selected 11 88478 ⟨1220169, by decide⟩ ⟨11, 2, 0, 1220169, 88478, 2121, 262144⟩
    (by decide) selected_cut_44363

theorem selected_cut_44364 : selected 10 ⟨1220198, by decide⟩
    (prefixPartial 11 88479) = some ⟨11, 2, 0, 1220198, 88479, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_88479_1220198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88479 ⟨1220198, by decide⟩ :=
  accepted_of_selected 11 88479 ⟨1220198, by decide⟩ ⟨11, 2, 0, 1220198, 88479, 1949, 262144⟩
    (by decide) selected_cut_44364

theorem unmarked_context_10_22119_1220199 : frontier 11 ⟨1220199, by decide⟩
    (prefixCache 10 22119) (prefixPartial 10 22119) = false := by
  decide +kernel

theorem node_context_10_22119_1220199 : EJMOriginalGlobalDAGData.nodes 11 ⟨1220199, by decide⟩ =
    .split (coordinate 10) (![⟨1220090, by decide⟩,⟨1220136, by decide⟩,⟨1220169, by decide⟩,⟨1220198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22119_1220199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22119 ⟨1220199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22119
    ⟨1220199, by decide⟩ (by decide) (![⟨1220090, by decide⟩,⟨1220136, by decide⟩,⟨1220169, by decide⟩,⟨1220198, by decide⟩]) unmarked_context_10_22119_1220199 node_context_10_22119_1220199
  intro a
  fin_cases a
  · exact context_11_88476_1220090
  · exact context_11_88477_1220136
  · exact context_11_88478_1220169
  · exact context_11_88479_1220198

theorem unmarked_context_9_5529_1220200 : frontier 12 ⟨1220200, by decide⟩
    (prefixCache 9 5529) (prefixPartial 9 5529) = false := by
  decide +kernel

theorem node_context_9_5529_1220200 : EJMOriginalGlobalDAGData.nodes 12 ⟨1220200, by decide⟩ =
    .split (coordinate 9) (![⟨1219858, by decide⟩,⟨893098, by decide⟩,⟨1220036, by decide⟩,⟨1220199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5529_1220200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5529 ⟨1220200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5529
    ⟨1220200, by decide⟩ (by decide) (![⟨1219858, by decide⟩,⟨893098, by decide⟩,⟨1220036, by decide⟩,⟨1220199, by decide⟩]) unmarked_context_9_5529_1220200 node_context_9_5529_1220200
  intro a
  fin_cases a
  · exact context_10_22116_1219858
  · exact context_10_22117_893098
  · exact context_10_22118_1220036
  · exact context_10_22119_1220199

theorem selected_cut_44365 : selected 10 ⟨1220238, by decide⟩
    (prefixPartial 11 88480) = some ⟨11, 2, 0, 1220238, 88480, 2821, 262144⟩ := by
  decide +kernel

theorem context_11_88480_1220238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88480 ⟨1220238, by decide⟩ :=
  accepted_of_selected 11 88480 ⟨1220238, by decide⟩ ⟨11, 2, 0, 1220238, 88480, 2821, 262144⟩
    (by decide) selected_cut_44365

theorem selected_cut_44366 : selected 10 ⟨1220273, by decide⟩
    (prefixPartial 11 88481) = some ⟨11, 2, 0, 1220273, 88481, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_88481_1220273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88481 ⟨1220273, by decide⟩ :=
  accepted_of_selected 11 88481 ⟨1220273, by decide⟩ ⟨11, 2, 0, 1220273, 88481, 2073, 262144⟩
    (by decide) selected_cut_44366

theorem selected_cut_44367 : selected 10 ⟨1220324, by decide⟩
    (prefixPartial 11 88482) = some ⟨11, 2, 0, 1220324, 88482, 3217, 262144⟩ := by
  decide +kernel

theorem context_11_88482_1220324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88482 ⟨1220324, by decide⟩ :=
  accepted_of_selected 11 88482 ⟨1220324, by decide⟩ ⟨11, 2, 0, 1220324, 88482, 3217, 262144⟩
    (by decide) selected_cut_44367

theorem selected_cut_44368 : selected 10 ⟨1220380, by decide⟩
    (prefixPartial 11 88483) = some ⟨11, 2, 0, 1220380, 88483, 3641, 262144⟩ := by
  decide +kernel

theorem context_11_88483_1220380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88483 ⟨1220380, by decide⟩ :=
  accepted_of_selected 11 88483 ⟨1220380, by decide⟩ ⟨11, 2, 0, 1220380, 88483, 3641, 262144⟩
    (by decide) selected_cut_44368

theorem unmarked_context_10_22120_1220381 : frontier 11 ⟨1220381, by decide⟩
    (prefixCache 10 22120) (prefixPartial 10 22120) = false := by
  decide +kernel

theorem node_context_10_22120_1220381 : EJMOriginalGlobalDAGData.nodes 11 ⟨1220381, by decide⟩ =
    .split (coordinate 10) (![⟨1220238, by decide⟩,⟨1220273, by decide⟩,⟨1220324, by decide⟩,⟨1220380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22120_1220381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22120 ⟨1220381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22120
    ⟨1220381, by decide⟩ (by decide) (![⟨1220238, by decide⟩,⟨1220273, by decide⟩,⟨1220324, by decide⟩,⟨1220380, by decide⟩]) unmarked_context_10_22120_1220381 node_context_10_22120_1220381
  intro a
  fin_cases a
  · exact context_11_88480_1220238
  · exact context_11_88481_1220273
  · exact context_11_88482_1220324
  · exact context_11_88483_1220380

theorem selected_cut_44369 : selected 10 ⟨1220416, by decide⟩
    (prefixPartial 11 88484) = some ⟨11, 2, 0, 1220416, 88484, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_88484_1220416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88484 ⟨1220416, by decide⟩ :=
  accepted_of_selected 11 88484 ⟨1220416, by decide⟩ ⟨11, 2, 0, 1220416, 88484, 2369, 262144⟩
    (by decide) selected_cut_44369

theorem selected_cut_44370 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88485) = some ⟨11, 1, 0, 892405, 88485, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88485_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88485 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88485 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88485, 1, 262144⟩
    (by decide) selected_cut_44370

theorem selected_cut_44371 : selected 10 ⟨1220457, by decide⟩
    (prefixPartial 11 88486) = some ⟨11, 2, 0, 1220457, 88486, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_88486_1220457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88486 ⟨1220457, by decide⟩ :=
  accepted_of_selected 11 88486 ⟨1220457, by decide⟩ ⟨11, 2, 0, 1220457, 88486, 2397, 262144⟩
    (by decide) selected_cut_44371

theorem selected_cut_44372 : selected 10 ⟨1220491, by decide⟩
    (prefixPartial 11 88487) = some ⟨11, 2, 0, 1220491, 88487, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_88487_1220491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88487 ⟨1220491, by decide⟩ :=
  accepted_of_selected 11 88487 ⟨1220491, by decide⟩ ⟨11, 2, 0, 1220491, 88487, 2165, 262144⟩
    (by decide) selected_cut_44372

theorem unmarked_context_10_22121_1220492 : frontier 11 ⟨1220492, by decide⟩
    (prefixCache 10 22121) (prefixPartial 10 22121) = false := by
  decide +kernel

theorem node_context_10_22121_1220492 : EJMOriginalGlobalDAGData.nodes 11 ⟨1220492, by decide⟩ =
    .split (coordinate 10) (![⟨1220416, by decide⟩,⟨892405, by decide⟩,⟨1220457, by decide⟩,⟨1220491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22121_1220492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22121 ⟨1220492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22121
    ⟨1220492, by decide⟩ (by decide) (![⟨1220416, by decide⟩,⟨892405, by decide⟩,⟨1220457, by decide⟩,⟨1220491, by decide⟩]) unmarked_context_10_22121_1220492 node_context_10_22121_1220492
  intro a
  fin_cases a
  · exact context_11_88484_1220416
  · exact context_11_88485_892405
  · exact context_11_88486_1220457
  · exact context_11_88487_1220491

theorem selected_cut_44373 : selected 11 ⟨1220533, by decide⟩
    (prefixPartial 10 22122) = some ⟨10, 2, 0, 1220533, 22122, 2981, 1048576⟩ := by
  decide +kernel

theorem context_10_22122_1220533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22122 ⟨1220533, by decide⟩ :=
  accepted_of_selected 10 22122 ⟨1220533, by decide⟩ ⟨10, 2, 0, 1220533, 22122, 2981, 1048576⟩
    (by decide) selected_cut_44373

theorem selected_cut_44374 : selected 10 ⟨1220561, by decide⟩
    (prefixPartial 11 88492) = some ⟨11, 2, 0, 1220561, 88492, 2325, 262144⟩ := by
  decide +kernel

theorem context_11_88492_1220561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88492 ⟨1220561, by decide⟩ :=
  accepted_of_selected 11 88492 ⟨1220561, by decide⟩ ⟨11, 2, 0, 1220561, 88492, 2325, 262144⟩
    (by decide) selected_cut_44374

theorem selected_cut_44375 : selected 10 ⟨1220581, by decide⟩
    (prefixPartial 11 88493) = some ⟨11, 2, 0, 1220581, 88493, 1085, 262144⟩ := by
  decide +kernel

theorem context_11_88493_1220581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88493 ⟨1220581, by decide⟩ :=
  accepted_of_selected 11 88493 ⟨1220581, by decide⟩ ⟨11, 2, 0, 1220581, 88493, 1085, 262144⟩
    (by decide) selected_cut_44375

theorem selected_cut_44376 : selected 10 ⟨1220602, by decide⟩
    (prefixPartial 11 88494) = some ⟨11, 2, 0, 1220602, 88494, 1509, 262144⟩ := by
  decide +kernel

theorem context_11_88494_1220602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88494 ⟨1220602, by decide⟩ :=
  accepted_of_selected 11 88494 ⟨1220602, by decide⟩ ⟨11, 2, 0, 1220602, 88494, 1509, 262144⟩
    (by decide) selected_cut_44376

theorem selected_cut_44377 : selected 10 ⟨1220616, by decide⟩
    (prefixPartial 11 88495) = some ⟨11, 2, 0, 1220616, 88495, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_88495_1220616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88495 ⟨1220616, by decide⟩ :=
  accepted_of_selected 11 88495 ⟨1220616, by decide⟩ ⟨11, 2, 0, 1220616, 88495, 1257, 262144⟩
    (by decide) selected_cut_44377

theorem unmarked_context_10_22123_1220617 : frontier 11 ⟨1220617, by decide⟩
    (prefixCache 10 22123) (prefixPartial 10 22123) = false := by
  decide +kernel

theorem node_context_10_22123_1220617 : EJMOriginalGlobalDAGData.nodes 11 ⟨1220617, by decide⟩ =
    .split (coordinate 10) (![⟨1220561, by decide⟩,⟨1220581, by decide⟩,⟨1220602, by decide⟩,⟨1220616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22123_1220617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22123 ⟨1220617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22123
    ⟨1220617, by decide⟩ (by decide) (![⟨1220561, by decide⟩,⟨1220581, by decide⟩,⟨1220602, by decide⟩,⟨1220616, by decide⟩]) unmarked_context_10_22123_1220617 node_context_10_22123_1220617
  intro a
  fin_cases a
  · exact context_11_88492_1220561
  · exact context_11_88493_1220581
  · exact context_11_88494_1220602
  · exact context_11_88495_1220616

theorem unmarked_context_9_5530_1220618 : frontier 12 ⟨1220618, by decide⟩
    (prefixCache 9 5530) (prefixPartial 9 5530) = false := by
  decide +kernel

theorem node_context_9_5530_1220618 : EJMOriginalGlobalDAGData.nodes 12 ⟨1220618, by decide⟩ =
    .split (coordinate 9) (![⟨1220381, by decide⟩,⟨1220492, by decide⟩,⟨1220533, by decide⟩,⟨1220617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5530_1220618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5530 ⟨1220618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5530
    ⟨1220618, by decide⟩ (by decide) (![⟨1220381, by decide⟩,⟨1220492, by decide⟩,⟨1220533, by decide⟩,⟨1220617, by decide⟩]) unmarked_context_9_5530_1220618 node_context_9_5530_1220618
  intro a
  fin_cases a
  · exact context_10_22120_1220381
  · exact context_10_22121_1220492
  · exact context_10_22122_1220533
  · exact context_10_22123_1220617

theorem selected_cut_44378 : selected 10 ⟨1220633, by decide⟩
    (prefixPartial 11 88496) = some ⟨11, 2, 0, 1220633, 88496, 1273, 262144⟩ := by
  decide +kernel

theorem context_11_88496_1220633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88496 ⟨1220633, by decide⟩ :=
  accepted_of_selected 11 88496 ⟨1220633, by decide⟩ ⟨11, 2, 0, 1220633, 88496, 1273, 262144⟩
    (by decide) selected_cut_44378

theorem selected_cut_44379 : selected 10 ⟨1220651, by decide⟩
    (prefixPartial 11 88497) = some ⟨11, 2, 0, 1220651, 88497, 1505, 262144⟩ := by
  decide +kernel

theorem context_11_88497_1220651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88497 ⟨1220651, by decide⟩ :=
  accepted_of_selected 11 88497 ⟨1220651, by decide⟩ ⟨11, 2, 0, 1220651, 88497, 1505, 262144⟩
    (by decide) selected_cut_44379

theorem selected_cut_44380 : selected 10 ⟨1220664, by decide⟩
    (prefixPartial 11 88498) = some ⟨11, 2, 0, 1220664, 88498, 1065, 262144⟩ := by
  decide +kernel

theorem context_11_88498_1220664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88498 ⟨1220664, by decide⟩ :=
  accepted_of_selected 11 88498 ⟨1220664, by decide⟩ ⟨11, 2, 0, 1220664, 88498, 1065, 262144⟩
    (by decide) selected_cut_44380

theorem selected_cut_44381 : selected 10 ⟨1220682, by decide⟩
    (prefixPartial 11 88499) = some ⟨11, 2, 0, 1220682, 88499, 1117, 262144⟩ := by
  decide +kernel

theorem context_11_88499_1220682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88499 ⟨1220682, by decide⟩ :=
  accepted_of_selected 11 88499 ⟨1220682, by decide⟩ ⟨11, 2, 0, 1220682, 88499, 1117, 262144⟩
    (by decide) selected_cut_44381

theorem unmarked_context_10_22124_1220683 : frontier 11 ⟨1220683, by decide⟩
    (prefixCache 10 22124) (prefixPartial 10 22124) = false := by
  decide +kernel

theorem node_context_10_22124_1220683 : EJMOriginalGlobalDAGData.nodes 11 ⟨1220683, by decide⟩ =
    .split (coordinate 10) (![⟨1220633, by decide⟩,⟨1220651, by decide⟩,⟨1220664, by decide⟩,⟨1220682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22124_1220683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22124 ⟨1220683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22124
    ⟨1220683, by decide⟩ (by decide) (![⟨1220633, by decide⟩,⟨1220651, by decide⟩,⟨1220664, by decide⟩,⟨1220682, by decide⟩]) unmarked_context_10_22124_1220683 node_context_10_22124_1220683
  intro a
  fin_cases a
  · exact context_11_88496_1220633
  · exact context_11_88497_1220651
  · exact context_11_88498_1220664
  · exact context_11_88499_1220682

theorem selected_cut_44382 : selected 11 ⟨1220724, by decide⟩
    (prefixPartial 10 22125) = some ⟨10, 2, 0, 1220724, 22125, 2429, 1048576⟩ := by
  decide +kernel

theorem context_10_22125_1220724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22125 ⟨1220724, by decide⟩ :=
  accepted_of_selected 10 22125 ⟨1220724, by decide⟩ ⟨10, 2, 0, 1220724, 22125, 2429, 1048576⟩
    (by decide) selected_cut_44382

theorem selected_cut_44383 : selected 11 ⟨1220764, by decide⟩
    (prefixPartial 10 22126) = some ⟨10, 2, 0, 1220764, 22126, 1617, 1048576⟩ := by
  decide +kernel

theorem context_10_22126_1220764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22126 ⟨1220764, by decide⟩ :=
  accepted_of_selected 10 22126 ⟨1220764, by decide⟩ ⟨10, 2, 0, 1220764, 22126, 1617, 1048576⟩
    (by decide) selected_cut_44383

theorem selected_cut_44384 : selected 11 ⟨1220782, by decide⟩
    (prefixPartial 10 22127) = some ⟨10, 2, 0, 1220782, 22127, 257, 1048576⟩ := by
  decide +kernel

theorem context_10_22127_1220782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22127 ⟨1220782, by decide⟩ :=
  accepted_of_selected 10 22127 ⟨1220782, by decide⟩ ⟨10, 2, 0, 1220782, 22127, 257, 1048576⟩
    (by decide) selected_cut_44384

theorem unmarked_context_9_5531_1220783 : frontier 12 ⟨1220783, by decide⟩
    (prefixCache 9 5531) (prefixPartial 9 5531) = false := by
  decide +kernel

theorem node_context_9_5531_1220783 : EJMOriginalGlobalDAGData.nodes 12 ⟨1220783, by decide⟩ =
    .split (coordinate 9) (![⟨1220683, by decide⟩,⟨1220724, by decide⟩,⟨1220764, by decide⟩,⟨1220782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5531_1220783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5531 ⟨1220783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5531
    ⟨1220783, by decide⟩ (by decide) (![⟨1220683, by decide⟩,⟨1220724, by decide⟩,⟨1220764, by decide⟩,⟨1220782, by decide⟩]) unmarked_context_9_5531_1220783 node_context_9_5531_1220783
  intro a
  fin_cases a
  · exact context_10_22124_1220683
  · exact context_10_22125_1220724
  · exact context_10_22126_1220764
  · exact context_10_22127_1220782

theorem unmarked_context_8_1382_1220784 : frontier 13 ⟨1220784, by decide⟩
    (prefixCache 8 1382) (prefixPartial 8 1382) = false := by
  decide +kernel

theorem node_context_8_1382_1220784 : EJMOriginalGlobalDAGData.nodes 13 ⟨1220784, by decide⟩ =
    .split (coordinate 8) (![⟨1219591, by decide⟩,⟨1220200, by decide⟩,⟨1220618, by decide⟩,⟨1220783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1382_1220784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1382 ⟨1220784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1382
    ⟨1220784, by decide⟩ (by decide) (![⟨1219591, by decide⟩,⟨1220200, by decide⟩,⟨1220618, by decide⟩,⟨1220783, by decide⟩]) unmarked_context_8_1382_1220784 node_context_8_1382_1220784
  intro a
  fin_cases a
  · exact context_9_5528_1219591
  · exact context_9_5529_1220200
  · exact context_9_5530_1220618
  · exact context_9_5531_1220783

theorem selected_cut_44385 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88512) = some ⟨11, 1, 0, 434745, 88512, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88512_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88512 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88512 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88512, 1, 262144⟩
    (by decide) selected_cut_44385

theorem selected_cut_44386 : selected 10 ⟨1220833, by decide⟩
    (prefixPartial 11 88513) = some ⟨11, 2, 0, 1220833, 88513, 1505, 262144⟩ := by
  decide +kernel

theorem context_11_88513_1220833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88513 ⟨1220833, by decide⟩ :=
  accepted_of_selected 11 88513 ⟨1220833, by decide⟩ ⟨11, 2, 0, 1220833, 88513, 1505, 262144⟩
    (by decide) selected_cut_44386

theorem selected_cut_44387 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 354056) = some ⟨12, 1, 0, 448748, 354056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354056_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354056 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 354056 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 354056, 1, 65536⟩
    (by decide) selected_cut_44387

theorem selected_cut_44388 : selected 9 ⟨1220902, by decide⟩
    (prefixPartial 12 354057) = some ⟨12, 2, 0, 1220902, 354057, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_354057_1220902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354057 ⟨1220902, by decide⟩ :=
  accepted_of_selected 12 354057 ⟨1220902, by decide⟩ ⟨12, 2, 0, 1220902, 354057, 2761, 65536⟩
    (by decide) selected_cut_44388

theorem selected_cut_44389 : selected 9 ⟨1220959, by decide⟩
    (prefixPartial 12 354058) = some ⟨12, 2, 0, 1220959, 354058, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_354058_1220959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354058 ⟨1220959, by decide⟩ :=
  accepted_of_selected 12 354058 ⟨1220959, by decide⟩ ⟨12, 2, 0, 1220959, 354058, 2969, 65536⟩
    (by decide) selected_cut_44389

theorem selected_cut_44390 : selected 9 ⟨1221049, by decide⟩
    (prefixPartial 12 354059) = some ⟨12, 2, 0, 1221049, 354059, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_354059_1221049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354059 ⟨1221049, by decide⟩ :=
  accepted_of_selected 12 354059 ⟨1221049, by decide⟩ ⟨12, 2, 0, 1221049, 354059, 3481, 65536⟩
    (by decide) selected_cut_44390

theorem unmarked_context_11_88514_1221050 : frontier 10 ⟨1221050, by decide⟩
    (prefixCache 11 88514) (prefixPartial 11 88514) = false := by
  decide +kernel

theorem node_context_11_88514_1221050 : EJMOriginalGlobalDAGData.nodes 10 ⟨1221050, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1220902, by decide⟩,⟨1220959, by decide⟩,⟨1221049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88514_1221050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88514 ⟨1221050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88514
    ⟨1221050, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1220902, by decide⟩,⟨1220959, by decide⟩,⟨1221049, by decide⟩]) unmarked_context_11_88514_1221050 node_context_11_88514_1221050
  intro a
  fin_cases a
  · exact context_12_354056_448748
  · exact context_12_354057_1220902
  · exact context_12_354058_1220959
  · exact context_12_354059_1221049

theorem selected_cut_44391 : selected 10 ⟨1221112, by decide⟩
    (prefixPartial 11 88515) = some ⟨11, 2, 0, 1221112, 88515, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_88515_1221112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88515 ⟨1221112, by decide⟩ :=
  accepted_of_selected 11 88515 ⟨1221112, by decide⟩ ⟨11, 2, 0, 1221112, 88515, 2985, 262144⟩
    (by decide) selected_cut_44391

theorem unmarked_context_10_22128_1221113 : frontier 11 ⟨1221113, by decide⟩
    (prefixCache 10 22128) (prefixPartial 10 22128) = false := by
  decide +kernel

theorem node_context_10_22128_1221113 : EJMOriginalGlobalDAGData.nodes 11 ⟨1221113, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1220833, by decide⟩,⟨1221050, by decide⟩,⟨1221112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22128_1221113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22128 ⟨1221113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22128
    ⟨1221113, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1220833, by decide⟩,⟨1221050, by decide⟩,⟨1221112, by decide⟩]) unmarked_context_10_22128_1221113 node_context_10_22128_1221113
  intro a
  fin_cases a
  · exact context_11_88512_434745
  · exact context_11_88513_1220833
  · exact context_11_88514_1221050
  · exact context_11_88515_1221112

theorem selected_cut_44392 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 354064) = some ⟨12, 1, 0, 435160, 354064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354064_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354064 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 354064 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 354064, 1, 65536⟩
    (by decide) selected_cut_44392

theorem selected_cut_44393 : selected 9 ⟨1221158, by decide⟩
    (prefixPartial 12 354065) = some ⟨12, 2, 0, 1221158, 354065, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_354065_1221158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354065 ⟨1221158, by decide⟩ :=
  accepted_of_selected 12 354065 ⟨1221158, by decide⟩ ⟨12, 2, 0, 1221158, 354065, 2373, 65536⟩
    (by decide) selected_cut_44393

theorem selected_cut_44394 : selected 9 ⟨1221220, by decide⟩
    (prefixPartial 12 354066) = some ⟨12, 2, 0, 1221220, 354066, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_354066_1221220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354066 ⟨1221220, by decide⟩ :=
  accepted_of_selected 12 354066 ⟨1221220, by decide⟩ ⟨12, 2, 0, 1221220, 354066, 3085, 65536⟩
    (by decide) selected_cut_44394

theorem selected_cut_44395 : selected 9 ⟨1221275, by decide⟩
    (prefixPartial 12 354067) = some ⟨12, 2, 0, 1221275, 354067, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_354067_1221275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354067 ⟨1221275, by decide⟩ :=
  accepted_of_selected 12 354067 ⟨1221275, by decide⟩ ⟨12, 2, 0, 1221275, 354067, 3009, 65536⟩
    (by decide) selected_cut_44395

theorem unmarked_context_11_88516_1221276 : frontier 10 ⟨1221276, by decide⟩
    (prefixCache 11 88516) (prefixPartial 11 88516) = false := by
  decide +kernel

theorem node_context_11_88516_1221276 : EJMOriginalGlobalDAGData.nodes 10 ⟨1221276, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1221158, by decide⟩,⟨1221220, by decide⟩,⟨1221275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88516_1221276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88516 ⟨1221276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88516
    ⟨1221276, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1221158, by decide⟩,⟨1221220, by decide⟩,⟨1221275, by decide⟩]) unmarked_context_11_88516_1221276 node_context_11_88516_1221276
  intro a
  fin_cases a
  · exact context_12_354064_435160
  · exact context_12_354065_1221158
  · exact context_12_354066_1221220
  · exact context_12_354067_1221275

theorem selected_cut_44396 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 88517) = some ⟨11, 1, 0, 892405, 88517, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88517_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88517 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 88517 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 88517, 1, 262144⟩
    (by decide) selected_cut_44396

theorem selected_cut_44397 : selected 9 ⟨1221327, by decide⟩
    (prefixPartial 12 354072) = some ⟨12, 2, 0, 1221327, 354072, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_354072_1221327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354072 ⟨1221327, by decide⟩ :=
  accepted_of_selected 12 354072 ⟨1221327, by decide⟩ ⟨12, 2, 0, 1221327, 354072, 2757, 65536⟩
    (by decide) selected_cut_44397

theorem selected_cut_44398 : selected 9 ⟨1221364, by decide⟩
    (prefixPartial 12 354073) = some ⟨12, 2, 0, 1221364, 354073, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_354073_1221364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354073 ⟨1221364, by decide⟩ :=
  accepted_of_selected 12 354073 ⟨1221364, by decide⟩ ⟨12, 2, 0, 1221364, 354073, 2305, 65536⟩
    (by decide) selected_cut_44398

theorem selected_cut_44399 : selected 9 ⟨1221410, by decide⟩
    (prefixPartial 12 354074) = some ⟨12, 2, 0, 1221410, 354074, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_354074_1221410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354074 ⟨1221410, by decide⟩ :=
  accepted_of_selected 12 354074 ⟨1221410, by decide⟩ ⟨12, 2, 0, 1221410, 354074, 2753, 65536⟩
    (by decide) selected_cut_44399

theorem selected_cut_44400 : selected 9 ⟨1221460, by decide⟩
    (prefixPartial 12 354075) = some ⟨12, 2, 0, 1221460, 354075, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_354075_1221460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354075 ⟨1221460, by decide⟩ :=
  accepted_of_selected 12 354075 ⟨1221460, by decide⟩ ⟨12, 2, 0, 1221460, 354075, 2917, 65536⟩
    (by decide) selected_cut_44400

theorem unmarked_context_11_88518_1221461 : frontier 10 ⟨1221461, by decide⟩
    (prefixCache 11 88518) (prefixPartial 11 88518) = false := by
  decide +kernel

theorem node_context_11_88518_1221461 : EJMOriginalGlobalDAGData.nodes 10 ⟨1221461, by decide⟩ =
    .split (coordinate 11) (![⟨1221327, by decide⟩,⟨1221364, by decide⟩,⟨1221410, by decide⟩,⟨1221460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88518_1221461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88518 ⟨1221461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88518
    ⟨1221461, by decide⟩ (by decide) (![⟨1221327, by decide⟩,⟨1221364, by decide⟩,⟨1221410, by decide⟩,⟨1221460, by decide⟩]) unmarked_context_11_88518_1221461 node_context_11_88518_1221461
  intro a
  fin_cases a
  · exact context_12_354072_1221327
  · exact context_12_354073_1221364
  · exact context_12_354074_1221410
  · exact context_12_354075_1221460

theorem selected_cut_44401 : selected 9 ⟨1221502, by decide⟩
    (prefixPartial 12 354076) = some ⟨12, 2, 0, 1221502, 354076, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_354076_1221502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354076 ⟨1221502, by decide⟩ :=
  accepted_of_selected 12 354076 ⟨1221502, by decide⟩ ⟨12, 2, 0, 1221502, 354076, 2409, 65536⟩
    (by decide) selected_cut_44401

theorem selected_cut_44402 : selected 9 ⟨1221529, by decide⟩
    (prefixPartial 12 354077) = some ⟨12, 2, 0, 1221529, 354077, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_354077_1221529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354077 ⟨1221529, by decide⟩ :=
  accepted_of_selected 12 354077 ⟨1221529, by decide⟩ ⟨12, 2, 0, 1221529, 354077, 1985, 65536⟩
    (by decide) selected_cut_44402

theorem selected_cut_44403 : selected 9 ⟨1221581, by decide⟩
    (prefixPartial 12 354078) = some ⟨12, 2, 0, 1221581, 354078, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_354078_1221581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354078 ⟨1221581, by decide⟩ :=
  accepted_of_selected 12 354078 ⟨1221581, by decide⟩ ⟨12, 2, 0, 1221581, 354078, 2745, 65536⟩
    (by decide) selected_cut_44403

theorem selected_cut_44404 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 354079) = some ⟨12, 1, 0, 903806, 354079, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354079_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354079 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 354079 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 354079, 1, 65536⟩
    (by decide) selected_cut_44404

theorem unmarked_context_11_88519_1221582 : frontier 10 ⟨1221582, by decide⟩
    (prefixCache 11 88519) (prefixPartial 11 88519) = false := by
  decide +kernel

theorem node_context_11_88519_1221582 : EJMOriginalGlobalDAGData.nodes 10 ⟨1221582, by decide⟩ =
    .split (coordinate 11) (![⟨1221502, by decide⟩,⟨1221529, by decide⟩,⟨1221581, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88519_1221582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88519 ⟨1221582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88519
    ⟨1221582, by decide⟩ (by decide) (![⟨1221502, by decide⟩,⟨1221529, by decide⟩,⟨1221581, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_88519_1221582 node_context_11_88519_1221582
  intro a
  fin_cases a
  · exact context_12_354076_1221502
  · exact context_12_354077_1221529
  · exact context_12_354078_1221581
  · exact context_12_354079_903806

theorem unmarked_context_10_22129_1221583 : frontier 11 ⟨1221583, by decide⟩
    (prefixCache 10 22129) (prefixPartial 10 22129) = false := by
  decide +kernel

theorem node_context_10_22129_1221583 : EJMOriginalGlobalDAGData.nodes 11 ⟨1221583, by decide⟩ =
    .split (coordinate 10) (![⟨1221276, by decide⟩,⟨892405, by decide⟩,⟨1221461, by decide⟩,⟨1221582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22129_1221583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22129 ⟨1221583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22129
    ⟨1221583, by decide⟩ (by decide) (![⟨1221276, by decide⟩,⟨892405, by decide⟩,⟨1221461, by decide⟩,⟨1221582, by decide⟩]) unmarked_context_10_22129_1221583 node_context_10_22129_1221583
  intro a
  fin_cases a
  · exact context_11_88516_1221276
  · exact context_11_88517_892405
  · exact context_11_88518_1221461
  · exact context_11_88519_1221582

theorem selected_cut_44405 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 354080) = some ⟨12, 1, 0, 1187656, 354080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354080_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354080 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 354080 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 354080, 1, 65536⟩
    (by decide) selected_cut_44405

theorem selected_cut_44406 : selected 9 ⟨1221622, by decide⟩
    (prefixPartial 12 354081) = some ⟨12, 2, 0, 1221622, 354081, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_354081_1221622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354081 ⟨1221622, by decide⟩ :=
  accepted_of_selected 12 354081 ⟨1221622, by decide⟩ ⟨12, 2, 0, 1221622, 354081, 2277, 65536⟩
    (by decide) selected_cut_44406

theorem selected_cut_44407 : selected 9 ⟨1221668, by decide⟩
    (prefixPartial 12 354082) = some ⟨12, 2, 0, 1221668, 354082, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_354082_1221668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354082 ⟨1221668, by decide⟩ :=
  accepted_of_selected 12 354082 ⟨1221668, by decide⟩ ⟨12, 2, 0, 1221668, 354082, 2733, 65536⟩
    (by decide) selected_cut_44407

theorem selected_cut_44408 : selected 9 ⟨1221719, by decide⟩
    (prefixPartial 12 354083) = some ⟨12, 2, 0, 1221719, 354083, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_354083_1221719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354083 ⟨1221719, by decide⟩ :=
  accepted_of_selected 12 354083 ⟨1221719, by decide⟩ ⟨12, 2, 0, 1221719, 354083, 2861, 65536⟩
    (by decide) selected_cut_44408

theorem unmarked_context_11_88520_1221720 : frontier 10 ⟨1221720, by decide⟩
    (prefixCache 11 88520) (prefixPartial 11 88520) = false := by
  decide +kernel

theorem node_context_11_88520_1221720 : EJMOriginalGlobalDAGData.nodes 10 ⟨1221720, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1221622, by decide⟩,⟨1221668, by decide⟩,⟨1221719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88520_1221720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88520 ⟨1221720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88520
    ⟨1221720, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1221622, by decide⟩,⟨1221668, by decide⟩,⟨1221719, by decide⟩]) unmarked_context_11_88520_1221720 node_context_11_88520_1221720
  intro a
  fin_cases a
  · exact context_12_354080_1187656
  · exact context_12_354081_1221622
  · exact context_12_354082_1221668
  · exact context_12_354083_1221719

theorem selected_cut_44409 : selected 9 ⟨1221759, by decide⟩
    (prefixPartial 12 354084) = some ⟨12, 2, 0, 1221759, 354084, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_354084_1221759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354084 ⟨1221759, by decide⟩ :=
  accepted_of_selected 12 354084 ⟨1221759, by decide⟩ ⟨12, 2, 0, 1221759, 354084, 2133, 65536⟩
    (by decide) selected_cut_44409

theorem selected_cut_44410 : selected 9 ⟨1221788, by decide⟩
    (prefixPartial 12 354085) = some ⟨12, 2, 0, 1221788, 354085, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_354085_1221788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354085 ⟨1221788, by decide⟩ :=
  accepted_of_selected 12 354085 ⟨1221788, by decide⟩ ⟨12, 2, 0, 1221788, 354085, 1853, 65536⟩
    (by decide) selected_cut_44410

theorem selected_cut_44411 : selected 9 ⟨1221819, by decide⟩
    (prefixPartial 12 354086) = some ⟨12, 2, 0, 1221819, 354086, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_354086_1221819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354086 ⟨1221819, by decide⟩ :=
  accepted_of_selected 12 354086 ⟨1221819, by decide⟩ ⟨12, 2, 0, 1221819, 354086, 2025, 65536⟩
    (by decide) selected_cut_44411

theorem selected_cut_44412 : selected 9 ⟨1221856, by decide⟩
    (prefixPartial 12 354087) = some ⟨12, 2, 0, 1221856, 354087, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_354087_1221856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354087 ⟨1221856, by decide⟩ :=
  accepted_of_selected 12 354087 ⟨1221856, by decide⟩ ⟨12, 2, 0, 1221856, 354087, 2257, 65536⟩
    (by decide) selected_cut_44412

theorem unmarked_context_11_88521_1221857 : frontier 10 ⟨1221857, by decide⟩
    (prefixCache 11 88521) (prefixPartial 11 88521) = false := by
  decide +kernel

theorem node_context_11_88521_1221857 : EJMOriginalGlobalDAGData.nodes 10 ⟨1221857, by decide⟩ =
    .split (coordinate 11) (![⟨1221759, by decide⟩,⟨1221788, by decide⟩,⟨1221819, by decide⟩,⟨1221856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88521_1221857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88521 ⟨1221857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88521
    ⟨1221857, by decide⟩ (by decide) (![⟨1221759, by decide⟩,⟨1221788, by decide⟩,⟨1221819, by decide⟩,⟨1221856, by decide⟩]) unmarked_context_11_88521_1221857 node_context_11_88521_1221857
  intro a
  fin_cases a
  · exact context_12_354084_1221759
  · exact context_12_354085_1221788
  · exact context_12_354086_1221819
  · exact context_12_354087_1221856

theorem selected_cut_44413 : selected 9 ⟨1221902, by decide⟩
    (prefixPartial 12 354088) = some ⟨12, 2, 0, 1221902, 354088, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_354088_1221902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354088 ⟨1221902, by decide⟩ :=
  accepted_of_selected 12 354088 ⟨1221902, by decide⟩ ⟨12, 2, 0, 1221902, 354088, 2493, 65536⟩
    (by decide) selected_cut_44413

theorem selected_cut_44414 : selected 9 ⟨1221932, by decide⟩
    (prefixPartial 12 354089) = some ⟨12, 2, 0, 1221932, 354089, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_354089_1221932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354089 ⟨1221932, by decide⟩ :=
  accepted_of_selected 12 354089 ⟨1221932, by decide⟩ ⟨12, 2, 0, 1221932, 354089, 2081, 65536⟩
    (by decide) selected_cut_44414

theorem selected_cut_44415 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 354090) = some ⟨12, 1, 0, 1113261, 354090, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354090_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354090 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 354090 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 354090, 1, 65536⟩
    (by decide) selected_cut_44415

theorem selected_cut_44416 : selected 9 ⟨1221969, by decide⟩
    (prefixPartial 12 354091) = some ⟨12, 2, 0, 1221969, 354091, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_354091_1221969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354091 ⟨1221969, by decide⟩ :=
  accepted_of_selected 12 354091 ⟨1221969, by decide⟩ ⟨12, 2, 0, 1221969, 354091, 2541, 65536⟩
    (by decide) selected_cut_44416

theorem unmarked_context_11_88522_1221970 : frontier 10 ⟨1221970, by decide⟩
    (prefixCache 11 88522) (prefixPartial 11 88522) = false := by
  decide +kernel

theorem node_context_11_88522_1221970 : EJMOriginalGlobalDAGData.nodes 10 ⟨1221970, by decide⟩ =
    .split (coordinate 11) (![⟨1221902, by decide⟩,⟨1221932, by decide⟩,⟨1113261, by decide⟩,⟨1221969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88522_1221970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88522 ⟨1221970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88522
    ⟨1221970, by decide⟩ (by decide) (![⟨1221902, by decide⟩,⟨1221932, by decide⟩,⟨1113261, by decide⟩,⟨1221969, by decide⟩]) unmarked_context_11_88522_1221970 node_context_11_88522_1221970
  intro a
  fin_cases a
  · exact context_12_354088_1221902
  · exact context_12_354089_1221932
  · exact context_12_354090_1113261
  · exact context_12_354091_1221969

theorem selected_cut_44417 : selected 9 ⟨1222013, by decide⟩
    (prefixPartial 12 354092) = some ⟨12, 2, 0, 1222013, 354092, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_354092_1222013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354092 ⟨1222013, by decide⟩ :=
  accepted_of_selected 12 354092 ⟨1222013, by decide⟩ ⟨12, 2, 0, 1222013, 354092, 2361, 65536⟩
    (by decide) selected_cut_44417

theorem selected_cut_44418 : selected 9 ⟨1222039, by decide⟩
    (prefixPartial 12 354093) = some ⟨12, 2, 0, 1222039, 354093, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_354093_1222039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354093 ⟨1222039, by decide⟩ :=
  accepted_of_selected 12 354093 ⟨1222039, by decide⟩ ⟨12, 2, 0, 1222039, 354093, 1877, 65536⟩
    (by decide) selected_cut_44418

theorem selected_cut_44419 : selected 9 ⟨1222080, by decide⟩
    (prefixPartial 12 354094) = some ⟨12, 2, 0, 1222080, 354094, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_354094_1222080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354094 ⟨1222080, by decide⟩ :=
  accepted_of_selected 12 354094 ⟨1222080, by decide⟩ ⟨12, 2, 0, 1222080, 354094, 2377, 65536⟩
    (by decide) selected_cut_44419

theorem selected_cut_44420 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 354095) = some ⟨12, 1, 0, 903806, 354095, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354095_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354095 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 354095 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 354095, 1, 65536⟩
    (by decide) selected_cut_44420

theorem unmarked_context_11_88523_1222081 : frontier 10 ⟨1222081, by decide⟩
    (prefixCache 11 88523) (prefixPartial 11 88523) = false := by
  decide +kernel

theorem node_context_11_88523_1222081 : EJMOriginalGlobalDAGData.nodes 10 ⟨1222081, by decide⟩ =
    .split (coordinate 11) (![⟨1222013, by decide⟩,⟨1222039, by decide⟩,⟨1222080, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88523_1222081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88523 ⟨1222081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88523
    ⟨1222081, by decide⟩ (by decide) (![⟨1222013, by decide⟩,⟨1222039, by decide⟩,⟨1222080, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_88523_1222081 node_context_11_88523_1222081
  intro a
  fin_cases a
  · exact context_12_354092_1222013
  · exact context_12_354093_1222039
  · exact context_12_354094_1222080
  · exact context_12_354095_903806

theorem unmarked_context_10_22130_1222082 : frontier 11 ⟨1222082, by decide⟩
    (prefixCache 10 22130) (prefixPartial 10 22130) = false := by
  decide +kernel

theorem node_context_10_22130_1222082 : EJMOriginalGlobalDAGData.nodes 11 ⟨1222082, by decide⟩ =
    .split (coordinate 10) (![⟨1221720, by decide⟩,⟨1221857, by decide⟩,⟨1221970, by decide⟩,⟨1222081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22130_1222082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22130 ⟨1222082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22130
    ⟨1222082, by decide⟩ (by decide) (![⟨1221720, by decide⟩,⟨1221857, by decide⟩,⟨1221970, by decide⟩,⟨1222081, by decide⟩]) unmarked_context_10_22130_1222082 node_context_10_22130_1222082
  intro a
  fin_cases a
  · exact context_11_88520_1221720
  · exact context_11_88521_1221857
  · exact context_11_88522_1221970
  · exact context_11_88523_1222081

theorem selected_cut_44421 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 354096) = some ⟨12, 1, 0, 1187656, 354096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354096_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354096 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 354096 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 354096, 1, 65536⟩
    (by decide) selected_cut_44421

theorem selected_cut_44422 : selected 9 ⟨1222119, by decide⟩
    (prefixPartial 12 354097) = some ⟨12, 2, 0, 1222119, 354097, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_354097_1222119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354097 ⟨1222119, by decide⟩ :=
  accepted_of_selected 12 354097 ⟨1222119, by decide⟩ ⟨12, 2, 0, 1222119, 354097, 2181, 65536⟩
    (by decide) selected_cut_44422

theorem selected_cut_44423 : selected 9 ⟨1222169, by decide⟩
    (prefixPartial 12 354098) = some ⟨12, 2, 0, 1222169, 354098, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_354098_1222169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354098 ⟨1222169, by decide⟩ :=
  accepted_of_selected 12 354098 ⟨1222169, by decide⟩ ⟨12, 2, 0, 1222169, 354098, 2617, 65536⟩
    (by decide) selected_cut_44423

theorem selected_cut_44424 : selected 9 ⟨1222214, by decide⟩
    (prefixPartial 12 354099) = some ⟨12, 2, 0, 1222214, 354099, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_354099_1222214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354099 ⟨1222214, by decide⟩ :=
  accepted_of_selected 12 354099 ⟨1222214, by decide⟩ ⟨12, 2, 0, 1222214, 354099, 2533, 65536⟩
    (by decide) selected_cut_44424

theorem unmarked_context_11_88524_1222215 : frontier 10 ⟨1222215, by decide⟩
    (prefixCache 11 88524) (prefixPartial 11 88524) = false := by
  decide +kernel

theorem node_context_11_88524_1222215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1222215, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1222119, by decide⟩,⟨1222169, by decide⟩,⟨1222214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88524_1222215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88524 ⟨1222215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88524
    ⟨1222215, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1222119, by decide⟩,⟨1222169, by decide⟩,⟨1222214, by decide⟩]) unmarked_context_11_88524_1222215 node_context_11_88524_1222215
  intro a
  fin_cases a
  · exact context_12_354096_1187656
  · exact context_12_354097_1222119
  · exact context_12_354098_1222169
  · exact context_12_354099_1222214

theorem selected_cut_44425 : selected 9 ⟨1222254, by decide⟩
    (prefixPartial 12 354100) = some ⟨12, 2, 0, 1222254, 354100, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_354100_1222254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354100 ⟨1222254, by decide⟩ :=
  accepted_of_selected 12 354100 ⟨1222254, by decide⟩ ⟨12, 2, 0, 1222254, 354100, 2145, 65536⟩
    (by decide) selected_cut_44425

theorem selected_cut_44426 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 354101) = some ⟨12, 1, 0, 689956, 354101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354101_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354101 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 354101 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 354101, 1, 65536⟩
    (by decide) selected_cut_44426

theorem selected_cut_44427 : selected 9 ⟨1222285, by decide⟩
    (prefixPartial 12 354102) = some ⟨12, 2, 0, 1222285, 354102, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_354102_1222285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354102 ⟨1222285, by decide⟩ :=
  accepted_of_selected 12 354102 ⟨1222285, by decide⟩ ⟨12, 2, 0, 1222285, 354102, 2009, 65536⟩
    (by decide) selected_cut_44427

theorem selected_cut_44428 : selected 9 ⟨1222315, by decide⟩
    (prefixPartial 12 354103) = some ⟨12, 2, 0, 1222315, 354103, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_354103_1222315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354103 ⟨1222315, by decide⟩ :=
  accepted_of_selected 12 354103 ⟨1222315, by decide⟩ ⟨12, 2, 0, 1222315, 354103, 2041, 65536⟩
    (by decide) selected_cut_44428

theorem unmarked_context_11_88525_1222316 : frontier 10 ⟨1222316, by decide⟩
    (prefixCache 11 88525) (prefixPartial 11 88525) = false := by
  decide +kernel

theorem node_context_11_88525_1222316 : EJMOriginalGlobalDAGData.nodes 10 ⟨1222316, by decide⟩ =
    .split (coordinate 11) (![⟨1222254, by decide⟩,⟨689956, by decide⟩,⟨1222285, by decide⟩,⟨1222315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88525_1222316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88525 ⟨1222316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88525
    ⟨1222316, by decide⟩ (by decide) (![⟨1222254, by decide⟩,⟨689956, by decide⟩,⟨1222285, by decide⟩,⟨1222315, by decide⟩]) unmarked_context_11_88525_1222316 node_context_11_88525_1222316
  intro a
  fin_cases a
  · exact context_12_354100_1222254
  · exact context_12_354101_689956
  · exact context_12_354102_1222285
  · exact context_12_354103_1222315

theorem selected_cut_44429 : selected 9 ⟨1222370, by decide⟩
    (prefixPartial 12 354104) = some ⟨12, 2, 0, 1222370, 354104, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_354104_1222370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354104 ⟨1222370, by decide⟩ :=
  accepted_of_selected 12 354104 ⟨1222370, by decide⟩ ⟨12, 2, 0, 1222370, 354104, 2597, 65536⟩
    (by decide) selected_cut_44429

theorem selected_cut_44430 : selected 9 ⟨1222413, by decide⟩
    (prefixPartial 12 354105) = some ⟨12, 2, 0, 1222413, 354105, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_354105_1222413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354105 ⟨1222413, by decide⟩ :=
  accepted_of_selected 12 354105 ⟨1222413, by decide⟩ ⟨12, 2, 0, 1222413, 354105, 2189, 65536⟩
    (by decide) selected_cut_44430

theorem selected_cut_44431 : selected 9 ⟨1222452, by decide⟩
    (prefixPartial 12 354106) = some ⟨12, 2, 0, 1222452, 354106, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_354106_1222452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354106 ⟨1222452, by decide⟩ :=
  accepted_of_selected 12 354106 ⟨1222452, by decide⟩ ⟨12, 2, 0, 1222452, 354106, 2333, 65536⟩
    (by decide) selected_cut_44431

theorem selected_cut_44432 : selected 9 ⟨1222494, by decide⟩
    (prefixPartial 12 354107) = some ⟨12, 2, 0, 1222494, 354107, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_354107_1222494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354107 ⟨1222494, by decide⟩ :=
  accepted_of_selected 12 354107 ⟨1222494, by decide⟩ ⟨12, 2, 0, 1222494, 354107, 2369, 65536⟩
    (by decide) selected_cut_44432

theorem unmarked_context_11_88526_1222495 : frontier 10 ⟨1222495, by decide⟩
    (prefixCache 11 88526) (prefixPartial 11 88526) = false := by
  decide +kernel

theorem node_context_11_88526_1222495 : EJMOriginalGlobalDAGData.nodes 10 ⟨1222495, by decide⟩ =
    .split (coordinate 11) (![⟨1222370, by decide⟩,⟨1222413, by decide⟩,⟨1222452, by decide⟩,⟨1222494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88526_1222495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88526 ⟨1222495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88526
    ⟨1222495, by decide⟩ (by decide) (![⟨1222370, by decide⟩,⟨1222413, by decide⟩,⟨1222452, by decide⟩,⟨1222494, by decide⟩]) unmarked_context_11_88526_1222495 node_context_11_88526_1222495
  intro a
  fin_cases a
  · exact context_12_354104_1222370
  · exact context_12_354105_1222413
  · exact context_12_354106_1222452
  · exact context_12_354107_1222494

theorem selected_cut_44433 : selected 9 ⟨1222534, by decide⟩
    (prefixPartial 12 354108) = some ⟨12, 2, 0, 1222534, 354108, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_354108_1222534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354108 ⟨1222534, by decide⟩ :=
  accepted_of_selected 12 354108 ⟨1222534, by decide⟩ ⟨12, 2, 0, 1222534, 354108, 2153, 65536⟩
    (by decide) selected_cut_44433

theorem selected_cut_44434 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 354109) = some ⟨12, 1, 0, 762108, 354109, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354109_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354109 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 354109 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 354109, 1, 65536⟩
    (by decide) selected_cut_44434

theorem selected_cut_44435 : selected 9 ⟨1222568, by decide⟩
    (prefixPartial 12 354110) = some ⟨12, 2, 0, 1222568, 354110, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_354110_1222568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354110 ⟨1222568, by decide⟩ :=
  accepted_of_selected 12 354110 ⟨1222568, by decide⟩ ⟨12, 2, 0, 1222568, 354110, 2157, 65536⟩
    (by decide) selected_cut_44435

theorem selected_cut_44436 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 354111) = some ⟨12, 1, 0, 1116246, 354111, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354111_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354111 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 354111 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 354111, 1, 65536⟩
    (by decide) selected_cut_44436

theorem unmarked_context_11_88527_1222569 : frontier 10 ⟨1222569, by decide⟩
    (prefixCache 11 88527) (prefixPartial 11 88527) = false := by
  decide +kernel

theorem node_context_11_88527_1222569 : EJMOriginalGlobalDAGData.nodes 10 ⟨1222569, by decide⟩ =
    .split (coordinate 11) (![⟨1222534, by decide⟩,⟨762108, by decide⟩,⟨1222568, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88527_1222569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88527 ⟨1222569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88527
    ⟨1222569, by decide⟩ (by decide) (![⟨1222534, by decide⟩,⟨762108, by decide⟩,⟨1222568, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_88527_1222569 node_context_11_88527_1222569
  intro a
  fin_cases a
  · exact context_12_354108_1222534
  · exact context_12_354109_762108
  · exact context_12_354110_1222568
  · exact context_12_354111_1116246

theorem unmarked_context_10_22131_1222570 : frontier 11 ⟨1222570, by decide⟩
    (prefixCache 10 22131) (prefixPartial 10 22131) = false := by
  decide +kernel

theorem node_context_10_22131_1222570 : EJMOriginalGlobalDAGData.nodes 11 ⟨1222570, by decide⟩ =
    .split (coordinate 10) (![⟨1222215, by decide⟩,⟨1222316, by decide⟩,⟨1222495, by decide⟩,⟨1222569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22131_1222570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22131 ⟨1222570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22131
    ⟨1222570, by decide⟩ (by decide) (![⟨1222215, by decide⟩,⟨1222316, by decide⟩,⟨1222495, by decide⟩,⟨1222569, by decide⟩]) unmarked_context_10_22131_1222570 node_context_10_22131_1222570
  intro a
  fin_cases a
  · exact context_11_88524_1222215
  · exact context_11_88525_1222316
  · exact context_11_88526_1222495
  · exact context_11_88527_1222569

theorem unmarked_context_9_5532_1222571 : frontier 12 ⟨1222571, by decide⟩
    (prefixCache 9 5532) (prefixPartial 9 5532) = false := by
  decide +kernel

theorem node_context_9_5532_1222571 : EJMOriginalGlobalDAGData.nodes 12 ⟨1222571, by decide⟩ =
    .split (coordinate 9) (![⟨1221113, by decide⟩,⟨1221583, by decide⟩,⟨1222082, by decide⟩,⟨1222570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5532_1222571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5532 ⟨1222571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5532
    ⟨1222571, by decide⟩ (by decide) (![⟨1221113, by decide⟩,⟨1221583, by decide⟩,⟨1222082, by decide⟩,⟨1222570, by decide⟩]) unmarked_context_9_5532_1222571 node_context_9_5532_1222571
  intro a
  fin_cases a
  · exact context_10_22128_1221113
  · exact context_10_22129_1221583
  · exact context_10_22130_1222082
  · exact context_10_22131_1222570

theorem selected_cut_44437 : selected 10 ⟨1222651, by decide⟩
    (prefixPartial 11 88528) = some ⟨11, 2, 0, 1222651, 88528, 3745, 262144⟩ := by
  decide +kernel

theorem context_11_88528_1222651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88528 ⟨1222651, by decide⟩ :=
  accepted_of_selected 11 88528 ⟨1222651, by decide⟩ ⟨11, 2, 0, 1222651, 88528, 3745, 262144⟩
    (by decide) selected_cut_44437

theorem selected_cut_44438 : selected 10 ⟨1222730, by decide⟩
    (prefixPartial 11 88529) = some ⟨11, 2, 0, 1222730, 88529, 4041, 262144⟩ := by
  decide +kernel

theorem context_11_88529_1222730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88529 ⟨1222730, by decide⟩ :=
  accepted_of_selected 11 88529 ⟨1222730, by decide⟩ ⟨11, 2, 0, 1222730, 88529, 4041, 262144⟩
    (by decide) selected_cut_44438

theorem selected_cut_44439 : selected 9 ⟨1222764, by decide⟩
    (prefixPartial 12 354120) = some ⟨12, 2, 0, 1222764, 354120, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_354120_1222764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354120 ⟨1222764, by decide⟩ :=
  accepted_of_selected 12 354120 ⟨1222764, by decide⟩ ⟨12, 2, 0, 1222764, 354120, 1777, 65536⟩
    (by decide) selected_cut_44439

theorem selected_cut_44440 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354121) = some ⟨12, 1, 0, 896706, 354121, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354121_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354121 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354121 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354121, 1, 65536⟩
    (by decide) selected_cut_44440

theorem selected_cut_44441 : selected 9 ⟨1222796, by decide⟩
    (prefixPartial 12 354122) = some ⟨12, 2, 0, 1222796, 354122, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_354122_1222796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354122 ⟨1222796, by decide⟩ :=
  accepted_of_selected 12 354122 ⟨1222796, by decide⟩ ⟨12, 2, 0, 1222796, 354122, 1761, 65536⟩
    (by decide) selected_cut_44441

theorem selected_cut_44442 : selected 9 ⟨1222831, by decide⟩
    (prefixPartial 12 354123) = some ⟨12, 2, 0, 1222831, 354123, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_354123_1222831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354123 ⟨1222831, by decide⟩ :=
  accepted_of_selected 12 354123 ⟨1222831, by decide⟩ ⟨12, 2, 0, 1222831, 354123, 1757, 65536⟩
    (by decide) selected_cut_44442

theorem unmarked_context_11_88530_1222832 : frontier 10 ⟨1222832, by decide⟩
    (prefixCache 11 88530) (prefixPartial 11 88530) = false := by
  decide +kernel

theorem node_context_11_88530_1222832 : EJMOriginalGlobalDAGData.nodes 10 ⟨1222832, by decide⟩ =
    .split (coordinate 11) (![⟨1222764, by decide⟩,⟨896706, by decide⟩,⟨1222796, by decide⟩,⟨1222831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88530_1222832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88530 ⟨1222832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88530
    ⟨1222832, by decide⟩ (by decide) (![⟨1222764, by decide⟩,⟨896706, by decide⟩,⟨1222796, by decide⟩,⟨1222831, by decide⟩]) unmarked_context_11_88530_1222832 node_context_11_88530_1222832
  intro a
  fin_cases a
  · exact context_12_354120_1222764
  · exact context_12_354121_896706
  · exact context_12_354122_1222796
  · exact context_12_354123_1222831

theorem selected_cut_44443 : selected 10 ⟨1222883, by decide⟩
    (prefixPartial 11 88531) = some ⟨11, 2, 0, 1222883, 88531, 2941, 262144⟩ := by
  decide +kernel

theorem context_11_88531_1222883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88531 ⟨1222883, by decide⟩ :=
  accepted_of_selected 11 88531 ⟨1222883, by decide⟩ ⟨11, 2, 0, 1222883, 88531, 2941, 262144⟩
    (by decide) selected_cut_44443

theorem unmarked_context_10_22132_1222884 : frontier 11 ⟨1222884, by decide⟩
    (prefixCache 10 22132) (prefixPartial 10 22132) = false := by
  decide +kernel

theorem node_context_10_22132_1222884 : EJMOriginalGlobalDAGData.nodes 11 ⟨1222884, by decide⟩ =
    .split (coordinate 10) (![⟨1222651, by decide⟩,⟨1222730, by decide⟩,⟨1222832, by decide⟩,⟨1222883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22132_1222884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22132 ⟨1222884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22132
    ⟨1222884, by decide⟩ (by decide) (![⟨1222651, by decide⟩,⟨1222730, by decide⟩,⟨1222832, by decide⟩,⟨1222883, by decide⟩]) unmarked_context_10_22132_1222884 node_context_10_22132_1222884
  intro a
  fin_cases a
  · exact context_11_88528_1222651
  · exact context_11_88529_1222730
  · exact context_11_88530_1222832
  · exact context_11_88531_1222883

theorem selected_cut_44444 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22133) = some ⟨10, 1, 0, 893098, 22133, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22133_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22133 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22133 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22133, 1, 1048576⟩
    (by decide) selected_cut_44444

theorem selected_cut_44445 : selected 9 ⟨1222908, by decide⟩
    (prefixPartial 12 354144) = some ⟨12, 2, 0, 1222908, 354144, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_354144_1222908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354144 ⟨1222908, by decide⟩ :=
  accepted_of_selected 12 354144 ⟨1222908, by decide⟩ ⟨12, 2, 0, 1222908, 354144, 1345, 65536⟩
    (by decide) selected_cut_44445

theorem selected_cut_44446 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 354145) = some ⟨12, 1, 0, 896706, 354145, 1, 65536⟩ := by
  decide +kernel

theorem context_12_354145_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354145 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 354145 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 354145, 1, 65536⟩
    (by decide) selected_cut_44446

theorem selected_cut_44447 : selected 9 ⟨1222929, by decide⟩
    (prefixPartial 12 354146) = some ⟨12, 2, 0, 1222929, 354146, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_354146_1222929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354146 ⟨1222929, by decide⟩ :=
  accepted_of_selected 12 354146 ⟨1222929, by decide⟩ ⟨12, 2, 0, 1222929, 354146, 1377, 65536⟩
    (by decide) selected_cut_44447

theorem selected_cut_44448 : selected 9 ⟨1222951, by decide⟩
    (prefixPartial 12 354147) = some ⟨12, 2, 0, 1222951, 354147, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_354147_1222951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 354147 ⟨1222951, by decide⟩ :=
  accepted_of_selected 12 354147 ⟨1222951, by decide⟩ ⟨12, 2, 0, 1222951, 354147, 1373, 65536⟩
    (by decide) selected_cut_44448

theorem unmarked_context_11_88536_1222952 : frontier 10 ⟨1222952, by decide⟩
    (prefixCache 11 88536) (prefixPartial 11 88536) = false := by
  decide +kernel

theorem node_context_11_88536_1222952 : EJMOriginalGlobalDAGData.nodes 10 ⟨1222952, by decide⟩ =
    .split (coordinate 11) (![⟨1222908, by decide⟩,⟨896706, by decide⟩,⟨1222929, by decide⟩,⟨1222951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88536_1222952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88536 ⟨1222952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88536
    ⟨1222952, by decide⟩ (by decide) (![⟨1222908, by decide⟩,⟨896706, by decide⟩,⟨1222929, by decide⟩,⟨1222951, by decide⟩]) unmarked_context_11_88536_1222952 node_context_11_88536_1222952
  intro a
  fin_cases a
  · exact context_12_354144_1222908
  · exact context_12_354145_896706
  · exact context_12_354146_1222929
  · exact context_12_354147_1222951

theorem selected_cut_44449 : selected 10 ⟨1222999, by decide⟩
    (prefixPartial 11 88537) = some ⟨11, 2, 0, 1222999, 88537, 2945, 262144⟩ := by
  decide +kernel

theorem context_11_88537_1222999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88537 ⟨1222999, by decide⟩ :=
  accepted_of_selected 11 88537 ⟨1222999, by decide⟩ ⟨11, 2, 0, 1222999, 88537, 2945, 262144⟩
    (by decide) selected_cut_44449

theorem selected_cut_44450 : selected 10 ⟨1223038, by decide⟩
    (prefixPartial 11 88538) = some ⟨11, 2, 0, 1223038, 88538, 2529, 262144⟩ := by
  decide +kernel

theorem context_11_88538_1223038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88538 ⟨1223038, by decide⟩ :=
  accepted_of_selected 11 88538 ⟨1223038, by decide⟩ ⟨11, 2, 0, 1223038, 88538, 2529, 262144⟩
    (by decide) selected_cut_44450

theorem selected_cut_44451 : selected 10 ⟨1223079, by decide⟩
    (prefixPartial 11 88539) = some ⟨11, 2, 0, 1223079, 88539, 2409, 262144⟩ := by
  decide +kernel

theorem context_11_88539_1223079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88539 ⟨1223079, by decide⟩ :=
  accepted_of_selected 11 88539 ⟨1223079, by decide⟩ ⟨11, 2, 0, 1223079, 88539, 2409, 262144⟩
    (by decide) selected_cut_44451

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
