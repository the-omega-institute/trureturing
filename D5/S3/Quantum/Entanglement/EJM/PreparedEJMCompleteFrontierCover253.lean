/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover252
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_24292 : selected 8 ⟨614429, by decide⟩
    (prefixPartial 13 308350) = some ⟨13, 2, 0, 614429, 308350, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_308350_614429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308350 ⟨614429, by decide⟩ :=
  accepted_of_selected 13 308350 ⟨614429, by decide⟩ ⟨13, 2, 0, 614429, 308350, 1769, 16384⟩
    (by decide) selected_cut_24292

theorem selected_cut_24293 : selected 8 ⟨614435, by decide⟩
    (prefixPartial 13 308351) = some ⟨13, 2, 0, 614435, 308351, 921, 16384⟩ := by
  decide +kernel

theorem context_13_308351_614435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308351 ⟨614435, by decide⟩ :=
  accepted_of_selected 13 308351 ⟨614435, by decide⟩ ⟨13, 2, 0, 614435, 308351, 921, 16384⟩
    (by decide) selected_cut_24293

theorem unmarked_context_12_77087_614436 : frontier 9 ⟨614436, by decide⟩
    (prefixCache 12 77087) (prefixPartial 12 77087) = false := by
  decide +kernel

theorem node_context_12_77087_614436 : EJMOriginalGlobalDAGData.nodes 9 ⟨614436, by decide⟩ =
    .split (coordinate 12) (![⟨614377, by decide⟩,⟨614405, by decide⟩,⟨614429, by decide⟩,⟨614435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77087_614436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77087 ⟨614436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77087
    ⟨614436, by decide⟩ (by decide) (![⟨614377, by decide⟩,⟨614405, by decide⟩,⟨614429, by decide⟩,⟨614435, by decide⟩]) unmarked_context_12_77087_614436 node_context_12_77087_614436
  intro a
  fin_cases a
  · exact context_13_308348_614377
  · exact context_13_308349_614405
  · exact context_13_308350_614429
  · exact context_13_308351_614435

theorem unmarked_context_11_19271_614437 : frontier 10 ⟨614437, by decide⟩
    (prefixCache 11 19271) (prefixPartial 11 19271) = false := by
  decide +kernel

theorem node_context_11_19271_614437 : EJMOriginalGlobalDAGData.nodes 10 ⟨614437, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨614274, by decide⟩,⟨614355, by decide⟩,⟨614436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19271_614437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19271 ⟨614437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19271
    ⟨614437, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨614274, by decide⟩,⟨614355, by decide⟩,⟨614436, by decide⟩]) unmarked_context_11_19271_614437 node_context_11_19271_614437
  intro a
  fin_cases a
  · exact context_12_77084_539296
  · exact context_12_77085_614274
  · exact context_12_77086_614355
  · exact context_12_77087_614436

theorem unmarked_context_10_4817_614438 : frontier 11 ⟨614438, by decide⟩
    (prefixCache 10 4817) (prefixPartial 10 4817) = false := by
  decide +kernel

theorem node_context_10_4817_614438 : EJMOriginalGlobalDAGData.nodes 11 ⟨614438, by decide⟩ =
    .split (coordinate 10) (![⟨613671, by decide⟩,⟨613857, by decide⟩,⟨614186, by decide⟩,⟨614437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4817_614438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4817 ⟨614438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4817
    ⟨614438, by decide⟩ (by decide) (![⟨613671, by decide⟩,⟨613857, by decide⟩,⟨614186, by decide⟩,⟨614437, by decide⟩]) unmarked_context_10_4817_614438 node_context_10_4817_614438
  intro a
  fin_cases a
  · exact context_11_19268_613671
  · exact context_11_19269_613857
  · exact context_11_19270_614186
  · exact context_11_19271_614437

theorem selected_cut_24294 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 77088) = some ⟨12, 1, 0, 435790, 77088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77088_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77088 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 77088 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 77088, 1, 65536⟩
    (by decide) selected_cut_24294

theorem selected_cut_24295 : selected 8 ⟨614461, by decide⟩
    (prefixPartial 13 308356) = some ⟨13, 2, 0, 614461, 308356, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_308356_614461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308356 ⟨614461, by decide⟩ :=
  accepted_of_selected 13 308356 ⟨614461, by decide⟩ ⟨13, 2, 0, 614461, 308356, 1269, 16384⟩
    (by decide) selected_cut_24295

theorem selected_cut_24296 : selected 8 ⟨614496, by decide⟩
    (prefixPartial 13 308357) = some ⟨13, 2, 0, 614496, 308357, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_308357_614496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308357 ⟨614496, by decide⟩ :=
  accepted_of_selected 13 308357 ⟨614496, by decide⟩ ⟨13, 2, 0, 614496, 308357, 1801, 16384⟩
    (by decide) selected_cut_24296

theorem selected_cut_24297 : selected 8 ⟨614518, by decide⟩
    (prefixPartial 13 308358) = some ⟨13, 2, 0, 614518, 308358, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_308358_614518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308358 ⟨614518, by decide⟩ :=
  accepted_of_selected 13 308358 ⟨614518, by decide⟩ ⟨13, 2, 0, 614518, 308358, 1653, 16384⟩
    (by decide) selected_cut_24297

theorem selected_cut_24298 : selected 8 ⟨614528, by decide⟩
    (prefixPartial 13 308359) = some ⟨13, 2, 0, 614528, 308359, 893, 16384⟩ := by
  decide +kernel

theorem context_13_308359_614528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308359 ⟨614528, by decide⟩ :=
  accepted_of_selected 13 308359 ⟨614528, by decide⟩ ⟨13, 2, 0, 614528, 308359, 893, 16384⟩
    (by decide) selected_cut_24298

theorem unmarked_context_12_77089_614529 : frontier 9 ⟨614529, by decide⟩
    (prefixCache 12 77089) (prefixPartial 12 77089) = false := by
  decide +kernel

theorem node_context_12_77089_614529 : EJMOriginalGlobalDAGData.nodes 9 ⟨614529, by decide⟩ =
    .split (coordinate 12) (![⟨614461, by decide⟩,⟨614496, by decide⟩,⟨614518, by decide⟩,⟨614528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77089_614529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77089 ⟨614529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77089
    ⟨614529, by decide⟩ (by decide) (![⟨614461, by decide⟩,⟨614496, by decide⟩,⟨614518, by decide⟩,⟨614528, by decide⟩]) unmarked_context_12_77089_614529 node_context_12_77089_614529
  intro a
  fin_cases a
  · exact context_13_308356_614461
  · exact context_13_308357_614496
  · exact context_13_308358_614518
  · exact context_13_308359_614528

theorem selected_cut_24299 : selected 8 ⟨614556, by decide⟩
    (prefixPartial 13 308360) = some ⟨13, 2, 0, 614556, 308360, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_308360_614556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308360 ⟨614556, by decide⟩ :=
  accepted_of_selected 13 308360 ⟨614556, by decide⟩ ⟨13, 2, 0, 614556, 308360, 1233, 16384⟩
    (by decide) selected_cut_24299

theorem selected_cut_24300 : selected 8 ⟨614589, by decide⟩
    (prefixPartial 13 308361) = some ⟨13, 2, 0, 614589, 308361, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_308361_614589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308361 ⟨614589, by decide⟩ :=
  accepted_of_selected 13 308361 ⟨614589, by decide⟩ ⟨13, 2, 0, 614589, 308361, 1761, 16384⟩
    (by decide) selected_cut_24300

theorem selected_cut_24301 : selected 8 ⟨614606, by decide⟩
    (prefixPartial 13 308362) = some ⟨13, 2, 0, 614606, 308362, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_308362_614606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308362 ⟨614606, by decide⟩ :=
  accepted_of_selected 13 308362 ⟨614606, by decide⟩ ⟨13, 2, 0, 614606, 308362, 1457, 16384⟩
    (by decide) selected_cut_24301

theorem selected_cut_24302 : selected 8 ⟨614617, by decide⟩
    (prefixPartial 13 308363) = some ⟨13, 2, 0, 614617, 308363, 965, 16384⟩ := by
  decide +kernel

theorem context_13_308363_614617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308363 ⟨614617, by decide⟩ :=
  accepted_of_selected 13 308363 ⟨614617, by decide⟩ ⟨13, 2, 0, 614617, 308363, 965, 16384⟩
    (by decide) selected_cut_24302

theorem unmarked_context_12_77090_614618 : frontier 9 ⟨614618, by decide⟩
    (prefixCache 12 77090) (prefixPartial 12 77090) = false := by
  decide +kernel

theorem node_context_12_77090_614618 : EJMOriginalGlobalDAGData.nodes 9 ⟨614618, by decide⟩ =
    .split (coordinate 12) (![⟨614556, by decide⟩,⟨614589, by decide⟩,⟨614606, by decide⟩,⟨614617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77090_614618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77090 ⟨614618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77090
    ⟨614618, by decide⟩ (by decide) (![⟨614556, by decide⟩,⟨614589, by decide⟩,⟨614606, by decide⟩,⟨614617, by decide⟩]) unmarked_context_12_77090_614618 node_context_12_77090_614618
  intro a
  fin_cases a
  · exact context_13_308360_614556
  · exact context_13_308361_614589
  · exact context_13_308362_614606
  · exact context_13_308363_614617

theorem selected_cut_24303 : selected 8 ⟨614647, by decide⟩
    (prefixPartial 13 308364) = some ⟨13, 2, 0, 614647, 308364, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_308364_614647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308364 ⟨614647, by decide⟩ :=
  accepted_of_selected 13 308364 ⟨614647, by decide⟩ ⟨13, 2, 0, 614647, 308364, 1325, 16384⟩
    (by decide) selected_cut_24303

theorem selected_cut_24304 : selected 8 ⟨614679, by decide⟩
    (prefixPartial 13 308365) = some ⟨13, 2, 0, 614679, 308365, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_308365_614679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308365 ⟨614679, by decide⟩ :=
  accepted_of_selected 13 308365 ⟨614679, by decide⟩ ⟨13, 2, 0, 614679, 308365, 2013, 16384⟩
    (by decide) selected_cut_24304

theorem selected_cut_24305 : selected 8 ⟨614703, by decide⟩
    (prefixPartial 13 308366) = some ⟨13, 2, 0, 614703, 308366, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_308366_614703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308366 ⟨614703, by decide⟩ :=
  accepted_of_selected 13 308366 ⟨614703, by decide⟩ ⟨13, 2, 0, 614703, 308366, 1797, 16384⟩
    (by decide) selected_cut_24305

theorem selected_cut_24306 : selected 8 ⟨614714, by decide⟩
    (prefixPartial 13 308367) = some ⟨13, 2, 0, 614714, 308367, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_308367_614714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308367 ⟨614714, by decide⟩ :=
  accepted_of_selected 13 308367 ⟨614714, by decide⟩ ⟨13, 2, 0, 614714, 308367, 1021, 16384⟩
    (by decide) selected_cut_24306

theorem unmarked_context_12_77091_614715 : frontier 9 ⟨614715, by decide⟩
    (prefixCache 12 77091) (prefixPartial 12 77091) = false := by
  decide +kernel

theorem node_context_12_77091_614715 : EJMOriginalGlobalDAGData.nodes 9 ⟨614715, by decide⟩ =
    .split (coordinate 12) (![⟨614647, by decide⟩,⟨614679, by decide⟩,⟨614703, by decide⟩,⟨614714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77091_614715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77091 ⟨614715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77091
    ⟨614715, by decide⟩ (by decide) (![⟨614647, by decide⟩,⟨614679, by decide⟩,⟨614703, by decide⟩,⟨614714, by decide⟩]) unmarked_context_12_77091_614715 node_context_12_77091_614715
  intro a
  fin_cases a
  · exact context_13_308364_614647
  · exact context_13_308365_614679
  · exact context_13_308366_614703
  · exact context_13_308367_614714

theorem unmarked_context_11_19272_614716 : frontier 10 ⟨614716, by decide⟩
    (prefixCache 11 19272) (prefixPartial 11 19272) = false := by
  decide +kernel

theorem node_context_11_19272_614716 : EJMOriginalGlobalDAGData.nodes 10 ⟨614716, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨614529, by decide⟩,⟨614618, by decide⟩,⟨614715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19272_614716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19272 ⟨614716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19272
    ⟨614716, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨614529, by decide⟩,⟨614618, by decide⟩,⟨614715, by decide⟩]) unmarked_context_11_19272_614716 node_context_11_19272_614716
  intro a
  fin_cases a
  · exact context_12_77088_435790
  · exact context_12_77089_614529
  · exact context_12_77090_614618
  · exact context_12_77091_614715

theorem selected_cut_24307 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 77092) = some ⟨12, 1, 0, 450498, 77092, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77092_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77092 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 77092 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 77092, 1, 65536⟩
    (by decide) selected_cut_24307

theorem selected_cut_24308 : selected 8 ⟨614749, by decide⟩
    (prefixPartial 13 308372) = some ⟨13, 2, 0, 614749, 308372, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_308372_614749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308372 ⟨614749, by decide⟩ :=
  accepted_of_selected 13 308372 ⟨614749, by decide⟩ ⟨13, 2, 0, 614749, 308372, 1693, 16384⟩
    (by decide) selected_cut_24308

theorem selected_cut_24309 : selected 8 ⟨614793, by decide⟩
    (prefixPartial 13 308373) = some ⟨13, 2, 0, 614793, 308373, 3105, 16384⟩ := by
  decide +kernel

theorem context_13_308373_614793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308373 ⟨614793, by decide⟩ :=
  accepted_of_selected 13 308373 ⟨614793, by decide⟩ ⟨13, 2, 0, 614793, 308373, 3105, 16384⟩
    (by decide) selected_cut_24309

theorem selected_cut_24310 : selected 8 ⟨614840, by decide⟩
    (prefixPartial 13 308374) = some ⟨13, 2, 0, 614840, 308374, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_308374_614840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308374 ⟨614840, by decide⟩ :=
  accepted_of_selected 13 308374 ⟨614840, by decide⟩ ⟨13, 2, 0, 614840, 308374, 2465, 16384⟩
    (by decide) selected_cut_24310

theorem selected_cut_24311 : selected 8 ⟨614867, by decide⟩
    (prefixPartial 13 308375) = some ⟨13, 2, 0, 614867, 308375, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_308375_614867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308375 ⟨614867, by decide⟩ :=
  accepted_of_selected 13 308375 ⟨614867, by decide⟩ ⟨13, 2, 0, 614867, 308375, 1201, 16384⟩
    (by decide) selected_cut_24311

theorem unmarked_context_12_77093_614868 : frontier 9 ⟨614868, by decide⟩
    (prefixCache 12 77093) (prefixPartial 12 77093) = false := by
  decide +kernel

theorem node_context_12_77093_614868 : EJMOriginalGlobalDAGData.nodes 9 ⟨614868, by decide⟩ =
    .split (coordinate 12) (![⟨614749, by decide⟩,⟨614793, by decide⟩,⟨614840, by decide⟩,⟨614867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77093_614868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77093 ⟨614868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77093
    ⟨614868, by decide⟩ (by decide) (![⟨614749, by decide⟩,⟨614793, by decide⟩,⟨614840, by decide⟩,⟨614867, by decide⟩]) unmarked_context_12_77093_614868 node_context_12_77093_614868
  intro a
  fin_cases a
  · exact context_13_308372_614749
  · exact context_13_308373_614793
  · exact context_13_308374_614840
  · exact context_13_308375_614867

theorem selected_cut_24312 : selected 8 ⟨614893, by decide⟩
    (prefixPartial 13 308376) = some ⟨13, 2, 0, 614893, 308376, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_308376_614893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308376 ⟨614893, by decide⟩ :=
  accepted_of_selected 13 308376 ⟨614893, by decide⟩ ⟨13, 2, 0, 614893, 308376, 1005, 16384⟩
    (by decide) selected_cut_24312

theorem selected_cut_24313 : selected 8 ⟨614928, by decide⟩
    (prefixPartial 13 308377) = some ⟨13, 2, 0, 614928, 308377, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_308377_614928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308377 ⟨614928, by decide⟩ :=
  accepted_of_selected 13 308377 ⟨614928, by decide⟩ ⟨13, 2, 0, 614928, 308377, 1849, 16384⟩
    (by decide) selected_cut_24313

theorem selected_cut_24314 : selected 8 ⟨614951, by decide⟩
    (prefixPartial 13 308378) = some ⟨13, 2, 0, 614951, 308378, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_308378_614951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308378 ⟨614951, by decide⟩ :=
  accepted_of_selected 13 308378 ⟨614951, by decide⟩ ⟨13, 2, 0, 614951, 308378, 1317, 16384⟩
    (by decide) selected_cut_24314

theorem selected_cut_24315 : selected 8 ⟨614960, by decide⟩
    (prefixPartial 13 308379) = some ⟨13, 2, 0, 614960, 308379, 989, 16384⟩ := by
  decide +kernel

theorem context_13_308379_614960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308379 ⟨614960, by decide⟩ :=
  accepted_of_selected 13 308379 ⟨614960, by decide⟩ ⟨13, 2, 0, 614960, 308379, 989, 16384⟩
    (by decide) selected_cut_24315

theorem unmarked_context_12_77094_614961 : frontier 9 ⟨614961, by decide⟩
    (prefixCache 12 77094) (prefixPartial 12 77094) = false := by
  decide +kernel

theorem node_context_12_77094_614961 : EJMOriginalGlobalDAGData.nodes 9 ⟨614961, by decide⟩ =
    .split (coordinate 12) (![⟨614893, by decide⟩,⟨614928, by decide⟩,⟨614951, by decide⟩,⟨614960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77094_614961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77094 ⟨614961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77094
    ⟨614961, by decide⟩ (by decide) (![⟨614893, by decide⟩,⟨614928, by decide⟩,⟨614951, by decide⟩,⟨614960, by decide⟩]) unmarked_context_12_77094_614961 node_context_12_77094_614961
  intro a
  fin_cases a
  · exact context_13_308376_614893
  · exact context_13_308377_614928
  · exact context_13_308378_614951
  · exact context_13_308379_614960

theorem selected_cut_24316 : selected 8 ⟨614983, by decide⟩
    (prefixPartial 13 308380) = some ⟨13, 2, 0, 614983, 308380, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_308380_614983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308380 ⟨614983, by decide⟩ :=
  accepted_of_selected 13 308380 ⟨614983, by decide⟩ ⟨13, 2, 0, 614983, 308380, 1065, 16384⟩
    (by decide) selected_cut_24316

theorem selected_cut_24317 : selected 8 ⟨615014, by decide⟩
    (prefixPartial 13 308381) = some ⟨13, 2, 0, 615014, 308381, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_308381_615014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308381 ⟨615014, by decide⟩ :=
  accepted_of_selected 13 308381 ⟨615014, by decide⟩ ⟨13, 2, 0, 615014, 308381, 2029, 16384⟩
    (by decide) selected_cut_24317

theorem selected_cut_24318 : selected 8 ⟨615041, by decide⟩
    (prefixPartial 13 308382) = some ⟨13, 2, 0, 615041, 308382, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_308382_615041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308382 ⟨615041, by decide⟩ :=
  accepted_of_selected 13 308382 ⟨615041, by decide⟩ ⟨13, 2, 0, 615041, 308382, 1813, 16384⟩
    (by decide) selected_cut_24318

theorem selected_cut_24319 : selected 8 ⟨615051, by decide⟩
    (prefixPartial 13 308383) = some ⟨13, 2, 0, 615051, 308383, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_308383_615051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308383 ⟨615051, by decide⟩ :=
  accepted_of_selected 13 308383 ⟨615051, by decide⟩ ⟨13, 2, 0, 615051, 308383, 1001, 16384⟩
    (by decide) selected_cut_24319

theorem unmarked_context_12_77095_615052 : frontier 9 ⟨615052, by decide⟩
    (prefixCache 12 77095) (prefixPartial 12 77095) = false := by
  decide +kernel

theorem node_context_12_77095_615052 : EJMOriginalGlobalDAGData.nodes 9 ⟨615052, by decide⟩ =
    .split (coordinate 12) (![⟨614983, by decide⟩,⟨615014, by decide⟩,⟨615041, by decide⟩,⟨615051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77095_615052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77095 ⟨615052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77095
    ⟨615052, by decide⟩ (by decide) (![⟨614983, by decide⟩,⟨615014, by decide⟩,⟨615041, by decide⟩,⟨615051, by decide⟩]) unmarked_context_12_77095_615052 node_context_12_77095_615052
  intro a
  fin_cases a
  · exact context_13_308380_614983
  · exact context_13_308381_615014
  · exact context_13_308382_615041
  · exact context_13_308383_615051

theorem unmarked_context_11_19273_615053 : frontier 10 ⟨615053, by decide⟩
    (prefixCache 11 19273) (prefixPartial 11 19273) = false := by
  decide +kernel

theorem node_context_11_19273_615053 : EJMOriginalGlobalDAGData.nodes 10 ⟨615053, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨614868, by decide⟩,⟨614961, by decide⟩,⟨615052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19273_615053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19273 ⟨615053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19273
    ⟨615053, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨614868, by decide⟩,⟨614961, by decide⟩,⟨615052, by decide⟩]) unmarked_context_11_19273_615053 node_context_11_19273_615053
  intro a
  fin_cases a
  · exact context_12_77092_450498
  · exact context_12_77093_614868
  · exact context_12_77094_614961
  · exact context_12_77095_615052

theorem selected_cut_24320 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 77096) = some ⟨12, 1, 0, 435790, 77096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77096_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77096 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 77096 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 77096, 1, 65536⟩
    (by decide) selected_cut_24320

theorem selected_cut_24321 : selected 8 ⟨615077, by decide⟩
    (prefixPartial 13 308388) = some ⟨13, 2, 0, 615077, 308388, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_308388_615077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308388 ⟨615077, by decide⟩ :=
  accepted_of_selected 13 308388 ⟨615077, by decide⟩ ⟨13, 2, 0, 615077, 308388, 1005, 16384⟩
    (by decide) selected_cut_24321

theorem selected_cut_24322 : selected 8 ⟨615104, by decide⟩
    (prefixPartial 13 308389) = some ⟨13, 2, 0, 615104, 308389, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_308389_615104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308389 ⟨615104, by decide⟩ :=
  accepted_of_selected 13 308389 ⟨615104, by decide⟩ ⟨13, 2, 0, 615104, 308389, 1913, 16384⟩
    (by decide) selected_cut_24322

theorem selected_cut_24323 : selected 8 ⟨615124, by decide⟩
    (prefixPartial 13 308390) = some ⟨13, 2, 0, 615124, 308390, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_308390_615124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308390 ⟨615124, by decide⟩ :=
  accepted_of_selected 13 308390 ⟨615124, by decide⟩ ⟨13, 2, 0, 615124, 308390, 2025, 16384⟩
    (by decide) selected_cut_24323

theorem selected_cut_24324 : selected 8 ⟨615133, by decide⟩
    (prefixPartial 13 308391) = some ⟨13, 2, 0, 615133, 308391, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_308391_615133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308391 ⟨615133, by decide⟩ :=
  accepted_of_selected 13 308391 ⟨615133, by decide⟩ ⟨13, 2, 0, 615133, 308391, 1041, 16384⟩
    (by decide) selected_cut_24324

theorem unmarked_context_12_77097_615134 : frontier 9 ⟨615134, by decide⟩
    (prefixCache 12 77097) (prefixPartial 12 77097) = false := by
  decide +kernel

theorem node_context_12_77097_615134 : EJMOriginalGlobalDAGData.nodes 9 ⟨615134, by decide⟩ =
    .split (coordinate 12) (![⟨615077, by decide⟩,⟨615104, by decide⟩,⟨615124, by decide⟩,⟨615133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77097_615134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77097 ⟨615134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77097
    ⟨615134, by decide⟩ (by decide) (![⟨615077, by decide⟩,⟨615104, by decide⟩,⟨615124, by decide⟩,⟨615133, by decide⟩]) unmarked_context_12_77097_615134 node_context_12_77097_615134
  intro a
  fin_cases a
  · exact context_13_308388_615077
  · exact context_13_308389_615104
  · exact context_13_308390_615124
  · exact context_13_308391_615133

theorem selected_cut_24325 : selected 8 ⟨615157, by decide⟩
    (prefixPartial 13 308392) = some ⟨13, 2, 0, 615157, 308392, 901, 16384⟩ := by
  decide +kernel

theorem context_13_308392_615157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308392 ⟨615157, by decide⟩ :=
  accepted_of_selected 13 308392 ⟨615157, by decide⟩ ⟨13, 2, 0, 615157, 308392, 901, 16384⟩
    (by decide) selected_cut_24325

theorem selected_cut_24326 : selected 8 ⟨615190, by decide⟩
    (prefixPartial 13 308393) = some ⟨13, 2, 0, 615190, 308393, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_308393_615190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308393 ⟨615190, by decide⟩ :=
  accepted_of_selected 13 308393 ⟨615190, by decide⟩ ⟨13, 2, 0, 615190, 308393, 1941, 16384⟩
    (by decide) selected_cut_24326

theorem selected_cut_24327 : selected 8 ⟨615214, by decide⟩
    (prefixPartial 13 308394) = some ⟨13, 2, 0, 615214, 308394, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_308394_615214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308394 ⟨615214, by decide⟩ :=
  accepted_of_selected 13 308394 ⟨615214, by decide⟩ ⟨13, 2, 0, 615214, 308394, 1653, 16384⟩
    (by decide) selected_cut_24327

theorem selected_cut_24328 : selected 8 ⟨615225, by decide⟩
    (prefixPartial 13 308395) = some ⟨13, 2, 0, 615225, 308395, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_308395_615225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308395 ⟨615225, by decide⟩ :=
  accepted_of_selected 13 308395 ⟨615225, by decide⟩ ⟨13, 2, 0, 615225, 308395, 1033, 16384⟩
    (by decide) selected_cut_24328

theorem unmarked_context_12_77098_615226 : frontier 9 ⟨615226, by decide⟩
    (prefixCache 12 77098) (prefixPartial 12 77098) = false := by
  decide +kernel

theorem node_context_12_77098_615226 : EJMOriginalGlobalDAGData.nodes 9 ⟨615226, by decide⟩ =
    .split (coordinate 12) (![⟨615157, by decide⟩,⟨615190, by decide⟩,⟨615214, by decide⟩,⟨615225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77098_615226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77098 ⟨615226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77098
    ⟨615226, by decide⟩ (by decide) (![⟨615157, by decide⟩,⟨615190, by decide⟩,⟨615214, by decide⟩,⟨615225, by decide⟩]) unmarked_context_12_77098_615226 node_context_12_77098_615226
  intro a
  fin_cases a
  · exact context_13_308392_615157
  · exact context_13_308393_615190
  · exact context_13_308394_615214
  · exact context_13_308395_615225

theorem selected_cut_24329 : selected 8 ⟨615245, by decide⟩
    (prefixPartial 13 308396) = some ⟨13, 2, 0, 615245, 308396, 933, 16384⟩ := by
  decide +kernel

theorem context_13_308396_615245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308396 ⟨615245, by decide⟩ :=
  accepted_of_selected 13 308396 ⟨615245, by decide⟩ ⟨13, 2, 0, 615245, 308396, 933, 16384⟩
    (by decide) selected_cut_24329

theorem selected_cut_24330 : selected 8 ⟨615274, by decide⟩
    (prefixPartial 13 308397) = some ⟨13, 2, 0, 615274, 308397, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_308397_615274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308397 ⟨615274, by decide⟩ :=
  accepted_of_selected 13 308397 ⟨615274, by decide⟩ ⟨13, 2, 0, 615274, 308397, 2253, 16384⟩
    (by decide) selected_cut_24330

theorem selected_cut_24331 : selected 8 ⟨615315, by decide⟩
    (prefixPartial 13 308398) = some ⟨13, 2, 0, 615315, 308398, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_308398_615315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308398 ⟨615315, by decide⟩ :=
  accepted_of_selected 13 308398 ⟨615315, by decide⟩ ⟨13, 2, 0, 615315, 308398, 2185, 16384⟩
    (by decide) selected_cut_24331

theorem selected_cut_24332 : selected 8 ⟨615329, by decide⟩
    (prefixPartial 13 308399) = some ⟨13, 2, 0, 615329, 308399, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_308399_615329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308399 ⟨615329, by decide⟩ :=
  accepted_of_selected 13 308399 ⟨615329, by decide⟩ ⟨13, 2, 0, 615329, 308399, 1069, 16384⟩
    (by decide) selected_cut_24332

theorem unmarked_context_12_77099_615330 : frontier 9 ⟨615330, by decide⟩
    (prefixCache 12 77099) (prefixPartial 12 77099) = false := by
  decide +kernel

theorem node_context_12_77099_615330 : EJMOriginalGlobalDAGData.nodes 9 ⟨615330, by decide⟩ =
    .split (coordinate 12) (![⟨615245, by decide⟩,⟨615274, by decide⟩,⟨615315, by decide⟩,⟨615329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77099_615330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77099 ⟨615330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77099
    ⟨615330, by decide⟩ (by decide) (![⟨615245, by decide⟩,⟨615274, by decide⟩,⟨615315, by decide⟩,⟨615329, by decide⟩]) unmarked_context_12_77099_615330 node_context_12_77099_615330
  intro a
  fin_cases a
  · exact context_13_308396_615245
  · exact context_13_308397_615274
  · exact context_13_308398_615315
  · exact context_13_308399_615329

theorem unmarked_context_11_19274_615331 : frontier 10 ⟨615331, by decide⟩
    (prefixCache 11 19274) (prefixPartial 11 19274) = false := by
  decide +kernel

theorem node_context_11_19274_615331 : EJMOriginalGlobalDAGData.nodes 10 ⟨615331, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨615134, by decide⟩,⟨615226, by decide⟩,⟨615330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19274_615331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19274 ⟨615331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19274
    ⟨615331, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨615134, by decide⟩,⟨615226, by decide⟩,⟨615330, by decide⟩]) unmarked_context_11_19274_615331 node_context_11_19274_615331
  intro a
  fin_cases a
  · exact context_12_77096_435790
  · exact context_12_77097_615134
  · exact context_12_77098_615226
  · exact context_12_77099_615330

theorem selected_cut_24333 : selected 8 ⟨615355, by decide⟩
    (prefixPartial 13 308400) = some ⟨13, 2, 0, 615355, 308400, 973, 16384⟩ := by
  decide +kernel

theorem context_13_308400_615355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308400 ⟨615355, by decide⟩ :=
  accepted_of_selected 13 308400 ⟨615355, by decide⟩ ⟨13, 2, 0, 615355, 308400, 973, 16384⟩
    (by decide) selected_cut_24333

theorem selected_cut_24334 : selected 8 ⟨615388, by decide⟩
    (prefixPartial 13 308401) = some ⟨13, 2, 0, 615388, 308401, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_308401_615388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308401 ⟨615388, by decide⟩ :=
  accepted_of_selected 13 308401 ⟨615388, by decide⟩ ⟨13, 2, 0, 615388, 308401, 2757, 16384⟩
    (by decide) selected_cut_24334

theorem selected_cut_24335 : selected 8 ⟨615425, by decide⟩
    (prefixPartial 13 308402) = some ⟨13, 2, 0, 615425, 308402, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_308402_615425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308402 ⟨615425, by decide⟩ :=
  accepted_of_selected 13 308402 ⟨615425, by decide⟩ ⟨13, 2, 0, 615425, 308402, 2177, 16384⟩
    (by decide) selected_cut_24335

theorem selected_cut_24336 : selected 8 ⟨615434, by decide⟩
    (prefixPartial 13 308403) = some ⟨13, 2, 0, 615434, 308403, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_308403_615434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308403 ⟨615434, by decide⟩ :=
  accepted_of_selected 13 308403 ⟨615434, by decide⟩ ⟨13, 2, 0, 615434, 308403, 1069, 16384⟩
    (by decide) selected_cut_24336

theorem unmarked_context_12_77100_615435 : frontier 9 ⟨615435, by decide⟩
    (prefixCache 12 77100) (prefixPartial 12 77100) = false := by
  decide +kernel

theorem node_context_12_77100_615435 : EJMOriginalGlobalDAGData.nodes 9 ⟨615435, by decide⟩ =
    .split (coordinate 12) (![⟨615355, by decide⟩,⟨615388, by decide⟩,⟨615425, by decide⟩,⟨615434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77100_615435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77100 ⟨615435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77100
    ⟨615435, by decide⟩ (by decide) (![⟨615355, by decide⟩,⟨615388, by decide⟩,⟨615425, by decide⟩,⟨615434, by decide⟩]) unmarked_context_12_77100_615435 node_context_12_77100_615435
  intro a
  fin_cases a
  · exact context_13_308400_615355
  · exact context_13_308401_615388
  · exact context_13_308402_615425
  · exact context_13_308403_615434

theorem selected_cut_24337 : selected 8 ⟨615448, by decide⟩
    (prefixPartial 13 308404) = some ⟨13, 2, 0, 615448, 308404, 657, 16384⟩ := by
  decide +kernel

theorem context_13_308404_615448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308404 ⟨615448, by decide⟩ :=
  accepted_of_selected 13 308404 ⟨615448, by decide⟩ ⟨13, 2, 0, 615448, 308404, 657, 16384⟩
    (by decide) selected_cut_24337

theorem selected_cut_24338 : selected 8 ⟨615472, by decide⟩
    (prefixPartial 13 308405) = some ⟨13, 2, 0, 615472, 308405, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_308405_615472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308405 ⟨615472, by decide⟩ :=
  accepted_of_selected 13 308405 ⟨615472, by decide⟩ ⟨13, 2, 0, 615472, 308405, 1833, 16384⟩
    (by decide) selected_cut_24338

theorem selected_cut_24339 : selected 8 ⟨615494, by decide⟩
    (prefixPartial 13 308406) = some ⟨13, 2, 0, 615494, 308406, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_308406_615494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308406 ⟨615494, by decide⟩ :=
  accepted_of_selected 13 308406 ⟨615494, by decide⟩ ⟨13, 2, 0, 615494, 308406, 1717, 16384⟩
    (by decide) selected_cut_24339

theorem selected_cut_24340 : selected 8 ⟨615506, by decide⟩
    (prefixPartial 13 308407) = some ⟨13, 2, 0, 615506, 308407, 885, 16384⟩ := by
  decide +kernel

theorem context_13_308407_615506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308407 ⟨615506, by decide⟩ :=
  accepted_of_selected 13 308407 ⟨615506, by decide⟩ ⟨13, 2, 0, 615506, 308407, 885, 16384⟩
    (by decide) selected_cut_24340

theorem unmarked_context_12_77101_615507 : frontier 9 ⟨615507, by decide⟩
    (prefixCache 12 77101) (prefixPartial 12 77101) = false := by
  decide +kernel

theorem node_context_12_77101_615507 : EJMOriginalGlobalDAGData.nodes 9 ⟨615507, by decide⟩ =
    .split (coordinate 12) (![⟨615448, by decide⟩,⟨615472, by decide⟩,⟨615494, by decide⟩,⟨615506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77101_615507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77101 ⟨615507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77101
    ⟨615507, by decide⟩ (by decide) (![⟨615448, by decide⟩,⟨615472, by decide⟩,⟨615494, by decide⟩,⟨615506, by decide⟩]) unmarked_context_12_77101_615507 node_context_12_77101_615507
  intro a
  fin_cases a
  · exact context_13_308404_615448
  · exact context_13_308405_615472
  · exact context_13_308406_615494
  · exact context_13_308407_615506

theorem selected_cut_24341 : selected 8 ⟨615523, by decide⟩
    (prefixPartial 13 308408) = some ⟨13, 2, 0, 615523, 308408, 653, 16384⟩ := by
  decide +kernel

theorem context_13_308408_615523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308408 ⟨615523, by decide⟩ :=
  accepted_of_selected 13 308408 ⟨615523, by decide⟩ ⟨13, 2, 0, 615523, 308408, 653, 16384⟩
    (by decide) selected_cut_24341

theorem selected_cut_24342 : selected 8 ⟨615548, by decide⟩
    (prefixPartial 13 308409) = some ⟨13, 2, 0, 615548, 308409, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_308409_615548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308409 ⟨615548, by decide⟩ :=
  accepted_of_selected 13 308409 ⟨615548, by decide⟩ ⟨13, 2, 0, 615548, 308409, 1869, 16384⟩
    (by decide) selected_cut_24342

theorem selected_cut_24343 : selected 8 ⟨615569, by decide⟩
    (prefixPartial 13 308410) = some ⟨13, 2, 0, 615569, 308410, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_308410_615569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308410 ⟨615569, by decide⟩ :=
  accepted_of_selected 13 308410 ⟨615569, by decide⟩ ⟨13, 2, 0, 615569, 308410, 1449, 16384⟩
    (by decide) selected_cut_24343

theorem selected_cut_24344 : selected 8 ⟨615577, by decide⟩
    (prefixPartial 13 308411) = some ⟨13, 2, 0, 615577, 308411, 993, 16384⟩ := by
  decide +kernel

theorem context_13_308411_615577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308411 ⟨615577, by decide⟩ :=
  accepted_of_selected 13 308411 ⟨615577, by decide⟩ ⟨13, 2, 0, 615577, 308411, 993, 16384⟩
    (by decide) selected_cut_24344

theorem unmarked_context_12_77102_615578 : frontier 9 ⟨615578, by decide⟩
    (prefixCache 12 77102) (prefixPartial 12 77102) = false := by
  decide +kernel

theorem node_context_12_77102_615578 : EJMOriginalGlobalDAGData.nodes 9 ⟨615578, by decide⟩ =
    .split (coordinate 12) (![⟨615523, by decide⟩,⟨615548, by decide⟩,⟨615569, by decide⟩,⟨615577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77102_615578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77102 ⟨615578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77102
    ⟨615578, by decide⟩ (by decide) (![⟨615523, by decide⟩,⟨615548, by decide⟩,⟨615569, by decide⟩,⟨615577, by decide⟩]) unmarked_context_12_77102_615578 node_context_12_77102_615578
  intro a
  fin_cases a
  · exact context_13_308408_615523
  · exact context_13_308409_615548
  · exact context_13_308410_615569
  · exact context_13_308411_615577

theorem selected_cut_24345 : selected 8 ⟨615594, by decide⟩
    (prefixPartial 13 308412) = some ⟨13, 2, 0, 615594, 308412, 649, 16384⟩ := by
  decide +kernel

theorem context_13_308412_615594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308412 ⟨615594, by decide⟩ :=
  accepted_of_selected 13 308412 ⟨615594, by decide⟩ ⟨13, 2, 0, 615594, 308412, 649, 16384⟩
    (by decide) selected_cut_24345

theorem selected_cut_24346 : selected 8 ⟨615618, by decide⟩
    (prefixPartial 13 308413) = some ⟨13, 2, 0, 615618, 308413, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_308413_615618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308413 ⟨615618, by decide⟩ :=
  accepted_of_selected 13 308413 ⟨615618, by decide⟩ ⟨13, 2, 0, 615618, 308413, 2093, 16384⟩
    (by decide) selected_cut_24346

theorem selected_cut_24347 : selected 8 ⟨615645, by decide⟩
    (prefixPartial 13 308414) = some ⟨13, 2, 0, 615645, 308414, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_308414_615645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308414 ⟨615645, by decide⟩ :=
  accepted_of_selected 13 308414 ⟨615645, by decide⟩ ⟨13, 2, 0, 615645, 308414, 1881, 16384⟩
    (by decide) selected_cut_24347

theorem selected_cut_24348 : selected 8 ⟨615653, by decide⟩
    (prefixPartial 13 308415) = some ⟨13, 2, 0, 615653, 308415, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_308415_615653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308415 ⟨615653, by decide⟩ :=
  accepted_of_selected 13 308415 ⟨615653, by decide⟩ ⟨13, 2, 0, 615653, 308415, 1017, 16384⟩
    (by decide) selected_cut_24348

theorem unmarked_context_12_77103_615654 : frontier 9 ⟨615654, by decide⟩
    (prefixCache 12 77103) (prefixPartial 12 77103) = false := by
  decide +kernel

theorem node_context_12_77103_615654 : EJMOriginalGlobalDAGData.nodes 9 ⟨615654, by decide⟩ =
    .split (coordinate 12) (![⟨615594, by decide⟩,⟨615618, by decide⟩,⟨615645, by decide⟩,⟨615653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77103_615654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77103 ⟨615654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77103
    ⟨615654, by decide⟩ (by decide) (![⟨615594, by decide⟩,⟨615618, by decide⟩,⟨615645, by decide⟩,⟨615653, by decide⟩]) unmarked_context_12_77103_615654 node_context_12_77103_615654
  intro a
  fin_cases a
  · exact context_13_308412_615594
  · exact context_13_308413_615618
  · exact context_13_308414_615645
  · exact context_13_308415_615653

theorem unmarked_context_11_19275_615655 : frontier 10 ⟨615655, by decide⟩
    (prefixCache 11 19275) (prefixPartial 11 19275) = false := by
  decide +kernel

theorem node_context_11_19275_615655 : EJMOriginalGlobalDAGData.nodes 10 ⟨615655, by decide⟩ =
    .split (coordinate 11) (![⟨615435, by decide⟩,⟨615507, by decide⟩,⟨615578, by decide⟩,⟨615654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19275_615655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19275 ⟨615655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19275
    ⟨615655, by decide⟩ (by decide) (![⟨615435, by decide⟩,⟨615507, by decide⟩,⟨615578, by decide⟩,⟨615654, by decide⟩]) unmarked_context_11_19275_615655 node_context_11_19275_615655
  intro a
  fin_cases a
  · exact context_12_77100_615435
  · exact context_12_77101_615507
  · exact context_12_77102_615578
  · exact context_12_77103_615654

theorem unmarked_context_10_4818_615656 : frontier 11 ⟨615656, by decide⟩
    (prefixCache 10 4818) (prefixPartial 10 4818) = false := by
  decide +kernel

theorem node_context_10_4818_615656 : EJMOriginalGlobalDAGData.nodes 11 ⟨615656, by decide⟩ =
    .split (coordinate 10) (![⟨614716, by decide⟩,⟨615053, by decide⟩,⟨615331, by decide⟩,⟨615655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4818_615656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4818 ⟨615656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4818
    ⟨615656, by decide⟩ (by decide) (![⟨614716, by decide⟩,⟨615053, by decide⟩,⟨615331, by decide⟩,⟨615655, by decide⟩]) unmarked_context_10_4818_615656 node_context_10_4818_615656
  intro a
  fin_cases a
  · exact context_11_19272_614716
  · exact context_11_19273_615053
  · exact context_11_19274_615331
  · exact context_11_19275_615655

theorem selected_cut_24349 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 77104) = some ⟨12, 1, 0, 445562, 77104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77104_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77104 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 77104 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 77104, 1, 65536⟩
    (by decide) selected_cut_24349

theorem selected_cut_24350 : selected 8 ⟨615670, by decide⟩
    (prefixPartial 13 308420) = some ⟨13, 2, 0, 615670, 308420, 557, 16384⟩ := by
  decide +kernel

theorem context_13_308420_615670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308420 ⟨615670, by decide⟩ :=
  accepted_of_selected 13 308420 ⟨615670, by decide⟩ ⟨13, 2, 0, 615670, 308420, 557, 16384⟩
    (by decide) selected_cut_24350

theorem selected_cut_24351 : selected 8 ⟨615699, by decide⟩
    (prefixPartial 13 308421) = some ⟨13, 2, 0, 615699, 308421, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_308421_615699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308421 ⟨615699, by decide⟩ :=
  accepted_of_selected 13 308421 ⟨615699, by decide⟩ ⟨13, 2, 0, 615699, 308421, 2173, 16384⟩
    (by decide) selected_cut_24351

theorem selected_cut_24352 : selected 8 ⟨615719, by decide⟩
    (prefixPartial 13 308422) = some ⟨13, 2, 0, 615719, 308422, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_308422_615719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308422 ⟨615719, by decide⟩ :=
  accepted_of_selected 13 308422 ⟨615719, by decide⟩ ⟨13, 2, 0, 615719, 308422, 1689, 16384⟩
    (by decide) selected_cut_24352

theorem selected_cut_24353 : selected 8 ⟨615727, by decide⟩
    (prefixPartial 13 308423) = some ⟨13, 2, 0, 615727, 308423, 849, 16384⟩ := by
  decide +kernel

theorem context_13_308423_615727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308423 ⟨615727, by decide⟩ :=
  accepted_of_selected 13 308423 ⟨615727, by decide⟩ ⟨13, 2, 0, 615727, 308423, 849, 16384⟩
    (by decide) selected_cut_24353

theorem unmarked_context_12_77105_615728 : frontier 9 ⟨615728, by decide⟩
    (prefixCache 12 77105) (prefixPartial 12 77105) = false := by
  decide +kernel

theorem node_context_12_77105_615728 : EJMOriginalGlobalDAGData.nodes 9 ⟨615728, by decide⟩ =
    .split (coordinate 12) (![⟨615670, by decide⟩,⟨615699, by decide⟩,⟨615719, by decide⟩,⟨615727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77105_615728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77105 ⟨615728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77105
    ⟨615728, by decide⟩ (by decide) (![⟨615670, by decide⟩,⟨615699, by decide⟩,⟨615719, by decide⟩,⟨615727, by decide⟩]) unmarked_context_12_77105_615728 node_context_12_77105_615728
  intro a
  fin_cases a
  · exact context_13_308420_615670
  · exact context_13_308421_615699
  · exact context_13_308422_615719
  · exact context_13_308423_615727

theorem selected_cut_24354 : selected 8 ⟨615739, by decide⟩
    (prefixPartial 13 308424) = some ⟨13, 2, 0, 615739, 308424, 445, 16384⟩ := by
  decide +kernel

theorem context_13_308424_615739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308424 ⟨615739, by decide⟩ :=
  accepted_of_selected 13 308424 ⟨615739, by decide⟩ ⟨13, 2, 0, 615739, 308424, 445, 16384⟩
    (by decide) selected_cut_24354

theorem selected_cut_24355 : selected 8 ⟨615773, by decide⟩
    (prefixPartial 13 308425) = some ⟨13, 2, 0, 615773, 308425, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_308425_615773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308425 ⟨615773, by decide⟩ :=
  accepted_of_selected 13 308425 ⟨615773, by decide⟩ ⟨13, 2, 0, 615773, 308425, 2277, 16384⟩
    (by decide) selected_cut_24355

theorem selected_cut_24356 : selected 8 ⟨615792, by decide⟩
    (prefixPartial 13 308426) = some ⟨13, 2, 0, 615792, 308426, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_308426_615792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308426 ⟨615792, by decide⟩ :=
  accepted_of_selected 13 308426 ⟨615792, by decide⟩ ⟨13, 2, 0, 615792, 308426, 1605, 16384⟩
    (by decide) selected_cut_24356

theorem selected_cut_24357 : selected 8 ⟨615806, by decide⟩
    (prefixPartial 13 308427) = some ⟨13, 2, 0, 615806, 308427, 913, 16384⟩ := by
  decide +kernel

theorem context_13_308427_615806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308427 ⟨615806, by decide⟩ :=
  accepted_of_selected 13 308427 ⟨615806, by decide⟩ ⟨13, 2, 0, 615806, 308427, 913, 16384⟩
    (by decide) selected_cut_24357

theorem unmarked_context_12_77106_615807 : frontier 9 ⟨615807, by decide⟩
    (prefixCache 12 77106) (prefixPartial 12 77106) = false := by
  decide +kernel

theorem node_context_12_77106_615807 : EJMOriginalGlobalDAGData.nodes 9 ⟨615807, by decide⟩ =
    .split (coordinate 12) (![⟨615739, by decide⟩,⟨615773, by decide⟩,⟨615792, by decide⟩,⟨615806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77106_615807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77106 ⟨615807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77106
    ⟨615807, by decide⟩ (by decide) (![⟨615739, by decide⟩,⟨615773, by decide⟩,⟨615792, by decide⟩,⟨615806, by decide⟩]) unmarked_context_12_77106_615807 node_context_12_77106_615807
  intro a
  fin_cases a
  · exact context_13_308424_615739
  · exact context_13_308425_615773
  · exact context_13_308426_615792
  · exact context_13_308427_615806

theorem selected_cut_24358 : selected 8 ⟨615818, by decide⟩
    (prefixPartial 13 308428) = some ⟨13, 2, 0, 615818, 308428, 577, 16384⟩ := by
  decide +kernel

theorem context_13_308428_615818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308428 ⟨615818, by decide⟩ :=
  accepted_of_selected 13 308428 ⟨615818, by decide⟩ ⟨13, 2, 0, 615818, 308428, 577, 16384⟩
    (by decide) selected_cut_24358

theorem selected_cut_24359 : selected 8 ⟨615853, by decide⟩
    (prefixPartial 13 308429) = some ⟨13, 2, 0, 615853, 308429, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_308429_615853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308429 ⟨615853, by decide⟩ :=
  accepted_of_selected 13 308429 ⟨615853, by decide⟩ ⟨13, 2, 0, 615853, 308429, 2389, 16384⟩
    (by decide) selected_cut_24359

theorem selected_cut_24360 : selected 8 ⟨615875, by decide⟩
    (prefixPartial 13 308430) = some ⟨13, 2, 0, 615875, 308430, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_308430_615875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308430 ⟨615875, by decide⟩ :=
  accepted_of_selected 13 308430 ⟨615875, by decide⟩ ⟨13, 2, 0, 615875, 308430, 1793, 16384⟩
    (by decide) selected_cut_24360

theorem selected_cut_24361 : selected 8 ⟨615885, by decide⟩
    (prefixPartial 13 308431) = some ⟨13, 2, 0, 615885, 308431, 893, 16384⟩ := by
  decide +kernel

theorem context_13_308431_615885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308431 ⟨615885, by decide⟩ :=
  accepted_of_selected 13 308431 ⟨615885, by decide⟩ ⟨13, 2, 0, 615885, 308431, 893, 16384⟩
    (by decide) selected_cut_24361

theorem unmarked_context_12_77107_615886 : frontier 9 ⟨615886, by decide⟩
    (prefixCache 12 77107) (prefixPartial 12 77107) = false := by
  decide +kernel

theorem node_context_12_77107_615886 : EJMOriginalGlobalDAGData.nodes 9 ⟨615886, by decide⟩ =
    .split (coordinate 12) (![⟨615818, by decide⟩,⟨615853, by decide⟩,⟨615875, by decide⟩,⟨615885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77107_615886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77107 ⟨615886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77107
    ⟨615886, by decide⟩ (by decide) (![⟨615818, by decide⟩,⟨615853, by decide⟩,⟨615875, by decide⟩,⟨615885, by decide⟩]) unmarked_context_12_77107_615886 node_context_12_77107_615886
  intro a
  fin_cases a
  · exact context_13_308428_615818
  · exact context_13_308429_615853
  · exact context_13_308430_615875
  · exact context_13_308431_615885

theorem unmarked_context_11_19276_615887 : frontier 10 ⟨615887, by decide⟩
    (prefixCache 11 19276) (prefixPartial 11 19276) = false := by
  decide +kernel

theorem node_context_11_19276_615887 : EJMOriginalGlobalDAGData.nodes 10 ⟨615887, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨615728, by decide⟩,⟨615807, by decide⟩,⟨615886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19276_615887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19276 ⟨615887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19276
    ⟨615887, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨615728, by decide⟩,⟨615807, by decide⟩,⟨615886, by decide⟩]) unmarked_context_11_19276_615887 node_context_11_19276_615887
  intro a
  fin_cases a
  · exact context_12_77104_445562
  · exact context_12_77105_615728
  · exact context_12_77106_615807
  · exact context_12_77107_615886

theorem selected_cut_24362 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 77108) = some ⟨12, 1, 0, 475533, 77108, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77108_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77108 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 77108 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 77108, 1, 65536⟩
    (by decide) selected_cut_24362

theorem selected_cut_24363 : selected 8 ⟨615898, by decide⟩
    (prefixPartial 13 308436) = some ⟨13, 2, 0, 615898, 308436, 709, 16384⟩ := by
  decide +kernel

theorem context_13_308436_615898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308436 ⟨615898, by decide⟩ :=
  accepted_of_selected 13 308436 ⟨615898, by decide⟩ ⟨13, 2, 0, 615898, 308436, 709, 16384⟩
    (by decide) selected_cut_24363

theorem selected_cut_24364 : selected 8 ⟨615935, by decide⟩
    (prefixPartial 13 308437) = some ⟨13, 2, 0, 615935, 308437, 3237, 16384⟩ := by
  decide +kernel

theorem context_13_308437_615935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308437 ⟨615935, by decide⟩ :=
  accepted_of_selected 13 308437 ⟨615935, by decide⟩ ⟨13, 2, 0, 615935, 308437, 3237, 16384⟩
    (by decide) selected_cut_24364

theorem selected_cut_24365 : selected 8 ⟨615982, by decide⟩
    (prefixPartial 13 308438) = some ⟨13, 2, 0, 615982, 308438, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_308438_615982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308438 ⟨615982, by decide⟩ :=
  accepted_of_selected 13 308438 ⟨615982, by decide⟩ ⟨13, 2, 0, 615982, 308438, 2589, 16384⟩
    (by decide) selected_cut_24365

theorem selected_cut_24366 : selected 8 ⟨615999, by decide⟩
    (prefixPartial 13 308439) = some ⟨13, 2, 0, 615999, 308439, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_308439_615999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308439 ⟨615999, by decide⟩ :=
  accepted_of_selected 13 308439 ⟨615999, by decide⟩ ⟨13, 2, 0, 615999, 308439, 1125, 16384⟩
    (by decide) selected_cut_24366

theorem unmarked_context_12_77109_616000 : frontier 9 ⟨616000, by decide⟩
    (prefixCache 12 77109) (prefixPartial 12 77109) = false := by
  decide +kernel

theorem node_context_12_77109_616000 : EJMOriginalGlobalDAGData.nodes 9 ⟨616000, by decide⟩ =
    .split (coordinate 12) (![⟨615898, by decide⟩,⟨615935, by decide⟩,⟨615982, by decide⟩,⟨615999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77109_616000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77109 ⟨616000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77109
    ⟨616000, by decide⟩ (by decide) (![⟨615898, by decide⟩,⟨615935, by decide⟩,⟨615982, by decide⟩,⟨615999, by decide⟩]) unmarked_context_12_77109_616000 node_context_12_77109_616000
  intro a
  fin_cases a
  · exact context_13_308436_615898
  · exact context_13_308437_615935
  · exact context_13_308438_615982
  · exact context_13_308439_615999

theorem selected_cut_24367 : selected 8 ⟨616010, by decide⟩
    (prefixPartial 13 308440) = some ⟨13, 2, 0, 616010, 308440, 305, 16384⟩ := by
  decide +kernel

theorem context_13_308440_616010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308440 ⟨616010, by decide⟩ :=
  accepted_of_selected 13 308440 ⟨616010, by decide⟩ ⟨13, 2, 0, 616010, 308440, 305, 16384⟩
    (by decide) selected_cut_24367

theorem selected_cut_24368 : selected 8 ⟨616034, by decide⟩
    (prefixPartial 13 308441) = some ⟨13, 2, 0, 616034, 308441, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_308441_616034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308441 ⟨616034, by decide⟩ :=
  accepted_of_selected 13 308441 ⟨616034, by decide⟩ ⟨13, 2, 0, 616034, 308441, 1977, 16384⟩
    (by decide) selected_cut_24368

theorem selected_cut_24369 : selected 8 ⟨616055, by decide⟩
    (prefixPartial 13 308442) = some ⟨13, 2, 0, 616055, 308442, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_308442_616055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308442 ⟨616055, by decide⟩ :=
  accepted_of_selected 13 308442 ⟨616055, by decide⟩ ⟨13, 2, 0, 616055, 308442, 1433, 16384⟩
    (by decide) selected_cut_24369

theorem selected_cut_24370 : selected 8 ⟨616065, by decide⟩
    (prefixPartial 13 308443) = some ⟨13, 2, 0, 616065, 308443, 857, 16384⟩ := by
  decide +kernel

theorem context_13_308443_616065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308443 ⟨616065, by decide⟩ :=
  accepted_of_selected 13 308443 ⟨616065, by decide⟩ ⟨13, 2, 0, 616065, 308443, 857, 16384⟩
    (by decide) selected_cut_24370

theorem unmarked_context_12_77110_616066 : frontier 9 ⟨616066, by decide⟩
    (prefixCache 12 77110) (prefixPartial 12 77110) = false := by
  decide +kernel

theorem node_context_12_77110_616066 : EJMOriginalGlobalDAGData.nodes 9 ⟨616066, by decide⟩ =
    .split (coordinate 12) (![⟨616010, by decide⟩,⟨616034, by decide⟩,⟨616055, by decide⟩,⟨616065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77110_616066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77110 ⟨616066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77110
    ⟨616066, by decide⟩ (by decide) (![⟨616010, by decide⟩,⟨616034, by decide⟩,⟨616055, by decide⟩,⟨616065, by decide⟩]) unmarked_context_12_77110_616066 node_context_12_77110_616066
  intro a
  fin_cases a
  · exact context_13_308440_616010
  · exact context_13_308441_616034
  · exact context_13_308442_616055
  · exact context_13_308443_616065

theorem selected_cut_24371 : selected 8 ⟨616075, by decide⟩
    (prefixPartial 13 308444) = some ⟨13, 2, 0, 616075, 308444, 373, 16384⟩ := by
  decide +kernel

theorem context_13_308444_616075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308444 ⟨616075, by decide⟩ :=
  accepted_of_selected 13 308444 ⟨616075, by decide⟩ ⟨13, 2, 0, 616075, 308444, 373, 16384⟩
    (by decide) selected_cut_24371

theorem selected_cut_24372 : selected 8 ⟨616104, by decide⟩
    (prefixPartial 13 308445) = some ⟨13, 2, 0, 616104, 308445, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_308445_616104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308445 ⟨616104, by decide⟩ :=
  accepted_of_selected 13 308445 ⟨616104, by decide⟩ ⟨13, 2, 0, 616104, 308445, 2133, 16384⟩
    (by decide) selected_cut_24372

theorem selected_cut_24373 : selected 8 ⟨616129, by decide⟩
    (prefixPartial 13 308446) = some ⟨13, 2, 0, 616129, 308446, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_308446_616129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308446 ⟨616129, by decide⟩ :=
  accepted_of_selected 13 308446 ⟨616129, by decide⟩ ⟨13, 2, 0, 616129, 308446, 1821, 16384⟩
    (by decide) selected_cut_24373

theorem selected_cut_24374 : selected 8 ⟨616136, by decide⟩
    (prefixPartial 13 308447) = some ⟨13, 2, 0, 616136, 308447, 777, 16384⟩ := by
  decide +kernel

theorem context_13_308447_616136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308447 ⟨616136, by decide⟩ :=
  accepted_of_selected 13 308447 ⟨616136, by decide⟩ ⟨13, 2, 0, 616136, 308447, 777, 16384⟩
    (by decide) selected_cut_24374

theorem unmarked_context_12_77111_616137 : frontier 9 ⟨616137, by decide⟩
    (prefixCache 12 77111) (prefixPartial 12 77111) = false := by
  decide +kernel

theorem node_context_12_77111_616137 : EJMOriginalGlobalDAGData.nodes 9 ⟨616137, by decide⟩ =
    .split (coordinate 12) (![⟨616075, by decide⟩,⟨616104, by decide⟩,⟨616129, by decide⟩,⟨616136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77111_616137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77111 ⟨616137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77111
    ⟨616137, by decide⟩ (by decide) (![⟨616075, by decide⟩,⟨616104, by decide⟩,⟨616129, by decide⟩,⟨616136, by decide⟩]) unmarked_context_12_77111_616137 node_context_12_77111_616137
  intro a
  fin_cases a
  · exact context_13_308444_616075
  · exact context_13_308445_616104
  · exact context_13_308446_616129
  · exact context_13_308447_616136

theorem unmarked_context_11_19277_616138 : frontier 10 ⟨616138, by decide⟩
    (prefixCache 11 19277) (prefixPartial 11 19277) = false := by
  decide +kernel

theorem node_context_11_19277_616138 : EJMOriginalGlobalDAGData.nodes 10 ⟨616138, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨616000, by decide⟩,⟨616066, by decide⟩,⟨616137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19277_616138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19277 ⟨616138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19277
    ⟨616138, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨616000, by decide⟩,⟨616066, by decide⟩,⟨616137, by decide⟩]) unmarked_context_11_19277_616138 node_context_11_19277_616138
  intro a
  fin_cases a
  · exact context_12_77108_475533
  · exact context_12_77109_616000
  · exact context_12_77110_616066
  · exact context_12_77111_616137

theorem selected_cut_24375 : selected 9 ⟨616250, by decide⟩
    (prefixPartial 12 77112) = some ⟨12, 2, 0, 616250, 77112, 4049, 65536⟩ := by
  decide +kernel

theorem context_12_77112_616250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77112 ⟨616250, by decide⟩ :=
  accepted_of_selected 12 77112 ⟨616250, by decide⟩ ⟨12, 2, 0, 616250, 77112, 4049, 65536⟩
    (by decide) selected_cut_24375

theorem selected_cut_24376 : selected 8 ⟨616259, by decide⟩
    (prefixPartial 13 308452) = some ⟨13, 2, 0, 616259, 308452, 337, 16384⟩ := by
  decide +kernel

theorem context_13_308452_616259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308452 ⟨616259, by decide⟩ :=
  accepted_of_selected 13 308452 ⟨616259, by decide⟩ ⟨13, 2, 0, 616259, 308452, 337, 16384⟩
    (by decide) selected_cut_24376

theorem selected_cut_24377 : selected 8 ⟨616286, by decide⟩
    (prefixPartial 13 308453) = some ⟨13, 2, 0, 616286, 308453, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_308453_616286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308453 ⟨616286, by decide⟩ :=
  accepted_of_selected 13 308453 ⟨616286, by decide⟩ ⟨13, 2, 0, 616286, 308453, 2133, 16384⟩
    (by decide) selected_cut_24377

theorem selected_cut_24378 : selected 8 ⟨616308, by decide⟩
    (prefixPartial 13 308454) = some ⟨13, 2, 0, 616308, 308454, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_308454_616308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308454 ⟨616308, by decide⟩ :=
  accepted_of_selected 13 308454 ⟨616308, by decide⟩ ⟨13, 2, 0, 616308, 308454, 1973, 16384⟩
    (by decide) selected_cut_24378

theorem selected_cut_24379 : selected 8 ⟨616319, by decide⟩
    (prefixPartial 13 308455) = some ⟨13, 2, 0, 616319, 308455, 949, 16384⟩ := by
  decide +kernel

theorem context_13_308455_616319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308455 ⟨616319, by decide⟩ :=
  accepted_of_selected 13 308455 ⟨616319, by decide⟩ ⟨13, 2, 0, 616319, 308455, 949, 16384⟩
    (by decide) selected_cut_24379

theorem unmarked_context_12_77113_616320 : frontier 9 ⟨616320, by decide⟩
    (prefixCache 12 77113) (prefixPartial 12 77113) = false := by
  decide +kernel

theorem node_context_12_77113_616320 : EJMOriginalGlobalDAGData.nodes 9 ⟨616320, by decide⟩ =
    .split (coordinate 12) (![⟨616259, by decide⟩,⟨616286, by decide⟩,⟨616308, by decide⟩,⟨616319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77113_616320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77113 ⟨616320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77113
    ⟨616320, by decide⟩ (by decide) (![⟨616259, by decide⟩,⟨616286, by decide⟩,⟨616308, by decide⟩,⟨616319, by decide⟩]) unmarked_context_12_77113_616320 node_context_12_77113_616320
  intro a
  fin_cases a
  · exact context_13_308452_616259
  · exact context_13_308453_616286
  · exact context_13_308454_616308
  · exact context_13_308455_616319

theorem selected_cut_24380 : selected 8 ⟨616327, by decide⟩
    (prefixPartial 13 308456) = some ⟨13, 2, 0, 616327, 308456, 205, 16384⟩ := by
  decide +kernel

theorem context_13_308456_616327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308456 ⟨616327, by decide⟩ :=
  accepted_of_selected 13 308456 ⟨616327, by decide⟩ ⟨13, 2, 0, 616327, 308456, 205, 16384⟩
    (by decide) selected_cut_24380

theorem selected_cut_24381 : selected 8 ⟨616358, by decide⟩
    (prefixPartial 13 308457) = some ⟨13, 2, 0, 616358, 308457, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_308457_616358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308457 ⟨616358, by decide⟩ :=
  accepted_of_selected 13 308457 ⟨616358, by decide⟩ ⟨13, 2, 0, 616358, 308457, 2241, 16384⟩
    (by decide) selected_cut_24381

theorem selected_cut_24382 : selected 8 ⟨616382, by decide⟩
    (prefixPartial 13 308458) = some ⟨13, 2, 0, 616382, 308458, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_308458_616382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308458 ⟨616382, by decide⟩ :=
  accepted_of_selected 13 308458 ⟨616382, by decide⟩ ⟨13, 2, 0, 616382, 308458, 1657, 16384⟩
    (by decide) selected_cut_24382

theorem selected_cut_24383 : selected 8 ⟨616393, by decide⟩
    (prefixPartial 13 308459) = some ⟨13, 2, 0, 616393, 308459, 937, 16384⟩ := by
  decide +kernel

theorem context_13_308459_616393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308459 ⟨616393, by decide⟩ :=
  accepted_of_selected 13 308459 ⟨616393, by decide⟩ ⟨13, 2, 0, 616393, 308459, 937, 16384⟩
    (by decide) selected_cut_24383

theorem unmarked_context_12_77114_616394 : frontier 9 ⟨616394, by decide⟩
    (prefixCache 12 77114) (prefixPartial 12 77114) = false := by
  decide +kernel

theorem node_context_12_77114_616394 : EJMOriginalGlobalDAGData.nodes 9 ⟨616394, by decide⟩ =
    .split (coordinate 12) (![⟨616327, by decide⟩,⟨616358, by decide⟩,⟨616382, by decide⟩,⟨616393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77114_616394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77114 ⟨616394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77114
    ⟨616394, by decide⟩ (by decide) (![⟨616327, by decide⟩,⟨616358, by decide⟩,⟨616382, by decide⟩,⟨616393, by decide⟩]) unmarked_context_12_77114_616394 node_context_12_77114_616394
  intro a
  fin_cases a
  · exact context_13_308456_616327
  · exact context_13_308457_616358
  · exact context_13_308458_616382
  · exact context_13_308459_616393

theorem selected_cut_24384 : selected 8 ⟨616401, by decide⟩
    (prefixPartial 13 308460) = some ⟨13, 2, 0, 616401, 308460, 205, 16384⟩ := by
  decide +kernel

theorem context_13_308460_616401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308460 ⟨616401, by decide⟩ :=
  accepted_of_selected 13 308460 ⟨616401, by decide⟩ ⟨13, 2, 0, 616401, 308460, 205, 16384⟩
    (by decide) selected_cut_24384

theorem selected_cut_24385 : selected 8 ⟨616440, by decide⟩
    (prefixPartial 13 308461) = some ⟨13, 2, 0, 616440, 308461, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_308461_616440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308461 ⟨616440, by decide⟩ :=
  accepted_of_selected 13 308461 ⟨616440, by decide⟩ ⟨13, 2, 0, 616440, 308461, 2497, 16384⟩
    (by decide) selected_cut_24385

theorem selected_cut_24386 : selected 8 ⟨616468, by decide⟩
    (prefixPartial 13 308462) = some ⟨13, 2, 0, 616468, 308462, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_308462_616468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308462 ⟨616468, by decide⟩ :=
  accepted_of_selected 13 308462 ⟨616468, by decide⟩ ⟨13, 2, 0, 616468, 308462, 1993, 16384⟩
    (by decide) selected_cut_24386

theorem selected_cut_24387 : selected 8 ⟨616489, by decide⟩
    (prefixPartial 13 308463) = some ⟨13, 2, 0, 616489, 308463, 941, 16384⟩ := by
  decide +kernel

theorem context_13_308463_616489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308463 ⟨616489, by decide⟩ :=
  accepted_of_selected 13 308463 ⟨616489, by decide⟩ ⟨13, 2, 0, 616489, 308463, 941, 16384⟩
    (by decide) selected_cut_24387

theorem unmarked_context_12_77115_616490 : frontier 9 ⟨616490, by decide⟩
    (prefixCache 12 77115) (prefixPartial 12 77115) = false := by
  decide +kernel

theorem node_context_12_77115_616490 : EJMOriginalGlobalDAGData.nodes 9 ⟨616490, by decide⟩ =
    .split (coordinate 12) (![⟨616401, by decide⟩,⟨616440, by decide⟩,⟨616468, by decide⟩,⟨616489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77115_616490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77115 ⟨616490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77115
    ⟨616490, by decide⟩ (by decide) (![⟨616401, by decide⟩,⟨616440, by decide⟩,⟨616468, by decide⟩,⟨616489, by decide⟩]) unmarked_context_12_77115_616490 node_context_12_77115_616490
  intro a
  fin_cases a
  · exact context_13_308460_616401
  · exact context_13_308461_616440
  · exact context_13_308462_616468
  · exact context_13_308463_616489

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
