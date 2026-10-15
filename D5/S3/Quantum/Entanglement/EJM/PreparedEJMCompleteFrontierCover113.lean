/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover112
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_10851 : selected 8 ⟨292885, by decide⟩
    (prefixPartial 13 101433) = some ⟨13, 2, 0, 292885, 101433, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_101433_292885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101433 ⟨292885, by decide⟩ :=
  accepted_of_selected 13 101433 ⟨292885, by decide⟩ ⟨13, 2, 0, 292885, 101433, 3333, 16384⟩
    (by decide) selected_cut_10851

theorem selected_cut_10852 : selected 8 ⟨292911, by decide⟩
    (prefixPartial 13 101434) = some ⟨13, 2, 0, 292911, 101434, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_101434_292911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101434 ⟨292911, by decide⟩ :=
  accepted_of_selected 13 101434 ⟨292911, by decide⟩ ⟨13, 2, 0, 292911, 101434, 2241, 16384⟩
    (by decide) selected_cut_10852

theorem selected_cut_10853 : selected 8 ⟨292919, by decide⟩
    (prefixPartial 13 101435) = some ⟨13, 2, 0, 292919, 101435, 857, 16384⟩ := by
  decide +kernel

theorem context_13_101435_292919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101435 ⟨292919, by decide⟩ :=
  accepted_of_selected 13 101435 ⟨292919, by decide⟩ ⟨13, 2, 0, 292919, 101435, 857, 16384⟩
    (by decide) selected_cut_10853

theorem unmarked_context_12_25358_292920 : frontier 9 ⟨292920, by decide⟩
    (prefixCache 12 25358) (prefixPartial 12 25358) = false := by
  decide +kernel

theorem node_context_12_25358_292920 : EJMOriginalGlobalDAGData.nodes 9 ⟨292920, by decide⟩ =
    .split (coordinate 12) (![⟨292837, by decide⟩,⟨292885, by decide⟩,⟨292911, by decide⟩,⟨292919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25358_292920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25358 ⟨292920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25358
    ⟨292920, by decide⟩ (by decide) (![⟨292837, by decide⟩,⟨292885, by decide⟩,⟨292911, by decide⟩,⟨292919, by decide⟩]) unmarked_context_12_25358_292920 node_context_12_25358_292920
  intro a
  fin_cases a
  · exact context_13_101432_292837
  · exact context_13_101433_292885
  · exact context_13_101434_292911
  · exact context_13_101435_292919

theorem selected_cut_10854 : selected 7 ⟨292928, by decide⟩
    (prefixPartial 14 405744) = some ⟨14, 2, 0, 292928, 405744, 277, 4096⟩ := by
  decide +kernel

theorem context_14_405744_292928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405744 ⟨292928, by decide⟩ :=
  accepted_of_selected 14 405744 ⟨292928, by decide⟩ ⟨14, 2, 0, 292928, 405744, 277, 4096⟩
    (by decide) selected_cut_10854

theorem selected_cut_10855 : selected 7 ⟨292960, by decide⟩
    (prefixPartial 14 405745) = some ⟨14, 2, 0, 292960, 405745, 1833, 4096⟩ := by
  decide +kernel

theorem context_14_405745_292960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405745 ⟨292960, by decide⟩ :=
  accepted_of_selected 14 405745 ⟨292960, by decide⟩ ⟨14, 2, 0, 292960, 405745, 1833, 4096⟩
    (by decide) selected_cut_10855

theorem selected_cut_10856 : selected 7 ⟨292979, by decide⟩
    (prefixPartial 14 405746) = some ⟨14, 2, 0, 292979, 405746, 1445, 4096⟩ := by
  decide +kernel

theorem context_14_405746_292979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405746 ⟨292979, by decide⟩ :=
  accepted_of_selected 14 405746 ⟨292979, by decide⟩ ⟨14, 2, 0, 292979, 405746, 1445, 4096⟩
    (by decide) selected_cut_10856

theorem selected_cut_10857 : selected 7 ⟨292996, by decide⟩
    (prefixPartial 14 405747) = some ⟨14, 2, 0, 292996, 405747, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_405747_292996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405747 ⟨292996, by decide⟩ :=
  accepted_of_selected 14 405747 ⟨292996, by decide⟩ ⟨14, 2, 0, 292996, 405747, 1193, 4096⟩
    (by decide) selected_cut_10857

theorem unmarked_context_13_101436_292997 : frontier 8 ⟨292997, by decide⟩
    (prefixCache 13 101436) (prefixPartial 13 101436) = false := by
  decide +kernel

theorem node_context_13_101436_292997 : EJMOriginalGlobalDAGData.nodes 8 ⟨292997, by decide⟩ =
    .split (coordinate 13) (![⟨292928, by decide⟩,⟨292960, by decide⟩,⟨292979, by decide⟩,⟨292996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_101436_292997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101436 ⟨292997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 101436
    ⟨292997, by decide⟩ (by decide) (![⟨292928, by decide⟩,⟨292960, by decide⟩,⟨292979, by decide⟩,⟨292996, by decide⟩]) unmarked_context_13_101436_292997 node_context_13_101436_292997
  intro a
  fin_cases a
  · exact context_14_405744_292928
  · exact context_14_405745_292960
  · exact context_14_405746_292979
  · exact context_14_405747_292996

theorem selected_cut_10858 : selected 7 ⟨293026, by decide⟩
    (prefixPartial 14 405748) = some ⟨14, 2, 0, 293026, 405748, 1561, 4096⟩ := by
  decide +kernel

theorem context_14_405748_293026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405748 ⟨293026, by decide⟩ :=
  accepted_of_selected 14 405748 ⟨293026, by decide⟩ ⟨14, 2, 0, 293026, 405748, 1561, 4096⟩
    (by decide) selected_cut_10858

theorem selected_cut_10859 : selected 7 ⟨293053, by decide⟩
    (prefixPartial 14 405749) = some ⟨14, 2, 0, 293053, 405749, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_405749_293053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405749 ⟨293053, by decide⟩ :=
  accepted_of_selected 14 405749 ⟨293053, by decide⟩ ⟨14, 2, 0, 293053, 405749, 1341, 4096⟩
    (by decide) selected_cut_10859

theorem selected_cut_10860 : selected 7 ⟨293076, by decide⟩
    (prefixPartial 14 405750) = some ⟨14, 2, 0, 293076, 405750, 1369, 4096⟩ := by
  decide +kernel

theorem context_14_405750_293076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405750 ⟨293076, by decide⟩ :=
  accepted_of_selected 14 405750 ⟨293076, by decide⟩ ⟨14, 2, 0, 293076, 405750, 1369, 4096⟩
    (by decide) selected_cut_10860

theorem selected_cut_10861 : selected 7 ⟨293101, by decide⟩
    (prefixPartial 14 405751) = some ⟨14, 2, 0, 293101, 405751, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_405751_293101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 405751 ⟨293101, by decide⟩ :=
  accepted_of_selected 14 405751 ⟨293101, by decide⟩ ⟨14, 2, 0, 293101, 405751, 1089, 4096⟩
    (by decide) selected_cut_10861

theorem unmarked_context_13_101437_293102 : frontier 8 ⟨293102, by decide⟩
    (prefixCache 13 101437) (prefixPartial 13 101437) = false := by
  decide +kernel

theorem node_context_13_101437_293102 : EJMOriginalGlobalDAGData.nodes 8 ⟨293102, by decide⟩ =
    .split (coordinate 13) (![⟨293026, by decide⟩,⟨293053, by decide⟩,⟨293076, by decide⟩,⟨293101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_101437_293102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101437 ⟨293102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 101437
    ⟨293102, by decide⟩ (by decide) (![⟨293026, by decide⟩,⟨293053, by decide⟩,⟨293076, by decide⟩,⟨293101, by decide⟩]) unmarked_context_13_101437_293102 node_context_13_101437_293102
  intro a
  fin_cases a
  · exact context_14_405748_293026
  · exact context_14_405749_293053
  · exact context_14_405750_293076
  · exact context_14_405751_293101

theorem selected_cut_10862 : selected 8 ⟨293194, by decide⟩
    (prefixPartial 13 101438) = some ⟨13, 2, 0, 293194, 101438, 3633, 16384⟩ := by
  decide +kernel

theorem context_13_101438_293194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101438 ⟨293194, by decide⟩ :=
  accepted_of_selected 13 101438 ⟨293194, by decide⟩ ⟨13, 2, 0, 293194, 101438, 3633, 16384⟩
    (by decide) selected_cut_10862

theorem selected_cut_10863 : selected 8 ⟨293251, by decide⟩
    (prefixPartial 13 101439) = some ⟨13, 2, 0, 293251, 101439, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_101439_293251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101439 ⟨293251, by decide⟩ :=
  accepted_of_selected 13 101439 ⟨293251, by decide⟩ ⟨13, 2, 0, 293251, 101439, 1501, 16384⟩
    (by decide) selected_cut_10863

theorem unmarked_context_12_25359_293252 : frontier 9 ⟨293252, by decide⟩
    (prefixCache 12 25359) (prefixPartial 12 25359) = false := by
  decide +kernel

theorem node_context_12_25359_293252 : EJMOriginalGlobalDAGData.nodes 9 ⟨293252, by decide⟩ =
    .split (coordinate 12) (![⟨292997, by decide⟩,⟨293102, by decide⟩,⟨293194, by decide⟩,⟨293251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25359_293252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25359 ⟨293252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25359
    ⟨293252, by decide⟩ (by decide) (![⟨292997, by decide⟩,⟨293102, by decide⟩,⟨293194, by decide⟩,⟨293251, by decide⟩]) unmarked_context_12_25359_293252 node_context_12_25359_293252
  intro a
  fin_cases a
  · exact context_13_101436_292997
  · exact context_13_101437_293102
  · exact context_13_101438_293194
  · exact context_13_101439_293251

theorem unmarked_context_11_6339_293253 : frontier 10 ⟨293253, by decide⟩
    (prefixCache 11 6339) (prefixPartial 11 6339) = false := by
  decide +kernel

theorem node_context_11_6339_293253 : EJMOriginalGlobalDAGData.nodes 10 ⟨293253, by decide⟩ =
    .split (coordinate 11) (![⟨292651, by decide⟩,⟨292793, by decide⟩,⟨292920, by decide⟩,⟨293252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6339_293253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6339 ⟨293253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6339
    ⟨293253, by decide⟩ (by decide) (![⟨292651, by decide⟩,⟨292793, by decide⟩,⟨292920, by decide⟩,⟨293252, by decide⟩]) unmarked_context_11_6339_293253 node_context_11_6339_293253
  intro a
  fin_cases a
  · exact context_12_25356_292651
  · exact context_12_25357_292793
  · exact context_12_25358_292920
  · exact context_12_25359_293252

theorem unmarked_context_10_1584_293254 : frontier 11 ⟨293254, by decide⟩
    (prefixCache 10 1584) (prefixPartial 10 1584) = false := by
  decide +kernel

theorem node_context_10_1584_293254 : EJMOriginalGlobalDAGData.nodes 11 ⟨293254, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨292027, by decide⟩,⟨292650, by decide⟩,⟨293253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1584_293254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1584 ⟨293254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1584
    ⟨293254, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨292027, by decide⟩,⟨292650, by decide⟩,⟨293253, by decide⟩]) unmarked_context_10_1584_293254 node_context_10_1584_293254
  intro a
  fin_cases a
  · exact context_11_6336_167448
  · exact context_11_6337_292027
  · exact context_11_6338_292650
  · exact context_11_6339_293253

theorem selected_cut_10864 : selected 8 ⟨293279, by decide⟩
    (prefixPartial 13 101440) = some ⟨13, 2, 0, 293279, 101440, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_101440_293279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101440 ⟨293279, by decide⟩ :=
  accepted_of_selected 13 101440 ⟨293279, by decide⟩ ⟨13, 2, 0, 293279, 101440, 1409, 16384⟩
    (by decide) selected_cut_10864

theorem selected_cut_10865 : selected 8 ⟨293297, by decide⟩
    (prefixPartial 13 101441) = some ⟨13, 2, 0, 293297, 101441, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_101441_293297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101441 ⟨293297, by decide⟩ :=
  accepted_of_selected 13 101441 ⟨293297, by decide⟩ ⟨13, 2, 0, 293297, 101441, 1221, 16384⟩
    (by decide) selected_cut_10865

theorem selected_cut_10866 : selected 8 ⟨293309, by decide⟩
    (prefixPartial 13 101442) = some ⟨13, 2, 0, 293309, 101442, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_101442_293309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101442 ⟨293309, by decide⟩ :=
  accepted_of_selected 13 101442 ⟨293309, by decide⟩ ⟨13, 2, 0, 293309, 101442, 1037, 16384⟩
    (by decide) selected_cut_10866

theorem selected_cut_10867 : selected 8 ⟨293315, by decide⟩
    (prefixPartial 13 101443) = some ⟨13, 2, 0, 293315, 101443, 605, 16384⟩ := by
  decide +kernel

theorem context_13_101443_293315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101443 ⟨293315, by decide⟩ :=
  accepted_of_selected 13 101443 ⟨293315, by decide⟩ ⟨13, 2, 0, 293315, 101443, 605, 16384⟩
    (by decide) selected_cut_10867

theorem unmarked_context_12_25360_293316 : frontier 9 ⟨293316, by decide⟩
    (prefixCache 12 25360) (prefixPartial 12 25360) = false := by
  decide +kernel

theorem node_context_12_25360_293316 : EJMOriginalGlobalDAGData.nodes 9 ⟨293316, by decide⟩ =
    .split (coordinate 12) (![⟨293279, by decide⟩,⟨293297, by decide⟩,⟨293309, by decide⟩,⟨293315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25360_293316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25360 ⟨293316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25360
    ⟨293316, by decide⟩ (by decide) (![⟨293279, by decide⟩,⟨293297, by decide⟩,⟨293309, by decide⟩,⟨293315, by decide⟩]) unmarked_context_12_25360_293316 node_context_12_25360_293316
  intro a
  fin_cases a
  · exact context_13_101440_293279
  · exact context_13_101441_293297
  · exact context_13_101442_293309
  · exact context_13_101443_293315

theorem selected_cut_10868 : selected 8 ⟨293334, by decide⟩
    (prefixPartial 13 101444) = some ⟨13, 2, 0, 293334, 101444, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_101444_293334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101444 ⟨293334, by decide⟩ :=
  accepted_of_selected 13 101444 ⟨293334, by decide⟩ ⟨13, 2, 0, 293334, 101444, 1377, 16384⟩
    (by decide) selected_cut_10868

theorem selected_cut_10869 : selected 8 ⟨293362, by decide⟩
    (prefixPartial 13 101445) = some ⟨13, 2, 0, 293362, 101445, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_101445_293362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101445 ⟨293362, by decide⟩ :=
  accepted_of_selected 13 101445 ⟨293362, by decide⟩ ⟨13, 2, 0, 293362, 101445, 1709, 16384⟩
    (by decide) selected_cut_10869

theorem selected_cut_10870 : selected 8 ⟨293378, by decide⟩
    (prefixPartial 13 101446) = some ⟨13, 2, 0, 293378, 101446, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_101446_293378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101446 ⟨293378, by decide⟩ :=
  accepted_of_selected 13 101446 ⟨293378, by decide⟩ ⟨13, 2, 0, 293378, 101446, 1353, 16384⟩
    (by decide) selected_cut_10870

theorem selected_cut_10871 : selected 8 ⟨293384, by decide⟩
    (prefixPartial 13 101447) = some ⟨13, 2, 0, 293384, 101447, 589, 16384⟩ := by
  decide +kernel

theorem context_13_101447_293384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101447 ⟨293384, by decide⟩ :=
  accepted_of_selected 13 101447 ⟨293384, by decide⟩ ⟨13, 2, 0, 293384, 101447, 589, 16384⟩
    (by decide) selected_cut_10871

theorem unmarked_context_12_25361_293385 : frontier 9 ⟨293385, by decide⟩
    (prefixCache 12 25361) (prefixPartial 12 25361) = false := by
  decide +kernel

theorem node_context_12_25361_293385 : EJMOriginalGlobalDAGData.nodes 9 ⟨293385, by decide⟩ =
    .split (coordinate 12) (![⟨293334, by decide⟩,⟨293362, by decide⟩,⟨293378, by decide⟩,⟨293384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25361_293385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25361 ⟨293385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25361
    ⟨293385, by decide⟩ (by decide) (![⟨293334, by decide⟩,⟨293362, by decide⟩,⟨293378, by decide⟩,⟨293384, by decide⟩]) unmarked_context_12_25361_293385 node_context_12_25361_293385
  intro a
  fin_cases a
  · exact context_13_101444_293334
  · exact context_13_101445_293362
  · exact context_13_101446_293378
  · exact context_13_101447_293384

theorem selected_cut_10872 : selected 8 ⟨293408, by decide⟩
    (prefixPartial 13 101448) = some ⟨13, 2, 0, 293408, 101448, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_101448_293408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101448 ⟨293408, by decide⟩ :=
  accepted_of_selected 13 101448 ⟨293408, by decide⟩ ⟨13, 2, 0, 293408, 101448, 1617, 16384⟩
    (by decide) selected_cut_10872

theorem selected_cut_10873 : selected 8 ⟨293432, by decide⟩
    (prefixPartial 13 101449) = some ⟨13, 2, 0, 293432, 101449, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_101449_293432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101449 ⟨293432, by decide⟩ :=
  accepted_of_selected 13 101449 ⟨293432, by decide⟩ ⟨13, 2, 0, 293432, 101449, 1673, 16384⟩
    (by decide) selected_cut_10873

theorem selected_cut_10874 : selected 8 ⟨293450, by decide⟩
    (prefixPartial 13 101450) = some ⟨13, 2, 0, 293450, 101450, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_101450_293450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101450 ⟨293450, by decide⟩ :=
  accepted_of_selected 13 101450 ⟨293450, by decide⟩ ⟨13, 2, 0, 293450, 101450, 1309, 16384⟩
    (by decide) selected_cut_10874

theorem selected_cut_10875 : selected 8 ⟨293454, by decide⟩
    (prefixPartial 13 101451) = some ⟨13, 2, 0, 293454, 101451, 589, 16384⟩ := by
  decide +kernel

theorem context_13_101451_293454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101451 ⟨293454, by decide⟩ :=
  accepted_of_selected 13 101451 ⟨293454, by decide⟩ ⟨13, 2, 0, 293454, 101451, 589, 16384⟩
    (by decide) selected_cut_10875

theorem unmarked_context_12_25362_293455 : frontier 9 ⟨293455, by decide⟩
    (prefixCache 12 25362) (prefixPartial 12 25362) = false := by
  decide +kernel

theorem node_context_12_25362_293455 : EJMOriginalGlobalDAGData.nodes 9 ⟨293455, by decide⟩ =
    .split (coordinate 12) (![⟨293408, by decide⟩,⟨293432, by decide⟩,⟨293450, by decide⟩,⟨293454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25362_293455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25362 ⟨293455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25362
    ⟨293455, by decide⟩ (by decide) (![⟨293408, by decide⟩,⟨293432, by decide⟩,⟨293450, by decide⟩,⟨293454, by decide⟩]) unmarked_context_12_25362_293455 node_context_12_25362_293455
  intro a
  fin_cases a
  · exact context_13_101448_293408
  · exact context_13_101449_293432
  · exact context_13_101450_293450
  · exact context_13_101451_293454

theorem selected_cut_10876 : selected 8 ⟨293475, by decide⟩
    (prefixPartial 13 101452) = some ⟨13, 2, 0, 293475, 101452, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_101452_293475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101452 ⟨293475, by decide⟩ :=
  accepted_of_selected 13 101452 ⟨293475, by decide⟩ ⟨13, 2, 0, 293475, 101452, 1501, 16384⟩
    (by decide) selected_cut_10876

theorem selected_cut_10877 : selected 8 ⟨293503, by decide⟩
    (prefixPartial 13 101453) = some ⟨13, 2, 0, 293503, 101453, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_101453_293503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101453 ⟨293503, by decide⟩ :=
  accepted_of_selected 13 101453 ⟨293503, by decide⟩ ⟨13, 2, 0, 293503, 101453, 1805, 16384⟩
    (by decide) selected_cut_10877

theorem selected_cut_10878 : selected 8 ⟨293519, by decide⟩
    (prefixPartial 13 101454) = some ⟨13, 2, 0, 293519, 101454, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_101454_293519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101454 ⟨293519, by decide⟩ :=
  accepted_of_selected 13 101454 ⟨293519, by decide⟩ ⟨13, 2, 0, 293519, 101454, 1257, 16384⟩
    (by decide) selected_cut_10878

theorem selected_cut_10879 : selected 8 ⟨293523, by decide⟩
    (prefixPartial 13 101455) = some ⟨13, 2, 0, 293523, 101455, 581, 16384⟩ := by
  decide +kernel

theorem context_13_101455_293523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101455 ⟨293523, by decide⟩ :=
  accepted_of_selected 13 101455 ⟨293523, by decide⟩ ⟨13, 2, 0, 293523, 101455, 581, 16384⟩
    (by decide) selected_cut_10879

theorem unmarked_context_12_25363_293524 : frontier 9 ⟨293524, by decide⟩
    (prefixCache 12 25363) (prefixPartial 12 25363) = false := by
  decide +kernel

theorem node_context_12_25363_293524 : EJMOriginalGlobalDAGData.nodes 9 ⟨293524, by decide⟩ =
    .split (coordinate 12) (![⟨293475, by decide⟩,⟨293503, by decide⟩,⟨293519, by decide⟩,⟨293523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25363_293524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25363 ⟨293524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25363
    ⟨293524, by decide⟩ (by decide) (![⟨293475, by decide⟩,⟨293503, by decide⟩,⟨293519, by decide⟩,⟨293523, by decide⟩]) unmarked_context_12_25363_293524 node_context_12_25363_293524
  intro a
  fin_cases a
  · exact context_13_101452_293475
  · exact context_13_101453_293503
  · exact context_13_101454_293519
  · exact context_13_101455_293523

theorem unmarked_context_11_6340_293525 : frontier 10 ⟨293525, by decide⟩
    (prefixCache 11 6340) (prefixPartial 11 6340) = false := by
  decide +kernel

theorem node_context_11_6340_293525 : EJMOriginalGlobalDAGData.nodes 10 ⟨293525, by decide⟩ =
    .split (coordinate 11) (![⟨293316, by decide⟩,⟨293385, by decide⟩,⟨293455, by decide⟩,⟨293524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6340_293525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6340 ⟨293525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6340
    ⟨293525, by decide⟩ (by decide) (![⟨293316, by decide⟩,⟨293385, by decide⟩,⟨293455, by decide⟩,⟨293524, by decide⟩]) unmarked_context_11_6340_293525 node_context_11_6340_293525
  intro a
  fin_cases a
  · exact context_12_25360_293316
  · exact context_12_25361_293385
  · exact context_12_25362_293455
  · exact context_12_25363_293524

theorem selected_cut_10880 : selected 8 ⟨293548, by decide⟩
    (prefixPartial 13 101456) = some ⟨13, 2, 0, 293548, 101456, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_101456_293548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101456 ⟨293548, by decide⟩ :=
  accepted_of_selected 13 101456 ⟨293548, by decide⟩ ⟨13, 2, 0, 293548, 101456, 1537, 16384⟩
    (by decide) selected_cut_10880

theorem selected_cut_10881 : selected 8 ⟨293571, by decide⟩
    (prefixPartial 13 101457) = some ⟨13, 2, 0, 293571, 101457, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_101457_293571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101457 ⟨293571, by decide⟩ :=
  accepted_of_selected 13 101457 ⟨293571, by decide⟩ ⟨13, 2, 0, 293571, 101457, 2013, 16384⟩
    (by decide) selected_cut_10881

theorem selected_cut_10882 : selected 8 ⟨293592, by decide⟩
    (prefixPartial 13 101458) = some ⟨13, 2, 0, 293592, 101458, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_101458_293592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101458 ⟨293592, by decide⟩ :=
  accepted_of_selected 13 101458 ⟨293592, by decide⟩ ⟨13, 2, 0, 293592, 101458, 1473, 16384⟩
    (by decide) selected_cut_10882

theorem selected_cut_10883 : selected 8 ⟨293598, by decide⟩
    (prefixPartial 13 101459) = some ⟨13, 2, 0, 293598, 101459, 733, 16384⟩ := by
  decide +kernel

theorem context_13_101459_293598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101459 ⟨293598, by decide⟩ :=
  accepted_of_selected 13 101459 ⟨293598, by decide⟩ ⟨13, 2, 0, 293598, 101459, 733, 16384⟩
    (by decide) selected_cut_10883

theorem unmarked_context_12_25364_293599 : frontier 9 ⟨293599, by decide⟩
    (prefixCache 12 25364) (prefixPartial 12 25364) = false := by
  decide +kernel

theorem node_context_12_25364_293599 : EJMOriginalGlobalDAGData.nodes 9 ⟨293599, by decide⟩ =
    .split (coordinate 12) (![⟨293548, by decide⟩,⟨293571, by decide⟩,⟨293592, by decide⟩,⟨293598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25364_293599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25364 ⟨293599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25364
    ⟨293599, by decide⟩ (by decide) (![⟨293548, by decide⟩,⟨293571, by decide⟩,⟨293592, by decide⟩,⟨293598, by decide⟩]) unmarked_context_12_25364_293599 node_context_12_25364_293599
  intro a
  fin_cases a
  · exact context_13_101456_293548
  · exact context_13_101457_293571
  · exact context_13_101458_293592
  · exact context_13_101459_293598

theorem selected_cut_10884 : selected 8 ⟨293621, by decide⟩
    (prefixPartial 13 101460) = some ⟨13, 2, 0, 293621, 101460, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_101460_293621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101460 ⟨293621, by decide⟩ :=
  accepted_of_selected 13 101460 ⟨293621, by decide⟩ ⟨13, 2, 0, 293621, 101460, 1497, 16384⟩
    (by decide) selected_cut_10884

theorem selected_cut_10885 : selected 8 ⟨293650, by decide⟩
    (prefixPartial 13 101461) = some ⟨13, 2, 0, 293650, 101461, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_101461_293650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101461 ⟨293650, by decide⟩ :=
  accepted_of_selected 13 101461 ⟨293650, by decide⟩ ⟨13, 2, 0, 293650, 101461, 2217, 16384⟩
    (by decide) selected_cut_10885

theorem selected_cut_10886 : selected 8 ⟨293674, by decide⟩
    (prefixPartial 13 101462) = some ⟨13, 2, 0, 293674, 101462, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_101462_293674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101462 ⟨293674, by decide⟩ :=
  accepted_of_selected 13 101462 ⟨293674, by decide⟩ ⟨13, 2, 0, 293674, 101462, 1681, 16384⟩
    (by decide) selected_cut_10886

theorem selected_cut_10887 : selected 8 ⟨293681, by decide⟩
    (prefixPartial 13 101463) = some ⟨13, 2, 0, 293681, 101463, 717, 16384⟩ := by
  decide +kernel

theorem context_13_101463_293681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101463 ⟨293681, by decide⟩ :=
  accepted_of_selected 13 101463 ⟨293681, by decide⟩ ⟨13, 2, 0, 293681, 101463, 717, 16384⟩
    (by decide) selected_cut_10887

theorem unmarked_context_12_25365_293682 : frontier 9 ⟨293682, by decide⟩
    (prefixCache 12 25365) (prefixPartial 12 25365) = false := by
  decide +kernel

theorem node_context_12_25365_293682 : EJMOriginalGlobalDAGData.nodes 9 ⟨293682, by decide⟩ =
    .split (coordinate 12) (![⟨293621, by decide⟩,⟨293650, by decide⟩,⟨293674, by decide⟩,⟨293681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25365_293682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25365 ⟨293682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25365
    ⟨293682, by decide⟩ (by decide) (![⟨293621, by decide⟩,⟨293650, by decide⟩,⟨293674, by decide⟩,⟨293681, by decide⟩]) unmarked_context_12_25365_293682 node_context_12_25365_293682
  intro a
  fin_cases a
  · exact context_13_101460_293621
  · exact context_13_101461_293650
  · exact context_13_101462_293674
  · exact context_13_101463_293681

theorem selected_cut_10888 : selected 8 ⟨293709, by decide⟩
    (prefixPartial 13 101464) = some ⟨13, 2, 0, 293709, 101464, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_101464_293709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101464 ⟨293709, by decide⟩ :=
  accepted_of_selected 13 101464 ⟨293709, by decide⟩ ⟨13, 2, 0, 293709, 101464, 1781, 16384⟩
    (by decide) selected_cut_10888

theorem selected_cut_10889 : selected 8 ⟨293736, by decide⟩
    (prefixPartial 13 101465) = some ⟨13, 2, 0, 293736, 101465, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_101465_293736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101465 ⟨293736, by decide⟩ :=
  accepted_of_selected 13 101465 ⟨293736, by decide⟩ ⟨13, 2, 0, 293736, 101465, 2253, 16384⟩
    (by decide) selected_cut_10889

theorem selected_cut_10890 : selected 8 ⟨293760, by decide⟩
    (prefixPartial 13 101466) = some ⟨13, 2, 0, 293760, 101466, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_101466_293760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101466 ⟨293760, by decide⟩ :=
  accepted_of_selected 13 101466 ⟨293760, by decide⟩ ⟨13, 2, 0, 293760, 101466, 1653, 16384⟩
    (by decide) selected_cut_10890

theorem selected_cut_10891 : selected 8 ⟨293769, by decide⟩
    (prefixPartial 13 101467) = some ⟨13, 2, 0, 293769, 101467, 829, 16384⟩ := by
  decide +kernel

theorem context_13_101467_293769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101467 ⟨293769, by decide⟩ :=
  accepted_of_selected 13 101467 ⟨293769, by decide⟩ ⟨13, 2, 0, 293769, 101467, 829, 16384⟩
    (by decide) selected_cut_10891

theorem unmarked_context_12_25366_293770 : frontier 9 ⟨293770, by decide⟩
    (prefixCache 12 25366) (prefixPartial 12 25366) = false := by
  decide +kernel

theorem node_context_12_25366_293770 : EJMOriginalGlobalDAGData.nodes 9 ⟨293770, by decide⟩ =
    .split (coordinate 12) (![⟨293709, by decide⟩,⟨293736, by decide⟩,⟨293760, by decide⟩,⟨293769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25366_293770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25366 ⟨293770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25366
    ⟨293770, by decide⟩ (by decide) (![⟨293709, by decide⟩,⟨293736, by decide⟩,⟨293760, by decide⟩,⟨293769, by decide⟩]) unmarked_context_12_25366_293770 node_context_12_25366_293770
  intro a
  fin_cases a
  · exact context_13_101464_293709
  · exact context_13_101465_293736
  · exact context_13_101466_293760
  · exact context_13_101467_293769

theorem selected_cut_10892 : selected 8 ⟨293804, by decide⟩
    (prefixPartial 13 101468) = some ⟨13, 2, 0, 293804, 101468, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_101468_293804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101468 ⟨293804, by decide⟩ :=
  accepted_of_selected 13 101468 ⟨293804, by decide⟩ ⟨13, 2, 0, 293804, 101468, 1785, 16384⟩
    (by decide) selected_cut_10892

theorem selected_cut_10893 : selected 8 ⟨293833, by decide⟩
    (prefixPartial 13 101469) = some ⟨13, 2, 0, 293833, 101469, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_101469_293833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101469 ⟨293833, by decide⟩ :=
  accepted_of_selected 13 101469 ⟨293833, by decide⟩ ⟨13, 2, 0, 293833, 101469, 2285, 16384⟩
    (by decide) selected_cut_10893

theorem selected_cut_10894 : selected 8 ⟨293852, by decide⟩
    (prefixPartial 13 101470) = some ⟨13, 2, 0, 293852, 101470, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_101470_293852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101470 ⟨293852, by decide⟩ :=
  accepted_of_selected 13 101470 ⟨293852, by decide⟩ ⟨13, 2, 0, 293852, 101470, 1757, 16384⟩
    (by decide) selected_cut_10894

theorem selected_cut_10895 : selected 8 ⟨293861, by decide⟩
    (prefixPartial 13 101471) = some ⟨13, 2, 0, 293861, 101471, 817, 16384⟩ := by
  decide +kernel

theorem context_13_101471_293861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101471 ⟨293861, by decide⟩ :=
  accepted_of_selected 13 101471 ⟨293861, by decide⟩ ⟨13, 2, 0, 293861, 101471, 817, 16384⟩
    (by decide) selected_cut_10895

theorem unmarked_context_12_25367_293862 : frontier 9 ⟨293862, by decide⟩
    (prefixCache 12 25367) (prefixPartial 12 25367) = false := by
  decide +kernel

theorem node_context_12_25367_293862 : EJMOriginalGlobalDAGData.nodes 9 ⟨293862, by decide⟩ =
    .split (coordinate 12) (![⟨293804, by decide⟩,⟨293833, by decide⟩,⟨293852, by decide⟩,⟨293861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25367_293862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25367 ⟨293862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25367
    ⟨293862, by decide⟩ (by decide) (![⟨293804, by decide⟩,⟨293833, by decide⟩,⟨293852, by decide⟩,⟨293861, by decide⟩]) unmarked_context_12_25367_293862 node_context_12_25367_293862
  intro a
  fin_cases a
  · exact context_13_101468_293804
  · exact context_13_101469_293833
  · exact context_13_101470_293852
  · exact context_13_101471_293861

theorem unmarked_context_11_6341_293863 : frontier 10 ⟨293863, by decide⟩
    (prefixCache 11 6341) (prefixPartial 11 6341) = false := by
  decide +kernel

theorem node_context_11_6341_293863 : EJMOriginalGlobalDAGData.nodes 10 ⟨293863, by decide⟩ =
    .split (coordinate 11) (![⟨293599, by decide⟩,⟨293682, by decide⟩,⟨293770, by decide⟩,⟨293862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6341_293863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6341 ⟨293863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6341
    ⟨293863, by decide⟩ (by decide) (![⟨293599, by decide⟩,⟨293682, by decide⟩,⟨293770, by decide⟩,⟨293862, by decide⟩]) unmarked_context_11_6341_293863 node_context_11_6341_293863
  intro a
  fin_cases a
  · exact context_12_25364_293599
  · exact context_12_25365_293682
  · exact context_12_25366_293770
  · exact context_12_25367_293862

theorem selected_cut_10896 : selected 8 ⟨293891, by decide⟩
    (prefixPartial 13 101472) = some ⟨13, 2, 0, 293891, 101472, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_101472_293891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101472 ⟨293891, by decide⟩ :=
  accepted_of_selected 13 101472 ⟨293891, by decide⟩ ⟨13, 2, 0, 293891, 101472, 1665, 16384⟩
    (by decide) selected_cut_10896

theorem selected_cut_10897 : selected 8 ⟨293915, by decide⟩
    (prefixPartial 13 101473) = some ⟨13, 2, 0, 293915, 101473, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_101473_293915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101473 ⟨293915, by decide⟩ :=
  accepted_of_selected 13 101473 ⟨293915, by decide⟩ ⟨13, 2, 0, 293915, 101473, 1773, 16384⟩
    (by decide) selected_cut_10897

theorem selected_cut_10898 : selected 8 ⟨293935, by decide⟩
    (prefixPartial 13 101474) = some ⟨13, 2, 0, 293935, 101474, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_101474_293935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101474 ⟨293935, by decide⟩ :=
  accepted_of_selected 13 101474 ⟨293935, by decide⟩ ⟨13, 2, 0, 293935, 101474, 1577, 16384⟩
    (by decide) selected_cut_10898

theorem selected_cut_10899 : selected 8 ⟨293940, by decide⟩
    (prefixPartial 13 101475) = some ⟨13, 2, 0, 293940, 101475, 641, 16384⟩ := by
  decide +kernel

theorem context_13_101475_293940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101475 ⟨293940, by decide⟩ :=
  accepted_of_selected 13 101475 ⟨293940, by decide⟩ ⟨13, 2, 0, 293940, 101475, 641, 16384⟩
    (by decide) selected_cut_10899

theorem unmarked_context_12_25368_293941 : frontier 9 ⟨293941, by decide⟩
    (prefixCache 12 25368) (prefixPartial 12 25368) = false := by
  decide +kernel

theorem node_context_12_25368_293941 : EJMOriginalGlobalDAGData.nodes 9 ⟨293941, by decide⟩ =
    .split (coordinate 12) (![⟨293891, by decide⟩,⟨293915, by decide⟩,⟨293935, by decide⟩,⟨293940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25368_293941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25368 ⟨293941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25368
    ⟨293941, by decide⟩ (by decide) (![⟨293891, by decide⟩,⟨293915, by decide⟩,⟨293935, by decide⟩,⟨293940, by decide⟩]) unmarked_context_12_25368_293941 node_context_12_25368_293941
  intro a
  fin_cases a
  · exact context_13_101472_293891
  · exact context_13_101473_293915
  · exact context_13_101474_293935
  · exact context_13_101475_293940

theorem selected_cut_10900 : selected 8 ⟨293964, by decide⟩
    (prefixPartial 13 101476) = some ⟨13, 2, 0, 293964, 101476, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_101476_293964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101476 ⟨293964, by decide⟩ :=
  accepted_of_selected 13 101476 ⟨293964, by decide⟩ ⟨13, 2, 0, 293964, 101476, 1525, 16384⟩
    (by decide) selected_cut_10900

theorem selected_cut_10901 : selected 8 ⟨293998, by decide⟩
    (prefixPartial 13 101477) = some ⟨13, 2, 0, 293998, 101477, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_101477_293998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101477 ⟨293998, by decide⟩ :=
  accepted_of_selected 13 101477 ⟨293998, by decide⟩ ⟨13, 2, 0, 293998, 101477, 2021, 16384⟩
    (by decide) selected_cut_10901

theorem selected_cut_10902 : selected 8 ⟨294020, by decide⟩
    (prefixPartial 13 101478) = some ⟨13, 2, 0, 294020, 101478, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_101478_294020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101478 ⟨294020, by decide⟩ :=
  accepted_of_selected 13 101478 ⟨294020, by decide⟩ ⟨13, 2, 0, 294020, 101478, 1617, 16384⟩
    (by decide) selected_cut_10902

theorem selected_cut_10903 : selected 8 ⟨294028, by decide⟩
    (prefixPartial 13 101479) = some ⟨13, 2, 0, 294028, 101479, 709, 16384⟩ := by
  decide +kernel

theorem context_13_101479_294028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101479 ⟨294028, by decide⟩ :=
  accepted_of_selected 13 101479 ⟨294028, by decide⟩ ⟨13, 2, 0, 294028, 101479, 709, 16384⟩
    (by decide) selected_cut_10903

theorem unmarked_context_12_25369_294029 : frontier 9 ⟨294029, by decide⟩
    (prefixCache 12 25369) (prefixPartial 12 25369) = false := by
  decide +kernel

theorem node_context_12_25369_294029 : EJMOriginalGlobalDAGData.nodes 9 ⟨294029, by decide⟩ =
    .split (coordinate 12) (![⟨293964, by decide⟩,⟨293998, by decide⟩,⟨294020, by decide⟩,⟨294028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25369_294029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25369 ⟨294029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25369
    ⟨294029, by decide⟩ (by decide) (![⟨293964, by decide⟩,⟨293998, by decide⟩,⟨294020, by decide⟩,⟨294028, by decide⟩]) unmarked_context_12_25369_294029 node_context_12_25369_294029
  intro a
  fin_cases a
  · exact context_13_101476_293964
  · exact context_13_101477_293998
  · exact context_13_101478_294020
  · exact context_13_101479_294028

theorem selected_cut_10904 : selected 8 ⟨294058, by decide⟩
    (prefixPartial 13 101480) = some ⟨13, 2, 0, 294058, 101480, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_101480_294058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101480 ⟨294058, by decide⟩ :=
  accepted_of_selected 13 101480 ⟨294058, by decide⟩ ⟨13, 2, 0, 294058, 101480, 1677, 16384⟩
    (by decide) selected_cut_10904

theorem selected_cut_10905 : selected 8 ⟨294085, by decide⟩
    (prefixPartial 13 101481) = some ⟨13, 2, 0, 294085, 101481, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_101481_294085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101481 ⟨294085, by decide⟩ :=
  accepted_of_selected 13 101481 ⟨294085, by decide⟩ ⟨13, 2, 0, 294085, 101481, 2009, 16384⟩
    (by decide) selected_cut_10905

theorem selected_cut_10906 : selected 8 ⟨294104, by decide⟩
    (prefixPartial 13 101482) = some ⟨13, 2, 0, 294104, 101482, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_101482_294104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101482 ⟨294104, by decide⟩ :=
  accepted_of_selected 13 101482 ⟨294104, by decide⟩ ⟨13, 2, 0, 294104, 101482, 1581, 16384⟩
    (by decide) selected_cut_10906

theorem selected_cut_10907 : selected 8 ⟨294111, by decide⟩
    (prefixPartial 13 101483) = some ⟨13, 2, 0, 294111, 101483, 653, 16384⟩ := by
  decide +kernel

theorem context_13_101483_294111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101483 ⟨294111, by decide⟩ :=
  accepted_of_selected 13 101483 ⟨294111, by decide⟩ ⟨13, 2, 0, 294111, 101483, 653, 16384⟩
    (by decide) selected_cut_10907

theorem unmarked_context_12_25370_294112 : frontier 9 ⟨294112, by decide⟩
    (prefixCache 12 25370) (prefixPartial 12 25370) = false := by
  decide +kernel

theorem node_context_12_25370_294112 : EJMOriginalGlobalDAGData.nodes 9 ⟨294112, by decide⟩ =
    .split (coordinate 12) (![⟨294058, by decide⟩,⟨294085, by decide⟩,⟨294104, by decide⟩,⟨294111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25370_294112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25370 ⟨294112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25370
    ⟨294112, by decide⟩ (by decide) (![⟨294058, by decide⟩,⟨294085, by decide⟩,⟨294104, by decide⟩,⟨294111, by decide⟩]) unmarked_context_12_25370_294112 node_context_12_25370_294112
  intro a
  fin_cases a
  · exact context_13_101480_294058
  · exact context_13_101481_294085
  · exact context_13_101482_294104
  · exact context_13_101483_294111

theorem selected_cut_10908 : selected 8 ⟨294136, by decide⟩
    (prefixPartial 13 101484) = some ⟨13, 2, 0, 294136, 101484, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_101484_294136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101484 ⟨294136, by decide⟩ :=
  accepted_of_selected 13 101484 ⟨294136, by decide⟩ ⟨13, 2, 0, 294136, 101484, 1601, 16384⟩
    (by decide) selected_cut_10908

theorem selected_cut_10909 : selected 8 ⟨294166, by decide⟩
    (prefixPartial 13 101485) = some ⟨13, 2, 0, 294166, 101485, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_101485_294166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101485 ⟨294166, by decide⟩ :=
  accepted_of_selected 13 101485 ⟨294166, by decide⟩ ⟨13, 2, 0, 294166, 101485, 2137, 16384⟩
    (by decide) selected_cut_10909

theorem selected_cut_10910 : selected 8 ⟨294186, by decide⟩
    (prefixPartial 13 101486) = some ⟨13, 2, 0, 294186, 101486, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_101486_294186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101486 ⟨294186, by decide⟩ :=
  accepted_of_selected 13 101486 ⟨294186, by decide⟩ ⟨13, 2, 0, 294186, 101486, 1517, 16384⟩
    (by decide) selected_cut_10910

theorem selected_cut_10911 : selected 8 ⟨294194, by decide⟩
    (prefixPartial 13 101487) = some ⟨13, 2, 0, 294194, 101487, 649, 16384⟩ := by
  decide +kernel

theorem context_13_101487_294194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101487 ⟨294194, by decide⟩ :=
  accepted_of_selected 13 101487 ⟨294194, by decide⟩ ⟨13, 2, 0, 294194, 101487, 649, 16384⟩
    (by decide) selected_cut_10911

theorem unmarked_context_12_25371_294195 : frontier 9 ⟨294195, by decide⟩
    (prefixCache 12 25371) (prefixPartial 12 25371) = false := by
  decide +kernel

theorem node_context_12_25371_294195 : EJMOriginalGlobalDAGData.nodes 9 ⟨294195, by decide⟩ =
    .split (coordinate 12) (![⟨294136, by decide⟩,⟨294166, by decide⟩,⟨294186, by decide⟩,⟨294194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25371_294195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25371 ⟨294195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25371
    ⟨294195, by decide⟩ (by decide) (![⟨294136, by decide⟩,⟨294166, by decide⟩,⟨294186, by decide⟩,⟨294194, by decide⟩]) unmarked_context_12_25371_294195 node_context_12_25371_294195
  intro a
  fin_cases a
  · exact context_13_101484_294136
  · exact context_13_101485_294166
  · exact context_13_101486_294186
  · exact context_13_101487_294194

theorem unmarked_context_11_6342_294196 : frontier 10 ⟨294196, by decide⟩
    (prefixCache 11 6342) (prefixPartial 11 6342) = false := by
  decide +kernel

theorem node_context_11_6342_294196 : EJMOriginalGlobalDAGData.nodes 10 ⟨294196, by decide⟩ =
    .split (coordinate 11) (![⟨293941, by decide⟩,⟨294029, by decide⟩,⟨294112, by decide⟩,⟨294195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6342_294196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6342 ⟨294196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6342
    ⟨294196, by decide⟩ (by decide) (![⟨293941, by decide⟩,⟨294029, by decide⟩,⟨294112, by decide⟩,⟨294195, by decide⟩]) unmarked_context_11_6342_294196 node_context_11_6342_294196
  intro a
  fin_cases a
  · exact context_12_25368_293941
  · exact context_12_25369_294029
  · exact context_12_25370_294112
  · exact context_12_25371_294195

theorem selected_cut_10912 : selected 8 ⟨294220, by decide⟩
    (prefixPartial 13 101488) = some ⟨13, 2, 0, 294220, 101488, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_101488_294220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101488 ⟨294220, by decide⟩ :=
  accepted_of_selected 13 101488 ⟨294220, by decide⟩ ⟨13, 2, 0, 294220, 101488, 1429, 16384⟩
    (by decide) selected_cut_10912

theorem selected_cut_10913 : selected 8 ⟨294240, by decide⟩
    (prefixPartial 13 101489) = some ⟨13, 2, 0, 294240, 101489, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_101489_294240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101489 ⟨294240, by decide⟩ :=
  accepted_of_selected 13 101489 ⟨294240, by decide⟩ ⟨13, 2, 0, 294240, 101489, 1541, 16384⟩
    (by decide) selected_cut_10913

theorem selected_cut_10914 : selected 8 ⟨294257, by decide⟩
    (prefixPartial 13 101490) = some ⟨13, 2, 0, 294257, 101490, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_101490_294257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101490 ⟨294257, by decide⟩ :=
  accepted_of_selected 13 101490 ⟨294257, by decide⟩ ⟨13, 2, 0, 294257, 101490, 1277, 16384⟩
    (by decide) selected_cut_10914

theorem selected_cut_10915 : selected 8 ⟨294261, by decide⟩
    (prefixPartial 13 101491) = some ⟨13, 2, 0, 294261, 101491, 633, 16384⟩ := by
  decide +kernel

theorem context_13_101491_294261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101491 ⟨294261, by decide⟩ :=
  accepted_of_selected 13 101491 ⟨294261, by decide⟩ ⟨13, 2, 0, 294261, 101491, 633, 16384⟩
    (by decide) selected_cut_10915

theorem unmarked_context_12_25372_294262 : frontier 9 ⟨294262, by decide⟩
    (prefixCache 12 25372) (prefixPartial 12 25372) = false := by
  decide +kernel

theorem node_context_12_25372_294262 : EJMOriginalGlobalDAGData.nodes 9 ⟨294262, by decide⟩ =
    .split (coordinate 12) (![⟨294220, by decide⟩,⟨294240, by decide⟩,⟨294257, by decide⟩,⟨294261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25372_294262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25372 ⟨294262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25372
    ⟨294262, by decide⟩ (by decide) (![⟨294220, by decide⟩,⟨294240, by decide⟩,⟨294257, by decide⟩,⟨294261, by decide⟩]) unmarked_context_12_25372_294262 node_context_12_25372_294262
  intro a
  fin_cases a
  · exact context_13_101488_294220
  · exact context_13_101489_294240
  · exact context_13_101490_294257
  · exact context_13_101491_294261

theorem selected_cut_10916 : selected 8 ⟨294283, by decide⟩
    (prefixPartial 13 101492) = some ⟨13, 2, 0, 294283, 101492, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_101492_294283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101492 ⟨294283, by decide⟩ :=
  accepted_of_selected 13 101492 ⟨294283, by decide⟩ ⟨13, 2, 0, 294283, 101492, 1477, 16384⟩
    (by decide) selected_cut_10916

theorem selected_cut_10917 : selected 8 ⟨294309, by decide⟩
    (prefixPartial 13 101493) = some ⟨13, 2, 0, 294309, 101493, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_101493_294309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101493 ⟨294309, by decide⟩ :=
  accepted_of_selected 13 101493 ⟨294309, by decide⟩ ⟨13, 2, 0, 294309, 101493, 1917, 16384⟩
    (by decide) selected_cut_10917

theorem selected_cut_10918 : selected 8 ⟨294328, by decide⟩
    (prefixPartial 13 101494) = some ⟨13, 2, 0, 294328, 101494, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_101494_294328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101494 ⟨294328, by decide⟩ :=
  accepted_of_selected 13 101494 ⟨294328, by decide⟩ ⟨13, 2, 0, 294328, 101494, 1597, 16384⟩
    (by decide) selected_cut_10918

theorem selected_cut_10919 : selected 8 ⟨294333, by decide⟩
    (prefixPartial 13 101495) = some ⟨13, 2, 0, 294333, 101495, 633, 16384⟩ := by
  decide +kernel

theorem context_13_101495_294333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101495 ⟨294333, by decide⟩ :=
  accepted_of_selected 13 101495 ⟨294333, by decide⟩ ⟨13, 2, 0, 294333, 101495, 633, 16384⟩
    (by decide) selected_cut_10919

theorem unmarked_context_12_25373_294334 : frontier 9 ⟨294334, by decide⟩
    (prefixCache 12 25373) (prefixPartial 12 25373) = false := by
  decide +kernel

theorem node_context_12_25373_294334 : EJMOriginalGlobalDAGData.nodes 9 ⟨294334, by decide⟩ =
    .split (coordinate 12) (![⟨294283, by decide⟩,⟨294309, by decide⟩,⟨294328, by decide⟩,⟨294333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25373_294334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25373 ⟨294334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25373
    ⟨294334, by decide⟩ (by decide) (![⟨294283, by decide⟩,⟨294309, by decide⟩,⟨294328, by decide⟩,⟨294333, by decide⟩]) unmarked_context_12_25373_294334 node_context_12_25373_294334
  intro a
  fin_cases a
  · exact context_13_101492_294283
  · exact context_13_101493_294309
  · exact context_13_101494_294328
  · exact context_13_101495_294333

theorem selected_cut_10920 : selected 8 ⟨294356, by decide⟩
    (prefixPartial 13 101496) = some ⟨13, 2, 0, 294356, 101496, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_101496_294356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101496 ⟨294356, by decide⟩ :=
  accepted_of_selected 13 101496 ⟨294356, by decide⟩ ⟨13, 2, 0, 294356, 101496, 1681, 16384⟩
    (by decide) selected_cut_10920

theorem selected_cut_10921 : selected 8 ⟨294387, by decide⟩
    (prefixPartial 13 101497) = some ⟨13, 2, 0, 294387, 101497, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_101497_294387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101497 ⟨294387, by decide⟩ :=
  accepted_of_selected 13 101497 ⟨294387, by decide⟩ ⟨13, 2, 0, 294387, 101497, 1981, 16384⟩
    (by decide) selected_cut_10921

theorem selected_cut_10922 : selected 8 ⟨294402, by decide⟩
    (prefixPartial 13 101498) = some ⟨13, 2, 0, 294402, 101498, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_101498_294402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101498 ⟨294402, by decide⟩ :=
  accepted_of_selected 13 101498 ⟨294402, by decide⟩ ⟨13, 2, 0, 294402, 101498, 1425, 16384⟩
    (by decide) selected_cut_10922

theorem selected_cut_10923 : selected 8 ⟨294408, by decide⟩
    (prefixPartial 13 101499) = some ⟨13, 2, 0, 294408, 101499, 645, 16384⟩ := by
  decide +kernel

theorem context_13_101499_294408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101499 ⟨294408, by decide⟩ :=
  accepted_of_selected 13 101499 ⟨294408, by decide⟩ ⟨13, 2, 0, 294408, 101499, 645, 16384⟩
    (by decide) selected_cut_10923

theorem unmarked_context_12_25374_294409 : frontier 9 ⟨294409, by decide⟩
    (prefixCache 12 25374) (prefixPartial 12 25374) = false := by
  decide +kernel

theorem node_context_12_25374_294409 : EJMOriginalGlobalDAGData.nodes 9 ⟨294409, by decide⟩ =
    .split (coordinate 12) (![⟨294356, by decide⟩,⟨294387, by decide⟩,⟨294402, by decide⟩,⟨294408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25374_294409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25374 ⟨294409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25374
    ⟨294409, by decide⟩ (by decide) (![⟨294356, by decide⟩,⟨294387, by decide⟩,⟨294402, by decide⟩,⟨294408, by decide⟩]) unmarked_context_12_25374_294409 node_context_12_25374_294409
  intro a
  fin_cases a
  · exact context_13_101496_294356
  · exact context_13_101497_294387
  · exact context_13_101498_294402
  · exact context_13_101499_294408

theorem selected_cut_10924 : selected 8 ⟨294451, by decide⟩
    (prefixPartial 13 101500) = some ⟨13, 2, 0, 294451, 101500, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_101500_294451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101500 ⟨294451, by decide⟩ :=
  accepted_of_selected 13 101500 ⟨294451, by decide⟩ ⟨13, 2, 0, 294451, 101500, 2549, 16384⟩
    (by decide) selected_cut_10924

theorem selected_cut_10925 : selected 8 ⟨294506, by decide⟩
    (prefixPartial 13 101501) = some ⟨13, 2, 0, 294506, 101501, 3593, 16384⟩ := by
  decide +kernel

theorem context_13_101501_294506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101501 ⟨294506, by decide⟩ :=
  accepted_of_selected 13 101501 ⟨294506, by decide⟩ ⟨13, 2, 0, 294506, 101501, 3593, 16384⟩
    (by decide) selected_cut_10925

theorem selected_cut_10926 : selected 8 ⟨294542, by decide⟩
    (prefixPartial 13 101502) = some ⟨13, 2, 0, 294542, 101502, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_101502_294542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101502 ⟨294542, by decide⟩ :=
  accepted_of_selected 13 101502 ⟨294542, by decide⟩ ⟨13, 2, 0, 294542, 101502, 2585, 16384⟩
    (by decide) selected_cut_10926

theorem selected_cut_10927 : selected 8 ⟨294570, by decide⟩
    (prefixPartial 13 101503) = some ⟨13, 2, 0, 294570, 101503, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_101503_294570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101503 ⟨294570, by decide⟩ :=
  accepted_of_selected 13 101503 ⟨294570, by decide⟩ ⟨13, 2, 0, 294570, 101503, 1133, 16384⟩
    (by decide) selected_cut_10927

theorem unmarked_context_12_25375_294571 : frontier 9 ⟨294571, by decide⟩
    (prefixCache 12 25375) (prefixPartial 12 25375) = false := by
  decide +kernel

theorem node_context_12_25375_294571 : EJMOriginalGlobalDAGData.nodes 9 ⟨294571, by decide⟩ =
    .split (coordinate 12) (![⟨294451, by decide⟩,⟨294506, by decide⟩,⟨294542, by decide⟩,⟨294570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25375_294571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25375 ⟨294571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25375
    ⟨294571, by decide⟩ (by decide) (![⟨294451, by decide⟩,⟨294506, by decide⟩,⟨294542, by decide⟩,⟨294570, by decide⟩]) unmarked_context_12_25375_294571 node_context_12_25375_294571
  intro a
  fin_cases a
  · exact context_13_101500_294451
  · exact context_13_101501_294506
  · exact context_13_101502_294542
  · exact context_13_101503_294570

theorem unmarked_context_11_6343_294572 : frontier 10 ⟨294572, by decide⟩
    (prefixCache 11 6343) (prefixPartial 11 6343) = false := by
  decide +kernel

theorem node_context_11_6343_294572 : EJMOriginalGlobalDAGData.nodes 10 ⟨294572, by decide⟩ =
    .split (coordinate 11) (![⟨294262, by decide⟩,⟨294334, by decide⟩,⟨294409, by decide⟩,⟨294571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6343_294572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6343 ⟨294572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6343
    ⟨294572, by decide⟩ (by decide) (![⟨294262, by decide⟩,⟨294334, by decide⟩,⟨294409, by decide⟩,⟨294571, by decide⟩]) unmarked_context_11_6343_294572 node_context_11_6343_294572
  intro a
  fin_cases a
  · exact context_12_25372_294262
  · exact context_12_25373_294334
  · exact context_12_25374_294409
  · exact context_12_25375_294571

theorem unmarked_context_10_1585_294573 : frontier 11 ⟨294573, by decide⟩
    (prefixCache 10 1585) (prefixPartial 10 1585) = false := by
  decide +kernel

theorem node_context_10_1585_294573 : EJMOriginalGlobalDAGData.nodes 11 ⟨294573, by decide⟩ =
    .split (coordinate 10) (![⟨293525, by decide⟩,⟨293863, by decide⟩,⟨294196, by decide⟩,⟨294572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1585_294573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1585 ⟨294573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1585
    ⟨294573, by decide⟩ (by decide) (![⟨293525, by decide⟩,⟨293863, by decide⟩,⟨294196, by decide⟩,⟨294572, by decide⟩]) unmarked_context_10_1585_294573 node_context_10_1585_294573
  intro a
  fin_cases a
  · exact context_11_6340_293525
  · exact context_11_6341_293863
  · exact context_11_6342_294196
  · exact context_11_6343_294572

theorem selected_cut_10928 : selected 9 ⟨294625, by decide⟩
    (prefixPartial 12 25376) = some ⟨12, 2, 0, 294625, 25376, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_25376_294625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25376 ⟨294625, by decide⟩ :=
  accepted_of_selected 12 25376 ⟨294625, by decide⟩ ⟨12, 2, 0, 294625, 25376, 3481, 65536⟩
    (by decide) selected_cut_10928

theorem selected_cut_10929 : selected 8 ⟨294637, by decide⟩
    (prefixPartial 13 101508) = some ⟨13, 2, 0, 294637, 101508, 817, 16384⟩ := by
  decide +kernel

theorem context_13_101508_294637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101508 ⟨294637, by decide⟩ :=
  accepted_of_selected 13 101508 ⟨294637, by decide⟩ ⟨13, 2, 0, 294637, 101508, 817, 16384⟩
    (by decide) selected_cut_10929

theorem selected_cut_10930 : selected 8 ⟨294671, by decide⟩
    (prefixPartial 13 101509) = some ⟨13, 2, 0, 294671, 101509, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_101509_294671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101509 ⟨294671, by decide⟩ :=
  accepted_of_selected 13 101509 ⟨294671, by decide⟩ ⟨13, 2, 0, 294671, 101509, 1861, 16384⟩
    (by decide) selected_cut_10930

theorem selected_cut_10931 : selected 8 ⟨294685, by decide⟩
    (prefixPartial 13 101510) = some ⟨13, 2, 0, 294685, 101510, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_101510_294685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101510 ⟨294685, by decide⟩ :=
  accepted_of_selected 13 101510 ⟨294685, by decide⟩ ⟨13, 2, 0, 294685, 101510, 1057, 16384⟩
    (by decide) selected_cut_10931

theorem selected_cut_10932 : selected 8 ⟨294689, by decide⟩
    (prefixPartial 13 101511) = some ⟨13, 2, 0, 294689, 101511, 601, 16384⟩ := by
  decide +kernel

theorem context_13_101511_294689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101511 ⟨294689, by decide⟩ :=
  accepted_of_selected 13 101511 ⟨294689, by decide⟩ ⟨13, 2, 0, 294689, 101511, 601, 16384⟩
    (by decide) selected_cut_10932

theorem unmarked_context_12_25377_294690 : frontier 9 ⟨294690, by decide⟩
    (prefixCache 12 25377) (prefixPartial 12 25377) = false := by
  decide +kernel

theorem node_context_12_25377_294690 : EJMOriginalGlobalDAGData.nodes 9 ⟨294690, by decide⟩ =
    .split (coordinate 12) (![⟨294637, by decide⟩,⟨294671, by decide⟩,⟨294685, by decide⟩,⟨294689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25377_294690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25377 ⟨294690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25377
    ⟨294690, by decide⟩ (by decide) (![⟨294637, by decide⟩,⟨294671, by decide⟩,⟨294685, by decide⟩,⟨294689, by decide⟩]) unmarked_context_12_25377_294690 node_context_12_25377_294690
  intro a
  fin_cases a
  · exact context_13_101508_294637
  · exact context_13_101509_294671
  · exact context_13_101510_294685
  · exact context_13_101511_294689

theorem selected_cut_10933 : selected 8 ⟨294700, by decide⟩
    (prefixPartial 13 101512) = some ⟨13, 2, 0, 294700, 101512, 789, 16384⟩ := by
  decide +kernel

theorem context_13_101512_294700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101512 ⟨294700, by decide⟩ :=
  accepted_of_selected 13 101512 ⟨294700, by decide⟩ ⟨13, 2, 0, 294700, 101512, 789, 16384⟩
    (by decide) selected_cut_10933

theorem selected_cut_10934 : selected 8 ⟨294735, by decide⟩
    (prefixPartial 13 101513) = some ⟨13, 2, 0, 294735, 101513, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_101513_294735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101513 ⟨294735, by decide⟩ :=
  accepted_of_selected 13 101513 ⟨294735, by decide⟩ ⟨13, 2, 0, 294735, 101513, 1873, 16384⟩
    (by decide) selected_cut_10934

theorem selected_cut_10935 : selected 8 ⟨294750, by decide⟩
    (prefixPartial 13 101514) = some ⟨13, 2, 0, 294750, 101514, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_101514_294750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101514 ⟨294750, by decide⟩ :=
  accepted_of_selected 13 101514 ⟨294750, by decide⟩ ⟨13, 2, 0, 294750, 101514, 1061, 16384⟩
    (by decide) selected_cut_10935

theorem selected_cut_10936 : selected 8 ⟨294755, by decide⟩
    (prefixPartial 13 101515) = some ⟨13, 2, 0, 294755, 101515, 581, 16384⟩ := by
  decide +kernel

theorem context_13_101515_294755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101515 ⟨294755, by decide⟩ :=
  accepted_of_selected 13 101515 ⟨294755, by decide⟩ ⟨13, 2, 0, 294755, 101515, 581, 16384⟩
    (by decide) selected_cut_10936

theorem unmarked_context_12_25378_294756 : frontier 9 ⟨294756, by decide⟩
    (prefixCache 12 25378) (prefixPartial 12 25378) = false := by
  decide +kernel

theorem node_context_12_25378_294756 : EJMOriginalGlobalDAGData.nodes 9 ⟨294756, by decide⟩ =
    .split (coordinate 12) (![⟨294700, by decide⟩,⟨294735, by decide⟩,⟨294750, by decide⟩,⟨294755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25378_294756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25378 ⟨294756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25378
    ⟨294756, by decide⟩ (by decide) (![⟨294700, by decide⟩,⟨294735, by decide⟩,⟨294750, by decide⟩,⟨294755, by decide⟩]) unmarked_context_12_25378_294756 node_context_12_25378_294756
  intro a
  fin_cases a
  · exact context_13_101512_294700
  · exact context_13_101513_294735
  · exact context_13_101514_294750
  · exact context_13_101515_294755

theorem selected_cut_10937 : selected 8 ⟨294770, by decide⟩
    (prefixPartial 13 101516) = some ⟨13, 2, 0, 294770, 101516, 777, 16384⟩ := by
  decide +kernel

theorem context_13_101516_294770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101516 ⟨294770, by decide⟩ :=
  accepted_of_selected 13 101516 ⟨294770, by decide⟩ ⟨13, 2, 0, 294770, 101516, 777, 16384⟩
    (by decide) selected_cut_10937

theorem selected_cut_10938 : selected 8 ⟨294802, by decide⟩
    (prefixPartial 13 101517) = some ⟨13, 2, 0, 294802, 101517, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_101517_294802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101517 ⟨294802, by decide⟩ :=
  accepted_of_selected 13 101517 ⟨294802, by decide⟩ ⟨13, 2, 0, 294802, 101517, 1825, 16384⟩
    (by decide) selected_cut_10938

theorem selected_cut_10939 : selected 8 ⟨294813, by decide⟩
    (prefixPartial 13 101518) = some ⟨13, 2, 0, 294813, 101518, 965, 16384⟩ := by
  decide +kernel

theorem context_13_101518_294813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101518 ⟨294813, by decide⟩ :=
  accepted_of_selected 13 101518 ⟨294813, by decide⟩ ⟨13, 2, 0, 294813, 101518, 965, 16384⟩
    (by decide) selected_cut_10939

theorem selected_cut_10940 : selected 8 ⟨294817, by decide⟩
    (prefixPartial 13 101519) = some ⟨13, 2, 0, 294817, 101519, 573, 16384⟩ := by
  decide +kernel

theorem context_13_101519_294817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101519 ⟨294817, by decide⟩ :=
  accepted_of_selected 13 101519 ⟨294817, by decide⟩ ⟨13, 2, 0, 294817, 101519, 573, 16384⟩
    (by decide) selected_cut_10940

theorem unmarked_context_12_25379_294818 : frontier 9 ⟨294818, by decide⟩
    (prefixCache 12 25379) (prefixPartial 12 25379) = false := by
  decide +kernel

theorem node_context_12_25379_294818 : EJMOriginalGlobalDAGData.nodes 9 ⟨294818, by decide⟩ =
    .split (coordinate 12) (![⟨294770, by decide⟩,⟨294802, by decide⟩,⟨294813, by decide⟩,⟨294817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25379_294818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25379 ⟨294818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25379
    ⟨294818, by decide⟩ (by decide) (![⟨294770, by decide⟩,⟨294802, by decide⟩,⟨294813, by decide⟩,⟨294817, by decide⟩]) unmarked_context_12_25379_294818 node_context_12_25379_294818
  intro a
  fin_cases a
  · exact context_13_101516_294770
  · exact context_13_101517_294802
  · exact context_13_101518_294813
  · exact context_13_101519_294817

theorem unmarked_context_11_6344_294819 : frontier 10 ⟨294819, by decide⟩
    (prefixCache 11 6344) (prefixPartial 11 6344) = false := by
  decide +kernel

theorem node_context_11_6344_294819 : EJMOriginalGlobalDAGData.nodes 10 ⟨294819, by decide⟩ =
    .split (coordinate 11) (![⟨294625, by decide⟩,⟨294690, by decide⟩,⟨294756, by decide⟩,⟨294818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6344_294819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6344 ⟨294819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6344
    ⟨294819, by decide⟩ (by decide) (![⟨294625, by decide⟩,⟨294690, by decide⟩,⟨294756, by decide⟩,⟨294818, by decide⟩]) unmarked_context_11_6344_294819 node_context_11_6344_294819
  intro a
  fin_cases a
  · exact context_12_25376_294625
  · exact context_12_25377_294690
  · exact context_12_25378_294756
  · exact context_12_25379_294818

theorem selected_cut_10941 : selected 8 ⟨294833, by decide⟩
    (prefixPartial 13 101520) = some ⟨13, 2, 0, 294833, 101520, 885, 16384⟩ := by
  decide +kernel

theorem context_13_101520_294833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101520 ⟨294833, by decide⟩ :=
  accepted_of_selected 13 101520 ⟨294833, by decide⟩ ⟨13, 2, 0, 294833, 101520, 885, 16384⟩
    (by decide) selected_cut_10941

theorem selected_cut_10942 : selected 8 ⟨294856, by decide⟩
    (prefixPartial 13 101521) = some ⟨13, 2, 0, 294856, 101521, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_101521_294856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101521 ⟨294856, by decide⟩ :=
  accepted_of_selected 13 101521 ⟨294856, by decide⟩ ⟨13, 2, 0, 294856, 101521, 2097, 16384⟩
    (by decide) selected_cut_10942

theorem selected_cut_10943 : selected 8 ⟨294873, by decide⟩
    (prefixPartial 13 101522) = some ⟨13, 2, 0, 294873, 101522, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_101522_294873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101522 ⟨294873, by decide⟩ :=
  accepted_of_selected 13 101522 ⟨294873, by decide⟩ ⟨13, 2, 0, 294873, 101522, 1225, 16384⟩
    (by decide) selected_cut_10943

theorem selected_cut_10944 : selected 8 ⟨294881, by decide⟩
    (prefixPartial 13 101523) = some ⟨13, 2, 0, 294881, 101523, 721, 16384⟩ := by
  decide +kernel

theorem context_13_101523_294881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101523 ⟨294881, by decide⟩ :=
  accepted_of_selected 13 101523 ⟨294881, by decide⟩ ⟨13, 2, 0, 294881, 101523, 721, 16384⟩
    (by decide) selected_cut_10944

theorem unmarked_context_12_25380_294882 : frontier 9 ⟨294882, by decide⟩
    (prefixCache 12 25380) (prefixPartial 12 25380) = false := by
  decide +kernel

theorem node_context_12_25380_294882 : EJMOriginalGlobalDAGData.nodes 9 ⟨294882, by decide⟩ =
    .split (coordinate 12) (![⟨294833, by decide⟩,⟨294856, by decide⟩,⟨294873, by decide⟩,⟨294881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25380_294882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25380 ⟨294882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25380
    ⟨294882, by decide⟩ (by decide) (![⟨294833, by decide⟩,⟨294856, by decide⟩,⟨294873, by decide⟩,⟨294881, by decide⟩]) unmarked_context_12_25380_294882 node_context_12_25380_294882
  intro a
  fin_cases a
  · exact context_13_101520_294833
  · exact context_13_101521_294856
  · exact context_13_101522_294873
  · exact context_13_101523_294881

theorem selected_cut_10945 : selected 8 ⟨294892, by decide⟩
    (prefixPartial 13 101524) = some ⟨13, 2, 0, 294892, 101524, 869, 16384⟩ := by
  decide +kernel

theorem context_13_101524_294892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101524 ⟨294892, by decide⟩ :=
  accepted_of_selected 13 101524 ⟨294892, by decide⟩ ⟨13, 2, 0, 294892, 101524, 869, 16384⟩
    (by decide) selected_cut_10945

theorem selected_cut_10946 : selected 8 ⟨294917, by decide⟩
    (prefixPartial 13 101525) = some ⟨13, 2, 0, 294917, 101525, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_101525_294917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101525 ⟨294917, by decide⟩ :=
  accepted_of_selected 13 101525 ⟨294917, by decide⟩ ⟨13, 2, 0, 294917, 101525, 2237, 16384⟩
    (by decide) selected_cut_10946

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
