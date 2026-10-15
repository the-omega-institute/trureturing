/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover010
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_01057 : selected 9 ⟨41832, by decide⟩
    (prefixPartial 12 4372) = some ⟨12, 2, 0, 41832, 4372, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_4372_41832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4372 ⟨41832, by decide⟩ :=
  accepted_of_selected 12 4372 ⟨41832, by decide⟩ ⟨12, 2, 0, 41832, 4372, 3945, 65536⟩
    (by decide) selected_cut_01057

theorem selected_cut_01058 : selected 8 ⟨41861, by decide⟩
    (prefixPartial 13 17492) = some ⟨13, 2, 0, 41861, 17492, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_17492_41861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17492 ⟨41861, by decide⟩ :=
  accepted_of_selected 13 17492 ⟨41861, by decide⟩ ⟨13, 2, 0, 41861, 17492, 1337, 16384⟩
    (by decide) selected_cut_01058

theorem selected_cut_01059 : selected 8 ⟨41891, by decide⟩
    (prefixPartial 13 17493) = some ⟨13, 2, 0, 41891, 17493, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_17493_41891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17493 ⟨41891, by decide⟩ :=
  accepted_of_selected 13 17493 ⟨41891, by decide⟩ ⟨13, 2, 0, 41891, 17493, 1805, 16384⟩
    (by decide) selected_cut_01059

theorem selected_cut_01060 : selected 8 ⟨41920, by decide⟩
    (prefixPartial 13 17494) = some ⟨13, 2, 0, 41920, 17494, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_17494_41920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17494 ⟨41920, by decide⟩ :=
  accepted_of_selected 13 17494 ⟨41920, by decide⟩ ⟨13, 2, 0, 41920, 17494, 2005, 16384⟩
    (by decide) selected_cut_01060

theorem selected_cut_01061 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 17495) = some ⟨13, 1, 0, 414, 17495, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17495_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17495 ⟨414, by decide⟩ :=
  accepted_of_selected 13 17495 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 17495, 1, 16384⟩
    (by decide) selected_cut_01061

theorem unmarked_context_12_4373_41921 : frontier 9 ⟨41921, by decide⟩
    (prefixCache 12 4373) (prefixPartial 12 4373) = false := by
  decide +kernel

theorem node_context_12_4373_41921 : EJMOriginalGlobalDAGData.nodes 9 ⟨41921, by decide⟩ =
    .split (coordinate 12) (![⟨41861, by decide⟩,⟨41891, by decide⟩,⟨41920, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4373_41921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4373 ⟨41921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4373
    ⟨41921, by decide⟩ (by decide) (![⟨41861, by decide⟩,⟨41891, by decide⟩,⟨41920, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_4373_41921 node_context_12_4373_41921
  intro a
  fin_cases a
  · exact context_13_17492_41861
  · exact context_13_17493_41891
  · exact context_13_17494_41920
  · exact context_13_17495_414

theorem selected_cut_01062 : selected 8 ⟨41963, by decide⟩
    (prefixPartial 13 17496) = some ⟨13, 2, 0, 41963, 17496, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_17496_41963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17496 ⟨41963, by decide⟩ :=
  accepted_of_selected 13 17496 ⟨41963, by decide⟩ ⟨13, 2, 0, 41963, 17496, 1681, 16384⟩
    (by decide) selected_cut_01062

theorem selected_cut_01063 : selected 8 ⟨42006, by decide⟩
    (prefixPartial 13 17497) = some ⟨13, 2, 0, 42006, 17497, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_17497_42006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17497 ⟨42006, by decide⟩ :=
  accepted_of_selected 13 17497 ⟨42006, by decide⟩ ⟨13, 2, 0, 42006, 17497, 2461, 16384⟩
    (by decide) selected_cut_01063

theorem selected_cut_01064 : selected 8 ⟨42029, by decide⟩
    (prefixPartial 13 17498) = some ⟨13, 2, 0, 42029, 17498, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_17498_42029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17498 ⟨42029, by decide⟩ :=
  accepted_of_selected 13 17498 ⟨42029, by decide⟩ ⟨13, 2, 0, 42029, 17498, 1561, 16384⟩
    (by decide) selected_cut_01064

theorem selected_cut_01065 : selected 8 ⟨42041, by decide⟩
    (prefixPartial 13 17499) = some ⟨13, 2, 0, 42041, 17499, 985, 16384⟩ := by
  decide +kernel

theorem context_13_17499_42041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17499 ⟨42041, by decide⟩ :=
  accepted_of_selected 13 17499 ⟨42041, by decide⟩ ⟨13, 2, 0, 42041, 17499, 985, 16384⟩
    (by decide) selected_cut_01065

theorem unmarked_context_12_4374_42042 : frontier 9 ⟨42042, by decide⟩
    (prefixCache 12 4374) (prefixPartial 12 4374) = false := by
  decide +kernel

theorem node_context_12_4374_42042 : EJMOriginalGlobalDAGData.nodes 9 ⟨42042, by decide⟩ =
    .split (coordinate 12) (![⟨41963, by decide⟩,⟨42006, by decide⟩,⟨42029, by decide⟩,⟨42041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4374_42042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4374 ⟨42042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4374
    ⟨42042, by decide⟩ (by decide) (![⟨41963, by decide⟩,⟨42006, by decide⟩,⟨42029, by decide⟩,⟨42041, by decide⟩]) unmarked_context_12_4374_42042 node_context_12_4374_42042
  intro a
  fin_cases a
  · exact context_13_17496_41963
  · exact context_13_17497_42006
  · exact context_13_17498_42029
  · exact context_13_17499_42041

theorem selected_cut_01066 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4375) = some ⟨12, 1, 0, 893, 4375, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4375_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4375 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4375 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4375, 1, 65536⟩
    (by decide) selected_cut_01066

theorem unmarked_context_11_1093_42043 : frontier 10 ⟨42043, by decide⟩
    (prefixCache 11 1093) (prefixPartial 11 1093) = false := by
  decide +kernel

theorem node_context_11_1093_42043 : EJMOriginalGlobalDAGData.nodes 10 ⟨42043, by decide⟩ =
    .split (coordinate 11) (![⟨41832, by decide⟩,⟨41921, by decide⟩,⟨42042, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1093_42043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1093 ⟨42043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1093
    ⟨42043, by decide⟩ (by decide) (![⟨41832, by decide⟩,⟨41921, by decide⟩,⟨42042, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1093_42043 node_context_11_1093_42043
  intro a
  fin_cases a
  · exact context_12_4372_41832
  · exact context_12_4373_41921
  · exact context_12_4374_42042
  · exact context_12_4375_893

theorem selected_cut_01067 : selected 8 ⟨42078, by decide⟩
    (prefixPartial 13 17504) = some ⟨13, 2, 0, 42078, 17504, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_17504_42078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17504 ⟨42078, by decide⟩ :=
  accepted_of_selected 13 17504 ⟨42078, by decide⟩ ⟨13, 2, 0, 42078, 17504, 1749, 16384⟩
    (by decide) selected_cut_01067

theorem selected_cut_01068 : selected 8 ⟨42145, by decide⟩
    (prefixPartial 13 17505) = some ⟨13, 2, 0, 42145, 17505, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_17505_42145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17505 ⟨42145, by decide⟩ :=
  accepted_of_selected 13 17505 ⟨42145, by decide⟩ ⟨13, 2, 0, 42145, 17505, 3457, 16384⟩
    (by decide) selected_cut_01068

theorem selected_cut_01069 : selected 8 ⟨42184, by decide⟩
    (prefixPartial 13 17506) = some ⟨13, 2, 0, 42184, 17506, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_17506_42184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17506 ⟨42184, by decide⟩ :=
  accepted_of_selected 13 17506 ⟨42184, by decide⟩ ⟨13, 2, 0, 42184, 17506, 2281, 16384⟩
    (by decide) selected_cut_01069

theorem selected_cut_01070 : selected 8 ⟨42202, by decide⟩
    (prefixPartial 13 17507) = some ⟨13, 2, 0, 42202, 17507, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_17507_42202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17507 ⟨42202, by decide⟩ :=
  accepted_of_selected 13 17507 ⟨42202, by decide⟩ ⟨13, 2, 0, 42202, 17507, 1069, 16384⟩
    (by decide) selected_cut_01070

theorem unmarked_context_12_4376_42203 : frontier 9 ⟨42203, by decide⟩
    (prefixCache 12 4376) (prefixPartial 12 4376) = false := by
  decide +kernel

theorem node_context_12_4376_42203 : EJMOriginalGlobalDAGData.nodes 9 ⟨42203, by decide⟩ =
    .split (coordinate 12) (![⟨42078, by decide⟩,⟨42145, by decide⟩,⟨42184, by decide⟩,⟨42202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4376_42203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4376 ⟨42203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4376
    ⟨42203, by decide⟩ (by decide) (![⟨42078, by decide⟩,⟨42145, by decide⟩,⟨42184, by decide⟩,⟨42202, by decide⟩]) unmarked_context_12_4376_42203 node_context_12_4376_42203
  intro a
  fin_cases a
  · exact context_13_17504_42078
  · exact context_13_17505_42145
  · exact context_13_17506_42184
  · exact context_13_17507_42202

theorem selected_cut_01071 : selected 8 ⟨42235, by decide⟩
    (prefixPartial 13 17508) = some ⟨13, 2, 0, 42235, 17508, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_17508_42235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17508 ⟨42235, by decide⟩ :=
  accepted_of_selected 13 17508 ⟨42235, by decide⟩ ⟨13, 2, 0, 42235, 17508, 1549, 16384⟩
    (by decide) selected_cut_01071

theorem selected_cut_01072 : selected 8 ⟨42272, by decide⟩
    (prefixPartial 13 17509) = some ⟨13, 2, 0, 42272, 17509, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_17509_42272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17509 ⟨42272, by decide⟩ :=
  accepted_of_selected 13 17509 ⟨42272, by decide⟩ ⟨13, 2, 0, 42272, 17509, 2169, 16384⟩
    (by decide) selected_cut_01072

theorem selected_cut_01073 : selected 8 ⟨42293, by decide⟩
    (prefixPartial 13 17510) = some ⟨13, 2, 0, 42293, 17510, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_17510_42293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17510 ⟨42293, by decide⟩ :=
  accepted_of_selected 13 17510 ⟨42293, by decide⟩ ⟨13, 2, 0, 42293, 17510, 1701, 16384⟩
    (by decide) selected_cut_01073

theorem selected_cut_01074 : selected 8 ⟨42303, by decide⟩
    (prefixPartial 13 17511) = some ⟨13, 2, 0, 42303, 17511, 933, 16384⟩ := by
  decide +kernel

theorem context_13_17511_42303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17511 ⟨42303, by decide⟩ :=
  accepted_of_selected 13 17511 ⟨42303, by decide⟩ ⟨13, 2, 0, 42303, 17511, 933, 16384⟩
    (by decide) selected_cut_01074

theorem unmarked_context_12_4377_42304 : frontier 9 ⟨42304, by decide⟩
    (prefixCache 12 4377) (prefixPartial 12 4377) = false := by
  decide +kernel

theorem node_context_12_4377_42304 : EJMOriginalGlobalDAGData.nodes 9 ⟨42304, by decide⟩ =
    .split (coordinate 12) (![⟨42235, by decide⟩,⟨42272, by decide⟩,⟨42293, by decide⟩,⟨42303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4377_42304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4377 ⟨42304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4377
    ⟨42304, by decide⟩ (by decide) (![⟨42235, by decide⟩,⟨42272, by decide⟩,⟨42293, by decide⟩,⟨42303, by decide⟩]) unmarked_context_12_4377_42304 node_context_12_4377_42304
  intro a
  fin_cases a
  · exact context_13_17508_42235
  · exact context_13_17509_42272
  · exact context_13_17510_42293
  · exact context_13_17511_42303

theorem selected_cut_01075 : selected 8 ⟨42341, by decide⟩
    (prefixPartial 13 17512) = some ⟨13, 2, 0, 42341, 17512, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_17512_42341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17512 ⟨42341, by decide⟩ :=
  accepted_of_selected 13 17512 ⟨42341, by decide⟩ ⟨13, 2, 0, 42341, 17512, 1813, 16384⟩
    (by decide) selected_cut_01075

theorem selected_cut_01076 : selected 8 ⟨42385, by decide⟩
    (prefixPartial 13 17513) = some ⟨13, 2, 0, 42385, 17513, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_17513_42385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17513 ⟨42385, by decide⟩ :=
  accepted_of_selected 13 17513 ⟨42385, by decide⟩ ⟨13, 2, 0, 42385, 17513, 2813, 16384⟩
    (by decide) selected_cut_01076

theorem selected_cut_01077 : selected 8 ⟨42406, by decide⟩
    (prefixPartial 13 17514) = some ⟨13, 2, 0, 42406, 17514, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_17514_42406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17514 ⟨42406, by decide⟩ :=
  accepted_of_selected 13 17514 ⟨42406, by decide⟩ ⟨13, 2, 0, 42406, 17514, 1653, 16384⟩
    (by decide) selected_cut_01077

theorem selected_cut_01078 : selected 8 ⟨42419, by decide⟩
    (prefixPartial 13 17515) = some ⟨13, 2, 0, 42419, 17515, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_17515_42419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17515 ⟨42419, by decide⟩ :=
  accepted_of_selected 13 17515 ⟨42419, by decide⟩ ⟨13, 2, 0, 42419, 17515, 1033, 16384⟩
    (by decide) selected_cut_01078

theorem unmarked_context_12_4378_42420 : frontier 9 ⟨42420, by decide⟩
    (prefixCache 12 4378) (prefixPartial 12 4378) = false := by
  decide +kernel

theorem node_context_12_4378_42420 : EJMOriginalGlobalDAGData.nodes 9 ⟨42420, by decide⟩ =
    .split (coordinate 12) (![⟨42341, by decide⟩,⟨42385, by decide⟩,⟨42406, by decide⟩,⟨42419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4378_42420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4378 ⟨42420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4378
    ⟨42420, by decide⟩ (by decide) (![⟨42341, by decide⟩,⟨42385, by decide⟩,⟨42406, by decide⟩,⟨42419, by decide⟩]) unmarked_context_12_4378_42420 node_context_12_4378_42420
  intro a
  fin_cases a
  · exact context_13_17512_42341
  · exact context_13_17513_42385
  · exact context_13_17514_42406
  · exact context_13_17515_42419

theorem selected_cut_01079 : selected 8 ⟨42457, by decide⟩
    (prefixPartial 13 17516) = some ⟨13, 2, 0, 42457, 17516, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_17516_42457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17516 ⟨42457, by decide⟩ :=
  accepted_of_selected 13 17516 ⟨42457, by decide⟩ ⟨13, 2, 0, 42457, 17516, 1749, 16384⟩
    (by decide) selected_cut_01079

theorem selected_cut_01080 : selected 8 ⟨42506, by decide⟩
    (prefixPartial 13 17517) = some ⟨13, 2, 0, 42506, 17517, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_17517_42506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17517 ⟨42506, by decide⟩ :=
  accepted_of_selected 13 17517 ⟨42506, by decide⟩ ⟨13, 2, 0, 42506, 17517, 2953, 16384⟩
    (by decide) selected_cut_01080

theorem selected_cut_01081 : selected 8 ⟨42532, by decide⟩
    (prefixPartial 13 17518) = some ⟨13, 2, 0, 42532, 17518, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_17518_42532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17518 ⟨42532, by decide⟩ :=
  accepted_of_selected 13 17518 ⟨42532, by decide⟩ ⟨13, 2, 0, 42532, 17518, 1877, 16384⟩
    (by decide) selected_cut_01081

theorem selected_cut_01082 : selected 8 ⟨42543, by decide⟩
    (prefixPartial 13 17519) = some ⟨13, 2, 0, 42543, 17519, 937, 16384⟩ := by
  decide +kernel

theorem context_13_17519_42543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17519 ⟨42543, by decide⟩ :=
  accepted_of_selected 13 17519 ⟨42543, by decide⟩ ⟨13, 2, 0, 42543, 17519, 937, 16384⟩
    (by decide) selected_cut_01082

theorem unmarked_context_12_4379_42544 : frontier 9 ⟨42544, by decide⟩
    (prefixCache 12 4379) (prefixPartial 12 4379) = false := by
  decide +kernel

theorem node_context_12_4379_42544 : EJMOriginalGlobalDAGData.nodes 9 ⟨42544, by decide⟩ =
    .split (coordinate 12) (![⟨42457, by decide⟩,⟨42506, by decide⟩,⟨42532, by decide⟩,⟨42543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4379_42544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4379 ⟨42544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4379
    ⟨42544, by decide⟩ (by decide) (![⟨42457, by decide⟩,⟨42506, by decide⟩,⟨42532, by decide⟩,⟨42543, by decide⟩]) unmarked_context_12_4379_42544 node_context_12_4379_42544
  intro a
  fin_cases a
  · exact context_13_17516_42457
  · exact context_13_17517_42506
  · exact context_13_17518_42532
  · exact context_13_17519_42543

theorem unmarked_context_11_1094_42545 : frontier 10 ⟨42545, by decide⟩
    (prefixCache 11 1094) (prefixPartial 11 1094) = false := by
  decide +kernel

theorem node_context_11_1094_42545 : EJMOriginalGlobalDAGData.nodes 10 ⟨42545, by decide⟩ =
    .split (coordinate 11) (![⟨42203, by decide⟩,⟨42304, by decide⟩,⟨42420, by decide⟩,⟨42544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1094_42545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1094 ⟨42545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1094
    ⟨42545, by decide⟩ (by decide) (![⟨42203, by decide⟩,⟨42304, by decide⟩,⟨42420, by decide⟩,⟨42544, by decide⟩]) unmarked_context_11_1094_42545 node_context_11_1094_42545
  intro a
  fin_cases a
  · exact context_12_4376_42203
  · exact context_12_4377_42304
  · exact context_12_4378_42420
  · exact context_12_4379_42544

theorem selected_cut_01083 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1095) = some ⟨11, 1, 0, 1736, 1095, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1095_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1095 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1095 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1095, 1, 262144⟩
    (by decide) selected_cut_01083

theorem unmarked_context_10_273_42546 : frontier 11 ⟨42546, by decide⟩
    (prefixCache 10 273) (prefixPartial 10 273) = false := by
  decide +kernel

theorem node_context_10_273_42546 : EJMOriginalGlobalDAGData.nodes 11 ⟨42546, by decide⟩ =
    .split (coordinate 10) (![⟨41741, by decide⟩,⟨42043, by decide⟩,⟨42545, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_273_42546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 273 ⟨42546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 273
    ⟨42546, by decide⟩ (by decide) (![⟨41741, by decide⟩,⟨42043, by decide⟩,⟨42545, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_273_42546 node_context_10_273_42546
  intro a
  fin_cases a
  · exact context_11_1092_41741
  · exact context_11_1093_42043
  · exact context_11_1094_42545
  · exact context_11_1095_1736

theorem selected_cut_01084 : selected 8 ⟨42576, by decide⟩
    (prefixPartial 13 17536) = some ⟨13, 2, 0, 42576, 17536, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_17536_42576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17536 ⟨42576, by decide⟩ :=
  accepted_of_selected 13 17536 ⟨42576, by decide⟩ ⟨13, 2, 0, 42576, 17536, 1297, 16384⟩
    (by decide) selected_cut_01084

theorem selected_cut_01085 : selected 8 ⟨42606, by decide⟩
    (prefixPartial 13 17537) = some ⟨13, 2, 0, 42606, 17537, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_17537_42606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17537 ⟨42606, by decide⟩ :=
  accepted_of_selected 13 17537 ⟨42606, by decide⟩ ⟨13, 2, 0, 42606, 17537, 2137, 16384⟩
    (by decide) selected_cut_01085

theorem selected_cut_01086 : selected 8 ⟨42627, by decide⟩
    (prefixPartial 13 17538) = some ⟨13, 2, 0, 42627, 17538, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_17538_42627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17538 ⟨42627, by decide⟩ :=
  accepted_of_selected 13 17538 ⟨42627, by decide⟩ ⟨13, 2, 0, 42627, 17538, 1517, 16384⟩
    (by decide) selected_cut_01086

theorem selected_cut_01087 : selected 8 ⟨42640, by decide⟩
    (prefixPartial 13 17539) = some ⟨13, 2, 0, 42640, 17539, 889, 16384⟩ := by
  decide +kernel

theorem context_13_17539_42640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17539 ⟨42640, by decide⟩ :=
  accepted_of_selected 13 17539 ⟨42640, by decide⟩ ⟨13, 2, 0, 42640, 17539, 889, 16384⟩
    (by decide) selected_cut_01087

theorem unmarked_context_12_4384_42641 : frontier 9 ⟨42641, by decide⟩
    (prefixCache 12 4384) (prefixPartial 12 4384) = false := by
  decide +kernel

theorem node_context_12_4384_42641 : EJMOriginalGlobalDAGData.nodes 9 ⟨42641, by decide⟩ =
    .split (coordinate 12) (![⟨42576, by decide⟩,⟨42606, by decide⟩,⟨42627, by decide⟩,⟨42640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4384_42641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4384 ⟨42641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4384
    ⟨42641, by decide⟩ (by decide) (![⟨42576, by decide⟩,⟨42606, by decide⟩,⟨42627, by decide⟩,⟨42640, by decide⟩]) unmarked_context_12_4384_42641 node_context_12_4384_42641
  intro a
  fin_cases a
  · exact context_13_17536_42576
  · exact context_13_17537_42606
  · exact context_13_17538_42627
  · exact context_13_17539_42640

theorem selected_cut_01088 : selected 8 ⟨42672, by decide⟩
    (prefixPartial 13 17540) = some ⟨13, 2, 0, 42672, 17540, 961, 16384⟩ := by
  decide +kernel

theorem context_13_17540_42672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17540 ⟨42672, by decide⟩ :=
  accepted_of_selected 13 17540 ⟨42672, by decide⟩ ⟨13, 2, 0, 42672, 17540, 961, 16384⟩
    (by decide) selected_cut_01088

theorem selected_cut_01089 : selected 8 ⟨42696, by decide⟩
    (prefixPartial 13 17541) = some ⟨13, 2, 0, 42696, 17541, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_17541_42696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17541 ⟨42696, by decide⟩ :=
  accepted_of_selected 13 17541 ⟨42696, by decide⟩ ⟨13, 2, 0, 42696, 17541, 1449, 16384⟩
    (by decide) selected_cut_01089

theorem selected_cut_01090 : selected 8 ⟨42717, by decide⟩
    (prefixPartial 13 17542) = some ⟨13, 2, 0, 42717, 17542, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_17542_42717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17542 ⟨42717, by decide⟩ :=
  accepted_of_selected 13 17542 ⟨42717, by decide⟩ ⟨13, 2, 0, 42717, 17542, 1245, 16384⟩
    (by decide) selected_cut_01090

theorem selected_cut_01091 : selected 8 ⟨42729, by decide⟩
    (prefixPartial 13 17543) = some ⟨13, 2, 0, 42729, 17543, 813, 16384⟩ := by
  decide +kernel

theorem context_13_17543_42729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17543 ⟨42729, by decide⟩ :=
  accepted_of_selected 13 17543 ⟨42729, by decide⟩ ⟨13, 2, 0, 42729, 17543, 813, 16384⟩
    (by decide) selected_cut_01091

theorem unmarked_context_12_4385_42730 : frontier 9 ⟨42730, by decide⟩
    (prefixCache 12 4385) (prefixPartial 12 4385) = false := by
  decide +kernel

theorem node_context_12_4385_42730 : EJMOriginalGlobalDAGData.nodes 9 ⟨42730, by decide⟩ =
    .split (coordinate 12) (![⟨42672, by decide⟩,⟨42696, by decide⟩,⟨42717, by decide⟩,⟨42729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4385_42730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4385 ⟨42730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4385
    ⟨42730, by decide⟩ (by decide) (![⟨42672, by decide⟩,⟨42696, by decide⟩,⟨42717, by decide⟩,⟨42729, by decide⟩]) unmarked_context_12_4385_42730 node_context_12_4385_42730
  intro a
  fin_cases a
  · exact context_13_17540_42672
  · exact context_13_17541_42696
  · exact context_13_17542_42717
  · exact context_13_17543_42729

theorem selected_cut_01092 : selected 8 ⟨42766, by decide⟩
    (prefixPartial 13 17544) = some ⟨13, 2, 0, 42766, 17544, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_17544_42766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17544 ⟨42766, by decide⟩ :=
  accepted_of_selected 13 17544 ⟨42766, by decide⟩ ⟨13, 2, 0, 42766, 17544, 1293, 16384⟩
    (by decide) selected_cut_01092

theorem selected_cut_01093 : selected 8 ⟨42803, by decide⟩
    (prefixPartial 13 17545) = some ⟨13, 2, 0, 42803, 17545, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_17545_42803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17545 ⟨42803, by decide⟩ :=
  accepted_of_selected 13 17545 ⟨42803, by decide⟩ ⟨13, 2, 0, 42803, 17545, 2209, 16384⟩
    (by decide) selected_cut_01093

theorem selected_cut_01094 : selected 8 ⟨42824, by decide⟩
    (prefixPartial 13 17546) = some ⟨13, 2, 0, 42824, 17546, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_17546_42824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17546 ⟨42824, by decide⟩ :=
  accepted_of_selected 13 17546 ⟨42824, by decide⟩ ⟨13, 2, 0, 42824, 17546, 1409, 16384⟩
    (by decide) selected_cut_01094

theorem selected_cut_01095 : selected 8 ⟨42835, by decide⟩
    (prefixPartial 13 17547) = some ⟨13, 2, 0, 42835, 17547, 929, 16384⟩ := by
  decide +kernel

theorem context_13_17547_42835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17547 ⟨42835, by decide⟩ :=
  accepted_of_selected 13 17547 ⟨42835, by decide⟩ ⟨13, 2, 0, 42835, 17547, 929, 16384⟩
    (by decide) selected_cut_01095

theorem unmarked_context_12_4386_42836 : frontier 9 ⟨42836, by decide⟩
    (prefixCache 12 4386) (prefixPartial 12 4386) = false := by
  decide +kernel

theorem node_context_12_4386_42836 : EJMOriginalGlobalDAGData.nodes 9 ⟨42836, by decide⟩ =
    .split (coordinate 12) (![⟨42766, by decide⟩,⟨42803, by decide⟩,⟨42824, by decide⟩,⟨42835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4386_42836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4386 ⟨42836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4386
    ⟨42836, by decide⟩ (by decide) (![⟨42766, by decide⟩,⟨42803, by decide⟩,⟨42824, by decide⟩,⟨42835, by decide⟩]) unmarked_context_12_4386_42836 node_context_12_4386_42836
  intro a
  fin_cases a
  · exact context_13_17544_42766
  · exact context_13_17545_42803
  · exact context_13_17546_42824
  · exact context_13_17547_42835

theorem selected_cut_01096 : selected 8 ⟨42864, by decide⟩
    (prefixPartial 13 17548) = some ⟨13, 2, 0, 42864, 17548, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_17548_42864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17548 ⟨42864, by decide⟩ :=
  accepted_of_selected 13 17548 ⟨42864, by decide⟩ ⟨13, 2, 0, 42864, 17548, 1265, 16384⟩
    (by decide) selected_cut_01096

theorem selected_cut_01097 : selected 8 ⟨42894, by decide⟩
    (prefixPartial 13 17549) = some ⟨13, 2, 0, 42894, 17549, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_17549_42894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17549 ⟨42894, by decide⟩ :=
  accepted_of_selected 13 17549 ⟨42894, by decide⟩ ⟨13, 2, 0, 42894, 17549, 2081, 16384⟩
    (by decide) selected_cut_01097

theorem selected_cut_01098 : selected 8 ⟨42916, by decide⟩
    (prefixPartial 13 17550) = some ⟨13, 2, 0, 42916, 17550, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_17550_42916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17550 ⟨42916, by decide⟩ :=
  accepted_of_selected 13 17550 ⟨42916, by decide⟩ ⟨13, 2, 0, 42916, 17550, 1433, 16384⟩
    (by decide) selected_cut_01098

theorem selected_cut_01099 : selected 8 ⟨42928, by decide⟩
    (prefixPartial 13 17551) = some ⟨13, 2, 0, 42928, 17551, 865, 16384⟩ := by
  decide +kernel

theorem context_13_17551_42928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17551 ⟨42928, by decide⟩ :=
  accepted_of_selected 13 17551 ⟨42928, by decide⟩ ⟨13, 2, 0, 42928, 17551, 865, 16384⟩
    (by decide) selected_cut_01099

theorem unmarked_context_12_4387_42929 : frontier 9 ⟨42929, by decide⟩
    (prefixCache 12 4387) (prefixPartial 12 4387) = false := by
  decide +kernel

theorem node_context_12_4387_42929 : EJMOriginalGlobalDAGData.nodes 9 ⟨42929, by decide⟩ =
    .split (coordinate 12) (![⟨42864, by decide⟩,⟨42894, by decide⟩,⟨42916, by decide⟩,⟨42928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4387_42929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4387 ⟨42929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4387
    ⟨42929, by decide⟩ (by decide) (![⟨42864, by decide⟩,⟨42894, by decide⟩,⟨42916, by decide⟩,⟨42928, by decide⟩]) unmarked_context_12_4387_42929 node_context_12_4387_42929
  intro a
  fin_cases a
  · exact context_13_17548_42864
  · exact context_13_17549_42894
  · exact context_13_17550_42916
  · exact context_13_17551_42928

theorem unmarked_context_11_1096_42930 : frontier 10 ⟨42930, by decide⟩
    (prefixCache 11 1096) (prefixPartial 11 1096) = false := by
  decide +kernel

theorem node_context_11_1096_42930 : EJMOriginalGlobalDAGData.nodes 10 ⟨42930, by decide⟩ =
    .split (coordinate 11) (![⟨42641, by decide⟩,⟨42730, by decide⟩,⟨42836, by decide⟩,⟨42929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1096_42930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1096 ⟨42930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1096
    ⟨42930, by decide⟩ (by decide) (![⟨42641, by decide⟩,⟨42730, by decide⟩,⟨42836, by decide⟩,⟨42929, by decide⟩]) unmarked_context_11_1096_42930 node_context_11_1096_42930
  intro a
  fin_cases a
  · exact context_12_4384_42641
  · exact context_12_4385_42730
  · exact context_12_4386_42836
  · exact context_12_4387_42929

theorem selected_cut_01100 : selected 8 ⟨42964, by decide⟩
    (prefixPartial 13 17552) = some ⟨13, 2, 0, 42964, 17552, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_17552_42964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17552 ⟨42964, by decide⟩ :=
  accepted_of_selected 13 17552 ⟨42964, by decide⟩ ⟨13, 2, 0, 42964, 17552, 1381, 16384⟩
    (by decide) selected_cut_01100

theorem selected_cut_01101 : selected 8 ⟨43005, by decide⟩
    (prefixPartial 13 17553) = some ⟨13, 2, 0, 43005, 17553, 2725, 16384⟩ := by
  decide +kernel

theorem context_13_17553_43005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17553 ⟨43005, by decide⟩ :=
  accepted_of_selected 13 17553 ⟨43005, by decide⟩ ⟨13, 2, 0, 43005, 17553, 2725, 16384⟩
    (by decide) selected_cut_01101

theorem selected_cut_01102 : selected 8 ⟨43034, by decide⟩
    (prefixPartial 13 17554) = some ⟨13, 2, 0, 43034, 17554, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_17554_43034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17554 ⟨43034, by decide⟩ :=
  accepted_of_selected 13 17554 ⟨43034, by decide⟩ ⟨13, 2, 0, 43034, 17554, 1905, 16384⟩
    (by decide) selected_cut_01102

theorem selected_cut_01103 : selected 8 ⟨43054, by decide⟩
    (prefixPartial 13 17555) = some ⟨13, 2, 0, 43054, 17555, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_17555_43054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17555 ⟨43054, by decide⟩ :=
  accepted_of_selected 13 17555 ⟨43054, by decide⟩ ⟨13, 2, 0, 43054, 17555, 1125, 16384⟩
    (by decide) selected_cut_01103

theorem unmarked_context_12_4388_43055 : frontier 9 ⟨43055, by decide⟩
    (prefixCache 12 4388) (prefixPartial 12 4388) = false := by
  decide +kernel

theorem node_context_12_4388_43055 : EJMOriginalGlobalDAGData.nodes 9 ⟨43055, by decide⟩ =
    .split (coordinate 12) (![⟨42964, by decide⟩,⟨43005, by decide⟩,⟨43034, by decide⟩,⟨43054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4388_43055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4388 ⟨43055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4388
    ⟨43055, by decide⟩ (by decide) (![⟨42964, by decide⟩,⟨43005, by decide⟩,⟨43034, by decide⟩,⟨43054, by decide⟩]) unmarked_context_12_4388_43055 node_context_12_4388_43055
  intro a
  fin_cases a
  · exact context_13_17552_42964
  · exact context_13_17553_43005
  · exact context_13_17554_43034
  · exact context_13_17555_43054

theorem selected_cut_01104 : selected 8 ⟨43086, by decide⟩
    (prefixPartial 13 17556) = some ⟨13, 2, 0, 43086, 17556, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_17556_43086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17556 ⟨43086, by decide⟩ :=
  accepted_of_selected 13 17556 ⟨43086, by decide⟩ ⟨13, 2, 0, 43086, 17556, 1801, 16384⟩
    (by decide) selected_cut_01104

theorem selected_cut_01105 : selected 8 ⟨43131, by decide⟩
    (prefixPartial 13 17557) = some ⟨13, 2, 0, 43131, 17557, 3769, 16384⟩ := by
  decide +kernel

theorem context_13_17557_43131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17557 ⟨43131, by decide⟩ :=
  accepted_of_selected 13 17557 ⟨43131, by decide⟩ ⟨13, 2, 0, 43131, 17557, 3769, 16384⟩
    (by decide) selected_cut_01105

theorem selected_cut_01106 : selected 8 ⟨43161, by decide⟩
    (prefixPartial 13 17558) = some ⟨13, 2, 0, 43161, 17558, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_17558_43161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17558 ⟨43161, by decide⟩ :=
  accepted_of_selected 13 17558 ⟨43161, by decide⟩ ⟨13, 2, 0, 43161, 17558, 2485, 16384⟩
    (by decide) selected_cut_01106

theorem selected_cut_01107 : selected 8 ⟨43182, by decide⟩
    (prefixPartial 13 17559) = some ⟨13, 2, 0, 43182, 17559, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_17559_43182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17559 ⟨43182, by decide⟩ :=
  accepted_of_selected 13 17559 ⟨43182, by decide⟩ ⟨13, 2, 0, 43182, 17559, 1341, 16384⟩
    (by decide) selected_cut_01107

theorem unmarked_context_12_4389_43183 : frontier 9 ⟨43183, by decide⟩
    (prefixCache 12 4389) (prefixPartial 12 4389) = false := by
  decide +kernel

theorem node_context_12_4389_43183 : EJMOriginalGlobalDAGData.nodes 9 ⟨43183, by decide⟩ =
    .split (coordinate 12) (![⟨43086, by decide⟩,⟨43131, by decide⟩,⟨43161, by decide⟩,⟨43182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4389_43183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4389 ⟨43183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4389
    ⟨43183, by decide⟩ (by decide) (![⟨43086, by decide⟩,⟨43131, by decide⟩,⟨43161, by decide⟩,⟨43182, by decide⟩]) unmarked_context_12_4389_43183 node_context_12_4389_43183
  intro a
  fin_cases a
  · exact context_13_17556_43086
  · exact context_13_17557_43131
  · exact context_13_17558_43161
  · exact context_13_17559_43182

theorem selected_cut_01108 : selected 8 ⟨43213, by decide⟩
    (prefixPartial 13 17560) = some ⟨13, 2, 0, 43213, 17560, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_17560_43213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17560 ⟨43213, by decide⟩ :=
  accepted_of_selected 13 17560 ⟨43213, by decide⟩ ⟨13, 2, 0, 43213, 17560, 1209, 16384⟩
    (by decide) selected_cut_01108

theorem selected_cut_01109 : selected 8 ⟨43248, by decide⟩
    (prefixPartial 13 17561) = some ⟨13, 2, 0, 43248, 17561, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_17561_43248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17561 ⟨43248, by decide⟩ :=
  accepted_of_selected 13 17561 ⟨43248, by decide⟩ ⟨13, 2, 0, 43248, 17561, 2817, 16384⟩
    (by decide) selected_cut_01109

theorem selected_cut_01110 : selected 8 ⟨43276, by decide⟩
    (prefixPartial 13 17562) = some ⟨13, 2, 0, 43276, 17562, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_17562_43276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17562 ⟨43276, by decide⟩ :=
  accepted_of_selected 13 17562 ⟨43276, by decide⟩ ⟨13, 2, 0, 43276, 17562, 1685, 16384⟩
    (by decide) selected_cut_01110

theorem selected_cut_01111 : selected 8 ⟨43288, by decide⟩
    (prefixPartial 13 17563) = some ⟨13, 2, 0, 43288, 17563, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_17563_43288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17563 ⟨43288, by decide⟩ :=
  accepted_of_selected 13 17563 ⟨43288, by decide⟩ ⟨13, 2, 0, 43288, 17563, 1109, 16384⟩
    (by decide) selected_cut_01111

theorem unmarked_context_12_4390_43289 : frontier 9 ⟨43289, by decide⟩
    (prefixCache 12 4390) (prefixPartial 12 4390) = false := by
  decide +kernel

theorem node_context_12_4390_43289 : EJMOriginalGlobalDAGData.nodes 9 ⟨43289, by decide⟩ =
    .split (coordinate 12) (![⟨43213, by decide⟩,⟨43248, by decide⟩,⟨43276, by decide⟩,⟨43288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4390_43289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4390 ⟨43289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4390
    ⟨43289, by decide⟩ (by decide) (![⟨43213, by decide⟩,⟨43248, by decide⟩,⟨43276, by decide⟩,⟨43288, by decide⟩]) unmarked_context_12_4390_43289 node_context_12_4390_43289
  intro a
  fin_cases a
  · exact context_13_17560_43213
  · exact context_13_17561_43248
  · exact context_13_17562_43276
  · exact context_13_17563_43288

theorem selected_cut_01112 : selected 8 ⟨43314, by decide⟩
    (prefixPartial 13 17564) = some ⟨13, 2, 0, 43314, 17564, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_17564_43314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17564 ⟨43314, by decide⟩ :=
  accepted_of_selected 13 17564 ⟨43314, by decide⟩ ⟨13, 2, 0, 43314, 17564, 1089, 16384⟩
    (by decide) selected_cut_01112

theorem selected_cut_01113 : selected 8 ⟨43348, by decide⟩
    (prefixPartial 13 17565) = some ⟨13, 2, 0, 43348, 17565, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_17565_43348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17565 ⟨43348, by decide⟩ :=
  accepted_of_selected 13 17565 ⟨43348, by decide⟩ ⟨13, 2, 0, 43348, 17565, 2745, 16384⟩
    (by decide) selected_cut_01113

theorem selected_cut_01114 : selected 8 ⟨43373, by decide⟩
    (prefixPartial 13 17566) = some ⟨13, 2, 0, 43373, 17566, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_17566_43373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17566 ⟨43373, by decide⟩ :=
  accepted_of_selected 13 17566 ⟨43373, by decide⟩ ⟨13, 2, 0, 43373, 17566, 1721, 16384⟩
    (by decide) selected_cut_01114

theorem selected_cut_01115 : selected 8 ⟨43385, by decide⟩
    (prefixPartial 13 17567) = some ⟨13, 2, 0, 43385, 17567, 957, 16384⟩ := by
  decide +kernel

theorem context_13_17567_43385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17567 ⟨43385, by decide⟩ :=
  accepted_of_selected 13 17567 ⟨43385, by decide⟩ ⟨13, 2, 0, 43385, 17567, 957, 16384⟩
    (by decide) selected_cut_01115

theorem unmarked_context_12_4391_43386 : frontier 9 ⟨43386, by decide⟩
    (prefixCache 12 4391) (prefixPartial 12 4391) = false := by
  decide +kernel

theorem node_context_12_4391_43386 : EJMOriginalGlobalDAGData.nodes 9 ⟨43386, by decide⟩ =
    .split (coordinate 12) (![⟨43314, by decide⟩,⟨43348, by decide⟩,⟨43373, by decide⟩,⟨43385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4391_43386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4391 ⟨43386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4391
    ⟨43386, by decide⟩ (by decide) (![⟨43314, by decide⟩,⟨43348, by decide⟩,⟨43373, by decide⟩,⟨43385, by decide⟩]) unmarked_context_12_4391_43386 node_context_12_4391_43386
  intro a
  fin_cases a
  · exact context_13_17564_43314
  · exact context_13_17565_43348
  · exact context_13_17566_43373
  · exact context_13_17567_43385

theorem unmarked_context_11_1097_43387 : frontier 10 ⟨43387, by decide⟩
    (prefixCache 11 1097) (prefixPartial 11 1097) = false := by
  decide +kernel

theorem node_context_11_1097_43387 : EJMOriginalGlobalDAGData.nodes 10 ⟨43387, by decide⟩ =
    .split (coordinate 11) (![⟨43055, by decide⟩,⟨43183, by decide⟩,⟨43289, by decide⟩,⟨43386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1097_43387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1097 ⟨43387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1097
    ⟨43387, by decide⟩ (by decide) (![⟨43055, by decide⟩,⟨43183, by decide⟩,⟨43289, by decide⟩,⟨43386, by decide⟩]) unmarked_context_11_1097_43387 node_context_11_1097_43387
  intro a
  fin_cases a
  · exact context_12_4388_43055
  · exact context_12_4389_43183
  · exact context_12_4390_43289
  · exact context_12_4391_43386

theorem selected_cut_01116 : selected 8 ⟨43407, by decide⟩
    (prefixPartial 13 17568) = some ⟨13, 2, 0, 43407, 17568, 813, 16384⟩ := by
  decide +kernel

theorem context_13_17568_43407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17568 ⟨43407, by decide⟩ :=
  accepted_of_selected 13 17568 ⟨43407, by decide⟩ ⟨13, 2, 0, 43407, 17568, 813, 16384⟩
    (by decide) selected_cut_01116

theorem selected_cut_01117 : selected 8 ⟨43454, by decide⟩
    (prefixPartial 13 17569) = some ⟨13, 2, 0, 43454, 17569, 3141, 16384⟩ := by
  decide +kernel

theorem context_13_17569_43454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17569 ⟨43454, by decide⟩ :=
  accepted_of_selected 13 17569 ⟨43454, by decide⟩ ⟨13, 2, 0, 43454, 17569, 3141, 16384⟩
    (by decide) selected_cut_01117

theorem selected_cut_01118 : selected 8 ⟨43485, by decide⟩
    (prefixPartial 13 17570) = some ⟨13, 2, 0, 43485, 17570, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_17570_43485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17570 ⟨43485, by decide⟩ :=
  accepted_of_selected 13 17570 ⟨43485, by decide⟩ ⟨13, 2, 0, 43485, 17570, 1993, 16384⟩
    (by decide) selected_cut_01118

theorem selected_cut_01119 : selected 8 ⟨43503, by decide⟩
    (prefixPartial 13 17571) = some ⟨13, 2, 0, 43503, 17571, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_17571_43503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17571 ⟨43503, by decide⟩ :=
  accepted_of_selected 13 17571 ⟨43503, by decide⟩ ⟨13, 2, 0, 43503, 17571, 1165, 16384⟩
    (by decide) selected_cut_01119

theorem unmarked_context_12_4392_43504 : frontier 9 ⟨43504, by decide⟩
    (prefixCache 12 4392) (prefixPartial 12 4392) = false := by
  decide +kernel

theorem node_context_12_4392_43504 : EJMOriginalGlobalDAGData.nodes 9 ⟨43504, by decide⟩ =
    .split (coordinate 12) (![⟨43407, by decide⟩,⟨43454, by decide⟩,⟨43485, by decide⟩,⟨43503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4392_43504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4392 ⟨43504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4392
    ⟨43504, by decide⟩ (by decide) (![⟨43407, by decide⟩,⟨43454, by decide⟩,⟨43485, by decide⟩,⟨43503, by decide⟩]) unmarked_context_12_4392_43504 node_context_12_4392_43504
  intro a
  fin_cases a
  · exact context_13_17568_43407
  · exact context_13_17569_43454
  · exact context_13_17570_43485
  · exact context_13_17571_43503

theorem selected_cut_01120 : selected 8 ⟨43522, by decide⟩
    (prefixPartial 13 17572) = some ⟨13, 2, 0, 43522, 17572, 749, 16384⟩ := by
  decide +kernel

theorem context_13_17572_43522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17572 ⟨43522, by decide⟩ :=
  accepted_of_selected 13 17572 ⟨43522, by decide⟩ ⟨13, 2, 0, 43522, 17572, 749, 16384⟩
    (by decide) selected_cut_01120

theorem selected_cut_01121 : selected 8 ⟨43561, by decide⟩
    (prefixPartial 13 17573) = some ⟨13, 2, 0, 43561, 17573, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_17573_43561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17573 ⟨43561, by decide⟩ :=
  accepted_of_selected 13 17573 ⟨43561, by decide⟩ ⟨13, 2, 0, 43561, 17573, 2161, 16384⟩
    (by decide) selected_cut_01121

theorem selected_cut_01122 : selected 8 ⟨43584, by decide⟩
    (prefixPartial 13 17574) = some ⟨13, 2, 0, 43584, 17574, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_17574_43584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17574 ⟨43584, by decide⟩ :=
  accepted_of_selected 13 17574 ⟨43584, by decide⟩ ⟨13, 2, 0, 43584, 17574, 1489, 16384⟩
    (by decide) selected_cut_01122

theorem selected_cut_01123 : selected 8 ⟨43591, by decide⟩
    (prefixPartial 13 17575) = some ⟨13, 2, 0, 43591, 17575, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_17575_43591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17575 ⟨43591, by decide⟩ :=
  accepted_of_selected 13 17575 ⟨43591, by decide⟩ ⟨13, 2, 0, 43591, 17575, 1105, 16384⟩
    (by decide) selected_cut_01123

theorem unmarked_context_12_4393_43592 : frontier 9 ⟨43592, by decide⟩
    (prefixCache 12 4393) (prefixPartial 12 4393) = false := by
  decide +kernel

theorem node_context_12_4393_43592 : EJMOriginalGlobalDAGData.nodes 9 ⟨43592, by decide⟩ =
    .split (coordinate 12) (![⟨43522, by decide⟩,⟨43561, by decide⟩,⟨43584, by decide⟩,⟨43591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4393_43592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4393 ⟨43592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4393
    ⟨43592, by decide⟩ (by decide) (![⟨43522, by decide⟩,⟨43561, by decide⟩,⟨43584, by decide⟩,⟨43591, by decide⟩]) unmarked_context_12_4393_43592 node_context_12_4393_43592
  intro a
  fin_cases a
  · exact context_13_17572_43522
  · exact context_13_17573_43561
  · exact context_13_17574_43584
  · exact context_13_17575_43591

theorem selected_cut_01124 : selected 8 ⟨43609, by decide⟩
    (prefixPartial 13 17576) = some ⟨13, 2, 0, 43609, 17576, 725, 16384⟩ := by
  decide +kernel

theorem context_13_17576_43609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17576 ⟨43609, by decide⟩ :=
  accepted_of_selected 13 17576 ⟨43609, by decide⟩ ⟨13, 2, 0, 43609, 17576, 725, 16384⟩
    (by decide) selected_cut_01124

theorem selected_cut_01125 : selected 8 ⟨43648, by decide⟩
    (prefixPartial 13 17577) = some ⟨13, 2, 0, 43648, 17577, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_17577_43648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17577 ⟨43648, by decide⟩ :=
  accepted_of_selected 13 17577 ⟨43648, by decide⟩ ⟨13, 2, 0, 43648, 17577, 2925, 16384⟩
    (by decide) selected_cut_01125

theorem selected_cut_01126 : selected 8 ⟨43670, by decide⟩
    (prefixPartial 13 17578) = some ⟨13, 2, 0, 43670, 17578, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_17578_43670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17578 ⟨43670, by decide⟩ :=
  accepted_of_selected 13 17578 ⟨43670, by decide⟩ ⟨13, 2, 0, 43670, 17578, 1541, 16384⟩
    (by decide) selected_cut_01126

theorem selected_cut_01127 : selected 8 ⟨43679, by decide⟩
    (prefixPartial 13 17579) = some ⟨13, 2, 0, 43679, 17579, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_17579_43679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17579 ⟨43679, by decide⟩ :=
  accepted_of_selected 13 17579 ⟨43679, by decide⟩ ⟨13, 2, 0, 43679, 17579, 1161, 16384⟩
    (by decide) selected_cut_01127

theorem unmarked_context_12_4394_43680 : frontier 9 ⟨43680, by decide⟩
    (prefixCache 12 4394) (prefixPartial 12 4394) = false := by
  decide +kernel

theorem node_context_12_4394_43680 : EJMOriginalGlobalDAGData.nodes 9 ⟨43680, by decide⟩ =
    .split (coordinate 12) (![⟨43609, by decide⟩,⟨43648, by decide⟩,⟨43670, by decide⟩,⟨43679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4394_43680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4394 ⟨43680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4394
    ⟨43680, by decide⟩ (by decide) (![⟨43609, by decide⟩,⟨43648, by decide⟩,⟨43670, by decide⟩,⟨43679, by decide⟩]) unmarked_context_12_4394_43680 node_context_12_4394_43680
  intro a
  fin_cases a
  · exact context_13_17576_43609
  · exact context_13_17577_43648
  · exact context_13_17578_43670
  · exact context_13_17579_43679

theorem selected_cut_01128 : selected 8 ⟨43692, by decide⟩
    (prefixPartial 13 17580) = some ⟨13, 2, 0, 43692, 17580, 645, 16384⟩ := by
  decide +kernel

theorem context_13_17580_43692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17580 ⟨43692, by decide⟩ :=
  accepted_of_selected 13 17580 ⟨43692, by decide⟩ ⟨13, 2, 0, 43692, 17580, 645, 16384⟩
    (by decide) selected_cut_01128

theorem selected_cut_01129 : selected 8 ⟨43732, by decide⟩
    (prefixPartial 13 17581) = some ⟨13, 2, 0, 43732, 17581, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_17581_43732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17581 ⟨43732, by decide⟩ :=
  accepted_of_selected 13 17581 ⟨43732, by decide⟩ ⟨13, 2, 0, 43732, 17581, 2893, 16384⟩
    (by decide) selected_cut_01129

theorem selected_cut_01130 : selected 8 ⟨43757, by decide⟩
    (prefixPartial 13 17582) = some ⟨13, 2, 0, 43757, 17582, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_17582_43757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17582 ⟨43757, by decide⟩ :=
  accepted_of_selected 13 17582 ⟨43757, by decide⟩ ⟨13, 2, 0, 43757, 17582, 1541, 16384⟩
    (by decide) selected_cut_01130

theorem selected_cut_01131 : selected 8 ⟨43769, by decide⟩
    (prefixPartial 13 17583) = some ⟨13, 2, 0, 43769, 17583, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_17583_43769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17583 ⟨43769, by decide⟩ :=
  accepted_of_selected 13 17583 ⟨43769, by decide⟩ ⟨13, 2, 0, 43769, 17583, 1165, 16384⟩
    (by decide) selected_cut_01131

theorem unmarked_context_12_4395_43770 : frontier 9 ⟨43770, by decide⟩
    (prefixCache 12 4395) (prefixPartial 12 4395) = false := by
  decide +kernel

theorem node_context_12_4395_43770 : EJMOriginalGlobalDAGData.nodes 9 ⟨43770, by decide⟩ =
    .split (coordinate 12) (![⟨43692, by decide⟩,⟨43732, by decide⟩,⟨43757, by decide⟩,⟨43769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4395_43770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4395 ⟨43770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4395
    ⟨43770, by decide⟩ (by decide) (![⟨43692, by decide⟩,⟨43732, by decide⟩,⟨43757, by decide⟩,⟨43769, by decide⟩]) unmarked_context_12_4395_43770 node_context_12_4395_43770
  intro a
  fin_cases a
  · exact context_13_17580_43692
  · exact context_13_17581_43732
  · exact context_13_17582_43757
  · exact context_13_17583_43769

theorem unmarked_context_11_1098_43771 : frontier 10 ⟨43771, by decide⟩
    (prefixCache 11 1098) (prefixPartial 11 1098) = false := by
  decide +kernel

theorem node_context_11_1098_43771 : EJMOriginalGlobalDAGData.nodes 10 ⟨43771, by decide⟩ =
    .split (coordinate 11) (![⟨43504, by decide⟩,⟨43592, by decide⟩,⟨43680, by decide⟩,⟨43770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1098_43771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1098 ⟨43771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1098
    ⟨43771, by decide⟩ (by decide) (![⟨43504, by decide⟩,⟨43592, by decide⟩,⟨43680, by decide⟩,⟨43770, by decide⟩]) unmarked_context_11_1098_43771 node_context_11_1098_43771
  intro a
  fin_cases a
  · exact context_12_4392_43504
  · exact context_12_4393_43592
  · exact context_12_4394_43680
  · exact context_12_4395_43770

theorem selected_cut_01132 : selected 8 ⟨43782, by decide⟩
    (prefixPartial 13 17584) = some ⟨13, 2, 0, 43782, 17584, 473, 16384⟩ := by
  decide +kernel

theorem context_13_17584_43782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17584 ⟨43782, by decide⟩ :=
  accepted_of_selected 13 17584 ⟨43782, by decide⟩ ⟨13, 2, 0, 43782, 17584, 473, 16384⟩
    (by decide) selected_cut_01132

theorem selected_cut_01133 : selected 8 ⟨43825, by decide⟩
    (prefixPartial 13 17585) = some ⟨13, 2, 0, 43825, 17585, 3385, 16384⟩ := by
  decide +kernel

theorem context_13_17585_43825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17585 ⟨43825, by decide⟩ :=
  accepted_of_selected 13 17585 ⟨43825, by decide⟩ ⟨13, 2, 0, 43825, 17585, 3385, 16384⟩
    (by decide) selected_cut_01133

theorem selected_cut_01134 : selected 8 ⟨43861, by decide⟩
    (prefixPartial 13 17586) = some ⟨13, 2, 0, 43861, 17586, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_17586_43861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17586 ⟨43861, by decide⟩ :=
  accepted_of_selected 13 17586 ⟨43861, by decide⟩ ⟨13, 2, 0, 43861, 17586, 2309, 16384⟩
    (by decide) selected_cut_01134

theorem selected_cut_01135 : selected 8 ⟨43877, by decide⟩
    (prefixPartial 13 17587) = some ⟨13, 2, 0, 43877, 17587, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_17587_43877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17587 ⟨43877, by decide⟩ :=
  accepted_of_selected 13 17587 ⟨43877, by decide⟩ ⟨13, 2, 0, 43877, 17587, 1225, 16384⟩
    (by decide) selected_cut_01135

theorem unmarked_context_12_4396_43878 : frontier 9 ⟨43878, by decide⟩
    (prefixCache 12 4396) (prefixPartial 12 4396) = false := by
  decide +kernel

theorem node_context_12_4396_43878 : EJMOriginalGlobalDAGData.nodes 9 ⟨43878, by decide⟩ =
    .split (coordinate 12) (![⟨43782, by decide⟩,⟨43825, by decide⟩,⟨43861, by decide⟩,⟨43877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4396_43878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4396 ⟨43878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4396
    ⟨43878, by decide⟩ (by decide) (![⟨43782, by decide⟩,⟨43825, by decide⟩,⟨43861, by decide⟩,⟨43877, by decide⟩]) unmarked_context_12_4396_43878 node_context_12_4396_43878
  intro a
  fin_cases a
  · exact context_13_17584_43782
  · exact context_13_17585_43825
  · exact context_13_17586_43861
  · exact context_13_17587_43877

theorem selected_cut_01136 : selected 8 ⟨43888, by decide⟩
    (prefixPartial 13 17588) = some ⟨13, 2, 0, 43888, 17588, 381, 16384⟩ := by
  decide +kernel

theorem context_13_17588_43888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17588 ⟨43888, by decide⟩ :=
  accepted_of_selected 13 17588 ⟨43888, by decide⟩ ⟨13, 2, 0, 43888, 17588, 381, 16384⟩
    (by decide) selected_cut_01136

theorem selected_cut_01137 : selected 8 ⟨43927, by decide⟩
    (prefixPartial 13 17589) = some ⟨13, 2, 0, 43927, 17589, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_17589_43927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17589 ⟨43927, by decide⟩ :=
  accepted_of_selected 13 17589 ⟨43927, by decide⟩ ⟨13, 2, 0, 43927, 17589, 2289, 16384⟩
    (by decide) selected_cut_01137

theorem selected_cut_01138 : selected 8 ⟨43946, by decide⟩
    (prefixPartial 13 17590) = some ⟨13, 2, 0, 43946, 17590, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_17590_43946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17590 ⟨43946, by decide⟩ :=
  accepted_of_selected 13 17590 ⟨43946, by decide⟩ ⟨13, 2, 0, 43946, 17590, 1929, 16384⟩
    (by decide) selected_cut_01138

theorem selected_cut_01139 : selected 8 ⟨43959, by decide⟩
    (prefixPartial 13 17591) = some ⟨13, 2, 0, 43959, 17591, 981, 16384⟩ := by
  decide +kernel

theorem context_13_17591_43959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17591 ⟨43959, by decide⟩ :=
  accepted_of_selected 13 17591 ⟨43959, by decide⟩ ⟨13, 2, 0, 43959, 17591, 981, 16384⟩
    (by decide) selected_cut_01139

theorem unmarked_context_12_4397_43960 : frontier 9 ⟨43960, by decide⟩
    (prefixCache 12 4397) (prefixPartial 12 4397) = false := by
  decide +kernel

theorem node_context_12_4397_43960 : EJMOriginalGlobalDAGData.nodes 9 ⟨43960, by decide⟩ =
    .split (coordinate 12) (![⟨43888, by decide⟩,⟨43927, by decide⟩,⟨43946, by decide⟩,⟨43959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4397_43960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4397 ⟨43960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4397
    ⟨43960, by decide⟩ (by decide) (![⟨43888, by decide⟩,⟨43927, by decide⟩,⟨43946, by decide⟩,⟨43959, by decide⟩]) unmarked_context_12_4397_43960 node_context_12_4397_43960
  intro a
  fin_cases a
  · exact context_13_17588_43888
  · exact context_13_17589_43927
  · exact context_13_17590_43946
  · exact context_13_17591_43959

theorem selected_cut_01140 : selected 8 ⟨43969, by decide⟩
    (prefixPartial 13 17592) = some ⟨13, 2, 0, 43969, 17592, 269, 16384⟩ := by
  decide +kernel

theorem context_13_17592_43969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17592 ⟨43969, by decide⟩ :=
  accepted_of_selected 13 17592 ⟨43969, by decide⟩ ⟨13, 2, 0, 43969, 17592, 269, 16384⟩
    (by decide) selected_cut_01140

theorem selected_cut_01141 : selected 8 ⟨44008, by decide⟩
    (prefixPartial 13 17593) = some ⟨13, 2, 0, 44008, 17593, 3129, 16384⟩ := by
  decide +kernel

theorem context_13_17593_44008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17593 ⟨44008, by decide⟩ :=
  accepted_of_selected 13 17593 ⟨44008, by decide⟩ ⟨13, 2, 0, 44008, 17593, 3129, 16384⟩
    (by decide) selected_cut_01141

theorem selected_cut_01142 : selected 8 ⟨44041, by decide⟩
    (prefixPartial 13 17594) = some ⟨13, 2, 0, 44041, 17594, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_17594_44041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17594 ⟨44041, by decide⟩ :=
  accepted_of_selected 13 17594 ⟨44041, by decide⟩ ⟨13, 2, 0, 44041, 17594, 2077, 16384⟩
    (by decide) selected_cut_01142

theorem selected_cut_01143 : selected 8 ⟨44054, by decide⟩
    (prefixPartial 13 17595) = some ⟨13, 2, 0, 44054, 17595, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_17595_44054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17595 ⟨44054, by decide⟩ :=
  accepted_of_selected 13 17595 ⟨44054, by decide⟩ ⟨13, 2, 0, 44054, 17595, 1077, 16384⟩
    (by decide) selected_cut_01143

theorem unmarked_context_12_4398_44055 : frontier 9 ⟨44055, by decide⟩
    (prefixCache 12 4398) (prefixPartial 12 4398) = false := by
  decide +kernel

theorem node_context_12_4398_44055 : EJMOriginalGlobalDAGData.nodes 9 ⟨44055, by decide⟩ =
    .split (coordinate 12) (![⟨43969, by decide⟩,⟨44008, by decide⟩,⟨44041, by decide⟩,⟨44054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4398_44055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4398 ⟨44055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4398
    ⟨44055, by decide⟩ (by decide) (![⟨43969, by decide⟩,⟨44008, by decide⟩,⟨44041, by decide⟩,⟨44054, by decide⟩]) unmarked_context_12_4398_44055 node_context_12_4398_44055
  intro a
  fin_cases a
  · exact context_13_17592_43969
  · exact context_13_17593_44008
  · exact context_13_17594_44041
  · exact context_13_17595_44054

theorem selected_cut_01144 : selected 8 ⟨44061, by decide⟩
    (prefixPartial 13 17596) = some ⟨13, 2, 0, 44061, 17596, 121, 16384⟩ := by
  decide +kernel

theorem context_13_17596_44061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17596 ⟨44061, by decide⟩ :=
  accepted_of_selected 13 17596 ⟨44061, by decide⟩ ⟨13, 2, 0, 44061, 17596, 121, 16384⟩
    (by decide) selected_cut_01144

theorem selected_cut_01145 : selected 8 ⟨44091, by decide⟩
    (prefixPartial 13 17597) = some ⟨13, 2, 0, 44091, 17597, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_17597_44091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17597 ⟨44091, by decide⟩ :=
  accepted_of_selected 13 17597 ⟨44091, by decide⟩ ⟨13, 2, 0, 44091, 17597, 3013, 16384⟩
    (by decide) selected_cut_01145

theorem selected_cut_01146 : selected 8 ⟨44119, by decide⟩
    (prefixPartial 13 17598) = some ⟨13, 2, 0, 44119, 17598, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_17598_44119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17598 ⟨44119, by decide⟩ :=
  accepted_of_selected 13 17598 ⟨44119, by decide⟩ ⟨13, 2, 0, 44119, 17598, 1957, 16384⟩
    (by decide) selected_cut_01146

theorem selected_cut_01147 : selected 8 ⟨44130, by decide⟩
    (prefixPartial 13 17599) = some ⟨13, 2, 0, 44130, 17599, 985, 16384⟩ := by
  decide +kernel

theorem context_13_17599_44130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17599 ⟨44130, by decide⟩ :=
  accepted_of_selected 13 17599 ⟨44130, by decide⟩ ⟨13, 2, 0, 44130, 17599, 985, 16384⟩
    (by decide) selected_cut_01147

theorem unmarked_context_12_4399_44131 : frontier 9 ⟨44131, by decide⟩
    (prefixCache 12 4399) (prefixPartial 12 4399) = false := by
  decide +kernel

theorem node_context_12_4399_44131 : EJMOriginalGlobalDAGData.nodes 9 ⟨44131, by decide⟩ =
    .split (coordinate 12) (![⟨44061, by decide⟩,⟨44091, by decide⟩,⟨44119, by decide⟩,⟨44130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4399_44131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4399 ⟨44131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4399
    ⟨44131, by decide⟩ (by decide) (![⟨44061, by decide⟩,⟨44091, by decide⟩,⟨44119, by decide⟩,⟨44130, by decide⟩]) unmarked_context_12_4399_44131 node_context_12_4399_44131
  intro a
  fin_cases a
  · exact context_13_17596_44061
  · exact context_13_17597_44091
  · exact context_13_17598_44119
  · exact context_13_17599_44130

theorem unmarked_context_11_1099_44132 : frontier 10 ⟨44132, by decide⟩
    (prefixCache 11 1099) (prefixPartial 11 1099) = false := by
  decide +kernel

theorem node_context_11_1099_44132 : EJMOriginalGlobalDAGData.nodes 10 ⟨44132, by decide⟩ =
    .split (coordinate 11) (![⟨43878, by decide⟩,⟨43960, by decide⟩,⟨44055, by decide⟩,⟨44131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1099_44132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1099 ⟨44132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1099
    ⟨44132, by decide⟩ (by decide) (![⟨43878, by decide⟩,⟨43960, by decide⟩,⟨44055, by decide⟩,⟨44131, by decide⟩]) unmarked_context_11_1099_44132 node_context_11_1099_44132
  intro a
  fin_cases a
  · exact context_12_4396_43878
  · exact context_12_4397_43960
  · exact context_12_4398_44055
  · exact context_12_4399_44131

theorem unmarked_context_10_274_44133 : frontier 11 ⟨44133, by decide⟩
    (prefixCache 10 274) (prefixPartial 10 274) = false := by
  decide +kernel

theorem node_context_10_274_44133 : EJMOriginalGlobalDAGData.nodes 11 ⟨44133, by decide⟩ =
    .split (coordinate 10) (![⟨42930, by decide⟩,⟨43387, by decide⟩,⟨43771, by decide⟩,⟨44132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_274_44133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 274 ⟨44133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 274
    ⟨44133, by decide⟩ (by decide) (![⟨42930, by decide⟩,⟨43387, by decide⟩,⟨43771, by decide⟩,⟨44132, by decide⟩]) unmarked_context_10_274_44133 node_context_10_274_44133
  intro a
  fin_cases a
  · exact context_11_1096_42930
  · exact context_11_1097_43387
  · exact context_11_1098_43771
  · exact context_11_1099_44132

theorem selected_cut_01148 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 275) = some ⟨10, 1, 0, 3440, 275, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_275_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 275 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 275 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 275, 1, 1048576⟩
    (by decide) selected_cut_01148

theorem unmarked_context_9_68_44134 : frontier 12 ⟨44134, by decide⟩
    (prefixCache 9 68) (prefixPartial 9 68) = false := by
  decide +kernel

theorem node_context_9_68_44134 : EJMOriginalGlobalDAGData.nodes 12 ⟨44134, by decide⟩ =
    .split (coordinate 9) (![⟨41501, by decide⟩,⟨42546, by decide⟩,⟨44133, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_68_44134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 68 ⟨44134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 68
    ⟨44134, by decide⟩ (by decide) (![⟨41501, by decide⟩,⟨42546, by decide⟩,⟨44133, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_68_44134 node_context_9_68_44134
  intro a
  fin_cases a
  · exact context_10_272_41501
  · exact context_10_273_42546
  · exact context_10_274_44133
  · exact context_10_275_3440

theorem selected_cut_01149 : selected 9 ⟨44190, by decide⟩
    (prefixPartial 12 4416) = some ⟨12, 2, 0, 44190, 4416, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_4416_44190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4416 ⟨44190, by decide⟩ :=
  accepted_of_selected 12 4416 ⟨44190, by decide⟩ ⟨12, 2, 0, 44190, 4416, 3333, 65536⟩
    (by decide) selected_cut_01149

theorem selected_cut_01150 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17668) = some ⟨13, 1, 0, 3444, 17668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17668, 1, 16384⟩
    (by decide) selected_cut_01150

theorem selected_cut_01151 : selected 8 ⟨44219, by decide⟩
    (prefixPartial 13 17669) = some ⟨13, 2, 0, 44219, 17669, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_17669_44219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17669 ⟨44219, by decide⟩ :=
  accepted_of_selected 13 17669 ⟨44219, by decide⟩ ⟨13, 2, 0, 44219, 17669, 1837, 16384⟩
    (by decide) selected_cut_01151

theorem selected_cut_01152 : selected 8 ⟨44267, by decide⟩
    (prefixPartial 13 17670) = some ⟨13, 2, 0, 44267, 17670, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_17670_44267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17670 ⟨44267, by decide⟩ :=
  accepted_of_selected 13 17670 ⟨44267, by decide⟩ ⟨13, 2, 0, 44267, 17670, 2361, 16384⟩
    (by decide) selected_cut_01152

theorem selected_cut_01153 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 17671) = some ⟨13, 1, 0, 414, 17671, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17671_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17671 ⟨414, by decide⟩ :=
  accepted_of_selected 13 17671 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 17671, 1, 16384⟩
    (by decide) selected_cut_01153

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
