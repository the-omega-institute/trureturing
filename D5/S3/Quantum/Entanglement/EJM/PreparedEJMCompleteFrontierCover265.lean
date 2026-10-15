/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover264
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_25443 : selected 7 ⟨643807, by decide⟩
    (prefixPartial 14 1400994) = some ⟨14, 2, 0, 643807, 1400994, 977, 4096⟩ := by
  decide +kernel

theorem context_14_1400994_643807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1400994 ⟨643807, by decide⟩ :=
  accepted_of_selected 14 1400994 ⟨643807, by decide⟩ ⟨14, 2, 0, 643807, 1400994, 977, 4096⟩
    (by decide) selected_cut_25443

theorem selected_cut_25444 : selected 7 ⟨643844, by decide⟩
    (prefixPartial 14 1400995) = some ⟨14, 2, 0, 643844, 1400995, 1481, 4096⟩ := by
  decide +kernel

theorem context_14_1400995_643844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1400995 ⟨643844, by decide⟩ :=
  accepted_of_selected 14 1400995 ⟨643844, by decide⟩ ⟨14, 2, 0, 643844, 1400995, 1481, 4096⟩
    (by decide) selected_cut_25444

theorem unmarked_context_13_350248_643845 : frontier 8 ⟨643845, by decide⟩
    (prefixCache 13 350248) (prefixPartial 13 350248) = false := by
  decide +kernel

theorem node_context_13_350248_643845 : EJMOriginalGlobalDAGData.nodes 8 ⟨643845, by decide⟩ =
    .split (coordinate 13) (![⟨643753, by decide⟩,⟨643785, by decide⟩,⟨643807, by decide⟩,⟨643844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_350248_643845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350248 ⟨643845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 350248
    ⟨643845, by decide⟩ (by decide) (![⟨643753, by decide⟩,⟨643785, by decide⟩,⟨643807, by decide⟩,⟨643844, by decide⟩]) unmarked_context_13_350248_643845 node_context_13_350248_643845
  intro a
  fin_cases a
  · exact context_14_1400992_643753
  · exact context_14_1400993_643785
  · exact context_14_1400994_643807
  · exact context_14_1400995_643844

theorem selected_cut_25445 : selected 8 ⟨643951, by decide⟩
    (prefixPartial 13 350249) = some ⟨13, 2, 0, 643951, 350249, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_350249_643951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350249 ⟨643951, by decide⟩ :=
  accepted_of_selected 13 350249 ⟨643951, by decide⟩ ⟨13, 2, 0, 643951, 350249, 2505, 16384⟩
    (by decide) selected_cut_25445

theorem selected_cut_25446 : selected 8 ⟨643961, by decide⟩
    (prefixPartial 13 350250) = some ⟨13, 2, 0, 643961, 350250, 649, 16384⟩ := by
  decide +kernel

theorem context_13_350250_643961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350250 ⟨643961, by decide⟩ :=
  accepted_of_selected 13 350250 ⟨643961, by decide⟩ ⟨13, 2, 0, 643961, 350250, 649, 16384⟩
    (by decide) selected_cut_25446

theorem selected_cut_25447 : selected 8 ⟨643969, by decide⟩
    (prefixPartial 13 350251) = some ⟨13, 2, 0, 643969, 350251, 169, 16384⟩ := by
  decide +kernel

theorem context_13_350251_643969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350251 ⟨643969, by decide⟩ :=
  accepted_of_selected 13 350251 ⟨643969, by decide⟩ ⟨13, 2, 0, 643969, 350251, 169, 16384⟩
    (by decide) selected_cut_25447

theorem unmarked_context_12_87562_643970 : frontier 9 ⟨643970, by decide⟩
    (prefixCache 12 87562) (prefixPartial 12 87562) = false := by
  decide +kernel

theorem node_context_12_87562_643970 : EJMOriginalGlobalDAGData.nodes 9 ⟨643970, by decide⟩ =
    .split (coordinate 12) (![⟨643845, by decide⟩,⟨643951, by decide⟩,⟨643961, by decide⟩,⟨643969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87562_643970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87562 ⟨643970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87562
    ⟨643970, by decide⟩ (by decide) (![⟨643845, by decide⟩,⟨643951, by decide⟩,⟨643961, by decide⟩,⟨643969, by decide⟩]) unmarked_context_12_87562_643970 node_context_12_87562_643970
  intro a
  fin_cases a
  · exact context_13_350248_643845
  · exact context_13_350249_643951
  · exact context_13_350250_643961
  · exact context_13_350251_643969

theorem selected_cut_25448 : selected 8 ⟨644037, by decide⟩
    (prefixPartial 13 350252) = some ⟨13, 2, 0, 644037, 350252, 3289, 16384⟩ := by
  decide +kernel

theorem context_13_350252_644037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350252 ⟨644037, by decide⟩ :=
  accepted_of_selected 13 350252 ⟨644037, by decide⟩ ⟨13, 2, 0, 644037, 350252, 3289, 16384⟩
    (by decide) selected_cut_25448

theorem selected_cut_25449 : selected 8 ⟨644112, by decide⟩
    (prefixPartial 13 350253) = some ⟨13, 2, 0, 644112, 350253, 3369, 16384⟩ := by
  decide +kernel

theorem context_13_350253_644112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350253 ⟨644112, by decide⟩ :=
  accepted_of_selected 13 350253 ⟨644112, by decide⟩ ⟨13, 2, 0, 644112, 350253, 3369, 16384⟩
    (by decide) selected_cut_25449

theorem selected_cut_25450 : selected 8 ⟨644135, by decide⟩
    (prefixPartial 13 350254) = some ⟨13, 2, 0, 644135, 350254, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_350254_644135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350254 ⟨644135, by decide⟩ :=
  accepted_of_selected 13 350254 ⟨644135, by decide⟩ ⟨13, 2, 0, 644135, 350254, 1617, 16384⟩
    (by decide) selected_cut_25450

theorem selected_cut_25451 : selected 8 ⟨644141, by decide⟩
    (prefixPartial 13 350255) = some ⟨13, 2, 0, 644141, 350255, 909, 16384⟩ := by
  decide +kernel

theorem context_13_350255_644141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350255 ⟨644141, by decide⟩ :=
  accepted_of_selected 13 350255 ⟨644141, by decide⟩ ⟨13, 2, 0, 644141, 350255, 909, 16384⟩
    (by decide) selected_cut_25451

theorem unmarked_context_12_87563_644142 : frontier 9 ⟨644142, by decide⟩
    (prefixCache 12 87563) (prefixPartial 12 87563) = false := by
  decide +kernel

theorem node_context_12_87563_644142 : EJMOriginalGlobalDAGData.nodes 9 ⟨644142, by decide⟩ =
    .split (coordinate 12) (![⟨644037, by decide⟩,⟨644112, by decide⟩,⟨644135, by decide⟩,⟨644141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87563_644142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87563 ⟨644142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87563
    ⟨644142, by decide⟩ (by decide) (![⟨644037, by decide⟩,⟨644112, by decide⟩,⟨644135, by decide⟩,⟨644141, by decide⟩]) unmarked_context_12_87563_644142 node_context_12_87563_644142
  intro a
  fin_cases a
  · exact context_13_350252_644037
  · exact context_13_350253_644112
  · exact context_13_350254_644135
  · exact context_13_350255_644141

theorem unmarked_context_11_21890_644143 : frontier 10 ⟨644143, by decide⟩
    (prefixCache 11 21890) (prefixPartial 11 21890) = false := by
  decide +kernel

theorem node_context_11_21890_644143 : EJMOriginalGlobalDAGData.nodes 10 ⟨644143, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨643970, by decide⟩,⟨644142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21890_644143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21890 ⟨644143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21890
    ⟨644143, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨643970, by decide⟩,⟨644142, by decide⟩]) unmarked_context_11_21890_644143 node_context_11_21890_644143
  intro a
  fin_cases a
  · exact context_12_87560_895
  · exact context_12_87561_895
  · exact context_12_87562_643970
  · exact context_12_87563_644142

theorem selected_cut_25452 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87564) = some ⟨12, 1, 0, 895, 87564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87564_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87564 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87564 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87564, 1, 65536⟩
    (by decide) selected_cut_25452

theorem selected_cut_25453 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87565) = some ⟨12, 1, 0, 895, 87565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87565_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87565 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87565 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87565, 1, 65536⟩
    (by decide) selected_cut_25453

theorem selected_cut_25454 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87566) = some ⟨12, 1, 0, 895, 87566, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87566_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87566 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87566 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87566, 1, 65536⟩
    (by decide) selected_cut_25454

theorem selected_cut_25455 : selected 8 ⟨644205, by decide⟩
    (prefixPartial 13 350268) = some ⟨13, 2, 0, 644205, 350268, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_350268_644205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350268 ⟨644205, by decide⟩ :=
  accepted_of_selected 13 350268 ⟨644205, by decide⟩ ⟨13, 2, 0, 644205, 350268, 3101, 16384⟩
    (by decide) selected_cut_25455

theorem selected_cut_25456 : selected 8 ⟨644251, by decide⟩
    (prefixPartial 13 350269) = some ⟨13, 2, 0, 644251, 350269, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_350269_644251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350269 ⟨644251, by decide⟩ :=
  accepted_of_selected 13 350269 ⟨644251, by decide⟩ ⟨13, 2, 0, 644251, 350269, 1701, 16384⟩
    (by decide) selected_cut_25456

theorem selected_cut_25457 : selected 8 ⟨644257, by decide⟩
    (prefixPartial 13 350270) = some ⟨13, 2, 0, 644257, 350270, 497, 16384⟩ := by
  decide +kernel

theorem context_13_350270_644257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350270 ⟨644257, by decide⟩ :=
  accepted_of_selected 13 350270 ⟨644257, by decide⟩ ⟨13, 2, 0, 644257, 350270, 497, 16384⟩
    (by decide) selected_cut_25457

theorem selected_cut_25458 : selected 8 ⟨644259, by decide⟩
    (prefixPartial 13 350271) = some ⟨13, 2, 0, 644259, 350271, 133, 16384⟩ := by
  decide +kernel

theorem context_13_350271_644259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350271 ⟨644259, by decide⟩ :=
  accepted_of_selected 13 350271 ⟨644259, by decide⟩ ⟨13, 2, 0, 644259, 350271, 133, 16384⟩
    (by decide) selected_cut_25458

theorem unmarked_context_12_87567_644260 : frontier 9 ⟨644260, by decide⟩
    (prefixCache 12 87567) (prefixPartial 12 87567) = false := by
  decide +kernel

theorem node_context_12_87567_644260 : EJMOriginalGlobalDAGData.nodes 9 ⟨644260, by decide⟩ =
    .split (coordinate 12) (![⟨644205, by decide⟩,⟨644251, by decide⟩,⟨644257, by decide⟩,⟨644259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87567_644260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87567 ⟨644260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87567
    ⟨644260, by decide⟩ (by decide) (![⟨644205, by decide⟩,⟨644251, by decide⟩,⟨644257, by decide⟩,⟨644259, by decide⟩]) unmarked_context_12_87567_644260 node_context_12_87567_644260
  intro a
  fin_cases a
  · exact context_13_350268_644205
  · exact context_13_350269_644251
  · exact context_13_350270_644257
  · exact context_13_350271_644259

theorem unmarked_context_11_21891_644261 : frontier 10 ⟨644261, by decide⟩
    (prefixCache 11 21891) (prefixPartial 11 21891) = false := by
  decide +kernel

theorem node_context_11_21891_644261 : EJMOriginalGlobalDAGData.nodes 10 ⟨644261, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨895, by decide⟩,⟨644260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21891_644261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21891 ⟨644261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21891
    ⟨644261, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨895, by decide⟩,⟨644260, by decide⟩]) unmarked_context_11_21891_644261 node_context_11_21891_644261
  intro a
  fin_cases a
  · exact context_12_87564_895
  · exact context_12_87565_895
  · exact context_12_87566_895
  · exact context_12_87567_644260

theorem unmarked_context_10_5472_644262 : frontier 11 ⟨644262, by decide⟩
    (prefixCache 10 5472) (prefixPartial 10 5472) = false := by
  decide +kernel

theorem node_context_10_5472_644262 : EJMOriginalGlobalDAGData.nodes 11 ⟨644262, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨643734, by decide⟩,⟨644143, by decide⟩,⟨644261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5472_644262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5472 ⟨644262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5472
    ⟨644262, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨643734, by decide⟩,⟨644143, by decide⟩,⟨644261, by decide⟩]) unmarked_context_10_5472_644262 node_context_10_5472_644262
  intro a
  fin_cases a
  · exact context_11_21888_434745
  · exact context_11_21889_643734
  · exact context_11_21890_644143
  · exact context_11_21891_644261

theorem selected_cut_25459 : selected 8 ⟨644284, by decide⟩
    (prefixPartial 13 350272) = some ⟨13, 2, 0, 644284, 350272, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_350272_644284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350272 ⟨644284, by decide⟩ :=
  accepted_of_selected 13 350272 ⟨644284, by decide⟩ ⟨13, 2, 0, 644284, 350272, 1777, 16384⟩
    (by decide) selected_cut_25459

theorem selected_cut_25460 : selected 8 ⟨644305, by decide⟩
    (prefixPartial 13 350273) = some ⟨13, 2, 0, 644305, 350273, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_350273_644305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350273 ⟨644305, by decide⟩ :=
  accepted_of_selected 13 350273 ⟨644305, by decide⟩ ⟨13, 2, 0, 644305, 350273, 1405, 16384⟩
    (by decide) selected_cut_25460

theorem selected_cut_25461 : selected 8 ⟨644323, by decide⟩
    (prefixPartial 13 350274) = some ⟨13, 2, 0, 644323, 350274, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_350274_644323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350274 ⟨644323, by decide⟩ :=
  accepted_of_selected 13 350274 ⟨644323, by decide⟩ ⟨13, 2, 0, 644323, 350274, 1393, 16384⟩
    (by decide) selected_cut_25461

theorem selected_cut_25462 : selected 8 ⟨644331, by decide⟩
    (prefixPartial 13 350275) = some ⟨13, 2, 0, 644331, 350275, 829, 16384⟩ := by
  decide +kernel

theorem context_13_350275_644331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350275 ⟨644331, by decide⟩ :=
  accepted_of_selected 13 350275 ⟨644331, by decide⟩ ⟨13, 2, 0, 644331, 350275, 829, 16384⟩
    (by decide) selected_cut_25462

theorem unmarked_context_12_87568_644332 : frontier 9 ⟨644332, by decide⟩
    (prefixCache 12 87568) (prefixPartial 12 87568) = false := by
  decide +kernel

theorem node_context_12_87568_644332 : EJMOriginalGlobalDAGData.nodes 9 ⟨644332, by decide⟩ =
    .split (coordinate 12) (![⟨644284, by decide⟩,⟨644305, by decide⟩,⟨644323, by decide⟩,⟨644331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87568_644332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87568 ⟨644332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87568
    ⟨644332, by decide⟩ (by decide) (![⟨644284, by decide⟩,⟨644305, by decide⟩,⟨644323, by decide⟩,⟨644331, by decide⟩]) unmarked_context_12_87568_644332 node_context_12_87568_644332
  intro a
  fin_cases a
  · exact context_13_350272_644284
  · exact context_13_350273_644305
  · exact context_13_350274_644323
  · exact context_13_350275_644331

theorem selected_cut_25463 : selected 8 ⟨644366, by decide⟩
    (prefixPartial 13 350276) = some ⟨13, 2, 0, 644366, 350276, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_350276_644366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350276 ⟨644366, by decide⟩ :=
  accepted_of_selected 13 350276 ⟨644366, by decide⟩ ⟨13, 2, 0, 644366, 350276, 1813, 16384⟩
    (by decide) selected_cut_25463

theorem selected_cut_25464 : selected 8 ⟨644385, by decide⟩
    (prefixPartial 13 350277) = some ⟨13, 2, 0, 644385, 350277, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_350277_644385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350277 ⟨644385, by decide⟩ :=
  accepted_of_selected 13 350277 ⟨644385, by decide⟩ ⟨13, 2, 0, 644385, 350277, 1385, 16384⟩
    (by decide) selected_cut_25464

theorem selected_cut_25465 : selected 8 ⟨644403, by decide⟩
    (prefixPartial 13 350278) = some ⟨13, 2, 0, 644403, 350278, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_350278_644403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350278 ⟨644403, by decide⟩ :=
  accepted_of_selected 13 350278 ⟨644403, by decide⟩ ⟨13, 2, 0, 644403, 350278, 1289, 16384⟩
    (by decide) selected_cut_25465

theorem selected_cut_25466 : selected 8 ⟨644408, by decide⟩
    (prefixPartial 13 350279) = some ⟨13, 2, 0, 644408, 350279, 849, 16384⟩ := by
  decide +kernel

theorem context_13_350279_644408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350279 ⟨644408, by decide⟩ :=
  accepted_of_selected 13 350279 ⟨644408, by decide⟩ ⟨13, 2, 0, 644408, 350279, 849, 16384⟩
    (by decide) selected_cut_25466

theorem unmarked_context_12_87569_644409 : frontier 9 ⟨644409, by decide⟩
    (prefixCache 12 87569) (prefixPartial 12 87569) = false := by
  decide +kernel

theorem node_context_12_87569_644409 : EJMOriginalGlobalDAGData.nodes 9 ⟨644409, by decide⟩ =
    .split (coordinate 12) (![⟨644366, by decide⟩,⟨644385, by decide⟩,⟨644403, by decide⟩,⟨644408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87569_644409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87569 ⟨644409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87569
    ⟨644409, by decide⟩ (by decide) (![⟨644366, by decide⟩,⟨644385, by decide⟩,⟨644403, by decide⟩,⟨644408, by decide⟩]) unmarked_context_12_87569_644409 node_context_12_87569_644409
  intro a
  fin_cases a
  · exact context_13_350276_644366
  · exact context_13_350277_644385
  · exact context_13_350278_644403
  · exact context_13_350279_644408

theorem selected_cut_25467 : selected 8 ⟨644434, by decide⟩
    (prefixPartial 13 350280) = some ⟨13, 2, 0, 644434, 350280, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_350280_644434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350280 ⟨644434, by decide⟩ :=
  accepted_of_selected 13 350280 ⟨644434, by decide⟩ ⟨13, 2, 0, 644434, 350280, 1701, 16384⟩
    (by decide) selected_cut_25467

theorem selected_cut_25468 : selected 8 ⟨644454, by decide⟩
    (prefixPartial 13 350281) = some ⟨13, 2, 0, 644454, 350281, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_350281_644454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350281 ⟨644454, by decide⟩ :=
  accepted_of_selected 13 350281 ⟨644454, by decide⟩ ⟨13, 2, 0, 644454, 350281, 1469, 16384⟩
    (by decide) selected_cut_25468

theorem selected_cut_25469 : selected 8 ⟨644471, by decide⟩
    (prefixPartial 13 350282) = some ⟨13, 2, 0, 644471, 350282, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_350282_644471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350282 ⟨644471, by decide⟩ :=
  accepted_of_selected 13 350282 ⟨644471, by decide⟩ ⟨13, 2, 0, 644471, 350282, 1157, 16384⟩
    (by decide) selected_cut_25469

theorem selected_cut_25470 : selected 8 ⟨644476, by decide⟩
    (prefixPartial 13 350283) = some ⟨13, 2, 0, 644476, 350283, 877, 16384⟩ := by
  decide +kernel

theorem context_13_350283_644476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350283 ⟨644476, by decide⟩ :=
  accepted_of_selected 13 350283 ⟨644476, by decide⟩ ⟨13, 2, 0, 644476, 350283, 877, 16384⟩
    (by decide) selected_cut_25470

theorem unmarked_context_12_87570_644477 : frontier 9 ⟨644477, by decide⟩
    (prefixCache 12 87570) (prefixPartial 12 87570) = false := by
  decide +kernel

theorem node_context_12_87570_644477 : EJMOriginalGlobalDAGData.nodes 9 ⟨644477, by decide⟩ =
    .split (coordinate 12) (![⟨644434, by decide⟩,⟨644454, by decide⟩,⟨644471, by decide⟩,⟨644476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87570_644477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87570 ⟨644477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87570
    ⟨644477, by decide⟩ (by decide) (![⟨644434, by decide⟩,⟨644454, by decide⟩,⟨644471, by decide⟩,⟨644476, by decide⟩]) unmarked_context_12_87570_644477 node_context_12_87570_644477
  intro a
  fin_cases a
  · exact context_13_350280_644434
  · exact context_13_350281_644454
  · exact context_13_350282_644471
  · exact context_13_350283_644476

theorem selected_cut_25471 : selected 8 ⟨644508, by decide⟩
    (prefixPartial 13 350284) = some ⟨13, 2, 0, 644508, 350284, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_350284_644508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350284 ⟨644508, by decide⟩ :=
  accepted_of_selected 13 350284 ⟨644508, by decide⟩ ⟨13, 2, 0, 644508, 350284, 2113, 16384⟩
    (by decide) selected_cut_25471

theorem selected_cut_25472 : selected 8 ⟨644530, by decide⟩
    (prefixPartial 13 350285) = some ⟨13, 2, 0, 644530, 350285, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_350285_644530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350285 ⟨644530, by decide⟩ :=
  accepted_of_selected 13 350285 ⟨644530, by decide⟩ ⟨13, 2, 0, 644530, 350285, 1721, 16384⟩
    (by decide) selected_cut_25472

theorem selected_cut_25473 : selected 8 ⟨644549, by decide⟩
    (prefixPartial 13 350286) = some ⟨13, 2, 0, 644549, 350286, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_350286_644549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350286 ⟨644549, by decide⟩ :=
  accepted_of_selected 13 350286 ⟨644549, by decide⟩ ⟨13, 2, 0, 644549, 350286, 1465, 16384⟩
    (by decide) selected_cut_25473

theorem selected_cut_25474 : selected 8 ⟨644554, by decide⟩
    (prefixPartial 13 350287) = some ⟨13, 2, 0, 644554, 350287, 793, 16384⟩ := by
  decide +kernel

theorem context_13_350287_644554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350287 ⟨644554, by decide⟩ :=
  accepted_of_selected 13 350287 ⟨644554, by decide⟩ ⟨13, 2, 0, 644554, 350287, 793, 16384⟩
    (by decide) selected_cut_25474

theorem unmarked_context_12_87571_644555 : frontier 9 ⟨644555, by decide⟩
    (prefixCache 12 87571) (prefixPartial 12 87571) = false := by
  decide +kernel

theorem node_context_12_87571_644555 : EJMOriginalGlobalDAGData.nodes 9 ⟨644555, by decide⟩ =
    .split (coordinate 12) (![⟨644508, by decide⟩,⟨644530, by decide⟩,⟨644549, by decide⟩,⟨644554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87571_644555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87571 ⟨644555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87571
    ⟨644555, by decide⟩ (by decide) (![⟨644508, by decide⟩,⟨644530, by decide⟩,⟨644549, by decide⟩,⟨644554, by decide⟩]) unmarked_context_12_87571_644555 node_context_12_87571_644555
  intro a
  fin_cases a
  · exact context_13_350284_644508
  · exact context_13_350285_644530
  · exact context_13_350286_644549
  · exact context_13_350287_644554

theorem unmarked_context_11_21892_644556 : frontier 10 ⟨644556, by decide⟩
    (prefixCache 11 21892) (prefixPartial 11 21892) = false := by
  decide +kernel

theorem node_context_11_21892_644556 : EJMOriginalGlobalDAGData.nodes 10 ⟨644556, by decide⟩ =
    .split (coordinate 11) (![⟨644332, by decide⟩,⟨644409, by decide⟩,⟨644477, by decide⟩,⟨644555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21892_644556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21892 ⟨644556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21892
    ⟨644556, by decide⟩ (by decide) (![⟨644332, by decide⟩,⟨644409, by decide⟩,⟨644477, by decide⟩,⟨644555, by decide⟩]) unmarked_context_11_21892_644556 node_context_11_21892_644556
  intro a
  fin_cases a
  · exact context_12_87568_644332
  · exact context_12_87569_644409
  · exact context_12_87570_644477
  · exact context_12_87571_644555

theorem selected_cut_25475 : selected 8 ⟨644596, by decide⟩
    (prefixPartial 13 350288) = some ⟨13, 2, 0, 644596, 350288, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_350288_644596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350288 ⟨644596, by decide⟩ :=
  accepted_of_selected 13 350288 ⟨644596, by decide⟩ ⟨13, 2, 0, 644596, 350288, 2281, 16384⟩
    (by decide) selected_cut_25475

theorem selected_cut_25476 : selected 8 ⟨644655, by decide⟩
    (prefixPartial 13 350289) = some ⟨13, 2, 0, 644655, 350289, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_350289_644655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350289 ⟨644655, by decide⟩ :=
  accepted_of_selected 13 350289 ⟨644655, by decide⟩ ⟨13, 2, 0, 644655, 350289, 2837, 16384⟩
    (by decide) selected_cut_25476

theorem selected_cut_25477 : selected 8 ⟨644680, by decide⟩
    (prefixPartial 13 350290) = some ⟨13, 2, 0, 644680, 350290, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_350290_644680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350290 ⟨644680, by decide⟩ :=
  accepted_of_selected 13 350290 ⟨644680, by decide⟩ ⟨13, 2, 0, 644680, 350290, 1829, 16384⟩
    (by decide) selected_cut_25477

theorem selected_cut_25478 : selected 8 ⟨644700, by decide⟩
    (prefixPartial 13 350291) = some ⟨13, 2, 0, 644700, 350291, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_350291_644700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350291 ⟨644700, by decide⟩ :=
  accepted_of_selected 13 350291 ⟨644700, by decide⟩ ⟨13, 2, 0, 644700, 350291, 1245, 16384⟩
    (by decide) selected_cut_25478

theorem unmarked_context_12_87572_644701 : frontier 9 ⟨644701, by decide⟩
    (prefixCache 12 87572) (prefixPartial 12 87572) = false := by
  decide +kernel

theorem node_context_12_87572_644701 : EJMOriginalGlobalDAGData.nodes 9 ⟨644701, by decide⟩ =
    .split (coordinate 12) (![⟨644596, by decide⟩,⟨644655, by decide⟩,⟨644680, by decide⟩,⟨644700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87572_644701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87572 ⟨644701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87572
    ⟨644701, by decide⟩ (by decide) (![⟨644596, by decide⟩,⟨644655, by decide⟩,⟨644680, by decide⟩,⟨644700, by decide⟩]) unmarked_context_12_87572_644701 node_context_12_87572_644701
  intro a
  fin_cases a
  · exact context_13_350288_644596
  · exact context_13_350289_644655
  · exact context_13_350290_644680
  · exact context_13_350291_644700

theorem selected_cut_25479 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 87573) = some ⟨12, 1, 0, 308705, 87573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87573_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87573 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 87573 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 87573, 1, 65536⟩
    (by decide) selected_cut_25479

theorem selected_cut_25480 : selected 8 ⟨644738, by decide⟩
    (prefixPartial 13 350296) = some ⟨13, 2, 0, 644738, 350296, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_350296_644738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350296 ⟨644738, by decide⟩ :=
  accepted_of_selected 13 350296 ⟨644738, by decide⟩ ⟨13, 2, 0, 644738, 350296, 2121, 16384⟩
    (by decide) selected_cut_25480

theorem selected_cut_25481 : selected 8 ⟨644784, by decide⟩
    (prefixPartial 13 350297) = some ⟨13, 2, 0, 644784, 350297, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_350297_644784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350297 ⟨644784, by decide⟩ :=
  accepted_of_selected 13 350297 ⟨644784, by decide⟩ ⟨13, 2, 0, 644784, 350297, 2365, 16384⟩
    (by decide) selected_cut_25481

theorem selected_cut_25482 : selected 8 ⟨644803, by decide⟩
    (prefixPartial 13 350298) = some ⟨13, 2, 0, 644803, 350298, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_350298_644803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350298 ⟨644803, by decide⟩ :=
  accepted_of_selected 13 350298 ⟨644803, by decide⟩ ⟨13, 2, 0, 644803, 350298, 1389, 16384⟩
    (by decide) selected_cut_25482

theorem selected_cut_25483 : selected 8 ⟨644816, by decide⟩
    (prefixPartial 13 350299) = some ⟨13, 2, 0, 644816, 350299, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_350299_644816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350299 ⟨644816, by decide⟩ :=
  accepted_of_selected 13 350299 ⟨644816, by decide⟩ ⟨13, 2, 0, 644816, 350299, 1181, 16384⟩
    (by decide) selected_cut_25483

theorem unmarked_context_12_87574_644817 : frontier 9 ⟨644817, by decide⟩
    (prefixCache 12 87574) (prefixPartial 12 87574) = false := by
  decide +kernel

theorem node_context_12_87574_644817 : EJMOriginalGlobalDAGData.nodes 9 ⟨644817, by decide⟩ =
    .split (coordinate 12) (![⟨644738, by decide⟩,⟨644784, by decide⟩,⟨644803, by decide⟩,⟨644816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87574_644817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87574 ⟨644817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87574
    ⟨644817, by decide⟩ (by decide) (![⟨644738, by decide⟩,⟨644784, by decide⟩,⟨644803, by decide⟩,⟨644816, by decide⟩]) unmarked_context_12_87574_644817 node_context_12_87574_644817
  intro a
  fin_cases a
  · exact context_13_350296_644738
  · exact context_13_350297_644784
  · exact context_13_350298_644803
  · exact context_13_350299_644816

theorem selected_cut_25484 : selected 8 ⟨644854, by decide⟩
    (prefixPartial 13 350300) = some ⟨13, 2, 0, 644854, 350300, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_350300_644854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350300 ⟨644854, by decide⟩ :=
  accepted_of_selected 13 350300 ⟨644854, by decide⟩ ⟨13, 2, 0, 644854, 350300, 2361, 16384⟩
    (by decide) selected_cut_25484

theorem selected_cut_25485 : selected 8 ⟨644903, by decide⟩
    (prefixPartial 13 350301) = some ⟨13, 2, 0, 644903, 350301, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_350301_644903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350301 ⟨644903, by decide⟩ :=
  accepted_of_selected 13 350301 ⟨644903, by decide⟩ ⟨13, 2, 0, 644903, 350301, 2561, 16384⟩
    (by decide) selected_cut_25485

theorem selected_cut_25486 : selected 8 ⟨644925, by decide⟩
    (prefixPartial 13 350302) = some ⟨13, 2, 0, 644925, 350302, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_350302_644925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350302 ⟨644925, by decide⟩ :=
  accepted_of_selected 13 350302 ⟨644925, by decide⟩ ⟨13, 2, 0, 644925, 350302, 1789, 16384⟩
    (by decide) selected_cut_25486

theorem selected_cut_25487 : selected 8 ⟨644933, by decide⟩
    (prefixPartial 13 350303) = some ⟨13, 2, 0, 644933, 350303, 981, 16384⟩ := by
  decide +kernel

theorem context_13_350303_644933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350303 ⟨644933, by decide⟩ :=
  accepted_of_selected 13 350303 ⟨644933, by decide⟩ ⟨13, 2, 0, 644933, 350303, 981, 16384⟩
    (by decide) selected_cut_25487

theorem unmarked_context_12_87575_644934 : frontier 9 ⟨644934, by decide⟩
    (prefixCache 12 87575) (prefixPartial 12 87575) = false := by
  decide +kernel

theorem node_context_12_87575_644934 : EJMOriginalGlobalDAGData.nodes 9 ⟨644934, by decide⟩ =
    .split (coordinate 12) (![⟨644854, by decide⟩,⟨644903, by decide⟩,⟨644925, by decide⟩,⟨644933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87575_644934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87575 ⟨644934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87575
    ⟨644934, by decide⟩ (by decide) (![⟨644854, by decide⟩,⟨644903, by decide⟩,⟨644925, by decide⟩,⟨644933, by decide⟩]) unmarked_context_12_87575_644934 node_context_12_87575_644934
  intro a
  fin_cases a
  · exact context_13_350300_644854
  · exact context_13_350301_644903
  · exact context_13_350302_644925
  · exact context_13_350303_644933

theorem unmarked_context_11_21893_644935 : frontier 10 ⟨644935, by decide⟩
    (prefixCache 11 21893) (prefixPartial 11 21893) = false := by
  decide +kernel

theorem node_context_11_21893_644935 : EJMOriginalGlobalDAGData.nodes 10 ⟨644935, by decide⟩ =
    .split (coordinate 11) (![⟨644701, by decide⟩,⟨308705, by decide⟩,⟨644817, by decide⟩,⟨644934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21893_644935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21893 ⟨644935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21893
    ⟨644935, by decide⟩ (by decide) (![⟨644701, by decide⟩,⟨308705, by decide⟩,⟨644817, by decide⟩,⟨644934, by decide⟩]) unmarked_context_11_21893_644935 node_context_11_21893_644935
  intro a
  fin_cases a
  · exact context_12_87572_644701
  · exact context_12_87573_308705
  · exact context_12_87574_644817
  · exact context_12_87575_644934

theorem selected_cut_25488 : selected 8 ⟨644956, by decide⟩
    (prefixPartial 13 350304) = some ⟨13, 2, 0, 644956, 350304, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_350304_644956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350304 ⟨644956, by decide⟩ :=
  accepted_of_selected 13 350304 ⟨644956, by decide⟩ ⟨13, 2, 0, 644956, 350304, 1529, 16384⟩
    (by decide) selected_cut_25488

theorem selected_cut_25489 : selected 8 ⟨644977, by decide⟩
    (prefixPartial 13 350305) = some ⟨13, 2, 0, 644977, 350305, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_350305_644977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350305 ⟨644977, by decide⟩ :=
  accepted_of_selected 13 350305 ⟨644977, by decide⟩ ⟨13, 2, 0, 644977, 350305, 1405, 16384⟩
    (by decide) selected_cut_25489

theorem selected_cut_25490 : selected 8 ⟨644995, by decide⟩
    (prefixPartial 13 350306) = some ⟨13, 2, 0, 644995, 350306, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_350306_644995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350306 ⟨644995, by decide⟩ :=
  accepted_of_selected 13 350306 ⟨644995, by decide⟩ ⟨13, 2, 0, 644995, 350306, 1413, 16384⟩
    (by decide) selected_cut_25490

theorem selected_cut_25491 : selected 8 ⟨645001, by decide⟩
    (prefixPartial 13 350307) = some ⟨13, 2, 0, 645001, 350307, 865, 16384⟩ := by
  decide +kernel

theorem context_13_350307_645001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350307 ⟨645001, by decide⟩ :=
  accepted_of_selected 13 350307 ⟨645001, by decide⟩ ⟨13, 2, 0, 645001, 350307, 865, 16384⟩
    (by decide) selected_cut_25491

theorem unmarked_context_12_87576_645002 : frontier 9 ⟨645002, by decide⟩
    (prefixCache 12 87576) (prefixPartial 12 87576) = false := by
  decide +kernel

theorem node_context_12_87576_645002 : EJMOriginalGlobalDAGData.nodes 9 ⟨645002, by decide⟩ =
    .split (coordinate 12) (![⟨644956, by decide⟩,⟨644977, by decide⟩,⟨644995, by decide⟩,⟨645001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87576_645002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87576 ⟨645002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87576
    ⟨645002, by decide⟩ (by decide) (![⟨644956, by decide⟩,⟨644977, by decide⟩,⟨644995, by decide⟩,⟨645001, by decide⟩]) unmarked_context_12_87576_645002 node_context_12_87576_645002
  intro a
  fin_cases a
  · exact context_13_350304_644956
  · exact context_13_350305_644977
  · exact context_13_350306_644995
  · exact context_13_350307_645001

theorem selected_cut_25492 : selected 8 ⟨645023, by decide⟩
    (prefixPartial 13 350308) = some ⟨13, 2, 0, 645023, 350308, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_350308_645023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350308 ⟨645023, by decide⟩ :=
  accepted_of_selected 13 350308 ⟨645023, by decide⟩ ⟨13, 2, 0, 645023, 350308, 1361, 16384⟩
    (by decide) selected_cut_25492

theorem selected_cut_25493 : selected 8 ⟨645043, by decide⟩
    (prefixPartial 13 350309) = some ⟨13, 2, 0, 645043, 350309, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_350309_645043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350309 ⟨645043, by decide⟩ :=
  accepted_of_selected 13 350309 ⟨645043, by decide⟩ ⟨13, 2, 0, 645043, 350309, 1189, 16384⟩
    (by decide) selected_cut_25493

theorem selected_cut_25494 : selected 8 ⟨645060, by decide⟩
    (prefixPartial 13 350310) = some ⟨13, 2, 0, 645060, 350310, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_350310_645060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350310 ⟨645060, by decide⟩ :=
  accepted_of_selected 13 350310 ⟨645060, by decide⟩ ⟨13, 2, 0, 645060, 350310, 1105, 16384⟩
    (by decide) selected_cut_25494

theorem selected_cut_25495 : selected 8 ⟨645065, by decide⟩
    (prefixPartial 13 350311) = some ⟨13, 2, 0, 645065, 350311, 845, 16384⟩ := by
  decide +kernel

theorem context_13_350311_645065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350311 ⟨645065, by decide⟩ :=
  accepted_of_selected 13 350311 ⟨645065, by decide⟩ ⟨13, 2, 0, 645065, 350311, 845, 16384⟩
    (by decide) selected_cut_25495

theorem unmarked_context_12_87577_645066 : frontier 9 ⟨645066, by decide⟩
    (prefixCache 12 87577) (prefixPartial 12 87577) = false := by
  decide +kernel

theorem node_context_12_87577_645066 : EJMOriginalGlobalDAGData.nodes 9 ⟨645066, by decide⟩ =
    .split (coordinate 12) (![⟨645023, by decide⟩,⟨645043, by decide⟩,⟨645060, by decide⟩,⟨645065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87577_645066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87577 ⟨645066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87577
    ⟨645066, by decide⟩ (by decide) (![⟨645023, by decide⟩,⟨645043, by decide⟩,⟨645060, by decide⟩,⟨645065, by decide⟩]) unmarked_context_12_87577_645066 node_context_12_87577_645066
  intro a
  fin_cases a
  · exact context_13_350308_645023
  · exact context_13_350309_645043
  · exact context_13_350310_645060
  · exact context_13_350311_645065

theorem selected_cut_25496 : selected 8 ⟨645105, by decide⟩
    (prefixPartial 13 350312) = some ⟨13, 2, 0, 645105, 350312, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_350312_645105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350312 ⟨645105, by decide⟩ :=
  accepted_of_selected 13 350312 ⟨645105, by decide⟩ ⟨13, 2, 0, 645105, 350312, 2345, 16384⟩
    (by decide) selected_cut_25496

theorem selected_cut_25497 : selected 8 ⟨645134, by decide⟩
    (prefixPartial 13 350313) = some ⟨13, 2, 0, 645134, 350313, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_350313_645134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350313 ⟨645134, by decide⟩ :=
  accepted_of_selected 13 350313 ⟨645134, by decide⟩ ⟨13, 2, 0, 645134, 350313, 2333, 16384⟩
    (by decide) selected_cut_25497

theorem selected_cut_25498 : selected 8 ⟨645159, by decide⟩
    (prefixPartial 13 350314) = some ⟨13, 2, 0, 645159, 350314, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_350314_645159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350314 ⟨645159, by decide⟩ :=
  accepted_of_selected 13 350314 ⟨645159, by decide⟩ ⟨13, 2, 0, 645159, 350314, 1909, 16384⟩
    (by decide) selected_cut_25498

theorem selected_cut_25499 : selected 8 ⟨645182, by decide⟩
    (prefixPartial 13 350315) = some ⟨13, 2, 0, 645182, 350315, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_350315_645182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350315 ⟨645182, by decide⟩ :=
  accepted_of_selected 13 350315 ⟨645182, by decide⟩ ⟨13, 2, 0, 645182, 350315, 1297, 16384⟩
    (by decide) selected_cut_25499

theorem unmarked_context_12_87578_645183 : frontier 9 ⟨645183, by decide⟩
    (prefixCache 12 87578) (prefixPartial 12 87578) = false := by
  decide +kernel

theorem node_context_12_87578_645183 : EJMOriginalGlobalDAGData.nodes 9 ⟨645183, by decide⟩ =
    .split (coordinate 12) (![⟨645105, by decide⟩,⟨645134, by decide⟩,⟨645159, by decide⟩,⟨645182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87578_645183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87578 ⟨645183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87578
    ⟨645183, by decide⟩ (by decide) (![⟨645105, by decide⟩,⟨645134, by decide⟩,⟨645159, by decide⟩,⟨645182, by decide⟩]) unmarked_context_12_87578_645183 node_context_12_87578_645183
  intro a
  fin_cases a
  · exact context_13_350312_645105
  · exact context_13_350313_645134
  · exact context_13_350314_645159
  · exact context_13_350315_645182

theorem selected_cut_25500 : selected 8 ⟨645202, by decide⟩
    (prefixPartial 13 350316) = some ⟨13, 2, 0, 645202, 350316, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_350316_645202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350316 ⟨645202, by decide⟩ :=
  accepted_of_selected 13 350316 ⟨645202, by decide⟩ ⟨13, 2, 0, 645202, 350316, 1449, 16384⟩
    (by decide) selected_cut_25500

theorem selected_cut_25501 : selected 8 ⟨645227, by decide⟩
    (prefixPartial 13 350317) = some ⟨13, 2, 0, 645227, 350317, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_350317_645227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350317 ⟨645227, by decide⟩ :=
  accepted_of_selected 13 350317 ⟨645227, by decide⟩ ⟨13, 2, 0, 645227, 350317, 1633, 16384⟩
    (by decide) selected_cut_25501

theorem selected_cut_25502 : selected 8 ⟨645243, by decide⟩
    (prefixPartial 13 350318) = some ⟨13, 2, 0, 645243, 350318, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_350318_645243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350318 ⟨645243, by decide⟩ :=
  accepted_of_selected 13 350318 ⟨645243, by decide⟩ ⟨13, 2, 0, 645243, 350318, 1381, 16384⟩
    (by decide) selected_cut_25502

theorem selected_cut_25503 : selected 8 ⟨645247, by decide⟩
    (prefixPartial 13 350319) = some ⟨13, 2, 0, 645247, 350319, 745, 16384⟩ := by
  decide +kernel

theorem context_13_350319_645247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350319 ⟨645247, by decide⟩ :=
  accepted_of_selected 13 350319 ⟨645247, by decide⟩ ⟨13, 2, 0, 645247, 350319, 745, 16384⟩
    (by decide) selected_cut_25503

theorem unmarked_context_12_87579_645248 : frontier 9 ⟨645248, by decide⟩
    (prefixCache 12 87579) (prefixPartial 12 87579) = false := by
  decide +kernel

theorem node_context_12_87579_645248 : EJMOriginalGlobalDAGData.nodes 9 ⟨645248, by decide⟩ =
    .split (coordinate 12) (![⟨645202, by decide⟩,⟨645227, by decide⟩,⟨645243, by decide⟩,⟨645247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87579_645248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87579 ⟨645248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87579
    ⟨645248, by decide⟩ (by decide) (![⟨645202, by decide⟩,⟨645227, by decide⟩,⟨645243, by decide⟩,⟨645247, by decide⟩]) unmarked_context_12_87579_645248 node_context_12_87579_645248
  intro a
  fin_cases a
  · exact context_13_350316_645202
  · exact context_13_350317_645227
  · exact context_13_350318_645243
  · exact context_13_350319_645247

theorem unmarked_context_11_21894_645249 : frontier 10 ⟨645249, by decide⟩
    (prefixCache 11 21894) (prefixPartial 11 21894) = false := by
  decide +kernel

theorem node_context_11_21894_645249 : EJMOriginalGlobalDAGData.nodes 10 ⟨645249, by decide⟩ =
    .split (coordinate 11) (![⟨645002, by decide⟩,⟨645066, by decide⟩,⟨645183, by decide⟩,⟨645248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21894_645249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21894 ⟨645249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21894
    ⟨645249, by decide⟩ (by decide) (![⟨645002, by decide⟩,⟨645066, by decide⟩,⟨645183, by decide⟩,⟨645248, by decide⟩]) unmarked_context_11_21894_645249 node_context_11_21894_645249
  intro a
  fin_cases a
  · exact context_12_87576_645002
  · exact context_12_87577_645066
  · exact context_12_87578_645183
  · exact context_12_87579_645248

theorem selected_cut_25504 : selected 8 ⟨645273, by decide⟩
    (prefixPartial 13 350320) = some ⟨13, 2, 0, 645273, 350320, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_350320_645273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350320 ⟨645273, by decide⟩ :=
  accepted_of_selected 13 350320 ⟨645273, by decide⟩ ⟨13, 2, 0, 645273, 350320, 1353, 16384⟩
    (by decide) selected_cut_25504

theorem selected_cut_25505 : selected 8 ⟨645304, by decide⟩
    (prefixPartial 13 350321) = some ⟨13, 2, 0, 645304, 350321, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_350321_645304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350321 ⟨645304, by decide⟩ :=
  accepted_of_selected 13 350321 ⟨645304, by decide⟩ ⟨13, 2, 0, 645304, 350321, 1509, 16384⟩
    (by decide) selected_cut_25505

theorem selected_cut_25506 : selected 8 ⟨645319, by decide⟩
    (prefixPartial 13 350322) = some ⟨13, 2, 0, 645319, 350322, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_350322_645319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350322 ⟨645319, by decide⟩ :=
  accepted_of_selected 13 350322 ⟨645319, by decide⟩ ⟨13, 2, 0, 645319, 350322, 1589, 16384⟩
    (by decide) selected_cut_25506

theorem selected_cut_25507 : selected 8 ⟨645327, by decide⟩
    (prefixPartial 13 350323) = some ⟨13, 2, 0, 645327, 350323, 953, 16384⟩ := by
  decide +kernel

theorem context_13_350323_645327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350323 ⟨645327, by decide⟩ :=
  accepted_of_selected 13 350323 ⟨645327, by decide⟩ ⟨13, 2, 0, 645327, 350323, 953, 16384⟩
    (by decide) selected_cut_25507

theorem unmarked_context_12_87580_645328 : frontier 9 ⟨645328, by decide⟩
    (prefixCache 12 87580) (prefixPartial 12 87580) = false := by
  decide +kernel

theorem node_context_12_87580_645328 : EJMOriginalGlobalDAGData.nodes 9 ⟨645328, by decide⟩ =
    .split (coordinate 12) (![⟨645273, by decide⟩,⟨645304, by decide⟩,⟨645319, by decide⟩,⟨645327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87580_645328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87580 ⟨645328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87580
    ⟨645328, by decide⟩ (by decide) (![⟨645273, by decide⟩,⟨645304, by decide⟩,⟨645319, by decide⟩,⟨645327, by decide⟩]) unmarked_context_12_87580_645328 node_context_12_87580_645328
  intro a
  fin_cases a
  · exact context_13_350320_645273
  · exact context_13_350321_645304
  · exact context_13_350322_645319
  · exact context_13_350323_645327

theorem selected_cut_25508 : selected 8 ⟨645346, by decide⟩
    (prefixPartial 13 350324) = some ⟨13, 2, 0, 645346, 350324, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_350324_645346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350324 ⟨645346, by decide⟩ :=
  accepted_of_selected 13 350324 ⟨645346, by decide⟩ ⟨13, 2, 0, 645346, 350324, 1305, 16384⟩
    (by decide) selected_cut_25508

theorem selected_cut_25509 : selected 8 ⟨645366, by decide⟩
    (prefixPartial 13 350325) = some ⟨13, 2, 0, 645366, 350325, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_350325_645366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350325 ⟨645366, by decide⟩ :=
  accepted_of_selected 13 350325 ⟨645366, by decide⟩ ⟨13, 2, 0, 645366, 350325, 1209, 16384⟩
    (by decide) selected_cut_25509

theorem selected_cut_25510 : selected 8 ⟨645384, by decide⟩
    (prefixPartial 13 350326) = some ⟨13, 2, 0, 645384, 350326, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_350326_645384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350326 ⟨645384, by decide⟩ :=
  accepted_of_selected 13 350326 ⟨645384, by decide⟩ ⟨13, 2, 0, 645384, 350326, 1201, 16384⟩
    (by decide) selected_cut_25510

theorem selected_cut_25511 : selected 8 ⟨645393, by decide⟩
    (prefixPartial 13 350327) = some ⟨13, 2, 0, 645393, 350327, 853, 16384⟩ := by
  decide +kernel

theorem context_13_350327_645393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350327 ⟨645393, by decide⟩ :=
  accepted_of_selected 13 350327 ⟨645393, by decide⟩ ⟨13, 2, 0, 645393, 350327, 853, 16384⟩
    (by decide) selected_cut_25511

theorem unmarked_context_12_87581_645394 : frontier 9 ⟨645394, by decide⟩
    (prefixCache 12 87581) (prefixPartial 12 87581) = false := by
  decide +kernel

theorem node_context_12_87581_645394 : EJMOriginalGlobalDAGData.nodes 9 ⟨645394, by decide⟩ =
    .split (coordinate 12) (![⟨645346, by decide⟩,⟨645366, by decide⟩,⟨645384, by decide⟩,⟨645393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87581_645394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87581 ⟨645394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87581
    ⟨645394, by decide⟩ (by decide) (![⟨645346, by decide⟩,⟨645366, by decide⟩,⟨645384, by decide⟩,⟨645393, by decide⟩]) unmarked_context_12_87581_645394 node_context_12_87581_645394
  intro a
  fin_cases a
  · exact context_13_350324_645346
  · exact context_13_350325_645366
  · exact context_13_350326_645384
  · exact context_13_350327_645393

theorem selected_cut_25512 : selected 8 ⟨645411, by decide⟩
    (prefixPartial 13 350328) = some ⟨13, 2, 0, 645411, 350328, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_350328_645411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350328 ⟨645411, by decide⟩ :=
  accepted_of_selected 13 350328 ⟨645411, by decide⟩ ⟨13, 2, 0, 645411, 350328, 1245, 16384⟩
    (by decide) selected_cut_25512

theorem selected_cut_25513 : selected 8 ⟨645434, by decide⟩
    (prefixPartial 13 350329) = some ⟨13, 2, 0, 645434, 350329, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_350329_645434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350329 ⟨645434, by decide⟩ :=
  accepted_of_selected 13 350329 ⟨645434, by decide⟩ ⟨13, 2, 0, 645434, 350329, 1441, 16384⟩
    (by decide) selected_cut_25513

theorem selected_cut_25514 : selected 8 ⟨645446, by decide⟩
    (prefixPartial 13 350330) = some ⟨13, 2, 0, 645446, 350330, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_350330_645446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350330 ⟨645446, by decide⟩ :=
  accepted_of_selected 13 350330 ⟨645446, by decide⟩ ⟨13, 2, 0, 645446, 350330, 1221, 16384⟩
    (by decide) selected_cut_25514

theorem selected_cut_25515 : selected 8 ⟨645453, by decide⟩
    (prefixPartial 13 350331) = some ⟨13, 2, 0, 645453, 350331, 881, 16384⟩ := by
  decide +kernel

theorem context_13_350331_645453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350331 ⟨645453, by decide⟩ :=
  accepted_of_selected 13 350331 ⟨645453, by decide⟩ ⟨13, 2, 0, 645453, 350331, 881, 16384⟩
    (by decide) selected_cut_25515

theorem unmarked_context_12_87582_645454 : frontier 9 ⟨645454, by decide⟩
    (prefixCache 12 87582) (prefixPartial 12 87582) = false := by
  decide +kernel

theorem node_context_12_87582_645454 : EJMOriginalGlobalDAGData.nodes 9 ⟨645454, by decide⟩ =
    .split (coordinate 12) (![⟨645411, by decide⟩,⟨645434, by decide⟩,⟨645446, by decide⟩,⟨645453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87582_645454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87582 ⟨645454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87582
    ⟨645454, by decide⟩ (by decide) (![⟨645411, by decide⟩,⟨645434, by decide⟩,⟨645446, by decide⟩,⟨645453, by decide⟩]) unmarked_context_12_87582_645454 node_context_12_87582_645454
  intro a
  fin_cases a
  · exact context_13_350328_645411
  · exact context_13_350329_645434
  · exact context_13_350330_645446
  · exact context_13_350331_645453

theorem selected_cut_25516 : selected 8 ⟨645474, by decide⟩
    (prefixPartial 13 350332) = some ⟨13, 2, 0, 645474, 350332, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_350332_645474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350332 ⟨645474, by decide⟩ :=
  accepted_of_selected 13 350332 ⟨645474, by decide⟩ ⟨13, 2, 0, 645474, 350332, 1349, 16384⟩
    (by decide) selected_cut_25516

theorem selected_cut_25517 : selected 8 ⟨645495, by decide⟩
    (prefixPartial 13 350333) = some ⟨13, 2, 0, 645495, 350333, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_350333_645495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350333 ⟨645495, by decide⟩ :=
  accepted_of_selected 13 350333 ⟨645495, by decide⟩ ⟨13, 2, 0, 645495, 350333, 1513, 16384⟩
    (by decide) selected_cut_25517

theorem selected_cut_25518 : selected 8 ⟨645512, by decide⟩
    (prefixPartial 13 350334) = some ⟨13, 2, 0, 645512, 350334, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_350334_645512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350334 ⟨645512, by decide⟩ :=
  accepted_of_selected 13 350334 ⟨645512, by decide⟩ ⟨13, 2, 0, 645512, 350334, 1601, 16384⟩
    (by decide) selected_cut_25518

theorem selected_cut_25519 : selected 8 ⟨645518, by decide⟩
    (prefixPartial 13 350335) = some ⟨13, 2, 0, 645518, 350335, 797, 16384⟩ := by
  decide +kernel

theorem context_13_350335_645518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350335 ⟨645518, by decide⟩ :=
  accepted_of_selected 13 350335 ⟨645518, by decide⟩ ⟨13, 2, 0, 645518, 350335, 797, 16384⟩
    (by decide) selected_cut_25519

theorem unmarked_context_12_87583_645519 : frontier 9 ⟨645519, by decide⟩
    (prefixCache 12 87583) (prefixPartial 12 87583) = false := by
  decide +kernel

theorem node_context_12_87583_645519 : EJMOriginalGlobalDAGData.nodes 9 ⟨645519, by decide⟩ =
    .split (coordinate 12) (![⟨645474, by decide⟩,⟨645495, by decide⟩,⟨645512, by decide⟩,⟨645518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87583_645519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87583 ⟨645519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87583
    ⟨645519, by decide⟩ (by decide) (![⟨645474, by decide⟩,⟨645495, by decide⟩,⟨645512, by decide⟩,⟨645518, by decide⟩]) unmarked_context_12_87583_645519 node_context_12_87583_645519
  intro a
  fin_cases a
  · exact context_13_350332_645474
  · exact context_13_350333_645495
  · exact context_13_350334_645512
  · exact context_13_350335_645518

theorem unmarked_context_11_21895_645520 : frontier 10 ⟨645520, by decide⟩
    (prefixCache 11 21895) (prefixPartial 11 21895) = false := by
  decide +kernel

theorem node_context_11_21895_645520 : EJMOriginalGlobalDAGData.nodes 10 ⟨645520, by decide⟩ =
    .split (coordinate 11) (![⟨645328, by decide⟩,⟨645394, by decide⟩,⟨645454, by decide⟩,⟨645519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21895_645520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21895 ⟨645520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21895
    ⟨645520, by decide⟩ (by decide) (![⟨645328, by decide⟩,⟨645394, by decide⟩,⟨645454, by decide⟩,⟨645519, by decide⟩]) unmarked_context_11_21895_645520 node_context_11_21895_645520
  intro a
  fin_cases a
  · exact context_12_87580_645328
  · exact context_12_87581_645394
  · exact context_12_87582_645454
  · exact context_12_87583_645519

theorem unmarked_context_10_5473_645521 : frontier 11 ⟨645521, by decide⟩
    (prefixCache 10 5473) (prefixPartial 10 5473) = false := by
  decide +kernel

theorem node_context_10_5473_645521 : EJMOriginalGlobalDAGData.nodes 11 ⟨645521, by decide⟩ =
    .split (coordinate 10) (![⟨644556, by decide⟩,⟨644935, by decide⟩,⟨645249, by decide⟩,⟨645520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5473_645521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5473 ⟨645521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5473
    ⟨645521, by decide⟩ (by decide) (![⟨644556, by decide⟩,⟨644935, by decide⟩,⟨645249, by decide⟩,⟨645520, by decide⟩]) unmarked_context_10_5473_645521 node_context_10_5473_645521
  intro a
  fin_cases a
  · exact context_11_21892_644556
  · exact context_11_21893_644935
  · exact context_11_21894_645249
  · exact context_11_21895_645520

theorem selected_cut_25520 : selected 9 ⟨645583, by decide⟩
    (prefixPartial 12 87584) = some ⟨12, 2, 0, 645583, 87584, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_87584_645583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87584 ⟨645583, by decide⟩ :=
  accepted_of_selected 12 87584 ⟨645583, by decide⟩ ⟨12, 2, 0, 645583, 87584, 3909, 65536⟩
    (by decide) selected_cut_25520

theorem selected_cut_25521 : selected 9 ⟨645646, by decide⟩
    (prefixPartial 12 87585) = some ⟨12, 2, 0, 645646, 87585, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_87585_645646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87585 ⟨645646, by decide⟩ :=
  accepted_of_selected 12 87585 ⟨645646, by decide⟩ ⟨12, 2, 0, 645646, 87585, 4057, 65536⟩
    (by decide) selected_cut_25521

theorem selected_cut_25522 : selected 9 ⟨645696, by decide⟩
    (prefixPartial 12 87586) = some ⟨12, 2, 0, 645696, 87586, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_87586_645696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87586 ⟨645696, by decide⟩ :=
  accepted_of_selected 12 87586 ⟨645696, by decide⟩ ⟨12, 2, 0, 645696, 87586, 3761, 65536⟩
    (by decide) selected_cut_25522

theorem selected_cut_25523 : selected 8 ⟨645716, by decide⟩
    (prefixPartial 13 350348) = some ⟨13, 2, 0, 645716, 350348, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_350348_645716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350348 ⟨645716, by decide⟩ :=
  accepted_of_selected 13 350348 ⟨645716, by decide⟩ ⟨13, 2, 0, 645716, 350348, 1005, 16384⟩
    (by decide) selected_cut_25523

theorem selected_cut_25524 : selected 8 ⟨645733, by decide⟩
    (prefixPartial 13 350349) = some ⟨13, 2, 0, 645733, 350349, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_350349_645733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350349 ⟨645733, by decide⟩ :=
  accepted_of_selected 13 350349 ⟨645733, by decide⟩ ⟨13, 2, 0, 645733, 350349, 1305, 16384⟩
    (by decide) selected_cut_25524

theorem selected_cut_25525 : selected 8 ⟨645751, by decide⟩
    (prefixPartial 13 350350) = some ⟨13, 2, 0, 645751, 350350, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_350350_645751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350350 ⟨645751, by decide⟩ :=
  accepted_of_selected 13 350350 ⟨645751, by decide⟩ ⟨13, 2, 0, 645751, 350350, 1297, 16384⟩
    (by decide) selected_cut_25525

theorem selected_cut_25526 : selected 8 ⟨645754, by decide⟩
    (prefixPartial 13 350351) = some ⟨13, 2, 0, 645754, 350351, 605, 16384⟩ := by
  decide +kernel

theorem context_13_350351_645754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350351 ⟨645754, by decide⟩ :=
  accepted_of_selected 13 350351 ⟨645754, by decide⟩ ⟨13, 2, 0, 645754, 350351, 605, 16384⟩
    (by decide) selected_cut_25526

theorem unmarked_context_12_87587_645755 : frontier 9 ⟨645755, by decide⟩
    (prefixCache 12 87587) (prefixPartial 12 87587) = false := by
  decide +kernel

theorem node_context_12_87587_645755 : EJMOriginalGlobalDAGData.nodes 9 ⟨645755, by decide⟩ =
    .split (coordinate 12) (![⟨645716, by decide⟩,⟨645733, by decide⟩,⟨645751, by decide⟩,⟨645754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87587_645755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87587 ⟨645755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87587
    ⟨645755, by decide⟩ (by decide) (![⟨645716, by decide⟩,⟨645733, by decide⟩,⟨645751, by decide⟩,⟨645754, by decide⟩]) unmarked_context_12_87587_645755 node_context_12_87587_645755
  intro a
  fin_cases a
  · exact context_13_350348_645716
  · exact context_13_350349_645733
  · exact context_13_350350_645751
  · exact context_13_350351_645754

theorem unmarked_context_11_21896_645756 : frontier 10 ⟨645756, by decide⟩
    (prefixCache 11 21896) (prefixPartial 11 21896) = false := by
  decide +kernel

theorem node_context_11_21896_645756 : EJMOriginalGlobalDAGData.nodes 10 ⟨645756, by decide⟩ =
    .split (coordinate 11) (![⟨645583, by decide⟩,⟨645646, by decide⟩,⟨645696, by decide⟩,⟨645755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21896_645756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21896 ⟨645756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21896
    ⟨645756, by decide⟩ (by decide) (![⟨645583, by decide⟩,⟨645646, by decide⟩,⟨645696, by decide⟩,⟨645755, by decide⟩]) unmarked_context_11_21896_645756 node_context_11_21896_645756
  intro a
  fin_cases a
  · exact context_12_87584_645583
  · exact context_12_87585_645646
  · exact context_12_87586_645696
  · exact context_12_87587_645755

theorem selected_cut_25527 : selected 8 ⟨645765, by decide⟩
    (prefixPartial 13 350352) = some ⟨13, 2, 0, 645765, 350352, 725, 16384⟩ := by
  decide +kernel

theorem context_13_350352_645765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350352 ⟨645765, by decide⟩ :=
  accepted_of_selected 13 350352 ⟨645765, by decide⟩ ⟨13, 2, 0, 645765, 350352, 725, 16384⟩
    (by decide) selected_cut_25527

theorem selected_cut_25528 : selected 8 ⟨645787, by decide⟩
    (prefixPartial 13 350353) = some ⟨13, 2, 0, 645787, 350353, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_350353_645787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350353 ⟨645787, by decide⟩ :=
  accepted_of_selected 13 350353 ⟨645787, by decide⟩ ⟨13, 2, 0, 645787, 350353, 1353, 16384⟩
    (by decide) selected_cut_25528

theorem selected_cut_25529 : selected 8 ⟨645804, by decide⟩
    (prefixPartial 13 350354) = some ⟨13, 2, 0, 645804, 350354, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_350354_645804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350354 ⟨645804, by decide⟩ :=
  accepted_of_selected 13 350354 ⟨645804, by decide⟩ ⟨13, 2, 0, 645804, 350354, 1281, 16384⟩
    (by decide) selected_cut_25529

theorem selected_cut_25530 : selected 8 ⟨645811, by decide⟩
    (prefixPartial 13 350355) = some ⟨13, 2, 0, 645811, 350355, 777, 16384⟩ := by
  decide +kernel

theorem context_13_350355_645811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350355 ⟨645811, by decide⟩ :=
  accepted_of_selected 13 350355 ⟨645811, by decide⟩ ⟨13, 2, 0, 645811, 350355, 777, 16384⟩
    (by decide) selected_cut_25530

theorem unmarked_context_12_87588_645812 : frontier 9 ⟨645812, by decide⟩
    (prefixCache 12 87588) (prefixPartial 12 87588) = false := by
  decide +kernel

theorem node_context_12_87588_645812 : EJMOriginalGlobalDAGData.nodes 9 ⟨645812, by decide⟩ =
    .split (coordinate 12) (![⟨645765, by decide⟩,⟨645787, by decide⟩,⟨645804, by decide⟩,⟨645811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87588_645812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87588 ⟨645812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87588
    ⟨645812, by decide⟩ (by decide) (![⟨645765, by decide⟩,⟨645787, by decide⟩,⟨645804, by decide⟩,⟨645811, by decide⟩]) unmarked_context_12_87588_645812 node_context_12_87588_645812
  intro a
  fin_cases a
  · exact context_13_350352_645765
  · exact context_13_350353_645787
  · exact context_13_350354_645804
  · exact context_13_350355_645811

theorem selected_cut_25531 : selected 9 ⟨645862, by decide⟩
    (prefixPartial 12 87589) = some ⟨12, 2, 0, 645862, 87589, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_87589_645862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87589 ⟨645862, by decide⟩ :=
  accepted_of_selected 12 87589 ⟨645862, by decide⟩ ⟨12, 2, 0, 645862, 87589, 3425, 65536⟩
    (by decide) selected_cut_25531

theorem selected_cut_25532 : selected 9 ⟨645909, by decide⟩
    (prefixPartial 12 87590) = some ⟨12, 2, 0, 645909, 87590, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_87590_645909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87590 ⟨645909, by decide⟩ :=
  accepted_of_selected 12 87590 ⟨645909, by decide⟩ ⟨12, 2, 0, 645909, 87590, 3489, 65536⟩
    (by decide) selected_cut_25532

theorem selected_cut_25533 : selected 9 ⟨645956, by decide⟩
    (prefixPartial 12 87591) = some ⟨12, 2, 0, 645956, 87591, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_87591_645956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87591 ⟨645956, by decide⟩ :=
  accepted_of_selected 12 87591 ⟨645956, by decide⟩ ⟨12, 2, 0, 645956, 87591, 3693, 65536⟩
    (by decide) selected_cut_25533

theorem unmarked_context_11_21897_645957 : frontier 10 ⟨645957, by decide⟩
    (prefixCache 11 21897) (prefixPartial 11 21897) = false := by
  decide +kernel

theorem node_context_11_21897_645957 : EJMOriginalGlobalDAGData.nodes 10 ⟨645957, by decide⟩ =
    .split (coordinate 11) (![⟨645812, by decide⟩,⟨645862, by decide⟩,⟨645909, by decide⟩,⟨645956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21897_645957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21897 ⟨645957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21897
    ⟨645957, by decide⟩ (by decide) (![⟨645812, by decide⟩,⟨645862, by decide⟩,⟨645909, by decide⟩,⟨645956, by decide⟩]) unmarked_context_11_21897_645957 node_context_11_21897_645957
  intro a
  fin_cases a
  · exact context_12_87588_645812
  · exact context_12_87589_645862
  · exact context_12_87590_645909
  · exact context_12_87591_645956

theorem selected_cut_25534 : selected 9 ⟨646015, by decide⟩
    (prefixPartial 12 87592) = some ⟨12, 2, 0, 646015, 87592, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_87592_646015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87592 ⟨646015, by decide⟩ :=
  accepted_of_selected 12 87592 ⟨646015, by decide⟩ ⟨12, 2, 0, 646015, 87592, 4001, 65536⟩
    (by decide) selected_cut_25534

theorem selected_cut_25535 : selected 9 ⟨646062, by decide⟩
    (prefixPartial 12 87593) = some ⟨12, 2, 0, 646062, 87593, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_87593_646062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87593 ⟨646062, by decide⟩ :=
  accepted_of_selected 12 87593 ⟨646062, by decide⟩ ⟨12, 2, 0, 646062, 87593, 3485, 65536⟩
    (by decide) selected_cut_25535

theorem selected_cut_25536 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 87594) = some ⟨12, 1, 0, 445248, 87594, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87594_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87594 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 87594 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 87594, 1, 65536⟩
    (by decide) selected_cut_25536

theorem selected_cut_25537 : selected 9 ⟨646113, by decide⟩
    (prefixPartial 12 87595) = some ⟨12, 2, 0, 646113, 87595, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_87595_646113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87595 ⟨646113, by decide⟩ :=
  accepted_of_selected 12 87595 ⟨646113, by decide⟩ ⟨12, 2, 0, 646113, 87595, 3805, 65536⟩
    (by decide) selected_cut_25537

theorem unmarked_context_11_21898_646114 : frontier 10 ⟨646114, by decide⟩
    (prefixCache 11 21898) (prefixPartial 11 21898) = false := by
  decide +kernel

theorem node_context_11_21898_646114 : EJMOriginalGlobalDAGData.nodes 10 ⟨646114, by decide⟩ =
    .split (coordinate 11) (![⟨646015, by decide⟩,⟨646062, by decide⟩,⟨445248, by decide⟩,⟨646113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21898_646114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21898 ⟨646114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21898
    ⟨646114, by decide⟩ (by decide) (![⟨646015, by decide⟩,⟨646062, by decide⟩,⟨445248, by decide⟩,⟨646113, by decide⟩]) unmarked_context_11_21898_646114 node_context_11_21898_646114
  intro a
  fin_cases a
  · exact context_12_87592_646015
  · exact context_12_87593_646062
  · exact context_12_87594_445248
  · exact context_12_87595_646113

theorem selected_cut_25538 : selected 8 ⟨646124, by decide⟩
    (prefixPartial 13 350384) = some ⟨13, 2, 0, 646124, 350384, 585, 16384⟩ := by
  decide +kernel

theorem context_13_350384_646124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 350384 ⟨646124, by decide⟩ :=
  accepted_of_selected 13 350384 ⟨646124, by decide⟩ ⟨13, 2, 0, 646124, 350384, 585, 16384⟩
    (by decide) selected_cut_25538

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
