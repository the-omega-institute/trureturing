/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover513
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_49348 : selected 10 ⟨1370051, by decide⟩
    (prefixPartial 11 101791) = some ⟨11, 1, 0, 1370051, 101791, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101791_1370051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101791 ⟨1370051, by decide⟩ :=
  accepted_of_selected 11 101791 ⟨1370051, by decide⟩ ⟨11, 1, 0, 1370051, 101791, 1, 262144⟩
    (by decide) selected_cut_49348

theorem unmarked_context_10_25447_1395535 : frontier 11 ⟨1395535, by decide⟩
    (prefixCache 10 25447) (prefixPartial 10 25447) = false := by
  decide +kernel

theorem node_context_10_25447_1395535 : EJMOriginalGlobalDAGData.nodes 11 ⟨1395535, by decide⟩ =
    .split (coordinate 10) (![⟨1395437, by decide⟩,⟨1395492, by decide⟩,⟨1395534, by decide⟩,⟨1370051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25447_1395535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25447 ⟨1395535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25447
    ⟨1395535, by decide⟩ (by decide) (![⟨1395437, by decide⟩,⟨1395492, by decide⟩,⟨1395534, by decide⟩,⟨1370051, by decide⟩]) unmarked_context_10_25447_1395535 node_context_10_25447_1395535
  intro a
  fin_cases a
  · exact context_11_101788_1395437
  · exact context_11_101789_1395492
  · exact context_11_101790_1395534
  · exact context_11_101791_1370051

theorem unmarked_context_9_6361_1395536 : frontier 12 ⟨1395536, by decide⟩
    (prefixCache 9 6361) (prefixPartial 9 6361) = false := by
  decide +kernel

theorem node_context_9_6361_1395536 : EJMOriginalGlobalDAGData.nodes 12 ⟨1395536, by decide⟩ =
    .split (coordinate 9) (![⟨1395167, by decide⟩,⟨893098, by decide⟩,⟨1395372, by decide⟩,⟨1395535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6361_1395536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6361 ⟨1395536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6361
    ⟨1395536, by decide⟩ (by decide) (![⟨1395167, by decide⟩,⟨893098, by decide⟩,⟨1395372, by decide⟩,⟨1395535, by decide⟩]) unmarked_context_9_6361_1395536 node_context_9_6361_1395536
  intro a
  fin_cases a
  · exact context_10_25444_1395167
  · exact context_10_25445_893098
  · exact context_10_25446_1395372
  · exact context_10_25447_1395535

theorem selected_cut_49349 : selected 10 ⟨1395553, by decide⟩
    (prefixPartial 11 101792) = some ⟨11, 2, 0, 1395553, 101792, 913, 262144⟩ := by
  decide +kernel

theorem context_11_101792_1395553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101792 ⟨1395553, by decide⟩ :=
  accepted_of_selected 11 101792 ⟨1395553, by decide⟩ ⟨11, 2, 0, 1395553, 101792, 913, 262144⟩
    (by decide) selected_cut_49349

theorem selected_cut_49350 : selected 10 ⟨1395586, by decide⟩
    (prefixPartial 11 101793) = some ⟨11, 2, 0, 1395586, 101793, 1721, 262144⟩ := by
  decide +kernel

theorem context_11_101793_1395586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101793 ⟨1395586, by decide⟩ :=
  accepted_of_selected 11 101793 ⟨1395586, by decide⟩ ⟨11, 2, 0, 1395586, 101793, 1721, 262144⟩
    (by decide) selected_cut_49350

theorem selected_cut_49351 : selected 10 ⟨1395627, by decide⟩
    (prefixPartial 11 101794) = some ⟨11, 2, 0, 1395627, 101794, 2249, 262144⟩ := by
  decide +kernel

theorem context_11_101794_1395627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101794 ⟨1395627, by decide⟩ :=
  accepted_of_selected 11 101794 ⟨1395627, by decide⟩ ⟨11, 2, 0, 1395627, 101794, 2249, 262144⟩
    (by decide) selected_cut_49351

theorem selected_cut_49352 : selected 10 ⟨1395667, by decide⟩
    (prefixPartial 11 101795) = some ⟨11, 2, 0, 1395667, 101795, 1837, 262144⟩ := by
  decide +kernel

theorem context_11_101795_1395667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101795 ⟨1395667, by decide⟩ :=
  accepted_of_selected 11 101795 ⟨1395667, by decide⟩ ⟨11, 2, 0, 1395667, 101795, 1837, 262144⟩
    (by decide) selected_cut_49352

theorem unmarked_context_10_25448_1395668 : frontier 11 ⟨1395668, by decide⟩
    (prefixCache 10 25448) (prefixPartial 10 25448) = false := by
  decide +kernel

theorem node_context_10_25448_1395668 : EJMOriginalGlobalDAGData.nodes 11 ⟨1395668, by decide⟩ =
    .split (coordinate 10) (![⟨1395553, by decide⟩,⟨1395586, by decide⟩,⟨1395627, by decide⟩,⟨1395667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25448_1395668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25448 ⟨1395668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25448
    ⟨1395668, by decide⟩ (by decide) (![⟨1395553, by decide⟩,⟨1395586, by decide⟩,⟨1395627, by decide⟩,⟨1395667, by decide⟩]) unmarked_context_10_25448_1395668 node_context_10_25448_1395668
  intro a
  fin_cases a
  · exact context_11_101792_1395553
  · exact context_11_101793_1395586
  · exact context_11_101794_1395627
  · exact context_11_101795_1395667

theorem selected_cut_49353 : selected 10 ⟨1395705, by decide⟩
    (prefixPartial 11 101796) = some ⟨11, 2, 0, 1395705, 101796, 1617, 262144⟩ := by
  decide +kernel

theorem context_11_101796_1395705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101796 ⟨1395705, by decide⟩ :=
  accepted_of_selected 11 101796 ⟨1395705, by decide⟩ ⟨11, 2, 0, 1395705, 101796, 1617, 262144⟩
    (by decide) selected_cut_49353

theorem selected_cut_49354 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101797) = some ⟨11, 1, 0, 892405, 101797, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101797_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101797 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101797 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101797, 1, 262144⟩
    (by decide) selected_cut_49354

theorem selected_cut_49355 : selected 10 ⟨1395742, by decide⟩
    (prefixPartial 11 101798) = some ⟨11, 2, 0, 1395742, 101798, 1921, 262144⟩ := by
  decide +kernel

theorem context_11_101798_1395742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101798 ⟨1395742, by decide⟩ :=
  accepted_of_selected 11 101798 ⟨1395742, by decide⟩ ⟨11, 2, 0, 1395742, 101798, 1921, 262144⟩
    (by decide) selected_cut_49355

theorem selected_cut_49356 : selected 10 ⟨1395786, by decide⟩
    (prefixPartial 11 101799) = some ⟨11, 2, 0, 1395786, 101799, 2025, 262144⟩ := by
  decide +kernel

theorem context_11_101799_1395786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101799 ⟨1395786, by decide⟩ :=
  accepted_of_selected 11 101799 ⟨1395786, by decide⟩ ⟨11, 2, 0, 1395786, 101799, 2025, 262144⟩
    (by decide) selected_cut_49356

theorem unmarked_context_10_25449_1395787 : frontier 11 ⟨1395787, by decide⟩
    (prefixCache 10 25449) (prefixPartial 10 25449) = false := by
  decide +kernel

theorem node_context_10_25449_1395787 : EJMOriginalGlobalDAGData.nodes 11 ⟨1395787, by decide⟩ =
    .split (coordinate 10) (![⟨1395705, by decide⟩,⟨892405, by decide⟩,⟨1395742, by decide⟩,⟨1395786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25449_1395787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25449 ⟨1395787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25449
    ⟨1395787, by decide⟩ (by decide) (![⟨1395705, by decide⟩,⟨892405, by decide⟩,⟨1395742, by decide⟩,⟨1395786, by decide⟩]) unmarked_context_10_25449_1395787 node_context_10_25449_1395787
  intro a
  fin_cases a
  · exact context_11_101796_1395705
  · exact context_11_101797_892405
  · exact context_11_101798_1395742
  · exact context_11_101799_1395786

theorem selected_cut_49357 : selected 11 ⟨1395812, by decide⟩
    (prefixPartial 10 25450) = some ⟨10, 2, 0, 1395812, 25450, 1189, 1048576⟩ := by
  decide +kernel

theorem context_10_25450_1395812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25450 ⟨1395812, by decide⟩ :=
  accepted_of_selected 10 25450 ⟨1395812, by decide⟩ ⟨10, 2, 0, 1395812, 25450, 1189, 1048576⟩
    (by decide) selected_cut_49357

theorem selected_cut_49358 : selected 10 ⟨1395832, by decide⟩
    (prefixPartial 11 101804) = some ⟨11, 2, 0, 1395832, 101804, 1157, 262144⟩ := by
  decide +kernel

theorem context_11_101804_1395832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101804 ⟨1395832, by decide⟩ :=
  accepted_of_selected 11 101804 ⟨1395832, by decide⟩ ⟨11, 2, 0, 1395832, 101804, 1157, 262144⟩
    (by decide) selected_cut_49358

theorem selected_cut_49359 : selected 10 ⟨1395866, by decide⟩
    (prefixPartial 11 101805) = some ⟨11, 2, 0, 1395866, 101805, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_101805_1395866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101805 ⟨1395866, by decide⟩ :=
  accepted_of_selected 11 101805 ⟨1395866, by decide⟩ ⟨11, 2, 0, 1395866, 101805, 1561, 262144⟩
    (by decide) selected_cut_49359

theorem selected_cut_49360 : selected 10 ⟨1395893, by decide⟩
    (prefixPartial 11 101806) = some ⟨11, 2, 0, 1395893, 101806, 1325, 262144⟩ := by
  decide +kernel

theorem context_11_101806_1395893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101806 ⟨1395893, by decide⟩ :=
  accepted_of_selected 11 101806 ⟨1395893, by decide⟩ ⟨11, 2, 0, 1395893, 101806, 1325, 262144⟩
    (by decide) selected_cut_49360

theorem selected_cut_49361 : selected 10 ⟨1395904, by decide⟩
    (prefixPartial 11 101807) = some ⟨11, 2, 0, 1395904, 101807, 505, 262144⟩ := by
  decide +kernel

theorem context_11_101807_1395904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101807 ⟨1395904, by decide⟩ :=
  accepted_of_selected 11 101807 ⟨1395904, by decide⟩ ⟨11, 2, 0, 1395904, 101807, 505, 262144⟩
    (by decide) selected_cut_49361

theorem unmarked_context_10_25451_1395905 : frontier 11 ⟨1395905, by decide⟩
    (prefixCache 10 25451) (prefixPartial 10 25451) = false := by
  decide +kernel

theorem node_context_10_25451_1395905 : EJMOriginalGlobalDAGData.nodes 11 ⟨1395905, by decide⟩ =
    .split (coordinate 10) (![⟨1395832, by decide⟩,⟨1395866, by decide⟩,⟨1395893, by decide⟩,⟨1395904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25451_1395905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25451 ⟨1395905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25451
    ⟨1395905, by decide⟩ (by decide) (![⟨1395832, by decide⟩,⟨1395866, by decide⟩,⟨1395893, by decide⟩,⟨1395904, by decide⟩]) unmarked_context_10_25451_1395905 node_context_10_25451_1395905
  intro a
  fin_cases a
  · exact context_11_101804_1395832
  · exact context_11_101805_1395866
  · exact context_11_101806_1395893
  · exact context_11_101807_1395904

theorem unmarked_context_9_6362_1395906 : frontier 12 ⟨1395906, by decide⟩
    (prefixCache 9 6362) (prefixPartial 9 6362) = false := by
  decide +kernel

theorem node_context_9_6362_1395906 : EJMOriginalGlobalDAGData.nodes 12 ⟨1395906, by decide⟩ =
    .split (coordinate 9) (![⟨1395668, by decide⟩,⟨1395787, by decide⟩,⟨1395812, by decide⟩,⟨1395905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6362_1395906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6362 ⟨1395906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6362
    ⟨1395906, by decide⟩ (by decide) (![⟨1395668, by decide⟩,⟨1395787, by decide⟩,⟨1395812, by decide⟩,⟨1395905, by decide⟩]) unmarked_context_9_6362_1395906 node_context_9_6362_1395906
  intro a
  fin_cases a
  · exact context_10_25448_1395668
  · exact context_10_25449_1395787
  · exact context_10_25450_1395812
  · exact context_10_25451_1395905

theorem selected_cut_49362 : selected 11 ⟨1395977, by decide⟩
    (prefixPartial 10 25452) = some ⟨10, 2, 0, 1395977, 25452, 3365, 1048576⟩ := by
  decide +kernel

theorem context_10_25452_1395977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25452 ⟨1395977, by decide⟩ :=
  accepted_of_selected 10 25452 ⟨1395977, by decide⟩ ⟨10, 2, 0, 1395977, 25452, 3365, 1048576⟩
    (by decide) selected_cut_49362

theorem selected_cut_49363 : selected 11 ⟨1396016, by decide⟩
    (prefixPartial 10 25453) = some ⟨10, 2, 0, 1396016, 25453, 1885, 1048576⟩ := by
  decide +kernel

theorem context_10_25453_1396016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25453 ⟨1396016, by decide⟩ :=
  accepted_of_selected 10 25453 ⟨1396016, by decide⟩ ⟨10, 2, 0, 1396016, 25453, 1885, 1048576⟩
    (by decide) selected_cut_49363

theorem selected_cut_49364 : selected 11 ⟨1396045, by decide⟩
    (prefixPartial 10 25454) = some ⟨10, 2, 0, 1396045, 25454, 905, 1048576⟩ := by
  decide +kernel

theorem context_10_25454_1396045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25454 ⟨1396045, by decide⟩ :=
  accepted_of_selected 10 25454 ⟨1396045, by decide⟩ ⟨10, 2, 0, 1396045, 25454, 905, 1048576⟩
    (by decide) selected_cut_49364

theorem selected_cut_49365 : selected 11 ⟨1396051, by decide⟩
    (prefixPartial 10 25455) = some ⟨10, 2, 0, 1396051, 25455, 73, 1048576⟩ := by
  decide +kernel

theorem context_10_25455_1396051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25455 ⟨1396051, by decide⟩ :=
  accepted_of_selected 10 25455 ⟨1396051, by decide⟩ ⟨10, 2, 0, 1396051, 25455, 73, 1048576⟩
    (by decide) selected_cut_49365

theorem unmarked_context_9_6363_1396052 : frontier 12 ⟨1396052, by decide⟩
    (prefixCache 9 6363) (prefixPartial 9 6363) = false := by
  decide +kernel

theorem node_context_9_6363_1396052 : EJMOriginalGlobalDAGData.nodes 12 ⟨1396052, by decide⟩ =
    .split (coordinate 9) (![⟨1395977, by decide⟩,⟨1396016, by decide⟩,⟨1396045, by decide⟩,⟨1396051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6363_1396052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6363 ⟨1396052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6363
    ⟨1396052, by decide⟩ (by decide) (![⟨1395977, by decide⟩,⟨1396016, by decide⟩,⟨1396045, by decide⟩,⟨1396051, by decide⟩]) unmarked_context_9_6363_1396052 node_context_9_6363_1396052
  intro a
  fin_cases a
  · exact context_10_25452_1395977
  · exact context_10_25453_1396016
  · exact context_10_25454_1396045
  · exact context_10_25455_1396051

theorem unmarked_context_8_1590_1396053 : frontier 13 ⟨1396053, by decide⟩
    (prefixCache 8 1590) (prefixPartial 8 1590) = false := by
  decide +kernel

theorem node_context_8_1590_1396053 : EJMOriginalGlobalDAGData.nodes 13 ⟨1396053, by decide⟩ =
    .split (coordinate 8) (![⟨1394918, by decide⟩,⟨1395536, by decide⟩,⟨1395906, by decide⟩,⟨1396052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1590_1396053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1590 ⟨1396053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1590
    ⟨1396053, by decide⟩ (by decide) (![⟨1394918, by decide⟩,⟨1395536, by decide⟩,⟨1395906, by decide⟩,⟨1396052, by decide⟩]) unmarked_context_8_1590_1396053 node_context_8_1590_1396053
  intro a
  fin_cases a
  · exact context_9_6360_1394918
  · exact context_9_6361_1395536
  · exact context_9_6362_1395906
  · exact context_9_6363_1396052

theorem selected_cut_49366 : selected 11 ⟨1396134, by decide⟩
    (prefixPartial 10 25456) = some ⟨10, 2, 0, 1396134, 25456, 3073, 1048576⟩ := by
  decide +kernel

theorem context_10_25456_1396134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25456 ⟨1396134, by decide⟩ :=
  accepted_of_selected 10 25456 ⟨1396134, by decide⟩ ⟨10, 2, 0, 1396134, 25456, 3073, 1048576⟩
    (by decide) selected_cut_49366

theorem selected_cut_49367 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407312) = some ⟨12, 1, 0, 1108174, 407312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407312_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407312 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407312 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407312, 1, 65536⟩
    (by decide) selected_cut_49367

theorem selected_cut_49368 : selected 9 ⟨1396175, by decide⟩
    (prefixPartial 12 407313) = some ⟨12, 2, 0, 1396175, 407313, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_407313_1396175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407313 ⟨1396175, by decide⟩ :=
  accepted_of_selected 12 407313 ⟨1396175, by decide⟩ ⟨12, 2, 0, 1396175, 407313, 2257, 65536⟩
    (by decide) selected_cut_49368

theorem selected_cut_49369 : selected 9 ⟨1396237, by decide⟩
    (prefixPartial 12 407314) = some ⟨12, 2, 0, 1396237, 407314, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_407314_1396237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407314 ⟨1396237, by decide⟩ :=
  accepted_of_selected 12 407314 ⟨1396237, by decide⟩ ⟨12, 2, 0, 1396237, 407314, 2645, 65536⟩
    (by decide) selected_cut_49369

theorem selected_cut_49370 : selected 9 ⟨1396286, by decide⟩
    (prefixPartial 12 407315) = some ⟨12, 2, 0, 1396286, 407315, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_407315_1396286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407315 ⟨1396286, by decide⟩ :=
  accepted_of_selected 12 407315 ⟨1396286, by decide⟩ ⟨12, 2, 0, 1396286, 407315, 2137, 65536⟩
    (by decide) selected_cut_49370

theorem unmarked_context_11_101828_1396287 : frontier 10 ⟨1396287, by decide⟩
    (prefixCache 11 101828) (prefixPartial 11 101828) = false := by
  decide +kernel

theorem node_context_11_101828_1396287 : EJMOriginalGlobalDAGData.nodes 10 ⟨1396287, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1396175, by decide⟩,⟨1396237, by decide⟩,⟨1396286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101828_1396287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101828 ⟨1396287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101828
    ⟨1396287, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1396175, by decide⟩,⟨1396237, by decide⟩,⟨1396286, by decide⟩]) unmarked_context_11_101828_1396287 node_context_11_101828_1396287
  intro a
  fin_cases a
  · exact context_12_407312_1108174
  · exact context_12_407313_1396175
  · exact context_12_407314_1396237
  · exact context_12_407315_1396286

theorem selected_cut_49371 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101829) = some ⟨11, 1, 0, 892405, 101829, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101829_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101829 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101829 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101829, 1, 262144⟩
    (by decide) selected_cut_49371

theorem selected_cut_49372 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407320) = some ⟨12, 1, 0, 1108174, 407320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407320_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407320 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407320 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407320, 1, 65536⟩
    (by decide) selected_cut_49372

theorem selected_cut_49373 : selected 9 ⟨1396327, by decide⟩
    (prefixPartial 12 407321) = some ⟨12, 2, 0, 1396327, 407321, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_407321_1396327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407321 ⟨1396327, by decide⟩ :=
  accepted_of_selected 12 407321 ⟨1396327, by decide⟩ ⟨12, 2, 0, 1396327, 407321, 1973, 65536⟩
    (by decide) selected_cut_49373

theorem selected_cut_49374 : selected 9 ⟨1396374, by decide⟩
    (prefixPartial 12 407322) = some ⟨12, 2, 0, 1396374, 407322, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_407322_1396374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407322 ⟨1396374, by decide⟩ :=
  accepted_of_selected 12 407322 ⟨1396374, by decide⟩ ⟨12, 2, 0, 1396374, 407322, 2181, 65536⟩
    (by decide) selected_cut_49374

theorem selected_cut_49375 : selected 9 ⟨1396415, by decide⟩
    (prefixPartial 12 407323) = some ⟨12, 2, 0, 1396415, 407323, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_407323_1396415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407323 ⟨1396415, by decide⟩ :=
  accepted_of_selected 12 407323 ⟨1396415, by decide⟩ ⟨12, 2, 0, 1396415, 407323, 1825, 65536⟩
    (by decide) selected_cut_49375

theorem unmarked_context_11_101830_1396416 : frontier 10 ⟨1396416, by decide⟩
    (prefixCache 11 101830) (prefixPartial 11 101830) = false := by
  decide +kernel

theorem node_context_11_101830_1396416 : EJMOriginalGlobalDAGData.nodes 10 ⟨1396416, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1396327, by decide⟩,⟨1396374, by decide⟩,⟨1396415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101830_1396416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101830 ⟨1396416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101830
    ⟨1396416, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1396327, by decide⟩,⟨1396374, by decide⟩,⟨1396415, by decide⟩]) unmarked_context_11_101830_1396416 node_context_11_101830_1396416
  intro a
  fin_cases a
  · exact context_12_407320_1108174
  · exact context_12_407321_1396327
  · exact context_12_407322_1396374
  · exact context_12_407323_1396415

theorem selected_cut_49376 : selected 10 ⟨1396513, by decide⟩
    (prefixPartial 11 101831) = some ⟨11, 2, 0, 1396513, 101831, 4077, 262144⟩ := by
  decide +kernel

theorem context_11_101831_1396513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101831 ⟨1396513, by decide⟩ :=
  accepted_of_selected 11 101831 ⟨1396513, by decide⟩ ⟨11, 2, 0, 1396513, 101831, 4077, 262144⟩
    (by decide) selected_cut_49376

theorem unmarked_context_10_25457_1396514 : frontier 11 ⟨1396514, by decide⟩
    (prefixCache 10 25457) (prefixPartial 10 25457) = false := by
  decide +kernel

theorem node_context_10_25457_1396514 : EJMOriginalGlobalDAGData.nodes 11 ⟨1396514, by decide⟩ =
    .split (coordinate 10) (![⟨1396287, by decide⟩,⟨892405, by decide⟩,⟨1396416, by decide⟩,⟨1396513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25457_1396514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25457 ⟨1396514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25457
    ⟨1396514, by decide⟩ (by decide) (![⟨1396287, by decide⟩,⟨892405, by decide⟩,⟨1396416, by decide⟩,⟨1396513, by decide⟩]) unmarked_context_10_25457_1396514 node_context_10_25457_1396514
  intro a
  fin_cases a
  · exact context_11_101828_1396287
  · exact context_11_101829_892405
  · exact context_11_101830_1396416
  · exact context_11_101831_1396513

theorem selected_cut_49377 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407328) = some ⟨12, 1, 0, 1108174, 407328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407328_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407328 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407328 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407328, 1, 65536⟩
    (by decide) selected_cut_49377

theorem selected_cut_49378 : selected 9 ⟨1396559, by decide⟩
    (prefixPartial 12 407329) = some ⟨12, 2, 0, 1396559, 407329, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_407329_1396559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407329 ⟨1396559, by decide⟩ :=
  accepted_of_selected 12 407329 ⟨1396559, by decide⟩ ⟨12, 2, 0, 1396559, 407329, 2073, 65536⟩
    (by decide) selected_cut_49378

theorem selected_cut_49379 : selected 9 ⟨1396627, by decide⟩
    (prefixPartial 12 407330) = some ⟨12, 2, 0, 1396627, 407330, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_407330_1396627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407330 ⟨1396627, by decide⟩ :=
  accepted_of_selected 12 407330 ⟨1396627, by decide⟩ ⟨12, 2, 0, 1396627, 407330, 2605, 65536⟩
    (by decide) selected_cut_49379

theorem selected_cut_49380 : selected 9 ⟨1396671, by decide⟩
    (prefixPartial 12 407331) = some ⟨12, 2, 0, 1396671, 407331, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_407331_1396671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407331 ⟨1396671, by decide⟩ :=
  accepted_of_selected 12 407331 ⟨1396671, by decide⟩ ⟨12, 2, 0, 1396671, 407331, 1981, 65536⟩
    (by decide) selected_cut_49380

theorem unmarked_context_11_101832_1396672 : frontier 10 ⟨1396672, by decide⟩
    (prefixCache 11 101832) (prefixPartial 11 101832) = false := by
  decide +kernel

theorem node_context_11_101832_1396672 : EJMOriginalGlobalDAGData.nodes 10 ⟨1396672, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1396559, by decide⟩,⟨1396627, by decide⟩,⟨1396671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101832_1396672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101832 ⟨1396672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101832
    ⟨1396672, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1396559, by decide⟩,⟨1396627, by decide⟩,⟨1396671, by decide⟩]) unmarked_context_11_101832_1396672 node_context_11_101832_1396672
  intro a
  fin_cases a
  · exact context_12_407328_1108174
  · exact context_12_407329_1396559
  · exact context_12_407330_1396627
  · exact context_12_407331_1396671

theorem selected_cut_49381 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407332) = some ⟨12, 1, 0, 1108174, 407332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407332_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407332 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407332 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407332, 1, 65536⟩
    (by decide) selected_cut_49381

theorem selected_cut_49382 : selected 9 ⟨1396703, by decide⟩
    (prefixPartial 12 407333) = some ⟨12, 2, 0, 1396703, 407333, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_407333_1396703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407333 ⟨1396703, by decide⟩ :=
  accepted_of_selected 12 407333 ⟨1396703, by decide⟩ ⟨12, 2, 0, 1396703, 407333, 1681, 65536⟩
    (by decide) selected_cut_49382

theorem selected_cut_49383 : selected 9 ⟨1396744, by decide⟩
    (prefixPartial 12 407334) = some ⟨12, 2, 0, 1396744, 407334, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_407334_1396744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407334 ⟨1396744, by decide⟩ :=
  accepted_of_selected 12 407334 ⟨1396744, by decide⟩ ⟨12, 2, 0, 1396744, 407334, 2017, 65536⟩
    (by decide) selected_cut_49383

theorem selected_cut_49384 : selected 9 ⟨1396769, by decide⟩
    (prefixPartial 12 407335) = some ⟨12, 2, 0, 1396769, 407335, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_407335_1396769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407335 ⟨1396769, by decide⟩ :=
  accepted_of_selected 12 407335 ⟨1396769, by decide⟩ ⟨12, 2, 0, 1396769, 407335, 1525, 65536⟩
    (by decide) selected_cut_49384

theorem unmarked_context_11_101833_1396770 : frontier 10 ⟨1396770, by decide⟩
    (prefixCache 11 101833) (prefixPartial 11 101833) = false := by
  decide +kernel

theorem node_context_11_101833_1396770 : EJMOriginalGlobalDAGData.nodes 10 ⟨1396770, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1396703, by decide⟩,⟨1396744, by decide⟩,⟨1396769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101833_1396770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101833 ⟨1396770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101833
    ⟨1396770, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1396703, by decide⟩,⟨1396744, by decide⟩,⟨1396769, by decide⟩]) unmarked_context_11_101833_1396770 node_context_11_101833_1396770
  intro a
  fin_cases a
  · exact context_12_407332_1108174
  · exact context_12_407333_1396703
  · exact context_12_407334_1396744
  · exact context_12_407335_1396769

theorem selected_cut_49385 : selected 10 ⟨1396810, by decide⟩
    (prefixPartial 11 101834) = some ⟨11, 2, 0, 1396810, 101834, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_101834_1396810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101834 ⟨1396810, by decide⟩ :=
  accepted_of_selected 11 101834 ⟨1396810, by decide⟩ ⟨11, 2, 0, 1396810, 101834, 1653, 262144⟩
    (by decide) selected_cut_49385

theorem selected_cut_49386 : selected 10 ⟨1396889, by decide⟩
    (prefixPartial 11 101835) = some ⟨11, 2, 0, 1396889, 101835, 3701, 262144⟩ := by
  decide +kernel

theorem context_11_101835_1396889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101835 ⟨1396889, by decide⟩ :=
  accepted_of_selected 11 101835 ⟨1396889, by decide⟩ ⟨11, 2, 0, 1396889, 101835, 3701, 262144⟩
    (by decide) selected_cut_49386

theorem unmarked_context_10_25458_1396890 : frontier 11 ⟨1396890, by decide⟩
    (prefixCache 10 25458) (prefixPartial 10 25458) = false := by
  decide +kernel

theorem node_context_10_25458_1396890 : EJMOriginalGlobalDAGData.nodes 11 ⟨1396890, by decide⟩ =
    .split (coordinate 10) (![⟨1396672, by decide⟩,⟨1396770, by decide⟩,⟨1396810, by decide⟩,⟨1396889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25458_1396890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25458 ⟨1396890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25458
    ⟨1396890, by decide⟩ (by decide) (![⟨1396672, by decide⟩,⟨1396770, by decide⟩,⟨1396810, by decide⟩,⟨1396889, by decide⟩]) unmarked_context_10_25458_1396890 node_context_10_25458_1396890
  intro a
  fin_cases a
  · exact context_11_101832_1396672
  · exact context_11_101833_1396770
  · exact context_11_101834_1396810
  · exact context_11_101835_1396889

theorem selected_cut_49387 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407344) = some ⟨12, 1, 0, 1108174, 407344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407344_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407344 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407344 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407344, 1, 65536⟩
    (by decide) selected_cut_49387

theorem selected_cut_49388 : selected 9 ⟨1396929, by decide⟩
    (prefixPartial 12 407345) = some ⟨12, 2, 0, 1396929, 407345, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_407345_1396929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407345 ⟨1396929, by decide⟩ :=
  accepted_of_selected 12 407345 ⟨1396929, by decide⟩ ⟨12, 2, 0, 1396929, 407345, 1901, 65536⟩
    (by decide) selected_cut_49388

theorem selected_cut_49389 : selected 9 ⟨1396972, by decide⟩
    (prefixPartial 12 407346) = some ⟨12, 2, 0, 1396972, 407346, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_407346_1396972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407346 ⟨1396972, by decide⟩ :=
  accepted_of_selected 12 407346 ⟨1396972, by decide⟩ ⟨12, 2, 0, 1396972, 407346, 2145, 65536⟩
    (by decide) selected_cut_49389

theorem selected_cut_49390 : selected 9 ⟨1397001, by decide⟩
    (prefixPartial 12 407347) = some ⟨12, 2, 0, 1397001, 407347, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_407347_1397001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407347 ⟨1397001, by decide⟩ :=
  accepted_of_selected 12 407347 ⟨1397001, by decide⟩ ⟨12, 2, 0, 1397001, 407347, 1669, 65536⟩
    (by decide) selected_cut_49390

theorem unmarked_context_11_101836_1397002 : frontier 10 ⟨1397002, by decide⟩
    (prefixCache 11 101836) (prefixPartial 11 101836) = false := by
  decide +kernel

theorem node_context_11_101836_1397002 : EJMOriginalGlobalDAGData.nodes 10 ⟨1397002, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1396929, by decide⟩,⟨1396972, by decide⟩,⟨1397001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101836_1397002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101836 ⟨1397002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101836
    ⟨1397002, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1396929, by decide⟩,⟨1396972, by decide⟩,⟨1397001, by decide⟩]) unmarked_context_11_101836_1397002 node_context_11_101836_1397002
  intro a
  fin_cases a
  · exact context_12_407344_1108174
  · exact context_12_407345_1396929
  · exact context_12_407346_1396972
  · exact context_12_407347_1397001

theorem selected_cut_49391 : selected 10 ⟨1397071, by decide⟩
    (prefixPartial 11 101837) = some ⟨11, 2, 0, 1397071, 101837, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_101837_1397071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101837 ⟨1397071, by decide⟩ :=
  accepted_of_selected 11 101837 ⟨1397071, by decide⟩ ⟨11, 2, 0, 1397071, 101837, 3137, 262144⟩
    (by decide) selected_cut_49391

theorem selected_cut_49392 : selected 10 ⟨1397128, by decide⟩
    (prefixPartial 11 101838) = some ⟨11, 2, 0, 1397128, 101838, 3133, 262144⟩ := by
  decide +kernel

theorem context_11_101838_1397128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101838 ⟨1397128, by decide⟩ :=
  accepted_of_selected 11 101838 ⟨1397128, by decide⟩ ⟨11, 2, 0, 1397128, 101838, 3133, 262144⟩
    (by decide) selected_cut_49392

theorem selected_cut_49393 : selected 10 ⟨1397199, by decide⟩
    (prefixPartial 11 101839) = some ⟨11, 2, 0, 1397199, 101839, 933, 262144⟩ := by
  decide +kernel

theorem context_11_101839_1397199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101839 ⟨1397199, by decide⟩ :=
  accepted_of_selected 11 101839 ⟨1397199, by decide⟩ ⟨11, 2, 0, 1397199, 101839, 933, 262144⟩
    (by decide) selected_cut_49393

theorem unmarked_context_10_25459_1397200 : frontier 11 ⟨1397200, by decide⟩
    (prefixCache 10 25459) (prefixPartial 10 25459) = false := by
  decide +kernel

theorem node_context_10_25459_1397200 : EJMOriginalGlobalDAGData.nodes 11 ⟨1397200, by decide⟩ =
    .split (coordinate 10) (![⟨1397002, by decide⟩,⟨1397071, by decide⟩,⟨1397128, by decide⟩,⟨1397199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25459_1397200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25459 ⟨1397200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25459
    ⟨1397200, by decide⟩ (by decide) (![⟨1397002, by decide⟩,⟨1397071, by decide⟩,⟨1397128, by decide⟩,⟨1397199, by decide⟩]) unmarked_context_10_25459_1397200 node_context_10_25459_1397200
  intro a
  fin_cases a
  · exact context_11_101836_1397002
  · exact context_11_101837_1397071
  · exact context_11_101838_1397128
  · exact context_11_101839_1397199

theorem unmarked_context_9_6364_1397201 : frontier 12 ⟨1397201, by decide⟩
    (prefixCache 9 6364) (prefixPartial 9 6364) = false := by
  decide +kernel

theorem node_context_9_6364_1397201 : EJMOriginalGlobalDAGData.nodes 12 ⟨1397201, by decide⟩ =
    .split (coordinate 9) (![⟨1396134, by decide⟩,⟨1396514, by decide⟩,⟨1396890, by decide⟩,⟨1397200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6364_1397201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6364 ⟨1397201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6364
    ⟨1397201, by decide⟩ (by decide) (![⟨1396134, by decide⟩,⟨1396514, by decide⟩,⟨1396890, by decide⟩,⟨1397200, by decide⟩]) unmarked_context_9_6364_1397201 node_context_9_6364_1397201
  intro a
  fin_cases a
  · exact context_10_25456_1396134
  · exact context_10_25457_1396514
  · exact context_10_25458_1396890
  · exact context_10_25459_1397200

theorem selected_cut_49394 : selected 10 ⟨1369428, by decide⟩
    (prefixPartial 11 101840) = some ⟨11, 1, 0, 1369428, 101840, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101840_1369428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101840 ⟨1369428, by decide⟩ :=
  accepted_of_selected 11 101840 ⟨1369428, by decide⟩ ⟨11, 1, 0, 1369428, 101840, 1, 262144⟩
    (by decide) selected_cut_49394

theorem selected_cut_49395 : selected 9 ⟨1397223, by decide⟩
    (prefixPartial 12 407364) = some ⟨12, 2, 0, 1397223, 407364, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_407364_1397223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407364 ⟨1397223, by decide⟩ :=
  accepted_of_selected 12 407364 ⟨1397223, by decide⟩ ⟨12, 2, 0, 1397223, 407364, 1357, 65536⟩
    (by decide) selected_cut_49395

theorem selected_cut_49396 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 407365) = some ⟨12, 1, 0, 642341, 407365, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407365_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407365 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 407365 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 407365, 1, 65536⟩
    (by decide) selected_cut_49396

theorem selected_cut_49397 : selected 9 ⟨1397241, by decide⟩
    (prefixPartial 12 407366) = some ⟨12, 2, 0, 1397241, 407366, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_407366_1397241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407366 ⟨1397241, by decide⟩ :=
  accepted_of_selected 12 407366 ⟨1397241, by decide⟩ ⟨12, 2, 0, 1397241, 407366, 1381, 65536⟩
    (by decide) selected_cut_49397

theorem selected_cut_49398 : selected 9 ⟨1397264, by decide⟩
    (prefixPartial 12 407367) = some ⟨12, 2, 0, 1397264, 407367, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_407367_1397264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407367 ⟨1397264, by decide⟩ :=
  accepted_of_selected 12 407367 ⟨1397264, by decide⟩ ⟨12, 2, 0, 1397264, 407367, 1381, 65536⟩
    (by decide) selected_cut_49398

theorem unmarked_context_11_101841_1397265 : frontier 10 ⟨1397265, by decide⟩
    (prefixCache 11 101841) (prefixPartial 11 101841) = false := by
  decide +kernel

theorem node_context_11_101841_1397265 : EJMOriginalGlobalDAGData.nodes 10 ⟨1397265, by decide⟩ =
    .split (coordinate 11) (![⟨1397223, by decide⟩,⟨642341, by decide⟩,⟨1397241, by decide⟩,⟨1397264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101841_1397265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101841 ⟨1397265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101841
    ⟨1397265, by decide⟩ (by decide) (![⟨1397223, by decide⟩,⟨642341, by decide⟩,⟨1397241, by decide⟩,⟨1397264, by decide⟩]) unmarked_context_11_101841_1397265 node_context_11_101841_1397265
  intro a
  fin_cases a
  · exact context_12_407364_1397223
  · exact context_12_407365_642341
  · exact context_12_407366_1397241
  · exact context_12_407367_1397264

theorem selected_cut_49399 : selected 9 ⟨1397287, by decide⟩
    (prefixPartial 12 407368) = some ⟨12, 2, 0, 1397287, 407368, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_407368_1397287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407368 ⟨1397287, by decide⟩ :=
  accepted_of_selected 12 407368 ⟨1397287, by decide⟩ ⟨12, 2, 0, 1397287, 407368, 1349, 65536⟩
    (by decide) selected_cut_49399

theorem selected_cut_49400 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 407369) = some ⟨12, 1, 0, 642341, 407369, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407369_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407369 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 407369 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 407369, 1, 65536⟩
    (by decide) selected_cut_49400

theorem selected_cut_49401 : selected 9 ⟨1397312, by decide⟩
    (prefixPartial 12 407370) = some ⟨12, 2, 0, 1397312, 407370, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_407370_1397312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407370 ⟨1397312, by decide⟩ :=
  accepted_of_selected 12 407370 ⟨1397312, by decide⟩ ⟨12, 2, 0, 1397312, 407370, 1421, 65536⟩
    (by decide) selected_cut_49401

theorem selected_cut_49402 : selected 9 ⟨1397337, by decide⟩
    (prefixPartial 12 407371) = some ⟨12, 2, 0, 1397337, 407371, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_407371_1397337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407371 ⟨1397337, by decide⟩ :=
  accepted_of_selected 12 407371 ⟨1397337, by decide⟩ ⟨12, 2, 0, 1397337, 407371, 1489, 65536⟩
    (by decide) selected_cut_49402

theorem unmarked_context_11_101842_1397338 : frontier 10 ⟨1397338, by decide⟩
    (prefixCache 11 101842) (prefixPartial 11 101842) = false := by
  decide +kernel

theorem node_context_11_101842_1397338 : EJMOriginalGlobalDAGData.nodes 10 ⟨1397338, by decide⟩ =
    .split (coordinate 11) (![⟨1397287, by decide⟩,⟨642341, by decide⟩,⟨1397312, by decide⟩,⟨1397337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101842_1397338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101842 ⟨1397338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101842
    ⟨1397338, by decide⟩ (by decide) (![⟨1397287, by decide⟩,⟨642341, by decide⟩,⟨1397312, by decide⟩,⟨1397337, by decide⟩]) unmarked_context_11_101842_1397338 node_context_11_101842_1397338
  intro a
  fin_cases a
  · exact context_12_407368_1397287
  · exact context_12_407369_642341
  · exact context_12_407370_1397312
  · exact context_12_407371_1397337

theorem selected_cut_49403 : selected 10 ⟨1397390, by decide⟩
    (prefixPartial 11 101843) = some ⟨11, 2, 0, 1397390, 101843, 2849, 262144⟩ := by
  decide +kernel

theorem context_11_101843_1397390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101843 ⟨1397390, by decide⟩ :=
  accepted_of_selected 11 101843 ⟨1397390, by decide⟩ ⟨11, 2, 0, 1397390, 101843, 2849, 262144⟩
    (by decide) selected_cut_49403

theorem unmarked_context_10_25460_1397391 : frontier 11 ⟨1397391, by decide⟩
    (prefixCache 10 25460) (prefixPartial 10 25460) = false := by
  decide +kernel

theorem node_context_10_25460_1397391 : EJMOriginalGlobalDAGData.nodes 11 ⟨1397391, by decide⟩ =
    .split (coordinate 10) (![⟨1369428, by decide⟩,⟨1397265, by decide⟩,⟨1397338, by decide⟩,⟨1397390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25460_1397391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25460 ⟨1397391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25460
    ⟨1397391, by decide⟩ (by decide) (![⟨1369428, by decide⟩,⟨1397265, by decide⟩,⟨1397338, by decide⟩,⟨1397390, by decide⟩]) unmarked_context_10_25460_1397391 node_context_10_25460_1397391
  intro a
  fin_cases a
  · exact context_11_101840_1369428
  · exact context_11_101841_1397265
  · exact context_11_101842_1397338
  · exact context_11_101843_1397390

theorem selected_cut_49404 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25461) = some ⟨10, 1, 0, 893098, 25461, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25461_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25461 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25461 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25461, 1, 1048576⟩
    (by decide) selected_cut_49404

theorem selected_cut_49405 : selected 9 ⟨1397420, by decide⟩
    (prefixPartial 12 407392) = some ⟨12, 2, 0, 1397420, 407392, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_407392_1397420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407392 ⟨1397420, by decide⟩ :=
  accepted_of_selected 12 407392 ⟨1397420, by decide⟩ ⟨12, 2, 0, 1397420, 407392, 1373, 65536⟩
    (by decide) selected_cut_49405

theorem selected_cut_49406 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 407393) = some ⟨12, 1, 0, 170504, 407393, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407393_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407393 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 407393 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 407393, 1, 65536⟩
    (by decide) selected_cut_49406

theorem selected_cut_49407 : selected 9 ⟨1397448, by decide⟩
    (prefixPartial 12 407394) = some ⟨12, 2, 0, 1397448, 407394, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_407394_1397448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407394 ⟨1397448, by decide⟩ :=
  accepted_of_selected 12 407394 ⟨1397448, by decide⟩ ⟨12, 2, 0, 1397448, 407394, 1417, 65536⟩
    (by decide) selected_cut_49407

theorem selected_cut_49408 : selected 9 ⟨1397477, by decide⟩
    (prefixPartial 12 407395) = some ⟨12, 2, 0, 1397477, 407395, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_407395_1397477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407395 ⟨1397477, by decide⟩ :=
  accepted_of_selected 12 407395 ⟨1397477, by decide⟩ ⟨12, 2, 0, 1397477, 407395, 1373, 65536⟩
    (by decide) selected_cut_49408

theorem unmarked_context_11_101848_1397478 : frontier 10 ⟨1397478, by decide⟩
    (prefixCache 11 101848) (prefixPartial 11 101848) = false := by
  decide +kernel

theorem node_context_11_101848_1397478 : EJMOriginalGlobalDAGData.nodes 10 ⟨1397478, by decide⟩ =
    .split (coordinate 11) (![⟨1397420, by decide⟩,⟨170504, by decide⟩,⟨1397448, by decide⟩,⟨1397477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101848_1397478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101848 ⟨1397478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101848
    ⟨1397478, by decide⟩ (by decide) (![⟨1397420, by decide⟩,⟨170504, by decide⟩,⟨1397448, by decide⟩,⟨1397477, by decide⟩]) unmarked_context_11_101848_1397478 node_context_11_101848_1397478
  intro a
  fin_cases a
  · exact context_12_407392_1397420
  · exact context_12_407393_170504
  · exact context_12_407394_1397448
  · exact context_12_407395_1397477

theorem selected_cut_49409 : selected 10 ⟨1397528, by decide⟩
    (prefixPartial 11 101849) = some ⟨11, 2, 0, 1397528, 101849, 3189, 262144⟩ := by
  decide +kernel

theorem context_11_101849_1397528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101849 ⟨1397528, by decide⟩ :=
  accepted_of_selected 11 101849 ⟨1397528, by decide⟩ ⟨11, 2, 0, 1397528, 101849, 3189, 262144⟩
    (by decide) selected_cut_49409

theorem selected_cut_49410 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 101850) = some ⟨11, 1, 0, 1369759, 101850, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101850_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101850 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 101850 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 101850, 1, 262144⟩
    (by decide) selected_cut_49410

theorem selected_cut_49411 : selected 10 ⟨1397585, by decide⟩
    (prefixPartial 11 101851) = some ⟨11, 2, 0, 1397585, 101851, 3109, 262144⟩ := by
  decide +kernel

theorem context_11_101851_1397585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101851 ⟨1397585, by decide⟩ :=
  accepted_of_selected 11 101851 ⟨1397585, by decide⟩ ⟨11, 2, 0, 1397585, 101851, 3109, 262144⟩
    (by decide) selected_cut_49411

theorem unmarked_context_10_25462_1397586 : frontier 11 ⟨1397586, by decide⟩
    (prefixCache 10 25462) (prefixPartial 10 25462) = false := by
  decide +kernel

theorem node_context_10_25462_1397586 : EJMOriginalGlobalDAGData.nodes 11 ⟨1397586, by decide⟩ =
    .split (coordinate 10) (![⟨1397478, by decide⟩,⟨1397528, by decide⟩,⟨1369759, by decide⟩,⟨1397585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25462_1397586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25462 ⟨1397586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25462
    ⟨1397586, by decide⟩ (by decide) (![⟨1397478, by decide⟩,⟨1397528, by decide⟩,⟨1369759, by decide⟩,⟨1397585, by decide⟩]) unmarked_context_10_25462_1397586 node_context_10_25462_1397586
  intro a
  fin_cases a
  · exact context_11_101848_1397478
  · exact context_11_101849_1397528
  · exact context_11_101850_1369759
  · exact context_11_101851_1397585

theorem selected_cut_49412 : selected 10 ⟨1397630, by decide⟩
    (prefixPartial 11 101852) = some ⟨11, 2, 0, 1397630, 101852, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_101852_1397630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101852 ⟨1397630, by decide⟩ :=
  accepted_of_selected 11 101852 ⟨1397630, by decide⟩ ⟨11, 2, 0, 1397630, 101852, 2449, 262144⟩
    (by decide) selected_cut_49412

theorem selected_cut_49413 : selected 10 ⟨1397682, by decide⟩
    (prefixPartial 11 101853) = some ⟨11, 2, 0, 1397682, 101853, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_101853_1397682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101853 ⟨1397682, by decide⟩ :=
  accepted_of_selected 11 101853 ⟨1397682, by decide⟩ ⟨11, 2, 0, 1397682, 101853, 2961, 262144⟩
    (by decide) selected_cut_49413

theorem selected_cut_49414 : selected 10 ⟨1397734, by decide⟩
    (prefixPartial 11 101854) = some ⟨11, 2, 0, 1397734, 101854, 2785, 262144⟩ := by
  decide +kernel

theorem context_11_101854_1397734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101854 ⟨1397734, by decide⟩ :=
  accepted_of_selected 11 101854 ⟨1397734, by decide⟩ ⟨11, 2, 0, 1397734, 101854, 2785, 262144⟩
    (by decide) selected_cut_49414

theorem selected_cut_49415 : selected 10 ⟨1370051, by decide⟩
    (prefixPartial 11 101855) = some ⟨11, 1, 0, 1370051, 101855, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101855_1370051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101855 ⟨1370051, by decide⟩ :=
  accepted_of_selected 11 101855 ⟨1370051, by decide⟩ ⟨11, 1, 0, 1370051, 101855, 1, 262144⟩
    (by decide) selected_cut_49415

theorem unmarked_context_10_25463_1397735 : frontier 11 ⟨1397735, by decide⟩
    (prefixCache 10 25463) (prefixPartial 10 25463) = false := by
  decide +kernel

theorem node_context_10_25463_1397735 : EJMOriginalGlobalDAGData.nodes 11 ⟨1397735, by decide⟩ =
    .split (coordinate 10) (![⟨1397630, by decide⟩,⟨1397682, by decide⟩,⟨1397734, by decide⟩,⟨1370051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25463_1397735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25463 ⟨1397735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25463
    ⟨1397735, by decide⟩ (by decide) (![⟨1397630, by decide⟩,⟨1397682, by decide⟩,⟨1397734, by decide⟩,⟨1370051, by decide⟩]) unmarked_context_10_25463_1397735 node_context_10_25463_1397735
  intro a
  fin_cases a
  · exact context_11_101852_1397630
  · exact context_11_101853_1397682
  · exact context_11_101854_1397734
  · exact context_11_101855_1370051

theorem unmarked_context_9_6365_1397736 : frontier 12 ⟨1397736, by decide⟩
    (prefixCache 9 6365) (prefixPartial 9 6365) = false := by
  decide +kernel

theorem node_context_9_6365_1397736 : EJMOriginalGlobalDAGData.nodes 12 ⟨1397736, by decide⟩ =
    .split (coordinate 9) (![⟨1397391, by decide⟩,⟨893098, by decide⟩,⟨1397586, by decide⟩,⟨1397735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6365_1397736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6365 ⟨1397736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6365
    ⟨1397736, by decide⟩ (by decide) (![⟨1397391, by decide⟩,⟨893098, by decide⟩,⟨1397586, by decide⟩,⟨1397735, by decide⟩]) unmarked_context_9_6365_1397736 node_context_9_6365_1397736
  intro a
  fin_cases a
  · exact context_10_25460_1397391
  · exact context_10_25461_893098
  · exact context_10_25462_1397586
  · exact context_10_25463_1397735

theorem selected_cut_49416 : selected 10 ⟨1397756, by decide⟩
    (prefixPartial 11 101856) = some ⟨11, 2, 0, 1397756, 101856, 889, 262144⟩ := by
  decide +kernel

theorem context_11_101856_1397756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101856 ⟨1397756, by decide⟩ :=
  accepted_of_selected 11 101856 ⟨1397756, by decide⟩ ⟨11, 2, 0, 1397756, 101856, 889, 262144⟩
    (by decide) selected_cut_49416

theorem selected_cut_49417 : selected 10 ⟨1397788, by decide⟩
    (prefixPartial 11 101857) = some ⟨11, 2, 0, 1397788, 101857, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_101857_1397788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101857 ⟨1397788, by decide⟩ :=
  accepted_of_selected 11 101857 ⟨1397788, by decide⟩ ⟨11, 2, 0, 1397788, 101857, 2241, 262144⟩
    (by decide) selected_cut_49417

theorem selected_cut_49418 : selected 10 ⟨1397817, by decide⟩
    (prefixPartial 11 101858) = some ⟨11, 2, 0, 1397817, 101858, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_101858_1397817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101858 ⟨1397817, by decide⟩ :=
  accepted_of_selected 11 101858 ⟨1397817, by decide⟩ ⟨11, 2, 0, 1397817, 101858, 2133, 262144⟩
    (by decide) selected_cut_49418

theorem selected_cut_49419 : selected 10 ⟨1397843, by decide⟩
    (prefixPartial 11 101859) = some ⟨11, 2, 0, 1397843, 101859, 1493, 262144⟩ := by
  decide +kernel

theorem context_11_101859_1397843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101859 ⟨1397843, by decide⟩ :=
  accepted_of_selected 11 101859 ⟨1397843, by decide⟩ ⟨11, 2, 0, 1397843, 101859, 1493, 262144⟩
    (by decide) selected_cut_49419

theorem unmarked_context_10_25464_1397844 : frontier 11 ⟨1397844, by decide⟩
    (prefixCache 10 25464) (prefixPartial 10 25464) = false := by
  decide +kernel

theorem node_context_10_25464_1397844 : EJMOriginalGlobalDAGData.nodes 11 ⟨1397844, by decide⟩ =
    .split (coordinate 10) (![⟨1397756, by decide⟩,⟨1397788, by decide⟩,⟨1397817, by decide⟩,⟨1397843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25464_1397844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25464 ⟨1397844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25464
    ⟨1397844, by decide⟩ (by decide) (![⟨1397756, by decide⟩,⟨1397788, by decide⟩,⟨1397817, by decide⟩,⟨1397843, by decide⟩]) unmarked_context_10_25464_1397844 node_context_10_25464_1397844
  intro a
  fin_cases a
  · exact context_11_101856_1397756
  · exact context_11_101857_1397788
  · exact context_11_101858_1397817
  · exact context_11_101859_1397843

theorem selected_cut_49420 : selected 10 ⟨1397879, by decide⟩
    (prefixPartial 11 101860) = some ⟨11, 2, 0, 1397879, 101860, 2105, 262144⟩ := by
  decide +kernel

theorem context_11_101860_1397879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101860 ⟨1397879, by decide⟩ :=
  accepted_of_selected 11 101860 ⟨1397879, by decide⟩ ⟨11, 2, 0, 1397879, 101860, 2105, 262144⟩
    (by decide) selected_cut_49420

theorem selected_cut_49421 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101861) = some ⟨11, 1, 0, 892405, 101861, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101861_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101861 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101861 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101861, 1, 262144⟩
    (by decide) selected_cut_49421

theorem selected_cut_49422 : selected 10 ⟨1397907, by decide⟩
    (prefixPartial 11 101862) = some ⟨11, 2, 0, 1397907, 101862, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_101862_1397907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101862 ⟨1397907, by decide⟩ :=
  accepted_of_selected 11 101862 ⟨1397907, by decide⟩ ⟨11, 2, 0, 1397907, 101862, 1753, 262144⟩
    (by decide) selected_cut_49422

theorem selected_cut_49423 : selected 10 ⟨1397937, by decide⟩
    (prefixPartial 11 101863) = some ⟨11, 2, 0, 1397937, 101863, 1605, 262144⟩ := by
  decide +kernel

theorem context_11_101863_1397937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101863 ⟨1397937, by decide⟩ :=
  accepted_of_selected 11 101863 ⟨1397937, by decide⟩ ⟨11, 2, 0, 1397937, 101863, 1605, 262144⟩
    (by decide) selected_cut_49423

theorem unmarked_context_10_25465_1397938 : frontier 11 ⟨1397938, by decide⟩
    (prefixCache 10 25465) (prefixPartial 10 25465) = false := by
  decide +kernel

theorem node_context_10_25465_1397938 : EJMOriginalGlobalDAGData.nodes 11 ⟨1397938, by decide⟩ =
    .split (coordinate 10) (![⟨1397879, by decide⟩,⟨892405, by decide⟩,⟨1397907, by decide⟩,⟨1397937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25465_1397938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25465 ⟨1397938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25465
    ⟨1397938, by decide⟩ (by decide) (![⟨1397879, by decide⟩,⟨892405, by decide⟩,⟨1397907, by decide⟩,⟨1397937, by decide⟩]) unmarked_context_10_25465_1397938 node_context_10_25465_1397938
  intro a
  fin_cases a
  · exact context_11_101860_1397879
  · exact context_11_101861_892405
  · exact context_11_101862_1397907
  · exact context_11_101863_1397937

theorem selected_cut_49424 : selected 11 ⟨1397954, by decide⟩
    (prefixPartial 10 25466) = some ⟨10, 2, 0, 1397954, 25466, 1009, 1048576⟩ := by
  decide +kernel

theorem context_10_25466_1397954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25466 ⟨1397954, by decide⟩ :=
  accepted_of_selected 10 25466 ⟨1397954, by decide⟩ ⟨10, 2, 0, 1397954, 25466, 1009, 1048576⟩
    (by decide) selected_cut_49424

theorem selected_cut_49425 : selected 11 ⟨1398038, by decide⟩
    (prefixPartial 10 25467) = some ⟨10, 2, 0, 1398038, 25467, 3937, 1048576⟩ := by
  decide +kernel

theorem context_10_25467_1398038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25467 ⟨1398038, by decide⟩ :=
  accepted_of_selected 10 25467 ⟨1398038, by decide⟩ ⟨10, 2, 0, 1398038, 25467, 3937, 1048576⟩
    (by decide) selected_cut_49425

theorem unmarked_context_9_6366_1398039 : frontier 12 ⟨1398039, by decide⟩
    (prefixCache 9 6366) (prefixPartial 9 6366) = false := by
  decide +kernel

theorem node_context_9_6366_1398039 : EJMOriginalGlobalDAGData.nodes 12 ⟨1398039, by decide⟩ =
    .split (coordinate 9) (![⟨1397844, by decide⟩,⟨1397938, by decide⟩,⟨1397954, by decide⟩,⟨1398038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6366_1398039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6366 ⟨1398039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6366
    ⟨1398039, by decide⟩ (by decide) (![⟨1397844, by decide⟩,⟨1397938, by decide⟩,⟨1397954, by decide⟩,⟨1398038, by decide⟩]) unmarked_context_9_6366_1398039 node_context_9_6366_1398039
  intro a
  fin_cases a
  · exact context_10_25464_1397844
  · exact context_10_25465_1397938
  · exact context_10_25466_1397954
  · exact context_10_25467_1398038

theorem selected_cut_49426 : selected 11 ⟨1398084, by decide⟩
    (prefixPartial 10 25468) = some ⟨10, 2, 0, 1398084, 25468, 2365, 1048576⟩ := by
  decide +kernel

theorem context_10_25468_1398084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25468 ⟨1398084, by decide⟩ :=
  accepted_of_selected 10 25468 ⟨1398084, by decide⟩ ⟨10, 2, 0, 1398084, 25468, 2365, 1048576⟩
    (by decide) selected_cut_49426

theorem selected_cut_49427 : selected 11 ⟨1398115, by decide⟩
    (prefixPartial 10 25469) = some ⟨10, 2, 0, 1398115, 25469, 1485, 1048576⟩ := by
  decide +kernel

theorem context_10_25469_1398115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25469 ⟨1398115, by decide⟩ :=
  accepted_of_selected 10 25469 ⟨1398115, by decide⟩ ⟨10, 2, 0, 1398115, 25469, 1485, 1048576⟩
    (by decide) selected_cut_49427

theorem selected_cut_49428 : selected 11 ⟨1398147, by decide⟩
    (prefixPartial 10 25470) = some ⟨10, 2, 0, 1398147, 25470, 1001, 1048576⟩ := by
  decide +kernel

theorem context_10_25470_1398147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25470 ⟨1398147, by decide⟩ :=
  accepted_of_selected 10 25470 ⟨1398147, by decide⟩ ⟨10, 2, 0, 1398147, 25470, 1001, 1048576⟩
    (by decide) selected_cut_49428

theorem selected_cut_49429 : selected 11 ⟨1398148, by decide⟩
    (prefixPartial 10 25471) = some ⟨10, 2, 0, 1398148, 25471, 81, 1048576⟩ := by
  decide +kernel

theorem context_10_25471_1398148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25471 ⟨1398148, by decide⟩ :=
  accepted_of_selected 10 25471 ⟨1398148, by decide⟩ ⟨10, 2, 0, 1398148, 25471, 81, 1048576⟩
    (by decide) selected_cut_49429

theorem unmarked_context_9_6367_1398149 : frontier 12 ⟨1398149, by decide⟩
    (prefixCache 9 6367) (prefixPartial 9 6367) = false := by
  decide +kernel

theorem node_context_9_6367_1398149 : EJMOriginalGlobalDAGData.nodes 12 ⟨1398149, by decide⟩ =
    .split (coordinate 9) (![⟨1398084, by decide⟩,⟨1398115, by decide⟩,⟨1398147, by decide⟩,⟨1398148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6367_1398149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6367 ⟨1398149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6367
    ⟨1398149, by decide⟩ (by decide) (![⟨1398084, by decide⟩,⟨1398115, by decide⟩,⟨1398147, by decide⟩,⟨1398148, by decide⟩]) unmarked_context_9_6367_1398149 node_context_9_6367_1398149
  intro a
  fin_cases a
  · exact context_10_25468_1398084
  · exact context_10_25469_1398115
  · exact context_10_25470_1398147
  · exact context_10_25471_1398148

theorem unmarked_context_8_1591_1398150 : frontier 13 ⟨1398150, by decide⟩
    (prefixCache 8 1591) (prefixPartial 8 1591) = false := by
  decide +kernel

theorem node_context_8_1591_1398150 : EJMOriginalGlobalDAGData.nodes 13 ⟨1398150, by decide⟩ =
    .split (coordinate 8) (![⟨1397201, by decide⟩,⟨1397736, by decide⟩,⟨1398039, by decide⟩,⟨1398149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1591_1398150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1591 ⟨1398150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1591
    ⟨1398150, by decide⟩ (by decide) (![⟨1397201, by decide⟩,⟨1397736, by decide⟩,⟨1398039, by decide⟩,⟨1398149, by decide⟩]) unmarked_context_8_1591_1398150 node_context_8_1591_1398150
  intro a
  fin_cases a
  · exact context_9_6364_1397201
  · exact context_9_6365_1397736
  · exact context_9_6366_1398039
  · exact context_9_6367_1398149

theorem unmarked_context_7_397_1398151 : frontier 14 ⟨1398151, by decide⟩
    (prefixCache 7 397) (prefixPartial 7 397) = false := by
  decide +kernel

theorem node_context_7_397_1398151 : EJMOriginalGlobalDAGData.nodes 14 ⟨1398151, by decide⟩ =
    .split (coordinate 7) (![⟨1391520, by decide⟩,⟨1393651, by decide⟩,⟨1396053, by decide⟩,⟨1398150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_397_1398151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 397 ⟨1398151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 397
    ⟨1398151, by decide⟩ (by decide) (![⟨1391520, by decide⟩,⟨1393651, by decide⟩,⟨1396053, by decide⟩,⟨1398150, by decide⟩]) unmarked_context_7_397_1398151 node_context_7_397_1398151
  intro a
  fin_cases a
  · exact context_8_1588_1391520
  · exact context_8_1589_1393651
  · exact context_8_1590_1396053
  · exact context_8_1591_1398150

theorem selected_cut_49430 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101888) = some ⟨11, 1, 0, 434745, 101888, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101888_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101888 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101888 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101888, 1, 262144⟩
    (by decide) selected_cut_49430

theorem selected_cut_49431 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101889) = some ⟨11, 1, 0, 434745, 101889, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101889_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101889 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101889 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101889, 1, 262144⟩
    (by decide) selected_cut_49431

theorem selected_cut_49432 : selected 10 ⟨1398210, by decide⟩
    (prefixPartial 11 101890) = some ⟨11, 2, 0, 1398210, 101890, 1977, 262144⟩ := by
  decide +kernel

theorem context_11_101890_1398210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101890 ⟨1398210, by decide⟩ :=
  accepted_of_selected 11 101890 ⟨1398210, by decide⟩ ⟨11, 2, 0, 1398210, 101890, 1977, 262144⟩
    (by decide) selected_cut_49432

theorem selected_cut_49433 : selected 10 ⟨1398292, by decide⟩
    (prefixPartial 11 101891) = some ⟨11, 2, 0, 1398292, 101891, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_101891_1398292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101891 ⟨1398292, by decide⟩ :=
  accepted_of_selected 11 101891 ⟨1398292, by decide⟩ ⟨11, 2, 0, 1398292, 101891, 2385, 262144⟩
    (by decide) selected_cut_49433

theorem unmarked_context_10_25472_1398293 : frontier 11 ⟨1398293, by decide⟩
    (prefixCache 10 25472) (prefixPartial 10 25472) = false := by
  decide +kernel

theorem node_context_10_25472_1398293 : EJMOriginalGlobalDAGData.nodes 11 ⟨1398293, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1398210, by decide⟩,⟨1398292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25472_1398293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25472 ⟨1398293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25472
    ⟨1398293, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1398210, by decide⟩,⟨1398292, by decide⟩]) unmarked_context_10_25472_1398293 node_context_10_25472_1398293
  intro a
  fin_cases a
  · exact context_11_101888_434745
  · exact context_11_101889_434745
  · exact context_11_101890_1398210
  · exact context_11_101891_1398292

theorem selected_cut_49434 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407568) = some ⟨12, 1, 0, 1108174, 407568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407568_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407568 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407568 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407568, 1, 65536⟩
    (by decide) selected_cut_49434

theorem selected_cut_49435 : selected 9 ⟨1398354, by decide⟩
    (prefixPartial 12 407569) = some ⟨12, 2, 0, 1398354, 407569, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_407569_1398354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407569 ⟨1398354, by decide⟩ :=
  accepted_of_selected 12 407569 ⟨1398354, by decide⟩ ⟨12, 2, 0, 1398354, 407569, 2085, 65536⟩
    (by decide) selected_cut_49435

theorem selected_cut_49436 : selected 9 ⟨1398398, by decide⟩
    (prefixPartial 12 407570) = some ⟨12, 2, 0, 1398398, 407570, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_407570_1398398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407570 ⟨1398398, by decide⟩ :=
  accepted_of_selected 12 407570 ⟨1398398, by decide⟩ ⟨12, 2, 0, 1398398, 407570, 1997, 65536⟩
    (by decide) selected_cut_49436

theorem selected_cut_49437 : selected 9 ⟨1398446, by decide⟩
    (prefixPartial 12 407571) = some ⟨12, 2, 0, 1398446, 407571, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_407571_1398446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407571 ⟨1398446, by decide⟩ :=
  accepted_of_selected 12 407571 ⟨1398446, by decide⟩ ⟨12, 2, 0, 1398446, 407571, 1901, 65536⟩
    (by decide) selected_cut_49437

theorem unmarked_context_11_101892_1398447 : frontier 10 ⟨1398447, by decide⟩
    (prefixCache 11 101892) (prefixPartial 11 101892) = false := by
  decide +kernel

theorem node_context_11_101892_1398447 : EJMOriginalGlobalDAGData.nodes 10 ⟨1398447, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1398354, by decide⟩,⟨1398398, by decide⟩,⟨1398446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101892_1398447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101892 ⟨1398447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101892
    ⟨1398447, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1398354, by decide⟩,⟨1398398, by decide⟩,⟨1398446, by decide⟩]) unmarked_context_11_101892_1398447 node_context_11_101892_1398447
  intro a
  fin_cases a
  · exact context_12_407568_1108174
  · exact context_12_407569_1398354
  · exact context_12_407570_1398398
  · exact context_12_407571_1398446

theorem selected_cut_49438 : selected 10 ⟨1398494, by decide⟩
    (prefixPartial 11 101893) = some ⟨11, 2, 0, 1398494, 101893, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_101893_1398494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101893 ⟨1398494, by decide⟩ :=
  accepted_of_selected 11 101893 ⟨1398494, by decide⟩ ⟨11, 2, 0, 1398494, 101893, 1949, 262144⟩
    (by decide) selected_cut_49438

theorem selected_cut_49439 : selected 10 ⟨1398594, by decide⟩
    (prefixPartial 11 101894) = some ⟨11, 2, 0, 1398594, 101894, 3993, 262144⟩ := by
  decide +kernel

theorem context_11_101894_1398594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101894 ⟨1398594, by decide⟩ :=
  accepted_of_selected 11 101894 ⟨1398594, by decide⟩ ⟨11, 2, 0, 1398594, 101894, 3993, 262144⟩
    (by decide) selected_cut_49439

theorem selected_cut_49440 : selected 10 ⟨1398693, by decide⟩
    (prefixPartial 11 101895) = some ⟨11, 2, 0, 1398693, 101895, 4041, 262144⟩ := by
  decide +kernel

theorem context_11_101895_1398693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101895 ⟨1398693, by decide⟩ :=
  accepted_of_selected 11 101895 ⟨1398693, by decide⟩ ⟨11, 2, 0, 1398693, 101895, 4041, 262144⟩
    (by decide) selected_cut_49440

theorem unmarked_context_10_25473_1398694 : frontier 11 ⟨1398694, by decide⟩
    (prefixCache 10 25473) (prefixPartial 10 25473) = false := by
  decide +kernel

theorem node_context_10_25473_1398694 : EJMOriginalGlobalDAGData.nodes 11 ⟨1398694, by decide⟩ =
    .split (coordinate 10) (![⟨1398447, by decide⟩,⟨1398494, by decide⟩,⟨1398594, by decide⟩,⟨1398693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25473_1398694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25473 ⟨1398694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25473
    ⟨1398694, by decide⟩ (by decide) (![⟨1398447, by decide⟩,⟨1398494, by decide⟩,⟨1398594, by decide⟩,⟨1398693, by decide⟩]) unmarked_context_10_25473_1398694 node_context_10_25473_1398694
  intro a
  fin_cases a
  · exact context_11_101892_1398447
  · exact context_11_101893_1398494
  · exact context_11_101894_1398594
  · exact context_11_101895_1398693

theorem selected_cut_49441 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407584) = some ⟨12, 1, 0, 1108174, 407584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407584_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407584 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407584 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407584, 1, 65536⟩
    (by decide) selected_cut_49441

theorem selected_cut_49442 : selected 9 ⟨1398733, by decide⟩
    (prefixPartial 12 407585) = some ⟨12, 2, 0, 1398733, 407585, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_407585_1398733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407585 ⟨1398733, by decide⟩ :=
  accepted_of_selected 12 407585 ⟨1398733, by decide⟩ ⟨12, 2, 0, 1398733, 407585, 1761, 65536⟩
    (by decide) selected_cut_49442

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
