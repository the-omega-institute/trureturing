/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover545
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_52419 : selected 10 ⟨1528179, by decide⟩
    (prefixPartial 11 289668) = some ⟨11, 2, 0, 1528179, 289668, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_289668_1528179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289668 ⟨1528179, by decide⟩ :=
  accepted_of_selected 11 289668 ⟨1528179, by decide⟩ ⟨11, 2, 0, 1528179, 289668, 1641, 262144⟩
    (by decide) selected_cut_52419

theorem selected_cut_52420 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289669) = some ⟨11, 1, 0, 1468419, 289669, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289669_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289669 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289669 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289669, 1, 262144⟩
    (by decide) selected_cut_52420

theorem selected_cut_52421 : selected 10 ⟨1528278, by decide⟩
    (prefixPartial 11 289670) = some ⟨11, 2, 0, 1528278, 289670, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_289670_1528278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289670 ⟨1528278, by decide⟩ :=
  accepted_of_selected 11 289670 ⟨1528278, by decide⟩ ⟨11, 2, 0, 1528278, 289670, 2917, 262144⟩
    (by decide) selected_cut_52421

theorem selected_cut_52422 : selected 10 ⟨1528370, by decide⟩
    (prefixPartial 11 289671) = some ⟨11, 2, 0, 1528370, 289671, 2597, 262144⟩ := by
  decide +kernel

theorem context_11_289671_1528370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289671 ⟨1528370, by decide⟩ :=
  accepted_of_selected 11 289671 ⟨1528370, by decide⟩ ⟨11, 2, 0, 1528370, 289671, 2597, 262144⟩
    (by decide) selected_cut_52422

theorem unmarked_context_10_72417_1528371 : frontier 11 ⟨1528371, by decide⟩
    (prefixCache 10 72417) (prefixPartial 10 72417) = false := by
  decide +kernel

theorem node_context_10_72417_1528371 : EJMOriginalGlobalDAGData.nodes 11 ⟨1528371, by decide⟩ =
    .split (coordinate 10) (![⟨1528179, by decide⟩,⟨1468419, by decide⟩,⟨1528278, by decide⟩,⟨1528370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72417_1528371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72417 ⟨1528371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72417
    ⟨1528371, by decide⟩ (by decide) (![⟨1528179, by decide⟩,⟨1468419, by decide⟩,⟨1528278, by decide⟩,⟨1528370, by decide⟩]) unmarked_context_10_72417_1528371 node_context_10_72417_1528371
  intro a
  fin_cases a
  · exact context_11_289668_1528179
  · exact context_11_289669_1468419
  · exact context_11_289670_1528278
  · exact context_11_289671_1528370

theorem selected_cut_52423 : selected 10 ⟨1528430, by decide⟩
    (prefixPartial 11 289672) = some ⟨11, 2, 0, 1528430, 289672, 2497, 262144⟩ := by
  decide +kernel

theorem context_11_289672_1528430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289672 ⟨1528430, by decide⟩ :=
  accepted_of_selected 11 289672 ⟨1528430, by decide⟩ ⟨11, 2, 0, 1528430, 289672, 2497, 262144⟩
    (by decide) selected_cut_52423

theorem selected_cut_52424 : selected 10 ⟨1528451, by decide⟩
    (prefixPartial 11 289673) = some ⟨11, 2, 0, 1528451, 289673, 1049, 262144⟩ := by
  decide +kernel

theorem context_11_289673_1528451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289673 ⟨1528451, by decide⟩ :=
  accepted_of_selected 11 289673 ⟨1528451, by decide⟩ ⟨11, 2, 0, 1528451, 289673, 1049, 262144⟩
    (by decide) selected_cut_52424

theorem selected_cut_52425 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 289674) = some ⟨11, 1, 0, 1468743, 289674, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289674_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289674 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 289674 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 289674, 1, 262144⟩
    (by decide) selected_cut_52425

theorem selected_cut_52426 : selected 10 ⟨1528483, by decide⟩
    (prefixPartial 11 289675) = some ⟨11, 2, 0, 1528483, 289675, 1053, 262144⟩ := by
  decide +kernel

theorem context_11_289675_1528483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289675 ⟨1528483, by decide⟩ :=
  accepted_of_selected 11 289675 ⟨1528483, by decide⟩ ⟨11, 2, 0, 1528483, 289675, 1053, 262144⟩
    (by decide) selected_cut_52426

theorem unmarked_context_10_72418_1528484 : frontier 11 ⟨1528484, by decide⟩
    (prefixCache 10 72418) (prefixPartial 10 72418) = false := by
  decide +kernel

theorem node_context_10_72418_1528484 : EJMOriginalGlobalDAGData.nodes 11 ⟨1528484, by decide⟩ =
    .split (coordinate 10) (![⟨1528430, by decide⟩,⟨1528451, by decide⟩,⟨1468743, by decide⟩,⟨1528483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72418_1528484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72418 ⟨1528484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72418
    ⟨1528484, by decide⟩ (by decide) (![⟨1528430, by decide⟩,⟨1528451, by decide⟩,⟨1468743, by decide⟩,⟨1528483, by decide⟩]) unmarked_context_10_72418_1528484 node_context_10_72418_1528484
  intro a
  fin_cases a
  · exact context_11_289672_1528430
  · exact context_11_289673_1528451
  · exact context_11_289674_1468743
  · exact context_11_289675_1528483

theorem selected_cut_52427 : selected 11 ⟨1528548, by decide⟩
    (prefixPartial 10 72419) = some ⟨10, 2, 0, 1528548, 72419, 2469, 1048576⟩ := by
  decide +kernel

theorem context_10_72419_1528548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72419 ⟨1528548, by decide⟩ :=
  accepted_of_selected 10 72419 ⟨1528548, by decide⟩ ⟨10, 2, 0, 1528548, 72419, 2469, 1048576⟩
    (by decide) selected_cut_52427

theorem unmarked_context_9_18104_1528549 : frontier 12 ⟨1528549, by decide⟩
    (prefixCache 9 18104) (prefixPartial 9 18104) = false := by
  decide +kernel

theorem node_context_9_18104_1528549 : EJMOriginalGlobalDAGData.nodes 12 ⟨1528549, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1528371, by decide⟩,⟨1528484, by decide⟩,⟨1528548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18104_1528549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18104 ⟨1528549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18104
    ⟨1528549, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1528371, by decide⟩,⟨1528484, by decide⟩,⟨1528548, by decide⟩]) unmarked_context_9_18104_1528549 node_context_9_18104_1528549
  intro a
  fin_cases a
  · exact context_10_72416_1468246
  · exact context_10_72417_1528371
  · exact context_10_72418_1528484
  · exact context_10_72419_1528548

theorem selected_cut_52428 : selected 11 ⟨1528639, by decide⟩
    (prefixPartial 10 72420) = some ⟨10, 2, 0, 1528639, 72420, 3785, 1048576⟩ := by
  decide +kernel

theorem context_10_72420_1528639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72420 ⟨1528639, by decide⟩ :=
  accepted_of_selected 10 72420 ⟨1528639, by decide⟩ ⟨10, 2, 0, 1528639, 72420, 3785, 1048576⟩
    (by decide) selected_cut_52428

theorem selected_cut_52429 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72421) = some ⟨10, 1, 0, 1468874, 72421, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72421_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72421 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72421 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72421, 1, 1048576⟩
    (by decide) selected_cut_52429

theorem selected_cut_52430 : selected 11 ⟨1528740, by decide⟩
    (prefixPartial 10 72422) = some ⟨10, 2, 0, 1528740, 72422, 3441, 1048576⟩ := by
  decide +kernel

theorem context_10_72422_1528740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72422 ⟨1528740, by decide⟩ :=
  accepted_of_selected 10 72422 ⟨1528740, by decide⟩ ⟨10, 2, 0, 1528740, 72422, 3441, 1048576⟩
    (by decide) selected_cut_52430

theorem selected_cut_52431 : selected 11 ⟨1528795, by decide⟩
    (prefixPartial 10 72423) = some ⟨10, 2, 0, 1528795, 72423, 1909, 1048576⟩ := by
  decide +kernel

theorem context_10_72423_1528795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72423 ⟨1528795, by decide⟩ :=
  accepted_of_selected 10 72423 ⟨1528795, by decide⟩ ⟨10, 2, 0, 1528795, 72423, 1909, 1048576⟩
    (by decide) selected_cut_52431

theorem unmarked_context_9_18105_1528796 : frontier 12 ⟨1528796, by decide⟩
    (prefixCache 9 18105) (prefixPartial 9 18105) = false := by
  decide +kernel

theorem node_context_9_18105_1528796 : EJMOriginalGlobalDAGData.nodes 12 ⟨1528796, by decide⟩ =
    .split (coordinate 9) (![⟨1528639, by decide⟩,⟨1468874, by decide⟩,⟨1528740, by decide⟩,⟨1528795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18105_1528796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18105 ⟨1528796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18105
    ⟨1528796, by decide⟩ (by decide) (![⟨1528639, by decide⟩,⟨1468874, by decide⟩,⟨1528740, by decide⟩,⟨1528795, by decide⟩]) unmarked_context_9_18105_1528796 node_context_9_18105_1528796
  intro a
  fin_cases a
  · exact context_10_72420_1528639
  · exact context_10_72421_1468874
  · exact context_10_72422_1528740
  · exact context_10_72423_1528795

theorem selected_cut_52432 : selected 12 ⟨1528916, by decide⟩
    (prefixPartial 9 18106) = some ⟨9, 2, 0, 1528916, 18106, 3917, 4194304⟩ := by
  decide +kernel

theorem context_9_18106_1528916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18106 ⟨1528916, by decide⟩ :=
  accepted_of_selected 9 18106 ⟨1528916, by decide⟩ ⟨9, 2, 0, 1528916, 18106, 3917, 4194304⟩
    (by decide) selected_cut_52432

theorem selected_cut_52433 : selected 12 ⟨1528946, by decide⟩
    (prefixPartial 9 18107) = some ⟨9, 2, 0, 1528946, 18107, 1213, 4194304⟩ := by
  decide +kernel

theorem context_9_18107_1528946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18107 ⟨1528946, by decide⟩ :=
  accepted_of_selected 9 18107 ⟨1528946, by decide⟩ ⟨9, 2, 0, 1528946, 18107, 1213, 4194304⟩
    (by decide) selected_cut_52433

theorem unmarked_context_8_4526_1528947 : frontier 13 ⟨1528947, by decide⟩
    (prefixCache 8 4526) (prefixPartial 8 4526) = false := by
  decide +kernel

theorem node_context_8_4526_1528947 : EJMOriginalGlobalDAGData.nodes 13 ⟨1528947, by decide⟩ =
    .split (coordinate 8) (![⟨1528549, by decide⟩,⟨1528796, by decide⟩,⟨1528916, by decide⟩,⟨1528946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4526_1528947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4526 ⟨1528947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4526
    ⟨1528947, by decide⟩ (by decide) (![⟨1528549, by decide⟩,⟨1528796, by decide⟩,⟨1528916, by decide⟩,⟨1528946, by decide⟩]) unmarked_context_8_4526_1528947 node_context_8_4526_1528947
  intro a
  fin_cases a
  · exact context_9_18104_1528549
  · exact context_9_18105_1528796
  · exact context_9_18106_1528916
  · exact context_9_18107_1528946

theorem selected_cut_52434 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72432) = some ⟨10, 1, 0, 1468246, 72432, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72432_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72432 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72432 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72432, 1, 1048576⟩
    (by decide) selected_cut_52434

theorem selected_cut_52435 : selected 10 ⟨1529028, by decide⟩
    (prefixPartial 11 289732) = some ⟨11, 2, 0, 1529028, 289732, 2945, 262144⟩ := by
  decide +kernel

theorem context_11_289732_1529028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289732 ⟨1529028, by decide⟩ :=
  accepted_of_selected 11 289732 ⟨1529028, by decide⟩ ⟨11, 2, 0, 1529028, 289732, 2945, 262144⟩
    (by decide) selected_cut_52435

theorem selected_cut_52436 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289733) = some ⟨11, 1, 0, 1468419, 289733, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289733_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289733 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289733 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289733, 1, 262144⟩
    (by decide) selected_cut_52436

theorem selected_cut_52437 : selected 10 ⟨1529109, by decide⟩
    (prefixPartial 11 289734) = some ⟨11, 2, 0, 1529109, 289734, 2753, 262144⟩ := by
  decide +kernel

theorem context_11_289734_1529109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289734 ⟨1529109, by decide⟩ :=
  accepted_of_selected 11 289734 ⟨1529109, by decide⟩ ⟨11, 2, 0, 1529109, 289734, 2753, 262144⟩
    (by decide) selected_cut_52437

theorem selected_cut_52438 : selected 10 ⟨1529136, by decide⟩
    (prefixPartial 11 289735) = some ⟨11, 2, 0, 1529136, 289735, 1137, 262144⟩ := by
  decide +kernel

theorem context_11_289735_1529136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289735 ⟨1529136, by decide⟩ :=
  accepted_of_selected 11 289735 ⟨1529136, by decide⟩ ⟨11, 2, 0, 1529136, 289735, 1137, 262144⟩
    (by decide) selected_cut_52438

theorem unmarked_context_10_72433_1529137 : frontier 11 ⟨1529137, by decide⟩
    (prefixCache 10 72433) (prefixPartial 10 72433) = false := by
  decide +kernel

theorem node_context_10_72433_1529137 : EJMOriginalGlobalDAGData.nodes 11 ⟨1529137, by decide⟩ =
    .split (coordinate 10) (![⟨1529028, by decide⟩,⟨1468419, by decide⟩,⟨1529109, by decide⟩,⟨1529136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72433_1529137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72433 ⟨1529137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72433
    ⟨1529137, by decide⟩ (by decide) (![⟨1529028, by decide⟩,⟨1468419, by decide⟩,⟨1529109, by decide⟩,⟨1529136, by decide⟩]) unmarked_context_10_72433_1529137 node_context_10_72433_1529137
  intro a
  fin_cases a
  · exact context_11_289732_1529028
  · exact context_11_289733_1468419
  · exact context_11_289734_1529109
  · exact context_11_289735_1529136

theorem selected_cut_52439 : selected 11 ⟨1529231, by decide⟩
    (prefixPartial 10 72434) = some ⟨10, 2, 0, 1529231, 72434, 3521, 1048576⟩ := by
  decide +kernel

theorem context_10_72434_1529231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72434 ⟨1529231, by decide⟩ :=
  accepted_of_selected 10 72434 ⟨1529231, by decide⟩ ⟨10, 2, 0, 1529231, 72434, 3521, 1048576⟩
    (by decide) selected_cut_52439

theorem selected_cut_52440 : selected 11 ⟨1529288, by decide⟩
    (prefixPartial 10 72435) = some ⟨10, 2, 0, 1529288, 72435, 2565, 1048576⟩ := by
  decide +kernel

theorem context_10_72435_1529288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72435 ⟨1529288, by decide⟩ :=
  accepted_of_selected 10 72435 ⟨1529288, by decide⟩ ⟨10, 2, 0, 1529288, 72435, 2565, 1048576⟩
    (by decide) selected_cut_52440

theorem unmarked_context_9_18108_1529289 : frontier 12 ⟨1529289, by decide⟩
    (prefixCache 9 18108) (prefixPartial 9 18108) = false := by
  decide +kernel

theorem node_context_9_18108_1529289 : EJMOriginalGlobalDAGData.nodes 12 ⟨1529289, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1529137, by decide⟩,⟨1529231, by decide⟩,⟨1529288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18108_1529289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18108 ⟨1529289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18108
    ⟨1529289, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1529137, by decide⟩,⟨1529231, by decide⟩,⟨1529288, by decide⟩]) unmarked_context_9_18108_1529289 node_context_9_18108_1529289
  intro a
  fin_cases a
  · exact context_10_72432_1468246
  · exact context_10_72433_1529137
  · exact context_10_72434_1529231
  · exact context_10_72435_1529288

theorem selected_cut_52441 : selected 11 ⟨1529358, by decide⟩
    (prefixPartial 10 72436) = some ⟨10, 2, 0, 1529358, 72436, 2809, 1048576⟩ := by
  decide +kernel

theorem context_10_72436_1529358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72436 ⟨1529358, by decide⟩ :=
  accepted_of_selected 10 72436 ⟨1529358, by decide⟩ ⟨10, 2, 0, 1529358, 72436, 2809, 1048576⟩
    (by decide) selected_cut_52441

theorem selected_cut_52442 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72437) = some ⟨10, 1, 0, 1468874, 72437, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72437_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72437 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72437 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72437, 1, 1048576⟩
    (by decide) selected_cut_52442

theorem selected_cut_52443 : selected 11 ⟨1529435, by decide⟩
    (prefixPartial 10 72438) = some ⟨10, 2, 0, 1529435, 72438, 2837, 1048576⟩ := by
  decide +kernel

theorem context_10_72438_1529435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72438 ⟨1529435, by decide⟩ :=
  accepted_of_selected 10 72438 ⟨1529435, by decide⟩ ⟨10, 2, 0, 1529435, 72438, 2837, 1048576⟩
    (by decide) selected_cut_52443

theorem selected_cut_52444 : selected 11 ⟨1529480, by decide⟩
    (prefixPartial 10 72439) = some ⟨10, 2, 0, 1529480, 72439, 1969, 1048576⟩ := by
  decide +kernel

theorem context_10_72439_1529480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72439 ⟨1529480, by decide⟩ :=
  accepted_of_selected 10 72439 ⟨1529480, by decide⟩ ⟨10, 2, 0, 1529480, 72439, 1969, 1048576⟩
    (by decide) selected_cut_52444

theorem unmarked_context_9_18109_1529481 : frontier 12 ⟨1529481, by decide⟩
    (prefixCache 9 18109) (prefixPartial 9 18109) = false := by
  decide +kernel

theorem node_context_9_18109_1529481 : EJMOriginalGlobalDAGData.nodes 12 ⟨1529481, by decide⟩ =
    .split (coordinate 9) (![⟨1529358, by decide⟩,⟨1468874, by decide⟩,⟨1529435, by decide⟩,⟨1529480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18109_1529481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18109 ⟨1529481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18109
    ⟨1529481, by decide⟩ (by decide) (![⟨1529358, by decide⟩,⟨1468874, by decide⟩,⟨1529435, by decide⟩,⟨1529480, by decide⟩]) unmarked_context_9_18109_1529481 node_context_9_18109_1529481
  intro a
  fin_cases a
  · exact context_10_72436_1529358
  · exact context_10_72437_1468874
  · exact context_10_72438_1529435
  · exact context_10_72439_1529480

theorem selected_cut_52445 : selected 12 ⟨1529587, by decide⟩
    (prefixPartial 9 18110) = some ⟨9, 2, 0, 1529587, 18110, 3685, 4194304⟩ := by
  decide +kernel

theorem context_9_18110_1529587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18110 ⟨1529587, by decide⟩ :=
  accepted_of_selected 9 18110 ⟨1529587, by decide⟩ ⟨9, 2, 0, 1529587, 18110, 3685, 4194304⟩
    (by decide) selected_cut_52445

theorem selected_cut_52446 : selected 12 ⟨1529633, by decide⟩
    (prefixPartial 9 18111) = some ⟨9, 2, 0, 1529633, 18111, 1569, 4194304⟩ := by
  decide +kernel

theorem context_9_18111_1529633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18111 ⟨1529633, by decide⟩ :=
  accepted_of_selected 9 18111 ⟨1529633, by decide⟩ ⟨9, 2, 0, 1529633, 18111, 1569, 4194304⟩
    (by decide) selected_cut_52446

theorem unmarked_context_8_4527_1529634 : frontier 13 ⟨1529634, by decide⟩
    (prefixCache 8 4527) (prefixPartial 8 4527) = false := by
  decide +kernel

theorem node_context_8_4527_1529634 : EJMOriginalGlobalDAGData.nodes 13 ⟨1529634, by decide⟩ =
    .split (coordinate 8) (![⟨1529289, by decide⟩,⟨1529481, by decide⟩,⟨1529587, by decide⟩,⟨1529633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4527_1529634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4527 ⟨1529634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4527
    ⟨1529634, by decide⟩ (by decide) (![⟨1529289, by decide⟩,⟨1529481, by decide⟩,⟨1529587, by decide⟩,⟨1529633, by decide⟩]) unmarked_context_8_4527_1529634 node_context_8_4527_1529634
  intro a
  fin_cases a
  · exact context_9_18108_1529289
  · exact context_9_18109_1529481
  · exact context_9_18110_1529587
  · exact context_9_18111_1529633

theorem unmarked_context_7_1131_1529635 : frontier 14 ⟨1529635, by decide⟩
    (prefixCache 7 1131) (prefixPartial 7 1131) = false := by
  decide +kernel

theorem node_context_7_1131_1529635 : EJMOriginalGlobalDAGData.nodes 14 ⟨1529635, by decide⟩ =
    .split (coordinate 7) (![⟨1527428, by decide⟩,⟨1528133, by decide⟩,⟨1528947, by decide⟩,⟨1529634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1131_1529635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1131 ⟨1529635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1131
    ⟨1529635, by decide⟩ (by decide) (![⟨1527428, by decide⟩,⟨1528133, by decide⟩,⟨1528947, by decide⟩,⟨1529634, by decide⟩]) unmarked_context_7_1131_1529635 node_context_7_1131_1529635
  intro a
  fin_cases a
  · exact context_8_4524_1527428
  · exact context_8_4525_1528133
  · exact context_8_4526_1528947
  · exact context_8_4527_1529634

theorem unmarked_context_6_282_1529636 : frontier 15 ⟨1529636, by decide⟩
    (prefixCache 6 282) (prefixPartial 6 282) = false := by
  decide +kernel

theorem node_context_6_282_1529636 : EJMOriginalGlobalDAGData.nodes 15 ⟨1529636, by decide⟩ =
    .split (coordinate 6) (![⟨1522548, by decide⟩,⟨1525059, by decide⟩,⟨1526686, by decide⟩,⟨1529635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_282_1529636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 282 ⟨1529636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 282
    ⟨1529636, by decide⟩ (by decide) (![⟨1522548, by decide⟩,⟨1525059, by decide⟩,⟨1526686, by decide⟩,⟨1529635, by decide⟩]) unmarked_context_6_282_1529636 node_context_6_282_1529636
  intro a
  fin_cases a
  · exact context_7_1128_1522548
  · exact context_7_1129_1525059
  · exact context_7_1130_1526686
  · exact context_7_1131_1529635

theorem selected_cut_52447 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72448) = some ⟨10, 1, 0, 1468246, 72448, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72448_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72448 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72448 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72448, 1, 1048576⟩
    (by decide) selected_cut_52447

theorem selected_cut_52448 : selected 10 ⟨1529667, by decide⟩
    (prefixPartial 11 289796) = some ⟨11, 2, 0, 1529667, 289796, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_289796_1529667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289796 ⟨1529667, by decide⟩ :=
  accepted_of_selected 11 289796 ⟨1529667, by decide⟩ ⟨11, 2, 0, 1529667, 289796, 1169, 262144⟩
    (by decide) selected_cut_52448

theorem selected_cut_52449 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289797) = some ⟨11, 1, 0, 1468419, 289797, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289797_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289797 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289797 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289797, 1, 262144⟩
    (by decide) selected_cut_52449

theorem selected_cut_52450 : selected 10 ⟨1529704, by decide⟩
    (prefixPartial 11 289798) = some ⟨11, 2, 0, 1529704, 289798, 1205, 262144⟩ := by
  decide +kernel

theorem context_11_289798_1529704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289798 ⟨1529704, by decide⟩ :=
  accepted_of_selected 11 289798 ⟨1529704, by decide⟩ ⟨11, 2, 0, 1529704, 289798, 1205, 262144⟩
    (by decide) selected_cut_52450

theorem selected_cut_52451 : selected 10 ⟨1529777, by decide⟩
    (prefixPartial 11 289799) = some ⟨11, 2, 0, 1529777, 289799, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_289799_1529777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289799 ⟨1529777, by decide⟩ :=
  accepted_of_selected 11 289799 ⟨1529777, by decide⟩ ⟨11, 2, 0, 1529777, 289799, 2397, 262144⟩
    (by decide) selected_cut_52451

theorem unmarked_context_10_72449_1529778 : frontier 11 ⟨1529778, by decide⟩
    (prefixCache 10 72449) (prefixPartial 10 72449) = false := by
  decide +kernel

theorem node_context_10_72449_1529778 : EJMOriginalGlobalDAGData.nodes 11 ⟨1529778, by decide⟩ =
    .split (coordinate 10) (![⟨1529667, by decide⟩,⟨1468419, by decide⟩,⟨1529704, by decide⟩,⟨1529777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72449_1529778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72449 ⟨1529778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72449
    ⟨1529778, by decide⟩ (by decide) (![⟨1529667, by decide⟩,⟨1468419, by decide⟩,⟨1529704, by decide⟩,⟨1529777, by decide⟩]) unmarked_context_10_72449_1529778 node_context_10_72449_1529778
  intro a
  fin_cases a
  · exact context_11_289796_1529667
  · exact context_11_289797_1468419
  · exact context_11_289798_1529704
  · exact context_11_289799_1529777

theorem selected_cut_52452 : selected 11 ⟨1529861, by decide⟩
    (prefixPartial 10 72450) = some ⟨10, 2, 0, 1529861, 72450, 3809, 1048576⟩ := by
  decide +kernel

theorem context_10_72450_1529861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72450 ⟨1529861, by decide⟩ :=
  accepted_of_selected 10 72450 ⟨1529861, by decide⟩ ⟨10, 2, 0, 1529861, 72450, 3809, 1048576⟩
    (by decide) selected_cut_52452

theorem selected_cut_52453 : selected 11 ⟨1529947, by decide⟩
    (prefixPartial 10 72451) = some ⟨10, 2, 0, 1529947, 72451, 2877, 1048576⟩ := by
  decide +kernel

theorem context_10_72451_1529947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72451 ⟨1529947, by decide⟩ :=
  accepted_of_selected 10 72451 ⟨1529947, by decide⟩ ⟨10, 2, 0, 1529947, 72451, 2877, 1048576⟩
    (by decide) selected_cut_52453

theorem unmarked_context_9_18112_1529948 : frontier 12 ⟨1529948, by decide⟩
    (prefixCache 9 18112) (prefixPartial 9 18112) = false := by
  decide +kernel

theorem node_context_9_18112_1529948 : EJMOriginalGlobalDAGData.nodes 12 ⟨1529948, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1529778, by decide⟩,⟨1529861, by decide⟩,⟨1529947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18112_1529948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18112 ⟨1529948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18112
    ⟨1529948, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1529778, by decide⟩,⟨1529861, by decide⟩,⟨1529947, by decide⟩]) unmarked_context_9_18112_1529948 node_context_9_18112_1529948
  intro a
  fin_cases a
  · exact context_10_72448_1468246
  · exact context_10_72449_1529778
  · exact context_10_72450_1529861
  · exact context_10_72451_1529947

theorem selected_cut_52454 : selected 11 ⟨1530018, by decide⟩
    (prefixPartial 10 72452) = some ⟨10, 2, 0, 1530018, 72452, 2689, 1048576⟩ := by
  decide +kernel

theorem context_10_72452_1530018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72452 ⟨1530018, by decide⟩ :=
  accepted_of_selected 10 72452 ⟨1530018, by decide⟩ ⟨10, 2, 0, 1530018, 72452, 2689, 1048576⟩
    (by decide) selected_cut_52454

theorem selected_cut_52455 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72453) = some ⟨10, 1, 0, 1468874, 72453, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72453_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72453 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72453 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72453, 1, 1048576⟩
    (by decide) selected_cut_52455

theorem selected_cut_52456 : selected 11 ⟨1530083, by decide⟩
    (prefixPartial 10 72454) = some ⟨10, 2, 0, 1530083, 72454, 2625, 1048576⟩ := by
  decide +kernel

theorem context_10_72454_1530083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72454 ⟨1530083, by decide⟩ :=
  accepted_of_selected 10 72454 ⟨1530083, by decide⟩ ⟨10, 2, 0, 1530083, 72454, 2625, 1048576⟩
    (by decide) selected_cut_52456

theorem selected_cut_52457 : selected 11 ⟨1530144, by decide⟩
    (prefixPartial 10 72455) = some ⟨10, 2, 0, 1530144, 72455, 2465, 1048576⟩ := by
  decide +kernel

theorem context_10_72455_1530144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72455 ⟨1530144, by decide⟩ :=
  accepted_of_selected 10 72455 ⟨1530144, by decide⟩ ⟨10, 2, 0, 1530144, 72455, 2465, 1048576⟩
    (by decide) selected_cut_52457

theorem unmarked_context_9_18113_1530145 : frontier 12 ⟨1530145, by decide⟩
    (prefixCache 9 18113) (prefixPartial 9 18113) = false := by
  decide +kernel

theorem node_context_9_18113_1530145 : EJMOriginalGlobalDAGData.nodes 12 ⟨1530145, by decide⟩ =
    .split (coordinate 9) (![⟨1530018, by decide⟩,⟨1468874, by decide⟩,⟨1530083, by decide⟩,⟨1530144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18113_1530145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18113 ⟨1530145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18113
    ⟨1530145, by decide⟩ (by decide) (![⟨1530018, by decide⟩,⟨1468874, by decide⟩,⟨1530083, by decide⟩,⟨1530144, by decide⟩]) unmarked_context_9_18113_1530145 node_context_9_18113_1530145
  intro a
  fin_cases a
  · exact context_10_72452_1530018
  · exact context_10_72453_1468874
  · exact context_10_72454_1530083
  · exact context_10_72455_1530144

theorem selected_cut_52458 : selected 12 ⟨1530238, by decide⟩
    (prefixPartial 9 18114) = some ⟨9, 2, 0, 1530238, 18114, 3329, 4194304⟩ := by
  decide +kernel

theorem context_9_18114_1530238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18114 ⟨1530238, by decide⟩ :=
  accepted_of_selected 9 18114 ⟨1530238, by decide⟩ ⟨9, 2, 0, 1530238, 18114, 3329, 4194304⟩
    (by decide) selected_cut_52458

theorem selected_cut_52459 : selected 12 ⟨1530298, by decide⟩
    (prefixPartial 9 18115) = some ⟨9, 2, 0, 1530298, 18115, 1461, 4194304⟩ := by
  decide +kernel

theorem context_9_18115_1530298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18115 ⟨1530298, by decide⟩ :=
  accepted_of_selected 9 18115 ⟨1530298, by decide⟩ ⟨9, 2, 0, 1530298, 18115, 1461, 4194304⟩
    (by decide) selected_cut_52459

theorem unmarked_context_8_4528_1530299 : frontier 13 ⟨1530299, by decide⟩
    (prefixCache 8 4528) (prefixPartial 8 4528) = false := by
  decide +kernel

theorem node_context_8_4528_1530299 : EJMOriginalGlobalDAGData.nodes 13 ⟨1530299, by decide⟩ =
    .split (coordinate 8) (![⟨1529948, by decide⟩,⟨1530145, by decide⟩,⟨1530238, by decide⟩,⟨1530298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4528_1530299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4528 ⟨1530299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4528
    ⟨1530299, by decide⟩ (by decide) (![⟨1529948, by decide⟩,⟨1530145, by decide⟩,⟨1530238, by decide⟩,⟨1530298, by decide⟩]) unmarked_context_8_4528_1530299 node_context_8_4528_1530299
  intro a
  fin_cases a
  · exact context_9_18112_1529948
  · exact context_9_18113_1530145
  · exact context_9_18114_1530238
  · exact context_9_18115_1530298

theorem selected_cut_52460 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72464) = some ⟨10, 1, 0, 1468246, 72464, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72464_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72464 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72464 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72464, 1, 1048576⟩
    (by decide) selected_cut_52460

theorem selected_cut_52461 : selected 10 ⟨1530334, by decide⟩
    (prefixPartial 11 289860) = some ⟨11, 2, 0, 1530334, 289860, 1189, 262144⟩ := by
  decide +kernel

theorem context_11_289860_1530334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289860 ⟨1530334, by decide⟩ :=
  accepted_of_selected 11 289860 ⟨1530334, by decide⟩ ⟨11, 2, 0, 1530334, 289860, 1189, 262144⟩
    (by decide) selected_cut_52461

theorem selected_cut_52462 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289861) = some ⟨11, 1, 0, 1468419, 289861, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289861_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289861 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289861 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289861, 1, 262144⟩
    (by decide) selected_cut_52462

theorem selected_cut_52463 : selected 10 ⟨1530370, by decide⟩
    (prefixPartial 11 289862) = some ⟨11, 2, 0, 1530370, 289862, 1325, 262144⟩ := by
  decide +kernel

theorem context_11_289862_1530370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289862 ⟨1530370, by decide⟩ :=
  accepted_of_selected 11 289862 ⟨1530370, by decide⟩ ⟨11, 2, 0, 1530370, 289862, 1325, 262144⟩
    (by decide) selected_cut_52463

theorem selected_cut_52464 : selected 10 ⟨1530448, by decide⟩
    (prefixPartial 11 289863) = some ⟨11, 2, 0, 1530448, 289863, 2381, 262144⟩ := by
  decide +kernel

theorem context_11_289863_1530448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289863 ⟨1530448, by decide⟩ :=
  accepted_of_selected 11 289863 ⟨1530448, by decide⟩ ⟨11, 2, 0, 1530448, 289863, 2381, 262144⟩
    (by decide) selected_cut_52464

theorem unmarked_context_10_72465_1530449 : frontier 11 ⟨1530449, by decide⟩
    (prefixCache 10 72465) (prefixPartial 10 72465) = false := by
  decide +kernel

theorem node_context_10_72465_1530449 : EJMOriginalGlobalDAGData.nodes 11 ⟨1530449, by decide⟩ =
    .split (coordinate 10) (![⟨1530334, by decide⟩,⟨1468419, by decide⟩,⟨1530370, by decide⟩,⟨1530448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72465_1530449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72465 ⟨1530449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72465
    ⟨1530449, by decide⟩ (by decide) (![⟨1530334, by decide⟩,⟨1468419, by decide⟩,⟨1530370, by decide⟩,⟨1530448, by decide⟩]) unmarked_context_10_72465_1530449 node_context_10_72465_1530449
  intro a
  fin_cases a
  · exact context_11_289860_1530334
  · exact context_11_289861_1468419
  · exact context_11_289862_1530370
  · exact context_11_289863_1530448

theorem selected_cut_52465 : selected 11 ⟨1530550, by decide⟩
    (prefixPartial 10 72466) = some ⟨10, 2, 0, 1530550, 72466, 3309, 1048576⟩ := by
  decide +kernel

theorem context_10_72466_1530550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72466 ⟨1530550, by decide⟩ :=
  accepted_of_selected 10 72466 ⟨1530550, by decide⟩ ⟨10, 2, 0, 1530550, 72466, 3309, 1048576⟩
    (by decide) selected_cut_52465

theorem selected_cut_52466 : selected 11 ⟨1530644, by decide⟩
    (prefixPartial 10 72467) = some ⟨10, 2, 0, 1530644, 72467, 3493, 1048576⟩ := by
  decide +kernel

theorem context_10_72467_1530644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72467 ⟨1530644, by decide⟩ :=
  accepted_of_selected 10 72467 ⟨1530644, by decide⟩ ⟨10, 2, 0, 1530644, 72467, 3493, 1048576⟩
    (by decide) selected_cut_52466

theorem unmarked_context_9_18116_1530645 : frontier 12 ⟨1530645, by decide⟩
    (prefixCache 9 18116) (prefixPartial 9 18116) = false := by
  decide +kernel

theorem node_context_9_18116_1530645 : EJMOriginalGlobalDAGData.nodes 12 ⟨1530645, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1530449, by decide⟩,⟨1530550, by decide⟩,⟨1530644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18116_1530645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18116 ⟨1530645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18116
    ⟨1530645, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1530449, by decide⟩,⟨1530550, by decide⟩,⟨1530644, by decide⟩]) unmarked_context_9_18116_1530645 node_context_9_18116_1530645
  intro a
  fin_cases a
  · exact context_10_72464_1468246
  · exact context_10_72465_1530449
  · exact context_10_72466_1530550
  · exact context_10_72467_1530644

theorem selected_cut_52467 : selected 11 ⟨1530723, by decide⟩
    (prefixPartial 10 72468) = some ⟨10, 2, 0, 1530723, 72468, 2957, 1048576⟩ := by
  decide +kernel

theorem context_10_72468_1530723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72468 ⟨1530723, by decide⟩ :=
  accepted_of_selected 10 72468 ⟨1530723, by decide⟩ ⟨10, 2, 0, 1530723, 72468, 2957, 1048576⟩
    (by decide) selected_cut_52467

theorem selected_cut_52468 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72469) = some ⟨10, 1, 0, 1468874, 72469, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72469_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72469 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72469 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72469, 1, 1048576⟩
    (by decide) selected_cut_52468

theorem selected_cut_52469 : selected 11 ⟨1530807, by decide⟩
    (prefixPartial 10 72470) = some ⟨10, 2, 0, 1530807, 72470, 3205, 1048576⟩ := by
  decide +kernel

theorem context_10_72470_1530807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72470 ⟨1530807, by decide⟩ :=
  accepted_of_selected 10 72470 ⟨1530807, by decide⟩ ⟨10, 2, 0, 1530807, 72470, 3205, 1048576⟩
    (by decide) selected_cut_52469

theorem selected_cut_52470 : selected 11 ⟨1530862, by decide⟩
    (prefixPartial 10 72471) = some ⟨10, 2, 0, 1530862, 72471, 2145, 1048576⟩ := by
  decide +kernel

theorem context_10_72471_1530862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72471 ⟨1530862, by decide⟩ :=
  accepted_of_selected 10 72471 ⟨1530862, by decide⟩ ⟨10, 2, 0, 1530862, 72471, 2145, 1048576⟩
    (by decide) selected_cut_52470

theorem unmarked_context_9_18117_1530863 : frontier 12 ⟨1530863, by decide⟩
    (prefixCache 9 18117) (prefixPartial 9 18117) = false := by
  decide +kernel

theorem node_context_9_18117_1530863 : EJMOriginalGlobalDAGData.nodes 12 ⟨1530863, by decide⟩ =
    .split (coordinate 9) (![⟨1530723, by decide⟩,⟨1468874, by decide⟩,⟨1530807, by decide⟩,⟨1530862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18117_1530863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18117 ⟨1530863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18117
    ⟨1530863, by decide⟩ (by decide) (![⟨1530723, by decide⟩,⟨1468874, by decide⟩,⟨1530807, by decide⟩,⟨1530862, by decide⟩]) unmarked_context_9_18117_1530863 node_context_9_18117_1530863
  intro a
  fin_cases a
  · exact context_10_72468_1530723
  · exact context_10_72469_1468874
  · exact context_10_72470_1530807
  · exact context_10_72471_1530862

theorem selected_cut_52471 : selected 12 ⟨1530946, by decide⟩
    (prefixPartial 9 18118) = some ⟨9, 2, 0, 1530946, 18118, 3201, 4194304⟩ := by
  decide +kernel

theorem context_9_18118_1530946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18118 ⟨1530946, by decide⟩ :=
  accepted_of_selected 9 18118 ⟨1530946, by decide⟩ ⟨9, 2, 0, 1530946, 18118, 3201, 4194304⟩
    (by decide) selected_cut_52471

theorem selected_cut_52472 : selected 12 ⟨1530996, by decide⟩
    (prefixPartial 9 18119) = some ⟨9, 2, 0, 1530996, 18119, 1033, 4194304⟩ := by
  decide +kernel

theorem context_9_18119_1530996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18119 ⟨1530996, by decide⟩ :=
  accepted_of_selected 9 18119 ⟨1530996, by decide⟩ ⟨9, 2, 0, 1530996, 18119, 1033, 4194304⟩
    (by decide) selected_cut_52472

theorem unmarked_context_8_4529_1530997 : frontier 13 ⟨1530997, by decide⟩
    (prefixCache 8 4529) (prefixPartial 8 4529) = false := by
  decide +kernel

theorem node_context_8_4529_1530997 : EJMOriginalGlobalDAGData.nodes 13 ⟨1530997, by decide⟩ =
    .split (coordinate 8) (![⟨1530645, by decide⟩,⟨1530863, by decide⟩,⟨1530946, by decide⟩,⟨1530996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4529_1530997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4529 ⟨1530997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4529
    ⟨1530997, by decide⟩ (by decide) (![⟨1530645, by decide⟩,⟨1530863, by decide⟩,⟨1530946, by decide⟩,⟨1530996, by decide⟩]) unmarked_context_8_4529_1530997 node_context_8_4529_1530997
  intro a
  fin_cases a
  · exact context_9_18116_1530645
  · exact context_9_18117_1530863
  · exact context_9_18118_1530946
  · exact context_9_18119_1530996

theorem selected_cut_52473 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72480) = some ⟨10, 1, 0, 1468246, 72480, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72480_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72480 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72480 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72480, 1, 1048576⟩
    (by decide) selected_cut_52473

theorem selected_cut_52474 : selected 10 ⟨1531078, by decide⟩
    (prefixPartial 11 289924) = some ⟨11, 2, 0, 1531078, 289924, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_289924_1531078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289924 ⟨1531078, by decide⟩ :=
  accepted_of_selected 11 289924 ⟨1531078, by decide⟩ ⟨11, 2, 0, 1531078, 289924, 1673, 262144⟩
    (by decide) selected_cut_52474

theorem selected_cut_52475 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 289925) = some ⟨11, 1, 0, 1468419, 289925, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289925_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289925 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 289925 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 289925, 1, 262144⟩
    (by decide) selected_cut_52475

theorem selected_cut_52476 : selected 10 ⟨1531136, by decide⟩
    (prefixPartial 11 289926) = some ⟨11, 2, 0, 1531136, 289926, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_289926_1531136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289926 ⟨1531136, by decide⟩ :=
  accepted_of_selected 11 289926 ⟨1531136, by decide⟩ ⟨11, 2, 0, 1531136, 289926, 1609, 262144⟩
    (by decide) selected_cut_52476

theorem selected_cut_52477 : selected 10 ⟨1531227, by decide⟩
    (prefixPartial 11 289927) = some ⟨11, 2, 0, 1531227, 289927, 3133, 262144⟩ := by
  decide +kernel

theorem context_11_289927_1531227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289927 ⟨1531227, by decide⟩ :=
  accepted_of_selected 11 289927 ⟨1531227, by decide⟩ ⟨11, 2, 0, 1531227, 289927, 3133, 262144⟩
    (by decide) selected_cut_52477

theorem unmarked_context_10_72481_1531228 : frontier 11 ⟨1531228, by decide⟩
    (prefixCache 10 72481) (prefixPartial 10 72481) = false := by
  decide +kernel

theorem node_context_10_72481_1531228 : EJMOriginalGlobalDAGData.nodes 11 ⟨1531228, by decide⟩ =
    .split (coordinate 10) (![⟨1531078, by decide⟩,⟨1468419, by decide⟩,⟨1531136, by decide⟩,⟨1531227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72481_1531228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72481 ⟨1531228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72481
    ⟨1531228, by decide⟩ (by decide) (![⟨1531078, by decide⟩,⟨1468419, by decide⟩,⟨1531136, by decide⟩,⟨1531227, by decide⟩]) unmarked_context_10_72481_1531228 node_context_10_72481_1531228
  intro a
  fin_cases a
  · exact context_11_289924_1531078
  · exact context_11_289925_1468419
  · exact context_11_289926_1531136
  · exact context_11_289927_1531227

theorem selected_cut_52478 : selected 10 ⟨1531303, by decide⟩
    (prefixPartial 11 289928) = some ⟨11, 2, 0, 1531303, 289928, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_289928_1531303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289928 ⟨1531303, by decide⟩ :=
  accepted_of_selected 11 289928 ⟨1531303, by decide⟩ ⟨11, 2, 0, 1531303, 289928, 2521, 262144⟩
    (by decide) selected_cut_52478

theorem selected_cut_52479 : selected 10 ⟨1531345, by decide⟩
    (prefixPartial 11 289929) = some ⟨11, 2, 0, 1531345, 289929, 1285, 262144⟩ := by
  decide +kernel

theorem context_11_289929_1531345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289929 ⟨1531345, by decide⟩ :=
  accepted_of_selected 11 289929 ⟨1531345, by decide⟩ ⟨11, 2, 0, 1531345, 289929, 1285, 262144⟩
    (by decide) selected_cut_52479

theorem selected_cut_52480 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 289930) = some ⟨11, 1, 0, 1468743, 289930, 1, 262144⟩ := by
  decide +kernel

theorem context_11_289930_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289930 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 289930 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 289930, 1, 262144⟩
    (by decide) selected_cut_52480

theorem selected_cut_52481 : selected 10 ⟨1531380, by decide⟩
    (prefixPartial 11 289931) = some ⟨11, 2, 0, 1531380, 289931, 1201, 262144⟩ := by
  decide +kernel

theorem context_11_289931_1531380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 289931 ⟨1531380, by decide⟩ :=
  accepted_of_selected 11 289931 ⟨1531380, by decide⟩ ⟨11, 2, 0, 1531380, 289931, 1201, 262144⟩
    (by decide) selected_cut_52481

theorem unmarked_context_10_72482_1531381 : frontier 11 ⟨1531381, by decide⟩
    (prefixCache 10 72482) (prefixPartial 10 72482) = false := by
  decide +kernel

theorem node_context_10_72482_1531381 : EJMOriginalGlobalDAGData.nodes 11 ⟨1531381, by decide⟩ =
    .split (coordinate 10) (![⟨1531303, by decide⟩,⟨1531345, by decide⟩,⟨1468743, by decide⟩,⟨1531380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72482_1531381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72482 ⟨1531381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72482
    ⟨1531381, by decide⟩ (by decide) (![⟨1531303, by decide⟩,⟨1531345, by decide⟩,⟨1468743, by decide⟩,⟨1531380, by decide⟩]) unmarked_context_10_72482_1531381 node_context_10_72482_1531381
  intro a
  fin_cases a
  · exact context_11_289928_1531303
  · exact context_11_289929_1531345
  · exact context_11_289930_1468743
  · exact context_11_289931_1531380

theorem selected_cut_52482 : selected 11 ⟨1531500, by decide⟩
    (prefixPartial 10 72483) = some ⟨10, 2, 0, 1531500, 72483, 3785, 1048576⟩ := by
  decide +kernel

theorem context_10_72483_1531500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72483 ⟨1531500, by decide⟩ :=
  accepted_of_selected 10 72483 ⟨1531500, by decide⟩ ⟨10, 2, 0, 1531500, 72483, 3785, 1048576⟩
    (by decide) selected_cut_52482

theorem unmarked_context_9_18120_1531501 : frontier 12 ⟨1531501, by decide⟩
    (prefixCache 9 18120) (prefixPartial 9 18120) = false := by
  decide +kernel

theorem node_context_9_18120_1531501 : EJMOriginalGlobalDAGData.nodes 12 ⟨1531501, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1531228, by decide⟩,⟨1531381, by decide⟩,⟨1531500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18120_1531501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18120 ⟨1531501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18120
    ⟨1531501, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1531228, by decide⟩,⟨1531381, by decide⟩,⟨1531500, by decide⟩]) unmarked_context_9_18120_1531501 node_context_9_18120_1531501
  intro a
  fin_cases a
  · exact context_10_72480_1468246
  · exact context_10_72481_1531228
  · exact context_10_72482_1531381
  · exact context_10_72483_1531500

theorem selected_cut_52483 : selected 11 ⟨1531599, by decide⟩
    (prefixPartial 10 72484) = some ⟨10, 2, 0, 1531599, 72484, 2629, 1048576⟩ := by
  decide +kernel

theorem context_10_72484_1531599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72484 ⟨1531599, by decide⟩ :=
  accepted_of_selected 10 72484 ⟨1531599, by decide⟩ ⟨10, 2, 0, 1531599, 72484, 2629, 1048576⟩
    (by decide) selected_cut_52483

theorem selected_cut_52484 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72485) = some ⟨10, 1, 0, 1468874, 72485, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72485_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72485 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72485 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72485, 1, 1048576⟩
    (by decide) selected_cut_52484

theorem selected_cut_52485 : selected 11 ⟨1531752, by decide⟩
    (prefixPartial 10 72486) = some ⟨10, 2, 0, 1531752, 72486, 3785, 1048576⟩ := by
  decide +kernel

theorem context_10_72486_1531752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72486 ⟨1531752, by decide⟩ :=
  accepted_of_selected 10 72486 ⟨1531752, by decide⟩ ⟨10, 2, 0, 1531752, 72486, 3785, 1048576⟩
    (by decide) selected_cut_52485

theorem selected_cut_52486 : selected 11 ⟨1531900, by decide⟩
    (prefixPartial 10 72487) = some ⟨10, 2, 0, 1531900, 72487, 2913, 1048576⟩ := by
  decide +kernel

theorem context_10_72487_1531900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72487 ⟨1531900, by decide⟩ :=
  accepted_of_selected 10 72487 ⟨1531900, by decide⟩ ⟨10, 2, 0, 1531900, 72487, 2913, 1048576⟩
    (by decide) selected_cut_52486

theorem unmarked_context_9_18121_1531901 : frontier 12 ⟨1531901, by decide⟩
    (prefixCache 9 18121) (prefixPartial 9 18121) = false := by
  decide +kernel

theorem node_context_9_18121_1531901 : EJMOriginalGlobalDAGData.nodes 12 ⟨1531901, by decide⟩ =
    .split (coordinate 9) (![⟨1531599, by decide⟩,⟨1468874, by decide⟩,⟨1531752, by decide⟩,⟨1531900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18121_1531901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18121 ⟨1531901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18121
    ⟨1531901, by decide⟩ (by decide) (![⟨1531599, by decide⟩,⟨1468874, by decide⟩,⟨1531752, by decide⟩,⟨1531900, by decide⟩]) unmarked_context_9_18121_1531901 node_context_9_18121_1531901
  intro a
  fin_cases a
  · exact context_10_72484_1531599
  · exact context_10_72485_1468874
  · exact context_10_72486_1531752
  · exact context_10_72487_1531900

theorem selected_cut_52487 : selected 12 ⟨1532028, by decide⟩
    (prefixPartial 9 18122) = some ⟨9, 2, 0, 1532028, 18122, 3781, 4194304⟩ := by
  decide +kernel

theorem context_9_18122_1532028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18122 ⟨1532028, by decide⟩ :=
  accepted_of_selected 9 18122 ⟨1532028, by decide⟩ ⟨9, 2, 0, 1532028, 18122, 3781, 4194304⟩
    (by decide) selected_cut_52487

theorem selected_cut_52488 : selected 12 ⟨1532094, by decide⟩
    (prefixPartial 9 18123) = some ⟨9, 2, 0, 1532094, 18123, 1361, 4194304⟩ := by
  decide +kernel

theorem context_9_18123_1532094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18123 ⟨1532094, by decide⟩ :=
  accepted_of_selected 9 18123 ⟨1532094, by decide⟩ ⟨9, 2, 0, 1532094, 18123, 1361, 4194304⟩
    (by decide) selected_cut_52488

theorem unmarked_context_8_4530_1532095 : frontier 13 ⟨1532095, by decide⟩
    (prefixCache 8 4530) (prefixPartial 8 4530) = false := by
  decide +kernel

theorem node_context_8_4530_1532095 : EJMOriginalGlobalDAGData.nodes 13 ⟨1532095, by decide⟩ =
    .split (coordinate 8) (![⟨1531501, by decide⟩,⟨1531901, by decide⟩,⟨1532028, by decide⟩,⟨1532094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4530_1532095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4530 ⟨1532095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4530
    ⟨1532095, by decide⟩ (by decide) (![⟨1531501, by decide⟩,⟨1531901, by decide⟩,⟨1532028, by decide⟩,⟨1532094, by decide⟩]) unmarked_context_8_4530_1532095 node_context_8_4530_1532095
  intro a
  fin_cases a
  · exact context_9_18120_1531501
  · exact context_9_18121_1531901
  · exact context_9_18122_1532028
  · exact context_9_18123_1532094

theorem selected_cut_52489 : selected 13 ⟨1532096, by decide⟩
    (prefixPartial 8 4531) = some ⟨8, 1, 0, 1532096, 4531, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4531_1532096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4531 ⟨1532096, by decide⟩ :=
  accepted_of_selected 8 4531 ⟨1532096, by decide⟩ ⟨8, 1, 0, 1532096, 4531, 1, 16777216⟩
    (by decide) selected_cut_52489

theorem unmarked_context_7_1132_1532097 : frontier 14 ⟨1532097, by decide⟩
    (prefixCache 7 1132) (prefixPartial 7 1132) = false := by
  decide +kernel

theorem node_context_7_1132_1532097 : EJMOriginalGlobalDAGData.nodes 14 ⟨1532097, by decide⟩ =
    .split (coordinate 7) (![⟨1530299, by decide⟩,⟨1530997, by decide⟩,⟨1532095, by decide⟩,⟨1532096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1132_1532097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1132 ⟨1532097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1132
    ⟨1532097, by decide⟩ (by decide) (![⟨1530299, by decide⟩,⟨1530997, by decide⟩,⟨1532095, by decide⟩,⟨1532096, by decide⟩]) unmarked_context_7_1132_1532097 node_context_7_1132_1532097
  intro a
  fin_cases a
  · exact context_8_4528_1530299
  · exact context_8_4529_1530997
  · exact context_8_4530_1532095
  · exact context_8_4531_1532096

theorem selected_cut_52490 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72512) = some ⟨10, 1, 0, 1468246, 72512, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72512_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72512 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72512 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72512, 1, 1048576⟩
    (by decide) selected_cut_52490

theorem selected_cut_52491 : selected 11 ⟨1532229, by decide⟩
    (prefixPartial 10 72513) = some ⟨10, 2, 0, 1532229, 72513, 3465, 1048576⟩ := by
  decide +kernel

theorem context_10_72513_1532229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72513 ⟨1532229, by decide⟩ :=
  accepted_of_selected 10 72513 ⟨1532229, by decide⟩ ⟨10, 2, 0, 1532229, 72513, 3465, 1048576⟩
    (by decide) selected_cut_52491

theorem selected_cut_52492 : selected 11 ⟨1532330, by decide⟩
    (prefixPartial 10 72514) = some ⟨10, 2, 0, 1532330, 72514, 3761, 1048576⟩ := by
  decide +kernel

theorem context_10_72514_1532330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72514 ⟨1532330, by decide⟩ :=
  accepted_of_selected 10 72514 ⟨1532330, by decide⟩ ⟨10, 2, 0, 1532330, 72514, 3761, 1048576⟩
    (by decide) selected_cut_52492

theorem selected_cut_52493 : selected 11 ⟨1532405, by decide⟩
    (prefixPartial 10 72515) = some ⟨10, 2, 0, 1532405, 72515, 2349, 1048576⟩ := by
  decide +kernel

theorem context_10_72515_1532405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72515 ⟨1532405, by decide⟩ :=
  accepted_of_selected 10 72515 ⟨1532405, by decide⟩ ⟨10, 2, 0, 1532405, 72515, 2349, 1048576⟩
    (by decide) selected_cut_52493

theorem unmarked_context_9_18128_1532406 : frontier 12 ⟨1532406, by decide⟩
    (prefixCache 9 18128) (prefixPartial 9 18128) = false := by
  decide +kernel

theorem node_context_9_18128_1532406 : EJMOriginalGlobalDAGData.nodes 12 ⟨1532406, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1532229, by decide⟩,⟨1532330, by decide⟩,⟨1532405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18128_1532406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18128 ⟨1532406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18128
    ⟨1532406, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1532229, by decide⟩,⟨1532330, by decide⟩,⟨1532405, by decide⟩]) unmarked_context_9_18128_1532406 node_context_9_18128_1532406
  intro a
  fin_cases a
  · exact context_10_72512_1468246
  · exact context_10_72513_1532229
  · exact context_10_72514_1532330
  · exact context_10_72515_1532405

theorem selected_cut_52494 : selected 11 ⟨1532481, by decide⟩
    (prefixPartial 10 72516) = some ⟨10, 2, 0, 1532481, 72516, 2489, 1048576⟩ := by
  decide +kernel

theorem context_10_72516_1532481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72516 ⟨1532481, by decide⟩ :=
  accepted_of_selected 10 72516 ⟨1532481, by decide⟩ ⟨10, 2, 0, 1532481, 72516, 2489, 1048576⟩
    (by decide) selected_cut_52494

theorem selected_cut_52495 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72517) = some ⟨10, 1, 0, 1468874, 72517, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72517_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72517 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72517 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72517, 1, 1048576⟩
    (by decide) selected_cut_52495

theorem selected_cut_52496 : selected 11 ⟨1532551, by decide⟩
    (prefixPartial 10 72518) = some ⟨10, 2, 0, 1532551, 72518, 2357, 1048576⟩ := by
  decide +kernel

theorem context_10_72518_1532551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72518 ⟨1532551, by decide⟩ :=
  accepted_of_selected 10 72518 ⟨1532551, by decide⟩ ⟨10, 2, 0, 1532551, 72518, 2357, 1048576⟩
    (by decide) selected_cut_52496

theorem selected_cut_52497 : selected 11 ⟨1532605, by decide⟩
    (prefixPartial 10 72519) = some ⟨10, 2, 0, 1532605, 72519, 1861, 1048576⟩ := by
  decide +kernel

theorem context_10_72519_1532605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72519 ⟨1532605, by decide⟩ :=
  accepted_of_selected 10 72519 ⟨1532605, by decide⟩ ⟨10, 2, 0, 1532605, 72519, 1861, 1048576⟩
    (by decide) selected_cut_52497

theorem unmarked_context_9_18129_1532606 : frontier 12 ⟨1532606, by decide⟩
    (prefixCache 9 18129) (prefixPartial 9 18129) = false := by
  decide +kernel

theorem node_context_9_18129_1532606 : EJMOriginalGlobalDAGData.nodes 12 ⟨1532606, by decide⟩ =
    .split (coordinate 9) (![⟨1532481, by decide⟩,⟨1468874, by decide⟩,⟨1532551, by decide⟩,⟨1532605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18129_1532606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18129 ⟨1532606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18129
    ⟨1532606, by decide⟩ (by decide) (![⟨1532481, by decide⟩,⟨1468874, by decide⟩,⟨1532551, by decide⟩,⟨1532605, by decide⟩]) unmarked_context_9_18129_1532606 node_context_9_18129_1532606
  intro a
  fin_cases a
  · exact context_10_72516_1532481
  · exact context_10_72517_1468874
  · exact context_10_72518_1532551
  · exact context_10_72519_1532605

theorem selected_cut_52498 : selected 12 ⟨1532679, by decide⟩
    (prefixPartial 9 18130) = some ⟨9, 2, 0, 1532679, 18130, 2857, 4194304⟩ := by
  decide +kernel

theorem context_9_18130_1532679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18130 ⟨1532679, by decide⟩ :=
  accepted_of_selected 9 18130 ⟨1532679, by decide⟩ ⟨9, 2, 0, 1532679, 18130, 2857, 4194304⟩
    (by decide) selected_cut_52498

theorem selected_cut_52499 : selected 12 ⟨1532731, by decide⟩
    (prefixPartial 9 18131) = some ⟨9, 2, 0, 1532731, 18131, 1053, 4194304⟩ := by
  decide +kernel

theorem context_9_18131_1532731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18131 ⟨1532731, by decide⟩ :=
  accepted_of_selected 9 18131 ⟨1532731, by decide⟩ ⟨9, 2, 0, 1532731, 18131, 1053, 4194304⟩
    (by decide) selected_cut_52499

theorem unmarked_context_8_4532_1532732 : frontier 13 ⟨1532732, by decide⟩
    (prefixCache 8 4532) (prefixPartial 8 4532) = false := by
  decide +kernel

theorem node_context_8_4532_1532732 : EJMOriginalGlobalDAGData.nodes 13 ⟨1532732, by decide⟩ =
    .split (coordinate 8) (![⟨1532406, by decide⟩,⟨1532606, by decide⟩,⟨1532679, by decide⟩,⟨1532731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4532_1532732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4532 ⟨1532732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4532
    ⟨1532732, by decide⟩ (by decide) (![⟨1532406, by decide⟩,⟨1532606, by decide⟩,⟨1532679, by decide⟩,⟨1532731, by decide⟩]) unmarked_context_8_4532_1532732 node_context_8_4532_1532732
  intro a
  fin_cases a
  · exact context_9_18128_1532406
  · exact context_9_18129_1532606
  · exact context_9_18130_1532679
  · exact context_9_18131_1532731

theorem selected_cut_52500 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72528) = some ⟨10, 1, 0, 1468246, 72528, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72528_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72528 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72528 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72528, 1, 1048576⟩
    (by decide) selected_cut_52500

theorem selected_cut_52501 : selected 11 ⟨1532836, by decide⟩
    (prefixPartial 10 72529) = some ⟨10, 2, 0, 1532836, 72529, 3377, 1048576⟩ := by
  decide +kernel

theorem context_10_72529_1532836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72529 ⟨1532836, by decide⟩ :=
  accepted_of_selected 10 72529 ⟨1532836, by decide⟩ ⟨10, 2, 0, 1532836, 72529, 3377, 1048576⟩
    (by decide) selected_cut_52501

theorem selected_cut_52502 : selected 11 ⟨1532926, by decide⟩
    (prefixPartial 10 72530) = some ⟨10, 2, 0, 1532926, 72530, 3101, 1048576⟩ := by
  decide +kernel

theorem context_10_72530_1532926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72530 ⟨1532926, by decide⟩ :=
  accepted_of_selected 10 72530 ⟨1532926, by decide⟩ ⟨10, 2, 0, 1532926, 72530, 3101, 1048576⟩
    (by decide) selected_cut_52502

theorem selected_cut_52503 : selected 11 ⟨1532986, by decide⟩
    (prefixPartial 10 72531) = some ⟨10, 2, 0, 1532986, 72531, 2497, 1048576⟩ := by
  decide +kernel

theorem context_10_72531_1532986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72531 ⟨1532986, by decide⟩ :=
  accepted_of_selected 10 72531 ⟨1532986, by decide⟩ ⟨10, 2, 0, 1532986, 72531, 2497, 1048576⟩
    (by decide) selected_cut_52503

theorem unmarked_context_9_18132_1532987 : frontier 12 ⟨1532987, by decide⟩
    (prefixCache 9 18132) (prefixPartial 9 18132) = false := by
  decide +kernel

theorem node_context_9_18132_1532987 : EJMOriginalGlobalDAGData.nodes 12 ⟨1532987, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1532836, by decide⟩,⟨1532926, by decide⟩,⟨1532986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18132_1532987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18132 ⟨1532987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18132
    ⟨1532987, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1532836, by decide⟩,⟨1532926, by decide⟩,⟨1532986, by decide⟩]) unmarked_context_9_18132_1532987 node_context_9_18132_1532987
  intro a
  fin_cases a
  · exact context_10_72528_1468246
  · exact context_10_72529_1532836
  · exact context_10_72530_1532926
  · exact context_10_72531_1532986

theorem selected_cut_52504 : selected 11 ⟨1533067, by decide⟩
    (prefixPartial 10 72532) = some ⟨10, 2, 0, 1533067, 72532, 2717, 1048576⟩ := by
  decide +kernel

theorem context_10_72532_1533067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72532 ⟨1533067, by decide⟩ :=
  accepted_of_selected 10 72532 ⟨1533067, by decide⟩ ⟨10, 2, 0, 1533067, 72532, 2717, 1048576⟩
    (by decide) selected_cut_52504

theorem selected_cut_52505 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72533) = some ⟨10, 1, 0, 1468874, 72533, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72533_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72533 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72533 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72533, 1, 1048576⟩
    (by decide) selected_cut_52505

theorem selected_cut_52506 : selected 11 ⟨1533167, by decide⟩
    (prefixPartial 10 72534) = some ⟨10, 2, 0, 1533167, 72534, 3557, 1048576⟩ := by
  decide +kernel

theorem context_10_72534_1533167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72534 ⟨1533167, by decide⟩ :=
  accepted_of_selected 10 72534 ⟨1533167, by decide⟩ ⟨10, 2, 0, 1533167, 72534, 3557, 1048576⟩
    (by decide) selected_cut_52506

theorem selected_cut_52507 : selected 11 ⟨1533229, by decide⟩
    (prefixPartial 10 72535) = some ⟨10, 2, 0, 1533229, 72535, 2289, 1048576⟩ := by
  decide +kernel

theorem context_10_72535_1533229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72535 ⟨1533229, by decide⟩ :=
  accepted_of_selected 10 72535 ⟨1533229, by decide⟩ ⟨10, 2, 0, 1533229, 72535, 2289, 1048576⟩
    (by decide) selected_cut_52507

theorem unmarked_context_9_18133_1533230 : frontier 12 ⟨1533230, by decide⟩
    (prefixCache 9 18133) (prefixPartial 9 18133) = false := by
  decide +kernel

theorem node_context_9_18133_1533230 : EJMOriginalGlobalDAGData.nodes 12 ⟨1533230, by decide⟩ =
    .split (coordinate 9) (![⟨1533067, by decide⟩,⟨1468874, by decide⟩,⟨1533167, by decide⟩,⟨1533229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18133_1533230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18133 ⟨1533230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18133
    ⟨1533230, by decide⟩ (by decide) (![⟨1533067, by decide⟩,⟨1468874, by decide⟩,⟨1533167, by decide⟩,⟨1533229, by decide⟩]) unmarked_context_9_18133_1533230 node_context_9_18133_1533230
  intro a
  fin_cases a
  · exact context_10_72532_1533067
  · exact context_10_72533_1468874
  · exact context_10_72534_1533167
  · exact context_10_72535_1533229

theorem selected_cut_52508 : selected 12 ⟨1533304, by decide⟩
    (prefixPartial 9 18134) = some ⟨9, 2, 0, 1533304, 18134, 2265, 4194304⟩ := by
  decide +kernel

theorem context_9_18134_1533304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18134 ⟨1533304, by decide⟩ :=
  accepted_of_selected 9 18134 ⟨1533304, by decide⟩ ⟨9, 2, 0, 1533304, 18134, 2265, 4194304⟩
    (by decide) selected_cut_52508

theorem selected_cut_52509 : selected 12 ⟨1533352, by decide⟩
    (prefixPartial 9 18135) = some ⟨9, 2, 0, 1533352, 18135, 1133, 4194304⟩ := by
  decide +kernel

theorem context_9_18135_1533352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18135 ⟨1533352, by decide⟩ :=
  accepted_of_selected 9 18135 ⟨1533352, by decide⟩ ⟨9, 2, 0, 1533352, 18135, 1133, 4194304⟩
    (by decide) selected_cut_52509

theorem unmarked_context_8_4533_1533353 : frontier 13 ⟨1533353, by decide⟩
    (prefixCache 8 4533) (prefixPartial 8 4533) = false := by
  decide +kernel

theorem node_context_8_4533_1533353 : EJMOriginalGlobalDAGData.nodes 13 ⟨1533353, by decide⟩ =
    .split (coordinate 8) (![⟨1532987, by decide⟩,⟨1533230, by decide⟩,⟨1533304, by decide⟩,⟨1533352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4533_1533353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4533 ⟨1533353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4533
    ⟨1533353, by decide⟩ (by decide) (![⟨1532987, by decide⟩,⟨1533230, by decide⟩,⟨1533304, by decide⟩,⟨1533352, by decide⟩]) unmarked_context_8_4533_1533353 node_context_8_4533_1533353
  intro a
  fin_cases a
  · exact context_9_18132_1532987
  · exact context_9_18133_1533230
  · exact context_9_18134_1533304
  · exact context_9_18135_1533352

theorem selected_cut_52510 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72544) = some ⟨10, 1, 0, 1468246, 72544, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72544_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72544 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72544 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72544, 1, 1048576⟩
    (by decide) selected_cut_52510

theorem selected_cut_52511 : selected 11 ⟨1533485, by decide⟩
    (prefixPartial 10 72545) = some ⟨10, 2, 0, 1533485, 72545, 3733, 1048576⟩ := by
  decide +kernel

theorem context_10_72545_1533485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72545 ⟨1533485, by decide⟩ :=
  accepted_of_selected 10 72545 ⟨1533485, by decide⟩ ⟨10, 2, 0, 1533485, 72545, 3733, 1048576⟩
    (by decide) selected_cut_52511

theorem selected_cut_52512 : selected 10 ⟨1533558, by decide⟩
    (prefixPartial 11 290184) = some ⟨11, 2, 0, 1533558, 290184, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_290184_1533558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290184 ⟨1533558, by decide⟩ :=
  accepted_of_selected 11 290184 ⟨1533558, by decide⟩ ⟨11, 2, 0, 1533558, 290184, 2265, 262144⟩
    (by decide) selected_cut_52512

theorem selected_cut_52513 : selected 10 ⟨1533582, by decide⟩
    (prefixPartial 11 290185) = some ⟨11, 2, 0, 1533582, 290185, 921, 262144⟩ := by
  decide +kernel

theorem context_11_290185_1533582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290185 ⟨1533582, by decide⟩ :=
  accepted_of_selected 11 290185 ⟨1533582, by decide⟩ ⟨11, 2, 0, 1533582, 290185, 921, 262144⟩
    (by decide) selected_cut_52513

theorem selected_cut_52514 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 290186) = some ⟨11, 1, 0, 1468743, 290186, 1, 262144⟩ := by
  decide +kernel

theorem context_11_290186_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290186 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 290186 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 290186, 1, 262144⟩
    (by decide) selected_cut_52514

theorem selected_cut_52515 : selected 10 ⟨1533609, by decide⟩
    (prefixPartial 11 290187) = some ⟨11, 2, 0, 1533609, 290187, 1013, 262144⟩ := by
  decide +kernel

theorem context_11_290187_1533609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290187 ⟨1533609, by decide⟩ :=
  accepted_of_selected 11 290187 ⟨1533609, by decide⟩ ⟨11, 2, 0, 1533609, 290187, 1013, 262144⟩
    (by decide) selected_cut_52515

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
