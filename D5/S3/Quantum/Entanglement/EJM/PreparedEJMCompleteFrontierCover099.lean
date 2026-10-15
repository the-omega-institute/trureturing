/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover098
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09507 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93636) = some ⟨13, 1, 0, 3444, 93636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93636, 1, 16384⟩
    (by decide) selected_cut_09507

theorem selected_cut_09508 : selected 8 ⟨262183, by decide⟩
    (prefixPartial 13 93637) = some ⟨13, 2, 0, 262183, 93637, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_93637_262183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93637 ⟨262183, by decide⟩ :=
  accepted_of_selected 13 93637 ⟨262183, by decide⟩ ⟨13, 2, 0, 262183, 93637, 1009, 16384⟩
    (by decide) selected_cut_09508

theorem selected_cut_09509 : selected 8 ⟨262230, by decide⟩
    (prefixPartial 13 93638) = some ⟨13, 2, 0, 262230, 93638, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_93638_262230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93638 ⟨262230, by decide⟩ :=
  accepted_of_selected 13 93638 ⟨262230, by decide⟩ ⟨13, 2, 0, 262230, 93638, 2245, 16384⟩
    (by decide) selected_cut_09509

theorem selected_cut_09510 : selected 8 ⟨262254, by decide⟩
    (prefixPartial 13 93639) = some ⟨13, 2, 0, 262254, 93639, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_93639_262254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93639 ⟨262254, by decide⟩ :=
  accepted_of_selected 13 93639 ⟨262254, by decide⟩ ⟨13, 2, 0, 262254, 93639, 1077, 16384⟩
    (by decide) selected_cut_09510

theorem unmarked_context_12_23409_262255 : frontier 9 ⟨262255, by decide⟩
    (prefixCache 12 23409) (prefixPartial 12 23409) = false := by
  decide +kernel

theorem node_context_12_23409_262255 : EJMOriginalGlobalDAGData.nodes 9 ⟨262255, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨262183, by decide⟩,⟨262230, by decide⟩,⟨262254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23409_262255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23409 ⟨262255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23409
    ⟨262255, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨262183, by decide⟩,⟨262230, by decide⟩,⟨262254, by decide⟩]) unmarked_context_12_23409_262255 node_context_12_23409_262255
  intro a
  fin_cases a
  · exact context_13_93636_3444
  · exact context_13_93637_262183
  · exact context_13_93638_262230
  · exact context_13_93639_262254

theorem selected_cut_09511 : selected 9 ⟨262316, by decide⟩
    (prefixPartial 12 23410) = some ⟨12, 2, 0, 262316, 23410, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_23410_262316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23410 ⟨262316, by decide⟩ :=
  accepted_of_selected 12 23410 ⟨262316, by decide⟩ ⟨12, 2, 0, 262316, 23410, 3633, 65536⟩
    (by decide) selected_cut_09511

theorem selected_cut_09512 : selected 9 ⟨262362, by decide⟩
    (prefixPartial 12 23411) = some ⟨12, 2, 0, 262362, 23411, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_23411_262362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23411 ⟨262362, by decide⟩ :=
  accepted_of_selected 12 23411 ⟨262362, by decide⟩ ⟨12, 2, 0, 262362, 23411, 3397, 65536⟩
    (by decide) selected_cut_09512

theorem unmarked_context_11_5852_262363 : frontier 10 ⟨262363, by decide⟩
    (prefixCache 11 5852) (prefixPartial 11 5852) = false := by
  decide +kernel

theorem node_context_11_5852_262363 : EJMOriginalGlobalDAGData.nodes 10 ⟨262363, by decide⟩ =
    .split (coordinate 11) (![⟨262154, by decide⟩,⟨262255, by decide⟩,⟨262316, by decide⟩,⟨262362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5852_262363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5852 ⟨262363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5852
    ⟨262363, by decide⟩ (by decide) (![⟨262154, by decide⟩,⟨262255, by decide⟩,⟨262316, by decide⟩,⟨262362, by decide⟩]) unmarked_context_11_5852_262363 node_context_11_5852_262363
  intro a
  fin_cases a
  · exact context_12_23408_262154
  · exact context_12_23409_262255
  · exact context_12_23410_262316
  · exact context_12_23411_262362

theorem selected_cut_09513 : selected 9 ⟨262404, by decide⟩
    (prefixPartial 12 23412) = some ⟨12, 2, 0, 262404, 23412, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_23412_262404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23412 ⟨262404, by decide⟩ :=
  accepted_of_selected 12 23412 ⟨262404, by decide⟩ ⟨12, 2, 0, 262404, 23412, 2977, 65536⟩
    (by decide) selected_cut_09513

theorem selected_cut_09514 : selected 9 ⟨262528, by decide⟩
    (prefixPartial 12 23413) = some ⟨12, 2, 0, 262528, 23413, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_23413_262528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23413 ⟨262528, by decide⟩ :=
  accepted_of_selected 12 23413 ⟨262528, by decide⟩ ⟨12, 2, 0, 262528, 23413, 2309, 65536⟩
    (by decide) selected_cut_09514

theorem selected_cut_09515 : selected 9 ⟨262577, by decide⟩
    (prefixPartial 12 23414) = some ⟨12, 2, 0, 262577, 23414, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_23414_262577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23414 ⟨262577, by decide⟩ :=
  accepted_of_selected 12 23414 ⟨262577, by decide⟩ ⟨12, 2, 0, 262577, 23414, 3269, 65536⟩
    (by decide) selected_cut_09515

theorem selected_cut_09516 : selected 9 ⟨262611, by decide⟩
    (prefixPartial 12 23415) = some ⟨12, 2, 0, 262611, 23415, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_23415_262611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23415 ⟨262611, by decide⟩ :=
  accepted_of_selected 12 23415 ⟨262611, by decide⟩ ⟨12, 2, 0, 262611, 23415, 3069, 65536⟩
    (by decide) selected_cut_09516

theorem unmarked_context_11_5853_262612 : frontier 10 ⟨262612, by decide⟩
    (prefixCache 11 5853) (prefixPartial 11 5853) = false := by
  decide +kernel

theorem node_context_11_5853_262612 : EJMOriginalGlobalDAGData.nodes 10 ⟨262612, by decide⟩ =
    .split (coordinate 11) (![⟨262404, by decide⟩,⟨262528, by decide⟩,⟨262577, by decide⟩,⟨262611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5853_262612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5853 ⟨262612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5853
    ⟨262612, by decide⟩ (by decide) (![⟨262404, by decide⟩,⟨262528, by decide⟩,⟨262577, by decide⟩,⟨262611, by decide⟩]) unmarked_context_11_5853_262612 node_context_11_5853_262612
  intro a
  fin_cases a
  · exact context_12_23412_262404
  · exact context_12_23413_262528
  · exact context_12_23414_262577
  · exact context_12_23415_262611

theorem selected_cut_09517 : selected 9 ⟨262661, by decide⟩
    (prefixPartial 12 23416) = some ⟨12, 2, 0, 262661, 23416, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_23416_262661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23416 ⟨262661, by decide⟩ :=
  accepted_of_selected 12 23416 ⟨262661, by decide⟩ ⟨12, 2, 0, 262661, 23416, 3337, 65536⟩
    (by decide) selected_cut_09517

theorem selected_cut_09518 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93668) = some ⟨13, 1, 0, 3444, 93668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93668, 1, 16384⟩
    (by decide) selected_cut_09518

theorem selected_cut_09519 : selected 8 ⟨262683, by decide⟩
    (prefixPartial 13 93669) = some ⟨13, 2, 0, 262683, 93669, 521, 16384⟩ := by
  decide +kernel

theorem context_13_93669_262683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93669 ⟨262683, by decide⟩ :=
  accepted_of_selected 13 93669 ⟨262683, by decide⟩ ⟨13, 2, 0, 262683, 93669, 521, 16384⟩
    (by decide) selected_cut_09519

theorem selected_cut_09520 : selected 8 ⟨262745, by decide⟩
    (prefixPartial 13 93670) = some ⟨13, 2, 0, 262745, 93670, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_93670_262745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93670 ⟨262745, by decide⟩ :=
  accepted_of_selected 13 93670 ⟨262745, by decide⟩ ⟨13, 2, 0, 262745, 93670, 2681, 16384⟩
    (by decide) selected_cut_09520

theorem selected_cut_09521 : selected 8 ⟨262790, by decide⟩
    (prefixPartial 13 93671) = some ⟨13, 2, 0, 262790, 93671, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_93671_262790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93671 ⟨262790, by decide⟩ :=
  accepted_of_selected 13 93671 ⟨262790, by decide⟩ ⟨13, 2, 0, 262790, 93671, 1433, 16384⟩
    (by decide) selected_cut_09521

theorem unmarked_context_12_23417_262791 : frontier 9 ⟨262791, by decide⟩
    (prefixCache 12 23417) (prefixPartial 12 23417) = false := by
  decide +kernel

theorem node_context_12_23417_262791 : EJMOriginalGlobalDAGData.nodes 9 ⟨262791, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨262683, by decide⟩,⟨262745, by decide⟩,⟨262790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23417_262791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23417 ⟨262791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23417
    ⟨262791, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨262683, by decide⟩,⟨262745, by decide⟩,⟨262790, by decide⟩]) unmarked_context_12_23417_262791 node_context_12_23417_262791
  intro a
  fin_cases a
  · exact context_13_93668_3444
  · exact context_13_93669_262683
  · exact context_13_93670_262745
  · exact context_13_93671_262790

theorem selected_cut_09522 : selected 9 ⟨262842, by decide⟩
    (prefixPartial 12 23418) = some ⟨12, 2, 0, 262842, 23418, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_23418_262842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23418 ⟨262842, by decide⟩ :=
  accepted_of_selected 12 23418 ⟨262842, by decide⟩ ⟨12, 2, 0, 262842, 23418, 3661, 65536⟩
    (by decide) selected_cut_09522

theorem selected_cut_09523 : selected 9 ⟨262882, by decide⟩
    (prefixPartial 12 23419) = some ⟨12, 2, 0, 262882, 23419, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_23419_262882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23419 ⟨262882, by decide⟩ :=
  accepted_of_selected 12 23419 ⟨262882, by decide⟩ ⟨12, 2, 0, 262882, 23419, 3581, 65536⟩
    (by decide) selected_cut_09523

theorem unmarked_context_11_5854_262883 : frontier 10 ⟨262883, by decide⟩
    (prefixCache 11 5854) (prefixPartial 11 5854) = false := by
  decide +kernel

theorem node_context_11_5854_262883 : EJMOriginalGlobalDAGData.nodes 10 ⟨262883, by decide⟩ =
    .split (coordinate 11) (![⟨262661, by decide⟩,⟨262791, by decide⟩,⟨262842, by decide⟩,⟨262882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5854_262883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5854 ⟨262883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5854
    ⟨262883, by decide⟩ (by decide) (![⟨262661, by decide⟩,⟨262791, by decide⟩,⟨262842, by decide⟩,⟨262882, by decide⟩]) unmarked_context_11_5854_262883 node_context_11_5854_262883
  intro a
  fin_cases a
  · exact context_12_23416_262661
  · exact context_12_23417_262791
  · exact context_12_23418_262842
  · exact context_12_23419_262882

theorem selected_cut_09524 : selected 9 ⟨262917, by decide⟩
    (prefixPartial 12 23420) = some ⟨12, 2, 0, 262917, 23420, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_23420_262917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23420 ⟨262917, by decide⟩ :=
  accepted_of_selected 12 23420 ⟨262917, by decide⟩ ⟨12, 2, 0, 262917, 23420, 2513, 65536⟩
    (by decide) selected_cut_09524

theorem selected_cut_09525 : selected 9 ⟨262976, by decide⟩
    (prefixPartial 12 23421) = some ⟨12, 2, 0, 262976, 23421, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_23421_262976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23421 ⟨262976, by decide⟩ :=
  accepted_of_selected 12 23421 ⟨262976, by decide⟩ ⟨12, 2, 0, 262976, 23421, 3445, 65536⟩
    (by decide) selected_cut_09525

theorem selected_cut_09526 : selected 9 ⟨263014, by decide⟩
    (prefixPartial 12 23422) = some ⟨12, 2, 0, 263014, 23422, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_23422_263014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23422 ⟨263014, by decide⟩ :=
  accepted_of_selected 12 23422 ⟨263014, by decide⟩ ⟨12, 2, 0, 263014, 23422, 2777, 65536⟩
    (by decide) selected_cut_09526

theorem selected_cut_09527 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93692) = some ⟨13, 1, 0, 3444, 93692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93692, 1, 16384⟩
    (by decide) selected_cut_09527

theorem selected_cut_09528 : selected 8 ⟨263019, by decide⟩
    (prefixPartial 13 93693) = some ⟨13, 2, 0, 263019, 93693, 89, 16384⟩ := by
  decide +kernel

theorem context_13_93693_263019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93693 ⟨263019, by decide⟩ :=
  accepted_of_selected 13 93693 ⟨263019, by decide⟩ ⟨13, 2, 0, 263019, 93693, 89, 16384⟩
    (by decide) selected_cut_09528

theorem selected_cut_09529 : selected 8 ⟨263077, by decide⟩
    (prefixPartial 13 93694) = some ⟨13, 2, 0, 263077, 93694, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_93694_263077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93694 ⟨263077, by decide⟩ :=
  accepted_of_selected 13 93694 ⟨263077, by decide⟩ ⟨13, 2, 0, 263077, 93694, 2721, 16384⟩
    (by decide) selected_cut_09529

theorem selected_cut_09530 : selected 8 ⟨263118, by decide⟩
    (prefixPartial 13 93695) = some ⟨13, 2, 0, 263118, 93695, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_93695_263118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93695 ⟨263118, by decide⟩ :=
  accepted_of_selected 13 93695 ⟨263118, by decide⟩ ⟨13, 2, 0, 263118, 93695, 1317, 16384⟩
    (by decide) selected_cut_09530

theorem unmarked_context_12_23423_263119 : frontier 9 ⟨263119, by decide⟩
    (prefixCache 12 23423) (prefixPartial 12 23423) = false := by
  decide +kernel

theorem node_context_12_23423_263119 : EJMOriginalGlobalDAGData.nodes 9 ⟨263119, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨263019, by decide⟩,⟨263077, by decide⟩,⟨263118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23423_263119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23423 ⟨263119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23423
    ⟨263119, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨263019, by decide⟩,⟨263077, by decide⟩,⟨263118, by decide⟩]) unmarked_context_12_23423_263119 node_context_12_23423_263119
  intro a
  fin_cases a
  · exact context_13_93692_3444
  · exact context_13_93693_263019
  · exact context_13_93694_263077
  · exact context_13_93695_263118

theorem unmarked_context_11_5855_263120 : frontier 10 ⟨263120, by decide⟩
    (prefixCache 11 5855) (prefixPartial 11 5855) = false := by
  decide +kernel

theorem node_context_11_5855_263120 : EJMOriginalGlobalDAGData.nodes 10 ⟨263120, by decide⟩ =
    .split (coordinate 11) (![⟨262917, by decide⟩,⟨262976, by decide⟩,⟨263014, by decide⟩,⟨263119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5855_263120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5855 ⟨263120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5855
    ⟨263120, by decide⟩ (by decide) (![⟨262917, by decide⟩,⟨262976, by decide⟩,⟨263014, by decide⟩,⟨263119, by decide⟩]) unmarked_context_11_5855_263120 node_context_11_5855_263120
  intro a
  fin_cases a
  · exact context_12_23420_262917
  · exact context_12_23421_262976
  · exact context_12_23422_263014
  · exact context_12_23423_263119

theorem unmarked_context_10_1463_263121 : frontier 11 ⟨263121, by decide⟩
    (prefixCache 10 1463) (prefixPartial 10 1463) = false := by
  decide +kernel

theorem node_context_10_1463_263121 : EJMOriginalGlobalDAGData.nodes 11 ⟨263121, by decide⟩ =
    .split (coordinate 10) (![⟨262363, by decide⟩,⟨262612, by decide⟩,⟨262883, by decide⟩,⟨263120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1463_263121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1463 ⟨263121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1463
    ⟨263121, by decide⟩ (by decide) (![⟨262363, by decide⟩,⟨262612, by decide⟩,⟨262883, by decide⟩,⟨263120, by decide⟩]) unmarked_context_10_1463_263121 node_context_10_1463_263121
  intro a
  fin_cases a
  · exact context_11_5852_262363
  · exact context_11_5853_262612
  · exact context_11_5854_262883
  · exact context_11_5855_263120

theorem unmarked_context_9_365_263122 : frontier 12 ⟨263122, by decide⟩
    (prefixCache 9 365) (prefixPartial 9 365) = false := by
  decide +kernel

theorem node_context_9_365_263122 : EJMOriginalGlobalDAGData.nodes 12 ⟨263122, by decide⟩ =
    .split (coordinate 9) (![⟨259601, by decide⟩,⟨260811, by decide⟩,⟨262110, by decide⟩,⟨263121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_365_263122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 365 ⟨263122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 365
    ⟨263122, by decide⟩ (by decide) (![⟨259601, by decide⟩,⟨260811, by decide⟩,⟨262110, by decide⟩,⟨263121, by decide⟩]) unmarked_context_9_365_263122 node_context_9_365_263122
  intro a
  fin_cases a
  · exact context_10_1460_259601
  · exact context_10_1461_260811
  · exact context_10_1462_262110
  · exact context_10_1463_263121

theorem selected_cut_09531 : selected 9 ⟨263161, by decide⟩
    (prefixPartial 12 23424) = some ⟨12, 2, 0, 263161, 23424, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_23424_263161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23424 ⟨263161, by decide⟩ :=
  accepted_of_selected 12 23424 ⟨263161, by decide⟩ ⟨12, 2, 0, 263161, 23424, 2613, 65536⟩
    (by decide) selected_cut_09531

theorem selected_cut_09532 : selected 9 ⟨263195, by decide⟩
    (prefixPartial 12 23425) = some ⟨12, 2, 0, 263195, 23425, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_23425_263195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23425 ⟨263195, by decide⟩ :=
  accepted_of_selected 12 23425 ⟨263195, by decide⟩ ⟨12, 2, 0, 263195, 23425, 2385, 65536⟩
    (by decide) selected_cut_09532

theorem selected_cut_09533 : selected 9 ⟨263231, by decide⟩
    (prefixPartial 12 23426) = some ⟨12, 2, 0, 263231, 23426, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_23426_263231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23426 ⟨263231, by decide⟩ :=
  accepted_of_selected 12 23426 ⟨263231, by decide⟩ ⟨12, 2, 0, 263231, 23426, 2485, 65536⟩
    (by decide) selected_cut_09533

theorem selected_cut_09534 : selected 9 ⟨263262, by decide⟩
    (prefixPartial 12 23427) = some ⟨12, 2, 0, 263262, 23427, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_23427_263262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23427 ⟨263262, by decide⟩ :=
  accepted_of_selected 12 23427 ⟨263262, by decide⟩ ⟨12, 2, 0, 263262, 23427, 2373, 65536⟩
    (by decide) selected_cut_09534

theorem unmarked_context_11_5856_263263 : frontier 10 ⟨263263, by decide⟩
    (prefixCache 11 5856) (prefixPartial 11 5856) = false := by
  decide +kernel

theorem node_context_11_5856_263263 : EJMOriginalGlobalDAGData.nodes 10 ⟨263263, by decide⟩ =
    .split (coordinate 11) (![⟨263161, by decide⟩,⟨263195, by decide⟩,⟨263231, by decide⟩,⟨263262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5856_263263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5856 ⟨263263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5856
    ⟨263263, by decide⟩ (by decide) (![⟨263161, by decide⟩,⟨263195, by decide⟩,⟨263231, by decide⟩,⟨263262, by decide⟩]) unmarked_context_11_5856_263263 node_context_11_5856_263263
  intro a
  fin_cases a
  · exact context_12_23424_263161
  · exact context_12_23425_263195
  · exact context_12_23426_263231
  · exact context_12_23427_263262

theorem selected_cut_09535 : selected 9 ⟨263299, by decide⟩
    (prefixPartial 12 23428) = some ⟨12, 2, 0, 263299, 23428, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_23428_263299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23428 ⟨263299, by decide⟩ :=
  accepted_of_selected 12 23428 ⟨263299, by decide⟩ ⟨12, 2, 0, 263299, 23428, 2505, 65536⟩
    (by decide) selected_cut_09535

theorem selected_cut_09536 : selected 9 ⟨263329, by decide⟩
    (prefixPartial 12 23429) = some ⟨12, 2, 0, 263329, 23429, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_23429_263329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23429 ⟨263329, by decide⟩ :=
  accepted_of_selected 12 23429 ⟨263329, by decide⟩ ⟨12, 2, 0, 263329, 23429, 2377, 65536⟩
    (by decide) selected_cut_09536

theorem selected_cut_09537 : selected 9 ⟨263358, by decide⟩
    (prefixPartial 12 23430) = some ⟨12, 2, 0, 263358, 23430, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_23430_263358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23430 ⟨263358, by decide⟩ :=
  accepted_of_selected 12 23430 ⟨263358, by decide⟩ ⟨12, 2, 0, 263358, 23430, 2505, 65536⟩
    (by decide) selected_cut_09537

theorem selected_cut_09538 : selected 9 ⟨263386, by decide⟩
    (prefixPartial 12 23431) = some ⟨12, 2, 0, 263386, 23431, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_23431_263386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23431 ⟨263386, by decide⟩ :=
  accepted_of_selected 12 23431 ⟨263386, by decide⟩ ⟨12, 2, 0, 263386, 23431, 2177, 65536⟩
    (by decide) selected_cut_09538

theorem unmarked_context_11_5857_263387 : frontier 10 ⟨263387, by decide⟩
    (prefixCache 11 5857) (prefixPartial 11 5857) = false := by
  decide +kernel

theorem node_context_11_5857_263387 : EJMOriginalGlobalDAGData.nodes 10 ⟨263387, by decide⟩ =
    .split (coordinate 11) (![⟨263299, by decide⟩,⟨263329, by decide⟩,⟨263358, by decide⟩,⟨263386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5857_263387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5857 ⟨263387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5857
    ⟨263387, by decide⟩ (by decide) (![⟨263299, by decide⟩,⟨263329, by decide⟩,⟨263358, by decide⟩,⟨263386, by decide⟩]) unmarked_context_11_5857_263387 node_context_11_5857_263387
  intro a
  fin_cases a
  · exact context_12_23428_263299
  · exact context_12_23429_263329
  · exact context_12_23430_263358
  · exact context_12_23431_263386

theorem selected_cut_09539 : selected 9 ⟨263422, by decide⟩
    (prefixPartial 12 23432) = some ⟨12, 2, 0, 263422, 23432, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_23432_263422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23432 ⟨263422, by decide⟩ :=
  accepted_of_selected 12 23432 ⟨263422, by decide⟩ ⟨12, 2, 0, 263422, 23432, 2589, 65536⟩
    (by decide) selected_cut_09539

theorem selected_cut_09540 : selected 9 ⟨263457, by decide⟩
    (prefixPartial 12 23433) = some ⟨12, 2, 0, 263457, 23433, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_23433_263457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23433 ⟨263457, by decide⟩ :=
  accepted_of_selected 12 23433 ⟨263457, by decide⟩ ⟨12, 2, 0, 263457, 23433, 2469, 65536⟩
    (by decide) selected_cut_09540

theorem selected_cut_09541 : selected 9 ⟨263483, by decide⟩
    (prefixPartial 12 23434) = some ⟨12, 2, 0, 263483, 23434, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_23434_263483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23434 ⟨263483, by decide⟩ :=
  accepted_of_selected 12 23434 ⟨263483, by decide⟩ ⟨12, 2, 0, 263483, 23434, 2373, 65536⟩
    (by decide) selected_cut_09541

theorem selected_cut_09542 : selected 9 ⟨263514, by decide⟩
    (prefixPartial 12 23435) = some ⟨12, 2, 0, 263514, 23435, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_23435_263514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23435 ⟨263514, by decide⟩ :=
  accepted_of_selected 12 23435 ⟨263514, by decide⟩ ⟨12, 2, 0, 263514, 23435, 2217, 65536⟩
    (by decide) selected_cut_09542

theorem unmarked_context_11_5858_263515 : frontier 10 ⟨263515, by decide⟩
    (prefixCache 11 5858) (prefixPartial 11 5858) = false := by
  decide +kernel

theorem node_context_11_5858_263515 : EJMOriginalGlobalDAGData.nodes 10 ⟨263515, by decide⟩ =
    .split (coordinate 11) (![⟨263422, by decide⟩,⟨263457, by decide⟩,⟨263483, by decide⟩,⟨263514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5858_263515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5858 ⟨263515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5858
    ⟨263515, by decide⟩ (by decide) (![⟨263422, by decide⟩,⟨263457, by decide⟩,⟨263483, by decide⟩,⟨263514, by decide⟩]) unmarked_context_11_5858_263515 node_context_11_5858_263515
  intro a
  fin_cases a
  · exact context_12_23432_263422
  · exact context_12_23433_263457
  · exact context_12_23434_263483
  · exact context_12_23435_263514

theorem selected_cut_09543 : selected 9 ⟨263537, by decide⟩
    (prefixPartial 12 23436) = some ⟨12, 2, 0, 263537, 23436, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_23436_263537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23436 ⟨263537, by decide⟩ :=
  accepted_of_selected 12 23436 ⟨263537, by decide⟩ ⟨12, 2, 0, 263537, 23436, 2125, 65536⟩
    (by decide) selected_cut_09543

theorem selected_cut_09544 : selected 9 ⟨263561, by decide⟩
    (prefixPartial 12 23437) = some ⟨12, 2, 0, 263561, 23437, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_23437_263561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23437 ⟨263561, by decide⟩ :=
  accepted_of_selected 12 23437 ⟨263561, by decide⟩ ⟨12, 2, 0, 263561, 23437, 2137, 65536⟩
    (by decide) selected_cut_09544

theorem selected_cut_09545 : selected 9 ⟨263585, by decide⟩
    (prefixPartial 12 23438) = some ⟨12, 2, 0, 263585, 23438, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_23438_263585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23438 ⟨263585, by decide⟩ :=
  accepted_of_selected 12 23438 ⟨263585, by decide⟩ ⟨12, 2, 0, 263585, 23438, 2129, 65536⟩
    (by decide) selected_cut_09545

theorem selected_cut_09546 : selected 9 ⟨263635, by decide⟩
    (prefixPartial 12 23439) = some ⟨12, 2, 0, 263635, 23439, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_23439_263635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23439 ⟨263635, by decide⟩ :=
  accepted_of_selected 12 23439 ⟨263635, by decide⟩ ⟨12, 2, 0, 263635, 23439, 2969, 65536⟩
    (by decide) selected_cut_09546

theorem unmarked_context_11_5859_263636 : frontier 10 ⟨263636, by decide⟩
    (prefixCache 11 5859) (prefixPartial 11 5859) = false := by
  decide +kernel

theorem node_context_11_5859_263636 : EJMOriginalGlobalDAGData.nodes 10 ⟨263636, by decide⟩ =
    .split (coordinate 11) (![⟨263537, by decide⟩,⟨263561, by decide⟩,⟨263585, by decide⟩,⟨263635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5859_263636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5859 ⟨263636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5859
    ⟨263636, by decide⟩ (by decide) (![⟨263537, by decide⟩,⟨263561, by decide⟩,⟨263585, by decide⟩,⟨263635, by decide⟩]) unmarked_context_11_5859_263636 node_context_11_5859_263636
  intro a
  fin_cases a
  · exact context_12_23436_263537
  · exact context_12_23437_263561
  · exact context_12_23438_263585
  · exact context_12_23439_263635

theorem unmarked_context_10_1464_263637 : frontier 11 ⟨263637, by decide⟩
    (prefixCache 10 1464) (prefixPartial 10 1464) = false := by
  decide +kernel

theorem node_context_10_1464_263637 : EJMOriginalGlobalDAGData.nodes 11 ⟨263637, by decide⟩ =
    .split (coordinate 10) (![⟨263263, by decide⟩,⟨263387, by decide⟩,⟨263515, by decide⟩,⟨263636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1464_263637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1464 ⟨263637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1464
    ⟨263637, by decide⟩ (by decide) (![⟨263263, by decide⟩,⟨263387, by decide⟩,⟨263515, by decide⟩,⟨263636, by decide⟩]) unmarked_context_10_1464_263637 node_context_10_1464_263637
  intro a
  fin_cases a
  · exact context_11_5856_263263
  · exact context_11_5857_263387
  · exact context_11_5858_263515
  · exact context_11_5859_263636

theorem selected_cut_09547 : selected 9 ⟨263662, by decide⟩
    (prefixPartial 12 23440) = some ⟨12, 2, 0, 263662, 23440, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_23440_263662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23440 ⟨263662, by decide⟩ :=
  accepted_of_selected 12 23440 ⟨263662, by decide⟩ ⟨12, 2, 0, 263662, 23440, 2193, 65536⟩
    (by decide) selected_cut_09547

theorem selected_cut_09548 : selected 9 ⟨263692, by decide⟩
    (prefixPartial 12 23441) = some ⟨12, 2, 0, 263692, 23441, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_23441_263692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23441 ⟨263692, by decide⟩ :=
  accepted_of_selected 12 23441 ⟨263692, by decide⟩ ⟨12, 2, 0, 263692, 23441, 2093, 65536⟩
    (by decide) selected_cut_09548

theorem selected_cut_09549 : selected 9 ⟨263721, by decide⟩
    (prefixPartial 12 23442) = some ⟨12, 2, 0, 263721, 23442, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_23442_263721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23442 ⟨263721, by decide⟩ :=
  accepted_of_selected 12 23442 ⟨263721, by decide⟩ ⟨12, 2, 0, 263721, 23442, 2349, 65536⟩
    (by decide) selected_cut_09549

theorem selected_cut_09550 : selected 9 ⟨263746, by decide⟩
    (prefixPartial 12 23443) = some ⟨12, 2, 0, 263746, 23443, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_23443_263746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23443 ⟨263746, by decide⟩ :=
  accepted_of_selected 12 23443 ⟨263746, by decide⟩ ⟨12, 2, 0, 263746, 23443, 2029, 65536⟩
    (by decide) selected_cut_09550

theorem unmarked_context_11_5860_263747 : frontier 10 ⟨263747, by decide⟩
    (prefixCache 11 5860) (prefixPartial 11 5860) = false := by
  decide +kernel

theorem node_context_11_5860_263747 : EJMOriginalGlobalDAGData.nodes 10 ⟨263747, by decide⟩ =
    .split (coordinate 11) (![⟨263662, by decide⟩,⟨263692, by decide⟩,⟨263721, by decide⟩,⟨263746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5860_263747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5860 ⟨263747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5860
    ⟨263747, by decide⟩ (by decide) (![⟨263662, by decide⟩,⟨263692, by decide⟩,⟨263721, by decide⟩,⟨263746, by decide⟩]) unmarked_context_11_5860_263747 node_context_11_5860_263747
  intro a
  fin_cases a
  · exact context_12_23440_263662
  · exact context_12_23441_263692
  · exact context_12_23442_263721
  · exact context_12_23443_263746

theorem selected_cut_09551 : selected 9 ⟨263775, by decide⟩
    (prefixPartial 12 23444) = some ⟨12, 2, 0, 263775, 23444, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_23444_263775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23444 ⟨263775, by decide⟩ :=
  accepted_of_selected 12 23444 ⟨263775, by decide⟩ ⟨12, 2, 0, 263775, 23444, 2093, 65536⟩
    (by decide) selected_cut_09551

theorem selected_cut_09552 : selected 9 ⟨263797, by decide⟩
    (prefixPartial 12 23445) = some ⟨12, 2, 0, 263797, 23445, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_23445_263797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23445 ⟨263797, by decide⟩ :=
  accepted_of_selected 12 23445 ⟨263797, by decide⟩ ⟨12, 2, 0, 263797, 23445, 2021, 65536⟩
    (by decide) selected_cut_09552

theorem selected_cut_09553 : selected 9 ⟨263827, by decide⟩
    (prefixPartial 12 23446) = some ⟨12, 2, 0, 263827, 23446, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_23446_263827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23446 ⟨263827, by decide⟩ :=
  accepted_of_selected 12 23446 ⟨263827, by decide⟩ ⟨12, 2, 0, 263827, 23446, 2289, 65536⟩
    (by decide) selected_cut_09553

theorem selected_cut_09554 : selected 9 ⟨263849, by decide⟩
    (prefixPartial 12 23447) = some ⟨12, 2, 0, 263849, 23447, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_23447_263849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23447 ⟨263849, by decide⟩ :=
  accepted_of_selected 12 23447 ⟨263849, by decide⟩ ⟨12, 2, 0, 263849, 23447, 1897, 65536⟩
    (by decide) selected_cut_09554

theorem unmarked_context_11_5861_263850 : frontier 10 ⟨263850, by decide⟩
    (prefixCache 11 5861) (prefixPartial 11 5861) = false := by
  decide +kernel

theorem node_context_11_5861_263850 : EJMOriginalGlobalDAGData.nodes 10 ⟨263850, by decide⟩ =
    .split (coordinate 11) (![⟨263775, by decide⟩,⟨263797, by decide⟩,⟨263827, by decide⟩,⟨263849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5861_263850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5861 ⟨263850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5861
    ⟨263850, by decide⟩ (by decide) (![⟨263775, by decide⟩,⟨263797, by decide⟩,⟨263827, by decide⟩,⟨263849, by decide⟩]) unmarked_context_11_5861_263850 node_context_11_5861_263850
  intro a
  fin_cases a
  · exact context_12_23444_263775
  · exact context_12_23445_263797
  · exact context_12_23446_263827
  · exact context_12_23447_263849

theorem selected_cut_09555 : selected 9 ⟨263879, by decide⟩
    (prefixPartial 12 23448) = some ⟨12, 2, 0, 263879, 23448, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_23448_263879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23448 ⟨263879, by decide⟩ :=
  accepted_of_selected 12 23448 ⟨263879, by decide⟩ ⟨12, 2, 0, 263879, 23448, 2029, 65536⟩
    (by decide) selected_cut_09555

theorem selected_cut_09556 : selected 9 ⟨263908, by decide⟩
    (prefixPartial 12 23449) = some ⟨12, 2, 0, 263908, 23449, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_23449_263908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23449 ⟨263908, by decide⟩ :=
  accepted_of_selected 12 23449 ⟨263908, by decide⟩ ⟨12, 2, 0, 263908, 23449, 2117, 65536⟩
    (by decide) selected_cut_09556

theorem selected_cut_09557 : selected 9 ⟨263930, by decide⟩
    (prefixPartial 12 23450) = some ⟨12, 2, 0, 263930, 23450, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_23450_263930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23450 ⟨263930, by decide⟩ :=
  accepted_of_selected 12 23450 ⟨263930, by decide⟩ ⟨12, 2, 0, 263930, 23450, 2105, 65536⟩
    (by decide) selected_cut_09557

theorem selected_cut_09558 : selected 9 ⟨263952, by decide⟩
    (prefixPartial 12 23451) = some ⟨12, 2, 0, 263952, 23451, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_23451_263952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23451 ⟨263952, by decide⟩ :=
  accepted_of_selected 12 23451 ⟨263952, by decide⟩ ⟨12, 2, 0, 263952, 23451, 1805, 65536⟩
    (by decide) selected_cut_09558

theorem unmarked_context_11_5862_263953 : frontier 10 ⟨263953, by decide⟩
    (prefixCache 11 5862) (prefixPartial 11 5862) = false := by
  decide +kernel

theorem node_context_11_5862_263953 : EJMOriginalGlobalDAGData.nodes 10 ⟨263953, by decide⟩ =
    .split (coordinate 11) (![⟨263879, by decide⟩,⟨263908, by decide⟩,⟨263930, by decide⟩,⟨263952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5862_263953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5862 ⟨263953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5862
    ⟨263953, by decide⟩ (by decide) (![⟨263879, by decide⟩,⟨263908, by decide⟩,⟨263930, by decide⟩,⟨263952, by decide⟩]) unmarked_context_11_5862_263953 node_context_11_5862_263953
  intro a
  fin_cases a
  · exact context_12_23448_263879
  · exact context_12_23449_263908
  · exact context_12_23450_263930
  · exact context_12_23451_263952

theorem selected_cut_09559 : selected 9 ⟨263975, by decide⟩
    (prefixPartial 12 23452) = some ⟨12, 2, 0, 263975, 23452, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_23452_263975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23452 ⟨263975, by decide⟩ :=
  accepted_of_selected 12 23452 ⟨263975, by decide⟩ ⟨12, 2, 0, 263975, 23452, 1661, 65536⟩
    (by decide) selected_cut_09559

theorem selected_cut_09560 : selected 9 ⟨263993, by decide⟩
    (prefixPartial 12 23453) = some ⟨12, 2, 0, 263993, 23453, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_23453_263993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23453 ⟨263993, by decide⟩ :=
  accepted_of_selected 12 23453 ⟨263993, by decide⟩ ⟨12, 2, 0, 263993, 23453, 1693, 65536⟩
    (by decide) selected_cut_09560

theorem selected_cut_09561 : selected 9 ⟨264011, by decide⟩
    (prefixPartial 12 23454) = some ⟨12, 2, 0, 264011, 23454, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_23454_264011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23454 ⟨264011, by decide⟩ :=
  accepted_of_selected 12 23454 ⟨264011, by decide⟩ ⟨12, 2, 0, 264011, 23454, 1809, 65536⟩
    (by decide) selected_cut_09561

theorem selected_cut_09562 : selected 9 ⟨264052, by decide⟩
    (prefixPartial 12 23455) = some ⟨12, 2, 0, 264052, 23455, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_23455_264052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23455 ⟨264052, by decide⟩ :=
  accepted_of_selected 12 23455 ⟨264052, by decide⟩ ⟨12, 2, 0, 264052, 23455, 2269, 65536⟩
    (by decide) selected_cut_09562

theorem unmarked_context_11_5863_264053 : frontier 10 ⟨264053, by decide⟩
    (prefixCache 11 5863) (prefixPartial 11 5863) = false := by
  decide +kernel

theorem node_context_11_5863_264053 : EJMOriginalGlobalDAGData.nodes 10 ⟨264053, by decide⟩ =
    .split (coordinate 11) (![⟨263975, by decide⟩,⟨263993, by decide⟩,⟨264011, by decide⟩,⟨264052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5863_264053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5863 ⟨264053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5863
    ⟨264053, by decide⟩ (by decide) (![⟨263975, by decide⟩,⟨263993, by decide⟩,⟨264011, by decide⟩,⟨264052, by decide⟩]) unmarked_context_11_5863_264053 node_context_11_5863_264053
  intro a
  fin_cases a
  · exact context_12_23452_263975
  · exact context_12_23453_263993
  · exact context_12_23454_264011
  · exact context_12_23455_264052

theorem unmarked_context_10_1465_264054 : frontier 11 ⟨264054, by decide⟩
    (prefixCache 10 1465) (prefixPartial 10 1465) = false := by
  decide +kernel

theorem node_context_10_1465_264054 : EJMOriginalGlobalDAGData.nodes 11 ⟨264054, by decide⟩ =
    .split (coordinate 10) (![⟨263747, by decide⟩,⟨263850, by decide⟩,⟨263953, by decide⟩,⟨264053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1465_264054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1465 ⟨264054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1465
    ⟨264054, by decide⟩ (by decide) (![⟨263747, by decide⟩,⟨263850, by decide⟩,⟨263953, by decide⟩,⟨264053, by decide⟩]) unmarked_context_10_1465_264054 node_context_10_1465_264054
  intro a
  fin_cases a
  · exact context_11_5860_263747
  · exact context_11_5861_263850
  · exact context_11_5862_263953
  · exact context_11_5863_264053

theorem selected_cut_09563 : selected 9 ⟨264073, by decide⟩
    (prefixPartial 12 23456) = some ⟨12, 2, 0, 264073, 23456, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_23456_264073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23456 ⟨264073, by decide⟩ :=
  accepted_of_selected 12 23456 ⟨264073, by decide⟩ ⟨12, 2, 0, 264073, 23456, 1525, 65536⟩
    (by decide) selected_cut_09563

theorem selected_cut_09564 : selected 9 ⟨264092, by decide⟩
    (prefixPartial 12 23457) = some ⟨12, 2, 0, 264092, 23457, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_23457_264092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23457 ⟨264092, by decide⟩ :=
  accepted_of_selected 12 23457 ⟨264092, by decide⟩ ⟨12, 2, 0, 264092, 23457, 1385, 65536⟩
    (by decide) selected_cut_09564

theorem selected_cut_09565 : selected 9 ⟨264107, by decide⟩
    (prefixPartial 12 23458) = some ⟨12, 2, 0, 264107, 23458, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_23458_264107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23458 ⟨264107, by decide⟩ :=
  accepted_of_selected 12 23458 ⟨264107, by decide⟩ ⟨12, 2, 0, 264107, 23458, 1445, 65536⟩
    (by decide) selected_cut_09565

theorem selected_cut_09566 : selected 9 ⟨264125, by decide⟩
    (prefixPartial 12 23459) = some ⟨12, 2, 0, 264125, 23459, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_23459_264125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23459 ⟨264125, by decide⟩ :=
  accepted_of_selected 12 23459 ⟨264125, by decide⟩ ⟨12, 2, 0, 264125, 23459, 1265, 65536⟩
    (by decide) selected_cut_09566

theorem unmarked_context_11_5864_264126 : frontier 10 ⟨264126, by decide⟩
    (prefixCache 11 5864) (prefixPartial 11 5864) = false := by
  decide +kernel

theorem node_context_11_5864_264126 : EJMOriginalGlobalDAGData.nodes 10 ⟨264126, by decide⟩ =
    .split (coordinate 11) (![⟨264073, by decide⟩,⟨264092, by decide⟩,⟨264107, by decide⟩,⟨264125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5864_264126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5864 ⟨264126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5864
    ⟨264126, by decide⟩ (by decide) (![⟨264073, by decide⟩,⟨264092, by decide⟩,⟨264107, by decide⟩,⟨264125, by decide⟩]) unmarked_context_11_5864_264126 node_context_11_5864_264126
  intro a
  fin_cases a
  · exact context_12_23456_264073
  · exact context_12_23457_264092
  · exact context_12_23458_264107
  · exact context_12_23459_264125

theorem selected_cut_09567 : selected 9 ⟨264151, by decide⟩
    (prefixPartial 12 23460) = some ⟨12, 2, 0, 264151, 23460, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_23460_264151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23460 ⟨264151, by decide⟩ :=
  accepted_of_selected 12 23460 ⟨264151, by decide⟩ ⟨12, 2, 0, 264151, 23460, 1489, 65536⟩
    (by decide) selected_cut_09567

theorem selected_cut_09568 : selected 9 ⟨264173, by decide⟩
    (prefixPartial 12 23461) = some ⟨12, 2, 0, 264173, 23461, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_23461_264173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23461 ⟨264173, by decide⟩ :=
  accepted_of_selected 12 23461 ⟨264173, by decide⟩ ⟨12, 2, 0, 264173, 23461, 1465, 65536⟩
    (by decide) selected_cut_09568

theorem selected_cut_09569 : selected 9 ⟨264190, by decide⟩
    (prefixPartial 12 23462) = some ⟨12, 2, 0, 264190, 23462, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_23462_264190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23462 ⟨264190, by decide⟩ :=
  accepted_of_selected 12 23462 ⟨264190, by decide⟩ ⟨12, 2, 0, 264190, 23462, 1529, 65536⟩
    (by decide) selected_cut_09569

theorem selected_cut_09570 : selected 9 ⟨264206, by decide⟩
    (prefixPartial 12 23463) = some ⟨12, 2, 0, 264206, 23463, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_23463_264206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23463 ⟨264206, by decide⟩ :=
  accepted_of_selected 12 23463 ⟨264206, by decide⟩ ⟨12, 2, 0, 264206, 23463, 1277, 65536⟩
    (by decide) selected_cut_09570

theorem unmarked_context_11_5865_264207 : frontier 10 ⟨264207, by decide⟩
    (prefixCache 11 5865) (prefixPartial 11 5865) = false := by
  decide +kernel

theorem node_context_11_5865_264207 : EJMOriginalGlobalDAGData.nodes 10 ⟨264207, by decide⟩ =
    .split (coordinate 11) (![⟨264151, by decide⟩,⟨264173, by decide⟩,⟨264190, by decide⟩,⟨264206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5865_264207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5865 ⟨264207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5865
    ⟨264207, by decide⟩ (by decide) (![⟨264151, by decide⟩,⟨264173, by decide⟩,⟨264190, by decide⟩,⟨264206, by decide⟩]) unmarked_context_11_5865_264207 node_context_11_5865_264207
  intro a
  fin_cases a
  · exact context_12_23460_264151
  · exact context_12_23461_264173
  · exact context_12_23462_264190
  · exact context_12_23463_264206

theorem selected_cut_09571 : selected 10 ⟨264257, by decide⟩
    (prefixPartial 11 5866) = some ⟨11, 2, 0, 264257, 5866, 3565, 262144⟩ := by
  decide +kernel

theorem context_11_5866_264257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5866 ⟨264257, by decide⟩ :=
  accepted_of_selected 11 5866 ⟨264257, by decide⟩ ⟨11, 2, 0, 264257, 5866, 3565, 262144⟩
    (by decide) selected_cut_09571

theorem selected_cut_09572 : selected 9 ⟨264274, by decide⟩
    (prefixPartial 12 23468) = some ⟨12, 2, 0, 264274, 23468, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_23468_264274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23468 ⟨264274, by decide⟩ :=
  accepted_of_selected 12 23468 ⟨264274, by decide⟩ ⟨12, 2, 0, 264274, 23468, 1297, 65536⟩
    (by decide) selected_cut_09572

theorem selected_cut_09573 : selected 9 ⟨264286, by decide⟩
    (prefixPartial 12 23469) = some ⟨12, 2, 0, 264286, 23469, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_23469_264286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23469 ⟨264286, by decide⟩ :=
  accepted_of_selected 12 23469 ⟨264286, by decide⟩ ⟨12, 2, 0, 264286, 23469, 1289, 65536⟩
    (by decide) selected_cut_09573

theorem selected_cut_09574 : selected 9 ⟨264299, by decide⟩
    (prefixPartial 12 23470) = some ⟨12, 2, 0, 264299, 23470, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_23470_264299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23470 ⟨264299, by decide⟩ :=
  accepted_of_selected 12 23470 ⟨264299, by decide⟩ ⟨12, 2, 0, 264299, 23470, 1221, 65536⟩
    (by decide) selected_cut_09574

theorem selected_cut_09575 : selected 9 ⟨264322, by decide⟩
    (prefixPartial 12 23471) = some ⟨12, 2, 0, 264322, 23471, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_23471_264322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23471 ⟨264322, by decide⟩ :=
  accepted_of_selected 12 23471 ⟨264322, by decide⟩ ⟨12, 2, 0, 264322, 23471, 1677, 65536⟩
    (by decide) selected_cut_09575

theorem unmarked_context_11_5867_264323 : frontier 10 ⟨264323, by decide⟩
    (prefixCache 11 5867) (prefixPartial 11 5867) = false := by
  decide +kernel

theorem node_context_11_5867_264323 : EJMOriginalGlobalDAGData.nodes 10 ⟨264323, by decide⟩ =
    .split (coordinate 11) (![⟨264274, by decide⟩,⟨264286, by decide⟩,⟨264299, by decide⟩,⟨264322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5867_264323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5867 ⟨264323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5867
    ⟨264323, by decide⟩ (by decide) (![⟨264274, by decide⟩,⟨264286, by decide⟩,⟨264299, by decide⟩,⟨264322, by decide⟩]) unmarked_context_11_5867_264323 node_context_11_5867_264323
  intro a
  fin_cases a
  · exact context_12_23468_264274
  · exact context_12_23469_264286
  · exact context_12_23470_264299
  · exact context_12_23471_264322

theorem unmarked_context_10_1466_264324 : frontier 11 ⟨264324, by decide⟩
    (prefixCache 10 1466) (prefixPartial 10 1466) = false := by
  decide +kernel

theorem node_context_10_1466_264324 : EJMOriginalGlobalDAGData.nodes 11 ⟨264324, by decide⟩ =
    .split (coordinate 10) (![⟨264126, by decide⟩,⟨264207, by decide⟩,⟨264257, by decide⟩,⟨264323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1466_264324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1466 ⟨264324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1466
    ⟨264324, by decide⟩ (by decide) (![⟨264126, by decide⟩,⟨264207, by decide⟩,⟨264257, by decide⟩,⟨264323, by decide⟩]) unmarked_context_10_1466_264324 node_context_10_1466_264324
  intro a
  fin_cases a
  · exact context_11_5864_264126
  · exact context_11_5865_264207
  · exact context_11_5866_264257
  · exact context_11_5867_264323

theorem selected_cut_09576 : selected 9 ⟨264338, by decide⟩
    (prefixPartial 12 23472) = some ⟨12, 2, 0, 264338, 23472, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_23472_264338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23472 ⟨264338, by decide⟩ :=
  accepted_of_selected 12 23472 ⟨264338, by decide⟩ ⟨12, 2, 0, 264338, 23472, 1305, 65536⟩
    (by decide) selected_cut_09576

theorem selected_cut_09577 : selected 9 ⟨264351, by decide⟩
    (prefixPartial 12 23473) = some ⟨12, 2, 0, 264351, 23473, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_23473_264351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23473 ⟨264351, by decide⟩ :=
  accepted_of_selected 12 23473 ⟨264351, by decide⟩ ⟨12, 2, 0, 264351, 23473, 1269, 65536⟩
    (by decide) selected_cut_09577

theorem selected_cut_09578 : selected 9 ⟨264368, by decide⟩
    (prefixPartial 12 23474) = some ⟨12, 2, 0, 264368, 23474, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_23474_264368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23474 ⟨264368, by decide⟩ :=
  accepted_of_selected 12 23474 ⟨264368, by decide⟩ ⟨12, 2, 0, 264368, 23474, 1225, 65536⟩
    (by decide) selected_cut_09578

theorem selected_cut_09579 : selected 9 ⟨264382, by decide⟩
    (prefixPartial 12 23475) = some ⟨12, 2, 0, 264382, 23475, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_23475_264382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23475 ⟨264382, by decide⟩ :=
  accepted_of_selected 12 23475 ⟨264382, by decide⟩ ⟨12, 2, 0, 264382, 23475, 1105, 65536⟩
    (by decide) selected_cut_09579

theorem unmarked_context_11_5868_264383 : frontier 10 ⟨264383, by decide⟩
    (prefixCache 11 5868) (prefixPartial 11 5868) = false := by
  decide +kernel

theorem node_context_11_5868_264383 : EJMOriginalGlobalDAGData.nodes 10 ⟨264383, by decide⟩ =
    .split (coordinate 11) (![⟨264338, by decide⟩,⟨264351, by decide⟩,⟨264368, by decide⟩,⟨264382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5868_264383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5868 ⟨264383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5868
    ⟨264383, by decide⟩ (by decide) (![⟨264338, by decide⟩,⟨264351, by decide⟩,⟨264368, by decide⟩,⟨264382, by decide⟩]) unmarked_context_11_5868_264383 node_context_11_5868_264383
  intro a
  fin_cases a
  · exact context_12_23472_264338
  · exact context_12_23473_264351
  · exact context_12_23474_264368
  · exact context_12_23475_264382

theorem selected_cut_09580 : selected 9 ⟨264408, by decide⟩
    (prefixPartial 12 23476) = some ⟨12, 2, 0, 264408, 23476, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_23476_264408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23476 ⟨264408, by decide⟩ :=
  accepted_of_selected 12 23476 ⟨264408, by decide⟩ ⟨12, 2, 0, 264408, 23476, 1289, 65536⟩
    (by decide) selected_cut_09580

theorem selected_cut_09581 : selected 9 ⟨264428, by decide⟩
    (prefixPartial 12 23477) = some ⟨12, 2, 0, 264428, 23477, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_23477_264428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23477 ⟨264428, by decide⟩ :=
  accepted_of_selected 12 23477 ⟨264428, by decide⟩ ⟨12, 2, 0, 264428, 23477, 1245, 65536⟩
    (by decide) selected_cut_09581

theorem selected_cut_09582 : selected 9 ⟨264450, by decide⟩
    (prefixPartial 12 23478) = some ⟨12, 2, 0, 264450, 23478, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_23478_264450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23478 ⟨264450, by decide⟩ :=
  accepted_of_selected 12 23478 ⟨264450, by decide⟩ ⟨12, 2, 0, 264450, 23478, 1213, 65536⟩
    (by decide) selected_cut_09582

theorem selected_cut_09583 : selected 9 ⟨264467, by decide⟩
    (prefixPartial 12 23479) = some ⟨12, 2, 0, 264467, 23479, 1025, 65536⟩ := by
  decide +kernel

theorem context_12_23479_264467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23479 ⟨264467, by decide⟩ :=
  accepted_of_selected 12 23479 ⟨264467, by decide⟩ ⟨12, 2, 0, 264467, 23479, 1025, 65536⟩
    (by decide) selected_cut_09583

theorem unmarked_context_11_5869_264468 : frontier 10 ⟨264468, by decide⟩
    (prefixCache 11 5869) (prefixPartial 11 5869) = false := by
  decide +kernel

theorem node_context_11_5869_264468 : EJMOriginalGlobalDAGData.nodes 10 ⟨264468, by decide⟩ =
    .split (coordinate 11) (![⟨264408, by decide⟩,⟨264428, by decide⟩,⟨264450, by decide⟩,⟨264467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5869_264468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5869 ⟨264468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5869
    ⟨264468, by decide⟩ (by decide) (![⟨264408, by decide⟩,⟨264428, by decide⟩,⟨264450, by decide⟩,⟨264467, by decide⟩]) unmarked_context_11_5869_264468 node_context_11_5869_264468
  intro a
  fin_cases a
  · exact context_12_23476_264408
  · exact context_12_23477_264428
  · exact context_12_23478_264450
  · exact context_12_23479_264467

theorem selected_cut_09584 : selected 9 ⟨264491, by decide⟩
    (prefixPartial 12 23480) = some ⟨12, 2, 0, 264491, 23480, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_23480_264491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23480 ⟨264491, by decide⟩ :=
  accepted_of_selected 12 23480 ⟨264491, by decide⟩ ⟨12, 2, 0, 264491, 23480, 1237, 65536⟩
    (by decide) selected_cut_09584

theorem selected_cut_09585 : selected 9 ⟨264512, by decide⟩
    (prefixPartial 12 23481) = some ⟨12, 2, 0, 264512, 23481, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_23481_264512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23481 ⟨264512, by decide⟩ :=
  accepted_of_selected 12 23481 ⟨264512, by decide⟩ ⟨12, 2, 0, 264512, 23481, 1357, 65536⟩
    (by decide) selected_cut_09585

theorem selected_cut_09586 : selected 9 ⟨264529, by decide⟩
    (prefixPartial 12 23482) = some ⟨12, 2, 0, 264529, 23482, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_23482_264529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23482 ⟨264529, by decide⟩ :=
  accepted_of_selected 12 23482 ⟨264529, by decide⟩ ⟨12, 2, 0, 264529, 23482, 1057, 65536⟩
    (by decide) selected_cut_09586

theorem selected_cut_09587 : selected 9 ⟨264544, by decide⟩
    (prefixPartial 12 23483) = some ⟨12, 2, 0, 264544, 23483, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_23483_264544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23483 ⟨264544, by decide⟩ :=
  accepted_of_selected 12 23483 ⟨264544, by decide⟩ ⟨12, 2, 0, 264544, 23483, 1093, 65536⟩
    (by decide) selected_cut_09587

theorem unmarked_context_11_5870_264545 : frontier 10 ⟨264545, by decide⟩
    (prefixCache 11 5870) (prefixPartial 11 5870) = false := by
  decide +kernel

theorem node_context_11_5870_264545 : EJMOriginalGlobalDAGData.nodes 10 ⟨264545, by decide⟩ =
    .split (coordinate 11) (![⟨264491, by decide⟩,⟨264512, by decide⟩,⟨264529, by decide⟩,⟨264544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5870_264545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5870 ⟨264545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5870
    ⟨264545, by decide⟩ (by decide) (![⟨264491, by decide⟩,⟨264512, by decide⟩,⟨264529, by decide⟩,⟨264544, by decide⟩]) unmarked_context_11_5870_264545 node_context_11_5870_264545
  intro a
  fin_cases a
  · exact context_12_23480_264491
  · exact context_12_23481_264512
  · exact context_12_23482_264529
  · exact context_12_23483_264544

theorem selected_cut_09588 : selected 10 ⟨264612, by decide⟩
    (prefixPartial 11 5871) = some ⟨11, 2, 0, 264612, 5871, 3121, 262144⟩ := by
  decide +kernel

theorem context_11_5871_264612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5871 ⟨264612, by decide⟩ :=
  accepted_of_selected 11 5871 ⟨264612, by decide⟩ ⟨11, 2, 0, 264612, 5871, 3121, 262144⟩
    (by decide) selected_cut_09588

theorem unmarked_context_10_1467_264613 : frontier 11 ⟨264613, by decide⟩
    (prefixCache 10 1467) (prefixPartial 10 1467) = false := by
  decide +kernel

theorem node_context_10_1467_264613 : EJMOriginalGlobalDAGData.nodes 11 ⟨264613, by decide⟩ =
    .split (coordinate 10) (![⟨264383, by decide⟩,⟨264468, by decide⟩,⟨264545, by decide⟩,⟨264612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1467_264613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1467 ⟨264613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1467
    ⟨264613, by decide⟩ (by decide) (![⟨264383, by decide⟩,⟨264468, by decide⟩,⟨264545, by decide⟩,⟨264612, by decide⟩]) unmarked_context_10_1467_264613 node_context_10_1467_264613
  intro a
  fin_cases a
  · exact context_11_5868_264383
  · exact context_11_5869_264468
  · exact context_11_5870_264545
  · exact context_11_5871_264612

theorem unmarked_context_9_366_264614 : frontier 12 ⟨264614, by decide⟩
    (prefixCache 9 366) (prefixPartial 9 366) = false := by
  decide +kernel

theorem node_context_9_366_264614 : EJMOriginalGlobalDAGData.nodes 12 ⟨264614, by decide⟩ =
    .split (coordinate 9) (![⟨263637, by decide⟩,⟨264054, by decide⟩,⟨264324, by decide⟩,⟨264613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_366_264614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 366 ⟨264614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 366
    ⟨264614, by decide⟩ (by decide) (![⟨263637, by decide⟩,⟨264054, by decide⟩,⟨264324, by decide⟩,⟨264613, by decide⟩]) unmarked_context_9_366_264614 node_context_9_366_264614
  intro a
  fin_cases a
  · exact context_10_1464_263637
  · exact context_10_1465_264054
  · exact context_10_1466_264324
  · exact context_10_1467_264613

theorem selected_cut_09589 : selected 10 ⟨264650, by decide⟩
    (prefixPartial 11 5872) = some ⟨11, 2, 0, 264650, 5872, 3013, 262144⟩ := by
  decide +kernel

theorem context_11_5872_264650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5872 ⟨264650, by decide⟩ :=
  accepted_of_selected 11 5872 ⟨264650, by decide⟩ ⟨11, 2, 0, 264650, 5872, 3013, 262144⟩
    (by decide) selected_cut_09589

theorem selected_cut_09590 : selected 10 ⟨264689, by decide⟩
    (prefixPartial 11 5873) = some ⟨11, 2, 0, 264689, 5873, 3073, 262144⟩ := by
  decide +kernel

theorem context_11_5873_264689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5873 ⟨264689, by decide⟩ :=
  accepted_of_selected 11 5873 ⟨264689, by decide⟩ ⟨11, 2, 0, 264689, 5873, 3073, 262144⟩
    (by decide) selected_cut_09590

theorem selected_cut_09591 : selected 10 ⟨264725, by decide⟩
    (prefixPartial 11 5874) = some ⟨11, 2, 0, 264725, 5874, 2773, 262144⟩ := by
  decide +kernel

theorem context_11_5874_264725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5874 ⟨264725, by decide⟩ :=
  accepted_of_selected 11 5874 ⟨264725, by decide⟩ ⟨11, 2, 0, 264725, 5874, 2773, 262144⟩
    (by decide) selected_cut_09591

theorem selected_cut_09592 : selected 10 ⟨264773, by decide⟩
    (prefixPartial 11 5875) = some ⟨11, 2, 0, 264773, 5875, 2953, 262144⟩ := by
  decide +kernel

theorem context_11_5875_264773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5875 ⟨264773, by decide⟩ :=
  accepted_of_selected 11 5875 ⟨264773, by decide⟩ ⟨11, 2, 0, 264773, 5875, 2953, 262144⟩
    (by decide) selected_cut_09592

theorem unmarked_context_10_1468_264774 : frontier 11 ⟨264774, by decide⟩
    (prefixCache 10 1468) (prefixPartial 10 1468) = false := by
  decide +kernel

theorem node_context_10_1468_264774 : EJMOriginalGlobalDAGData.nodes 11 ⟨264774, by decide⟩ =
    .split (coordinate 10) (![⟨264650, by decide⟩,⟨264689, by decide⟩,⟨264725, by decide⟩,⟨264773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1468_264774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1468 ⟨264774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1468
    ⟨264774, by decide⟩ (by decide) (![⟨264650, by decide⟩,⟨264689, by decide⟩,⟨264725, by decide⟩,⟨264773, by decide⟩]) unmarked_context_10_1468_264774 node_context_10_1468_264774
  intro a
  fin_cases a
  · exact context_11_5872_264650
  · exact context_11_5873_264689
  · exact context_11_5874_264725
  · exact context_11_5875_264773

theorem selected_cut_09593 : selected 10 ⟨264811, by decide⟩
    (prefixPartial 11 5876) = some ⟨11, 2, 0, 264811, 5876, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_5876_264811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5876 ⟨264811, by decide⟩ :=
  accepted_of_selected 11 5876 ⟨264811, by decide⟩ ⟨11, 2, 0, 264811, 5876, 2725, 262144⟩
    (by decide) selected_cut_09593

theorem selected_cut_09594 : selected 10 ⟨264844, by decide⟩
    (prefixPartial 11 5877) = some ⟨11, 2, 0, 264844, 5877, 2549, 262144⟩ := by
  decide +kernel

theorem context_11_5877_264844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5877 ⟨264844, by decide⟩ :=
  accepted_of_selected 11 5877 ⟨264844, by decide⟩ ⟨11, 2, 0, 264844, 5877, 2549, 262144⟩
    (by decide) selected_cut_09594

theorem selected_cut_09595 : selected 10 ⟨264876, by decide⟩
    (prefixPartial 11 5878) = some ⟨11, 2, 0, 264876, 5878, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_5878_264876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5878 ⟨264876, by decide⟩ :=
  accepted_of_selected 11 5878 ⟨264876, by decide⟩ ⟨11, 2, 0, 264876, 5878, 2117, 262144⟩
    (by decide) selected_cut_09595

theorem selected_cut_09596 : selected 10 ⟨264922, by decide⟩
    (prefixPartial 11 5879) = some ⟨11, 2, 0, 264922, 5879, 1497, 262144⟩ := by
  decide +kernel

theorem context_11_5879_264922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5879 ⟨264922, by decide⟩ :=
  accepted_of_selected 11 5879 ⟨264922, by decide⟩ ⟨11, 2, 0, 264922, 5879, 1497, 262144⟩
    (by decide) selected_cut_09596

theorem unmarked_context_10_1469_264923 : frontier 11 ⟨264923, by decide⟩
    (prefixCache 10 1469) (prefixPartial 10 1469) = false := by
  decide +kernel

theorem node_context_10_1469_264923 : EJMOriginalGlobalDAGData.nodes 11 ⟨264923, by decide⟩ =
    .split (coordinate 10) (![⟨264811, by decide⟩,⟨264844, by decide⟩,⟨264876, by decide⟩,⟨264922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1469_264923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1469 ⟨264923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1469
    ⟨264923, by decide⟩ (by decide) (![⟨264811, by decide⟩,⟨264844, by decide⟩,⟨264876, by decide⟩,⟨264922, by decide⟩]) unmarked_context_10_1469_264923 node_context_10_1469_264923
  intro a
  fin_cases a
  · exact context_11_5876_264811
  · exact context_11_5877_264844
  · exact context_11_5878_264876
  · exact context_11_5879_264922

theorem selected_cut_09597 : selected 10 ⟨264942, by decide⟩
    (prefixPartial 11 5880) = some ⟨11, 2, 0, 264942, 5880, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_5880_264942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5880 ⟨264942, by decide⟩ :=
  accepted_of_selected 11 5880 ⟨264942, by decide⟩ ⟨11, 2, 0, 264942, 5880, 1549, 262144⟩
    (by decide) selected_cut_09597

theorem selected_cut_09598 : selected 10 ⟨264957, by decide⟩
    (prefixPartial 11 5881) = some ⟨11, 2, 0, 264957, 5881, 1285, 262144⟩ := by
  decide +kernel

theorem context_11_5881_264957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5881 ⟨264957, by decide⟩ :=
  accepted_of_selected 11 5881 ⟨264957, by decide⟩ ⟨11, 2, 0, 264957, 5881, 1285, 262144⟩
    (by decide) selected_cut_09598

theorem selected_cut_09599 : selected 10 ⟨264979, by decide⟩
    (prefixPartial 11 5882) = some ⟨11, 2, 0, 264979, 5882, 961, 262144⟩ := by
  decide +kernel

theorem context_11_5882_264979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5882 ⟨264979, by decide⟩ :=
  accepted_of_selected 11 5882 ⟨264979, by decide⟩ ⟨11, 2, 0, 264979, 5882, 961, 262144⟩
    (by decide) selected_cut_09599

theorem selected_cut_09600 : selected 10 ⟨265000, by decide⟩
    (prefixPartial 11 5883) = some ⟨11, 2, 0, 265000, 5883, 957, 262144⟩ := by
  decide +kernel

theorem context_11_5883_265000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5883 ⟨265000, by decide⟩ :=
  accepted_of_selected 11 5883 ⟨265000, by decide⟩ ⟨11, 2, 0, 265000, 5883, 957, 262144⟩
    (by decide) selected_cut_09600

theorem unmarked_context_10_1470_265001 : frontier 11 ⟨265001, by decide⟩
    (prefixCache 10 1470) (prefixPartial 10 1470) = false := by
  decide +kernel

theorem node_context_10_1470_265001 : EJMOriginalGlobalDAGData.nodes 11 ⟨265001, by decide⟩ =
    .split (coordinate 10) (![⟨264942, by decide⟩,⟨264957, by decide⟩,⟨264979, by decide⟩,⟨265000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1470_265001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1470 ⟨265001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1470
    ⟨265001, by decide⟩ (by decide) (![⟨264942, by decide⟩,⟨264957, by decide⟩,⟨264979, by decide⟩,⟨265000, by decide⟩]) unmarked_context_10_1470_265001 node_context_10_1470_265001
  intro a
  fin_cases a
  · exact context_11_5880_264942
  · exact context_11_5881_264957
  · exact context_11_5882_264979
  · exact context_11_5883_265000

theorem selected_cut_09601 : selected 11 ⟨265054, by decide⟩
    (prefixPartial 10 1471) = some ⟨10, 2, 0, 265054, 1471, 1405, 1048576⟩ := by
  decide +kernel

theorem context_10_1471_265054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1471 ⟨265054, by decide⟩ :=
  accepted_of_selected 10 1471 ⟨265054, by decide⟩ ⟨10, 2, 0, 265054, 1471, 1405, 1048576⟩
    (by decide) selected_cut_09601

theorem unmarked_context_9_367_265055 : frontier 12 ⟨265055, by decide⟩
    (prefixCache 9 367) (prefixPartial 9 367) = false := by
  decide +kernel

theorem node_context_9_367_265055 : EJMOriginalGlobalDAGData.nodes 12 ⟨265055, by decide⟩ =
    .split (coordinate 9) (![⟨264774, by decide⟩,⟨264923, by decide⟩,⟨265001, by decide⟩,⟨265054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_367_265055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 367 ⟨265055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 367
    ⟨265055, by decide⟩ (by decide) (![⟨264774, by decide⟩,⟨264923, by decide⟩,⟨265001, by decide⟩,⟨265054, by decide⟩]) unmarked_context_9_367_265055 node_context_9_367_265055
  intro a
  fin_cases a
  · exact context_10_1468_264774
  · exact context_10_1469_264923
  · exact context_10_1470_265001
  · exact context_10_1471_265054

theorem unmarked_context_8_91_265056 : frontier 13 ⟨265056, by decide⟩
    (prefixCache 8 91) (prefixPartial 8 91) = false := by
  decide +kernel

theorem node_context_8_91_265056 : EJMOriginalGlobalDAGData.nodes 13 ⟨265056, by decide⟩ =
    .split (coordinate 8) (![⟨257786, by decide⟩,⟨263122, by decide⟩,⟨264614, by decide⟩,⟨265055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_91_265056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 91 ⟨265056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 91
    ⟨265056, by decide⟩ (by decide) (![⟨257786, by decide⟩,⟨263122, by decide⟩,⟨264614, by decide⟩,⟨265055, by decide⟩]) unmarked_context_8_91_265056 node_context_8_91_265056
  intro a
  fin_cases a
  · exact context_9_364_257786
  · exact context_9_365_263122
  · exact context_9_366_264614
  · exact context_9_367_265055

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
