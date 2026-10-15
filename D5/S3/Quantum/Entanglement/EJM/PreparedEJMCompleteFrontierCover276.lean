/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover275
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26499 : selected 8 ⟨670521, by decide⟩
    (prefixPartial 13 355473) = some ⟨13, 2, 0, 670521, 355473, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_355473_670521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355473 ⟨670521, by decide⟩ :=
  accepted_of_selected 13 355473 ⟨670521, by decide⟩ ⟨13, 2, 0, 670521, 355473, 2513, 16384⟩
    (by decide) selected_cut_26499

theorem selected_cut_26500 : selected 8 ⟨670538, by decide⟩
    (prefixPartial 13 355474) = some ⟨13, 2, 0, 670538, 355474, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_355474_670538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355474 ⟨670538, by decide⟩ :=
  accepted_of_selected 13 355474 ⟨670538, by decide⟩ ⟨13, 2, 0, 670538, 355474, 1197, 16384⟩
    (by decide) selected_cut_26500

theorem selected_cut_26501 : selected 8 ⟨670545, by decide⟩
    (prefixPartial 13 355475) = some ⟨13, 2, 0, 670545, 355475, 853, 16384⟩ := by
  decide +kernel

theorem context_13_355475_670545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355475 ⟨670545, by decide⟩ :=
  accepted_of_selected 13 355475 ⟨670545, by decide⟩ ⟨13, 2, 0, 670545, 355475, 853, 16384⟩
    (by decide) selected_cut_26501

theorem unmarked_context_12_88868_670546 : frontier 9 ⟨670546, by decide⟩
    (prefixCache 12 88868) (prefixPartial 12 88868) = false := by
  decide +kernel

theorem node_context_12_88868_670546 : EJMOriginalGlobalDAGData.nodes 9 ⟨670546, by decide⟩ =
    .split (coordinate 12) (![⟨670472, by decide⟩,⟨670521, by decide⟩,⟨670538, by decide⟩,⟨670545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88868_670546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88868 ⟨670546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88868
    ⟨670546, by decide⟩ (by decide) (![⟨670472, by decide⟩,⟨670521, by decide⟩,⟨670538, by decide⟩,⟨670545, by decide⟩]) unmarked_context_12_88868_670546 node_context_12_88868_670546
  intro a
  fin_cases a
  · exact context_13_355472_670472
  · exact context_13_355473_670521
  · exact context_13_355474_670538
  · exact context_13_355475_670545

theorem selected_cut_26502 : selected 8 ⟨670559, by decide⟩
    (prefixPartial 13 355476) = some ⟨13, 2, 0, 670559, 355476, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_355476_670559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355476 ⟨670559, by decide⟩ :=
  accepted_of_selected 13 355476 ⟨670559, by decide⟩ ⟨13, 2, 0, 670559, 355476, 1073, 16384⟩
    (by decide) selected_cut_26502

theorem selected_cut_26503 : selected 8 ⟨670583, by decide⟩
    (prefixPartial 13 355477) = some ⟨13, 2, 0, 670583, 355477, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_355477_670583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355477 ⟨670583, by decide⟩ :=
  accepted_of_selected 13 355477 ⟨670583, by decide⟩ ⟨13, 2, 0, 670583, 355477, 1789, 16384⟩
    (by decide) selected_cut_26503

theorem selected_cut_26504 : selected 8 ⟨670598, by decide⟩
    (prefixPartial 13 355478) = some ⟨13, 2, 0, 670598, 355478, 989, 16384⟩ := by
  decide +kernel

theorem context_13_355478_670598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355478 ⟨670598, by decide⟩ :=
  accepted_of_selected 13 355478 ⟨670598, by decide⟩ ⟨13, 2, 0, 670598, 355478, 989, 16384⟩
    (by decide) selected_cut_26504

theorem selected_cut_26505 : selected 8 ⟨670604, by decide⟩
    (prefixPartial 13 355479) = some ⟨13, 2, 0, 670604, 355479, 717, 16384⟩ := by
  decide +kernel

theorem context_13_355479_670604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355479 ⟨670604, by decide⟩ :=
  accepted_of_selected 13 355479 ⟨670604, by decide⟩ ⟨13, 2, 0, 670604, 355479, 717, 16384⟩
    (by decide) selected_cut_26505

theorem unmarked_context_12_88869_670605 : frontier 9 ⟨670605, by decide⟩
    (prefixCache 12 88869) (prefixPartial 12 88869) = false := by
  decide +kernel

theorem node_context_12_88869_670605 : EJMOriginalGlobalDAGData.nodes 9 ⟨670605, by decide⟩ =
    .split (coordinate 12) (![⟨670559, by decide⟩,⟨670583, by decide⟩,⟨670598, by decide⟩,⟨670604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88869_670605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88869 ⟨670605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88869
    ⟨670605, by decide⟩ (by decide) (![⟨670559, by decide⟩,⟨670583, by decide⟩,⟨670598, by decide⟩,⟨670604, by decide⟩]) unmarked_context_12_88869_670605 node_context_12_88869_670605
  intro a
  fin_cases a
  · exact context_13_355476_670559
  · exact context_13_355477_670583
  · exact context_13_355478_670598
  · exact context_13_355479_670604

theorem selected_cut_26506 : selected 8 ⟨670625, by decide⟩
    (prefixPartial 13 355480) = some ⟨13, 2, 0, 670625, 355480, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_355480_670625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355480 ⟨670625, by decide⟩ :=
  accepted_of_selected 13 355480 ⟨670625, by decide⟩ ⟨13, 2, 0, 670625, 355480, 1233, 16384⟩
    (by decide) selected_cut_26506

theorem selected_cut_26507 : selected 8 ⟨670664, by decide⟩
    (prefixPartial 13 355481) = some ⟨13, 2, 0, 670664, 355481, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_355481_670664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355481 ⟨670664, by decide⟩ :=
  accepted_of_selected 13 355481 ⟨670664, by decide⟩ ⟨13, 2, 0, 670664, 355481, 2481, 16384⟩
    (by decide) selected_cut_26507

theorem selected_cut_26508 : selected 8 ⟨670679, by decide⟩
    (prefixPartial 13 355482) = some ⟨13, 2, 0, 670679, 355482, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_355482_670679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355482 ⟨670679, by decide⟩ :=
  accepted_of_selected 13 355482 ⟨670679, by decide⟩ ⟨13, 2, 0, 670679, 355482, 1437, 16384⟩
    (by decide) selected_cut_26508

theorem selected_cut_26509 : selected 8 ⟨670686, by decide⟩
    (prefixPartial 13 355483) = some ⟨13, 2, 0, 670686, 355483, 825, 16384⟩ := by
  decide +kernel

theorem context_13_355483_670686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355483 ⟨670686, by decide⟩ :=
  accepted_of_selected 13 355483 ⟨670686, by decide⟩ ⟨13, 2, 0, 670686, 355483, 825, 16384⟩
    (by decide) selected_cut_26509

theorem unmarked_context_12_88870_670687 : frontier 9 ⟨670687, by decide⟩
    (prefixCache 12 88870) (prefixPartial 12 88870) = false := by
  decide +kernel

theorem node_context_12_88870_670687 : EJMOriginalGlobalDAGData.nodes 9 ⟨670687, by decide⟩ =
    .split (coordinate 12) (![⟨670625, by decide⟩,⟨670664, by decide⟩,⟨670679, by decide⟩,⟨670686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88870_670687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88870 ⟨670687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88870
    ⟨670687, by decide⟩ (by decide) (![⟨670625, by decide⟩,⟨670664, by decide⟩,⟨670679, by decide⟩,⟨670686, by decide⟩]) unmarked_context_12_88870_670687 node_context_12_88870_670687
  intro a
  fin_cases a
  · exact context_13_355480_670625
  · exact context_13_355481_670664
  · exact context_13_355482_670679
  · exact context_13_355483_670686

theorem selected_cut_26510 : selected 8 ⟨670700, by decide⟩
    (prefixPartial 13 355484) = some ⟨13, 2, 0, 670700, 355484, 977, 16384⟩ := by
  decide +kernel

theorem context_13_355484_670700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355484 ⟨670700, by decide⟩ :=
  accepted_of_selected 13 355484 ⟨670700, by decide⟩ ⟨13, 2, 0, 670700, 355484, 977, 16384⟩
    (by decide) selected_cut_26510

theorem selected_cut_26511 : selected 8 ⟨670731, by decide⟩
    (prefixPartial 13 355485) = some ⟨13, 2, 0, 670731, 355485, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_355485_670731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355485 ⟨670731, by decide⟩ :=
  accepted_of_selected 13 355485 ⟨670731, by decide⟩ ⟨13, 2, 0, 670731, 355485, 2081, 16384⟩
    (by decide) selected_cut_26511

theorem selected_cut_26512 : selected 8 ⟨670747, by decide⟩
    (prefixPartial 13 355486) = some ⟨13, 2, 0, 670747, 355486, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_355486_670747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355486 ⟨670747, by decide⟩ :=
  accepted_of_selected 13 355486 ⟨670747, by decide⟩ ⟨13, 2, 0, 670747, 355486, 1129, 16384⟩
    (by decide) selected_cut_26512

theorem selected_cut_26513 : selected 8 ⟨670751, by decide⟩
    (prefixPartial 13 355487) = some ⟨13, 2, 0, 670751, 355487, 725, 16384⟩ := by
  decide +kernel

theorem context_13_355487_670751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355487 ⟨670751, by decide⟩ :=
  accepted_of_selected 13 355487 ⟨670751, by decide⟩ ⟨13, 2, 0, 670751, 355487, 725, 16384⟩
    (by decide) selected_cut_26513

theorem unmarked_context_12_88871_670752 : frontier 9 ⟨670752, by decide⟩
    (prefixCache 12 88871) (prefixPartial 12 88871) = false := by
  decide +kernel

theorem node_context_12_88871_670752 : EJMOriginalGlobalDAGData.nodes 9 ⟨670752, by decide⟩ =
    .split (coordinate 12) (![⟨670700, by decide⟩,⟨670731, by decide⟩,⟨670747, by decide⟩,⟨670751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88871_670752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88871 ⟨670752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88871
    ⟨670752, by decide⟩ (by decide) (![⟨670700, by decide⟩,⟨670731, by decide⟩,⟨670747, by decide⟩,⟨670751, by decide⟩]) unmarked_context_12_88871_670752 node_context_12_88871_670752
  intro a
  fin_cases a
  · exact context_13_355484_670700
  · exact context_13_355485_670731
  · exact context_13_355486_670747
  · exact context_13_355487_670751

theorem unmarked_context_11_22217_670753 : frontier 10 ⟨670753, by decide⟩
    (prefixCache 11 22217) (prefixPartial 11 22217) = false := by
  decide +kernel

theorem node_context_11_22217_670753 : EJMOriginalGlobalDAGData.nodes 10 ⟨670753, by decide⟩ =
    .split (coordinate 11) (![⟨670546, by decide⟩,⟨670605, by decide⟩,⟨670687, by decide⟩,⟨670752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22217_670753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22217 ⟨670753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22217
    ⟨670753, by decide⟩ (by decide) (![⟨670546, by decide⟩,⟨670605, by decide⟩,⟨670687, by decide⟩,⟨670752, by decide⟩]) unmarked_context_11_22217_670753 node_context_11_22217_670753
  intro a
  fin_cases a
  · exact context_12_88868_670546
  · exact context_12_88869_670605
  · exact context_12_88870_670687
  · exact context_12_88871_670752

theorem selected_cut_26514 : selected 8 ⟨670794, by decide⟩
    (prefixPartial 13 355488) = some ⟨13, 2, 0, 670794, 355488, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_355488_670794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355488 ⟨670794, by decide⟩ :=
  accepted_of_selected 13 355488 ⟨670794, by decide⟩ ⟨13, 2, 0, 670794, 355488, 1009, 16384⟩
    (by decide) selected_cut_26514

theorem selected_cut_26515 : selected 8 ⟨670926, by decide⟩
    (prefixPartial 13 355489) = some ⟨13, 2, 0, 670926, 355489, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_355489_670926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355489 ⟨670926, by decide⟩ :=
  accepted_of_selected 13 355489 ⟨670926, by decide⟩ ⟨13, 2, 0, 670926, 355489, 2533, 16384⟩
    (by decide) selected_cut_26515

theorem selected_cut_26516 : selected 8 ⟨670992, by decide⟩
    (prefixPartial 13 355490) = some ⟨13, 2, 0, 670992, 355490, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_355490_670992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355490 ⟨670992, by decide⟩ :=
  accepted_of_selected 13 355490 ⟨670992, by decide⟩ ⟨13, 2, 0, 670992, 355490, 1637, 16384⟩
    (by decide) selected_cut_26516

theorem selected_cut_26517 : selected 8 ⟨671030, by decide⟩
    (prefixPartial 13 355491) = some ⟨13, 2, 0, 671030, 355491, 893, 16384⟩ := by
  decide +kernel

theorem context_13_355491_671030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355491 ⟨671030, by decide⟩ :=
  accepted_of_selected 13 355491 ⟨671030, by decide⟩ ⟨13, 2, 0, 671030, 355491, 893, 16384⟩
    (by decide) selected_cut_26517

theorem unmarked_context_12_88872_671031 : frontier 9 ⟨671031, by decide⟩
    (prefixCache 12 88872) (prefixPartial 12 88872) = false := by
  decide +kernel

theorem node_context_12_88872_671031 : EJMOriginalGlobalDAGData.nodes 9 ⟨671031, by decide⟩ =
    .split (coordinate 12) (![⟨670794, by decide⟩,⟨670926, by decide⟩,⟨670992, by decide⟩,⟨671030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88872_671031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88872 ⟨671031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88872
    ⟨671031, by decide⟩ (by decide) (![⟨670794, by decide⟩,⟨670926, by decide⟩,⟨670992, by decide⟩,⟨671030, by decide⟩]) unmarked_context_12_88872_671031 node_context_12_88872_671031
  intro a
  fin_cases a
  · exact context_13_355488_670794
  · exact context_13_355489_670926
  · exact context_13_355490_670992
  · exact context_13_355491_671030

theorem selected_cut_26518 : selected 8 ⟨671052, by decide⟩
    (prefixPartial 13 355492) = some ⟨13, 2, 0, 671052, 355492, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_355492_671052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355492 ⟨671052, by decide⟩ :=
  accepted_of_selected 13 355492 ⟨671052, by decide⟩ ⟨13, 2, 0, 671052, 355492, 1345, 16384⟩
    (by decide) selected_cut_26518

theorem selected_cut_26519 : selected 8 ⟨671103, by decide⟩
    (prefixPartial 13 355493) = some ⟨13, 2, 0, 671103, 355493, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_355493_671103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355493 ⟨671103, by decide⟩ :=
  accepted_of_selected 13 355493 ⟨671103, by decide⟩ ⟨13, 2, 0, 671103, 355493, 2385, 16384⟩
    (by decide) selected_cut_26519

theorem selected_cut_26520 : selected 8 ⟨671122, by decide⟩
    (prefixPartial 13 355494) = some ⟨13, 2, 0, 671122, 355494, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_355494_671122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355494 ⟨671122, by decide⟩ :=
  accepted_of_selected 13 355494 ⟨671122, by decide⟩ ⟨13, 2, 0, 671122, 355494, 1869, 16384⟩
    (by decide) selected_cut_26520

theorem selected_cut_26521 : selected 8 ⟨671131, by decide⟩
    (prefixPartial 13 355495) = some ⟨13, 2, 0, 671131, 355495, 925, 16384⟩ := by
  decide +kernel

theorem context_13_355495_671131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355495 ⟨671131, by decide⟩ :=
  accepted_of_selected 13 355495 ⟨671131, by decide⟩ ⟨13, 2, 0, 671131, 355495, 925, 16384⟩
    (by decide) selected_cut_26521

theorem unmarked_context_12_88873_671132 : frontier 9 ⟨671132, by decide⟩
    (prefixCache 12 88873) (prefixPartial 12 88873) = false := by
  decide +kernel

theorem node_context_12_88873_671132 : EJMOriginalGlobalDAGData.nodes 9 ⟨671132, by decide⟩ =
    .split (coordinate 12) (![⟨671052, by decide⟩,⟨671103, by decide⟩,⟨671122, by decide⟩,⟨671131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88873_671132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88873 ⟨671132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88873
    ⟨671132, by decide⟩ (by decide) (![⟨671052, by decide⟩,⟨671103, by decide⟩,⟨671122, by decide⟩,⟨671131, by decide⟩]) unmarked_context_12_88873_671132 node_context_12_88873_671132
  intro a
  fin_cases a
  · exact context_13_355492_671052
  · exact context_13_355493_671103
  · exact context_13_355494_671122
  · exact context_13_355495_671131

theorem selected_cut_26522 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 88874) = some ⟨12, 1, 0, 224365, 88874, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88874_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88874 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 88874 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 88874, 1, 65536⟩
    (by decide) selected_cut_26522

theorem selected_cut_26523 : selected 8 ⟨671156, by decide⟩
    (prefixPartial 13 355500) = some ⟨13, 2, 0, 671156, 355500, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_355500_671156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355500 ⟨671156, by decide⟩ :=
  accepted_of_selected 13 355500 ⟨671156, by decide⟩ ⟨13, 2, 0, 671156, 355500, 1189, 16384⟩
    (by decide) selected_cut_26523

theorem selected_cut_26524 : selected 8 ⟨671220, by decide⟩
    (prefixPartial 13 355501) = some ⟨13, 2, 0, 671220, 355501, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_355501_671220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355501 ⟨671220, by decide⟩ :=
  accepted_of_selected 13 355501 ⟨671220, by decide⟩ ⟨13, 2, 0, 671220, 355501, 3005, 16384⟩
    (by decide) selected_cut_26524

theorem selected_cut_26525 : selected 8 ⟨671239, by decide⟩
    (prefixPartial 13 355502) = some ⟨13, 2, 0, 671239, 355502, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_355502_671239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355502 ⟨671239, by decide⟩ :=
  accepted_of_selected 13 355502 ⟨671239, by decide⟩ ⟨13, 2, 0, 671239, 355502, 1929, 16384⟩
    (by decide) selected_cut_26525

theorem selected_cut_26526 : selected 8 ⟨671248, by decide⟩
    (prefixPartial 13 355503) = some ⟨13, 2, 0, 671248, 355503, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_355503_671248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355503 ⟨671248, by decide⟩ :=
  accepted_of_selected 13 355503 ⟨671248, by decide⟩ ⟨13, 2, 0, 671248, 355503, 1001, 16384⟩
    (by decide) selected_cut_26526

theorem unmarked_context_12_88875_671249 : frontier 9 ⟨671249, by decide⟩
    (prefixCache 12 88875) (prefixPartial 12 88875) = false := by
  decide +kernel

theorem node_context_12_88875_671249 : EJMOriginalGlobalDAGData.nodes 9 ⟨671249, by decide⟩ =
    .split (coordinate 12) (![⟨671156, by decide⟩,⟨671220, by decide⟩,⟨671239, by decide⟩,⟨671248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88875_671249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88875 ⟨671249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88875
    ⟨671249, by decide⟩ (by decide) (![⟨671156, by decide⟩,⟨671220, by decide⟩,⟨671239, by decide⟩,⟨671248, by decide⟩]) unmarked_context_12_88875_671249 node_context_12_88875_671249
  intro a
  fin_cases a
  · exact context_13_355500_671156
  · exact context_13_355501_671220
  · exact context_13_355502_671239
  · exact context_13_355503_671248

theorem unmarked_context_11_22218_671250 : frontier 10 ⟨671250, by decide⟩
    (prefixCache 11 22218) (prefixPartial 11 22218) = false := by
  decide +kernel

theorem node_context_11_22218_671250 : EJMOriginalGlobalDAGData.nodes 10 ⟨671250, by decide⟩ =
    .split (coordinate 11) (![⟨671031, by decide⟩,⟨671132, by decide⟩,⟨224365, by decide⟩,⟨671249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22218_671250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22218 ⟨671250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22218
    ⟨671250, by decide⟩ (by decide) (![⟨671031, by decide⟩,⟨671132, by decide⟩,⟨224365, by decide⟩,⟨671249, by decide⟩]) unmarked_context_11_22218_671250 node_context_11_22218_671250
  intro a
  fin_cases a
  · exact context_12_88872_671031
  · exact context_12_88873_671132
  · exact context_12_88874_224365
  · exact context_12_88875_671249

theorem selected_cut_26527 : selected 8 ⟨671264, by decide⟩
    (prefixPartial 13 355504) = some ⟨13, 2, 0, 671264, 355504, 861, 16384⟩ := by
  decide +kernel

theorem context_13_355504_671264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355504 ⟨671264, by decide⟩ :=
  accepted_of_selected 13 355504 ⟨671264, by decide⟩ ⟨13, 2, 0, 671264, 355504, 861, 16384⟩
    (by decide) selected_cut_26527

theorem selected_cut_26528 : selected 8 ⟨671296, by decide⟩
    (prefixPartial 13 355505) = some ⟨13, 2, 0, 671296, 355505, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_355505_671296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355505 ⟨671296, by decide⟩ :=
  accepted_of_selected 13 355505 ⟨671296, by decide⟩ ⟨13, 2, 0, 671296, 355505, 1949, 16384⟩
    (by decide) selected_cut_26528

theorem selected_cut_26529 : selected 8 ⟨671311, by decide⟩
    (prefixPartial 13 355506) = some ⟨13, 2, 0, 671311, 355506, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_355506_671311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355506 ⟨671311, by decide⟩ :=
  accepted_of_selected 13 355506 ⟨671311, by decide⟩ ⟨13, 2, 0, 671311, 355506, 1429, 16384⟩
    (by decide) selected_cut_26529

theorem selected_cut_26530 : selected 8 ⟨671319, by decide⟩
    (prefixPartial 13 355507) = some ⟨13, 2, 0, 671319, 355507, 861, 16384⟩ := by
  decide +kernel

theorem context_13_355507_671319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355507 ⟨671319, by decide⟩ :=
  accepted_of_selected 13 355507 ⟨671319, by decide⟩ ⟨13, 2, 0, 671319, 355507, 861, 16384⟩
    (by decide) selected_cut_26530

theorem unmarked_context_12_88876_671320 : frontier 9 ⟨671320, by decide⟩
    (prefixCache 12 88876) (prefixPartial 12 88876) = false := by
  decide +kernel

theorem node_context_12_88876_671320 : EJMOriginalGlobalDAGData.nodes 9 ⟨671320, by decide⟩ =
    .split (coordinate 12) (![⟨671264, by decide⟩,⟨671296, by decide⟩,⟨671311, by decide⟩,⟨671319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88876_671320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88876 ⟨671320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88876
    ⟨671320, by decide⟩ (by decide) (![⟨671264, by decide⟩,⟨671296, by decide⟩,⟨671311, by decide⟩,⟨671319, by decide⟩]) unmarked_context_12_88876_671320 node_context_12_88876_671320
  intro a
  fin_cases a
  · exact context_13_355504_671264
  · exact context_13_355505_671296
  · exact context_13_355506_671311
  · exact context_13_355507_671319

theorem selected_cut_26531 : selected 8 ⟨671330, by decide⟩
    (prefixPartial 13 355508) = some ⟨13, 2, 0, 671330, 355508, 721, 16384⟩ := by
  decide +kernel

theorem context_13_355508_671330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355508 ⟨671330, by decide⟩ :=
  accepted_of_selected 13 355508 ⟨671330, by decide⟩ ⟨13, 2, 0, 671330, 355508, 721, 16384⟩
    (by decide) selected_cut_26531

theorem selected_cut_26532 : selected 8 ⟨671351, by decide⟩
    (prefixPartial 13 355509) = some ⟨13, 2, 0, 671351, 355509, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_355509_671351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355509 ⟨671351, by decide⟩ :=
  accepted_of_selected 13 355509 ⟨671351, by decide⟩ ⟨13, 2, 0, 671351, 355509, 1509, 16384⟩
    (by decide) selected_cut_26532

theorem selected_cut_26533 : selected 8 ⟨671365, by decide⟩
    (prefixPartial 13 355510) = some ⟨13, 2, 0, 671365, 355510, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_355510_671365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355510 ⟨671365, by decide⟩ :=
  accepted_of_selected 13 355510 ⟨671365, by decide⟩ ⟨13, 2, 0, 671365, 355510, 1501, 16384⟩
    (by decide) selected_cut_26533

theorem selected_cut_26534 : selected 8 ⟨671371, by decide⟩
    (prefixPartial 13 355511) = some ⟨13, 2, 0, 671371, 355511, 737, 16384⟩ := by
  decide +kernel

theorem context_13_355511_671371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355511 ⟨671371, by decide⟩ :=
  accepted_of_selected 13 355511 ⟨671371, by decide⟩ ⟨13, 2, 0, 671371, 355511, 737, 16384⟩
    (by decide) selected_cut_26534

theorem unmarked_context_12_88877_671372 : frontier 9 ⟨671372, by decide⟩
    (prefixCache 12 88877) (prefixPartial 12 88877) = false := by
  decide +kernel

theorem node_context_12_88877_671372 : EJMOriginalGlobalDAGData.nodes 9 ⟨671372, by decide⟩ =
    .split (coordinate 12) (![⟨671330, by decide⟩,⟨671351, by decide⟩,⟨671365, by decide⟩,⟨671371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88877_671372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88877 ⟨671372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88877
    ⟨671372, by decide⟩ (by decide) (![⟨671330, by decide⟩,⟨671351, by decide⟩,⟨671365, by decide⟩,⟨671371, by decide⟩]) unmarked_context_12_88877_671372 node_context_12_88877_671372
  intro a
  fin_cases a
  · exact context_13_355508_671330
  · exact context_13_355509_671351
  · exact context_13_355510_671365
  · exact context_13_355511_671371

theorem selected_cut_26535 : selected 8 ⟨671384, by decide⟩
    (prefixPartial 13 355512) = some ⟨13, 2, 0, 671384, 355512, 853, 16384⟩ := by
  decide +kernel

theorem context_13_355512_671384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355512 ⟨671384, by decide⟩ :=
  accepted_of_selected 13 355512 ⟨671384, by decide⟩ ⟨13, 2, 0, 671384, 355512, 853, 16384⟩
    (by decide) selected_cut_26535

theorem selected_cut_26536 : selected 8 ⟨671425, by decide⟩
    (prefixPartial 13 355513) = some ⟨13, 2, 0, 671425, 355513, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_355513_671425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355513 ⟨671425, by decide⟩ :=
  accepted_of_selected 13 355513 ⟨671425, by decide⟩ ⟨13, 2, 0, 671425, 355513, 2381, 16384⟩
    (by decide) selected_cut_26536

theorem selected_cut_26537 : selected 8 ⟨671441, by decide⟩
    (prefixPartial 13 355514) = some ⟨13, 2, 0, 671441, 355514, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_355514_671441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355514 ⟨671441, by decide⟩ :=
  accepted_of_selected 13 355514 ⟨671441, by decide⟩ ⟨13, 2, 0, 671441, 355514, 1649, 16384⟩
    (by decide) selected_cut_26537

theorem selected_cut_26538 : selected 8 ⟨671447, by decide⟩
    (prefixPartial 13 355515) = some ⟨13, 2, 0, 671447, 355515, 797, 16384⟩ := by
  decide +kernel

theorem context_13_355515_671447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355515 ⟨671447, by decide⟩ :=
  accepted_of_selected 13 355515 ⟨671447, by decide⟩ ⟨13, 2, 0, 671447, 355515, 797, 16384⟩
    (by decide) selected_cut_26538

theorem unmarked_context_12_88878_671448 : frontier 9 ⟨671448, by decide⟩
    (prefixCache 12 88878) (prefixPartial 12 88878) = false := by
  decide +kernel

theorem node_context_12_88878_671448 : EJMOriginalGlobalDAGData.nodes 9 ⟨671448, by decide⟩ =
    .split (coordinate 12) (![⟨671384, by decide⟩,⟨671425, by decide⟩,⟨671441, by decide⟩,⟨671447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88878_671448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88878 ⟨671448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88878
    ⟨671448, by decide⟩ (by decide) (![⟨671384, by decide⟩,⟨671425, by decide⟩,⟨671441, by decide⟩,⟨671447, by decide⟩]) unmarked_context_12_88878_671448 node_context_12_88878_671448
  intro a
  fin_cases a
  · exact context_13_355512_671384
  · exact context_13_355513_671425
  · exact context_13_355514_671441
  · exact context_13_355515_671447

theorem selected_cut_26539 : selected 8 ⟨671464, by decide⟩
    (prefixPartial 13 355516) = some ⟨13, 2, 0, 671464, 355516, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_355516_671464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355516 ⟨671464, by decide⟩ :=
  accepted_of_selected 13 355516 ⟨671464, by decide⟩ ⟨13, 2, 0, 671464, 355516, 1021, 16384⟩
    (by decide) selected_cut_26539

theorem selected_cut_26540 : selected 8 ⟨671526, by decide⟩
    (prefixPartial 13 355517) = some ⟨13, 2, 0, 671526, 355517, 3173, 16384⟩ := by
  decide +kernel

theorem context_13_355517_671526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355517 ⟨671526, by decide⟩ :=
  accepted_of_selected 13 355517 ⟨671526, by decide⟩ ⟨13, 2, 0, 671526, 355517, 3173, 16384⟩
    (by decide) selected_cut_26540

theorem selected_cut_26541 : selected 8 ⟨671560, by decide⟩
    (prefixPartial 13 355518) = some ⟨13, 2, 0, 671560, 355518, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_355518_671560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355518 ⟨671560, by decide⟩ :=
  accepted_of_selected 13 355518 ⟨671560, by decide⟩ ⟨13, 2, 0, 671560, 355518, 2453, 16384⟩
    (by decide) selected_cut_26541

theorem selected_cut_26542 : selected 8 ⟨671568, by decide⟩
    (prefixPartial 13 355519) = some ⟨13, 2, 0, 671568, 355519, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_355519_671568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355519 ⟨671568, by decide⟩ :=
  accepted_of_selected 13 355519 ⟨671568, by decide⟩ ⟨13, 2, 0, 671568, 355519, 1105, 16384⟩
    (by decide) selected_cut_26542

theorem unmarked_context_12_88879_671569 : frontier 9 ⟨671569, by decide⟩
    (prefixCache 12 88879) (prefixPartial 12 88879) = false := by
  decide +kernel

theorem node_context_12_88879_671569 : EJMOriginalGlobalDAGData.nodes 9 ⟨671569, by decide⟩ =
    .split (coordinate 12) (![⟨671464, by decide⟩,⟨671526, by decide⟩,⟨671560, by decide⟩,⟨671568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88879_671569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88879 ⟨671569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88879
    ⟨671569, by decide⟩ (by decide) (![⟨671464, by decide⟩,⟨671526, by decide⟩,⟨671560, by decide⟩,⟨671568, by decide⟩]) unmarked_context_12_88879_671569 node_context_12_88879_671569
  intro a
  fin_cases a
  · exact context_13_355516_671464
  · exact context_13_355517_671526
  · exact context_13_355518_671560
  · exact context_13_355519_671568

theorem unmarked_context_11_22219_671570 : frontier 10 ⟨671570, by decide⟩
    (prefixCache 11 22219) (prefixPartial 11 22219) = false := by
  decide +kernel

theorem node_context_11_22219_671570 : EJMOriginalGlobalDAGData.nodes 10 ⟨671570, by decide⟩ =
    .split (coordinate 11) (![⟨671320, by decide⟩,⟨671372, by decide⟩,⟨671448, by decide⟩,⟨671569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22219_671570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22219 ⟨671570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22219
    ⟨671570, by decide⟩ (by decide) (![⟨671320, by decide⟩,⟨671372, by decide⟩,⟨671448, by decide⟩,⟨671569, by decide⟩]) unmarked_context_11_22219_671570 node_context_11_22219_671570
  intro a
  fin_cases a
  · exact context_12_88876_671320
  · exact context_12_88877_671372
  · exact context_12_88878_671448
  · exact context_12_88879_671569

theorem unmarked_context_10_5554_671571 : frontier 11 ⟨671571, by decide⟩
    (prefixCache 10 5554) (prefixPartial 10 5554) = false := by
  decide +kernel

theorem node_context_10_5554_671571 : EJMOriginalGlobalDAGData.nodes 11 ⟨671571, by decide⟩ =
    .split (coordinate 10) (![⟨670459, by decide⟩,⟨670753, by decide⟩,⟨671250, by decide⟩,⟨671570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5554_671571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5554 ⟨671571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5554
    ⟨671571, by decide⟩ (by decide) (![⟨670459, by decide⟩,⟨670753, by decide⟩,⟨671250, by decide⟩,⟨671570, by decide⟩]) unmarked_context_10_5554_671571 node_context_10_5554_671571
  intro a
  fin_cases a
  · exact context_11_22216_670459
  · exact context_11_22217_670753
  · exact context_11_22218_671250
  · exact context_11_22219_671570

theorem selected_cut_26543 : selected 8 ⟨671577, by decide⟩
    (prefixPartial 13 355520) = some ⟨13, 2, 0, 671577, 355520, 581, 16384⟩ := by
  decide +kernel

theorem context_13_355520_671577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355520 ⟨671577, by decide⟩ :=
  accepted_of_selected 13 355520 ⟨671577, by decide⟩ ⟨13, 2, 0, 671577, 355520, 581, 16384⟩
    (by decide) selected_cut_26543

theorem selected_cut_26544 : selected 8 ⟨671602, by decide⟩
    (prefixPartial 13 355521) = some ⟨13, 2, 0, 671602, 355521, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_355521_671602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355521 ⟨671602, by decide⟩ :=
  accepted_of_selected 13 355521 ⟨671602, by decide⟩ ⟨13, 2, 0, 671602, 355521, 1665, 16384⟩
    (by decide) selected_cut_26544

theorem selected_cut_26545 : selected 8 ⟨671621, by decide⟩
    (prefixPartial 13 355522) = some ⟨13, 2, 0, 671621, 355522, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_355522_671621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355522 ⟨671621, by decide⟩ :=
  accepted_of_selected 13 355522 ⟨671621, by decide⟩ ⟨13, 2, 0, 671621, 355522, 1397, 16384⟩
    (by decide) selected_cut_26545

theorem selected_cut_26546 : selected 8 ⟨671627, by decide⟩
    (prefixPartial 13 355523) = some ⟨13, 2, 0, 671627, 355523, 793, 16384⟩ := by
  decide +kernel

theorem context_13_355523_671627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355523 ⟨671627, by decide⟩ :=
  accepted_of_selected 13 355523 ⟨671627, by decide⟩ ⟨13, 2, 0, 671627, 355523, 793, 16384⟩
    (by decide) selected_cut_26546

theorem unmarked_context_12_88880_671628 : frontier 9 ⟨671628, by decide⟩
    (prefixCache 12 88880) (prefixPartial 12 88880) = false := by
  decide +kernel

theorem node_context_12_88880_671628 : EJMOriginalGlobalDAGData.nodes 9 ⟨671628, by decide⟩ =
    .split (coordinate 12) (![⟨671577, by decide⟩,⟨671602, by decide⟩,⟨671621, by decide⟩,⟨671627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88880_671628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88880 ⟨671628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88880
    ⟨671628, by decide⟩ (by decide) (![⟨671577, by decide⟩,⟨671602, by decide⟩,⟨671621, by decide⟩,⟨671627, by decide⟩]) unmarked_context_12_88880_671628 node_context_12_88880_671628
  intro a
  fin_cases a
  · exact context_13_355520_671577
  · exact context_13_355521_671602
  · exact context_13_355522_671621
  · exact context_13_355523_671627

theorem selected_cut_26547 : selected 8 ⟨671637, by decide⟩
    (prefixPartial 13 355524) = some ⟨13, 2, 0, 671637, 355524, 581, 16384⟩ := by
  decide +kernel

theorem context_13_355524_671637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355524 ⟨671637, by decide⟩ :=
  accepted_of_selected 13 355524 ⟨671637, by decide⟩ ⟨13, 2, 0, 671637, 355524, 581, 16384⟩
    (by decide) selected_cut_26547

theorem selected_cut_26548 : selected 8 ⟨671674, by decide⟩
    (prefixPartial 13 355525) = some ⟨13, 2, 0, 671674, 355525, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_355525_671674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355525 ⟨671674, by decide⟩ :=
  accepted_of_selected 13 355525 ⟨671674, by decide⟩ ⟨13, 2, 0, 671674, 355525, 1909, 16384⟩
    (by decide) selected_cut_26548

theorem selected_cut_26549 : selected 8 ⟨671689, by decide⟩
    (prefixPartial 13 355526) = some ⟨13, 2, 0, 671689, 355526, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_355526_671689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355526 ⟨671689, by decide⟩ :=
  accepted_of_selected 13 355526 ⟨671689, by decide⟩ ⟨13, 2, 0, 671689, 355526, 1361, 16384⟩
    (by decide) selected_cut_26549

theorem selected_cut_26550 : selected 8 ⟨671693, by decide⟩
    (prefixPartial 13 355527) = some ⟨13, 2, 0, 671693, 355527, 753, 16384⟩ := by
  decide +kernel

theorem context_13_355527_671693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355527 ⟨671693, by decide⟩ :=
  accepted_of_selected 13 355527 ⟨671693, by decide⟩ ⟨13, 2, 0, 671693, 355527, 753, 16384⟩
    (by decide) selected_cut_26550

theorem unmarked_context_12_88881_671694 : frontier 9 ⟨671694, by decide⟩
    (prefixCache 12 88881) (prefixPartial 12 88881) = false := by
  decide +kernel

theorem node_context_12_88881_671694 : EJMOriginalGlobalDAGData.nodes 9 ⟨671694, by decide⟩ =
    .split (coordinate 12) (![⟨671637, by decide⟩,⟨671674, by decide⟩,⟨671689, by decide⟩,⟨671693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88881_671694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88881 ⟨671694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88881
    ⟨671694, by decide⟩ (by decide) (![⟨671637, by decide⟩,⟨671674, by decide⟩,⟨671689, by decide⟩,⟨671693, by decide⟩]) unmarked_context_12_88881_671694 node_context_12_88881_671694
  intro a
  fin_cases a
  · exact context_13_355524_671637
  · exact context_13_355525_671674
  · exact context_13_355526_671689
  · exact context_13_355527_671693

theorem selected_cut_26551 : selected 8 ⟨671704, by decide⟩
    (prefixPartial 13 355528) = some ⟨13, 2, 0, 671704, 355528, 605, 16384⟩ := by
  decide +kernel

theorem context_13_355528_671704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355528 ⟨671704, by decide⟩ :=
  accepted_of_selected 13 355528 ⟨671704, by decide⟩ ⟨13, 2, 0, 671704, 355528, 605, 16384⟩
    (by decide) selected_cut_26551

theorem selected_cut_26552 : selected 8 ⟨671734, by decide⟩
    (prefixPartial 13 355529) = some ⟨13, 2, 0, 671734, 355529, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_355529_671734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355529 ⟨671734, by decide⟩ :=
  accepted_of_selected 13 355529 ⟨671734, by decide⟩ ⟨13, 2, 0, 671734, 355529, 2205, 16384⟩
    (by decide) selected_cut_26552

theorem selected_cut_26553 : selected 8 ⟨671761, by decide⟩
    (prefixPartial 13 355530) = some ⟨13, 2, 0, 671761, 355530, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_355530_671761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355530 ⟨671761, by decide⟩ :=
  accepted_of_selected 13 355530 ⟨671761, by decide⟩ ⟨13, 2, 0, 671761, 355530, 1721, 16384⟩
    (by decide) selected_cut_26553

theorem selected_cut_26554 : selected 8 ⟨671765, by decide⟩
    (prefixPartial 13 355531) = some ⟨13, 2, 0, 671765, 355531, 781, 16384⟩ := by
  decide +kernel

theorem context_13_355531_671765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355531 ⟨671765, by decide⟩ :=
  accepted_of_selected 13 355531 ⟨671765, by decide⟩ ⟨13, 2, 0, 671765, 355531, 781, 16384⟩
    (by decide) selected_cut_26554

theorem unmarked_context_12_88882_671766 : frontier 9 ⟨671766, by decide⟩
    (prefixCache 12 88882) (prefixPartial 12 88882) = false := by
  decide +kernel

theorem node_context_12_88882_671766 : EJMOriginalGlobalDAGData.nodes 9 ⟨671766, by decide⟩ =
    .split (coordinate 12) (![⟨671704, by decide⟩,⟨671734, by decide⟩,⟨671761, by decide⟩,⟨671765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88882_671766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88882 ⟨671766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88882
    ⟨671766, by decide⟩ (by decide) (![⟨671704, by decide⟩,⟨671734, by decide⟩,⟨671761, by decide⟩,⟨671765, by decide⟩]) unmarked_context_12_88882_671766 node_context_12_88882_671766
  intro a
  fin_cases a
  · exact context_13_355528_671704
  · exact context_13_355529_671734
  · exact context_13_355530_671761
  · exact context_13_355531_671765

theorem selected_cut_26555 : selected 8 ⟨671772, by decide⟩
    (prefixPartial 13 355532) = some ⟨13, 2, 0, 671772, 355532, 521, 16384⟩ := by
  decide +kernel

theorem context_13_355532_671772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355532 ⟨671772, by decide⟩ :=
  accepted_of_selected 13 355532 ⟨671772, by decide⟩ ⟨13, 2, 0, 671772, 355532, 521, 16384⟩
    (by decide) selected_cut_26555

theorem selected_cut_26556 : selected 8 ⟨671797, by decide⟩
    (prefixPartial 13 355533) = some ⟨13, 2, 0, 671797, 355533, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_355533_671797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355533 ⟨671797, by decide⟩ :=
  accepted_of_selected 13 355533 ⟨671797, by decide⟩ ⟨13, 2, 0, 671797, 355533, 1949, 16384⟩
    (by decide) selected_cut_26556

theorem selected_cut_26557 : selected 8 ⟨671814, by decide⟩
    (prefixPartial 13 355534) = some ⟨13, 2, 0, 671814, 355534, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_355534_671814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355534 ⟨671814, by decide⟩ :=
  accepted_of_selected 13 355534 ⟨671814, by decide⟩ ⟨13, 2, 0, 671814, 355534, 1525, 16384⟩
    (by decide) selected_cut_26557

theorem selected_cut_26558 : selected 8 ⟨671817, by decide⟩
    (prefixPartial 13 355535) = some ⟨13, 2, 0, 671817, 355535, 745, 16384⟩ := by
  decide +kernel

theorem context_13_355535_671817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355535 ⟨671817, by decide⟩ :=
  accepted_of_selected 13 355535 ⟨671817, by decide⟩ ⟨13, 2, 0, 671817, 355535, 745, 16384⟩
    (by decide) selected_cut_26558

theorem unmarked_context_12_88883_671818 : frontier 9 ⟨671818, by decide⟩
    (prefixCache 12 88883) (prefixPartial 12 88883) = false := by
  decide +kernel

theorem node_context_12_88883_671818 : EJMOriginalGlobalDAGData.nodes 9 ⟨671818, by decide⟩ =
    .split (coordinate 12) (![⟨671772, by decide⟩,⟨671797, by decide⟩,⟨671814, by decide⟩,⟨671817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88883_671818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88883 ⟨671818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88883
    ⟨671818, by decide⟩ (by decide) (![⟨671772, by decide⟩,⟨671797, by decide⟩,⟨671814, by decide⟩,⟨671817, by decide⟩]) unmarked_context_12_88883_671818 node_context_12_88883_671818
  intro a
  fin_cases a
  · exact context_13_355532_671772
  · exact context_13_355533_671797
  · exact context_13_355534_671814
  · exact context_13_355535_671817

theorem unmarked_context_11_22220_671819 : frontier 10 ⟨671819, by decide⟩
    (prefixCache 11 22220) (prefixPartial 11 22220) = false := by
  decide +kernel

theorem node_context_11_22220_671819 : EJMOriginalGlobalDAGData.nodes 10 ⟨671819, by decide⟩ =
    .split (coordinate 11) (![⟨671628, by decide⟩,⟨671694, by decide⟩,⟨671766, by decide⟩,⟨671818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22220_671819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22220 ⟨671819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22220
    ⟨671819, by decide⟩ (by decide) (![⟨671628, by decide⟩,⟨671694, by decide⟩,⟨671766, by decide⟩,⟨671818, by decide⟩]) unmarked_context_11_22220_671819 node_context_11_22220_671819
  intro a
  fin_cases a
  · exact context_12_88880_671628
  · exact context_12_88881_671694
  · exact context_12_88882_671766
  · exact context_12_88883_671818

theorem selected_cut_26559 : selected 8 ⟨671823, by decide⟩
    (prefixPartial 13 355536) = some ⟨13, 2, 0, 671823, 355536, 405, 16384⟩ := by
  decide +kernel

theorem context_13_355536_671823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355536 ⟨671823, by decide⟩ :=
  accepted_of_selected 13 355536 ⟨671823, by decide⟩ ⟨13, 2, 0, 671823, 355536, 405, 16384⟩
    (by decide) selected_cut_26559

theorem selected_cut_26560 : selected 8 ⟨671858, by decide⟩
    (prefixPartial 13 355537) = some ⟨13, 2, 0, 671858, 355537, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_355537_671858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355537 ⟨671858, by decide⟩ :=
  accepted_of_selected 13 355537 ⟨671858, by decide⟩ ⟨13, 2, 0, 671858, 355537, 2141, 16384⟩
    (by decide) selected_cut_26560

theorem selected_cut_26561 : selected 8 ⟨671872, by decide⟩
    (prefixPartial 13 355538) = some ⟨13, 2, 0, 671872, 355538, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_355538_671872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355538 ⟨671872, by decide⟩ :=
  accepted_of_selected 13 355538 ⟨671872, by decide⟩ ⟨13, 2, 0, 671872, 355538, 1381, 16384⟩
    (by decide) selected_cut_26561

theorem selected_cut_26562 : selected 8 ⟨671878, by decide⟩
    (prefixPartial 13 355539) = some ⟨13, 2, 0, 671878, 355539, 845, 16384⟩ := by
  decide +kernel

theorem context_13_355539_671878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355539 ⟨671878, by decide⟩ :=
  accepted_of_selected 13 355539 ⟨671878, by decide⟩ ⟨13, 2, 0, 671878, 355539, 845, 16384⟩
    (by decide) selected_cut_26562

theorem unmarked_context_12_88884_671879 : frontier 9 ⟨671879, by decide⟩
    (prefixCache 12 88884) (prefixPartial 12 88884) = false := by
  decide +kernel

theorem node_context_12_88884_671879 : EJMOriginalGlobalDAGData.nodes 9 ⟨671879, by decide⟩ =
    .split (coordinate 12) (![⟨671823, by decide⟩,⟨671858, by decide⟩,⟨671872, by decide⟩,⟨671878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88884_671879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88884 ⟨671879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88884
    ⟨671879, by decide⟩ (by decide) (![⟨671823, by decide⟩,⟨671858, by decide⟩,⟨671872, by decide⟩,⟨671878, by decide⟩]) unmarked_context_12_88884_671879 node_context_12_88884_671879
  intro a
  fin_cases a
  · exact context_13_355536_671823
  · exact context_13_355537_671858
  · exact context_13_355538_671872
  · exact context_13_355539_671878

theorem selected_cut_26563 : selected 8 ⟨671884, by decide⟩
    (prefixPartial 13 355540) = some ⟨13, 2, 0, 671884, 355540, 389, 16384⟩ := by
  decide +kernel

theorem context_13_355540_671884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355540 ⟨671884, by decide⟩ :=
  accepted_of_selected 13 355540 ⟨671884, by decide⟩ ⟨13, 2, 0, 671884, 355540, 389, 16384⟩
    (by decide) selected_cut_26563

theorem selected_cut_26564 : selected 8 ⟨671917, by decide⟩
    (prefixPartial 13 355541) = some ⟨13, 2, 0, 671917, 355541, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_355541_671917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355541 ⟨671917, by decide⟩ :=
  accepted_of_selected 13 355541 ⟨671917, by decide⟩ ⟨13, 2, 0, 671917, 355541, 1857, 16384⟩
    (by decide) selected_cut_26564

theorem selected_cut_26565 : selected 8 ⟨671930, by decide⟩
    (prefixPartial 13 355542) = some ⟨13, 2, 0, 671930, 355542, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_355542_671930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355542 ⟨671930, by decide⟩ :=
  accepted_of_selected 13 355542 ⟨671930, by decide⟩ ⟨13, 2, 0, 671930, 355542, 1117, 16384⟩
    (by decide) selected_cut_26565

theorem selected_cut_26566 : selected 8 ⟨671935, by decide⟩
    (prefixPartial 13 355543) = some ⟨13, 2, 0, 671935, 355543, 801, 16384⟩ := by
  decide +kernel

theorem context_13_355543_671935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355543 ⟨671935, by decide⟩ :=
  accepted_of_selected 13 355543 ⟨671935, by decide⟩ ⟨13, 2, 0, 671935, 355543, 801, 16384⟩
    (by decide) selected_cut_26566

theorem unmarked_context_12_88885_671936 : frontier 9 ⟨671936, by decide⟩
    (prefixCache 12 88885) (prefixPartial 12 88885) = false := by
  decide +kernel

theorem node_context_12_88885_671936 : EJMOriginalGlobalDAGData.nodes 9 ⟨671936, by decide⟩ =
    .split (coordinate 12) (![⟨671884, by decide⟩,⟨671917, by decide⟩,⟨671930, by decide⟩,⟨671935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88885_671936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88885 ⟨671936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88885
    ⟨671936, by decide⟩ (by decide) (![⟨671884, by decide⟩,⟨671917, by decide⟩,⟨671930, by decide⟩,⟨671935, by decide⟩]) unmarked_context_12_88885_671936 node_context_12_88885_671936
  intro a
  fin_cases a
  · exact context_13_355540_671884
  · exact context_13_355541_671917
  · exact context_13_355542_671930
  · exact context_13_355543_671935

theorem selected_cut_26567 : selected 8 ⟨671942, by decide⟩
    (prefixPartial 13 355544) = some ⟨13, 2, 0, 671942, 355544, 389, 16384⟩ := by
  decide +kernel

theorem context_13_355544_671942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355544 ⟨671942, by decide⟩ :=
  accepted_of_selected 13 355544 ⟨671942, by decide⟩ ⟨13, 2, 0, 671942, 355544, 389, 16384⟩
    (by decide) selected_cut_26567

theorem selected_cut_26568 : selected 8 ⟨671982, by decide⟩
    (prefixPartial 13 355545) = some ⟨13, 2, 0, 671982, 355545, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_355545_671982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355545 ⟨671982, by decide⟩ :=
  accepted_of_selected 13 355545 ⟨671982, by decide⟩ ⟨13, 2, 0, 671982, 355545, 2225, 16384⟩
    (by decide) selected_cut_26568

theorem selected_cut_26569 : selected 8 ⟨672000, by decide⟩
    (prefixPartial 13 355546) = some ⟨13, 2, 0, 672000, 355546, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_355546_672000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355546 ⟨672000, by decide⟩ :=
  accepted_of_selected 13 355546 ⟨672000, by decide⟩ ⟨13, 2, 0, 672000, 355546, 1509, 16384⟩
    (by decide) selected_cut_26569

theorem selected_cut_26570 : selected 8 ⟨672010, by decide⟩
    (prefixPartial 13 355547) = some ⟨13, 2, 0, 672010, 355547, 837, 16384⟩ := by
  decide +kernel

theorem context_13_355547_672010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355547 ⟨672010, by decide⟩ :=
  accepted_of_selected 13 355547 ⟨672010, by decide⟩ ⟨13, 2, 0, 672010, 355547, 837, 16384⟩
    (by decide) selected_cut_26570

theorem unmarked_context_12_88886_672011 : frontier 9 ⟨672011, by decide⟩
    (prefixCache 12 88886) (prefixPartial 12 88886) = false := by
  decide +kernel

theorem node_context_12_88886_672011 : EJMOriginalGlobalDAGData.nodes 9 ⟨672011, by decide⟩ =
    .split (coordinate 12) (![⟨671942, by decide⟩,⟨671982, by decide⟩,⟨672000, by decide⟩,⟨672010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88886_672011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88886 ⟨672011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88886
    ⟨672011, by decide⟩ (by decide) (![⟨671942, by decide⟩,⟨671982, by decide⟩,⟨672000, by decide⟩,⟨672010, by decide⟩]) unmarked_context_12_88886_672011 node_context_12_88886_672011
  intro a
  fin_cases a
  · exact context_13_355544_671942
  · exact context_13_355545_671982
  · exact context_13_355546_672000
  · exact context_13_355547_672010

theorem selected_cut_26571 : selected 8 ⟨672016, by decide⟩
    (prefixPartial 13 355548) = some ⟨13, 2, 0, 672016, 355548, 305, 16384⟩ := by
  decide +kernel

theorem context_13_355548_672016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355548 ⟨672016, by decide⟩ :=
  accepted_of_selected 13 355548 ⟨672016, by decide⟩ ⟨13, 2, 0, 672016, 355548, 305, 16384⟩
    (by decide) selected_cut_26571

theorem selected_cut_26572 : selected 8 ⟨672046, by decide⟩
    (prefixPartial 13 355549) = some ⟨13, 2, 0, 672046, 355549, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_355549_672046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355549 ⟨672046, by decide⟩ :=
  accepted_of_selected 13 355549 ⟨672046, by decide⟩ ⟨13, 2, 0, 672046, 355549, 1949, 16384⟩
    (by decide) selected_cut_26572

theorem selected_cut_26573 : selected 8 ⟨672059, by decide⟩
    (prefixPartial 13 355550) = some ⟨13, 2, 0, 672059, 355550, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_355550_672059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355550 ⟨672059, by decide⟩ :=
  accepted_of_selected 13 355550 ⟨672059, by decide⟩ ⟨13, 2, 0, 672059, 355550, 1293, 16384⟩
    (by decide) selected_cut_26573

theorem selected_cut_26574 : selected 8 ⟨672063, by decide⟩
    (prefixPartial 13 355551) = some ⟨13, 2, 0, 672063, 355551, 781, 16384⟩ := by
  decide +kernel

theorem context_13_355551_672063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355551 ⟨672063, by decide⟩ :=
  accepted_of_selected 13 355551 ⟨672063, by decide⟩ ⟨13, 2, 0, 672063, 355551, 781, 16384⟩
    (by decide) selected_cut_26574

theorem unmarked_context_12_88887_672064 : frontier 9 ⟨672064, by decide⟩
    (prefixCache 12 88887) (prefixPartial 12 88887) = false := by
  decide +kernel

theorem node_context_12_88887_672064 : EJMOriginalGlobalDAGData.nodes 9 ⟨672064, by decide⟩ =
    .split (coordinate 12) (![⟨672016, by decide⟩,⟨672046, by decide⟩,⟨672059, by decide⟩,⟨672063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88887_672064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88887 ⟨672064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88887
    ⟨672064, by decide⟩ (by decide) (![⟨672016, by decide⟩,⟨672046, by decide⟩,⟨672059, by decide⟩,⟨672063, by decide⟩]) unmarked_context_12_88887_672064 node_context_12_88887_672064
  intro a
  fin_cases a
  · exact context_13_355548_672016
  · exact context_13_355549_672046
  · exact context_13_355550_672059
  · exact context_13_355551_672063

theorem unmarked_context_11_22221_672065 : frontier 10 ⟨672065, by decide⟩
    (prefixCache 11 22221) (prefixPartial 11 22221) = false := by
  decide +kernel

theorem node_context_11_22221_672065 : EJMOriginalGlobalDAGData.nodes 10 ⟨672065, by decide⟩ =
    .split (coordinate 11) (![⟨671879, by decide⟩,⟨671936, by decide⟩,⟨672011, by decide⟩,⟨672064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22221_672065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22221 ⟨672065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22221
    ⟨672065, by decide⟩ (by decide) (![⟨671879, by decide⟩,⟨671936, by decide⟩,⟨672011, by decide⟩,⟨672064, by decide⟩]) unmarked_context_11_22221_672065 node_context_11_22221_672065
  intro a
  fin_cases a
  · exact context_12_88884_671879
  · exact context_12_88885_671936
  · exact context_12_88886_672011
  · exact context_12_88887_672064

theorem selected_cut_26575 : selected 8 ⟨672069, by decide⟩
    (prefixPartial 13 355552) = some ⟨13, 2, 0, 672069, 355552, 241, 16384⟩ := by
  decide +kernel

theorem context_13_355552_672069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355552 ⟨672069, by decide⟩ :=
  accepted_of_selected 13 355552 ⟨672069, by decide⟩ ⟨13, 2, 0, 672069, 355552, 241, 16384⟩
    (by decide) selected_cut_26575

theorem selected_cut_26576 : selected 8 ⟨672099, by decide⟩
    (prefixPartial 13 355553) = some ⟨13, 2, 0, 672099, 355553, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_355553_672099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355553 ⟨672099, by decide⟩ :=
  accepted_of_selected 13 355553 ⟨672099, by decide⟩ ⟨13, 2, 0, 672099, 355553, 2097, 16384⟩
    (by decide) selected_cut_26576

theorem selected_cut_26577 : selected 8 ⟨672127, by decide⟩
    (prefixPartial 13 355554) = some ⟨13, 2, 0, 672127, 355554, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_355554_672127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355554 ⟨672127, by decide⟩ :=
  accepted_of_selected 13 355554 ⟨672127, by decide⟩ ⟨13, 2, 0, 672127, 355554, 1769, 16384⟩
    (by decide) selected_cut_26577

theorem selected_cut_26578 : selected 8 ⟨672134, by decide⟩
    (prefixPartial 13 355555) = some ⟨13, 2, 0, 672134, 355555, 825, 16384⟩ := by
  decide +kernel

theorem context_13_355555_672134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355555 ⟨672134, by decide⟩ :=
  accepted_of_selected 13 355555 ⟨672134, by decide⟩ ⟨13, 2, 0, 672134, 355555, 825, 16384⟩
    (by decide) selected_cut_26578

theorem unmarked_context_12_88888_672135 : frontier 9 ⟨672135, by decide⟩
    (prefixCache 12 88888) (prefixPartial 12 88888) = false := by
  decide +kernel

theorem node_context_12_88888_672135 : EJMOriginalGlobalDAGData.nodes 9 ⟨672135, by decide⟩ =
    .split (coordinate 12) (![⟨672069, by decide⟩,⟨672099, by decide⟩,⟨672127, by decide⟩,⟨672134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88888_672135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88888 ⟨672135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88888
    ⟨672135, by decide⟩ (by decide) (![⟨672069, by decide⟩,⟨672099, by decide⟩,⟨672127, by decide⟩,⟨672134, by decide⟩]) unmarked_context_12_88888_672135 node_context_12_88888_672135
  intro a
  fin_cases a
  · exact context_13_355552_672069
  · exact context_13_355553_672099
  · exact context_13_355554_672127
  · exact context_13_355555_672134

theorem selected_cut_26579 : selected 8 ⟨672139, by decide⟩
    (prefixPartial 13 355556) = some ⟨13, 2, 0, 672139, 355556, 233, 16384⟩ := by
  decide +kernel

theorem context_13_355556_672139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355556 ⟨672139, by decide⟩ :=
  accepted_of_selected 13 355556 ⟨672139, by decide⟩ ⟨13, 2, 0, 672139, 355556, 233, 16384⟩
    (by decide) selected_cut_26579

theorem selected_cut_26580 : selected 8 ⟨672165, by decide⟩
    (prefixPartial 13 355557) = some ⟨13, 2, 0, 672165, 355557, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_355557_672165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355557 ⟨672165, by decide⟩ :=
  accepted_of_selected 13 355557 ⟨672165, by decide⟩ ⟨13, 2, 0, 672165, 355557, 1789, 16384⟩
    (by decide) selected_cut_26580

theorem selected_cut_26581 : selected 8 ⟨672183, by decide⟩
    (prefixPartial 13 355558) = some ⟨13, 2, 0, 672183, 355558, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_355558_672183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355558 ⟨672183, by decide⟩ :=
  accepted_of_selected 13 355558 ⟨672183, by decide⟩ ⟨13, 2, 0, 672183, 355558, 1541, 16384⟩
    (by decide) selected_cut_26581

theorem selected_cut_26582 : selected 8 ⟨672191, by decide⟩
    (prefixPartial 13 355559) = some ⟨13, 2, 0, 672191, 355559, 801, 16384⟩ := by
  decide +kernel

theorem context_13_355559_672191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355559 ⟨672191, by decide⟩ :=
  accepted_of_selected 13 355559 ⟨672191, by decide⟩ ⟨13, 2, 0, 672191, 355559, 801, 16384⟩
    (by decide) selected_cut_26582

theorem unmarked_context_12_88889_672192 : frontier 9 ⟨672192, by decide⟩
    (prefixCache 12 88889) (prefixPartial 12 88889) = false := by
  decide +kernel

theorem node_context_12_88889_672192 : EJMOriginalGlobalDAGData.nodes 9 ⟨672192, by decide⟩ =
    .split (coordinate 12) (![⟨672139, by decide⟩,⟨672165, by decide⟩,⟨672183, by decide⟩,⟨672191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88889_672192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88889 ⟨672192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88889
    ⟨672192, by decide⟩ (by decide) (![⟨672139, by decide⟩,⟨672165, by decide⟩,⟨672183, by decide⟩,⟨672191, by decide⟩]) unmarked_context_12_88889_672192 node_context_12_88889_672192
  intro a
  fin_cases a
  · exact context_13_355556_672139
  · exact context_13_355557_672165
  · exact context_13_355558_672183
  · exact context_13_355559_672191

theorem selected_cut_26583 : selected 8 ⟨672196, by decide⟩
    (prefixPartial 13 355560) = some ⟨13, 2, 0, 672196, 355560, 201, 16384⟩ := by
  decide +kernel

theorem context_13_355560_672196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355560 ⟨672196, by decide⟩ :=
  accepted_of_selected 13 355560 ⟨672196, by decide⟩ ⟨13, 2, 0, 672196, 355560, 201, 16384⟩
    (by decide) selected_cut_26583

theorem selected_cut_26584 : selected 8 ⟨672231, by decide⟩
    (prefixPartial 13 355561) = some ⟨13, 2, 0, 672231, 355561, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_355561_672231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355561 ⟨672231, by decide⟩ :=
  accepted_of_selected 13 355561 ⟨672231, by decide⟩ ⟨13, 2, 0, 672231, 355561, 2357, 16384⟩
    (by decide) selected_cut_26584

theorem selected_cut_26585 : selected 8 ⟨672262, by decide⟩
    (prefixPartial 13 355562) = some ⟨13, 2, 0, 672262, 355562, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_355562_672262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355562 ⟨672262, by decide⟩ :=
  accepted_of_selected 13 355562 ⟨672262, by decide⟩ ⟨13, 2, 0, 672262, 355562, 1901, 16384⟩
    (by decide) selected_cut_26585

theorem selected_cut_26586 : selected 8 ⟨672269, by decide⟩
    (prefixPartial 13 355563) = some ⟨13, 2, 0, 672269, 355563, 837, 16384⟩ := by
  decide +kernel

theorem context_13_355563_672269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355563 ⟨672269, by decide⟩ :=
  accepted_of_selected 13 355563 ⟨672269, by decide⟩ ⟨13, 2, 0, 672269, 355563, 837, 16384⟩
    (by decide) selected_cut_26586

theorem unmarked_context_12_88890_672270 : frontier 9 ⟨672270, by decide⟩
    (prefixCache 12 88890) (prefixPartial 12 88890) = false := by
  decide +kernel

theorem node_context_12_88890_672270 : EJMOriginalGlobalDAGData.nodes 9 ⟨672270, by decide⟩ =
    .split (coordinate 12) (![⟨672196, by decide⟩,⟨672231, by decide⟩,⟨672262, by decide⟩,⟨672269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88890_672270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88890 ⟨672270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88890
    ⟨672270, by decide⟩ (by decide) (![⟨672196, by decide⟩,⟨672231, by decide⟩,⟨672262, by decide⟩,⟨672269, by decide⟩]) unmarked_context_12_88890_672270 node_context_12_88890_672270
  intro a
  fin_cases a
  · exact context_13_355560_672196
  · exact context_13_355561_672231
  · exact context_13_355562_672262
  · exact context_13_355563_672269

theorem selected_cut_26587 : selected 8 ⟨672274, by decide⟩
    (prefixPartial 13 355564) = some ⟨13, 2, 0, 672274, 355564, 153, 16384⟩ := by
  decide +kernel

theorem context_13_355564_672274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355564 ⟨672274, by decide⟩ :=
  accepted_of_selected 13 355564 ⟨672274, by decide⟩ ⟨13, 2, 0, 672274, 355564, 153, 16384⟩
    (by decide) selected_cut_26587

theorem selected_cut_26588 : selected 8 ⟨672303, by decide⟩
    (prefixPartial 13 355565) = some ⟨13, 2, 0, 672303, 355565, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_355565_672303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355565 ⟨672303, by decide⟩ :=
  accepted_of_selected 13 355565 ⟨672303, by decide⟩ ⟨13, 2, 0, 672303, 355565, 2261, 16384⟩
    (by decide) selected_cut_26588

theorem selected_cut_26589 : selected 8 ⟨672322, by decide⟩
    (prefixPartial 13 355566) = some ⟨13, 2, 0, 672322, 355566, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_355566_672322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355566 ⟨672322, by decide⟩ :=
  accepted_of_selected 13 355566 ⟨672322, by decide⟩ ⟨13, 2, 0, 672322, 355566, 1761, 16384⟩
    (by decide) selected_cut_26589

theorem selected_cut_26590 : selected 8 ⟨672326, by decide⟩
    (prefixPartial 13 355567) = some ⟨13, 2, 0, 672326, 355567, 853, 16384⟩ := by
  decide +kernel

theorem context_13_355567_672326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355567 ⟨672326, by decide⟩ :=
  accepted_of_selected 13 355567 ⟨672326, by decide⟩ ⟨13, 2, 0, 672326, 355567, 853, 16384⟩
    (by decide) selected_cut_26590

theorem unmarked_context_12_88891_672327 : frontier 9 ⟨672327, by decide⟩
    (prefixCache 12 88891) (prefixPartial 12 88891) = false := by
  decide +kernel

theorem node_context_12_88891_672327 : EJMOriginalGlobalDAGData.nodes 9 ⟨672327, by decide⟩ =
    .split (coordinate 12) (![⟨672274, by decide⟩,⟨672303, by decide⟩,⟨672322, by decide⟩,⟨672326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88891_672327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88891 ⟨672327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88891
    ⟨672327, by decide⟩ (by decide) (![⟨672274, by decide⟩,⟨672303, by decide⟩,⟨672322, by decide⟩,⟨672326, by decide⟩]) unmarked_context_12_88891_672327 node_context_12_88891_672327
  intro a
  fin_cases a
  · exact context_13_355564_672274
  · exact context_13_355565_672303
  · exact context_13_355566_672322
  · exact context_13_355567_672326

theorem unmarked_context_11_22222_672328 : frontier 10 ⟨672328, by decide⟩
    (prefixCache 11 22222) (prefixPartial 11 22222) = false := by
  decide +kernel

theorem node_context_11_22222_672328 : EJMOriginalGlobalDAGData.nodes 10 ⟨672328, by decide⟩ =
    .split (coordinate 11) (![⟨672135, by decide⟩,⟨672192, by decide⟩,⟨672270, by decide⟩,⟨672327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22222_672328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22222 ⟨672328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22222
    ⟨672328, by decide⟩ (by decide) (![⟨672135, by decide⟩,⟨672192, by decide⟩,⟨672270, by decide⟩,⟨672327, by decide⟩]) unmarked_context_11_22222_672328 node_context_11_22222_672328
  intro a
  fin_cases a
  · exact context_12_88888_672135
  · exact context_12_88889_672192
  · exact context_12_88890_672270
  · exact context_12_88891_672327

theorem selected_cut_26591 : selected 8 ⟨672331, by decide⟩
    (prefixPartial 13 355568) = some ⟨13, 2, 0, 672331, 355568, 105, 16384⟩ := by
  decide +kernel

theorem context_13_355568_672331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355568 ⟨672331, by decide⟩ :=
  accepted_of_selected 13 355568 ⟨672331, by decide⟩ ⟨13, 2, 0, 672331, 355568, 105, 16384⟩
    (by decide) selected_cut_26591

theorem selected_cut_26592 : selected 8 ⟨672352, by decide⟩
    (prefixPartial 13 355569) = some ⟨13, 2, 0, 672352, 355569, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_355569_672352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355569 ⟨672352, by decide⟩ :=
  accepted_of_selected 13 355569 ⟨672352, by decide⟩ ⟨13, 2, 0, 672352, 355569, 1781, 16384⟩
    (by decide) selected_cut_26592

theorem selected_cut_26593 : selected 8 ⟨672371, by decide⟩
    (prefixPartial 13 355570) = some ⟨13, 2, 0, 672371, 355570, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_355570_672371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355570 ⟨672371, by decide⟩ :=
  accepted_of_selected 13 355570 ⟨672371, by decide⟩ ⟨13, 2, 0, 672371, 355570, 1553, 16384⟩
    (by decide) selected_cut_26593

theorem selected_cut_26594 : selected 8 ⟨672377, by decide⟩
    (prefixPartial 13 355571) = some ⟨13, 2, 0, 672377, 355571, 849, 16384⟩ := by
  decide +kernel

theorem context_13_355571_672377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355571 ⟨672377, by decide⟩ :=
  accepted_of_selected 13 355571 ⟨672377, by decide⟩ ⟨13, 2, 0, 672377, 355571, 849, 16384⟩
    (by decide) selected_cut_26594

theorem unmarked_context_12_88892_672378 : frontier 9 ⟨672378, by decide⟩
    (prefixCache 12 88892) (prefixPartial 12 88892) = false := by
  decide +kernel

theorem node_context_12_88892_672378 : EJMOriginalGlobalDAGData.nodes 9 ⟨672378, by decide⟩ =
    .split (coordinate 12) (![⟨672331, by decide⟩,⟨672352, by decide⟩,⟨672371, by decide⟩,⟨672377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88892_672378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88892 ⟨672378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88892
    ⟨672378, by decide⟩ (by decide) (![⟨672331, by decide⟩,⟨672352, by decide⟩,⟨672371, by decide⟩,⟨672377, by decide⟩]) unmarked_context_12_88892_672378 node_context_12_88892_672378
  intro a
  fin_cases a
  · exact context_13_355568_672331
  · exact context_13_355569_672352
  · exact context_13_355570_672371
  · exact context_13_355571_672377

theorem selected_cut_26595 : selected 9 ⟨672428, by decide⟩
    (prefixPartial 12 88893) = some ⟨12, 2, 0, 672428, 88893, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_88893_672428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88893 ⟨672428, by decide⟩ :=
  accepted_of_selected 12 88893 ⟨672428, by decide⟩ ⟨12, 2, 0, 672428, 88893, 4053, 65536⟩
    (by decide) selected_cut_26595

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
