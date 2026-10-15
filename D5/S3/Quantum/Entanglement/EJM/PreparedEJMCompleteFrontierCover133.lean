/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover132
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12770 : selected 8 ⟨337078, by decide⟩
    (prefixPartial 13 105536) = some ⟨13, 2, 0, 337078, 105536, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_105536_337078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105536 ⟨337078, by decide⟩ :=
  accepted_of_selected 13 105536 ⟨337078, by decide⟩ ⟨13, 2, 0, 337078, 105536, 1589, 16384⟩
    (by decide) selected_cut_12770

theorem selected_cut_12771 : selected 8 ⟨337098, by decide⟩
    (prefixPartial 13 105537) = some ⟨13, 2, 0, 337098, 105537, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_105537_337098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105537 ⟨337098, by decide⟩ :=
  accepted_of_selected 13 105537 ⟨337098, by decide⟩ ⟨13, 2, 0, 337098, 105537, 1501, 16384⟩
    (by decide) selected_cut_12771

theorem selected_cut_12772 : selected 8 ⟨337115, by decide⟩
    (prefixPartial 13 105538) = some ⟨13, 2, 0, 337115, 105538, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_105538_337115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105538 ⟨337115, by decide⟩ :=
  accepted_of_selected 13 105538 ⟨337115, by decide⟩ ⟨13, 2, 0, 337115, 105538, 1181, 16384⟩
    (by decide) selected_cut_12772

theorem selected_cut_12773 : selected 8 ⟨337123, by decide⟩
    (prefixPartial 13 105539) = some ⟨13, 2, 0, 337123, 105539, 689, 16384⟩ := by
  decide +kernel

theorem context_13_105539_337123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105539 ⟨337123, by decide⟩ :=
  accepted_of_selected 13 105539 ⟨337123, by decide⟩ ⟨13, 2, 0, 337123, 105539, 689, 16384⟩
    (by decide) selected_cut_12773

theorem unmarked_context_12_26384_337124 : frontier 9 ⟨337124, by decide⟩
    (prefixCache 12 26384) (prefixPartial 12 26384) = false := by
  decide +kernel

theorem node_context_12_26384_337124 : EJMOriginalGlobalDAGData.nodes 9 ⟨337124, by decide⟩ =
    .split (coordinate 12) (![⟨337078, by decide⟩,⟨337098, by decide⟩,⟨337115, by decide⟩,⟨337123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26384_337124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26384 ⟨337124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26384
    ⟨337124, by decide⟩ (by decide) (![⟨337078, by decide⟩,⟨337098, by decide⟩,⟨337115, by decide⟩,⟨337123, by decide⟩]) unmarked_context_12_26384_337124 node_context_12_26384_337124
  intro a
  fin_cases a
  · exact context_13_105536_337078
  · exact context_13_105537_337098
  · exact context_13_105538_337115
  · exact context_13_105539_337123

theorem selected_cut_12774 : selected 8 ⟨337151, by decide⟩
    (prefixPartial 13 105540) = some ⟨13, 2, 0, 337151, 105540, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_105540_337151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105540 ⟨337151, by decide⟩ :=
  accepted_of_selected 13 105540 ⟨337151, by decide⟩ ⟨13, 2, 0, 337151, 105540, 2197, 16384⟩
    (by decide) selected_cut_12774

theorem selected_cut_12775 : selected 8 ⟨337177, by decide⟩
    (prefixPartial 13 105541) = some ⟨13, 2, 0, 337177, 105541, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_105541_337177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105541 ⟨337177, by decide⟩ :=
  accepted_of_selected 13 105541 ⟨337177, by decide⟩ ⟨13, 2, 0, 337177, 105541, 1801, 16384⟩
    (by decide) selected_cut_12775

theorem selected_cut_12776 : selected 8 ⟨337195, by decide⟩
    (prefixPartial 13 105542) = some ⟨13, 2, 0, 337195, 105542, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_105542_337195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105542 ⟨337195, by decide⟩ :=
  accepted_of_selected 13 105542 ⟨337195, by decide⟩ ⟨13, 2, 0, 337195, 105542, 1485, 16384⟩
    (by decide) selected_cut_12776

theorem selected_cut_12777 : selected 8 ⟨337201, by decide⟩
    (prefixPartial 13 105543) = some ⟨13, 2, 0, 337201, 105543, 565, 16384⟩ := by
  decide +kernel

theorem context_13_105543_337201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105543 ⟨337201, by decide⟩ :=
  accepted_of_selected 13 105543 ⟨337201, by decide⟩ ⟨13, 2, 0, 337201, 105543, 565, 16384⟩
    (by decide) selected_cut_12777

theorem unmarked_context_12_26385_337202 : frontier 9 ⟨337202, by decide⟩
    (prefixCache 12 26385) (prefixPartial 12 26385) = false := by
  decide +kernel

theorem node_context_12_26385_337202 : EJMOriginalGlobalDAGData.nodes 9 ⟨337202, by decide⟩ =
    .split (coordinate 12) (![⟨337151, by decide⟩,⟨337177, by decide⟩,⟨337195, by decide⟩,⟨337201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26385_337202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26385 ⟨337202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26385
    ⟨337202, by decide⟩ (by decide) (![⟨337151, by decide⟩,⟨337177, by decide⟩,⟨337195, by decide⟩,⟨337201, by decide⟩]) unmarked_context_12_26385_337202 node_context_12_26385_337202
  intro a
  fin_cases a
  · exact context_13_105540_337151
  · exact context_13_105541_337177
  · exact context_13_105542_337195
  · exact context_13_105543_337201

theorem selected_cut_12778 : selected 8 ⟨337233, by decide⟩
    (prefixPartial 13 105544) = some ⟨13, 2, 0, 337233, 105544, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_105544_337233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105544 ⟨337233, by decide⟩ :=
  accepted_of_selected 13 105544 ⟨337233, by decide⟩ ⟨13, 2, 0, 337233, 105544, 2181, 16384⟩
    (by decide) selected_cut_12778

theorem selected_cut_12779 : selected 8 ⟨337265, by decide⟩
    (prefixPartial 13 105545) = some ⟨13, 2, 0, 337265, 105545, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_105545_337265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105545 ⟨337265, by decide⟩ :=
  accepted_of_selected 13 105545 ⟨337265, by decide⟩ ⟨13, 2, 0, 337265, 105545, 1953, 16384⟩
    (by decide) selected_cut_12779

theorem selected_cut_12780 : selected 8 ⟨337283, by decide⟩
    (prefixPartial 13 105546) = some ⟨13, 2, 0, 337283, 105546, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_105546_337283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105546 ⟨337283, by decide⟩ :=
  accepted_of_selected 13 105546 ⟨337283, by decide⟩ ⟨13, 2, 0, 337283, 105546, 1473, 16384⟩
    (by decide) selected_cut_12780

theorem selected_cut_12781 : selected 8 ⟨337290, by decide⟩
    (prefixPartial 13 105547) = some ⟨13, 2, 0, 337290, 105547, 633, 16384⟩ := by
  decide +kernel

theorem context_13_105547_337290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105547 ⟨337290, by decide⟩ :=
  accepted_of_selected 13 105547 ⟨337290, by decide⟩ ⟨13, 2, 0, 337290, 105547, 633, 16384⟩
    (by decide) selected_cut_12781

theorem unmarked_context_12_26386_337291 : frontier 9 ⟨337291, by decide⟩
    (prefixCache 12 26386) (prefixPartial 12 26386) = false := by
  decide +kernel

theorem node_context_12_26386_337291 : EJMOriginalGlobalDAGData.nodes 9 ⟨337291, by decide⟩ =
    .split (coordinate 12) (![⟨337233, by decide⟩,⟨337265, by decide⟩,⟨337283, by decide⟩,⟨337290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26386_337291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26386 ⟨337291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26386
    ⟨337291, by decide⟩ (by decide) (![⟨337233, by decide⟩,⟨337265, by decide⟩,⟨337283, by decide⟩,⟨337290, by decide⟩]) unmarked_context_12_26386_337291 node_context_12_26386_337291
  intro a
  fin_cases a
  · exact context_13_105544_337233
  · exact context_13_105545_337265
  · exact context_13_105546_337283
  · exact context_13_105547_337290

theorem selected_cut_12782 : selected 8 ⟨337310, by decide⟩
    (prefixPartial 13 105548) = some ⟨13, 2, 0, 337310, 105548, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_105548_337310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105548 ⟨337310, by decide⟩ :=
  accepted_of_selected 13 105548 ⟨337310, by decide⟩ ⟨13, 2, 0, 337310, 105548, 1949, 16384⟩
    (by decide) selected_cut_12782

theorem selected_cut_12783 : selected 8 ⟨337335, by decide⟩
    (prefixPartial 13 105549) = some ⟨13, 2, 0, 337335, 105549, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_105549_337335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105549 ⟨337335, by decide⟩ :=
  accepted_of_selected 13 105549 ⟨337335, by decide⟩ ⟨13, 2, 0, 337335, 105549, 2093, 16384⟩
    (by decide) selected_cut_12783

theorem selected_cut_12784 : selected 8 ⟨337354, by decide⟩
    (prefixPartial 13 105550) = some ⟨13, 2, 0, 337354, 105550, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_105550_337354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105550 ⟨337354, by decide⟩ :=
  accepted_of_selected 13 105550 ⟨337354, by decide⟩ ⟨13, 2, 0, 337354, 105550, 1465, 16384⟩
    (by decide) selected_cut_12784

theorem selected_cut_12785 : selected 8 ⟨337360, by decide⟩
    (prefixPartial 13 105551) = some ⟨13, 2, 0, 337360, 105551, 637, 16384⟩ := by
  decide +kernel

theorem context_13_105551_337360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105551 ⟨337360, by decide⟩ :=
  accepted_of_selected 13 105551 ⟨337360, by decide⟩ ⟨13, 2, 0, 337360, 105551, 637, 16384⟩
    (by decide) selected_cut_12785

theorem unmarked_context_12_26387_337361 : frontier 9 ⟨337361, by decide⟩
    (prefixCache 12 26387) (prefixPartial 12 26387) = false := by
  decide +kernel

theorem node_context_12_26387_337361 : EJMOriginalGlobalDAGData.nodes 9 ⟨337361, by decide⟩ =
    .split (coordinate 12) (![⟨337310, by decide⟩,⟨337335, by decide⟩,⟨337354, by decide⟩,⟨337360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26387_337361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26387 ⟨337361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26387
    ⟨337361, by decide⟩ (by decide) (![⟨337310, by decide⟩,⟨337335, by decide⟩,⟨337354, by decide⟩,⟨337360, by decide⟩]) unmarked_context_12_26387_337361 node_context_12_26387_337361
  intro a
  fin_cases a
  · exact context_13_105548_337310
  · exact context_13_105549_337335
  · exact context_13_105550_337354
  · exact context_13_105551_337360

theorem unmarked_context_11_6596_337362 : frontier 10 ⟨337362, by decide⟩
    (prefixCache 11 6596) (prefixPartial 11 6596) = false := by
  decide +kernel

theorem node_context_11_6596_337362 : EJMOriginalGlobalDAGData.nodes 10 ⟨337362, by decide⟩ =
    .split (coordinate 11) (![⟨337124, by decide⟩,⟨337202, by decide⟩,⟨337291, by decide⟩,⟨337361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6596_337362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6596 ⟨337362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6596
    ⟨337362, by decide⟩ (by decide) (![⟨337124, by decide⟩,⟨337202, by decide⟩,⟨337291, by decide⟩,⟨337361, by decide⟩]) unmarked_context_11_6596_337362 node_context_11_6596_337362
  intro a
  fin_cases a
  · exact context_12_26384_337124
  · exact context_12_26385_337202
  · exact context_12_26386_337291
  · exact context_12_26387_337361

theorem selected_cut_12786 : selected 8 ⟨337390, by decide⟩
    (prefixPartial 13 105552) = some ⟨13, 2, 0, 337390, 105552, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_105552_337390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105552 ⟨337390, by decide⟩ :=
  accepted_of_selected 13 105552 ⟨337390, by decide⟩ ⟨13, 2, 0, 337390, 105552, 2117, 16384⟩
    (by decide) selected_cut_12786

theorem selected_cut_12787 : selected 8 ⟨337445, by decide⟩
    (prefixPartial 13 105553) = some ⟨13, 2, 0, 337445, 105553, 3313, 16384⟩ := by
  decide +kernel

theorem context_13_105553_337445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105553 ⟨337445, by decide⟩ :=
  accepted_of_selected 13 105553 ⟨337445, by decide⟩ ⟨13, 2, 0, 337445, 105553, 3313, 16384⟩
    (by decide) selected_cut_12787

theorem selected_cut_12788 : selected 8 ⟨337468, by decide⟩
    (prefixPartial 13 105554) = some ⟨13, 2, 0, 337468, 105554, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_105554_337468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105554 ⟨337468, by decide⟩ :=
  accepted_of_selected 13 105554 ⟨337468, by decide⟩ ⟨13, 2, 0, 337468, 105554, 1937, 16384⟩
    (by decide) selected_cut_12788

theorem selected_cut_12789 : selected 8 ⟨337475, by decide⟩
    (prefixPartial 13 105555) = some ⟨13, 2, 0, 337475, 105555, 969, 16384⟩ := by
  decide +kernel

theorem context_13_105555_337475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105555 ⟨337475, by decide⟩ :=
  accepted_of_selected 13 105555 ⟨337475, by decide⟩ ⟨13, 2, 0, 337475, 105555, 969, 16384⟩
    (by decide) selected_cut_12789

theorem unmarked_context_12_26388_337476 : frontier 9 ⟨337476, by decide⟩
    (prefixCache 12 26388) (prefixPartial 12 26388) = false := by
  decide +kernel

theorem node_context_12_26388_337476 : EJMOriginalGlobalDAGData.nodes 9 ⟨337476, by decide⟩ =
    .split (coordinate 12) (![⟨337390, by decide⟩,⟨337445, by decide⟩,⟨337468, by decide⟩,⟨337475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26388_337476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26388 ⟨337476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26388
    ⟨337476, by decide⟩ (by decide) (![⟨337390, by decide⟩,⟨337445, by decide⟩,⟨337468, by decide⟩,⟨337475, by decide⟩]) unmarked_context_12_26388_337476 node_context_12_26388_337476
  intro a
  fin_cases a
  · exact context_13_105552_337390
  · exact context_13_105553_337445
  · exact context_13_105554_337468
  · exact context_13_105555_337475

theorem selected_cut_12790 : selected 8 ⟨337527, by decide⟩
    (prefixPartial 13 105556) = some ⟨13, 2, 0, 337527, 105556, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_105556_337527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105556 ⟨337527, by decide⟩ :=
  accepted_of_selected 13 105556 ⟨337527, by decide⟩ ⟨13, 2, 0, 337527, 105556, 3029, 16384⟩
    (by decide) selected_cut_12790

theorem selected_cut_12791 : selected 8 ⟨337598, by decide⟩
    (prefixPartial 13 105557) = some ⟨13, 2, 0, 337598, 105557, 3577, 16384⟩ := by
  decide +kernel

theorem context_13_105557_337598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105557 ⟨337598, by decide⟩ :=
  accepted_of_selected 13 105557 ⟨337598, by decide⟩ ⟨13, 2, 0, 337598, 105557, 3577, 16384⟩
    (by decide) selected_cut_12791

theorem selected_cut_12792 : selected 8 ⟨337633, by decide⟩
    (prefixPartial 13 105558) = some ⟨13, 2, 0, 337633, 105558, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_105558_337633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105558 ⟨337633, by decide⟩ :=
  accepted_of_selected 13 105558 ⟨337633, by decide⟩ ⟨13, 2, 0, 337633, 105558, 2189, 16384⟩
    (by decide) selected_cut_12792

theorem selected_cut_12793 : selected 8 ⟨337642, by decide⟩
    (prefixPartial 13 105559) = some ⟨13, 2, 0, 337642, 105559, 897, 16384⟩ := by
  decide +kernel

theorem context_13_105559_337642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105559 ⟨337642, by decide⟩ :=
  accepted_of_selected 13 105559 ⟨337642, by decide⟩ ⟨13, 2, 0, 337642, 105559, 897, 16384⟩
    (by decide) selected_cut_12793

theorem unmarked_context_12_26389_337643 : frontier 9 ⟨337643, by decide⟩
    (prefixCache 12 26389) (prefixPartial 12 26389) = false := by
  decide +kernel

theorem node_context_12_26389_337643 : EJMOriginalGlobalDAGData.nodes 9 ⟨337643, by decide⟩ =
    .split (coordinate 12) (![⟨337527, by decide⟩,⟨337598, by decide⟩,⟨337633, by decide⟩,⟨337642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26389_337643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26389 ⟨337643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26389
    ⟨337643, by decide⟩ (by decide) (![⟨337527, by decide⟩,⟨337598, by decide⟩,⟨337633, by decide⟩,⟨337642, by decide⟩]) unmarked_context_12_26389_337643 node_context_12_26389_337643
  intro a
  fin_cases a
  · exact context_13_105556_337527
  · exact context_13_105557_337598
  · exact context_13_105558_337633
  · exact context_13_105559_337642

theorem selected_cut_12794 : selected 8 ⟨337705, by decide⟩
    (prefixPartial 13 105560) = some ⟨13, 2, 0, 337705, 105560, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_105560_337705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105560 ⟨337705, by decide⟩ :=
  accepted_of_selected 13 105560 ⟨337705, by decide⟩ ⟨13, 2, 0, 337705, 105560, 2933, 16384⟩
    (by decide) selected_cut_12794

theorem selected_cut_12795 : selected 8 ⟨337786, by decide⟩
    (prefixPartial 13 105561) = some ⟨13, 2, 0, 337786, 105561, 3865, 16384⟩ := by
  decide +kernel

theorem context_13_105561_337786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105561 ⟨337786, by decide⟩ :=
  accepted_of_selected 13 105561 ⟨337786, by decide⟩ ⟨13, 2, 0, 337786, 105561, 3865, 16384⟩
    (by decide) selected_cut_12795

theorem selected_cut_12796 : selected 8 ⟨337819, by decide⟩
    (prefixPartial 13 105562) = some ⟨13, 2, 0, 337819, 105562, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_105562_337819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105562 ⟨337819, by decide⟩ :=
  accepted_of_selected 13 105562 ⟨337819, by decide⟩ ⟨13, 2, 0, 337819, 105562, 2185, 16384⟩
    (by decide) selected_cut_12796

theorem selected_cut_12797 : selected 8 ⟨337839, by decide⟩
    (prefixPartial 13 105563) = some ⟨13, 2, 0, 337839, 105563, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_105563_337839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105563 ⟨337839, by decide⟩ :=
  accepted_of_selected 13 105563 ⟨337839, by decide⟩ ⟨13, 2, 0, 337839, 105563, 1089, 16384⟩
    (by decide) selected_cut_12797

theorem unmarked_context_12_26390_337840 : frontier 9 ⟨337840, by decide⟩
    (prefixCache 12 26390) (prefixPartial 12 26390) = false := by
  decide +kernel

theorem node_context_12_26390_337840 : EJMOriginalGlobalDAGData.nodes 9 ⟨337840, by decide⟩ =
    .split (coordinate 12) (![⟨337705, by decide⟩,⟨337786, by decide⟩,⟨337819, by decide⟩,⟨337839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26390_337840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26390 ⟨337840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26390
    ⟨337840, by decide⟩ (by decide) (![⟨337705, by decide⟩,⟨337786, by decide⟩,⟨337819, by decide⟩,⟨337839, by decide⟩]) unmarked_context_12_26390_337840 node_context_12_26390_337840
  intro a
  fin_cases a
  · exact context_13_105560_337705
  · exact context_13_105561_337786
  · exact context_13_105562_337819
  · exact context_13_105563_337839

theorem selected_cut_12798 : selected 8 ⟨337878, by decide⟩
    (prefixPartial 13 105564) = some ⟨13, 2, 0, 337878, 105564, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_105564_337878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105564 ⟨337878, by decide⟩ :=
  accepted_of_selected 13 105564 ⟨337878, by decide⟩ ⟨13, 2, 0, 337878, 105564, 2517, 16384⟩
    (by decide) selected_cut_12798

theorem selected_cut_12799 : selected 8 ⟨337947, by decide⟩
    (prefixPartial 13 105565) = some ⟨13, 2, 0, 337947, 105565, 4009, 16384⟩ := by
  decide +kernel

theorem context_13_105565_337947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105565 ⟨337947, by decide⟩ :=
  accepted_of_selected 13 105565 ⟨337947, by decide⟩ ⟨13, 2, 0, 337947, 105565, 4009, 16384⟩
    (by decide) selected_cut_12799

theorem selected_cut_12800 : selected 8 ⟨337973, by decide⟩
    (prefixPartial 13 105566) = some ⟨13, 2, 0, 337973, 105566, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_105566_337973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105566 ⟨337973, by decide⟩ :=
  accepted_of_selected 13 105566 ⟨337973, by decide⟩ ⟨13, 2, 0, 337973, 105566, 2153, 16384⟩
    (by decide) selected_cut_12800

theorem selected_cut_12801 : selected 8 ⟨337983, by decide⟩
    (prefixPartial 13 105567) = some ⟨13, 2, 0, 337983, 105567, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_105567_337983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105567 ⟨337983, by decide⟩ :=
  accepted_of_selected 13 105567 ⟨337983, by decide⟩ ⟨13, 2, 0, 337983, 105567, 1033, 16384⟩
    (by decide) selected_cut_12801

theorem unmarked_context_12_26391_337984 : frontier 9 ⟨337984, by decide⟩
    (prefixCache 12 26391) (prefixPartial 12 26391) = false := by
  decide +kernel

theorem node_context_12_26391_337984 : EJMOriginalGlobalDAGData.nodes 9 ⟨337984, by decide⟩ =
    .split (coordinate 12) (![⟨337878, by decide⟩,⟨337947, by decide⟩,⟨337973, by decide⟩,⟨337983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26391_337984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26391 ⟨337984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26391
    ⟨337984, by decide⟩ (by decide) (![⟨337878, by decide⟩,⟨337947, by decide⟩,⟨337973, by decide⟩,⟨337983, by decide⟩]) unmarked_context_12_26391_337984 node_context_12_26391_337984
  intro a
  fin_cases a
  · exact context_13_105564_337878
  · exact context_13_105565_337947
  · exact context_13_105566_337973
  · exact context_13_105567_337983

theorem unmarked_context_11_6597_337985 : frontier 10 ⟨337985, by decide⟩
    (prefixCache 11 6597) (prefixPartial 11 6597) = false := by
  decide +kernel

theorem node_context_11_6597_337985 : EJMOriginalGlobalDAGData.nodes 10 ⟨337985, by decide⟩ =
    .split (coordinate 11) (![⟨337476, by decide⟩,⟨337643, by decide⟩,⟨337840, by decide⟩,⟨337984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6597_337985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6597 ⟨337985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6597
    ⟨337985, by decide⟩ (by decide) (![⟨337476, by decide⟩,⟨337643, by decide⟩,⟨337840, by decide⟩,⟨337984, by decide⟩]) unmarked_context_11_6597_337985 node_context_11_6597_337985
  intro a
  fin_cases a
  · exact context_12_26388_337476
  · exact context_12_26389_337643
  · exact context_12_26390_337840
  · exact context_12_26391_337984

theorem selected_cut_12802 : selected 8 ⟨338002, by decide⟩
    (prefixPartial 13 105568) = some ⟨13, 2, 0, 338002, 105568, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_105568_338002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105568 ⟨338002, by decide⟩ :=
  accepted_of_selected 13 105568 ⟨338002, by decide⟩ ⟨13, 2, 0, 338002, 105568, 1257, 16384⟩
    (by decide) selected_cut_12802

theorem selected_cut_12803 : selected 8 ⟨338029, by decide⟩
    (prefixPartial 13 105569) = some ⟨13, 2, 0, 338029, 105569, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_105569_338029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105569 ⟨338029, by decide⟩ :=
  accepted_of_selected 13 105569 ⟨338029, by decide⟩ ⟨13, 2, 0, 338029, 105569, 1825, 16384⟩
    (by decide) selected_cut_12803

theorem selected_cut_12804 : selected 8 ⟨338047, by decide⟩
    (prefixPartial 13 105570) = some ⟨13, 2, 0, 338047, 105570, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_105570_338047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105570 ⟨338047, by decide⟩ :=
  accepted_of_selected 13 105570 ⟨338047, by decide⟩ ⟨13, 2, 0, 338047, 105570, 1593, 16384⟩
    (by decide) selected_cut_12804

theorem selected_cut_12805 : selected 8 ⟨338059, by decide⟩
    (prefixPartial 13 105571) = some ⟨13, 2, 0, 338059, 105571, 781, 16384⟩ := by
  decide +kernel

theorem context_13_105571_338059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105571 ⟨338059, by decide⟩ :=
  accepted_of_selected 13 105571 ⟨338059, by decide⟩ ⟨13, 2, 0, 338059, 105571, 781, 16384⟩
    (by decide) selected_cut_12805

theorem unmarked_context_12_26392_338060 : frontier 9 ⟨338060, by decide⟩
    (prefixCache 12 26392) (prefixPartial 12 26392) = false := by
  decide +kernel

theorem node_context_12_26392_338060 : EJMOriginalGlobalDAGData.nodes 9 ⟨338060, by decide⟩ =
    .split (coordinate 12) (![⟨338002, by decide⟩,⟨338029, by decide⟩,⟨338047, by decide⟩,⟨338059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26392_338060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26392 ⟨338060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26392
    ⟨338060, by decide⟩ (by decide) (![⟨338002, by decide⟩,⟨338029, by decide⟩,⟨338047, by decide⟩,⟨338059, by decide⟩]) unmarked_context_12_26392_338060 node_context_12_26392_338060
  intro a
  fin_cases a
  · exact context_13_105568_338002
  · exact context_13_105569_338029
  · exact context_13_105570_338047
  · exact context_13_105571_338059

theorem selected_cut_12806 : selected 8 ⟨338080, by decide⟩
    (prefixPartial 13 105572) = some ⟨13, 2, 0, 338080, 105572, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_105572_338080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105572 ⟨338080, by decide⟩ :=
  accepted_of_selected 13 105572 ⟨338080, by decide⟩ ⟨13, 2, 0, 338080, 105572, 1653, 16384⟩
    (by decide) selected_cut_12806

theorem selected_cut_12807 : selected 8 ⟨338112, by decide⟩
    (prefixPartial 13 105573) = some ⟨13, 2, 0, 338112, 105573, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_105573_338112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105573 ⟨338112, by decide⟩ :=
  accepted_of_selected 13 105573 ⟨338112, by decide⟩ ⟨13, 2, 0, 338112, 105573, 1905, 16384⟩
    (by decide) selected_cut_12807

theorem selected_cut_12808 : selected 8 ⟨338132, by decide⟩
    (prefixPartial 13 105574) = some ⟨13, 2, 0, 338132, 105574, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_105574_338132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105574 ⟨338132, by decide⟩ :=
  accepted_of_selected 13 105574 ⟨338132, by decide⟩ ⟨13, 2, 0, 338132, 105574, 1541, 16384⟩
    (by decide) selected_cut_12808

theorem selected_cut_12809 : selected 8 ⟨338142, by decide⟩
    (prefixPartial 13 105575) = some ⟨13, 2, 0, 338142, 105575, 765, 16384⟩ := by
  decide +kernel

theorem context_13_105575_338142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105575 ⟨338142, by decide⟩ :=
  accepted_of_selected 13 105575 ⟨338142, by decide⟩ ⟨13, 2, 0, 338142, 105575, 765, 16384⟩
    (by decide) selected_cut_12809

theorem unmarked_context_12_26393_338143 : frontier 9 ⟨338143, by decide⟩
    (prefixCache 12 26393) (prefixPartial 12 26393) = false := by
  decide +kernel

theorem node_context_12_26393_338143 : EJMOriginalGlobalDAGData.nodes 9 ⟨338143, by decide⟩ =
    .split (coordinate 12) (![⟨338080, by decide⟩,⟨338112, by decide⟩,⟨338132, by decide⟩,⟨338142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26393_338143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26393 ⟨338143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26393
    ⟨338143, by decide⟩ (by decide) (![⟨338080, by decide⟩,⟨338112, by decide⟩,⟨338132, by decide⟩,⟨338142, by decide⟩]) unmarked_context_12_26393_338143 node_context_12_26393_338143
  intro a
  fin_cases a
  · exact context_13_105572_338080
  · exact context_13_105573_338112
  · exact context_13_105574_338132
  · exact context_13_105575_338142

theorem selected_cut_12810 : selected 8 ⟨338159, by decide⟩
    (prefixPartial 13 105576) = some ⟨13, 2, 0, 338159, 105576, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_105576_338159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105576 ⟨338159, by decide⟩ :=
  accepted_of_selected 13 105576 ⟨338159, by decide⟩ ⟨13, 2, 0, 338159, 105576, 1489, 16384⟩
    (by decide) selected_cut_12810

theorem selected_cut_12811 : selected 8 ⟨338193, by decide⟩
    (prefixPartial 13 105577) = some ⟨13, 2, 0, 338193, 105577, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_105577_338193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105577 ⟨338193, by decide⟩ :=
  accepted_of_selected 13 105577 ⟨338193, by decide⟩ ⟨13, 2, 0, 338193, 105577, 1977, 16384⟩
    (by decide) selected_cut_12811

theorem selected_cut_12812 : selected 8 ⟨338210, by decide⟩
    (prefixPartial 13 105578) = some ⟨13, 2, 0, 338210, 105578, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_105578_338210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105578 ⟨338210, by decide⟩ :=
  accepted_of_selected 13 105578 ⟨338210, by decide⟩ ⟨13, 2, 0, 338210, 105578, 1565, 16384⟩
    (by decide) selected_cut_12812

theorem selected_cut_12813 : selected 8 ⟨338219, by decide⟩
    (prefixPartial 13 105579) = some ⟨13, 2, 0, 338219, 105579, 793, 16384⟩ := by
  decide +kernel

theorem context_13_105579_338219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105579 ⟨338219, by decide⟩ :=
  accepted_of_selected 13 105579 ⟨338219, by decide⟩ ⟨13, 2, 0, 338219, 105579, 793, 16384⟩
    (by decide) selected_cut_12813

theorem unmarked_context_12_26394_338220 : frontier 9 ⟨338220, by decide⟩
    (prefixCache 12 26394) (prefixPartial 12 26394) = false := by
  decide +kernel

theorem node_context_12_26394_338220 : EJMOriginalGlobalDAGData.nodes 9 ⟨338220, by decide⟩ =
    .split (coordinate 12) (![⟨338159, by decide⟩,⟨338193, by decide⟩,⟨338210, by decide⟩,⟨338219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26394_338220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26394 ⟨338220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26394
    ⟨338220, by decide⟩ (by decide) (![⟨338159, by decide⟩,⟨338193, by decide⟩,⟨338210, by decide⟩,⟨338219, by decide⟩]) unmarked_context_12_26394_338220 node_context_12_26394_338220
  intro a
  fin_cases a
  · exact context_13_105576_338159
  · exact context_13_105577_338193
  · exact context_13_105578_338210
  · exact context_13_105579_338219

theorem selected_cut_12814 : selected 8 ⟨338235, by decide⟩
    (prefixPartial 13 105580) = some ⟨13, 2, 0, 338235, 105580, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_105580_338235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105580 ⟨338235, by decide⟩ :=
  accepted_of_selected 13 105580 ⟨338235, by decide⟩ ⟨13, 2, 0, 338235, 105580, 1317, 16384⟩
    (by decide) selected_cut_12814

theorem selected_cut_12815 : selected 8 ⟨338273, by decide⟩
    (prefixPartial 13 105581) = some ⟨13, 2, 0, 338273, 105581, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_105581_338273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105581 ⟨338273, by decide⟩ :=
  accepted_of_selected 13 105581 ⟨338273, by decide⟩ ⟨13, 2, 0, 338273, 105581, 2285, 16384⟩
    (by decide) selected_cut_12815

theorem selected_cut_12816 : selected 8 ⟨338292, by decide⟩
    (prefixPartial 13 105582) = some ⟨13, 2, 0, 338292, 105582, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_105582_338292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105582 ⟨338292, by decide⟩ :=
  accepted_of_selected 13 105582 ⟨338292, by decide⟩ ⟨13, 2, 0, 338292, 105582, 1437, 16384⟩
    (by decide) selected_cut_12816

theorem selected_cut_12817 : selected 8 ⟨338300, by decide⟩
    (prefixPartial 13 105583) = some ⟨13, 2, 0, 338300, 105583, 741, 16384⟩ := by
  decide +kernel

theorem context_13_105583_338300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105583 ⟨338300, by decide⟩ :=
  accepted_of_selected 13 105583 ⟨338300, by decide⟩ ⟨13, 2, 0, 338300, 105583, 741, 16384⟩
    (by decide) selected_cut_12817

theorem unmarked_context_12_26395_338301 : frontier 9 ⟨338301, by decide⟩
    (prefixCache 12 26395) (prefixPartial 12 26395) = false := by
  decide +kernel

theorem node_context_12_26395_338301 : EJMOriginalGlobalDAGData.nodes 9 ⟨338301, by decide⟩ =
    .split (coordinate 12) (![⟨338235, by decide⟩,⟨338273, by decide⟩,⟨338292, by decide⟩,⟨338300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26395_338301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26395 ⟨338301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26395
    ⟨338301, by decide⟩ (by decide) (![⟨338235, by decide⟩,⟨338273, by decide⟩,⟨338292, by decide⟩,⟨338300, by decide⟩]) unmarked_context_12_26395_338301 node_context_12_26395_338301
  intro a
  fin_cases a
  · exact context_13_105580_338235
  · exact context_13_105581_338273
  · exact context_13_105582_338292
  · exact context_13_105583_338300

theorem unmarked_context_11_6598_338302 : frontier 10 ⟨338302, by decide⟩
    (prefixCache 11 6598) (prefixPartial 11 6598) = false := by
  decide +kernel

theorem node_context_11_6598_338302 : EJMOriginalGlobalDAGData.nodes 10 ⟨338302, by decide⟩ =
    .split (coordinate 11) (![⟨338060, by decide⟩,⟨338143, by decide⟩,⟨338220, by decide⟩,⟨338301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6598_338302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6598 ⟨338302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6598
    ⟨338302, by decide⟩ (by decide) (![⟨338060, by decide⟩,⟨338143, by decide⟩,⟨338220, by decide⟩,⟨338301, by decide⟩]) unmarked_context_11_6598_338302 node_context_11_6598_338302
  intro a
  fin_cases a
  · exact context_12_26392_338060
  · exact context_12_26393_338143
  · exact context_12_26394_338220
  · exact context_12_26395_338301

theorem selected_cut_12818 : selected 8 ⟨338316, by decide⟩
    (prefixPartial 13 105584) = some ⟨13, 2, 0, 338316, 105584, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_105584_338316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105584 ⟨338316, by decide⟩ :=
  accepted_of_selected 13 105584 ⟨338316, by decide⟩ ⟨13, 2, 0, 338316, 105584, 1009, 16384⟩
    (by decide) selected_cut_12818

theorem selected_cut_12819 : selected 8 ⟨338340, by decide⟩
    (prefixPartial 13 105585) = some ⟨13, 2, 0, 338340, 105585, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_105585_338340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105585 ⟨338340, by decide⟩ :=
  accepted_of_selected 13 105585 ⟨338340, by decide⟩ ⟨13, 2, 0, 338340, 105585, 1537, 16384⟩
    (by decide) selected_cut_12819

theorem selected_cut_12820 : selected 8 ⟨338355, by decide⟩
    (prefixPartial 13 105586) = some ⟨13, 2, 0, 338355, 105586, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_105586_338355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105586 ⟨338355, by decide⟩ :=
  accepted_of_selected 13 105586 ⟨338355, by decide⟩ ⟨13, 2, 0, 338355, 105586, 1173, 16384⟩
    (by decide) selected_cut_12820

theorem selected_cut_12821 : selected 8 ⟨338361, by decide⟩
    (prefixPartial 13 105587) = some ⟨13, 2, 0, 338361, 105587, 629, 16384⟩ := by
  decide +kernel

theorem context_13_105587_338361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105587 ⟨338361, by decide⟩ :=
  accepted_of_selected 13 105587 ⟨338361, by decide⟩ ⟨13, 2, 0, 338361, 105587, 629, 16384⟩
    (by decide) selected_cut_12821

theorem unmarked_context_12_26396_338362 : frontier 9 ⟨338362, by decide⟩
    (prefixCache 12 26396) (prefixPartial 12 26396) = false := by
  decide +kernel

theorem node_context_12_26396_338362 : EJMOriginalGlobalDAGData.nodes 9 ⟨338362, by decide⟩ =
    .split (coordinate 12) (![⟨338316, by decide⟩,⟨338340, by decide⟩,⟨338355, by decide⟩,⟨338361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26396_338362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26396 ⟨338362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26396
    ⟨338362, by decide⟩ (by decide) (![⟨338316, by decide⟩,⟨338340, by decide⟩,⟨338355, by decide⟩,⟨338361, by decide⟩]) unmarked_context_12_26396_338362 node_context_12_26396_338362
  intro a
  fin_cases a
  · exact context_13_105584_338316
  · exact context_13_105585_338340
  · exact context_13_105586_338355
  · exact context_13_105587_338361

theorem selected_cut_12822 : selected 8 ⟨338380, by decide⟩
    (prefixPartial 13 105588) = some ⟨13, 2, 0, 338380, 105588, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_105588_338380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105588 ⟨338380, by decide⟩ :=
  accepted_of_selected 13 105588 ⟨338380, by decide⟩ ⟨13, 2, 0, 338380, 105588, 1361, 16384⟩
    (by decide) selected_cut_12822

theorem selected_cut_12823 : selected 8 ⟨338406, by decide⟩
    (prefixPartial 13 105589) = some ⟨13, 2, 0, 338406, 105589, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_105589_338406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105589 ⟨338406, by decide⟩ :=
  accepted_of_selected 13 105589 ⟨338406, by decide⟩ ⟨13, 2, 0, 338406, 105589, 1629, 16384⟩
    (by decide) selected_cut_12823

theorem selected_cut_12824 : selected 8 ⟨338429, by decide⟩
    (prefixPartial 13 105590) = some ⟨13, 2, 0, 338429, 105590, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_105590_338429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105590 ⟨338429, by decide⟩ :=
  accepted_of_selected 13 105590 ⟨338429, by decide⟩ ⟨13, 2, 0, 338429, 105590, 1449, 16384⟩
    (by decide) selected_cut_12824

theorem selected_cut_12825 : selected 8 ⟨338434, by decide⟩
    (prefixPartial 13 105591) = some ⟨13, 2, 0, 338434, 105591, 557, 16384⟩ := by
  decide +kernel

theorem context_13_105591_338434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105591 ⟨338434, by decide⟩ :=
  accepted_of_selected 13 105591 ⟨338434, by decide⟩ ⟨13, 2, 0, 338434, 105591, 557, 16384⟩
    (by decide) selected_cut_12825

theorem unmarked_context_12_26397_338435 : frontier 9 ⟨338435, by decide⟩
    (prefixCache 12 26397) (prefixPartial 12 26397) = false := by
  decide +kernel

theorem node_context_12_26397_338435 : EJMOriginalGlobalDAGData.nodes 9 ⟨338435, by decide⟩ =
    .split (coordinate 12) (![⟨338380, by decide⟩,⟨338406, by decide⟩,⟨338429, by decide⟩,⟨338434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26397_338435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26397 ⟨338435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26397
    ⟨338435, by decide⟩ (by decide) (![⟨338380, by decide⟩,⟨338406, by decide⟩,⟨338429, by decide⟩,⟨338434, by decide⟩]) unmarked_context_12_26397_338435 node_context_12_26397_338435
  intro a
  fin_cases a
  · exact context_13_105588_338380
  · exact context_13_105589_338406
  · exact context_13_105590_338429
  · exact context_13_105591_338434

theorem selected_cut_12826 : selected 8 ⟨338459, by decide⟩
    (prefixPartial 13 105592) = some ⟨13, 2, 0, 338459, 105592, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_105592_338459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105592 ⟨338459, by decide⟩ :=
  accepted_of_selected 13 105592 ⟨338459, by decide⟩ ⟨13, 2, 0, 338459, 105592, 1329, 16384⟩
    (by decide) selected_cut_12826

theorem selected_cut_12827 : selected 8 ⟨338482, by decide⟩
    (prefixPartial 13 105593) = some ⟨13, 2, 0, 338482, 105593, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_105593_338482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105593 ⟨338482, by decide⟩ :=
  accepted_of_selected 13 105593 ⟨338482, by decide⟩ ⟨13, 2, 0, 338482, 105593, 1809, 16384⟩
    (by decide) selected_cut_12827

theorem selected_cut_12828 : selected 8 ⟨338502, by decide⟩
    (prefixPartial 13 105594) = some ⟨13, 2, 0, 338502, 105594, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_105594_338502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105594 ⟨338502, by decide⟩ :=
  accepted_of_selected 13 105594 ⟨338502, by decide⟩ ⟨13, 2, 0, 338502, 105594, 1341, 16384⟩
    (by decide) selected_cut_12828

theorem selected_cut_12829 : selected 8 ⟨338512, by decide⟩
    (prefixPartial 13 105595) = some ⟨13, 2, 0, 338512, 105595, 653, 16384⟩ := by
  decide +kernel

theorem context_13_105595_338512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105595 ⟨338512, by decide⟩ :=
  accepted_of_selected 13 105595 ⟨338512, by decide⟩ ⟨13, 2, 0, 338512, 105595, 653, 16384⟩
    (by decide) selected_cut_12829

theorem unmarked_context_12_26398_338513 : frontier 9 ⟨338513, by decide⟩
    (prefixCache 12 26398) (prefixPartial 12 26398) = false := by
  decide +kernel

theorem node_context_12_26398_338513 : EJMOriginalGlobalDAGData.nodes 9 ⟨338513, by decide⟩ =
    .split (coordinate 12) (![⟨338459, by decide⟩,⟨338482, by decide⟩,⟨338502, by decide⟩,⟨338512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26398_338513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26398 ⟨338513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26398
    ⟨338513, by decide⟩ (by decide) (![⟨338459, by decide⟩,⟨338482, by decide⟩,⟨338502, by decide⟩,⟨338512, by decide⟩]) unmarked_context_12_26398_338513 node_context_12_26398_338513
  intro a
  fin_cases a
  · exact context_13_105592_338459
  · exact context_13_105593_338482
  · exact context_13_105594_338502
  · exact context_13_105595_338512

theorem selected_cut_12830 : selected 8 ⟨338549, by decide⟩
    (prefixPartial 13 105596) = some ⟨13, 2, 0, 338549, 105596, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_105596_338549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105596 ⟨338549, by decide⟩ :=
  accepted_of_selected 13 105596 ⟨338549, by decide⟩ ⟨13, 2, 0, 338549, 105596, 2009, 16384⟩
    (by decide) selected_cut_12830

theorem selected_cut_12831 : selected 8 ⟨338611, by decide⟩
    (prefixPartial 13 105597) = some ⟨13, 2, 0, 338611, 105597, 3341, 16384⟩ := by
  decide +kernel

theorem context_13_105597_338611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105597 ⟨338611, by decide⟩ :=
  accepted_of_selected 13 105597 ⟨338611, by decide⟩ ⟨13, 2, 0, 338611, 105597, 3341, 16384⟩
    (by decide) selected_cut_12831

theorem selected_cut_12832 : selected 8 ⟨338658, by decide⟩
    (prefixPartial 13 105598) = some ⟨13, 2, 0, 338658, 105598, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_105598_338658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105598 ⟨338658, by decide⟩ :=
  accepted_of_selected 13 105598 ⟨338658, by decide⟩ ⟨13, 2, 0, 338658, 105598, 2297, 16384⟩
    (by decide) selected_cut_12832

theorem selected_cut_12833 : selected 8 ⟨338670, by decide⟩
    (prefixPartial 13 105599) = some ⟨13, 2, 0, 338670, 105599, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_105599_338670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105599 ⟨338670, by decide⟩ :=
  accepted_of_selected 13 105599 ⟨338670, by decide⟩ ⟨13, 2, 0, 338670, 105599, 1033, 16384⟩
    (by decide) selected_cut_12833

theorem unmarked_context_12_26399_338671 : frontier 9 ⟨338671, by decide⟩
    (prefixCache 12 26399) (prefixPartial 12 26399) = false := by
  decide +kernel

theorem node_context_12_26399_338671 : EJMOriginalGlobalDAGData.nodes 9 ⟨338671, by decide⟩ =
    .split (coordinate 12) (![⟨338549, by decide⟩,⟨338611, by decide⟩,⟨338658, by decide⟩,⟨338670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26399_338671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26399 ⟨338671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26399
    ⟨338671, by decide⟩ (by decide) (![⟨338549, by decide⟩,⟨338611, by decide⟩,⟨338658, by decide⟩,⟨338670, by decide⟩]) unmarked_context_12_26399_338671 node_context_12_26399_338671
  intro a
  fin_cases a
  · exact context_13_105596_338549
  · exact context_13_105597_338611
  · exact context_13_105598_338658
  · exact context_13_105599_338670

theorem unmarked_context_11_6599_338672 : frontier 10 ⟨338672, by decide⟩
    (prefixCache 11 6599) (prefixPartial 11 6599) = false := by
  decide +kernel

theorem node_context_11_6599_338672 : EJMOriginalGlobalDAGData.nodes 10 ⟨338672, by decide⟩ =
    .split (coordinate 11) (![⟨338362, by decide⟩,⟨338435, by decide⟩,⟨338513, by decide⟩,⟨338671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6599_338672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6599 ⟨338672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6599
    ⟨338672, by decide⟩ (by decide) (![⟨338362, by decide⟩,⟨338435, by decide⟩,⟨338513, by decide⟩,⟨338671, by decide⟩]) unmarked_context_11_6599_338672 node_context_11_6599_338672
  intro a
  fin_cases a
  · exact context_12_26396_338362
  · exact context_12_26397_338435
  · exact context_12_26398_338513
  · exact context_12_26399_338671

theorem unmarked_context_10_1649_338673 : frontier 11 ⟨338673, by decide⟩
    (prefixCache 10 1649) (prefixPartial 10 1649) = false := by
  decide +kernel

theorem node_context_10_1649_338673 : EJMOriginalGlobalDAGData.nodes 11 ⟨338673, by decide⟩ =
    .split (coordinate 10) (![⟨337362, by decide⟩,⟨337985, by decide⟩,⟨338302, by decide⟩,⟨338672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1649_338673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1649 ⟨338673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1649
    ⟨338673, by decide⟩ (by decide) (![⟨337362, by decide⟩,⟨337985, by decide⟩,⟨338302, by decide⟩,⟨338672, by decide⟩]) unmarked_context_10_1649_338673 node_context_10_1649_338673
  intro a
  fin_cases a
  · exact context_11_6596_337362
  · exact context_11_6597_337985
  · exact context_11_6598_338302
  · exact context_11_6599_338672

theorem selected_cut_12834 : selected 8 ⟨338684, by decide⟩
    (prefixPartial 13 105600) = some ⟨13, 2, 0, 338684, 105600, 833, 16384⟩ := by
  decide +kernel

theorem context_13_105600_338684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105600 ⟨338684, by decide⟩ :=
  accepted_of_selected 13 105600 ⟨338684, by decide⟩ ⟨13, 2, 0, 338684, 105600, 833, 16384⟩
    (by decide) selected_cut_12834

theorem selected_cut_12835 : selected 8 ⟨338707, by decide⟩
    (prefixPartial 13 105601) = some ⟨13, 2, 0, 338707, 105601, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_105601_338707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105601 ⟨338707, by decide⟩ :=
  accepted_of_selected 13 105601 ⟨338707, by decide⟩ ⟨13, 2, 0, 338707, 105601, 1721, 16384⟩
    (by decide) selected_cut_12835

theorem selected_cut_12836 : selected 8 ⟨338717, by decide⟩
    (prefixPartial 13 105602) = some ⟨13, 2, 0, 338717, 105602, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_105602_338717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105602 ⟨338717, by decide⟩ :=
  accepted_of_selected 13 105602 ⟨338717, by decide⟩ ⟨13, 2, 0, 338717, 105602, 1025, 16384⟩
    (by decide) selected_cut_12836

theorem selected_cut_12837 : selected 8 ⟨338728, by decide⟩
    (prefixPartial 13 105603) = some ⟨13, 2, 0, 338728, 105603, 781, 16384⟩ := by
  decide +kernel

theorem context_13_105603_338728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105603 ⟨338728, by decide⟩ :=
  accepted_of_selected 13 105603 ⟨338728, by decide⟩ ⟨13, 2, 0, 338728, 105603, 781, 16384⟩
    (by decide) selected_cut_12837

theorem unmarked_context_12_26400_338729 : frontier 9 ⟨338729, by decide⟩
    (prefixCache 12 26400) (prefixPartial 12 26400) = false := by
  decide +kernel

theorem node_context_12_26400_338729 : EJMOriginalGlobalDAGData.nodes 9 ⟨338729, by decide⟩ =
    .split (coordinate 12) (![⟨338684, by decide⟩,⟨338707, by decide⟩,⟨338717, by decide⟩,⟨338728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26400_338729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26400 ⟨338729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26400
    ⟨338729, by decide⟩ (by decide) (![⟨338684, by decide⟩,⟨338707, by decide⟩,⟨338717, by decide⟩,⟨338728, by decide⟩]) unmarked_context_12_26400_338729 node_context_12_26400_338729
  intro a
  fin_cases a
  · exact context_13_105600_338684
  · exact context_13_105601_338707
  · exact context_13_105602_338717
  · exact context_13_105603_338728

theorem selected_cut_12838 : selected 8 ⟨338741, by decide⟩
    (prefixPartial 13 105604) = some ⟨13, 2, 0, 338741, 105604, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_105604_338741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105604 ⟨338741, by decide⟩ :=
  accepted_of_selected 13 105604 ⟨338741, by decide⟩ ⟨13, 2, 0, 338741, 105604, 1221, 16384⟩
    (by decide) selected_cut_12838

theorem selected_cut_12839 : selected 8 ⟨338784, by decide⟩
    (prefixPartial 13 105605) = some ⟨13, 2, 0, 338784, 105605, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_105605_338784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105605 ⟨338784, by decide⟩ :=
  accepted_of_selected 13 105605 ⟨338784, by decide⟩ ⟨13, 2, 0, 338784, 105605, 2389, 16384⟩
    (by decide) selected_cut_12839

theorem selected_cut_12840 : selected 8 ⟨338803, by decide⟩
    (prefixPartial 13 105606) = some ⟨13, 2, 0, 338803, 105606, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_105606_338803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105606 ⟨338803, by decide⟩ :=
  accepted_of_selected 13 105606 ⟨338803, by decide⟩ ⟨13, 2, 0, 338803, 105606, 1281, 16384⟩
    (by decide) selected_cut_12840

theorem selected_cut_12841 : selected 8 ⟨338811, by decide⟩
    (prefixPartial 13 105607) = some ⟨13, 2, 0, 338811, 105607, 649, 16384⟩ := by
  decide +kernel

theorem context_13_105607_338811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105607 ⟨338811, by decide⟩ :=
  accepted_of_selected 13 105607 ⟨338811, by decide⟩ ⟨13, 2, 0, 338811, 105607, 649, 16384⟩
    (by decide) selected_cut_12841

theorem unmarked_context_12_26401_338812 : frontier 9 ⟨338812, by decide⟩
    (prefixCache 12 26401) (prefixPartial 12 26401) = false := by
  decide +kernel

theorem node_context_12_26401_338812 : EJMOriginalGlobalDAGData.nodes 9 ⟨338812, by decide⟩ =
    .split (coordinate 12) (![⟨338741, by decide⟩,⟨338784, by decide⟩,⟨338803, by decide⟩,⟨338811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26401_338812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26401 ⟨338812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26401
    ⟨338812, by decide⟩ (by decide) (![⟨338741, by decide⟩,⟨338784, by decide⟩,⟨338803, by decide⟩,⟨338811, by decide⟩]) unmarked_context_12_26401_338812 node_context_12_26401_338812
  intro a
  fin_cases a
  · exact context_13_105604_338741
  · exact context_13_105605_338784
  · exact context_13_105606_338803
  · exact context_13_105607_338811

theorem selected_cut_12842 : selected 8 ⟨338829, by decide⟩
    (prefixPartial 13 105608) = some ⟨13, 2, 0, 338829, 105608, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_105608_338829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105608 ⟨338829, by decide⟩ :=
  accepted_of_selected 13 105608 ⟨338829, by decide⟩ ⟨13, 2, 0, 338829, 105608, 1233, 16384⟩
    (by decide) selected_cut_12842

theorem selected_cut_12843 : selected 8 ⟨338861, by decide⟩
    (prefixPartial 13 105609) = some ⟨13, 2, 0, 338861, 105609, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_105609_338861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105609 ⟨338861, by decide⟩ :=
  accepted_of_selected 13 105609 ⟨338861, by decide⟩ ⟨13, 2, 0, 338861, 105609, 2197, 16384⟩
    (by decide) selected_cut_12843

theorem selected_cut_12844 : selected 8 ⟨338877, by decide⟩
    (prefixPartial 13 105610) = some ⟨13, 2, 0, 338877, 105610, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_105610_338877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105610 ⟨338877, by decide⟩ :=
  accepted_of_selected 13 105610 ⟨338877, by decide⟩ ⟨13, 2, 0, 338877, 105610, 1213, 16384⟩
    (by decide) selected_cut_12844

theorem selected_cut_12845 : selected 8 ⟨338884, by decide⟩
    (prefixPartial 13 105611) = some ⟨13, 2, 0, 338884, 105611, 709, 16384⟩ := by
  decide +kernel

theorem context_13_105611_338884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105611 ⟨338884, by decide⟩ :=
  accepted_of_selected 13 105611 ⟨338884, by decide⟩ ⟨13, 2, 0, 338884, 105611, 709, 16384⟩
    (by decide) selected_cut_12845

theorem unmarked_context_12_26402_338885 : frontier 9 ⟨338885, by decide⟩
    (prefixCache 12 26402) (prefixPartial 12 26402) = false := by
  decide +kernel

theorem node_context_12_26402_338885 : EJMOriginalGlobalDAGData.nodes 9 ⟨338885, by decide⟩ =
    .split (coordinate 12) (![⟨338829, by decide⟩,⟨338861, by decide⟩,⟨338877, by decide⟩,⟨338884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26402_338885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26402 ⟨338885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26402
    ⟨338885, by decide⟩ (by decide) (![⟨338829, by decide⟩,⟨338861, by decide⟩,⟨338877, by decide⟩,⟨338884, by decide⟩]) unmarked_context_12_26402_338885 node_context_12_26402_338885
  intro a
  fin_cases a
  · exact context_13_105608_338829
  · exact context_13_105609_338861
  · exact context_13_105610_338877
  · exact context_13_105611_338884

theorem selected_cut_12846 : selected 8 ⟨338895, by decide⟩
    (prefixPartial 13 105612) = some ⟨13, 2, 0, 338895, 105612, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_105612_338895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105612 ⟨338895, by decide⟩ :=
  accepted_of_selected 13 105612 ⟨338895, by decide⟩ ⟨13, 2, 0, 338895, 105612, 1121, 16384⟩
    (by decide) selected_cut_12846

theorem selected_cut_12847 : selected 8 ⟨338934, by decide⟩
    (prefixPartial 13 105613) = some ⟨13, 2, 0, 338934, 105613, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_105613_338934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105613 ⟨338934, by decide⟩ :=
  accepted_of_selected 13 105613 ⟨338934, by decide⟩ ⟨13, 2, 0, 338934, 105613, 2405, 16384⟩
    (by decide) selected_cut_12847

theorem selected_cut_12848 : selected 8 ⟨338952, by decide⟩
    (prefixPartial 13 105614) = some ⟨13, 2, 0, 338952, 105614, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_105614_338952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105614 ⟨338952, by decide⟩ :=
  accepted_of_selected 13 105614 ⟨338952, by decide⟩ ⟨13, 2, 0, 338952, 105614, 1225, 16384⟩
    (by decide) selected_cut_12848

theorem selected_cut_12849 : selected 8 ⟨338957, by decide⟩
    (prefixPartial 13 105615) = some ⟨13, 2, 0, 338957, 105615, 661, 16384⟩ := by
  decide +kernel

theorem context_13_105615_338957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105615 ⟨338957, by decide⟩ :=
  accepted_of_selected 13 105615 ⟨338957, by decide⟩ ⟨13, 2, 0, 338957, 105615, 661, 16384⟩
    (by decide) selected_cut_12849

theorem unmarked_context_12_26403_338958 : frontier 9 ⟨338958, by decide⟩
    (prefixCache 12 26403) (prefixPartial 12 26403) = false := by
  decide +kernel

theorem node_context_12_26403_338958 : EJMOriginalGlobalDAGData.nodes 9 ⟨338958, by decide⟩ =
    .split (coordinate 12) (![⟨338895, by decide⟩,⟨338934, by decide⟩,⟨338952, by decide⟩,⟨338957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26403_338958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26403 ⟨338958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26403
    ⟨338958, by decide⟩ (by decide) (![⟨338895, by decide⟩,⟨338934, by decide⟩,⟨338952, by decide⟩,⟨338957, by decide⟩]) unmarked_context_12_26403_338958 node_context_12_26403_338958
  intro a
  fin_cases a
  · exact context_13_105612_338895
  · exact context_13_105613_338934
  · exact context_13_105614_338952
  · exact context_13_105615_338957

theorem unmarked_context_11_6600_338959 : frontier 10 ⟨338959, by decide⟩
    (prefixCache 11 6600) (prefixPartial 11 6600) = false := by
  decide +kernel

theorem node_context_11_6600_338959 : EJMOriginalGlobalDAGData.nodes 10 ⟨338959, by decide⟩ =
    .split (coordinate 11) (![⟨338729, by decide⟩,⟨338812, by decide⟩,⟨338885, by decide⟩,⟨338958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6600_338959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6600 ⟨338959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6600
    ⟨338959, by decide⟩ (by decide) (![⟨338729, by decide⟩,⟨338812, by decide⟩,⟨338885, by decide⟩,⟨338958, by decide⟩]) unmarked_context_11_6600_338959 node_context_11_6600_338959
  intro a
  fin_cases a
  · exact context_12_26400_338729
  · exact context_12_26401_338812
  · exact context_12_26402_338885
  · exact context_12_26403_338958

theorem selected_cut_12850 : selected 8 ⟨338968, by decide⟩
    (prefixPartial 13 105616) = some ⟨13, 2, 0, 338968, 105616, 737, 16384⟩ := by
  decide +kernel

theorem context_13_105616_338968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105616 ⟨338968, by decide⟩ :=
  accepted_of_selected 13 105616 ⟨338968, by decide⟩ ⟨13, 2, 0, 338968, 105616, 737, 16384⟩
    (by decide) selected_cut_12850

theorem selected_cut_12851 : selected 8 ⟨338995, by decide⟩
    (prefixPartial 13 105617) = some ⟨13, 2, 0, 338995, 105617, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_105617_338995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105617 ⟨338995, by decide⟩ :=
  accepted_of_selected 13 105617 ⟨338995, by decide⟩ ⟨13, 2, 0, 338995, 105617, 2049, 16384⟩
    (by decide) selected_cut_12851

theorem selected_cut_12852 : selected 8 ⟨339011, by decide⟩
    (prefixPartial 13 105618) = some ⟨13, 2, 0, 339011, 105618, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_105618_339011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105618 ⟨339011, by decide⟩ :=
  accepted_of_selected 13 105618 ⟨339011, by decide⟩ ⟨13, 2, 0, 339011, 105618, 1257, 16384⟩
    (by decide) selected_cut_12852

theorem selected_cut_12853 : selected 8 ⟨339020, by decide⟩
    (prefixPartial 13 105619) = some ⟨13, 2, 0, 339020, 105619, 737, 16384⟩ := by
  decide +kernel

theorem context_13_105619_339020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105619 ⟨339020, by decide⟩ :=
  accepted_of_selected 13 105619 ⟨339020, by decide⟩ ⟨13, 2, 0, 339020, 105619, 737, 16384⟩
    (by decide) selected_cut_12853

theorem unmarked_context_12_26404_339021 : frontier 9 ⟨339021, by decide⟩
    (prefixCache 12 26404) (prefixPartial 12 26404) = false := by
  decide +kernel

theorem node_context_12_26404_339021 : EJMOriginalGlobalDAGData.nodes 9 ⟨339021, by decide⟩ =
    .split (coordinate 12) (![⟨338968, by decide⟩,⟨338995, by decide⟩,⟨339011, by decide⟩,⟨339020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26404_339021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26404 ⟨339021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26404
    ⟨339021, by decide⟩ (by decide) (![⟨338968, by decide⟩,⟨338995, by decide⟩,⟨339011, by decide⟩,⟨339020, by decide⟩]) unmarked_context_12_26404_339021 node_context_12_26404_339021
  intro a
  fin_cases a
  · exact context_13_105616_338968
  · exact context_13_105617_338995
  · exact context_13_105618_339011
  · exact context_13_105619_339020

theorem selected_cut_12854 : selected 8 ⟨339030, by decide⟩
    (prefixPartial 13 105620) = some ⟨13, 2, 0, 339030, 105620, 849, 16384⟩ := by
  decide +kernel

theorem context_13_105620_339030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105620 ⟨339030, by decide⟩ :=
  accepted_of_selected 13 105620 ⟨339030, by decide⟩ ⟨13, 2, 0, 339030, 105620, 849, 16384⟩
    (by decide) selected_cut_12854

theorem selected_cut_12855 : selected 8 ⟨339067, by decide⟩
    (prefixPartial 13 105621) = some ⟨13, 2, 0, 339067, 105621, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_105621_339067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105621 ⟨339067, by decide⟩ :=
  accepted_of_selected 13 105621 ⟨339067, by decide⟩ ⟨13, 2, 0, 339067, 105621, 2461, 16384⟩
    (by decide) selected_cut_12855

theorem selected_cut_12856 : selected 8 ⟨339084, by decide⟩
    (prefixPartial 13 105622) = some ⟨13, 2, 0, 339084, 105622, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_105622_339084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105622 ⟨339084, by decide⟩ :=
  accepted_of_selected 13 105622 ⟨339084, by decide⟩ ⟨13, 2, 0, 339084, 105622, 1313, 16384⟩
    (by decide) selected_cut_12856

theorem selected_cut_12857 : selected 8 ⟨339091, by decide⟩
    (prefixPartial 13 105623) = some ⟨13, 2, 0, 339091, 105623, 677, 16384⟩ := by
  decide +kernel

theorem context_13_105623_339091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105623 ⟨339091, by decide⟩ :=
  accepted_of_selected 13 105623 ⟨339091, by decide⟩ ⟨13, 2, 0, 339091, 105623, 677, 16384⟩
    (by decide) selected_cut_12857

theorem unmarked_context_12_26405_339092 : frontier 9 ⟨339092, by decide⟩
    (prefixCache 12 26405) (prefixPartial 12 26405) = false := by
  decide +kernel

theorem node_context_12_26405_339092 : EJMOriginalGlobalDAGData.nodes 9 ⟨339092, by decide⟩ =
    .split (coordinate 12) (![⟨339030, by decide⟩,⟨339067, by decide⟩,⟨339084, by decide⟩,⟨339091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26405_339092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26405 ⟨339092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26405
    ⟨339092, by decide⟩ (by decide) (![⟨339030, by decide⟩,⟨339067, by decide⟩,⟨339084, by decide⟩,⟨339091, by decide⟩]) unmarked_context_12_26405_339092 node_context_12_26405_339092
  intro a
  fin_cases a
  · exact context_13_105620_339030
  · exact context_13_105621_339067
  · exact context_13_105622_339084
  · exact context_13_105623_339091

theorem selected_cut_12858 : selected 8 ⟨339101, by decide⟩
    (prefixPartial 13 105624) = some ⟨13, 2, 0, 339101, 105624, 857, 16384⟩ := by
  decide +kernel

theorem context_13_105624_339101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105624 ⟨339101, by decide⟩ :=
  accepted_of_selected 13 105624 ⟨339101, by decide⟩ ⟨13, 2, 0, 339101, 105624, 857, 16384⟩
    (by decide) selected_cut_12858

theorem selected_cut_12859 : selected 8 ⟨339136, by decide⟩
    (prefixPartial 13 105625) = some ⟨13, 2, 0, 339136, 105625, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_105625_339136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105625 ⟨339136, by decide⟩ :=
  accepted_of_selected 13 105625 ⟨339136, by decide⟩ ⟨13, 2, 0, 339136, 105625, 2321, 16384⟩
    (by decide) selected_cut_12859

theorem selected_cut_12860 : selected 8 ⟨339152, by decide⟩
    (prefixPartial 13 105626) = some ⟨13, 2, 0, 339152, 105626, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_105626_339152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105626 ⟨339152, by decide⟩ :=
  accepted_of_selected 13 105626 ⟨339152, by decide⟩ ⟨13, 2, 0, 339152, 105626, 1233, 16384⟩
    (by decide) selected_cut_12860

theorem selected_cut_12861 : selected 8 ⟨339160, by decide⟩
    (prefixPartial 13 105627) = some ⟨13, 2, 0, 339160, 105627, 809, 16384⟩ := by
  decide +kernel

theorem context_13_105627_339160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105627 ⟨339160, by decide⟩ :=
  accepted_of_selected 13 105627 ⟨339160, by decide⟩ ⟨13, 2, 0, 339160, 105627, 809, 16384⟩
    (by decide) selected_cut_12861

theorem unmarked_context_12_26406_339161 : frontier 9 ⟨339161, by decide⟩
    (prefixCache 12 26406) (prefixPartial 12 26406) = false := by
  decide +kernel

theorem node_context_12_26406_339161 : EJMOriginalGlobalDAGData.nodes 9 ⟨339161, by decide⟩ =
    .split (coordinate 12) (![⟨339101, by decide⟩,⟨339136, by decide⟩,⟨339152, by decide⟩,⟨339160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26406_339161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26406 ⟨339161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26406
    ⟨339161, by decide⟩ (by decide) (![⟨339101, by decide⟩,⟨339136, by decide⟩,⟨339152, by decide⟩,⟨339160, by decide⟩]) unmarked_context_12_26406_339161 node_context_12_26406_339161
  intro a
  fin_cases a
  · exact context_13_105624_339101
  · exact context_13_105625_339136
  · exact context_13_105626_339152
  · exact context_13_105627_339160

theorem selected_cut_12862 : selected 8 ⟨339171, by decide⟩
    (prefixPartial 13 105628) = some ⟨13, 2, 0, 339171, 105628, 785, 16384⟩ := by
  decide +kernel

theorem context_13_105628_339171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105628 ⟨339171, by decide⟩ :=
  accepted_of_selected 13 105628 ⟨339171, by decide⟩ ⟨13, 2, 0, 339171, 105628, 785, 16384⟩
    (by decide) selected_cut_12862

theorem selected_cut_12863 : selected 8 ⟨339203, by decide⟩
    (prefixPartial 13 105629) = some ⟨13, 2, 0, 339203, 105629, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_105629_339203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105629 ⟨339203, by decide⟩ :=
  accepted_of_selected 13 105629 ⟨339203, by decide⟩ ⟨13, 2, 0, 339203, 105629, 2341, 16384⟩
    (by decide) selected_cut_12863

theorem selected_cut_12864 : selected 8 ⟨339219, by decide⟩
    (prefixPartial 13 105630) = some ⟨13, 2, 0, 339219, 105630, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_105630_339219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105630 ⟨339219, by decide⟩ :=
  accepted_of_selected 13 105630 ⟨339219, by decide⟩ ⟨13, 2, 0, 339219, 105630, 1337, 16384⟩
    (by decide) selected_cut_12864

theorem selected_cut_12865 : selected 8 ⟨339226, by decide⟩
    (prefixPartial 13 105631) = some ⟨13, 2, 0, 339226, 105631, 701, 16384⟩ := by
  decide +kernel

theorem context_13_105631_339226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105631 ⟨339226, by decide⟩ :=
  accepted_of_selected 13 105631 ⟨339226, by decide⟩ ⟨13, 2, 0, 339226, 105631, 701, 16384⟩
    (by decide) selected_cut_12865

theorem unmarked_context_12_26407_339227 : frontier 9 ⟨339227, by decide⟩
    (prefixCache 12 26407) (prefixPartial 12 26407) = false := by
  decide +kernel

theorem node_context_12_26407_339227 : EJMOriginalGlobalDAGData.nodes 9 ⟨339227, by decide⟩ =
    .split (coordinate 12) (![⟨339171, by decide⟩,⟨339203, by decide⟩,⟨339219, by decide⟩,⟨339226, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26407_339227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26407 ⟨339227, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26407
    ⟨339227, by decide⟩ (by decide) (![⟨339171, by decide⟩,⟨339203, by decide⟩,⟨339219, by decide⟩,⟨339226, by decide⟩]) unmarked_context_12_26407_339227 node_context_12_26407_339227
  intro a
  fin_cases a
  · exact context_13_105628_339171
  · exact context_13_105629_339203
  · exact context_13_105630_339219
  · exact context_13_105631_339226

theorem unmarked_context_11_6601_339228 : frontier 10 ⟨339228, by decide⟩
    (prefixCache 11 6601) (prefixPartial 11 6601) = false := by
  decide +kernel

theorem node_context_11_6601_339228 : EJMOriginalGlobalDAGData.nodes 10 ⟨339228, by decide⟩ =
    .split (coordinate 11) (![⟨339021, by decide⟩,⟨339092, by decide⟩,⟨339161, by decide⟩,⟨339227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6601_339228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6601 ⟨339228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6601
    ⟨339228, by decide⟩ (by decide) (![⟨339021, by decide⟩,⟨339092, by decide⟩,⟨339161, by decide⟩,⟨339227, by decide⟩]) unmarked_context_11_6601_339228 node_context_11_6601_339228
  intro a
  fin_cases a
  · exact context_12_26404_339021
  · exact context_12_26405_339092
  · exact context_12_26406_339161
  · exact context_12_26407_339227

theorem selected_cut_12866 : selected 8 ⟨339237, by decide⟩
    (prefixPartial 13 105632) = some ⟨13, 2, 0, 339237, 105632, 653, 16384⟩ := by
  decide +kernel

theorem context_13_105632_339237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105632 ⟨339237, by decide⟩ :=
  accepted_of_selected 13 105632 ⟨339237, by decide⟩ ⟨13, 2, 0, 339237, 105632, 653, 16384⟩
    (by decide) selected_cut_12866

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
