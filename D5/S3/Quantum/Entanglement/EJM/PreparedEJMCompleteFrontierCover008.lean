/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover007
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00770 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6488) = some ⟨13, 1, 0, 3444, 6488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6488, 1, 16384⟩
    (by decide) selected_cut_00770

theorem selected_cut_00771 : selected 8 ⟨31056, by decide⟩
    (prefixPartial 13 6489) = some ⟨13, 2, 0, 31056, 6489, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_6489_31056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6489 ⟨31056, by decide⟩ :=
  accepted_of_selected 13 6489 ⟨31056, by decide⟩ ⟨13, 2, 0, 31056, 6489, 2649, 16384⟩
    (by decide) selected_cut_00771

theorem selected_cut_00772 : selected 8 ⟨31105, by decide⟩
    (prefixPartial 13 6490) = some ⟨13, 2, 0, 31105, 6490, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_6490_31105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6490 ⟨31105, by decide⟩ :=
  accepted_of_selected 13 6490 ⟨31105, by decide⟩ ⟨13, 2, 0, 31105, 6490, 1897, 16384⟩
    (by decide) selected_cut_00772

theorem selected_cut_00773 : selected 8 ⟨31129, by decide⟩
    (prefixPartial 13 6491) = some ⟨13, 2, 0, 31129, 6491, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_6491_31129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6491 ⟨31129, by decide⟩ :=
  accepted_of_selected 13 6491 ⟨31129, by decide⟩ ⟨13, 2, 0, 31129, 6491, 1553, 16384⟩
    (by decide) selected_cut_00773

theorem unmarked_context_12_1622_31130 : frontier 9 ⟨31130, by decide⟩
    (prefixCache 12 1622) (prefixPartial 12 1622) = false := by
  decide +kernel

theorem node_context_12_1622_31130 : EJMOriginalGlobalDAGData.nodes 9 ⟨31130, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨31056, by decide⟩,⟨31105, by decide⟩,⟨31129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1622_31130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1622 ⟨31130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1622
    ⟨31130, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨31056, by decide⟩,⟨31105, by decide⟩,⟨31129, by decide⟩]) unmarked_context_12_1622_31130 node_context_12_1622_31130
  intro a
  fin_cases a
  · exact context_13_6488_3444
  · exact context_13_6489_31056
  · exact context_13_6490_31105
  · exact context_13_6491_31129

theorem selected_cut_00774 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6492) = some ⟨13, 1, 0, 3444, 6492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6492, 1, 16384⟩
    (by decide) selected_cut_00774

theorem selected_cut_00775 : selected 8 ⟨31189, by decide⟩
    (prefixPartial 13 6493) = some ⟨13, 2, 0, 31189, 6493, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_6493_31189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6493 ⟨31189, by decide⟩ :=
  accepted_of_selected 13 6493 ⟨31189, by decide⟩ ⟨13, 2, 0, 31189, 6493, 2837, 16384⟩
    (by decide) selected_cut_00775

theorem selected_cut_00776 : selected 8 ⟨31258, by decide⟩
    (prefixPartial 13 6494) = some ⟨13, 2, 0, 31258, 6494, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_6494_31258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6494 ⟨31258, by decide⟩ :=
  accepted_of_selected 13 6494 ⟨31258, by decide⟩ ⟨13, 2, 0, 31258, 6494, 2153, 16384⟩
    (by decide) selected_cut_00776

theorem selected_cut_00777 : selected 8 ⟨31301, by decide⟩
    (prefixPartial 13 6495) = some ⟨13, 2, 0, 31301, 6495, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_6495_31301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6495 ⟨31301, by decide⟩ :=
  accepted_of_selected 13 6495 ⟨31301, by decide⟩ ⟨13, 2, 0, 31301, 6495, 1685, 16384⟩
    (by decide) selected_cut_00777

theorem unmarked_context_12_1623_31302 : frontier 9 ⟨31302, by decide⟩
    (prefixCache 12 1623) (prefixPartial 12 1623) = false := by
  decide +kernel

theorem node_context_12_1623_31302 : EJMOriginalGlobalDAGData.nodes 9 ⟨31302, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨31189, by decide⟩,⟨31258, by decide⟩,⟨31301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1623_31302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1623 ⟨31302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1623
    ⟨31302, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨31189, by decide⟩,⟨31258, by decide⟩,⟨31301, by decide⟩]) unmarked_context_12_1623_31302 node_context_12_1623_31302
  intro a
  fin_cases a
  · exact context_13_6492_3444
  · exact context_13_6493_31189
  · exact context_13_6494_31258
  · exact context_13_6495_31301

theorem unmarked_context_11_405_31303 : frontier 10 ⟨31303, by decide⟩
    (prefixCache 11 405) (prefixPartial 11 405) = false := by
  decide +kernel

theorem node_context_11_405_31303 : EJMOriginalGlobalDAGData.nodes 10 ⟨31303, by decide⟩ =
    .split (coordinate 11) (![⟨30872, by decide⟩,⟨31006, by decide⟩,⟨31130, by decide⟩,⟨31302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_405_31303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 405 ⟨31303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 405
    ⟨31303, by decide⟩ (by decide) (![⟨30872, by decide⟩,⟨31006, by decide⟩,⟨31130, by decide⟩,⟨31302, by decide⟩]) unmarked_context_11_405_31303 node_context_11_405_31303
  intro a
  fin_cases a
  · exact context_12_1620_30872
  · exact context_12_1621_31006
  · exact context_12_1622_31130
  · exact context_12_1623_31302

theorem selected_cut_00778 : selected 9 ⟨31354, by decide⟩
    (prefixPartial 12 1624) = some ⟨12, 2, 0, 31354, 1624, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_1624_31354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1624 ⟨31354, by decide⟩ :=
  accepted_of_selected 12 1624 ⟨31354, by decide⟩ ⟨12, 2, 0, 31354, 1624, 3981, 65536⟩
    (by decide) selected_cut_00778

theorem selected_cut_00779 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6500) = some ⟨13, 1, 0, 3444, 6500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6500, 1, 16384⟩
    (by decide) selected_cut_00779

theorem selected_cut_00780 : selected 8 ⟨31377, by decide⟩
    (prefixPartial 13 6501) = some ⟨13, 2, 0, 31377, 6501, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_6501_31377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6501 ⟨31377, by decide⟩ :=
  accepted_of_selected 13 6501 ⟨31377, by decide⟩ ⟨13, 2, 0, 31377, 6501, 1501, 16384⟩
    (by decide) selected_cut_00780

theorem selected_cut_00781 : selected 8 ⟨31403, by decide⟩
    (prefixPartial 13 6502) = some ⟨13, 2, 0, 31403, 6502, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_6502_31403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6502 ⟨31403, by decide⟩ :=
  accepted_of_selected 13 6502 ⟨31403, by decide⟩ ⟨13, 2, 0, 31403, 6502, 1413, 16384⟩
    (by decide) selected_cut_00781

theorem selected_cut_00782 : selected 8 ⟨31420, by decide⟩
    (prefixPartial 13 6503) = some ⟨13, 2, 0, 31420, 6503, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_6503_31420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6503 ⟨31420, by decide⟩ :=
  accepted_of_selected 13 6503 ⟨31420, by decide⟩ ⟨13, 2, 0, 31420, 6503, 1253, 16384⟩
    (by decide) selected_cut_00782

theorem unmarked_context_12_1625_31421 : frontier 9 ⟨31421, by decide⟩
    (prefixCache 12 1625) (prefixPartial 12 1625) = false := by
  decide +kernel

theorem node_context_12_1625_31421 : EJMOriginalGlobalDAGData.nodes 9 ⟨31421, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨31377, by decide⟩,⟨31403, by decide⟩,⟨31420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1625_31421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1625 ⟨31421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1625
    ⟨31421, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨31377, by decide⟩,⟨31403, by decide⟩,⟨31420, by decide⟩]) unmarked_context_12_1625_31421 node_context_12_1625_31421
  intro a
  fin_cases a
  · exact context_13_6500_3444
  · exact context_13_6501_31377
  · exact context_13_6502_31403
  · exact context_13_6503_31420

theorem selected_cut_00783 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6504) = some ⟨13, 1, 0, 3444, 6504, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6504_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6504 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6504 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6504, 1, 16384⟩
    (by decide) selected_cut_00783

theorem selected_cut_00784 : selected 8 ⟨31463, by decide⟩
    (prefixPartial 13 6505) = some ⟨13, 2, 0, 31463, 6505, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_6505_31463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6505 ⟨31463, by decide⟩ :=
  accepted_of_selected 13 6505 ⟨31463, by decide⟩ ⟨13, 2, 0, 31463, 6505, 2273, 16384⟩
    (by decide) selected_cut_00784

theorem selected_cut_00785 : selected 8 ⟨31528, by decide⟩
    (prefixPartial 13 6506) = some ⟨13, 2, 0, 31528, 6506, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_6506_31528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6506 ⟨31528, by decide⟩ :=
  accepted_of_selected 13 6506 ⟨31528, by decide⟩ ⟨13, 2, 0, 31528, 6506, 1981, 16384⟩
    (by decide) selected_cut_00785

theorem selected_cut_00786 : selected 8 ⟨31558, by decide⟩
    (prefixPartial 13 6507) = some ⟨13, 2, 0, 31558, 6507, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_6507_31558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6507 ⟨31558, by decide⟩ :=
  accepted_of_selected 13 6507 ⟨31558, by decide⟩ ⟨13, 2, 0, 31558, 6507, 1561, 16384⟩
    (by decide) selected_cut_00786

theorem unmarked_context_12_1626_31559 : frontier 9 ⟨31559, by decide⟩
    (prefixCache 12 1626) (prefixPartial 12 1626) = false := by
  decide +kernel

theorem node_context_12_1626_31559 : EJMOriginalGlobalDAGData.nodes 9 ⟨31559, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨31463, by decide⟩,⟨31528, by decide⟩,⟨31558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1626_31559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1626 ⟨31559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1626
    ⟨31559, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨31463, by decide⟩,⟨31528, by decide⟩,⟨31558, by decide⟩]) unmarked_context_12_1626_31559 node_context_12_1626_31559
  intro a
  fin_cases a
  · exact context_13_6504_3444
  · exact context_13_6505_31463
  · exact context_13_6506_31528
  · exact context_13_6507_31558

theorem selected_cut_00787 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6508) = some ⟨13, 1, 0, 3444, 6508, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6508_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6508 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6508 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6508, 1, 16384⟩
    (by decide) selected_cut_00787

theorem selected_cut_00788 : selected 8 ⟨31580, by decide⟩
    (prefixPartial 13 6509) = some ⟨13, 2, 0, 31580, 6509, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_6509_31580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6509 ⟨31580, by decide⟩ :=
  accepted_of_selected 13 6509 ⟨31580, by decide⟩ ⟨13, 2, 0, 31580, 6509, 1497, 16384⟩
    (by decide) selected_cut_00788

theorem selected_cut_00789 : selected 8 ⟨31607, by decide⟩
    (prefixPartial 13 6510) = some ⟨13, 2, 0, 31607, 6510, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_6510_31607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6510 ⟨31607, by decide⟩ :=
  accepted_of_selected 13 6510 ⟨31607, by decide⟩ ⟨13, 2, 0, 31607, 6510, 1345, 16384⟩
    (by decide) selected_cut_00789

theorem selected_cut_00790 : selected 8 ⟨31626, by decide⟩
    (prefixPartial 13 6511) = some ⟨13, 2, 0, 31626, 6511, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_6511_31626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6511 ⟨31626, by decide⟩ :=
  accepted_of_selected 13 6511 ⟨31626, by decide⟩ ⟨13, 2, 0, 31626, 6511, 1285, 16384⟩
    (by decide) selected_cut_00790

theorem unmarked_context_12_1627_31627 : frontier 9 ⟨31627, by decide⟩
    (prefixCache 12 1627) (prefixPartial 12 1627) = false := by
  decide +kernel

theorem node_context_12_1627_31627 : EJMOriginalGlobalDAGData.nodes 9 ⟨31627, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨31580, by decide⟩,⟨31607, by decide⟩,⟨31626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1627_31627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1627 ⟨31627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1627
    ⟨31627, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨31580, by decide⟩,⟨31607, by decide⟩,⟨31626, by decide⟩]) unmarked_context_12_1627_31627 node_context_12_1627_31627
  intro a
  fin_cases a
  · exact context_13_6508_3444
  · exact context_13_6509_31580
  · exact context_13_6510_31607
  · exact context_13_6511_31626

theorem unmarked_context_11_406_31628 : frontier 10 ⟨31628, by decide⟩
    (prefixCache 11 406) (prefixPartial 11 406) = false := by
  decide +kernel

theorem node_context_11_406_31628 : EJMOriginalGlobalDAGData.nodes 10 ⟨31628, by decide⟩ =
    .split (coordinate 11) (![⟨31354, by decide⟩,⟨31421, by decide⟩,⟨31559, by decide⟩,⟨31627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_406_31628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 406 ⟨31628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 406
    ⟨31628, by decide⟩ (by decide) (![⟨31354, by decide⟩,⟨31421, by decide⟩,⟨31559, by decide⟩,⟨31627, by decide⟩]) unmarked_context_11_406_31628 node_context_11_406_31628
  intro a
  fin_cases a
  · exact context_12_1624_31354
  · exact context_12_1625_31421
  · exact context_12_1626_31559
  · exact context_12_1627_31627

theorem selected_cut_00791 : selected 9 ⟨31689, by decide⟩
    (prefixPartial 12 1628) = some ⟨12, 2, 0, 31689, 1628, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_1628_31689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1628 ⟨31689, by decide⟩ :=
  accepted_of_selected 12 1628 ⟨31689, by decide⟩ ⟨12, 2, 0, 31689, 1628, 3941, 65536⟩
    (by decide) selected_cut_00791

theorem selected_cut_00792 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 6516) = some ⟨13, 1, 0, 3444, 6516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_6516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 6516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 6516, 1, 16384⟩
    (by decide) selected_cut_00792

theorem selected_cut_00793 : selected 8 ⟨31726, by decide⟩
    (prefixPartial 13 6517) = some ⟨13, 2, 0, 31726, 6517, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_6517_31726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6517 ⟨31726, by decide⟩ :=
  accepted_of_selected 13 6517 ⟨31726, by decide⟩ ⟨13, 2, 0, 31726, 6517, 1613, 16384⟩
    (by decide) selected_cut_00793

theorem selected_cut_00794 : selected 8 ⟨31756, by decide⟩
    (prefixPartial 13 6518) = some ⟨13, 2, 0, 31756, 6518, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_6518_31756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6518 ⟨31756, by decide⟩ :=
  accepted_of_selected 13 6518 ⟨31756, by decide⟩ ⟨13, 2, 0, 31756, 6518, 1333, 16384⟩
    (by decide) selected_cut_00794

theorem selected_cut_00795 : selected 8 ⟨31775, by decide⟩
    (prefixPartial 13 6519) = some ⟨13, 2, 0, 31775, 6519, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_6519_31775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6519 ⟨31775, by decide⟩ :=
  accepted_of_selected 13 6519 ⟨31775, by decide⟩ ⟨13, 2, 0, 31775, 6519, 1297, 16384⟩
    (by decide) selected_cut_00795

theorem unmarked_context_12_1629_31776 : frontier 9 ⟨31776, by decide⟩
    (prefixCache 12 1629) (prefixPartial 12 1629) = false := by
  decide +kernel

theorem node_context_12_1629_31776 : EJMOriginalGlobalDAGData.nodes 9 ⟨31776, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨31726, by decide⟩,⟨31756, by decide⟩,⟨31775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1629_31776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1629 ⟨31776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1629
    ⟨31776, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨31726, by decide⟩,⟨31756, by decide⟩,⟨31775, by decide⟩]) unmarked_context_12_1629_31776 node_context_12_1629_31776
  intro a
  fin_cases a
  · exact context_13_6516_3444
  · exact context_13_6517_31726
  · exact context_13_6518_31756
  · exact context_13_6519_31775

theorem selected_cut_00796 : selected 9 ⟨31844, by decide⟩
    (prefixPartial 12 1630) = some ⟨12, 2, 0, 31844, 1630, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_1630_31844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1630 ⟨31844, by decide⟩ :=
  accepted_of_selected 12 1630 ⟨31844, by decide⟩ ⟨12, 2, 0, 31844, 1630, 3833, 65536⟩
    (by decide) selected_cut_00796

theorem selected_cut_00797 : selected 9 ⟨31906, by decide⟩
    (prefixPartial 12 1631) = some ⟨12, 2, 0, 31906, 1631, 3709, 65536⟩ := by
  decide +kernel

theorem context_12_1631_31906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1631 ⟨31906, by decide⟩ :=
  accepted_of_selected 12 1631 ⟨31906, by decide⟩ ⟨12, 2, 0, 31906, 1631, 3709, 65536⟩
    (by decide) selected_cut_00797

theorem unmarked_context_11_407_31907 : frontier 10 ⟨31907, by decide⟩
    (prefixCache 11 407) (prefixPartial 11 407) = false := by
  decide +kernel

theorem node_context_11_407_31907 : EJMOriginalGlobalDAGData.nodes 10 ⟨31907, by decide⟩ =
    .split (coordinate 11) (![⟨31689, by decide⟩,⟨31776, by decide⟩,⟨31844, by decide⟩,⟨31906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_407_31907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 407 ⟨31907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 407
    ⟨31907, by decide⟩ (by decide) (![⟨31689, by decide⟩,⟨31776, by decide⟩,⟨31844, by decide⟩,⟨31906, by decide⟩]) unmarked_context_11_407_31907 node_context_11_407_31907
  intro a
  fin_cases a
  · exact context_12_1628_31689
  · exact context_12_1629_31776
  · exact context_12_1630_31844
  · exact context_12_1631_31906

theorem unmarked_context_10_101_31908 : frontier 11 ⟨31908, by decide⟩
    (prefixCache 10 101) (prefixPartial 10 101) = false := by
  decide +kernel

theorem node_context_10_101_31908 : EJMOriginalGlobalDAGData.nodes 11 ⟨31908, by decide⟩ =
    .split (coordinate 10) (![⟨30717, by decide⟩,⟨31303, by decide⟩,⟨31628, by decide⟩,⟨31907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_101_31908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 101 ⟨31908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 101
    ⟨31908, by decide⟩ (by decide) (![⟨30717, by decide⟩,⟨31303, by decide⟩,⟨31628, by decide⟩,⟨31907, by decide⟩]) unmarked_context_10_101_31908 node_context_10_101_31908
  intro a
  fin_cases a
  · exact context_11_404_30717
  · exact context_11_405_31303
  · exact context_11_406_31628
  · exact context_11_407_31907

theorem selected_cut_00798 : selected 9 ⟨31959, by decide⟩
    (prefixPartial 12 1632) = some ⟨12, 2, 0, 31959, 1632, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_1632_31959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1632 ⟨31959, by decide⟩ :=
  accepted_of_selected 12 1632 ⟨31959, by decide⟩ ⟨12, 2, 0, 31959, 1632, 3213, 65536⟩
    (by decide) selected_cut_00798

theorem selected_cut_00799 : selected 9 ⟨32017, by decide⟩
    (prefixPartial 12 1633) = some ⟨12, 2, 0, 32017, 1633, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_1633_32017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1633 ⟨32017, by decide⟩ :=
  accepted_of_selected 12 1633 ⟨32017, by decide⟩ ⟨12, 2, 0, 32017, 1633, 3009, 65536⟩
    (by decide) selected_cut_00799

theorem selected_cut_00800 : selected 9 ⟨32068, by decide⟩
    (prefixPartial 12 1634) = some ⟨12, 2, 0, 32068, 1634, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_1634_32068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1634 ⟨32068, by decide⟩ :=
  accepted_of_selected 12 1634 ⟨32068, by decide⟩ ⟨12, 2, 0, 32068, 1634, 2961, 65536⟩
    (by decide) selected_cut_00800

theorem selected_cut_00801 : selected 9 ⟨32120, by decide⟩
    (prefixPartial 12 1635) = some ⟨12, 2, 0, 32120, 1635, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_1635_32120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1635 ⟨32120, by decide⟩ :=
  accepted_of_selected 12 1635 ⟨32120, by decide⟩ ⟨12, 2, 0, 32120, 1635, 3101, 65536⟩
    (by decide) selected_cut_00801

theorem unmarked_context_11_408_32121 : frontier 10 ⟨32121, by decide⟩
    (prefixCache 11 408) (prefixPartial 11 408) = false := by
  decide +kernel

theorem node_context_11_408_32121 : EJMOriginalGlobalDAGData.nodes 10 ⟨32121, by decide⟩ =
    .split (coordinate 11) (![⟨31959, by decide⟩,⟨32017, by decide⟩,⟨32068, by decide⟩,⟨32120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_408_32121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 408 ⟨32121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 408
    ⟨32121, by decide⟩ (by decide) (![⟨31959, by decide⟩,⟨32017, by decide⟩,⟨32068, by decide⟩,⟨32120, by decide⟩]) unmarked_context_11_408_32121 node_context_11_408_32121
  intro a
  fin_cases a
  · exact context_12_1632_31959
  · exact context_12_1633_32017
  · exact context_12_1634_32068
  · exact context_12_1635_32120

theorem selected_cut_00802 : selected 9 ⟨32171, by decide⟩
    (prefixPartial 12 1636) = some ⟨12, 2, 0, 32171, 1636, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_1636_32171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1636 ⟨32171, by decide⟩ :=
  accepted_of_selected 12 1636 ⟨32171, by decide⟩ ⟨12, 2, 0, 32171, 1636, 3085, 65536⟩
    (by decide) selected_cut_00802

theorem selected_cut_00803 : selected 9 ⟨32224, by decide⟩
    (prefixPartial 12 1637) = some ⟨12, 2, 0, 32224, 1637, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_1637_32224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1637 ⟨32224, by decide⟩ :=
  accepted_of_selected 12 1637 ⟨32224, by decide⟩ ⟨12, 2, 0, 32224, 1637, 2905, 65536⟩
    (by decide) selected_cut_00803

theorem selected_cut_00804 : selected 9 ⟨32278, by decide⟩
    (prefixPartial 12 1638) = some ⟨12, 2, 0, 32278, 1638, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_1638_32278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1638 ⟨32278, by decide⟩ :=
  accepted_of_selected 12 1638 ⟨32278, by decide⟩ ⟨12, 2, 0, 32278, 1638, 3337, 65536⟩
    (by decide) selected_cut_00804

theorem selected_cut_00805 : selected 9 ⟨32351, by decide⟩
    (prefixPartial 12 1639) = some ⟨12, 2, 0, 32351, 1639, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_1639_32351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1639 ⟨32351, by decide⟩ :=
  accepted_of_selected 12 1639 ⟨32351, by decide⟩ ⟨12, 2, 0, 32351, 1639, 3445, 65536⟩
    (by decide) selected_cut_00805

theorem unmarked_context_11_409_32352 : frontier 10 ⟨32352, by decide⟩
    (prefixCache 11 409) (prefixPartial 11 409) = false := by
  decide +kernel

theorem node_context_11_409_32352 : EJMOriginalGlobalDAGData.nodes 10 ⟨32352, by decide⟩ =
    .split (coordinate 11) (![⟨32171, by decide⟩,⟨32224, by decide⟩,⟨32278, by decide⟩,⟨32351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_409_32352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 409 ⟨32352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 409
    ⟨32352, by decide⟩ (by decide) (![⟨32171, by decide⟩,⟨32224, by decide⟩,⟨32278, by decide⟩,⟨32351, by decide⟩]) unmarked_context_11_409_32352 node_context_11_409_32352
  intro a
  fin_cases a
  · exact context_12_1636_32171
  · exact context_12_1637_32224
  · exact context_12_1638_32278
  · exact context_12_1639_32351

theorem selected_cut_00806 : selected 9 ⟨32398, by decide⟩
    (prefixPartial 12 1640) = some ⟨12, 2, 0, 32398, 1640, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_1640_32398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1640 ⟨32398, by decide⟩ :=
  accepted_of_selected 12 1640 ⟨32398, by decide⟩ ⟨12, 2, 0, 32398, 1640, 2709, 65536⟩
    (by decide) selected_cut_00806

theorem selected_cut_00807 : selected 9 ⟨32451, by decide⟩
    (prefixPartial 12 1641) = some ⟨12, 2, 0, 32451, 1641, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_1641_32451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1641 ⟨32451, by decide⟩ :=
  accepted_of_selected 12 1641 ⟨32451, by decide⟩ ⟨12, 2, 0, 32451, 1641, 2849, 65536⟩
    (by decide) selected_cut_00807

theorem selected_cut_00808 : selected 9 ⟨32550, by decide⟩
    (prefixPartial 12 1642) = some ⟨12, 2, 0, 32550, 1642, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_1642_32550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1642 ⟨32550, by decide⟩ :=
  accepted_of_selected 12 1642 ⟨32550, by decide⟩ ⟨12, 2, 0, 32550, 1642, 3829, 65536⟩
    (by decide) selected_cut_00808

theorem selected_cut_00809 : selected 9 ⟨32600, by decide⟩
    (prefixPartial 12 1643) = some ⟨12, 2, 0, 32600, 1643, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_1643_32600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1643 ⟨32600, by decide⟩ :=
  accepted_of_selected 12 1643 ⟨32600, by decide⟩ ⟨12, 2, 0, 32600, 1643, 2877, 65536⟩
    (by decide) selected_cut_00809

theorem unmarked_context_11_410_32601 : frontier 10 ⟨32601, by decide⟩
    (prefixCache 11 410) (prefixPartial 11 410) = false := by
  decide +kernel

theorem node_context_11_410_32601 : EJMOriginalGlobalDAGData.nodes 10 ⟨32601, by decide⟩ =
    .split (coordinate 11) (![⟨32398, by decide⟩,⟨32451, by decide⟩,⟨32550, by decide⟩,⟨32600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_410_32601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 410 ⟨32601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 410
    ⟨32601, by decide⟩ (by decide) (![⟨32398, by decide⟩,⟨32451, by decide⟩,⟨32550, by decide⟩,⟨32600, by decide⟩]) unmarked_context_11_410_32601 node_context_11_410_32601
  intro a
  fin_cases a
  · exact context_12_1640_32398
  · exact context_12_1641_32451
  · exact context_12_1642_32550
  · exact context_12_1643_32600

theorem selected_cut_00810 : selected 9 ⟨32661, by decide⟩
    (prefixPartial 12 1644) = some ⟨12, 2, 0, 32661, 1644, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_1644_32661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1644 ⟨32661, by decide⟩ :=
  accepted_of_selected 12 1644 ⟨32661, by decide⟩ ⟨12, 2, 0, 32661, 1644, 2945, 65536⟩
    (by decide) selected_cut_00810

theorem selected_cut_00811 : selected 9 ⟨32736, by decide⟩
    (prefixPartial 12 1645) = some ⟨12, 2, 0, 32736, 1645, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_1645_32736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1645 ⟨32736, by decide⟩ :=
  accepted_of_selected 12 1645 ⟨32736, by decide⟩ ⟨12, 2, 0, 32736, 1645, 3129, 65536⟩
    (by decide) selected_cut_00811

theorem selected_cut_00812 : selected 9 ⟨32797, by decide⟩
    (prefixPartial 12 1646) = some ⟨12, 2, 0, 32797, 1646, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_1646_32797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1646 ⟨32797, by decide⟩ :=
  accepted_of_selected 12 1646 ⟨32797, by decide⟩ ⟨12, 2, 0, 32797, 1646, 2909, 65536⟩
    (by decide) selected_cut_00812

theorem selected_cut_00813 : selected 9 ⟨32857, by decide⟩
    (prefixPartial 12 1647) = some ⟨12, 2, 0, 32857, 1647, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_1647_32857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1647 ⟨32857, by decide⟩ :=
  accepted_of_selected 12 1647 ⟨32857, by decide⟩ ⟨12, 2, 0, 32857, 1647, 2757, 65536⟩
    (by decide) selected_cut_00813

theorem unmarked_context_11_411_32858 : frontier 10 ⟨32858, by decide⟩
    (prefixCache 11 411) (prefixPartial 11 411) = false := by
  decide +kernel

theorem node_context_11_411_32858 : EJMOriginalGlobalDAGData.nodes 10 ⟨32858, by decide⟩ =
    .split (coordinate 11) (![⟨32661, by decide⟩,⟨32736, by decide⟩,⟨32797, by decide⟩,⟨32857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_411_32858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 411 ⟨32858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 411
    ⟨32858, by decide⟩ (by decide) (![⟨32661, by decide⟩,⟨32736, by decide⟩,⟨32797, by decide⟩,⟨32857, by decide⟩]) unmarked_context_11_411_32858 node_context_11_411_32858
  intro a
  fin_cases a
  · exact context_12_1644_32661
  · exact context_12_1645_32736
  · exact context_12_1646_32797
  · exact context_12_1647_32857

theorem unmarked_context_10_102_32859 : frontier 11 ⟨32859, by decide⟩
    (prefixCache 10 102) (prefixPartial 10 102) = false := by
  decide +kernel

theorem node_context_10_102_32859 : EJMOriginalGlobalDAGData.nodes 11 ⟨32859, by decide⟩ =
    .split (coordinate 10) (![⟨32121, by decide⟩,⟨32352, by decide⟩,⟨32601, by decide⟩,⟨32858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_102_32859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 102 ⟨32859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 102
    ⟨32859, by decide⟩ (by decide) (![⟨32121, by decide⟩,⟨32352, by decide⟩,⟨32601, by decide⟩,⟨32858, by decide⟩]) unmarked_context_10_102_32859 node_context_10_102_32859
  intro a
  fin_cases a
  · exact context_11_408_32121
  · exact context_11_409_32352
  · exact context_11_410_32601
  · exact context_11_411_32858

theorem selected_cut_00814 : selected 9 ⟨32903, by decide⟩
    (prefixPartial 12 1648) = some ⟨12, 2, 0, 32903, 1648, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_1648_32903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1648 ⟨32903, by decide⟩ :=
  accepted_of_selected 12 1648 ⟨32903, by decide⟩ ⟨12, 2, 0, 32903, 1648, 2265, 65536⟩
    (by decide) selected_cut_00814

theorem selected_cut_00815 : selected 9 ⟨32939, by decide⟩
    (prefixPartial 12 1649) = some ⟨12, 2, 0, 32939, 1649, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_1649_32939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1649 ⟨32939, by decide⟩ :=
  accepted_of_selected 12 1649 ⟨32939, by decide⟩ ⟨12, 2, 0, 32939, 1649, 2113, 65536⟩
    (by decide) selected_cut_00815

theorem selected_cut_00816 : selected 9 ⟨32972, by decide⟩
    (prefixPartial 12 1650) = some ⟨12, 2, 0, 32972, 1650, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_1650_32972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1650 ⟨32972, by decide⟩ :=
  accepted_of_selected 12 1650 ⟨32972, by decide⟩ ⟨12, 2, 0, 32972, 1650, 2065, 65536⟩
    (by decide) selected_cut_00816

theorem selected_cut_00817 : selected 9 ⟨33012, by decide⟩
    (prefixPartial 12 1651) = some ⟨12, 2, 0, 33012, 1651, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_1651_33012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1651 ⟨33012, by decide⟩ :=
  accepted_of_selected 12 1651 ⟨33012, by decide⟩ ⟨12, 2, 0, 33012, 1651, 2157, 65536⟩
    (by decide) selected_cut_00817

theorem unmarked_context_11_412_33013 : frontier 10 ⟨33013, by decide⟩
    (prefixCache 11 412) (prefixPartial 11 412) = false := by
  decide +kernel

theorem node_context_11_412_33013 : EJMOriginalGlobalDAGData.nodes 10 ⟨33013, by decide⟩ =
    .split (coordinate 11) (![⟨32903, by decide⟩,⟨32939, by decide⟩,⟨32972, by decide⟩,⟨33012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_412_33013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 412 ⟨33013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 412
    ⟨33013, by decide⟩ (by decide) (![⟨32903, by decide⟩,⟨32939, by decide⟩,⟨32972, by decide⟩,⟨33012, by decide⟩]) unmarked_context_11_412_33013 node_context_11_412_33013
  intro a
  fin_cases a
  · exact context_12_1648_32903
  · exact context_12_1649_32939
  · exact context_12_1650_32972
  · exact context_12_1651_33012

theorem selected_cut_00818 : selected 9 ⟨33059, by decide⟩
    (prefixPartial 12 1652) = some ⟨12, 2, 0, 33059, 1652, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_1652_33059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1652 ⟨33059, by decide⟩ :=
  accepted_of_selected 12 1652 ⟨33059, by decide⟩ ⟨12, 2, 0, 33059, 1652, 2189, 65536⟩
    (by decide) selected_cut_00818

theorem selected_cut_00819 : selected 9 ⟨33099, by decide⟩
    (prefixPartial 12 1653) = some ⟨12, 2, 0, 33099, 1653, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_1653_33099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1653 ⟨33099, by decide⟩ :=
  accepted_of_selected 12 1653 ⟨33099, by decide⟩ ⟨12, 2, 0, 33099, 1653, 1917, 65536⟩
    (by decide) selected_cut_00819

theorem selected_cut_00820 : selected 9 ⟨33144, by decide⟩
    (prefixPartial 12 1654) = some ⟨12, 2, 0, 33144, 1654, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_1654_33144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1654 ⟨33144, by decide⟩ :=
  accepted_of_selected 12 1654 ⟨33144, by decide⟩ ⟨12, 2, 0, 33144, 1654, 2145, 65536⟩
    (by decide) selected_cut_00820

theorem selected_cut_00821 : selected 9 ⟨33206, by decide⟩
    (prefixPartial 12 1655) = some ⟨12, 2, 0, 33206, 1655, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_1655_33206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1655 ⟨33206, by decide⟩ :=
  accepted_of_selected 12 1655 ⟨33206, by decide⟩ ⟨12, 2, 0, 33206, 1655, 2305, 65536⟩
    (by decide) selected_cut_00821

theorem unmarked_context_11_413_33207 : frontier 10 ⟨33207, by decide⟩
    (prefixCache 11 413) (prefixPartial 11 413) = false := by
  decide +kernel

theorem node_context_11_413_33207 : EJMOriginalGlobalDAGData.nodes 10 ⟨33207, by decide⟩ =
    .split (coordinate 11) (![⟨33059, by decide⟩,⟨33099, by decide⟩,⟨33144, by decide⟩,⟨33206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_413_33207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 413 ⟨33207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 413
    ⟨33207, by decide⟩ (by decide) (![⟨33059, by decide⟩,⟨33099, by decide⟩,⟨33144, by decide⟩,⟨33206, by decide⟩]) unmarked_context_11_413_33207 node_context_11_413_33207
  intro a
  fin_cases a
  · exact context_12_1652_33059
  · exact context_12_1653_33099
  · exact context_12_1654_33144
  · exact context_12_1655_33206

theorem selected_cut_00822 : selected 9 ⟨33230, by decide⟩
    (prefixPartial 12 1656) = some ⟨12, 2, 0, 33230, 1656, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_1656_33230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1656 ⟨33230, by decide⟩ :=
  accepted_of_selected 12 1656 ⟨33230, by decide⟩ ⟨12, 2, 0, 33230, 1656, 1937, 65536⟩
    (by decide) selected_cut_00822

theorem selected_cut_00823 : selected 9 ⟨33265, by decide⟩
    (prefixPartial 12 1657) = some ⟨12, 2, 0, 33265, 1657, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_1657_33265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1657 ⟨33265, by decide⟩ :=
  accepted_of_selected 12 1657 ⟨33265, by decide⟩ ⟨12, 2, 0, 33265, 1657, 1893, 65536⟩
    (by decide) selected_cut_00823

theorem selected_cut_00824 : selected 9 ⟨33336, by decide⟩
    (prefixPartial 12 1658) = some ⟨12, 2, 0, 33336, 1658, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_1658_33336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1658 ⟨33336, by decide⟩ :=
  accepted_of_selected 12 1658 ⟨33336, by decide⟩ ⟨12, 2, 0, 33336, 1658, 2469, 65536⟩
    (by decide) selected_cut_00824

theorem selected_cut_00825 : selected 9 ⟨33366, by decide⟩
    (prefixPartial 12 1659) = some ⟨12, 2, 0, 33366, 1659, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_1659_33366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1659 ⟨33366, by decide⟩ :=
  accepted_of_selected 12 1659 ⟨33366, by decide⟩ ⟨12, 2, 0, 33366, 1659, 1837, 65536⟩
    (by decide) selected_cut_00825

theorem unmarked_context_11_414_33367 : frontier 10 ⟨33367, by decide⟩
    (prefixCache 11 414) (prefixPartial 11 414) = false := by
  decide +kernel

theorem node_context_11_414_33367 : EJMOriginalGlobalDAGData.nodes 10 ⟨33367, by decide⟩ =
    .split (coordinate 11) (![⟨33230, by decide⟩,⟨33265, by decide⟩,⟨33336, by decide⟩,⟨33366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_414_33367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 414 ⟨33367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 414
    ⟨33367, by decide⟩ (by decide) (![⟨33230, by decide⟩,⟨33265, by decide⟩,⟨33336, by decide⟩,⟨33366, by decide⟩]) unmarked_context_11_414_33367 node_context_11_414_33367
  intro a
  fin_cases a
  · exact context_12_1656_33230
  · exact context_12_1657_33265
  · exact context_12_1658_33336
  · exact context_12_1659_33366

theorem selected_cut_00826 : selected 9 ⟨33395, by decide⟩
    (prefixPartial 12 1660) = some ⟨12, 2, 0, 33395, 1660, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_1660_33395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1660 ⟨33395, by decide⟩ :=
  accepted_of_selected 12 1660 ⟨33395, by decide⟩ ⟨12, 2, 0, 33395, 1660, 1565, 65536⟩
    (by decide) selected_cut_00826

theorem selected_cut_00827 : selected 9 ⟨33418, by decide⟩
    (prefixPartial 12 1661) = some ⟨12, 2, 0, 33418, 1661, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_1661_33418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1661 ⟨33418, by decide⟩ :=
  accepted_of_selected 12 1661 ⟨33418, by decide⟩ ⟨12, 2, 0, 33418, 1661, 1473, 65536⟩
    (by decide) selected_cut_00827

theorem selected_cut_00828 : selected 9 ⟨33440, by decide⟩
    (prefixPartial 12 1662) = some ⟨12, 2, 0, 33440, 1662, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_1662_33440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1662 ⟨33440, by decide⟩ :=
  accepted_of_selected 12 1662 ⟨33440, by decide⟩ ⟨12, 2, 0, 33440, 1662, 1397, 65536⟩
    (by decide) selected_cut_00828

theorem selected_cut_00829 : selected 9 ⟨33462, by decide⟩
    (prefixPartial 12 1663) = some ⟨12, 2, 0, 33462, 1663, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_1663_33462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1663 ⟨33462, by decide⟩ :=
  accepted_of_selected 12 1663 ⟨33462, by decide⟩ ⟨12, 2, 0, 33462, 1663, 1349, 65536⟩
    (by decide) selected_cut_00829

theorem unmarked_context_11_415_33463 : frontier 10 ⟨33463, by decide⟩
    (prefixCache 11 415) (prefixPartial 11 415) = false := by
  decide +kernel

theorem node_context_11_415_33463 : EJMOriginalGlobalDAGData.nodes 10 ⟨33463, by decide⟩ =
    .split (coordinate 11) (![⟨33395, by decide⟩,⟨33418, by decide⟩,⟨33440, by decide⟩,⟨33462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_415_33463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 415 ⟨33463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 415
    ⟨33463, by decide⟩ (by decide) (![⟨33395, by decide⟩,⟨33418, by decide⟩,⟨33440, by decide⟩,⟨33462, by decide⟩]) unmarked_context_11_415_33463 node_context_11_415_33463
  intro a
  fin_cases a
  · exact context_12_1660_33395
  · exact context_12_1661_33418
  · exact context_12_1662_33440
  · exact context_12_1663_33462

theorem unmarked_context_10_103_33464 : frontier 11 ⟨33464, by decide⟩
    (prefixCache 10 103) (prefixPartial 10 103) = false := by
  decide +kernel

theorem node_context_10_103_33464 : EJMOriginalGlobalDAGData.nodes 11 ⟨33464, by decide⟩ =
    .split (coordinate 10) (![⟨33013, by decide⟩,⟨33207, by decide⟩,⟨33367, by decide⟩,⟨33463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_103_33464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 103 ⟨33464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 103
    ⟨33464, by decide⟩ (by decide) (![⟨33013, by decide⟩,⟨33207, by decide⟩,⟨33367, by decide⟩,⟨33463, by decide⟩]) unmarked_context_10_103_33464 node_context_10_103_33464
  intro a
  fin_cases a
  · exact context_11_412_33013
  · exact context_11_413_33207
  · exact context_11_414_33367
  · exact context_11_415_33463

theorem unmarked_context_9_25_33465 : frontier 12 ⟨33465, by decide⟩
    (prefixCache 9 25) (prefixPartial 9 25) = false := by
  decide +kernel

theorem node_context_9_25_33465 : EJMOriginalGlobalDAGData.nodes 12 ⟨33465, by decide⟩ =
    .split (coordinate 9) (![⟨30490, by decide⟩,⟨31908, by decide⟩,⟨32859, by decide⟩,⟨33464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_25_33465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 25 ⟨33465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 25
    ⟨33465, by decide⟩ (by decide) (![⟨30490, by decide⟩,⟨31908, by decide⟩,⟨32859, by decide⟩,⟨33464, by decide⟩]) unmarked_context_9_25_33465 node_context_9_25_33465
  intro a
  fin_cases a
  · exact context_10_100_30490
  · exact context_10_101_31908
  · exact context_10_102_32859
  · exact context_10_103_33464

theorem selected_cut_00830 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 26) = some ⟨9, 1, 0, 33466, 26, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_26_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 26 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 26 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 26, 1, 4194304⟩
    (by decide) selected_cut_00830

theorem selected_cut_00831 : selected 10 ⟨33526, by decide⟩
    (prefixPartial 11 432) = some ⟨11, 2, 0, 33526, 432, 3689, 262144⟩ := by
  decide +kernel

theorem context_11_432_33526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 432 ⟨33526, by decide⟩ :=
  accepted_of_selected 11 432 ⟨33526, by decide⟩ ⟨11, 2, 0, 33526, 432, 3689, 262144⟩
    (by decide) selected_cut_00831

theorem selected_cut_00832 : selected 10 ⟨33590, by decide⟩
    (prefixPartial 11 433) = some ⟨11, 2, 0, 33590, 433, 3345, 262144⟩ := by
  decide +kernel

theorem context_11_433_33590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 433 ⟨33590, by decide⟩ :=
  accepted_of_selected 11 433 ⟨33590, by decide⟩ ⟨11, 2, 0, 33590, 433, 3345, 262144⟩
    (by decide) selected_cut_00832

theorem selected_cut_00833 : selected 10 ⟨33645, by decide⟩
    (prefixPartial 11 434) = some ⟨11, 2, 0, 33645, 434, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_434_33645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 434 ⟨33645, by decide⟩ :=
  accepted_of_selected 11 434 ⟨33645, by decide⟩ ⟨11, 2, 0, 33645, 434, 2385, 262144⟩
    (by decide) selected_cut_00833

theorem selected_cut_00834 : selected 10 ⟨33714, by decide⟩
    (prefixPartial 11 435) = some ⟨11, 2, 0, 33714, 435, 2513, 262144⟩ := by
  decide +kernel

theorem context_11_435_33714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 435 ⟨33714, by decide⟩ :=
  accepted_of_selected 11 435 ⟨33714, by decide⟩ ⟨11, 2, 0, 33714, 435, 2513, 262144⟩
    (by decide) selected_cut_00834

theorem unmarked_context_10_108_33715 : frontier 11 ⟨33715, by decide⟩
    (prefixCache 10 108) (prefixPartial 10 108) = false := by
  decide +kernel

theorem node_context_10_108_33715 : EJMOriginalGlobalDAGData.nodes 11 ⟨33715, by decide⟩ =
    .split (coordinate 10) (![⟨33526, by decide⟩,⟨33590, by decide⟩,⟨33645, by decide⟩,⟨33714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_108_33715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 108 ⟨33715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 108
    ⟨33715, by decide⟩ (by decide) (![⟨33526, by decide⟩,⟨33590, by decide⟩,⟨33645, by decide⟩,⟨33714, by decide⟩]) unmarked_context_10_108_33715 node_context_10_108_33715
  intro a
  fin_cases a
  · exact context_11_432_33526
  · exact context_11_433_33590
  · exact context_11_434_33645
  · exact context_11_435_33714

theorem selected_cut_00835 : selected 10 ⟨33758, by decide⟩
    (prefixPartial 11 436) = some ⟨11, 2, 0, 33758, 436, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_436_33758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 436 ⟨33758, by decide⟩ :=
  accepted_of_selected 11 436 ⟨33758, by decide⟩ ⟨11, 2, 0, 33758, 436, 1673, 262144⟩
    (by decide) selected_cut_00835

theorem selected_cut_00836 : selected 10 ⟨33867, by decide⟩
    (prefixPartial 11 437) = some ⟨11, 2, 0, 33867, 437, 1993, 262144⟩ := by
  decide +kernel

theorem context_11_437_33867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 437 ⟨33867, by decide⟩ :=
  accepted_of_selected 11 437 ⟨33867, by decide⟩ ⟨11, 2, 0, 33867, 437, 1993, 262144⟩
    (by decide) selected_cut_00836

theorem selected_cut_00837 : selected 10 ⟨33901, by decide⟩
    (prefixPartial 11 438) = some ⟨11, 2, 0, 33901, 438, 861, 262144⟩ := by
  decide +kernel

theorem context_11_438_33901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 438 ⟨33901, by decide⟩ :=
  accepted_of_selected 11 438 ⟨33901, by decide⟩ ⟨11, 2, 0, 33901, 438, 861, 262144⟩
    (by decide) selected_cut_00837

theorem selected_cut_00838 : selected 10 ⟨33940, by decide⟩
    (prefixPartial 11 439) = some ⟨11, 2, 0, 33940, 439, 985, 262144⟩ := by
  decide +kernel

theorem context_11_439_33940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 439 ⟨33940, by decide⟩ :=
  accepted_of_selected 11 439 ⟨33940, by decide⟩ ⟨11, 2, 0, 33940, 439, 985, 262144⟩
    (by decide) selected_cut_00838

theorem unmarked_context_10_109_33941 : frontier 11 ⟨33941, by decide⟩
    (prefixCache 10 109) (prefixPartial 10 109) = false := by
  decide +kernel

theorem node_context_10_109_33941 : EJMOriginalGlobalDAGData.nodes 11 ⟨33941, by decide⟩ =
    .split (coordinate 10) (![⟨33758, by decide⟩,⟨33867, by decide⟩,⟨33901, by decide⟩,⟨33940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_109_33941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 109 ⟨33941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 109
    ⟨33941, by decide⟩ (by decide) (![⟨33758, by decide⟩,⟨33867, by decide⟩,⟨33901, by decide⟩,⟨33940, by decide⟩]) unmarked_context_10_109_33941 node_context_10_109_33941
  intro a
  fin_cases a
  · exact context_11_436_33758
  · exact context_11_437_33867
  · exact context_11_438_33901
  · exact context_11_439_33940

theorem selected_cut_00839 : selected 11 ⟨34007, by decide⟩
    (prefixPartial 10 110) = some ⟨10, 2, 0, 34007, 110, 1237, 1048576⟩ := by
  decide +kernel

theorem context_10_110_34007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 110 ⟨34007, by decide⟩ :=
  accepted_of_selected 10 110 ⟨34007, by decide⟩ ⟨10, 2, 0, 34007, 110, 1237, 1048576⟩
    (by decide) selected_cut_00839

theorem selected_cut_00840 : selected 11 ⟨34027, by decide⟩
    (prefixPartial 10 111) = some ⟨10, 2, 0, 34027, 111, 181, 1048576⟩ := by
  decide +kernel

theorem context_10_111_34027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 111 ⟨34027, by decide⟩ :=
  accepted_of_selected 10 111 ⟨34027, by decide⟩ ⟨10, 2, 0, 34027, 111, 181, 1048576⟩
    (by decide) selected_cut_00840

theorem unmarked_context_9_27_34028 : frontier 12 ⟨34028, by decide⟩
    (prefixCache 9 27) (prefixPartial 9 27) = false := by
  decide +kernel

theorem node_context_9_27_34028 : EJMOriginalGlobalDAGData.nodes 12 ⟨34028, by decide⟩ =
    .split (coordinate 9) (![⟨33715, by decide⟩,⟨33941, by decide⟩,⟨34007, by decide⟩,⟨34027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_27_34028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 27 ⟨34028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 27
    ⟨34028, by decide⟩ (by decide) (![⟨33715, by decide⟩,⟨33941, by decide⟩,⟨34007, by decide⟩,⟨34027, by decide⟩]) unmarked_context_9_27_34028 node_context_9_27_34028
  intro a
  fin_cases a
  · exact context_10_108_33715
  · exact context_10_109_33941
  · exact context_10_110_34007
  · exact context_10_111_34027

theorem unmarked_context_8_6_34029 : frontier 13 ⟨34029, by decide⟩
    (prefixCache 8 6) (prefixPartial 8 6) = false := by
  decide +kernel

theorem node_context_8_6_34029 : EJMOriginalGlobalDAGData.nodes 13 ⟨34029, by decide⟩ =
    .split (coordinate 8) (![⟨29103, by decide⟩,⟨33465, by decide⟩,⟨33466, by decide⟩,⟨34028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_6_34029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 6 ⟨34029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 6
    ⟨34029, by decide⟩ (by decide) (![⟨29103, by decide⟩,⟨33465, by decide⟩,⟨33466, by decide⟩,⟨34028, by decide⟩]) unmarked_context_8_6_34029 node_context_8_6_34029
  intro a
  fin_cases a
  · exact context_9_24_29103
  · exact context_9_25_33465
  · exact context_9_26_33466
  · exact context_9_27_34028

theorem selected_cut_00841 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 7) = some ⟨8, 1, 0, 14298, 7, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_7_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 7 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 7 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 7, 1, 16777216⟩
    (by decide) selected_cut_00841

theorem unmarked_context_7_1_34030 : frontier 14 ⟨34030, by decide⟩
    (prefixCache 7 1) (prefixPartial 7 1) = false := by
  decide +kernel

theorem node_context_7_1_34030 : EJMOriginalGlobalDAGData.nodes 14 ⟨34030, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨23022, by decide⟩,⟨34029, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1_34030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1 ⟨34030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1
    ⟨34030, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨23022, by decide⟩,⟨34029, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_1_34030 node_context_7_1_34030
  intro a
  fin_cases a
  · exact context_8_4_14300
  · exact context_8_5_23022
  · exact context_8_6_34029
  · exact context_8_7_14298

theorem selected_cut_00842 : selected 14 ⟨34031, by decide⟩
    (prefixPartial 7 2) = some ⟨7, 1, 0, 34031, 2, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_2_34031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 2 ⟨34031, by decide⟩ :=
  accepted_of_selected 7 2 ⟨34031, by decide⟩ ⟨7, 1, 0, 34031, 2, 1, 67108864⟩
    (by decide) selected_cut_00842

theorem selected_cut_00843 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 3) = some ⟨7, 1, 0, 34032, 3, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_3_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 3 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 3 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 3, 1, 67108864⟩
    (by decide) selected_cut_00843

theorem unmarked_context_6_0_34033 : frontier 15 ⟨34033, by decide⟩
    (prefixCache 6 0) (prefixPartial 6 0) = false := by
  decide +kernel

theorem node_context_6_0_34033 : EJMOriginalGlobalDAGData.nodes 15 ⟨34033, by decide⟩ =
    .split (coordinate 6) (![⟨14299, by decide⟩,⟨34030, by decide⟩,⟨34031, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_0_34033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 0 ⟨34033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 0
    ⟨34033, by decide⟩ (by decide) (![⟨14299, by decide⟩,⟨34030, by decide⟩,⟨34031, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_0_34033 node_context_6_0_34033
  intro a
  fin_cases a
  · exact context_7_0_14299
  · exact context_7_1_34030
  · exact context_7_2_34031
  · exact context_7_3_34032

theorem selected_cut_00844 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 4096) = some ⟨12, 1, 0, 34034, 4096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4096_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4096 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 4096 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 4096, 1, 65536⟩
    (by decide) selected_cut_00844

theorem selected_cut_00845 : selected 9 ⟨34156, by decide⟩
    (prefixPartial 12 4097) = some ⟨12, 2, 0, 34156, 4097, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_4097_34156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4097 ⟨34156, by decide⟩ :=
  accepted_of_selected 12 4097 ⟨34156, by decide⟩ ⟨12, 2, 0, 34156, 4097, 2345, 65536⟩
    (by decide) selected_cut_00845

theorem selected_cut_00846 : selected 8 ⟨34220, by decide⟩
    (prefixPartial 13 16392) = some ⟨13, 2, 0, 34220, 16392, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_16392_34220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16392 ⟨34220, by decide⟩ :=
  accepted_of_selected 13 16392 ⟨34220, by decide⟩ ⟨13, 2, 0, 34220, 16392, 1449, 16384⟩
    (by decide) selected_cut_00846

theorem selected_cut_00847 : selected 8 ⟨34275, by decide⟩
    (prefixPartial 13 16393) = some ⟨13, 2, 0, 34275, 16393, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_16393_34275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16393 ⟨34275, by decide⟩ :=
  accepted_of_selected 13 16393 ⟨34275, by decide⟩ ⟨13, 2, 0, 34275, 16393, 1937, 16384⟩
    (by decide) selected_cut_00847

theorem selected_cut_00848 : selected 8 ⟨34326, by decide⟩
    (prefixPartial 13 16394) = some ⟨13, 2, 0, 34326, 16394, 789, 16384⟩ := by
  decide +kernel

theorem context_13_16394_34326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16394 ⟨34326, by decide⟩ :=
  accepted_of_selected 13 16394 ⟨34326, by decide⟩ ⟨13, 2, 0, 34326, 16394, 789, 16384⟩
    (by decide) selected_cut_00848

theorem selected_cut_00849 : selected 8 ⟨34336, by decide⟩
    (prefixPartial 13 16395) = some ⟨13, 2, 0, 34336, 16395, 149, 16384⟩ := by
  decide +kernel

theorem context_13_16395_34336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16395 ⟨34336, by decide⟩ :=
  accepted_of_selected 13 16395 ⟨34336, by decide⟩ ⟨13, 2, 0, 34336, 16395, 149, 16384⟩
    (by decide) selected_cut_00849

theorem unmarked_context_12_4098_34337 : frontier 9 ⟨34337, by decide⟩
    (prefixCache 12 4098) (prefixPartial 12 4098) = false := by
  decide +kernel

theorem node_context_12_4098_34337 : EJMOriginalGlobalDAGData.nodes 9 ⟨34337, by decide⟩ =
    .split (coordinate 12) (![⟨34220, by decide⟩,⟨34275, by decide⟩,⟨34326, by decide⟩,⟨34336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4098_34337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4098 ⟨34337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4098
    ⟨34337, by decide⟩ (by decide) (![⟨34220, by decide⟩,⟨34275, by decide⟩,⟨34326, by decide⟩,⟨34336, by decide⟩]) unmarked_context_12_4098_34337 node_context_12_4098_34337
  intro a
  fin_cases a
  · exact context_13_16392_34220
  · exact context_13_16393_34275
  · exact context_13_16394_34326
  · exact context_13_16395_34336

theorem selected_cut_00850 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4099) = some ⟨12, 1, 0, 893, 4099, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4099_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4099 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4099 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4099, 1, 65536⟩
    (by decide) selected_cut_00850

theorem unmarked_context_11_1024_34338 : frontier 10 ⟨34338, by decide⟩
    (prefixCache 11 1024) (prefixPartial 11 1024) = false := by
  decide +kernel

theorem node_context_11_1024_34338 : EJMOriginalGlobalDAGData.nodes 10 ⟨34338, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨34156, by decide⟩,⟨34337, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1024_34338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1024 ⟨34338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1024
    ⟨34338, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨34156, by decide⟩,⟨34337, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1024_34338 node_context_11_1024_34338
  intro a
  fin_cases a
  · exact context_12_4096_34034
  · exact context_12_4097_34156
  · exact context_12_4098_34337
  · exact context_12_4099_893

theorem selected_cut_00851 : selected 9 ⟨34459, by decide⟩
    (prefixPartial 12 4100) = some ⟨12, 2, 0, 34459, 4100, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_4100_34459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4100 ⟨34459, by decide⟩ :=
  accepted_of_selected 12 4100 ⟨34459, by decide⟩ ⟨12, 2, 0, 34459, 4100, 3045, 65536⟩
    (by decide) selected_cut_00851

theorem selected_cut_00852 : selected 9 ⟨34553, by decide⟩
    (prefixPartial 12 4101) = some ⟨12, 2, 0, 34553, 4101, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_4101_34553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4101 ⟨34553, by decide⟩ :=
  accepted_of_selected 12 4101 ⟨34553, by decide⟩ ⟨12, 2, 0, 34553, 4101, 3621, 65536⟩
    (by decide) selected_cut_00852

theorem selected_cut_00853 : selected 8 ⟨34599, by decide⟩
    (prefixPartial 13 16408) = some ⟨13, 2, 0, 34599, 16408, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_16408_34599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16408 ⟨34599, by decide⟩ :=
  accepted_of_selected 13 16408 ⟨34599, by decide⟩ ⟨13, 2, 0, 34599, 16408, 1309, 16384⟩
    (by decide) selected_cut_00853

theorem selected_cut_00854 : selected 8 ⟨34656, by decide⟩
    (prefixPartial 13 16409) = some ⟨13, 2, 0, 34656, 16409, 3121, 16384⟩ := by
  decide +kernel

theorem context_13_16409_34656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16409 ⟨34656, by decide⟩ :=
  accepted_of_selected 13 16409 ⟨34656, by decide⟩ ⟨13, 2, 0, 34656, 16409, 3121, 16384⟩
    (by decide) selected_cut_00854

theorem selected_cut_00855 : selected 8 ⟨34690, by decide⟩
    (prefixPartial 13 16410) = some ⟨13, 2, 0, 34690, 16410, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_16410_34690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16410 ⟨34690, by decide⟩ :=
  accepted_of_selected 13 16410 ⟨34690, by decide⟩ ⟨13, 2, 0, 34690, 16410, 2005, 16384⟩
    (by decide) selected_cut_00855

theorem selected_cut_00856 : selected 8 ⟨34714, by decide⟩
    (prefixPartial 13 16411) = some ⟨13, 2, 0, 34714, 16411, 937, 16384⟩ := by
  decide +kernel

theorem context_13_16411_34714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16411 ⟨34714, by decide⟩ :=
  accepted_of_selected 13 16411 ⟨34714, by decide⟩ ⟨13, 2, 0, 34714, 16411, 937, 16384⟩
    (by decide) selected_cut_00856

theorem unmarked_context_12_4102_34715 : frontier 9 ⟨34715, by decide⟩
    (prefixCache 12 4102) (prefixPartial 12 4102) = false := by
  decide +kernel

theorem node_context_12_4102_34715 : EJMOriginalGlobalDAGData.nodes 9 ⟨34715, by decide⟩ =
    .split (coordinate 12) (![⟨34599, by decide⟩,⟨34656, by decide⟩,⟨34690, by decide⟩,⟨34714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4102_34715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4102 ⟨34715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4102
    ⟨34715, by decide⟩ (by decide) (![⟨34599, by decide⟩,⟨34656, by decide⟩,⟨34690, by decide⟩,⟨34714, by decide⟩]) unmarked_context_12_4102_34715 node_context_12_4102_34715
  intro a
  fin_cases a
  · exact context_13_16408_34599
  · exact context_13_16409_34656
  · exact context_13_16410_34690
  · exact context_13_16411_34714

theorem selected_cut_00857 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4103) = some ⟨12, 1, 0, 893, 4103, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4103_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4103 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4103 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4103, 1, 65536⟩
    (by decide) selected_cut_00857

theorem unmarked_context_11_1025_34716 : frontier 10 ⟨34716, by decide⟩
    (prefixCache 11 1025) (prefixPartial 11 1025) = false := by
  decide +kernel

theorem node_context_11_1025_34716 : EJMOriginalGlobalDAGData.nodes 10 ⟨34716, by decide⟩ =
    .split (coordinate 11) (![⟨34459, by decide⟩,⟨34553, by decide⟩,⟨34715, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1025_34716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1025 ⟨34716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1025
    ⟨34716, by decide⟩ (by decide) (![⟨34459, by decide⟩,⟨34553, by decide⟩,⟨34715, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1025_34716 node_context_11_1025_34716
  intro a
  fin_cases a
  · exact context_12_4100_34459
  · exact context_12_4101_34553
  · exact context_12_4102_34715
  · exact context_12_4103_893

theorem selected_cut_00858 : selected 9 ⟨34858, by decide⟩
    (prefixPartial 12 4104) = some ⟨12, 2, 0, 34858, 4104, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_4104_34858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4104 ⟨34858, by decide⟩ :=
  accepted_of_selected 12 4104 ⟨34858, by decide⟩ ⟨12, 2, 0, 34858, 4104, 2481, 65536⟩
    (by decide) selected_cut_00858

theorem selected_cut_00859 : selected 8 ⟨34889, by decide⟩
    (prefixPartial 13 16420) = some ⟨13, 2, 0, 34889, 16420, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_16420_34889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16420 ⟨34889, by decide⟩ :=
  accepted_of_selected 13 16420 ⟨34889, by decide⟩ ⟨13, 2, 0, 34889, 16420, 1045, 16384⟩
    (by decide) selected_cut_00859

theorem selected_cut_00860 : selected 8 ⟨34937, by decide⟩
    (prefixPartial 13 16421) = some ⟨13, 2, 0, 34937, 16421, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_16421_34937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16421 ⟨34937, by decide⟩ :=
  accepted_of_selected 13 16421 ⟨34937, by decide⟩ ⟨13, 2, 0, 34937, 16421, 2705, 16384⟩
    (by decide) selected_cut_00860

theorem selected_cut_00861 : selected 8 ⟨34969, by decide⟩
    (prefixPartial 13 16422) = some ⟨13, 2, 0, 34969, 16422, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_16422_34969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16422 ⟨34969, by decide⟩ :=
  accepted_of_selected 13 16422 ⟨34969, by decide⟩ ⟨13, 2, 0, 34969, 16422, 1913, 16384⟩
    (by decide) selected_cut_00861

theorem selected_cut_00862 : selected 8 ⟨34985, by decide⟩
    (prefixPartial 13 16423) = some ⟨13, 2, 0, 34985, 16423, 909, 16384⟩ := by
  decide +kernel

theorem context_13_16423_34985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16423 ⟨34985, by decide⟩ :=
  accepted_of_selected 13 16423 ⟨34985, by decide⟩ ⟨13, 2, 0, 34985, 16423, 909, 16384⟩
    (by decide) selected_cut_00862

theorem unmarked_context_12_4105_34986 : frontier 9 ⟨34986, by decide⟩
    (prefixCache 12 4105) (prefixPartial 12 4105) = false := by
  decide +kernel

theorem node_context_12_4105_34986 : EJMOriginalGlobalDAGData.nodes 9 ⟨34986, by decide⟩ =
    .split (coordinate 12) (![⟨34889, by decide⟩,⟨34937, by decide⟩,⟨34969, by decide⟩,⟨34985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4105_34986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4105 ⟨34986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4105
    ⟨34986, by decide⟩ (by decide) (![⟨34889, by decide⟩,⟨34937, by decide⟩,⟨34969, by decide⟩,⟨34985, by decide⟩]) unmarked_context_12_4105_34986 node_context_12_4105_34986
  intro a
  fin_cases a
  · exact context_13_16420_34889
  · exact context_13_16421_34937
  · exact context_13_16422_34969
  · exact context_13_16423_34985

theorem selected_cut_00863 : selected 8 ⟨35019, by decide⟩
    (prefixPartial 13 16424) = some ⟨13, 2, 0, 35019, 16424, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_16424_35019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16424 ⟨35019, by decide⟩ :=
  accepted_of_selected 13 16424 ⟨35019, by decide⟩ ⟨13, 2, 0, 35019, 16424, 1041, 16384⟩
    (by decide) selected_cut_00863

theorem selected_cut_00864 : selected 8 ⟨35064, by decide⟩
    (prefixPartial 13 16425) = some ⟨13, 2, 0, 35064, 16425, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_16425_35064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16425 ⟨35064, by decide⟩ :=
  accepted_of_selected 13 16425 ⟨35064, by decide⟩ ⟨13, 2, 0, 35064, 16425, 2909, 16384⟩
    (by decide) selected_cut_00864

theorem selected_cut_00865 : selected 8 ⟨35093, by decide⟩
    (prefixPartial 13 16426) = some ⟨13, 2, 0, 35093, 16426, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_16426_35093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16426 ⟨35093, by decide⟩ :=
  accepted_of_selected 13 16426 ⟨35093, by decide⟩ ⟨13, 2, 0, 35093, 16426, 1729, 16384⟩
    (by decide) selected_cut_00865

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
