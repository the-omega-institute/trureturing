/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover474
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_45604 : selected 10 ⟨1266621, by decide⟩
    (prefixPartial 11 92083) = some ⟨11, 2, 0, 1266621, 92083, 1181, 262144⟩ := by
  decide +kernel

theorem context_11_92083_1266621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92083 ⟨1266621, by decide⟩ :=
  accepted_of_selected 11 92083 ⟨1266621, by decide⟩ ⟨11, 2, 0, 1266621, 92083, 1181, 262144⟩
    (by decide) selected_cut_45604

theorem unmarked_context_10_23020_1266622 : frontier 11 ⟨1266622, by decide⟩
    (prefixCache 10 23020) (prefixPartial 10 23020) = false := by
  decide +kernel

theorem node_context_10_23020_1266622 : EJMOriginalGlobalDAGData.nodes 11 ⟨1266622, by decide⟩ =
    .split (coordinate 10) (![⟨1266556, by decide⟩,⟨1266588, by decide⟩,⟨1266599, by decide⟩,⟨1266621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23020_1266622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23020 ⟨1266622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23020
    ⟨1266622, by decide⟩ (by decide) (![⟨1266556, by decide⟩,⟨1266588, by decide⟩,⟨1266599, by decide⟩,⟨1266621, by decide⟩]) unmarked_context_10_23020_1266622 node_context_10_23020_1266622
  intro a
  fin_cases a
  · exact context_11_92080_1266556
  · exact context_11_92081_1266588
  · exact context_11_92082_1266599
  · exact context_11_92083_1266621

theorem selected_cut_45605 : selected 11 ⟨1266674, by decide⟩
    (prefixPartial 10 23021) = some ⟨10, 2, 0, 1266674, 23021, 2465, 1048576⟩ := by
  decide +kernel

theorem context_10_23021_1266674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23021 ⟨1266674, by decide⟩ :=
  accepted_of_selected 10 23021 ⟨1266674, by decide⟩ ⟨10, 2, 0, 1266674, 23021, 2465, 1048576⟩
    (by decide) selected_cut_45605

theorem selected_cut_45606 : selected 11 ⟨1266723, by decide⟩
    (prefixPartial 10 23022) = some ⟨10, 2, 0, 1266723, 23022, 1945, 1048576⟩ := by
  decide +kernel

theorem context_10_23022_1266723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23022 ⟨1266723, by decide⟩ :=
  accepted_of_selected 10 23022 ⟨1266723, by decide⟩ ⟨10, 2, 0, 1266723, 23022, 1945, 1048576⟩
    (by decide) selected_cut_45606

theorem selected_cut_45607 : selected 11 ⟨1266734, by decide⟩
    (prefixPartial 10 23023) = some ⟨10, 2, 0, 1266734, 23023, 249, 1048576⟩ := by
  decide +kernel

theorem context_10_23023_1266734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23023 ⟨1266734, by decide⟩ :=
  accepted_of_selected 10 23023 ⟨1266734, by decide⟩ ⟨10, 2, 0, 1266734, 23023, 249, 1048576⟩
    (by decide) selected_cut_45607

theorem unmarked_context_9_5755_1266735 : frontier 12 ⟨1266735, by decide⟩
    (prefixCache 9 5755) (prefixPartial 9 5755) = false := by
  decide +kernel

theorem node_context_9_5755_1266735 : EJMOriginalGlobalDAGData.nodes 12 ⟨1266735, by decide⟩ =
    .split (coordinate 9) (![⟨1266622, by decide⟩,⟨1266674, by decide⟩,⟨1266723, by decide⟩,⟨1266734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5755_1266735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5755 ⟨1266735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5755
    ⟨1266735, by decide⟩ (by decide) (![⟨1266622, by decide⟩,⟨1266674, by decide⟩,⟨1266723, by decide⟩,⟨1266734, by decide⟩]) unmarked_context_9_5755_1266735 node_context_9_5755_1266735
  intro a
  fin_cases a
  · exact context_10_23020_1266622
  · exact context_10_23021_1266674
  · exact context_10_23022_1266723
  · exact context_10_23023_1266734

theorem unmarked_context_8_1438_1266736 : frontier 13 ⟨1266736, by decide⟩
    (prefixCache 8 1438) (prefixPartial 8 1438) = false := by
  decide +kernel

theorem node_context_8_1438_1266736 : EJMOriginalGlobalDAGData.nodes 13 ⟨1266736, by decide⟩ =
    .split (coordinate 8) (![⟨1265050, by decide⟩,⟨1266052, by decide⟩,⟨1266525, by decide⟩,⟨1266735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1438_1266736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1438 ⟨1266736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1438
    ⟨1266736, by decide⟩ (by decide) (![⟨1265050, by decide⟩,⟨1266052, by decide⟩,⟨1266525, by decide⟩,⟨1266735, by decide⟩]) unmarked_context_8_1438_1266736 node_context_8_1438_1266736
  intro a
  fin_cases a
  · exact context_9_5752_1265050
  · exact context_9_5753_1266052
  · exact context_9_5754_1266525
  · exact context_9_5755_1266735

theorem selected_cut_45608 : selected 13 ⟨814757, by decide⟩
    (prefixPartial 8 1439) = some ⟨8, 1, 0, 814757, 1439, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1439_814757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1439 ⟨814757, by decide⟩ :=
  accepted_of_selected 8 1439 ⟨814757, by decide⟩ ⟨8, 1, 0, 814757, 1439, 1, 16777216⟩
    (by decide) selected_cut_45608

theorem unmarked_context_7_359_1266737 : frontier 14 ⟨1266737, by decide⟩
    (prefixCache 7 359) (prefixPartial 7 359) = false := by
  decide +kernel

theorem node_context_7_359_1266737 : EJMOriginalGlobalDAGData.nodes 14 ⟨1266737, by decide⟩ =
    .split (coordinate 7) (![⟨1262380, by decide⟩,⟨1109534, by decide⟩,⟨1266736, by decide⟩,⟨814757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_359_1266737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 359 ⟨1266737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 359
    ⟨1266737, by decide⟩ (by decide) (![⟨1262380, by decide⟩,⟨1109534, by decide⟩,⟨1266736, by decide⟩,⟨814757, by decide⟩]) unmarked_context_7_359_1266737 node_context_7_359_1266737
  intro a
  fin_cases a
  · exact context_8_1436_1262380
  · exact context_8_1437_1109534
  · exact context_8_1438_1266736
  · exact context_8_1439_814757

theorem unmarked_context_6_89_1266738 : frontier 15 ⟨1266738, by decide⟩
    (prefixCache 6 89) (prefixPartial 6 89) = false := by
  decide +kernel

theorem node_context_6_89_1266738 : EJMOriginalGlobalDAGData.nodes 15 ⟨1266738, by decide⟩ =
    .split (coordinate 6) (![⟨116316, by decide⟩,⟨116316, by decide⟩,⟨1259911, by decide⟩,⟨1266737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_89_1266738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 89 ⟨1266738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 89
    ⟨1266738, by decide⟩ (by decide) (![⟨116316, by decide⟩,⟨116316, by decide⟩,⟨1259911, by decide⟩,⟨1266737, by decide⟩]) unmarked_context_6_89_1266738 node_context_6_89_1266738
  intro a
  fin_cases a
  · exact context_7_356_116316
  · exact context_7_357_116316
  · exact context_7_358_1259911
  · exact context_7_359_1266737

theorem selected_cut_45609 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92160) = some ⟨11, 1, 0, 434745, 92160, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92160_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92160 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92160 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92160, 1, 262144⟩
    (by decide) selected_cut_45609

theorem selected_cut_45610 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 92161) = some ⟨11, 1, 0, 167448, 92161, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92161_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92161 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 92161 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 92161, 1, 262144⟩
    (by decide) selected_cut_45610

theorem selected_cut_45611 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 368648) = some ⟨12, 1, 0, 448748, 368648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368648_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368648 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 368648 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 368648, 1, 65536⟩
    (by decide) selected_cut_45611

theorem selected_cut_45612 : selected 9 ⟨1266823, by decide⟩
    (prefixPartial 12 368649) = some ⟨12, 2, 0, 1266823, 368649, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_368649_1266823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368649 ⟨1266823, by decide⟩ :=
  accepted_of_selected 12 368649 ⟨1266823, by decide⟩ ⟨12, 2, 0, 1266823, 368649, 2825, 65536⟩
    (by decide) selected_cut_45612

theorem selected_cut_45613 : selected 9 ⟨663554, by decide⟩
    (prefixPartial 12 368650) = some ⟨12, 1, 0, 663554, 368650, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368650_663554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368650 ⟨663554, by decide⟩ :=
  accepted_of_selected 12 368650 ⟨663554, by decide⟩ ⟨12, 1, 0, 663554, 368650, 1, 65536⟩
    (by decide) selected_cut_45613

theorem selected_cut_45614 : selected 9 ⟨1266898, by decide⟩
    (prefixPartial 12 368651) = some ⟨12, 2, 0, 1266898, 368651, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_368651_1266898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368651 ⟨1266898, by decide⟩ :=
  accepted_of_selected 12 368651 ⟨1266898, by decide⟩ ⟨12, 2, 0, 1266898, 368651, 3061, 65536⟩
    (by decide) selected_cut_45614

theorem unmarked_context_11_92162_1266899 : frontier 10 ⟨1266899, by decide⟩
    (prefixCache 11 92162) (prefixPartial 11 92162) = false := by
  decide +kernel

theorem node_context_11_92162_1266899 : EJMOriginalGlobalDAGData.nodes 10 ⟨1266899, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1266823, by decide⟩,⟨663554, by decide⟩,⟨1266898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92162_1266899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92162 ⟨1266899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92162
    ⟨1266899, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1266823, by decide⟩,⟨663554, by decide⟩,⟨1266898, by decide⟩]) unmarked_context_11_92162_1266899 node_context_11_92162_1266899
  intro a
  fin_cases a
  · exact context_12_368648_448748
  · exact context_12_368649_1266823
  · exact context_12_368650_663554
  · exact context_12_368651_1266898

theorem selected_cut_45615 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 368652) = some ⟨12, 1, 0, 448748, 368652, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368652_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368652 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 368652 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 368652, 1, 65536⟩
    (by decide) selected_cut_45615

theorem selected_cut_45616 : selected 9 ⟨1266955, by decide⟩
    (prefixPartial 12 368653) = some ⟨12, 2, 0, 1266955, 368653, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_368653_1266955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368653 ⟨1266955, by decide⟩ :=
  accepted_of_selected 12 368653 ⟨1266955, by decide⟩ ⟨12, 2, 0, 1266955, 368653, 2537, 65536⟩
    (by decide) selected_cut_45616

theorem selected_cut_45617 : selected 9 ⟨1266999, by decide⟩
    (prefixPartial 12 368654) = some ⟨12, 2, 0, 1266999, 368654, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_368654_1266999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368654 ⟨1266999, by decide⟩ :=
  accepted_of_selected 12 368654 ⟨1266999, by decide⟩ ⟨12, 2, 0, 1266999, 368654, 2413, 65536⟩
    (by decide) selected_cut_45617

theorem selected_cut_45618 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 368655) = some ⟨12, 1, 0, 760511, 368655, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368655_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368655 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 368655 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 368655, 1, 65536⟩
    (by decide) selected_cut_45618

theorem unmarked_context_11_92163_1267000 : frontier 10 ⟨1267000, by decide⟩
    (prefixCache 11 92163) (prefixPartial 11 92163) = false := by
  decide +kernel

theorem node_context_11_92163_1267000 : EJMOriginalGlobalDAGData.nodes 10 ⟨1267000, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1266955, by decide⟩,⟨1266999, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92163_1267000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92163 ⟨1267000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92163
    ⟨1267000, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1266955, by decide⟩,⟨1266999, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_92163_1267000 node_context_11_92163_1267000
  intro a
  fin_cases a
  · exact context_12_368652_448748
  · exact context_12_368653_1266955
  · exact context_12_368654_1266999
  · exact context_12_368655_760511

theorem unmarked_context_10_23040_1267001 : frontier 11 ⟨1267001, by decide⟩
    (prefixCache 10 23040) (prefixPartial 10 23040) = false := by
  decide +kernel

theorem node_context_10_23040_1267001 : EJMOriginalGlobalDAGData.nodes 11 ⟨1267001, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1266899, by decide⟩,⟨1267000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23040_1267001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23040 ⟨1267001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23040
    ⟨1267001, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1266899, by decide⟩,⟨1267000, by decide⟩]) unmarked_context_10_23040_1267001 node_context_10_23040_1267001
  intro a
  fin_cases a
  · exact context_11_92160_434745
  · exact context_11_92161_167448
  · exact context_11_92162_1266899
  · exact context_11_92163_1267000

theorem selected_cut_45619 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 368656) = some ⟨12, 1, 0, 985390, 368656, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368656_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368656 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 368656 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 368656, 1, 65536⟩
    (by decide) selected_cut_45619

theorem selected_cut_45620 : selected 9 ⟨1267041, by decide⟩
    (prefixPartial 12 368657) = some ⟨12, 2, 0, 1267041, 368657, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_368657_1267041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368657 ⟨1267041, by decide⟩ :=
  accepted_of_selected 12 368657 ⟨1267041, by decide⟩ ⟨12, 2, 0, 1267041, 368657, 2253, 65536⟩
    (by decide) selected_cut_45620

theorem selected_cut_45621 : selected 9 ⟨1267077, by decide⟩
    (prefixPartial 12 368658) = some ⟨12, 2, 0, 1267077, 368658, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_368658_1267077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368658 ⟨1267077, by decide⟩ :=
  accepted_of_selected 12 368658 ⟨1267077, by decide⟩ ⟨12, 2, 0, 1267077, 368658, 1965, 65536⟩
    (by decide) selected_cut_45621

theorem selected_cut_45622 : selected 9 ⟨1267122, by decide⟩
    (prefixPartial 12 368659) = some ⟨12, 2, 0, 1267122, 368659, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_368659_1267122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368659 ⟨1267122, by decide⟩ :=
  accepted_of_selected 12 368659 ⟨1267122, by decide⟩ ⟨12, 2, 0, 1267122, 368659, 2421, 65536⟩
    (by decide) selected_cut_45622

theorem unmarked_context_11_92164_1267123 : frontier 10 ⟨1267123, by decide⟩
    (prefixCache 11 92164) (prefixPartial 11 92164) = false := by
  decide +kernel

theorem node_context_11_92164_1267123 : EJMOriginalGlobalDAGData.nodes 10 ⟨1267123, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1267041, by decide⟩,⟨1267077, by decide⟩,⟨1267122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92164_1267123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92164 ⟨1267123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92164
    ⟨1267123, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1267041, by decide⟩,⟨1267077, by decide⟩,⟨1267122, by decide⟩]) unmarked_context_11_92164_1267123 node_context_11_92164_1267123
  intro a
  fin_cases a
  · exact context_12_368656_985390
  · exact context_12_368657_1267041
  · exact context_12_368658_1267077
  · exact context_12_368659_1267122

theorem selected_cut_45623 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 92165) = some ⟨11, 1, 0, 815620, 92165, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92165_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92165 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 92165 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 92165, 1, 262144⟩
    (by decide) selected_cut_45623

theorem selected_cut_45624 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 368664) = some ⟨12, 1, 0, 994572, 368664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368664_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368664 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 368664 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 368664, 1, 65536⟩
    (by decide) selected_cut_45624

theorem selected_cut_45625 : selected 9 ⟨1267185, by decide⟩
    (prefixPartial 12 368665) = some ⟨12, 2, 0, 1267185, 368665, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_368665_1267185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368665 ⟨1267185, by decide⟩ :=
  accepted_of_selected 12 368665 ⟨1267185, by decide⟩ ⟨12, 2, 0, 1267185, 368665, 2825, 65536⟩
    (by decide) selected_cut_45625

theorem selected_cut_45626 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 368666) = some ⟨12, 1, 0, 806997, 368666, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368666_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368666 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 368666 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 368666, 1, 65536⟩
    (by decide) selected_cut_45626

theorem selected_cut_45627 : selected 9 ⟨1267260, by decide⟩
    (prefixPartial 12 368667) = some ⟨12, 2, 0, 1267260, 368667, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_368667_1267260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368667 ⟨1267260, by decide⟩ :=
  accepted_of_selected 12 368667 ⟨1267260, by decide⟩ ⟨12, 2, 0, 1267260, 368667, 3173, 65536⟩
    (by decide) selected_cut_45627

theorem unmarked_context_11_92166_1267261 : frontier 10 ⟨1267261, by decide⟩
    (prefixCache 11 92166) (prefixPartial 11 92166) = false := by
  decide +kernel

theorem node_context_11_92166_1267261 : EJMOriginalGlobalDAGData.nodes 10 ⟨1267261, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1267185, by decide⟩,⟨806997, by decide⟩,⟨1267260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92166_1267261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92166 ⟨1267261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92166
    ⟨1267261, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1267185, by decide⟩,⟨806997, by decide⟩,⟨1267260, by decide⟩]) unmarked_context_11_92166_1267261 node_context_11_92166_1267261
  intro a
  fin_cases a
  · exact context_12_368664_994572
  · exact context_12_368665_1267185
  · exact context_12_368666_806997
  · exact context_12_368667_1267260

theorem selected_cut_45628 : selected 9 ⟨1267309, by decide⟩
    (prefixPartial 12 368668) = some ⟨12, 2, 0, 1267309, 368668, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_368668_1267309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368668 ⟨1267309, by decide⟩ :=
  accepted_of_selected 12 368668 ⟨1267309, by decide⟩ ⟨12, 2, 0, 1267309, 368668, 2505, 65536⟩
    (by decide) selected_cut_45628

theorem selected_cut_45629 : selected 9 ⟨1267359, by decide⟩
    (prefixPartial 12 368669) = some ⟨12, 2, 0, 1267359, 368669, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_368669_1267359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368669 ⟨1267359, by decide⟩ :=
  accepted_of_selected 12 368669 ⟨1267359, by decide⟩ ⟨12, 2, 0, 1267359, 368669, 2577, 65536⟩
    (by decide) selected_cut_45629

theorem selected_cut_45630 : selected 9 ⟨1267405, by decide⟩
    (prefixPartial 12 368670) = some ⟨12, 2, 0, 1267405, 368670, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_368670_1267405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368670 ⟨1267405, by decide⟩ :=
  accepted_of_selected 12 368670 ⟨1267405, by decide⟩ ⟨12, 2, 0, 1267405, 368670, 2445, 65536⟩
    (by decide) selected_cut_45630

theorem selected_cut_45631 : selected 9 ⟨1267454, by decide⟩
    (prefixPartial 12 368671) = some ⟨12, 2, 0, 1267454, 368671, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_368671_1267454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368671 ⟨1267454, by decide⟩ :=
  accepted_of_selected 12 368671 ⟨1267454, by decide⟩ ⟨12, 2, 0, 1267454, 368671, 2817, 65536⟩
    (by decide) selected_cut_45631

theorem unmarked_context_11_92167_1267455 : frontier 10 ⟨1267455, by decide⟩
    (prefixCache 11 92167) (prefixPartial 11 92167) = false := by
  decide +kernel

theorem node_context_11_92167_1267455 : EJMOriginalGlobalDAGData.nodes 10 ⟨1267455, by decide⟩ =
    .split (coordinate 11) (![⟨1267309, by decide⟩,⟨1267359, by decide⟩,⟨1267405, by decide⟩,⟨1267454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92167_1267455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92167 ⟨1267455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92167
    ⟨1267455, by decide⟩ (by decide) (![⟨1267309, by decide⟩,⟨1267359, by decide⟩,⟨1267405, by decide⟩,⟨1267454, by decide⟩]) unmarked_context_11_92167_1267455 node_context_11_92167_1267455
  intro a
  fin_cases a
  · exact context_12_368668_1267309
  · exact context_12_368669_1267359
  · exact context_12_368670_1267405
  · exact context_12_368671_1267454

theorem unmarked_context_10_23041_1267456 : frontier 11 ⟨1267456, by decide⟩
    (prefixCache 10 23041) (prefixPartial 10 23041) = false := by
  decide +kernel

theorem node_context_10_23041_1267456 : EJMOriginalGlobalDAGData.nodes 11 ⟨1267456, by decide⟩ =
    .split (coordinate 10) (![⟨1267123, by decide⟩,⟨815620, by decide⟩,⟨1267261, by decide⟩,⟨1267455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23041_1267456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23041 ⟨1267456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23041
    ⟨1267456, by decide⟩ (by decide) (![⟨1267123, by decide⟩,⟨815620, by decide⟩,⟨1267261, by decide⟩,⟨1267455, by decide⟩]) unmarked_context_10_23041_1267456 node_context_10_23041_1267456
  intro a
  fin_cases a
  · exact context_11_92164_1267123
  · exact context_11_92165_815620
  · exact context_11_92166_1267261
  · exact context_11_92167_1267455

theorem selected_cut_45632 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 368672) = some ⟨12, 1, 0, 435790, 368672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368672_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368672 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 368672 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 368672, 1, 65536⟩
    (by decide) selected_cut_45632

theorem selected_cut_45633 : selected 9 ⟨1267494, by decide⟩
    (prefixPartial 12 368673) = some ⟨12, 2, 0, 1267494, 368673, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_368673_1267494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368673 ⟨1267494, by decide⟩ :=
  accepted_of_selected 12 368673 ⟨1267494, by decide⟩ ⟨12, 2, 0, 1267494, 368673, 2205, 65536⟩
    (by decide) selected_cut_45633

theorem selected_cut_45634 : selected 9 ⟨1267529, by decide⟩
    (prefixPartial 12 368674) = some ⟨12, 2, 0, 1267529, 368674, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_368674_1267529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368674 ⟨1267529, by decide⟩ :=
  accepted_of_selected 12 368674 ⟨1267529, by decide⟩ ⟨12, 2, 0, 1267529, 368674, 1997, 65536⟩
    (by decide) selected_cut_45634

theorem selected_cut_45635 : selected 9 ⟨1267567, by decide⟩
    (prefixPartial 12 368675) = some ⟨12, 2, 0, 1267567, 368675, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_368675_1267567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368675 ⟨1267567, by decide⟩ :=
  accepted_of_selected 12 368675 ⟨1267567, by decide⟩ ⟨12, 2, 0, 1267567, 368675, 2265, 65536⟩
    (by decide) selected_cut_45635

theorem unmarked_context_11_92168_1267568 : frontier 10 ⟨1267568, by decide⟩
    (prefixCache 11 92168) (prefixPartial 11 92168) = false := by
  decide +kernel

theorem node_context_11_92168_1267568 : EJMOriginalGlobalDAGData.nodes 10 ⟨1267568, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1267494, by decide⟩,⟨1267529, by decide⟩,⟨1267567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92168_1267568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92168 ⟨1267568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92168
    ⟨1267568, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1267494, by decide⟩,⟨1267529, by decide⟩,⟨1267567, by decide⟩]) unmarked_context_11_92168_1267568 node_context_11_92168_1267568
  intro a
  fin_cases a
  · exact context_12_368672_435790
  · exact context_12_368673_1267494
  · exact context_12_368674_1267529
  · exact context_12_368675_1267567

theorem selected_cut_45636 : selected 9 ⟨1267624, by decide⟩
    (prefixPartial 12 368676) = some ⟨12, 2, 0, 1267624, 368676, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_368676_1267624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368676 ⟨1267624, by decide⟩ :=
  accepted_of_selected 12 368676 ⟨1267624, by decide⟩ ⟨12, 2, 0, 1267624, 368676, 1881, 65536⟩
    (by decide) selected_cut_45636

theorem selected_cut_45637 : selected 9 ⟨1267692, by decide⟩
    (prefixPartial 12 368677) = some ⟨12, 2, 0, 1267692, 368677, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_368677_1267692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368677 ⟨1267692, by decide⟩ :=
  accepted_of_selected 12 368677 ⟨1267692, by decide⟩ ⟨12, 2, 0, 1267692, 368677, 3153, 65536⟩
    (by decide) selected_cut_45637

theorem selected_cut_45638 : selected 9 ⟨1267752, by decide⟩
    (prefixPartial 12 368678) = some ⟨12, 2, 0, 1267752, 368678, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_368678_1267752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368678 ⟨1267752, by decide⟩ :=
  accepted_of_selected 12 368678 ⟨1267752, by decide⟩ ⟨12, 2, 0, 1267752, 368678, 2993, 65536⟩
    (by decide) selected_cut_45638

theorem selected_cut_45639 : selected 9 ⟨1267816, by decide⟩
    (prefixPartial 12 368679) = some ⟨12, 2, 0, 1267816, 368679, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_368679_1267816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368679 ⟨1267816, by decide⟩ :=
  accepted_of_selected 12 368679 ⟨1267816, by decide⟩ ⟨12, 2, 0, 1267816, 368679, 3449, 65536⟩
    (by decide) selected_cut_45639

theorem unmarked_context_11_92169_1267817 : frontier 10 ⟨1267817, by decide⟩
    (prefixCache 11 92169) (prefixPartial 11 92169) = false := by
  decide +kernel

theorem node_context_11_92169_1267817 : EJMOriginalGlobalDAGData.nodes 10 ⟨1267817, by decide⟩ =
    .split (coordinate 11) (![⟨1267624, by decide⟩,⟨1267692, by decide⟩,⟨1267752, by decide⟩,⟨1267816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92169_1267817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92169 ⟨1267817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92169
    ⟨1267817, by decide⟩ (by decide) (![⟨1267624, by decide⟩,⟨1267692, by decide⟩,⟨1267752, by decide⟩,⟨1267816, by decide⟩]) unmarked_context_11_92169_1267817 node_context_11_92169_1267817
  intro a
  fin_cases a
  · exact context_12_368676_1267624
  · exact context_12_368677_1267692
  · exact context_12_368678_1267752
  · exact context_12_368679_1267816

theorem selected_cut_45640 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 368680) = some ⟨12, 1, 0, 435790, 368680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368680_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368680 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 368680 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 368680, 1, 65536⟩
    (by decide) selected_cut_45640

theorem selected_cut_45641 : selected 9 ⟨1267861, by decide⟩
    (prefixPartial 12 368681) = some ⟨12, 2, 0, 1267861, 368681, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_368681_1267861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368681 ⟨1267861, by decide⟩ :=
  accepted_of_selected 12 368681 ⟨1267861, by decide⟩ ⟨12, 2, 0, 1267861, 368681, 2473, 65536⟩
    (by decide) selected_cut_45641

theorem selected_cut_45642 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 368682) = some ⟨12, 1, 0, 224365, 368682, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368682_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368682 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 368682 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 368682, 1, 65536⟩
    (by decide) selected_cut_45642

theorem selected_cut_45643 : selected 9 ⟨1267911, by decide⟩
    (prefixPartial 12 368683) = some ⟨12, 2, 0, 1267911, 368683, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_368683_1267911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368683 ⟨1267911, by decide⟩ :=
  accepted_of_selected 12 368683 ⟨1267911, by decide⟩ ⟨12, 2, 0, 1267911, 368683, 2701, 65536⟩
    (by decide) selected_cut_45643

theorem unmarked_context_11_92170_1267912 : frontier 10 ⟨1267912, by decide⟩
    (prefixCache 11 92170) (prefixPartial 11 92170) = false := by
  decide +kernel

theorem node_context_11_92170_1267912 : EJMOriginalGlobalDAGData.nodes 10 ⟨1267912, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1267861, by decide⟩,⟨224365, by decide⟩,⟨1267911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92170_1267912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92170 ⟨1267912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92170
    ⟨1267912, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1267861, by decide⟩,⟨224365, by decide⟩,⟨1267911, by decide⟩]) unmarked_context_11_92170_1267912 node_context_11_92170_1267912
  intro a
  fin_cases a
  · exact context_12_368680_435790
  · exact context_12_368681_1267861
  · exact context_12_368682_224365
  · exact context_12_368683_1267911

theorem selected_cut_45644 : selected 9 ⟨1267961, by decide⟩
    (prefixPartial 12 368684) = some ⟨12, 2, 0, 1267961, 368684, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_368684_1267961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368684 ⟨1267961, by decide⟩ :=
  accepted_of_selected 12 368684 ⟨1267961, by decide⟩ ⟨12, 2, 0, 1267961, 368684, 2557, 65536⟩
    (by decide) selected_cut_45644

theorem selected_cut_45645 : selected 9 ⟨1268007, by decide⟩
    (prefixPartial 12 368685) = some ⟨12, 2, 0, 1268007, 368685, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_368685_1268007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368685 ⟨1268007, by decide⟩ :=
  accepted_of_selected 12 368685 ⟨1268007, by decide⟩ ⟨12, 2, 0, 1268007, 368685, 2585, 65536⟩
    (by decide) selected_cut_45645

theorem selected_cut_45646 : selected 9 ⟨1268055, by decide⟩
    (prefixPartial 12 368686) = some ⟨12, 2, 0, 1268055, 368686, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_368686_1268055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368686 ⟨1268055, by decide⟩ :=
  accepted_of_selected 12 368686 ⟨1268055, by decide⟩ ⟨12, 2, 0, 1268055, 368686, 2541, 65536⟩
    (by decide) selected_cut_45646

theorem selected_cut_45647 : selected 9 ⟨1268109, by decide⟩
    (prefixPartial 12 368687) = some ⟨12, 2, 0, 1268109, 368687, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_368687_1268109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368687 ⟨1268109, by decide⟩ :=
  accepted_of_selected 12 368687 ⟨1268109, by decide⟩ ⟨12, 2, 0, 1268109, 368687, 2681, 65536⟩
    (by decide) selected_cut_45647

theorem unmarked_context_11_92171_1268110 : frontier 10 ⟨1268110, by decide⟩
    (prefixCache 11 92171) (prefixPartial 11 92171) = false := by
  decide +kernel

theorem node_context_11_92171_1268110 : EJMOriginalGlobalDAGData.nodes 10 ⟨1268110, by decide⟩ =
    .split (coordinate 11) (![⟨1267961, by decide⟩,⟨1268007, by decide⟩,⟨1268055, by decide⟩,⟨1268109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92171_1268110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92171 ⟨1268110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92171
    ⟨1268110, by decide⟩ (by decide) (![⟨1267961, by decide⟩,⟨1268007, by decide⟩,⟨1268055, by decide⟩,⟨1268109, by decide⟩]) unmarked_context_11_92171_1268110 node_context_11_92171_1268110
  intro a
  fin_cases a
  · exact context_12_368684_1267961
  · exact context_12_368685_1268007
  · exact context_12_368686_1268055
  · exact context_12_368687_1268109

theorem unmarked_context_10_23042_1268111 : frontier 11 ⟨1268111, by decide⟩
    (prefixCache 10 23042) (prefixPartial 10 23042) = false := by
  decide +kernel

theorem node_context_10_23042_1268111 : EJMOriginalGlobalDAGData.nodes 11 ⟨1268111, by decide⟩ =
    .split (coordinate 10) (![⟨1267568, by decide⟩,⟨1267817, by decide⟩,⟨1267912, by decide⟩,⟨1268110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23042_1268111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23042 ⟨1268111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23042
    ⟨1268111, by decide⟩ (by decide) (![⟨1267568, by decide⟩,⟨1267817, by decide⟩,⟨1267912, by decide⟩,⟨1268110, by decide⟩]) unmarked_context_10_23042_1268111 node_context_10_23042_1268111
  intro a
  fin_cases a
  · exact context_11_92168_1267568
  · exact context_11_92169_1267817
  · exact context_11_92170_1267912
  · exact context_11_92171_1268110

theorem selected_cut_45648 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 368688) = some ⟨12, 1, 0, 985390, 368688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368688_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368688 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 368688 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 368688, 1, 65536⟩
    (by decide) selected_cut_45648

theorem selected_cut_45649 : selected 9 ⟨1268143, by decide⟩
    (prefixPartial 12 368689) = some ⟨12, 2, 0, 1268143, 368689, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_368689_1268143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368689 ⟨1268143, by decide⟩ :=
  accepted_of_selected 12 368689 ⟨1268143, by decide⟩ ⟨12, 2, 0, 1268143, 368689, 1841, 65536⟩
    (by decide) selected_cut_45649

theorem selected_cut_45650 : selected 9 ⟨1268171, by decide⟩
    (prefixPartial 12 368690) = some ⟨12, 2, 0, 1268171, 368690, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_368690_1268171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368690 ⟨1268171, by decide⟩ :=
  accepted_of_selected 12 368690 ⟨1268171, by decide⟩ ⟨12, 2, 0, 1268171, 368690, 1745, 65536⟩
    (by decide) selected_cut_45650

theorem selected_cut_45651 : selected 9 ⟨1268203, by decide⟩
    (prefixPartial 12 368691) = some ⟨12, 2, 0, 1268203, 368691, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_368691_1268203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368691 ⟨1268203, by decide⟩ :=
  accepted_of_selected 12 368691 ⟨1268203, by decide⟩ ⟨12, 2, 0, 1268203, 368691, 2085, 65536⟩
    (by decide) selected_cut_45651

theorem unmarked_context_11_92172_1268204 : frontier 10 ⟨1268204, by decide⟩
    (prefixCache 11 92172) (prefixPartial 11 92172) = false := by
  decide +kernel

theorem node_context_11_92172_1268204 : EJMOriginalGlobalDAGData.nodes 10 ⟨1268204, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1268143, by decide⟩,⟨1268171, by decide⟩,⟨1268203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92172_1268204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92172 ⟨1268204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92172
    ⟨1268204, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1268143, by decide⟩,⟨1268171, by decide⟩,⟨1268203, by decide⟩]) unmarked_context_11_92172_1268204 node_context_11_92172_1268204
  intro a
  fin_cases a
  · exact context_12_368688_985390
  · exact context_12_368689_1268143
  · exact context_12_368690_1268171
  · exact context_12_368691_1268203

theorem selected_cut_45652 : selected 9 ⟨1268256, by decide⟩
    (prefixPartial 12 368692) = some ⟨12, 2, 0, 1268256, 368692, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_368692_1268256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368692 ⟨1268256, by decide⟩ :=
  accepted_of_selected 12 368692 ⟨1268256, by decide⟩ ⟨12, 2, 0, 1268256, 368692, 2585, 65536⟩
    (by decide) selected_cut_45652

theorem selected_cut_45653 : selected 9 ⟨1268298, by decide⟩
    (prefixPartial 12 368693) = some ⟨12, 2, 0, 1268298, 368693, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_368693_1268298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368693 ⟨1268298, by decide⟩ :=
  accepted_of_selected 12 368693 ⟨1268298, by decide⟩ ⟨12, 2, 0, 1268298, 368693, 2289, 65536⟩
    (by decide) selected_cut_45653

theorem selected_cut_45654 : selected 9 ⟨1268341, by decide⟩
    (prefixPartial 12 368694) = some ⟨12, 2, 0, 1268341, 368694, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_368694_1268341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368694 ⟨1268341, by decide⟩ :=
  accepted_of_selected 12 368694 ⟨1268341, by decide⟩ ⟨12, 2, 0, 1268341, 368694, 2341, 65536⟩
    (by decide) selected_cut_45654

theorem selected_cut_45655 : selected 9 ⟨1268390, by decide⟩
    (prefixPartial 12 368695) = some ⟨12, 2, 0, 1268390, 368695, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_368695_1268390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368695 ⟨1268390, by decide⟩ :=
  accepted_of_selected 12 368695 ⟨1268390, by decide⟩ ⟨12, 2, 0, 1268390, 368695, 2757, 65536⟩
    (by decide) selected_cut_45655

theorem unmarked_context_11_92173_1268391 : frontier 10 ⟨1268391, by decide⟩
    (prefixCache 11 92173) (prefixPartial 11 92173) = false := by
  decide +kernel

theorem node_context_11_92173_1268391 : EJMOriginalGlobalDAGData.nodes 10 ⟨1268391, by decide⟩ =
    .split (coordinate 11) (![⟨1268256, by decide⟩,⟨1268298, by decide⟩,⟨1268341, by decide⟩,⟨1268390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92173_1268391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92173 ⟨1268391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92173
    ⟨1268391, by decide⟩ (by decide) (![⟨1268256, by decide⟩,⟨1268298, by decide⟩,⟨1268341, by decide⟩,⟨1268390, by decide⟩]) unmarked_context_11_92173_1268391 node_context_11_92173_1268391
  intro a
  fin_cases a
  · exact context_12_368692_1268256
  · exact context_12_368693_1268298
  · exact context_12_368694_1268341
  · exact context_12_368695_1268390

theorem selected_cut_45656 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 368696) = some ⟨12, 1, 0, 994572, 368696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368696_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368696 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 368696 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 368696, 1, 65536⟩
    (by decide) selected_cut_45656

theorem selected_cut_45657 : selected 9 ⟨1268426, by decide⟩
    (prefixPartial 12 368697) = some ⟨12, 2, 0, 1268426, 368697, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_368697_1268426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368697 ⟨1268426, by decide⟩ :=
  accepted_of_selected 12 368697 ⟨1268426, by decide⟩ ⟨12, 2, 0, 1268426, 368697, 2193, 65536⟩
    (by decide) selected_cut_45657

theorem selected_cut_45658 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 368698) = some ⟨12, 1, 0, 806997, 368698, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368698_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368698 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 368698 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 368698, 1, 65536⟩
    (by decide) selected_cut_45658

theorem selected_cut_45659 : selected 9 ⟨1268484, by decide⟩
    (prefixPartial 12 368699) = some ⟨12, 2, 0, 1268484, 368699, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_368699_1268484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368699 ⟨1268484, by decide⟩ :=
  accepted_of_selected 12 368699 ⟨1268484, by decide⟩ ⟨12, 2, 0, 1268484, 368699, 2569, 65536⟩
    (by decide) selected_cut_45659

theorem unmarked_context_11_92174_1268485 : frontier 10 ⟨1268485, by decide⟩
    (prefixCache 11 92174) (prefixPartial 11 92174) = false := by
  decide +kernel

theorem node_context_11_92174_1268485 : EJMOriginalGlobalDAGData.nodes 10 ⟨1268485, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1268426, by decide⟩,⟨806997, by decide⟩,⟨1268484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92174_1268485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92174 ⟨1268485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92174
    ⟨1268485, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1268426, by decide⟩,⟨806997, by decide⟩,⟨1268484, by decide⟩]) unmarked_context_11_92174_1268485 node_context_11_92174_1268485
  intro a
  fin_cases a
  · exact context_12_368696_994572
  · exact context_12_368697_1268426
  · exact context_12_368698_806997
  · exact context_12_368699_1268484

theorem selected_cut_45660 : selected 10 ⟨1268554, by decide⟩
    (prefixPartial 11 92175) = some ⟨11, 2, 0, 1268554, 92175, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_92175_1268554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92175 ⟨1268554, by decide⟩ :=
  accepted_of_selected 11 92175 ⟨1268554, by decide⟩ ⟨11, 2, 0, 1268554, 92175, 3785, 262144⟩
    (by decide) selected_cut_45660

theorem unmarked_context_10_23043_1268555 : frontier 11 ⟨1268555, by decide⟩
    (prefixCache 10 23043) (prefixPartial 10 23043) = false := by
  decide +kernel

theorem node_context_10_23043_1268555 : EJMOriginalGlobalDAGData.nodes 11 ⟨1268555, by decide⟩ =
    .split (coordinate 10) (![⟨1268204, by decide⟩,⟨1268391, by decide⟩,⟨1268485, by decide⟩,⟨1268554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23043_1268555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23043 ⟨1268555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23043
    ⟨1268555, by decide⟩ (by decide) (![⟨1268204, by decide⟩,⟨1268391, by decide⟩,⟨1268485, by decide⟩,⟨1268554, by decide⟩]) unmarked_context_10_23043_1268555 node_context_10_23043_1268555
  intro a
  fin_cases a
  · exact context_11_92172_1268204
  · exact context_11_92173_1268391
  · exact context_11_92174_1268485
  · exact context_11_92175_1268554

theorem unmarked_context_9_5760_1268556 : frontier 12 ⟨1268556, by decide⟩
    (prefixCache 9 5760) (prefixPartial 9 5760) = false := by
  decide +kernel

theorem node_context_9_5760_1268556 : EJMOriginalGlobalDAGData.nodes 12 ⟨1268556, by decide⟩ =
    .split (coordinate 9) (![⟨1267001, by decide⟩,⟨1267456, by decide⟩,⟨1268111, by decide⟩,⟨1268555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5760_1268556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5760 ⟨1268556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5760
    ⟨1268556, by decide⟩ (by decide) (![⟨1267001, by decide⟩,⟨1267456, by decide⟩,⟨1268111, by decide⟩,⟨1268555, by decide⟩]) unmarked_context_9_5760_1268556 node_context_9_5760_1268556
  intro a
  fin_cases a
  · exact context_10_23040_1267001
  · exact context_10_23041_1267456
  · exact context_10_23042_1268111
  · exact context_10_23043_1268555

theorem selected_cut_45661 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92176) = some ⟨11, 1, 0, 907917, 92176, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92176_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92176 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92176 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92176, 1, 262144⟩
    (by decide) selected_cut_45661

theorem selected_cut_45662 : selected 9 ⟨1268597, by decide⟩
    (prefixPartial 12 368708) = some ⟨12, 2, 0, 1268597, 368708, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_368708_1268597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368708 ⟨1268597, by decide⟩ :=
  accepted_of_selected 12 368708 ⟨1268597, by decide⟩ ⟨12, 2, 0, 1268597, 368708, 2069, 65536⟩
    (by decide) selected_cut_45662

theorem selected_cut_45663 : selected 9 ⟨692443, by decide⟩
    (prefixPartial 12 368709) = some ⟨12, 1, 0, 692443, 368709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368709_692443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368709 ⟨692443, by decide⟩ :=
  accepted_of_selected 12 368709 ⟨692443, by decide⟩ ⟨12, 1, 0, 692443, 368709, 1, 65536⟩
    (by decide) selected_cut_45663

theorem selected_cut_45664 : selected 9 ⟨1268636, by decide⟩
    (prefixPartial 12 368710) = some ⟨12, 2, 0, 1268636, 368710, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_368710_1268636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368710 ⟨1268636, by decide⟩ :=
  accepted_of_selected 12 368710 ⟨1268636, by decide⟩ ⟨12, 2, 0, 1268636, 368710, 2069, 65536⟩
    (by decide) selected_cut_45664

theorem selected_cut_45665 : selected 9 ⟨1268689, by decide⟩
    (prefixPartial 12 368711) = some ⟨12, 2, 0, 1268689, 368711, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_368711_1268689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368711 ⟨1268689, by decide⟩ :=
  accepted_of_selected 12 368711 ⟨1268689, by decide⟩ ⟨12, 2, 0, 1268689, 368711, 2393, 65536⟩
    (by decide) selected_cut_45665

theorem unmarked_context_11_92177_1268690 : frontier 10 ⟨1268690, by decide⟩
    (prefixCache 11 92177) (prefixPartial 11 92177) = false := by
  decide +kernel

theorem node_context_11_92177_1268690 : EJMOriginalGlobalDAGData.nodes 10 ⟨1268690, by decide⟩ =
    .split (coordinate 11) (![⟨1268597, by decide⟩,⟨692443, by decide⟩,⟨1268636, by decide⟩,⟨1268689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92177_1268690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92177 ⟨1268690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92177
    ⟨1268690, by decide⟩ (by decide) (![⟨1268597, by decide⟩,⟨692443, by decide⟩,⟨1268636, by decide⟩,⟨1268689, by decide⟩]) unmarked_context_11_92177_1268690 node_context_11_92177_1268690
  intro a
  fin_cases a
  · exact context_12_368708_1268597
  · exact context_12_368709_692443
  · exact context_12_368710_1268636
  · exact context_12_368711_1268689

theorem selected_cut_45666 : selected 9 ⟨1268718, by decide⟩
    (prefixPartial 12 368712) = some ⟨12, 2, 0, 1268718, 368712, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_368712_1268718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368712 ⟨1268718, by decide⟩ :=
  accepted_of_selected 12 368712 ⟨1268718, by decide⟩ ⟨12, 2, 0, 1268718, 368712, 1693, 65536⟩
    (by decide) selected_cut_45666

theorem selected_cut_45667 : selected 9 ⟨1268752, by decide⟩
    (prefixPartial 12 368713) = some ⟨12, 2, 0, 1268752, 368713, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_368713_1268752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368713 ⟨1268752, by decide⟩ :=
  accepted_of_selected 12 368713 ⟨1268752, by decide⟩ ⟨12, 2, 0, 1268752, 368713, 1781, 65536⟩
    (by decide) selected_cut_45667

theorem selected_cut_45668 : selected 9 ⟨663554, by decide⟩
    (prefixPartial 12 368714) = some ⟨12, 1, 0, 663554, 368714, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368714_663554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368714 ⟨663554, by decide⟩ :=
  accepted_of_selected 12 368714 ⟨663554, by decide⟩ ⟨12, 1, 0, 663554, 368714, 1, 65536⟩
    (by decide) selected_cut_45668

theorem selected_cut_45669 : selected 9 ⟨1268801, by decide⟩
    (prefixPartial 12 368715) = some ⟨12, 2, 0, 1268801, 368715, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_368715_1268801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368715 ⟨1268801, by decide⟩ :=
  accepted_of_selected 12 368715 ⟨1268801, by decide⟩ ⟨12, 2, 0, 1268801, 368715, 2121, 65536⟩
    (by decide) selected_cut_45669

theorem unmarked_context_11_92178_1268802 : frontier 10 ⟨1268802, by decide⟩
    (prefixCache 11 92178) (prefixPartial 11 92178) = false := by
  decide +kernel

theorem node_context_11_92178_1268802 : EJMOriginalGlobalDAGData.nodes 10 ⟨1268802, by decide⟩ =
    .split (coordinate 11) (![⟨1268718, by decide⟩,⟨1268752, by decide⟩,⟨663554, by decide⟩,⟨1268801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92178_1268802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92178 ⟨1268802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92178
    ⟨1268802, by decide⟩ (by decide) (![⟨1268718, by decide⟩,⟨1268752, by decide⟩,⟨663554, by decide⟩,⟨1268801, by decide⟩]) unmarked_context_11_92178_1268802 node_context_11_92178_1268802
  intro a
  fin_cases a
  · exact context_12_368712_1268718
  · exact context_12_368713_1268752
  · exact context_12_368714_663554
  · exact context_12_368715_1268801

theorem selected_cut_45670 : selected 9 ⟨1268828, by decide⟩
    (prefixPartial 12 368716) = some ⟨12, 2, 0, 1268828, 368716, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_368716_1268828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368716 ⟨1268828, by decide⟩ :=
  accepted_of_selected 12 368716 ⟨1268828, by decide⟩ ⟨12, 2, 0, 1268828, 368716, 1593, 65536⟩
    (by decide) selected_cut_45670

theorem selected_cut_45671 : selected 9 ⟨1268858, by decide⟩
    (prefixPartial 12 368717) = some ⟨12, 2, 0, 1268858, 368717, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_368717_1268858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368717 ⟨1268858, by decide⟩ :=
  accepted_of_selected 12 368717 ⟨1268858, by decide⟩ ⟨12, 2, 0, 1268858, 368717, 1653, 65536⟩
    (by decide) selected_cut_45671

theorem selected_cut_45672 : selected 9 ⟨1268895, by decide⟩
    (prefixPartial 12 368718) = some ⟨12, 2, 0, 1268895, 368718, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_368718_1268895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368718 ⟨1268895, by decide⟩ :=
  accepted_of_selected 12 368718 ⟨1268895, by decide⟩ ⟨12, 2, 0, 1268895, 368718, 1761, 65536⟩
    (by decide) selected_cut_45672

theorem selected_cut_45673 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 368719) = some ⟨12, 1, 0, 760511, 368719, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368719_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368719 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 368719 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 368719, 1, 65536⟩
    (by decide) selected_cut_45673

theorem unmarked_context_11_92179_1268896 : frontier 10 ⟨1268896, by decide⟩
    (prefixCache 11 92179) (prefixPartial 11 92179) = false := by
  decide +kernel

theorem node_context_11_92179_1268896 : EJMOriginalGlobalDAGData.nodes 10 ⟨1268896, by decide⟩ =
    .split (coordinate 11) (![⟨1268828, by decide⟩,⟨1268858, by decide⟩,⟨1268895, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92179_1268896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92179 ⟨1268896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92179
    ⟨1268896, by decide⟩ (by decide) (![⟨1268828, by decide⟩,⟨1268858, by decide⟩,⟨1268895, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_92179_1268896 node_context_11_92179_1268896
  intro a
  fin_cases a
  · exact context_12_368716_1268828
  · exact context_12_368717_1268858
  · exact context_12_368718_1268895
  · exact context_12_368719_760511

theorem unmarked_context_10_23044_1268897 : frontier 11 ⟨1268897, by decide⟩
    (prefixCache 10 23044) (prefixPartial 10 23044) = false := by
  decide +kernel

theorem node_context_10_23044_1268897 : EJMOriginalGlobalDAGData.nodes 11 ⟨1268897, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1268690, by decide⟩,⟨1268802, by decide⟩,⟨1268896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23044_1268897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23044 ⟨1268897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23044
    ⟨1268897, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1268690, by decide⟩,⟨1268802, by decide⟩,⟨1268896, by decide⟩]) unmarked_context_10_23044_1268897 node_context_10_23044_1268897
  intro a
  fin_cases a
  · exact context_11_92176_907917
  · exact context_11_92177_1268690
  · exact context_11_92178_1268802
  · exact context_11_92179_1268896

theorem selected_cut_45674 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23045) = some ⟨10, 1, 0, 893098, 23045, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23045_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23045 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23045 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23045, 1, 1048576⟩
    (by decide) selected_cut_45674

theorem selected_cut_45675 : selected 10 ⟨1268949, by decide⟩
    (prefixPartial 11 92184) = some ⟨11, 2, 0, 1268949, 92184, 2849, 262144⟩ := by
  decide +kernel

theorem context_11_92184_1268949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92184 ⟨1268949, by decide⟩ :=
  accepted_of_selected 11 92184 ⟨1268949, by decide⟩ ⟨11, 2, 0, 1268949, 92184, 2849, 262144⟩
    (by decide) selected_cut_45675

theorem selected_cut_45676 : selected 9 ⟨1268987, by decide⟩
    (prefixPartial 12 368740) = some ⟨12, 2, 0, 1268987, 368740, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_368740_1268987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368740 ⟨1268987, by decide⟩ :=
  accepted_of_selected 12 368740 ⟨1268987, by decide⟩ ⟨12, 2, 0, 1268987, 368740, 1993, 65536⟩
    (by decide) selected_cut_45676

theorem selected_cut_45677 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 368741) = some ⟨12, 1, 0, 1256866, 368741, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368741_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368741 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 368741 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 368741, 1, 65536⟩
    (by decide) selected_cut_45677

theorem selected_cut_45678 : selected 9 ⟨1269018, by decide⟩
    (prefixPartial 12 368742) = some ⟨12, 2, 0, 1269018, 368742, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_368742_1269018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368742 ⟨1269018, by decide⟩ :=
  accepted_of_selected 12 368742 ⟨1269018, by decide⟩ ⟨12, 2, 0, 1269018, 368742, 1881, 65536⟩
    (by decide) selected_cut_45678

theorem selected_cut_45679 : selected 9 ⟨1269065, by decide⟩
    (prefixPartial 12 368743) = some ⟨12, 2, 0, 1269065, 368743, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_368743_1269065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368743 ⟨1269065, by decide⟩ :=
  accepted_of_selected 12 368743 ⟨1269065, by decide⟩ ⟨12, 2, 0, 1269065, 368743, 2033, 65536⟩
    (by decide) selected_cut_45679

theorem unmarked_context_11_92185_1269066 : frontier 10 ⟨1269066, by decide⟩
    (prefixCache 11 92185) (prefixPartial 11 92185) = false := by
  decide +kernel

theorem node_context_11_92185_1269066 : EJMOriginalGlobalDAGData.nodes 10 ⟨1269066, by decide⟩ =
    .split (coordinate 11) (![⟨1268987, by decide⟩,⟨1256866, by decide⟩,⟨1269018, by decide⟩,⟨1269065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92185_1269066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92185 ⟨1269066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92185
    ⟨1269066, by decide⟩ (by decide) (![⟨1268987, by decide⟩,⟨1256866, by decide⟩,⟨1269018, by decide⟩,⟨1269065, by decide⟩]) unmarked_context_11_92185_1269066 node_context_11_92185_1269066
  intro a
  fin_cases a
  · exact context_12_368740_1268987
  · exact context_12_368741_1256866
  · exact context_12_368742_1269018
  · exact context_12_368743_1269065

theorem selected_cut_45680 : selected 10 ⟨1269095, by decide⟩
    (prefixPartial 11 92186) = some ⟨11, 2, 0, 1269095, 92186, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_92186_1269095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92186 ⟨1269095, by decide⟩ :=
  accepted_of_selected 11 92186 ⟨1269095, by decide⟩ ⟨11, 2, 0, 1269095, 92186, 1653, 262144⟩
    (by decide) selected_cut_45680

theorem selected_cut_45681 : selected 9 ⟨1269126, by decide⟩
    (prefixPartial 12 368748) = some ⟨12, 2, 0, 1269126, 368748, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_368748_1269126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368748 ⟨1269126, by decide⟩ :=
  accepted_of_selected 12 368748 ⟨1269126, by decide⟩ ⟨12, 2, 0, 1269126, 368748, 1629, 65536⟩
    (by decide) selected_cut_45681

theorem selected_cut_45682 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 368749) = some ⟨12, 1, 0, 1256866, 368749, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368749_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368749 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 368749 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 368749, 1, 65536⟩
    (by decide) selected_cut_45682

theorem selected_cut_45683 : selected 9 ⟨1269155, by decide⟩
    (prefixPartial 12 368750) = some ⟨12, 2, 0, 1269155, 368750, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_368750_1269155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368750 ⟨1269155, by decide⟩ :=
  accepted_of_selected 12 368750 ⟨1269155, by decide⟩ ⟨12, 2, 0, 1269155, 368750, 1633, 65536⟩
    (by decide) selected_cut_45683

theorem selected_cut_45684 : selected 9 ⟨1269182, by decide⟩
    (prefixPartial 12 368751) = some ⟨12, 2, 0, 1269182, 368751, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_368751_1269182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368751 ⟨1269182, by decide⟩ :=
  accepted_of_selected 12 368751 ⟨1269182, by decide⟩ ⟨12, 2, 0, 1269182, 368751, 1777, 65536⟩
    (by decide) selected_cut_45684

theorem unmarked_context_11_92187_1269183 : frontier 10 ⟨1269183, by decide⟩
    (prefixCache 11 92187) (prefixPartial 11 92187) = false := by
  decide +kernel

theorem node_context_11_92187_1269183 : EJMOriginalGlobalDAGData.nodes 10 ⟨1269183, by decide⟩ =
    .split (coordinate 11) (![⟨1269126, by decide⟩,⟨1256866, by decide⟩,⟨1269155, by decide⟩,⟨1269182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92187_1269183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92187 ⟨1269183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92187
    ⟨1269183, by decide⟩ (by decide) (![⟨1269126, by decide⟩,⟨1256866, by decide⟩,⟨1269155, by decide⟩,⟨1269182, by decide⟩]) unmarked_context_11_92187_1269183 node_context_11_92187_1269183
  intro a
  fin_cases a
  · exact context_12_368748_1269126
  · exact context_12_368749_1256866
  · exact context_12_368750_1269155
  · exact context_12_368751_1269182

theorem unmarked_context_10_23046_1269184 : frontier 11 ⟨1269184, by decide⟩
    (prefixCache 10 23046) (prefixPartial 10 23046) = false := by
  decide +kernel

theorem node_context_10_23046_1269184 : EJMOriginalGlobalDAGData.nodes 11 ⟨1269184, by decide⟩ =
    .split (coordinate 10) (![⟨1268949, by decide⟩,⟨1269066, by decide⟩,⟨1269095, by decide⟩,⟨1269183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23046_1269184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23046 ⟨1269184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23046
    ⟨1269184, by decide⟩ (by decide) (![⟨1268949, by decide⟩,⟨1269066, by decide⟩,⟨1269095, by decide⟩,⟨1269183, by decide⟩]) unmarked_context_10_23046_1269184 node_context_10_23046_1269184
  intro a
  fin_cases a
  · exact context_11_92184_1268949
  · exact context_11_92185_1269066
  · exact context_11_92186_1269095
  · exact context_11_92187_1269183

theorem selected_cut_45685 : selected 10 ⟨1269247, by decide⟩
    (prefixPartial 11 92188) = some ⟨11, 2, 0, 1269247, 92188, 3765, 262144⟩ := by
  decide +kernel

theorem context_11_92188_1269247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92188 ⟨1269247, by decide⟩ :=
  accepted_of_selected 11 92188 ⟨1269247, by decide⟩ ⟨11, 2, 0, 1269247, 92188, 3765, 262144⟩
    (by decide) selected_cut_45685

theorem selected_cut_45686 : selected 9 ⟨1269271, by decide⟩
    (prefixPartial 12 368756) = some ⟨12, 2, 0, 1269271, 368756, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_368756_1269271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368756 ⟨1269271, by decide⟩ :=
  accepted_of_selected 12 368756 ⟨1269271, by decide⟩ ⟨12, 2, 0, 1269271, 368756, 1489, 65536⟩
    (by decide) selected_cut_45686

theorem selected_cut_45687 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 368757) = some ⟨12, 1, 0, 1257136, 368757, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368757_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368757 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 368757 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 368757, 1, 65536⟩
    (by decide) selected_cut_45687

theorem selected_cut_45688 : selected 9 ⟨1269298, by decide⟩
    (prefixPartial 12 368758) = some ⟨12, 2, 0, 1269298, 368758, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_368758_1269298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368758 ⟨1269298, by decide⟩ :=
  accepted_of_selected 12 368758 ⟨1269298, by decide⟩ ⟨12, 2, 0, 1269298, 368758, 1425, 65536⟩
    (by decide) selected_cut_45688

theorem selected_cut_45689 : selected 9 ⟨1269340, by decide⟩
    (prefixPartial 12 368759) = some ⟨12, 2, 0, 1269340, 368759, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_368759_1269340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368759 ⟨1269340, by decide⟩ :=
  accepted_of_selected 12 368759 ⟨1269340, by decide⟩ ⟨12, 2, 0, 1269340, 368759, 1665, 65536⟩
    (by decide) selected_cut_45689

theorem unmarked_context_11_92189_1269341 : frontier 10 ⟨1269341, by decide⟩
    (prefixCache 11 92189) (prefixPartial 11 92189) = false := by
  decide +kernel

theorem node_context_11_92189_1269341 : EJMOriginalGlobalDAGData.nodes 10 ⟨1269341, by decide⟩ =
    .split (coordinate 11) (![⟨1269271, by decide⟩,⟨1257136, by decide⟩,⟨1269298, by decide⟩,⟨1269340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92189_1269341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92189 ⟨1269341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92189
    ⟨1269341, by decide⟩ (by decide) (![⟨1269271, by decide⟩,⟨1257136, by decide⟩,⟨1269298, by decide⟩,⟨1269340, by decide⟩]) unmarked_context_11_92189_1269341 node_context_11_92189_1269341
  intro a
  fin_cases a
  · exact context_12_368756_1269271
  · exact context_12_368757_1257136
  · exact context_12_368758_1269298
  · exact context_12_368759_1269340

theorem selected_cut_45690 : selected 9 ⟨1269362, by decide⟩
    (prefixPartial 12 368760) = some ⟨12, 2, 0, 1269362, 368760, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_368760_1269362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368760 ⟨1269362, by decide⟩ :=
  accepted_of_selected 12 368760 ⟨1269362, by decide⟩ ⟨12, 2, 0, 1269362, 368760, 1229, 65536⟩
    (by decide) selected_cut_45690

theorem selected_cut_45691 : selected 9 ⟨1269389, by decide⟩
    (prefixPartial 12 368761) = some ⟨12, 2, 0, 1269389, 368761, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_368761_1269389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368761 ⟨1269389, by decide⟩ :=
  accepted_of_selected 12 368761 ⟨1269389, by decide⟩ ⟨12, 2, 0, 1269389, 368761, 1309, 65536⟩
    (by decide) selected_cut_45691

theorem selected_cut_45692 : selected 9 ⟨1269412, by decide⟩
    (prefixPartial 12 368762) = some ⟨12, 2, 0, 1269412, 368762, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_368762_1269412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368762 ⟨1269412, by decide⟩ :=
  accepted_of_selected 12 368762 ⟨1269412, by decide⟩ ⟨12, 2, 0, 1269412, 368762, 1213, 65536⟩
    (by decide) selected_cut_45692

theorem selected_cut_45693 : selected 9 ⟨1269440, by decide⟩
    (prefixPartial 12 368763) = some ⟨12, 2, 0, 1269440, 368763, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_368763_1269440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368763 ⟨1269440, by decide⟩ :=
  accepted_of_selected 12 368763 ⟨1269440, by decide⟩ ⟨12, 2, 0, 1269440, 368763, 1417, 65536⟩
    (by decide) selected_cut_45693

theorem unmarked_context_11_92190_1269441 : frontier 10 ⟨1269441, by decide⟩
    (prefixCache 11 92190) (prefixPartial 11 92190) = false := by
  decide +kernel

theorem node_context_11_92190_1269441 : EJMOriginalGlobalDAGData.nodes 10 ⟨1269441, by decide⟩ =
    .split (coordinate 11) (![⟨1269362, by decide⟩,⟨1269389, by decide⟩,⟨1269412, by decide⟩,⟨1269440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92190_1269441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92190 ⟨1269441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92190
    ⟨1269441, by decide⟩ (by decide) (![⟨1269362, by decide⟩,⟨1269389, by decide⟩,⟨1269412, by decide⟩,⟨1269440, by decide⟩]) unmarked_context_11_92190_1269441 node_context_11_92190_1269441
  intro a
  fin_cases a
  · exact context_12_368760_1269362
  · exact context_12_368761_1269389
  · exact context_12_368762_1269412
  · exact context_12_368763_1269440

theorem selected_cut_45694 : selected 10 ⟨1269485, by decide⟩
    (prefixPartial 11 92191) = some ⟨11, 2, 0, 1269485, 92191, 2277, 262144⟩ := by
  decide +kernel

theorem context_11_92191_1269485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92191 ⟨1269485, by decide⟩ :=
  accepted_of_selected 11 92191 ⟨1269485, by decide⟩ ⟨11, 2, 0, 1269485, 92191, 2277, 262144⟩
    (by decide) selected_cut_45694

theorem unmarked_context_10_23047_1269486 : frontier 11 ⟨1269486, by decide⟩
    (prefixCache 10 23047) (prefixPartial 10 23047) = false := by
  decide +kernel

theorem node_context_10_23047_1269486 : EJMOriginalGlobalDAGData.nodes 11 ⟨1269486, by decide⟩ =
    .split (coordinate 10) (![⟨1269247, by decide⟩,⟨1269341, by decide⟩,⟨1269441, by decide⟩,⟨1269485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23047_1269486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23047 ⟨1269486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23047
    ⟨1269486, by decide⟩ (by decide) (![⟨1269247, by decide⟩,⟨1269341, by decide⟩,⟨1269441, by decide⟩,⟨1269485, by decide⟩]) unmarked_context_10_23047_1269486 node_context_10_23047_1269486
  intro a
  fin_cases a
  · exact context_11_92188_1269247
  · exact context_11_92189_1269341
  · exact context_11_92190_1269441
  · exact context_11_92191_1269485

theorem unmarked_context_9_5761_1269487 : frontier 12 ⟨1269487, by decide⟩
    (prefixCache 9 5761) (prefixPartial 9 5761) = false := by
  decide +kernel

theorem node_context_9_5761_1269487 : EJMOriginalGlobalDAGData.nodes 12 ⟨1269487, by decide⟩ =
    .split (coordinate 9) (![⟨1268897, by decide⟩,⟨893098, by decide⟩,⟨1269184, by decide⟩,⟨1269486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5761_1269487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5761 ⟨1269487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5761
    ⟨1269487, by decide⟩ (by decide) (![⟨1268897, by decide⟩,⟨893098, by decide⟩,⟨1269184, by decide⟩,⟨1269486, by decide⟩]) unmarked_context_9_5761_1269487 node_context_9_5761_1269487
  intro a
  fin_cases a
  · exact context_10_23044_1268897
  · exact context_10_23045_893098
  · exact context_10_23046_1269184
  · exact context_10_23047_1269486

theorem selected_cut_45695 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92192) = some ⟨11, 1, 0, 907917, 92192, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92192_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92192 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92192 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92192, 1, 262144⟩
    (by decide) selected_cut_45695

theorem selected_cut_45696 : selected 10 ⟨1269530, by decide⟩
    (prefixPartial 11 92193) = some ⟨11, 2, 0, 1269530, 92193, 2261, 262144⟩ := by
  decide +kernel

theorem context_11_92193_1269530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92193 ⟨1269530, by decide⟩ :=
  accepted_of_selected 11 92193 ⟨1269530, by decide⟩ ⟨11, 2, 0, 1269530, 92193, 2261, 262144⟩
    (by decide) selected_cut_45696

theorem selected_cut_45697 : selected 10 ⟨1269585, by decide⟩
    (prefixPartial 11 92194) = some ⟨11, 2, 0, 1269585, 92194, 3013, 262144⟩ := by
  decide +kernel

theorem context_11_92194_1269585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92194 ⟨1269585, by decide⟩ :=
  accepted_of_selected 11 92194 ⟨1269585, by decide⟩ ⟨11, 2, 0, 1269585, 92194, 3013, 262144⟩
    (by decide) selected_cut_45697

theorem selected_cut_45698 : selected 10 ⟨1269620, by decide⟩
    (prefixPartial 11 92195) = some ⟨11, 2, 0, 1269620, 92195, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_92195_1269620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92195 ⟨1269620, by decide⟩ :=
  accepted_of_selected 11 92195 ⟨1269620, by decide⟩ ⟨11, 2, 0, 1269620, 92195, 1897, 262144⟩
    (by decide) selected_cut_45698

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
