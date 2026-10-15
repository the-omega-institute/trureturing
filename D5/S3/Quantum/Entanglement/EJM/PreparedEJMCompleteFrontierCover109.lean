/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover108
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_10467 : selected 8 ⟨284552, by decide⟩
    (prefixPartial 13 100431) = some ⟨13, 2, 0, 284552, 100431, 793, 16384⟩ := by
  decide +kernel

theorem context_13_100431_284552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100431 ⟨284552, by decide⟩ :=
  accepted_of_selected 13 100431 ⟨284552, by decide⟩ ⟨13, 2, 0, 284552, 100431, 793, 16384⟩
    (by decide) selected_cut_10467

theorem unmarked_context_12_25107_284553 : frontier 9 ⟨284553, by decide⟩
    (prefixCache 12 25107) (prefixPartial 12 25107) = false := by
  decide +kernel

theorem node_context_12_25107_284553 : EJMOriginalGlobalDAGData.nodes 9 ⟨284553, by decide⟩ =
    .split (coordinate 12) (![⟨284501, by decide⟩,⟨284528, by decide⟩,⟨284545, by decide⟩,⟨284552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25107_284553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25107 ⟨284553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25107
    ⟨284553, by decide⟩ (by decide) (![⟨284501, by decide⟩,⟨284528, by decide⟩,⟨284545, by decide⟩,⟨284552, by decide⟩]) unmarked_context_12_25107_284553 node_context_12_25107_284553
  intro a
  fin_cases a
  · exact context_13_100428_284501
  · exact context_13_100429_284528
  · exact context_13_100430_284545
  · exact context_13_100431_284552

theorem unmarked_context_11_6276_284554 : frontier 10 ⟨284554, by decide⟩
    (prefixCache 11 6276) (prefixPartial 11 6276) = false := by
  decide +kernel

theorem node_context_11_6276_284554 : EJMOriginalGlobalDAGData.nodes 10 ⟨284554, by decide⟩ =
    .split (coordinate 11) (![⟨284326, by decide⟩,⟨284403, by decide⟩,⟨284469, by decide⟩,⟨284553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6276_284554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6276 ⟨284554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6276
    ⟨284554, by decide⟩ (by decide) (![⟨284326, by decide⟩,⟨284403, by decide⟩,⟨284469, by decide⟩,⟨284553, by decide⟩]) unmarked_context_11_6276_284554 node_context_11_6276_284554
  intro a
  fin_cases a
  · exact context_12_25104_284326
  · exact context_12_25105_284403
  · exact context_12_25106_284469
  · exact context_12_25107_284553

theorem selected_cut_10468 : selected 8 ⟨284580, by decide⟩
    (prefixPartial 13 100432) = some ⟨13, 2, 0, 284580, 100432, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_100432_284580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100432 ⟨284580, by decide⟩ :=
  accepted_of_selected 13 100432 ⟨284580, by decide⟩ ⟨13, 2, 0, 284580, 100432, 1689, 16384⟩
    (by decide) selected_cut_10468

theorem selected_cut_10469 : selected 8 ⟨284602, by decide⟩
    (prefixPartial 13 100433) = some ⟨13, 2, 0, 284602, 100433, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_100433_284602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100433 ⟨284602, by decide⟩ :=
  accepted_of_selected 13 100433 ⟨284602, by decide⟩ ⟨13, 2, 0, 284602, 100433, 1865, 16384⟩
    (by decide) selected_cut_10469

theorem selected_cut_10470 : selected 8 ⟨284620, by decide⟩
    (prefixPartial 13 100434) = some ⟨13, 2, 0, 284620, 100434, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_100434_284620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100434 ⟨284620, by decide⟩ :=
  accepted_of_selected 13 100434 ⟨284620, by decide⟩ ⟨13, 2, 0, 284620, 100434, 1149, 16384⟩
    (by decide) selected_cut_10470

theorem selected_cut_10471 : selected 8 ⟨284629, by decide⟩
    (prefixPartial 13 100435) = some ⟨13, 2, 0, 284629, 100435, 857, 16384⟩ := by
  decide +kernel

theorem context_13_100435_284629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100435 ⟨284629, by decide⟩ :=
  accepted_of_selected 13 100435 ⟨284629, by decide⟩ ⟨13, 2, 0, 284629, 100435, 857, 16384⟩
    (by decide) selected_cut_10471

theorem unmarked_context_12_25108_284630 : frontier 9 ⟨284630, by decide⟩
    (prefixCache 12 25108) (prefixPartial 12 25108) = false := by
  decide +kernel

theorem node_context_12_25108_284630 : EJMOriginalGlobalDAGData.nodes 9 ⟨284630, by decide⟩ =
    .split (coordinate 12) (![⟨284580, by decide⟩,⟨284602, by decide⟩,⟨284620, by decide⟩,⟨284629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25108_284630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25108 ⟨284630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25108
    ⟨284630, by decide⟩ (by decide) (![⟨284580, by decide⟩,⟨284602, by decide⟩,⟨284620, by decide⟩,⟨284629, by decide⟩]) unmarked_context_12_25108_284630 node_context_12_25108_284630
  intro a
  fin_cases a
  · exact context_13_100432_284580
  · exact context_13_100433_284602
  · exact context_13_100434_284620
  · exact context_13_100435_284629

theorem selected_cut_10472 : selected 8 ⟨284652, by decide⟩
    (prefixPartial 13 100436) = some ⟨13, 2, 0, 284652, 100436, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_100436_284652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100436 ⟨284652, by decide⟩ :=
  accepted_of_selected 13 100436 ⟨284652, by decide⟩ ⟨13, 2, 0, 284652, 100436, 1589, 16384⟩
    (by decide) selected_cut_10472

theorem selected_cut_10473 : selected 8 ⟨284680, by decide⟩
    (prefixPartial 13 100437) = some ⟨13, 2, 0, 284680, 100437, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_100437_284680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100437 ⟨284680, by decide⟩ :=
  accepted_of_selected 13 100437 ⟨284680, by decide⟩ ⟨13, 2, 0, 284680, 100437, 1921, 16384⟩
    (by decide) selected_cut_10473

theorem selected_cut_10474 : selected 8 ⟨284699, by decide⟩
    (prefixPartial 13 100438) = some ⟨13, 2, 0, 284699, 100438, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_100438_284699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100438 ⟨284699, by decide⟩ :=
  accepted_of_selected 13 100438 ⟨284699, by decide⟩ ⟨13, 2, 0, 284699, 100438, 1429, 16384⟩
    (by decide) selected_cut_10474

theorem selected_cut_10475 : selected 8 ⟨284706, by decide⟩
    (prefixPartial 13 100439) = some ⟨13, 2, 0, 284706, 100439, 933, 16384⟩ := by
  decide +kernel

theorem context_13_100439_284706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100439 ⟨284706, by decide⟩ :=
  accepted_of_selected 13 100439 ⟨284706, by decide⟩ ⟨13, 2, 0, 284706, 100439, 933, 16384⟩
    (by decide) selected_cut_10475

theorem unmarked_context_12_25109_284707 : frontier 9 ⟨284707, by decide⟩
    (prefixCache 12 25109) (prefixPartial 12 25109) = false := by
  decide +kernel

theorem node_context_12_25109_284707 : EJMOriginalGlobalDAGData.nodes 9 ⟨284707, by decide⟩ =
    .split (coordinate 12) (![⟨284652, by decide⟩,⟨284680, by decide⟩,⟨284699, by decide⟩,⟨284706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25109_284707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25109 ⟨284707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25109
    ⟨284707, by decide⟩ (by decide) (![⟨284652, by decide⟩,⟨284680, by decide⟩,⟨284699, by decide⟩,⟨284706, by decide⟩]) unmarked_context_12_25109_284707 node_context_12_25109_284707
  intro a
  fin_cases a
  · exact context_13_100436_284652
  · exact context_13_100437_284680
  · exact context_13_100438_284699
  · exact context_13_100439_284706

theorem selected_cut_10476 : selected 8 ⟨284732, by decide⟩
    (prefixPartial 13 100440) = some ⟨13, 2, 0, 284732, 100440, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_100440_284732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100440 ⟨284732, by decide⟩ :=
  accepted_of_selected 13 100440 ⟨284732, by decide⟩ ⟨13, 2, 0, 284732, 100440, 1613, 16384⟩
    (by decide) selected_cut_10476

theorem selected_cut_10477 : selected 8 ⟨284756, by decide⟩
    (prefixPartial 13 100441) = some ⟨13, 2, 0, 284756, 100441, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_100441_284756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100441 ⟨284756, by decide⟩ :=
  accepted_of_selected 13 100441 ⟨284756, by decide⟩ ⟨13, 2, 0, 284756, 100441, 1985, 16384⟩
    (by decide) selected_cut_10477

theorem selected_cut_10478 : selected 8 ⟨284773, by decide⟩
    (prefixPartial 13 100442) = some ⟨13, 2, 0, 284773, 100442, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_100442_284773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100442 ⟨284773, by decide⟩ :=
  accepted_of_selected 13 100442 ⟨284773, by decide⟩ ⟨13, 2, 0, 284773, 100442, 1265, 16384⟩
    (by decide) selected_cut_10478

theorem selected_cut_10479 : selected 8 ⟨284779, by decide⟩
    (prefixPartial 13 100443) = some ⟨13, 2, 0, 284779, 100443, 985, 16384⟩ := by
  decide +kernel

theorem context_13_100443_284779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100443 ⟨284779, by decide⟩ :=
  accepted_of_selected 13 100443 ⟨284779, by decide⟩ ⟨13, 2, 0, 284779, 100443, 985, 16384⟩
    (by decide) selected_cut_10479

theorem unmarked_context_12_25110_284780 : frontier 9 ⟨284780, by decide⟩
    (prefixCache 12 25110) (prefixPartial 12 25110) = false := by
  decide +kernel

theorem node_context_12_25110_284780 : EJMOriginalGlobalDAGData.nodes 9 ⟨284780, by decide⟩ =
    .split (coordinate 12) (![⟨284732, by decide⟩,⟨284756, by decide⟩,⟨284773, by decide⟩,⟨284779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25110_284780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25110 ⟨284780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25110
    ⟨284780, by decide⟩ (by decide) (![⟨284732, by decide⟩,⟨284756, by decide⟩,⟨284773, by decide⟩,⟨284779, by decide⟩]) unmarked_context_12_25110_284780 node_context_12_25110_284780
  intro a
  fin_cases a
  · exact context_13_100440_284732
  · exact context_13_100441_284756
  · exact context_13_100442_284773
  · exact context_13_100443_284779

theorem selected_cut_10480 : selected 8 ⟨284808, by decide⟩
    (prefixPartial 13 100444) = some ⟨13, 2, 0, 284808, 100444, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_100444_284808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100444 ⟨284808, by decide⟩ :=
  accepted_of_selected 13 100444 ⟨284808, by decide⟩ ⟨13, 2, 0, 284808, 100444, 2165, 16384⟩
    (by decide) selected_cut_10480

theorem selected_cut_10481 : selected 8 ⟨284832, by decide⟩
    (prefixPartial 13 100445) = some ⟨13, 2, 0, 284832, 100445, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_100445_284832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100445 ⟨284832, by decide⟩ :=
  accepted_of_selected 13 100445 ⟨284832, by decide⟩ ⟨13, 2, 0, 284832, 100445, 2209, 16384⟩
    (by decide) selected_cut_10481

theorem selected_cut_10482 : selected 8 ⟨284851, by decide⟩
    (prefixPartial 13 100446) = some ⟨13, 2, 0, 284851, 100446, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_100446_284851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100446 ⟨284851, by decide⟩ :=
  accepted_of_selected 13 100446 ⟨284851, by decide⟩ ⟨13, 2, 0, 284851, 100446, 1481, 16384⟩
    (by decide) selected_cut_10482

theorem selected_cut_10483 : selected 8 ⟨284857, by decide⟩
    (prefixPartial 13 100447) = some ⟨13, 2, 0, 284857, 100447, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_100447_284857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100447 ⟨284857, by decide⟩ :=
  accepted_of_selected 13 100447 ⟨284857, by decide⟩ ⟨13, 2, 0, 284857, 100447, 1061, 16384⟩
    (by decide) selected_cut_10483

theorem unmarked_context_12_25111_284858 : frontier 9 ⟨284858, by decide⟩
    (prefixCache 12 25111) (prefixPartial 12 25111) = false := by
  decide +kernel

theorem node_context_12_25111_284858 : EJMOriginalGlobalDAGData.nodes 9 ⟨284858, by decide⟩ =
    .split (coordinate 12) (![⟨284808, by decide⟩,⟨284832, by decide⟩,⟨284851, by decide⟩,⟨284857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25111_284858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25111 ⟨284858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25111
    ⟨284858, by decide⟩ (by decide) (![⟨284808, by decide⟩,⟨284832, by decide⟩,⟨284851, by decide⟩,⟨284857, by decide⟩]) unmarked_context_12_25111_284858 node_context_12_25111_284858
  intro a
  fin_cases a
  · exact context_13_100444_284808
  · exact context_13_100445_284832
  · exact context_13_100446_284851
  · exact context_13_100447_284857

theorem unmarked_context_11_6277_284859 : frontier 10 ⟨284859, by decide⟩
    (prefixCache 11 6277) (prefixPartial 11 6277) = false := by
  decide +kernel

theorem node_context_11_6277_284859 : EJMOriginalGlobalDAGData.nodes 10 ⟨284859, by decide⟩ =
    .split (coordinate 11) (![⟨284630, by decide⟩,⟨284707, by decide⟩,⟨284780, by decide⟩,⟨284858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6277_284859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6277 ⟨284859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6277
    ⟨284859, by decide⟩ (by decide) (![⟨284630, by decide⟩,⟨284707, by decide⟩,⟨284780, by decide⟩,⟨284858, by decide⟩]) unmarked_context_11_6277_284859 node_context_11_6277_284859
  intro a
  fin_cases a
  · exact context_12_25108_284630
  · exact context_12_25109_284707
  · exact context_12_25110_284780
  · exact context_12_25111_284858

theorem selected_cut_10484 : selected 8 ⟨284884, by decide⟩
    (prefixPartial 13 100448) = some ⟨13, 2, 0, 284884, 100448, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_100448_284884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100448 ⟨284884, by decide⟩ :=
  accepted_of_selected 13 100448 ⟨284884, by decide⟩ ⟨13, 2, 0, 284884, 100448, 1401, 16384⟩
    (by decide) selected_cut_10484

theorem selected_cut_10485 : selected 8 ⟨284905, by decide⟩
    (prefixPartial 13 100449) = some ⟨13, 2, 0, 284905, 100449, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_100449_284905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100449 ⟨284905, by decide⟩ :=
  accepted_of_selected 13 100449 ⟨284905, by decide⟩ ⟨13, 2, 0, 284905, 100449, 1349, 16384⟩
    (by decide) selected_cut_10485

theorem selected_cut_10486 : selected 8 ⟨284921, by decide⟩
    (prefixPartial 13 100450) = some ⟨13, 2, 0, 284921, 100450, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_100450_284921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100450 ⟨284921, by decide⟩ :=
  accepted_of_selected 13 100450 ⟨284921, by decide⟩ ⟨13, 2, 0, 284921, 100450, 1021, 16384⟩
    (by decide) selected_cut_10486

theorem selected_cut_10487 : selected 8 ⟨284927, by decide⟩
    (prefixPartial 13 100451) = some ⟨13, 2, 0, 284927, 100451, 741, 16384⟩ := by
  decide +kernel

theorem context_13_100451_284927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100451 ⟨284927, by decide⟩ :=
  accepted_of_selected 13 100451 ⟨284927, by decide⟩ ⟨13, 2, 0, 284927, 100451, 741, 16384⟩
    (by decide) selected_cut_10487

theorem unmarked_context_12_25112_284928 : frontier 9 ⟨284928, by decide⟩
    (prefixCache 12 25112) (prefixPartial 12 25112) = false := by
  decide +kernel

theorem node_context_12_25112_284928 : EJMOriginalGlobalDAGData.nodes 9 ⟨284928, by decide⟩ =
    .split (coordinate 12) (![⟨284884, by decide⟩,⟨284905, by decide⟩,⟨284921, by decide⟩,⟨284927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25112_284928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25112 ⟨284928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25112
    ⟨284928, by decide⟩ (by decide) (![⟨284884, by decide⟩,⟨284905, by decide⟩,⟨284921, by decide⟩,⟨284927, by decide⟩]) unmarked_context_12_25112_284928 node_context_12_25112_284928
  intro a
  fin_cases a
  · exact context_13_100448_284884
  · exact context_13_100449_284905
  · exact context_13_100450_284921
  · exact context_13_100451_284927

theorem selected_cut_10488 : selected 8 ⟨284944, by decide⟩
    (prefixPartial 13 100452) = some ⟨13, 2, 0, 284944, 100452, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_100452_284944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100452 ⟨284944, by decide⟩ :=
  accepted_of_selected 13 100452 ⟨284944, by decide⟩ ⟨13, 2, 0, 284944, 100452, 1293, 16384⟩
    (by decide) selected_cut_10488

theorem selected_cut_10489 : selected 8 ⟨284971, by decide⟩
    (prefixPartial 13 100453) = some ⟨13, 2, 0, 284971, 100453, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_100453_284971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100453 ⟨284971, by decide⟩ :=
  accepted_of_selected 13 100453 ⟨284971, by decide⟩ ⟨13, 2, 0, 284971, 100453, 1757, 16384⟩
    (by decide) selected_cut_10489

theorem selected_cut_10490 : selected 8 ⟨284990, by decide⟩
    (prefixPartial 13 100454) = some ⟨13, 2, 0, 284990, 100454, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_100454_284990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100454 ⟨284990, by decide⟩ :=
  accepted_of_selected 13 100454 ⟨284990, by decide⟩ ⟨13, 2, 0, 284990, 100454, 1409, 16384⟩
    (by decide) selected_cut_10490

theorem selected_cut_10491 : selected 8 ⟨284997, by decide⟩
    (prefixPartial 13 100455) = some ⟨13, 2, 0, 284997, 100455, 821, 16384⟩ := by
  decide +kernel

theorem context_13_100455_284997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100455 ⟨284997, by decide⟩ :=
  accepted_of_selected 13 100455 ⟨284997, by decide⟩ ⟨13, 2, 0, 284997, 100455, 821, 16384⟩
    (by decide) selected_cut_10491

theorem unmarked_context_12_25113_284998 : frontier 9 ⟨284998, by decide⟩
    (prefixCache 12 25113) (prefixPartial 12 25113) = false := by
  decide +kernel

theorem node_context_12_25113_284998 : EJMOriginalGlobalDAGData.nodes 9 ⟨284998, by decide⟩ =
    .split (coordinate 12) (![⟨284944, by decide⟩,⟨284971, by decide⟩,⟨284990, by decide⟩,⟨284997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25113_284998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25113 ⟨284998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25113
    ⟨284998, by decide⟩ (by decide) (![⟨284944, by decide⟩,⟨284971, by decide⟩,⟨284990, by decide⟩,⟨284997, by decide⟩]) unmarked_context_12_25113_284998 node_context_12_25113_284998
  intro a
  fin_cases a
  · exact context_13_100452_284944
  · exact context_13_100453_284971
  · exact context_13_100454_284990
  · exact context_13_100455_284997

theorem selected_cut_10492 : selected 8 ⟨285022, by decide⟩
    (prefixPartial 13 100456) = some ⟨13, 2, 0, 285022, 100456, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_100456_285022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100456 ⟨285022, by decide⟩ :=
  accepted_of_selected 13 100456 ⟨285022, by decide⟩ ⟨13, 2, 0, 285022, 100456, 2289, 16384⟩
    (by decide) selected_cut_10492

theorem selected_cut_10493 : selected 8 ⟨285052, by decide⟩
    (prefixPartial 13 100457) = some ⟨13, 2, 0, 285052, 100457, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_100457_285052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100457 ⟨285052, by decide⟩ :=
  accepted_of_selected 13 100457 ⟨285052, by decide⟩ ⟨13, 2, 0, 285052, 100457, 2981, 16384⟩
    (by decide) selected_cut_10493

theorem selected_cut_10494 : selected 8 ⟨285073, by decide⟩
    (prefixPartial 13 100458) = some ⟨13, 2, 0, 285073, 100458, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_100458_285073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100458 ⟨285073, by decide⟩ :=
  accepted_of_selected 13 100458 ⟨285073, by decide⟩ ⟨13, 2, 0, 285073, 100458, 2045, 16384⟩
    (by decide) selected_cut_10494

theorem selected_cut_10495 : selected 8 ⟨285080, by decide⟩
    (prefixPartial 13 100459) = some ⟨13, 2, 0, 285080, 100459, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_100459_285080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100459 ⟨285080, by decide⟩ :=
  accepted_of_selected 13 100459 ⟨285080, by decide⟩ ⟨13, 2, 0, 285080, 100459, 1149, 16384⟩
    (by decide) selected_cut_10495

theorem unmarked_context_12_25114_285081 : frontier 9 ⟨285081, by decide⟩
    (prefixCache 12 25114) (prefixPartial 12 25114) = false := by
  decide +kernel

theorem node_context_12_25114_285081 : EJMOriginalGlobalDAGData.nodes 9 ⟨285081, by decide⟩ =
    .split (coordinate 12) (![⟨285022, by decide⟩,⟨285052, by decide⟩,⟨285073, by decide⟩,⟨285080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25114_285081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25114 ⟨285081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25114
    ⟨285081, by decide⟩ (by decide) (![⟨285022, by decide⟩,⟨285052, by decide⟩,⟨285073, by decide⟩,⟨285080, by decide⟩]) unmarked_context_12_25114_285081 node_context_12_25114_285081
  intro a
  fin_cases a
  · exact context_13_100456_285022
  · exact context_13_100457_285052
  · exact context_13_100458_285073
  · exact context_13_100459_285080

theorem selected_cut_10496 : selected 8 ⟨285106, by decide⟩
    (prefixPartial 13 100460) = some ⟨13, 2, 0, 285106, 100460, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_100460_285106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100460 ⟨285106, by decide⟩ :=
  accepted_of_selected 13 100460 ⟨285106, by decide⟩ ⟨13, 2, 0, 285106, 100460, 1681, 16384⟩
    (by decide) selected_cut_10496

theorem selected_cut_10497 : selected 8 ⟨285136, by decide⟩
    (prefixPartial 13 100461) = some ⟨13, 2, 0, 285136, 100461, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_100461_285136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100461 ⟨285136, by decide⟩ :=
  accepted_of_selected 13 100461 ⟨285136, by decide⟩ ⟨13, 2, 0, 285136, 100461, 2013, 16384⟩
    (by decide) selected_cut_10497

theorem selected_cut_10498 : selected 8 ⟨285156, by decide⟩
    (prefixPartial 13 100462) = some ⟨13, 2, 0, 285156, 100462, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_100462_285156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100462 ⟨285156, by decide⟩ :=
  accepted_of_selected 13 100462 ⟨285156, by decide⟩ ⟨13, 2, 0, 285156, 100462, 1373, 16384⟩
    (by decide) selected_cut_10498

theorem selected_cut_10499 : selected 8 ⟨285164, by decide⟩
    (prefixPartial 13 100463) = some ⟨13, 2, 0, 285164, 100463, 833, 16384⟩ := by
  decide +kernel

theorem context_13_100463_285164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100463 ⟨285164, by decide⟩ :=
  accepted_of_selected 13 100463 ⟨285164, by decide⟩ ⟨13, 2, 0, 285164, 100463, 833, 16384⟩
    (by decide) selected_cut_10499

theorem unmarked_context_12_25115_285165 : frontier 9 ⟨285165, by decide⟩
    (prefixCache 12 25115) (prefixPartial 12 25115) = false := by
  decide +kernel

theorem node_context_12_25115_285165 : EJMOriginalGlobalDAGData.nodes 9 ⟨285165, by decide⟩ =
    .split (coordinate 12) (![⟨285106, by decide⟩,⟨285136, by decide⟩,⟨285156, by decide⟩,⟨285164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25115_285165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25115 ⟨285165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25115
    ⟨285165, by decide⟩ (by decide) (![⟨285106, by decide⟩,⟨285136, by decide⟩,⟨285156, by decide⟩,⟨285164, by decide⟩]) unmarked_context_12_25115_285165 node_context_12_25115_285165
  intro a
  fin_cases a
  · exact context_13_100460_285106
  · exact context_13_100461_285136
  · exact context_13_100462_285156
  · exact context_13_100463_285164

theorem unmarked_context_11_6278_285166 : frontier 10 ⟨285166, by decide⟩
    (prefixCache 11 6278) (prefixPartial 11 6278) = false := by
  decide +kernel

theorem node_context_11_6278_285166 : EJMOriginalGlobalDAGData.nodes 10 ⟨285166, by decide⟩ =
    .split (coordinate 11) (![⟨284928, by decide⟩,⟨284998, by decide⟩,⟨285081, by decide⟩,⟨285165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6278_285166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6278 ⟨285166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6278
    ⟨285166, by decide⟩ (by decide) (![⟨284928, by decide⟩,⟨284998, by decide⟩,⟨285081, by decide⟩,⟨285165, by decide⟩]) unmarked_context_11_6278_285166 node_context_11_6278_285166
  intro a
  fin_cases a
  · exact context_12_25112_284928
  · exact context_12_25113_284998
  · exact context_12_25114_285081
  · exact context_12_25115_285165

theorem selected_cut_10500 : selected 8 ⟨285189, by decide⟩
    (prefixPartial 13 100464) = some ⟨13, 2, 0, 285189, 100464, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_100464_285189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100464 ⟨285189, by decide⟩ :=
  accepted_of_selected 13 100464 ⟨285189, by decide⟩ ⟨13, 2, 0, 285189, 100464, 1517, 16384⟩
    (by decide) selected_cut_10500

theorem selected_cut_10501 : selected 8 ⟨285211, by decide⟩
    (prefixPartial 13 100465) = some ⟨13, 2, 0, 285211, 100465, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_100465_285211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100465 ⟨285211, by decide⟩ :=
  accepted_of_selected 13 100465 ⟨285211, by decide⟩ ⟨13, 2, 0, 285211, 100465, 1721, 16384⟩
    (by decide) selected_cut_10501

theorem selected_cut_10502 : selected 8 ⟨285229, by decide⟩
    (prefixPartial 13 100466) = some ⟨13, 2, 0, 285229, 100466, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_100466_285229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100466 ⟨285229, by decide⟩ :=
  accepted_of_selected 13 100466 ⟨285229, by decide⟩ ⟨13, 2, 0, 285229, 100466, 1253, 16384⟩
    (by decide) selected_cut_10502

theorem selected_cut_10503 : selected 8 ⟨285235, by decide⟩
    (prefixPartial 13 100467) = some ⟨13, 2, 0, 285235, 100467, 825, 16384⟩ := by
  decide +kernel

theorem context_13_100467_285235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100467 ⟨285235, by decide⟩ :=
  accepted_of_selected 13 100467 ⟨285235, by decide⟩ ⟨13, 2, 0, 285235, 100467, 825, 16384⟩
    (by decide) selected_cut_10503

theorem unmarked_context_12_25116_285236 : frontier 9 ⟨285236, by decide⟩
    (prefixCache 12 25116) (prefixPartial 12 25116) = false := by
  decide +kernel

theorem node_context_12_25116_285236 : EJMOriginalGlobalDAGData.nodes 9 ⟨285236, by decide⟩ =
    .split (coordinate 12) (![⟨285189, by decide⟩,⟨285211, by decide⟩,⟨285229, by decide⟩,⟨285235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25116_285236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25116 ⟨285236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25116
    ⟨285236, by decide⟩ (by decide) (![⟨285189, by decide⟩,⟨285211, by decide⟩,⟨285229, by decide⟩,⟨285235, by decide⟩]) unmarked_context_12_25116_285236 node_context_12_25116_285236
  intro a
  fin_cases a
  · exact context_13_100464_285189
  · exact context_13_100465_285211
  · exact context_13_100466_285229
  · exact context_13_100467_285235

theorem selected_cut_10504 : selected 8 ⟨285256, by decide⟩
    (prefixPartial 13 100468) = some ⟨13, 2, 0, 285256, 100468, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_100468_285256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100468 ⟨285256, by decide⟩ :=
  accepted_of_selected 13 100468 ⟨285256, by decide⟩ ⟨13, 2, 0, 285256, 100468, 1549, 16384⟩
    (by decide) selected_cut_10504

theorem selected_cut_10505 : selected 8 ⟨285285, by decide⟩
    (prefixPartial 13 100469) = some ⟨13, 2, 0, 285285, 100469, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_100469_285285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100469 ⟨285285, by decide⟩ :=
  accepted_of_selected 13 100469 ⟨285285, by decide⟩ ⟨13, 2, 0, 285285, 100469, 2229, 16384⟩
    (by decide) selected_cut_10505

theorem selected_cut_10506 : selected 8 ⟨285305, by decide⟩
    (prefixPartial 13 100470) = some ⟨13, 2, 0, 285305, 100470, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_100470_285305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100470 ⟨285305, by decide⟩ :=
  accepted_of_selected 13 100470 ⟨285305, by decide⟩ ⟨13, 2, 0, 285305, 100470, 1497, 16384⟩
    (by decide) selected_cut_10506

theorem selected_cut_10507 : selected 8 ⟨285312, by decide⟩
    (prefixPartial 13 100471) = some ⟨13, 2, 0, 285312, 100471, 821, 16384⟩ := by
  decide +kernel

theorem context_13_100471_285312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100471 ⟨285312, by decide⟩ :=
  accepted_of_selected 13 100471 ⟨285312, by decide⟩ ⟨13, 2, 0, 285312, 100471, 821, 16384⟩
    (by decide) selected_cut_10507

theorem unmarked_context_12_25117_285313 : frontier 9 ⟨285313, by decide⟩
    (prefixCache 12 25117) (prefixPartial 12 25117) = false := by
  decide +kernel

theorem node_context_12_25117_285313 : EJMOriginalGlobalDAGData.nodes 9 ⟨285313, by decide⟩ =
    .split (coordinate 12) (![⟨285256, by decide⟩,⟨285285, by decide⟩,⟨285305, by decide⟩,⟨285312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25117_285313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25117 ⟨285313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25117
    ⟨285313, by decide⟩ (by decide) (![⟨285256, by decide⟩,⟨285285, by decide⟩,⟨285305, by decide⟩,⟨285312, by decide⟩]) unmarked_context_12_25117_285313 node_context_12_25117_285313
  intro a
  fin_cases a
  · exact context_13_100468_285256
  · exact context_13_100469_285285
  · exact context_13_100470_285305
  · exact context_13_100471_285312

theorem selected_cut_10508 : selected 8 ⟨285333, by decide⟩
    (prefixPartial 13 100472) = some ⟨13, 2, 0, 285333, 100472, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_100472_285333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100472 ⟨285333, by decide⟩ :=
  accepted_of_selected 13 100472 ⟨285333, by decide⟩ ⟨13, 2, 0, 285333, 100472, 1417, 16384⟩
    (by decide) selected_cut_10508

theorem selected_cut_10509 : selected 8 ⟨285355, by decide⟩
    (prefixPartial 13 100473) = some ⟨13, 2, 0, 285355, 100473, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_100473_285355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100473 ⟨285355, by decide⟩ :=
  accepted_of_selected 13 100473 ⟨285355, by decide⟩ ⟨13, 2, 0, 285355, 100473, 1985, 16384⟩
    (by decide) selected_cut_10509

theorem selected_cut_10510 : selected 8 ⟨285370, by decide⟩
    (prefixPartial 13 100474) = some ⟨13, 2, 0, 285370, 100474, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_100474_285370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100474 ⟨285370, by decide⟩ :=
  accepted_of_selected 13 100474 ⟨285370, by decide⟩ ⟨13, 2, 0, 285370, 100474, 1245, 16384⟩
    (by decide) selected_cut_10510

theorem selected_cut_10511 : selected 8 ⟨285380, by decide⟩
    (prefixPartial 13 100475) = some ⟨13, 2, 0, 285380, 100475, 785, 16384⟩ := by
  decide +kernel

theorem context_13_100475_285380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100475 ⟨285380, by decide⟩ :=
  accepted_of_selected 13 100475 ⟨285380, by decide⟩ ⟨13, 2, 0, 285380, 100475, 785, 16384⟩
    (by decide) selected_cut_10511

theorem unmarked_context_12_25118_285381 : frontier 9 ⟨285381, by decide⟩
    (prefixCache 12 25118) (prefixPartial 12 25118) = false := by
  decide +kernel

theorem node_context_12_25118_285381 : EJMOriginalGlobalDAGData.nodes 9 ⟨285381, by decide⟩ =
    .split (coordinate 12) (![⟨285333, by decide⟩,⟨285355, by decide⟩,⟨285370, by decide⟩,⟨285380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25118_285381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25118 ⟨285381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25118
    ⟨285381, by decide⟩ (by decide) (![⟨285333, by decide⟩,⟨285355, by decide⟩,⟨285370, by decide⟩,⟨285380, by decide⟩]) unmarked_context_12_25118_285381 node_context_12_25118_285381
  intro a
  fin_cases a
  · exact context_13_100472_285333
  · exact context_13_100473_285355
  · exact context_13_100474_285370
  · exact context_13_100475_285380

theorem selected_cut_10512 : selected 8 ⟨285410, by decide⟩
    (prefixPartial 13 100476) = some ⟨13, 2, 0, 285410, 100476, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_100476_285410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100476 ⟨285410, by decide⟩ :=
  accepted_of_selected 13 100476 ⟨285410, by decide⟩ ⟨13, 2, 0, 285410, 100476, 1797, 16384⟩
    (by decide) selected_cut_10512

theorem selected_cut_10513 : selected 8 ⟨285435, by decide⟩
    (prefixPartial 13 100477) = some ⟨13, 2, 0, 285435, 100477, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_100477_285435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100477 ⟨285435, by decide⟩ :=
  accepted_of_selected 13 100477 ⟨285435, by decide⟩ ⟨13, 2, 0, 285435, 100477, 2125, 16384⟩
    (by decide) selected_cut_10513

theorem selected_cut_10514 : selected 8 ⟨285454, by decide⟩
    (prefixPartial 13 100478) = some ⟨13, 2, 0, 285454, 100478, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_100478_285454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100478 ⟨285454, by decide⟩ :=
  accepted_of_selected 13 100478 ⟨285454, by decide⟩ ⟨13, 2, 0, 285454, 100478, 1525, 16384⟩
    (by decide) selected_cut_10514

theorem selected_cut_10515 : selected 8 ⟨285463, by decide⟩
    (prefixPartial 13 100479) = some ⟨13, 2, 0, 285463, 100479, 857, 16384⟩ := by
  decide +kernel

theorem context_13_100479_285463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100479 ⟨285463, by decide⟩ :=
  accepted_of_selected 13 100479 ⟨285463, by decide⟩ ⟨13, 2, 0, 285463, 100479, 857, 16384⟩
    (by decide) selected_cut_10515

theorem unmarked_context_12_25119_285464 : frontier 9 ⟨285464, by decide⟩
    (prefixCache 12 25119) (prefixPartial 12 25119) = false := by
  decide +kernel

theorem node_context_12_25119_285464 : EJMOriginalGlobalDAGData.nodes 9 ⟨285464, by decide⟩ =
    .split (coordinate 12) (![⟨285410, by decide⟩,⟨285435, by decide⟩,⟨285454, by decide⟩,⟨285463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25119_285464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25119 ⟨285464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25119
    ⟨285464, by decide⟩ (by decide) (![⟨285410, by decide⟩,⟨285435, by decide⟩,⟨285454, by decide⟩,⟨285463, by decide⟩]) unmarked_context_12_25119_285464 node_context_12_25119_285464
  intro a
  fin_cases a
  · exact context_13_100476_285410
  · exact context_13_100477_285435
  · exact context_13_100478_285454
  · exact context_13_100479_285463

theorem unmarked_context_11_6279_285465 : frontier 10 ⟨285465, by decide⟩
    (prefixCache 11 6279) (prefixPartial 11 6279) = false := by
  decide +kernel

theorem node_context_11_6279_285465 : EJMOriginalGlobalDAGData.nodes 10 ⟨285465, by decide⟩ =
    .split (coordinate 11) (![⟨285236, by decide⟩,⟨285313, by decide⟩,⟨285381, by decide⟩,⟨285464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6279_285465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6279 ⟨285465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6279
    ⟨285465, by decide⟩ (by decide) (![⟨285236, by decide⟩,⟨285313, by decide⟩,⟨285381, by decide⟩,⟨285464, by decide⟩]) unmarked_context_11_6279_285465 node_context_11_6279_285465
  intro a
  fin_cases a
  · exact context_12_25116_285236
  · exact context_12_25117_285313
  · exact context_12_25118_285381
  · exact context_12_25119_285464

theorem unmarked_context_10_1569_285466 : frontier 11 ⟨285466, by decide⟩
    (prefixCache 10 1569) (prefixPartial 10 1569) = false := by
  decide +kernel

theorem node_context_10_1569_285466 : EJMOriginalGlobalDAGData.nodes 11 ⟨285466, by decide⟩ =
    .split (coordinate 10) (![⟨284554, by decide⟩,⟨284859, by decide⟩,⟨285166, by decide⟩,⟨285465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1569_285466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1569 ⟨285466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1569
    ⟨285466, by decide⟩ (by decide) (![⟨284554, by decide⟩,⟨284859, by decide⟩,⟨285166, by decide⟩,⟨285465, by decide⟩]) unmarked_context_10_1569_285466 node_context_10_1569_285466
  intro a
  fin_cases a
  · exact context_11_6276_284554
  · exact context_11_6277_284859
  · exact context_11_6278_285166
  · exact context_11_6279_285465

theorem selected_cut_10516 : selected 9 ⟨285513, by decide⟩
    (prefixPartial 12 25120) = some ⟨12, 2, 0, 285513, 25120, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_25120_285513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25120 ⟨285513, by decide⟩ :=
  accepted_of_selected 12 25120 ⟨285513, by decide⟩ ⟨12, 2, 0, 285513, 25120, 3437, 65536⟩
    (by decide) selected_cut_10516

theorem selected_cut_10517 : selected 8 ⟨285525, by decide⟩
    (prefixPartial 13 100484) = some ⟨13, 2, 0, 285525, 100484, 889, 16384⟩ := by
  decide +kernel

theorem context_13_100484_285525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100484 ⟨285525, by decide⟩ :=
  accepted_of_selected 13 100484 ⟨285525, by decide⟩ ⟨13, 2, 0, 285525, 100484, 889, 16384⟩
    (by decide) selected_cut_10517

theorem selected_cut_10518 : selected 8 ⟨285548, by decide⟩
    (prefixPartial 13 100485) = some ⟨13, 2, 0, 285548, 100485, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_100485_285548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100485 ⟨285548, by decide⟩ :=
  accepted_of_selected 13 100485 ⟨285548, by decide⟩ ⟨13, 2, 0, 285548, 100485, 1677, 16384⟩
    (by decide) selected_cut_10518

theorem selected_cut_10519 : selected 8 ⟨285565, by decide⟩
    (prefixPartial 13 100486) = some ⟨13, 2, 0, 285565, 100486, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_100486_285565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100486 ⟨285565, by decide⟩ :=
  accepted_of_selected 13 100486 ⟨285565, by decide⟩ ⟨13, 2, 0, 285565, 100486, 1153, 16384⟩
    (by decide) selected_cut_10519

theorem selected_cut_10520 : selected 8 ⟨285570, by decide⟩
    (prefixPartial 13 100487) = some ⟨13, 2, 0, 285570, 100487, 657, 16384⟩ := by
  decide +kernel

theorem context_13_100487_285570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100487 ⟨285570, by decide⟩ :=
  accepted_of_selected 13 100487 ⟨285570, by decide⟩ ⟨13, 2, 0, 285570, 100487, 657, 16384⟩
    (by decide) selected_cut_10520

theorem unmarked_context_12_25121_285571 : frontier 9 ⟨285571, by decide⟩
    (prefixCache 12 25121) (prefixPartial 12 25121) = false := by
  decide +kernel

theorem node_context_12_25121_285571 : EJMOriginalGlobalDAGData.nodes 9 ⟨285571, by decide⟩ =
    .split (coordinate 12) (![⟨285525, by decide⟩,⟨285548, by decide⟩,⟨285565, by decide⟩,⟨285570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25121_285571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25121 ⟨285571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25121
    ⟨285571, by decide⟩ (by decide) (![⟨285525, by decide⟩,⟨285548, by decide⟩,⟨285565, by decide⟩,⟨285570, by decide⟩]) unmarked_context_12_25121_285571 node_context_12_25121_285571
  intro a
  fin_cases a
  · exact context_13_100484_285525
  · exact context_13_100485_285548
  · exact context_13_100486_285565
  · exact context_13_100487_285570

theorem selected_cut_10521 : selected 9 ⟨285615, by decide⟩
    (prefixPartial 12 25122) = some ⟨12, 2, 0, 285615, 25122, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_25122_285615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25122 ⟨285615, by decide⟩ :=
  accepted_of_selected 12 25122 ⟨285615, by decide⟩ ⟨12, 2, 0, 285615, 25122, 3437, 65536⟩
    (by decide) selected_cut_10521

theorem selected_cut_10522 : selected 8 ⟨285631, by decide⟩
    (prefixPartial 13 100492) = some ⟨13, 2, 0, 285631, 100492, 953, 16384⟩ := by
  decide +kernel

theorem context_13_100492_285631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100492 ⟨285631, by decide⟩ :=
  accepted_of_selected 13 100492 ⟨285631, by decide⟩ ⟨13, 2, 0, 285631, 100492, 953, 16384⟩
    (by decide) selected_cut_10522

theorem selected_cut_10523 : selected 8 ⟨285660, by decide⟩
    (prefixPartial 13 100493) = some ⟨13, 2, 0, 285660, 100493, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_100493_285660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100493 ⟨285660, by decide⟩ :=
  accepted_of_selected 13 100493 ⟨285660, by decide⟩ ⟨13, 2, 0, 285660, 100493, 2057, 16384⟩
    (by decide) selected_cut_10523

theorem selected_cut_10524 : selected 8 ⟨285675, by decide⟩
    (prefixPartial 13 100494) = some ⟨13, 2, 0, 285675, 100494, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_100494_285675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100494 ⟨285675, by decide⟩ :=
  accepted_of_selected 13 100494 ⟨285675, by decide⟩ ⟨13, 2, 0, 285675, 100494, 1169, 16384⟩
    (by decide) selected_cut_10524

theorem selected_cut_10525 : selected 8 ⟨285679, by decide⟩
    (prefixPartial 13 100495) = some ⟨13, 2, 0, 285679, 100495, 625, 16384⟩ := by
  decide +kernel

theorem context_13_100495_285679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100495 ⟨285679, by decide⟩ :=
  accepted_of_selected 13 100495 ⟨285679, by decide⟩ ⟨13, 2, 0, 285679, 100495, 625, 16384⟩
    (by decide) selected_cut_10525

theorem unmarked_context_12_25123_285680 : frontier 9 ⟨285680, by decide⟩
    (prefixCache 12 25123) (prefixPartial 12 25123) = false := by
  decide +kernel

theorem node_context_12_25123_285680 : EJMOriginalGlobalDAGData.nodes 9 ⟨285680, by decide⟩ =
    .split (coordinate 12) (![⟨285631, by decide⟩,⟨285660, by decide⟩,⟨285675, by decide⟩,⟨285679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25123_285680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25123 ⟨285680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25123
    ⟨285680, by decide⟩ (by decide) (![⟨285631, by decide⟩,⟨285660, by decide⟩,⟨285675, by decide⟩,⟨285679, by decide⟩]) unmarked_context_12_25123_285680 node_context_12_25123_285680
  intro a
  fin_cases a
  · exact context_13_100492_285631
  · exact context_13_100493_285660
  · exact context_13_100494_285675
  · exact context_13_100495_285679

theorem unmarked_context_11_6280_285681 : frontier 10 ⟨285681, by decide⟩
    (prefixCache 11 6280) (prefixPartial 11 6280) = false := by
  decide +kernel

theorem node_context_11_6280_285681 : EJMOriginalGlobalDAGData.nodes 10 ⟨285681, by decide⟩ =
    .split (coordinate 11) (![⟨285513, by decide⟩,⟨285571, by decide⟩,⟨285615, by decide⟩,⟨285680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6280_285681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6280 ⟨285681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6280
    ⟨285681, by decide⟩ (by decide) (![⟨285513, by decide⟩,⟨285571, by decide⟩,⟨285615, by decide⟩,⟨285680, by decide⟩]) unmarked_context_11_6280_285681 node_context_11_6280_285681
  intro a
  fin_cases a
  · exact context_12_25120_285513
  · exact context_12_25121_285571
  · exact context_12_25122_285615
  · exact context_12_25123_285680

theorem selected_cut_10526 : selected 8 ⟨285693, by decide⟩
    (prefixPartial 13 100496) = some ⟨13, 2, 0, 285693, 100496, 857, 16384⟩ := by
  decide +kernel

theorem context_13_100496_285693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100496 ⟨285693, by decide⟩ :=
  accepted_of_selected 13 100496 ⟨285693, by decide⟩ ⟨13, 2, 0, 285693, 100496, 857, 16384⟩
    (by decide) selected_cut_10526

theorem selected_cut_10527 : selected 8 ⟨285717, by decide⟩
    (prefixPartial 13 100497) = some ⟨13, 2, 0, 285717, 100497, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_100497_285717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100497 ⟨285717, by decide⟩ :=
  accepted_of_selected 13 100497 ⟨285717, by decide⟩ ⟨13, 2, 0, 285717, 100497, 1893, 16384⟩
    (by decide) selected_cut_10527

theorem selected_cut_10528 : selected 8 ⟨285733, by decide⟩
    (prefixPartial 13 100498) = some ⟨13, 2, 0, 285733, 100498, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_100498_285733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100498 ⟨285733, by decide⟩ :=
  accepted_of_selected 13 100498 ⟨285733, by decide⟩ ⟨13, 2, 0, 285733, 100498, 1197, 16384⟩
    (by decide) selected_cut_10528

theorem selected_cut_10529 : selected 8 ⟨285736, by decide⟩
    (prefixPartial 13 100499) = some ⟨13, 2, 0, 285736, 100499, 665, 16384⟩ := by
  decide +kernel

theorem context_13_100499_285736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100499 ⟨285736, by decide⟩ :=
  accepted_of_selected 13 100499 ⟨285736, by decide⟩ ⟨13, 2, 0, 285736, 100499, 665, 16384⟩
    (by decide) selected_cut_10529

theorem unmarked_context_12_25124_285737 : frontier 9 ⟨285737, by decide⟩
    (prefixCache 12 25124) (prefixPartial 12 25124) = false := by
  decide +kernel

theorem node_context_12_25124_285737 : EJMOriginalGlobalDAGData.nodes 9 ⟨285737, by decide⟩ =
    .split (coordinate 12) (![⟨285693, by decide⟩,⟨285717, by decide⟩,⟨285733, by decide⟩,⟨285736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25124_285737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25124 ⟨285737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25124
    ⟨285737, by decide⟩ (by decide) (![⟨285693, by decide⟩,⟨285717, by decide⟩,⟨285733, by decide⟩,⟨285736, by decide⟩]) unmarked_context_12_25124_285737 node_context_12_25124_285737
  intro a
  fin_cases a
  · exact context_13_100496_285693
  · exact context_13_100497_285717
  · exact context_13_100498_285733
  · exact context_13_100499_285736

theorem selected_cut_10530 : selected 8 ⟨285751, by decide⟩
    (prefixPartial 13 100500) = some ⟨13, 2, 0, 285751, 100500, 873, 16384⟩ := by
  decide +kernel

theorem context_13_100500_285751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100500 ⟨285751, by decide⟩ :=
  accepted_of_selected 13 100500 ⟨285751, by decide⟩ ⟨13, 2, 0, 285751, 100500, 873, 16384⟩
    (by decide) selected_cut_10530

theorem selected_cut_10531 : selected 8 ⟨285777, by decide⟩
    (prefixPartial 13 100501) = some ⟨13, 2, 0, 285777, 100501, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_100501_285777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100501 ⟨285777, by decide⟩ :=
  accepted_of_selected 13 100501 ⟨285777, by decide⟩ ⟨13, 2, 0, 285777, 100501, 1869, 16384⟩
    (by decide) selected_cut_10531

theorem selected_cut_10532 : selected 8 ⟨285795, by decide⟩
    (prefixPartial 13 100502) = some ⟨13, 2, 0, 285795, 100502, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_100502_285795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100502 ⟨285795, by decide⟩ :=
  accepted_of_selected 13 100502 ⟨285795, by decide⟩ ⟨13, 2, 0, 285795, 100502, 1385, 16384⟩
    (by decide) selected_cut_10532

theorem selected_cut_10533 : selected 8 ⟨285802, by decide⟩
    (prefixPartial 13 100503) = some ⟨13, 2, 0, 285802, 100503, 749, 16384⟩ := by
  decide +kernel

theorem context_13_100503_285802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100503 ⟨285802, by decide⟩ :=
  accepted_of_selected 13 100503 ⟨285802, by decide⟩ ⟨13, 2, 0, 285802, 100503, 749, 16384⟩
    (by decide) selected_cut_10533

theorem unmarked_context_12_25125_285803 : frontier 9 ⟨285803, by decide⟩
    (prefixCache 12 25125) (prefixPartial 12 25125) = false := by
  decide +kernel

theorem node_context_12_25125_285803 : EJMOriginalGlobalDAGData.nodes 9 ⟨285803, by decide⟩ =
    .split (coordinate 12) (![⟨285751, by decide⟩,⟨285777, by decide⟩,⟨285795, by decide⟩,⟨285802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25125_285803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25125 ⟨285803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25125
    ⟨285803, by decide⟩ (by decide) (![⟨285751, by decide⟩,⟨285777, by decide⟩,⟨285795, by decide⟩,⟨285802, by decide⟩]) unmarked_context_12_25125_285803 node_context_12_25125_285803
  intro a
  fin_cases a
  · exact context_13_100500_285751
  · exact context_13_100501_285777
  · exact context_13_100502_285795
  · exact context_13_100503_285802

theorem selected_cut_10534 : selected 8 ⟨285816, by decide⟩
    (prefixPartial 13 100504) = some ⟨13, 2, 0, 285816, 100504, 741, 16384⟩ := by
  decide +kernel

theorem context_13_100504_285816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100504 ⟨285816, by decide⟩ :=
  accepted_of_selected 13 100504 ⟨285816, by decide⟩ ⟨13, 2, 0, 285816, 100504, 741, 16384⟩
    (by decide) selected_cut_10534

theorem selected_cut_10535 : selected 8 ⟨285839, by decide⟩
    (prefixPartial 13 100505) = some ⟨13, 2, 0, 285839, 100505, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_100505_285839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100505 ⟨285839, by decide⟩ :=
  accepted_of_selected 13 100505 ⟨285839, by decide⟩ ⟨13, 2, 0, 285839, 100505, 1729, 16384⟩
    (by decide) selected_cut_10535

theorem selected_cut_10536 : selected 8 ⟨285853, by decide⟩
    (prefixPartial 13 100506) = some ⟨13, 2, 0, 285853, 100506, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_100506_285853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100506 ⟨285853, by decide⟩ :=
  accepted_of_selected 13 100506 ⟨285853, by decide⟩ ⟨13, 2, 0, 285853, 100506, 1061, 16384⟩
    (by decide) selected_cut_10536

theorem selected_cut_10537 : selected 8 ⟨285857, by decide⟩
    (prefixPartial 13 100507) = some ⟨13, 2, 0, 285857, 100507, 709, 16384⟩ := by
  decide +kernel

theorem context_13_100507_285857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100507 ⟨285857, by decide⟩ :=
  accepted_of_selected 13 100507 ⟨285857, by decide⟩ ⟨13, 2, 0, 285857, 100507, 709, 16384⟩
    (by decide) selected_cut_10537

theorem unmarked_context_12_25126_285858 : frontier 9 ⟨285858, by decide⟩
    (prefixCache 12 25126) (prefixPartial 12 25126) = false := by
  decide +kernel

theorem node_context_12_25126_285858 : EJMOriginalGlobalDAGData.nodes 9 ⟨285858, by decide⟩ =
    .split (coordinate 12) (![⟨285816, by decide⟩,⟨285839, by decide⟩,⟨285853, by decide⟩,⟨285857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25126_285858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25126 ⟨285858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25126
    ⟨285858, by decide⟩ (by decide) (![⟨285816, by decide⟩,⟨285839, by decide⟩,⟨285853, by decide⟩,⟨285857, by decide⟩]) unmarked_context_12_25126_285858 node_context_12_25126_285858
  intro a
  fin_cases a
  · exact context_13_100504_285816
  · exact context_13_100505_285839
  · exact context_13_100506_285853
  · exact context_13_100507_285857

theorem selected_cut_10538 : selected 8 ⟨285873, by decide⟩
    (prefixPartial 13 100508) = some ⟨13, 2, 0, 285873, 100508, 985, 16384⟩ := by
  decide +kernel

theorem context_13_100508_285873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100508 ⟨285873, by decide⟩ :=
  accepted_of_selected 13 100508 ⟨285873, by decide⟩ ⟨13, 2, 0, 285873, 100508, 985, 16384⟩
    (by decide) selected_cut_10538

theorem selected_cut_10539 : selected 8 ⟨285897, by decide⟩
    (prefixPartial 13 100509) = some ⟨13, 2, 0, 285897, 100509, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_100509_285897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100509 ⟨285897, by decide⟩ :=
  accepted_of_selected 13 100509 ⟨285897, by decide⟩ ⟨13, 2, 0, 285897, 100509, 2281, 16384⟩
    (by decide) selected_cut_10539

theorem selected_cut_10540 : selected 8 ⟨285915, by decide⟩
    (prefixPartial 13 100510) = some ⟨13, 2, 0, 285915, 100510, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_100510_285915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100510 ⟨285915, by decide⟩ :=
  accepted_of_selected 13 100510 ⟨285915, by decide⟩ ⟨13, 2, 0, 285915, 100510, 1401, 16384⟩
    (by decide) selected_cut_10540

theorem selected_cut_10541 : selected 8 ⟨285923, by decide⟩
    (prefixPartial 13 100511) = some ⟨13, 2, 0, 285923, 100511, 737, 16384⟩ := by
  decide +kernel

theorem context_13_100511_285923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100511 ⟨285923, by decide⟩ :=
  accepted_of_selected 13 100511 ⟨285923, by decide⟩ ⟨13, 2, 0, 285923, 100511, 737, 16384⟩
    (by decide) selected_cut_10541

theorem unmarked_context_12_25127_285924 : frontier 9 ⟨285924, by decide⟩
    (prefixCache 12 25127) (prefixPartial 12 25127) = false := by
  decide +kernel

theorem node_context_12_25127_285924 : EJMOriginalGlobalDAGData.nodes 9 ⟨285924, by decide⟩ =
    .split (coordinate 12) (![⟨285873, by decide⟩,⟨285897, by decide⟩,⟨285915, by decide⟩,⟨285923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25127_285924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25127 ⟨285924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25127
    ⟨285924, by decide⟩ (by decide) (![⟨285873, by decide⟩,⟨285897, by decide⟩,⟨285915, by decide⟩,⟨285923, by decide⟩]) unmarked_context_12_25127_285924 node_context_12_25127_285924
  intro a
  fin_cases a
  · exact context_13_100508_285873
  · exact context_13_100509_285897
  · exact context_13_100510_285915
  · exact context_13_100511_285923

theorem unmarked_context_11_6281_285925 : frontier 10 ⟨285925, by decide⟩
    (prefixCache 11 6281) (prefixPartial 11 6281) = false := by
  decide +kernel

theorem node_context_11_6281_285925 : EJMOriginalGlobalDAGData.nodes 10 ⟨285925, by decide⟩ =
    .split (coordinate 11) (![⟨285737, by decide⟩,⟨285803, by decide⟩,⟨285858, by decide⟩,⟨285924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6281_285925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6281 ⟨285925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6281
    ⟨285925, by decide⟩ (by decide) (![⟨285737, by decide⟩,⟨285803, by decide⟩,⟨285858, by decide⟩,⟨285924, by decide⟩]) unmarked_context_11_6281_285925 node_context_11_6281_285925
  intro a
  fin_cases a
  · exact context_12_25124_285737
  · exact context_12_25125_285803
  · exact context_12_25126_285858
  · exact context_12_25127_285924

theorem selected_cut_10542 : selected 9 ⟨285979, by decide⟩
    (prefixPartial 12 25128) = some ⟨12, 2, 0, 285979, 25128, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_25128_285979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25128 ⟨285979, by decide⟩ :=
  accepted_of_selected 12 25128 ⟨285979, by decide⟩ ⟨12, 2, 0, 285979, 25128, 3713, 65536⟩
    (by decide) selected_cut_10542

theorem selected_cut_10543 : selected 8 ⟨285990, by decide⟩
    (prefixPartial 13 100516) = some ⟨13, 2, 0, 285990, 100516, 725, 16384⟩ := by
  decide +kernel

theorem context_13_100516_285990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100516 ⟨285990, by decide⟩ :=
  accepted_of_selected 13 100516 ⟨285990, by decide⟩ ⟨13, 2, 0, 285990, 100516, 725, 16384⟩
    (by decide) selected_cut_10543

theorem selected_cut_10544 : selected 8 ⟨286016, by decide⟩
    (prefixPartial 13 100517) = some ⟨13, 2, 0, 286016, 100517, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_100517_286016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100517 ⟨286016, by decide⟩ :=
  accepted_of_selected 13 100517 ⟨286016, by decide⟩ ⟨13, 2, 0, 286016, 100517, 1745, 16384⟩
    (by decide) selected_cut_10544

theorem selected_cut_10545 : selected 8 ⟨286035, by decide⟩
    (prefixPartial 13 100518) = some ⟨13, 2, 0, 286035, 100518, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_100518_286035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100518 ⟨286035, by decide⟩ :=
  accepted_of_selected 13 100518 ⟨286035, by decide⟩ ⟨13, 2, 0, 286035, 100518, 1325, 16384⟩
    (by decide) selected_cut_10545

theorem selected_cut_10546 : selected 8 ⟨286040, by decide⟩
    (prefixPartial 13 100519) = some ⟨13, 2, 0, 286040, 100519, 701, 16384⟩ := by
  decide +kernel

theorem context_13_100519_286040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100519 ⟨286040, by decide⟩ :=
  accepted_of_selected 13 100519 ⟨286040, by decide⟩ ⟨13, 2, 0, 286040, 100519, 701, 16384⟩
    (by decide) selected_cut_10546

theorem unmarked_context_12_25129_286041 : frontier 9 ⟨286041, by decide⟩
    (prefixCache 12 25129) (prefixPartial 12 25129) = false := by
  decide +kernel

theorem node_context_12_25129_286041 : EJMOriginalGlobalDAGData.nodes 9 ⟨286041, by decide⟩ =
    .split (coordinate 12) (![⟨285990, by decide⟩,⟨286016, by decide⟩,⟨286035, by decide⟩,⟨286040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25129_286041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25129 ⟨286041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25129
    ⟨286041, by decide⟩ (by decide) (![⟨285990, by decide⟩,⟨286016, by decide⟩,⟨286035, by decide⟩,⟨286040, by decide⟩]) unmarked_context_12_25129_286041 node_context_12_25129_286041
  intro a
  fin_cases a
  · exact context_13_100516_285990
  · exact context_13_100517_286016
  · exact context_13_100518_286035
  · exact context_13_100519_286040

theorem selected_cut_10547 : selected 9 ⟨188189, by decide⟩
    (prefixPartial 12 25130) = some ⟨12, 1, 0, 188189, 25130, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25130_188189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25130 ⟨188189, by decide⟩ :=
  accepted_of_selected 12 25130 ⟨188189, by decide⟩ ⟨12, 1, 0, 188189, 25130, 1, 65536⟩
    (by decide) selected_cut_10547

theorem selected_cut_10548 : selected 8 ⟨286050, by decide⟩
    (prefixPartial 13 100524) = some ⟨13, 2, 0, 286050, 100524, 761, 16384⟩ := by
  decide +kernel

theorem context_13_100524_286050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100524 ⟨286050, by decide⟩ :=
  accepted_of_selected 13 100524 ⟨286050, by decide⟩ ⟨13, 2, 0, 286050, 100524, 761, 16384⟩
    (by decide) selected_cut_10548

theorem selected_cut_10549 : selected 8 ⟨286079, by decide⟩
    (prefixPartial 13 100525) = some ⟨13, 2, 0, 286079, 100525, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_100525_286079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100525 ⟨286079, by decide⟩ :=
  accepted_of_selected 13 100525 ⟨286079, by decide⟩ ⟨13, 2, 0, 286079, 100525, 2037, 16384⟩
    (by decide) selected_cut_10549

theorem selected_cut_10550 : selected 8 ⟨286095, by decide⟩
    (prefixPartial 13 100526) = some ⟨13, 2, 0, 286095, 100526, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_100526_286095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100526 ⟨286095, by decide⟩ :=
  accepted_of_selected 13 100526 ⟨286095, by decide⟩ ⟨13, 2, 0, 286095, 100526, 1121, 16384⟩
    (by decide) selected_cut_10550

theorem selected_cut_10551 : selected 8 ⟨286099, by decide⟩
    (prefixPartial 13 100527) = some ⟨13, 2, 0, 286099, 100527, 641, 16384⟩ := by
  decide +kernel

theorem context_13_100527_286099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100527 ⟨286099, by decide⟩ :=
  accepted_of_selected 13 100527 ⟨286099, by decide⟩ ⟨13, 2, 0, 286099, 100527, 641, 16384⟩
    (by decide) selected_cut_10551

theorem unmarked_context_12_25131_286100 : frontier 9 ⟨286100, by decide⟩
    (prefixCache 12 25131) (prefixPartial 12 25131) = false := by
  decide +kernel

theorem node_context_12_25131_286100 : EJMOriginalGlobalDAGData.nodes 9 ⟨286100, by decide⟩ =
    .split (coordinate 12) (![⟨286050, by decide⟩,⟨286079, by decide⟩,⟨286095, by decide⟩,⟨286099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25131_286100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25131 ⟨286100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25131
    ⟨286100, by decide⟩ (by decide) (![⟨286050, by decide⟩,⟨286079, by decide⟩,⟨286095, by decide⟩,⟨286099, by decide⟩]) unmarked_context_12_25131_286100 node_context_12_25131_286100
  intro a
  fin_cases a
  · exact context_13_100524_286050
  · exact context_13_100525_286079
  · exact context_13_100526_286095
  · exact context_13_100527_286099

theorem unmarked_context_11_6282_286101 : frontier 10 ⟨286101, by decide⟩
    (prefixCache 11 6282) (prefixPartial 11 6282) = false := by
  decide +kernel

theorem node_context_11_6282_286101 : EJMOriginalGlobalDAGData.nodes 10 ⟨286101, by decide⟩ =
    .split (coordinate 11) (![⟨285979, by decide⟩,⟨286041, by decide⟩,⟨188189, by decide⟩,⟨286100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6282_286101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6282 ⟨286101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6282
    ⟨286101, by decide⟩ (by decide) (![⟨285979, by decide⟩,⟨286041, by decide⟩,⟨188189, by decide⟩,⟨286100, by decide⟩]) unmarked_context_11_6282_286101 node_context_11_6282_286101
  intro a
  fin_cases a
  · exact context_12_25128_285979
  · exact context_12_25129_286041
  · exact context_12_25130_188189
  · exact context_12_25131_286100

theorem selected_cut_10552 : selected 8 ⟨286111, by decide⟩
    (prefixPartial 13 100528) = some ⟨13, 2, 0, 286111, 100528, 681, 16384⟩ := by
  decide +kernel

theorem context_13_100528_286111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100528 ⟨286111, by decide⟩ :=
  accepted_of_selected 13 100528 ⟨286111, by decide⟩ ⟨13, 2, 0, 286111, 100528, 681, 16384⟩
    (by decide) selected_cut_10552

theorem selected_cut_10553 : selected 8 ⟨286137, by decide⟩
    (prefixPartial 13 100529) = some ⟨13, 2, 0, 286137, 100529, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_100529_286137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100529 ⟨286137, by decide⟩ :=
  accepted_of_selected 13 100529 ⟨286137, by decide⟩ ⟨13, 2, 0, 286137, 100529, 1841, 16384⟩
    (by decide) selected_cut_10553

theorem selected_cut_10554 : selected 8 ⟨286154, by decide⟩
    (prefixPartial 13 100530) = some ⟨13, 2, 0, 286154, 100530, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_100530_286154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100530 ⟨286154, by decide⟩ :=
  accepted_of_selected 13 100530 ⟨286154, by decide⟩ ⟨13, 2, 0, 286154, 100530, 1253, 16384⟩
    (by decide) selected_cut_10554

theorem selected_cut_10555 : selected 8 ⟨286161, by decide⟩
    (prefixPartial 13 100531) = some ⟨13, 2, 0, 286161, 100531, 737, 16384⟩ := by
  decide +kernel

theorem context_13_100531_286161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100531 ⟨286161, by decide⟩ :=
  accepted_of_selected 13 100531 ⟨286161, by decide⟩ ⟨13, 2, 0, 286161, 100531, 737, 16384⟩
    (by decide) selected_cut_10555

theorem unmarked_context_12_25132_286162 : frontier 9 ⟨286162, by decide⟩
    (prefixCache 12 25132) (prefixPartial 12 25132) = false := by
  decide +kernel

theorem node_context_12_25132_286162 : EJMOriginalGlobalDAGData.nodes 9 ⟨286162, by decide⟩ =
    .split (coordinate 12) (![⟨286111, by decide⟩,⟨286137, by decide⟩,⟨286154, by decide⟩,⟨286161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25132_286162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25132 ⟨286162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25132
    ⟨286162, by decide⟩ (by decide) (![⟨286111, by decide⟩,⟨286137, by decide⟩,⟨286154, by decide⟩,⟨286161, by decide⟩]) unmarked_context_12_25132_286162 node_context_12_25132_286162
  intro a
  fin_cases a
  · exact context_13_100528_286111
  · exact context_13_100529_286137
  · exact context_13_100530_286154
  · exact context_13_100531_286161

theorem selected_cut_10556 : selected 8 ⟨286173, by decide⟩
    (prefixPartial 13 100532) = some ⟨13, 2, 0, 286173, 100532, 801, 16384⟩ := by
  decide +kernel

theorem context_13_100532_286173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100532 ⟨286173, by decide⟩ :=
  accepted_of_selected 13 100532 ⟨286173, by decide⟩ ⟨13, 2, 0, 286173, 100532, 801, 16384⟩
    (by decide) selected_cut_10556

theorem selected_cut_10557 : selected 8 ⟨286199, by decide⟩
    (prefixPartial 13 100533) = some ⟨13, 2, 0, 286199, 100533, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_100533_286199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100533 ⟨286199, by decide⟩ :=
  accepted_of_selected 13 100533 ⟨286199, by decide⟩ ⟨13, 2, 0, 286199, 100533, 2377, 16384⟩
    (by decide) selected_cut_10557

theorem selected_cut_10558 : selected 8 ⟨286219, by decide⟩
    (prefixPartial 13 100534) = some ⟨13, 2, 0, 286219, 100534, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_100534_286219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100534 ⟨286219, by decide⟩ :=
  accepted_of_selected 13 100534 ⟨286219, by decide⟩ ⟨13, 2, 0, 286219, 100534, 1557, 16384⟩
    (by decide) selected_cut_10558

theorem selected_cut_10559 : selected 8 ⟨286224, by decide⟩
    (prefixPartial 13 100535) = some ⟨13, 2, 0, 286224, 100535, 829, 16384⟩ := by
  decide +kernel

theorem context_13_100535_286224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100535 ⟨286224, by decide⟩ :=
  accepted_of_selected 13 100535 ⟨286224, by decide⟩ ⟨13, 2, 0, 286224, 100535, 829, 16384⟩
    (by decide) selected_cut_10559

theorem unmarked_context_12_25133_286225 : frontier 9 ⟨286225, by decide⟩
    (prefixCache 12 25133) (prefixPartial 12 25133) = false := by
  decide +kernel

theorem node_context_12_25133_286225 : EJMOriginalGlobalDAGData.nodes 9 ⟨286225, by decide⟩ =
    .split (coordinate 12) (![⟨286173, by decide⟩,⟨286199, by decide⟩,⟨286219, by decide⟩,⟨286224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25133_286225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25133 ⟨286225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25133
    ⟨286225, by decide⟩ (by decide) (![⟨286173, by decide⟩,⟨286199, by decide⟩,⟨286219, by decide⟩,⟨286224, by decide⟩]) unmarked_context_12_25133_286225 node_context_12_25133_286225
  intro a
  fin_cases a
  · exact context_13_100532_286173
  · exact context_13_100533_286199
  · exact context_13_100534_286219
  · exact context_13_100535_286224

theorem selected_cut_10560 : selected 8 ⟨286234, by decide⟩
    (prefixPartial 13 100536) = some ⟨13, 2, 0, 286234, 100536, 577, 16384⟩ := by
  decide +kernel

theorem context_13_100536_286234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100536 ⟨286234, by decide⟩ :=
  accepted_of_selected 13 100536 ⟨286234, by decide⟩ ⟨13, 2, 0, 286234, 100536, 577, 16384⟩
    (by decide) selected_cut_10560

theorem selected_cut_10561 : selected 8 ⟨286261, by decide⟩
    (prefixPartial 13 100537) = some ⟨13, 2, 0, 286261, 100537, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_100537_286261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100537 ⟨286261, by decide⟩ :=
  accepted_of_selected 13 100537 ⟨286261, by decide⟩ ⟨13, 2, 0, 286261, 100537, 1945, 16384⟩
    (by decide) selected_cut_10561

theorem selected_cut_10562 : selected 8 ⟨286273, by decide⟩
    (prefixPartial 13 100538) = some ⟨13, 2, 0, 286273, 100538, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_100538_286273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100538 ⟨286273, by decide⟩ :=
  accepted_of_selected 13 100538 ⟨286273, by decide⟩ ⟨13, 2, 0, 286273, 100538, 1061, 16384⟩
    (by decide) selected_cut_10562

theorem selected_cut_10563 : selected 8 ⟨286279, by decide⟩
    (prefixPartial 13 100539) = some ⟨13, 2, 0, 286279, 100539, 729, 16384⟩ := by
  decide +kernel

theorem context_13_100539_286279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100539 ⟨286279, by decide⟩ :=
  accepted_of_selected 13 100539 ⟨286279, by decide⟩ ⟨13, 2, 0, 286279, 100539, 729, 16384⟩
    (by decide) selected_cut_10563

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
