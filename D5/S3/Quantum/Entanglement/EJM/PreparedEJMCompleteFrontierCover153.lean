/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover152
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14692 : selected 7 ⟨379019, by decide⟩
    (prefixPartial 14 438517) = some ⟨14, 2, 0, 379019, 438517, 1601, 4096⟩ := by
  decide +kernel

theorem context_14_438517_379019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438517 ⟨379019, by decide⟩ :=
  accepted_of_selected 14 438517 ⟨379019, by decide⟩ ⟨14, 2, 0, 379019, 438517, 1601, 4096⟩
    (by decide) selected_cut_14692

theorem selected_cut_14693 : selected 7 ⟨379061, by decide⟩
    (prefixPartial 14 438518) = some ⟨14, 2, 0, 379061, 438518, 1665, 4096⟩ := by
  decide +kernel

theorem context_14_438518_379061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438518 ⟨379061, by decide⟩ :=
  accepted_of_selected 14 438518 ⟨379061, by decide⟩ ⟨14, 2, 0, 379061, 438518, 1665, 4096⟩
    (by decide) selected_cut_14693

theorem selected_cut_14694 : selected 7 ⟨379100, by decide⟩
    (prefixPartial 14 438519) = some ⟨14, 2, 0, 379100, 438519, 1269, 4096⟩ := by
  decide +kernel

theorem context_14_438519_379100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 438519 ⟨379100, by decide⟩ :=
  accepted_of_selected 14 438519 ⟨379100, by decide⟩ ⟨14, 2, 0, 379100, 438519, 1269, 4096⟩
    (by decide) selected_cut_14694

theorem unmarked_context_13_109629_379101 : frontier 8 ⟨379101, by decide⟩
    (prefixCache 13 109629) (prefixPartial 13 109629) = false := by
  decide +kernel

theorem node_context_13_109629_379101 : EJMOriginalGlobalDAGData.nodes 8 ⟨379101, by decide⟩ =
    .split (coordinate 13) (![⟨378977, by decide⟩,⟨379019, by decide⟩,⟨379061, by decide⟩,⟨379100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_109629_379101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109629 ⟨379101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 109629
    ⟨379101, by decide⟩ (by decide) (![⟨378977, by decide⟩,⟨379019, by decide⟩,⟨379061, by decide⟩,⟨379100, by decide⟩]) unmarked_context_13_109629_379101 node_context_13_109629_379101
  intro a
  fin_cases a
  · exact context_14_438516_378977
  · exact context_14_438517_379019
  · exact context_14_438518_379061
  · exact context_14_438519_379100

theorem selected_cut_14695 : selected 8 ⟨379219, by decide⟩
    (prefixPartial 13 109630) = some ⟨13, 2, 0, 379219, 109630, 3593, 16384⟩ := by
  decide +kernel

theorem context_13_109630_379219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109630 ⟨379219, by decide⟩ :=
  accepted_of_selected 13 109630 ⟨379219, by decide⟩ ⟨13, 2, 0, 379219, 109630, 3593, 16384⟩
    (by decide) selected_cut_14695

theorem selected_cut_14696 : selected 8 ⟨379280, by decide⟩
    (prefixPartial 13 109631) = some ⟨13, 2, 0, 379280, 109631, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_109631_379280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109631 ⟨379280, by decide⟩ :=
  accepted_of_selected 13 109631 ⟨379280, by decide⟩ ⟨13, 2, 0, 379280, 109631, 1413, 16384⟩
    (by decide) selected_cut_14696

theorem unmarked_context_12_27407_379281 : frontier 9 ⟨379281, by decide⟩
    (prefixCache 12 27407) (prefixPartial 12 27407) = false := by
  decide +kernel

theorem node_context_12_27407_379281 : EJMOriginalGlobalDAGData.nodes 9 ⟨379281, by decide⟩ =
    .split (coordinate 12) (![⟨378930, by decide⟩,⟨379101, by decide⟩,⟨379219, by decide⟩,⟨379280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27407_379281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27407 ⟨379281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27407
    ⟨379281, by decide⟩ (by decide) (![⟨378930, by decide⟩,⟨379101, by decide⟩,⟨379219, by decide⟩,⟨379280, by decide⟩]) unmarked_context_12_27407_379281 node_context_12_27407_379281
  intro a
  fin_cases a
  · exact context_13_109628_378930
  · exact context_13_109629_379101
  · exact context_13_109630_379219
  · exact context_13_109631_379280

theorem unmarked_context_11_6851_379282 : frontier 10 ⟨379282, by decide⟩
    (prefixCache 11 6851) (prefixPartial 11 6851) = false := by
  decide +kernel

theorem node_context_11_6851_379282 : EJMOriginalGlobalDAGData.nodes 10 ⟨379282, by decide⟩ =
    .split (coordinate 11) (![⟨378507, by decide⟩,⟨378656, by decide⟩,⟨378834, by decide⟩,⟨379281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6851_379282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6851 ⟨379282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6851
    ⟨379282, by decide⟩ (by decide) (![⟨378507, by decide⟩,⟨378656, by decide⟩,⟨378834, by decide⟩,⟨379281, by decide⟩]) unmarked_context_11_6851_379282 node_context_11_6851_379282
  intro a
  fin_cases a
  · exact context_12_27404_378507
  · exact context_12_27405_378656
  · exact context_12_27406_378834
  · exact context_12_27407_379281

theorem unmarked_context_10_1712_379283 : frontier 11 ⟨379283, by decide⟩
    (prefixCache 10 1712) (prefixPartial 10 1712) = false := by
  decide +kernel

theorem node_context_10_1712_379283 : EJMOriginalGlobalDAGData.nodes 11 ⟨379283, by decide⟩ =
    .split (coordinate 10) (![⟨377015, by decide⟩,⟨377552, by decide⟩,⟨378359, by decide⟩,⟨379282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1712_379283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1712 ⟨379283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1712
    ⟨379283, by decide⟩ (by decide) (![⟨377015, by decide⟩,⟨377552, by decide⟩,⟨378359, by decide⟩,⟨379282, by decide⟩]) unmarked_context_10_1712_379283 node_context_10_1712_379283
  intro a
  fin_cases a
  · exact context_11_6848_377015
  · exact context_11_6849_377552
  · exact context_11_6850_378359
  · exact context_11_6851_379282

theorem selected_cut_14697 : selected 8 ⟨379309, by decide⟩
    (prefixPartial 13 109632) = some ⟨13, 2, 0, 379309, 109632, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_109632_379309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109632 ⟨379309, by decide⟩ :=
  accepted_of_selected 13 109632 ⟨379309, by decide⟩ ⟨13, 2, 0, 379309, 109632, 1809, 16384⟩
    (by decide) selected_cut_14697

theorem selected_cut_14698 : selected 8 ⟨379335, by decide⟩
    (prefixPartial 13 109633) = some ⟨13, 2, 0, 379335, 109633, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_109633_379335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109633 ⟨379335, by decide⟩ :=
  accepted_of_selected 13 109633 ⟨379335, by decide⟩ ⟨13, 2, 0, 379335, 109633, 2257, 16384⟩
    (by decide) selected_cut_14698

theorem selected_cut_14699 : selected 8 ⟨379346, by decide⟩
    (prefixPartial 13 109634) = some ⟨13, 2, 0, 379346, 109634, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_109634_379346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109634 ⟨379346, by decide⟩ :=
  accepted_of_selected 13 109634 ⟨379346, by decide⟩ ⟨13, 2, 0, 379346, 109634, 1297, 16384⟩
    (by decide) selected_cut_14699

theorem selected_cut_14700 : selected 8 ⟨379351, by decide⟩
    (prefixPartial 13 109635) = some ⟨13, 2, 0, 379351, 109635, 817, 16384⟩ := by
  decide +kernel

theorem context_13_109635_379351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109635 ⟨379351, by decide⟩ :=
  accepted_of_selected 13 109635 ⟨379351, by decide⟩ ⟨13, 2, 0, 379351, 109635, 817, 16384⟩
    (by decide) selected_cut_14700

theorem unmarked_context_12_27408_379352 : frontier 9 ⟨379352, by decide⟩
    (prefixCache 12 27408) (prefixPartial 12 27408) = false := by
  decide +kernel

theorem node_context_12_27408_379352 : EJMOriginalGlobalDAGData.nodes 9 ⟨379352, by decide⟩ =
    .split (coordinate 12) (![⟨379309, by decide⟩,⟨379335, by decide⟩,⟨379346, by decide⟩,⟨379351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27408_379352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27408 ⟨379352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27408
    ⟨379352, by decide⟩ (by decide) (![⟨379309, by decide⟩,⟨379335, by decide⟩,⟨379346, by decide⟩,⟨379351, by decide⟩]) unmarked_context_12_27408_379352 node_context_12_27408_379352
  intro a
  fin_cases a
  · exact context_13_109632_379309
  · exact context_13_109633_379335
  · exact context_13_109634_379346
  · exact context_13_109635_379351

theorem selected_cut_14701 : selected 8 ⟨379380, by decide⟩
    (prefixPartial 13 109636) = some ⟨13, 2, 0, 379380, 109636, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_109636_379380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109636 ⟨379380, by decide⟩ :=
  accepted_of_selected 13 109636 ⟨379380, by decide⟩ ⟨13, 2, 0, 379380, 109636, 2205, 16384⟩
    (by decide) selected_cut_14701

theorem selected_cut_14702 : selected 8 ⟨379407, by decide⟩
    (prefixPartial 13 109637) = some ⟨13, 2, 0, 379407, 109637, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_109637_379407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109637 ⟨379407, by decide⟩ :=
  accepted_of_selected 13 109637 ⟨379407, by decide⟩ ⟨13, 2, 0, 379407, 109637, 2153, 16384⟩
    (by decide) selected_cut_14702

theorem selected_cut_14703 : selected 8 ⟨379426, by decide⟩
    (prefixPartial 13 109638) = some ⟨13, 2, 0, 379426, 109638, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_109638_379426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109638 ⟨379426, by decide⟩ :=
  accepted_of_selected 13 109638 ⟨379426, by decide⟩ ⟨13, 2, 0, 379426, 109638, 1537, 16384⟩
    (by decide) selected_cut_14703

theorem selected_cut_14704 : selected 8 ⟨379433, by decide⟩
    (prefixPartial 13 109639) = some ⟨13, 2, 0, 379433, 109639, 673, 16384⟩ := by
  decide +kernel

theorem context_13_109639_379433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109639 ⟨379433, by decide⟩ :=
  accepted_of_selected 13 109639 ⟨379433, by decide⟩ ⟨13, 2, 0, 379433, 109639, 673, 16384⟩
    (by decide) selected_cut_14704

theorem unmarked_context_12_27409_379434 : frontier 9 ⟨379434, by decide⟩
    (prefixCache 12 27409) (prefixPartial 12 27409) = false := by
  decide +kernel

theorem node_context_12_27409_379434 : EJMOriginalGlobalDAGData.nodes 9 ⟨379434, by decide⟩ =
    .split (coordinate 12) (![⟨379380, by decide⟩,⟨379407, by decide⟩,⟨379426, by decide⟩,⟨379433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27409_379434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27409 ⟨379434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27409
    ⟨379434, by decide⟩ (by decide) (![⟨379380, by decide⟩,⟨379407, by decide⟩,⟨379426, by decide⟩,⟨379433, by decide⟩]) unmarked_context_12_27409_379434 node_context_12_27409_379434
  intro a
  fin_cases a
  · exact context_13_109636_379380
  · exact context_13_109637_379407
  · exact context_13_109638_379426
  · exact context_13_109639_379433

theorem selected_cut_14705 : selected 8 ⟨379461, by decide⟩
    (prefixPartial 13 109640) = some ⟨13, 2, 0, 379461, 109640, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_109640_379461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109640 ⟨379461, by decide⟩ :=
  accepted_of_selected 13 109640 ⟨379461, by decide⟩ ⟨13, 2, 0, 379461, 109640, 2205, 16384⟩
    (by decide) selected_cut_14705

theorem selected_cut_14706 : selected 8 ⟨379494, by decide⟩
    (prefixPartial 13 109641) = some ⟨13, 2, 0, 379494, 109641, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_109641_379494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109641 ⟨379494, by decide⟩ :=
  accepted_of_selected 13 109641 ⟨379494, by decide⟩ ⟨13, 2, 0, 379494, 109641, 2493, 16384⟩
    (by decide) selected_cut_14706

theorem selected_cut_14707 : selected 8 ⟨379520, by decide⟩
    (prefixPartial 13 109642) = some ⟨13, 2, 0, 379520, 109642, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_109642_379520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109642 ⟨379520, by decide⟩ :=
  accepted_of_selected 13 109642 ⟨379520, by decide⟩ ⟨13, 2, 0, 379520, 109642, 1717, 16384⟩
    (by decide) selected_cut_14707

theorem selected_cut_14708 : selected 8 ⟨379526, by decide⟩
    (prefixPartial 13 109643) = some ⟨13, 2, 0, 379526, 109643, 773, 16384⟩ := by
  decide +kernel

theorem context_13_109643_379526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109643 ⟨379526, by decide⟩ :=
  accepted_of_selected 13 109643 ⟨379526, by decide⟩ ⟨13, 2, 0, 379526, 109643, 773, 16384⟩
    (by decide) selected_cut_14708

theorem unmarked_context_12_27410_379527 : frontier 9 ⟨379527, by decide⟩
    (prefixCache 12 27410) (prefixPartial 12 27410) = false := by
  decide +kernel

theorem node_context_12_27410_379527 : EJMOriginalGlobalDAGData.nodes 9 ⟨379527, by decide⟩ =
    .split (coordinate 12) (![⟨379461, by decide⟩,⟨379494, by decide⟩,⟨379520, by decide⟩,⟨379526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27410_379527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27410 ⟨379527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27410
    ⟨379527, by decide⟩ (by decide) (![⟨379461, by decide⟩,⟨379494, by decide⟩,⟨379520, by decide⟩,⟨379526, by decide⟩]) unmarked_context_12_27410_379527 node_context_12_27410_379527
  intro a
  fin_cases a
  · exact context_13_109640_379461
  · exact context_13_109641_379494
  · exact context_13_109642_379520
  · exact context_13_109643_379526

theorem selected_cut_14709 : selected 8 ⟨379548, by decide⟩
    (prefixPartial 13 109644) = some ⟨13, 2, 0, 379548, 109644, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_109644_379548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109644 ⟨379548, by decide⟩ :=
  accepted_of_selected 13 109644 ⟨379548, by decide⟩ ⟨13, 2, 0, 379548, 109644, 2113, 16384⟩
    (by decide) selected_cut_14709

theorem selected_cut_14710 : selected 8 ⟨379573, by decide⟩
    (prefixPartial 13 109645) = some ⟨13, 2, 0, 379573, 109645, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_109645_379573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109645 ⟨379573, by decide⟩ :=
  accepted_of_selected 13 109645 ⟨379573, by decide⟩ ⟨13, 2, 0, 379573, 109645, 2673, 16384⟩
    (by decide) selected_cut_14710

theorem selected_cut_14711 : selected 8 ⟨379592, by decide⟩
    (prefixPartial 13 109646) = some ⟨13, 2, 0, 379592, 109646, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_109646_379592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109646 ⟨379592, by decide⟩ :=
  accepted_of_selected 13 109646 ⟨379592, by decide⟩ ⟨13, 2, 0, 379592, 109646, 1509, 16384⟩
    (by decide) selected_cut_14711

theorem selected_cut_14712 : selected 8 ⟨379597, by decide⟩
    (prefixPartial 13 109647) = some ⟨13, 2, 0, 379597, 109647, 781, 16384⟩ := by
  decide +kernel

theorem context_13_109647_379597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109647 ⟨379597, by decide⟩ :=
  accepted_of_selected 13 109647 ⟨379597, by decide⟩ ⟨13, 2, 0, 379597, 109647, 781, 16384⟩
    (by decide) selected_cut_14712

theorem unmarked_context_12_27411_379598 : frontier 9 ⟨379598, by decide⟩
    (prefixCache 12 27411) (prefixPartial 12 27411) = false := by
  decide +kernel

theorem node_context_12_27411_379598 : EJMOriginalGlobalDAGData.nodes 9 ⟨379598, by decide⟩ =
    .split (coordinate 12) (![⟨379548, by decide⟩,⟨379573, by decide⟩,⟨379592, by decide⟩,⟨379597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27411_379598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27411 ⟨379598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27411
    ⟨379598, by decide⟩ (by decide) (![⟨379548, by decide⟩,⟨379573, by decide⟩,⟨379592, by decide⟩,⟨379597, by decide⟩]) unmarked_context_12_27411_379598 node_context_12_27411_379598
  intro a
  fin_cases a
  · exact context_13_109644_379548
  · exact context_13_109645_379573
  · exact context_13_109646_379592
  · exact context_13_109647_379597

theorem unmarked_context_11_6852_379599 : frontier 10 ⟨379599, by decide⟩
    (prefixCache 11 6852) (prefixPartial 11 6852) = false := by
  decide +kernel

theorem node_context_11_6852_379599 : EJMOriginalGlobalDAGData.nodes 10 ⟨379599, by decide⟩ =
    .split (coordinate 11) (![⟨379352, by decide⟩,⟨379434, by decide⟩,⟨379527, by decide⟩,⟨379598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6852_379599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6852 ⟨379599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6852
    ⟨379599, by decide⟩ (by decide) (![⟨379352, by decide⟩,⟨379434, by decide⟩,⟨379527, by decide⟩,⟨379598, by decide⟩]) unmarked_context_11_6852_379599 node_context_11_6852_379599
  intro a
  fin_cases a
  · exact context_12_27408_379352
  · exact context_12_27409_379434
  · exact context_12_27410_379527
  · exact context_12_27411_379598

theorem selected_cut_14713 : selected 8 ⟨379616, by decide⟩
    (prefixPartial 13 109648) = some ⟨13, 2, 0, 379616, 109648, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_109648_379616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109648 ⟨379616, by decide⟩ :=
  accepted_of_selected 13 109648 ⟨379616, by decide⟩ ⟨13, 2, 0, 379616, 109648, 1661, 16384⟩
    (by decide) selected_cut_14713

theorem selected_cut_14714 : selected 8 ⟨379651, by decide⟩
    (prefixPartial 13 109649) = some ⟨13, 2, 0, 379651, 109649, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_109649_379651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109649 ⟨379651, by decide⟩ :=
  accepted_of_selected 13 109649 ⟨379651, by decide⟩ ⟨13, 2, 0, 379651, 109649, 2613, 16384⟩
    (by decide) selected_cut_14714

theorem selected_cut_14715 : selected 8 ⟨379670, by decide⟩
    (prefixPartial 13 109650) = some ⟨13, 2, 0, 379670, 109650, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_109650_379670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109650 ⟨379670, by decide⟩ :=
  accepted_of_selected 13 109650 ⟨379670, by decide⟩ ⟨13, 2, 0, 379670, 109650, 1477, 16384⟩
    (by decide) selected_cut_14715

theorem selected_cut_14716 : selected 8 ⟨379676, by decide⟩
    (prefixPartial 13 109651) = some ⟨13, 2, 0, 379676, 109651, 889, 16384⟩ := by
  decide +kernel

theorem context_13_109651_379676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109651 ⟨379676, by decide⟩ :=
  accepted_of_selected 13 109651 ⟨379676, by decide⟩ ⟨13, 2, 0, 379676, 109651, 889, 16384⟩
    (by decide) selected_cut_14716

theorem unmarked_context_12_27412_379677 : frontier 9 ⟨379677, by decide⟩
    (prefixCache 12 27412) (prefixPartial 12 27412) = false := by
  decide +kernel

theorem node_context_12_27412_379677 : EJMOriginalGlobalDAGData.nodes 9 ⟨379677, by decide⟩ =
    .split (coordinate 12) (![⟨379616, by decide⟩,⟨379651, by decide⟩,⟨379670, by decide⟩,⟨379676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27412_379677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27412 ⟨379677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27412
    ⟨379677, by decide⟩ (by decide) (![⟨379616, by decide⟩,⟨379651, by decide⟩,⟨379670, by decide⟩,⟨379676, by decide⟩]) unmarked_context_12_27412_379677 node_context_12_27412_379677
  intro a
  fin_cases a
  · exact context_13_109648_379616
  · exact context_13_109649_379651
  · exact context_13_109650_379670
  · exact context_13_109651_379676

theorem selected_cut_14717 : selected 8 ⟨379704, by decide⟩
    (prefixPartial 13 109652) = some ⟨13, 2, 0, 379704, 109652, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_109652_379704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109652 ⟨379704, by decide⟩ :=
  accepted_of_selected 13 109652 ⟨379704, by decide⟩ ⟨13, 2, 0, 379704, 109652, 1941, 16384⟩
    (by decide) selected_cut_14717

theorem selected_cut_14718 : selected 8 ⟨379730, by decide⟩
    (prefixPartial 13 109653) = some ⟨13, 2, 0, 379730, 109653, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_109653_379730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109653 ⟨379730, by decide⟩ :=
  accepted_of_selected 13 109653 ⟨379730, by decide⟩ ⟨13, 2, 0, 379730, 109653, 2137, 16384⟩
    (by decide) selected_cut_14718

theorem selected_cut_14719 : selected 8 ⟨379750, by decide⟩
    (prefixPartial 13 109654) = some ⟨13, 2, 0, 379750, 109654, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_109654_379750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109654 ⟨379750, by decide⟩ :=
  accepted_of_selected 13 109654 ⟨379750, by decide⟩ ⟨13, 2, 0, 379750, 109654, 1581, 16384⟩
    (by decide) selected_cut_14719

theorem selected_cut_14720 : selected 8 ⟨379758, by decide⟩
    (prefixPartial 13 109655) = some ⟨13, 2, 0, 379758, 109655, 825, 16384⟩ := by
  decide +kernel

theorem context_13_109655_379758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109655 ⟨379758, by decide⟩ :=
  accepted_of_selected 13 109655 ⟨379758, by decide⟩ ⟨13, 2, 0, 379758, 109655, 825, 16384⟩
    (by decide) selected_cut_14720

theorem unmarked_context_12_27413_379759 : frontier 9 ⟨379759, by decide⟩
    (prefixCache 12 27413) (prefixPartial 12 27413) = false := by
  decide +kernel

theorem node_context_12_27413_379759 : EJMOriginalGlobalDAGData.nodes 9 ⟨379759, by decide⟩ =
    .split (coordinate 12) (![⟨379704, by decide⟩,⟨379730, by decide⟩,⟨379750, by decide⟩,⟨379758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27413_379759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27413 ⟨379759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27413
    ⟨379759, by decide⟩ (by decide) (![⟨379704, by decide⟩,⟨379730, by decide⟩,⟨379750, by decide⟩,⟨379758, by decide⟩]) unmarked_context_12_27413_379759 node_context_12_27413_379759
  intro a
  fin_cases a
  · exact context_13_109652_379704
  · exact context_13_109653_379730
  · exact context_13_109654_379750
  · exact context_13_109655_379758

theorem selected_cut_14721 : selected 8 ⟨379779, by decide⟩
    (prefixPartial 13 109656) = some ⟨13, 2, 0, 379779, 109656, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_109656_379779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109656 ⟨379779, by decide⟩ :=
  accepted_of_selected 13 109656 ⟨379779, by decide⟩ ⟨13, 2, 0, 379779, 109656, 2045, 16384⟩
    (by decide) selected_cut_14721

theorem selected_cut_14722 : selected 8 ⟨379808, by decide⟩
    (prefixPartial 13 109657) = some ⟨13, 2, 0, 379808, 109657, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_109657_379808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109657 ⟨379808, by decide⟩ :=
  accepted_of_selected 13 109657 ⟨379808, by decide⟩ ⟨13, 2, 0, 379808, 109657, 2549, 16384⟩
    (by decide) selected_cut_14722

theorem selected_cut_14723 : selected 8 ⟨379831, by decide⟩
    (prefixPartial 13 109658) = some ⟨13, 2, 0, 379831, 109658, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_109658_379831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109658 ⟨379831, by decide⟩ :=
  accepted_of_selected 13 109658 ⟨379831, by decide⟩ ⟨13, 2, 0, 379831, 109658, 1821, 16384⟩
    (by decide) selected_cut_14723

theorem selected_cut_14724 : selected 8 ⟨379840, by decide⟩
    (prefixPartial 13 109659) = some ⟨13, 2, 0, 379840, 109659, 949, 16384⟩ := by
  decide +kernel

theorem context_13_109659_379840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109659 ⟨379840, by decide⟩ :=
  accepted_of_selected 13 109659 ⟨379840, by decide⟩ ⟨13, 2, 0, 379840, 109659, 949, 16384⟩
    (by decide) selected_cut_14724

theorem unmarked_context_12_27414_379841 : frontier 9 ⟨379841, by decide⟩
    (prefixCache 12 27414) (prefixPartial 12 27414) = false := by
  decide +kernel

theorem node_context_12_27414_379841 : EJMOriginalGlobalDAGData.nodes 9 ⟨379841, by decide⟩ =
    .split (coordinate 12) (![⟨379779, by decide⟩,⟨379808, by decide⟩,⟨379831, by decide⟩,⟨379840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27414_379841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27414 ⟨379841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27414
    ⟨379841, by decide⟩ (by decide) (![⟨379779, by decide⟩,⟨379808, by decide⟩,⟨379831, by decide⟩,⟨379840, by decide⟩]) unmarked_context_12_27414_379841 node_context_12_27414_379841
  intro a
  fin_cases a
  · exact context_13_109656_379779
  · exact context_13_109657_379808
  · exact context_13_109658_379831
  · exact context_13_109659_379840

theorem selected_cut_14725 : selected 8 ⟨379866, by decide⟩
    (prefixPartial 13 109660) = some ⟨13, 2, 0, 379866, 109660, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_109660_379866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109660 ⟨379866, by decide⟩ :=
  accepted_of_selected 13 109660 ⟨379866, by decide⟩ ⟨13, 2, 0, 379866, 109660, 1885, 16384⟩
    (by decide) selected_cut_14725

theorem selected_cut_14726 : selected 8 ⟨379892, by decide⟩
    (prefixPartial 13 109661) = some ⟨13, 2, 0, 379892, 109661, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_109661_379892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109661 ⟨379892, by decide⟩ :=
  accepted_of_selected 13 109661 ⟨379892, by decide⟩ ⟨13, 2, 0, 379892, 109661, 2489, 16384⟩
    (by decide) selected_cut_14726

theorem selected_cut_14727 : selected 8 ⟨379912, by decide⟩
    (prefixPartial 13 109662) = some ⟨13, 2, 0, 379912, 109662, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_109662_379912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109662 ⟨379912, by decide⟩ :=
  accepted_of_selected 13 109662 ⟨379912, by decide⟩ ⟨13, 2, 0, 379912, 109662, 1669, 16384⟩
    (by decide) selected_cut_14727

theorem selected_cut_14728 : selected 8 ⟨379920, by decide⟩
    (prefixPartial 13 109663) = some ⟨13, 2, 0, 379920, 109663, 897, 16384⟩ := by
  decide +kernel

theorem context_13_109663_379920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109663 ⟨379920, by decide⟩ :=
  accepted_of_selected 13 109663 ⟨379920, by decide⟩ ⟨13, 2, 0, 379920, 109663, 897, 16384⟩
    (by decide) selected_cut_14728

theorem unmarked_context_12_27415_379921 : frontier 9 ⟨379921, by decide⟩
    (prefixCache 12 27415) (prefixPartial 12 27415) = false := by
  decide +kernel

theorem node_context_12_27415_379921 : EJMOriginalGlobalDAGData.nodes 9 ⟨379921, by decide⟩ =
    .split (coordinate 12) (![⟨379866, by decide⟩,⟨379892, by decide⟩,⟨379912, by decide⟩,⟨379920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27415_379921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27415 ⟨379921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27415
    ⟨379921, by decide⟩ (by decide) (![⟨379866, by decide⟩,⟨379892, by decide⟩,⟨379912, by decide⟩,⟨379920, by decide⟩]) unmarked_context_12_27415_379921 node_context_12_27415_379921
  intro a
  fin_cases a
  · exact context_13_109660_379866
  · exact context_13_109661_379892
  · exact context_13_109662_379912
  · exact context_13_109663_379920

theorem unmarked_context_11_6853_379922 : frontier 10 ⟨379922, by decide⟩
    (prefixCache 11 6853) (prefixPartial 11 6853) = false := by
  decide +kernel

theorem node_context_11_6853_379922 : EJMOriginalGlobalDAGData.nodes 10 ⟨379922, by decide⟩ =
    .split (coordinate 11) (![⟨379677, by decide⟩,⟨379759, by decide⟩,⟨379841, by decide⟩,⟨379921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6853_379922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6853 ⟨379922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6853
    ⟨379922, by decide⟩ (by decide) (![⟨379677, by decide⟩,⟨379759, by decide⟩,⟨379841, by decide⟩,⟨379921, by decide⟩]) unmarked_context_11_6853_379922 node_context_11_6853_379922
  intro a
  fin_cases a
  · exact context_12_27412_379677
  · exact context_12_27413_379759
  · exact context_12_27414_379841
  · exact context_12_27415_379921

theorem selected_cut_14729 : selected 8 ⟨379940, by decide⟩
    (prefixPartial 13 109664) = some ⟨13, 2, 0, 379940, 109664, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_109664_379940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109664 ⟨379940, by decide⟩ :=
  accepted_of_selected 13 109664 ⟨379940, by decide⟩ ⟨13, 2, 0, 379940, 109664, 1461, 16384⟩
    (by decide) selected_cut_14729

theorem selected_cut_14730 : selected 8 ⟨379975, by decide⟩
    (prefixPartial 13 109665) = some ⟨13, 2, 0, 379975, 109665, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_109665_379975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109665 ⟨379975, by decide⟩ :=
  accepted_of_selected 13 109665 ⟨379975, by decide⟩ ⟨13, 2, 0, 379975, 109665, 2517, 16384⟩
    (by decide) selected_cut_14730

theorem selected_cut_14731 : selected 8 ⟨379989, by decide⟩
    (prefixPartial 13 109666) = some ⟨13, 2, 0, 379989, 109666, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_109666_379989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109666 ⟨379989, by decide⟩ :=
  accepted_of_selected 13 109666 ⟨379989, by decide⟩ ⟨13, 2, 0, 379989, 109666, 1489, 16384⟩
    (by decide) selected_cut_14731

theorem selected_cut_14732 : selected 8 ⟨379995, by decide⟩
    (prefixPartial 13 109667) = some ⟨13, 2, 0, 379995, 109667, 737, 16384⟩ := by
  decide +kernel

theorem context_13_109667_379995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109667 ⟨379995, by decide⟩ :=
  accepted_of_selected 13 109667 ⟨379995, by decide⟩ ⟨13, 2, 0, 379995, 109667, 737, 16384⟩
    (by decide) selected_cut_14732

theorem unmarked_context_12_27416_379996 : frontier 9 ⟨379996, by decide⟩
    (prefixCache 12 27416) (prefixPartial 12 27416) = false := by
  decide +kernel

theorem node_context_12_27416_379996 : EJMOriginalGlobalDAGData.nodes 9 ⟨379996, by decide⟩ =
    .split (coordinate 12) (![⟨379940, by decide⟩,⟨379975, by decide⟩,⟨379989, by decide⟩,⟨379995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27416_379996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27416 ⟨379996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27416
    ⟨379996, by decide⟩ (by decide) (![⟨379940, by decide⟩,⟨379975, by decide⟩,⟨379989, by decide⟩,⟨379995, by decide⟩]) unmarked_context_12_27416_379996 node_context_12_27416_379996
  intro a
  fin_cases a
  · exact context_13_109664_379940
  · exact context_13_109665_379975
  · exact context_13_109666_379989
  · exact context_13_109667_379995

theorem selected_cut_14733 : selected 8 ⟨380018, by decide⟩
    (prefixPartial 13 109668) = some ⟨13, 2, 0, 380018, 109668, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_109668_380018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109668 ⟨380018, by decide⟩ :=
  accepted_of_selected 13 109668 ⟨380018, by decide⟩ ⟨13, 2, 0, 380018, 109668, 1589, 16384⟩
    (by decide) selected_cut_14733

theorem selected_cut_14734 : selected 8 ⟨380049, by decide⟩
    (prefixPartial 13 109669) = some ⟨13, 2, 0, 380049, 109669, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_109669_380049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109669 ⟨380049, by decide⟩ :=
  accepted_of_selected 13 109669 ⟨380049, by decide⟩ ⟨13, 2, 0, 380049, 109669, 2177, 16384⟩
    (by decide) selected_cut_14734

theorem selected_cut_14735 : selected 8 ⟨380065, by decide⟩
    (prefixPartial 13 109670) = some ⟨13, 2, 0, 380065, 109670, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_109670_380065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109670 ⟨380065, by decide⟩ :=
  accepted_of_selected 13 109670 ⟨380065, by decide⟩ ⟨13, 2, 0, 380065, 109670, 1461, 16384⟩
    (by decide) selected_cut_14735

theorem selected_cut_14736 : selected 8 ⟨380070, by decide⟩
    (prefixPartial 13 109671) = some ⟨13, 2, 0, 380070, 109671, 717, 16384⟩ := by
  decide +kernel

theorem context_13_109671_380070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109671 ⟨380070, by decide⟩ :=
  accepted_of_selected 13 109671 ⟨380070, by decide⟩ ⟨13, 2, 0, 380070, 109671, 717, 16384⟩
    (by decide) selected_cut_14736

theorem unmarked_context_12_27417_380071 : frontier 9 ⟨380071, by decide⟩
    (prefixCache 12 27417) (prefixPartial 12 27417) = false := by
  decide +kernel

theorem node_context_12_27417_380071 : EJMOriginalGlobalDAGData.nodes 9 ⟨380071, by decide⟩ =
    .split (coordinate 12) (![⟨380018, by decide⟩,⟨380049, by decide⟩,⟨380065, by decide⟩,⟨380070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27417_380071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27417 ⟨380071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27417
    ⟨380071, by decide⟩ (by decide) (![⟨380018, by decide⟩,⟨380049, by decide⟩,⟨380065, by decide⟩,⟨380070, by decide⟩]) unmarked_context_12_27417_380071 node_context_12_27417_380071
  intro a
  fin_cases a
  · exact context_13_109668_380018
  · exact context_13_109669_380049
  · exact context_13_109670_380065
  · exact context_13_109671_380070

theorem selected_cut_14737 : selected 8 ⟨380090, by decide⟩
    (prefixPartial 13 109672) = some ⟨13, 2, 0, 380090, 109672, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_109672_380090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109672 ⟨380090, by decide⟩ :=
  accepted_of_selected 13 109672 ⟨380090, by decide⟩ ⟨13, 2, 0, 380090, 109672, 1525, 16384⟩
    (by decide) selected_cut_14737

theorem selected_cut_14738 : selected 8 ⟨380118, by decide⟩
    (prefixPartial 13 109673) = some ⟨13, 2, 0, 380118, 109673, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_109673_380118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109673 ⟨380118, by decide⟩ :=
  accepted_of_selected 13 109673 ⟨380118, by decide⟩ ⟨13, 2, 0, 380118, 109673, 2417, 16384⟩
    (by decide) selected_cut_14738

theorem selected_cut_14739 : selected 8 ⟨380137, by decide⟩
    (prefixPartial 13 109674) = some ⟨13, 2, 0, 380137, 109674, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_109674_380137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109674 ⟨380137, by decide⟩ :=
  accepted_of_selected 13 109674 ⟨380137, by decide⟩ ⟨13, 2, 0, 380137, 109674, 1649, 16384⟩
    (by decide) selected_cut_14739

theorem selected_cut_14740 : selected 8 ⟨380142, by decide⟩
    (prefixPartial 13 109675) = some ⟨13, 2, 0, 380142, 109675, 773, 16384⟩ := by
  decide +kernel

theorem context_13_109675_380142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109675 ⟨380142, by decide⟩ :=
  accepted_of_selected 13 109675 ⟨380142, by decide⟩ ⟨13, 2, 0, 380142, 109675, 773, 16384⟩
    (by decide) selected_cut_14740

theorem unmarked_context_12_27418_380143 : frontier 9 ⟨380143, by decide⟩
    (prefixCache 12 27418) (prefixPartial 12 27418) = false := by
  decide +kernel

theorem node_context_12_27418_380143 : EJMOriginalGlobalDAGData.nodes 9 ⟨380143, by decide⟩ =
    .split (coordinate 12) (![⟨380090, by decide⟩,⟨380118, by decide⟩,⟨380137, by decide⟩,⟨380142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27418_380143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27418 ⟨380143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27418
    ⟨380143, by decide⟩ (by decide) (![⟨380090, by decide⟩,⟨380118, by decide⟩,⟨380137, by decide⟩,⟨380142, by decide⟩]) unmarked_context_12_27418_380143 node_context_12_27418_380143
  intro a
  fin_cases a
  · exact context_13_109672_380090
  · exact context_13_109673_380118
  · exact context_13_109674_380137
  · exact context_13_109675_380142

theorem selected_cut_14741 : selected 8 ⟨380160, by decide⟩
    (prefixPartial 13 109676) = some ⟨13, 2, 0, 380160, 109676, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_109676_380160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109676 ⟨380160, by decide⟩ :=
  accepted_of_selected 13 109676 ⟨380160, by decide⟩ ⟨13, 2, 0, 380160, 109676, 1449, 16384⟩
    (by decide) selected_cut_14741

theorem selected_cut_14742 : selected 8 ⟨380189, by decide⟩
    (prefixPartial 13 109677) = some ⟨13, 2, 0, 380189, 109677, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_109677_380189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109677 ⟨380189, by decide⟩ :=
  accepted_of_selected 13 109677 ⟨380189, by decide⟩ ⟨13, 2, 0, 380189, 109677, 2617, 16384⟩
    (by decide) selected_cut_14742

theorem selected_cut_14743 : selected 8 ⟨380210, by decide⟩
    (prefixPartial 13 109678) = some ⟨13, 2, 0, 380210, 109678, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_109678_380210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109678 ⟨380210, by decide⟩ :=
  accepted_of_selected 13 109678 ⟨380210, by decide⟩ ⟨13, 2, 0, 380210, 109678, 1393, 16384⟩
    (by decide) selected_cut_14743

theorem selected_cut_14744 : selected 8 ⟨380217, by decide⟩
    (prefixPartial 13 109679) = some ⟨13, 2, 0, 380217, 109679, 645, 16384⟩ := by
  decide +kernel

theorem context_13_109679_380217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109679 ⟨380217, by decide⟩ :=
  accepted_of_selected 13 109679 ⟨380217, by decide⟩ ⟨13, 2, 0, 380217, 109679, 645, 16384⟩
    (by decide) selected_cut_14744

theorem unmarked_context_12_27419_380218 : frontier 9 ⟨380218, by decide⟩
    (prefixCache 12 27419) (prefixPartial 12 27419) = false := by
  decide +kernel

theorem node_context_12_27419_380218 : EJMOriginalGlobalDAGData.nodes 9 ⟨380218, by decide⟩ =
    .split (coordinate 12) (![⟨380160, by decide⟩,⟨380189, by decide⟩,⟨380210, by decide⟩,⟨380217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27419_380218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27419 ⟨380218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27419
    ⟨380218, by decide⟩ (by decide) (![⟨380160, by decide⟩,⟨380189, by decide⟩,⟨380210, by decide⟩,⟨380217, by decide⟩]) unmarked_context_12_27419_380218 node_context_12_27419_380218
  intro a
  fin_cases a
  · exact context_13_109676_380160
  · exact context_13_109677_380189
  · exact context_13_109678_380210
  · exact context_13_109679_380217

theorem unmarked_context_11_6854_380219 : frontier 10 ⟨380219, by decide⟩
    (prefixCache 11 6854) (prefixPartial 11 6854) = false := by
  decide +kernel

theorem node_context_11_6854_380219 : EJMOriginalGlobalDAGData.nodes 10 ⟨380219, by decide⟩ =
    .split (coordinate 11) (![⟨379996, by decide⟩,⟨380071, by decide⟩,⟨380143, by decide⟩,⟨380218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6854_380219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6854 ⟨380219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6854
    ⟨380219, by decide⟩ (by decide) (![⟨379996, by decide⟩,⟨380071, by decide⟩,⟨380143, by decide⟩,⟨380218, by decide⟩]) unmarked_context_11_6854_380219 node_context_11_6854_380219
  intro a
  fin_cases a
  · exact context_12_27416_379996
  · exact context_12_27417_380071
  · exact context_12_27418_380143
  · exact context_12_27419_380218

theorem selected_cut_14745 : selected 8 ⟨380234, by decide⟩
    (prefixPartial 13 109680) = some ⟨13, 2, 0, 380234, 109680, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_109680_380234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109680 ⟨380234, by decide⟩ :=
  accepted_of_selected 13 109680 ⟨380234, by decide⟩ ⟨13, 2, 0, 380234, 109680, 1281, 16384⟩
    (by decide) selected_cut_14745

theorem selected_cut_14746 : selected 8 ⟨380263, by decide⟩
    (prefixPartial 13 109681) = some ⟨13, 2, 0, 380263, 109681, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_109681_380263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109681 ⟨380263, by decide⟩ :=
  accepted_of_selected 13 109681 ⟨380263, by decide⟩ ⟨13, 2, 0, 380263, 109681, 2169, 16384⟩
    (by decide) selected_cut_14746

theorem selected_cut_14747 : selected 8 ⟨380280, by decide⟩
    (prefixPartial 13 109682) = some ⟨13, 2, 0, 380280, 109682, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_109682_380280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109682 ⟨380280, by decide⟩ :=
  accepted_of_selected 13 109682 ⟨380280, by decide⟩ ⟨13, 2, 0, 380280, 109682, 1229, 16384⟩
    (by decide) selected_cut_14747

theorem selected_cut_14748 : selected 8 ⟨380283, by decide⟩
    (prefixPartial 13 109683) = some ⟨13, 2, 0, 380283, 109683, 709, 16384⟩ := by
  decide +kernel

theorem context_13_109683_380283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109683 ⟨380283, by decide⟩ :=
  accepted_of_selected 13 109683 ⟨380283, by decide⟩ ⟨13, 2, 0, 380283, 109683, 709, 16384⟩
    (by decide) selected_cut_14748

theorem unmarked_context_12_27420_380284 : frontier 9 ⟨380284, by decide⟩
    (prefixCache 12 27420) (prefixPartial 12 27420) = false := by
  decide +kernel

theorem node_context_12_27420_380284 : EJMOriginalGlobalDAGData.nodes 9 ⟨380284, by decide⟩ =
    .split (coordinate 12) (![⟨380234, by decide⟩,⟨380263, by decide⟩,⟨380280, by decide⟩,⟨380283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27420_380284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27420 ⟨380284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27420
    ⟨380284, by decide⟩ (by decide) (![⟨380234, by decide⟩,⟨380263, by decide⟩,⟨380280, by decide⟩,⟨380283, by decide⟩]) unmarked_context_12_27420_380284 node_context_12_27420_380284
  intro a
  fin_cases a
  · exact context_13_109680_380234
  · exact context_13_109681_380263
  · exact context_13_109682_380280
  · exact context_13_109683_380283

theorem selected_cut_14749 : selected 8 ⟨380304, by decide⟩
    (prefixPartial 13 109684) = some ⟨13, 2, 0, 380304, 109684, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_109684_380304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109684 ⟨380304, by decide⟩ :=
  accepted_of_selected 13 109684 ⟨380304, by decide⟩ ⟨13, 2, 0, 380304, 109684, 1573, 16384⟩
    (by decide) selected_cut_14749

theorem selected_cut_14750 : selected 8 ⟨380334, by decide⟩
    (prefixPartial 13 109685) = some ⟨13, 2, 0, 380334, 109685, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_109685_380334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109685 ⟨380334, by decide⟩ :=
  accepted_of_selected 13 109685 ⟨380334, by decide⟩ ⟨13, 2, 0, 380334, 109685, 1993, 16384⟩
    (by decide) selected_cut_14750

theorem selected_cut_14751 : selected 8 ⟨380350, by decide⟩
    (prefixPartial 13 109686) = some ⟨13, 2, 0, 380350, 109686, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_109686_380350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109686 ⟨380350, by decide⟩ :=
  accepted_of_selected 13 109686 ⟨380350, by decide⟩ ⟨13, 2, 0, 380350, 109686, 1425, 16384⟩
    (by decide) selected_cut_14751

theorem selected_cut_14752 : selected 8 ⟨380355, by decide⟩
    (prefixPartial 13 109687) = some ⟨13, 2, 0, 380355, 109687, 633, 16384⟩ := by
  decide +kernel

theorem context_13_109687_380355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109687 ⟨380355, by decide⟩ :=
  accepted_of_selected 13 109687 ⟨380355, by decide⟩ ⟨13, 2, 0, 380355, 109687, 633, 16384⟩
    (by decide) selected_cut_14752

theorem unmarked_context_12_27421_380356 : frontier 9 ⟨380356, by decide⟩
    (prefixCache 12 27421) (prefixPartial 12 27421) = false := by
  decide +kernel

theorem node_context_12_27421_380356 : EJMOriginalGlobalDAGData.nodes 9 ⟨380356, by decide⟩ =
    .split (coordinate 12) (![⟨380304, by decide⟩,⟨380334, by decide⟩,⟨380350, by decide⟩,⟨380355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27421_380356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27421 ⟨380356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27421
    ⟨380356, by decide⟩ (by decide) (![⟨380304, by decide⟩,⟨380334, by decide⟩,⟨380350, by decide⟩,⟨380355, by decide⟩]) unmarked_context_12_27421_380356 node_context_12_27421_380356
  intro a
  fin_cases a
  · exact context_13_109684_380304
  · exact context_13_109685_380334
  · exact context_13_109686_380350
  · exact context_13_109687_380355

theorem selected_cut_14753 : selected 8 ⟨380382, by decide⟩
    (prefixPartial 13 109688) = some ⟨13, 2, 0, 380382, 109688, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_109688_380382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109688 ⟨380382, by decide⟩ :=
  accepted_of_selected 13 109688 ⟨380382, by decide⟩ ⟨13, 2, 0, 380382, 109688, 1581, 16384⟩
    (by decide) selected_cut_14753

theorem selected_cut_14754 : selected 8 ⟨380419, by decide⟩
    (prefixPartial 13 109689) = some ⟨13, 2, 0, 380419, 109689, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_109689_380419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109689 ⟨380419, by decide⟩ :=
  accepted_of_selected 13 109689 ⟨380419, by decide⟩ ⟨13, 2, 0, 380419, 109689, 2421, 16384⟩
    (by decide) selected_cut_14754

theorem selected_cut_14755 : selected 8 ⟨380438, by decide⟩
    (prefixPartial 13 109690) = some ⟨13, 2, 0, 380438, 109690, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_109690_380438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109690 ⟨380438, by decide⟩ :=
  accepted_of_selected 13 109690 ⟨380438, by decide⟩ ⟨13, 2, 0, 380438, 109690, 1453, 16384⟩
    (by decide) selected_cut_14755

theorem selected_cut_14756 : selected 8 ⟨380443, by decide⟩
    (prefixPartial 13 109691) = some ⟨13, 2, 0, 380443, 109691, 685, 16384⟩ := by
  decide +kernel

theorem context_13_109691_380443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109691 ⟨380443, by decide⟩ :=
  accepted_of_selected 13 109691 ⟨380443, by decide⟩ ⟨13, 2, 0, 380443, 109691, 685, 16384⟩
    (by decide) selected_cut_14756

theorem unmarked_context_12_27422_380444 : frontier 9 ⟨380444, by decide⟩
    (prefixCache 12 27422) (prefixPartial 12 27422) = false := by
  decide +kernel

theorem node_context_12_27422_380444 : EJMOriginalGlobalDAGData.nodes 9 ⟨380444, by decide⟩ =
    .split (coordinate 12) (![⟨380382, by decide⟩,⟨380419, by decide⟩,⟨380438, by decide⟩,⟨380443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27422_380444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27422 ⟨380444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27422
    ⟨380444, by decide⟩ (by decide) (![⟨380382, by decide⟩,⟨380419, by decide⟩,⟨380438, by decide⟩,⟨380443, by decide⟩]) unmarked_context_12_27422_380444 node_context_12_27422_380444
  intro a
  fin_cases a
  · exact context_13_109688_380382
  · exact context_13_109689_380419
  · exact context_13_109690_380438
  · exact context_13_109691_380443

theorem selected_cut_14757 : selected 8 ⟨380494, by decide⟩
    (prefixPartial 13 109692) = some ⟨13, 2, 0, 380494, 109692, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_109692_380494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109692 ⟨380494, by decide⟩ :=
  accepted_of_selected 13 109692 ⟨380494, by decide⟩ ⟨13, 2, 0, 380494, 109692, 2501, 16384⟩
    (by decide) selected_cut_14757

theorem selected_cut_14758 : selected 8 ⟨380600, by decide⟩
    (prefixPartial 13 109693) = some ⟨13, 2, 0, 380600, 109693, 4025, 16384⟩ := by
  decide +kernel

theorem context_13_109693_380600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109693 ⟨380600, by decide⟩ :=
  accepted_of_selected 13 109693 ⟨380600, by decide⟩ ⟨13, 2, 0, 380600, 109693, 4025, 16384⟩
    (by decide) selected_cut_14758

theorem selected_cut_14759 : selected 8 ⟨380627, by decide⟩
    (prefixPartial 13 109694) = some ⟨13, 2, 0, 380627, 109694, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_109694_380627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109694 ⟨380627, by decide⟩ :=
  accepted_of_selected 13 109694 ⟨380627, by decide⟩ ⟨13, 2, 0, 380627, 109694, 2253, 16384⟩
    (by decide) selected_cut_14759

theorem selected_cut_14760 : selected 8 ⟨380638, by decide⟩
    (prefixPartial 13 109695) = some ⟨13, 2, 0, 380638, 109695, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_109695_380638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109695 ⟨380638, by decide⟩ :=
  accepted_of_selected 13 109695 ⟨380638, by decide⟩ ⟨13, 2, 0, 380638, 109695, 1041, 16384⟩
    (by decide) selected_cut_14760

theorem unmarked_context_12_27423_380639 : frontier 9 ⟨380639, by decide⟩
    (prefixCache 12 27423) (prefixPartial 12 27423) = false := by
  decide +kernel

theorem node_context_12_27423_380639 : EJMOriginalGlobalDAGData.nodes 9 ⟨380639, by decide⟩ =
    .split (coordinate 12) (![⟨380494, by decide⟩,⟨380600, by decide⟩,⟨380627, by decide⟩,⟨380638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27423_380639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27423 ⟨380639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27423
    ⟨380639, by decide⟩ (by decide) (![⟨380494, by decide⟩,⟨380600, by decide⟩,⟨380627, by decide⟩,⟨380638, by decide⟩]) unmarked_context_12_27423_380639 node_context_12_27423_380639
  intro a
  fin_cases a
  · exact context_13_109692_380494
  · exact context_13_109693_380600
  · exact context_13_109694_380627
  · exact context_13_109695_380638

theorem unmarked_context_11_6855_380640 : frontier 10 ⟨380640, by decide⟩
    (prefixCache 11 6855) (prefixPartial 11 6855) = false := by
  decide +kernel

theorem node_context_11_6855_380640 : EJMOriginalGlobalDAGData.nodes 10 ⟨380640, by decide⟩ =
    .split (coordinate 11) (![⟨380284, by decide⟩,⟨380356, by decide⟩,⟨380444, by decide⟩,⟨380639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6855_380640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6855 ⟨380640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6855
    ⟨380640, by decide⟩ (by decide) (![⟨380284, by decide⟩,⟨380356, by decide⟩,⟨380444, by decide⟩,⟨380639, by decide⟩]) unmarked_context_11_6855_380640 node_context_11_6855_380640
  intro a
  fin_cases a
  · exact context_12_27420_380284
  · exact context_12_27421_380356
  · exact context_12_27422_380444
  · exact context_12_27423_380639

theorem unmarked_context_10_1713_380641 : frontier 11 ⟨380641, by decide⟩
    (prefixCache 10 1713) (prefixPartial 10 1713) = false := by
  decide +kernel

theorem node_context_10_1713_380641 : EJMOriginalGlobalDAGData.nodes 11 ⟨380641, by decide⟩ =
    .split (coordinate 10) (![⟨379599, by decide⟩,⟨379922, by decide⟩,⟨380219, by decide⟩,⟨380640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1713_380641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1713 ⟨380641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1713
    ⟨380641, by decide⟩ (by decide) (![⟨379599, by decide⟩,⟨379922, by decide⟩,⟨380219, by decide⟩,⟨380640, by decide⟩]) unmarked_context_10_1713_380641 node_context_10_1713_380641
  intro a
  fin_cases a
  · exact context_11_6852_379599
  · exact context_11_6853_379922
  · exact context_11_6854_380219
  · exact context_11_6855_380640

theorem selected_cut_14761 : selected 8 ⟨380654, by decide⟩
    (prefixPartial 13 109696) = some ⟨13, 2, 0, 380654, 109696, 969, 16384⟩ := by
  decide +kernel

theorem context_13_109696_380654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109696 ⟨380654, by decide⟩ :=
  accepted_of_selected 13 109696 ⟨380654, by decide⟩ ⟨13, 2, 0, 380654, 109696, 969, 16384⟩
    (by decide) selected_cut_14761

theorem selected_cut_14762 : selected 8 ⟨380675, by decide⟩
    (prefixPartial 13 109697) = some ⟨13, 2, 0, 380675, 109697, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_109697_380675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109697 ⟨380675, by decide⟩ :=
  accepted_of_selected 13 109697 ⟨380675, by decide⟩ ⟨13, 2, 0, 380675, 109697, 2045, 16384⟩
    (by decide) selected_cut_14762

theorem selected_cut_14763 : selected 8 ⟨380692, by decide⟩
    (prefixPartial 13 109698) = some ⟨13, 2, 0, 380692, 109698, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_109698_380692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109698 ⟨380692, by decide⟩ :=
  accepted_of_selected 13 109698 ⟨380692, by decide⟩ ⟨13, 2, 0, 380692, 109698, 1037, 16384⟩
    (by decide) selected_cut_14763

theorem selected_cut_14764 : selected 8 ⟨380696, by decide⟩
    (prefixPartial 13 109699) = some ⟨13, 2, 0, 380696, 109699, 785, 16384⟩ := by
  decide +kernel

theorem context_13_109699_380696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109699 ⟨380696, by decide⟩ :=
  accepted_of_selected 13 109699 ⟨380696, by decide⟩ ⟨13, 2, 0, 380696, 109699, 785, 16384⟩
    (by decide) selected_cut_14764

theorem unmarked_context_12_27424_380697 : frontier 9 ⟨380697, by decide⟩
    (prefixCache 12 27424) (prefixPartial 12 27424) = false := by
  decide +kernel

theorem node_context_12_27424_380697 : EJMOriginalGlobalDAGData.nodes 9 ⟨380697, by decide⟩ =
    .split (coordinate 12) (![⟨380654, by decide⟩,⟨380675, by decide⟩,⟨380692, by decide⟩,⟨380696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27424_380697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27424 ⟨380697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27424
    ⟨380697, by decide⟩ (by decide) (![⟨380654, by decide⟩,⟨380675, by decide⟩,⟨380692, by decide⟩,⟨380696, by decide⟩]) unmarked_context_12_27424_380697 node_context_12_27424_380697
  intro a
  fin_cases a
  · exact context_13_109696_380654
  · exact context_13_109697_380675
  · exact context_13_109698_380692
  · exact context_13_109699_380696

theorem selected_cut_14765 : selected 8 ⟨380715, by decide⟩
    (prefixPartial 13 109700) = some ⟨13, 2, 0, 380715, 109700, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_109700_380715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109700 ⟨380715, by decide⟩ :=
  accepted_of_selected 13 109700 ⟨380715, by decide⟩ ⟨13, 2, 0, 380715, 109700, 1217, 16384⟩
    (by decide) selected_cut_14765

theorem selected_cut_14766 : selected 8 ⟨380753, by decide⟩
    (prefixPartial 13 109701) = some ⟨13, 2, 0, 380753, 109701, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_109701_380753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109701 ⟨380753, by decide⟩ :=
  accepted_of_selected 13 109701 ⟨380753, by decide⟩ ⟨13, 2, 0, 380753, 109701, 2093, 16384⟩
    (by decide) selected_cut_14766

theorem selected_cut_14767 : selected 8 ⟨380769, by decide⟩
    (prefixPartial 13 109702) = some ⟨13, 2, 0, 380769, 109702, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_109702_380769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109702 ⟨380769, by decide⟩ :=
  accepted_of_selected 13 109702 ⟨380769, by decide⟩ ⟨13, 2, 0, 380769, 109702, 1161, 16384⟩
    (by decide) selected_cut_14767

theorem selected_cut_14768 : selected 8 ⟨380774, by decide⟩
    (prefixPartial 13 109703) = some ⟨13, 2, 0, 380774, 109703, 629, 16384⟩ := by
  decide +kernel

theorem context_13_109703_380774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109703 ⟨380774, by decide⟩ :=
  accepted_of_selected 13 109703 ⟨380774, by decide⟩ ⟨13, 2, 0, 380774, 109703, 629, 16384⟩
    (by decide) selected_cut_14768

theorem unmarked_context_12_27425_380775 : frontier 9 ⟨380775, by decide⟩
    (prefixCache 12 27425) (prefixPartial 12 27425) = false := by
  decide +kernel

theorem node_context_12_27425_380775 : EJMOriginalGlobalDAGData.nodes 9 ⟨380775, by decide⟩ =
    .split (coordinate 12) (![⟨380715, by decide⟩,⟨380753, by decide⟩,⟨380769, by decide⟩,⟨380774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27425_380775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27425 ⟨380775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27425
    ⟨380775, by decide⟩ (by decide) (![⟨380715, by decide⟩,⟨380753, by decide⟩,⟨380769, by decide⟩,⟨380774, by decide⟩]) unmarked_context_12_27425_380775 node_context_12_27425_380775
  intro a
  fin_cases a
  · exact context_13_109700_380715
  · exact context_13_109701_380753
  · exact context_13_109702_380769
  · exact context_13_109703_380774

theorem selected_cut_14769 : selected 8 ⟨380790, by decide⟩
    (prefixPartial 13 109704) = some ⟨13, 2, 0, 380790, 109704, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_109704_380790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109704 ⟨380790, by decide⟩ :=
  accepted_of_selected 13 109704 ⟨380790, by decide⟩ ⟨13, 2, 0, 380790, 109704, 1157, 16384⟩
    (by decide) selected_cut_14769

theorem selected_cut_14770 : selected 8 ⟨380821, by decide⟩
    (prefixPartial 13 109705) = some ⟨13, 2, 0, 380821, 109705, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_109705_380821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109705 ⟨380821, by decide⟩ :=
  accepted_of_selected 13 109705 ⟨380821, by decide⟩ ⟨13, 2, 0, 380821, 109705, 2145, 16384⟩
    (by decide) selected_cut_14770

theorem selected_cut_14771 : selected 8 ⟨380836, by decide⟩
    (prefixPartial 13 109706) = some ⟨13, 2, 0, 380836, 109706, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_109706_380836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109706 ⟨380836, by decide⟩ :=
  accepted_of_selected 13 109706 ⟨380836, by decide⟩ ⟨13, 2, 0, 380836, 109706, 1129, 16384⟩
    (by decide) selected_cut_14771

theorem selected_cut_14772 : selected 8 ⟨380841, by decide⟩
    (prefixPartial 13 109707) = some ⟨13, 2, 0, 380841, 109707, 677, 16384⟩ := by
  decide +kernel

theorem context_13_109707_380841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109707 ⟨380841, by decide⟩ :=
  accepted_of_selected 13 109707 ⟨380841, by decide⟩ ⟨13, 2, 0, 380841, 109707, 677, 16384⟩
    (by decide) selected_cut_14772

theorem unmarked_context_12_27426_380842 : frontier 9 ⟨380842, by decide⟩
    (prefixCache 12 27426) (prefixPartial 12 27426) = false := by
  decide +kernel

theorem node_context_12_27426_380842 : EJMOriginalGlobalDAGData.nodes 9 ⟨380842, by decide⟩ =
    .split (coordinate 12) (![⟨380790, by decide⟩,⟨380821, by decide⟩,⟨380836, by decide⟩,⟨380841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27426_380842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27426 ⟨380842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27426
    ⟨380842, by decide⟩ (by decide) (![⟨380790, by decide⟩,⟨380821, by decide⟩,⟨380836, by decide⟩,⟨380841, by decide⟩]) unmarked_context_12_27426_380842 node_context_12_27426_380842
  intro a
  fin_cases a
  · exact context_13_109704_380790
  · exact context_13_109705_380821
  · exact context_13_109706_380836
  · exact context_13_109707_380841

theorem selected_cut_14773 : selected 8 ⟨380853, by decide⟩
    (prefixPartial 13 109708) = some ⟨13, 2, 0, 380853, 109708, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_109708_380853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109708 ⟨380853, by decide⟩ :=
  accepted_of_selected 13 109708 ⟨380853, by decide⟩ ⟨13, 2, 0, 380853, 109708, 1085, 16384⟩
    (by decide) selected_cut_14773

theorem selected_cut_14774 : selected 8 ⟨380885, by decide⟩
    (prefixPartial 13 109709) = some ⟨13, 2, 0, 380885, 109709, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_109709_380885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109709 ⟨380885, by decide⟩ :=
  accepted_of_selected 13 109709 ⟨380885, by decide⟩ ⟨13, 2, 0, 380885, 109709, 2249, 16384⟩
    (by decide) selected_cut_14774

theorem selected_cut_14775 : selected 8 ⟨380900, by decide⟩
    (prefixPartial 13 109710) = some ⟨13, 2, 0, 380900, 109710, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_109710_380900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109710 ⟨380900, by decide⟩ :=
  accepted_of_selected 13 109710 ⟨380900, by decide⟩ ⟨13, 2, 0, 380900, 109710, 1057, 16384⟩
    (by decide) selected_cut_14775

theorem selected_cut_14776 : selected 8 ⟨380907, by decide⟩
    (prefixPartial 13 109711) = some ⟨13, 2, 0, 380907, 109711, 645, 16384⟩ := by
  decide +kernel

theorem context_13_109711_380907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109711 ⟨380907, by decide⟩ :=
  accepted_of_selected 13 109711 ⟨380907, by decide⟩ ⟨13, 2, 0, 380907, 109711, 645, 16384⟩
    (by decide) selected_cut_14776

theorem unmarked_context_12_27427_380908 : frontier 9 ⟨380908, by decide⟩
    (prefixCache 12 27427) (prefixPartial 12 27427) = false := by
  decide +kernel

theorem node_context_12_27427_380908 : EJMOriginalGlobalDAGData.nodes 9 ⟨380908, by decide⟩ =
    .split (coordinate 12) (![⟨380853, by decide⟩,⟨380885, by decide⟩,⟨380900, by decide⟩,⟨380907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27427_380908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27427 ⟨380908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27427
    ⟨380908, by decide⟩ (by decide) (![⟨380853, by decide⟩,⟨380885, by decide⟩,⟨380900, by decide⟩,⟨380907, by decide⟩]) unmarked_context_12_27427_380908 node_context_12_27427_380908
  intro a
  fin_cases a
  · exact context_13_109708_380853
  · exact context_13_109709_380885
  · exact context_13_109710_380900
  · exact context_13_109711_380907

theorem unmarked_context_11_6856_380909 : frontier 10 ⟨380909, by decide⟩
    (prefixCache 11 6856) (prefixPartial 11 6856) = false := by
  decide +kernel

theorem node_context_11_6856_380909 : EJMOriginalGlobalDAGData.nodes 10 ⟨380909, by decide⟩ =
    .split (coordinate 11) (![⟨380697, by decide⟩,⟨380775, by decide⟩,⟨380842, by decide⟩,⟨380908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6856_380909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6856 ⟨380909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6856
    ⟨380909, by decide⟩ (by decide) (![⟨380697, by decide⟩,⟨380775, by decide⟩,⟨380842, by decide⟩,⟨380908, by decide⟩]) unmarked_context_11_6856_380909 node_context_11_6856_380909
  intro a
  fin_cases a
  · exact context_12_27424_380697
  · exact context_12_27425_380775
  · exact context_12_27426_380842
  · exact context_12_27427_380908

theorem selected_cut_14777 : selected 8 ⟨380921, by decide⟩
    (prefixPartial 13 109712) = some ⟨13, 2, 0, 380921, 109712, 841, 16384⟩ := by
  decide +kernel

theorem context_13_109712_380921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109712 ⟨380921, by decide⟩ :=
  accepted_of_selected 13 109712 ⟨380921, by decide⟩ ⟨13, 2, 0, 380921, 109712, 841, 16384⟩
    (by decide) selected_cut_14777

theorem selected_cut_14778 : selected 8 ⟨380948, by decide⟩
    (prefixPartial 13 109713) = some ⟨13, 2, 0, 380948, 109713, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_109713_380948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109713 ⟨380948, by decide⟩ :=
  accepted_of_selected 13 109713 ⟨380948, by decide⟩ ⟨13, 2, 0, 380948, 109713, 2365, 16384⟩
    (by decide) selected_cut_14778

theorem selected_cut_14779 : selected 8 ⟨380967, by decide⟩
    (prefixPartial 13 109714) = some ⟨13, 2, 0, 380967, 109714, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_109714_380967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109714 ⟨380967, by decide⟩ :=
  accepted_of_selected 13 109714 ⟨380967, by decide⟩ ⟨13, 2, 0, 380967, 109714, 1357, 16384⟩
    (by decide) selected_cut_14779

theorem selected_cut_14780 : selected 8 ⟨380971, by decide⟩
    (prefixPartial 13 109715) = some ⟨13, 2, 0, 380971, 109715, 861, 16384⟩ := by
  decide +kernel

theorem context_13_109715_380971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109715 ⟨380971, by decide⟩ :=
  accepted_of_selected 13 109715 ⟨380971, by decide⟩ ⟨13, 2, 0, 380971, 109715, 861, 16384⟩
    (by decide) selected_cut_14780

theorem unmarked_context_12_27428_380972 : frontier 9 ⟨380972, by decide⟩
    (prefixCache 12 27428) (prefixPartial 12 27428) = false := by
  decide +kernel

theorem node_context_12_27428_380972 : EJMOriginalGlobalDAGData.nodes 9 ⟨380972, by decide⟩ =
    .split (coordinate 12) (![⟨380921, by decide⟩,⟨380948, by decide⟩,⟨380967, by decide⟩,⟨380971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27428_380972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27428 ⟨380972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27428
    ⟨380972, by decide⟩ (by decide) (![⟨380921, by decide⟩,⟨380948, by decide⟩,⟨380967, by decide⟩,⟨380971, by decide⟩]) unmarked_context_12_27428_380972 node_context_12_27428_380972
  intro a
  fin_cases a
  · exact context_13_109712_380921
  · exact context_13_109713_380948
  · exact context_13_109714_380967
  · exact context_13_109715_380971

theorem selected_cut_14781 : selected 8 ⟨380984, by decide⟩
    (prefixPartial 13 109716) = some ⟨13, 2, 0, 380984, 109716, 857, 16384⟩ := by
  decide +kernel

theorem context_13_109716_380984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109716 ⟨380984, by decide⟩ :=
  accepted_of_selected 13 109716 ⟨380984, by decide⟩ ⟨13, 2, 0, 380984, 109716, 857, 16384⟩
    (by decide) selected_cut_14781

theorem selected_cut_14782 : selected 8 ⟨381008, by decide⟩
    (prefixPartial 13 109717) = some ⟨13, 2, 0, 381008, 109717, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_109717_381008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109717 ⟨381008, by decide⟩ :=
  accepted_of_selected 13 109717 ⟨381008, by decide⟩ ⟨13, 2, 0, 381008, 109717, 1933, 16384⟩
    (by decide) selected_cut_14782

theorem selected_cut_14783 : selected 8 ⟨381025, by decide⟩
    (prefixPartial 13 109718) = some ⟨13, 2, 0, 381025, 109718, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_109718_381025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109718 ⟨381025, by decide⟩ :=
  accepted_of_selected 13 109718 ⟨381025, by decide⟩ ⟨13, 2, 0, 381025, 109718, 1405, 16384⟩
    (by decide) selected_cut_14783

theorem selected_cut_14784 : selected 8 ⟨381030, by decide⟩
    (prefixPartial 13 109719) = some ⟨13, 2, 0, 381030, 109719, 781, 16384⟩ := by
  decide +kernel

theorem context_13_109719_381030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109719 ⟨381030, by decide⟩ :=
  accepted_of_selected 13 109719 ⟨381030, by decide⟩ ⟨13, 2, 0, 381030, 109719, 781, 16384⟩
    (by decide) selected_cut_14784

theorem unmarked_context_12_27429_381031 : frontier 9 ⟨381031, by decide⟩
    (prefixCache 12 27429) (prefixPartial 12 27429) = false := by
  decide +kernel

theorem node_context_12_27429_381031 : EJMOriginalGlobalDAGData.nodes 9 ⟨381031, by decide⟩ =
    .split (coordinate 12) (![⟨380984, by decide⟩,⟨381008, by decide⟩,⟨381025, by decide⟩,⟨381030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27429_381031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27429 ⟨381031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27429
    ⟨381031, by decide⟩ (by decide) (![⟨380984, by decide⟩,⟨381008, by decide⟩,⟨381025, by decide⟩,⟨381030, by decide⟩]) unmarked_context_12_27429_381031 node_context_12_27429_381031
  intro a
  fin_cases a
  · exact context_13_109716_380984
  · exact context_13_109717_381008
  · exact context_13_109718_381025
  · exact context_13_109719_381030

theorem selected_cut_14785 : selected 8 ⟨381041, by decide⟩
    (prefixPartial 13 109720) = some ⟨13, 2, 0, 381041, 109720, 861, 16384⟩ := by
  decide +kernel

theorem context_13_109720_381041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109720 ⟨381041, by decide⟩ :=
  accepted_of_selected 13 109720 ⟨381041, by decide⟩ ⟨13, 2, 0, 381041, 109720, 861, 16384⟩
    (by decide) selected_cut_14785

theorem selected_cut_14786 : selected 8 ⟨381066, by decide⟩
    (prefixPartial 13 109721) = some ⟨13, 2, 0, 381066, 109721, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_109721_381066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109721 ⟨381066, by decide⟩ :=
  accepted_of_selected 13 109721 ⟨381066, by decide⟩ ⟨13, 2, 0, 381066, 109721, 2161, 16384⟩
    (by decide) selected_cut_14786

theorem selected_cut_14787 : selected 8 ⟨381082, by decide⟩
    (prefixPartial 13 109722) = some ⟨13, 2, 0, 381082, 109722, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_109722_381082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109722 ⟨381082, by decide⟩ :=
  accepted_of_selected 13 109722 ⟨381082, by decide⟩ ⟨13, 2, 0, 381082, 109722, 1369, 16384⟩
    (by decide) selected_cut_14787

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
