/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover314
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30245 : selected 9 ⟨763295, by decide⟩
    (prefixPartial 12 94139) = some ⟨12, 2, 0, 763295, 94139, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_94139_763295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94139 ⟨763295, by decide⟩ :=
  accepted_of_selected 12 94139 ⟨763295, by decide⟩ ⟨12, 2, 0, 763295, 94139, 1049, 65536⟩
    (by decide) selected_cut_30245

theorem unmarked_context_11_23534_763296 : frontier 10 ⟨763296, by decide⟩
    (prefixCache 11 23534) (prefixPartial 11 23534) = false := by
  decide +kernel

theorem node_context_11_23534_763296 : EJMOriginalGlobalDAGData.nodes 10 ⟨763296, by decide⟩ =
    .split (coordinate 11) (![⟨763263, by decide⟩,⟨763273, by decide⟩,⟨763285, by decide⟩,⟨763295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23534_763296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23534 ⟨763296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23534
    ⟨763296, by decide⟩ (by decide) (![⟨763263, by decide⟩,⟨763273, by decide⟩,⟨763285, by decide⟩,⟨763295, by decide⟩]) unmarked_context_11_23534_763296 node_context_11_23534_763296
  intro a
  fin_cases a
  · exact context_12_94136_763263
  · exact context_12_94137_763273
  · exact context_12_94138_763285
  · exact context_12_94139_763295

theorem selected_cut_30246 : selected 10 ⟨762110, by decide⟩
    (prefixPartial 11 23535) = some ⟨11, 2, 0, 762110, 23535, 5, 262144⟩ := by
  decide +kernel

theorem context_11_23535_762110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23535 ⟨762110, by decide⟩ :=
  accepted_of_selected 11 23535 ⟨762110, by decide⟩ ⟨11, 2, 0, 762110, 23535, 5, 262144⟩
    (by decide) selected_cut_30246

theorem unmarked_context_10_5883_763297 : frontier 11 ⟨763297, by decide⟩
    (prefixCache 10 5883) (prefixPartial 10 5883) = false := by
  decide +kernel

theorem node_context_10_5883_763297 : EJMOriginalGlobalDAGData.nodes 11 ⟨763297, by decide⟩ =
    .split (coordinate 10) (![⟨763200, by decide⟩,⟨763254, by decide⟩,⟨763296, by decide⟩,⟨762110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5883_763297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5883 ⟨763297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5883
    ⟨763297, by decide⟩ (by decide) (![⟨763200, by decide⟩,⟨763254, by decide⟩,⟨763296, by decide⟩,⟨762110, by decide⟩]) unmarked_context_10_5883_763297 node_context_10_5883_763297
  intro a
  fin_cases a
  · exact context_11_23532_763200
  · exact context_11_23533_763254
  · exact context_11_23534_763296
  · exact context_11_23535_762110

theorem unmarked_context_9_1470_763298 : frontier 12 ⟨763298, by decide⟩
    (prefixCache 9 1470) (prefixPartial 9 1470) = false := by
  decide +kernel

theorem node_context_9_1470_763298 : EJMOriginalGlobalDAGData.nodes 12 ⟨763298, by decide⟩ =
    .split (coordinate 9) (![⟨762529, by decide⟩,⟨762891, by decide⟩,⟨763135, by decide⟩,⟨763297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1470_763298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1470 ⟨763298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1470
    ⟨763298, by decide⟩ (by decide) (![⟨762529, by decide⟩,⟨762891, by decide⟩,⟨763135, by decide⟩,⟨763297, by decide⟩]) unmarked_context_9_1470_763298 node_context_9_1470_763298
  intro a
  fin_cases a
  · exact context_10_5880_762529
  · exact context_10_5881_762891
  · exact context_10_5882_763135
  · exact context_10_5883_763297

theorem selected_cut_30247 : selected 10 ⟨763324, by decide⟩
    (prefixPartial 11 23536) = some ⟨11, 2, 0, 763324, 23536, 2145, 262144⟩ := by
  decide +kernel

theorem context_11_23536_763324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23536 ⟨763324, by decide⟩ :=
  accepted_of_selected 11 23536 ⟨763324, by decide⟩ ⟨11, 2, 0, 763324, 23536, 2145, 262144⟩
    (by decide) selected_cut_30247

theorem selected_cut_30248 : selected 10 ⟨763350, by decide⟩
    (prefixPartial 11 23537) = some ⟨11, 2, 0, 763350, 23537, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_23537_763350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23537 ⟨763350, by decide⟩ :=
  accepted_of_selected 11 23537 ⟨763350, by decide⟩ ⟨11, 2, 0, 763350, 23537, 2117, 262144⟩
    (by decide) selected_cut_30248

theorem selected_cut_30249 : selected 10 ⟨763374, by decide⟩
    (prefixPartial 11 23538) = some ⟨11, 2, 0, 763374, 23538, 2373, 262144⟩ := by
  decide +kernel

theorem context_11_23538_763374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23538 ⟨763374, by decide⟩ :=
  accepted_of_selected 11 23538 ⟨763374, by decide⟩ ⟨11, 2, 0, 763374, 23538, 2373, 262144⟩
    (by decide) selected_cut_30249

theorem selected_cut_30250 : selected 10 ⟨763397, by decide⟩
    (prefixPartial 11 23539) = some ⟨11, 2, 0, 763397, 23539, 1329, 262144⟩ := by
  decide +kernel

theorem context_11_23539_763397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23539 ⟨763397, by decide⟩ :=
  accepted_of_selected 11 23539 ⟨763397, by decide⟩ ⟨11, 2, 0, 763397, 23539, 1329, 262144⟩
    (by decide) selected_cut_30250

theorem unmarked_context_10_5884_763398 : frontier 11 ⟨763398, by decide⟩
    (prefixCache 10 5884) (prefixPartial 10 5884) = false := by
  decide +kernel

theorem node_context_10_5884_763398 : EJMOriginalGlobalDAGData.nodes 11 ⟨763398, by decide⟩ =
    .split (coordinate 10) (![⟨763324, by decide⟩,⟨763350, by decide⟩,⟨763374, by decide⟩,⟨763397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5884_763398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5884 ⟨763398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5884
    ⟨763398, by decide⟩ (by decide) (![⟨763324, by decide⟩,⟨763350, by decide⟩,⟨763374, by decide⟩,⟨763397, by decide⟩]) unmarked_context_10_5884_763398 node_context_10_5884_763398
  intro a
  fin_cases a
  · exact context_11_23536_763324
  · exact context_11_23537_763350
  · exact context_11_23538_763374
  · exact context_11_23539_763397

theorem selected_cut_30251 : selected 10 ⟨763423, by decide⟩
    (prefixPartial 11 23540) = some ⟨11, 2, 0, 763423, 23540, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_23540_763423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23540 ⟨763423, by decide⟩ :=
  accepted_of_selected 11 23540 ⟨763423, by decide⟩ ⟨11, 2, 0, 763423, 23540, 2061, 262144⟩
    (by decide) selected_cut_30251

theorem selected_cut_30252 : selected 10 ⟨763452, by decide⟩
    (prefixPartial 11 23541) = some ⟨11, 2, 0, 763452, 23541, 2013, 262144⟩ := by
  decide +kernel

theorem context_11_23541_763452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23541 ⟨763452, by decide⟩ :=
  accepted_of_selected 11 23541 ⟨763452, by decide⟩ ⟨11, 2, 0, 763452, 23541, 2013, 262144⟩
    (by decide) selected_cut_30252

theorem selected_cut_30253 : selected 10 ⟨763474, by decide⟩
    (prefixPartial 11 23542) = some ⟨11, 2, 0, 763474, 23542, 1737, 262144⟩ := by
  decide +kernel

theorem context_11_23542_763474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23542 ⟨763474, by decide⟩ :=
  accepted_of_selected 11 23542 ⟨763474, by decide⟩ ⟨11, 2, 0, 763474, 23542, 1737, 262144⟩
    (by decide) selected_cut_30253

theorem selected_cut_30254 : selected 10 ⟨763492, by decide⟩
    (prefixPartial 11 23543) = some ⟨11, 2, 0, 763492, 23543, 1049, 262144⟩ := by
  decide +kernel

theorem context_11_23543_763492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23543 ⟨763492, by decide⟩ :=
  accepted_of_selected 11 23543 ⟨763492, by decide⟩ ⟨11, 2, 0, 763492, 23543, 1049, 262144⟩
    (by decide) selected_cut_30254

theorem unmarked_context_10_5885_763493 : frontier 11 ⟨763493, by decide⟩
    (prefixCache 10 5885) (prefixPartial 10 5885) = false := by
  decide +kernel

theorem node_context_10_5885_763493 : EJMOriginalGlobalDAGData.nodes 11 ⟨763493, by decide⟩ =
    .split (coordinate 10) (![⟨763423, by decide⟩,⟨763452, by decide⟩,⟨763474, by decide⟩,⟨763492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5885_763493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5885 ⟨763493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5885
    ⟨763493, by decide⟩ (by decide) (![⟨763423, by decide⟩,⟨763452, by decide⟩,⟨763474, by decide⟩,⟨763492, by decide⟩]) unmarked_context_10_5885_763493 node_context_10_5885_763493
  intro a
  fin_cases a
  · exact context_11_23540_763423
  · exact context_11_23541_763452
  · exact context_11_23542_763474
  · exact context_11_23543_763492

theorem selected_cut_30255 : selected 11 ⟨763555, by decide⟩
    (prefixPartial 10 5886) = some ⟨10, 2, 0, 763555, 5886, 3745, 1048576⟩ := by
  decide +kernel

theorem context_10_5886_763555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5886 ⟨763555, by decide⟩ :=
  accepted_of_selected 10 5886 ⟨763555, by decide⟩ ⟨10, 2, 0, 763555, 5886, 3745, 1048576⟩
    (by decide) selected_cut_30255

theorem selected_cut_30256 : selected 11 ⟨763584, by decide⟩
    (prefixPartial 10 5887) = some ⟨10, 2, 0, 763584, 5887, 1045, 1048576⟩ := by
  decide +kernel

theorem context_10_5887_763584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5887 ⟨763584, by decide⟩ :=
  accepted_of_selected 10 5887 ⟨763584, by decide⟩ ⟨10, 2, 0, 763584, 5887, 1045, 1048576⟩
    (by decide) selected_cut_30256

theorem unmarked_context_9_1471_763585 : frontier 12 ⟨763585, by decide⟩
    (prefixCache 9 1471) (prefixPartial 9 1471) = false := by
  decide +kernel

theorem node_context_9_1471_763585 : EJMOriginalGlobalDAGData.nodes 12 ⟨763585, by decide⟩ =
    .split (coordinate 9) (![⟨763398, by decide⟩,⟨763493, by decide⟩,⟨763555, by decide⟩,⟨763584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1471_763585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1471 ⟨763585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1471
    ⟨763585, by decide⟩ (by decide) (![⟨763398, by decide⟩,⟨763493, by decide⟩,⟨763555, by decide⟩,⟨763584, by decide⟩]) unmarked_context_9_1471_763585 node_context_9_1471_763585
  intro a
  fin_cases a
  · exact context_10_5884_763398
  · exact context_10_5885_763493
  · exact context_10_5886_763555
  · exact context_10_5887_763584

theorem unmarked_context_8_367_763586 : frontier 13 ⟨763586, by decide⟩
    (prefixCache 8 367) (prefixPartial 8 367) = false := by
  decide +kernel

theorem node_context_8_367_763586 : EJMOriginalGlobalDAGData.nodes 13 ⟨763586, by decide⟩ =
    .split (coordinate 8) (![⟨759811, by decide⟩,⟨762112, by decide⟩,⟨763298, by decide⟩,⟨763585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_367_763586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 367 ⟨763586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 367
    ⟨763586, by decide⟩ (by decide) (![⟨759811, by decide⟩,⟨762112, by decide⟩,⟨763298, by decide⟩,⟨763585, by decide⟩]) unmarked_context_8_367_763586 node_context_8_367_763586
  intro a
  fin_cases a
  · exact context_9_1468_759811
  · exact context_9_1469_762112
  · exact context_9_1470_763298
  · exact context_9_1471_763585

theorem unmarked_context_7_91_763587 : frontier 14 ⟨763587, by decide⟩
    (prefixCache 7 91) (prefixPartial 7 91) = false := by
  decide +kernel

theorem node_context_7_91_763587 : EJMOriginalGlobalDAGData.nodes 14 ⟨763587, by decide⟩ =
    .split (coordinate 7) (![⟨738183, by decide⟩,⟨746105, by decide⟩,⟨755032, by decide⟩,⟨763586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_91_763587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 91 ⟨763587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 91
    ⟨763587, by decide⟩ (by decide) (![⟨738183, by decide⟩,⟨746105, by decide⟩,⟨755032, by decide⟩,⟨763586, by decide⟩]) unmarked_context_7_91_763587 node_context_7_91_763587
  intro a
  fin_cases a
  · exact context_8_364_738183
  · exact context_8_365_746105
  · exact context_8_366_755032
  · exact context_8_367_763586

theorem unmarked_context_6_22_763588 : frontier 15 ⟨763588, by decide⟩
    (prefixCache 6 22) (prefixPartial 6 22) = false := by
  decide +kernel

theorem node_context_6_22_763588 : EJMOriginalGlobalDAGData.nodes 15 ⟨763588, by decide⟩ =
    .split (coordinate 6) (![⟨676732, by decide⟩,⟨710493, by decide⟩,⟨728915, by decide⟩,⟨763587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_22_763588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 22 ⟨763588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 22
    ⟨763588, by decide⟩ (by decide) (![⟨676732, by decide⟩,⟨710493, by decide⟩,⟨728915, by decide⟩,⟨763587, by decide⟩]) unmarked_context_6_22_763588 node_context_6_22_763588
  intro a
  fin_cases a
  · exact context_7_88_676732
  · exact context_7_89_710493
  · exact context_7_90_728915
  · exact context_7_91_763587

theorem selected_cut_30257 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 23) = some ⟨6, 1, 0, 116314, 23, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_23_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 23 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 23 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 23, 1, 268435456⟩
    (by decide) selected_cut_30257

theorem unmarked_context_5_5_763589 : frontier 16 ⟨763589, by decide⟩
    (prefixCache 5 5) (prefixPartial 5 5) = false := by
  decide +kernel

theorem node_context_5_5_763589 : EJMOriginalGlobalDAGData.nodes 16 ⟨763589, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨676731, by decide⟩,⟨763588, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_5_763589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 5 ⟨763589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 5
    ⟨763589, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨676731, by decide⟩,⟨763588, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_5_763589 node_context_5_5_763589
  intro a
  fin_cases a
  · exact context_6_20_434744
  · exact context_6_21_676731
  · exact context_6_22_763588
  · exact context_6_23_116314

theorem selected_cut_30258 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 24) = some ⟨6, 1, 0, 434744, 24, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_24_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 24 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 24 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 24, 1, 268435456⟩
    (by decide) selected_cut_30258

theorem selected_cut_30259 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 100) = some ⟨7, 1, 0, 116316, 100, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_100_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 100 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 100 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 100, 1, 67108864⟩
    (by decide) selected_cut_30259

theorem selected_cut_30260 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 101) = some ⟨7, 1, 0, 116316, 101, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_101_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 101 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 101 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 101, 1, 67108864⟩
    (by decide) selected_cut_30260

theorem selected_cut_30261 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26112) = some ⟨11, 1, 0, 434745, 26112, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26112_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26112 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26112 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26112, 1, 262144⟩
    (by decide) selected_cut_30261

theorem selected_cut_30262 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104452) = some ⟨12, 1, 0, 895, 104452, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104452_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104452 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104452 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104452, 1, 65536⟩
    (by decide) selected_cut_30262

theorem selected_cut_30263 : selected 8 ⟨763718, by decide⟩
    (prefixPartial 13 417812) = some ⟨13, 2, 0, 763718, 417812, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_417812_763718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417812 ⟨763718, by decide⟩ :=
  accepted_of_selected 13 417812 ⟨763718, by decide⟩ ⟨13, 2, 0, 763718, 417812, 2469, 16384⟩
    (by decide) selected_cut_30263

theorem selected_cut_30264 : selected 8 ⟨763808, by decide⟩
    (prefixPartial 13 417813) = some ⟨13, 2, 0, 763808, 417813, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_417813_763808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417813 ⟨763808, by decide⟩ :=
  accepted_of_selected 13 417813 ⟨763808, by decide⟩ ⟨13, 2, 0, 763808, 417813, 1977, 16384⟩
    (by decide) selected_cut_30264

theorem selected_cut_30265 : selected 8 ⟨763838, by decide⟩
    (prefixPartial 13 417814) = some ⟨13, 2, 0, 763838, 417814, 541, 16384⟩ := by
  decide +kernel

theorem context_13_417814_763838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417814 ⟨763838, by decide⟩ :=
  accepted_of_selected 13 417814 ⟨763838, by decide⟩ ⟨13, 2, 0, 763838, 417814, 541, 16384⟩
    (by decide) selected_cut_30265

theorem selected_cut_30266 : selected 8 ⟨763840, by decide⟩
    (prefixPartial 13 417815) = some ⟨13, 2, 0, 763840, 417815, 145, 16384⟩ := by
  decide +kernel

theorem context_13_417815_763840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417815 ⟨763840, by decide⟩ :=
  accepted_of_selected 13 417815 ⟨763840, by decide⟩ ⟨13, 2, 0, 763840, 417815, 145, 16384⟩
    (by decide) selected_cut_30266

theorem unmarked_context_12_104453_763841 : frontier 9 ⟨763841, by decide⟩
    (prefixCache 12 104453) (prefixPartial 12 104453) = false := by
  decide +kernel

theorem node_context_12_104453_763841 : EJMOriginalGlobalDAGData.nodes 9 ⟨763841, by decide⟩ =
    .split (coordinate 12) (![⟨763718, by decide⟩,⟨763808, by decide⟩,⟨763838, by decide⟩,⟨763840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104453_763841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104453 ⟨763841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104453
    ⟨763841, by decide⟩ (by decide) (![⟨763718, by decide⟩,⟨763808, by decide⟩,⟨763838, by decide⟩,⟨763840, by decide⟩]) unmarked_context_12_104453_763841 node_context_12_104453_763841
  intro a
  fin_cases a
  · exact context_13_417812_763718
  · exact context_13_417813_763808
  · exact context_13_417814_763838
  · exact context_13_417815_763840

theorem selected_cut_30267 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 104454) = some ⟨12, 1, 0, 763842, 104454, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104454_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104454 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 104454 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 104454, 1, 65536⟩
    (by decide) selected_cut_30267

theorem selected_cut_30268 : selected 8 ⟨763919, by decide⟩
    (prefixPartial 13 417820) = some ⟨13, 2, 0, 763919, 417820, 2869, 16384⟩ := by
  decide +kernel

theorem context_13_417820_763919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417820 ⟨763919, by decide⟩ :=
  accepted_of_selected 13 417820 ⟨763919, by decide⟩ ⟨13, 2, 0, 763919, 417820, 2869, 16384⟩
    (by decide) selected_cut_30268

theorem selected_cut_30269 : selected 8 ⟨764046, by decide⟩
    (prefixPartial 13 417821) = some ⟨13, 2, 0, 764046, 417821, 4093, 16384⟩ := by
  decide +kernel

theorem context_13_417821_764046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417821 ⟨764046, by decide⟩ :=
  accepted_of_selected 13 417821 ⟨764046, by decide⟩ ⟨13, 2, 0, 764046, 417821, 4093, 16384⟩
    (by decide) selected_cut_30269

theorem selected_cut_30270 : selected 8 ⟨764138, by decide⟩
    (prefixPartial 13 417822) = some ⟨13, 2, 0, 764138, 417822, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_417822_764138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417822 ⟨764138, by decide⟩ :=
  accepted_of_selected 13 417822 ⟨764138, by decide⟩ ⟨13, 2, 0, 764138, 417822, 2197, 16384⟩
    (by decide) selected_cut_30270

theorem selected_cut_30271 : selected 8 ⟨764166, by decide⟩
    (prefixPartial 13 417823) = some ⟨13, 2, 0, 764166, 417823, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_417823_764166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417823 ⟨764166, by decide⟩ :=
  accepted_of_selected 13 417823 ⟨764166, by decide⟩ ⟨13, 2, 0, 764166, 417823, 1209, 16384⟩
    (by decide) selected_cut_30271

theorem unmarked_context_12_104455_764167 : frontier 9 ⟨764167, by decide⟩
    (prefixCache 12 104455) (prefixPartial 12 104455) = false := by
  decide +kernel

theorem node_context_12_104455_764167 : EJMOriginalGlobalDAGData.nodes 9 ⟨764167, by decide⟩ =
    .split (coordinate 12) (![⟨763919, by decide⟩,⟨764046, by decide⟩,⟨764138, by decide⟩,⟨764166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104455_764167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104455 ⟨764167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104455
    ⟨764167, by decide⟩ (by decide) (![⟨763919, by decide⟩,⟨764046, by decide⟩,⟨764138, by decide⟩,⟨764166, by decide⟩]) unmarked_context_12_104455_764167 node_context_12_104455_764167
  intro a
  fin_cases a
  · exact context_13_417820_763919
  · exact context_13_417821_764046
  · exact context_13_417822_764138
  · exact context_13_417823_764166

theorem unmarked_context_11_26113_764168 : frontier 10 ⟨764168, by decide⟩
    (prefixCache 11 26113) (prefixPartial 11 26113) = false := by
  decide +kernel

theorem node_context_11_26113_764168 : EJMOriginalGlobalDAGData.nodes 10 ⟨764168, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨763841, by decide⟩,⟨763842, by decide⟩,⟨764167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26113_764168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26113 ⟨764168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26113
    ⟨764168, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨763841, by decide⟩,⟨763842, by decide⟩,⟨764167, by decide⟩]) unmarked_context_11_26113_764168 node_context_11_26113_764168
  intro a
  fin_cases a
  · exact context_12_104452_895
  · exact context_12_104453_763841
  · exact context_12_104454_763842
  · exact context_12_104455_764167

theorem selected_cut_30272 : selected 10 ⟨764169, by decide⟩
    (prefixPartial 11 26114) = some ⟨11, 1, 0, 764169, 26114, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26114_764169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26114 ⟨764169, by decide⟩ :=
  accepted_of_selected 11 26114 ⟨764169, by decide⟩ ⟨11, 1, 0, 764169, 26114, 1, 262144⟩
    (by decide) selected_cut_30272

theorem selected_cut_30273 : selected 10 ⟨764333, by decide⟩
    (prefixPartial 11 26115) = some ⟨11, 2, 0, 764333, 26115, 3029, 262144⟩ := by
  decide +kernel

theorem context_11_26115_764333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26115 ⟨764333, by decide⟩ :=
  accepted_of_selected 11 26115 ⟨764333, by decide⟩ ⟨11, 2, 0, 764333, 26115, 3029, 262144⟩
    (by decide) selected_cut_30273

theorem unmarked_context_10_6528_764334 : frontier 11 ⟨764334, by decide⟩
    (prefixCache 10 6528) (prefixPartial 10 6528) = false := by
  decide +kernel

theorem node_context_10_6528_764334 : EJMOriginalGlobalDAGData.nodes 11 ⟨764334, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨764168, by decide⟩,⟨764169, by decide⟩,⟨764333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6528_764334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6528 ⟨764334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6528
    ⟨764334, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨764168, by decide⟩,⟨764169, by decide⟩,⟨764333, by decide⟩]) unmarked_context_10_6528_764334 node_context_10_6528_764334
  intro a
  fin_cases a
  · exact context_11_26112_434745
  · exact context_11_26113_764168
  · exact context_11_26114_764169
  · exact context_11_26115_764333

theorem selected_cut_30274 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 104464) = some ⟨12, 1, 0, 307381, 104464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104464_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104464 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 104464 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 104464, 1, 65536⟩
    (by decide) selected_cut_30274

theorem selected_cut_30275 : selected 8 ⟨764372, by decide⟩
    (prefixPartial 13 417860) = some ⟨13, 2, 0, 764372, 417860, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_417860_764372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417860 ⟨764372, by decide⟩ :=
  accepted_of_selected 13 417860 ⟨764372, by decide⟩ ⟨13, 2, 0, 764372, 417860, 1689, 16384⟩
    (by decide) selected_cut_30275

theorem selected_cut_30276 : selected 8 ⟨764413, by decide⟩
    (prefixPartial 13 417861) = some ⟨13, 2, 0, 764413, 417861, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_417861_764413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417861 ⟨764413, by decide⟩ :=
  accepted_of_selected 13 417861 ⟨764413, by decide⟩ ⟨13, 2, 0, 764413, 417861, 2025, 16384⟩
    (by decide) selected_cut_30276

theorem selected_cut_30277 : selected 8 ⟨764439, by decide⟩
    (prefixPartial 13 417862) = some ⟨13, 2, 0, 764439, 417862, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_417862_764439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417862 ⟨764439, by decide⟩ :=
  accepted_of_selected 13 417862 ⟨764439, by decide⟩ ⟨13, 2, 0, 764439, 417862, 1197, 16384⟩
    (by decide) selected_cut_30277

theorem selected_cut_30278 : selected 8 ⟨764460, by decide⟩
    (prefixPartial 13 417863) = some ⟨13, 2, 0, 764460, 417863, 909, 16384⟩ := by
  decide +kernel

theorem context_13_417863_764460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417863 ⟨764460, by decide⟩ :=
  accepted_of_selected 13 417863 ⟨764460, by decide⟩ ⟨13, 2, 0, 764460, 417863, 909, 16384⟩
    (by decide) selected_cut_30278

theorem unmarked_context_12_104465_764461 : frontier 9 ⟨764461, by decide⟩
    (prefixCache 12 104465) (prefixPartial 12 104465) = false := by
  decide +kernel

theorem node_context_12_104465_764461 : EJMOriginalGlobalDAGData.nodes 9 ⟨764461, by decide⟩ =
    .split (coordinate 12) (![⟨764372, by decide⟩,⟨764413, by decide⟩,⟨764439, by decide⟩,⟨764460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104465_764461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104465 ⟨764461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104465
    ⟨764461, by decide⟩ (by decide) (![⟨764372, by decide⟩,⟨764413, by decide⟩,⟨764439, by decide⟩,⟨764460, by decide⟩]) unmarked_context_12_104465_764461 node_context_12_104465_764461
  intro a
  fin_cases a
  · exact context_13_417860_764372
  · exact context_13_417861_764413
  · exact context_13_417862_764439
  · exact context_13_417863_764460

theorem selected_cut_30279 : selected 8 ⟨764493, by decide⟩
    (prefixPartial 13 417864) = some ⟨13, 2, 0, 764493, 417864, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_417864_764493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417864 ⟨764493, by decide⟩ :=
  accepted_of_selected 13 417864 ⟨764493, by decide⟩ ⟨13, 2, 0, 764493, 417864, 1517, 16384⟩
    (by decide) selected_cut_30279

theorem selected_cut_30280 : selected 8 ⟨764522, by decide⟩
    (prefixPartial 13 417865) = some ⟨13, 2, 0, 764522, 417865, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_417865_764522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417865 ⟨764522, by decide⟩ :=
  accepted_of_selected 13 417865 ⟨764522, by decide⟩ ⟨13, 2, 0, 764522, 417865, 1849, 16384⟩
    (by decide) selected_cut_30280

theorem selected_cut_30281 : selected 8 ⟨764541, by decide⟩
    (prefixPartial 13 417866) = some ⟨13, 2, 0, 764541, 417866, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_417866_764541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417866 ⟨764541, by decide⟩ :=
  accepted_of_selected 13 417866 ⟨764541, by decide⟩ ⟨13, 2, 0, 764541, 417866, 1053, 16384⟩
    (by decide) selected_cut_30281

theorem selected_cut_30282 : selected 8 ⟨764550, by decide⟩
    (prefixPartial 13 417867) = some ⟨13, 2, 0, 764550, 417867, 861, 16384⟩ := by
  decide +kernel

theorem context_13_417867_764550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417867 ⟨764550, by decide⟩ :=
  accepted_of_selected 13 417867 ⟨764550, by decide⟩ ⟨13, 2, 0, 764550, 417867, 861, 16384⟩
    (by decide) selected_cut_30282

theorem unmarked_context_12_104466_764551 : frontier 9 ⟨764551, by decide⟩
    (prefixCache 12 104466) (prefixPartial 12 104466) = false := by
  decide +kernel

theorem node_context_12_104466_764551 : EJMOriginalGlobalDAGData.nodes 9 ⟨764551, by decide⟩ =
    .split (coordinate 12) (![⟨764493, by decide⟩,⟨764522, by decide⟩,⟨764541, by decide⟩,⟨764550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104466_764551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104466 ⟨764551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104466
    ⟨764551, by decide⟩ (by decide) (![⟨764493, by decide⟩,⟨764522, by decide⟩,⟨764541, by decide⟩,⟨764550, by decide⟩]) unmarked_context_12_104466_764551 node_context_12_104466_764551
  intro a
  fin_cases a
  · exact context_13_417864_764493
  · exact context_13_417865_764522
  · exact context_13_417866_764541
  · exact context_13_417867_764550

theorem selected_cut_30283 : selected 8 ⟨764587, by decide⟩
    (prefixPartial 13 417868) = some ⟨13, 2, 0, 764587, 417868, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_417868_764587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417868 ⟨764587, by decide⟩ :=
  accepted_of_selected 13 417868 ⟨764587, by decide⟩ ⟨13, 2, 0, 764587, 417868, 1641, 16384⟩
    (by decide) selected_cut_30283

theorem selected_cut_30284 : selected 8 ⟨764618, by decide⟩
    (prefixPartial 13 417869) = some ⟨13, 2, 0, 764618, 417869, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_417869_764618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417869 ⟨764618, by decide⟩ :=
  accepted_of_selected 13 417869 ⟨764618, by decide⟩ ⟨13, 2, 0, 764618, 417869, 2217, 16384⟩
    (by decide) selected_cut_30284

theorem selected_cut_30285 : selected 8 ⟨764644, by decide⟩
    (prefixPartial 13 417870) = some ⟨13, 2, 0, 764644, 417870, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_417870_764644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417870 ⟨764644, by decide⟩ :=
  accepted_of_selected 13 417870 ⟨764644, by decide⟩ ⟨13, 2, 0, 764644, 417870, 1325, 16384⟩
    (by decide) selected_cut_30285

theorem selected_cut_30286 : selected 8 ⟨764650, by decide⟩
    (prefixPartial 13 417871) = some ⟨13, 2, 0, 764650, 417871, 749, 16384⟩ := by
  decide +kernel

theorem context_13_417871_764650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417871 ⟨764650, by decide⟩ :=
  accepted_of_selected 13 417871 ⟨764650, by decide⟩ ⟨13, 2, 0, 764650, 417871, 749, 16384⟩
    (by decide) selected_cut_30286

theorem unmarked_context_12_104467_764651 : frontier 9 ⟨764651, by decide⟩
    (prefixCache 12 104467) (prefixPartial 12 104467) = false := by
  decide +kernel

theorem node_context_12_104467_764651 : EJMOriginalGlobalDAGData.nodes 9 ⟨764651, by decide⟩ =
    .split (coordinate 12) (![⟨764587, by decide⟩,⟨764618, by decide⟩,⟨764644, by decide⟩,⟨764650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104467_764651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104467 ⟨764651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104467
    ⟨764651, by decide⟩ (by decide) (![⟨764587, by decide⟩,⟨764618, by decide⟩,⟨764644, by decide⟩,⟨764650, by decide⟩]) unmarked_context_12_104467_764651 node_context_12_104467_764651
  intro a
  fin_cases a
  · exact context_13_417868_764587
  · exact context_13_417869_764618
  · exact context_13_417870_764644
  · exact context_13_417871_764650

theorem unmarked_context_11_26116_764652 : frontier 10 ⟨764652, by decide⟩
    (prefixCache 11 26116) (prefixPartial 11 26116) = false := by
  decide +kernel

theorem node_context_11_26116_764652 : EJMOriginalGlobalDAGData.nodes 10 ⟨764652, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨764461, by decide⟩,⟨764551, by decide⟩,⟨764651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26116_764652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26116 ⟨764652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26116
    ⟨764652, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨764461, by decide⟩,⟨764551, by decide⟩,⟨764651, by decide⟩]) unmarked_context_11_26116_764652 node_context_11_26116_764652
  intro a
  fin_cases a
  · exact context_12_104464_307381
  · exact context_12_104465_764461
  · exact context_12_104466_764551
  · exact context_12_104467_764651

theorem selected_cut_30287 : selected 8 ⟨764670, by decide⟩
    (prefixPartial 13 417872) = some ⟨13, 2, 0, 764670, 417872, 973, 16384⟩ := by
  decide +kernel

theorem context_13_417872_764670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417872 ⟨764670, by decide⟩ :=
  accepted_of_selected 13 417872 ⟨764670, by decide⟩ ⟨13, 2, 0, 764670, 417872, 973, 16384⟩
    (by decide) selected_cut_30287

theorem selected_cut_30288 : selected 8 ⟨764702, by decide⟩
    (prefixPartial 13 417873) = some ⟨13, 2, 0, 764702, 417873, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_417873_764702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417873 ⟨764702, by decide⟩ :=
  accepted_of_selected 13 417873 ⟨764702, by decide⟩ ⟨13, 2, 0, 764702, 417873, 1881, 16384⟩
    (by decide) selected_cut_30288

theorem selected_cut_30289 : selected 8 ⟨764725, by decide⟩
    (prefixPartial 13 417874) = some ⟨13, 2, 0, 764725, 417874, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_417874_764725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417874 ⟨764725, by decide⟩ :=
  accepted_of_selected 13 417874 ⟨764725, by decide⟩ ⟨13, 2, 0, 764725, 417874, 1101, 16384⟩
    (by decide) selected_cut_30289

theorem selected_cut_30290 : selected 8 ⟨764733, by decide⟩
    (prefixPartial 13 417875) = some ⟨13, 2, 0, 764733, 417875, 849, 16384⟩ := by
  decide +kernel

theorem context_13_417875_764733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417875 ⟨764733, by decide⟩ :=
  accepted_of_selected 13 417875 ⟨764733, by decide⟩ ⟨13, 2, 0, 764733, 417875, 849, 16384⟩
    (by decide) selected_cut_30290

theorem unmarked_context_12_104468_764734 : frontier 9 ⟨764734, by decide⟩
    (prefixCache 12 104468) (prefixPartial 12 104468) = false := by
  decide +kernel

theorem node_context_12_104468_764734 : EJMOriginalGlobalDAGData.nodes 9 ⟨764734, by decide⟩ =
    .split (coordinate 12) (![⟨764670, by decide⟩,⟨764702, by decide⟩,⟨764725, by decide⟩,⟨764733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104468_764734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104468 ⟨764734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104468
    ⟨764734, by decide⟩ (by decide) (![⟨764670, by decide⟩,⟨764702, by decide⟩,⟨764725, by decide⟩,⟨764733, by decide⟩]) unmarked_context_12_104468_764734 node_context_12_104468_764734
  intro a
  fin_cases a
  · exact context_13_417872_764670
  · exact context_13_417873_764702
  · exact context_13_417874_764725
  · exact context_13_417875_764733

theorem selected_cut_30291 : selected 8 ⟨764755, by decide⟩
    (prefixPartial 13 417876) = some ⟨13, 2, 0, 764755, 417876, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_417876_764755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417876 ⟨764755, by decide⟩ :=
  accepted_of_selected 13 417876 ⟨764755, by decide⟩ ⟨13, 2, 0, 764755, 417876, 1273, 16384⟩
    (by decide) selected_cut_30291

theorem selected_cut_30292 : selected 8 ⟨764789, by decide⟩
    (prefixPartial 13 417877) = some ⟨13, 2, 0, 764789, 417877, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_417877_764789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417877 ⟨764789, by decide⟩ :=
  accepted_of_selected 13 417877 ⟨764789, by decide⟩ ⟨13, 2, 0, 764789, 417877, 1885, 16384⟩
    (by decide) selected_cut_30292

theorem selected_cut_30293 : selected 8 ⟨764817, by decide⟩
    (prefixPartial 13 417878) = some ⟨13, 2, 0, 764817, 417878, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_417878_764817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417878 ⟨764817, by decide⟩ :=
  accepted_of_selected 13 417878 ⟨764817, by decide⟩ ⟨13, 2, 0, 764817, 417878, 1129, 16384⟩
    (by decide) selected_cut_30293

theorem selected_cut_30294 : selected 8 ⟨764825, by decide⟩
    (prefixPartial 13 417879) = some ⟨13, 2, 0, 764825, 417879, 949, 16384⟩ := by
  decide +kernel

theorem context_13_417879_764825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417879 ⟨764825, by decide⟩ :=
  accepted_of_selected 13 417879 ⟨764825, by decide⟩ ⟨13, 2, 0, 764825, 417879, 949, 16384⟩
    (by decide) selected_cut_30294

theorem unmarked_context_12_104469_764826 : frontier 9 ⟨764826, by decide⟩
    (prefixCache 12 104469) (prefixPartial 12 104469) = false := by
  decide +kernel

theorem node_context_12_104469_764826 : EJMOriginalGlobalDAGData.nodes 9 ⟨764826, by decide⟩ =
    .split (coordinate 12) (![⟨764755, by decide⟩,⟨764789, by decide⟩,⟨764817, by decide⟩,⟨764825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104469_764826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104469 ⟨764826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104469
    ⟨764826, by decide⟩ (by decide) (![⟨764755, by decide⟩,⟨764789, by decide⟩,⟨764817, by decide⟩,⟨764825, by decide⟩]) unmarked_context_12_104469_764826 node_context_12_104469_764826
  intro a
  fin_cases a
  · exact context_13_417876_764755
  · exact context_13_417877_764789
  · exact context_13_417878_764817
  · exact context_13_417879_764825

theorem selected_cut_30295 : selected 8 ⟨764852, by decide⟩
    (prefixPartial 13 417880) = some ⟨13, 2, 0, 764852, 417880, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_417880_764852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417880 ⟨764852, by decide⟩ :=
  accepted_of_selected 13 417880 ⟨764852, by decide⟩ ⟨13, 2, 0, 764852, 417880, 1449, 16384⟩
    (by decide) selected_cut_30295

theorem selected_cut_30296 : selected 8 ⟨764893, by decide⟩
    (prefixPartial 13 417881) = some ⟨13, 2, 0, 764893, 417881, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_417881_764893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417881 ⟨764893, by decide⟩ :=
  accepted_of_selected 13 417881 ⟨764893, by decide⟩ ⟨13, 2, 0, 764893, 417881, 2021, 16384⟩
    (by decide) selected_cut_30296

theorem selected_cut_30297 : selected 8 ⟨764919, by decide⟩
    (prefixPartial 13 417882) = some ⟨13, 2, 0, 764919, 417882, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_417882_764919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417882 ⟨764919, by decide⟩ :=
  accepted_of_selected 13 417882 ⟨764919, by decide⟩ ⟨13, 2, 0, 764919, 417882, 1089, 16384⟩
    (by decide) selected_cut_30297

theorem selected_cut_30298 : selected 8 ⟨764927, by decide⟩
    (prefixPartial 13 417883) = some ⟨13, 2, 0, 764927, 417883, 873, 16384⟩ := by
  decide +kernel

theorem context_13_417883_764927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417883 ⟨764927, by decide⟩ :=
  accepted_of_selected 13 417883 ⟨764927, by decide⟩ ⟨13, 2, 0, 764927, 417883, 873, 16384⟩
    (by decide) selected_cut_30298

theorem unmarked_context_12_104470_764928 : frontier 9 ⟨764928, by decide⟩
    (prefixCache 12 104470) (prefixPartial 12 104470) = false := by
  decide +kernel

theorem node_context_12_104470_764928 : EJMOriginalGlobalDAGData.nodes 9 ⟨764928, by decide⟩ =
    .split (coordinate 12) (![⟨764852, by decide⟩,⟨764893, by decide⟩,⟨764919, by decide⟩,⟨764927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104470_764928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104470 ⟨764928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104470
    ⟨764928, by decide⟩ (by decide) (![⟨764852, by decide⟩,⟨764893, by decide⟩,⟨764919, by decide⟩,⟨764927, by decide⟩]) unmarked_context_12_104470_764928 node_context_12_104470_764928
  intro a
  fin_cases a
  · exact context_13_417880_764852
  · exact context_13_417881_764893
  · exact context_13_417882_764919
  · exact context_13_417883_764927

theorem selected_cut_30299 : selected 8 ⟨764957, by decide⟩
    (prefixPartial 13 417884) = some ⟨13, 2, 0, 764957, 417884, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_417884_764957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417884 ⟨764957, by decide⟩ :=
  accepted_of_selected 13 417884 ⟨764957, by decide⟩ ⟨13, 2, 0, 764957, 417884, 1553, 16384⟩
    (by decide) selected_cut_30299

theorem selected_cut_30300 : selected 8 ⟨765012, by decide⟩
    (prefixPartial 13 417885) = some ⟨13, 2, 0, 765012, 417885, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_417885_765012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417885 ⟨765012, by decide⟩ :=
  accepted_of_selected 13 417885 ⟨765012, by decide⟩ ⟨13, 2, 0, 765012, 417885, 2405, 16384⟩
    (by decide) selected_cut_30300

theorem selected_cut_30301 : selected 8 ⟨765039, by decide⟩
    (prefixPartial 13 417886) = some ⟨13, 2, 0, 765039, 417886, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_417886_765039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417886 ⟨765039, by decide⟩ :=
  accepted_of_selected 13 417886 ⟨765039, by decide⟩ ⟨13, 2, 0, 765039, 417886, 1285, 16384⟩
    (by decide) selected_cut_30301

theorem selected_cut_30302 : selected 8 ⟨765047, by decide⟩
    (prefixPartial 13 417887) = some ⟨13, 2, 0, 765047, 417887, 841, 16384⟩ := by
  decide +kernel

theorem context_13_417887_765047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417887 ⟨765047, by decide⟩ :=
  accepted_of_selected 13 417887 ⟨765047, by decide⟩ ⟨13, 2, 0, 765047, 417887, 841, 16384⟩
    (by decide) selected_cut_30302

theorem unmarked_context_12_104471_765048 : frontier 9 ⟨765048, by decide⟩
    (prefixCache 12 104471) (prefixPartial 12 104471) = false := by
  decide +kernel

theorem node_context_12_104471_765048 : EJMOriginalGlobalDAGData.nodes 9 ⟨765048, by decide⟩ =
    .split (coordinate 12) (![⟨764957, by decide⟩,⟨765012, by decide⟩,⟨765039, by decide⟩,⟨765047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104471_765048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104471 ⟨765048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104471
    ⟨765048, by decide⟩ (by decide) (![⟨764957, by decide⟩,⟨765012, by decide⟩,⟨765039, by decide⟩,⟨765047, by decide⟩]) unmarked_context_12_104471_765048 node_context_12_104471_765048
  intro a
  fin_cases a
  · exact context_13_417884_764957
  · exact context_13_417885_765012
  · exact context_13_417886_765039
  · exact context_13_417887_765047

theorem unmarked_context_11_26117_765049 : frontier 10 ⟨765049, by decide⟩
    (prefixCache 11 26117) (prefixPartial 11 26117) = false := by
  decide +kernel

theorem node_context_11_26117_765049 : EJMOriginalGlobalDAGData.nodes 10 ⟨765049, by decide⟩ =
    .split (coordinate 11) (![⟨764734, by decide⟩,⟨764826, by decide⟩,⟨764928, by decide⟩,⟨765048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26117_765049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26117 ⟨765049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26117
    ⟨765049, by decide⟩ (by decide) (![⟨764734, by decide⟩,⟨764826, by decide⟩,⟨764928, by decide⟩,⟨765048, by decide⟩]) unmarked_context_11_26117_765049 node_context_11_26117_765049
  intro a
  fin_cases a
  · exact context_12_104468_764734
  · exact context_12_104469_764826
  · exact context_12_104470_764928
  · exact context_12_104471_765048

theorem selected_cut_30303 : selected 8 ⟨765066, by decide⟩
    (prefixPartial 13 417888) = some ⟨13, 2, 0, 765066, 417888, 913, 16384⟩ := by
  decide +kernel

theorem context_13_417888_765066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417888 ⟨765066, by decide⟩ :=
  accepted_of_selected 13 417888 ⟨765066, by decide⟩ ⟨13, 2, 0, 765066, 417888, 913, 16384⟩
    (by decide) selected_cut_30303

theorem selected_cut_30304 : selected 8 ⟨765089, by decide⟩
    (prefixPartial 13 417889) = some ⟨13, 2, 0, 765089, 417889, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_417889_765089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417889 ⟨765089, by decide⟩ :=
  accepted_of_selected 13 417889 ⟨765089, by decide⟩ ⟨13, 2, 0, 765089, 417889, 1645, 16384⟩
    (by decide) selected_cut_30304

theorem selected_cut_30305 : selected 8 ⟨765109, by decide⟩
    (prefixPartial 13 417890) = some ⟨13, 2, 0, 765109, 417890, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_417890_765109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417890 ⟨765109, by decide⟩ :=
  accepted_of_selected 13 417890 ⟨765109, by decide⟩ ⟨13, 2, 0, 765109, 417890, 1189, 16384⟩
    (by decide) selected_cut_30305

theorem selected_cut_30306 : selected 8 ⟨765119, by decide⟩
    (prefixPartial 13 417891) = some ⟨13, 2, 0, 765119, 417891, 717, 16384⟩ := by
  decide +kernel

theorem context_13_417891_765119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417891 ⟨765119, by decide⟩ :=
  accepted_of_selected 13 417891 ⟨765119, by decide⟩ ⟨13, 2, 0, 765119, 417891, 717, 16384⟩
    (by decide) selected_cut_30306

theorem unmarked_context_12_104472_765120 : frontier 9 ⟨765120, by decide⟩
    (prefixCache 12 104472) (prefixPartial 12 104472) = false := by
  decide +kernel

theorem node_context_12_104472_765120 : EJMOriginalGlobalDAGData.nodes 9 ⟨765120, by decide⟩ =
    .split (coordinate 12) (![⟨765066, by decide⟩,⟨765089, by decide⟩,⟨765109, by decide⟩,⟨765119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104472_765120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104472 ⟨765120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104472
    ⟨765120, by decide⟩ (by decide) (![⟨765066, by decide⟩,⟨765089, by decide⟩,⟨765109, by decide⟩,⟨765119, by decide⟩]) unmarked_context_12_104472_765120 node_context_12_104472_765120
  intro a
  fin_cases a
  · exact context_13_417888_765066
  · exact context_13_417889_765089
  · exact context_13_417890_765109
  · exact context_13_417891_765119

theorem selected_cut_30307 : selected 8 ⟨765143, by decide⟩
    (prefixPartial 13 417892) = some ⟨13, 2, 0, 765143, 417892, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_417892_765143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417892 ⟨765143, by decide⟩ :=
  accepted_of_selected 13 417892 ⟨765143, by decide⟩ ⟨13, 2, 0, 765143, 417892, 1281, 16384⟩
    (by decide) selected_cut_30307

theorem selected_cut_30308 : selected 8 ⟨765180, by decide⟩
    (prefixPartial 13 417893) = some ⟨13, 2, 0, 765180, 417893, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_417893_765180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417893 ⟨765180, by decide⟩ :=
  accepted_of_selected 13 417893 ⟨765180, by decide⟩ ⟨13, 2, 0, 765180, 417893, 1913, 16384⟩
    (by decide) selected_cut_30308

theorem selected_cut_30309 : selected 8 ⟨765204, by decide⟩
    (prefixPartial 13 417894) = some ⟨13, 2, 0, 765204, 417894, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_417894_765204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417894 ⟨765204, by decide⟩ :=
  accepted_of_selected 13 417894 ⟨765204, by decide⟩ ⟨13, 2, 0, 765204, 417894, 1313, 16384⟩
    (by decide) selected_cut_30309

theorem selected_cut_30310 : selected 8 ⟨765214, by decide⟩
    (prefixPartial 13 417895) = some ⟨13, 2, 0, 765214, 417895, 917, 16384⟩ := by
  decide +kernel

theorem context_13_417895_765214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417895 ⟨765214, by decide⟩ :=
  accepted_of_selected 13 417895 ⟨765214, by decide⟩ ⟨13, 2, 0, 765214, 417895, 917, 16384⟩
    (by decide) selected_cut_30310

theorem unmarked_context_12_104473_765215 : frontier 9 ⟨765215, by decide⟩
    (prefixCache 12 104473) (prefixPartial 12 104473) = false := by
  decide +kernel

theorem node_context_12_104473_765215 : EJMOriginalGlobalDAGData.nodes 9 ⟨765215, by decide⟩ =
    .split (coordinate 12) (![⟨765143, by decide⟩,⟨765180, by decide⟩,⟨765204, by decide⟩,⟨765214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104473_765215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104473 ⟨765215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104473
    ⟨765215, by decide⟩ (by decide) (![⟨765143, by decide⟩,⟨765180, by decide⟩,⟨765204, by decide⟩,⟨765214, by decide⟩]) unmarked_context_12_104473_765215 node_context_12_104473_765215
  intro a
  fin_cases a
  · exact context_13_417892_765143
  · exact context_13_417893_765180
  · exact context_13_417894_765204
  · exact context_13_417895_765214

theorem selected_cut_30311 : selected 8 ⟨765236, by decide⟩
    (prefixPartial 13 417896) = some ⟨13, 2, 0, 765236, 417896, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_417896_765236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417896 ⟨765236, by decide⟩ :=
  accepted_of_selected 13 417896 ⟨765236, by decide⟩ ⟨13, 2, 0, 765236, 417896, 1061, 16384⟩
    (by decide) selected_cut_30311

theorem selected_cut_30312 : selected 8 ⟨765257, by decide⟩
    (prefixPartial 13 417897) = some ⟨13, 2, 0, 765257, 417897, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_417897_765257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417897 ⟨765257, by decide⟩ :=
  accepted_of_selected 13 417897 ⟨765257, by decide⟩ ⟨13, 2, 0, 765257, 417897, 1493, 16384⟩
    (by decide) selected_cut_30312

theorem selected_cut_30313 : selected 8 ⟨765276, by decide⟩
    (prefixPartial 13 417898) = some ⟨13, 2, 0, 765276, 417898, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_417898_765276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417898 ⟨765276, by decide⟩ :=
  accepted_of_selected 13 417898 ⟨765276, by decide⟩ ⟨13, 2, 0, 765276, 417898, 1017, 16384⟩
    (by decide) selected_cut_30313

theorem selected_cut_30314 : selected 8 ⟨765284, by decide⟩
    (prefixPartial 13 417899) = some ⟨13, 2, 0, 765284, 417899, 769, 16384⟩ := by
  decide +kernel

theorem context_13_417899_765284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417899 ⟨765284, by decide⟩ :=
  accepted_of_selected 13 417899 ⟨765284, by decide⟩ ⟨13, 2, 0, 765284, 417899, 769, 16384⟩
    (by decide) selected_cut_30314

theorem unmarked_context_12_104474_765285 : frontier 9 ⟨765285, by decide⟩
    (prefixCache 12 104474) (prefixPartial 12 104474) = false := by
  decide +kernel

theorem node_context_12_104474_765285 : EJMOriginalGlobalDAGData.nodes 9 ⟨765285, by decide⟩ =
    .split (coordinate 12) (![⟨765236, by decide⟩,⟨765257, by decide⟩,⟨765276, by decide⟩,⟨765284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104474_765285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104474 ⟨765285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104474
    ⟨765285, by decide⟩ (by decide) (![⟨765236, by decide⟩,⟨765257, by decide⟩,⟨765276, by decide⟩,⟨765284, by decide⟩]) unmarked_context_12_104474_765285 node_context_12_104474_765285
  intro a
  fin_cases a
  · exact context_13_417896_765236
  · exact context_13_417897_765257
  · exact context_13_417898_765276
  · exact context_13_417899_765284

theorem selected_cut_30315 : selected 8 ⟨765309, by decide⟩
    (prefixPartial 13 417900) = some ⟨13, 2, 0, 765309, 417900, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_417900_765309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417900 ⟨765309, by decide⟩ :=
  accepted_of_selected 13 417900 ⟨765309, by decide⟩ ⟨13, 2, 0, 765309, 417900, 1281, 16384⟩
    (by decide) selected_cut_30315

theorem selected_cut_30316 : selected 8 ⟨765339, by decide⟩
    (prefixPartial 13 417901) = some ⟨13, 2, 0, 765339, 417901, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_417901_765339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417901 ⟨765339, by decide⟩ :=
  accepted_of_selected 13 417901 ⟨765339, by decide⟩ ⟨13, 2, 0, 765339, 417901, 2021, 16384⟩
    (by decide) selected_cut_30316

theorem selected_cut_30317 : selected 8 ⟨765359, by decide⟩
    (prefixPartial 13 417902) = some ⟨13, 2, 0, 765359, 417902, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_417902_765359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417902 ⟨765359, by decide⟩ :=
  accepted_of_selected 13 417902 ⟨765359, by decide⟩ ⟨13, 2, 0, 765359, 417902, 1317, 16384⟩
    (by decide) selected_cut_30317

theorem selected_cut_30318 : selected 8 ⟨765366, by decide⟩
    (prefixPartial 13 417903) = some ⟨13, 2, 0, 765366, 417903, 777, 16384⟩ := by
  decide +kernel

theorem context_13_417903_765366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417903 ⟨765366, by decide⟩ :=
  accepted_of_selected 13 417903 ⟨765366, by decide⟩ ⟨13, 2, 0, 765366, 417903, 777, 16384⟩
    (by decide) selected_cut_30318

theorem unmarked_context_12_104475_765367 : frontier 9 ⟨765367, by decide⟩
    (prefixCache 12 104475) (prefixPartial 12 104475) = false := by
  decide +kernel

theorem node_context_12_104475_765367 : EJMOriginalGlobalDAGData.nodes 9 ⟨765367, by decide⟩ =
    .split (coordinate 12) (![⟨765309, by decide⟩,⟨765339, by decide⟩,⟨765359, by decide⟩,⟨765366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104475_765367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104475 ⟨765367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104475
    ⟨765367, by decide⟩ (by decide) (![⟨765309, by decide⟩,⟨765339, by decide⟩,⟨765359, by decide⟩,⟨765366, by decide⟩]) unmarked_context_12_104475_765367 node_context_12_104475_765367
  intro a
  fin_cases a
  · exact context_13_417900_765309
  · exact context_13_417901_765339
  · exact context_13_417902_765359
  · exact context_13_417903_765366

theorem unmarked_context_11_26118_765368 : frontier 10 ⟨765368, by decide⟩
    (prefixCache 11 26118) (prefixPartial 11 26118) = false := by
  decide +kernel

theorem node_context_11_26118_765368 : EJMOriginalGlobalDAGData.nodes 10 ⟨765368, by decide⟩ =
    .split (coordinate 11) (![⟨765120, by decide⟩,⟨765215, by decide⟩,⟨765285, by decide⟩,⟨765367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26118_765368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26118 ⟨765368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26118
    ⟨765368, by decide⟩ (by decide) (![⟨765120, by decide⟩,⟨765215, by decide⟩,⟨765285, by decide⟩,⟨765367, by decide⟩]) unmarked_context_11_26118_765368 node_context_11_26118_765368
  intro a
  fin_cases a
  · exact context_12_104472_765120
  · exact context_12_104473_765215
  · exact context_12_104474_765285
  · exact context_12_104475_765367

theorem selected_cut_30319 : selected 8 ⟨765381, by decide⟩
    (prefixPartial 13 417904) = some ⟨13, 2, 0, 765381, 417904, 961, 16384⟩ := by
  decide +kernel

theorem context_13_417904_765381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417904 ⟨765381, by decide⟩ :=
  accepted_of_selected 13 417904 ⟨765381, by decide⟩ ⟨13, 2, 0, 765381, 417904, 961, 16384⟩
    (by decide) selected_cut_30319

theorem selected_cut_30320 : selected 8 ⟨765403, by decide⟩
    (prefixPartial 13 417905) = some ⟨13, 2, 0, 765403, 417905, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_417905_765403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417905 ⟨765403, by decide⟩ :=
  accepted_of_selected 13 417905 ⟨765403, by decide⟩ ⟨13, 2, 0, 765403, 417905, 1685, 16384⟩
    (by decide) selected_cut_30320

theorem selected_cut_30321 : selected 8 ⟨765429, by decide⟩
    (prefixPartial 13 417906) = some ⟨13, 2, 0, 765429, 417906, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_417906_765429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417906 ⟨765429, by decide⟩ :=
  accepted_of_selected 13 417906 ⟨765429, by decide⟩ ⟨13, 2, 0, 765429, 417906, 1253, 16384⟩
    (by decide) selected_cut_30321

theorem selected_cut_30322 : selected 8 ⟨765435, by decide⟩
    (prefixPartial 13 417907) = some ⟨13, 2, 0, 765435, 417907, 821, 16384⟩ := by
  decide +kernel

theorem context_13_417907_765435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417907 ⟨765435, by decide⟩ :=
  accepted_of_selected 13 417907 ⟨765435, by decide⟩ ⟨13, 2, 0, 765435, 417907, 821, 16384⟩
    (by decide) selected_cut_30322

theorem unmarked_context_12_104476_765436 : frontier 9 ⟨765436, by decide⟩
    (prefixCache 12 104476) (prefixPartial 12 104476) = false := by
  decide +kernel

theorem node_context_12_104476_765436 : EJMOriginalGlobalDAGData.nodes 9 ⟨765436, by decide⟩ =
    .split (coordinate 12) (![⟨765381, by decide⟩,⟨765403, by decide⟩,⟨765429, by decide⟩,⟨765435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104476_765436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104476 ⟨765436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104476
    ⟨765436, by decide⟩ (by decide) (![⟨765381, by decide⟩,⟨765403, by decide⟩,⟨765429, by decide⟩,⟨765435, by decide⟩]) unmarked_context_12_104476_765436 node_context_12_104476_765436
  intro a
  fin_cases a
  · exact context_13_417904_765381
  · exact context_13_417905_765403
  · exact context_13_417906_765429
  · exact context_13_417907_765435

theorem selected_cut_30323 : selected 8 ⟨765458, by decide⟩
    (prefixPartial 13 417908) = some ⟨13, 2, 0, 765458, 417908, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_417908_765458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417908 ⟨765458, by decide⟩ :=
  accepted_of_selected 13 417908 ⟨765458, by decide⟩ ⟨13, 2, 0, 765458, 417908, 1253, 16384⟩
    (by decide) selected_cut_30323

theorem selected_cut_30324 : selected 8 ⟨765496, by decide⟩
    (prefixPartial 13 417909) = some ⟨13, 2, 0, 765496, 417909, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_417909_765496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417909 ⟨765496, by decide⟩ :=
  accepted_of_selected 13 417909 ⟨765496, by decide⟩ ⟨13, 2, 0, 765496, 417909, 2009, 16384⟩
    (by decide) selected_cut_30324

theorem selected_cut_30325 : selected 8 ⟨765527, by decide⟩
    (prefixPartial 13 417910) = some ⟨13, 2, 0, 765527, 417910, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_417910_765527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417910 ⟨765527, by decide⟩ :=
  accepted_of_selected 13 417910 ⟨765527, by decide⟩ ⟨13, 2, 0, 765527, 417910, 1485, 16384⟩
    (by decide) selected_cut_30325

theorem selected_cut_30326 : selected 8 ⟨765542, by decide⟩
    (prefixPartial 13 417911) = some ⟨13, 2, 0, 765542, 417911, 949, 16384⟩ := by
  decide +kernel

theorem context_13_417911_765542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417911 ⟨765542, by decide⟩ :=
  accepted_of_selected 13 417911 ⟨765542, by decide⟩ ⟨13, 2, 0, 765542, 417911, 949, 16384⟩
    (by decide) selected_cut_30326

theorem unmarked_context_12_104477_765543 : frontier 9 ⟨765543, by decide⟩
    (prefixCache 12 104477) (prefixPartial 12 104477) = false := by
  decide +kernel

theorem node_context_12_104477_765543 : EJMOriginalGlobalDAGData.nodes 9 ⟨765543, by decide⟩ =
    .split (coordinate 12) (![⟨765458, by decide⟩,⟨765496, by decide⟩,⟨765527, by decide⟩,⟨765542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104477_765543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104477 ⟨765543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104477
    ⟨765543, by decide⟩ (by decide) (![⟨765458, by decide⟩,⟨765496, by decide⟩,⟨765527, by decide⟩,⟨765542, by decide⟩]) unmarked_context_12_104477_765543 node_context_12_104477_765543
  intro a
  fin_cases a
  · exact context_13_417908_765458
  · exact context_13_417909_765496
  · exact context_13_417910_765527
  · exact context_13_417911_765542

theorem selected_cut_30327 : selected 8 ⟨765565, by decide⟩
    (prefixPartial 13 417912) = some ⟨13, 2, 0, 765565, 417912, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_417912_765565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417912 ⟨765565, by decide⟩ :=
  accepted_of_selected 13 417912 ⟨765565, by decide⟩ ⟨13, 2, 0, 765565, 417912, 1173, 16384⟩
    (by decide) selected_cut_30327

theorem selected_cut_30328 : selected 8 ⟨765593, by decide⟩
    (prefixPartial 13 417913) = some ⟨13, 2, 0, 765593, 417913, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_417913_765593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417913 ⟨765593, by decide⟩ :=
  accepted_of_selected 13 417913 ⟨765593, by decide⟩ ⟨13, 2, 0, 765593, 417913, 1789, 16384⟩
    (by decide) selected_cut_30328

theorem selected_cut_30329 : selected 8 ⟨765621, by decide⟩
    (prefixPartial 13 417914) = some ⟨13, 2, 0, 765621, 417914, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_417914_765621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417914 ⟨765621, by decide⟩ :=
  accepted_of_selected 13 417914 ⟨765621, by decide⟩ ⟨13, 2, 0, 765621, 417914, 1321, 16384⟩
    (by decide) selected_cut_30329

theorem selected_cut_30330 : selected 8 ⟨765627, by decide⟩
    (prefixPartial 13 417915) = some ⟨13, 2, 0, 765627, 417915, 841, 16384⟩ := by
  decide +kernel

theorem context_13_417915_765627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417915 ⟨765627, by decide⟩ :=
  accepted_of_selected 13 417915 ⟨765627, by decide⟩ ⟨13, 2, 0, 765627, 417915, 841, 16384⟩
    (by decide) selected_cut_30330

theorem unmarked_context_12_104478_765628 : frontier 9 ⟨765628, by decide⟩
    (prefixCache 12 104478) (prefixPartial 12 104478) = false := by
  decide +kernel

theorem node_context_12_104478_765628 : EJMOriginalGlobalDAGData.nodes 9 ⟨765628, by decide⟩ =
    .split (coordinate 12) (![⟨765565, by decide⟩,⟨765593, by decide⟩,⟨765621, by decide⟩,⟨765627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104478_765628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104478 ⟨765628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104478
    ⟨765628, by decide⟩ (by decide) (![⟨765565, by decide⟩,⟨765593, by decide⟩,⟨765621, by decide⟩,⟨765627, by decide⟩]) unmarked_context_12_104478_765628 node_context_12_104478_765628
  intro a
  fin_cases a
  · exact context_13_417912_765565
  · exact context_13_417913_765593
  · exact context_13_417914_765621
  · exact context_13_417915_765627

theorem selected_cut_30331 : selected 8 ⟨765643, by decide⟩
    (prefixPartial 13 417916) = some ⟨13, 2, 0, 765643, 417916, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_417916_765643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417916 ⟨765643, by decide⟩ :=
  accepted_of_selected 13 417916 ⟨765643, by decide⟩ ⟨13, 2, 0, 765643, 417916, 1081, 16384⟩
    (by decide) selected_cut_30331

theorem selected_cut_30332 : selected 8 ⟨765673, by decide⟩
    (prefixPartial 13 417917) = some ⟨13, 2, 0, 765673, 417917, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_417917_765673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417917 ⟨765673, by decide⟩ :=
  accepted_of_selected 13 417917 ⟨765673, by decide⟩ ⟨13, 2, 0, 765673, 417917, 1893, 16384⟩
    (by decide) selected_cut_30332

theorem selected_cut_30333 : selected 8 ⟨765695, by decide⟩
    (prefixPartial 13 417918) = some ⟨13, 2, 0, 765695, 417918, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_417918_765695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417918 ⟨765695, by decide⟩ :=
  accepted_of_selected 13 417918 ⟨765695, by decide⟩ ⟨13, 2, 0, 765695, 417918, 1337, 16384⟩
    (by decide) selected_cut_30333

theorem selected_cut_30334 : selected 8 ⟨765702, by decide⟩
    (prefixPartial 13 417919) = some ⟨13, 2, 0, 765702, 417919, 737, 16384⟩ := by
  decide +kernel

theorem context_13_417919_765702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417919 ⟨765702, by decide⟩ :=
  accepted_of_selected 13 417919 ⟨765702, by decide⟩ ⟨13, 2, 0, 765702, 417919, 737, 16384⟩
    (by decide) selected_cut_30334

theorem unmarked_context_12_104479_765703 : frontier 9 ⟨765703, by decide⟩
    (prefixCache 12 104479) (prefixPartial 12 104479) = false := by
  decide +kernel

theorem node_context_12_104479_765703 : EJMOriginalGlobalDAGData.nodes 9 ⟨765703, by decide⟩ =
    .split (coordinate 12) (![⟨765643, by decide⟩,⟨765673, by decide⟩,⟨765695, by decide⟩,⟨765702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104479_765703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104479 ⟨765703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104479
    ⟨765703, by decide⟩ (by decide) (![⟨765643, by decide⟩,⟨765673, by decide⟩,⟨765695, by decide⟩,⟨765702, by decide⟩]) unmarked_context_12_104479_765703 node_context_12_104479_765703
  intro a
  fin_cases a
  · exact context_13_417916_765643
  · exact context_13_417917_765673
  · exact context_13_417918_765695
  · exact context_13_417919_765702

theorem unmarked_context_11_26119_765704 : frontier 10 ⟨765704, by decide⟩
    (prefixCache 11 26119) (prefixPartial 11 26119) = false := by
  decide +kernel

theorem node_context_11_26119_765704 : EJMOriginalGlobalDAGData.nodes 10 ⟨765704, by decide⟩ =
    .split (coordinate 11) (![⟨765436, by decide⟩,⟨765543, by decide⟩,⟨765628, by decide⟩,⟨765703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26119_765704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26119 ⟨765704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26119
    ⟨765704, by decide⟩ (by decide) (![⟨765436, by decide⟩,⟨765543, by decide⟩,⟨765628, by decide⟩,⟨765703, by decide⟩]) unmarked_context_11_26119_765704 node_context_11_26119_765704
  intro a
  fin_cases a
  · exact context_12_104476_765436
  · exact context_12_104477_765543
  · exact context_12_104478_765628
  · exact context_12_104479_765703

theorem unmarked_context_10_6529_765705 : frontier 11 ⟨765705, by decide⟩
    (prefixCache 10 6529) (prefixPartial 10 6529) = false := by
  decide +kernel

theorem node_context_10_6529_765705 : EJMOriginalGlobalDAGData.nodes 11 ⟨765705, by decide⟩ =
    .split (coordinate 10) (![⟨764652, by decide⟩,⟨765049, by decide⟩,⟨765368, by decide⟩,⟨765704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6529_765705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6529 ⟨765705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6529
    ⟨765705, by decide⟩ (by decide) (![⟨764652, by decide⟩,⟨765049, by decide⟩,⟨765368, by decide⟩,⟨765704, by decide⟩]) unmarked_context_10_6529_765705 node_context_10_6529_765705
  intro a
  fin_cases a
  · exact context_11_26116_764652
  · exact context_11_26117_765049
  · exact context_11_26118_765368
  · exact context_11_26119_765704

theorem selected_cut_30335 : selected 9 ⟨765706, by decide⟩
    (prefixPartial 12 104480) = some ⟨12, 1, 0, 765706, 104480, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104480_765706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104480 ⟨765706, by decide⟩ :=
  accepted_of_selected 12 104480 ⟨765706, by decide⟩ ⟨12, 1, 0, 765706, 104480, 1, 65536⟩
    (by decide) selected_cut_30335

theorem selected_cut_30336 : selected 8 ⟨765743, by decide⟩
    (prefixPartial 13 417924) = some ⟨13, 2, 0, 765743, 417924, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_417924_765743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417924 ⟨765743, by decide⟩ :=
  accepted_of_selected 13 417924 ⟨765743, by decide⟩ ⟨13, 2, 0, 765743, 417924, 1165, 16384⟩
    (by decide) selected_cut_30336

theorem selected_cut_30337 : selected 8 ⟨765769, by decide⟩
    (prefixPartial 13 417925) = some ⟨13, 2, 0, 765769, 417925, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_417925_765769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417925 ⟨765769, by decide⟩ :=
  accepted_of_selected 13 417925 ⟨765769, by decide⟩ ⟨13, 2, 0, 765769, 417925, 1569, 16384⟩
    (by decide) selected_cut_30337

theorem selected_cut_30338 : selected 8 ⟨765788, by decide⟩
    (prefixPartial 13 417926) = some ⟨13, 2, 0, 765788, 417926, 857, 16384⟩ := by
  decide +kernel

theorem context_13_417926_765788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417926 ⟨765788, by decide⟩ :=
  accepted_of_selected 13 417926 ⟨765788, by decide⟩ ⟨13, 2, 0, 765788, 417926, 857, 16384⟩
    (by decide) selected_cut_30338

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
