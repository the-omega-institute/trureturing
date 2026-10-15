/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover096
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09316 : selected 8 ⟨257419, by decide⟩
    (prefixPartial 13 93421) = some ⟨13, 2, 0, 257419, 93421, 3181, 16384⟩ := by
  decide +kernel

theorem context_13_93421_257419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93421 ⟨257419, by decide⟩ :=
  accepted_of_selected 13 93421 ⟨257419, by decide⟩ ⟨13, 2, 0, 257419, 93421, 3181, 16384⟩
    (by decide) selected_cut_09316

theorem selected_cut_09317 : selected 8 ⟨257447, by decide⟩
    (prefixPartial 13 93422) = some ⟨13, 2, 0, 257447, 93422, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_93422_257447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93422 ⟨257447, by decide⟩ :=
  accepted_of_selected 13 93422 ⟨257447, by decide⟩ ⟨13, 2, 0, 257447, 93422, 1765, 16384⟩
    (by decide) selected_cut_09317

theorem selected_cut_09318 : selected 8 ⟨257456, by decide⟩
    (prefixPartial 13 93423) = some ⟨13, 2, 0, 257456, 93423, 849, 16384⟩ := by
  decide +kernel

theorem context_13_93423_257456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93423 ⟨257456, by decide⟩ :=
  accepted_of_selected 13 93423 ⟨257456, by decide⟩ ⟨13, 2, 0, 257456, 93423, 849, 16384⟩
    (by decide) selected_cut_09318

theorem unmarked_context_12_23355_257457 : frontier 9 ⟨257457, by decide⟩
    (prefixCache 12 23355) (prefixPartial 12 23355) = false := by
  decide +kernel

theorem node_context_12_23355_257457 : EJMOriginalGlobalDAGData.nodes 9 ⟨257457, by decide⟩ =
    .split (coordinate 12) (![⟨257381, by decide⟩,⟨257419, by decide⟩,⟨257447, by decide⟩,⟨257456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23355_257457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23355 ⟨257457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23355
    ⟨257457, by decide⟩ (by decide) (![⟨257381, by decide⟩,⟨257419, by decide⟩,⟨257447, by decide⟩,⟨257456, by decide⟩]) unmarked_context_12_23355_257457 node_context_12_23355_257457
  intro a
  fin_cases a
  · exact context_13_93420_257381
  · exact context_13_93421_257419
  · exact context_13_93422_257447
  · exact context_13_93423_257456

theorem unmarked_context_11_5838_257458 : frontier 10 ⟨257458, by decide⟩
    (prefixCache 11 5838) (prefixPartial 11 5838) = false := by
  decide +kernel

theorem node_context_11_5838_257458 : EJMOriginalGlobalDAGData.nodes 10 ⟨257458, by decide⟩ =
    .split (coordinate 11) (![⟨257175, by decide⟩,⟨257273, by decide⟩,⟨257377, by decide⟩,⟨257457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5838_257458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5838 ⟨257458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5838
    ⟨257458, by decide⟩ (by decide) (![⟨257175, by decide⟩,⟨257273, by decide⟩,⟨257377, by decide⟩,⟨257457, by decide⟩]) unmarked_context_11_5838_257458 node_context_11_5838_257458
  intro a
  fin_cases a
  · exact context_12_23352_257175
  · exact context_12_23353_257273
  · exact context_12_23354_257377
  · exact context_12_23355_257457

theorem selected_cut_09319 : selected 8 ⟨257461, by decide⟩
    (prefixPartial 13 93424) = some ⟨13, 2, 0, 257461, 93424, 133, 16384⟩ := by
  decide +kernel

theorem context_13_93424_257461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93424 ⟨257461, by decide⟩ :=
  accepted_of_selected 13 93424 ⟨257461, by decide⟩ ⟨13, 2, 0, 257461, 93424, 133, 16384⟩
    (by decide) selected_cut_09319

theorem selected_cut_09320 : selected 8 ⟨257491, by decide⟩
    (prefixPartial 13 93425) = some ⟨13, 2, 0, 257491, 93425, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_93425_257491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93425 ⟨257491, by decide⟩ :=
  accepted_of_selected 13 93425 ⟨257491, by decide⟩ ⟨13, 2, 0, 257491, 93425, 2365, 16384⟩
    (by decide) selected_cut_09320

theorem selected_cut_09321 : selected 8 ⟨257512, by decide⟩
    (prefixPartial 13 93426) = some ⟨13, 2, 0, 257512, 93426, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_93426_257512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93426 ⟨257512, by decide⟩ :=
  accepted_of_selected 13 93426 ⟨257512, by decide⟩ ⟨13, 2, 0, 257512, 93426, 1249, 16384⟩
    (by decide) selected_cut_09321

theorem selected_cut_09322 : selected 8 ⟨257522, by decide⟩
    (prefixPartial 13 93427) = some ⟨13, 2, 0, 257522, 93427, 817, 16384⟩ := by
  decide +kernel

theorem context_13_93427_257522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93427 ⟨257522, by decide⟩ :=
  accepted_of_selected 13 93427 ⟨257522, by decide⟩ ⟨13, 2, 0, 257522, 93427, 817, 16384⟩
    (by decide) selected_cut_09322

theorem unmarked_context_12_23356_257523 : frontier 9 ⟨257523, by decide⟩
    (prefixCache 12 23356) (prefixPartial 12 23356) = false := by
  decide +kernel

theorem node_context_12_23356_257523 : EJMOriginalGlobalDAGData.nodes 9 ⟨257523, by decide⟩ =
    .split (coordinate 12) (![⟨257461, by decide⟩,⟨257491, by decide⟩,⟨257512, by decide⟩,⟨257522, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23356_257523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23356 ⟨257523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23356
    ⟨257523, by decide⟩ (by decide) (![⟨257461, by decide⟩,⟨257491, by decide⟩,⟨257512, by decide⟩,⟨257522, by decide⟩]) unmarked_context_12_23356_257523 node_context_12_23356_257523
  intro a
  fin_cases a
  · exact context_13_93424_257461
  · exact context_13_93425_257491
  · exact context_13_93426_257512
  · exact context_13_93427_257522

theorem selected_cut_09323 : selected 8 ⟨257526, by decide⟩
    (prefixPartial 13 93428) = some ⟨13, 2, 0, 257526, 93428, 121, 16384⟩ := by
  decide +kernel

theorem context_13_93428_257526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93428 ⟨257526, by decide⟩ :=
  accepted_of_selected 13 93428 ⟨257526, by decide⟩ ⟨13, 2, 0, 257526, 93428, 121, 16384⟩
    (by decide) selected_cut_09323

theorem selected_cut_09324 : selected 8 ⟨257561, by decide⟩
    (prefixPartial 13 93429) = some ⟨13, 2, 0, 257561, 93429, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_93429_257561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93429 ⟨257561, by decide⟩ :=
  accepted_of_selected 13 93429 ⟨257561, by decide⟩ ⟨13, 2, 0, 257561, 93429, 2257, 16384⟩
    (by decide) selected_cut_09324

theorem selected_cut_09325 : selected 8 ⟨257580, by decide⟩
    (prefixPartial 13 93430) = some ⟨13, 2, 0, 257580, 93430, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_93430_257580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93430 ⟨257580, by decide⟩ :=
  accepted_of_selected 13 93430 ⟨257580, by decide⟩ ⟨13, 2, 0, 257580, 93430, 1409, 16384⟩
    (by decide) selected_cut_09325

theorem selected_cut_09326 : selected 8 ⟨257585, by decide⟩
    (prefixPartial 13 93431) = some ⟨13, 2, 0, 257585, 93431, 777, 16384⟩ := by
  decide +kernel

theorem context_13_93431_257585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93431 ⟨257585, by decide⟩ :=
  accepted_of_selected 13 93431 ⟨257585, by decide⟩ ⟨13, 2, 0, 257585, 93431, 777, 16384⟩
    (by decide) selected_cut_09326

theorem unmarked_context_12_23357_257586 : frontier 9 ⟨257586, by decide⟩
    (prefixCache 12 23357) (prefixPartial 12 23357) = false := by
  decide +kernel

theorem node_context_12_23357_257586 : EJMOriginalGlobalDAGData.nodes 9 ⟨257586, by decide⟩ =
    .split (coordinate 12) (![⟨257526, by decide⟩,⟨257561, by decide⟩,⟨257580, by decide⟩,⟨257585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23357_257586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23357 ⟨257586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23357
    ⟨257586, by decide⟩ (by decide) (![⟨257526, by decide⟩,⟨257561, by decide⟩,⟨257580, by decide⟩,⟨257585, by decide⟩]) unmarked_context_12_23357_257586 node_context_12_23357_257586
  intro a
  fin_cases a
  · exact context_13_93428_257526
  · exact context_13_93429_257561
  · exact context_13_93430_257580
  · exact context_13_93431_257585

theorem selected_cut_09327 : selected 8 ⟨257589, by decide⟩
    (prefixPartial 13 93432) = some ⟨13, 2, 0, 257589, 93432, 85, 16384⟩ := by
  decide +kernel

theorem context_13_93432_257589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93432 ⟨257589, by decide⟩ :=
  accepted_of_selected 13 93432 ⟨257589, by decide⟩ ⟨13, 2, 0, 257589, 93432, 85, 16384⟩
    (by decide) selected_cut_09327

theorem selected_cut_09328 : selected 8 ⟨257623, by decide⟩
    (prefixPartial 13 93433) = some ⟨13, 2, 0, 257623, 93433, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_93433_257623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93433 ⟨257623, by decide⟩ :=
  accepted_of_selected 13 93433 ⟨257623, by decide⟩ ⟨13, 2, 0, 257623, 93433, 2821, 16384⟩
    (by decide) selected_cut_09328

theorem selected_cut_09329 : selected 8 ⟨257641, by decide⟩
    (prefixPartial 13 93434) = some ⟨13, 2, 0, 257641, 93434, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_93434_257641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93434 ⟨257641, by decide⟩ :=
  accepted_of_selected 13 93434 ⟨257641, by decide⟩ ⟨13, 2, 0, 257641, 93434, 1597, 16384⟩
    (by decide) selected_cut_09329

theorem selected_cut_09330 : selected 8 ⟨257646, by decide⟩
    (prefixPartial 13 93435) = some ⟨13, 2, 0, 257646, 93435, 797, 16384⟩ := by
  decide +kernel

theorem context_13_93435_257646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93435 ⟨257646, by decide⟩ :=
  accepted_of_selected 13 93435 ⟨257646, by decide⟩ ⟨13, 2, 0, 257646, 93435, 797, 16384⟩
    (by decide) selected_cut_09330

theorem unmarked_context_12_23358_257647 : frontier 9 ⟨257647, by decide⟩
    (prefixCache 12 23358) (prefixPartial 12 23358) = false := by
  decide +kernel

theorem node_context_12_23358_257647 : EJMOriginalGlobalDAGData.nodes 9 ⟨257647, by decide⟩ =
    .split (coordinate 12) (![⟨257589, by decide⟩,⟨257623, by decide⟩,⟨257641, by decide⟩,⟨257646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23358_257647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23358 ⟨257647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23358
    ⟨257647, by decide⟩ (by decide) (![⟨257589, by decide⟩,⟨257623, by decide⟩,⟨257641, by decide⟩,⟨257646, by decide⟩]) unmarked_context_12_23358_257647 node_context_12_23358_257647
  intro a
  fin_cases a
  · exact context_13_93432_257589
  · exact context_13_93433_257623
  · exact context_13_93434_257641
  · exact context_13_93435_257646

theorem selected_cut_09331 : selected 8 ⟨257652, by decide⟩
    (prefixPartial 13 93436) = some ⟨13, 2, 0, 257652, 93436, 113, 16384⟩ := by
  decide +kernel

theorem context_13_93436_257652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93436 ⟨257652, by decide⟩ :=
  accepted_of_selected 13 93436 ⟨257652, by decide⟩ ⟨13, 2, 0, 257652, 93436, 113, 16384⟩
    (by decide) selected_cut_09331

theorem selected_cut_09332 : selected 8 ⟨257727, by decide⟩
    (prefixPartial 13 93437) = some ⟨13, 2, 0, 257727, 93437, 3989, 16384⟩ := by
  decide +kernel

theorem context_13_93437_257727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93437 ⟨257727, by decide⟩ :=
  accepted_of_selected 13 93437 ⟨257727, by decide⟩ ⟨13, 2, 0, 257727, 93437, 3989, 16384⟩
    (by decide) selected_cut_09332

theorem selected_cut_09333 : selected 8 ⟨257754, by decide⟩
    (prefixPartial 13 93438) = some ⟨13, 2, 0, 257754, 93438, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_93438_257754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93438 ⟨257754, by decide⟩ :=
  accepted_of_selected 13 93438 ⟨257754, by decide⟩ ⟨13, 2, 0, 257754, 93438, 2149, 16384⟩
    (by decide) selected_cut_09333

theorem selected_cut_09334 : selected 8 ⟨257782, by decide⟩
    (prefixPartial 13 93439) = some ⟨13, 2, 0, 257782, 93439, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_93439_257782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93439 ⟨257782, by decide⟩ :=
  accepted_of_selected 13 93439 ⟨257782, by decide⟩ ⟨13, 2, 0, 257782, 93439, 1045, 16384⟩
    (by decide) selected_cut_09334

theorem unmarked_context_12_23359_257783 : frontier 9 ⟨257783, by decide⟩
    (prefixCache 12 23359) (prefixPartial 12 23359) = false := by
  decide +kernel

theorem node_context_12_23359_257783 : EJMOriginalGlobalDAGData.nodes 9 ⟨257783, by decide⟩ =
    .split (coordinate 12) (![⟨257652, by decide⟩,⟨257727, by decide⟩,⟨257754, by decide⟩,⟨257782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23359_257783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23359 ⟨257783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23359
    ⟨257783, by decide⟩ (by decide) (![⟨257652, by decide⟩,⟨257727, by decide⟩,⟨257754, by decide⟩,⟨257782, by decide⟩]) unmarked_context_12_23359_257783 node_context_12_23359_257783
  intro a
  fin_cases a
  · exact context_13_93436_257652
  · exact context_13_93437_257727
  · exact context_13_93438_257754
  · exact context_13_93439_257782

theorem unmarked_context_11_5839_257784 : frontier 10 ⟨257784, by decide⟩
    (prefixCache 11 5839) (prefixPartial 11 5839) = false := by
  decide +kernel

theorem node_context_11_5839_257784 : EJMOriginalGlobalDAGData.nodes 10 ⟨257784, by decide⟩ =
    .split (coordinate 11) (![⟨257523, by decide⟩,⟨257586, by decide⟩,⟨257647, by decide⟩,⟨257783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5839_257784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5839 ⟨257784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5839
    ⟨257784, by decide⟩ (by decide) (![⟨257523, by decide⟩,⟨257586, by decide⟩,⟨257647, by decide⟩,⟨257783, by decide⟩]) unmarked_context_11_5839_257784 node_context_11_5839_257784
  intro a
  fin_cases a
  · exact context_12_23356_257523
  · exact context_12_23357_257586
  · exact context_12_23358_257647
  · exact context_12_23359_257783

theorem unmarked_context_10_1459_257785 : frontier 11 ⟨257785, by decide⟩
    (prefixCache 10 1459) (prefixPartial 10 1459) = false := by
  decide +kernel

theorem node_context_10_1459_257785 : EJMOriginalGlobalDAGData.nodes 11 ⟨257785, by decide⟩ =
    .split (coordinate 10) (![⟨256766, by decide⟩,⟨257093, by decide⟩,⟨257458, by decide⟩,⟨257784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1459_257785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1459 ⟨257785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1459
    ⟨257785, by decide⟩ (by decide) (![⟨256766, by decide⟩,⟨257093, by decide⟩,⟨257458, by decide⟩,⟨257784, by decide⟩]) unmarked_context_10_1459_257785 node_context_10_1459_257785
  intro a
  fin_cases a
  · exact context_11_5836_256766
  · exact context_11_5837_257093
  · exact context_11_5838_257458
  · exact context_11_5839_257784

theorem unmarked_context_9_364_257786 : frontier 12 ⟨257786, by decide⟩
    (prefixCache 9 364) (prefixPartial 9 364) = false := by
  decide +kernel

theorem node_context_9_364_257786 : EJMOriginalGlobalDAGData.nodes 12 ⟨257786, by decide⟩ =
    .split (coordinate 9) (![⟨253168, by decide⟩,⟨254825, by decide⟩,⟨256492, by decide⟩,⟨257785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_364_257786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 364 ⟨257786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 364
    ⟨257786, by decide⟩ (by decide) (![⟨253168, by decide⟩,⟨254825, by decide⟩,⟨256492, by decide⟩,⟨257785, by decide⟩]) unmarked_context_9_364_257786 node_context_9_364_257786
  intro a
  fin_cases a
  · exact context_10_1456_253168
  · exact context_10_1457_254825
  · exact context_10_1458_256492
  · exact context_10_1459_257785

theorem selected_cut_09335 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93440) = some ⟨13, 1, 0, 3444, 93440, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93440_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93440 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93440 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93440, 1, 16384⟩
    (by decide) selected_cut_09335

theorem selected_cut_09336 : selected 8 ⟨257836, by decide⟩
    (prefixPartial 13 93441) = some ⟨13, 2, 0, 257836, 93441, 3373, 16384⟩ := by
  decide +kernel

theorem context_13_93441_257836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93441 ⟨257836, by decide⟩ :=
  accepted_of_selected 13 93441 ⟨257836, by decide⟩ ⟨13, 2, 0, 257836, 93441, 3373, 16384⟩
    (by decide) selected_cut_09336

theorem selected_cut_09337 : selected 8 ⟨257863, by decide⟩
    (prefixPartial 13 93442) = some ⟨13, 2, 0, 257863, 93442, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_93442_257863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93442 ⟨257863, by decide⟩ :=
  accepted_of_selected 13 93442 ⟨257863, by decide⟩ ⟨13, 2, 0, 257863, 93442, 1501, 16384⟩
    (by decide) selected_cut_09337

theorem selected_cut_09338 : selected 8 ⟨257879, by decide⟩
    (prefixPartial 13 93443) = some ⟨13, 2, 0, 257879, 93443, 929, 16384⟩ := by
  decide +kernel

theorem context_13_93443_257879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93443 ⟨257879, by decide⟩ :=
  accepted_of_selected 13 93443 ⟨257879, by decide⟩ ⟨13, 2, 0, 257879, 93443, 929, 16384⟩
    (by decide) selected_cut_09338

theorem unmarked_context_12_23360_257880 : frontier 9 ⟨257880, by decide⟩
    (prefixCache 12 23360) (prefixPartial 12 23360) = false := by
  decide +kernel

theorem node_context_12_23360_257880 : EJMOriginalGlobalDAGData.nodes 9 ⟨257880, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨257836, by decide⟩,⟨257863, by decide⟩,⟨257879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23360_257880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23360 ⟨257880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23360
    ⟨257880, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨257836, by decide⟩,⟨257863, by decide⟩,⟨257879, by decide⟩]) unmarked_context_12_23360_257880 node_context_12_23360_257880
  intro a
  fin_cases a
  · exact context_13_93440_3444
  · exact context_13_93441_257836
  · exact context_13_93442_257863
  · exact context_13_93443_257879

theorem selected_cut_09339 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93444) = some ⟨13, 1, 0, 3444, 93444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93444, 1, 16384⟩
    (by decide) selected_cut_09339

theorem selected_cut_09340 : selected 7 ⟨257924, by decide⟩
    (prefixPartial 14 373780) = some ⟨14, 2, 0, 257924, 373780, 1497, 4096⟩ := by
  decide +kernel

theorem context_14_373780_257924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373780 ⟨257924, by decide⟩ :=
  accepted_of_selected 14 373780 ⟨257924, by decide⟩ ⟨14, 2, 0, 257924, 373780, 1497, 4096⟩
    (by decide) selected_cut_09340

theorem selected_cut_09341 : selected 7 ⟨257948, by decide⟩
    (prefixPartial 14 373781) = some ⟨14, 2, 0, 257948, 373781, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_373781_257948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373781 ⟨257948, by decide⟩ :=
  accepted_of_selected 14 373781 ⟨257948, by decide⟩ ⟨14, 2, 0, 257948, 373781, 1189, 4096⟩
    (by decide) selected_cut_09341

theorem selected_cut_09342 : selected 7 ⟨257992, by decide⟩
    (prefixPartial 14 373782) = some ⟨14, 2, 0, 257992, 373782, 1457, 4096⟩ := by
  decide +kernel

theorem context_14_373782_257992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373782 ⟨257992, by decide⟩ :=
  accepted_of_selected 14 373782 ⟨257992, by decide⟩ ⟨14, 2, 0, 257992, 373782, 1457, 4096⟩
    (by decide) selected_cut_09342

theorem selected_cut_09343 : selected 7 ⟨258020, by decide⟩
    (prefixPartial 14 373783) = some ⟨14, 2, 0, 258020, 373783, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_373783_258020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373783 ⟨258020, by decide⟩ :=
  accepted_of_selected 14 373783 ⟨258020, by decide⟩ ⟨14, 2, 0, 258020, 373783, 1117, 4096⟩
    (by decide) selected_cut_09343

theorem unmarked_context_13_93445_258021 : frontier 8 ⟨258021, by decide⟩
    (prefixCache 13 93445) (prefixPartial 13 93445) = false := by
  decide +kernel

theorem node_context_13_93445_258021 : EJMOriginalGlobalDAGData.nodes 8 ⟨258021, by decide⟩ =
    .split (coordinate 13) (![⟨257924, by decide⟩,⟨257948, by decide⟩,⟨257992, by decide⟩,⟨258020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93445_258021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93445 ⟨258021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93445
    ⟨258021, by decide⟩ (by decide) (![⟨257924, by decide⟩,⟨257948, by decide⟩,⟨257992, by decide⟩,⟨258020, by decide⟩]) unmarked_context_13_93445_258021 node_context_13_93445_258021
  intro a
  fin_cases a
  · exact context_14_373780_257924
  · exact context_14_373781_257948
  · exact context_14_373782_257992
  · exact context_14_373783_258020

theorem selected_cut_09344 : selected 8 ⟨258058, by decide⟩
    (prefixPartial 13 93446) = some ⟨13, 2, 0, 258058, 93446, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_93446_258058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93446 ⟨258058, by decide⟩ :=
  accepted_of_selected 13 93446 ⟨258058, by decide⟩ ⟨13, 2, 0, 258058, 93446, 2133, 16384⟩
    (by decide) selected_cut_09344

theorem selected_cut_09345 : selected 8 ⟨258073, by decide⟩
    (prefixPartial 13 93447) = some ⟨13, 2, 0, 258073, 93447, 957, 16384⟩ := by
  decide +kernel

theorem context_13_93447_258073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93447 ⟨258073, by decide⟩ :=
  accepted_of_selected 13 93447 ⟨258073, by decide⟩ ⟨13, 2, 0, 258073, 93447, 957, 16384⟩
    (by decide) selected_cut_09345

theorem unmarked_context_12_23361_258074 : frontier 9 ⟨258074, by decide⟩
    (prefixCache 12 23361) (prefixPartial 12 23361) = false := by
  decide +kernel

theorem node_context_12_23361_258074 : EJMOriginalGlobalDAGData.nodes 9 ⟨258074, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258021, by decide⟩,⟨258058, by decide⟩,⟨258073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23361_258074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23361 ⟨258074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23361
    ⟨258074, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258021, by decide⟩,⟨258058, by decide⟩,⟨258073, by decide⟩]) unmarked_context_12_23361_258074 node_context_12_23361_258074
  intro a
  fin_cases a
  · exact context_13_93444_3444
  · exact context_13_93445_258021
  · exact context_13_93446_258058
  · exact context_13_93447_258073

theorem selected_cut_09346 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93448) = some ⟨13, 1, 0, 3444, 93448, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93448_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93448 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93448 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93448, 1, 16384⟩
    (by decide) selected_cut_09346

theorem selected_cut_09347 : selected 8 ⟨258142, by decide⟩
    (prefixPartial 13 93449) = some ⟨13, 2, 0, 258142, 93449, 3725, 16384⟩ := by
  decide +kernel

theorem context_13_93449_258142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93449 ⟨258142, by decide⟩ :=
  accepted_of_selected 13 93449 ⟨258142, by decide⟩ ⟨13, 2, 0, 258142, 93449, 3725, 16384⟩
    (by decide) selected_cut_09347

theorem selected_cut_09348 : selected 8 ⟨258168, by decide⟩
    (prefixPartial 13 93450) = some ⟨13, 2, 0, 258168, 93450, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_93450_258168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93450 ⟨258168, by decide⟩ :=
  accepted_of_selected 13 93450 ⟨258168, by decide⟩ ⟨13, 2, 0, 258168, 93450, 1885, 16384⟩
    (by decide) selected_cut_09348

theorem selected_cut_09349 : selected 8 ⟨258173, by decide⟩
    (prefixPartial 13 93451) = some ⟨13, 2, 0, 258173, 93451, 713, 16384⟩ := by
  decide +kernel

theorem context_13_93451_258173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93451 ⟨258173, by decide⟩ :=
  accepted_of_selected 13 93451 ⟨258173, by decide⟩ ⟨13, 2, 0, 258173, 93451, 713, 16384⟩
    (by decide) selected_cut_09349

theorem unmarked_context_12_23362_258174 : frontier 9 ⟨258174, by decide⟩
    (prefixCache 12 23362) (prefixPartial 12 23362) = false := by
  decide +kernel

theorem node_context_12_23362_258174 : EJMOriginalGlobalDAGData.nodes 9 ⟨258174, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258142, by decide⟩,⟨258168, by decide⟩,⟨258173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23362_258174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23362 ⟨258174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23362
    ⟨258174, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258142, by decide⟩,⟨258168, by decide⟩,⟨258173, by decide⟩]) unmarked_context_12_23362_258174 node_context_12_23362_258174
  intro a
  fin_cases a
  · exact context_13_93448_3444
  · exact context_13_93449_258142
  · exact context_13_93450_258168
  · exact context_13_93451_258173

theorem selected_cut_09350 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93452) = some ⟨13, 1, 0, 3444, 93452, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93452_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93452 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93452 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93452, 1, 16384⟩
    (by decide) selected_cut_09350

theorem selected_cut_09351 : selected 8 ⟨258225, by decide⟩
    (prefixPartial 13 93453) = some ⟨13, 2, 0, 258225, 93453, 3557, 16384⟩ := by
  decide +kernel

theorem context_13_93453_258225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93453 ⟨258225, by decide⟩ :=
  accepted_of_selected 13 93453 ⟨258225, by decide⟩ ⟨13, 2, 0, 258225, 93453, 3557, 16384⟩
    (by decide) selected_cut_09351

theorem selected_cut_09352 : selected 8 ⟨258258, by decide⟩
    (prefixPartial 13 93454) = some ⟨13, 2, 0, 258258, 93454, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_93454_258258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93454 ⟨258258, by decide⟩ :=
  accepted_of_selected 13 93454 ⟨258258, by decide⟩ ⟨13, 2, 0, 258258, 93454, 1905, 16384⟩
    (by decide) selected_cut_09352

theorem selected_cut_09353 : selected 8 ⟨258267, by decide⟩
    (prefixPartial 13 93455) = some ⟨13, 2, 0, 258267, 93455, 681, 16384⟩ := by
  decide +kernel

theorem context_13_93455_258267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93455 ⟨258267, by decide⟩ :=
  accepted_of_selected 13 93455 ⟨258267, by decide⟩ ⟨13, 2, 0, 258267, 93455, 681, 16384⟩
    (by decide) selected_cut_09353

theorem unmarked_context_12_23363_258268 : frontier 9 ⟨258268, by decide⟩
    (prefixCache 12 23363) (prefixPartial 12 23363) = false := by
  decide +kernel

theorem node_context_12_23363_258268 : EJMOriginalGlobalDAGData.nodes 9 ⟨258268, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258225, by decide⟩,⟨258258, by decide⟩,⟨258267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23363_258268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23363 ⟨258268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23363
    ⟨258268, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258225, by decide⟩,⟨258258, by decide⟩,⟨258267, by decide⟩]) unmarked_context_12_23363_258268 node_context_12_23363_258268
  intro a
  fin_cases a
  · exact context_13_93452_3444
  · exact context_13_93453_258225
  · exact context_13_93454_258258
  · exact context_13_93455_258267

theorem unmarked_context_11_5840_258269 : frontier 10 ⟨258269, by decide⟩
    (prefixCache 11 5840) (prefixPartial 11 5840) = false := by
  decide +kernel

theorem node_context_11_5840_258269 : EJMOriginalGlobalDAGData.nodes 10 ⟨258269, by decide⟩ =
    .split (coordinate 11) (![⟨257880, by decide⟩,⟨258074, by decide⟩,⟨258174, by decide⟩,⟨258268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5840_258269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5840 ⟨258269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5840
    ⟨258269, by decide⟩ (by decide) (![⟨257880, by decide⟩,⟨258074, by decide⟩,⟨258174, by decide⟩,⟨258268, by decide⟩]) unmarked_context_11_5840_258269 node_context_11_5840_258269
  intro a
  fin_cases a
  · exact context_12_23360_257880
  · exact context_12_23361_258074
  · exact context_12_23362_258174
  · exact context_12_23363_258268

theorem selected_cut_09354 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93456) = some ⟨13, 1, 0, 3444, 93456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93456, 1, 16384⟩
    (by decide) selected_cut_09354

theorem selected_cut_09355 : selected 8 ⟨258325, by decide⟩
    (prefixPartial 13 93457) = some ⟨13, 2, 0, 258325, 93457, 3445, 16384⟩ := by
  decide +kernel

theorem context_13_93457_258325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93457 ⟨258325, by decide⟩ :=
  accepted_of_selected 13 93457 ⟨258325, by decide⟩ ⟨13, 2, 0, 258325, 93457, 3445, 16384⟩
    (by decide) selected_cut_09355

theorem selected_cut_09356 : selected 8 ⟨258346, by decide⟩
    (prefixPartial 13 93458) = some ⟨13, 2, 0, 258346, 93458, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_93458_258346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93458 ⟨258346, by decide⟩ :=
  accepted_of_selected 13 93458 ⟨258346, by decide⟩ ⟨13, 2, 0, 258346, 93458, 1589, 16384⟩
    (by decide) selected_cut_09356

theorem selected_cut_09357 : selected 8 ⟨258360, by decide⟩
    (prefixPartial 13 93459) = some ⟨13, 2, 0, 258360, 93459, 989, 16384⟩ := by
  decide +kernel

theorem context_13_93459_258360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93459 ⟨258360, by decide⟩ :=
  accepted_of_selected 13 93459 ⟨258360, by decide⟩ ⟨13, 2, 0, 258360, 93459, 989, 16384⟩
    (by decide) selected_cut_09357

theorem unmarked_context_12_23364_258361 : frontier 9 ⟨258361, by decide⟩
    (prefixCache 12 23364) (prefixPartial 12 23364) = false := by
  decide +kernel

theorem node_context_12_23364_258361 : EJMOriginalGlobalDAGData.nodes 9 ⟨258361, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258325, by decide⟩,⟨258346, by decide⟩,⟨258360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23364_258361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23364 ⟨258361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23364
    ⟨258361, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258325, by decide⟩,⟨258346, by decide⟩,⟨258360, by decide⟩]) unmarked_context_12_23364_258361 node_context_12_23364_258361
  intro a
  fin_cases a
  · exact context_13_93456_3444
  · exact context_13_93457_258325
  · exact context_13_93458_258346
  · exact context_13_93459_258360

theorem selected_cut_09358 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93460) = some ⟨13, 1, 0, 3444, 93460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93460, 1, 16384⟩
    (by decide) selected_cut_09358

theorem selected_cut_09359 : selected 7 ⟨258391, by decide⟩
    (prefixPartial 14 373844) = some ⟨14, 2, 0, 258391, 373844, 1261, 4096⟩ := by
  decide +kernel

theorem context_14_373844_258391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373844 ⟨258391, by decide⟩ :=
  accepted_of_selected 14 373844 ⟨258391, by decide⟩ ⟨14, 2, 0, 258391, 373844, 1261, 4096⟩
    (by decide) selected_cut_09359

theorem selected_cut_09360 : selected 7 ⟨258409, by decide⟩
    (prefixPartial 14 373845) = some ⟨14, 2, 0, 258409, 373845, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_373845_258409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373845 ⟨258409, by decide⟩ :=
  accepted_of_selected 14 373845 ⟨258409, by decide⟩ ⟨14, 2, 0, 258409, 373845, 1065, 4096⟩
    (by decide) selected_cut_09360

theorem selected_cut_09361 : selected 7 ⟨258436, by decide⟩
    (prefixPartial 14 373846) = some ⟨14, 2, 0, 258436, 373846, 1333, 4096⟩ := by
  decide +kernel

theorem context_14_373846_258436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373846 ⟨258436, by decide⟩ :=
  accepted_of_selected 14 373846 ⟨258436, by decide⟩ ⟨14, 2, 0, 258436, 373846, 1333, 4096⟩
    (by decide) selected_cut_09361

theorem selected_cut_09362 : selected 7 ⟨258452, by decide⟩
    (prefixPartial 14 373847) = some ⟨14, 2, 0, 258452, 373847, 1005, 4096⟩ := by
  decide +kernel

theorem context_14_373847_258452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 373847 ⟨258452, by decide⟩ :=
  accepted_of_selected 14 373847 ⟨258452, by decide⟩ ⟨14, 2, 0, 258452, 373847, 1005, 4096⟩
    (by decide) selected_cut_09362

theorem unmarked_context_13_93461_258453 : frontier 8 ⟨258453, by decide⟩
    (prefixCache 13 93461) (prefixPartial 13 93461) = false := by
  decide +kernel

theorem node_context_13_93461_258453 : EJMOriginalGlobalDAGData.nodes 8 ⟨258453, by decide⟩ =
    .split (coordinate 13) (![⟨258391, by decide⟩,⟨258409, by decide⟩,⟨258436, by decide⟩,⟨258452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93461_258453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93461 ⟨258453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93461
    ⟨258453, by decide⟩ (by decide) (![⟨258391, by decide⟩,⟨258409, by decide⟩,⟨258436, by decide⟩,⟨258452, by decide⟩]) unmarked_context_13_93461_258453 node_context_13_93461_258453
  intro a
  fin_cases a
  · exact context_14_373844_258391
  · exact context_14_373845_258409
  · exact context_14_373846_258436
  · exact context_14_373847_258452

theorem selected_cut_09363 : selected 8 ⟨258478, by decide⟩
    (prefixPartial 13 93462) = some ⟨13, 2, 0, 258478, 93462, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_93462_258478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93462 ⟨258478, by decide⟩ :=
  accepted_of_selected 13 93462 ⟨258478, by decide⟩ ⟨13, 2, 0, 258478, 93462, 2029, 16384⟩
    (by decide) selected_cut_09363

theorem selected_cut_09364 : selected 8 ⟨258494, by decide⟩
    (prefixPartial 13 93463) = some ⟨13, 2, 0, 258494, 93463, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_93463_258494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93463 ⟨258494, by decide⟩ :=
  accepted_of_selected 13 93463 ⟨258494, by decide⟩ ⟨13, 2, 0, 258494, 93463, 1121, 16384⟩
    (by decide) selected_cut_09364

theorem unmarked_context_12_23365_258495 : frontier 9 ⟨258495, by decide⟩
    (prefixCache 12 23365) (prefixPartial 12 23365) = false := by
  decide +kernel

theorem node_context_12_23365_258495 : EJMOriginalGlobalDAGData.nodes 9 ⟨258495, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258453, by decide⟩,⟨258478, by decide⟩,⟨258494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23365_258495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23365 ⟨258495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23365
    ⟨258495, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258453, by decide⟩,⟨258478, by decide⟩,⟨258494, by decide⟩]) unmarked_context_12_23365_258495 node_context_12_23365_258495
  intro a
  fin_cases a
  · exact context_13_93460_3444
  · exact context_13_93461_258453
  · exact context_13_93462_258478
  · exact context_13_93463_258494

theorem selected_cut_09365 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93464) = some ⟨13, 1, 0, 3444, 93464, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93464_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93464 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93464 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93464, 1, 16384⟩
    (by decide) selected_cut_09365

theorem selected_cut_09366 : selected 8 ⟨258554, by decide⟩
    (prefixPartial 13 93465) = some ⟨13, 2, 0, 258554, 93465, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_93465_258554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93465 ⟨258554, by decide⟩ :=
  accepted_of_selected 13 93465 ⟨258554, by decide⟩ ⟨13, 2, 0, 258554, 93465, 3381, 16384⟩
    (by decide) selected_cut_09366

theorem selected_cut_09367 : selected 8 ⟨258577, by decide⟩
    (prefixPartial 13 93466) = some ⟨13, 2, 0, 258577, 93466, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_93466_258577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93466 ⟨258577, by decide⟩ :=
  accepted_of_selected 13 93466 ⟨258577, by decide⟩ ⟨13, 2, 0, 258577, 93466, 1837, 16384⟩
    (by decide) selected_cut_09367

theorem selected_cut_09368 : selected 8 ⟨258588, by decide⟩
    (prefixPartial 13 93467) = some ⟨13, 2, 0, 258588, 93467, 965, 16384⟩ := by
  decide +kernel

theorem context_13_93467_258588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93467 ⟨258588, by decide⟩ :=
  accepted_of_selected 13 93467 ⟨258588, by decide⟩ ⟨13, 2, 0, 258588, 93467, 965, 16384⟩
    (by decide) selected_cut_09368

theorem unmarked_context_12_23366_258589 : frontier 9 ⟨258589, by decide⟩
    (prefixCache 12 23366) (prefixPartial 12 23366) = false := by
  decide +kernel

theorem node_context_12_23366_258589 : EJMOriginalGlobalDAGData.nodes 9 ⟨258589, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258554, by decide⟩,⟨258577, by decide⟩,⟨258588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23366_258589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23366 ⟨258589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23366
    ⟨258589, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258554, by decide⟩,⟨258577, by decide⟩,⟨258588, by decide⟩]) unmarked_context_12_23366_258589 node_context_12_23366_258589
  intro a
  fin_cases a
  · exact context_13_93464_3444
  · exact context_13_93465_258554
  · exact context_13_93466_258577
  · exact context_13_93467_258588

theorem selected_cut_09369 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93468) = some ⟨13, 1, 0, 3444, 93468, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93468_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93468 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93468 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93468, 1, 16384⟩
    (by decide) selected_cut_09369

theorem selected_cut_09370 : selected 8 ⟨258633, by decide⟩
    (prefixPartial 13 93469) = some ⟨13, 2, 0, 258633, 93469, 3037, 16384⟩ := by
  decide +kernel

theorem context_13_93469_258633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93469 ⟨258633, by decide⟩ :=
  accepted_of_selected 13 93469 ⟨258633, by decide⟩ ⟨13, 2, 0, 258633, 93469, 3037, 16384⟩
    (by decide) selected_cut_09370

theorem selected_cut_09371 : selected 8 ⟨258658, by decide⟩
    (prefixPartial 13 93470) = some ⟨13, 2, 0, 258658, 93470, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_93470_258658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93470 ⟨258658, by decide⟩ :=
  accepted_of_selected 13 93470 ⟨258658, by decide⟩ ⟨13, 2, 0, 258658, 93470, 1853, 16384⟩
    (by decide) selected_cut_09371

theorem selected_cut_09372 : selected 8 ⟨258668, by decide⟩
    (prefixPartial 13 93471) = some ⟨13, 2, 0, 258668, 93471, 817, 16384⟩ := by
  decide +kernel

theorem context_13_93471_258668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93471 ⟨258668, by decide⟩ :=
  accepted_of_selected 13 93471 ⟨258668, by decide⟩ ⟨13, 2, 0, 258668, 93471, 817, 16384⟩
    (by decide) selected_cut_09372

theorem unmarked_context_12_23367_258669 : frontier 9 ⟨258669, by decide⟩
    (prefixCache 12 23367) (prefixPartial 12 23367) = false := by
  decide +kernel

theorem node_context_12_23367_258669 : EJMOriginalGlobalDAGData.nodes 9 ⟨258669, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258633, by decide⟩,⟨258658, by decide⟩,⟨258668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23367_258669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23367 ⟨258669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23367
    ⟨258669, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258633, by decide⟩,⟨258658, by decide⟩,⟨258668, by decide⟩]) unmarked_context_12_23367_258669 node_context_12_23367_258669
  intro a
  fin_cases a
  · exact context_13_93468_3444
  · exact context_13_93469_258633
  · exact context_13_93470_258658
  · exact context_13_93471_258668

theorem unmarked_context_11_5841_258670 : frontier 10 ⟨258670, by decide⟩
    (prefixCache 11 5841) (prefixPartial 11 5841) = false := by
  decide +kernel

theorem node_context_11_5841_258670 : EJMOriginalGlobalDAGData.nodes 10 ⟨258670, by decide⟩ =
    .split (coordinate 11) (![⟨258361, by decide⟩,⟨258495, by decide⟩,⟨258589, by decide⟩,⟨258669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5841_258670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5841 ⟨258670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5841
    ⟨258670, by decide⟩ (by decide) (![⟨258361, by decide⟩,⟨258495, by decide⟩,⟨258589, by decide⟩,⟨258669, by decide⟩]) unmarked_context_11_5841_258670 node_context_11_5841_258670
  intro a
  fin_cases a
  · exact context_12_23364_258361
  · exact context_12_23365_258495
  · exact context_12_23366_258589
  · exact context_12_23367_258669

theorem selected_cut_09373 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93472) = some ⟨13, 1, 0, 3444, 93472, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93472_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93472 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93472 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93472, 1, 16384⟩
    (by decide) selected_cut_09373

theorem selected_cut_09374 : selected 8 ⟨258708, by decide⟩
    (prefixPartial 13 93473) = some ⟨13, 2, 0, 258708, 93473, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_93473_258708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93473 ⟨258708, by decide⟩ :=
  accepted_of_selected 13 93473 ⟨258708, by decide⟩ ⟨13, 2, 0, 258708, 93473, 2821, 16384⟩
    (by decide) selected_cut_09374

theorem selected_cut_09375 : selected 8 ⟨258733, by decide⟩
    (prefixPartial 13 93474) = some ⟨13, 2, 0, 258733, 93474, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_93474_258733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93474 ⟨258733, by decide⟩ :=
  accepted_of_selected 13 93474 ⟨258733, by decide⟩ ⟨13, 2, 0, 258733, 93474, 1973, 16384⟩
    (by decide) selected_cut_09375

theorem selected_cut_09376 : selected 8 ⟨258745, by decide⟩
    (prefixPartial 13 93475) = some ⟨13, 2, 0, 258745, 93475, 997, 16384⟩ := by
  decide +kernel

theorem context_13_93475_258745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93475 ⟨258745, by decide⟩ :=
  accepted_of_selected 13 93475 ⟨258745, by decide⟩ ⟨13, 2, 0, 258745, 93475, 997, 16384⟩
    (by decide) selected_cut_09376

theorem unmarked_context_12_23368_258746 : frontier 9 ⟨258746, by decide⟩
    (prefixCache 12 23368) (prefixPartial 12 23368) = false := by
  decide +kernel

theorem node_context_12_23368_258746 : EJMOriginalGlobalDAGData.nodes 9 ⟨258746, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258708, by decide⟩,⟨258733, by decide⟩,⟨258745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23368_258746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23368 ⟨258746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23368
    ⟨258746, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258708, by decide⟩,⟨258733, by decide⟩,⟨258745, by decide⟩]) unmarked_context_12_23368_258746 node_context_12_23368_258746
  intro a
  fin_cases a
  · exact context_13_93472_3444
  · exact context_13_93473_258708
  · exact context_13_93474_258733
  · exact context_13_93475_258745

theorem selected_cut_09377 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93476) = some ⟨13, 1, 0, 3444, 93476, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93476_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93476 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93476 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93476, 1, 16384⟩
    (by decide) selected_cut_09377

theorem selected_cut_09378 : selected 8 ⟨258827, by decide⟩
    (prefixPartial 13 93477) = some ⟨13, 2, 0, 258827, 93477, 4025, 16384⟩ := by
  decide +kernel

theorem context_13_93477_258827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93477 ⟨258827, by decide⟩ :=
  accepted_of_selected 13 93477 ⟨258827, by decide⟩ ⟨13, 2, 0, 258827, 93477, 4025, 16384⟩
    (by decide) selected_cut_09378

theorem selected_cut_09379 : selected 8 ⟨258874, by decide⟩
    (prefixPartial 13 93478) = some ⟨13, 2, 0, 258874, 93478, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_93478_258874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93478 ⟨258874, by decide⟩ :=
  accepted_of_selected 13 93478 ⟨258874, by decide⟩ ⟨13, 2, 0, 258874, 93478, 2633, 16384⟩
    (by decide) selected_cut_09379

theorem selected_cut_09380 : selected 8 ⟨258894, by decide⟩
    (prefixPartial 13 93479) = some ⟨13, 2, 0, 258894, 93479, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_93479_258894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93479 ⟨258894, by decide⟩ :=
  accepted_of_selected 13 93479 ⟨258894, by decide⟩ ⟨13, 2, 0, 258894, 93479, 1257, 16384⟩
    (by decide) selected_cut_09380

theorem unmarked_context_12_23369_258895 : frontier 9 ⟨258895, by decide⟩
    (prefixCache 12 23369) (prefixPartial 12 23369) = false := by
  decide +kernel

theorem node_context_12_23369_258895 : EJMOriginalGlobalDAGData.nodes 9 ⟨258895, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258827, by decide⟩,⟨258874, by decide⟩,⟨258894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23369_258895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23369 ⟨258895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23369
    ⟨258895, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258827, by decide⟩,⟨258874, by decide⟩,⟨258894, by decide⟩]) unmarked_context_12_23369_258895 node_context_12_23369_258895
  intro a
  fin_cases a
  · exact context_13_93476_3444
  · exact context_13_93477_258827
  · exact context_13_93478_258874
  · exact context_13_93479_258894

theorem selected_cut_09381 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93480) = some ⟨13, 1, 0, 3444, 93480, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93480_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93480 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93480 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93480, 1, 16384⟩
    (by decide) selected_cut_09381

theorem selected_cut_09382 : selected 8 ⟨258930, by decide⟩
    (prefixPartial 13 93481) = some ⟨13, 2, 0, 258930, 93481, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_93481_258930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93481 ⟨258930, by decide⟩ :=
  accepted_of_selected 13 93481 ⟨258930, by decide⟩ ⟨13, 2, 0, 258930, 93481, 2813, 16384⟩
    (by decide) selected_cut_09382

theorem selected_cut_09383 : selected 8 ⟨258958, by decide⟩
    (prefixPartial 13 93482) = some ⟨13, 2, 0, 258958, 93482, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_93482_258958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93482 ⟨258958, by decide⟩ :=
  accepted_of_selected 13 93482 ⟨258958, by decide⟩ ⟨13, 2, 0, 258958, 93482, 2245, 16384⟩
    (by decide) selected_cut_09383

theorem selected_cut_09384 : selected 8 ⟨258968, by decide⟩
    (prefixPartial 13 93483) = some ⟨13, 2, 0, 258968, 93483, 869, 16384⟩ := by
  decide +kernel

theorem context_13_93483_258968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93483 ⟨258968, by decide⟩ :=
  accepted_of_selected 13 93483 ⟨258968, by decide⟩ ⟨13, 2, 0, 258968, 93483, 869, 16384⟩
    (by decide) selected_cut_09384

theorem unmarked_context_12_23370_258969 : frontier 9 ⟨258969, by decide⟩
    (prefixCache 12 23370) (prefixPartial 12 23370) = false := by
  decide +kernel

theorem node_context_12_23370_258969 : EJMOriginalGlobalDAGData.nodes 9 ⟨258969, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨258930, by decide⟩,⟨258958, by decide⟩,⟨258968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23370_258969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23370 ⟨258969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23370
    ⟨258969, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨258930, by decide⟩,⟨258958, by decide⟩,⟨258968, by decide⟩]) unmarked_context_12_23370_258969 node_context_12_23370_258969
  intro a
  fin_cases a
  · exact context_13_93480_3444
  · exact context_13_93481_258930
  · exact context_13_93482_258958
  · exact context_13_93483_258968

theorem selected_cut_09385 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93484) = some ⟨13, 1, 0, 3444, 93484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93484, 1, 16384⟩
    (by decide) selected_cut_09385

theorem selected_cut_09386 : selected 8 ⟨259015, by decide⟩
    (prefixPartial 13 93485) = some ⟨13, 2, 0, 259015, 93485, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_93485_259015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93485 ⟨259015, by decide⟩ :=
  accepted_of_selected 13 93485 ⟨259015, by decide⟩ ⟨13, 2, 0, 259015, 93485, 2785, 16384⟩
    (by decide) selected_cut_09386

theorem selected_cut_09387 : selected 8 ⟨259058, by decide⟩
    (prefixPartial 13 93486) = some ⟨13, 2, 0, 259058, 93486, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_93486_259058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93486 ⟨259058, by decide⟩ :=
  accepted_of_selected 13 93486 ⟨259058, by decide⟩ ⟨13, 2, 0, 259058, 93486, 2245, 16384⟩
    (by decide) selected_cut_09387

theorem selected_cut_09388 : selected 8 ⟨259069, by decide⟩
    (prefixPartial 13 93487) = some ⟨13, 2, 0, 259069, 93487, 897, 16384⟩ := by
  decide +kernel

theorem context_13_93487_259069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93487 ⟨259069, by decide⟩ :=
  accepted_of_selected 13 93487 ⟨259069, by decide⟩ ⟨13, 2, 0, 259069, 93487, 897, 16384⟩
    (by decide) selected_cut_09388

theorem unmarked_context_12_23371_259070 : frontier 9 ⟨259070, by decide⟩
    (prefixCache 12 23371) (prefixPartial 12 23371) = false := by
  decide +kernel

theorem node_context_12_23371_259070 : EJMOriginalGlobalDAGData.nodes 9 ⟨259070, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259015, by decide⟩,⟨259058, by decide⟩,⟨259069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23371_259070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23371 ⟨259070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23371
    ⟨259070, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259015, by decide⟩,⟨259058, by decide⟩,⟨259069, by decide⟩]) unmarked_context_12_23371_259070 node_context_12_23371_259070
  intro a
  fin_cases a
  · exact context_13_93484_3444
  · exact context_13_93485_259015
  · exact context_13_93486_259058
  · exact context_13_93487_259069

theorem unmarked_context_11_5842_259071 : frontier 10 ⟨259071, by decide⟩
    (prefixCache 11 5842) (prefixPartial 11 5842) = false := by
  decide +kernel

theorem node_context_11_5842_259071 : EJMOriginalGlobalDAGData.nodes 10 ⟨259071, by decide⟩ =
    .split (coordinate 11) (![⟨258746, by decide⟩,⟨258895, by decide⟩,⟨258969, by decide⟩,⟨259070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5842_259071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5842 ⟨259071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5842
    ⟨259071, by decide⟩ (by decide) (![⟨258746, by decide⟩,⟨258895, by decide⟩,⟨258969, by decide⟩,⟨259070, by decide⟩]) unmarked_context_11_5842_259071 node_context_11_5842_259071
  intro a
  fin_cases a
  · exact context_12_23368_258746
  · exact context_12_23369_258895
  · exact context_12_23370_258969
  · exact context_12_23371_259070

theorem selected_cut_09389 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93488) = some ⟨13, 1, 0, 3444, 93488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93488, 1, 16384⟩
    (by decide) selected_cut_09389

theorem selected_cut_09390 : selected 8 ⟨259104, by decide⟩
    (prefixPartial 13 93489) = some ⟨13, 2, 0, 259104, 93489, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_93489_259104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93489 ⟨259104, by decide⟩ :=
  accepted_of_selected 13 93489 ⟨259104, by decide⟩ ⟨13, 2, 0, 259104, 93489, 2337, 16384⟩
    (by decide) selected_cut_09390

theorem selected_cut_09391 : selected 8 ⟨259125, by decide⟩
    (prefixPartial 13 93490) = some ⟨13, 2, 0, 259125, 93490, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_93490_259125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93490 ⟨259125, by decide⟩ :=
  accepted_of_selected 13 93490 ⟨259125, by decide⟩ ⟨13, 2, 0, 259125, 93490, 1557, 16384⟩
    (by decide) selected_cut_09391

theorem selected_cut_09392 : selected 8 ⟨259134, by decide⟩
    (prefixPartial 13 93491) = some ⟨13, 2, 0, 259134, 93491, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_93491_259134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93491 ⟨259134, by decide⟩ :=
  accepted_of_selected 13 93491 ⟨259134, by decide⟩ ⟨13, 2, 0, 259134, 93491, 1001, 16384⟩
    (by decide) selected_cut_09392

theorem unmarked_context_12_23372_259135 : frontier 9 ⟨259135, by decide⟩
    (prefixCache 12 23372) (prefixPartial 12 23372) = false := by
  decide +kernel

theorem node_context_12_23372_259135 : EJMOriginalGlobalDAGData.nodes 9 ⟨259135, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259104, by decide⟩,⟨259125, by decide⟩,⟨259134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23372_259135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23372 ⟨259135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23372
    ⟨259135, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259104, by decide⟩,⟨259125, by decide⟩,⟨259134, by decide⟩]) unmarked_context_12_23372_259135 node_context_12_23372_259135
  intro a
  fin_cases a
  · exact context_13_93488_3444
  · exact context_13_93489_259104
  · exact context_13_93490_259125
  · exact context_13_93491_259134

theorem selected_cut_09393 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93492) = some ⟨13, 1, 0, 3444, 93492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93492, 1, 16384⟩
    (by decide) selected_cut_09393

theorem selected_cut_09394 : selected 8 ⟨259197, by decide⟩
    (prefixPartial 13 93493) = some ⟨13, 2, 0, 259197, 93493, 3485, 16384⟩ := by
  decide +kernel

theorem context_13_93493_259197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93493 ⟨259197, by decide⟩ :=
  accepted_of_selected 13 93493 ⟨259197, by decide⟩ ⟨13, 2, 0, 259197, 93493, 3485, 16384⟩
    (by decide) selected_cut_09394

theorem selected_cut_09395 : selected 8 ⟨259228, by decide⟩
    (prefixPartial 13 93494) = some ⟨13, 2, 0, 259228, 93494, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_93494_259228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93494 ⟨259228, by decide⟩ :=
  accepted_of_selected 13 93494 ⟨259228, by decide⟩ ⟨13, 2, 0, 259228, 93494, 2261, 16384⟩
    (by decide) selected_cut_09395

theorem selected_cut_09396 : selected 8 ⟨259255, by decide⟩
    (prefixPartial 13 93495) = some ⟨13, 2, 0, 259255, 93495, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_93495_259255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93495 ⟨259255, by decide⟩ :=
  accepted_of_selected 13 93495 ⟨259255, by decide⟩ ⟨13, 2, 0, 259255, 93495, 1153, 16384⟩
    (by decide) selected_cut_09396

theorem unmarked_context_12_23373_259256 : frontier 9 ⟨259256, by decide⟩
    (prefixCache 12 23373) (prefixPartial 12 23373) = false := by
  decide +kernel

theorem node_context_12_23373_259256 : EJMOriginalGlobalDAGData.nodes 9 ⟨259256, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259197, by decide⟩,⟨259228, by decide⟩,⟨259255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23373_259256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23373 ⟨259256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23373
    ⟨259256, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259197, by decide⟩,⟨259228, by decide⟩,⟨259255, by decide⟩]) unmarked_context_12_23373_259256 node_context_12_23373_259256
  intro a
  fin_cases a
  · exact context_13_93492_3444
  · exact context_13_93493_259197
  · exact context_13_93494_259228
  · exact context_13_93495_259255

theorem selected_cut_09397 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93496) = some ⟨13, 1, 0, 3444, 93496, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93496_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93496 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93496 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93496, 1, 16384⟩
    (by decide) selected_cut_09397

theorem selected_cut_09398 : selected 8 ⟨259297, by decide⟩
    (prefixPartial 13 93497) = some ⟨13, 2, 0, 259297, 93497, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_93497_259297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93497 ⟨259297, by decide⟩ :=
  accepted_of_selected 13 93497 ⟨259297, by decide⟩ ⟨13, 2, 0, 259297, 93497, 2701, 16384⟩
    (by decide) selected_cut_09398

theorem selected_cut_09399 : selected 8 ⟨259323, by decide⟩
    (prefixPartial 13 93498) = some ⟨13, 2, 0, 259323, 93498, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_93498_259323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93498 ⟨259323, by decide⟩ :=
  accepted_of_selected 13 93498 ⟨259323, by decide⟩ ⟨13, 2, 0, 259323, 93498, 1881, 16384⟩
    (by decide) selected_cut_09399

theorem selected_cut_09400 : selected 8 ⟨259331, by decide⟩
    (prefixPartial 13 93499) = some ⟨13, 2, 0, 259331, 93499, 937, 16384⟩ := by
  decide +kernel

theorem context_13_93499_259331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93499 ⟨259331, by decide⟩ :=
  accepted_of_selected 13 93499 ⟨259331, by decide⟩ ⟨13, 2, 0, 259331, 93499, 937, 16384⟩
    (by decide) selected_cut_09400

theorem unmarked_context_12_23374_259332 : frontier 9 ⟨259332, by decide⟩
    (prefixCache 12 23374) (prefixPartial 12 23374) = false := by
  decide +kernel

theorem node_context_12_23374_259332 : EJMOriginalGlobalDAGData.nodes 9 ⟨259332, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259297, by decide⟩,⟨259323, by decide⟩,⟨259331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23374_259332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23374 ⟨259332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23374
    ⟨259332, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259297, by decide⟩,⟨259323, by decide⟩,⟨259331, by decide⟩]) unmarked_context_12_23374_259332 node_context_12_23374_259332
  intro a
  fin_cases a
  · exact context_13_93496_3444
  · exact context_13_93497_259297
  · exact context_13_93498_259323
  · exact context_13_93499_259331

theorem selected_cut_09401 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93500) = some ⟨13, 1, 0, 3444, 93500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93500, 1, 16384⟩
    (by decide) selected_cut_09401

theorem selected_cut_09402 : selected 8 ⟨259423, by decide⟩
    (prefixPartial 13 93501) = some ⟨13, 2, 0, 259423, 93501, 3785, 16384⟩ := by
  decide +kernel

theorem context_13_93501_259423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93501 ⟨259423, by decide⟩ :=
  accepted_of_selected 13 93501 ⟨259423, by decide⟩ ⟨13, 2, 0, 259423, 93501, 3785, 16384⟩
    (by decide) selected_cut_09402

theorem selected_cut_09403 : selected 8 ⟨259541, by decide⟩
    (prefixPartial 13 93502) = some ⟨13, 2, 0, 259541, 93502, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_93502_259541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93502 ⟨259541, by decide⟩ :=
  accepted_of_selected 13 93502 ⟨259541, by decide⟩ ⟨13, 2, 0, 259541, 93502, 3049, 16384⟩
    (by decide) selected_cut_09403

theorem selected_cut_09404 : selected 8 ⟨259598, by decide⟩
    (prefixPartial 13 93503) = some ⟨13, 2, 0, 259598, 93503, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_93503_259598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93503 ⟨259598, by decide⟩ :=
  accepted_of_selected 13 93503 ⟨259598, by decide⟩ ⟨13, 2, 0, 259598, 93503, 1329, 16384⟩
    (by decide) selected_cut_09404

theorem unmarked_context_12_23375_259599 : frontier 9 ⟨259599, by decide⟩
    (prefixCache 12 23375) (prefixPartial 12 23375) = false := by
  decide +kernel

theorem node_context_12_23375_259599 : EJMOriginalGlobalDAGData.nodes 9 ⟨259599, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259423, by decide⟩,⟨259541, by decide⟩,⟨259598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23375_259599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23375 ⟨259599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23375
    ⟨259599, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259423, by decide⟩,⟨259541, by decide⟩,⟨259598, by decide⟩]) unmarked_context_12_23375_259599 node_context_12_23375_259599
  intro a
  fin_cases a
  · exact context_13_93500_3444
  · exact context_13_93501_259423
  · exact context_13_93502_259541
  · exact context_13_93503_259598

theorem unmarked_context_11_5843_259600 : frontier 10 ⟨259600, by decide⟩
    (prefixCache 11 5843) (prefixPartial 11 5843) = false := by
  decide +kernel

theorem node_context_11_5843_259600 : EJMOriginalGlobalDAGData.nodes 10 ⟨259600, by decide⟩ =
    .split (coordinate 11) (![⟨259135, by decide⟩,⟨259256, by decide⟩,⟨259332, by decide⟩,⟨259599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5843_259600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5843 ⟨259600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5843
    ⟨259600, by decide⟩ (by decide) (![⟨259135, by decide⟩,⟨259256, by decide⟩,⟨259332, by decide⟩,⟨259599, by decide⟩]) unmarked_context_11_5843_259600 node_context_11_5843_259600
  intro a
  fin_cases a
  · exact context_12_23372_259135
  · exact context_12_23373_259256
  · exact context_12_23374_259332
  · exact context_12_23375_259599

theorem unmarked_context_10_1460_259601 : frontier 11 ⟨259601, by decide⟩
    (prefixCache 10 1460) (prefixPartial 10 1460) = false := by
  decide +kernel

theorem node_context_10_1460_259601 : EJMOriginalGlobalDAGData.nodes 11 ⟨259601, by decide⟩ =
    .split (coordinate 10) (![⟨258269, by decide⟩,⟨258670, by decide⟩,⟨259071, by decide⟩,⟨259600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1460_259601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1460 ⟨259601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1460
    ⟨259601, by decide⟩ (by decide) (![⟨258269, by decide⟩,⟨258670, by decide⟩,⟨259071, by decide⟩,⟨259600, by decide⟩]) unmarked_context_10_1460_259601 node_context_10_1460_259601
  intro a
  fin_cases a
  · exact context_11_5840_258269
  · exact context_11_5841_258670
  · exact context_11_5842_259071
  · exact context_11_5843_259600

theorem selected_cut_09405 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93504) = some ⟨13, 1, 0, 3444, 93504, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93504_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93504 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93504 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93504, 1, 16384⟩
    (by decide) selected_cut_09405

theorem selected_cut_09406 : selected 8 ⟨259624, by decide⟩
    (prefixPartial 13 93505) = some ⟨13, 2, 0, 259624, 93505, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_93505_259624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93505 ⟨259624, by decide⟩ :=
  accepted_of_selected 13 93505 ⟨259624, by decide⟩ ⟨13, 2, 0, 259624, 93505, 2009, 16384⟩
    (by decide) selected_cut_09406

theorem selected_cut_09407 : selected 8 ⟨259645, by decide⟩
    (prefixPartial 13 93506) = some ⟨13, 2, 0, 259645, 93506, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_93506_259645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93506 ⟨259645, by decide⟩ :=
  accepted_of_selected 13 93506 ⟨259645, by decide⟩ ⟨13, 2, 0, 259645, 93506, 1433, 16384⟩
    (by decide) selected_cut_09407

theorem selected_cut_09408 : selected 8 ⟨259656, by decide⟩
    (prefixPartial 13 93507) = some ⟨13, 2, 0, 259656, 93507, 901, 16384⟩ := by
  decide +kernel

theorem context_13_93507_259656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93507 ⟨259656, by decide⟩ :=
  accepted_of_selected 13 93507 ⟨259656, by decide⟩ ⟨13, 2, 0, 259656, 93507, 901, 16384⟩
    (by decide) selected_cut_09408

theorem unmarked_context_12_23376_259657 : frontier 9 ⟨259657, by decide⟩
    (prefixCache 12 23376) (prefixPartial 12 23376) = false := by
  decide +kernel

theorem node_context_12_23376_259657 : EJMOriginalGlobalDAGData.nodes 9 ⟨259657, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259624, by decide⟩,⟨259645, by decide⟩,⟨259656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23376_259657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23376 ⟨259657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23376
    ⟨259657, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259624, by decide⟩,⟨259645, by decide⟩,⟨259656, by decide⟩]) unmarked_context_12_23376_259657 node_context_12_23376_259657
  intro a
  fin_cases a
  · exact context_13_93504_3444
  · exact context_13_93505_259624
  · exact context_13_93506_259645
  · exact context_13_93507_259656

theorem selected_cut_09409 : selected 9 ⟨259743, by decide⟩
    (prefixPartial 12 23377) = some ⟨12, 2, 0, 259743, 23377, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_23377_259743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23377 ⟨259743, by decide⟩ :=
  accepted_of_selected 12 23377 ⟨259743, by decide⟩ ⟨12, 2, 0, 259743, 23377, 2217, 65536⟩
    (by decide) selected_cut_09409

theorem selected_cut_09410 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93512) = some ⟨13, 1, 0, 3444, 93512, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93512_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93512 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93512 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93512, 1, 16384⟩
    (by decide) selected_cut_09410

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
