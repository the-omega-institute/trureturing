/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover249
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_76842_606457 : frontier 9 ⟨606457, by decide⟩
    (prefixCache 12 76842) (prefixPartial 12 76842) = false := by
  decide +kernel

theorem node_context_12_76842_606457 : EJMOriginalGlobalDAGData.nodes 9 ⟨606457, by decide⟩ =
    .split (coordinate 12) (![⟨606374, by decide⟩,⟨606416, by decide⟩,⟨606444, by decide⟩,⟨606456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76842_606457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76842 ⟨606457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76842
    ⟨606457, by decide⟩ (by decide) (![⟨606374, by decide⟩,⟨606416, by decide⟩,⟨606444, by decide⟩,⟨606456, by decide⟩]) unmarked_context_12_76842_606457 node_context_12_76842_606457
  intro a
  fin_cases a
  · exact context_13_307368_606374
  · exact context_13_307369_606416
  · exact context_13_307370_606444
  · exact context_13_307371_606456

theorem selected_cut_24004 : selected 8 ⟨606474, by decide⟩
    (prefixPartial 13 307372) = some ⟨13, 2, 0, 606474, 307372, 817, 16384⟩ := by
  decide +kernel

theorem context_13_307372_606474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307372 ⟨606474, by decide⟩ :=
  accepted_of_selected 13 307372 ⟨606474, by decide⟩ ⟨13, 2, 0, 606474, 307372, 817, 16384⟩
    (by decide) selected_cut_24004

theorem selected_cut_24005 : selected 8 ⟨606514, by decide⟩
    (prefixPartial 13 307373) = some ⟨13, 2, 0, 606514, 307373, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_307373_606514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307373 ⟨606514, by decide⟩ :=
  accepted_of_selected 13 307373 ⟨606514, by decide⟩ ⟨13, 2, 0, 606514, 307373, 2521, 16384⟩
    (by decide) selected_cut_24005

theorem selected_cut_24006 : selected 8 ⟨606537, by decide⟩
    (prefixPartial 13 307374) = some ⟨13, 2, 0, 606537, 307374, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_307374_606537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307374 ⟨606537, by decide⟩ :=
  accepted_of_selected 13 307374 ⟨606537, by decide⟩ ⟨13, 2, 0, 606537, 307374, 1785, 16384⟩
    (by decide) selected_cut_24006

theorem selected_cut_24007 : selected 8 ⟨606548, by decide⟩
    (prefixPartial 13 307375) = some ⟨13, 2, 0, 606548, 307375, 929, 16384⟩ := by
  decide +kernel

theorem context_13_307375_606548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307375 ⟨606548, by decide⟩ :=
  accepted_of_selected 13 307375 ⟨606548, by decide⟩ ⟨13, 2, 0, 606548, 307375, 929, 16384⟩
    (by decide) selected_cut_24007

theorem unmarked_context_12_76843_606549 : frontier 9 ⟨606549, by decide⟩
    (prefixCache 12 76843) (prefixPartial 12 76843) = false := by
  decide +kernel

theorem node_context_12_76843_606549 : EJMOriginalGlobalDAGData.nodes 9 ⟨606549, by decide⟩ =
    .split (coordinate 12) (![⟨606474, by decide⟩,⟨606514, by decide⟩,⟨606537, by decide⟩,⟨606548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76843_606549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76843 ⟨606549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76843
    ⟨606549, by decide⟩ (by decide) (![⟨606474, by decide⟩,⟨606514, by decide⟩,⟨606537, by decide⟩,⟨606548, by decide⟩]) unmarked_context_12_76843_606549 node_context_12_76843_606549
  intro a
  fin_cases a
  · exact context_13_307372_606474
  · exact context_13_307373_606514
  · exact context_13_307374_606537
  · exact context_13_307375_606548

theorem unmarked_context_11_19210_606550 : frontier 10 ⟨606550, by decide⟩
    (prefixCache 11 19210) (prefixPartial 11 19210) = false := by
  decide +kernel

theorem node_context_11_19210_606550 : EJMOriginalGlobalDAGData.nodes 10 ⟨606550, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨606354, by decide⟩,⟨606457, by decide⟩,⟨606549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19210_606550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19210 ⟨606550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19210
    ⟨606550, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨606354, by decide⟩,⟨606457, by decide⟩,⟨606549, by decide⟩]) unmarked_context_11_19210_606550 node_context_11_19210_606550
  intro a
  fin_cases a
  · exact context_12_76840_435790
  · exact context_12_76841_606354
  · exact context_12_76842_606457
  · exact context_12_76843_606549

theorem selected_cut_24008 : selected 9 ⟨540189, by decide⟩
    (prefixPartial 12 76844) = some ⟨12, 1, 0, 540189, 76844, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76844_540189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76844 ⟨540189, by decide⟩ :=
  accepted_of_selected 12 76844 ⟨540189, by decide⟩ ⟨12, 1, 0, 540189, 76844, 1, 65536⟩
    (by decide) selected_cut_24008

theorem selected_cut_24009 : selected 8 ⟨606566, by decide⟩
    (prefixPartial 13 307380) = some ⟨13, 2, 0, 606566, 307380, 713, 16384⟩ := by
  decide +kernel

theorem context_13_307380_606566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307380 ⟨606566, by decide⟩ :=
  accepted_of_selected 13 307380 ⟨606566, by decide⟩ ⟨13, 2, 0, 606566, 307380, 713, 16384⟩
    (by decide) selected_cut_24009

theorem selected_cut_24010 : selected 8 ⟨606604, by decide⟩
    (prefixPartial 13 307381) = some ⟨13, 2, 0, 606604, 307381, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_307381_606604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307381 ⟨606604, by decide⟩ :=
  accepted_of_selected 13 307381 ⟨606604, by decide⟩ ⟨13, 2, 0, 606604, 307381, 2513, 16384⟩
    (by decide) selected_cut_24010

theorem selected_cut_24011 : selected 8 ⟨606628, by decide⟩
    (prefixPartial 13 307382) = some ⟨13, 2, 0, 606628, 307382, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_307382_606628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307382 ⟨606628, by decide⟩ :=
  accepted_of_selected 13 307382 ⟨606628, by decide⟩ ⟨13, 2, 0, 606628, 307382, 1757, 16384⟩
    (by decide) selected_cut_24011

theorem selected_cut_24012 : selected 8 ⟨606640, by decide⟩
    (prefixPartial 13 307383) = some ⟨13, 2, 0, 606640, 307383, 757, 16384⟩ := by
  decide +kernel

theorem context_13_307383_606640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307383 ⟨606640, by decide⟩ :=
  accepted_of_selected 13 307383 ⟨606640, by decide⟩ ⟨13, 2, 0, 606640, 307383, 757, 16384⟩
    (by decide) selected_cut_24012

theorem unmarked_context_12_76845_606641 : frontier 9 ⟨606641, by decide⟩
    (prefixCache 12 76845) (prefixPartial 12 76845) = false := by
  decide +kernel

theorem node_context_12_76845_606641 : EJMOriginalGlobalDAGData.nodes 9 ⟨606641, by decide⟩ =
    .split (coordinate 12) (![⟨606566, by decide⟩,⟨606604, by decide⟩,⟨606628, by decide⟩,⟨606640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76845_606641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76845 ⟨606641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76845
    ⟨606641, by decide⟩ (by decide) (![⟨606566, by decide⟩,⟨606604, by decide⟩,⟨606628, by decide⟩,⟨606640, by decide⟩]) unmarked_context_12_76845_606641 node_context_12_76845_606641
  intro a
  fin_cases a
  · exact context_13_307380_606566
  · exact context_13_307381_606604
  · exact context_13_307382_606628
  · exact context_13_307383_606640

theorem selected_cut_24013 : selected 8 ⟨606657, by decide⟩
    (prefixPartial 13 307384) = some ⟨13, 2, 0, 606657, 307384, 565, 16384⟩ := by
  decide +kernel

theorem context_13_307384_606657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307384 ⟨606657, by decide⟩ :=
  accepted_of_selected 13 307384 ⟨606657, by decide⟩ ⟨13, 2, 0, 606657, 307384, 565, 16384⟩
    (by decide) selected_cut_24013

theorem selected_cut_24014 : selected 8 ⟨606692, by decide⟩
    (prefixPartial 13 307385) = some ⟨13, 2, 0, 606692, 307385, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_307385_606692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307385 ⟨606692, by decide⟩ :=
  accepted_of_selected 13 307385 ⟨606692, by decide⟩ ⟨13, 2, 0, 606692, 307385, 2385, 16384⟩
    (by decide) selected_cut_24014

theorem selected_cut_24015 : selected 8 ⟨606714, by decide⟩
    (prefixPartial 13 307386) = some ⟨13, 2, 0, 606714, 307386, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_307386_606714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307386 ⟨606714, by decide⟩ :=
  accepted_of_selected 13 307386 ⟨606714, by decide⟩ ⟨13, 2, 0, 606714, 307386, 1281, 16384⟩
    (by decide) selected_cut_24015

theorem selected_cut_24016 : selected 8 ⟨606725, by decide⟩
    (prefixPartial 13 307387) = some ⟨13, 2, 0, 606725, 307387, 809, 16384⟩ := by
  decide +kernel

theorem context_13_307387_606725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307387 ⟨606725, by decide⟩ :=
  accepted_of_selected 13 307387 ⟨606725, by decide⟩ ⟨13, 2, 0, 606725, 307387, 809, 16384⟩
    (by decide) selected_cut_24016

theorem unmarked_context_12_76846_606726 : frontier 9 ⟨606726, by decide⟩
    (prefixCache 12 76846) (prefixPartial 12 76846) = false := by
  decide +kernel

theorem node_context_12_76846_606726 : EJMOriginalGlobalDAGData.nodes 9 ⟨606726, by decide⟩ =
    .split (coordinate 12) (![⟨606657, by decide⟩,⟨606692, by decide⟩,⟨606714, by decide⟩,⟨606725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76846_606726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76846 ⟨606726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76846
    ⟨606726, by decide⟩ (by decide) (![⟨606657, by decide⟩,⟨606692, by decide⟩,⟨606714, by decide⟩,⟨606725, by decide⟩]) unmarked_context_12_76846_606726 node_context_12_76846_606726
  intro a
  fin_cases a
  · exact context_13_307384_606657
  · exact context_13_307385_606692
  · exact context_13_307386_606714
  · exact context_13_307387_606725

theorem selected_cut_24017 : selected 8 ⟨606739, by decide⟩
    (prefixPartial 13 307388) = some ⟨13, 2, 0, 606739, 307388, 525, 16384⟩ := by
  decide +kernel

theorem context_13_307388_606739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307388 ⟨606739, by decide⟩ :=
  accepted_of_selected 13 307388 ⟨606739, by decide⟩ ⟨13, 2, 0, 606739, 307388, 525, 16384⟩
    (by decide) selected_cut_24017

theorem selected_cut_24018 : selected 8 ⟨606769, by decide⟩
    (prefixPartial 13 307389) = some ⟨13, 2, 0, 606769, 307389, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_307389_606769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307389 ⟨606769, by decide⟩ :=
  accepted_of_selected 13 307389 ⟨606769, by decide⟩ ⟨13, 2, 0, 606769, 307389, 2269, 16384⟩
    (by decide) selected_cut_24018

theorem selected_cut_24019 : selected 8 ⟨606791, by decide⟩
    (prefixPartial 13 307390) = some ⟨13, 2, 0, 606791, 307390, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_307390_606791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307390 ⟨606791, by decide⟩ :=
  accepted_of_selected 13 307390 ⟨606791, by decide⟩ ⟨13, 2, 0, 606791, 307390, 1537, 16384⟩
    (by decide) selected_cut_24019

theorem selected_cut_24020 : selected 8 ⟨606804, by decide⟩
    (prefixPartial 13 307391) = some ⟨13, 2, 0, 606804, 307391, 825, 16384⟩ := by
  decide +kernel

theorem context_13_307391_606804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307391 ⟨606804, by decide⟩ :=
  accepted_of_selected 13 307391 ⟨606804, by decide⟩ ⟨13, 2, 0, 606804, 307391, 825, 16384⟩
    (by decide) selected_cut_24020

theorem unmarked_context_12_76847_606805 : frontier 9 ⟨606805, by decide⟩
    (prefixCache 12 76847) (prefixPartial 12 76847) = false := by
  decide +kernel

theorem node_context_12_76847_606805 : EJMOriginalGlobalDAGData.nodes 9 ⟨606805, by decide⟩ =
    .split (coordinate 12) (![⟨606739, by decide⟩,⟨606769, by decide⟩,⟨606791, by decide⟩,⟨606804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76847_606805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76847 ⟨606805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76847
    ⟨606805, by decide⟩ (by decide) (![⟨606739, by decide⟩,⟨606769, by decide⟩,⟨606791, by decide⟩,⟨606804, by decide⟩]) unmarked_context_12_76847_606805 node_context_12_76847_606805
  intro a
  fin_cases a
  · exact context_13_307388_606739
  · exact context_13_307389_606769
  · exact context_13_307390_606791
  · exact context_13_307391_606804

theorem unmarked_context_11_19211_606806 : frontier 10 ⟨606806, by decide⟩
    (prefixCache 11 19211) (prefixPartial 11 19211) = false := by
  decide +kernel

theorem node_context_11_19211_606806 : EJMOriginalGlobalDAGData.nodes 10 ⟨606806, by decide⟩ =
    .split (coordinate 11) (![⟨540189, by decide⟩,⟨606641, by decide⟩,⟨606726, by decide⟩,⟨606805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19211_606806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19211 ⟨606806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19211
    ⟨606806, by decide⟩ (by decide) (![⟨540189, by decide⟩,⟨606641, by decide⟩,⟨606726, by decide⟩,⟨606805, by decide⟩]) unmarked_context_11_19211_606806 node_context_11_19211_606806
  intro a
  fin_cases a
  · exact context_12_76844_540189
  · exact context_12_76845_606641
  · exact context_12_76846_606726
  · exact context_12_76847_606805

theorem unmarked_context_10_4802_606807 : frontier 11 ⟨606807, by decide⟩
    (prefixCache 10 4802) (prefixPartial 10 4802) = false := by
  decide +kernel

theorem node_context_10_4802_606807 : EJMOriginalGlobalDAGData.nodes 11 ⟨606807, by decide⟩ =
    .split (coordinate 10) (![⟨605921, by decide⟩,⟨606242, by decide⟩,⟨606550, by decide⟩,⟨606806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4802_606807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4802 ⟨606807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4802
    ⟨606807, by decide⟩ (by decide) (![⟨605921, by decide⟩,⟨606242, by decide⟩,⟨606550, by decide⟩,⟨606806, by decide⟩]) unmarked_context_10_4802_606807 node_context_10_4802_606807
  intro a
  fin_cases a
  · exact context_11_19208_605921
  · exact context_11_19209_606242
  · exact context_11_19210_606550
  · exact context_11_19211_606806

theorem selected_cut_24021 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76848) = some ⟨12, 1, 0, 445562, 76848, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76848_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76848 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76848 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76848, 1, 65536⟩
    (by decide) selected_cut_24021

theorem selected_cut_24022 : selected 8 ⟨606821, by decide⟩
    (prefixPartial 13 307396) = some ⟨13, 2, 0, 606821, 307396, 485, 16384⟩ := by
  decide +kernel

theorem context_13_307396_606821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307396 ⟨606821, by decide⟩ :=
  accepted_of_selected 13 307396 ⟨606821, by decide⟩ ⟨13, 2, 0, 606821, 307396, 485, 16384⟩
    (by decide) selected_cut_24022

theorem selected_cut_24023 : selected 8 ⟨606846, by decide⟩
    (prefixPartial 13 307397) = some ⟨13, 2, 0, 606846, 307397, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_307397_606846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307397 ⟨606846, by decide⟩ :=
  accepted_of_selected 13 307397 ⟨606846, by decide⟩ ⟨13, 2, 0, 606846, 307397, 1857, 16384⟩
    (by decide) selected_cut_24023

theorem selected_cut_24024 : selected 8 ⟨606870, by decide⟩
    (prefixPartial 13 307398) = some ⟨13, 2, 0, 606870, 307398, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_307398_606870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307398 ⟨606870, by decide⟩ :=
  accepted_of_selected 13 307398 ⟨606870, by decide⟩ ⟨13, 2, 0, 606870, 307398, 1537, 16384⟩
    (by decide) selected_cut_24024

theorem selected_cut_24025 : selected 8 ⟨606881, by decide⟩
    (prefixPartial 13 307399) = some ⟨13, 2, 0, 606881, 307399, 729, 16384⟩ := by
  decide +kernel

theorem context_13_307399_606881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307399 ⟨606881, by decide⟩ :=
  accepted_of_selected 13 307399 ⟨606881, by decide⟩ ⟨13, 2, 0, 606881, 307399, 729, 16384⟩
    (by decide) selected_cut_24025

theorem unmarked_context_12_76849_606882 : frontier 9 ⟨606882, by decide⟩
    (prefixCache 12 76849) (prefixPartial 12 76849) = false := by
  decide +kernel

theorem node_context_12_76849_606882 : EJMOriginalGlobalDAGData.nodes 9 ⟨606882, by decide⟩ =
    .split (coordinate 12) (![⟨606821, by decide⟩,⟨606846, by decide⟩,⟨606870, by decide⟩,⟨606881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76849_606882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76849 ⟨606882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76849
    ⟨606882, by decide⟩ (by decide) (![⟨606821, by decide⟩,⟨606846, by decide⟩,⟨606870, by decide⟩,⟨606881, by decide⟩]) unmarked_context_12_76849_606882 node_context_12_76849_606882
  intro a
  fin_cases a
  · exact context_13_307396_606821
  · exact context_13_307397_606846
  · exact context_13_307398_606870
  · exact context_13_307399_606881

theorem selected_cut_24026 : selected 8 ⟨606893, by decide⟩
    (prefixPartial 13 307400) = some ⟨13, 2, 0, 606893, 307400, 405, 16384⟩ := by
  decide +kernel

theorem context_13_307400_606893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307400 ⟨606893, by decide⟩ :=
  accepted_of_selected 13 307400 ⟨606893, by decide⟩ ⟨13, 2, 0, 606893, 307400, 405, 16384⟩
    (by decide) selected_cut_24026

theorem selected_cut_24027 : selected 8 ⟨606923, by decide⟩
    (prefixPartial 13 307401) = some ⟨13, 2, 0, 606923, 307401, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_307401_606923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307401 ⟨606923, by decide⟩ :=
  accepted_of_selected 13 307401 ⟨606923, by decide⟩ ⟨13, 2, 0, 606923, 307401, 1869, 16384⟩
    (by decide) selected_cut_24027

theorem selected_cut_24028 : selected 8 ⟨606947, by decide⟩
    (prefixPartial 13 307402) = some ⟨13, 2, 0, 606947, 307402, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_307402_606947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307402 ⟨606947, by decide⟩ :=
  accepted_of_selected 13 307402 ⟨606947, by decide⟩ ⟨13, 2, 0, 606947, 307402, 1177, 16384⟩
    (by decide) selected_cut_24028

theorem selected_cut_24029 : selected 8 ⟨606957, by decide⟩
    (prefixPartial 13 307403) = some ⟨13, 2, 0, 606957, 307403, 657, 16384⟩ := by
  decide +kernel

theorem context_13_307403_606957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307403 ⟨606957, by decide⟩ :=
  accepted_of_selected 13 307403 ⟨606957, by decide⟩ ⟨13, 2, 0, 606957, 307403, 657, 16384⟩
    (by decide) selected_cut_24029

theorem unmarked_context_12_76850_606958 : frontier 9 ⟨606958, by decide⟩
    (prefixCache 12 76850) (prefixPartial 12 76850) = false := by
  decide +kernel

theorem node_context_12_76850_606958 : EJMOriginalGlobalDAGData.nodes 9 ⟨606958, by decide⟩ =
    .split (coordinate 12) (![⟨606893, by decide⟩,⟨606923, by decide⟩,⟨606947, by decide⟩,⟨606957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76850_606958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76850 ⟨606958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76850
    ⟨606958, by decide⟩ (by decide) (![⟨606893, by decide⟩,⟨606923, by decide⟩,⟨606947, by decide⟩,⟨606957, by decide⟩]) unmarked_context_12_76850_606958 node_context_12_76850_606958
  intro a
  fin_cases a
  · exact context_13_307400_606893
  · exact context_13_307401_606923
  · exact context_13_307402_606947
  · exact context_13_307403_606957

theorem selected_cut_24030 : selected 8 ⟨606971, by decide⟩
    (prefixPartial 13 307404) = some ⟨13, 2, 0, 606971, 307404, 433, 16384⟩ := by
  decide +kernel

theorem context_13_307404_606971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307404 ⟨606971, by decide⟩ :=
  accepted_of_selected 13 307404 ⟨606971, by decide⟩ ⟨13, 2, 0, 606971, 307404, 433, 16384⟩
    (by decide) selected_cut_24030

theorem selected_cut_24031 : selected 8 ⟨607000, by decide⟩
    (prefixPartial 13 307405) = some ⟨13, 2, 0, 607000, 307405, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_307405_607000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307405 ⟨607000, by decide⟩ :=
  accepted_of_selected 13 307405 ⟨607000, by decide⟩ ⟨13, 2, 0, 607000, 307405, 1945, 16384⟩
    (by decide) selected_cut_24031

theorem selected_cut_24032 : selected 8 ⟨607025, by decide⟩
    (prefixPartial 13 307406) = some ⟨13, 2, 0, 607025, 307406, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_307406_607025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307406 ⟨607025, by decide⟩ :=
  accepted_of_selected 13 307406 ⟨607025, by decide⟩ ⟨13, 2, 0, 607025, 307406, 1441, 16384⟩
    (by decide) selected_cut_24032

theorem selected_cut_24033 : selected 8 ⟨607033, by decide⟩
    (prefixPartial 13 307407) = some ⟨13, 2, 0, 607033, 307407, 729, 16384⟩ := by
  decide +kernel

theorem context_13_307407_607033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307407 ⟨607033, by decide⟩ :=
  accepted_of_selected 13 307407 ⟨607033, by decide⟩ ⟨13, 2, 0, 607033, 307407, 729, 16384⟩
    (by decide) selected_cut_24033

theorem unmarked_context_12_76851_607034 : frontier 9 ⟨607034, by decide⟩
    (prefixCache 12 76851) (prefixPartial 12 76851) = false := by
  decide +kernel

theorem node_context_12_76851_607034 : EJMOriginalGlobalDAGData.nodes 9 ⟨607034, by decide⟩ =
    .split (coordinate 12) (![⟨606971, by decide⟩,⟨607000, by decide⟩,⟨607025, by decide⟩,⟨607033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76851_607034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76851 ⟨607034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76851
    ⟨607034, by decide⟩ (by decide) (![⟨606971, by decide⟩,⟨607000, by decide⟩,⟨607025, by decide⟩,⟨607033, by decide⟩]) unmarked_context_12_76851_607034 node_context_12_76851_607034
  intro a
  fin_cases a
  · exact context_13_307404_606971
  · exact context_13_307405_607000
  · exact context_13_307406_607025
  · exact context_13_307407_607033

theorem unmarked_context_11_19212_607035 : frontier 10 ⟨607035, by decide⟩
    (prefixCache 11 19212) (prefixPartial 11 19212) = false := by
  decide +kernel

theorem node_context_11_19212_607035 : EJMOriginalGlobalDAGData.nodes 10 ⟨607035, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨606882, by decide⟩,⟨606958, by decide⟩,⟨607034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19212_607035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19212 ⟨607035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19212
    ⟨607035, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨606882, by decide⟩,⟨606958, by decide⟩,⟨607034, by decide⟩]) unmarked_context_11_19212_607035 node_context_11_19212_607035
  intro a
  fin_cases a
  · exact context_12_76848_445562
  · exact context_12_76849_606882
  · exact context_12_76850_606958
  · exact context_12_76851_607034

theorem selected_cut_24034 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 76852) = some ⟨12, 1, 0, 475533, 76852, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76852_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76852 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 76852 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 76852, 1, 65536⟩
    (by decide) selected_cut_24034

theorem selected_cut_24035 : selected 8 ⟨607048, by decide⟩
    (prefixPartial 13 307412) = some ⟨13, 2, 0, 607048, 307412, 425, 16384⟩ := by
  decide +kernel

theorem context_13_307412_607048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307412 ⟨607048, by decide⟩ :=
  accepted_of_selected 13 307412 ⟨607048, by decide⟩ ⟨13, 2, 0, 607048, 307412, 425, 16384⟩
    (by decide) selected_cut_24035

theorem selected_cut_24036 : selected 8 ⟨607070, by decide⟩
    (prefixPartial 13 307413) = some ⟨13, 2, 0, 607070, 307413, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_307413_607070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307413 ⟨607070, by decide⟩ :=
  accepted_of_selected 13 307413 ⟨607070, by decide⟩ ⟨13, 2, 0, 607070, 307413, 1929, 16384⟩
    (by decide) selected_cut_24036

theorem selected_cut_24037 : selected 8 ⟨607094, by decide⟩
    (prefixPartial 13 307414) = some ⟨13, 2, 0, 607094, 307414, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_307414_607094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307414 ⟨607094, by decide⟩ :=
  accepted_of_selected 13 307414 ⟨607094, by decide⟩ ⟨13, 2, 0, 607094, 307414, 1889, 16384⟩
    (by decide) selected_cut_24037

theorem selected_cut_24038 : selected 8 ⟨607105, by decide⟩
    (prefixPartial 13 307415) = some ⟨13, 2, 0, 607105, 307415, 777, 16384⟩ := by
  decide +kernel

theorem context_13_307415_607105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307415 ⟨607105, by decide⟩ :=
  accepted_of_selected 13 307415 ⟨607105, by decide⟩ ⟨13, 2, 0, 607105, 307415, 777, 16384⟩
    (by decide) selected_cut_24038

theorem unmarked_context_12_76853_607106 : frontier 9 ⟨607106, by decide⟩
    (prefixCache 12 76853) (prefixPartial 12 76853) = false := by
  decide +kernel

theorem node_context_12_76853_607106 : EJMOriginalGlobalDAGData.nodes 9 ⟨607106, by decide⟩ =
    .split (coordinate 12) (![⟨607048, by decide⟩,⟨607070, by decide⟩,⟨607094, by decide⟩,⟨607105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76853_607106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76853 ⟨607106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76853
    ⟨607106, by decide⟩ (by decide) (![⟨607048, by decide⟩,⟨607070, by decide⟩,⟨607094, by decide⟩,⟨607105, by decide⟩]) unmarked_context_12_76853_607106 node_context_12_76853_607106
  intro a
  fin_cases a
  · exact context_13_307412_607048
  · exact context_13_307413_607070
  · exact context_13_307414_607094
  · exact context_13_307415_607105

theorem selected_cut_24039 : selected 8 ⟨607112, by decide⟩
    (prefixPartial 13 307416) = some ⟨13, 2, 0, 607112, 307416, 365, 16384⟩ := by
  decide +kernel

theorem context_13_307416_607112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307416 ⟨607112, by decide⟩ :=
  accepted_of_selected 13 307416 ⟨607112, by decide⟩ ⟨13, 2, 0, 607112, 307416, 365, 16384⟩
    (by decide) selected_cut_24039

theorem selected_cut_24040 : selected 8 ⟨607150, by decide⟩
    (prefixPartial 13 307417) = some ⟨13, 2, 0, 607150, 307417, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_307417_607150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307417 ⟨607150, by decide⟩ :=
  accepted_of_selected 13 307417 ⟨607150, by decide⟩ ⟨13, 2, 0, 607150, 307417, 2245, 16384⟩
    (by decide) selected_cut_24040

theorem selected_cut_24041 : selected 8 ⟨607174, by decide⟩
    (prefixPartial 13 307418) = some ⟨13, 2, 0, 607174, 307418, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_307418_607174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307418 ⟨607174, by decide⟩ :=
  accepted_of_selected 13 307418 ⟨607174, by decide⟩ ⟨13, 2, 0, 607174, 307418, 1565, 16384⟩
    (by decide) selected_cut_24041

theorem selected_cut_24042 : selected 8 ⟨607182, by decide⟩
    (prefixPartial 13 307419) = some ⟨13, 2, 0, 607182, 307419, 757, 16384⟩ := by
  decide +kernel

theorem context_13_307419_607182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307419 ⟨607182, by decide⟩ :=
  accepted_of_selected 13 307419 ⟨607182, by decide⟩ ⟨13, 2, 0, 607182, 307419, 757, 16384⟩
    (by decide) selected_cut_24042

theorem unmarked_context_12_76854_607183 : frontier 9 ⟨607183, by decide⟩
    (prefixCache 12 76854) (prefixPartial 12 76854) = false := by
  decide +kernel

theorem node_context_12_76854_607183 : EJMOriginalGlobalDAGData.nodes 9 ⟨607183, by decide⟩ =
    .split (coordinate 12) (![⟨607112, by decide⟩,⟨607150, by decide⟩,⟨607174, by decide⟩,⟨607182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76854_607183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76854 ⟨607183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76854
    ⟨607183, by decide⟩ (by decide) (![⟨607112, by decide⟩,⟨607150, by decide⟩,⟨607174, by decide⟩,⟨607182, by decide⟩]) unmarked_context_12_76854_607183 node_context_12_76854_607183
  intro a
  fin_cases a
  · exact context_13_307416_607112
  · exact context_13_307417_607150
  · exact context_13_307418_607174
  · exact context_13_307419_607182

theorem selected_cut_24043 : selected 8 ⟨607191, by decide⟩
    (prefixPartial 13 307420) = some ⟨13, 2, 0, 607191, 307420, 377, 16384⟩ := by
  decide +kernel

theorem context_13_307420_607191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307420 ⟨607191, by decide⟩ :=
  accepted_of_selected 13 307420 ⟨607191, by decide⟩ ⟨13, 2, 0, 607191, 307420, 377, 16384⟩
    (by decide) selected_cut_24043

theorem selected_cut_24044 : selected 8 ⟨607223, by decide⟩
    (prefixPartial 13 307421) = some ⟨13, 2, 0, 607223, 307421, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_307421_607223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307421 ⟨607223, by decide⟩ :=
  accepted_of_selected 13 307421 ⟨607223, by decide⟩ ⟨13, 2, 0, 607223, 307421, 2237, 16384⟩
    (by decide) selected_cut_24044

theorem selected_cut_24045 : selected 8 ⟨607249, by decide⟩
    (prefixPartial 13 307422) = some ⟨13, 2, 0, 607249, 307422, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_307422_607249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307422 ⟨607249, by decide⟩ :=
  accepted_of_selected 13 307422 ⟨607249, by decide⟩ ⟨13, 2, 0, 607249, 307422, 1861, 16384⟩
    (by decide) selected_cut_24045

theorem selected_cut_24046 : selected 8 ⟨607260, by decide⟩
    (prefixPartial 13 307423) = some ⟨13, 2, 0, 607260, 307423, 837, 16384⟩ := by
  decide +kernel

theorem context_13_307423_607260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307423 ⟨607260, by decide⟩ :=
  accepted_of_selected 13 307423 ⟨607260, by decide⟩ ⟨13, 2, 0, 607260, 307423, 837, 16384⟩
    (by decide) selected_cut_24046

theorem unmarked_context_12_76855_607261 : frontier 9 ⟨607261, by decide⟩
    (prefixCache 12 76855) (prefixPartial 12 76855) = false := by
  decide +kernel

theorem node_context_12_76855_607261 : EJMOriginalGlobalDAGData.nodes 9 ⟨607261, by decide⟩ =
    .split (coordinate 12) (![⟨607191, by decide⟩,⟨607223, by decide⟩,⟨607249, by decide⟩,⟨607260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76855_607261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76855 ⟨607261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76855
    ⟨607261, by decide⟩ (by decide) (![⟨607191, by decide⟩,⟨607223, by decide⟩,⟨607249, by decide⟩,⟨607260, by decide⟩]) unmarked_context_12_76855_607261 node_context_12_76855_607261
  intro a
  fin_cases a
  · exact context_13_307420_607191
  · exact context_13_307421_607223
  · exact context_13_307422_607249
  · exact context_13_307423_607260

theorem unmarked_context_11_19213_607262 : frontier 10 ⟨607262, by decide⟩
    (prefixCache 11 19213) (prefixPartial 11 19213) = false := by
  decide +kernel

theorem node_context_11_19213_607262 : EJMOriginalGlobalDAGData.nodes 10 ⟨607262, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨607106, by decide⟩,⟨607183, by decide⟩,⟨607261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19213_607262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19213 ⟨607262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19213
    ⟨607262, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨607106, by decide⟩,⟨607183, by decide⟩,⟨607261, by decide⟩]) unmarked_context_11_19213_607262 node_context_11_19213_607262
  intro a
  fin_cases a
  · exact context_12_76852_475533
  · exact context_12_76853_607106
  · exact context_12_76854_607183
  · exact context_12_76855_607261

theorem selected_cut_24047 : selected 9 ⟨540780, by decide⟩
    (prefixPartial 12 76856) = some ⟨12, 1, 0, 540780, 76856, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76856_540780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76856 ⟨540780, by decide⟩ :=
  accepted_of_selected 12 76856 ⟨540780, by decide⟩ ⟨12, 1, 0, 540780, 76856, 1, 65536⟩
    (by decide) selected_cut_24047

theorem selected_cut_24048 : selected 8 ⟨607273, by decide⟩
    (prefixPartial 13 307428) = some ⟨13, 2, 0, 607273, 307428, 409, 16384⟩ := by
  decide +kernel

theorem context_13_307428_607273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307428 ⟨607273, by decide⟩ :=
  accepted_of_selected 13 307428 ⟨607273, by decide⟩ ⟨13, 2, 0, 607273, 307428, 409, 16384⟩
    (by decide) selected_cut_24048

theorem selected_cut_24049 : selected 8 ⟨607306, by decide⟩
    (prefixPartial 13 307429) = some ⟨13, 2, 0, 607306, 307429, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_307429_607306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307429 ⟨607306, by decide⟩ :=
  accepted_of_selected 13 307429 ⟨607306, by decide⟩ ⟨13, 2, 0, 607306, 307429, 2301, 16384⟩
    (by decide) selected_cut_24049

theorem selected_cut_24050 : selected 8 ⟨607338, by decide⟩
    (prefixPartial 13 307430) = some ⟨13, 2, 0, 607338, 307430, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_307430_607338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307430 ⟨607338, by decide⟩ :=
  accepted_of_selected 13 307430 ⟨607338, by decide⟩ ⟨13, 2, 0, 607338, 307430, 1989, 16384⟩
    (by decide) selected_cut_24050

theorem selected_cut_24051 : selected 8 ⟨607345, by decide⟩
    (prefixPartial 13 307431) = some ⟨13, 2, 0, 607345, 307431, 845, 16384⟩ := by
  decide +kernel

theorem context_13_307431_607345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307431 ⟨607345, by decide⟩ :=
  accepted_of_selected 13 307431 ⟨607345, by decide⟩ ⟨13, 2, 0, 607345, 307431, 845, 16384⟩
    (by decide) selected_cut_24051

theorem unmarked_context_12_76857_607346 : frontier 9 ⟨607346, by decide⟩
    (prefixCache 12 76857) (prefixPartial 12 76857) = false := by
  decide +kernel

theorem node_context_12_76857_607346 : EJMOriginalGlobalDAGData.nodes 9 ⟨607346, by decide⟩ =
    .split (coordinate 12) (![⟨607273, by decide⟩,⟨607306, by decide⟩,⟨607338, by decide⟩,⟨607345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76857_607346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76857 ⟨607346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76857
    ⟨607346, by decide⟩ (by decide) (![⟨607273, by decide⟩,⟨607306, by decide⟩,⟨607338, by decide⟩,⟨607345, by decide⟩]) unmarked_context_12_76857_607346 node_context_12_76857_607346
  intro a
  fin_cases a
  · exact context_13_307428_607273
  · exact context_13_307429_607306
  · exact context_13_307430_607338
  · exact context_13_307431_607345

theorem selected_cut_24052 : selected 8 ⟨607352, by decide⟩
    (prefixPartial 13 307432) = some ⟨13, 2, 0, 607352, 307432, 225, 16384⟩ := by
  decide +kernel

theorem context_13_307432_607352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307432 ⟨607352, by decide⟩ :=
  accepted_of_selected 13 307432 ⟨607352, by decide⟩ ⟨13, 2, 0, 607352, 307432, 225, 16384⟩
    (by decide) selected_cut_24052

theorem selected_cut_24053 : selected 8 ⟨607385, by decide⟩
    (prefixPartial 13 307433) = some ⟨13, 2, 0, 607385, 307433, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_307433_607385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307433 ⟨607385, by decide⟩ :=
  accepted_of_selected 13 307433 ⟨607385, by decide⟩ ⟨13, 2, 0, 607385, 307433, 2161, 16384⟩
    (by decide) selected_cut_24053

theorem selected_cut_24054 : selected 8 ⟨607406, by decide⟩
    (prefixPartial 13 307434) = some ⟨13, 2, 0, 607406, 307434, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_307434_607406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307434 ⟨607406, by decide⟩ :=
  accepted_of_selected 13 307434 ⟨607406, by decide⟩ ⟨13, 2, 0, 607406, 307434, 1481, 16384⟩
    (by decide) selected_cut_24054

theorem selected_cut_24055 : selected 8 ⟨607412, by decide⟩
    (prefixPartial 13 307435) = some ⟨13, 2, 0, 607412, 307435, 757, 16384⟩ := by
  decide +kernel

theorem context_13_307435_607412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307435 ⟨607412, by decide⟩ :=
  accepted_of_selected 13 307435 ⟨607412, by decide⟩ ⟨13, 2, 0, 607412, 307435, 757, 16384⟩
    (by decide) selected_cut_24055

theorem unmarked_context_12_76858_607413 : frontier 9 ⟨607413, by decide⟩
    (prefixCache 12 76858) (prefixPartial 12 76858) = false := by
  decide +kernel

theorem node_context_12_76858_607413 : EJMOriginalGlobalDAGData.nodes 9 ⟨607413, by decide⟩ =
    .split (coordinate 12) (![⟨607352, by decide⟩,⟨607385, by decide⟩,⟨607406, by decide⟩,⟨607412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76858_607413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76858 ⟨607413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76858
    ⟨607413, by decide⟩ (by decide) (![⟨607352, by decide⟩,⟨607385, by decide⟩,⟨607406, by decide⟩,⟨607412, by decide⟩]) unmarked_context_12_76858_607413 node_context_12_76858_607413
  intro a
  fin_cases a
  · exact context_13_307432_607352
  · exact context_13_307433_607385
  · exact context_13_307434_607406
  · exact context_13_307435_607412

theorem selected_cut_24056 : selected 8 ⟨607420, by decide⟩
    (prefixPartial 13 307436) = some ⟨13, 2, 0, 607420, 307436, 213, 16384⟩ := by
  decide +kernel

theorem context_13_307436_607420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307436 ⟨607420, by decide⟩ :=
  accepted_of_selected 13 307436 ⟨607420, by decide⟩ ⟨13, 2, 0, 607420, 307436, 213, 16384⟩
    (by decide) selected_cut_24056

theorem selected_cut_24057 : selected 8 ⟨607451, by decide⟩
    (prefixPartial 13 307437) = some ⟨13, 2, 0, 607451, 307437, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_307437_607451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307437 ⟨607451, by decide⟩ :=
  accepted_of_selected 13 307437 ⟨607451, by decide⟩ ⟨13, 2, 0, 607451, 307437, 2453, 16384⟩
    (by decide) selected_cut_24057

theorem selected_cut_24058 : selected 8 ⟨607483, by decide⟩
    (prefixPartial 13 307438) = some ⟨13, 2, 0, 607483, 307438, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_307438_607483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307438 ⟨607483, by decide⟩ :=
  accepted_of_selected 13 307438 ⟨607483, by decide⟩ ⟨13, 2, 0, 607483, 307438, 1805, 16384⟩
    (by decide) selected_cut_24058

theorem selected_cut_24059 : selected 8 ⟨607494, by decide⟩
    (prefixPartial 13 307439) = some ⟨13, 2, 0, 607494, 307439, 881, 16384⟩ := by
  decide +kernel

theorem context_13_307439_607494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307439 ⟨607494, by decide⟩ :=
  accepted_of_selected 13 307439 ⟨607494, by decide⟩ ⟨13, 2, 0, 607494, 307439, 881, 16384⟩
    (by decide) selected_cut_24059

theorem unmarked_context_12_76859_607495 : frontier 9 ⟨607495, by decide⟩
    (prefixCache 12 76859) (prefixPartial 12 76859) = false := by
  decide +kernel

theorem node_context_12_76859_607495 : EJMOriginalGlobalDAGData.nodes 9 ⟨607495, by decide⟩ =
    .split (coordinate 12) (![⟨607420, by decide⟩,⟨607451, by decide⟩,⟨607483, by decide⟩,⟨607494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76859_607495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76859 ⟨607495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76859
    ⟨607495, by decide⟩ (by decide) (![⟨607420, by decide⟩,⟨607451, by decide⟩,⟨607483, by decide⟩,⟨607494, by decide⟩]) unmarked_context_12_76859_607495 node_context_12_76859_607495
  intro a
  fin_cases a
  · exact context_13_307436_607420
  · exact context_13_307437_607451
  · exact context_13_307438_607483
  · exact context_13_307439_607494

theorem unmarked_context_11_19214_607496 : frontier 10 ⟨607496, by decide⟩
    (prefixCache 11 19214) (prefixPartial 11 19214) = false := by
  decide +kernel

theorem node_context_11_19214_607496 : EJMOriginalGlobalDAGData.nodes 10 ⟨607496, by decide⟩ =
    .split (coordinate 11) (![⟨540780, by decide⟩,⟨607346, by decide⟩,⟨607413, by decide⟩,⟨607495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19214_607496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19214 ⟨607496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19214
    ⟨607496, by decide⟩ (by decide) (![⟨540780, by decide⟩,⟨607346, by decide⟩,⟨607413, by decide⟩,⟨607495, by decide⟩]) unmarked_context_11_19214_607496 node_context_11_19214_607496
  intro a
  fin_cases a
  · exact context_12_76856_540780
  · exact context_12_76857_607346
  · exact context_12_76858_607413
  · exact context_12_76859_607495

theorem selected_cut_24060 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76860) = some ⟨12, 1, 0, 445562, 76860, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76860_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76860 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76860 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76860, 1, 65536⟩
    (by decide) selected_cut_24060

theorem selected_cut_24061 : selected 8 ⟨607505, by decide⟩
    (prefixPartial 13 307444) = some ⟨13, 2, 0, 607505, 307444, 241, 16384⟩ := by
  decide +kernel

theorem context_13_307444_607505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307444 ⟨607505, by decide⟩ :=
  accepted_of_selected 13 307444 ⟨607505, by decide⟩ ⟨13, 2, 0, 607505, 307444, 241, 16384⟩
    (by decide) selected_cut_24061

theorem selected_cut_24062 : selected 8 ⟨607560, by decide⟩
    (prefixPartial 13 307445) = some ⟨13, 2, 0, 607560, 307445, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_307445_607560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307445 ⟨607560, by decide⟩ :=
  accepted_of_selected 13 307445 ⟨607560, by decide⟩ ⟨13, 2, 0, 607560, 307445, 2953, 16384⟩
    (by decide) selected_cut_24062

theorem selected_cut_24063 : selected 8 ⟨607613, by decide⟩
    (prefixPartial 13 307446) = some ⟨13, 2, 0, 607613, 307446, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_307446_607613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307446 ⟨607613, by decide⟩ :=
  accepted_of_selected 13 307446 ⟨607613, by decide⟩ ⟨13, 2, 0, 607613, 307446, 2477, 16384⟩
    (by decide) selected_cut_24063

theorem selected_cut_24064 : selected 8 ⟨607625, by decide⟩
    (prefixPartial 13 307447) = some ⟨13, 2, 0, 607625, 307447, 985, 16384⟩ := by
  decide +kernel

theorem context_13_307447_607625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307447 ⟨607625, by decide⟩ :=
  accepted_of_selected 13 307447 ⟨607625, by decide⟩ ⟨13, 2, 0, 607625, 307447, 985, 16384⟩
    (by decide) selected_cut_24064

theorem unmarked_context_12_76861_607626 : frontier 9 ⟨607626, by decide⟩
    (prefixCache 12 76861) (prefixPartial 12 76861) = false := by
  decide +kernel

theorem node_context_12_76861_607626 : EJMOriginalGlobalDAGData.nodes 9 ⟨607626, by decide⟩ =
    .split (coordinate 12) (![⟨607505, by decide⟩,⟨607560, by decide⟩,⟨607613, by decide⟩,⟨607625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76861_607626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76861 ⟨607626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76861
    ⟨607626, by decide⟩ (by decide) (![⟨607505, by decide⟩,⟨607560, by decide⟩,⟨607613, by decide⟩,⟨607625, by decide⟩]) unmarked_context_12_76861_607626 node_context_12_76861_607626
  intro a
  fin_cases a
  · exact context_13_307444_607505
  · exact context_13_307445_607560
  · exact context_13_307446_607613
  · exact context_13_307447_607625

theorem selected_cut_24065 : selected 8 ⟨607630, by decide⟩
    (prefixPartial 13 307448) = some ⟨13, 2, 0, 607630, 307448, 73, 16384⟩ := by
  decide +kernel

theorem context_13_307448_607630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307448 ⟨607630, by decide⟩ :=
  accepted_of_selected 13 307448 ⟨607630, by decide⟩ ⟨13, 2, 0, 607630, 307448, 73, 16384⟩
    (by decide) selected_cut_24065

theorem selected_cut_24066 : selected 8 ⟨607678, by decide⟩
    (prefixPartial 13 307449) = some ⟨13, 2, 0, 607678, 307449, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_307449_607678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307449 ⟨607678, by decide⟩ :=
  accepted_of_selected 13 307449 ⟨607678, by decide⟩ ⟨13, 2, 0, 607678, 307449, 2981, 16384⟩
    (by decide) selected_cut_24066

theorem selected_cut_24067 : selected 8 ⟨607704, by decide⟩
    (prefixPartial 13 307450) = some ⟨13, 2, 0, 607704, 307450, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_307450_607704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307450 ⟨607704, by decide⟩ :=
  accepted_of_selected 13 307450 ⟨607704, by decide⟩ ⟨13, 2, 0, 607704, 307450, 1909, 16384⟩
    (by decide) selected_cut_24067

theorem selected_cut_24068 : selected 8 ⟨607717, by decide⟩
    (prefixPartial 13 307451) = some ⟨13, 2, 0, 607717, 307451, 949, 16384⟩ := by
  decide +kernel

theorem context_13_307451_607717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307451 ⟨607717, by decide⟩ :=
  accepted_of_selected 13 307451 ⟨607717, by decide⟩ ⟨13, 2, 0, 607717, 307451, 949, 16384⟩
    (by decide) selected_cut_24068

theorem unmarked_context_12_76862_607718 : frontier 9 ⟨607718, by decide⟩
    (prefixCache 12 76862) (prefixPartial 12 76862) = false := by
  decide +kernel

theorem node_context_12_76862_607718 : EJMOriginalGlobalDAGData.nodes 9 ⟨607718, by decide⟩ =
    .split (coordinate 12) (![⟨607630, by decide⟩,⟨607678, by decide⟩,⟨607704, by decide⟩,⟨607717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76862_607718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76862 ⟨607718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76862
    ⟨607718, by decide⟩ (by decide) (![⟨607630, by decide⟩,⟨607678, by decide⟩,⟨607704, by decide⟩,⟨607717, by decide⟩]) unmarked_context_12_76862_607718 node_context_12_76862_607718
  intro a
  fin_cases a
  · exact context_13_307448_607630
  · exact context_13_307449_607678
  · exact context_13_307450_607704
  · exact context_13_307451_607717

theorem selected_cut_24069 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 76863) = some ⟨12, 1, 0, 607719, 76863, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76863_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76863 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 76863 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 76863, 1, 65536⟩
    (by decide) selected_cut_24069

theorem unmarked_context_11_19215_607720 : frontier 10 ⟨607720, by decide⟩
    (prefixCache 11 19215) (prefixPartial 11 19215) = false := by
  decide +kernel

theorem node_context_11_19215_607720 : EJMOriginalGlobalDAGData.nodes 10 ⟨607720, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨607626, by decide⟩,⟨607718, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19215_607720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19215 ⟨607720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19215
    ⟨607720, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨607626, by decide⟩,⟨607718, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_19215_607720 node_context_11_19215_607720
  intro a
  fin_cases a
  · exact context_12_76860_445562
  · exact context_12_76861_607626
  · exact context_12_76862_607718
  · exact context_12_76863_607719

theorem unmarked_context_10_4803_607721 : frontier 11 ⟨607721, by decide⟩
    (prefixCache 10 4803) (prefixPartial 10 4803) = false := by
  decide +kernel

theorem node_context_10_4803_607721 : EJMOriginalGlobalDAGData.nodes 11 ⟨607721, by decide⟩ =
    .split (coordinate 10) (![⟨607035, by decide⟩,⟨607262, by decide⟩,⟨607496, by decide⟩,⟨607720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4803_607721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4803 ⟨607721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4803
    ⟨607721, by decide⟩ (by decide) (![⟨607035, by decide⟩,⟨607262, by decide⟩,⟨607496, by decide⟩,⟨607720, by decide⟩]) unmarked_context_10_4803_607721 node_context_10_4803_607721
  intro a
  fin_cases a
  · exact context_11_19212_607035
  · exact context_11_19213_607262
  · exact context_11_19214_607496
  · exact context_11_19215_607720

theorem unmarked_context_9_1200_607722 : frontier 12 ⟨607722, by decide⟩
    (prefixCache 9 1200) (prefixPartial 9 1200) = false := by
  decide +kernel

theorem node_context_9_1200_607722 : EJMOriginalGlobalDAGData.nodes 12 ⟨607722, by decide⟩ =
    .split (coordinate 9) (![⟨604134, by decide⟩,⟨605653, by decide⟩,⟨606807, by decide⟩,⟨607721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1200_607722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1200 ⟨607722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1200
    ⟨607722, by decide⟩ (by decide) (![⟨604134, by decide⟩,⟨605653, by decide⟩,⟨606807, by decide⟩,⟨607721, by decide⟩]) unmarked_context_9_1200_607722 node_context_9_1200_607722
  intro a
  fin_cases a
  · exact context_10_4800_604134
  · exact context_10_4801_605653
  · exact context_10_4802_606807
  · exact context_10_4803_607721

theorem selected_cut_24070 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 76864) = some ⟨12, 1, 0, 450982, 76864, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76864_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76864 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 76864 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 76864, 1, 65536⟩
    (by decide) selected_cut_24070

theorem selected_cut_24071 : selected 9 ⟨607783, by decide⟩
    (prefixPartial 12 76865) = some ⟨12, 2, 0, 607783, 76865, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_76865_607783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76865 ⟨607783, by decide⟩ :=
  accepted_of_selected 12 76865 ⟨607783, by decide⟩ ⟨12, 2, 0, 607783, 76865, 3265, 65536⟩
    (by decide) selected_cut_24071

theorem selected_cut_24072 : selected 9 ⟨607845, by decide⟩
    (prefixPartial 12 76866) = some ⟨12, 2, 0, 607845, 76866, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_76866_607845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76866 ⟨607845, by decide⟩ :=
  accepted_of_selected 12 76866 ⟨607845, by decide⟩ ⟨12, 2, 0, 607845, 76866, 3773, 65536⟩
    (by decide) selected_cut_24072

theorem selected_cut_24073 : selected 9 ⟨607897, by decide⟩
    (prefixPartial 12 76867) = some ⟨12, 2, 0, 607897, 76867, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_76867_607897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76867 ⟨607897, by decide⟩ :=
  accepted_of_selected 12 76867 ⟨607897, by decide⟩ ⟨12, 2, 0, 607897, 76867, 3769, 65536⟩
    (by decide) selected_cut_24073

theorem unmarked_context_11_19216_607898 : frontier 10 ⟨607898, by decide⟩
    (prefixCache 11 19216) (prefixPartial 11 19216) = false := by
  decide +kernel

theorem node_context_11_19216_607898 : EJMOriginalGlobalDAGData.nodes 10 ⟨607898, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨607783, by decide⟩,⟨607845, by decide⟩,⟨607897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19216_607898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19216 ⟨607898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19216
    ⟨607898, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨607783, by decide⟩,⟨607845, by decide⟩,⟨607897, by decide⟩]) unmarked_context_11_19216_607898 node_context_11_19216_607898
  intro a
  fin_cases a
  · exact context_12_76864_450982
  · exact context_12_76865_607783
  · exact context_12_76866_607845
  · exact context_12_76867_607897

theorem selected_cut_24074 : selected 9 ⟨607955, by decide⟩
    (prefixPartial 12 76868) = some ⟨12, 2, 0, 607955, 76868, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_76868_607955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76868 ⟨607955, by decide⟩ :=
  accepted_of_selected 12 76868 ⟨607955, by decide⟩ ⟨12, 2, 0, 607955, 76868, 3089, 65536⟩
    (by decide) selected_cut_24074

theorem selected_cut_24075 : selected 9 ⟨608011, by decide⟩
    (prefixPartial 12 76869) = some ⟨12, 2, 0, 608011, 76869, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_76869_608011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76869 ⟨608011, by decide⟩ :=
  accepted_of_selected 12 76869 ⟨608011, by decide⟩ ⟨12, 2, 0, 608011, 76869, 3485, 65536⟩
    (by decide) selected_cut_24075

theorem selected_cut_24076 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307480) = some ⟨13, 1, 0, 3444, 307480, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307480_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307480 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307480 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307480, 1, 16384⟩
    (by decide) selected_cut_24076

theorem selected_cut_24077 : selected 8 ⟨608039, by decide⟩
    (prefixPartial 13 307481) = some ⟨13, 2, 0, 608039, 307481, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_307481_608039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307481 ⟨608039, by decide⟩ :=
  accepted_of_selected 13 307481 ⟨608039, by decide⟩ ⟨13, 2, 0, 608039, 307481, 1905, 16384⟩
    (by decide) selected_cut_24077

theorem selected_cut_24078 : selected 8 ⟨608064, by decide⟩
    (prefixPartial 13 307482) = some ⟨13, 2, 0, 608064, 307482, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_307482_608064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307482 ⟨608064, by decide⟩ :=
  accepted_of_selected 13 307482 ⟨608064, by decide⟩ ⟨13, 2, 0, 608064, 307482, 1489, 16384⟩
    (by decide) selected_cut_24078

theorem selected_cut_24079 : selected 8 ⟨608077, by decide⟩
    (prefixPartial 13 307483) = some ⟨13, 2, 0, 608077, 307483, 753, 16384⟩ := by
  decide +kernel

theorem context_13_307483_608077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307483 ⟨608077, by decide⟩ :=
  accepted_of_selected 13 307483 ⟨608077, by decide⟩ ⟨13, 2, 0, 608077, 307483, 753, 16384⟩
    (by decide) selected_cut_24079

theorem unmarked_context_12_76870_608078 : frontier 9 ⟨608078, by decide⟩
    (prefixCache 12 76870) (prefixPartial 12 76870) = false := by
  decide +kernel

theorem node_context_12_76870_608078 : EJMOriginalGlobalDAGData.nodes 9 ⟨608078, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨608039, by decide⟩,⟨608064, by decide⟩,⟨608077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76870_608078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76870 ⟨608078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76870
    ⟨608078, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨608039, by decide⟩,⟨608064, by decide⟩,⟨608077, by decide⟩]) unmarked_context_12_76870_608078 node_context_12_76870_608078
  intro a
  fin_cases a
  · exact context_13_307480_3444
  · exact context_13_307481_608039
  · exact context_13_307482_608064
  · exact context_13_307483_608077

theorem selected_cut_24080 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307484) = some ⟨13, 1, 0, 3444, 307484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307484, 1, 16384⟩
    (by decide) selected_cut_24080

theorem selected_cut_24081 : selected 8 ⟨608104, by decide⟩
    (prefixPartial 13 307485) = some ⟨13, 2, 0, 608104, 307485, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_307485_608104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307485 ⟨608104, by decide⟩ :=
  accepted_of_selected 13 307485 ⟨608104, by decide⟩ ⟨13, 2, 0, 608104, 307485, 1841, 16384⟩
    (by decide) selected_cut_24081

theorem selected_cut_24082 : selected 8 ⟨608125, by decide⟩
    (prefixPartial 13 307486) = some ⟨13, 2, 0, 608125, 307486, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_307486_608125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307486 ⟨608125, by decide⟩ :=
  accepted_of_selected 13 307486 ⟨608125, by decide⟩ ⟨13, 2, 0, 608125, 307486, 1585, 16384⟩
    (by decide) selected_cut_24082

theorem selected_cut_24083 : selected 8 ⟨608139, by decide⟩
    (prefixPartial 13 307487) = some ⟨13, 2, 0, 608139, 307487, 733, 16384⟩ := by
  decide +kernel

theorem context_13_307487_608139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307487 ⟨608139, by decide⟩ :=
  accepted_of_selected 13 307487 ⟨608139, by decide⟩ ⟨13, 2, 0, 608139, 307487, 733, 16384⟩
    (by decide) selected_cut_24083

theorem unmarked_context_12_76871_608140 : frontier 9 ⟨608140, by decide⟩
    (prefixCache 12 76871) (prefixPartial 12 76871) = false := by
  decide +kernel

theorem node_context_12_76871_608140 : EJMOriginalGlobalDAGData.nodes 9 ⟨608140, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨608104, by decide⟩,⟨608125, by decide⟩,⟨608139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76871_608140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76871 ⟨608140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76871
    ⟨608140, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨608104, by decide⟩,⟨608125, by decide⟩,⟨608139, by decide⟩]) unmarked_context_12_76871_608140 node_context_12_76871_608140
  intro a
  fin_cases a
  · exact context_13_307484_3444
  · exact context_13_307485_608104
  · exact context_13_307486_608125
  · exact context_13_307487_608139

theorem unmarked_context_11_19217_608141 : frontier 10 ⟨608141, by decide⟩
    (prefixCache 11 19217) (prefixPartial 11 19217) = false := by
  decide +kernel

theorem node_context_11_19217_608141 : EJMOriginalGlobalDAGData.nodes 10 ⟨608141, by decide⟩ =
    .split (coordinate 11) (![⟨607955, by decide⟩,⟨608011, by decide⟩,⟨608078, by decide⟩,⟨608140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19217_608141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19217 ⟨608141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19217
    ⟨608141, by decide⟩ (by decide) (![⟨607955, by decide⟩,⟨608011, by decide⟩,⟨608078, by decide⟩,⟨608140, by decide⟩]) unmarked_context_11_19217_608141 node_context_11_19217_608141
  intro a
  fin_cases a
  · exact context_12_76868_607955
  · exact context_12_76869_608011
  · exact context_12_76870_608078
  · exact context_12_76871_608140

theorem selected_cut_24084 : selected 9 ⟨608191, by decide⟩
    (prefixPartial 12 76872) = some ⟨12, 2, 0, 608191, 76872, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_76872_608191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76872 ⟨608191, by decide⟩ :=
  accepted_of_selected 12 76872 ⟨608191, by decide⟩ ⟨12, 2, 0, 608191, 76872, 3225, 65536⟩
    (by decide) selected_cut_24084

theorem selected_cut_24085 : selected 9 ⟨608252, by decide⟩
    (prefixPartial 12 76873) = some ⟨12, 2, 0, 608252, 76873, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_76873_608252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76873 ⟨608252, by decide⟩ :=
  accepted_of_selected 12 76873 ⟨608252, by decide⟩ ⟨12, 2, 0, 608252, 76873, 3737, 65536⟩
    (by decide) selected_cut_24085

theorem selected_cut_24086 : selected 9 ⟨608312, by decide⟩
    (prefixPartial 12 76874) = some ⟨12, 2, 0, 608312, 76874, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_76874_608312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76874 ⟨608312, by decide⟩ :=
  accepted_of_selected 12 76874 ⟨608312, by decide⟩ ⟨12, 2, 0, 608312, 76874, 3901, 65536⟩
    (by decide) selected_cut_24086

theorem selected_cut_24087 : selected 9 ⟨608373, by decide⟩
    (prefixPartial 12 76875) = some ⟨12, 2, 0, 608373, 76875, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_76875_608373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76875 ⟨608373, by decide⟩ :=
  accepted_of_selected 12 76875 ⟨608373, by decide⟩ ⟨12, 2, 0, 608373, 76875, 3977, 65536⟩
    (by decide) selected_cut_24087

theorem unmarked_context_11_19218_608374 : frontier 10 ⟨608374, by decide⟩
    (prefixCache 11 19218) (prefixPartial 11 19218) = false := by
  decide +kernel

theorem node_context_11_19218_608374 : EJMOriginalGlobalDAGData.nodes 10 ⟨608374, by decide⟩ =
    .split (coordinate 11) (![⟨608191, by decide⟩,⟨608252, by decide⟩,⟨608312, by decide⟩,⟨608373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19218_608374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19218 ⟨608374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19218
    ⟨608374, by decide⟩ (by decide) (![⟨608191, by decide⟩,⟨608252, by decide⟩,⟨608312, by decide⟩,⟨608373, by decide⟩]) unmarked_context_11_19218_608374 node_context_11_19218_608374
  intro a
  fin_cases a
  · exact context_12_76872_608191
  · exact context_12_76873_608252
  · exact context_12_76874_608312
  · exact context_12_76875_608373

theorem selected_cut_24088 : selected 9 ⟨608420, by decide⟩
    (prefixPartial 12 76876) = some ⟨12, 2, 0, 608420, 76876, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_76876_608420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76876 ⟨608420, by decide⟩ :=
  accepted_of_selected 12 76876 ⟨608420, by decide⟩ ⟨12, 2, 0, 608420, 76876, 2669, 65536⟩
    (by decide) selected_cut_24088

theorem selected_cut_24089 : selected 9 ⟨608475, by decide⟩
    (prefixPartial 12 76877) = some ⟨12, 2, 0, 608475, 76877, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_76877_608475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76877 ⟨608475, by decide⟩ :=
  accepted_of_selected 12 76877 ⟨608475, by decide⟩ ⟨12, 2, 0, 608475, 76877, 3273, 65536⟩
    (by decide) selected_cut_24089

theorem selected_cut_24090 : selected 9 ⟨608532, by decide⟩
    (prefixPartial 12 76878) = some ⟨12, 2, 0, 608532, 76878, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_76878_608532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76878 ⟨608532, by decide⟩ :=
  accepted_of_selected 12 76878 ⟨608532, by decide⟩ ⟨12, 2, 0, 608532, 76878, 3705, 65536⟩
    (by decide) selected_cut_24090

theorem selected_cut_24091 : selected 9 ⟨608585, by decide⟩
    (prefixPartial 12 76879) = some ⟨12, 2, 0, 608585, 76879, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_76879_608585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76879 ⟨608585, by decide⟩ :=
  accepted_of_selected 12 76879 ⟨608585, by decide⟩ ⟨12, 2, 0, 608585, 76879, 3541, 65536⟩
    (by decide) selected_cut_24091

theorem unmarked_context_11_19219_608586 : frontier 10 ⟨608586, by decide⟩
    (prefixCache 11 19219) (prefixPartial 11 19219) = false := by
  decide +kernel

theorem node_context_11_19219_608586 : EJMOriginalGlobalDAGData.nodes 10 ⟨608586, by decide⟩ =
    .split (coordinate 11) (![⟨608420, by decide⟩,⟨608475, by decide⟩,⟨608532, by decide⟩,⟨608585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19219_608586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19219 ⟨608586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19219
    ⟨608586, by decide⟩ (by decide) (![⟨608420, by decide⟩,⟨608475, by decide⟩,⟨608532, by decide⟩,⟨608585, by decide⟩]) unmarked_context_11_19219_608586 node_context_11_19219_608586
  intro a
  fin_cases a
  · exact context_12_76876_608420
  · exact context_12_76877_608475
  · exact context_12_76878_608532
  · exact context_12_76879_608585

theorem unmarked_context_10_4804_608587 : frontier 11 ⟨608587, by decide⟩
    (prefixCache 10 4804) (prefixPartial 10 4804) = false := by
  decide +kernel

theorem node_context_10_4804_608587 : EJMOriginalGlobalDAGData.nodes 11 ⟨608587, by decide⟩ =
    .split (coordinate 10) (![⟨607898, by decide⟩,⟨608141, by decide⟩,⟨608374, by decide⟩,⟨608586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4804_608587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4804 ⟨608587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4804
    ⟨608587, by decide⟩ (by decide) (![⟨607898, by decide⟩,⟨608141, by decide⟩,⟨608374, by decide⟩,⟨608586, by decide⟩]) unmarked_context_10_4804_608587 node_context_10_4804_608587
  intro a
  fin_cases a
  · exact context_11_19216_607898
  · exact context_11_19217_608141
  · exact context_11_19218_608374
  · exact context_11_19219_608586

theorem selected_cut_24092 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 76880) = some ⟨12, 1, 0, 266170, 76880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76880_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76880 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 76880 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 76880, 1, 65536⟩
    (by decide) selected_cut_24092

theorem selected_cut_24093 : selected 9 ⟨608648, by decide⟩
    (prefixPartial 12 76881) = some ⟨12, 2, 0, 608648, 76881, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_76881_608648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76881 ⟨608648, by decide⟩ :=
  accepted_of_selected 12 76881 ⟨608648, by decide⟩ ⟨12, 2, 0, 608648, 76881, 3961, 65536⟩
    (by decide) selected_cut_24093

theorem selected_cut_24094 : selected 9 ⟨608699, by decide⟩
    (prefixPartial 12 76882) = some ⟨12, 2, 0, 608699, 76882, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_76882_608699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76882 ⟨608699, by decide⟩ :=
  accepted_of_selected 12 76882 ⟨608699, by decide⟩ ⟨12, 2, 0, 608699, 76882, 4061, 65536⟩
    (by decide) selected_cut_24094

theorem selected_cut_24095 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 307532) = some ⟨13, 1, 0, 3444, 307532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_307532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 307532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 307532, 1, 16384⟩
    (by decide) selected_cut_24095

theorem selected_cut_24096 : selected 8 ⟨608720, by decide⟩
    (prefixPartial 13 307533) = some ⟨13, 2, 0, 608720, 307533, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_307533_608720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307533 ⟨608720, by decide⟩ :=
  accepted_of_selected 13 307533 ⟨608720, by decide⟩ ⟨13, 2, 0, 608720, 307533, 1793, 16384⟩
    (by decide) selected_cut_24096

theorem selected_cut_24097 : selected 8 ⟨608738, by decide⟩
    (prefixPartial 13 307534) = some ⟨13, 2, 0, 608738, 307534, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_307534_608738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307534 ⟨608738, by decide⟩ :=
  accepted_of_selected 13 307534 ⟨608738, by decide⟩ ⟨13, 2, 0, 608738, 307534, 1725, 16384⟩
    (by decide) selected_cut_24097

theorem selected_cut_24098 : selected 8 ⟨608747, by decide⟩
    (prefixPartial 13 307535) = some ⟨13, 2, 0, 608747, 307535, 773, 16384⟩ := by
  decide +kernel

theorem context_13_307535_608747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 307535 ⟨608747, by decide⟩ :=
  accepted_of_selected 13 307535 ⟨608747, by decide⟩ ⟨13, 2, 0, 608747, 307535, 773, 16384⟩
    (by decide) selected_cut_24098

theorem unmarked_context_12_76883_608748 : frontier 9 ⟨608748, by decide⟩
    (prefixCache 12 76883) (prefixPartial 12 76883) = false := by
  decide +kernel

theorem node_context_12_76883_608748 : EJMOriginalGlobalDAGData.nodes 9 ⟨608748, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨608720, by decide⟩,⟨608738, by decide⟩,⟨608747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76883_608748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76883 ⟨608748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76883
    ⟨608748, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨608720, by decide⟩,⟨608738, by decide⟩,⟨608747, by decide⟩]) unmarked_context_12_76883_608748 node_context_12_76883_608748
  intro a
  fin_cases a
  · exact context_13_307532_3444
  · exact context_13_307533_608720
  · exact context_13_307534_608738
  · exact context_13_307535_608747

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
