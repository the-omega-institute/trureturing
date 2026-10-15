/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover451
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43394 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 349712) = some ⟨12, 1, 0, 435160, 349712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349712_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349712 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 349712 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 349712, 1, 65536⟩
    (by decide) selected_cut_43394

theorem selected_cut_43395 : selected 9 ⟨1187273, by decide⟩
    (prefixPartial 12 349713) = some ⟨12, 2, 0, 1187273, 349713, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_349713_1187273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349713 ⟨1187273, by decide⟩ :=
  accepted_of_selected 12 349713 ⟨1187273, by decide⟩ ⟨12, 2, 0, 1187273, 349713, 1989, 65536⟩
    (by decide) selected_cut_43395

theorem selected_cut_43396 : selected 9 ⟨1187313, by decide⟩
    (prefixPartial 12 349714) = some ⟨12, 2, 0, 1187313, 349714, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_349714_1187313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349714 ⟨1187313, by decide⟩ :=
  accepted_of_selected 12 349714 ⟨1187313, by decide⟩ ⟨12, 2, 0, 1187313, 349714, 2425, 65536⟩
    (by decide) selected_cut_43396

theorem selected_cut_43397 : selected 9 ⟨1187371, by decide⟩
    (prefixPartial 12 349715) = some ⟨12, 2, 0, 1187371, 349715, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_349715_1187371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349715 ⟨1187371, by decide⟩ :=
  accepted_of_selected 12 349715 ⟨1187371, by decide⟩ ⟨12, 2, 0, 1187371, 349715, 2821, 65536⟩
    (by decide) selected_cut_43397

theorem unmarked_context_11_87428_1187372 : frontier 10 ⟨1187372, by decide⟩
    (prefixCache 11 87428) (prefixPartial 11 87428) = false := by
  decide +kernel

theorem node_context_11_87428_1187372 : EJMOriginalGlobalDAGData.nodes 10 ⟨1187372, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1187273, by decide⟩,⟨1187313, by decide⟩,⟨1187371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87428_1187372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87428 ⟨1187372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87428
    ⟨1187372, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1187273, by decide⟩,⟨1187313, by decide⟩,⟨1187371, by decide⟩]) unmarked_context_11_87428_1187372 node_context_11_87428_1187372
  intro a
  fin_cases a
  · exact context_12_349712_435160
  · exact context_12_349713_1187273
  · exact context_12_349714_1187313
  · exact context_12_349715_1187371

theorem selected_cut_43398 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 87429) = some ⟨11, 1, 0, 892405, 87429, 1, 262144⟩ := by
  decide +kernel

theorem context_11_87429_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87429 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 87429 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 87429, 1, 262144⟩
    (by decide) selected_cut_43398

theorem selected_cut_43399 : selected 9 ⟨1187423, by decide⟩
    (prefixPartial 12 349720) = some ⟨12, 2, 0, 1187423, 349720, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_349720_1187423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349720 ⟨1187423, by decide⟩ :=
  accepted_of_selected 12 349720 ⟨1187423, by decide⟩ ⟨12, 2, 0, 1187423, 349720, 2521, 65536⟩
    (by decide) selected_cut_43399

theorem selected_cut_43400 : selected 9 ⟨1187458, by decide⟩
    (prefixPartial 12 349721) = some ⟨12, 2, 0, 1187458, 349721, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_349721_1187458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349721 ⟨1187458, by decide⟩ :=
  accepted_of_selected 12 349721 ⟨1187458, by decide⟩ ⟨12, 2, 0, 1187458, 349721, 1813, 65536⟩
    (by decide) selected_cut_43400

theorem selected_cut_43401 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 349722) = some ⟨12, 1, 0, 893903, 349722, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349722_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349722 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 349722 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 349722, 1, 65536⟩
    (by decide) selected_cut_43401

theorem selected_cut_43402 : selected 9 ⟨1187508, by decide⟩
    (prefixPartial 12 349723) = some ⟨12, 2, 0, 1187508, 349723, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_349723_1187508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349723 ⟨1187508, by decide⟩ :=
  accepted_of_selected 12 349723 ⟨1187508, by decide⟩ ⟨12, 2, 0, 1187508, 349723, 2761, 65536⟩
    (by decide) selected_cut_43402

theorem unmarked_context_11_87430_1187509 : frontier 10 ⟨1187509, by decide⟩
    (prefixCache 11 87430) (prefixPartial 11 87430) = false := by
  decide +kernel

theorem node_context_11_87430_1187509 : EJMOriginalGlobalDAGData.nodes 10 ⟨1187509, by decide⟩ =
    .split (coordinate 11) (![⟨1187423, by decide⟩,⟨1187458, by decide⟩,⟨893903, by decide⟩,⟨1187508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87430_1187509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87430 ⟨1187509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87430
    ⟨1187509, by decide⟩ (by decide) (![⟨1187423, by decide⟩,⟨1187458, by decide⟩,⟨893903, by decide⟩,⟨1187508, by decide⟩]) unmarked_context_11_87430_1187509 node_context_11_87430_1187509
  intro a
  fin_cases a
  · exact context_12_349720_1187423
  · exact context_12_349721_1187458
  · exact context_12_349722_893903
  · exact context_12_349723_1187508

theorem selected_cut_43403 : selected 9 ⟨1187558, by decide⟩
    (prefixPartial 12 349724) = some ⟨12, 2, 0, 1187558, 349724, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_349724_1187558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349724 ⟨1187558, by decide⟩ :=
  accepted_of_selected 12 349724 ⟨1187558, by decide⟩ ⟨12, 2, 0, 1187558, 349724, 2541, 65536⟩
    (by decide) selected_cut_43403

theorem selected_cut_43404 : selected 9 ⟨1187584, by decide⟩
    (prefixPartial 12 349725) = some ⟨12, 2, 0, 1187584, 349725, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_349725_1187584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349725 ⟨1187584, by decide⟩ :=
  accepted_of_selected 12 349725 ⟨1187584, by decide⟩ ⟨12, 2, 0, 1187584, 349725, 1777, 65536⟩
    (by decide) selected_cut_43404

theorem selected_cut_43405 : selected 9 ⟨1187620, by decide⟩
    (prefixPartial 12 349726) = some ⟨12, 2, 0, 1187620, 349726, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_349726_1187620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349726 ⟨1187620, by decide⟩ :=
  accepted_of_selected 12 349726 ⟨1187620, by decide⟩ ⟨12, 2, 0, 1187620, 349726, 2293, 65536⟩
    (by decide) selected_cut_43405

theorem selected_cut_43406 : selected 9 ⟨1187653, by decide⟩
    (prefixPartial 12 349727) = some ⟨12, 2, 0, 1187653, 349727, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_349727_1187653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349727 ⟨1187653, by decide⟩ :=
  accepted_of_selected 12 349727 ⟨1187653, by decide⟩ ⟨12, 2, 0, 1187653, 349727, 2197, 65536⟩
    (by decide) selected_cut_43406

theorem unmarked_context_11_87431_1187654 : frontier 10 ⟨1187654, by decide⟩
    (prefixCache 11 87431) (prefixPartial 11 87431) = false := by
  decide +kernel

theorem node_context_11_87431_1187654 : EJMOriginalGlobalDAGData.nodes 10 ⟨1187654, by decide⟩ =
    .split (coordinate 11) (![⟨1187558, by decide⟩,⟨1187584, by decide⟩,⟨1187620, by decide⟩,⟨1187653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87431_1187654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87431 ⟨1187654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87431
    ⟨1187654, by decide⟩ (by decide) (![⟨1187558, by decide⟩,⟨1187584, by decide⟩,⟨1187620, by decide⟩,⟨1187653, by decide⟩]) unmarked_context_11_87431_1187654 node_context_11_87431_1187654
  intro a
  fin_cases a
  · exact context_12_349724_1187558
  · exact context_12_349725_1187584
  · exact context_12_349726_1187620
  · exact context_12_349727_1187653

theorem unmarked_context_10_21857_1187655 : frontier 11 ⟨1187655, by decide⟩
    (prefixCache 10 21857) (prefixPartial 10 21857) = false := by
  decide +kernel

theorem node_context_10_21857_1187655 : EJMOriginalGlobalDAGData.nodes 11 ⟨1187655, by decide⟩ =
    .split (coordinate 10) (![⟨1187372, by decide⟩,⟨892405, by decide⟩,⟨1187509, by decide⟩,⟨1187654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21857_1187655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21857 ⟨1187655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21857
    ⟨1187655, by decide⟩ (by decide) (![⟨1187372, by decide⟩,⟨892405, by decide⟩,⟨1187509, by decide⟩,⟨1187654, by decide⟩]) unmarked_context_10_21857_1187655 node_context_10_21857_1187655
  intro a
  fin_cases a
  · exact context_11_87428_1187372
  · exact context_11_87429_892405
  · exact context_11_87430_1187509
  · exact context_11_87431_1187654

theorem selected_cut_43407 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 349728) = some ⟨12, 1, 0, 1187656, 349728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349728_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349728 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 349728 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 349728, 1, 65536⟩
    (by decide) selected_cut_43407

theorem selected_cut_43408 : selected 9 ⟨1187686, by decide⟩
    (prefixPartial 12 349729) = some ⟨12, 2, 0, 1187686, 349729, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_349729_1187686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349729 ⟨1187686, by decide⟩ :=
  accepted_of_selected 12 349729 ⟨1187686, by decide⟩ ⟨12, 2, 0, 1187686, 349729, 1873, 65536⟩
    (by decide) selected_cut_43408

theorem selected_cut_43409 : selected 9 ⟨1187726, by decide⟩
    (prefixPartial 12 349730) = some ⟨12, 2, 0, 1187726, 349730, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_349730_1187726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349730 ⟨1187726, by decide⟩ :=
  accepted_of_selected 12 349730 ⟨1187726, by decide⟩ ⟨12, 2, 0, 1187726, 349730, 2089, 65536⟩
    (by decide) selected_cut_43409

theorem selected_cut_43410 : selected 9 ⟨1187767, by decide⟩
    (prefixPartial 12 349731) = some ⟨12, 2, 0, 1187767, 349731, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_349731_1187767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349731 ⟨1187767, by decide⟩ :=
  accepted_of_selected 12 349731 ⟨1187767, by decide⟩ ⟨12, 2, 0, 1187767, 349731, 2229, 65536⟩
    (by decide) selected_cut_43410

theorem unmarked_context_11_87432_1187768 : frontier 10 ⟨1187768, by decide⟩
    (prefixCache 11 87432) (prefixPartial 11 87432) = false := by
  decide +kernel

theorem node_context_11_87432_1187768 : EJMOriginalGlobalDAGData.nodes 10 ⟨1187768, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1187686, by decide⟩,⟨1187726, by decide⟩,⟨1187767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87432_1187768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87432 ⟨1187768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87432
    ⟨1187768, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1187686, by decide⟩,⟨1187726, by decide⟩,⟨1187767, by decide⟩]) unmarked_context_11_87432_1187768 node_context_11_87432_1187768
  intro a
  fin_cases a
  · exact context_12_349728_1187656
  · exact context_12_349729_1187686
  · exact context_12_349730_1187726
  · exact context_12_349731_1187767

theorem selected_cut_43411 : selected 9 ⟨1187804, by decide⟩
    (prefixPartial 12 349732) = some ⟨12, 2, 0, 1187804, 349732, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_349732_1187804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349732 ⟨1187804, by decide⟩ :=
  accepted_of_selected 12 349732 ⟨1187804, by decide⟩ ⟨12, 2, 0, 1187804, 349732, 1717, 65536⟩
    (by decide) selected_cut_43411

theorem selected_cut_43412 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 349733) = some ⟨12, 1, 0, 688903, 349733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349733_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349733 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 349733 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 349733, 1, 65536⟩
    (by decide) selected_cut_43412

theorem selected_cut_43413 : selected 9 ⟨1187832, by decide⟩
    (prefixPartial 12 349734) = some ⟨12, 2, 0, 1187832, 349734, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_349734_1187832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349734 ⟨1187832, by decide⟩ :=
  accepted_of_selected 12 349734 ⟨1187832, by decide⟩ ⟨12, 2, 0, 1187832, 349734, 1657, 65536⟩
    (by decide) selected_cut_43413

theorem selected_cut_43414 : selected 9 ⟨1187868, by decide⟩
    (prefixPartial 12 349735) = some ⟨12, 2, 0, 1187868, 349735, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_349735_1187868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349735 ⟨1187868, by decide⟩ :=
  accepted_of_selected 12 349735 ⟨1187868, by decide⟩ ⟨12, 2, 0, 1187868, 349735, 1729, 65536⟩
    (by decide) selected_cut_43414

theorem unmarked_context_11_87433_1187869 : frontier 10 ⟨1187869, by decide⟩
    (prefixCache 11 87433) (prefixPartial 11 87433) = false := by
  decide +kernel

theorem node_context_11_87433_1187869 : EJMOriginalGlobalDAGData.nodes 10 ⟨1187869, by decide⟩ =
    .split (coordinate 11) (![⟨1187804, by decide⟩,⟨688903, by decide⟩,⟨1187832, by decide⟩,⟨1187868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87433_1187869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87433 ⟨1187869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87433
    ⟨1187869, by decide⟩ (by decide) (![⟨1187804, by decide⟩,⟨688903, by decide⟩,⟨1187832, by decide⟩,⟨1187868, by decide⟩]) unmarked_context_11_87433_1187869 node_context_11_87433_1187869
  intro a
  fin_cases a
  · exact context_12_349732_1187804
  · exact context_12_349733_688903
  · exact context_12_349734_1187832
  · exact context_12_349735_1187868

theorem selected_cut_43415 : selected 9 ⟨1187910, by decide⟩
    (prefixPartial 12 349736) = some ⟨12, 2, 0, 1187910, 349736, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_349736_1187910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349736 ⟨1187910, by decide⟩ :=
  accepted_of_selected 12 349736 ⟨1187910, by decide⟩ ⟨12, 2, 0, 1187910, 349736, 2101, 65536⟩
    (by decide) selected_cut_43415

theorem selected_cut_43416 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 349737) = some ⟨12, 1, 0, 661671, 349737, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349737_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349737 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 349737 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 349737, 1, 65536⟩
    (by decide) selected_cut_43416

theorem selected_cut_43417 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 349738) = some ⟨12, 1, 0, 1113261, 349738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349738_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349738 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 349738 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 349738, 1, 65536⟩
    (by decide) selected_cut_43417

theorem selected_cut_43418 : selected 9 ⟨1187949, by decide⟩
    (prefixPartial 12 349739) = some ⟨12, 2, 0, 1187949, 349739, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_349739_1187949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349739 ⟨1187949, by decide⟩ :=
  accepted_of_selected 12 349739 ⟨1187949, by decide⟩ ⟨12, 2, 0, 1187949, 349739, 2177, 65536⟩
    (by decide) selected_cut_43418

theorem unmarked_context_11_87434_1187950 : frontier 10 ⟨1187950, by decide⟩
    (prefixCache 11 87434) (prefixPartial 11 87434) = false := by
  decide +kernel

theorem node_context_11_87434_1187950 : EJMOriginalGlobalDAGData.nodes 10 ⟨1187950, by decide⟩ =
    .split (coordinate 11) (![⟨1187910, by decide⟩,⟨661671, by decide⟩,⟨1113261, by decide⟩,⟨1187949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87434_1187950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87434 ⟨1187950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87434
    ⟨1187950, by decide⟩ (by decide) (![⟨1187910, by decide⟩,⟨661671, by decide⟩,⟨1113261, by decide⟩,⟨1187949, by decide⟩]) unmarked_context_11_87434_1187950 node_context_11_87434_1187950
  intro a
  fin_cases a
  · exact context_12_349736_1187910
  · exact context_12_349737_661671
  · exact context_12_349738_1113261
  · exact context_12_349739_1187949

theorem selected_cut_43419 : selected 9 ⟨1187989, by decide⟩
    (prefixPartial 12 349740) = some ⟨12, 2, 0, 1187989, 349740, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_349740_1187989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349740 ⟨1187989, by decide⟩ :=
  accepted_of_selected 12 349740 ⟨1187989, by decide⟩ ⟨12, 2, 0, 1187989, 349740, 2021, 65536⟩
    (by decide) selected_cut_43419

theorem selected_cut_43420 : selected 9 ⟨1188016, by decide⟩
    (prefixPartial 12 349741) = some ⟨12, 2, 0, 1188016, 349741, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_349741_1188016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349741 ⟨1188016, by decide⟩ :=
  accepted_of_selected 12 349741 ⟨1188016, by decide⟩ ⟨12, 2, 0, 1188016, 349741, 1573, 65536⟩
    (by decide) selected_cut_43420

theorem selected_cut_43421 : selected 9 ⟨1188044, by decide⟩
    (prefixPartial 12 349742) = some ⟨12, 2, 0, 1188044, 349742, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_349742_1188044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349742 ⟨1188044, by decide⟩ :=
  accepted_of_selected 12 349742 ⟨1188044, by decide⟩ ⟨12, 2, 0, 1188044, 349742, 1885, 65536⟩
    (by decide) selected_cut_43421

theorem selected_cut_43422 : selected 9 ⟨1188072, by decide⟩
    (prefixPartial 12 349743) = some ⟨12, 2, 0, 1188072, 349743, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_349743_1188072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349743 ⟨1188072, by decide⟩ :=
  accepted_of_selected 12 349743 ⟨1188072, by decide⟩ ⟨12, 2, 0, 1188072, 349743, 1769, 65536⟩
    (by decide) selected_cut_43422

theorem unmarked_context_11_87435_1188073 : frontier 10 ⟨1188073, by decide⟩
    (prefixCache 11 87435) (prefixPartial 11 87435) = false := by
  decide +kernel

theorem node_context_11_87435_1188073 : EJMOriginalGlobalDAGData.nodes 10 ⟨1188073, by decide⟩ =
    .split (coordinate 11) (![⟨1187989, by decide⟩,⟨1188016, by decide⟩,⟨1188044, by decide⟩,⟨1188072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87435_1188073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87435 ⟨1188073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87435
    ⟨1188073, by decide⟩ (by decide) (![⟨1187989, by decide⟩,⟨1188016, by decide⟩,⟨1188044, by decide⟩,⟨1188072, by decide⟩]) unmarked_context_11_87435_1188073 node_context_11_87435_1188073
  intro a
  fin_cases a
  · exact context_12_349740_1187989
  · exact context_12_349741_1188016
  · exact context_12_349742_1188044
  · exact context_12_349743_1188072

theorem unmarked_context_10_21858_1188074 : frontier 11 ⟨1188074, by decide⟩
    (prefixCache 10 21858) (prefixPartial 10 21858) = false := by
  decide +kernel

theorem node_context_10_21858_1188074 : EJMOriginalGlobalDAGData.nodes 11 ⟨1188074, by decide⟩ =
    .split (coordinate 10) (![⟨1187768, by decide⟩,⟨1187869, by decide⟩,⟨1187950, by decide⟩,⟨1188073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21858_1188074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21858 ⟨1188074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21858
    ⟨1188074, by decide⟩ (by decide) (![⟨1187768, by decide⟩,⟨1187869, by decide⟩,⟨1187950, by decide⟩,⟨1188073, by decide⟩]) unmarked_context_10_21858_1188074 node_context_10_21858_1188074
  intro a
  fin_cases a
  · exact context_11_87432_1187768
  · exact context_11_87433_1187869
  · exact context_11_87434_1187950
  · exact context_11_87435_1188073

theorem selected_cut_43423 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 349744) = some ⟨12, 1, 0, 1187656, 349744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349744_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349744 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 349744 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 349744, 1, 65536⟩
    (by decide) selected_cut_43423

theorem selected_cut_43424 : selected 9 ⟨1188105, by decide⟩
    (prefixPartial 12 349745) = some ⟨12, 2, 0, 1188105, 349745, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_349745_1188105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349745 ⟨1188105, by decide⟩ :=
  accepted_of_selected 12 349745 ⟨1188105, by decide⟩ ⟨12, 2, 0, 1188105, 349745, 1477, 65536⟩
    (by decide) selected_cut_43424

theorem selected_cut_43425 : selected 9 ⟨1188140, by decide⟩
    (prefixPartial 12 349746) = some ⟨12, 2, 0, 1188140, 349746, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_349746_1188140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349746 ⟨1188140, by decide⟩ :=
  accepted_of_selected 12 349746 ⟨1188140, by decide⟩ ⟨12, 2, 0, 1188140, 349746, 1589, 65536⟩
    (by decide) selected_cut_43425

theorem selected_cut_43426 : selected 9 ⟨1188177, by decide⟩
    (prefixPartial 12 349747) = some ⟨12, 2, 0, 1188177, 349747, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_349747_1188177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349747 ⟨1188177, by decide⟩ :=
  accepted_of_selected 12 349747 ⟨1188177, by decide⟩ ⟨12, 2, 0, 1188177, 349747, 1705, 65536⟩
    (by decide) selected_cut_43426

theorem unmarked_context_11_87436_1188178 : frontier 10 ⟨1188178, by decide⟩
    (prefixCache 11 87436) (prefixPartial 11 87436) = false := by
  decide +kernel

theorem node_context_11_87436_1188178 : EJMOriginalGlobalDAGData.nodes 10 ⟨1188178, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1188105, by decide⟩,⟨1188140, by decide⟩,⟨1188177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87436_1188178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87436 ⟨1188178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87436
    ⟨1188178, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1188105, by decide⟩,⟨1188140, by decide⟩,⟨1188177, by decide⟩]) unmarked_context_11_87436_1188178 node_context_11_87436_1188178
  intro a
  fin_cases a
  · exact context_12_349744_1187656
  · exact context_12_349745_1188105
  · exact context_12_349746_1188140
  · exact context_12_349747_1188177

theorem selected_cut_43427 : selected 9 ⟨1188204, by decide⟩
    (prefixPartial 12 349748) = some ⟨12, 2, 0, 1188204, 349748, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_349748_1188204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349748 ⟨1188204, by decide⟩ :=
  accepted_of_selected 12 349748 ⟨1188204, by decide⟩ ⟨12, 2, 0, 1188204, 349748, 1257, 65536⟩
    (by decide) selected_cut_43427

theorem selected_cut_43428 : selected 9 ⟨1188224, by decide⟩
    (prefixPartial 12 349749) = some ⟨12, 2, 0, 1188224, 349749, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_349749_1188224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349749 ⟨1188224, by decide⟩ :=
  accepted_of_selected 12 349749 ⟨1188224, by decide⟩ ⟨12, 2, 0, 1188224, 349749, 1257, 65536⟩
    (by decide) selected_cut_43428

theorem selected_cut_43429 : selected 9 ⟨1188252, by decide⟩
    (prefixPartial 12 349750) = some ⟨12, 2, 0, 1188252, 349750, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_349750_1188252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349750 ⟨1188252, by decide⟩ :=
  accepted_of_selected 12 349750 ⟨1188252, by decide⟩ ⟨12, 2, 0, 1188252, 349750, 1257, 65536⟩
    (by decide) selected_cut_43429

theorem selected_cut_43430 : selected 9 ⟨1188279, by decide⟩
    (prefixPartial 12 349751) = some ⟨12, 2, 0, 1188279, 349751, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_349751_1188279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349751 ⟨1188279, by decide⟩ :=
  accepted_of_selected 12 349751 ⟨1188279, by decide⟩ ⟨12, 2, 0, 1188279, 349751, 1289, 65536⟩
    (by decide) selected_cut_43430

theorem unmarked_context_11_87437_1188280 : frontier 10 ⟨1188280, by decide⟩
    (prefixCache 11 87437) (prefixPartial 11 87437) = false := by
  decide +kernel

theorem node_context_11_87437_1188280 : EJMOriginalGlobalDAGData.nodes 10 ⟨1188280, by decide⟩ =
    .split (coordinate 11) (![⟨1188204, by decide⟩,⟨1188224, by decide⟩,⟨1188252, by decide⟩,⟨1188279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87437_1188280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87437 ⟨1188280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87437
    ⟨1188280, by decide⟩ (by decide) (![⟨1188204, by decide⟩,⟨1188224, by decide⟩,⟨1188252, by decide⟩,⟨1188279, by decide⟩]) unmarked_context_11_87437_1188280 node_context_11_87437_1188280
  intro a
  fin_cases a
  · exact context_12_349748_1188204
  · exact context_12_349749_1188224
  · exact context_12_349750_1188252
  · exact context_12_349751_1188279

theorem selected_cut_43431 : selected 9 ⟨1188314, by decide⟩
    (prefixPartial 12 349752) = some ⟨12, 2, 0, 1188314, 349752, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_349752_1188314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349752 ⟨1188314, by decide⟩ :=
  accepted_of_selected 12 349752 ⟨1188314, by decide⟩ ⟨12, 2, 0, 1188314, 349752, 1521, 65536⟩
    (by decide) selected_cut_43431

theorem selected_cut_43432 : selected 9 ⟨1188340, by decide⟩
    (prefixPartial 12 349753) = some ⟨12, 2, 0, 1188340, 349753, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_349753_1188340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349753 ⟨1188340, by decide⟩ :=
  accepted_of_selected 12 349753 ⟨1188340, by decide⟩ ⟨12, 2, 0, 1188340, 349753, 1245, 65536⟩
    (by decide) selected_cut_43432

theorem selected_cut_43433 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 349754) = some ⟨12, 1, 0, 893903, 349754, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349754_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349754 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 349754 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 349754, 1, 65536⟩
    (by decide) selected_cut_43433

theorem selected_cut_43434 : selected 9 ⟨1188378, by decide⟩
    (prefixPartial 12 349755) = some ⟨12, 2, 0, 1188378, 349755, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_349755_1188378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349755 ⟨1188378, by decide⟩ :=
  accepted_of_selected 12 349755 ⟨1188378, by decide⟩ ⟨12, 2, 0, 1188378, 349755, 1665, 65536⟩
    (by decide) selected_cut_43434

theorem unmarked_context_11_87438_1188379 : frontier 10 ⟨1188379, by decide⟩
    (prefixCache 11 87438) (prefixPartial 11 87438) = false := by
  decide +kernel

theorem node_context_11_87438_1188379 : EJMOriginalGlobalDAGData.nodes 10 ⟨1188379, by decide⟩ =
    .split (coordinate 11) (![⟨1188314, by decide⟩,⟨1188340, by decide⟩,⟨893903, by decide⟩,⟨1188378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87438_1188379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87438 ⟨1188379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87438
    ⟨1188379, by decide⟩ (by decide) (![⟨1188314, by decide⟩,⟨1188340, by decide⟩,⟨893903, by decide⟩,⟨1188378, by decide⟩]) unmarked_context_11_87438_1188379 node_context_11_87438_1188379
  intro a
  fin_cases a
  · exact context_12_349752_1188314
  · exact context_12_349753_1188340
  · exact context_12_349754_893903
  · exact context_12_349755_1188378

theorem selected_cut_43435 : selected 10 ⟨1188458, by decide⟩
    (prefixPartial 11 87439) = some ⟨11, 2, 0, 1188458, 87439, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_87439_1188458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87439 ⟨1188458, by decide⟩ :=
  accepted_of_selected 11 87439 ⟨1188458, by decide⟩ ⟨11, 2, 0, 1188458, 87439, 3785, 262144⟩
    (by decide) selected_cut_43435

theorem unmarked_context_10_21859_1188459 : frontier 11 ⟨1188459, by decide⟩
    (prefixCache 10 21859) (prefixPartial 10 21859) = false := by
  decide +kernel

theorem node_context_10_21859_1188459 : EJMOriginalGlobalDAGData.nodes 11 ⟨1188459, by decide⟩ =
    .split (coordinate 10) (![⟨1188178, by decide⟩,⟨1188280, by decide⟩,⟨1188379, by decide⟩,⟨1188458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21859_1188459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21859 ⟨1188459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21859
    ⟨1188459, by decide⟩ (by decide) (![⟨1188178, by decide⟩,⟨1188280, by decide⟩,⟨1188379, by decide⟩,⟨1188458, by decide⟩]) unmarked_context_10_21859_1188459 node_context_10_21859_1188459
  intro a
  fin_cases a
  · exact context_11_87436_1188178
  · exact context_11_87437_1188280
  · exact context_11_87438_1188379
  · exact context_11_87439_1188458

theorem unmarked_context_9_5464_1188460 : frontier 12 ⟨1188460, by decide⟩
    (prefixCache 9 5464) (prefixPartial 9 5464) = false := by
  decide +kernel

theorem node_context_9_5464_1188460 : EJMOriginalGlobalDAGData.nodes 12 ⟨1188460, by decide⟩ =
    .split (coordinate 9) (![⟨1187231, by decide⟩,⟨1187655, by decide⟩,⟨1188074, by decide⟩,⟨1188459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5464_1188460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5464 ⟨1188460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5464
    ⟨1188460, by decide⟩ (by decide) (![⟨1187231, by decide⟩,⟨1187655, by decide⟩,⟨1188074, by decide⟩,⟨1188459, by decide⟩]) unmarked_context_9_5464_1188460 node_context_9_5464_1188460
  intro a
  fin_cases a
  · exact context_10_21856_1187231
  · exact context_10_21857_1187655
  · exact context_10_21858_1188074
  · exact context_10_21859_1188459

theorem selected_cut_43436 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 21860) = some ⟨10, 1, 0, 3442, 21860, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21860_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21860 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 21860 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 21860, 1, 1048576⟩
    (by decide) selected_cut_43436

theorem selected_cut_43437 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21861) = some ⟨10, 1, 0, 893098, 21861, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21861_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21861 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21861 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21861, 1, 1048576⟩
    (by decide) selected_cut_43437

theorem selected_cut_43438 : selected 10 ⟨1188554, by decide⟩
    (prefixPartial 11 87448) = some ⟨11, 2, 0, 1188554, 87448, 3221, 262144⟩ := by
  decide +kernel

theorem context_11_87448_1188554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87448 ⟨1188554, by decide⟩ :=
  accepted_of_selected 11 87448 ⟨1188554, by decide⟩ ⟨11, 2, 0, 1188554, 87448, 3221, 262144⟩
    (by decide) selected_cut_43438

theorem selected_cut_43439 : selected 10 ⟨1188621, by decide⟩
    (prefixPartial 11 87449) = some ⟨11, 2, 0, 1188621, 87449, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_87449_1188621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87449 ⟨1188621, by decide⟩ :=
  accepted_of_selected 11 87449 ⟨1188621, by decide⟩ ⟨11, 2, 0, 1188621, 87449, 2433, 262144⟩
    (by decide) selected_cut_43439

theorem selected_cut_43440 : selected 10 ⟨1188682, by decide⟩
    (prefixPartial 11 87450) = some ⟨11, 2, 0, 1188682, 87450, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_87450_1188682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87450 ⟨1188682, by decide⟩ :=
  accepted_of_selected 11 87450 ⟨1188682, by decide⟩ ⟨11, 2, 0, 1188682, 87450, 2125, 262144⟩
    (by decide) selected_cut_43440

theorem selected_cut_43441 : selected 10 ⟨1188748, by decide⟩
    (prefixPartial 11 87451) = some ⟨11, 2, 0, 1188748, 87451, 2801, 262144⟩ := by
  decide +kernel

theorem context_11_87451_1188748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87451 ⟨1188748, by decide⟩ :=
  accepted_of_selected 11 87451 ⟨1188748, by decide⟩ ⟨11, 2, 0, 1188748, 87451, 2801, 262144⟩
    (by decide) selected_cut_43441

theorem unmarked_context_10_21862_1188749 : frontier 11 ⟨1188749, by decide⟩
    (prefixCache 10 21862) (prefixPartial 10 21862) = false := by
  decide +kernel

theorem node_context_10_21862_1188749 : EJMOriginalGlobalDAGData.nodes 11 ⟨1188749, by decide⟩ =
    .split (coordinate 10) (![⟨1188554, by decide⟩,⟨1188621, by decide⟩,⟨1188682, by decide⟩,⟨1188748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21862_1188749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21862 ⟨1188749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21862
    ⟨1188749, by decide⟩ (by decide) (![⟨1188554, by decide⟩,⟨1188621, by decide⟩,⟨1188682, by decide⟩,⟨1188748, by decide⟩]) unmarked_context_10_21862_1188749 node_context_10_21862_1188749
  intro a
  fin_cases a
  · exact context_11_87448_1188554
  · exact context_11_87449_1188621
  · exact context_11_87450_1188682
  · exact context_11_87451_1188748

theorem selected_cut_43442 : selected 10 ⟨1188803, by decide⟩
    (prefixPartial 11 87452) = some ⟨11, 2, 0, 1188803, 87452, 2017, 262144⟩ := by
  decide +kernel

theorem context_11_87452_1188803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87452 ⟨1188803, by decide⟩ :=
  accepted_of_selected 11 87452 ⟨1188803, by decide⟩ ⟨11, 2, 0, 1188803, 87452, 2017, 262144⟩
    (by decide) selected_cut_43442

theorem selected_cut_43443 : selected 10 ⟨1188855, by decide⟩
    (prefixPartial 11 87453) = some ⟨11, 2, 0, 1188855, 87453, 1421, 262144⟩ := by
  decide +kernel

theorem context_11_87453_1188855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87453 ⟨1188855, by decide⟩ :=
  accepted_of_selected 11 87453 ⟨1188855, by decide⟩ ⟨11, 2, 0, 1188855, 87453, 1421, 262144⟩
    (by decide) selected_cut_43443

theorem selected_cut_43444 : selected 10 ⟨1188889, by decide⟩
    (prefixPartial 11 87454) = some ⟨11, 2, 0, 1188889, 87454, 1237, 262144⟩ := by
  decide +kernel

theorem context_11_87454_1188889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87454 ⟨1188889, by decide⟩ :=
  accepted_of_selected 11 87454 ⟨1188889, by decide⟩ ⟨11, 2, 0, 1188889, 87454, 1237, 262144⟩
    (by decide) selected_cut_43444

theorem selected_cut_43445 : selected 10 ⟨1188912, by decide⟩
    (prefixPartial 11 87455) = some ⟨11, 2, 0, 1188912, 87455, 1105, 262144⟩ := by
  decide +kernel

theorem context_11_87455_1188912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87455 ⟨1188912, by decide⟩ :=
  accepted_of_selected 11 87455 ⟨1188912, by decide⟩ ⟨11, 2, 0, 1188912, 87455, 1105, 262144⟩
    (by decide) selected_cut_43445

theorem unmarked_context_10_21863_1188913 : frontier 11 ⟨1188913, by decide⟩
    (prefixCache 10 21863) (prefixPartial 10 21863) = false := by
  decide +kernel

theorem node_context_10_21863_1188913 : EJMOriginalGlobalDAGData.nodes 11 ⟨1188913, by decide⟩ =
    .split (coordinate 10) (![⟨1188803, by decide⟩,⟨1188855, by decide⟩,⟨1188889, by decide⟩,⟨1188912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21863_1188913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21863 ⟨1188913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21863
    ⟨1188913, by decide⟩ (by decide) (![⟨1188803, by decide⟩,⟨1188855, by decide⟩,⟨1188889, by decide⟩,⟨1188912, by decide⟩]) unmarked_context_10_21863_1188913 node_context_10_21863_1188913
  intro a
  fin_cases a
  · exact context_11_87452_1188803
  · exact context_11_87453_1188855
  · exact context_11_87454_1188889
  · exact context_11_87455_1188912

theorem unmarked_context_9_5465_1188914 : frontier 12 ⟨1188914, by decide⟩
    (prefixCache 9 5465) (prefixPartial 9 5465) = false := by
  decide +kernel

theorem node_context_9_5465_1188914 : EJMOriginalGlobalDAGData.nodes 12 ⟨1188914, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1188749, by decide⟩,⟨1188913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5465_1188914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5465 ⟨1188914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5465
    ⟨1188914, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1188749, by decide⟩,⟨1188913, by decide⟩]) unmarked_context_9_5465_1188914 node_context_9_5465_1188914
  intro a
  fin_cases a
  · exact context_10_21860_3442
  · exact context_10_21861_893098
  · exact context_10_21862_1188749
  · exact context_10_21863_1188913

theorem selected_cut_43446 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 21864) = some ⟨10, 1, 0, 3442, 21864, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21864_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21864 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 21864 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 21864, 1, 1048576⟩
    (by decide) selected_cut_43446

theorem selected_cut_43447 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 21865) = some ⟨10, 1, 0, 3442, 21865, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21865_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21865 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 21865 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 21865, 1, 1048576⟩
    (by decide) selected_cut_43447

theorem selected_cut_43448 : selected 11 ⟨1188962, by decide⟩
    (prefixPartial 10 21866) = some ⟨10, 2, 0, 1188962, 21866, 1701, 1048576⟩ := by
  decide +kernel

theorem context_10_21866_1188962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21866 ⟨1188962, by decide⟩ :=
  accepted_of_selected 10 21866 ⟨1188962, by decide⟩ ⟨10, 2, 0, 1188962, 21866, 1701, 1048576⟩
    (by decide) selected_cut_43448

theorem selected_cut_43449 : selected 11 ⟨1189057, by decide⟩
    (prefixPartial 10 21867) = some ⟨10, 2, 0, 1189057, 21867, 2861, 1048576⟩ := by
  decide +kernel

theorem context_10_21867_1189057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21867 ⟨1189057, by decide⟩ :=
  accepted_of_selected 10 21867 ⟨1189057, by decide⟩ ⟨10, 2, 0, 1189057, 21867, 2861, 1048576⟩
    (by decide) selected_cut_43449

theorem unmarked_context_9_5466_1189058 : frontier 12 ⟨1189058, by decide⟩
    (prefixCache 9 5466) (prefixPartial 9 5466) = false := by
  decide +kernel

theorem node_context_9_5466_1189058 : EJMOriginalGlobalDAGData.nodes 12 ⟨1189058, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨1188962, by decide⟩,⟨1189057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5466_1189058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5466 ⟨1189058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5466
    ⟨1189058, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨1188962, by decide⟩,⟨1189057, by decide⟩]) unmarked_context_9_5466_1189058 node_context_9_5466_1189058
  intro a
  fin_cases a
  · exact context_10_21864_3442
  · exact context_10_21865_3442
  · exact context_10_21866_1188962
  · exact context_10_21867_1189057

theorem selected_cut_43450 : selected 12 ⟨1189078, by decide⟩
    (prefixPartial 9 5467) = some ⟨9, 2, 0, 1189078, 5467, 221, 4194304⟩ := by
  decide +kernel

theorem context_9_5467_1189078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5467 ⟨1189078, by decide⟩ :=
  accepted_of_selected 9 5467 ⟨1189078, by decide⟩ ⟨9, 2, 0, 1189078, 5467, 221, 4194304⟩
    (by decide) selected_cut_43450

theorem unmarked_context_8_1366_1189079 : frontier 13 ⟨1189079, by decide⟩
    (prefixCache 8 1366) (prefixPartial 8 1366) = false := by
  decide +kernel

theorem node_context_8_1366_1189079 : EJMOriginalGlobalDAGData.nodes 13 ⟨1189079, by decide⟩ =
    .split (coordinate 8) (![⟨1188460, by decide⟩,⟨1188914, by decide⟩,⟨1189058, by decide⟩,⟨1189078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1366_1189079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1366 ⟨1189079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1366
    ⟨1189079, by decide⟩ (by decide) (![⟨1188460, by decide⟩,⟨1188914, by decide⟩,⟨1189058, by decide⟩,⟨1189078, by decide⟩]) unmarked_context_8_1366_1189079 node_context_8_1366_1189079
  intro a
  fin_cases a
  · exact context_9_5464_1188460
  · exact context_9_5465_1188914
  · exact context_9_5466_1189058
  · exact context_9_5467_1189078

theorem selected_cut_43451 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 1367) = some ⟨8, 1, 0, 14298, 1367, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1367_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1367 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 1367 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 1367, 1, 16777216⟩
    (by decide) selected_cut_43451

theorem unmarked_context_7_341_1189080 : frontier 14 ⟨1189080, by decide⟩
    (prefixCache 7 341) (prefixPartial 7 341) = false := by
  decide +kernel

theorem node_context_7_341_1189080 : EJMOriginalGlobalDAGData.nodes 14 ⟨1189080, by decide⟩ =
    .split (coordinate 7) (![⟨643294, by decide⟩,⟨1109534, by decide⟩,⟨1189079, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_341_1189080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 341 ⟨1189080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 341
    ⟨1189080, by decide⟩ (by decide) (![⟨643294, by decide⟩,⟨1109534, by decide⟩,⟨1189079, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_341_1189080 node_context_7_341_1189080
  intro a
  fin_cases a
  · exact context_8_1364_643294
  · exact context_8_1365_1109534
  · exact context_8_1366_1189079
  · exact context_8_1367_14298

theorem selected_cut_43452 : selected 13 ⟨643294, by decide⟩
    (prefixPartial 8 1368) = some ⟨8, 1, 0, 643294, 1368, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1368_643294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1368 ⟨643294, by decide⟩ :=
  accepted_of_selected 8 1368 ⟨643294, by decide⟩ ⟨8, 1, 0, 643294, 1368, 1, 16777216⟩
    (by decide) selected_cut_43452

theorem selected_cut_43453 : selected 13 ⟨1109534, by decide⟩
    (prefixPartial 8 1369) = some ⟨8, 1, 0, 1109534, 1369, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1369_1109534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1369 ⟨1109534, by decide⟩ :=
  accepted_of_selected 8 1369 ⟨1109534, by decide⟩ ⟨8, 1, 0, 1109534, 1369, 1, 16777216⟩
    (by decide) selected_cut_43453

theorem selected_cut_43454 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 87680) = some ⟨11, 1, 0, 434745, 87680, 1, 262144⟩ := by
  decide +kernel

theorem context_11_87680_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87680 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 87680 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 87680, 1, 262144⟩
    (by decide) selected_cut_43454

theorem selected_cut_43455 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 350724) = some ⟨12, 1, 0, 448748, 350724, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350724_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350724 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 350724 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 350724, 1, 65536⟩
    (by decide) selected_cut_43455

theorem selected_cut_43456 : selected 9 ⟨1189174, by decide⟩
    (prefixPartial 12 350725) = some ⟨12, 2, 0, 1189174, 350725, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_350725_1189174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350725 ⟨1189174, by decide⟩ :=
  accepted_of_selected 12 350725 ⟨1189174, by decide⟩ ⟨12, 2, 0, 1189174, 350725, 3581, 65536⟩
    (by decide) selected_cut_43456

theorem selected_cut_43457 : selected 9 ⟨1189247, by decide⟩
    (prefixPartial 12 350726) = some ⟨12, 2, 0, 1189247, 350726, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_350726_1189247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350726 ⟨1189247, by decide⟩ :=
  accepted_of_selected 12 350726 ⟨1189247, by decide⟩ ⟨12, 2, 0, 1189247, 350726, 3185, 65536⟩
    (by decide) selected_cut_43457

theorem selected_cut_43458 : selected 9 ⟨1189324, by decide⟩
    (prefixPartial 12 350727) = some ⟨12, 2, 0, 1189324, 350727, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_350727_1189324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350727 ⟨1189324, by decide⟩ :=
  accepted_of_selected 12 350727 ⟨1189324, by decide⟩ ⟨12, 2, 0, 1189324, 350727, 3405, 65536⟩
    (by decide) selected_cut_43458

theorem unmarked_context_11_87681_1189325 : frontier 10 ⟨1189325, by decide⟩
    (prefixCache 11 87681) (prefixPartial 11 87681) = false := by
  decide +kernel

theorem node_context_11_87681_1189325 : EJMOriginalGlobalDAGData.nodes 10 ⟨1189325, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1189174, by decide⟩,⟨1189247, by decide⟩,⟨1189324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87681_1189325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87681 ⟨1189325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87681
    ⟨1189325, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1189174, by decide⟩,⟨1189247, by decide⟩,⟨1189324, by decide⟩]) unmarked_context_11_87681_1189325 node_context_11_87681_1189325
  intro a
  fin_cases a
  · exact context_12_350724_448748
  · exact context_12_350725_1189174
  · exact context_12_350726_1189247
  · exact context_12_350727_1189324

theorem selected_cut_43459 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 350728) = some ⟨12, 1, 0, 448748, 350728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350728_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350728 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 350728 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 350728, 1, 65536⟩
    (by decide) selected_cut_43459

theorem selected_cut_43460 : selected 9 ⟨1189381, by decide⟩
    (prefixPartial 12 350729) = some ⟨12, 2, 0, 1189381, 350729, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_350729_1189381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350729 ⟨1189381, by decide⟩ :=
  accepted_of_selected 12 350729 ⟨1189381, by decide⟩ ⟨12, 2, 0, 1189381, 350729, 3013, 65536⟩
    (by decide) selected_cut_43460

theorem selected_cut_43461 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 350730) = some ⟨12, 1, 0, 893903, 350730, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350730_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350730 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 350730 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 350730, 1, 65536⟩
    (by decide) selected_cut_43461

theorem selected_cut_43462 : selected 9 ⟨1189464, by decide⟩
    (prefixPartial 12 350731) = some ⟨12, 2, 0, 1189464, 350731, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_350731_1189464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350731 ⟨1189464, by decide⟩ :=
  accepted_of_selected 12 350731 ⟨1189464, by decide⟩ ⟨12, 2, 0, 1189464, 350731, 3665, 65536⟩
    (by decide) selected_cut_43462

theorem unmarked_context_11_87682_1189465 : frontier 10 ⟨1189465, by decide⟩
    (prefixCache 11 87682) (prefixPartial 11 87682) = false := by
  decide +kernel

theorem node_context_11_87682_1189465 : EJMOriginalGlobalDAGData.nodes 10 ⟨1189465, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1189381, by decide⟩,⟨893903, by decide⟩,⟨1189464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87682_1189465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87682 ⟨1189465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87682
    ⟨1189465, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1189381, by decide⟩,⟨893903, by decide⟩,⟨1189464, by decide⟩]) unmarked_context_11_87682_1189465 node_context_11_87682_1189465
  intro a
  fin_cases a
  · exact context_12_350728_448748
  · exact context_12_350729_1189381
  · exact context_12_350730_893903
  · exact context_12_350731_1189464

theorem selected_cut_43463 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 350732) = some ⟨12, 1, 0, 448748, 350732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350732_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350732 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 350732 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 350732, 1, 65536⟩
    (by decide) selected_cut_43463

theorem selected_cut_43464 : selected 9 ⟨1189532, by decide⟩
    (prefixPartial 12 350733) = some ⟨12, 2, 0, 1189532, 350733, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_350733_1189532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350733 ⟨1189532, by decide⟩ :=
  accepted_of_selected 12 350733 ⟨1189532, by decide⟩ ⟨12, 2, 0, 1189532, 350733, 3317, 65536⟩
    (by decide) selected_cut_43464

theorem selected_cut_43465 : selected 9 ⟨1189609, by decide⟩
    (prefixPartial 12 350734) = some ⟨12, 2, 0, 1189609, 350734, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_350734_1189609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350734 ⟨1189609, by decide⟩ :=
  accepted_of_selected 12 350734 ⟨1189609, by decide⟩ ⟨12, 2, 0, 1189609, 350734, 3737, 65536⟩
    (by decide) selected_cut_43465

theorem selected_cut_43466 : selected 9 ⟨1189679, by decide⟩
    (prefixPartial 12 350735) = some ⟨12, 2, 0, 1189679, 350735, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_350735_1189679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350735 ⟨1189679, by decide⟩ :=
  accepted_of_selected 12 350735 ⟨1189679, by decide⟩ ⟨12, 2, 0, 1189679, 350735, 3465, 65536⟩
    (by decide) selected_cut_43466

theorem unmarked_context_11_87683_1189680 : frontier 10 ⟨1189680, by decide⟩
    (prefixCache 11 87683) (prefixPartial 11 87683) = false := by
  decide +kernel

theorem node_context_11_87683_1189680 : EJMOriginalGlobalDAGData.nodes 10 ⟨1189680, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1189532, by decide⟩,⟨1189609, by decide⟩,⟨1189679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87683_1189680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87683 ⟨1189680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87683
    ⟨1189680, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1189532, by decide⟩,⟨1189609, by decide⟩,⟨1189679, by decide⟩]) unmarked_context_11_87683_1189680 node_context_11_87683_1189680
  intro a
  fin_cases a
  · exact context_12_350732_448748
  · exact context_12_350733_1189532
  · exact context_12_350734_1189609
  · exact context_12_350735_1189679

theorem unmarked_context_10_21920_1189681 : frontier 11 ⟨1189681, by decide⟩
    (prefixCache 10 21920) (prefixPartial 10 21920) = false := by
  decide +kernel

theorem node_context_10_21920_1189681 : EJMOriginalGlobalDAGData.nodes 11 ⟨1189681, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1189325, by decide⟩,⟨1189465, by decide⟩,⟨1189680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21920_1189681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21920 ⟨1189681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21920
    ⟨1189681, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1189325, by decide⟩,⟨1189465, by decide⟩,⟨1189680, by decide⟩]) unmarked_context_10_21920_1189681 node_context_10_21920_1189681
  intro a
  fin_cases a
  · exact context_11_87680_434745
  · exact context_11_87681_1189325
  · exact context_11_87682_1189465
  · exact context_11_87683_1189680

theorem selected_cut_43467 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 350736) = some ⟨12, 1, 0, 435160, 350736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350736_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350736 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 350736 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 350736, 1, 65536⟩
    (by decide) selected_cut_43467

theorem selected_cut_43468 : selected 9 ⟨1189748, by decide⟩
    (prefixPartial 12 350737) = some ⟨12, 2, 0, 1189748, 350737, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_350737_1189748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350737 ⟨1189748, by decide⟩ :=
  accepted_of_selected 12 350737 ⟨1189748, by decide⟩ ⟨12, 2, 0, 1189748, 350737, 3125, 65536⟩
    (by decide) selected_cut_43468

theorem selected_cut_43469 : selected 9 ⟨1189844, by decide⟩
    (prefixPartial 12 350738) = some ⟨12, 2, 0, 1189844, 350738, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_350738_1189844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350738 ⟨1189844, by decide⟩ :=
  accepted_of_selected 12 350738 ⟨1189844, by decide⟩ ⟨12, 2, 0, 1189844, 350738, 3829, 65536⟩
    (by decide) selected_cut_43469

theorem selected_cut_43470 : selected 8 ⟨1189891, by decide⟩
    (prefixPartial 13 1402956) = some ⟨13, 2, 0, 1189891, 1402956, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_1402956_1189891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1402956 ⟨1189891, by decide⟩ :=
  accepted_of_selected 13 1402956 ⟨1189891, by decide⟩ ⟨13, 2, 0, 1189891, 1402956, 1861, 16384⟩
    (by decide) selected_cut_43470

theorem selected_cut_43471 : selected 8 ⟨1189918, by decide⟩
    (prefixPartial 13 1402957) = some ⟨13, 2, 0, 1189918, 1402957, 981, 16384⟩ := by
  decide +kernel

theorem context_13_1402957_1189918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1402957 ⟨1189918, by decide⟩ :=
  accepted_of_selected 13 1402957 ⟨1189918, by decide⟩ ⟨13, 2, 0, 1189918, 1402957, 981, 16384⟩
    (by decide) selected_cut_43471

theorem selected_cut_43472 : selected 8 ⟨1189938, by decide⟩
    (prefixPartial 13 1402958) = some ⟨13, 2, 0, 1189938, 1402958, 917, 16384⟩ := by
  decide +kernel

theorem context_13_1402958_1189938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1402958 ⟨1189938, by decide⟩ :=
  accepted_of_selected 13 1402958 ⟨1189938, by decide⟩ ⟨13, 2, 0, 1189938, 1402958, 917, 16384⟩
    (by decide) selected_cut_43472

theorem selected_cut_43473 : selected 8 ⟨1189946, by decide⟩
    (prefixPartial 13 1402959) = some ⟨13, 2, 0, 1189946, 1402959, 593, 16384⟩ := by
  decide +kernel

theorem context_13_1402959_1189946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1402959 ⟨1189946, by decide⟩ :=
  accepted_of_selected 13 1402959 ⟨1189946, by decide⟩ ⟨13, 2, 0, 1189946, 1402959, 593, 16384⟩
    (by decide) selected_cut_43473

theorem unmarked_context_12_350739_1189947 : frontier 9 ⟨1189947, by decide⟩
    (prefixCache 12 350739) (prefixPartial 12 350739) = false := by
  decide +kernel

theorem node_context_12_350739_1189947 : EJMOriginalGlobalDAGData.nodes 9 ⟨1189947, by decide⟩ =
    .split (coordinate 12) (![⟨1189891, by decide⟩,⟨1189918, by decide⟩,⟨1189938, by decide⟩,⟨1189946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_350739_1189947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350739 ⟨1189947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 350739
    ⟨1189947, by decide⟩ (by decide) (![⟨1189891, by decide⟩,⟨1189918, by decide⟩,⟨1189938, by decide⟩,⟨1189946, by decide⟩]) unmarked_context_12_350739_1189947 node_context_12_350739_1189947
  intro a
  fin_cases a
  · exact context_13_1402956_1189891
  · exact context_13_1402957_1189918
  · exact context_13_1402958_1189938
  · exact context_13_1402959_1189946

theorem unmarked_context_11_87684_1189948 : frontier 10 ⟨1189948, by decide⟩
    (prefixCache 11 87684) (prefixPartial 11 87684) = false := by
  decide +kernel

theorem node_context_11_87684_1189948 : EJMOriginalGlobalDAGData.nodes 10 ⟨1189948, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1189748, by decide⟩,⟨1189844, by decide⟩,⟨1189947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87684_1189948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87684 ⟨1189948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87684
    ⟨1189948, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1189748, by decide⟩,⟨1189844, by decide⟩,⟨1189947, by decide⟩]) unmarked_context_11_87684_1189948 node_context_11_87684_1189948
  intro a
  fin_cases a
  · exact context_12_350736_435160
  · exact context_12_350737_1189748
  · exact context_12_350738_1189844
  · exact context_12_350739_1189947

theorem selected_cut_43474 : selected 9 ⟨1190011, by decide⟩
    (prefixPartial 12 350740) = some ⟨12, 2, 0, 1190011, 350740, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_350740_1190011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350740 ⟨1190011, by decide⟩ :=
  accepted_of_selected 12 350740 ⟨1190011, by decide⟩ ⟨12, 2, 0, 1190011, 350740, 1861, 65536⟩
    (by decide) selected_cut_43474

theorem selected_cut_43475 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 350741) = some ⟨12, 1, 0, 1118965, 350741, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350741_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350741 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 350741 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 350741, 1, 65536⟩
    (by decide) selected_cut_43475

theorem selected_cut_43476 : selected 9 ⟨1190070, by decide⟩
    (prefixPartial 12 350742) = some ⟨12, 2, 0, 1190070, 350742, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_350742_1190070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350742 ⟨1190070, by decide⟩ :=
  accepted_of_selected 12 350742 ⟨1190070, by decide⟩ ⟨12, 2, 0, 1190070, 350742, 3017, 65536⟩
    (by decide) selected_cut_43476

theorem selected_cut_43477 : selected 9 ⟨1190130, by decide⟩
    (prefixPartial 12 350743) = some ⟨12, 2, 0, 1190130, 350743, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_350743_1190130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350743 ⟨1190130, by decide⟩ :=
  accepted_of_selected 12 350743 ⟨1190130, by decide⟩ ⟨12, 2, 0, 1190130, 350743, 3313, 65536⟩
    (by decide) selected_cut_43477

theorem unmarked_context_11_87685_1190131 : frontier 10 ⟨1190131, by decide⟩
    (prefixCache 11 87685) (prefixPartial 11 87685) = false := by
  decide +kernel

theorem node_context_11_87685_1190131 : EJMOriginalGlobalDAGData.nodes 10 ⟨1190131, by decide⟩ =
    .split (coordinate 11) (![⟨1190011, by decide⟩,⟨1118965, by decide⟩,⟨1190070, by decide⟩,⟨1190130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87685_1190131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87685 ⟨1190131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87685
    ⟨1190131, by decide⟩ (by decide) (![⟨1190011, by decide⟩,⟨1118965, by decide⟩,⟨1190070, by decide⟩,⟨1190130, by decide⟩]) unmarked_context_11_87685_1190131 node_context_11_87685_1190131
  intro a
  fin_cases a
  · exact context_12_350740_1190011
  · exact context_12_350741_1118965
  · exact context_12_350742_1190070
  · exact context_12_350743_1190130

theorem selected_cut_43478 : selected 9 ⟨1190215, by decide⟩
    (prefixPartial 12 350744) = some ⟨12, 2, 0, 1190215, 350744, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_350744_1190215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350744 ⟨1190215, by decide⟩ :=
  accepted_of_selected 12 350744 ⟨1190215, by decide⟩ ⟨12, 2, 0, 1190215, 350744, 3265, 65536⟩
    (by decide) selected_cut_43478

theorem selected_cut_43479 : selected 9 ⟨1190266, by decide⟩
    (prefixPartial 12 350745) = some ⟨12, 2, 0, 1190266, 350745, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_350745_1190266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350745 ⟨1190266, by decide⟩ :=
  accepted_of_selected 12 350745 ⟨1190266, by decide⟩ ⟨12, 2, 0, 1190266, 350745, 2761, 65536⟩
    (by decide) selected_cut_43479

theorem selected_cut_43480 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 350746) = some ⟨12, 1, 0, 893903, 350746, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350746_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350746 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 350746 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 350746, 1, 65536⟩
    (by decide) selected_cut_43480

theorem selected_cut_43481 : selected 9 ⟨1190357, by decide⟩
    (prefixPartial 12 350747) = some ⟨12, 2, 0, 1190357, 350747, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_350747_1190357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350747 ⟨1190357, by decide⟩ :=
  accepted_of_selected 12 350747 ⟨1190357, by decide⟩ ⟨12, 2, 0, 1190357, 350747, 3845, 65536⟩
    (by decide) selected_cut_43481

theorem unmarked_context_11_87686_1190358 : frontier 10 ⟨1190358, by decide⟩
    (prefixCache 11 87686) (prefixPartial 11 87686) = false := by
  decide +kernel

theorem node_context_11_87686_1190358 : EJMOriginalGlobalDAGData.nodes 10 ⟨1190358, by decide⟩ =
    .split (coordinate 11) (![⟨1190215, by decide⟩,⟨1190266, by decide⟩,⟨893903, by decide⟩,⟨1190357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87686_1190358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87686 ⟨1190358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87686
    ⟨1190358, by decide⟩ (by decide) (![⟨1190215, by decide⟩,⟨1190266, by decide⟩,⟨893903, by decide⟩,⟨1190357, by decide⟩]) unmarked_context_11_87686_1190358 node_context_11_87686_1190358
  intro a
  fin_cases a
  · exact context_12_350744_1190215
  · exact context_12_350745_1190266
  · exact context_12_350746_893903
  · exact context_12_350747_1190357

theorem selected_cut_43482 : selected 9 ⟨1190437, by decide⟩
    (prefixPartial 12 350748) = some ⟨12, 2, 0, 1190437, 350748, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_350748_1190437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350748 ⟨1190437, by decide⟩ :=
  accepted_of_selected 12 350748 ⟨1190437, by decide⟩ ⟨12, 2, 0, 1190437, 350748, 3497, 65536⟩
    (by decide) selected_cut_43482

theorem selected_cut_43483 : selected 9 ⟨1190486, by decide⟩
    (prefixPartial 12 350749) = some ⟨12, 2, 0, 1190486, 350749, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_350749_1190486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350749 ⟨1190486, by decide⟩ :=
  accepted_of_selected 12 350749 ⟨1190486, by decide⟩ ⟨12, 2, 0, 1190486, 350749, 2773, 65536⟩
    (by decide) selected_cut_43483

theorem selected_cut_43484 : selected 9 ⟨1190565, by decide⟩
    (prefixPartial 12 350750) = some ⟨12, 2, 0, 1190565, 350750, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_350750_1190565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350750 ⟨1190565, by decide⟩ :=
  accepted_of_selected 12 350750 ⟨1190565, by decide⟩ ⟨12, 2, 0, 1190565, 350750, 3569, 65536⟩
    (by decide) selected_cut_43484

theorem selected_cut_43485 : selected 9 ⟨1190632, by decide⟩
    (prefixPartial 12 350751) = some ⟨12, 2, 0, 1190632, 350751, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_350751_1190632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350751 ⟨1190632, by decide⟩ :=
  accepted_of_selected 12 350751 ⟨1190632, by decide⟩ ⟨12, 2, 0, 1190632, 350751, 3245, 65536⟩
    (by decide) selected_cut_43485

theorem unmarked_context_11_87687_1190633 : frontier 10 ⟨1190633, by decide⟩
    (prefixCache 11 87687) (prefixPartial 11 87687) = false := by
  decide +kernel

theorem node_context_11_87687_1190633 : EJMOriginalGlobalDAGData.nodes 10 ⟨1190633, by decide⟩ =
    .split (coordinate 11) (![⟨1190437, by decide⟩,⟨1190486, by decide⟩,⟨1190565, by decide⟩,⟨1190632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87687_1190633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87687 ⟨1190633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87687
    ⟨1190633, by decide⟩ (by decide) (![⟨1190437, by decide⟩,⟨1190486, by decide⟩,⟨1190565, by decide⟩,⟨1190632, by decide⟩]) unmarked_context_11_87687_1190633 node_context_11_87687_1190633
  intro a
  fin_cases a
  · exact context_12_350748_1190437
  · exact context_12_350749_1190486
  · exact context_12_350750_1190565
  · exact context_12_350751_1190632

theorem unmarked_context_10_21921_1190634 : frontier 11 ⟨1190634, by decide⟩
    (prefixCache 10 21921) (prefixPartial 10 21921) = false := by
  decide +kernel

theorem node_context_10_21921_1190634 : EJMOriginalGlobalDAGData.nodes 11 ⟨1190634, by decide⟩ =
    .split (coordinate 10) (![⟨1189948, by decide⟩,⟨1190131, by decide⟩,⟨1190358, by decide⟩,⟨1190633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21921_1190634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21921 ⟨1190634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21921
    ⟨1190634, by decide⟩ (by decide) (![⟨1189948, by decide⟩,⟨1190131, by decide⟩,⟨1190358, by decide⟩,⟨1190633, by decide⟩]) unmarked_context_10_21921_1190634 node_context_10_21921_1190634
  intro a
  fin_cases a
  · exact context_11_87684_1189948
  · exact context_11_87685_1190131
  · exact context_11_87686_1190358
  · exact context_11_87687_1190633

theorem selected_cut_43486 : selected 9 ⟨355612, by decide⟩
    (prefixPartial 12 350752) = some ⟨12, 1, 0, 355612, 350752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_350752_355612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350752 ⟨355612, by decide⟩ :=
  accepted_of_selected 12 350752 ⟨355612, by decide⟩ ⟨12, 1, 0, 355612, 350752, 1, 65536⟩
    (by decide) selected_cut_43486

theorem selected_cut_43487 : selected 9 ⟨1190684, by decide⟩
    (prefixPartial 12 350753) = some ⟨12, 2, 0, 1190684, 350753, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_350753_1190684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350753 ⟨1190684, by decide⟩ :=
  accepted_of_selected 12 350753 ⟨1190684, by decide⟩ ⟨12, 2, 0, 1190684, 350753, 2561, 65536⟩
    (by decide) selected_cut_43487

theorem selected_cut_43488 : selected 9 ⟨1190736, by decide⟩
    (prefixPartial 12 350754) = some ⟨12, 2, 0, 1190736, 350754, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_350754_1190736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350754 ⟨1190736, by decide⟩ :=
  accepted_of_selected 12 350754 ⟨1190736, by decide⟩ ⟨12, 2, 0, 1190736, 350754, 2693, 65536⟩
    (by decide) selected_cut_43488

theorem selected_cut_43489 : selected 9 ⟨1190803, by decide⟩
    (prefixPartial 12 350755) = some ⟨12, 2, 0, 1190803, 350755, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_350755_1190803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350755 ⟨1190803, by decide⟩ :=
  accepted_of_selected 12 350755 ⟨1190803, by decide⟩ ⟨12, 2, 0, 1190803, 350755, 3101, 65536⟩
    (by decide) selected_cut_43489

theorem unmarked_context_11_87688_1190804 : frontier 10 ⟨1190804, by decide⟩
    (prefixCache 11 87688) (prefixPartial 11 87688) = false := by
  decide +kernel

theorem node_context_11_87688_1190804 : EJMOriginalGlobalDAGData.nodes 10 ⟨1190804, by decide⟩ =
    .split (coordinate 11) (![⟨355612, by decide⟩,⟨1190684, by decide⟩,⟨1190736, by decide⟩,⟨1190803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87688_1190804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87688 ⟨1190804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87688
    ⟨1190804, by decide⟩ (by decide) (![⟨355612, by decide⟩,⟨1190684, by decide⟩,⟨1190736, by decide⟩,⟨1190803, by decide⟩]) unmarked_context_11_87688_1190804 node_context_11_87688_1190804
  intro a
  fin_cases a
  · exact context_12_350752_355612
  · exact context_12_350753_1190684
  · exact context_12_350754_1190736
  · exact context_12_350755_1190803

theorem selected_cut_43490 : selected 9 ⟨1190851, by decide⟩
    (prefixPartial 12 350756) = some ⟨12, 2, 0, 1190851, 350756, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_350756_1190851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 350756 ⟨1190851, by decide⟩ :=
  accepted_of_selected 12 350756 ⟨1190851, by decide⟩ ⟨12, 2, 0, 1190851, 350756, 2353, 65536⟩
    (by decide) selected_cut_43490

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
