/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover483
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_92685_1295895 : frontier 10 ⟨1295895, by decide⟩
    (prefixCache 11 92685) (prefixPartial 11 92685) = false := by
  decide +kernel

theorem node_context_11_92685_1295895 : EJMOriginalGlobalDAGData.nodes 10 ⟨1295895, by decide⟩ =
    .split (coordinate 11) (![⟨1295767, by decide⟩,⟨1295803, by decide⟩,⟨1295844, by decide⟩,⟨1295894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92685_1295895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92685 ⟨1295895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92685
    ⟨1295895, by decide⟩ (by decide) (![⟨1295767, by decide⟩,⟨1295803, by decide⟩,⟨1295844, by decide⟩,⟨1295894, by decide⟩]) unmarked_context_11_92685_1295895 node_context_11_92685_1295895
  intro a
  fin_cases a
  · exact context_12_370740_1295767
  · exact context_12_370741_1295803
  · exact context_12_370742_1295844
  · exact context_12_370743_1295894

theorem selected_cut_46468 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 370744) = some ⟨12, 1, 0, 994572, 370744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370744_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370744 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 370744 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 370744, 1, 65536⟩
    (by decide) selected_cut_46468

theorem selected_cut_46469 : selected 9 ⟨1295932, by decide⟩
    (prefixPartial 12 370745) = some ⟨12, 2, 0, 1295932, 370745, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_370745_1295932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370745 ⟨1295932, by decide⟩ :=
  accepted_of_selected 12 370745 ⟨1295932, by decide⟩ ⟨12, 2, 0, 1295932, 370745, 2321, 65536⟩
    (by decide) selected_cut_46469

theorem selected_cut_46470 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 370746) = some ⟨12, 1, 0, 806997, 370746, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370746_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370746 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 370746 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 370746, 1, 65536⟩
    (by decide) selected_cut_46470

theorem selected_cut_46471 : selected 9 ⟨1295972, by decide⟩
    (prefixPartial 12 370747) = some ⟨12, 2, 0, 1295972, 370747, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_370747_1295972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370747 ⟨1295972, by decide⟩ :=
  accepted_of_selected 12 370747 ⟨1295972, by decide⟩ ⟨12, 2, 0, 1295972, 370747, 2525, 65536⟩
    (by decide) selected_cut_46471

theorem unmarked_context_11_92686_1295973 : frontier 10 ⟨1295973, by decide⟩
    (prefixCache 11 92686) (prefixPartial 11 92686) = false := by
  decide +kernel

theorem node_context_11_92686_1295973 : EJMOriginalGlobalDAGData.nodes 10 ⟨1295973, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1295932, by decide⟩,⟨806997, by decide⟩,⟨1295972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92686_1295973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92686 ⟨1295973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92686
    ⟨1295973, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1295932, by decide⟩,⟨806997, by decide⟩,⟨1295972, by decide⟩]) unmarked_context_11_92686_1295973 node_context_11_92686_1295973
  intro a
  fin_cases a
  · exact context_12_370744_994572
  · exact context_12_370745_1295932
  · exact context_12_370746_806997
  · exact context_12_370747_1295972

theorem selected_cut_46472 : selected 9 ⟨1296007, by decide⟩
    (prefixPartial 12 370748) = some ⟨12, 2, 0, 1296007, 370748, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_370748_1296007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370748 ⟨1296007, by decide⟩ :=
  accepted_of_selected 12 370748 ⟨1296007, by decide⟩ ⟨12, 2, 0, 1296007, 370748, 1989, 65536⟩
    (by decide) selected_cut_46472

theorem selected_cut_46473 : selected 9 ⟨1296042, by decide⟩
    (prefixPartial 12 370749) = some ⟨12, 2, 0, 1296042, 370749, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_370749_1296042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370749 ⟨1296042, by decide⟩ :=
  accepted_of_selected 12 370749 ⟨1296042, by decide⟩ ⟨12, 2, 0, 1296042, 370749, 2033, 65536⟩
    (by decide) selected_cut_46473

theorem selected_cut_46474 : selected 9 ⟨1296075, by decide⟩
    (prefixPartial 12 370750) = some ⟨12, 2, 0, 1296075, 370750, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_370750_1296075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370750 ⟨1296075, by decide⟩ :=
  accepted_of_selected 12 370750 ⟨1296075, by decide⟩ ⟨12, 2, 0, 1296075, 370750, 1901, 65536⟩
    (by decide) selected_cut_46474

theorem selected_cut_46475 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 370751) = some ⟨12, 1, 0, 1120582, 370751, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370751_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370751 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 370751 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 370751, 1, 65536⟩
    (by decide) selected_cut_46475

theorem unmarked_context_11_92687_1296076 : frontier 10 ⟨1296076, by decide⟩
    (prefixCache 11 92687) (prefixPartial 11 92687) = false := by
  decide +kernel

theorem node_context_11_92687_1296076 : EJMOriginalGlobalDAGData.nodes 10 ⟨1296076, by decide⟩ =
    .split (coordinate 11) (![⟨1296007, by decide⟩,⟨1296042, by decide⟩,⟨1296075, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92687_1296076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92687 ⟨1296076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92687
    ⟨1296076, by decide⟩ (by decide) (![⟨1296007, by decide⟩,⟨1296042, by decide⟩,⟨1296075, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_92687_1296076 node_context_11_92687_1296076
  intro a
  fin_cases a
  · exact context_12_370748_1296007
  · exact context_12_370749_1296042
  · exact context_12_370750_1296075
  · exact context_12_370751_1120582

theorem unmarked_context_10_23171_1296077 : frontier 11 ⟨1296077, by decide⟩
    (prefixCache 10 23171) (prefixPartial 10 23171) = false := by
  decide +kernel

theorem node_context_10_23171_1296077 : EJMOriginalGlobalDAGData.nodes 11 ⟨1296077, by decide⟩ =
    .split (coordinate 10) (![⟨1295721, by decide⟩,⟨1295895, by decide⟩,⟨1295973, by decide⟩,⟨1296076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23171_1296077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23171 ⟨1296077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23171
    ⟨1296077, by decide⟩ (by decide) (![⟨1295721, by decide⟩,⟨1295895, by decide⟩,⟨1295973, by decide⟩,⟨1296076, by decide⟩]) unmarked_context_10_23171_1296077 node_context_10_23171_1296077
  intro a
  fin_cases a
  · exact context_11_92684_1295721
  · exact context_11_92685_1295895
  · exact context_11_92686_1295973
  · exact context_11_92687_1296076

theorem unmarked_context_9_5792_1296078 : frontier 12 ⟨1296078, by decide⟩
    (prefixCache 9 5792) (prefixPartial 9 5792) = false := by
  decide +kernel

theorem node_context_9_5792_1296078 : EJMOriginalGlobalDAGData.nodes 12 ⟨1296078, by decide⟩ =
    .split (coordinate 9) (![⟨1294597, by decide⟩,⟨1295149, by decide⟩,⟨1295610, by decide⟩,⟨1296077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5792_1296078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5792 ⟨1296078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5792
    ⟨1296078, by decide⟩ (by decide) (![⟨1294597, by decide⟩,⟨1295149, by decide⟩,⟨1295610, by decide⟩,⟨1296077, by decide⟩]) unmarked_context_9_5792_1296078 node_context_9_5792_1296078
  intro a
  fin_cases a
  · exact context_10_23168_1294597
  · exact context_10_23169_1295149
  · exact context_10_23170_1295610
  · exact context_10_23171_1296077

theorem selected_cut_46476 : selected 10 ⟨1296145, by decide⟩
    (prefixPartial 11 92688) = some ⟨11, 2, 0, 1296145, 92688, 3341, 262144⟩ := by
  decide +kernel

theorem context_11_92688_1296145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92688 ⟨1296145, by decide⟩ :=
  accepted_of_selected 11 92688 ⟨1296145, by decide⟩ ⟨11, 2, 0, 1296145, 92688, 3341, 262144⟩
    (by decide) selected_cut_46476

theorem selected_cut_46477 : selected 9 ⟨1296183, by decide⟩
    (prefixPartial 12 370756) = some ⟨12, 2, 0, 1296183, 370756, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_370756_1296183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370756 ⟨1296183, by decide⟩ :=
  accepted_of_selected 12 370756 ⟨1296183, by decide⟩ ⟨12, 2, 0, 1296183, 370756, 1917, 65536⟩
    (by decide) selected_cut_46477

theorem selected_cut_46478 : selected 9 ⟨275013, by decide⟩
    (prefixPartial 12 370757) = some ⟨12, 1, 0, 275013, 370757, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370757_275013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370757 ⟨275013, by decide⟩ :=
  accepted_of_selected 12 370757 ⟨275013, by decide⟩ ⟨12, 1, 0, 275013, 370757, 1, 65536⟩
    (by decide) selected_cut_46478

theorem selected_cut_46479 : selected 9 ⟨1296211, by decide⟩
    (prefixPartial 12 370758) = some ⟨12, 2, 0, 1296211, 370758, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_370758_1296211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370758 ⟨1296211, by decide⟩ :=
  accepted_of_selected 12 370758 ⟨1296211, by decide⟩ ⟨12, 2, 0, 1296211, 370758, 1725, 65536⟩
    (by decide) selected_cut_46479

theorem selected_cut_46480 : selected 9 ⟨1296255, by decide⟩
    (prefixPartial 12 370759) = some ⟨12, 2, 0, 1296255, 370759, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_370759_1296255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370759 ⟨1296255, by decide⟩ :=
  accepted_of_selected 12 370759 ⟨1296255, by decide⟩ ⟨12, 2, 0, 1296255, 370759, 2121, 65536⟩
    (by decide) selected_cut_46480

theorem unmarked_context_11_92689_1296256 : frontier 10 ⟨1296256, by decide⟩
    (prefixCache 11 92689) (prefixPartial 11 92689) = false := by
  decide +kernel

theorem node_context_11_92689_1296256 : EJMOriginalGlobalDAGData.nodes 10 ⟨1296256, by decide⟩ =
    .split (coordinate 11) (![⟨1296183, by decide⟩,⟨275013, by decide⟩,⟨1296211, by decide⟩,⟨1296255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92689_1296256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92689 ⟨1296256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92689
    ⟨1296256, by decide⟩ (by decide) (![⟨1296183, by decide⟩,⟨275013, by decide⟩,⟨1296211, by decide⟩,⟨1296255, by decide⟩]) unmarked_context_11_92689_1296256 node_context_11_92689_1296256
  intro a
  fin_cases a
  · exact context_12_370756_1296183
  · exact context_12_370757_275013
  · exact context_12_370758_1296211
  · exact context_12_370759_1296255

theorem selected_cut_46481 : selected 10 ⟨1296319, by decide⟩
    (prefixPartial 11 92690) = some ⟨11, 2, 0, 1296319, 92690, 3517, 262144⟩ := by
  decide +kernel

theorem context_11_92690_1296319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92690 ⟨1296319, by decide⟩ :=
  accepted_of_selected 11 92690 ⟨1296319, by decide⟩ ⟨11, 2, 0, 1296319, 92690, 3517, 262144⟩
    (by decide) selected_cut_46481

theorem selected_cut_46482 : selected 9 ⟨1296345, by decide⟩
    (prefixPartial 12 370764) = some ⟨12, 2, 0, 1296345, 370764, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_370764_1296345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370764 ⟨1296345, by decide⟩ :=
  accepted_of_selected 12 370764 ⟨1296345, by decide⟩ ⟨12, 2, 0, 1296345, 370764, 1549, 65536⟩
    (by decide) selected_cut_46482

theorem selected_cut_46483 : selected 9 ⟨1296375, by decide⟩
    (prefixPartial 12 370765) = some ⟨12, 2, 0, 1296375, 370765, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_370765_1296375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370765 ⟨1296375, by decide⟩ :=
  accepted_of_selected 12 370765 ⟨1296375, by decide⟩ ⟨12, 2, 0, 1296375, 370765, 1537, 65536⟩
    (by decide) selected_cut_46483

theorem selected_cut_46484 : selected 9 ⟨1296398, by decide⟩
    (prefixPartial 12 370766) = some ⟨12, 2, 0, 1296398, 370766, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_370766_1296398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370766 ⟨1296398, by decide⟩ :=
  accepted_of_selected 12 370766 ⟨1296398, by decide⟩ ⟨12, 2, 0, 1296398, 370766, 1505, 65536⟩
    (by decide) selected_cut_46484

theorem selected_cut_46485 : selected 9 ⟨1296435, by decide⟩
    (prefixPartial 12 370767) = some ⟨12, 2, 0, 1296435, 370767, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_370767_1296435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370767 ⟨1296435, by decide⟩ :=
  accepted_of_selected 12 370767 ⟨1296435, by decide⟩ ⟨12, 2, 0, 1296435, 370767, 1721, 65536⟩
    (by decide) selected_cut_46485

theorem unmarked_context_11_92691_1296436 : frontier 10 ⟨1296436, by decide⟩
    (prefixCache 11 92691) (prefixPartial 11 92691) = false := by
  decide +kernel

theorem node_context_11_92691_1296436 : EJMOriginalGlobalDAGData.nodes 10 ⟨1296436, by decide⟩ =
    .split (coordinate 11) (![⟨1296345, by decide⟩,⟨1296375, by decide⟩,⟨1296398, by decide⟩,⟨1296435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92691_1296436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92691 ⟨1296436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92691
    ⟨1296436, by decide⟩ (by decide) (![⟨1296345, by decide⟩,⟨1296375, by decide⟩,⟨1296398, by decide⟩,⟨1296435, by decide⟩]) unmarked_context_11_92691_1296436 node_context_11_92691_1296436
  intro a
  fin_cases a
  · exact context_12_370764_1296345
  · exact context_12_370765_1296375
  · exact context_12_370766_1296398
  · exact context_12_370767_1296435

theorem unmarked_context_10_23172_1296437 : frontier 11 ⟨1296437, by decide⟩
    (prefixCache 10 23172) (prefixPartial 10 23172) = false := by
  decide +kernel

theorem node_context_10_23172_1296437 : EJMOriginalGlobalDAGData.nodes 11 ⟨1296437, by decide⟩ =
    .split (coordinate 10) (![⟨1296145, by decide⟩,⟨1296256, by decide⟩,⟨1296319, by decide⟩,⟨1296436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23172_1296437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23172 ⟨1296437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23172
    ⟨1296437, by decide⟩ (by decide) (![⟨1296145, by decide⟩,⟨1296256, by decide⟩,⟨1296319, by decide⟩,⟨1296436, by decide⟩]) unmarked_context_10_23172_1296437 node_context_10_23172_1296437
  intro a
  fin_cases a
  · exact context_11_92688_1296145
  · exact context_11_92689_1296256
  · exact context_11_92690_1296319
  · exact context_11_92691_1296436

theorem selected_cut_46486 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23173) = some ⟨10, 1, 0, 893098, 23173, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23173_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23173 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23173 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23173, 1, 1048576⟩
    (by decide) selected_cut_46486

theorem selected_cut_46487 : selected 10 ⟨1296475, by decide⟩
    (prefixPartial 11 92696) = some ⟨11, 2, 0, 1296475, 92696, 2421, 262144⟩ := by
  decide +kernel

theorem context_11_92696_1296475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92696 ⟨1296475, by decide⟩ :=
  accepted_of_selected 11 92696 ⟨1296475, by decide⟩ ⟨11, 2, 0, 1296475, 92696, 2421, 262144⟩
    (by decide) selected_cut_46487

theorem selected_cut_46488 : selected 9 ⟨1296497, by decide⟩
    (prefixPartial 12 370788) = some ⟨12, 2, 0, 1296497, 370788, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_370788_1296497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370788 ⟨1296497, by decide⟩ :=
  accepted_of_selected 12 370788 ⟨1296497, by decide⟩ ⟨12, 2, 0, 1296497, 370788, 1517, 65536⟩
    (by decide) selected_cut_46488

theorem selected_cut_46489 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 370789) = some ⟨12, 1, 0, 1256866, 370789, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370789_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370789 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 370789 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 370789, 1, 65536⟩
    (by decide) selected_cut_46489

theorem selected_cut_46490 : selected 9 ⟨1296517, by decide⟩
    (prefixPartial 12 370790) = some ⟨12, 2, 0, 1296517, 370790, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_370790_1296517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370790 ⟨1296517, by decide⟩ :=
  accepted_of_selected 12 370790 ⟨1296517, by decide⟩ ⟨12, 2, 0, 1296517, 370790, 1349, 65536⟩
    (by decide) selected_cut_46490

theorem selected_cut_46491 : selected 9 ⟨1296543, by decide⟩
    (prefixPartial 12 370791) = some ⟨12, 2, 0, 1296543, 370791, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_370791_1296543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370791 ⟨1296543, by decide⟩ :=
  accepted_of_selected 12 370791 ⟨1296543, by decide⟩ ⟨12, 2, 0, 1296543, 370791, 1501, 65536⟩
    (by decide) selected_cut_46491

theorem unmarked_context_11_92697_1296544 : frontier 10 ⟨1296544, by decide⟩
    (prefixCache 11 92697) (prefixPartial 11 92697) = false := by
  decide +kernel

theorem node_context_11_92697_1296544 : EJMOriginalGlobalDAGData.nodes 10 ⟨1296544, by decide⟩ =
    .split (coordinate 11) (![⟨1296497, by decide⟩,⟨1256866, by decide⟩,⟨1296517, by decide⟩,⟨1296543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92697_1296544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92697 ⟨1296544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92697
    ⟨1296544, by decide⟩ (by decide) (![⟨1296497, by decide⟩,⟨1256866, by decide⟩,⟨1296517, by decide⟩,⟨1296543, by decide⟩]) unmarked_context_11_92697_1296544 node_context_11_92697_1296544
  intro a
  fin_cases a
  · exact context_12_370788_1296497
  · exact context_12_370789_1256866
  · exact context_12_370790_1296517
  · exact context_12_370791_1296543

theorem selected_cut_46492 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92698) = some ⟨11, 1, 0, 900587, 92698, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92698_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92698 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92698 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92698, 1, 262144⟩
    (by decide) selected_cut_46492

theorem selected_cut_46493 : selected 10 ⟨1296594, by decide⟩
    (prefixPartial 11 92699) = some ⟨11, 2, 0, 1296594, 92699, 3573, 262144⟩ := by
  decide +kernel

theorem context_11_92699_1296594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92699 ⟨1296594, by decide⟩ :=
  accepted_of_selected 11 92699 ⟨1296594, by decide⟩ ⟨11, 2, 0, 1296594, 92699, 3573, 262144⟩
    (by decide) selected_cut_46493

theorem unmarked_context_10_23174_1296595 : frontier 11 ⟨1296595, by decide⟩
    (prefixCache 10 23174) (prefixPartial 10 23174) = false := by
  decide +kernel

theorem node_context_10_23174_1296595 : EJMOriginalGlobalDAGData.nodes 11 ⟨1296595, by decide⟩ =
    .split (coordinate 10) (![⟨1296475, by decide⟩,⟨1296544, by decide⟩,⟨900587, by decide⟩,⟨1296594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23174_1296595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23174 ⟨1296595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23174
    ⟨1296595, by decide⟩ (by decide) (![⟨1296475, by decide⟩,⟨1296544, by decide⟩,⟨900587, by decide⟩,⟨1296594, by decide⟩]) unmarked_context_10_23174_1296595 node_context_10_23174_1296595
  intro a
  fin_cases a
  · exact context_11_92696_1296475
  · exact context_11_92697_1296544
  · exact context_11_92698_900587
  · exact context_11_92699_1296594

theorem selected_cut_46494 : selected 10 ⟨1296652, by decide⟩
    (prefixPartial 11 92700) = some ⟨11, 2, 0, 1296652, 92700, 3645, 262144⟩ := by
  decide +kernel

theorem context_11_92700_1296652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92700 ⟨1296652, by decide⟩ :=
  accepted_of_selected 11 92700 ⟨1296652, by decide⟩ ⟨11, 2, 0, 1296652, 92700, 3645, 262144⟩
    (by decide) selected_cut_46494

theorem selected_cut_46495 : selected 9 ⟨1296670, by decide⟩
    (prefixPartial 12 370804) = some ⟨12, 2, 0, 1296670, 370804, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_370804_1296670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370804 ⟨1296670, by decide⟩ :=
  accepted_of_selected 12 370804 ⟨1296670, by decide⟩ ⟨12, 2, 0, 1296670, 370804, 1385, 65536⟩
    (by decide) selected_cut_46495

theorem selected_cut_46496 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 370805) = some ⟨12, 1, 0, 1257136, 370805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370805_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370805 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 370805 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 370805, 1, 65536⟩
    (by decide) selected_cut_46496

theorem selected_cut_46497 : selected 9 ⟨1296690, by decide⟩
    (prefixPartial 12 370806) = some ⟨12, 2, 0, 1296690, 370806, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_370806_1296690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370806 ⟨1296690, by decide⟩ :=
  accepted_of_selected 12 370806 ⟨1296690, by decide⟩ ⟨12, 2, 0, 1296690, 370806, 1269, 65536⟩
    (by decide) selected_cut_46497

theorem selected_cut_46498 : selected 9 ⟨1296711, by decide⟩
    (prefixPartial 12 370807) = some ⟨12, 2, 0, 1296711, 370807, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_370807_1296711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370807 ⟨1296711, by decide⟩ :=
  accepted_of_selected 12 370807 ⟨1296711, by decide⟩ ⟨12, 2, 0, 1296711, 370807, 1441, 65536⟩
    (by decide) selected_cut_46498

theorem unmarked_context_11_92701_1296712 : frontier 10 ⟨1296712, by decide⟩
    (prefixCache 11 92701) (prefixPartial 11 92701) = false := by
  decide +kernel

theorem node_context_11_92701_1296712 : EJMOriginalGlobalDAGData.nodes 10 ⟨1296712, by decide⟩ =
    .split (coordinate 11) (![⟨1296670, by decide⟩,⟨1257136, by decide⟩,⟨1296690, by decide⟩,⟨1296711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92701_1296712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92701 ⟨1296712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92701
    ⟨1296712, by decide⟩ (by decide) (![⟨1296670, by decide⟩,⟨1257136, by decide⟩,⟨1296690, by decide⟩,⟨1296711, by decide⟩]) unmarked_context_11_92701_1296712 node_context_11_92701_1296712
  intro a
  fin_cases a
  · exact context_12_370804_1296670
  · exact context_12_370805_1257136
  · exact context_12_370806_1296690
  · exact context_12_370807_1296711

theorem selected_cut_46499 : selected 9 ⟨1296731, by decide⟩
    (prefixPartial 12 370808) = some ⟨12, 2, 0, 1296731, 370808, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_370808_1296731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370808 ⟨1296731, by decide⟩ :=
  accepted_of_selected 12 370808 ⟨1296731, by decide⟩ ⟨12, 2, 0, 1296731, 370808, 1153, 65536⟩
    (by decide) selected_cut_46499

theorem selected_cut_46500 : selected 9 ⟨1296745, by decide⟩
    (prefixPartial 12 370809) = some ⟨12, 2, 0, 1296745, 370809, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_370809_1296745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370809 ⟨1296745, by decide⟩ :=
  accepted_of_selected 12 370809 ⟨1296745, by decide⟩ ⟨12, 2, 0, 1296745, 370809, 1185, 65536⟩
    (by decide) selected_cut_46500

theorem selected_cut_46501 : selected 9 ⟨1296765, by decide⟩
    (prefixPartial 12 370810) = some ⟨12, 2, 0, 1296765, 370810, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_370810_1296765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370810 ⟨1296765, by decide⟩ :=
  accepted_of_selected 12 370810 ⟨1296765, by decide⟩ ⟨12, 2, 0, 1296765, 370810, 1057, 65536⟩
    (by decide) selected_cut_46501

theorem selected_cut_46502 : selected 9 ⟨1296782, by decide⟩
    (prefixPartial 12 370811) = some ⟨12, 2, 0, 1296782, 370811, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_370811_1296782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370811 ⟨1296782, by decide⟩ :=
  accepted_of_selected 12 370811 ⟨1296782, by decide⟩ ⟨12, 2, 0, 1296782, 370811, 1165, 65536⟩
    (by decide) selected_cut_46502

theorem unmarked_context_11_92702_1296783 : frontier 10 ⟨1296783, by decide⟩
    (prefixCache 11 92702) (prefixPartial 11 92702) = false := by
  decide +kernel

theorem node_context_11_92702_1296783 : EJMOriginalGlobalDAGData.nodes 10 ⟨1296783, by decide⟩ =
    .split (coordinate 11) (![⟨1296731, by decide⟩,⟨1296745, by decide⟩,⟨1296765, by decide⟩,⟨1296782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92702_1296783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92702 ⟨1296783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92702
    ⟨1296783, by decide⟩ (by decide) (![⟨1296731, by decide⟩,⟨1296745, by decide⟩,⟨1296765, by decide⟩,⟨1296782, by decide⟩]) unmarked_context_11_92702_1296783 node_context_11_92702_1296783
  intro a
  fin_cases a
  · exact context_12_370808_1296731
  · exact context_12_370809_1296745
  · exact context_12_370810_1296765
  · exact context_12_370811_1296782

theorem selected_cut_46503 : selected 10 ⟨1296832, by decide⟩
    (prefixPartial 11 92703) = some ⟨11, 2, 0, 1296832, 92703, 3009, 262144⟩ := by
  decide +kernel

theorem context_11_92703_1296832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92703 ⟨1296832, by decide⟩ :=
  accepted_of_selected 11 92703 ⟨1296832, by decide⟩ ⟨11, 2, 0, 1296832, 92703, 3009, 262144⟩
    (by decide) selected_cut_46503

theorem unmarked_context_10_23175_1296833 : frontier 11 ⟨1296833, by decide⟩
    (prefixCache 10 23175) (prefixPartial 10 23175) = false := by
  decide +kernel

theorem node_context_10_23175_1296833 : EJMOriginalGlobalDAGData.nodes 11 ⟨1296833, by decide⟩ =
    .split (coordinate 10) (![⟨1296652, by decide⟩,⟨1296712, by decide⟩,⟨1296783, by decide⟩,⟨1296832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23175_1296833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23175 ⟨1296833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23175
    ⟨1296833, by decide⟩ (by decide) (![⟨1296652, by decide⟩,⟨1296712, by decide⟩,⟨1296783, by decide⟩,⟨1296832, by decide⟩]) unmarked_context_10_23175_1296833 node_context_10_23175_1296833
  intro a
  fin_cases a
  · exact context_11_92700_1296652
  · exact context_11_92701_1296712
  · exact context_11_92702_1296783
  · exact context_11_92703_1296832

theorem unmarked_context_9_5793_1296834 : frontier 12 ⟨1296834, by decide⟩
    (prefixCache 9 5793) (prefixPartial 9 5793) = false := by
  decide +kernel

theorem node_context_9_5793_1296834 : EJMOriginalGlobalDAGData.nodes 12 ⟨1296834, by decide⟩ =
    .split (coordinate 9) (![⟨1296437, by decide⟩,⟨893098, by decide⟩,⟨1296595, by decide⟩,⟨1296833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5793_1296834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5793 ⟨1296834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5793
    ⟨1296834, by decide⟩ (by decide) (![⟨1296437, by decide⟩,⟨893098, by decide⟩,⟨1296595, by decide⟩,⟨1296833, by decide⟩]) unmarked_context_9_5793_1296834 node_context_9_5793_1296834
  intro a
  fin_cases a
  · exact context_10_23172_1296437
  · exact context_10_23173_893098
  · exact context_10_23174_1296595
  · exact context_10_23175_1296833

theorem selected_cut_46504 : selected 10 ⟨1296858, by decide⟩
    (prefixPartial 11 92704) = some ⟨11, 2, 0, 1296858, 92704, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_92704_1296858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92704 ⟨1296858, by decide⟩ :=
  accepted_of_selected 11 92704 ⟨1296858, by decide⟩ ⟨11, 2, 0, 1296858, 92704, 1089, 262144⟩
    (by decide) selected_cut_46504

theorem selected_cut_46505 : selected 10 ⟨1296942, by decide⟩
    (prefixPartial 11 92705) = some ⟨11, 2, 0, 1296942, 92705, 2849, 262144⟩ := by
  decide +kernel

theorem context_11_92705_1296942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92705 ⟨1296942, by decide⟩ :=
  accepted_of_selected 11 92705 ⟨1296942, by decide⟩ ⟨11, 2, 0, 1296942, 92705, 2849, 262144⟩
    (by decide) selected_cut_46505

theorem selected_cut_46506 : selected 10 ⟨1296993, by decide⟩
    (prefixPartial 11 92706) = some ⟨11, 2, 0, 1296993, 92706, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_92706_1296993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92706 ⟨1296993, by decide⟩ :=
  accepted_of_selected 11 92706 ⟨1296993, by decide⟩ ⟨11, 2, 0, 1296993, 92706, 3181, 262144⟩
    (by decide) selected_cut_46506

theorem selected_cut_46507 : selected 10 ⟨1297035, by decide⟩
    (prefixPartial 11 92707) = some ⟨11, 2, 0, 1297035, 92707, 3049, 262144⟩ := by
  decide +kernel

theorem context_11_92707_1297035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92707 ⟨1297035, by decide⟩ :=
  accepted_of_selected 11 92707 ⟨1297035, by decide⟩ ⟨11, 2, 0, 1297035, 92707, 3049, 262144⟩
    (by decide) selected_cut_46507

theorem unmarked_context_10_23176_1297036 : frontier 11 ⟨1297036, by decide⟩
    (prefixCache 10 23176) (prefixPartial 10 23176) = false := by
  decide +kernel

theorem node_context_10_23176_1297036 : EJMOriginalGlobalDAGData.nodes 11 ⟨1297036, by decide⟩ =
    .split (coordinate 10) (![⟨1296858, by decide⟩,⟨1296942, by decide⟩,⟨1296993, by decide⟩,⟨1297035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23176_1297036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23176 ⟨1297036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23176
    ⟨1297036, by decide⟩ (by decide) (![⟨1296858, by decide⟩,⟨1296942, by decide⟩,⟨1296993, by decide⟩,⟨1297035, by decide⟩]) unmarked_context_10_23176_1297036 node_context_10_23176_1297036
  intro a
  fin_cases a
  · exact context_11_92704_1296858
  · exact context_11_92705_1296942
  · exact context_11_92706_1296993
  · exact context_11_92707_1297035

theorem selected_cut_46508 : selected 10 ⟨1297061, by decide⟩
    (prefixPartial 11 92708) = some ⟨11, 2, 0, 1297061, 92708, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_92708_1297061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92708 ⟨1297061, by decide⟩ :=
  accepted_of_selected 11 92708 ⟨1297061, by decide⟩ ⟨11, 2, 0, 1297061, 92708, 1801, 262144⟩
    (by decide) selected_cut_46508

theorem selected_cut_46509 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 92709) = some ⟨11, 1, 0, 1192826, 92709, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92709_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92709 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 92709 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 92709, 1, 262144⟩
    (by decide) selected_cut_46509

theorem selected_cut_46510 : selected 10 ⟨1297098, by decide⟩
    (prefixPartial 11 92710) = some ⟨11, 2, 0, 1297098, 92710, 2557, 262144⟩ := by
  decide +kernel

theorem context_11_92710_1297098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92710 ⟨1297098, by decide⟩ :=
  accepted_of_selected 11 92710 ⟨1297098, by decide⟩ ⟨11, 2, 0, 1297098, 92710, 2557, 262144⟩
    (by decide) selected_cut_46510

theorem selected_cut_46511 : selected 10 ⟨1297133, by decide⟩
    (prefixPartial 11 92711) = some ⟨11, 2, 0, 1297133, 92711, 2453, 262144⟩ := by
  decide +kernel

theorem context_11_92711_1297133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92711 ⟨1297133, by decide⟩ :=
  accepted_of_selected 11 92711 ⟨1297133, by decide⟩ ⟨11, 2, 0, 1297133, 92711, 2453, 262144⟩
    (by decide) selected_cut_46511

theorem unmarked_context_10_23177_1297134 : frontier 11 ⟨1297134, by decide⟩
    (prefixCache 10 23177) (prefixPartial 10 23177) = false := by
  decide +kernel

theorem node_context_10_23177_1297134 : EJMOriginalGlobalDAGData.nodes 11 ⟨1297134, by decide⟩ =
    .split (coordinate 10) (![⟨1297061, by decide⟩,⟨1192826, by decide⟩,⟨1297098, by decide⟩,⟨1297133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23177_1297134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23177 ⟨1297134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23177
    ⟨1297134, by decide⟩ (by decide) (![⟨1297061, by decide⟩,⟨1192826, by decide⟩,⟨1297098, by decide⟩,⟨1297133, by decide⟩]) unmarked_context_10_23177_1297134 node_context_10_23177_1297134
  intro a
  fin_cases a
  · exact context_11_92708_1297061
  · exact context_11_92709_1192826
  · exact context_11_92710_1297098
  · exact context_11_92711_1297133

theorem selected_cut_46512 : selected 11 ⟨1297174, by decide⟩
    (prefixPartial 10 23178) = some ⟨10, 2, 0, 1297174, 23178, 2353, 1048576⟩ := by
  decide +kernel

theorem context_10_23178_1297174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23178 ⟨1297174, by decide⟩ :=
  accepted_of_selected 10 23178 ⟨1297174, by decide⟩ ⟨10, 2, 0, 1297174, 23178, 2353, 1048576⟩
    (by decide) selected_cut_46512

theorem selected_cut_46513 : selected 10 ⟨1297191, by decide⟩
    (prefixPartial 11 92716) = some ⟨11, 2, 0, 1297191, 92716, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_92716_1297191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92716 ⟨1297191, by decide⟩ :=
  accepted_of_selected 11 92716 ⟨1297191, by decide⟩ ⟨11, 2, 0, 1297191, 92716, 1277, 262144⟩
    (by decide) selected_cut_46513

theorem selected_cut_46514 : selected 10 ⟨1297225, by decide⟩
    (prefixPartial 11 92717) = some ⟨11, 2, 0, 1297225, 92717, 2037, 262144⟩ := by
  decide +kernel

theorem context_11_92717_1297225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92717 ⟨1297225, by decide⟩ :=
  accepted_of_selected 11 92717 ⟨1297225, by decide⟩ ⟨11, 2, 0, 1297225, 92717, 2037, 262144⟩
    (by decide) selected_cut_46514

theorem selected_cut_46515 : selected 10 ⟨1297247, by decide⟩
    (prefixPartial 11 92718) = some ⟨11, 2, 0, 1297247, 92718, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_92718_1297247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92718 ⟨1297247, by decide⟩ :=
  accepted_of_selected 11 92718 ⟨1297247, by decide⟩ ⟨11, 2, 0, 1297247, 92718, 1609, 262144⟩
    (by decide) selected_cut_46515

theorem selected_cut_46516 : selected 10 ⟨1297262, by decide⟩
    (prefixPartial 11 92719) = some ⟨11, 2, 0, 1297262, 92719, 1005, 262144⟩ := by
  decide +kernel

theorem context_11_92719_1297262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92719 ⟨1297262, by decide⟩ :=
  accepted_of_selected 11 92719 ⟨1297262, by decide⟩ ⟨11, 2, 0, 1297262, 92719, 1005, 262144⟩
    (by decide) selected_cut_46516

theorem unmarked_context_10_23179_1297263 : frontier 11 ⟨1297263, by decide⟩
    (prefixCache 10 23179) (prefixPartial 10 23179) = false := by
  decide +kernel

theorem node_context_10_23179_1297263 : EJMOriginalGlobalDAGData.nodes 11 ⟨1297263, by decide⟩ =
    .split (coordinate 10) (![⟨1297191, by decide⟩,⟨1297225, by decide⟩,⟨1297247, by decide⟩,⟨1297262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23179_1297263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23179 ⟨1297263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23179
    ⟨1297263, by decide⟩ (by decide) (![⟨1297191, by decide⟩,⟨1297225, by decide⟩,⟨1297247, by decide⟩,⟨1297262, by decide⟩]) unmarked_context_10_23179_1297263 node_context_10_23179_1297263
  intro a
  fin_cases a
  · exact context_11_92716_1297191
  · exact context_11_92717_1297225
  · exact context_11_92718_1297247
  · exact context_11_92719_1297262

theorem unmarked_context_9_5794_1297264 : frontier 12 ⟨1297264, by decide⟩
    (prefixCache 9 5794) (prefixPartial 9 5794) = false := by
  decide +kernel

theorem node_context_9_5794_1297264 : EJMOriginalGlobalDAGData.nodes 12 ⟨1297264, by decide⟩ =
    .split (coordinate 9) (![⟨1297036, by decide⟩,⟨1297134, by decide⟩,⟨1297174, by decide⟩,⟨1297263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5794_1297264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5794 ⟨1297264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5794
    ⟨1297264, by decide⟩ (by decide) (![⟨1297036, by decide⟩,⟨1297134, by decide⟩,⟨1297174, by decide⟩,⟨1297263, by decide⟩]) unmarked_context_9_5794_1297264 node_context_9_5794_1297264
  intro a
  fin_cases a
  · exact context_10_23176_1297036
  · exact context_10_23177_1297134
  · exact context_10_23178_1297174
  · exact context_10_23179_1297263

theorem selected_cut_46517 : selected 10 ⟨1297279, by decide⟩
    (prefixPartial 11 92720) = some ⟨11, 2, 0, 1297279, 92720, 1037, 262144⟩ := by
  decide +kernel

theorem context_11_92720_1297279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92720 ⟨1297279, by decide⟩ :=
  accepted_of_selected 11 92720 ⟨1297279, by decide⟩ ⟨11, 2, 0, 1297279, 92720, 1037, 262144⟩
    (by decide) selected_cut_46517

theorem selected_cut_46518 : selected 10 ⟨1297313, by decide⟩
    (prefixPartial 11 92721) = some ⟨11, 2, 0, 1297313, 92721, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_92721_1297313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92721 ⟨1297313, by decide⟩ :=
  accepted_of_selected 11 92721 ⟨1297313, by decide⟩ ⟨11, 2, 0, 1297313, 92721, 2225, 262144⟩
    (by decide) selected_cut_46518

theorem selected_cut_46519 : selected 10 ⟨1297339, by decide⟩
    (prefixPartial 11 92722) = some ⟨11, 2, 0, 1297339, 92722, 1477, 262144⟩ := by
  decide +kernel

theorem context_11_92722_1297339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92722 ⟨1297339, by decide⟩ :=
  accepted_of_selected 11 92722 ⟨1297339, by decide⟩ ⟨11, 2, 0, 1297339, 92722, 1477, 262144⟩
    (by decide) selected_cut_46519

theorem selected_cut_46520 : selected 10 ⟨1297360, by decide⟩
    (prefixPartial 11 92723) = some ⟨11, 2, 0, 1297360, 92723, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_92723_1297360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92723 ⟨1297360, by decide⟩ :=
  accepted_of_selected 11 92723 ⟨1297360, by decide⟩ ⟨11, 2, 0, 1297360, 92723, 1425, 262144⟩
    (by decide) selected_cut_46520

theorem unmarked_context_10_23180_1297361 : frontier 11 ⟨1297361, by decide⟩
    (prefixCache 10 23180) (prefixPartial 10 23180) = false := by
  decide +kernel

theorem node_context_10_23180_1297361 : EJMOriginalGlobalDAGData.nodes 11 ⟨1297361, by decide⟩ =
    .split (coordinate 10) (![⟨1297279, by decide⟩,⟨1297313, by decide⟩,⟨1297339, by decide⟩,⟨1297360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23180_1297361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23180 ⟨1297361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23180
    ⟨1297361, by decide⟩ (by decide) (![⟨1297279, by decide⟩,⟨1297313, by decide⟩,⟨1297339, by decide⟩,⟨1297360, by decide⟩]) unmarked_context_10_23180_1297361 node_context_10_23180_1297361
  intro a
  fin_cases a
  · exact context_11_92720_1297279
  · exact context_11_92721_1297313
  · exact context_11_92722_1297339
  · exact context_11_92723_1297360

theorem selected_cut_46521 : selected 11 ⟨1297417, by decide⟩
    (prefixPartial 10 23181) = some ⟨10, 2, 0, 1297417, 23181, 3881, 1048576⟩ := by
  decide +kernel

theorem context_10_23181_1297417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23181 ⟨1297417, by decide⟩ :=
  accepted_of_selected 10 23181 ⟨1297417, by decide⟩ ⟨10, 2, 0, 1297417, 23181, 3881, 1048576⟩
    (by decide) selected_cut_46521

theorem selected_cut_46522 : selected 11 ⟨1297447, by decide⟩
    (prefixPartial 10 23182) = some ⟨10, 2, 0, 1297447, 23182, 1617, 1048576⟩ := by
  decide +kernel

theorem context_10_23182_1297447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23182 ⟨1297447, by decide⟩ :=
  accepted_of_selected 10 23182 ⟨1297447, by decide⟩ ⟨10, 2, 0, 1297447, 23182, 1617, 1048576⟩
    (by decide) selected_cut_46522

theorem selected_cut_46523 : selected 11 ⟨1297455, by decide⟩
    (prefixPartial 10 23183) = some ⟨10, 2, 0, 1297455, 23183, 373, 1048576⟩ := by
  decide +kernel

theorem context_10_23183_1297455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23183 ⟨1297455, by decide⟩ :=
  accepted_of_selected 10 23183 ⟨1297455, by decide⟩ ⟨10, 2, 0, 1297455, 23183, 373, 1048576⟩
    (by decide) selected_cut_46523

theorem unmarked_context_9_5795_1297456 : frontier 12 ⟨1297456, by decide⟩
    (prefixCache 9 5795) (prefixPartial 9 5795) = false := by
  decide +kernel

theorem node_context_9_5795_1297456 : EJMOriginalGlobalDAGData.nodes 12 ⟨1297456, by decide⟩ =
    .split (coordinate 9) (![⟨1297361, by decide⟩,⟨1297417, by decide⟩,⟨1297447, by decide⟩,⟨1297455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5795_1297456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5795 ⟨1297456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5795
    ⟨1297456, by decide⟩ (by decide) (![⟨1297361, by decide⟩,⟨1297417, by decide⟩,⟨1297447, by decide⟩,⟨1297455, by decide⟩]) unmarked_context_9_5795_1297456 node_context_9_5795_1297456
  intro a
  fin_cases a
  · exact context_10_23180_1297361
  · exact context_10_23181_1297417
  · exact context_10_23182_1297447
  · exact context_10_23183_1297455

theorem unmarked_context_8_1448_1297457 : frontier 13 ⟨1297457, by decide⟩
    (prefixCache 8 1448) (prefixPartial 8 1448) = false := by
  decide +kernel

theorem node_context_8_1448_1297457 : EJMOriginalGlobalDAGData.nodes 13 ⟨1297457, by decide⟩ =
    .split (coordinate 8) (![⟨1296078, by decide⟩,⟨1296834, by decide⟩,⟨1297264, by decide⟩,⟨1297456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1448_1297457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1448 ⟨1297457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1448
    ⟨1297457, by decide⟩ (by decide) (![⟨1296078, by decide⟩,⟨1296834, by decide⟩,⟨1297264, by decide⟩,⟨1297456, by decide⟩]) unmarked_context_8_1448_1297457 node_context_8_1448_1297457
  intro a
  fin_cases a
  · exact context_9_5792_1296078
  · exact context_9_5793_1296834
  · exact context_9_5794_1297264
  · exact context_9_5795_1297456

theorem selected_cut_46524 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92736) = some ⟨11, 1, 0, 434745, 92736, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92736_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92736 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92736 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92736, 1, 262144⟩
    (by decide) selected_cut_46524

theorem selected_cut_46525 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370948) = some ⟨12, 1, 0, 448748, 370948, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370948_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370948 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370948 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370948, 1, 65536⟩
    (by decide) selected_cut_46525

theorem selected_cut_46526 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 370949) = some ⟨12, 1, 0, 34034, 370949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370949_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370949 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 370949 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 370949, 1, 65536⟩
    (by decide) selected_cut_46526

theorem selected_cut_46527 : selected 9 ⟨1297511, by decide⟩
    (prefixPartial 12 370950) = some ⟨12, 2, 0, 1297511, 370950, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_370950_1297511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370950 ⟨1297511, by decide⟩ :=
  accepted_of_selected 12 370950 ⟨1297511, by decide⟩ ⟨12, 2, 0, 1297511, 370950, 1629, 65536⟩
    (by decide) selected_cut_46527

theorem selected_cut_46528 : selected 9 ⟨1297567, by decide⟩
    (prefixPartial 12 370951) = some ⟨12, 2, 0, 1297567, 370951, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_370951_1297567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370951 ⟨1297567, by decide⟩ :=
  accepted_of_selected 12 370951 ⟨1297567, by decide⟩ ⟨12, 2, 0, 1297567, 370951, 3117, 65536⟩
    (by decide) selected_cut_46528

theorem unmarked_context_11_92737_1297568 : frontier 10 ⟨1297568, by decide⟩
    (prefixCache 11 92737) (prefixPartial 11 92737) = false := by
  decide +kernel

theorem node_context_11_92737_1297568 : EJMOriginalGlobalDAGData.nodes 10 ⟨1297568, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1297511, by decide⟩,⟨1297567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92737_1297568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92737 ⟨1297568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92737
    ⟨1297568, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1297511, by decide⟩,⟨1297567, by decide⟩]) unmarked_context_11_92737_1297568 node_context_11_92737_1297568
  intro a
  fin_cases a
  · exact context_12_370948_448748
  · exact context_12_370949_34034
  · exact context_12_370950_1297511
  · exact context_12_370951_1297567

theorem selected_cut_46529 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370952) = some ⟨12, 1, 0, 448748, 370952, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370952_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370952 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370952 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370952, 1, 65536⟩
    (by decide) selected_cut_46529

theorem selected_cut_46530 : selected 9 ⟨1297649, by decide⟩
    (prefixPartial 12 370953) = some ⟨12, 2, 0, 1297649, 370953, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_370953_1297649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370953 ⟨1297649, by decide⟩ :=
  accepted_of_selected 12 370953 ⟨1297649, by decide⟩ ⟨12, 2, 0, 1297649, 370953, 3453, 65536⟩
    (by decide) selected_cut_46530

theorem selected_cut_46531 : selected 9 ⟨1297698, by decide⟩
    (prefixPartial 12 370954) = some ⟨12, 2, 0, 1297698, 370954, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_370954_1297698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370954 ⟨1297698, by decide⟩ :=
  accepted_of_selected 12 370954 ⟨1297698, by decide⟩ ⟨12, 2, 0, 1297698, 370954, 2669, 65536⟩
    (by decide) selected_cut_46531

theorem selected_cut_46532 : selected 9 ⟨1297751, by decide⟩
    (prefixPartial 12 370955) = some ⟨12, 2, 0, 1297751, 370955, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_370955_1297751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370955 ⟨1297751, by decide⟩ :=
  accepted_of_selected 12 370955 ⟨1297751, by decide⟩ ⟨12, 2, 0, 1297751, 370955, 3029, 65536⟩
    (by decide) selected_cut_46532

theorem unmarked_context_11_92738_1297752 : frontier 10 ⟨1297752, by decide⟩
    (prefixCache 11 92738) (prefixPartial 11 92738) = false := by
  decide +kernel

theorem node_context_11_92738_1297752 : EJMOriginalGlobalDAGData.nodes 10 ⟨1297752, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1297649, by decide⟩,⟨1297698, by decide⟩,⟨1297751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92738_1297752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92738 ⟨1297752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92738
    ⟨1297752, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1297649, by decide⟩,⟨1297698, by decide⟩,⟨1297751, by decide⟩]) unmarked_context_11_92738_1297752 node_context_11_92738_1297752
  intro a
  fin_cases a
  · exact context_12_370952_448748
  · exact context_12_370953_1297649
  · exact context_12_370954_1297698
  · exact context_12_370955_1297751

theorem selected_cut_46533 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370956) = some ⟨12, 1, 0, 448748, 370956, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370956_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370956 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370956 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370956, 1, 65536⟩
    (by decide) selected_cut_46533

theorem selected_cut_46534 : selected 9 ⟨1297800, by decide⟩
    (prefixPartial 12 370957) = some ⟨12, 2, 0, 1297800, 370957, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_370957_1297800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370957 ⟨1297800, by decide⟩ :=
  accepted_of_selected 12 370957 ⟨1297800, by decide⟩ ⟨12, 2, 0, 1297800, 370957, 2981, 65536⟩
    (by decide) selected_cut_46534

theorem selected_cut_46535 : selected 9 ⟨1297844, by decide⟩
    (prefixPartial 12 370958) = some ⟨12, 2, 0, 1297844, 370958, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_370958_1297844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370958 ⟨1297844, by decide⟩ :=
  accepted_of_selected 12 370958 ⟨1297844, by decide⟩ ⟨12, 2, 0, 1297844, 370958, 2501, 65536⟩
    (by decide) selected_cut_46535

theorem selected_cut_46536 : selected 9 ⟨1297892, by decide⟩
    (prefixPartial 12 370959) = some ⟨12, 2, 0, 1297892, 370959, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_370959_1297892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370959 ⟨1297892, by decide⟩ :=
  accepted_of_selected 12 370959 ⟨1297892, by decide⟩ ⟨12, 2, 0, 1297892, 370959, 2917, 65536⟩
    (by decide) selected_cut_46536

theorem unmarked_context_11_92739_1297893 : frontier 10 ⟨1297893, by decide⟩
    (prefixCache 11 92739) (prefixPartial 11 92739) = false := by
  decide +kernel

theorem node_context_11_92739_1297893 : EJMOriginalGlobalDAGData.nodes 10 ⟨1297893, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1297800, by decide⟩,⟨1297844, by decide⟩,⟨1297892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92739_1297893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92739 ⟨1297893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92739
    ⟨1297893, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1297800, by decide⟩,⟨1297844, by decide⟩,⟨1297892, by decide⟩]) unmarked_context_11_92739_1297893 node_context_11_92739_1297893
  intro a
  fin_cases a
  · exact context_12_370956_448748
  · exact context_12_370957_1297800
  · exact context_12_370958_1297844
  · exact context_12_370959_1297892

theorem unmarked_context_10_23184_1297894 : frontier 11 ⟨1297894, by decide⟩
    (prefixCache 10 23184) (prefixPartial 10 23184) = false := by
  decide +kernel

theorem node_context_10_23184_1297894 : EJMOriginalGlobalDAGData.nodes 11 ⟨1297894, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1297568, by decide⟩,⟨1297752, by decide⟩,⟨1297893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23184_1297894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23184 ⟨1297894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23184
    ⟨1297894, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1297568, by decide⟩,⟨1297752, by decide⟩,⟨1297893, by decide⟩]) unmarked_context_10_23184_1297894 node_context_10_23184_1297894
  intro a
  fin_cases a
  · exact context_11_92736_434745
  · exact context_11_92737_1297568
  · exact context_11_92738_1297752
  · exact context_11_92739_1297893

theorem selected_cut_46537 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 370960) = some ⟨12, 1, 0, 307381, 370960, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370960_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370960 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 370960 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 370960, 1, 65536⟩
    (by decide) selected_cut_46537

theorem selected_cut_46538 : selected 9 ⟨1297944, by decide⟩
    (prefixPartial 12 370961) = some ⟨12, 2, 0, 1297944, 370961, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_370961_1297944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370961 ⟨1297944, by decide⟩ :=
  accepted_of_selected 12 370961 ⟨1297944, by decide⟩ ⟨12, 2, 0, 1297944, 370961, 2821, 65536⟩
    (by decide) selected_cut_46538

theorem selected_cut_46539 : selected 9 ⟨1297981, by decide⟩
    (prefixPartial 12 370962) = some ⟨12, 2, 0, 1297981, 370962, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_370962_1297981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370962 ⟨1297981, by decide⟩ :=
  accepted_of_selected 12 370962 ⟨1297981, by decide⟩ ⟨12, 2, 0, 1297981, 370962, 2237, 65536⟩
    (by decide) selected_cut_46539

theorem selected_cut_46540 : selected 9 ⟨1298020, by decide⟩
    (prefixPartial 12 370963) = some ⟨12, 2, 0, 1298020, 370963, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_370963_1298020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370963 ⟨1298020, by decide⟩ :=
  accepted_of_selected 12 370963 ⟨1298020, by decide⟩ ⟨12, 2, 0, 1298020, 370963, 2729, 65536⟩
    (by decide) selected_cut_46540

theorem unmarked_context_11_92740_1298021 : frontier 10 ⟨1298021, by decide⟩
    (prefixCache 11 92740) (prefixPartial 11 92740) = false := by
  decide +kernel

theorem node_context_11_92740_1298021 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298021, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨1297944, by decide⟩,⟨1297981, by decide⟩,⟨1298020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92740_1298021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92740 ⟨1298021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92740
    ⟨1298021, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨1297944, by decide⟩,⟨1297981, by decide⟩,⟨1298020, by decide⟩]) unmarked_context_11_92740_1298021 node_context_11_92740_1298021
  intro a
  fin_cases a
  · exact context_12_370960_307381
  · exact context_12_370961_1297944
  · exact context_12_370962_1297981
  · exact context_12_370963_1298020

theorem selected_cut_46541 : selected 9 ⟨1298070, by decide⟩
    (prefixPartial 12 370964) = some ⟨12, 2, 0, 1298070, 370964, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_370964_1298070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370964 ⟨1298070, by decide⟩ :=
  accepted_of_selected 12 370964 ⟨1298070, by decide⟩ ⟨12, 2, 0, 1298070, 370964, 2429, 65536⟩
    (by decide) selected_cut_46541

theorem selected_cut_46542 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 370965) = some ⟨12, 1, 0, 1118965, 370965, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370965_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370965 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 370965 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 370965, 1, 65536⟩
    (by decide) selected_cut_46542

theorem selected_cut_46543 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 370966) = some ⟨12, 1, 0, 692793, 370966, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370966_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370966 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 370966 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 370966, 1, 65536⟩
    (by decide) selected_cut_46543

theorem selected_cut_46544 : selected 9 ⟨1298123, by decide⟩
    (prefixPartial 12 370967) = some ⟨12, 2, 0, 1298123, 370967, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_370967_1298123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370967 ⟨1298123, by decide⟩ :=
  accepted_of_selected 12 370967 ⟨1298123, by decide⟩ ⟨12, 2, 0, 1298123, 370967, 2917, 65536⟩
    (by decide) selected_cut_46544

theorem unmarked_context_11_92741_1298124 : frontier 10 ⟨1298124, by decide⟩
    (prefixCache 11 92741) (prefixPartial 11 92741) = false := by
  decide +kernel

theorem node_context_11_92741_1298124 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298124, by decide⟩ =
    .split (coordinate 11) (![⟨1298070, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1298123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92741_1298124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92741 ⟨1298124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92741
    ⟨1298124, by decide⟩ (by decide) (![⟨1298070, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1298123, by decide⟩]) unmarked_context_11_92741_1298124 node_context_11_92741_1298124
  intro a
  fin_cases a
  · exact context_12_370964_1298070
  · exact context_12_370965_1118965
  · exact context_12_370966_692793
  · exact context_12_370967_1298123

theorem selected_cut_46545 : selected 9 ⟨1298172, by decide⟩
    (prefixPartial 12 370968) = some ⟨12, 2, 0, 1298172, 370968, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_370968_1298172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370968 ⟨1298172, by decide⟩ :=
  accepted_of_selected 12 370968 ⟨1298172, by decide⟩ ⟨12, 2, 0, 1298172, 370968, 2061, 65536⟩
    (by decide) selected_cut_46545

theorem selected_cut_46546 : selected 9 ⟨1298219, by decide⟩
    (prefixPartial 12 370969) = some ⟨12, 2, 0, 1298219, 370969, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_370969_1298219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370969 ⟨1298219, by decide⟩ :=
  accepted_of_selected 12 370969 ⟨1298219, by decide⟩ ⟨12, 2, 0, 1298219, 370969, 2773, 65536⟩
    (by decide) selected_cut_46546

theorem selected_cut_46547 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 370970) = some ⟨12, 1, 0, 660636, 370970, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370970_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370970 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 370970 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 370970, 1, 65536⟩
    (by decide) selected_cut_46547

theorem selected_cut_46548 : selected 9 ⟨1298269, by decide⟩
    (prefixPartial 12 370971) = some ⟨12, 2, 0, 1298269, 370971, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_370971_1298269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370971 ⟨1298269, by decide⟩ :=
  accepted_of_selected 12 370971 ⟨1298269, by decide⟩ ⟨12, 2, 0, 1298269, 370971, 2629, 65536⟩
    (by decide) selected_cut_46548

theorem unmarked_context_11_92742_1298270 : frontier 10 ⟨1298270, by decide⟩
    (prefixCache 11 92742) (prefixPartial 11 92742) = false := by
  decide +kernel

theorem node_context_11_92742_1298270 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298270, by decide⟩ =
    .split (coordinate 11) (![⟨1298172, by decide⟩,⟨1298219, by decide⟩,⟨660636, by decide⟩,⟨1298269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92742_1298270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92742 ⟨1298270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92742
    ⟨1298270, by decide⟩ (by decide) (![⟨1298172, by decide⟩,⟨1298219, by decide⟩,⟨660636, by decide⟩,⟨1298269, by decide⟩]) unmarked_context_11_92742_1298270 node_context_11_92742_1298270
  intro a
  fin_cases a
  · exact context_12_370968_1298172
  · exact context_12_370969_1298219
  · exact context_12_370970_660636
  · exact context_12_370971_1298269

theorem selected_cut_46549 : selected 9 ⟨1298303, by decide⟩
    (prefixPartial 12 370972) = some ⟨12, 2, 0, 1298303, 370972, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_370972_1298303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370972 ⟨1298303, by decide⟩ :=
  accepted_of_selected 12 370972 ⟨1298303, by decide⟩ ⟨12, 2, 0, 1298303, 370972, 2197, 65536⟩
    (by decide) selected_cut_46549

theorem selected_cut_46550 : selected 9 ⟨1298341, by decide⟩
    (prefixPartial 12 370973) = some ⟨12, 2, 0, 1298341, 370973, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_370973_1298341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370973 ⟨1298341, by decide⟩ :=
  accepted_of_selected 12 370973 ⟨1298341, by decide⟩ ⟨12, 2, 0, 1298341, 370973, 2461, 65536⟩
    (by decide) selected_cut_46550

theorem selected_cut_46551 : selected 9 ⟨1298370, by decide⟩
    (prefixPartial 12 370974) = some ⟨12, 2, 0, 1298370, 370974, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_370974_1298370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370974 ⟨1298370, by decide⟩ :=
  accepted_of_selected 12 370974 ⟨1298370, by decide⟩ ⟨12, 2, 0, 1298370, 370974, 2113, 65536⟩
    (by decide) selected_cut_46551

theorem selected_cut_46552 : selected 9 ⟨1298410, by decide⟩
    (prefixPartial 12 370975) = some ⟨12, 2, 0, 1298410, 370975, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_370975_1298410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370975 ⟨1298410, by decide⟩ :=
  accepted_of_selected 12 370975 ⟨1298410, by decide⟩ ⟨12, 2, 0, 1298410, 370975, 2477, 65536⟩
    (by decide) selected_cut_46552

theorem unmarked_context_11_92743_1298411 : frontier 10 ⟨1298411, by decide⟩
    (prefixCache 11 92743) (prefixPartial 11 92743) = false := by
  decide +kernel

theorem node_context_11_92743_1298411 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298411, by decide⟩ =
    .split (coordinate 11) (![⟨1298303, by decide⟩,⟨1298341, by decide⟩,⟨1298370, by decide⟩,⟨1298410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92743_1298411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92743 ⟨1298411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92743
    ⟨1298411, by decide⟩ (by decide) (![⟨1298303, by decide⟩,⟨1298341, by decide⟩,⟨1298370, by decide⟩,⟨1298410, by decide⟩]) unmarked_context_11_92743_1298411 node_context_11_92743_1298411
  intro a
  fin_cases a
  · exact context_12_370972_1298303
  · exact context_12_370973_1298341
  · exact context_12_370974_1298370
  · exact context_12_370975_1298410

theorem unmarked_context_10_23185_1298412 : frontier 11 ⟨1298412, by decide⟩
    (prefixCache 10 23185) (prefixPartial 10 23185) = false := by
  decide +kernel

theorem node_context_10_23185_1298412 : EJMOriginalGlobalDAGData.nodes 11 ⟨1298412, by decide⟩ =
    .split (coordinate 10) (![⟨1298021, by decide⟩,⟨1298124, by decide⟩,⟨1298270, by decide⟩,⟨1298411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23185_1298412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23185 ⟨1298412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23185
    ⟨1298412, by decide⟩ (by decide) (![⟨1298021, by decide⟩,⟨1298124, by decide⟩,⟨1298270, by decide⟩,⟨1298411, by decide⟩]) unmarked_context_10_23185_1298412 node_context_10_23185_1298412
  intro a
  fin_cases a
  · exact context_11_92740_1298021
  · exact context_11_92741_1298124
  · exact context_11_92742_1298270
  · exact context_11_92743_1298411

theorem selected_cut_46553 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 370976) = some ⟨12, 1, 0, 435790, 370976, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370976_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370976 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 370976 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 370976, 1, 65536⟩
    (by decide) selected_cut_46553

theorem selected_cut_46554 : selected 9 ⟨1298448, by decide⟩
    (prefixPartial 12 370977) = some ⟨12, 2, 0, 1298448, 370977, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_370977_1298448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370977 ⟨1298448, by decide⟩ :=
  accepted_of_selected 12 370977 ⟨1298448, by decide⟩ ⟨12, 2, 0, 1298448, 370977, 2485, 65536⟩
    (by decide) selected_cut_46554

theorem selected_cut_46555 : selected 9 ⟨1298485, by decide⟩
    (prefixPartial 12 370978) = some ⟨12, 2, 0, 1298485, 370978, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_370978_1298485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370978 ⟨1298485, by decide⟩ :=
  accepted_of_selected 12 370978 ⟨1298485, by decide⟩ ⟨12, 2, 0, 1298485, 370978, 1873, 65536⟩
    (by decide) selected_cut_46555

theorem selected_cut_46556 : selected 9 ⟨1298511, by decide⟩
    (prefixPartial 12 370979) = some ⟨12, 2, 0, 1298511, 370979, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_370979_1298511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370979 ⟨1298511, by decide⟩ :=
  accepted_of_selected 12 370979 ⟨1298511, by decide⟩ ⟨12, 2, 0, 1298511, 370979, 2177, 65536⟩
    (by decide) selected_cut_46556

theorem unmarked_context_11_92744_1298512 : frontier 10 ⟨1298512, by decide⟩
    (prefixCache 11 92744) (prefixPartial 11 92744) = false := by
  decide +kernel

theorem node_context_11_92744_1298512 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298512, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1298448, by decide⟩,⟨1298485, by decide⟩,⟨1298511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92744_1298512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92744 ⟨1298512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92744
    ⟨1298512, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1298448, by decide⟩,⟨1298485, by decide⟩,⟨1298511, by decide⟩]) unmarked_context_11_92744_1298512 node_context_11_92744_1298512
  intro a
  fin_cases a
  · exact context_12_370976_435790
  · exact context_12_370977_1298448
  · exact context_12_370978_1298485
  · exact context_12_370979_1298511

theorem selected_cut_46557 : selected 9 ⟨1298546, by decide⟩
    (prefixPartial 12 370980) = some ⟨12, 2, 0, 1298546, 370980, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_370980_1298546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370980 ⟨1298546, by decide⟩ :=
  accepted_of_selected 12 370980 ⟨1298546, by decide⟩ ⟨12, 2, 0, 1298546, 370980, 1277, 65536⟩
    (by decide) selected_cut_46557

theorem selected_cut_46558 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 370981) = some ⟨12, 1, 0, 891951, 370981, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370981_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370981 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 370981 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 370981, 1, 65536⟩
    (by decide) selected_cut_46558

theorem selected_cut_46559 : selected 9 ⟨1298577, by decide⟩
    (prefixPartial 12 370982) = some ⟨12, 2, 0, 1298577, 370982, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_370982_1298577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370982 ⟨1298577, by decide⟩ :=
  accepted_of_selected 12 370982 ⟨1298577, by decide⟩ ⟨12, 2, 0, 1298577, 370982, 2189, 65536⟩
    (by decide) selected_cut_46559

theorem selected_cut_46560 : selected 9 ⟨1298608, by decide⟩
    (prefixPartial 12 370983) = some ⟨12, 2, 0, 1298608, 370983, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_370983_1298608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370983 ⟨1298608, by decide⟩ :=
  accepted_of_selected 12 370983 ⟨1298608, by decide⟩ ⟨12, 2, 0, 1298608, 370983, 2373, 65536⟩
    (by decide) selected_cut_46560

theorem unmarked_context_11_92745_1298609 : frontier 10 ⟨1298609, by decide⟩
    (prefixCache 11 92745) (prefixPartial 11 92745) = false := by
  decide +kernel

theorem node_context_11_92745_1298609 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298609, by decide⟩ =
    .split (coordinate 11) (![⟨1298546, by decide⟩,⟨891951, by decide⟩,⟨1298577, by decide⟩,⟨1298608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92745_1298609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92745 ⟨1298609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92745
    ⟨1298609, by decide⟩ (by decide) (![⟨1298546, by decide⟩,⟨891951, by decide⟩,⟨1298577, by decide⟩,⟨1298608, by decide⟩]) unmarked_context_11_92745_1298609 node_context_11_92745_1298609
  intro a
  fin_cases a
  · exact context_12_370980_1298546
  · exact context_12_370981_891951
  · exact context_12_370982_1298577
  · exact context_12_370983_1298608

theorem selected_cut_46561 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92746) = some ⟨11, 1, 0, 900587, 92746, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92746_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92746 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92746 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92746, 1, 262144⟩
    (by decide) selected_cut_46561

theorem selected_cut_46562 : selected 9 ⟨1298637, by decide⟩
    (prefixPartial 12 370988) = some ⟨12, 2, 0, 1298637, 370988, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_370988_1298637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370988 ⟨1298637, by decide⟩ :=
  accepted_of_selected 12 370988 ⟨1298637, by decide⟩ ⟨12, 2, 0, 1298637, 370988, 2165, 65536⟩
    (by decide) selected_cut_46562

theorem selected_cut_46563 : selected 9 ⟨1298669, by decide⟩
    (prefixPartial 12 370989) = some ⟨12, 2, 0, 1298669, 370989, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_370989_1298669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370989 ⟨1298669, by decide⟩ :=
  accepted_of_selected 12 370989 ⟨1298669, by decide⟩ ⟨12, 2, 0, 1298669, 370989, 2213, 65536⟩
    (by decide) selected_cut_46563

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
