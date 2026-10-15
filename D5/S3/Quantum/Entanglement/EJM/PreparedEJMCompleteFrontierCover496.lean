/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover495
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_47619 : selected 9 ⟨1333241, by decide⟩
    (prefixPartial 12 373812) = some ⟨12, 2, 0, 1333241, 373812, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_373812_1333241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373812 ⟨1333241, by decide⟩ :=
  accepted_of_selected 12 373812 ⟨1333241, by decide⟩ ⟨12, 2, 0, 1333241, 373812, 2337, 65536⟩
    (by decide) selected_cut_47619

theorem selected_cut_47620 : selected 9 ⟨1008220, by decide⟩
    (prefixPartial 12 373813) = some ⟨12, 1, 0, 1008220, 373813, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373813_1008220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373813 ⟨1008220, by decide⟩ :=
  accepted_of_selected 12 373813 ⟨1008220, by decide⟩ ⟨12, 1, 0, 1008220, 373813, 1, 65536⟩
    (by decide) selected_cut_47620

theorem selected_cut_47621 : selected 9 ⟨1333281, by decide⟩
    (prefixPartial 12 373814) = some ⟨12, 2, 0, 1333281, 373814, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_373814_1333281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373814 ⟨1333281, by decide⟩ :=
  accepted_of_selected 12 373814 ⟨1333281, by decide⟩ ⟨12, 2, 0, 1333281, 373814, 2281, 65536⟩
    (by decide) selected_cut_47621

theorem selected_cut_47622 : selected 9 ⟨1333318, by decide⟩
    (prefixPartial 12 373815) = some ⟨12, 2, 0, 1333318, 373815, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_373815_1333318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373815 ⟨1333318, by decide⟩ :=
  accepted_of_selected 12 373815 ⟨1333318, by decide⟩ ⟨12, 2, 0, 1333318, 373815, 2225, 65536⟩
    (by decide) selected_cut_47622

theorem unmarked_context_11_93453_1333319 : frontier 10 ⟨1333319, by decide⟩
    (prefixCache 11 93453) (prefixPartial 11 93453) = false := by
  decide +kernel

theorem node_context_11_93453_1333319 : EJMOriginalGlobalDAGData.nodes 10 ⟨1333319, by decide⟩ =
    .split (coordinate 11) (![⟨1333241, by decide⟩,⟨1008220, by decide⟩,⟨1333281, by decide⟩,⟨1333318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93453_1333319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93453 ⟨1333319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93453
    ⟨1333319, by decide⟩ (by decide) (![⟨1333241, by decide⟩,⟨1008220, by decide⟩,⟨1333281, by decide⟩,⟨1333318, by decide⟩]) unmarked_context_11_93453_1333319 node_context_11_93453_1333319
  intro a
  fin_cases a
  · exact context_12_373812_1333241
  · exact context_12_373813_1008220
  · exact context_12_373814_1333281
  · exact context_12_373815_1333318

theorem selected_cut_47623 : selected 10 ⟨1333384, by decide⟩
    (prefixPartial 11 93454) = some ⟨11, 2, 0, 1333384, 93454, 3949, 262144⟩ := by
  decide +kernel

theorem context_11_93454_1333384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93454 ⟨1333384, by decide⟩ :=
  accepted_of_selected 11 93454 ⟨1333384, by decide⟩ ⟨11, 2, 0, 1333384, 93454, 3949, 262144⟩
    (by decide) selected_cut_47623

theorem selected_cut_47624 : selected 10 ⟨1333450, by decide⟩
    (prefixPartial 11 93455) = some ⟨11, 2, 0, 1333450, 93455, 4073, 262144⟩ := by
  decide +kernel

theorem context_11_93455_1333450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93455 ⟨1333450, by decide⟩ :=
  accepted_of_selected 11 93455 ⟨1333450, by decide⟩ ⟨11, 2, 0, 1333450, 93455, 4073, 262144⟩
    (by decide) selected_cut_47624

theorem unmarked_context_10_23363_1333451 : frontier 11 ⟨1333451, by decide⟩
    (prefixCache 10 23363) (prefixPartial 10 23363) = false := by
  decide +kernel

theorem node_context_10_23363_1333451 : EJMOriginalGlobalDAGData.nodes 11 ⟨1333451, by decide⟩ =
    .split (coordinate 10) (![⟨1333201, by decide⟩,⟨1333319, by decide⟩,⟨1333384, by decide⟩,⟨1333450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23363_1333451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23363 ⟨1333451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23363
    ⟨1333451, by decide⟩ (by decide) (![⟨1333201, by decide⟩,⟨1333319, by decide⟩,⟨1333384, by decide⟩,⟨1333450, by decide⟩]) unmarked_context_10_23363_1333451 node_context_10_23363_1333451
  intro a
  fin_cases a
  · exact context_11_93452_1333201
  · exact context_11_93453_1333319
  · exact context_11_93454_1333384
  · exact context_11_93455_1333450

theorem unmarked_context_9_5840_1333452 : frontier 12 ⟨1333452, by decide⟩
    (prefixCache 9 5840) (prefixPartial 9 5840) = false := by
  decide +kernel

theorem node_context_9_5840_1333452 : EJMOriginalGlobalDAGData.nodes 12 ⟨1333452, by decide⟩ =
    .split (coordinate 9) (![⟨1332315, by decide⟩,⟨1332709, by decide⟩,⟨1333086, by decide⟩,⟨1333451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5840_1333452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5840 ⟨1333452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5840
    ⟨1333452, by decide⟩ (by decide) (![⟨1332315, by decide⟩,⟨1332709, by decide⟩,⟨1333086, by decide⟩,⟨1333451, by decide⟩]) unmarked_context_9_5840_1333452 node_context_9_5840_1333452
  intro a
  fin_cases a
  · exact context_10_23360_1332315
  · exact context_10_23361_1332709
  · exact context_10_23362_1333086
  · exact context_10_23363_1333451

theorem selected_cut_47625 : selected 10 ⟨1283168, by decide⟩
    (prefixPartial 11 93456) = some ⟨11, 1, 0, 1283168, 93456, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93456_1283168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93456 ⟨1283168, by decide⟩ :=
  accepted_of_selected 11 93456 ⟨1283168, by decide⟩ ⟨11, 1, 0, 1283168, 93456, 1, 262144⟩
    (by decide) selected_cut_47625

theorem selected_cut_47626 : selected 9 ⟨1333482, by decide⟩
    (prefixPartial 12 373828) = some ⟨12, 2, 0, 1333482, 373828, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_373828_1333482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373828 ⟨1333482, by decide⟩ :=
  accepted_of_selected 12 373828 ⟨1333482, by decide⟩ ⟨12, 2, 0, 1333482, 373828, 1877, 65536⟩
    (by decide) selected_cut_47626

theorem selected_cut_47627 : selected 9 ⟨692443, by decide⟩
    (prefixPartial 12 373829) = some ⟨12, 1, 0, 692443, 373829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373829_692443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373829 ⟨692443, by decide⟩ :=
  accepted_of_selected 12 373829 ⟨692443, by decide⟩ ⟨12, 1, 0, 692443, 373829, 1, 65536⟩
    (by decide) selected_cut_47627

theorem selected_cut_47628 : selected 9 ⟨1333515, by decide⟩
    (prefixPartial 12 373830) = some ⟨12, 2, 0, 1333515, 373830, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_373830_1333515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373830 ⟨1333515, by decide⟩ :=
  accepted_of_selected 12 373830 ⟨1333515, by decide⟩ ⟨12, 2, 0, 1333515, 373830, 1873, 65536⟩
    (by decide) selected_cut_47628

theorem selected_cut_47629 : selected 9 ⟨1333548, by decide⟩
    (prefixPartial 12 373831) = some ⟨12, 2, 0, 1333548, 373831, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_373831_1333548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373831 ⟨1333548, by decide⟩ :=
  accepted_of_selected 12 373831 ⟨1333548, by decide⟩ ⟨12, 2, 0, 1333548, 373831, 1965, 65536⟩
    (by decide) selected_cut_47629

theorem unmarked_context_11_93457_1333549 : frontier 10 ⟨1333549, by decide⟩
    (prefixCache 11 93457) (prefixPartial 11 93457) = false := by
  decide +kernel

theorem node_context_11_93457_1333549 : EJMOriginalGlobalDAGData.nodes 10 ⟨1333549, by decide⟩ =
    .split (coordinate 11) (![⟨1333482, by decide⟩,⟨692443, by decide⟩,⟨1333515, by decide⟩,⟨1333548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93457_1333549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93457 ⟨1333549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93457
    ⟨1333549, by decide⟩ (by decide) (![⟨1333482, by decide⟩,⟨692443, by decide⟩,⟨1333515, by decide⟩,⟨1333548, by decide⟩]) unmarked_context_11_93457_1333549 node_context_11_93457_1333549
  intro a
  fin_cases a
  · exact context_12_373828_1333482
  · exact context_12_373829_692443
  · exact context_12_373830_1333515
  · exact context_12_373831_1333548

theorem selected_cut_47630 : selected 10 ⟨1333635, by decide⟩
    (prefixPartial 11 93458) = some ⟨11, 2, 0, 1333635, 93458, 3937, 262144⟩ := by
  decide +kernel

theorem context_11_93458_1333635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93458 ⟨1333635, by decide⟩ :=
  accepted_of_selected 11 93458 ⟨1333635, by decide⟩ ⟨11, 2, 0, 1333635, 93458, 3937, 262144⟩
    (by decide) selected_cut_47630

theorem selected_cut_47631 : selected 9 ⟨1333666, by decide⟩
    (prefixPartial 12 373836) = some ⟨12, 2, 0, 1333666, 373836, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_373836_1333666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373836 ⟨1333666, by decide⟩ :=
  accepted_of_selected 12 373836 ⟨1333666, by decide⟩ ⟨12, 2, 0, 1333666, 373836, 1833, 65536⟩
    (by decide) selected_cut_47631

theorem selected_cut_47632 : selected 9 ⟨1333694, by decide⟩
    (prefixPartial 12 373837) = some ⟨12, 2, 0, 1333694, 373837, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_373837_1333694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373837 ⟨1333694, by decide⟩ :=
  accepted_of_selected 12 373837 ⟨1333694, by decide⟩ ⟨12, 2, 0, 1333694, 373837, 1557, 65536⟩
    (by decide) selected_cut_47632

theorem selected_cut_47633 : selected 9 ⟨1333731, by decide⟩
    (prefixPartial 12 373838) = some ⟨12, 2, 0, 1333731, 373838, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_373838_1333731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373838 ⟨1333731, by decide⟩ :=
  accepted_of_selected 12 373838 ⟨1333731, by decide⟩ ⟨12, 2, 0, 1333731, 373838, 1977, 65536⟩
    (by decide) selected_cut_47633

theorem selected_cut_47634 : selected 9 ⟨296530, by decide⟩
    (prefixPartial 12 373839) = some ⟨12, 1, 0, 296530, 373839, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373839_296530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373839 ⟨296530, by decide⟩ :=
  accepted_of_selected 12 373839 ⟨296530, by decide⟩ ⟨12, 1, 0, 296530, 373839, 1, 65536⟩
    (by decide) selected_cut_47634

theorem unmarked_context_11_93459_1333732 : frontier 10 ⟨1333732, by decide⟩
    (prefixCache 11 93459) (prefixPartial 11 93459) = false := by
  decide +kernel

theorem node_context_11_93459_1333732 : EJMOriginalGlobalDAGData.nodes 10 ⟨1333732, by decide⟩ =
    .split (coordinate 11) (![⟨1333666, by decide⟩,⟨1333694, by decide⟩,⟨1333731, by decide⟩,⟨296530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93459_1333732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93459 ⟨1333732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93459
    ⟨1333732, by decide⟩ (by decide) (![⟨1333666, by decide⟩,⟨1333694, by decide⟩,⟨1333731, by decide⟩,⟨296530, by decide⟩]) unmarked_context_11_93459_1333732 node_context_11_93459_1333732
  intro a
  fin_cases a
  · exact context_12_373836_1333666
  · exact context_12_373837_1333694
  · exact context_12_373838_1333731
  · exact context_12_373839_296530

theorem unmarked_context_10_23364_1333733 : frontier 11 ⟨1333733, by decide⟩
    (prefixCache 10 23364) (prefixPartial 10 23364) = false := by
  decide +kernel

theorem node_context_10_23364_1333733 : EJMOriginalGlobalDAGData.nodes 11 ⟨1333733, by decide⟩ =
    .split (coordinate 10) (![⟨1283168, by decide⟩,⟨1333549, by decide⟩,⟨1333635, by decide⟩,⟨1333732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23364_1333733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23364 ⟨1333733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23364
    ⟨1333733, by decide⟩ (by decide) (![⟨1283168, by decide⟩,⟨1333549, by decide⟩,⟨1333635, by decide⟩,⟨1333732, by decide⟩]) unmarked_context_10_23364_1333733 node_context_10_23364_1333733
  intro a
  fin_cases a
  · exact context_11_93456_1283168
  · exact context_11_93457_1333549
  · exact context_11_93458_1333635
  · exact context_11_93459_1333732

theorem selected_cut_47635 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23365) = some ⟨10, 1, 0, 893098, 23365, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23365_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23365 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23365 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23365, 1, 1048576⟩
    (by decide) selected_cut_47635

theorem selected_cut_47636 : selected 10 ⟨1333795, by decide⟩
    (prefixPartial 11 93464) = some ⟨11, 2, 0, 1333795, 93464, 3133, 262144⟩ := by
  decide +kernel

theorem context_11_93464_1333795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93464 ⟨1333795, by decide⟩ :=
  accepted_of_selected 11 93464 ⟨1333795, by decide⟩ ⟨11, 2, 0, 1333795, 93464, 3133, 262144⟩
    (by decide) selected_cut_47636

theorem selected_cut_47637 : selected 9 ⟨1333824, by decide⟩
    (prefixPartial 12 373860) = some ⟨12, 2, 0, 1333824, 373860, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_373860_1333824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373860 ⟨1333824, by decide⟩ :=
  accepted_of_selected 12 373860 ⟨1333824, by decide⟩ ⟨12, 2, 0, 1333824, 373860, 1457, 65536⟩
    (by decide) selected_cut_47637

theorem selected_cut_47638 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 373861) = some ⟨12, 1, 0, 1256866, 373861, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373861_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373861 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 373861 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 373861, 1, 65536⟩
    (by decide) selected_cut_47638

theorem selected_cut_47639 : selected 9 ⟨1333850, by decide⟩
    (prefixPartial 12 373862) = some ⟨12, 2, 0, 1333850, 373862, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_373862_1333850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373862 ⟨1333850, by decide⟩ :=
  accepted_of_selected 12 373862 ⟨1333850, by decide⟩ ⟨12, 2, 0, 1333850, 373862, 1489, 65536⟩
    (by decide) selected_cut_47639

theorem selected_cut_47640 : selected 9 ⟨1333883, by decide⟩
    (prefixPartial 12 373863) = some ⟨12, 2, 0, 1333883, 373863, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_373863_1333883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373863 ⟨1333883, by decide⟩ :=
  accepted_of_selected 12 373863 ⟨1333883, by decide⟩ ⟨12, 2, 0, 1333883, 373863, 1521, 65536⟩
    (by decide) selected_cut_47640

theorem unmarked_context_11_93465_1333884 : frontier 10 ⟨1333884, by decide⟩
    (prefixCache 11 93465) (prefixPartial 11 93465) = false := by
  decide +kernel

theorem node_context_11_93465_1333884 : EJMOriginalGlobalDAGData.nodes 10 ⟨1333884, by decide⟩ =
    .split (coordinate 11) (![⟨1333824, by decide⟩,⟨1256866, by decide⟩,⟨1333850, by decide⟩,⟨1333883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93465_1333884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93465 ⟨1333884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93465
    ⟨1333884, by decide⟩ (by decide) (![⟨1333824, by decide⟩,⟨1256866, by decide⟩,⟨1333850, by decide⟩,⟨1333883, by decide⟩]) unmarked_context_11_93465_1333884 node_context_11_93465_1333884
  intro a
  fin_cases a
  · exact context_12_373860_1333824
  · exact context_12_373861_1256866
  · exact context_12_373862_1333850
  · exact context_12_373863_1333883

theorem selected_cut_47641 : selected 10 ⟨1283737, by decide⟩
    (prefixPartial 11 93466) = some ⟨11, 1, 0, 1283737, 93466, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93466_1283737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93466 ⟨1283737, by decide⟩ :=
  accepted_of_selected 11 93466 ⟨1283737, by decide⟩ ⟨11, 1, 0, 1283737, 93466, 1, 262144⟩
    (by decide) selected_cut_47641

theorem selected_cut_47642 : selected 9 ⟨1333910, by decide⟩
    (prefixPartial 12 373868) = some ⟨12, 2, 0, 1333910, 373868, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_373868_1333910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373868 ⟨1333910, by decide⟩ :=
  accepted_of_selected 12 373868 ⟨1333910, by decide⟩ ⟨12, 2, 0, 1333910, 373868, 1473, 65536⟩
    (by decide) selected_cut_47642

theorem selected_cut_47643 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 373869) = some ⟨12, 1, 0, 1256866, 373869, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373869_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373869 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 373869 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 373869, 1, 65536⟩
    (by decide) selected_cut_47643

theorem selected_cut_47644 : selected 9 ⟨1333942, by decide⟩
    (prefixPartial 12 373870) = some ⟨12, 2, 0, 1333942, 373870, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_373870_1333942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373870 ⟨1333942, by decide⟩ :=
  accepted_of_selected 12 373870 ⟨1333942, by decide⟩ ⟨12, 2, 0, 1333942, 373870, 1573, 65536⟩
    (by decide) selected_cut_47644

theorem selected_cut_47645 : selected 9 ⟨1333974, by decide⟩
    (prefixPartial 12 373871) = some ⟨12, 2, 0, 1333974, 373871, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_373871_1333974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373871 ⟨1333974, by decide⟩ :=
  accepted_of_selected 12 373871 ⟨1333974, by decide⟩ ⟨12, 2, 0, 1333974, 373871, 1565, 65536⟩
    (by decide) selected_cut_47645

theorem unmarked_context_11_93467_1333975 : frontier 10 ⟨1333975, by decide⟩
    (prefixCache 11 93467) (prefixPartial 11 93467) = false := by
  decide +kernel

theorem node_context_11_93467_1333975 : EJMOriginalGlobalDAGData.nodes 10 ⟨1333975, by decide⟩ =
    .split (coordinate 11) (![⟨1333910, by decide⟩,⟨1256866, by decide⟩,⟨1333942, by decide⟩,⟨1333974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93467_1333975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93467 ⟨1333975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93467
    ⟨1333975, by decide⟩ (by decide) (![⟨1333910, by decide⟩,⟨1256866, by decide⟩,⟨1333942, by decide⟩,⟨1333974, by decide⟩]) unmarked_context_11_93467_1333975 node_context_11_93467_1333975
  intro a
  fin_cases a
  · exact context_12_373868_1333910
  · exact context_12_373869_1256866
  · exact context_12_373870_1333942
  · exact context_12_373871_1333974

theorem unmarked_context_10_23366_1333976 : frontier 11 ⟨1333976, by decide⟩
    (prefixCache 10 23366) (prefixPartial 10 23366) = false := by
  decide +kernel

theorem node_context_10_23366_1333976 : EJMOriginalGlobalDAGData.nodes 11 ⟨1333976, by decide⟩ =
    .split (coordinate 10) (![⟨1333795, by decide⟩,⟨1333884, by decide⟩,⟨1283737, by decide⟩,⟨1333975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23366_1333976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23366 ⟨1333976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23366
    ⟨1333976, by decide⟩ (by decide) (![⟨1333795, by decide⟩,⟨1333884, by decide⟩,⟨1283737, by decide⟩,⟨1333975, by decide⟩]) unmarked_context_10_23366_1333976 node_context_10_23366_1333976
  intro a
  fin_cases a
  · exact context_11_93464_1333795
  · exact context_11_93465_1333884
  · exact context_11_93466_1283737
  · exact context_11_93467_1333975

theorem selected_cut_47646 : selected 10 ⟨1334032, by decide⟩
    (prefixPartial 11 93468) = some ⟨11, 2, 0, 1334032, 93468, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_93468_1334032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93468 ⟨1334032, by decide⟩ :=
  accepted_of_selected 11 93468 ⟨1334032, by decide⟩ ⟨11, 2, 0, 1334032, 93468, 3417, 262144⟩
    (by decide) selected_cut_47646

theorem selected_cut_47647 : selected 10 ⟨1334085, by decide⟩
    (prefixPartial 11 93469) = some ⟨11, 2, 0, 1334085, 93469, 3369, 262144⟩ := by
  decide +kernel

theorem context_11_93469_1334085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93469 ⟨1334085, by decide⟩ :=
  accepted_of_selected 11 93469 ⟨1334085, by decide⟩ ⟨11, 2, 0, 1334085, 93469, 3369, 262144⟩
    (by decide) selected_cut_47647

theorem selected_cut_47648 : selected 10 ⟨1334148, by decide⟩
    (prefixPartial 11 93470) = some ⟨11, 2, 0, 1334148, 93470, 3433, 262144⟩ := by
  decide +kernel

theorem context_11_93470_1334148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93470 ⟨1334148, by decide⟩ :=
  accepted_of_selected 11 93470 ⟨1334148, by decide⟩ ⟨11, 2, 0, 1334148, 93470, 3433, 262144⟩
    (by decide) selected_cut_47648

theorem selected_cut_47649 : selected 10 ⟨1284138, by decide⟩
    (prefixPartial 11 93471) = some ⟨11, 1, 0, 1284138, 93471, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93471_1284138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93471 ⟨1284138, by decide⟩ :=
  accepted_of_selected 11 93471 ⟨1284138, by decide⟩ ⟨11, 1, 0, 1284138, 93471, 1, 262144⟩
    (by decide) selected_cut_47649

theorem unmarked_context_10_23367_1334149 : frontier 11 ⟨1334149, by decide⟩
    (prefixCache 10 23367) (prefixPartial 10 23367) = false := by
  decide +kernel

theorem node_context_10_23367_1334149 : EJMOriginalGlobalDAGData.nodes 11 ⟨1334149, by decide⟩ =
    .split (coordinate 10) (![⟨1334032, by decide⟩,⟨1334085, by decide⟩,⟨1334148, by decide⟩,⟨1284138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23367_1334149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23367 ⟨1334149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23367
    ⟨1334149, by decide⟩ (by decide) (![⟨1334032, by decide⟩,⟨1334085, by decide⟩,⟨1334148, by decide⟩,⟨1284138, by decide⟩]) unmarked_context_10_23367_1334149 node_context_10_23367_1334149
  intro a
  fin_cases a
  · exact context_11_93468_1334032
  · exact context_11_93469_1334085
  · exact context_11_93470_1334148
  · exact context_11_93471_1284138

theorem unmarked_context_9_5841_1334150 : frontier 12 ⟨1334150, by decide⟩
    (prefixCache 9 5841) (prefixPartial 9 5841) = false := by
  decide +kernel

theorem node_context_9_5841_1334150 : EJMOriginalGlobalDAGData.nodes 12 ⟨1334150, by decide⟩ =
    .split (coordinate 9) (![⟨1333733, by decide⟩,⟨893098, by decide⟩,⟨1333976, by decide⟩,⟨1334149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5841_1334150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5841 ⟨1334150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5841
    ⟨1334150, by decide⟩ (by decide) (![⟨1333733, by decide⟩,⟨893098, by decide⟩,⟨1333976, by decide⟩,⟨1334149, by decide⟩]) unmarked_context_9_5841_1334150 node_context_9_5841_1334150
  intro a
  fin_cases a
  · exact context_10_23364_1333733
  · exact context_10_23365_893098
  · exact context_10_23366_1333976
  · exact context_10_23367_1334149

theorem selected_cut_47650 : selected 10 ⟨1334167, by decide⟩
    (prefixPartial 11 93472) = some ⟨11, 2, 0, 1334167, 93472, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_93472_1334167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93472 ⟨1334167, by decide⟩ :=
  accepted_of_selected 11 93472 ⟨1334167, by decide⟩ ⟨11, 2, 0, 1334167, 93472, 1089, 262144⟩
    (by decide) selected_cut_47650

theorem selected_cut_47651 : selected 10 ⟨1334204, by decide⟩
    (prefixPartial 11 93473) = some ⟨11, 2, 0, 1334204, 93473, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_93473_1334204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93473 ⟨1334204, by decide⟩ :=
  accepted_of_selected 11 93473 ⟨1334204, by decide⟩ ⟨11, 2, 0, 1334204, 93473, 2233, 262144⟩
    (by decide) selected_cut_47651

theorem selected_cut_47652 : selected 10 ⟨1334258, by decide⟩
    (prefixPartial 11 93474) = some ⟨11, 2, 0, 1334258, 93474, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_93474_1334258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93474 ⟨1334258, by decide⟩ :=
  accepted_of_selected 11 93474 ⟨1334258, by decide⟩ ⟨11, 2, 0, 1334258, 93474, 3137, 262144⟩
    (by decide) selected_cut_47652

theorem selected_cut_47653 : selected 10 ⟨1334295, by decide⟩
    (prefixPartial 11 93475) = some ⟨11, 2, 0, 1334295, 93475, 2705, 262144⟩ := by
  decide +kernel

theorem context_11_93475_1334295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93475 ⟨1334295, by decide⟩ :=
  accepted_of_selected 11 93475 ⟨1334295, by decide⟩ ⟨11, 2, 0, 1334295, 93475, 2705, 262144⟩
    (by decide) selected_cut_47653

theorem unmarked_context_10_23368_1334296 : frontier 11 ⟨1334296, by decide⟩
    (prefixCache 10 23368) (prefixPartial 10 23368) = false := by
  decide +kernel

theorem node_context_10_23368_1334296 : EJMOriginalGlobalDAGData.nodes 11 ⟨1334296, by decide⟩ =
    .split (coordinate 10) (![⟨1334167, by decide⟩,⟨1334204, by decide⟩,⟨1334258, by decide⟩,⟨1334295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23368_1334296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23368 ⟨1334296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23368
    ⟨1334296, by decide⟩ (by decide) (![⟨1334167, by decide⟩,⟨1334204, by decide⟩,⟨1334258, by decide⟩,⟨1334295, by decide⟩]) unmarked_context_10_23368_1334296 node_context_10_23368_1334296
  intro a
  fin_cases a
  · exact context_11_93472_1334167
  · exact context_11_93473_1334204
  · exact context_11_93474_1334258
  · exact context_11_93475_1334295

theorem selected_cut_47654 : selected 10 ⟨1334311, by decide⟩
    (prefixPartial 11 93476) = some ⟨11, 2, 0, 1334311, 93476, 1437, 262144⟩ := by
  decide +kernel

theorem context_11_93476_1334311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93476 ⟨1334311, by decide⟩ :=
  accepted_of_selected 11 93476 ⟨1334311, by decide⟩ ⟨11, 2, 0, 1334311, 93476, 1437, 262144⟩
    (by decide) selected_cut_47654

theorem selected_cut_47655 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93477) = some ⟨11, 1, 0, 892405, 93477, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93477_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93477 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93477 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93477, 1, 262144⟩
    (by decide) selected_cut_47655

theorem selected_cut_47656 : selected 10 ⟨1334346, by decide⟩
    (prefixPartial 11 93478) = some ⟨11, 2, 0, 1334346, 93478, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_93478_1334346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93478 ⟨1334346, by decide⟩ :=
  accepted_of_selected 11 93478 ⟨1334346, by decide⟩ ⟨11, 2, 0, 1334346, 93478, 2237, 262144⟩
    (by decide) selected_cut_47656

theorem selected_cut_47657 : selected 10 ⟨1334369, by decide⟩
    (prefixPartial 11 93479) = some ⟨11, 2, 0, 1334369, 93479, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_93479_1334369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93479 ⟨1334369, by decide⟩ :=
  accepted_of_selected 11 93479 ⟨1334369, by decide⟩ ⟨11, 2, 0, 1334369, 93479, 2085, 262144⟩
    (by decide) selected_cut_47657

theorem unmarked_context_10_23369_1334370 : frontier 11 ⟨1334370, by decide⟩
    (prefixCache 10 23369) (prefixPartial 10 23369) = false := by
  decide +kernel

theorem node_context_10_23369_1334370 : EJMOriginalGlobalDAGData.nodes 11 ⟨1334370, by decide⟩ =
    .split (coordinate 10) (![⟨1334311, by decide⟩,⟨892405, by decide⟩,⟨1334346, by decide⟩,⟨1334369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23369_1334370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23369 ⟨1334370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23369
    ⟨1334370, by decide⟩ (by decide) (![⟨1334311, by decide⟩,⟨892405, by decide⟩,⟨1334346, by decide⟩,⟨1334369, by decide⟩]) unmarked_context_10_23369_1334370 node_context_10_23369_1334370
  intro a
  fin_cases a
  · exact context_11_93476_1334311
  · exact context_11_93477_892405
  · exact context_11_93478_1334346
  · exact context_11_93479_1334369

theorem selected_cut_47658 : selected 11 ⟨1334400, by decide⟩
    (prefixPartial 10 23370) = some ⟨10, 2, 0, 1334400, 23370, 1929, 1048576⟩ := by
  decide +kernel

theorem context_10_23370_1334400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23370 ⟨1334400, by decide⟩ :=
  accepted_of_selected 10 23370 ⟨1334400, by decide⟩ ⟨10, 2, 0, 1334400, 23370, 1929, 1048576⟩
    (by decide) selected_cut_47658

theorem selected_cut_47659 : selected 10 ⟨1334412, by decide⟩
    (prefixPartial 11 93484) = some ⟨11, 2, 0, 1334412, 93484, 1041, 262144⟩ := by
  decide +kernel

theorem context_11_93484_1334412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93484 ⟨1334412, by decide⟩ :=
  accepted_of_selected 11 93484 ⟨1334412, by decide⟩ ⟨11, 2, 0, 1334412, 93484, 1041, 262144⟩
    (by decide) selected_cut_47659

theorem selected_cut_47660 : selected 10 ⟨1334432, by decide⟩
    (prefixPartial 11 93485) = some ⟨11, 2, 0, 1334432, 93485, 1521, 262144⟩ := by
  decide +kernel

theorem context_11_93485_1334432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93485 ⟨1334432, by decide⟩ :=
  accepted_of_selected 11 93485 ⟨1334432, by decide⟩ ⟨11, 2, 0, 1334432, 93485, 1521, 262144⟩
    (by decide) selected_cut_47660

theorem selected_cut_47661 : selected 10 ⟨1334458, by decide⟩
    (prefixPartial 11 93486) = some ⟨11, 2, 0, 1334458, 93486, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_93486_1334458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93486 ⟨1334458, by decide⟩ :=
  accepted_of_selected 11 93486 ⟨1334458, by decide⟩ ⟨11, 2, 0, 1334458, 93486, 1481, 262144⟩
    (by decide) selected_cut_47661

theorem selected_cut_47662 : selected 10 ⟨1334470, by decide⟩
    (prefixPartial 11 93487) = some ⟨11, 2, 0, 1334470, 93487, 793, 262144⟩ := by
  decide +kernel

theorem context_11_93487_1334470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93487 ⟨1334470, by decide⟩ :=
  accepted_of_selected 11 93487 ⟨1334470, by decide⟩ ⟨11, 2, 0, 1334470, 93487, 793, 262144⟩
    (by decide) selected_cut_47662

theorem unmarked_context_10_23371_1334471 : frontier 11 ⟨1334471, by decide⟩
    (prefixCache 10 23371) (prefixPartial 10 23371) = false := by
  decide +kernel

theorem node_context_10_23371_1334471 : EJMOriginalGlobalDAGData.nodes 11 ⟨1334471, by decide⟩ =
    .split (coordinate 10) (![⟨1334412, by decide⟩,⟨1334432, by decide⟩,⟨1334458, by decide⟩,⟨1334470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23371_1334471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23371 ⟨1334471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23371
    ⟨1334471, by decide⟩ (by decide) (![⟨1334412, by decide⟩,⟨1334432, by decide⟩,⟨1334458, by decide⟩,⟨1334470, by decide⟩]) unmarked_context_10_23371_1334471 node_context_10_23371_1334471
  intro a
  fin_cases a
  · exact context_11_93484_1334412
  · exact context_11_93485_1334432
  · exact context_11_93486_1334458
  · exact context_11_93487_1334470

theorem unmarked_context_9_5842_1334472 : frontier 12 ⟨1334472, by decide⟩
    (prefixCache 9 5842) (prefixPartial 9 5842) = false := by
  decide +kernel

theorem node_context_9_5842_1334472 : EJMOriginalGlobalDAGData.nodes 12 ⟨1334472, by decide⟩ =
    .split (coordinate 9) (![⟨1334296, by decide⟩,⟨1334370, by decide⟩,⟨1334400, by decide⟩,⟨1334471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5842_1334472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5842 ⟨1334472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5842
    ⟨1334472, by decide⟩ (by decide) (![⟨1334296, by decide⟩,⟨1334370, by decide⟩,⟨1334400, by decide⟩,⟨1334471, by decide⟩]) unmarked_context_9_5842_1334472 node_context_9_5842_1334472
  intro a
  fin_cases a
  · exact context_10_23368_1334296
  · exact context_10_23369_1334370
  · exact context_10_23370_1334400
  · exact context_10_23371_1334471

theorem selected_cut_47663 : selected 11 ⟨1334525, by decide⟩
    (prefixPartial 10 23372) = some ⟨10, 2, 0, 1334525, 23372, 3713, 1048576⟩ := by
  decide +kernel

theorem context_10_23372_1334525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23372 ⟨1334525, by decide⟩ :=
  accepted_of_selected 10 23372 ⟨1334525, by decide⟩ ⟨10, 2, 0, 1334525, 23372, 3713, 1048576⟩
    (by decide) selected_cut_47663

theorem selected_cut_47664 : selected 11 ⟨1334571, by decide⟩
    (prefixPartial 10 23373) = some ⟨10, 2, 0, 1334571, 23373, 2449, 1048576⟩ := by
  decide +kernel

theorem context_10_23373_1334571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23373 ⟨1334571, by decide⟩ :=
  accepted_of_selected 10 23373 ⟨1334571, by decide⟩ ⟨10, 2, 0, 1334571, 23373, 2449, 1048576⟩
    (by decide) selected_cut_47664

theorem selected_cut_47665 : selected 11 ⟨1334607, by decide⟩
    (prefixPartial 10 23374) = some ⟨10, 2, 0, 1334607, 23374, 1181, 1048576⟩ := by
  decide +kernel

theorem context_10_23374_1334607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23374 ⟨1334607, by decide⟩ :=
  accepted_of_selected 10 23374 ⟨1334607, by decide⟩ ⟨10, 2, 0, 1334607, 23374, 1181, 1048576⟩
    (by decide) selected_cut_47665

theorem selected_cut_47666 : selected 11 ⟨1334615, by decide⟩
    (prefixPartial 10 23375) = some ⟨10, 2, 0, 1334615, 23375, 165, 1048576⟩ := by
  decide +kernel

theorem context_10_23375_1334615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23375 ⟨1334615, by decide⟩ :=
  accepted_of_selected 10 23375 ⟨1334615, by decide⟩ ⟨10, 2, 0, 1334615, 23375, 165, 1048576⟩
    (by decide) selected_cut_47666

theorem unmarked_context_9_5843_1334616 : frontier 12 ⟨1334616, by decide⟩
    (prefixCache 9 5843) (prefixPartial 9 5843) = false := by
  decide +kernel

theorem node_context_9_5843_1334616 : EJMOriginalGlobalDAGData.nodes 12 ⟨1334616, by decide⟩ =
    .split (coordinate 9) (![⟨1334525, by decide⟩,⟨1334571, by decide⟩,⟨1334607, by decide⟩,⟨1334615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5843_1334616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5843 ⟨1334616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5843
    ⟨1334616, by decide⟩ (by decide) (![⟨1334525, by decide⟩,⟨1334571, by decide⟩,⟨1334607, by decide⟩,⟨1334615, by decide⟩]) unmarked_context_9_5843_1334616 node_context_9_5843_1334616
  intro a
  fin_cases a
  · exact context_10_23372_1334525
  · exact context_10_23373_1334571
  · exact context_10_23374_1334607
  · exact context_10_23375_1334615

theorem unmarked_context_8_1460_1334617 : frontier 13 ⟨1334617, by decide⟩
    (prefixCache 8 1460) (prefixPartial 8 1460) = false := by
  decide +kernel

theorem node_context_8_1460_1334617 : EJMOriginalGlobalDAGData.nodes 13 ⟨1334617, by decide⟩ =
    .split (coordinate 8) (![⟨1333452, by decide⟩,⟨1334150, by decide⟩,⟨1334472, by decide⟩,⟨1334616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1460_1334617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1460 ⟨1334617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1460
    ⟨1334617, by decide⟩ (by decide) (![⟨1333452, by decide⟩,⟨1334150, by decide⟩,⟨1334472, by decide⟩,⟨1334616, by decide⟩]) unmarked_context_8_1460_1334617 node_context_8_1460_1334617
  intro a
  fin_cases a
  · exact context_9_5840_1333452
  · exact context_9_5841_1334150
  · exact context_9_5842_1334472
  · exact context_9_5843_1334616

theorem selected_cut_47667 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93504) = some ⟨11, 1, 0, 434745, 93504, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93504_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93504 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93504 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93504, 1, 262144⟩
    (by decide) selected_cut_47667

theorem selected_cut_47668 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 93505) = some ⟨11, 1, 0, 167448, 93505, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93505_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93505 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 93505 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 93505, 1, 262144⟩
    (by decide) selected_cut_47668

theorem selected_cut_47669 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 374024) = some ⟨12, 1, 0, 448748, 374024, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374024_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374024 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 374024 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 374024, 1, 65536⟩
    (by decide) selected_cut_47669

theorem selected_cut_47670 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 374025) = some ⟨12, 1, 0, 34034, 374025, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374025_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374025 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 374025 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 374025, 1, 65536⟩
    (by decide) selected_cut_47670

theorem selected_cut_47671 : selected 9 ⟨1334673, by decide⟩
    (prefixPartial 12 374026) = some ⟨12, 2, 0, 1334673, 374026, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_374026_1334673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374026 ⟨1334673, by decide⟩ :=
  accepted_of_selected 12 374026 ⟨1334673, by decide⟩ ⟨12, 2, 0, 1334673, 374026, 2977, 65536⟩
    (by decide) selected_cut_47671

theorem selected_cut_47672 : selected 9 ⟨1334721, by decide⟩
    (prefixPartial 12 374027) = some ⟨12, 2, 0, 1334721, 374027, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_374027_1334721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374027 ⟨1334721, by decide⟩ :=
  accepted_of_selected 12 374027 ⟨1334721, by decide⟩ ⟨12, 2, 0, 1334721, 374027, 2721, 65536⟩
    (by decide) selected_cut_47672

theorem unmarked_context_11_93506_1334722 : frontier 10 ⟨1334722, by decide⟩
    (prefixCache 11 93506) (prefixPartial 11 93506) = false := by
  decide +kernel

theorem node_context_11_93506_1334722 : EJMOriginalGlobalDAGData.nodes 10 ⟨1334722, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1334673, by decide⟩,⟨1334721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93506_1334722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93506 ⟨1334722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93506
    ⟨1334722, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1334673, by decide⟩,⟨1334721, by decide⟩]) unmarked_context_11_93506_1334722 node_context_11_93506_1334722
  intro a
  fin_cases a
  · exact context_12_374024_448748
  · exact context_12_374025_34034
  · exact context_12_374026_1334673
  · exact context_12_374027_1334721

theorem selected_cut_47673 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 374028) = some ⟨12, 1, 0, 448748, 374028, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374028_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374028 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 374028 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 374028, 1, 65536⟩
    (by decide) selected_cut_47673

theorem selected_cut_47674 : selected 9 ⟨1334778, by decide⟩
    (prefixPartial 12 374029) = some ⟨12, 2, 0, 1334778, 374029, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_374029_1334778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374029 ⟨1334778, by decide⟩ :=
  accepted_of_selected 12 374029 ⟨1334778, by decide⟩ ⟨12, 2, 0, 1334778, 374029, 2589, 65536⟩
    (by decide) selected_cut_47674

theorem selected_cut_47675 : selected 9 ⟨1334830, by decide⟩
    (prefixPartial 12 374030) = some ⟨12, 2, 0, 1334830, 374030, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_374030_1334830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374030 ⟨1334830, by decide⟩ :=
  accepted_of_selected 12 374030 ⟨1334830, by decide⟩ ⟨12, 2, 0, 1334830, 374030, 2813, 65536⟩
    (by decide) selected_cut_47675

theorem selected_cut_47676 : selected 9 ⟨1334870, by decide⟩
    (prefixPartial 12 374031) = some ⟨12, 2, 0, 1334870, 374031, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_374031_1334870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374031 ⟨1334870, by decide⟩ :=
  accepted_of_selected 12 374031 ⟨1334870, by decide⟩ ⟨12, 2, 0, 1334870, 374031, 2713, 65536⟩
    (by decide) selected_cut_47676

theorem unmarked_context_11_93507_1334871 : frontier 10 ⟨1334871, by decide⟩
    (prefixCache 11 93507) (prefixPartial 11 93507) = false := by
  decide +kernel

theorem node_context_11_93507_1334871 : EJMOriginalGlobalDAGData.nodes 10 ⟨1334871, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1334778, by decide⟩,⟨1334830, by decide⟩,⟨1334870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93507_1334871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93507 ⟨1334871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93507
    ⟨1334871, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1334778, by decide⟩,⟨1334830, by decide⟩,⟨1334870, by decide⟩]) unmarked_context_11_93507_1334871 node_context_11_93507_1334871
  intro a
  fin_cases a
  · exact context_12_374028_448748
  · exact context_12_374029_1334778
  · exact context_12_374030_1334830
  · exact context_12_374031_1334870

theorem unmarked_context_10_23376_1334872 : frontier 11 ⟨1334872, by decide⟩
    (prefixCache 10 23376) (prefixPartial 10 23376) = false := by
  decide +kernel

theorem node_context_10_23376_1334872 : EJMOriginalGlobalDAGData.nodes 11 ⟨1334872, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1334722, by decide⟩,⟨1334871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23376_1334872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23376 ⟨1334872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23376
    ⟨1334872, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1334722, by decide⟩,⟨1334871, by decide⟩]) unmarked_context_10_23376_1334872 node_context_10_23376_1334872
  intro a
  fin_cases a
  · exact context_11_93504_434745
  · exact context_11_93505_167448
  · exact context_11_93506_1334722
  · exact context_11_93507_1334871

theorem selected_cut_47677 : selected 9 ⟨815337, by decide⟩
    (prefixPartial 12 374032) = some ⟨12, 1, 0, 815337, 374032, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374032_815337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374032 ⟨815337, by decide⟩ :=
  accepted_of_selected 12 374032 ⟨815337, by decide⟩ ⟨12, 1, 0, 815337, 374032, 1, 65536⟩
    (by decide) selected_cut_47677

theorem selected_cut_47678 : selected 9 ⟨1334910, by decide⟩
    (prefixPartial 12 374033) = some ⟨12, 2, 0, 1334910, 374033, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_374033_1334910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374033 ⟨1334910, by decide⟩ :=
  accepted_of_selected 12 374033 ⟨1334910, by decide⟩ ⟨12, 2, 0, 1334910, 374033, 2173, 65536⟩
    (by decide) selected_cut_47678

theorem selected_cut_47679 : selected 9 ⟨1334953, by decide⟩
    (prefixPartial 12 374034) = some ⟨12, 2, 0, 1334953, 374034, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_374034_1334953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374034 ⟨1334953, by decide⟩ :=
  accepted_of_selected 12 374034 ⟨1334953, by decide⟩ ⟨12, 2, 0, 1334953, 374034, 2349, 65536⟩
    (by decide) selected_cut_47679

theorem selected_cut_47680 : selected 9 ⟨1334994, by decide⟩
    (prefixPartial 12 374035) = some ⟨12, 2, 0, 1334994, 374035, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_374035_1334994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374035 ⟨1334994, by decide⟩ :=
  accepted_of_selected 12 374035 ⟨1334994, by decide⟩ ⟨12, 2, 0, 1334994, 374035, 2457, 65536⟩
    (by decide) selected_cut_47680

theorem unmarked_context_11_93508_1334995 : frontier 10 ⟨1334995, by decide⟩
    (prefixCache 11 93508) (prefixPartial 11 93508) = false := by
  decide +kernel

theorem node_context_11_93508_1334995 : EJMOriginalGlobalDAGData.nodes 10 ⟨1334995, by decide⟩ =
    .split (coordinate 11) (![⟨815337, by decide⟩,⟨1334910, by decide⟩,⟨1334953, by decide⟩,⟨1334994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93508_1334995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93508 ⟨1334995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93508
    ⟨1334995, by decide⟩ (by decide) (![⟨815337, by decide⟩,⟨1334910, by decide⟩,⟨1334953, by decide⟩,⟨1334994, by decide⟩]) unmarked_context_11_93508_1334995 node_context_11_93508_1334995
  intro a
  fin_cases a
  · exact context_12_374032_815337
  · exact context_12_374033_1334910
  · exact context_12_374034_1334953
  · exact context_12_374035_1334994

theorem selected_cut_47681 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93509) = some ⟨11, 1, 0, 892405, 93509, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93509_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93509 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93509 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93509, 1, 262144⟩
    (by decide) selected_cut_47681

theorem selected_cut_47682 : selected 9 ⟨1072955, by decide⟩
    (prefixPartial 12 374040) = some ⟨12, 1, 0, 1072955, 374040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374040_1072955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374040 ⟨1072955, by decide⟩ :=
  accepted_of_selected 12 374040 ⟨1072955, by decide⟩ ⟨12, 1, 0, 1072955, 374040, 1, 65536⟩
    (by decide) selected_cut_47682

theorem selected_cut_47683 : selected 9 ⟨1335025, by decide⟩
    (prefixPartial 12 374041) = some ⟨12, 2, 0, 1335025, 374041, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_374041_1335025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374041 ⟨1335025, by decide⟩ :=
  accepted_of_selected 12 374041 ⟨1335025, by decide⟩ ⟨12, 2, 0, 1335025, 374041, 1961, 65536⟩
    (by decide) selected_cut_47683

theorem selected_cut_47684 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 374042) = some ⟨12, 1, 0, 660636, 374042, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374042_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374042 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 374042 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 374042, 1, 65536⟩
    (by decide) selected_cut_47684

theorem selected_cut_47685 : selected 9 ⟨1335064, by decide⟩
    (prefixPartial 12 374043) = some ⟨12, 2, 0, 1335064, 374043, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_374043_1335064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374043 ⟨1335064, by decide⟩ :=
  accepted_of_selected 12 374043 ⟨1335064, by decide⟩ ⟨12, 2, 0, 1335064, 374043, 2361, 65536⟩
    (by decide) selected_cut_47685

theorem unmarked_context_11_93510_1335065 : frontier 10 ⟨1335065, by decide⟩
    (prefixCache 11 93510) (prefixPartial 11 93510) = false := by
  decide +kernel

theorem node_context_11_93510_1335065 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335065, by decide⟩ =
    .split (coordinate 11) (![⟨1072955, by decide⟩,⟨1335025, by decide⟩,⟨660636, by decide⟩,⟨1335064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93510_1335065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93510 ⟨1335065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93510
    ⟨1335065, by decide⟩ (by decide) (![⟨1072955, by decide⟩,⟨1335025, by decide⟩,⟨660636, by decide⟩,⟨1335064, by decide⟩]) unmarked_context_11_93510_1335065 node_context_11_93510_1335065
  intro a
  fin_cases a
  · exact context_12_374040_1072955
  · exact context_12_374041_1335025
  · exact context_12_374042_660636
  · exact context_12_374043_1335064

theorem selected_cut_47686 : selected 9 ⟨1335110, by decide⟩
    (prefixPartial 12 374044) = some ⟨12, 2, 0, 1335110, 374044, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_374044_1335110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374044 ⟨1335110, by decide⟩ :=
  accepted_of_selected 12 374044 ⟨1335110, by decide⟩ ⟨12, 2, 0, 1335110, 374044, 2441, 65536⟩
    (by decide) selected_cut_47686

theorem selected_cut_47687 : selected 9 ⟨1335146, by decide⟩
    (prefixPartial 12 374045) = some ⟨12, 2, 0, 1335146, 374045, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_374045_1335146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374045 ⟨1335146, by decide⟩ :=
  accepted_of_selected 12 374045 ⟨1335146, by decide⟩ ⟨12, 2, 0, 1335146, 374045, 2085, 65536⟩
    (by decide) selected_cut_47687

theorem selected_cut_47688 : selected 9 ⟨1335192, by decide⟩
    (prefixPartial 12 374046) = some ⟨12, 2, 0, 1335192, 374046, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_374046_1335192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374046 ⟨1335192, by decide⟩ :=
  accepted_of_selected 12 374046 ⟨1335192, by decide⟩ ⟨12, 2, 0, 1335192, 374046, 2337, 65536⟩
    (by decide) selected_cut_47688

theorem selected_cut_47689 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 374047) = some ⟨12, 1, 0, 757807, 374047, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374047_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374047 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 374047 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 374047, 1, 65536⟩
    (by decide) selected_cut_47689

theorem unmarked_context_11_93511_1335193 : frontier 10 ⟨1335193, by decide⟩
    (prefixCache 11 93511) (prefixPartial 11 93511) = false := by
  decide +kernel

theorem node_context_11_93511_1335193 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335193, by decide⟩ =
    .split (coordinate 11) (![⟨1335110, by decide⟩,⟨1335146, by decide⟩,⟨1335192, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93511_1335193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93511 ⟨1335193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93511
    ⟨1335193, by decide⟩ (by decide) (![⟨1335110, by decide⟩,⟨1335146, by decide⟩,⟨1335192, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_93511_1335193 node_context_11_93511_1335193
  intro a
  fin_cases a
  · exact context_12_374044_1335110
  · exact context_12_374045_1335146
  · exact context_12_374046_1335192
  · exact context_12_374047_757807

theorem unmarked_context_10_23377_1335194 : frontier 11 ⟨1335194, by decide⟩
    (prefixCache 10 23377) (prefixPartial 10 23377) = false := by
  decide +kernel

theorem node_context_10_23377_1335194 : EJMOriginalGlobalDAGData.nodes 11 ⟨1335194, by decide⟩ =
    .split (coordinate 10) (![⟨1334995, by decide⟩,⟨892405, by decide⟩,⟨1335065, by decide⟩,⟨1335193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23377_1335194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23377 ⟨1335194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23377
    ⟨1335194, by decide⟩ (by decide) (![⟨1334995, by decide⟩,⟨892405, by decide⟩,⟨1335065, by decide⟩,⟨1335193, by decide⟩]) unmarked_context_10_23377_1335194 node_context_10_23377_1335194
  intro a
  fin_cases a
  · exact context_11_93508_1334995
  · exact context_11_93509_892405
  · exact context_11_93510_1335065
  · exact context_11_93511_1335193

theorem selected_cut_47690 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374048) = some ⟨12, 1, 0, 435790, 374048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374048_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374048 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374048 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374048, 1, 65536⟩
    (by decide) selected_cut_47690

theorem selected_cut_47691 : selected 9 ⟨1335233, by decide⟩
    (prefixPartial 12 374049) = some ⟨12, 2, 0, 1335233, 374049, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_374049_1335233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374049 ⟨1335233, by decide⟩ :=
  accepted_of_selected 12 374049 ⟨1335233, by decide⟩ ⟨12, 2, 0, 1335233, 374049, 2277, 65536⟩
    (by decide) selected_cut_47691

theorem selected_cut_47692 : selected 9 ⟨1335278, by decide⟩
    (prefixPartial 12 374050) = some ⟨12, 2, 0, 1335278, 374050, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_374050_1335278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374050 ⟨1335278, by decide⟩ :=
  accepted_of_selected 12 374050 ⟨1335278, by decide⟩ ⟨12, 2, 0, 1335278, 374050, 2309, 65536⟩
    (by decide) selected_cut_47692

theorem selected_cut_47693 : selected 9 ⟨1335328, by decide⟩
    (prefixPartial 12 374051) = some ⟨12, 2, 0, 1335328, 374051, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_374051_1335328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374051 ⟨1335328, by decide⟩ :=
  accepted_of_selected 12 374051 ⟨1335328, by decide⟩ ⟨12, 2, 0, 1335328, 374051, 2473, 65536⟩
    (by decide) selected_cut_47693

theorem unmarked_context_11_93512_1335329 : frontier 10 ⟨1335329, by decide⟩
    (prefixCache 11 93512) (prefixPartial 11 93512) = false := by
  decide +kernel

theorem node_context_11_93512_1335329 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335329, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1335233, by decide⟩,⟨1335278, by decide⟩,⟨1335328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93512_1335329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93512 ⟨1335329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93512
    ⟨1335329, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1335233, by decide⟩,⟨1335278, by decide⟩,⟨1335328, by decide⟩]) unmarked_context_11_93512_1335329 node_context_11_93512_1335329
  intro a
  fin_cases a
  · exact context_12_374048_435790
  · exact context_12_374049_1335233
  · exact context_12_374050_1335278
  · exact context_12_374051_1335328

theorem selected_cut_47694 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374052) = some ⟨12, 1, 0, 435790, 374052, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374052_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374052 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374052 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374052, 1, 65536⟩
    (by decide) selected_cut_47694

theorem selected_cut_47695 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 374053) = some ⟨12, 1, 0, 891951, 374053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374053_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374053 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 374053 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 374053, 1, 65536⟩
    (by decide) selected_cut_47695

theorem selected_cut_47696 : selected 9 ⟨1335365, by decide⟩
    (prefixPartial 12 374054) = some ⟨12, 2, 0, 1335365, 374054, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_374054_1335365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374054 ⟨1335365, by decide⟩ :=
  accepted_of_selected 12 374054 ⟨1335365, by decide⟩ ⟨12, 2, 0, 1335365, 374054, 2221, 65536⟩
    (by decide) selected_cut_47696

theorem selected_cut_47697 : selected 9 ⟨1335401, by decide⟩
    (prefixPartial 12 374055) = some ⟨12, 2, 0, 1335401, 374055, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_374055_1335401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374055 ⟨1335401, by decide⟩ :=
  accepted_of_selected 12 374055 ⟨1335401, by decide⟩ ⟨12, 2, 0, 1335401, 374055, 2225, 65536⟩
    (by decide) selected_cut_47697

theorem unmarked_context_11_93513_1335402 : frontier 10 ⟨1335402, by decide⟩
    (prefixCache 11 93513) (prefixPartial 11 93513) = false := by
  decide +kernel

theorem node_context_11_93513_1335402 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335402, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1335365, by decide⟩,⟨1335401, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93513_1335402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93513 ⟨1335402, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93513
    ⟨1335402, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1335365, by decide⟩,⟨1335401, by decide⟩]) unmarked_context_11_93513_1335402 node_context_11_93513_1335402
  intro a
  fin_cases a
  · exact context_12_374052_435790
  · exact context_12_374053_891951
  · exact context_12_374054_1335365
  · exact context_12_374055_1335401

theorem selected_cut_47698 : selected 10 ⟨1335448, by decide⟩
    (prefixPartial 11 93514) = some ⟨11, 2, 0, 1335448, 93514, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_93514_1335448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93514 ⟨1335448, by decide⟩ :=
  accepted_of_selected 11 93514 ⟨1335448, by decide⟩ ⟨11, 2, 0, 1335448, 93514, 2369, 262144⟩
    (by decide) selected_cut_47698

theorem selected_cut_47699 : selected 9 ⟨1335489, by decide⟩
    (prefixPartial 12 374060) = some ⟨12, 2, 0, 1335489, 374060, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_374060_1335489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374060 ⟨1335489, by decide⟩ :=
  accepted_of_selected 12 374060 ⟨1335489, by decide⟩ ⟨12, 2, 0, 1335489, 374060, 2353, 65536⟩
    (by decide) selected_cut_47699

theorem selected_cut_47700 : selected 9 ⟨1335531, by decide⟩
    (prefixPartial 12 374061) = some ⟨12, 2, 0, 1335531, 374061, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_374061_1335531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374061 ⟨1335531, by decide⟩ :=
  accepted_of_selected 12 374061 ⟨1335531, by decide⟩ ⟨12, 2, 0, 1335531, 374061, 2241, 65536⟩
    (by decide) selected_cut_47700

theorem selected_cut_47701 : selected 9 ⟨1335570, by decide⟩
    (prefixPartial 12 374062) = some ⟨12, 2, 0, 1335570, 374062, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_374062_1335570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374062 ⟨1335570, by decide⟩ :=
  accepted_of_selected 12 374062 ⟨1335570, by decide⟩ ⟨12, 2, 0, 1335570, 374062, 2229, 65536⟩
    (by decide) selected_cut_47701

theorem selected_cut_47702 : selected 9 ⟨1335610, by decide⟩
    (prefixPartial 12 374063) = some ⟨12, 2, 0, 1335610, 374063, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_374063_1335610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374063 ⟨1335610, by decide⟩ :=
  accepted_of_selected 12 374063 ⟨1335610, by decide⟩ ⟨12, 2, 0, 1335610, 374063, 2325, 65536⟩
    (by decide) selected_cut_47702

theorem unmarked_context_11_93515_1335611 : frontier 10 ⟨1335611, by decide⟩
    (prefixCache 11 93515) (prefixPartial 11 93515) = false := by
  decide +kernel

theorem node_context_11_93515_1335611 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335611, by decide⟩ =
    .split (coordinate 11) (![⟨1335489, by decide⟩,⟨1335531, by decide⟩,⟨1335570, by decide⟩,⟨1335610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93515_1335611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93515 ⟨1335611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93515
    ⟨1335611, by decide⟩ (by decide) (![⟨1335489, by decide⟩,⟨1335531, by decide⟩,⟨1335570, by decide⟩,⟨1335610, by decide⟩]) unmarked_context_11_93515_1335611 node_context_11_93515_1335611
  intro a
  fin_cases a
  · exact context_12_374060_1335489
  · exact context_12_374061_1335531
  · exact context_12_374062_1335570
  · exact context_12_374063_1335610

theorem unmarked_context_10_23378_1335612 : frontier 11 ⟨1335612, by decide⟩
    (prefixCache 10 23378) (prefixPartial 10 23378) = false := by
  decide +kernel

theorem node_context_10_23378_1335612 : EJMOriginalGlobalDAGData.nodes 11 ⟨1335612, by decide⟩ =
    .split (coordinate 10) (![⟨1335329, by decide⟩,⟨1335402, by decide⟩,⟨1335448, by decide⟩,⟨1335611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23378_1335612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23378 ⟨1335612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23378
    ⟨1335612, by decide⟩ (by decide) (![⟨1335329, by decide⟩,⟨1335402, by decide⟩,⟨1335448, by decide⟩,⟨1335611, by decide⟩]) unmarked_context_10_23378_1335612 node_context_10_23378_1335612
  intro a
  fin_cases a
  · exact context_11_93512_1335329
  · exact context_11_93513_1335402
  · exact context_11_93514_1335448
  · exact context_11_93515_1335611

theorem selected_cut_47703 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 374064) = some ⟨12, 1, 0, 1255011, 374064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374064_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374064 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 374064 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 374064, 1, 65536⟩
    (by decide) selected_cut_47703

theorem selected_cut_47704 : selected 9 ⟨1335635, by decide⟩
    (prefixPartial 12 374065) = some ⟨12, 2, 0, 1335635, 374065, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_374065_1335635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374065 ⟨1335635, by decide⟩ :=
  accepted_of_selected 12 374065 ⟨1335635, by decide⟩ ⟨12, 2, 0, 1335635, 374065, 1813, 65536⟩
    (by decide) selected_cut_47704

theorem selected_cut_47705 : selected 9 ⟨1335668, by decide⟩
    (prefixPartial 12 374066) = some ⟨12, 2, 0, 1335668, 374066, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_374066_1335668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374066 ⟨1335668, by decide⟩ :=
  accepted_of_selected 12 374066 ⟨1335668, by decide⟩ ⟨12, 2, 0, 1335668, 374066, 1941, 65536⟩
    (by decide) selected_cut_47705

theorem selected_cut_47706 : selected 9 ⟨1335697, by decide⟩
    (prefixPartial 12 374067) = some ⟨12, 2, 0, 1335697, 374067, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_374067_1335697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374067 ⟨1335697, by decide⟩ :=
  accepted_of_selected 12 374067 ⟨1335697, by decide⟩ ⟨12, 2, 0, 1335697, 374067, 1937, 65536⟩
    (by decide) selected_cut_47706

theorem unmarked_context_11_93516_1335698 : frontier 10 ⟨1335698, by decide⟩
    (prefixCache 11 93516) (prefixPartial 11 93516) = false := by
  decide +kernel

theorem node_context_11_93516_1335698 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335698, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1335635, by decide⟩,⟨1335668, by decide⟩,⟨1335697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93516_1335698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93516 ⟨1335698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93516
    ⟨1335698, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1335635, by decide⟩,⟨1335668, by decide⟩,⟨1335697, by decide⟩]) unmarked_context_11_93516_1335698 node_context_11_93516_1335698
  intro a
  fin_cases a
  · exact context_12_374064_1255011
  · exact context_12_374065_1335635
  · exact context_12_374066_1335668
  · exact context_12_374067_1335697

theorem selected_cut_47707 : selected 9 ⟨1335740, by decide⟩
    (prefixPartial 12 374068) = some ⟨12, 2, 0, 1335740, 374068, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_374068_1335740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374068 ⟨1335740, by decide⟩ :=
  accepted_of_selected 12 374068 ⟨1335740, by decide⟩ ⟨12, 2, 0, 1335740, 374068, 2017, 65536⟩
    (by decide) selected_cut_47707

theorem selected_cut_47708 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 374069) = some ⟨12, 1, 0, 891951, 374069, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374069_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374069 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 374069 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 374069, 1, 65536⟩
    (by decide) selected_cut_47708

theorem selected_cut_47709 : selected 9 ⟨1335773, by decide⟩
    (prefixPartial 12 374070) = some ⟨12, 2, 0, 1335773, 374070, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_374070_1335773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374070 ⟨1335773, by decide⟩ :=
  accepted_of_selected 12 374070 ⟨1335773, by decide⟩ ⟨12, 2, 0, 1335773, 374070, 1785, 65536⟩
    (by decide) selected_cut_47709

theorem selected_cut_47710 : selected 9 ⟨1335796, by decide⟩
    (prefixPartial 12 374071) = some ⟨12, 2, 0, 1335796, 374071, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_374071_1335796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374071 ⟨1335796, by decide⟩ :=
  accepted_of_selected 12 374071 ⟨1335796, by decide⟩ ⟨12, 2, 0, 1335796, 374071, 1681, 65536⟩
    (by decide) selected_cut_47710

theorem unmarked_context_11_93517_1335797 : frontier 10 ⟨1335797, by decide⟩
    (prefixCache 11 93517) (prefixPartial 11 93517) = false := by
  decide +kernel

theorem node_context_11_93517_1335797 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335797, by decide⟩ =
    .split (coordinate 11) (![⟨1335740, by decide⟩,⟨891951, by decide⟩,⟨1335773, by decide⟩,⟨1335796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93517_1335797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93517 ⟨1335797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93517
    ⟨1335797, by decide⟩ (by decide) (![⟨1335740, by decide⟩,⟨891951, by decide⟩,⟨1335773, by decide⟩,⟨1335796, by decide⟩]) unmarked_context_11_93517_1335797 node_context_11_93517_1335797
  intro a
  fin_cases a
  · exact context_12_374068_1335740
  · exact context_12_374069_891951
  · exact context_12_374070_1335773
  · exact context_12_374071_1335796

theorem selected_cut_47711 : selected 9 ⟨1335830, by decide⟩
    (prefixPartial 12 374072) = some ⟨12, 2, 0, 1335830, 374072, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_374072_1335830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374072 ⟨1335830, by decide⟩ :=
  accepted_of_selected 12 374072 ⟨1335830, by decide⟩ ⟨12, 2, 0, 1335830, 374072, 1861, 65536⟩
    (by decide) selected_cut_47711

theorem selected_cut_47712 : selected 9 ⟨1335850, by decide⟩
    (prefixPartial 12 374073) = some ⟨12, 2, 0, 1335850, 374073, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_374073_1335850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374073 ⟨1335850, by decide⟩ :=
  accepted_of_selected 12 374073 ⟨1335850, by decide⟩ ⟨12, 2, 0, 1335850, 374073, 1525, 65536⟩
    (by decide) selected_cut_47712

theorem selected_cut_47713 : selected 9 ⟨1335883, by decide⟩
    (prefixPartial 12 374074) = some ⟨12, 2, 0, 1335883, 374074, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_374074_1335883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374074 ⟨1335883, by decide⟩ :=
  accepted_of_selected 12 374074 ⟨1335883, by decide⟩ ⟨12, 2, 0, 1335883, 374074, 1861, 65536⟩
    (by decide) selected_cut_47713

theorem selected_cut_47714 : selected 9 ⟨1335908, by decide⟩
    (prefixPartial 12 374075) = some ⟨12, 2, 0, 1335908, 374075, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_374075_1335908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374075 ⟨1335908, by decide⟩ :=
  accepted_of_selected 12 374075 ⟨1335908, by decide⟩ ⟨12, 2, 0, 1335908, 374075, 1605, 65536⟩
    (by decide) selected_cut_47714

theorem unmarked_context_11_93518_1335909 : frontier 10 ⟨1335909, by decide⟩
    (prefixCache 11 93518) (prefixPartial 11 93518) = false := by
  decide +kernel

theorem node_context_11_93518_1335909 : EJMOriginalGlobalDAGData.nodes 10 ⟨1335909, by decide⟩ =
    .split (coordinate 11) (![⟨1335830, by decide⟩,⟨1335850, by decide⟩,⟨1335883, by decide⟩,⟨1335908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93518_1335909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93518 ⟨1335909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93518
    ⟨1335909, by decide⟩ (by decide) (![⟨1335830, by decide⟩,⟨1335850, by decide⟩,⟨1335883, by decide⟩,⟨1335908, by decide⟩]) unmarked_context_11_93518_1335909 node_context_11_93518_1335909
  intro a
  fin_cases a
  · exact context_12_374072_1335830
  · exact context_12_374073_1335850
  · exact context_12_374074_1335883
  · exact context_12_374075_1335908

theorem selected_cut_47715 : selected 10 ⟨1335968, by decide⟩
    (prefixPartial 11 93519) = some ⟨11, 2, 0, 1335968, 93519, 3201, 262144⟩ := by
  decide +kernel

theorem context_11_93519_1335968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93519 ⟨1335968, by decide⟩ :=
  accepted_of_selected 11 93519 ⟨1335968, by decide⟩ ⟨11, 2, 0, 1335968, 93519, 3201, 262144⟩
    (by decide) selected_cut_47715

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
