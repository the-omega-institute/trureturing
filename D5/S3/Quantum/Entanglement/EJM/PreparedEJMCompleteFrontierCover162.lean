/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover161
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_15555 : selected 9 ⟨398432, by decide⟩
    (prefixPartial 12 27801) = some ⟨12, 2, 0, 398432, 27801, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_27801_398432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27801 ⟨398432, by decide⟩ :=
  accepted_of_selected 12 27801 ⟨398432, by decide⟩ ⟨12, 2, 0, 398432, 27801, 2473, 65536⟩
    (by decide) selected_cut_15555

theorem selected_cut_15556 : selected 9 ⟨398456, by decide⟩
    (prefixPartial 12 27802) = some ⟨12, 2, 0, 398456, 27802, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_27802_398456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27802 ⟨398456, by decide⟩ :=
  accepted_of_selected 12 27802 ⟨398456, by decide⟩ ⟨12, 2, 0, 398456, 27802, 2197, 65536⟩
    (by decide) selected_cut_15556

theorem selected_cut_15557 : selected 9 ⟨398491, by decide⟩
    (prefixPartial 12 27803) = some ⟨12, 2, 0, 398491, 27803, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_27803_398491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27803 ⟨398491, by decide⟩ :=
  accepted_of_selected 12 27803 ⟨398491, by decide⟩ ⟨12, 2, 0, 398491, 27803, 2485, 65536⟩
    (by decide) selected_cut_15557

theorem unmarked_context_11_6950_398492 : frontier 10 ⟨398492, by decide⟩
    (prefixCache 11 6950) (prefixPartial 11 6950) = false := by
  decide +kernel

theorem node_context_11_6950_398492 : EJMOriginalGlobalDAGData.nodes 10 ⟨398492, by decide⟩ =
    .split (coordinate 11) (![⟨398405, by decide⟩,⟨398432, by decide⟩,⟨398456, by decide⟩,⟨398491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6950_398492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6950 ⟨398492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6950
    ⟨398492, by decide⟩ (by decide) (![⟨398405, by decide⟩,⟨398432, by decide⟩,⟨398456, by decide⟩,⟨398491, by decide⟩]) unmarked_context_11_6950_398492 node_context_11_6950_398492
  intro a
  fin_cases a
  · exact context_12_27800_398405
  · exact context_12_27801_398432
  · exact context_12_27802_398456
  · exact context_12_27803_398491

theorem selected_cut_15558 : selected 9 ⟨398512, by decide⟩
    (prefixPartial 12 27804) = some ⟨12, 2, 0, 398512, 27804, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_27804_398512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27804 ⟨398512, by decide⟩ :=
  accepted_of_selected 12 27804 ⟨398512, by decide⟩ ⟨12, 2, 0, 398512, 27804, 1877, 65536⟩
    (by decide) selected_cut_15558

theorem selected_cut_15559 : selected 9 ⟨398530, by decide⟩
    (prefixPartial 12 27805) = some ⟨12, 2, 0, 398530, 27805, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_27805_398530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27805 ⟨398530, by decide⟩ :=
  accepted_of_selected 12 27805 ⟨398530, by decide⟩ ⟨12, 2, 0, 398530, 27805, 2101, 65536⟩
    (by decide) selected_cut_15559

theorem selected_cut_15560 : selected 9 ⟨398547, by decide⟩
    (prefixPartial 12 27806) = some ⟨12, 2, 0, 398547, 27806, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_27806_398547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27806 ⟨398547, by decide⟩ :=
  accepted_of_selected 12 27806 ⟨398547, by decide⟩ ⟨12, 2, 0, 398547, 27806, 1997, 65536⟩
    (by decide) selected_cut_15560

theorem selected_cut_15561 : selected 9 ⟨398564, by decide⟩
    (prefixPartial 12 27807) = some ⟨12, 2, 0, 398564, 27807, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_27807_398564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27807 ⟨398564, by decide⟩ :=
  accepted_of_selected 12 27807 ⟨398564, by decide⟩ ⟨12, 2, 0, 398564, 27807, 2129, 65536⟩
    (by decide) selected_cut_15561

theorem unmarked_context_11_6951_398565 : frontier 10 ⟨398565, by decide⟩
    (prefixCache 11 6951) (prefixPartial 11 6951) = false := by
  decide +kernel

theorem node_context_11_6951_398565 : EJMOriginalGlobalDAGData.nodes 10 ⟨398565, by decide⟩ =
    .split (coordinate 11) (![⟨398512, by decide⟩,⟨398530, by decide⟩,⟨398547, by decide⟩,⟨398564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6951_398565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6951 ⟨398565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6951
    ⟨398565, by decide⟩ (by decide) (![⟨398512, by decide⟩,⟨398530, by decide⟩,⟨398547, by decide⟩,⟨398564, by decide⟩]) unmarked_context_11_6951_398565 node_context_11_6951_398565
  intro a
  fin_cases a
  · exact context_12_27804_398512
  · exact context_12_27805_398530
  · exact context_12_27806_398547
  · exact context_12_27807_398564

theorem unmarked_context_10_1737_398566 : frontier 11 ⟨398566, by decide⟩
    (prefixCache 10 1737) (prefixPartial 10 1737) = false := by
  decide +kernel

theorem node_context_10_1737_398566 : EJMOriginalGlobalDAGData.nodes 11 ⟨398566, by decide⟩ =
    .split (coordinate 10) (![⟨398271, by decide⟩,⟨398376, by decide⟩,⟨398492, by decide⟩,⟨398565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1737_398566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1737 ⟨398566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1737
    ⟨398566, by decide⟩ (by decide) (![⟨398271, by decide⟩,⟨398376, by decide⟩,⟨398492, by decide⟩,⟨398565, by decide⟩]) unmarked_context_10_1737_398566 node_context_10_1737_398566
  intro a
  fin_cases a
  · exact context_11_6948_398271
  · exact context_11_6949_398376
  · exact context_11_6950_398492
  · exact context_11_6951_398565

theorem selected_cut_15562 : selected 9 ⟨398601, by decide⟩
    (prefixPartial 12 27808) = some ⟨12, 2, 0, 398601, 27808, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_27808_398601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27808 ⟨398601, by decide⟩ :=
  accepted_of_selected 12 27808 ⟨398601, by decide⟩ ⟨12, 2, 0, 398601, 27808, 2485, 65536⟩
    (by decide) selected_cut_15562

theorem selected_cut_15563 : selected 9 ⟨398619, by decide⟩
    (prefixPartial 12 27809) = some ⟨12, 2, 0, 398619, 27809, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_27809_398619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27809 ⟨398619, by decide⟩ :=
  accepted_of_selected 12 27809 ⟨398619, by decide⟩ ⟨12, 2, 0, 398619, 27809, 1893, 65536⟩
    (by decide) selected_cut_15563

theorem selected_cut_15564 : selected 9 ⟨398639, by decide⟩
    (prefixPartial 12 27810) = some ⟨12, 2, 0, 398639, 27810, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_27810_398639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27810 ⟨398639, by decide⟩ :=
  accepted_of_selected 12 27810 ⟨398639, by decide⟩ ⟨12, 2, 0, 398639, 27810, 1785, 65536⟩
    (by decide) selected_cut_15564

theorem selected_cut_15565 : selected 9 ⟨398659, by decide⟩
    (prefixPartial 12 27811) = some ⟨12, 2, 0, 398659, 27811, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_27811_398659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27811 ⟨398659, by decide⟩ :=
  accepted_of_selected 12 27811 ⟨398659, by decide⟩ ⟨12, 2, 0, 398659, 27811, 1845, 65536⟩
    (by decide) selected_cut_15565

theorem unmarked_context_11_6952_398660 : frontier 10 ⟨398660, by decide⟩
    (prefixCache 11 6952) (prefixPartial 11 6952) = false := by
  decide +kernel

theorem node_context_11_6952_398660 : EJMOriginalGlobalDAGData.nodes 10 ⟨398660, by decide⟩ =
    .split (coordinate 11) (![⟨398601, by decide⟩,⟨398619, by decide⟩,⟨398639, by decide⟩,⟨398659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6952_398660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6952 ⟨398660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6952
    ⟨398660, by decide⟩ (by decide) (![⟨398601, by decide⟩,⟨398619, by decide⟩,⟨398639, by decide⟩,⟨398659, by decide⟩]) unmarked_context_11_6952_398660 node_context_11_6952_398660
  intro a
  fin_cases a
  · exact context_12_27808_398601
  · exact context_12_27809_398619
  · exact context_12_27810_398639
  · exact context_12_27811_398659

theorem selected_cut_15566 : selected 9 ⟨398678, by decide⟩
    (prefixPartial 12 27812) = some ⟨12, 2, 0, 398678, 27812, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_27812_398678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27812 ⟨398678, by decide⟩ :=
  accepted_of_selected 12 27812 ⟨398678, by decide⟩ ⟨12, 2, 0, 398678, 27812, 1477, 65536⟩
    (by decide) selected_cut_15566

theorem selected_cut_15567 : selected 9 ⟨398697, by decide⟩
    (prefixPartial 12 27813) = some ⟨12, 2, 0, 398697, 27813, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_27813_398697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27813 ⟨398697, by decide⟩ :=
  accepted_of_selected 12 27813 ⟨398697, by decide⟩ ⟨12, 2, 0, 398697, 27813, 1681, 65536⟩
    (by decide) selected_cut_15567

theorem selected_cut_15568 : selected 9 ⟨398714, by decide⟩
    (prefixPartial 12 27814) = some ⟨12, 2, 0, 398714, 27814, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_27814_398714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27814 ⟨398714, by decide⟩ :=
  accepted_of_selected 12 27814 ⟨398714, by decide⟩ ⟨12, 2, 0, 398714, 27814, 1629, 65536⟩
    (by decide) selected_cut_15568

theorem selected_cut_15569 : selected 9 ⟨398738, by decide⟩
    (prefixPartial 12 27815) = some ⟨12, 2, 0, 398738, 27815, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_27815_398738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27815 ⟨398738, by decide⟩ :=
  accepted_of_selected 12 27815 ⟨398738, by decide⟩ ⟨12, 2, 0, 398738, 27815, 1769, 65536⟩
    (by decide) selected_cut_15569

theorem unmarked_context_11_6953_398739 : frontier 10 ⟨398739, by decide⟩
    (prefixCache 11 6953) (prefixPartial 11 6953) = false := by
  decide +kernel

theorem node_context_11_6953_398739 : EJMOriginalGlobalDAGData.nodes 10 ⟨398739, by decide⟩ =
    .split (coordinate 11) (![⟨398678, by decide⟩,⟨398697, by decide⟩,⟨398714, by decide⟩,⟨398738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6953_398739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6953 ⟨398739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6953
    ⟨398739, by decide⟩ (by decide) (![⟨398678, by decide⟩,⟨398697, by decide⟩,⟨398714, by decide⟩,⟨398738, by decide⟩]) unmarked_context_11_6953_398739 node_context_11_6953_398739
  intro a
  fin_cases a
  · exact context_12_27812_398678
  · exact context_12_27813_398697
  · exact context_12_27814_398714
  · exact context_12_27815_398738

theorem selected_cut_15570 : selected 9 ⟨398759, by decide⟩
    (prefixPartial 12 27816) = some ⟨12, 2, 0, 398759, 27816, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_27816_398759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27816 ⟨398759, by decide⟩ :=
  accepted_of_selected 12 27816 ⟨398759, by decide⟩ ⟨12, 2, 0, 398759, 27816, 1649, 65536⟩
    (by decide) selected_cut_15570

theorem selected_cut_15571 : selected 9 ⟨398774, by decide⟩
    (prefixPartial 12 27817) = some ⟨12, 2, 0, 398774, 27817, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_27817_398774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27817 ⟨398774, by decide⟩ :=
  accepted_of_selected 12 27817 ⟨398774, by decide⟩ ⟨12, 2, 0, 398774, 27817, 1685, 65536⟩
    (by decide) selected_cut_15571

theorem selected_cut_15572 : selected 9 ⟨398790, by decide⟩
    (prefixPartial 12 27818) = some ⟨12, 2, 0, 398790, 27818, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_27818_398790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27818 ⟨398790, by decide⟩ :=
  accepted_of_selected 12 27818 ⟨398790, by decide⟩ ⟨12, 2, 0, 398790, 27818, 1541, 65536⟩
    (by decide) selected_cut_15572

theorem selected_cut_15573 : selected 9 ⟨398806, by decide⟩
    (prefixPartial 12 27819) = some ⟨12, 2, 0, 398806, 27819, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_27819_398806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27819 ⟨398806, by decide⟩ :=
  accepted_of_selected 12 27819 ⟨398806, by decide⟩ ⟨12, 2, 0, 398806, 27819, 1701, 65536⟩
    (by decide) selected_cut_15573

theorem unmarked_context_11_6954_398807 : frontier 10 ⟨398807, by decide⟩
    (prefixCache 11 6954) (prefixPartial 11 6954) = false := by
  decide +kernel

theorem node_context_11_6954_398807 : EJMOriginalGlobalDAGData.nodes 10 ⟨398807, by decide⟩ =
    .split (coordinate 11) (![⟨398759, by decide⟩,⟨398774, by decide⟩,⟨398790, by decide⟩,⟨398806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6954_398807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6954 ⟨398807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6954
    ⟨398807, by decide⟩ (by decide) (![⟨398759, by decide⟩,⟨398774, by decide⟩,⟨398790, by decide⟩,⟨398806, by decide⟩]) unmarked_context_11_6954_398807 node_context_11_6954_398807
  intro a
  fin_cases a
  · exact context_12_27816_398759
  · exact context_12_27817_398774
  · exact context_12_27818_398790
  · exact context_12_27819_398806

theorem selected_cut_15574 : selected 9 ⟨398823, by decide⟩
    (prefixPartial 12 27820) = some ⟨12, 2, 0, 398823, 27820, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_27820_398823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27820 ⟨398823, by decide⟩ :=
  accepted_of_selected 12 27820 ⟨398823, by decide⟩ ⟨12, 2, 0, 398823, 27820, 1453, 65536⟩
    (by decide) selected_cut_15574

theorem selected_cut_15575 : selected 9 ⟨398838, by decide⟩
    (prefixPartial 12 27821) = some ⟨12, 2, 0, 398838, 27821, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_27821_398838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27821 ⟨398838, by decide⟩ :=
  accepted_of_selected 12 27821 ⟨398838, by decide⟩ ⟨12, 2, 0, 398838, 27821, 1489, 65536⟩
    (by decide) selected_cut_15575

theorem selected_cut_15576 : selected 9 ⟨398854, by decide⟩
    (prefixPartial 12 27822) = some ⟨12, 2, 0, 398854, 27822, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_27822_398854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27822 ⟨398854, by decide⟩ :=
  accepted_of_selected 12 27822 ⟨398854, by decide⟩ ⟨12, 2, 0, 398854, 27822, 1473, 65536⟩
    (by decide) selected_cut_15576

theorem selected_cut_15577 : selected 9 ⟨398869, by decide⟩
    (prefixPartial 12 27823) = some ⟨12, 2, 0, 398869, 27823, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_27823_398869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27823 ⟨398869, by decide⟩ :=
  accepted_of_selected 12 27823 ⟨398869, by decide⟩ ⟨12, 2, 0, 398869, 27823, 1537, 65536⟩
    (by decide) selected_cut_15577

theorem unmarked_context_11_6955_398870 : frontier 10 ⟨398870, by decide⟩
    (prefixCache 11 6955) (prefixPartial 11 6955) = false := by
  decide +kernel

theorem node_context_11_6955_398870 : EJMOriginalGlobalDAGData.nodes 10 ⟨398870, by decide⟩ =
    .split (coordinate 11) (![⟨398823, by decide⟩,⟨398838, by decide⟩,⟨398854, by decide⟩,⟨398869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6955_398870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6955 ⟨398870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6955
    ⟨398870, by decide⟩ (by decide) (![⟨398823, by decide⟩,⟨398838, by decide⟩,⟨398854, by decide⟩,⟨398869, by decide⟩]) unmarked_context_11_6955_398870 node_context_11_6955_398870
  intro a
  fin_cases a
  · exact context_12_27820_398823
  · exact context_12_27821_398838
  · exact context_12_27822_398854
  · exact context_12_27823_398869

theorem unmarked_context_10_1738_398871 : frontier 11 ⟨398871, by decide⟩
    (prefixCache 10 1738) (prefixPartial 10 1738) = false := by
  decide +kernel

theorem node_context_10_1738_398871 : EJMOriginalGlobalDAGData.nodes 11 ⟨398871, by decide⟩ =
    .split (coordinate 10) (![⟨398660, by decide⟩,⟨398739, by decide⟩,⟨398807, by decide⟩,⟨398870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1738_398871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1738 ⟨398871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1738
    ⟨398871, by decide⟩ (by decide) (![⟨398660, by decide⟩,⟨398739, by decide⟩,⟨398807, by decide⟩,⟨398870, by decide⟩]) unmarked_context_10_1738_398871 node_context_10_1738_398871
  intro a
  fin_cases a
  · exact context_11_6952_398660
  · exact context_11_6953_398739
  · exact context_11_6954_398807
  · exact context_11_6955_398870

theorem selected_cut_15578 : selected 9 ⟨398897, by decide⟩
    (prefixPartial 12 27824) = some ⟨12, 2, 0, 398897, 27824, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_27824_398897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27824 ⟨398897, by decide⟩ :=
  accepted_of_selected 12 27824 ⟨398897, by decide⟩ ⟨12, 2, 0, 398897, 27824, 1817, 65536⟩
    (by decide) selected_cut_15578

theorem selected_cut_15579 : selected 9 ⟨398908, by decide⟩
    (prefixPartial 12 27825) = some ⟨12, 2, 0, 398908, 27825, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_27825_398908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27825 ⟨398908, by decide⟩ :=
  accepted_of_selected 12 27825 ⟨398908, by decide⟩ ⟨12, 2, 0, 398908, 27825, 1273, 65536⟩
    (by decide) selected_cut_15579

theorem selected_cut_15580 : selected 9 ⟨398920, by decide⟩
    (prefixPartial 12 27826) = some ⟨12, 2, 0, 398920, 27826, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_27826_398920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27826 ⟨398920, by decide⟩ :=
  accepted_of_selected 12 27826 ⟨398920, by decide⟩ ⟨12, 2, 0, 398920, 27826, 1225, 65536⟩
    (by decide) selected_cut_15580

theorem selected_cut_15581 : selected 9 ⟨398930, by decide⟩
    (prefixPartial 12 27827) = some ⟨12, 2, 0, 398930, 27827, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_27827_398930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27827 ⟨398930, by decide⟩ :=
  accepted_of_selected 12 27827 ⟨398930, by decide⟩ ⟨12, 2, 0, 398930, 27827, 1345, 65536⟩
    (by decide) selected_cut_15581

theorem unmarked_context_11_6956_398931 : frontier 10 ⟨398931, by decide⟩
    (prefixCache 11 6956) (prefixPartial 11 6956) = false := by
  decide +kernel

theorem node_context_11_6956_398931 : EJMOriginalGlobalDAGData.nodes 10 ⟨398931, by decide⟩ =
    .split (coordinate 11) (![⟨398897, by decide⟩,⟨398908, by decide⟩,⟨398920, by decide⟩,⟨398930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6956_398931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6956 ⟨398931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6956
    ⟨398931, by decide⟩ (by decide) (![⟨398897, by decide⟩,⟨398908, by decide⟩,⟨398920, by decide⟩,⟨398930, by decide⟩]) unmarked_context_11_6956_398931 node_context_11_6956_398931
  intro a
  fin_cases a
  · exact context_12_27824_398897
  · exact context_12_27825_398908
  · exact context_12_27826_398920
  · exact context_12_27827_398930

theorem selected_cut_15582 : selected 9 ⟨398946, by decide⟩
    (prefixPartial 12 27828) = some ⟨12, 2, 0, 398946, 27828, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_27828_398946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27828 ⟨398946, by decide⟩ :=
  accepted_of_selected 12 27828 ⟨398946, by decide⟩ ⟨12, 2, 0, 398946, 27828, 1229, 65536⟩
    (by decide) selected_cut_15582

theorem selected_cut_15583 : selected 9 ⟨398958, by decide⟩
    (prefixPartial 12 27829) = some ⟨12, 2, 0, 398958, 27829, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_27829_398958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27829 ⟨398958, by decide⟩ :=
  accepted_of_selected 12 27829 ⟨398958, by decide⟩ ⟨12, 2, 0, 398958, 27829, 1305, 65536⟩
    (by decide) selected_cut_15583

theorem selected_cut_15584 : selected 9 ⟨398971, by decide⟩
    (prefixPartial 12 27830) = some ⟨12, 2, 0, 398971, 27830, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_27830_398971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27830 ⟨398971, by decide⟩ :=
  accepted_of_selected 12 27830 ⟨398971, by decide⟩ ⟨12, 2, 0, 398971, 27830, 1297, 65536⟩
    (by decide) selected_cut_15584

theorem selected_cut_15585 : selected 9 ⟨398986, by decide⟩
    (prefixPartial 12 27831) = some ⟨12, 2, 0, 398986, 27831, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_27831_398986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27831 ⟨398986, by decide⟩ :=
  accepted_of_selected 12 27831 ⟨398986, by decide⟩ ⟨12, 2, 0, 398986, 27831, 1409, 65536⟩
    (by decide) selected_cut_15585

theorem unmarked_context_11_6957_398987 : frontier 10 ⟨398987, by decide⟩
    (prefixCache 11 6957) (prefixPartial 11 6957) = false := by
  decide +kernel

theorem node_context_11_6957_398987 : EJMOriginalGlobalDAGData.nodes 10 ⟨398987, by decide⟩ =
    .split (coordinate 11) (![⟨398946, by decide⟩,⟨398958, by decide⟩,⟨398971, by decide⟩,⟨398986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6957_398987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6957 ⟨398987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6957
    ⟨398987, by decide⟩ (by decide) (![⟨398946, by decide⟩,⟨398958, by decide⟩,⟨398971, by decide⟩,⟨398986, by decide⟩]) unmarked_context_11_6957_398987 node_context_11_6957_398987
  intro a
  fin_cases a
  · exact context_12_27828_398946
  · exact context_12_27829_398958
  · exact context_12_27830_398971
  · exact context_12_27831_398986

theorem selected_cut_15586 : selected 9 ⟨399002, by decide⟩
    (prefixPartial 12 27832) = some ⟨12, 2, 0, 399002, 27832, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_27832_399002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27832 ⟨399002, by decide⟩ :=
  accepted_of_selected 12 27832 ⟨399002, by decide⟩ ⟨12, 2, 0, 399002, 27832, 1241, 65536⟩
    (by decide) selected_cut_15586

theorem selected_cut_15587 : selected 9 ⟨399014, by decide⟩
    (prefixPartial 12 27833) = some ⟨12, 2, 0, 399014, 27833, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_27833_399014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27833 ⟨399014, by decide⟩ :=
  accepted_of_selected 12 27833 ⟨399014, by decide⟩ ⟨12, 2, 0, 399014, 27833, 1221, 65536⟩
    (by decide) selected_cut_15587

theorem selected_cut_15588 : selected 9 ⟨399028, by decide⟩
    (prefixPartial 12 27834) = some ⟨12, 2, 0, 399028, 27834, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_27834_399028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27834 ⟨399028, by decide⟩ :=
  accepted_of_selected 12 27834 ⟨399028, by decide⟩ ⟨12, 2, 0, 399028, 27834, 1189, 65536⟩
    (by decide) selected_cut_15588

theorem selected_cut_15589 : selected 9 ⟨399041, by decide⟩
    (prefixPartial 12 27835) = some ⟨12, 2, 0, 399041, 27835, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_27835_399041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27835 ⟨399041, by decide⟩ :=
  accepted_of_selected 12 27835 ⟨399041, by decide⟩ ⟨12, 2, 0, 399041, 27835, 1281, 65536⟩
    (by decide) selected_cut_15589

theorem unmarked_context_11_6958_399042 : frontier 10 ⟨399042, by decide⟩
    (prefixCache 11 6958) (prefixPartial 11 6958) = false := by
  decide +kernel

theorem node_context_11_6958_399042 : EJMOriginalGlobalDAGData.nodes 10 ⟨399042, by decide⟩ =
    .split (coordinate 11) (![⟨399002, by decide⟩,⟨399014, by decide⟩,⟨399028, by decide⟩,⟨399041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6958_399042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6958 ⟨399042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6958
    ⟨399042, by decide⟩ (by decide) (![⟨399002, by decide⟩,⟨399014, by decide⟩,⟨399028, by decide⟩,⟨399041, by decide⟩]) unmarked_context_11_6958_399042 node_context_11_6958_399042
  intro a
  fin_cases a
  · exact context_12_27832_399002
  · exact context_12_27833_399014
  · exact context_12_27834_399028
  · exact context_12_27835_399041

theorem selected_cut_15590 : selected 10 ⟨399076, by decide⟩
    (prefixPartial 11 6959) = some ⟨11, 2, 0, 399076, 6959, 3713, 262144⟩ := by
  decide +kernel

theorem context_11_6959_399076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6959 ⟨399076, by decide⟩ :=
  accepted_of_selected 11 6959 ⟨399076, by decide⟩ ⟨11, 2, 0, 399076, 6959, 3713, 262144⟩
    (by decide) selected_cut_15590

theorem unmarked_context_10_1739_399077 : frontier 11 ⟨399077, by decide⟩
    (prefixCache 10 1739) (prefixPartial 10 1739) = false := by
  decide +kernel

theorem node_context_10_1739_399077 : EJMOriginalGlobalDAGData.nodes 11 ⟨399077, by decide⟩ =
    .split (coordinate 10) (![⟨398931, by decide⟩,⟨398987, by decide⟩,⟨399042, by decide⟩,⟨399076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1739_399077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1739 ⟨399077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1739
    ⟨399077, by decide⟩ (by decide) (![⟨398931, by decide⟩,⟨398987, by decide⟩,⟨399042, by decide⟩,⟨399076, by decide⟩]) unmarked_context_10_1739_399077 node_context_10_1739_399077
  intro a
  fin_cases a
  · exact context_11_6956_398931
  · exact context_11_6957_398987
  · exact context_11_6958_399042
  · exact context_11_6959_399076

theorem unmarked_context_9_434_399078 : frontier 12 ⟨399078, by decide⟩
    (prefixCache 9 434) (prefixPartial 9 434) = false := by
  decide +kernel

theorem node_context_9_434_399078 : EJMOriginalGlobalDAGData.nodes 12 ⟨399078, by decide⟩ =
    .split (coordinate 9) (![⟨398119, by decide⟩,⟨398566, by decide⟩,⟨398871, by decide⟩,⟨399077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_434_399078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 434 ⟨399078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 434
    ⟨399078, by decide⟩ (by decide) (![⟨398119, by decide⟩,⟨398566, by decide⟩,⟨398871, by decide⟩,⟨399077, by decide⟩]) unmarked_context_9_434_399078 node_context_9_434_399078
  intro a
  fin_cases a
  · exact context_10_1736_398119
  · exact context_10_1737_398566
  · exact context_10_1738_398871
  · exact context_10_1739_399077

theorem selected_cut_15591 : selected 10 ⟨399102, by decide⟩
    (prefixPartial 11 6960) = some ⟨11, 2, 0, 399102, 6960, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_6960_399102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6960 ⟨399102, by decide⟩ :=
  accepted_of_selected 11 6960 ⟨399102, by decide⟩ ⟨11, 2, 0, 399102, 6960, 2489, 262144⟩
    (by decide) selected_cut_15591

theorem selected_cut_15592 : selected 10 ⟨399136, by decide⟩
    (prefixPartial 11 6961) = some ⟨11, 2, 0, 399136, 6961, 3049, 262144⟩ := by
  decide +kernel

theorem context_11_6961_399136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6961 ⟨399136, by decide⟩ :=
  accepted_of_selected 11 6961 ⟨399136, by decide⟩ ⟨11, 2, 0, 399136, 6961, 3049, 262144⟩
    (by decide) selected_cut_15592

theorem selected_cut_15593 : selected 10 ⟨399168, by decide⟩
    (prefixPartial 11 6962) = some ⟨11, 2, 0, 399168, 6962, 3333, 262144⟩ := by
  decide +kernel

theorem context_11_6962_399168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6962 ⟨399168, by decide⟩ :=
  accepted_of_selected 11 6962 ⟨399168, by decide⟩ ⟨11, 2, 0, 399168, 6962, 3333, 262144⟩
    (by decide) selected_cut_15593

theorem selected_cut_15594 : selected 10 ⟨399201, by decide⟩
    (prefixPartial 11 6963) = some ⟨11, 2, 0, 399201, 6963, 2713, 262144⟩ := by
  decide +kernel

theorem context_11_6963_399201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6963 ⟨399201, by decide⟩ :=
  accepted_of_selected 11 6963 ⟨399201, by decide⟩ ⟨11, 2, 0, 399201, 6963, 2713, 262144⟩
    (by decide) selected_cut_15594

theorem unmarked_context_10_1740_399202 : frontier 11 ⟨399202, by decide⟩
    (prefixCache 10 1740) (prefixPartial 10 1740) = false := by
  decide +kernel

theorem node_context_10_1740_399202 : EJMOriginalGlobalDAGData.nodes 11 ⟨399202, by decide⟩ =
    .split (coordinate 10) (![⟨399102, by decide⟩,⟨399136, by decide⟩,⟨399168, by decide⟩,⟨399201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1740_399202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1740 ⟨399202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1740
    ⟨399202, by decide⟩ (by decide) (![⟨399102, by decide⟩,⟨399136, by decide⟩,⟨399168, by decide⟩,⟨399201, by decide⟩]) unmarked_context_10_1740_399202 node_context_10_1740_399202
  intro a
  fin_cases a
  · exact context_11_6960_399102
  · exact context_11_6961_399136
  · exact context_11_6962_399168
  · exact context_11_6963_399201

theorem selected_cut_15595 : selected 10 ⟨399228, by decide⟩
    (prefixPartial 11 6964) = some ⟨11, 2, 0, 399228, 6964, 3085, 262144⟩ := by
  decide +kernel

theorem context_11_6964_399228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6964 ⟨399228, by decide⟩ :=
  accepted_of_selected 11 6964 ⟨399228, by decide⟩ ⟨11, 2, 0, 399228, 6964, 3085, 262144⟩
    (by decide) selected_cut_15595

theorem selected_cut_15596 : selected 10 ⟨399252, by decide⟩
    (prefixPartial 11 6965) = some ⟨11, 2, 0, 399252, 6965, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_6965_399252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6965 ⟨399252, by decide⟩ :=
  accepted_of_selected 11 6965 ⟨399252, by decide⟩ ⟨11, 2, 0, 399252, 6965, 2313, 262144⟩
    (by decide) selected_cut_15596

theorem selected_cut_15597 : selected 10 ⟨399271, by decide⟩
    (prefixPartial 11 6966) = some ⟨11, 2, 0, 399271, 6966, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_6966_399271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6966 ⟨399271, by decide⟩ :=
  accepted_of_selected 11 6966 ⟨399271, by decide⟩ ⟨11, 2, 0, 399271, 6966, 2157, 262144⟩
    (by decide) selected_cut_15597

theorem selected_cut_15598 : selected 10 ⟨399287, by decide⟩
    (prefixPartial 11 6967) = some ⟨11, 2, 0, 399287, 6967, 1817, 262144⟩ := by
  decide +kernel

theorem context_11_6967_399287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6967 ⟨399287, by decide⟩ :=
  accepted_of_selected 11 6967 ⟨399287, by decide⟩ ⟨11, 2, 0, 399287, 6967, 1817, 262144⟩
    (by decide) selected_cut_15598

theorem unmarked_context_10_1741_399288 : frontier 11 ⟨399288, by decide⟩
    (prefixCache 10 1741) (prefixPartial 10 1741) = false := by
  decide +kernel

theorem node_context_10_1741_399288 : EJMOriginalGlobalDAGData.nodes 11 ⟨399288, by decide⟩ =
    .split (coordinate 10) (![⟨399228, by decide⟩,⟨399252, by decide⟩,⟨399271, by decide⟩,⟨399287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1741_399288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1741 ⟨399288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1741
    ⟨399288, by decide⟩ (by decide) (![⟨399228, by decide⟩,⟨399252, by decide⟩,⟨399271, by decide⟩,⟨399287, by decide⟩]) unmarked_context_10_1741_399288 node_context_10_1741_399288
  intro a
  fin_cases a
  · exact context_11_6964_399228
  · exact context_11_6965_399252
  · exact context_11_6966_399271
  · exact context_11_6967_399287

theorem selected_cut_15599 : selected 10 ⟨399302, by decide⟩
    (prefixPartial 11 6968) = some ⟨11, 2, 0, 399302, 6968, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_6968_399302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6968 ⟨399302, by decide⟩ :=
  accepted_of_selected 11 6968 ⟨399302, by decide⟩ ⟨11, 2, 0, 399302, 6968, 1685, 262144⟩
    (by decide) selected_cut_15599

theorem selected_cut_15600 : selected 10 ⟨399317, by decide⟩
    (prefixPartial 11 6969) = some ⟨11, 2, 0, 399317, 6969, 1233, 262144⟩ := by
  decide +kernel

theorem context_11_6969_399317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6969 ⟨399317, by decide⟩ :=
  accepted_of_selected 11 6969 ⟨399317, by decide⟩ ⟨11, 2, 0, 399317, 6969, 1233, 262144⟩
    (by decide) selected_cut_15600

theorem selected_cut_15601 : selected 10 ⟨399333, by decide⟩
    (prefixPartial 11 6970) = some ⟨11, 2, 0, 399333, 6970, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_6970_399333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6970 ⟨399333, by decide⟩ :=
  accepted_of_selected 11 6970 ⟨399333, by decide⟩ ⟨11, 2, 0, 399333, 6970, 1093, 262144⟩
    (by decide) selected_cut_15601

theorem selected_cut_15602 : selected 10 ⟨399343, by decide⟩
    (prefixPartial 11 6971) = some ⟨11, 2, 0, 399343, 6971, 809, 262144⟩ := by
  decide +kernel

theorem context_11_6971_399343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6971 ⟨399343, by decide⟩ :=
  accepted_of_selected 11 6971 ⟨399343, by decide⟩ ⟨11, 2, 0, 399343, 6971, 809, 262144⟩
    (by decide) selected_cut_15602

theorem unmarked_context_10_1742_399344 : frontier 11 ⟨399344, by decide⟩
    (prefixCache 10 1742) (prefixPartial 10 1742) = false := by
  decide +kernel

theorem node_context_10_1742_399344 : EJMOriginalGlobalDAGData.nodes 11 ⟨399344, by decide⟩ =
    .split (coordinate 10) (![⟨399302, by decide⟩,⟨399317, by decide⟩,⟨399333, by decide⟩,⟨399343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1742_399344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1742 ⟨399344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1742
    ⟨399344, by decide⟩ (by decide) (![⟨399302, by decide⟩,⟨399317, by decide⟩,⟨399333, by decide⟩,⟨399343, by decide⟩]) unmarked_context_10_1742_399344 node_context_10_1742_399344
  intro a
  fin_cases a
  · exact context_11_6968_399302
  · exact context_11_6969_399317
  · exact context_11_6970_399333
  · exact context_11_6971_399343

theorem selected_cut_15603 : selected 11 ⟨399387, by decide⟩
    (prefixPartial 10 1743) = some ⟨10, 2, 0, 399387, 1743, 1209, 1048576⟩ := by
  decide +kernel

theorem context_10_1743_399387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1743 ⟨399387, by decide⟩ :=
  accepted_of_selected 10 1743 ⟨399387, by decide⟩ ⟨10, 2, 0, 399387, 1743, 1209, 1048576⟩
    (by decide) selected_cut_15603

theorem unmarked_context_9_435_399388 : frontier 12 ⟨399388, by decide⟩
    (prefixCache 9 435) (prefixPartial 9 435) = false := by
  decide +kernel

theorem node_context_9_435_399388 : EJMOriginalGlobalDAGData.nodes 12 ⟨399388, by decide⟩ =
    .split (coordinate 9) (![⟨399202, by decide⟩,⟨399288, by decide⟩,⟨399344, by decide⟩,⟨399387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_435_399388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 435 ⟨399388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 435
    ⟨399388, by decide⟩ (by decide) (![⟨399202, by decide⟩,⟨399288, by decide⟩,⟨399344, by decide⟩,⟨399387, by decide⟩]) unmarked_context_9_435_399388 node_context_9_435_399388
  intro a
  fin_cases a
  · exact context_10_1740_399202
  · exact context_10_1741_399288
  · exact context_10_1742_399344
  · exact context_10_1743_399387

theorem unmarked_context_8_108_399389 : frontier 13 ⟨399389, by decide⟩
    (prefixCache 8 108) (prefixPartial 8 108) = false := by
  decide +kernel

theorem node_context_8_108_399389 : EJMOriginalGlobalDAGData.nodes 13 ⟨399389, by decide⟩ =
    .split (coordinate 8) (![⟨394178, by decide⟩,⟨397573, by decide⟩,⟨399078, by decide⟩,⟨399388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_108_399389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 108 ⟨399389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 108
    ⟨399389, by decide⟩ (by decide) (![⟨394178, by decide⟩,⟨397573, by decide⟩,⟨399078, by decide⟩,⟨399388, by decide⟩]) unmarked_context_8_108_399389 node_context_8_108_399389
  intro a
  fin_cases a
  · exact context_9_432_394178
  · exact context_9_433_397573
  · exact context_9_434_399078
  · exact context_9_435_399388

theorem selected_cut_15604 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27904) = some ⟨12, 1, 0, 34034, 27904, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27904_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27904 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27904 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27904, 1, 65536⟩
    (by decide) selected_cut_15604

theorem selected_cut_15605 : selected 9 ⟨388829, by decide⟩
    (prefixPartial 12 27905) = some ⟨12, 1, 0, 388829, 27905, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27905_388829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27905 ⟨388829, by decide⟩ :=
  accepted_of_selected 12 27905 ⟨388829, by decide⟩ ⟨12, 1, 0, 388829, 27905, 1, 65536⟩
    (by decide) selected_cut_15605

theorem selected_cut_15606 : selected 7 ⟨399440, by decide⟩
    (prefixPartial 14 446496) = some ⟨14, 2, 0, 399440, 446496, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_446496_399440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446496 ⟨399440, by decide⟩ :=
  accepted_of_selected 14 446496 ⟨399440, by decide⟩ ⟨14, 2, 0, 399440, 446496, 1249, 4096⟩
    (by decide) selected_cut_15606

theorem selected_cut_15607 : selected 7 ⟨399460, by decide⟩
    (prefixPartial 14 446497) = some ⟨14, 2, 0, 399460, 446497, 945, 4096⟩ := by
  decide +kernel

theorem context_14_446497_399460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446497 ⟨399460, by decide⟩ :=
  accepted_of_selected 14 446497 ⟨399460, by decide⟩ ⟨14, 2, 0, 399460, 446497, 945, 4096⟩
    (by decide) selected_cut_15607

theorem selected_cut_15608 : selected 7 ⟨399480, by decide⟩
    (prefixPartial 14 446498) = some ⟨14, 2, 0, 399480, 446498, 1225, 4096⟩ := by
  decide +kernel

theorem context_14_446498_399480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446498 ⟨399480, by decide⟩ :=
  accepted_of_selected 14 446498 ⟨399480, by decide⟩ ⟨14, 2, 0, 399480, 446498, 1225, 4096⟩
    (by decide) selected_cut_15608

theorem selected_cut_15609 : selected 7 ⟨399501, by decide⟩
    (prefixPartial 14 446499) = some ⟨14, 2, 0, 399501, 446499, 1209, 4096⟩ := by
  decide +kernel

theorem context_14_446499_399501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446499 ⟨399501, by decide⟩ :=
  accepted_of_selected 14 446499 ⟨399501, by decide⟩ ⟨14, 2, 0, 399501, 446499, 1209, 4096⟩
    (by decide) selected_cut_15609

theorem unmarked_context_13_111624_399502 : frontier 8 ⟨399502, by decide⟩
    (prefixCache 13 111624) (prefixPartial 13 111624) = false := by
  decide +kernel

theorem node_context_13_111624_399502 : EJMOriginalGlobalDAGData.nodes 8 ⟨399502, by decide⟩ =
    .split (coordinate 13) (![⟨399440, by decide⟩,⟨399460, by decide⟩,⟨399480, by decide⟩,⟨399501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111624_399502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111624 ⟨399502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111624
    ⟨399502, by decide⟩ (by decide) (![⟨399440, by decide⟩,⟨399460, by decide⟩,⟨399480, by decide⟩,⟨399501, by decide⟩]) unmarked_context_13_111624_399502 node_context_13_111624_399502
  intro a
  fin_cases a
  · exact context_14_446496_399440
  · exact context_14_446497_399460
  · exact context_14_446498_399480
  · exact context_14_446499_399501

theorem selected_cut_15610 : selected 8 ⟨399594, by decide⟩
    (prefixPartial 13 111625) = some ⟨13, 2, 0, 399594, 111625, 4077, 16384⟩ := by
  decide +kernel

theorem context_13_111625_399594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111625 ⟨399594, by decide⟩ :=
  accepted_of_selected 13 111625 ⟨399594, by decide⟩ ⟨13, 2, 0, 399594, 111625, 4077, 16384⟩
    (by decide) selected_cut_15610

theorem selected_cut_15611 : selected 8 ⟨399644, by decide⟩
    (prefixPartial 13 111626) = some ⟨13, 2, 0, 399644, 111626, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_111626_399644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111626 ⟨399644, by decide⟩ :=
  accepted_of_selected 13 111626 ⟨399644, by decide⟩ ⟨13, 2, 0, 399644, 111626, 2673, 16384⟩
    (by decide) selected_cut_15611

theorem selected_cut_15612 : selected 8 ⟨399667, by decide⟩
    (prefixPartial 13 111627) = some ⟨13, 2, 0, 399667, 111627, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_111627_399667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111627 ⟨399667, by decide⟩ :=
  accepted_of_selected 13 111627 ⟨399667, by decide⟩ ⟨13, 2, 0, 399667, 111627, 1225, 16384⟩
    (by decide) selected_cut_15612

theorem unmarked_context_12_27906_399668 : frontier 9 ⟨399668, by decide⟩
    (prefixCache 12 27906) (prefixPartial 12 27906) = false := by
  decide +kernel

theorem node_context_12_27906_399668 : EJMOriginalGlobalDAGData.nodes 9 ⟨399668, by decide⟩ =
    .split (coordinate 12) (![⟨399502, by decide⟩,⟨399594, by decide⟩,⟨399644, by decide⟩,⟨399667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27906_399668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27906 ⟨399668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27906
    ⟨399668, by decide⟩ (by decide) (![⟨399502, by decide⟩,⟨399594, by decide⟩,⟨399644, by decide⟩,⟨399667, by decide⟩]) unmarked_context_12_27906_399668 node_context_12_27906_399668
  intro a
  fin_cases a
  · exact context_13_111624_399502
  · exact context_13_111625_399594
  · exact context_13_111626_399644
  · exact context_13_111627_399667

theorem selected_cut_15613 : selected 9 ⟨389061, by decide⟩
    (prefixPartial 12 27907) = some ⟨12, 1, 0, 389061, 27907, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27907_389061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27907 ⟨389061, by decide⟩ :=
  accepted_of_selected 12 27907 ⟨389061, by decide⟩ ⟨12, 1, 0, 389061, 27907, 1, 65536⟩
    (by decide) selected_cut_15613

theorem unmarked_context_11_6976_399669 : frontier 10 ⟨399669, by decide⟩
    (prefixCache 11 6976) (prefixPartial 11 6976) = false := by
  decide +kernel

theorem node_context_11_6976_399669 : EJMOriginalGlobalDAGData.nodes 10 ⟨399669, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨388829, by decide⟩,⟨399668, by decide⟩,⟨389061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6976_399669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6976 ⟨399669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6976
    ⟨399669, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨388829, by decide⟩,⟨399668, by decide⟩,⟨389061, by decide⟩]) unmarked_context_11_6976_399669 node_context_11_6976_399669
  intro a
  fin_cases a
  · exact context_12_27904_34034
  · exact context_12_27905_388829
  · exact context_12_27906_399668
  · exact context_12_27907_389061

theorem selected_cut_15614 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 27908) = some ⟨12, 1, 0, 34034, 27908, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27908_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27908 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 27908 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 27908, 1, 65536⟩
    (by decide) selected_cut_15614

theorem selected_cut_15615 : selected 7 ⟨399737, by decide⟩
    (prefixPartial 14 446544) = some ⟨14, 2, 0, 399737, 446544, 2105, 4096⟩ := by
  decide +kernel

theorem context_14_446544_399737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446544 ⟨399737, by decide⟩ :=
  accepted_of_selected 14 446544 ⟨399737, by decide⟩ ⟨14, 2, 0, 399737, 446544, 2105, 4096⟩
    (by decide) selected_cut_15615

theorem selected_cut_15616 : selected 7 ⟨399757, by decide⟩
    (prefixPartial 14 446545) = some ⟨14, 2, 0, 399757, 446545, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_446545_399757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446545 ⟨399757, by decide⟩ :=
  accepted_of_selected 14 446545 ⟨399757, by decide⟩ ⟨14, 2, 0, 399757, 446545, 1277, 4096⟩
    (by decide) selected_cut_15616

theorem selected_cut_15617 : selected 7 ⟨399786, by decide⟩
    (prefixPartial 14 446546) = some ⟨14, 2, 0, 399786, 446546, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_446546_399786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446546 ⟨399786, by decide⟩ :=
  accepted_of_selected 14 446546 ⟨399786, by decide⟩ ⟨14, 2, 0, 399786, 446546, 1405, 4096⟩
    (by decide) selected_cut_15617

theorem selected_cut_15618 : selected 7 ⟨399806, by decide⟩
    (prefixPartial 14 446547) = some ⟨14, 2, 0, 399806, 446547, 1393, 4096⟩ := by
  decide +kernel

theorem context_14_446547_399806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446547 ⟨399806, by decide⟩ :=
  accepted_of_selected 14 446547 ⟨399806, by decide⟩ ⟨14, 2, 0, 399806, 446547, 1393, 4096⟩
    (by decide) selected_cut_15618

theorem unmarked_context_13_111636_399807 : frontier 8 ⟨399807, by decide⟩
    (prefixCache 13 111636) (prefixPartial 13 111636) = false := by
  decide +kernel

theorem node_context_13_111636_399807 : EJMOriginalGlobalDAGData.nodes 8 ⟨399807, by decide⟩ =
    .split (coordinate 13) (![⟨399737, by decide⟩,⟨399757, by decide⟩,⟨399786, by decide⟩,⟨399806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111636_399807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111636 ⟨399807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111636
    ⟨399807, by decide⟩ (by decide) (![⟨399737, by decide⟩,⟨399757, by decide⟩,⟨399786, by decide⟩,⟨399806, by decide⟩]) unmarked_context_13_111636_399807 node_context_13_111636_399807
  intro a
  fin_cases a
  · exact context_14_446544_399737
  · exact context_14_446545_399757
  · exact context_14_446546_399786
  · exact context_14_446547_399806

theorem selected_cut_15619 : selected 7 ⟨399850, by decide⟩
    (prefixPartial 14 446548) = some ⟨14, 2, 0, 399850, 446548, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_446548_399850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446548 ⟨399850, by decide⟩ :=
  accepted_of_selected 14 446548 ⟨399850, by decide⟩ ⟨14, 2, 0, 399850, 446548, 1437, 4096⟩
    (by decide) selected_cut_15619

theorem selected_cut_15620 : selected 7 ⟨399874, by decide⟩
    (prefixPartial 14 446549) = some ⟨14, 2, 0, 399874, 446549, 865, 4096⟩ := by
  decide +kernel

theorem context_14_446549_399874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446549 ⟨399874, by decide⟩ :=
  accepted_of_selected 14 446549 ⟨399874, by decide⟩ ⟨14, 2, 0, 399874, 446549, 865, 4096⟩
    (by decide) selected_cut_15620

theorem selected_cut_15621 : selected 7 ⟨399927, by decide⟩
    (prefixPartial 14 446550) = some ⟨14, 2, 0, 399927, 446550, 1885, 4096⟩ := by
  decide +kernel

theorem context_14_446550_399927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446550 ⟨399927, by decide⟩ :=
  accepted_of_selected 14 446550 ⟨399927, by decide⟩ ⟨14, 2, 0, 399927, 446550, 1885, 4096⟩
    (by decide) selected_cut_15621

theorem selected_cut_15622 : selected 7 ⟨399986, by decide⟩
    (prefixPartial 14 446551) = some ⟨14, 2, 0, 399986, 446551, 1425, 4096⟩ := by
  decide +kernel

theorem context_14_446551_399986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446551 ⟨399986, by decide⟩ :=
  accepted_of_selected 14 446551 ⟨399986, by decide⟩ ⟨14, 2, 0, 399986, 446551, 1425, 4096⟩
    (by decide) selected_cut_15622

theorem unmarked_context_13_111637_399987 : frontier 8 ⟨399987, by decide⟩
    (prefixCache 13 111637) (prefixPartial 13 111637) = false := by
  decide +kernel

theorem node_context_13_111637_399987 : EJMOriginalGlobalDAGData.nodes 8 ⟨399987, by decide⟩ =
    .split (coordinate 13) (![⟨399850, by decide⟩,⟨399874, by decide⟩,⟨399927, by decide⟩,⟨399986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111637_399987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111637 ⟨399987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111637
    ⟨399987, by decide⟩ (by decide) (![⟨399850, by decide⟩,⟨399874, by decide⟩,⟨399927, by decide⟩,⟨399986, by decide⟩]) unmarked_context_13_111637_399987 node_context_13_111637_399987
  intro a
  fin_cases a
  · exact context_14_446548_399850
  · exact context_14_446549_399874
  · exact context_14_446550_399927
  · exact context_14_446551_399986

theorem selected_cut_15623 : selected 8 ⟨400103, by decide⟩
    (prefixPartial 13 111638) = some ⟨13, 2, 0, 400103, 111638, 3901, 16384⟩ := by
  decide +kernel

theorem context_13_111638_400103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111638 ⟨400103, by decide⟩ :=
  accepted_of_selected 13 111638 ⟨400103, by decide⟩ ⟨13, 2, 0, 400103, 111638, 3901, 16384⟩
    (by decide) selected_cut_15623

theorem selected_cut_15624 : selected 8 ⟨400162, by decide⟩
    (prefixPartial 13 111639) = some ⟨13, 2, 0, 400162, 111639, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_111639_400162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111639 ⟨400162, by decide⟩ :=
  accepted_of_selected 13 111639 ⟨400162, by decide⟩ ⟨13, 2, 0, 400162, 111639, 1445, 16384⟩
    (by decide) selected_cut_15624

theorem unmarked_context_12_27909_400163 : frontier 9 ⟨400163, by decide⟩
    (prefixCache 12 27909) (prefixPartial 12 27909) = false := by
  decide +kernel

theorem node_context_12_27909_400163 : EJMOriginalGlobalDAGData.nodes 9 ⟨400163, by decide⟩ =
    .split (coordinate 12) (![⟨399807, by decide⟩,⟨399987, by decide⟩,⟨400103, by decide⟩,⟨400162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27909_400163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27909 ⟨400163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27909
    ⟨400163, by decide⟩ (by decide) (![⟨399807, by decide⟩,⟨399987, by decide⟩,⟨400103, by decide⟩,⟨400162, by decide⟩]) unmarked_context_12_27909_400163 node_context_12_27909_400163
  intro a
  fin_cases a
  · exact context_13_111636_399807
  · exact context_13_111637_399987
  · exact context_13_111638_400103
  · exact context_13_111639_400162

theorem selected_cut_15625 : selected 7 ⟨400185, by decide⟩
    (prefixPartial 14 446560) = some ⟨14, 2, 0, 400185, 446560, 957, 4096⟩ := by
  decide +kernel

theorem context_14_446560_400185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446560 ⟨400185, by decide⟩ :=
  accepted_of_selected 14 446560 ⟨400185, by decide⟩ ⟨14, 2, 0, 400185, 446560, 957, 4096⟩
    (by decide) selected_cut_15625

theorem selected_cut_15626 : selected 7 ⟨400202, by decide⟩
    (prefixPartial 14 446561) = some ⟨14, 2, 0, 400202, 446561, 1025, 4096⟩ := by
  decide +kernel

theorem context_14_446561_400202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446561 ⟨400202, by decide⟩ :=
  accepted_of_selected 14 446561 ⟨400202, by decide⟩ ⟨14, 2, 0, 400202, 446561, 1025, 4096⟩
    (by decide) selected_cut_15626

theorem selected_cut_15627 : selected 7 ⟨400221, by decide⟩
    (prefixPartial 14 446562) = some ⟨14, 2, 0, 400221, 446562, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_446562_400221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446562 ⟨400221, by decide⟩ :=
  accepted_of_selected 14 446562 ⟨400221, by decide⟩ ⟨14, 2, 0, 400221, 446562, 1137, 4096⟩
    (by decide) selected_cut_15627

theorem selected_cut_15628 : selected 7 ⟨400241, by decide⟩
    (prefixPartial 14 446563) = some ⟨14, 2, 0, 400241, 446563, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_446563_400241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446563 ⟨400241, by decide⟩ :=
  accepted_of_selected 14 446563 ⟨400241, by decide⟩ ⟨14, 2, 0, 400241, 446563, 1185, 4096⟩
    (by decide) selected_cut_15628

theorem unmarked_context_13_111640_400242 : frontier 8 ⟨400242, by decide⟩
    (prefixCache 13 111640) (prefixPartial 13 111640) = false := by
  decide +kernel

theorem node_context_13_111640_400242 : EJMOriginalGlobalDAGData.nodes 8 ⟨400242, by decide⟩ =
    .split (coordinate 13) (![⟨400185, by decide⟩,⟨400202, by decide⟩,⟨400221, by decide⟩,⟨400241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111640_400242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111640 ⟨400242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111640
    ⟨400242, by decide⟩ (by decide) (![⟨400185, by decide⟩,⟨400202, by decide⟩,⟨400221, by decide⟩,⟨400241, by decide⟩]) unmarked_context_13_111640_400242 node_context_13_111640_400242
  intro a
  fin_cases a
  · exact context_14_446560_400185
  · exact context_14_446561_400202
  · exact context_14_446562_400221
  · exact context_14_446563_400241

theorem selected_cut_15629 : selected 8 ⟨400304, by decide⟩
    (prefixPartial 13 111641) = some ⟨13, 2, 0, 400304, 111641, 3517, 16384⟩ := by
  decide +kernel

theorem context_13_111641_400304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111641 ⟨400304, by decide⟩ :=
  accepted_of_selected 13 111641 ⟨400304, by decide⟩ ⟨13, 2, 0, 400304, 111641, 3517, 16384⟩
    (by decide) selected_cut_15629

theorem selected_cut_15630 : selected 8 ⟨400344, by decide⟩
    (prefixPartial 13 111642) = some ⟨13, 2, 0, 400344, 111642, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_111642_400344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111642 ⟨400344, by decide⟩ :=
  accepted_of_selected 13 111642 ⟨400344, by decide⟩ ⟨13, 2, 0, 400344, 111642, 2517, 16384⟩
    (by decide) selected_cut_15630

theorem selected_cut_15631 : selected 8 ⟨400357, by decide⟩
    (prefixPartial 13 111643) = some ⟨13, 2, 0, 400357, 111643, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_111643_400357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111643 ⟨400357, by decide⟩ :=
  accepted_of_selected 13 111643 ⟨400357, by decide⟩ ⟨13, 2, 0, 400357, 111643, 1157, 16384⟩
    (by decide) selected_cut_15631

theorem unmarked_context_12_27910_400358 : frontier 9 ⟨400358, by decide⟩
    (prefixCache 12 27910) (prefixPartial 12 27910) = false := by
  decide +kernel

theorem node_context_12_27910_400358 : EJMOriginalGlobalDAGData.nodes 9 ⟨400358, by decide⟩ =
    .split (coordinate 12) (![⟨400242, by decide⟩,⟨400304, by decide⟩,⟨400344, by decide⟩,⟨400357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27910_400358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27910 ⟨400358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27910
    ⟨400358, by decide⟩ (by decide) (![⟨400242, by decide⟩,⟨400304, by decide⟩,⟨400344, by decide⟩,⟨400357, by decide⟩]) unmarked_context_12_27910_400358 node_context_12_27910_400358
  intro a
  fin_cases a
  · exact context_13_111640_400242
  · exact context_13_111641_400304
  · exact context_13_111642_400344
  · exact context_13_111643_400357

theorem selected_cut_15632 : selected 7 ⟨400379, by decide⟩
    (prefixPartial 14 446576) = some ⟨14, 2, 0, 400379, 446576, 969, 4096⟩ := by
  decide +kernel

theorem context_14_446576_400379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446576 ⟨400379, by decide⟩ :=
  accepted_of_selected 14 446576 ⟨400379, by decide⟩ ⟨14, 2, 0, 400379, 446576, 969, 4096⟩
    (by decide) selected_cut_15632

theorem selected_cut_15633 : selected 7 ⟨400393, by decide⟩
    (prefixPartial 14 446577) = some ⟨14, 2, 0, 400393, 446577, 1157, 4096⟩ := by
  decide +kernel

theorem context_14_446577_400393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446577 ⟨400393, by decide⟩ :=
  accepted_of_selected 14 446577 ⟨400393, by decide⟩ ⟨14, 2, 0, 400393, 446577, 1157, 4096⟩
    (by decide) selected_cut_15633

theorem selected_cut_15634 : selected 7 ⟨400410, by decide⟩
    (prefixPartial 14 446578) = some ⟨14, 2, 0, 400410, 446578, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_446578_400410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446578 ⟨400410, by decide⟩ :=
  accepted_of_selected 14 446578 ⟨400410, by decide⟩ ⟨14, 2, 0, 400410, 446578, 1189, 4096⟩
    (by decide) selected_cut_15634

theorem selected_cut_15635 : selected 7 ⟨400423, by decide⟩
    (prefixPartial 14 446579) = some ⟨14, 2, 0, 400423, 446579, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_446579_400423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446579 ⟨400423, by decide⟩ :=
  accepted_of_selected 14 446579 ⟨400423, by decide⟩ ⟨14, 2, 0, 400423, 446579, 1153, 4096⟩
    (by decide) selected_cut_15635

theorem unmarked_context_13_111644_400424 : frontier 8 ⟨400424, by decide⟩
    (prefixCache 13 111644) (prefixPartial 13 111644) = false := by
  decide +kernel

theorem node_context_13_111644_400424 : EJMOriginalGlobalDAGData.nodes 8 ⟨400424, by decide⟩ =
    .split (coordinate 13) (![⟨400379, by decide⟩,⟨400393, by decide⟩,⟨400410, by decide⟩,⟨400423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111644_400424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111644 ⟨400424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111644
    ⟨400424, by decide⟩ (by decide) (![⟨400379, by decide⟩,⟨400393, by decide⟩,⟨400410, by decide⟩,⟨400423, by decide⟩]) unmarked_context_13_111644_400424 node_context_13_111644_400424
  intro a
  fin_cases a
  · exact context_14_446576_400379
  · exact context_14_446577_400393
  · exact context_14_446578_400410
  · exact context_14_446579_400423

theorem selected_cut_15636 : selected 8 ⟨400496, by decide⟩
    (prefixPartial 13 111645) = some ⟨13, 2, 0, 400496, 111645, 3777, 16384⟩ := by
  decide +kernel

theorem context_13_111645_400496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111645 ⟨400496, by decide⟩ :=
  accepted_of_selected 13 111645 ⟨400496, by decide⟩ ⟨13, 2, 0, 400496, 111645, 3777, 16384⟩
    (by decide) selected_cut_15636

theorem selected_cut_15637 : selected 8 ⟨400546, by decide⟩
    (prefixPartial 13 111646) = some ⟨13, 2, 0, 400546, 111646, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_111646_400546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111646 ⟨400546, by decide⟩ :=
  accepted_of_selected 13 111646 ⟨400546, by decide⟩ ⟨13, 2, 0, 400546, 111646, 2829, 16384⟩
    (by decide) selected_cut_15637

theorem selected_cut_15638 : selected 8 ⟨400557, by decide⟩
    (prefixPartial 13 111647) = some ⟨13, 2, 0, 400557, 111647, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_111647_400557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111647 ⟨400557, by decide⟩ :=
  accepted_of_selected 13 111647 ⟨400557, by decide⟩ ⟨13, 2, 0, 400557, 111647, 1185, 16384⟩
    (by decide) selected_cut_15638

theorem unmarked_context_12_27911_400558 : frontier 9 ⟨400558, by decide⟩
    (prefixCache 12 27911) (prefixPartial 12 27911) = false := by
  decide +kernel

theorem node_context_12_27911_400558 : EJMOriginalGlobalDAGData.nodes 9 ⟨400558, by decide⟩ =
    .split (coordinate 12) (![⟨400424, by decide⟩,⟨400496, by decide⟩,⟨400546, by decide⟩,⟨400557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27911_400558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27911 ⟨400558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27911
    ⟨400558, by decide⟩ (by decide) (![⟨400424, by decide⟩,⟨400496, by decide⟩,⟨400546, by decide⟩,⟨400557, by decide⟩]) unmarked_context_12_27911_400558 node_context_12_27911_400558
  intro a
  fin_cases a
  · exact context_13_111644_400424
  · exact context_13_111645_400496
  · exact context_13_111646_400546
  · exact context_13_111647_400557

theorem unmarked_context_11_6977_400559 : frontier 10 ⟨400559, by decide⟩
    (prefixCache 11 6977) (prefixPartial 11 6977) = false := by
  decide +kernel

theorem node_context_11_6977_400559 : EJMOriginalGlobalDAGData.nodes 10 ⟨400559, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨400163, by decide⟩,⟨400358, by decide⟩,⟨400558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6977_400559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6977 ⟨400559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6977
    ⟨400559, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨400163, by decide⟩,⟨400358, by decide⟩,⟨400558, by decide⟩]) unmarked_context_11_6977_400559 node_context_11_6977_400559
  intro a
  fin_cases a
  · exact context_12_27908_34034
  · exact context_12_27909_400163
  · exact context_12_27910_400358
  · exact context_12_27911_400558

theorem selected_cut_15639 : selected 8 ⟨400623, by decide⟩
    (prefixPartial 13 111648) = some ⟨13, 2, 0, 400623, 111648, 3441, 16384⟩ := by
  decide +kernel

theorem context_13_111648_400623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111648 ⟨400623, by decide⟩ :=
  accepted_of_selected 13 111648 ⟨400623, by decide⟩ ⟨13, 2, 0, 400623, 111648, 3441, 16384⟩
    (by decide) selected_cut_15639

theorem selected_cut_15640 : selected 7 ⟨400649, by decide⟩
    (prefixPartial 14 446596) = some ⟨14, 2, 0, 400649, 446596, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_446596_400649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446596 ⟨400649, by decide⟩ :=
  accepted_of_selected 14 446596 ⟨400649, by decide⟩ ⟨14, 2, 0, 400649, 446596, 1221, 4096⟩
    (by decide) selected_cut_15640

theorem selected_cut_15641 : selected 7 ⟨400656, by decide⟩
    (prefixPartial 14 446597) = some ⟨14, 2, 0, 400656, 446597, 557, 4096⟩ := by
  decide +kernel

theorem context_14_446597_400656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446597 ⟨400656, by decide⟩ :=
  accepted_of_selected 14 446597 ⟨400656, by decide⟩ ⟨14, 2, 0, 400656, 446597, 557, 4096⟩
    (by decide) selected_cut_15641

theorem selected_cut_15642 : selected 7 ⟨400681, by decide⟩
    (prefixPartial 14 446598) = some ⟨14, 2, 0, 400681, 446598, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_446598_400681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446598 ⟨400681, by decide⟩ :=
  accepted_of_selected 14 446598 ⟨400681, by decide⟩ ⟨14, 2, 0, 400681, 446598, 1341, 4096⟩
    (by decide) selected_cut_15642

theorem selected_cut_15643 : selected 7 ⟨400703, by decide⟩
    (prefixPartial 14 446599) = some ⟨14, 2, 0, 400703, 446599, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_446599_400703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 446599 ⟨400703, by decide⟩ :=
  accepted_of_selected 14 446599 ⟨400703, by decide⟩ ⟨14, 2, 0, 400703, 446599, 1049, 4096⟩
    (by decide) selected_cut_15643

theorem unmarked_context_13_111649_400704 : frontier 8 ⟨400704, by decide⟩
    (prefixCache 13 111649) (prefixPartial 13 111649) = false := by
  decide +kernel

theorem node_context_13_111649_400704 : EJMOriginalGlobalDAGData.nodes 8 ⟨400704, by decide⟩ =
    .split (coordinate 13) (![⟨400649, by decide⟩,⟨400656, by decide⟩,⟨400681, by decide⟩,⟨400703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_111649_400704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111649 ⟨400704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 111649
    ⟨400704, by decide⟩ (by decide) (![⟨400649, by decide⟩,⟨400656, by decide⟩,⟨400681, by decide⟩,⟨400703, by decide⟩]) unmarked_context_13_111649_400704 node_context_13_111649_400704
  intro a
  fin_cases a
  · exact context_14_446596_400649
  · exact context_14_446597_400656
  · exact context_14_446598_400681
  · exact context_14_446599_400703

theorem selected_cut_15644 : selected 8 ⟨400746, by decide⟩
    (prefixPartial 13 111650) = some ⟨13, 2, 0, 400746, 111650, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_111650_400746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111650 ⟨400746, by decide⟩ :=
  accepted_of_selected 13 111650 ⟨400746, by decide⟩ ⟨13, 2, 0, 400746, 111650, 2593, 16384⟩
    (by decide) selected_cut_15644

theorem selected_cut_15645 : selected 8 ⟨400754, by decide⟩
    (prefixPartial 13 111651) = some ⟨13, 2, 0, 400754, 111651, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_111651_400754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111651 ⟨400754, by decide⟩ :=
  accepted_of_selected 13 111651 ⟨400754, by decide⟩ ⟨13, 2, 0, 400754, 111651, 1121, 16384⟩
    (by decide) selected_cut_15645

theorem unmarked_context_12_27912_400755 : frontier 9 ⟨400755, by decide⟩
    (prefixCache 12 27912) (prefixPartial 12 27912) = false := by
  decide +kernel

theorem node_context_12_27912_400755 : EJMOriginalGlobalDAGData.nodes 9 ⟨400755, by decide⟩ =
    .split (coordinate 12) (![⟨400623, by decide⟩,⟨400704, by decide⟩,⟨400746, by decide⟩,⟨400754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27912_400755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27912 ⟨400755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27912
    ⟨400755, by decide⟩ (by decide) (![⟨400623, by decide⟩,⟨400704, by decide⟩,⟨400746, by decide⟩,⟨400754, by decide⟩]) unmarked_context_12_27912_400755 node_context_12_27912_400755
  intro a
  fin_cases a
  · exact context_13_111648_400623
  · exact context_13_111649_400704
  · exact context_13_111650_400746
  · exact context_13_111651_400754

theorem selected_cut_15646 : selected 8 ⟨400806, by decide⟩
    (prefixPartial 13 111652) = some ⟨13, 2, 0, 400806, 111652, 3401, 16384⟩ := by
  decide +kernel

theorem context_13_111652_400806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111652 ⟨400806, by decide⟩ :=
  accepted_of_selected 13 111652 ⟨400806, by decide⟩ ⟨13, 2, 0, 400806, 111652, 3401, 16384⟩
    (by decide) selected_cut_15646

theorem selected_cut_15647 : selected 8 ⟨400855, by decide⟩
    (prefixPartial 13 111653) = some ⟨13, 2, 0, 400855, 111653, 3401, 16384⟩ := by
  decide +kernel

theorem context_13_111653_400855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111653 ⟨400855, by decide⟩ :=
  accepted_of_selected 13 111653 ⟨400855, by decide⟩ ⟨13, 2, 0, 400855, 111653, 3401, 16384⟩
    (by decide) selected_cut_15647

theorem selected_cut_15648 : selected 8 ⟨400888, by decide⟩
    (prefixPartial 13 111654) = some ⟨13, 2, 0, 400888, 111654, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_111654_400888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111654 ⟨400888, by decide⟩ :=
  accepted_of_selected 13 111654 ⟨400888, by decide⟩ ⟨13, 2, 0, 400888, 111654, 2525, 16384⟩
    (by decide) selected_cut_15648

theorem selected_cut_15649 : selected 8 ⟨400905, by decide⟩
    (prefixPartial 13 111655) = some ⟨13, 2, 0, 400905, 111655, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_111655_400905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111655 ⟨400905, by decide⟩ :=
  accepted_of_selected 13 111655 ⟨400905, by decide⟩ ⟨13, 2, 0, 400905, 111655, 1177, 16384⟩
    (by decide) selected_cut_15649

theorem unmarked_context_12_27913_400906 : frontier 9 ⟨400906, by decide⟩
    (prefixCache 12 27913) (prefixPartial 12 27913) = false := by
  decide +kernel

theorem node_context_12_27913_400906 : EJMOriginalGlobalDAGData.nodes 9 ⟨400906, by decide⟩ =
    .split (coordinate 12) (![⟨400806, by decide⟩,⟨400855, by decide⟩,⟨400888, by decide⟩,⟨400905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27913_400906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27913 ⟨400906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27913
    ⟨400906, by decide⟩ (by decide) (![⟨400806, by decide⟩,⟨400855, by decide⟩,⟨400888, by decide⟩,⟨400905, by decide⟩]) unmarked_context_12_27913_400906 node_context_12_27913_400906
  intro a
  fin_cases a
  · exact context_13_111652_400806
  · exact context_13_111653_400855
  · exact context_13_111654_400888
  · exact context_13_111655_400905

theorem selected_cut_15650 : selected 8 ⟨400983, by decide⟩
    (prefixPartial 13 111656) = some ⟨13, 2, 0, 400983, 111656, 3949, 16384⟩ := by
  decide +kernel

theorem context_13_111656_400983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111656 ⟨400983, by decide⟩ :=
  accepted_of_selected 13 111656 ⟨400983, by decide⟩ ⟨13, 2, 0, 400983, 111656, 3949, 16384⟩
    (by decide) selected_cut_15650

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
