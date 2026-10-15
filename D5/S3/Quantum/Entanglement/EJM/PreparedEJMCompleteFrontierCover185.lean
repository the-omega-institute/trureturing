/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover184
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17763 : selected 9 ⟨452466, by decide⟩
    (prefixPartial 12 70767) = some ⟨12, 2, 0, 452466, 70767, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_70767_452466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70767 ⟨452466, by decide⟩ :=
  accepted_of_selected 12 70767 ⟨452466, by decide⟩ ⟨12, 2, 0, 452466, 70767, 2821, 65536⟩
    (by decide) selected_cut_17763

theorem unmarked_context_11_17691_452467 : frontier 10 ⟨452467, by decide⟩
    (prefixCache 11 17691) (prefixPartial 11 17691) = false := by
  decide +kernel

theorem node_context_11_17691_452467 : EJMOriginalGlobalDAGData.nodes 10 ⟨452467, by decide⟩ =
    .split (coordinate 11) (![⟨452349, by decide⟩,⟨452388, by decide⟩,⟨452429, by decide⟩,⟨452466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17691_452467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17691 ⟨452467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17691
    ⟨452467, by decide⟩ (by decide) (![⟨452349, by decide⟩,⟨452388, by decide⟩,⟨452429, by decide⟩,⟨452466, by decide⟩]) unmarked_context_11_17691_452467 node_context_11_17691_452467
  intro a
  fin_cases a
  · exact context_12_70764_452349
  · exact context_12_70765_452388
  · exact context_12_70766_452429
  · exact context_12_70767_452466

theorem unmarked_context_10_4422_452468 : frontier 11 ⟨452468, by decide⟩
    (prefixCache 10 4422) (prefixPartial 10 4422) = false := by
  decide +kernel

theorem node_context_10_4422_452468 : EJMOriginalGlobalDAGData.nodes 11 ⟨452468, by decide⟩ =
    .split (coordinate 10) (![⟨451963, by decide⟩,⟨452151, by decide⟩,⟨452313, by decide⟩,⟨452467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4422_452468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4422 ⟨452468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4422
    ⟨452468, by decide⟩ (by decide) (![⟨451963, by decide⟩,⟨452151, by decide⟩,⟨452313, by decide⟩,⟨452467, by decide⟩]) unmarked_context_10_4422_452468 node_context_10_4422_452468
  intro a
  fin_cases a
  · exact context_11_17688_451963
  · exact context_11_17689_452151
  · exact context_11_17690_452313
  · exact context_11_17691_452467

theorem selected_cut_17764 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4423) = some ⟨10, 1, 0, 3440, 4423, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4423_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4423 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4423 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4423, 1, 1048576⟩
    (by decide) selected_cut_17764

theorem unmarked_context_9_1105_452469 : frontier 12 ⟨452469, by decide⟩
    (prefixCache 9 1105) (prefixPartial 9 1105) = false := by
  decide +kernel

theorem node_context_9_1105_452469 : EJMOriginalGlobalDAGData.nodes 12 ⟨452469, by decide⟩ =
    .split (coordinate 9) (![⟨451412, by decide⟩,⟨451716, by decide⟩,⟨452468, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1105_452469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1105 ⟨452469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1105
    ⟨452469, by decide⟩ (by decide) (![⟨451412, by decide⟩,⟨451716, by decide⟩,⟨452468, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1105_452469 node_context_9_1105_452469
  intro a
  fin_cases a
  · exact context_10_4420_451412
  · exact context_10_4421_451716
  · exact context_10_4422_452468
  · exact context_10_4423_3440

theorem selected_cut_17765 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 70784) = some ⟨12, 1, 0, 450982, 70784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70784_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70784 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 70784 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 70784, 1, 65536⟩
    (by decide) selected_cut_17765

theorem selected_cut_17766 : selected 9 ⟨452492, by decide⟩
    (prefixPartial 12 70785) = some ⟨12, 2, 0, 452492, 70785, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_70785_452492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70785 ⟨452492, by decide⟩ :=
  accepted_of_selected 12 70785 ⟨452492, by decide⟩ ⟨12, 2, 0, 452492, 70785, 1877, 65536⟩
    (by decide) selected_cut_17766

theorem selected_cut_17767 : selected 9 ⟨452510, by decide⟩
    (prefixPartial 12 70786) = some ⟨12, 2, 0, 452510, 70786, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_70786_452510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70786 ⟨452510, by decide⟩ :=
  accepted_of_selected 12 70786 ⟨452510, by decide⟩ ⟨12, 2, 0, 452510, 70786, 1837, 65536⟩
    (by decide) selected_cut_17767

theorem selected_cut_17768 : selected 9 ⟨452535, by decide⟩
    (prefixPartial 12 70787) = some ⟨12, 2, 0, 452535, 70787, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_70787_452535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70787 ⟨452535, by decide⟩ :=
  accepted_of_selected 12 70787 ⟨452535, by decide⟩ ⟨12, 2, 0, 452535, 70787, 1917, 65536⟩
    (by decide) selected_cut_17768

theorem unmarked_context_11_17696_452536 : frontier 10 ⟨452536, by decide⟩
    (prefixCache 11 17696) (prefixPartial 11 17696) = false := by
  decide +kernel

theorem node_context_11_17696_452536 : EJMOriginalGlobalDAGData.nodes 10 ⟨452536, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨452492, by decide⟩,⟨452510, by decide⟩,⟨452535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17696_452536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17696 ⟨452536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17696
    ⟨452536, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨452492, by decide⟩,⟨452510, by decide⟩,⟨452535, by decide⟩]) unmarked_context_11_17696_452536 node_context_11_17696_452536
  intro a
  fin_cases a
  · exact context_12_70784_450982
  · exact context_12_70785_452492
  · exact context_12_70786_452510
  · exact context_12_70787_452535

theorem selected_cut_17769 : selected 9 ⟨452557, by decide⟩
    (prefixPartial 12 70788) = some ⟨12, 2, 0, 452557, 70788, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_70788_452557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70788 ⟨452557, by decide⟩ :=
  accepted_of_selected 12 70788 ⟨452557, by decide⟩ ⟨12, 2, 0, 452557, 70788, 1769, 65536⟩
    (by decide) selected_cut_17769

theorem selected_cut_17770 : selected 9 ⟨452578, by decide⟩
    (prefixPartial 12 70789) = some ⟨12, 2, 0, 452578, 70789, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_70789_452578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70789 ⟨452578, by decide⟩ :=
  accepted_of_selected 12 70789 ⟨452578, by decide⟩ ⟨12, 2, 0, 452578, 70789, 1697, 65536⟩
    (by decide) selected_cut_17770

theorem selected_cut_17771 : selected 9 ⟨452601, by decide⟩
    (prefixPartial 12 70790) = some ⟨12, 2, 0, 452601, 70790, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_70790_452601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70790 ⟨452601, by decide⟩ :=
  accepted_of_selected 12 70790 ⟨452601, by decide⟩ ⟨12, 2, 0, 452601, 70790, 1849, 65536⟩
    (by decide) selected_cut_17771

theorem selected_cut_17772 : selected 9 ⟨452628, by decide⟩
    (prefixPartial 12 70791) = some ⟨12, 2, 0, 452628, 70791, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_70791_452628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70791 ⟨452628, by decide⟩ :=
  accepted_of_selected 12 70791 ⟨452628, by decide⟩ ⟨12, 2, 0, 452628, 70791, 1873, 65536⟩
    (by decide) selected_cut_17772

theorem unmarked_context_11_17697_452629 : frontier 10 ⟨452629, by decide⟩
    (prefixCache 11 17697) (prefixPartial 11 17697) = false := by
  decide +kernel

theorem node_context_11_17697_452629 : EJMOriginalGlobalDAGData.nodes 10 ⟨452629, by decide⟩ =
    .split (coordinate 11) (![⟨452557, by decide⟩,⟨452578, by decide⟩,⟨452601, by decide⟩,⟨452628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17697_452629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17697 ⟨452629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17697
    ⟨452629, by decide⟩ (by decide) (![⟨452557, by decide⟩,⟨452578, by decide⟩,⟨452601, by decide⟩,⟨452628, by decide⟩]) unmarked_context_11_17697_452629 node_context_11_17697_452629
  intro a
  fin_cases a
  · exact context_12_70788_452557
  · exact context_12_70789_452578
  · exact context_12_70790_452601
  · exact context_12_70791_452628

theorem selected_cut_17773 : selected 9 ⟨452651, by decide⟩
    (prefixPartial 12 70792) = some ⟨12, 2, 0, 452651, 70792, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_70792_452651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70792 ⟨452651, by decide⟩ :=
  accepted_of_selected 12 70792 ⟨452651, by decide⟩ ⟨12, 2, 0, 452651, 70792, 1813, 65536⟩
    (by decide) selected_cut_17773

theorem selected_cut_17774 : selected 9 ⟨452674, by decide⟩
    (prefixPartial 12 70793) = some ⟨12, 2, 0, 452674, 70793, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_70793_452674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70793 ⟨452674, by decide⟩ :=
  accepted_of_selected 12 70793 ⟨452674, by decide⟩ ⟨12, 2, 0, 452674, 70793, 1941, 65536⟩
    (by decide) selected_cut_17774

theorem selected_cut_17775 : selected 9 ⟨452694, by decide⟩
    (prefixPartial 12 70794) = some ⟨12, 2, 0, 452694, 70794, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_70794_452694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70794 ⟨452694, by decide⟩ :=
  accepted_of_selected 12 70794 ⟨452694, by decide⟩ ⟨12, 2, 0, 452694, 70794, 1785, 65536⟩
    (by decide) selected_cut_17775

theorem selected_cut_17776 : selected 9 ⟨452720, by decide⟩
    (prefixPartial 12 70795) = some ⟨12, 2, 0, 452720, 70795, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_70795_452720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70795 ⟨452720, by decide⟩ :=
  accepted_of_selected 12 70795 ⟨452720, by decide⟩ ⟨12, 2, 0, 452720, 70795, 1913, 65536⟩
    (by decide) selected_cut_17776

theorem unmarked_context_11_17698_452721 : frontier 10 ⟨452721, by decide⟩
    (prefixCache 11 17698) (prefixPartial 11 17698) = false := by
  decide +kernel

theorem node_context_11_17698_452721 : EJMOriginalGlobalDAGData.nodes 10 ⟨452721, by decide⟩ =
    .split (coordinate 11) (![⟨452651, by decide⟩,⟨452674, by decide⟩,⟨452694, by decide⟩,⟨452720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17698_452721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17698 ⟨452721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17698
    ⟨452721, by decide⟩ (by decide) (![⟨452651, by decide⟩,⟨452674, by decide⟩,⟨452694, by decide⟩,⟨452720, by decide⟩]) unmarked_context_11_17698_452721 node_context_11_17698_452721
  intro a
  fin_cases a
  · exact context_12_70792_452651
  · exact context_12_70793_452674
  · exact context_12_70794_452694
  · exact context_12_70795_452720

theorem selected_cut_17777 : selected 9 ⟨452738, by decide⟩
    (prefixPartial 12 70796) = some ⟨12, 2, 0, 452738, 70796, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_70796_452738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70796 ⟨452738, by decide⟩ :=
  accepted_of_selected 12 70796 ⟨452738, by decide⟩ ⟨12, 2, 0, 452738, 70796, 1585, 65536⟩
    (by decide) selected_cut_17777

theorem selected_cut_17778 : selected 9 ⟨452756, by decide⟩
    (prefixPartial 12 70797) = some ⟨12, 2, 0, 452756, 70797, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_70797_452756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70797 ⟨452756, by decide⟩ :=
  accepted_of_selected 12 70797 ⟨452756, by decide⟩ ⟨12, 2, 0, 452756, 70797, 1669, 65536⟩
    (by decide) selected_cut_17778

theorem selected_cut_17779 : selected 9 ⟨452771, by decide⟩
    (prefixPartial 12 70798) = some ⟨12, 2, 0, 452771, 70798, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_70798_452771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70798 ⟨452771, by decide⟩ :=
  accepted_of_selected 12 70798 ⟨452771, by decide⟩ ⟨12, 2, 0, 452771, 70798, 1669, 65536⟩
    (by decide) selected_cut_17779

theorem selected_cut_17780 : selected 9 ⟨452787, by decide⟩
    (prefixPartial 12 70799) = some ⟨12, 2, 0, 452787, 70799, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_70799_452787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70799 ⟨452787, by decide⟩ :=
  accepted_of_selected 12 70799 ⟨452787, by decide⟩ ⟨12, 2, 0, 452787, 70799, 1641, 65536⟩
    (by decide) selected_cut_17780

theorem unmarked_context_11_17699_452788 : frontier 10 ⟨452788, by decide⟩
    (prefixCache 11 17699) (prefixPartial 11 17699) = false := by
  decide +kernel

theorem node_context_11_17699_452788 : EJMOriginalGlobalDAGData.nodes 10 ⟨452788, by decide⟩ =
    .split (coordinate 11) (![⟨452738, by decide⟩,⟨452756, by decide⟩,⟨452771, by decide⟩,⟨452787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17699_452788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17699 ⟨452788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17699
    ⟨452788, by decide⟩ (by decide) (![⟨452738, by decide⟩,⟨452756, by decide⟩,⟨452771, by decide⟩,⟨452787, by decide⟩]) unmarked_context_11_17699_452788 node_context_11_17699_452788
  intro a
  fin_cases a
  · exact context_12_70796_452738
  · exact context_12_70797_452756
  · exact context_12_70798_452771
  · exact context_12_70799_452787

theorem unmarked_context_10_4424_452789 : frontier 11 ⟨452789, by decide⟩
    (prefixCache 10 4424) (prefixPartial 10 4424) = false := by
  decide +kernel

theorem node_context_10_4424_452789 : EJMOriginalGlobalDAGData.nodes 11 ⟨452789, by decide⟩ =
    .split (coordinate 10) (![⟨452536, by decide⟩,⟨452629, by decide⟩,⟨452721, by decide⟩,⟨452788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4424_452789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4424 ⟨452789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4424
    ⟨452789, by decide⟩ (by decide) (![⟨452536, by decide⟩,⟨452629, by decide⟩,⟨452721, by decide⟩,⟨452788, by decide⟩]) unmarked_context_10_4424_452789 node_context_10_4424_452789
  intro a
  fin_cases a
  · exact context_11_17696_452536
  · exact context_11_17697_452629
  · exact context_11_17698_452721
  · exact context_11_17699_452788

theorem selected_cut_17781 : selected 9 ⟨452825, by decide⟩
    (prefixPartial 12 70800) = some ⟨12, 2, 0, 452825, 70800, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_70800_452825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70800 ⟨452825, by decide⟩ :=
  accepted_of_selected 12 70800 ⟨452825, by decide⟩ ⟨12, 2, 0, 452825, 70800, 2373, 65536⟩
    (by decide) selected_cut_17781

theorem selected_cut_17782 : selected 9 ⟨452854, by decide⟩
    (prefixPartial 12 70801) = some ⟨12, 2, 0, 452854, 70801, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_70801_452854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70801 ⟨452854, by decide⟩ :=
  accepted_of_selected 12 70801 ⟨452854, by decide⟩ ⟨12, 2, 0, 452854, 70801, 1513, 65536⟩
    (by decide) selected_cut_17782

theorem selected_cut_17783 : selected 9 ⟨452877, by decide⟩
    (prefixPartial 12 70802) = some ⟨12, 2, 0, 452877, 70802, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_70802_452877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70802 ⟨452877, by decide⟩ :=
  accepted_of_selected 12 70802 ⟨452877, by decide⟩ ⟨12, 2, 0, 452877, 70802, 1705, 65536⟩
    (by decide) selected_cut_17783

theorem selected_cut_17784 : selected 9 ⟨452897, by decide⟩
    (prefixPartial 12 70803) = some ⟨12, 2, 0, 452897, 70803, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_70803_452897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70803 ⟨452897, by decide⟩ :=
  accepted_of_selected 12 70803 ⟨452897, by decide⟩ ⟨12, 2, 0, 452897, 70803, 1745, 65536⟩
    (by decide) selected_cut_17784

theorem unmarked_context_11_17700_452898 : frontier 10 ⟨452898, by decide⟩
    (prefixCache 11 17700) (prefixPartial 11 17700) = false := by
  decide +kernel

theorem node_context_11_17700_452898 : EJMOriginalGlobalDAGData.nodes 10 ⟨452898, by decide⟩ =
    .split (coordinate 11) (![⟨452825, by decide⟩,⟨452854, by decide⟩,⟨452877, by decide⟩,⟨452897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17700_452898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17700 ⟨452898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17700
    ⟨452898, by decide⟩ (by decide) (![⟨452825, by decide⟩,⟨452854, by decide⟩,⟨452877, by decide⟩,⟨452897, by decide⟩]) unmarked_context_11_17700_452898 node_context_11_17700_452898
  intro a
  fin_cases a
  · exact context_12_70800_452825
  · exact context_12_70801_452854
  · exact context_12_70802_452877
  · exact context_12_70803_452897

theorem selected_cut_17785 : selected 9 ⟨452935, by decide⟩
    (prefixPartial 12 70804) = some ⟨12, 2, 0, 452935, 70804, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_70804_452935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70804 ⟨452935, by decide⟩ :=
  accepted_of_selected 12 70804 ⟨452935, by decide⟩ ⟨12, 2, 0, 452935, 70804, 2117, 65536⟩
    (by decide) selected_cut_17785

theorem selected_cut_17786 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 70805) = some ⟨12, 1, 0, 449506, 70805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70805_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70805 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 70805 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 70805, 1, 65536⟩
    (by decide) selected_cut_17786

theorem selected_cut_17787 : selected 9 ⟨452980, by decide⟩
    (prefixPartial 12 70806) = some ⟨12, 2, 0, 452980, 70806, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_70806_452980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70806 ⟨452980, by decide⟩ :=
  accepted_of_selected 12 70806 ⟨452980, by decide⟩ ⟨12, 2, 0, 452980, 70806, 2221, 65536⟩
    (by decide) selected_cut_17787

theorem selected_cut_17788 : selected 9 ⟨453014, by decide⟩
    (prefixPartial 12 70807) = some ⟨12, 2, 0, 453014, 70807, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_70807_453014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70807 ⟨453014, by decide⟩ :=
  accepted_of_selected 12 70807 ⟨453014, by decide⟩ ⟨12, 2, 0, 453014, 70807, 2161, 65536⟩
    (by decide) selected_cut_17788

theorem unmarked_context_11_17701_453015 : frontier 10 ⟨453015, by decide⟩
    (prefixCache 11 17701) (prefixPartial 11 17701) = false := by
  decide +kernel

theorem node_context_11_17701_453015 : EJMOriginalGlobalDAGData.nodes 10 ⟨453015, by decide⟩ =
    .split (coordinate 11) (![⟨452935, by decide⟩,⟨449506, by decide⟩,⟨452980, by decide⟩,⟨453014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17701_453015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17701 ⟨453015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17701
    ⟨453015, by decide⟩ (by decide) (![⟨452935, by decide⟩,⟨449506, by decide⟩,⟨452980, by decide⟩,⟨453014, by decide⟩]) unmarked_context_11_17701_453015 node_context_11_17701_453015
  intro a
  fin_cases a
  · exact context_12_70804_452935
  · exact context_12_70805_449506
  · exact context_12_70806_452980
  · exact context_12_70807_453014

theorem selected_cut_17789 : selected 9 ⟨453038, by decide⟩
    (prefixPartial 12 70808) = some ⟨12, 2, 0, 453038, 70808, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_70808_453038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70808 ⟨453038, by decide⟩ :=
  accepted_of_selected 12 70808 ⟨453038, by decide⟩ ⟨12, 2, 0, 453038, 70808, 1605, 65536⟩
    (by decide) selected_cut_17789

theorem selected_cut_17790 : selected 9 ⟨453057, by decide⟩
    (prefixPartial 12 70809) = some ⟨12, 2, 0, 453057, 70809, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_70809_453057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70809 ⟨453057, by decide⟩ :=
  accepted_of_selected 12 70809 ⟨453057, by decide⟩ ⟨12, 2, 0, 453057, 70809, 1565, 65536⟩
    (by decide) selected_cut_17790

theorem selected_cut_17791 : selected 9 ⟨453080, by decide⟩
    (prefixPartial 12 70810) = some ⟨12, 2, 0, 453080, 70810, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_70810_453080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70810 ⟨453080, by decide⟩ :=
  accepted_of_selected 12 70810 ⟨453080, by decide⟩ ⟨12, 2, 0, 453080, 70810, 1581, 65536⟩
    (by decide) selected_cut_17791

theorem selected_cut_17792 : selected 9 ⟨453101, by decide⟩
    (prefixPartial 12 70811) = some ⟨12, 2, 0, 453101, 70811, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_70811_453101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70811 ⟨453101, by decide⟩ :=
  accepted_of_selected 12 70811 ⟨453101, by decide⟩ ⟨12, 2, 0, 453101, 70811, 1633, 65536⟩
    (by decide) selected_cut_17792

theorem unmarked_context_11_17702_453102 : frontier 10 ⟨453102, by decide⟩
    (prefixCache 11 17702) (prefixPartial 11 17702) = false := by
  decide +kernel

theorem node_context_11_17702_453102 : EJMOriginalGlobalDAGData.nodes 10 ⟨453102, by decide⟩ =
    .split (coordinate 11) (![⟨453038, by decide⟩,⟨453057, by decide⟩,⟨453080, by decide⟩,⟨453101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17702_453102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17702 ⟨453102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17702
    ⟨453102, by decide⟩ (by decide) (![⟨453038, by decide⟩,⟨453057, by decide⟩,⟨453080, by decide⟩,⟨453101, by decide⟩]) unmarked_context_11_17702_453102 node_context_11_17702_453102
  intro a
  fin_cases a
  · exact context_12_70808_453038
  · exact context_12_70809_453057
  · exact context_12_70810_453080
  · exact context_12_70811_453101

theorem selected_cut_17793 : selected 9 ⟨453120, by decide⟩
    (prefixPartial 12 70812) = some ⟨12, 2, 0, 453120, 70812, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_70812_453120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70812 ⟨453120, by decide⟩ :=
  accepted_of_selected 12 70812 ⟨453120, by decide⟩ ⟨12, 2, 0, 453120, 70812, 1289, 65536⟩
    (by decide) selected_cut_17793

theorem selected_cut_17794 : selected 9 ⟨453136, by decide⟩
    (prefixPartial 12 70813) = some ⟨12, 2, 0, 453136, 70813, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_70813_453136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70813 ⟨453136, by decide⟩ :=
  accepted_of_selected 12 70813 ⟨453136, by decide⟩ ⟨12, 2, 0, 453136, 70813, 1261, 65536⟩
    (by decide) selected_cut_17794

theorem selected_cut_17795 : selected 9 ⟨453152, by decide⟩
    (prefixPartial 12 70814) = some ⟨12, 2, 0, 453152, 70814, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_70814_453152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70814 ⟨453152, by decide⟩ :=
  accepted_of_selected 12 70814 ⟨453152, by decide⟩ ⟨12, 2, 0, 453152, 70814, 1373, 65536⟩
    (by decide) selected_cut_17795

theorem selected_cut_17796 : selected 9 ⟨453168, by decide⟩
    (prefixPartial 12 70815) = some ⟨12, 2, 0, 453168, 70815, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_70815_453168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70815 ⟨453168, by decide⟩ :=
  accepted_of_selected 12 70815 ⟨453168, by decide⟩ ⟨12, 2, 0, 453168, 70815, 1297, 65536⟩
    (by decide) selected_cut_17796

theorem unmarked_context_11_17703_453169 : frontier 10 ⟨453169, by decide⟩
    (prefixCache 11 17703) (prefixPartial 11 17703) = false := by
  decide +kernel

theorem node_context_11_17703_453169 : EJMOriginalGlobalDAGData.nodes 10 ⟨453169, by decide⟩ =
    .split (coordinate 11) (![⟨453120, by decide⟩,⟨453136, by decide⟩,⟨453152, by decide⟩,⟨453168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17703_453169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17703 ⟨453169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17703
    ⟨453169, by decide⟩ (by decide) (![⟨453120, by decide⟩,⟨453136, by decide⟩,⟨453152, by decide⟩,⟨453168, by decide⟩]) unmarked_context_11_17703_453169 node_context_11_17703_453169
  intro a
  fin_cases a
  · exact context_12_70812_453120
  · exact context_12_70813_453136
  · exact context_12_70814_453152
  · exact context_12_70815_453168

theorem unmarked_context_10_4425_453170 : frontier 11 ⟨453170, by decide⟩
    (prefixCache 10 4425) (prefixPartial 10 4425) = false := by
  decide +kernel

theorem node_context_10_4425_453170 : EJMOriginalGlobalDAGData.nodes 11 ⟨453170, by decide⟩ =
    .split (coordinate 10) (![⟨452898, by decide⟩,⟨453015, by decide⟩,⟨453102, by decide⟩,⟨453169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4425_453170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4425 ⟨453170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4425
    ⟨453170, by decide⟩ (by decide) (![⟨452898, by decide⟩,⟨453015, by decide⟩,⟨453102, by decide⟩,⟨453169, by decide⟩]) unmarked_context_10_4425_453170 node_context_10_4425_453170
  intro a
  fin_cases a
  · exact context_11_17700_452898
  · exact context_11_17701_453015
  · exact context_11_17702_453102
  · exact context_11_17703_453169

theorem selected_cut_17797 : selected 10 ⟨453213, by decide⟩
    (prefixPartial 11 17704) = some ⟨11, 2, 0, 453213, 17704, 3553, 262144⟩ := by
  decide +kernel

theorem context_11_17704_453213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17704 ⟨453213, by decide⟩ :=
  accepted_of_selected 11 17704 ⟨453213, by decide⟩ ⟨11, 2, 0, 453213, 17704, 3553, 262144⟩
    (by decide) selected_cut_17797

theorem selected_cut_17798 : selected 10 ⟨453269, by decide⟩
    (prefixPartial 11 17705) = some ⟨11, 2, 0, 453269, 17705, 3165, 262144⟩ := by
  decide +kernel

theorem context_11_17705_453269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17705 ⟨453269, by decide⟩ :=
  accepted_of_selected 11 17705 ⟨453269, by decide⟩ ⟨11, 2, 0, 453269, 17705, 3165, 262144⟩
    (by decide) selected_cut_17798

theorem selected_cut_17799 : selected 10 ⟨453325, by decide⟩
    (prefixPartial 11 17706) = some ⟨11, 2, 0, 453325, 17706, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_17706_453325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17706 ⟨453325, by decide⟩ :=
  accepted_of_selected 11 17706 ⟨453325, by decide⟩ ⟨11, 2, 0, 453325, 17706, 2649, 262144⟩
    (by decide) selected_cut_17799

theorem selected_cut_17800 : selected 10 ⟨453368, by decide⟩
    (prefixPartial 11 17707) = some ⟨11, 2, 0, 453368, 17707, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_17707_453368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17707 ⟨453368, by decide⟩ :=
  accepted_of_selected 11 17707 ⟨453368, by decide⟩ ⟨11, 2, 0, 453368, 17707, 2189, 262144⟩
    (by decide) selected_cut_17800

theorem unmarked_context_10_4426_453369 : frontier 11 ⟨453369, by decide⟩
    (prefixCache 10 4426) (prefixPartial 10 4426) = false := by
  decide +kernel

theorem node_context_10_4426_453369 : EJMOriginalGlobalDAGData.nodes 11 ⟨453369, by decide⟩ =
    .split (coordinate 10) (![⟨453213, by decide⟩,⟨453269, by decide⟩,⟨453325, by decide⟩,⟨453368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4426_453369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4426 ⟨453369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4426
    ⟨453369, by decide⟩ (by decide) (![⟨453213, by decide⟩,⟨453269, by decide⟩,⟨453325, by decide⟩,⟨453368, by decide⟩]) unmarked_context_10_4426_453369 node_context_10_4426_453369
  intro a
  fin_cases a
  · exact context_11_17704_453213
  · exact context_11_17705_453269
  · exact context_11_17706_453325
  · exact context_11_17707_453368

theorem selected_cut_17801 : selected 10 ⟨453413, by decide⟩
    (prefixPartial 11 17708) = some ⟨11, 2, 0, 453413, 17708, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_17708_453413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17708 ⟨453413, by decide⟩ :=
  accepted_of_selected 11 17708 ⟨453413, by decide⟩ ⟨11, 2, 0, 453413, 17708, 1889, 262144⟩
    (by decide) selected_cut_17801

theorem selected_cut_17802 : selected 10 ⟨453441, by decide⟩
    (prefixPartial 11 17709) = some ⟨11, 2, 0, 453441, 17709, 1377, 262144⟩ := by
  decide +kernel

theorem context_11_17709_453441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17709 ⟨453441, by decide⟩ :=
  accepted_of_selected 11 17709 ⟨453441, by decide⟩ ⟨11, 2, 0, 453441, 17709, 1377, 262144⟩
    (by decide) selected_cut_17802

theorem selected_cut_17803 : selected 10 ⟨453464, by decide⟩
    (prefixPartial 11 17710) = some ⟨11, 2, 0, 453464, 17710, 897, 262144⟩ := by
  decide +kernel

theorem context_11_17710_453464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17710 ⟨453464, by decide⟩ :=
  accepted_of_selected 11 17710 ⟨453464, by decide⟩ ⟨11, 2, 0, 453464, 17710, 897, 262144⟩
    (by decide) selected_cut_17803

theorem selected_cut_17804 : selected 10 ⟨453479, by decide⟩
    (prefixPartial 11 17711) = some ⟨11, 2, 0, 453479, 17711, 377, 262144⟩ := by
  decide +kernel

theorem context_11_17711_453479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17711 ⟨453479, by decide⟩ :=
  accepted_of_selected 11 17711 ⟨453479, by decide⟩ ⟨11, 2, 0, 453479, 17711, 377, 262144⟩
    (by decide) selected_cut_17804

theorem unmarked_context_10_4427_453480 : frontier 11 ⟨453480, by decide⟩
    (prefixCache 10 4427) (prefixPartial 10 4427) = false := by
  decide +kernel

theorem node_context_10_4427_453480 : EJMOriginalGlobalDAGData.nodes 11 ⟨453480, by decide⟩ =
    .split (coordinate 10) (![⟨453413, by decide⟩,⟨453441, by decide⟩,⟨453464, by decide⟩,⟨453479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4427_453480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4427 ⟨453480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4427
    ⟨453480, by decide⟩ (by decide) (![⟨453413, by decide⟩,⟨453441, by decide⟩,⟨453464, by decide⟩,⟨453479, by decide⟩]) unmarked_context_10_4427_453480 node_context_10_4427_453480
  intro a
  fin_cases a
  · exact context_11_17708_453413
  · exact context_11_17709_453441
  · exact context_11_17710_453464
  · exact context_11_17711_453479

theorem unmarked_context_9_1106_453481 : frontier 12 ⟨453481, by decide⟩
    (prefixCache 9 1106) (prefixPartial 9 1106) = false := by
  decide +kernel

theorem node_context_9_1106_453481 : EJMOriginalGlobalDAGData.nodes 12 ⟨453481, by decide⟩ =
    .split (coordinate 9) (![⟨452789, by decide⟩,⟨453170, by decide⟩,⟨453369, by decide⟩,⟨453480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1106_453481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1106 ⟨453481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1106
    ⟨453481, by decide⟩ (by decide) (![⟨452789, by decide⟩,⟨453170, by decide⟩,⟨453369, by decide⟩,⟨453480, by decide⟩]) unmarked_context_9_1106_453481 node_context_9_1106_453481
  intro a
  fin_cases a
  · exact context_10_4424_452789
  · exact context_10_4425_453170
  · exact context_10_4426_453369
  · exact context_10_4427_453480

theorem selected_cut_17805 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 1107) = some ⟨9, 1, 0, 4601, 1107, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_1107_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1107 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 1107 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 1107, 1, 4194304⟩
    (by decide) selected_cut_17805

theorem unmarked_context_8_276_453482 : frontier 13 ⟨453482, by decide⟩
    (prefixCache 8 276) (prefixPartial 8 276) = false := by
  decide +kernel

theorem node_context_8_276_453482 : EJMOriginalGlobalDAGData.nodes 13 ⟨453482, by decide⟩ =
    .split (coordinate 8) (![⟨450981, by decide⟩,⟨452469, by decide⟩,⟨453481, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_276_453482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 276 ⟨453482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 276
    ⟨453482, by decide⟩ (by decide) (![⟨450981, by decide⟩,⟨452469, by decide⟩,⟨453481, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_276_453482 node_context_8_276_453482
  intro a
  fin_cases a
  · exact context_9_1104_450981
  · exact context_9_1105_452469
  · exact context_9_1106_453481
  · exact context_9_1107_4601

theorem selected_cut_17806 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17728) = some ⟨11, 1, 0, 434745, 17728, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17728_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17728 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17728 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17728, 1, 262144⟩
    (by decide) selected_cut_17806

theorem selected_cut_17807 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 70916) = some ⟨12, 1, 0, 448748, 70916, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70916_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70916 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 70916 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 70916, 1, 65536⟩
    (by decide) selected_cut_17807

theorem selected_cut_17808 : selected 7 ⟨453553, by decide⟩
    (prefixPartial 14 1134672) = some ⟨14, 2, 0, 453553, 1134672, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_1134672_453553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134672 ⟨453553, by decide⟩ :=
  accepted_of_selected 14 1134672 ⟨453553, by decide⟩ ⟨14, 2, 0, 453553, 1134672, 1189, 4096⟩
    (by decide) selected_cut_17808

theorem selected_cut_17809 : selected 7 ⟨453622, by decide⟩
    (prefixPartial 14 1134673) = some ⟨14, 2, 0, 453622, 1134673, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_1134673_453622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134673 ⟨453622, by decide⟩ :=
  accepted_of_selected 14 1134673 ⟨453622, by decide⟩ ⟨14, 2, 0, 453622, 1134673, 1249, 4096⟩
    (by decide) selected_cut_17809

theorem selected_cut_17810 : selected 7 ⟨453746, by decide⟩
    (prefixPartial 14 1134674) = some ⟨14, 2, 0, 453746, 1134674, 1913, 4096⟩ := by
  decide +kernel

theorem context_14_1134674_453746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134674 ⟨453746, by decide⟩ :=
  accepted_of_selected 14 1134674 ⟨453746, by decide⟩ ⟨14, 2, 0, 453746, 1134674, 1913, 4096⟩
    (by decide) selected_cut_17810

theorem selected_cut_17811 : selected 7 ⟨291, by decide⟩
    (prefixPartial 14 1134675) = some ⟨14, 1, 0, 291, 1134675, 1, 4096⟩ := by
  decide +kernel

theorem context_14_1134675_291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134675 ⟨291, by decide⟩ :=
  accepted_of_selected 14 1134675 ⟨291, by decide⟩ ⟨14, 1, 0, 291, 1134675, 1, 4096⟩
    (by decide) selected_cut_17811

theorem unmarked_context_13_283668_453747 : frontier 8 ⟨453747, by decide⟩
    (prefixCache 13 283668) (prefixPartial 13 283668) = false := by
  decide +kernel

theorem node_context_13_283668_453747 : EJMOriginalGlobalDAGData.nodes 8 ⟨453747, by decide⟩ =
    .split (coordinate 13) (![⟨453553, by decide⟩,⟨453622, by decide⟩,⟨453746, by decide⟩,⟨291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_283668_453747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283668 ⟨453747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 283668
    ⟨453747, by decide⟩ (by decide) (![⟨453553, by decide⟩,⟨453622, by decide⟩,⟨453746, by decide⟩,⟨291, by decide⟩]) unmarked_context_13_283668_453747 node_context_13_283668_453747
  intro a
  fin_cases a
  · exact context_14_1134672_453553
  · exact context_14_1134673_453622
  · exact context_14_1134674_453746
  · exact context_14_1134675_291

theorem selected_cut_17812 : selected 8 ⟨453862, by decide⟩
    (prefixPartial 13 283669) = some ⟨13, 2, 0, 453862, 283669, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_283669_453862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283669 ⟨453862, by decide⟩ :=
  accepted_of_selected 13 283669 ⟨453862, by decide⟩ ⟨13, 2, 0, 453862, 283669, 1845, 16384⟩
    (by decide) selected_cut_17812

theorem selected_cut_17813 : selected 8 ⟨453949, by decide⟩
    (prefixPartial 13 283670) = some ⟨13, 2, 0, 453949, 283670, 865, 16384⟩ := by
  decide +kernel

theorem context_13_283670_453949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283670 ⟨453949, by decide⟩ :=
  accepted_of_selected 13 283670 ⟨453949, by decide⟩ ⟨13, 2, 0, 453949, 283670, 865, 16384⟩
    (by decide) selected_cut_17813

theorem selected_cut_17814 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 283671) = some ⟨13, 1, 0, 414, 283671, 1, 16384⟩ := by
  decide +kernel

theorem context_13_283671_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283671 ⟨414, by decide⟩ :=
  accepted_of_selected 13 283671 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 283671, 1, 16384⟩
    (by decide) selected_cut_17814

theorem unmarked_context_12_70917_453950 : frontier 9 ⟨453950, by decide⟩
    (prefixCache 12 70917) (prefixPartial 12 70917) = false := by
  decide +kernel

theorem node_context_12_70917_453950 : EJMOriginalGlobalDAGData.nodes 9 ⟨453950, by decide⟩ =
    .split (coordinate 12) (![⟨453747, by decide⟩,⟨453862, by decide⟩,⟨453949, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70917_453950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70917 ⟨453950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70917
    ⟨453950, by decide⟩ (by decide) (![⟨453747, by decide⟩,⟨453862, by decide⟩,⟨453949, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_70917_453950 node_context_12_70917_453950
  intro a
  fin_cases a
  · exact context_13_283668_453747
  · exact context_13_283669_453862
  · exact context_13_283670_453949
  · exact context_13_283671_414

theorem selected_cut_17815 : selected 7 ⟨454000, by decide⟩
    (prefixPartial 14 1134688) = some ⟨14, 2, 0, 454000, 1134688, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_1134688_454000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134688 ⟨454000, by decide⟩ :=
  accepted_of_selected 14 1134688 ⟨454000, by decide⟩ ⟨14, 2, 0, 454000, 1134688, 1221, 4096⟩
    (by decide) selected_cut_17815

theorem selected_cut_17816 : selected 7 ⟨454040, by decide⟩
    (prefixPartial 14 1134689) = some ⟨14, 2, 0, 454040, 1134689, 1429, 4096⟩ := by
  decide +kernel

theorem context_14_1134689_454040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134689 ⟨454040, by decide⟩ :=
  accepted_of_selected 14 1134689 ⟨454040, by decide⟩ ⟨14, 2, 0, 454040, 1134689, 1429, 4096⟩
    (by decide) selected_cut_17816

theorem selected_cut_17817 : selected 7 ⟨454104, by decide⟩
    (prefixPartial 14 1134690) = some ⟨14, 2, 0, 454104, 1134690, 1913, 4096⟩ := by
  decide +kernel

theorem context_14_1134690_454104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134690 ⟨454104, by decide⟩ :=
  accepted_of_selected 14 1134690 ⟨454104, by decide⟩ ⟨14, 2, 0, 454104, 1134690, 1913, 4096⟩
    (by decide) selected_cut_17817

theorem selected_cut_17818 : selected 7 ⟨454158, by decide⟩
    (prefixPartial 14 1134691) = some ⟨14, 2, 0, 454158, 1134691, 1729, 4096⟩ := by
  decide +kernel

theorem context_14_1134691_454158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134691 ⟨454158, by decide⟩ :=
  accepted_of_selected 14 1134691 ⟨454158, by decide⟩ ⟨14, 2, 0, 454158, 1134691, 1729, 4096⟩
    (by decide) selected_cut_17818

theorem unmarked_context_13_283672_454159 : frontier 8 ⟨454159, by decide⟩
    (prefixCache 13 283672) (prefixPartial 13 283672) = false := by
  decide +kernel

theorem node_context_13_283672_454159 : EJMOriginalGlobalDAGData.nodes 8 ⟨454159, by decide⟩ =
    .split (coordinate 13) (![⟨454000, by decide⟩,⟨454040, by decide⟩,⟨454104, by decide⟩,⟨454158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_283672_454159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283672 ⟨454159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 283672
    ⟨454159, by decide⟩ (by decide) (![⟨454000, by decide⟩,⟨454040, by decide⟩,⟨454104, by decide⟩,⟨454158, by decide⟩]) unmarked_context_13_283672_454159 node_context_13_283672_454159
  intro a
  fin_cases a
  · exact context_14_1134688_454000
  · exact context_14_1134689_454040
  · exact context_14_1134690_454104
  · exact context_14_1134691_454158

theorem selected_cut_17819 : selected 8 ⟨454230, by decide⟩
    (prefixPartial 13 283673) = some ⟨13, 2, 0, 454230, 283673, 3609, 16384⟩ := by
  decide +kernel

theorem context_13_283673_454230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283673 ⟨454230, by decide⟩ :=
  accepted_of_selected 13 283673 ⟨454230, by decide⟩ ⟨13, 2, 0, 454230, 283673, 3609, 16384⟩
    (by decide) selected_cut_17819

theorem selected_cut_17820 : selected 8 ⟨454282, by decide⟩
    (prefixPartial 13 283674) = some ⟨13, 2, 0, 454282, 283674, 2949, 16384⟩ := by
  decide +kernel

theorem context_13_283674_454282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283674 ⟨454282, by decide⟩ :=
  accepted_of_selected 13 283674 ⟨454282, by decide⟩ ⟨13, 2, 0, 454282, 283674, 2949, 16384⟩
    (by decide) selected_cut_17820

theorem selected_cut_17821 : selected 8 ⟨454325, by decide⟩
    (prefixPartial 13 283675) = some ⟨13, 2, 0, 454325, 283675, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_283675_454325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283675 ⟨454325, by decide⟩ :=
  accepted_of_selected 13 283675 ⟨454325, by decide⟩ ⟨13, 2, 0, 454325, 283675, 1685, 16384⟩
    (by decide) selected_cut_17821

theorem unmarked_context_12_70918_454326 : frontier 9 ⟨454326, by decide⟩
    (prefixCache 12 70918) (prefixPartial 12 70918) = false := by
  decide +kernel

theorem node_context_12_70918_454326 : EJMOriginalGlobalDAGData.nodes 9 ⟨454326, by decide⟩ =
    .split (coordinate 12) (![⟨454159, by decide⟩,⟨454230, by decide⟩,⟨454282, by decide⟩,⟨454325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70918_454326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70918 ⟨454326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70918
    ⟨454326, by decide⟩ (by decide) (![⟨454159, by decide⟩,⟨454230, by decide⟩,⟨454282, by decide⟩,⟨454325, by decide⟩]) unmarked_context_12_70918_454326 node_context_12_70918_454326
  intro a
  fin_cases a
  · exact context_13_283672_454159
  · exact context_13_283673_454230
  · exact context_13_283674_454282
  · exact context_13_283675_454325

theorem selected_cut_17822 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70919) = some ⟨12, 1, 0, 893, 70919, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70919_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70919 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70919 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70919, 1, 65536⟩
    (by decide) selected_cut_17822

theorem unmarked_context_11_17729_454327 : frontier 10 ⟨454327, by decide⟩
    (prefixCache 11 17729) (prefixPartial 11 17729) = false := by
  decide +kernel

theorem node_context_11_17729_454327 : EJMOriginalGlobalDAGData.nodes 10 ⟨454327, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨453950, by decide⟩,⟨454326, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17729_454327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17729 ⟨454327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17729
    ⟨454327, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨453950, by decide⟩,⟨454326, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17729_454327 node_context_11_17729_454327
  intro a
  fin_cases a
  · exact context_12_70916_448748
  · exact context_12_70917_453950
  · exact context_12_70918_454326
  · exact context_12_70919_893

theorem selected_cut_17823 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 70920) = some ⟨12, 1, 0, 448748, 70920, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70920_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70920 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 70920 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 70920, 1, 65536⟩
    (by decide) selected_cut_17823

theorem selected_cut_17824 : selected 7 ⟨454354, by decide⟩
    (prefixPartial 14 1134736) = some ⟨14, 2, 0, 454354, 1134736, 701, 4096⟩ := by
  decide +kernel

theorem context_14_1134736_454354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134736 ⟨454354, by decide⟩ :=
  accepted_of_selected 14 1134736 ⟨454354, by decide⟩ ⟨14, 2, 0, 454354, 1134736, 701, 4096⟩
    (by decide) selected_cut_17824

theorem selected_cut_17825 : selected 7 ⟨454398, by decide⟩
    (prefixPartial 14 1134737) = some ⟨14, 2, 0, 454398, 1134737, 1377, 4096⟩ := by
  decide +kernel

theorem context_14_1134737_454398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134737 ⟨454398, by decide⟩ :=
  accepted_of_selected 14 1134737 ⟨454398, by decide⟩ ⟨14, 2, 0, 454398, 1134737, 1377, 4096⟩
    (by decide) selected_cut_17825

theorem selected_cut_17826 : selected 7 ⟨454432, by decide⟩
    (prefixPartial 14 1134738) = some ⟨14, 2, 0, 454432, 1134738, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_1134738_454432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134738 ⟨454432, by decide⟩ :=
  accepted_of_selected 14 1134738 ⟨454432, by decide⟩ ⟨14, 2, 0, 454432, 1134738, 1117, 4096⟩
    (by decide) selected_cut_17826

theorem selected_cut_17827 : selected 7 ⟨454470, by decide⟩
    (prefixPartial 14 1134739) = some ⟨14, 2, 0, 454470, 1134739, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_1134739_454470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134739 ⟨454470, by decide⟩ :=
  accepted_of_selected 14 1134739 ⟨454470, by decide⟩ ⟨14, 2, 0, 454470, 1134739, 1341, 4096⟩
    (by decide) selected_cut_17827

theorem unmarked_context_13_283684_454471 : frontier 8 ⟨454471, by decide⟩
    (prefixCache 13 283684) (prefixPartial 13 283684) = false := by
  decide +kernel

theorem node_context_13_283684_454471 : EJMOriginalGlobalDAGData.nodes 8 ⟨454471, by decide⟩ =
    .split (coordinate 13) (![⟨454354, by decide⟩,⟨454398, by decide⟩,⟨454432, by decide⟩,⟨454470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_283684_454471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283684 ⟨454471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 283684
    ⟨454471, by decide⟩ (by decide) (![⟨454354, by decide⟩,⟨454398, by decide⟩,⟨454432, by decide⟩,⟨454470, by decide⟩]) unmarked_context_13_283684_454471 node_context_13_283684_454471
  intro a
  fin_cases a
  · exact context_14_1134736_454354
  · exact context_14_1134737_454398
  · exact context_14_1134738_454432
  · exact context_14_1134739_454470

theorem selected_cut_17828 : selected 8 ⟨454563, by decide⟩
    (prefixPartial 13 283685) = some ⟨13, 2, 0, 454563, 283685, 3517, 16384⟩ := by
  decide +kernel

theorem context_13_283685_454563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283685 ⟨454563, by decide⟩ :=
  accepted_of_selected 13 283685 ⟨454563, by decide⟩ ⟨13, 2, 0, 454563, 283685, 3517, 16384⟩
    (by decide) selected_cut_17828

theorem selected_cut_17829 : selected 8 ⟨454627, by decide⟩
    (prefixPartial 13 283686) = some ⟨13, 2, 0, 454627, 283686, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_283686_454627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283686 ⟨454627, by decide⟩ :=
  accepted_of_selected 13 283686 ⟨454627, by decide⟩ ⟨13, 2, 0, 454627, 283686, 2741, 16384⟩
    (by decide) selected_cut_17829

theorem selected_cut_17830 : selected 8 ⟨454660, by decide⟩
    (prefixPartial 13 283687) = some ⟨13, 2, 0, 454660, 283687, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_283687_454660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283687 ⟨454660, by decide⟩ :=
  accepted_of_selected 13 283687 ⟨454660, by decide⟩ ⟨13, 2, 0, 454660, 283687, 1405, 16384⟩
    (by decide) selected_cut_17830

theorem unmarked_context_12_70921_454661 : frontier 9 ⟨454661, by decide⟩
    (prefixCache 12 70921) (prefixPartial 12 70921) = false := by
  decide +kernel

theorem node_context_12_70921_454661 : EJMOriginalGlobalDAGData.nodes 9 ⟨454661, by decide⟩ =
    .split (coordinate 12) (![⟨454471, by decide⟩,⟨454563, by decide⟩,⟨454627, by decide⟩,⟨454660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70921_454661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70921 ⟨454661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70921
    ⟨454661, by decide⟩ (by decide) (![⟨454471, by decide⟩,⟨454563, by decide⟩,⟨454627, by decide⟩,⟨454660, by decide⟩]) unmarked_context_12_70921_454661 node_context_12_70921_454661
  intro a
  fin_cases a
  · exact context_13_283684_454471
  · exact context_13_283685_454563
  · exact context_13_283686_454627
  · exact context_13_283687_454660

theorem selected_cut_17831 : selected 7 ⟨454686, by decide⟩
    (prefixPartial 14 1134752) = some ⟨14, 2, 0, 454686, 1134752, 705, 4096⟩ := by
  decide +kernel

theorem context_14_1134752_454686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134752 ⟨454686, by decide⟩ :=
  accepted_of_selected 14 1134752 ⟨454686, by decide⟩ ⟨14, 2, 0, 454686, 1134752, 705, 4096⟩
    (by decide) selected_cut_17831

theorem selected_cut_17832 : selected 7 ⟨454735, by decide⟩
    (prefixPartial 14 1134753) = some ⟨14, 2, 0, 454735, 1134753, 1833, 4096⟩ := by
  decide +kernel

theorem context_14_1134753_454735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134753 ⟨454735, by decide⟩ :=
  accepted_of_selected 14 1134753 ⟨454735, by decide⟩ ⟨14, 2, 0, 454735, 1134753, 1833, 4096⟩
    (by decide) selected_cut_17832

theorem selected_cut_17833 : selected 7 ⟨454775, by decide⟩
    (prefixPartial 14 1134754) = some ⟨14, 2, 0, 454775, 1134754, 1613, 4096⟩ := by
  decide +kernel

theorem context_14_1134754_454775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134754 ⟨454775, by decide⟩ :=
  accepted_of_selected 14 1134754 ⟨454775, by decide⟩ ⟨14, 2, 0, 454775, 1134754, 1613, 4096⟩
    (by decide) selected_cut_17833

theorem selected_cut_17834 : selected 7 ⟨454811, by decide⟩
    (prefixPartial 14 1134755) = some ⟨14, 2, 0, 454811, 1134755, 1605, 4096⟩ := by
  decide +kernel

theorem context_14_1134755_454811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134755 ⟨454811, by decide⟩ :=
  accepted_of_selected 14 1134755 ⟨454811, by decide⟩ ⟨14, 2, 0, 454811, 1134755, 1605, 4096⟩
    (by decide) selected_cut_17834

theorem unmarked_context_13_283688_454812 : frontier 8 ⟨454812, by decide⟩
    (prefixCache 13 283688) (prefixPartial 13 283688) = false := by
  decide +kernel

theorem node_context_13_283688_454812 : EJMOriginalGlobalDAGData.nodes 8 ⟨454812, by decide⟩ =
    .split (coordinate 13) (![⟨454686, by decide⟩,⟨454735, by decide⟩,⟨454775, by decide⟩,⟨454811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_283688_454812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283688 ⟨454812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 283688
    ⟨454812, by decide⟩ (by decide) (![⟨454686, by decide⟩,⟨454735, by decide⟩,⟨454775, by decide⟩,⟨454811, by decide⟩]) unmarked_context_13_283688_454812 node_context_13_283688_454812
  intro a
  fin_cases a
  · exact context_14_1134752_454686
  · exact context_14_1134753_454735
  · exact context_14_1134754_454775
  · exact context_14_1134755_454811

theorem selected_cut_17835 : selected 8 ⟨454911, by decide⟩
    (prefixPartial 13 283689) = some ⟨13, 2, 0, 454911, 283689, 3989, 16384⟩ := by
  decide +kernel

theorem context_13_283689_454911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283689 ⟨454911, by decide⟩ :=
  accepted_of_selected 13 283689 ⟨454911, by decide⟩ ⟨13, 2, 0, 454911, 283689, 3989, 16384⟩
    (by decide) selected_cut_17835

theorem selected_cut_17836 : selected 8 ⟨454991, by decide⟩
    (prefixPartial 13 283690) = some ⟨13, 2, 0, 454991, 283690, 2949, 16384⟩ := by
  decide +kernel

theorem context_13_283690_454991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283690 ⟨454991, by decide⟩ :=
  accepted_of_selected 13 283690 ⟨454991, by decide⟩ ⟨13, 2, 0, 454991, 283690, 2949, 16384⟩
    (by decide) selected_cut_17836

theorem selected_cut_17837 : selected 8 ⟨455063, by decide⟩
    (prefixPartial 13 283691) = some ⟨13, 2, 0, 455063, 283691, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_283691_455063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283691 ⟨455063, by decide⟩ :=
  accepted_of_selected 13 283691 ⟨455063, by decide⟩ ⟨13, 2, 0, 455063, 283691, 1589, 16384⟩
    (by decide) selected_cut_17837

theorem unmarked_context_12_70922_455064 : frontier 9 ⟨455064, by decide⟩
    (prefixCache 12 70922) (prefixPartial 12 70922) = false := by
  decide +kernel

theorem node_context_12_70922_455064 : EJMOriginalGlobalDAGData.nodes 9 ⟨455064, by decide⟩ =
    .split (coordinate 12) (![⟨454812, by decide⟩,⟨454911, by decide⟩,⟨454991, by decide⟩,⟨455063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70922_455064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70922 ⟨455064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70922
    ⟨455064, by decide⟩ (by decide) (![⟨454812, by decide⟩,⟨454911, by decide⟩,⟨454991, by decide⟩,⟨455063, by decide⟩]) unmarked_context_12_70922_455064 node_context_12_70922_455064
  intro a
  fin_cases a
  · exact context_13_283688_454812
  · exact context_13_283689_454911
  · exact context_13_283690_454991
  · exact context_13_283691_455063

theorem selected_cut_17838 : selected 7 ⟨455076, by decide⟩
    (prefixPartial 14 1134768) = some ⟨14, 2, 0, 455076, 1134768, 345, 4096⟩ := by
  decide +kernel

theorem context_14_1134768_455076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134768 ⟨455076, by decide⟩ :=
  accepted_of_selected 14 1134768 ⟨455076, by decide⟩ ⟨14, 2, 0, 455076, 1134768, 345, 4096⟩
    (by decide) selected_cut_17838

theorem selected_cut_17839 : selected 7 ⟨455132, by decide⟩
    (prefixPartial 14 1134769) = some ⟨14, 2, 0, 455132, 1134769, 1869, 4096⟩ := by
  decide +kernel

theorem context_14_1134769_455132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134769 ⟨455132, by decide⟩ :=
  accepted_of_selected 14 1134769 ⟨455132, by decide⟩ ⟨14, 2, 0, 455132, 1134769, 1869, 4096⟩
    (by decide) selected_cut_17839

theorem selected_cut_17840 : selected 7 ⟨455173, by decide⟩
    (prefixPartial 14 1134770) = some ⟨14, 2, 0, 455173, 1134770, 1633, 4096⟩ := by
  decide +kernel

theorem context_14_1134770_455173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134770 ⟨455173, by decide⟩ :=
  accepted_of_selected 14 1134770 ⟨455173, by decide⟩ ⟨14, 2, 0, 455173, 1134770, 1633, 4096⟩
    (by decide) selected_cut_17840

theorem selected_cut_17841 : selected 7 ⟨455213, by decide⟩
    (prefixPartial 14 1134771) = some ⟨14, 2, 0, 455213, 1134771, 1709, 4096⟩ := by
  decide +kernel

theorem context_14_1134771_455213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134771 ⟨455213, by decide⟩ :=
  accepted_of_selected 14 1134771 ⟨455213, by decide⟩ ⟨14, 2, 0, 455213, 1134771, 1709, 4096⟩
    (by decide) selected_cut_17841

theorem unmarked_context_13_283692_455214 : frontier 8 ⟨455214, by decide⟩
    (prefixCache 13 283692) (prefixPartial 13 283692) = false := by
  decide +kernel

theorem node_context_13_283692_455214 : EJMOriginalGlobalDAGData.nodes 8 ⟨455214, by decide⟩ =
    .split (coordinate 13) (![⟨455076, by decide⟩,⟨455132, by decide⟩,⟨455173, by decide⟩,⟨455213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_283692_455214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283692 ⟨455214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 283692
    ⟨455214, by decide⟩ (by decide) (![⟨455076, by decide⟩,⟨455132, by decide⟩,⟨455173, by decide⟩,⟨455213, by decide⟩]) unmarked_context_13_283692_455214 node_context_13_283692_455214
  intro a
  fin_cases a
  · exact context_14_1134768_455076
  · exact context_14_1134769_455132
  · exact context_14_1134770_455173
  · exact context_14_1134771_455213

theorem selected_cut_17842 : selected 7 ⟨455225, by decide⟩
    (prefixPartial 14 1134772) = some ⟨14, 2, 0, 455225, 1134772, 841, 4096⟩ := by
  decide +kernel

theorem context_14_1134772_455225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134772 ⟨455225, by decide⟩ :=
  accepted_of_selected 14 1134772 ⟨455225, by decide⟩ ⟨14, 2, 0, 455225, 1134772, 841, 4096⟩
    (by decide) selected_cut_17842

theorem selected_cut_17843 : selected 7 ⟨455245, by decide⟩
    (prefixPartial 14 1134773) = some ⟨14, 2, 0, 455245, 1134773, 941, 4096⟩ := by
  decide +kernel

theorem context_14_1134773_455245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134773 ⟨455245, by decide⟩ :=
  accepted_of_selected 14 1134773 ⟨455245, by decide⟩ ⟨14, 2, 0, 455245, 1134773, 941, 4096⟩
    (by decide) selected_cut_17843

theorem selected_cut_17844 : selected 7 ⟨455277, by decide⟩
    (prefixPartial 14 1134774) = some ⟨14, 2, 0, 455277, 1134774, 1165, 4096⟩ := by
  decide +kernel

theorem context_14_1134774_455277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134774 ⟨455277, by decide⟩ :=
  accepted_of_selected 14 1134774 ⟨455277, by decide⟩ ⟨14, 2, 0, 455277, 1134774, 1165, 4096⟩
    (by decide) selected_cut_17844

theorem selected_cut_17845 : selected 7 ⟨455314, by decide⟩
    (prefixPartial 14 1134775) = some ⟨14, 2, 0, 455314, 1134775, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_1134775_455314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1134775 ⟨455314, by decide⟩ :=
  accepted_of_selected 14 1134775 ⟨455314, by decide⟩ ⟨14, 2, 0, 455314, 1134775, 1289, 4096⟩
    (by decide) selected_cut_17845

theorem unmarked_context_13_283693_455315 : frontier 8 ⟨455315, by decide⟩
    (prefixCache 13 283693) (prefixPartial 13 283693) = false := by
  decide +kernel

theorem node_context_13_283693_455315 : EJMOriginalGlobalDAGData.nodes 8 ⟨455315, by decide⟩ =
    .split (coordinate 13) (![⟨455225, by decide⟩,⟨455245, by decide⟩,⟨455277, by decide⟩,⟨455314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_283693_455315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283693 ⟨455315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 283693
    ⟨455315, by decide⟩ (by decide) (![⟨455225, by decide⟩,⟨455245, by decide⟩,⟨455277, by decide⟩,⟨455314, by decide⟩]) unmarked_context_13_283693_455315 node_context_13_283693_455315
  intro a
  fin_cases a
  · exact context_14_1134772_455225
  · exact context_14_1134773_455245
  · exact context_14_1134774_455277
  · exact context_14_1134775_455314

theorem selected_cut_17846 : selected 8 ⟨455418, by decide⟩
    (prefixPartial 13 283694) = some ⟨13, 2, 0, 455418, 283694, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_283694_455418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283694 ⟨455418, by decide⟩ :=
  accepted_of_selected 13 283694 ⟨455418, by decide⟩ ⟨13, 2, 0, 455418, 283694, 3217, 16384⟩
    (by decide) selected_cut_17846

theorem selected_cut_17847 : selected 8 ⟨455490, by decide⟩
    (prefixPartial 13 283695) = some ⟨13, 2, 0, 455490, 283695, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_283695_455490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283695 ⟨455490, by decide⟩ :=
  accepted_of_selected 13 283695 ⟨455490, by decide⟩ ⟨13, 2, 0, 455490, 283695, 1513, 16384⟩
    (by decide) selected_cut_17847

theorem unmarked_context_12_70923_455491 : frontier 9 ⟨455491, by decide⟩
    (prefixCache 12 70923) (prefixPartial 12 70923) = false := by
  decide +kernel

theorem node_context_12_70923_455491 : EJMOriginalGlobalDAGData.nodes 9 ⟨455491, by decide⟩ =
    .split (coordinate 12) (![⟨455214, by decide⟩,⟨455315, by decide⟩,⟨455418, by decide⟩,⟨455490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70923_455491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70923 ⟨455491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70923
    ⟨455491, by decide⟩ (by decide) (![⟨455214, by decide⟩,⟨455315, by decide⟩,⟨455418, by decide⟩,⟨455490, by decide⟩]) unmarked_context_12_70923_455491 node_context_12_70923_455491
  intro a
  fin_cases a
  · exact context_13_283692_455214
  · exact context_13_283693_455315
  · exact context_13_283694_455418
  · exact context_13_283695_455490

theorem unmarked_context_11_17730_455492 : frontier 10 ⟨455492, by decide⟩
    (prefixCache 11 17730) (prefixPartial 11 17730) = false := by
  decide +kernel

theorem node_context_11_17730_455492 : EJMOriginalGlobalDAGData.nodes 10 ⟨455492, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨454661, by decide⟩,⟨455064, by decide⟩,⟨455491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17730_455492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17730 ⟨455492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17730
    ⟨455492, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨454661, by decide⟩,⟨455064, by decide⟩,⟨455491, by decide⟩]) unmarked_context_11_17730_455492 node_context_11_17730_455492
  intro a
  fin_cases a
  · exact context_12_70920_448748
  · exact context_12_70921_454661
  · exact context_12_70922_455064
  · exact context_12_70923_455491

theorem selected_cut_17848 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17731) = some ⟨11, 1, 0, 1736, 17731, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17731_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17731 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17731 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17731, 1, 262144⟩
    (by decide) selected_cut_17848

theorem unmarked_context_10_4432_455493 : frontier 11 ⟨455493, by decide⟩
    (prefixCache 10 4432) (prefixPartial 10 4432) = false := by
  decide +kernel

theorem node_context_10_4432_455493 : EJMOriginalGlobalDAGData.nodes 11 ⟨455493, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨454327, by decide⟩,⟨455492, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4432_455493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4432 ⟨455493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4432
    ⟨455493, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨454327, by decide⟩,⟨455492, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4432_455493 node_context_10_4432_455493
  intro a
  fin_cases a
  · exact context_11_17728_434745
  · exact context_11_17729_454327
  · exact context_11_17730_455492
  · exact context_11_17731_1736

theorem selected_cut_17849 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 70928) = some ⟨12, 1, 0, 435160, 70928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70928_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70928 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 70928 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 70928, 1, 65536⟩
    (by decide) selected_cut_17849

theorem selected_cut_17850 : selected 9 ⟨455552, by decide⟩
    (prefixPartial 12 70929) = some ⟨12, 2, 0, 455552, 70929, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_70929_455552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70929 ⟨455552, by decide⟩ :=
  accepted_of_selected 12 70929 ⟨455552, by decide⟩ ⟨12, 2, 0, 455552, 70929, 3041, 65536⟩
    (by decide) selected_cut_17850

theorem selected_cut_17851 : selected 8 ⟨455624, by decide⟩
    (prefixPartial 13 283720) = some ⟨13, 2, 0, 455624, 283720, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_283720_455624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283720 ⟨455624, by decide⟩ :=
  accepted_of_selected 13 283720 ⟨455624, by decide⟩ ⟨13, 2, 0, 455624, 283720, 2609, 16384⟩
    (by decide) selected_cut_17851

theorem selected_cut_17852 : selected 8 ⟨455668, by decide⟩
    (prefixPartial 13 283721) = some ⟨13, 2, 0, 455668, 283721, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_283721_455668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283721 ⟨455668, by decide⟩ :=
  accepted_of_selected 13 283721 ⟨455668, by decide⟩ ⟨13, 2, 0, 455668, 283721, 2361, 16384⟩
    (by decide) selected_cut_17852

theorem selected_cut_17853 : selected 8 ⟨455709, by decide⟩
    (prefixPartial 13 283722) = some ⟨13, 2, 0, 455709, 283722, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_283722_455709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283722 ⟨455709, by decide⟩ :=
  accepted_of_selected 13 283722 ⟨455709, by decide⟩ ⟨13, 2, 0, 455709, 283722, 2025, 16384⟩
    (by decide) selected_cut_17853

theorem selected_cut_17854 : selected 8 ⟨455734, by decide⟩
    (prefixPartial 13 283723) = some ⟨13, 2, 0, 455734, 283723, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_283723_455734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 283723 ⟨455734, by decide⟩ :=
  accepted_of_selected 13 283723 ⟨455734, by decide⟩ ⟨13, 2, 0, 455734, 283723, 1093, 16384⟩
    (by decide) selected_cut_17854

theorem unmarked_context_12_70930_455735 : frontier 9 ⟨455735, by decide⟩
    (prefixCache 12 70930) (prefixPartial 12 70930) = false := by
  decide +kernel

theorem node_context_12_70930_455735 : EJMOriginalGlobalDAGData.nodes 9 ⟨455735, by decide⟩ =
    .split (coordinate 12) (![⟨455624, by decide⟩,⟨455668, by decide⟩,⟨455709, by decide⟩,⟨455734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70930_455735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70930 ⟨455735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70930
    ⟨455735, by decide⟩ (by decide) (![⟨455624, by decide⟩,⟨455668, by decide⟩,⟨455709, by decide⟩,⟨455734, by decide⟩]) unmarked_context_12_70930_455735 node_context_12_70930_455735
  intro a
  fin_cases a
  · exact context_13_283720_455624
  · exact context_13_283721_455668
  · exact context_13_283722_455709
  · exact context_13_283723_455734

theorem selected_cut_17855 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 70931) = some ⟨12, 1, 0, 893, 70931, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70931_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70931 ⟨893, by decide⟩ :=
  accepted_of_selected 12 70931 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 70931, 1, 65536⟩
    (by decide) selected_cut_17855

theorem unmarked_context_11_17732_455736 : frontier 10 ⟨455736, by decide⟩
    (prefixCache 11 17732) (prefixPartial 11 17732) = false := by
  decide +kernel

theorem node_context_11_17732_455736 : EJMOriginalGlobalDAGData.nodes 10 ⟨455736, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨455552, by decide⟩,⟨455735, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17732_455736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17732 ⟨455736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17732
    ⟨455736, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨455552, by decide⟩,⟨455735, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17732_455736 node_context_11_17732_455736
  intro a
  fin_cases a
  · exact context_12_70928_435160
  · exact context_12_70929_455552
  · exact context_12_70930_455735
  · exact context_12_70931_893

theorem selected_cut_17856 : selected 9 ⟨455938, by decide⟩
    (prefixPartial 12 70932) = some ⟨12, 2, 0, 455938, 70932, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_70932_455938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70932 ⟨455938, by decide⟩ :=
  accepted_of_selected 12 70932 ⟨455938, by decide⟩ ⟨12, 2, 0, 455938, 70932, 2401, 65536⟩
    (by decide) selected_cut_17856

theorem selected_cut_17857 : selected 9 ⟨455939, by decide⟩
    (prefixPartial 12 70933) = some ⟨12, 1, 0, 455939, 70933, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70933_455939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70933 ⟨455939, by decide⟩ :=
  accepted_of_selected 12 70933 ⟨455939, by decide⟩ ⟨12, 1, 0, 455939, 70933, 1, 65536⟩
    (by decide) selected_cut_17857

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
