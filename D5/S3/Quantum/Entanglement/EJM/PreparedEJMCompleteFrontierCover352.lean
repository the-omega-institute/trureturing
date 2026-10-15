/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover351
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33796 : selected 9 ⟨870368, by decide⟩
    (prefixPartial 12 110500) = some ⟨12, 2, 0, 870368, 110500, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_110500_870368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110500 ⟨870368, by decide⟩ :=
  accepted_of_selected 12 110500 ⟨870368, by decide⟩ ⟨12, 2, 0, 870368, 110500, 1585, 65536⟩
    (by decide) selected_cut_33796

theorem selected_cut_33797 : selected 9 ⟨870382, by decide⟩
    (prefixPartial 12 110501) = some ⟨12, 2, 0, 870382, 110501, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_110501_870382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110501 ⟨870382, by decide⟩ :=
  accepted_of_selected 12 110501 ⟨870382, by decide⟩ ⟨12, 2, 0, 870382, 110501, 1385, 65536⟩
    (by decide) selected_cut_33797

theorem selected_cut_33798 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 110502) = some ⟨12, 1, 0, 769937, 110502, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110502_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110502 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 110502 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 110502, 1, 65536⟩
    (by decide) selected_cut_33798

theorem selected_cut_33799 : selected 9 ⟨870402, by decide⟩
    (prefixPartial 12 110503) = some ⟨12, 2, 0, 870402, 110503, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_110503_870402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110503 ⟨870402, by decide⟩ :=
  accepted_of_selected 12 110503 ⟨870402, by decide⟩ ⟨12, 2, 0, 870402, 110503, 1489, 65536⟩
    (by decide) selected_cut_33799

theorem unmarked_context_11_27625_870403 : frontier 10 ⟨870403, by decide⟩
    (prefixCache 11 27625) (prefixPartial 11 27625) = false := by
  decide +kernel

theorem node_context_11_27625_870403 : EJMOriginalGlobalDAGData.nodes 10 ⟨870403, by decide⟩ =
    .split (coordinate 11) (![⟨870368, by decide⟩,⟨870382, by decide⟩,⟨769937, by decide⟩,⟨870402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27625_870403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27625 ⟨870403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27625
    ⟨870403, by decide⟩ (by decide) (![⟨870368, by decide⟩,⟨870382, by decide⟩,⟨769937, by decide⟩,⟨870402, by decide⟩]) unmarked_context_11_27625_870403 node_context_11_27625_870403
  intro a
  fin_cases a
  · exact context_12_110500_870368
  · exact context_12_110501_870382
  · exact context_12_110502_769937
  · exact context_12_110503_870402

theorem selected_cut_33800 : selected 10 ⟨870451, by decide⟩
    (prefixPartial 11 27626) = some ⟨11, 2, 0, 870451, 27626, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_27626_870451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27626 ⟨870451, by decide⟩ :=
  accepted_of_selected 11 27626 ⟨870451, by decide⟩ ⟨11, 2, 0, 870451, 27626, 3337, 262144⟩
    (by decide) selected_cut_33800

theorem selected_cut_33801 : selected 10 ⟨870482, by decide⟩
    (prefixPartial 11 27627) = some ⟨11, 2, 0, 870482, 27627, 2317, 262144⟩ := by
  decide +kernel

theorem context_11_27627_870482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27627 ⟨870482, by decide⟩ :=
  accepted_of_selected 11 27627 ⟨870482, by decide⟩ ⟨11, 2, 0, 870482, 27627, 2317, 262144⟩
    (by decide) selected_cut_33801

theorem unmarked_context_10_6906_870483 : frontier 11 ⟨870483, by decide⟩
    (prefixCache 10 6906) (prefixPartial 10 6906) = false := by
  decide +kernel

theorem node_context_10_6906_870483 : EJMOriginalGlobalDAGData.nodes 11 ⟨870483, by decide⟩ =
    .split (coordinate 10) (![⟨870351, by decide⟩,⟨870403, by decide⟩,⟨870451, by decide⟩,⟨870482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6906_870483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6906 ⟨870483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6906
    ⟨870483, by decide⟩ (by decide) (![⟨870351, by decide⟩,⟨870403, by decide⟩,⟨870451, by decide⟩,⟨870482, by decide⟩]) unmarked_context_10_6906_870483 node_context_10_6906_870483
  intro a
  fin_cases a
  · exact context_11_27624_870351
  · exact context_11_27625_870403
  · exact context_11_27626_870451
  · exact context_11_27627_870482

theorem selected_cut_33802 : selected 10 ⟨870524, by decide⟩
    (prefixPartial 11 27628) = some ⟨11, 2, 0, 870524, 27628, 3297, 262144⟩ := by
  decide +kernel

theorem context_11_27628_870524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27628 ⟨870524, by decide⟩ :=
  accepted_of_selected 11 27628 ⟨870524, by decide⟩ ⟨11, 2, 0, 870524, 27628, 3297, 262144⟩
    (by decide) selected_cut_33802

theorem selected_cut_33803 : selected 10 ⟨870561, by decide⟩
    (prefixPartial 11 27629) = some ⟨11, 2, 0, 870561, 27629, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_27629_870561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27629 ⟨870561, by decide⟩ :=
  accepted_of_selected 11 27629 ⟨870561, by decide⟩ ⟨11, 2, 0, 870561, 27629, 3181, 262144⟩
    (by decide) selected_cut_33803

theorem selected_cut_33804 : selected 10 ⟨870595, by decide⟩
    (prefixPartial 11 27630) = some ⟨11, 2, 0, 870595, 27630, 2589, 262144⟩ := by
  decide +kernel

theorem context_11_27630_870595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27630 ⟨870595, by decide⟩ :=
  accepted_of_selected 11 27630 ⟨870595, by decide⟩ ⟨11, 2, 0, 870595, 27630, 2589, 262144⟩
    (by decide) selected_cut_33804

theorem selected_cut_33805 : selected 10 ⟨870596, by decide⟩
    (prefixPartial 11 27631) = some ⟨11, 2, 0, 870596, 27631, 5, 262144⟩ := by
  decide +kernel

theorem context_11_27631_870596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27631 ⟨870596, by decide⟩ :=
  accepted_of_selected 11 27631 ⟨870596, by decide⟩ ⟨11, 2, 0, 870596, 27631, 5, 262144⟩
    (by decide) selected_cut_33805

theorem unmarked_context_10_6907_870597 : frontier 11 ⟨870597, by decide⟩
    (prefixCache 10 6907) (prefixPartial 10 6907) = false := by
  decide +kernel

theorem node_context_10_6907_870597 : EJMOriginalGlobalDAGData.nodes 11 ⟨870597, by decide⟩ =
    .split (coordinate 10) (![⟨870524, by decide⟩,⟨870561, by decide⟩,⟨870595, by decide⟩,⟨870596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6907_870597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6907 ⟨870597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6907
    ⟨870597, by decide⟩ (by decide) (![⟨870524, by decide⟩,⟨870561, by decide⟩,⟨870595, by decide⟩,⟨870596, by decide⟩]) unmarked_context_10_6907_870597 node_context_10_6907_870597
  intro a
  fin_cases a
  · exact context_11_27628_870524
  · exact context_11_27629_870561
  · exact context_11_27630_870595
  · exact context_11_27631_870596

theorem unmarked_context_9_1726_870598 : frontier 12 ⟨870598, by decide⟩
    (prefixCache 9 1726) (prefixPartial 9 1726) = false := by
  decide +kernel

theorem node_context_9_1726_870598 : EJMOriginalGlobalDAGData.nodes 12 ⟨870598, by decide⟩ =
    .split (coordinate 9) (![⟨869958, by decide⟩,⟨870296, by decide⟩,⟨870483, by decide⟩,⟨870597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1726_870598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1726 ⟨870598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1726
    ⟨870598, by decide⟩ (by decide) (![⟨869958, by decide⟩,⟨870296, by decide⟩,⟨870483, by decide⟩,⟨870597, by decide⟩]) unmarked_context_9_1726_870598 node_context_9_1726_870598
  intro a
  fin_cases a
  · exact context_10_6904_869958
  · exact context_10_6905_870296
  · exact context_10_6906_870483
  · exact context_10_6907_870597

theorem selected_cut_33806 : selected 10 ⟨870620, by decide⟩
    (prefixPartial 11 27632) = some ⟨11, 2, 0, 870620, 27632, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_27632_870620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27632 ⟨870620, by decide⟩ :=
  accepted_of_selected 11 27632 ⟨870620, by decide⟩ ⟨11, 2, 0, 870620, 27632, 2125, 262144⟩
    (by decide) selected_cut_33806

theorem selected_cut_33807 : selected 10 ⟨870643, by decide⟩
    (prefixPartial 11 27633) = some ⟨11, 2, 0, 870643, 27633, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_27633_870643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27633 ⟨870643, by decide⟩ :=
  accepted_of_selected 11 27633 ⟨870643, by decide⟩ ⟨11, 2, 0, 870643, 27633, 2157, 262144⟩
    (by decide) selected_cut_33807

theorem selected_cut_33808 : selected 10 ⟨870663, by decide⟩
    (prefixPartial 11 27634) = some ⟨11, 2, 0, 870663, 27634, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_27634_870663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27634 ⟨870663, by decide⟩ :=
  accepted_of_selected 11 27634 ⟨870663, by decide⟩ ⟨11, 2, 0, 870663, 27634, 1717, 262144⟩
    (by decide) selected_cut_33808

theorem selected_cut_33809 : selected 10 ⟨870679, by decide⟩
    (prefixPartial 11 27635) = some ⟨11, 2, 0, 870679, 27635, 1333, 262144⟩ := by
  decide +kernel

theorem context_11_27635_870679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27635 ⟨870679, by decide⟩ :=
  accepted_of_selected 11 27635 ⟨870679, by decide⟩ ⟨11, 2, 0, 870679, 27635, 1333, 262144⟩
    (by decide) selected_cut_33809

theorem unmarked_context_10_6908_870680 : frontier 11 ⟨870680, by decide⟩
    (prefixCache 10 6908) (prefixPartial 10 6908) = false := by
  decide +kernel

theorem node_context_10_6908_870680 : EJMOriginalGlobalDAGData.nodes 11 ⟨870680, by decide⟩ =
    .split (coordinate 10) (![⟨870620, by decide⟩,⟨870643, by decide⟩,⟨870663, by decide⟩,⟨870679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6908_870680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6908 ⟨870680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6908
    ⟨870680, by decide⟩ (by decide) (![⟨870620, by decide⟩,⟨870643, by decide⟩,⟨870663, by decide⟩,⟨870679, by decide⟩]) unmarked_context_10_6908_870680 node_context_10_6908_870680
  intro a
  fin_cases a
  · exact context_11_27632_870620
  · exact context_11_27633_870643
  · exact context_11_27634_870663
  · exact context_11_27635_870679

theorem selected_cut_33810 : selected 10 ⟨870703, by decide⟩
    (prefixPartial 11 27636) = some ⟨11, 2, 0, 870703, 27636, 1961, 262144⟩ := by
  decide +kernel

theorem context_11_27636_870703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27636 ⟨870703, by decide⟩ :=
  accepted_of_selected 11 27636 ⟨870703, by decide⟩ ⟨11, 2, 0, 870703, 27636, 1961, 262144⟩
    (by decide) selected_cut_33810

theorem selected_cut_33811 : selected 10 ⟨870726, by decide⟩
    (prefixPartial 11 27637) = some ⟨11, 2, 0, 870726, 27637, 1737, 262144⟩ := by
  decide +kernel

theorem context_11_27637_870726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27637 ⟨870726, by decide⟩ :=
  accepted_of_selected 11 27637 ⟨870726, by decide⟩ ⟨11, 2, 0, 870726, 27637, 1737, 262144⟩
    (by decide) selected_cut_33811

theorem selected_cut_33812 : selected 10 ⟨870747, by decide⟩
    (prefixPartial 11 27638) = some ⟨11, 2, 0, 870747, 27638, 1361, 262144⟩ := by
  decide +kernel

theorem context_11_27638_870747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27638 ⟨870747, by decide⟩ :=
  accepted_of_selected 11 27638 ⟨870747, by decide⟩ ⟨11, 2, 0, 870747, 27638, 1361, 262144⟩
    (by decide) selected_cut_33812

theorem selected_cut_33813 : selected 10 ⟨870765, by decide⟩
    (prefixPartial 11 27639) = some ⟨11, 2, 0, 870765, 27639, 989, 262144⟩ := by
  decide +kernel

theorem context_11_27639_870765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27639 ⟨870765, by decide⟩ :=
  accepted_of_selected 11 27639 ⟨870765, by decide⟩ ⟨11, 2, 0, 870765, 27639, 989, 262144⟩
    (by decide) selected_cut_33813

theorem unmarked_context_10_6909_870766 : frontier 11 ⟨870766, by decide⟩
    (prefixCache 10 6909) (prefixPartial 10 6909) = false := by
  decide +kernel

theorem node_context_10_6909_870766 : EJMOriginalGlobalDAGData.nodes 11 ⟨870766, by decide⟩ =
    .split (coordinate 10) (![⟨870703, by decide⟩,⟨870726, by decide⟩,⟨870747, by decide⟩,⟨870765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6909_870766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6909 ⟨870766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6909
    ⟨870766, by decide⟩ (by decide) (![⟨870703, by decide⟩,⟨870726, by decide⟩,⟨870747, by decide⟩,⟨870765, by decide⟩]) unmarked_context_10_6909_870766 node_context_10_6909_870766
  intro a
  fin_cases a
  · exact context_11_27636_870703
  · exact context_11_27637_870726
  · exact context_11_27638_870747
  · exact context_11_27639_870765

theorem selected_cut_33814 : selected 11 ⟨870821, by decide⟩
    (prefixPartial 10 6910) = some ⟨10, 2, 0, 870821, 6910, 3477, 1048576⟩ := by
  decide +kernel

theorem context_10_6910_870821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6910 ⟨870821, by decide⟩ :=
  accepted_of_selected 10 6910 ⟨870821, by decide⟩ ⟨10, 2, 0, 870821, 6910, 3477, 1048576⟩
    (by decide) selected_cut_33814

theorem selected_cut_33815 : selected 11 ⟨870849, by decide⟩
    (prefixPartial 10 6911) = some ⟨10, 2, 0, 870849, 6911, 881, 1048576⟩ := by
  decide +kernel

theorem context_10_6911_870849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6911 ⟨870849, by decide⟩ :=
  accepted_of_selected 10 6911 ⟨870849, by decide⟩ ⟨10, 2, 0, 870849, 6911, 881, 1048576⟩
    (by decide) selected_cut_33815

theorem unmarked_context_9_1727_870850 : frontier 12 ⟨870850, by decide⟩
    (prefixCache 9 1727) (prefixPartial 9 1727) = false := by
  decide +kernel

theorem node_context_9_1727_870850 : EJMOriginalGlobalDAGData.nodes 12 ⟨870850, by decide⟩ =
    .split (coordinate 9) (![⟨870680, by decide⟩,⟨870766, by decide⟩,⟨870821, by decide⟩,⟨870849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1727_870850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1727 ⟨870850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1727
    ⟨870850, by decide⟩ (by decide) (![⟨870680, by decide⟩,⟨870766, by decide⟩,⟨870821, by decide⟩,⟨870849, by decide⟩]) unmarked_context_9_1727_870850 node_context_9_1727_870850
  intro a
  fin_cases a
  · exact context_10_6908_870680
  · exact context_10_6909_870766
  · exact context_10_6910_870821
  · exact context_10_6911_870849

theorem unmarked_context_8_431_870851 : frontier 13 ⟨870851, by decide⟩
    (prefixCache 8 431) (prefixPartial 8 431) = false := by
  decide +kernel

theorem node_context_8_431_870851 : EJMOriginalGlobalDAGData.nodes 13 ⟨870851, by decide⟩ =
    .split (coordinate 8) (![⟨866474, by decide⟩,⟨869567, by decide⟩,⟨870598, by decide⟩,⟨870850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_431_870851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 431 ⟨870851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 431
    ⟨870851, by decide⟩ (by decide) (![⟨866474, by decide⟩,⟨869567, by decide⟩,⟨870598, by decide⟩,⟨870850, by decide⟩]) unmarked_context_8_431_870851 node_context_8_431_870851
  intro a
  fin_cases a
  · exact context_9_1724_866474
  · exact context_9_1725_869567
  · exact context_9_1726_870598
  · exact context_9_1727_870850

theorem unmarked_context_7_107_870852 : frontier 14 ⟨870852, by decide⟩
    (prefixCache 7 107) (prefixPartial 7 107) = false := by
  decide +kernel

theorem node_context_7_107_870852 : EJMOriginalGlobalDAGData.nodes 14 ⟨870852, by decide⟩ =
    .split (coordinate 7) (![⟨844995, by decide⟩,⟨853643, by decide⟩,⟨861761, by decide⟩,⟨870851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_107_870852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 107 ⟨870852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 107
    ⟨870852, by decide⟩ (by decide) (![⟨844995, by decide⟩,⟨853643, by decide⟩,⟨861761, by decide⟩,⟨870851, by decide⟩]) unmarked_context_7_107_870852 node_context_7_107_870852
  intro a
  fin_cases a
  · exact context_8_428_844995
  · exact context_8_429_853643
  · exact context_8_430_861761
  · exact context_8_431_870851

theorem unmarked_context_6_26_870853 : frontier 15 ⟨870853, by decide⟩
    (prefixCache 6 26) (prefixPartial 6 26) = false := by
  decide +kernel

theorem node_context_6_26_870853 : EJMOriginalGlobalDAGData.nodes 15 ⟨870853, by decide⟩ =
    .split (coordinate 6) (![⟨676732, by decide⟩,⟨836035, by decide⟩,⟨676732, by decide⟩,⟨870852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_26_870853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 26 ⟨870853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 26
    ⟨870853, by decide⟩ (by decide) (![⟨676732, by decide⟩,⟨836035, by decide⟩,⟨676732, by decide⟩,⟨870852, by decide⟩]) unmarked_context_6_26_870853 node_context_6_26_870853
  intro a
  fin_cases a
  · exact context_7_104_676732
  · exact context_7_105_836035
  · exact context_7_106_676732
  · exact context_7_107_870852

theorem selected_cut_33816 : selected 14 ⟨870854, by decide⟩
    (prefixPartial 7 108) = some ⟨7, 1, 0, 870854, 108, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_108_870854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 108 ⟨870854, by decide⟩ :=
  accepted_of_selected 7 108 ⟨870854, by decide⟩ ⟨7, 1, 0, 870854, 108, 1, 67108864⟩
    (by decide) selected_cut_33816

theorem selected_cut_33817 : selected 14 ⟨870855, by decide⟩
    (prefixPartial 7 109) = some ⟨7, 1, 0, 870855, 109, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_109_870855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 109 ⟨870855, by decide⟩ :=
  accepted_of_selected 7 109 ⟨870855, by decide⟩ ⟨7, 1, 0, 870855, 109, 1, 67108864⟩
    (by decide) selected_cut_33817

theorem selected_cut_33818 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 28160) = some ⟨11, 1, 0, 434745, 28160, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28160_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28160 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 28160 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 28160, 1, 262144⟩
    (by decide) selected_cut_33818

theorem selected_cut_33819 : selected 10 ⟨871047, by decide⟩
    (prefixPartial 11 28161) = some ⟨11, 2, 0, 871047, 28161, 2949, 262144⟩ := by
  decide +kernel

theorem context_11_28161_871047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28161 ⟨871047, by decide⟩ :=
  accepted_of_selected 11 28161 ⟨871047, by decide⟩ ⟨11, 2, 0, 871047, 28161, 2949, 262144⟩
    (by decide) selected_cut_33819

theorem selected_cut_33820 : selected 10 ⟨764169, by decide⟩
    (prefixPartial 11 28162) = some ⟨11, 1, 0, 764169, 28162, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28162_764169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28162 ⟨764169, by decide⟩ :=
  accepted_of_selected 11 28162 ⟨764169, by decide⟩ ⟨11, 1, 0, 764169, 28162, 1, 262144⟩
    (by decide) selected_cut_33820

theorem selected_cut_33821 : selected 9 ⟨870856, by decide⟩
    (prefixPartial 12 112652) = some ⟨12, 1, 0, 870856, 112652, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112652_870856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112652 ⟨870856, by decide⟩ :=
  accepted_of_selected 12 112652 ⟨870856, by decide⟩ ⟨12, 1, 0, 870856, 112652, 1, 65536⟩
    (by decide) selected_cut_33821

theorem selected_cut_33822 : selected 8 ⟨871184, by decide⟩
    (prefixPartial 13 450612) = some ⟨13, 2, 0, 871184, 450612, 3529, 16384⟩ := by
  decide +kernel

theorem context_13_450612_871184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450612 ⟨871184, by decide⟩ :=
  accepted_of_selected 13 450612 ⟨871184, by decide⟩ ⟨13, 2, 0, 871184, 450612, 3529, 16384⟩
    (by decide) selected_cut_33822

theorem selected_cut_33823 : selected 8 ⟨871290, by decide⟩
    (prefixPartial 13 450613) = some ⟨13, 2, 0, 871290, 450613, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_450613_871290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450613 ⟨871290, by decide⟩ :=
  accepted_of_selected 13 450613 ⟨871290, by decide⟩ ⟨13, 2, 0, 871290, 450613, 2233, 16384⟩
    (by decide) selected_cut_33823

theorem selected_cut_33824 : selected 8 ⟨871348, by decide⟩
    (prefixPartial 13 450614) = some ⟨13, 2, 0, 871348, 450614, 637, 16384⟩ := by
  decide +kernel

theorem context_13_450614_871348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450614 ⟨871348, by decide⟩ :=
  accepted_of_selected 13 450614 ⟨871348, by decide⟩ ⟨13, 2, 0, 871348, 450614, 637, 16384⟩
    (by decide) selected_cut_33824

theorem selected_cut_33825 : selected 8 ⟨871372, by decide⟩
    (prefixPartial 13 450615) = some ⟨13, 2, 0, 871372, 450615, 165, 16384⟩ := by
  decide +kernel

theorem context_13_450615_871372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450615 ⟨871372, by decide⟩ :=
  accepted_of_selected 13 450615 ⟨871372, by decide⟩ ⟨13, 2, 0, 871372, 450615, 165, 16384⟩
    (by decide) selected_cut_33825

theorem unmarked_context_12_112653_871373 : frontier 9 ⟨871373, by decide⟩
    (prefixCache 12 112653) (prefixPartial 12 112653) = false := by
  decide +kernel

theorem node_context_12_112653_871373 : EJMOriginalGlobalDAGData.nodes 9 ⟨871373, by decide⟩ =
    .split (coordinate 12) (![⟨871184, by decide⟩,⟨871290, by decide⟩,⟨871348, by decide⟩,⟨871372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112653_871373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112653 ⟨871373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112653
    ⟨871373, by decide⟩ (by decide) (![⟨871184, by decide⟩,⟨871290, by decide⟩,⟨871348, by decide⟩,⟨871372, by decide⟩]) unmarked_context_12_112653_871373 node_context_12_112653_871373
  intro a
  fin_cases a
  · exact context_13_450612_871184
  · exact context_13_450613_871290
  · exact context_13_450614_871348
  · exact context_13_450615_871372

theorem selected_cut_33826 : selected 9 ⟨870856, by decide⟩
    (prefixPartial 12 112654) = some ⟨12, 1, 0, 870856, 112654, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112654_870856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112654 ⟨870856, by decide⟩ :=
  accepted_of_selected 12 112654 ⟨870856, by decide⟩ ⟨12, 1, 0, 870856, 112654, 1, 65536⟩
    (by decide) selected_cut_33826

theorem selected_cut_33827 : selected 9 ⟨870856, by decide⟩
    (prefixPartial 12 112655) = some ⟨12, 1, 0, 870856, 112655, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112655_870856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112655 ⟨870856, by decide⟩ :=
  accepted_of_selected 12 112655 ⟨870856, by decide⟩ ⟨12, 1, 0, 870856, 112655, 1, 65536⟩
    (by decide) selected_cut_33827

theorem unmarked_context_11_28163_871374 : frontier 10 ⟨871374, by decide⟩
    (prefixCache 11 28163) (prefixPartial 11 28163) = false := by
  decide +kernel

theorem node_context_11_28163_871374 : EJMOriginalGlobalDAGData.nodes 10 ⟨871374, by decide⟩ =
    .split (coordinate 11) (![⟨870856, by decide⟩,⟨871373, by decide⟩,⟨870856, by decide⟩,⟨870856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28163_871374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28163 ⟨871374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28163
    ⟨871374, by decide⟩ (by decide) (![⟨870856, by decide⟩,⟨871373, by decide⟩,⟨870856, by decide⟩,⟨870856, by decide⟩]) unmarked_context_11_28163_871374 node_context_11_28163_871374
  intro a
  fin_cases a
  · exact context_12_112652_870856
  · exact context_12_112653_871373
  · exact context_12_112654_870856
  · exact context_12_112655_870856

theorem unmarked_context_10_7040_871375 : frontier 11 ⟨871375, by decide⟩
    (prefixCache 10 7040) (prefixPartial 10 7040) = false := by
  decide +kernel

theorem node_context_10_7040_871375 : EJMOriginalGlobalDAGData.nodes 11 ⟨871375, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨871047, by decide⟩,⟨764169, by decide⟩,⟨871374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7040_871375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7040 ⟨871375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7040
    ⟨871375, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨871047, by decide⟩,⟨764169, by decide⟩,⟨871374, by decide⟩]) unmarked_context_10_7040_871375 node_context_10_7040_871375
  intro a
  fin_cases a
  · exact context_11_28160_434745
  · exact context_11_28161_871047
  · exact context_11_28162_764169
  · exact context_11_28163_871374

theorem selected_cut_33828 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 112656) = some ⟨12, 1, 0, 307381, 112656, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112656_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112656 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 112656 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 112656, 1, 65536⟩
    (by decide) selected_cut_33828

theorem selected_cut_33829 : selected 8 ⟨871416, by decide⟩
    (prefixPartial 13 450628) = some ⟨13, 2, 0, 871416, 450628, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_450628_871416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450628 ⟨871416, by decide⟩ :=
  accepted_of_selected 13 450628 ⟨871416, by decide⟩ ⟨13, 2, 0, 871416, 450628, 2185, 16384⟩
    (by decide) selected_cut_33829

theorem selected_cut_33830 : selected 8 ⟨871453, by decide⟩
    (prefixPartial 13 450629) = some ⟨13, 2, 0, 871453, 450629, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_450629_871453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450629 ⟨871453, by decide⟩ :=
  accepted_of_selected 13 450629 ⟨871453, by decide⟩ ⟨13, 2, 0, 871453, 450629, 2273, 16384⟩
    (by decide) selected_cut_33830

theorem selected_cut_33831 : selected 8 ⟨871487, by decide⟩
    (prefixPartial 13 450630) = some ⟨13, 2, 0, 871487, 450630, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_450630_871487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450630 ⟨871487, by decide⟩ :=
  accepted_of_selected 13 450630 ⟨871487, by decide⟩ ⟨13, 2, 0, 871487, 450630, 1277, 16384⟩
    (by decide) selected_cut_33831

theorem selected_cut_33832 : selected 8 ⟨871522, by decide⟩
    (prefixPartial 13 450631) = some ⟨13, 2, 0, 871522, 450631, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_450631_871522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450631 ⟨871522, by decide⟩ :=
  accepted_of_selected 13 450631 ⟨871522, by decide⟩ ⟨13, 2, 0, 871522, 450631, 1049, 16384⟩
    (by decide) selected_cut_33832

theorem unmarked_context_12_112657_871523 : frontier 9 ⟨871523, by decide⟩
    (prefixCache 12 112657) (prefixPartial 12 112657) = false := by
  decide +kernel

theorem node_context_12_112657_871523 : EJMOriginalGlobalDAGData.nodes 9 ⟨871523, by decide⟩ =
    .split (coordinate 12) (![⟨871416, by decide⟩,⟨871453, by decide⟩,⟨871487, by decide⟩,⟨871522, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112657_871523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112657 ⟨871523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112657
    ⟨871523, by decide⟩ (by decide) (![⟨871416, by decide⟩,⟨871453, by decide⟩,⟨871487, by decide⟩,⟨871522, by decide⟩]) unmarked_context_12_112657_871523 node_context_12_112657_871523
  intro a
  fin_cases a
  · exact context_13_450628_871416
  · exact context_13_450629_871453
  · exact context_13_450630_871487
  · exact context_13_450631_871522

theorem selected_cut_33833 : selected 8 ⟨871554, by decide⟩
    (prefixPartial 13 450632) = some ⟨13, 2, 0, 871554, 450632, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_450632_871554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450632 ⟨871554, by decide⟩ :=
  accepted_of_selected 13 450632 ⟨871554, by decide⟩ ⟨13, 2, 0, 871554, 450632, 1709, 16384⟩
    (by decide) selected_cut_33833

theorem selected_cut_33834 : selected 8 ⟨871576, by decide⟩
    (prefixPartial 13 450633) = some ⟨13, 2, 0, 871576, 450633, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_450633_871576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450633 ⟨871576, by decide⟩ :=
  accepted_of_selected 13 450633 ⟨871576, by decide⟩ ⟨13, 2, 0, 871576, 450633, 1749, 16384⟩
    (by decide) selected_cut_33834

theorem selected_cut_33835 : selected 8 ⟨871594, by decide⟩
    (prefixPartial 13 450634) = some ⟨13, 2, 0, 871594, 450634, 997, 16384⟩ := by
  decide +kernel

theorem context_13_450634_871594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450634 ⟨871594, by decide⟩ :=
  accepted_of_selected 13 450634 ⟨871594, by decide⟩ ⟨13, 2, 0, 871594, 450634, 997, 16384⟩
    (by decide) selected_cut_33835

theorem selected_cut_33836 : selected 8 ⟨871607, by decide⟩
    (prefixPartial 13 450635) = some ⟨13, 2, 0, 871607, 450635, 897, 16384⟩ := by
  decide +kernel

theorem context_13_450635_871607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450635 ⟨871607, by decide⟩ :=
  accepted_of_selected 13 450635 ⟨871607, by decide⟩ ⟨13, 2, 0, 871607, 450635, 897, 16384⟩
    (by decide) selected_cut_33836

theorem unmarked_context_12_112658_871608 : frontier 9 ⟨871608, by decide⟩
    (prefixCache 12 112658) (prefixPartial 12 112658) = false := by
  decide +kernel

theorem node_context_12_112658_871608 : EJMOriginalGlobalDAGData.nodes 9 ⟨871608, by decide⟩ =
    .split (coordinate 12) (![⟨871554, by decide⟩,⟨871576, by decide⟩,⟨871594, by decide⟩,⟨871607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112658_871608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112658 ⟨871608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112658
    ⟨871608, by decide⟩ (by decide) (![⟨871554, by decide⟩,⟨871576, by decide⟩,⟨871594, by decide⟩,⟨871607, by decide⟩]) unmarked_context_12_112658_871608 node_context_12_112658_871608
  intro a
  fin_cases a
  · exact context_13_450632_871554
  · exact context_13_450633_871576
  · exact context_13_450634_871594
  · exact context_13_450635_871607

theorem selected_cut_33837 : selected 8 ⟨871642, by decide⟩
    (prefixPartial 13 450636) = some ⟨13, 2, 0, 871642, 450636, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_450636_871642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450636 ⟨871642, by decide⟩ :=
  accepted_of_selected 13 450636 ⟨871642, by decide⟩ ⟨13, 2, 0, 871642, 450636, 1725, 16384⟩
    (by decide) selected_cut_33837

theorem selected_cut_33838 : selected 8 ⟨871671, by decide⟩
    (prefixPartial 13 450637) = some ⟨13, 2, 0, 871671, 450637, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_450637_871671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450637 ⟨871671, by decide⟩ :=
  accepted_of_selected 13 450637 ⟨871671, by decide⟩ ⟨13, 2, 0, 871671, 450637, 2061, 16384⟩
    (by decide) selected_cut_33838

theorem selected_cut_33839 : selected 8 ⟨871688, by decide⟩
    (prefixPartial 13 450638) = some ⟨13, 2, 0, 871688, 450638, 965, 16384⟩ := by
  decide +kernel

theorem context_13_450638_871688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450638 ⟨871688, by decide⟩ :=
  accepted_of_selected 13 450638 ⟨871688, by decide⟩ ⟨13, 2, 0, 871688, 450638, 965, 16384⟩
    (by decide) selected_cut_33839

theorem selected_cut_33840 : selected 8 ⟨871697, by decide⟩
    (prefixPartial 13 450639) = some ⟨13, 2, 0, 871697, 450639, 697, 16384⟩ := by
  decide +kernel

theorem context_13_450639_871697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450639 ⟨871697, by decide⟩ :=
  accepted_of_selected 13 450639 ⟨871697, by decide⟩ ⟨13, 2, 0, 871697, 450639, 697, 16384⟩
    (by decide) selected_cut_33840

theorem unmarked_context_12_112659_871698 : frontier 9 ⟨871698, by decide⟩
    (prefixCache 12 112659) (prefixPartial 12 112659) = false := by
  decide +kernel

theorem node_context_12_112659_871698 : EJMOriginalGlobalDAGData.nodes 9 ⟨871698, by decide⟩ =
    .split (coordinate 12) (![⟨871642, by decide⟩,⟨871671, by decide⟩,⟨871688, by decide⟩,⟨871697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112659_871698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112659 ⟨871698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112659
    ⟨871698, by decide⟩ (by decide) (![⟨871642, by decide⟩,⟨871671, by decide⟩,⟨871688, by decide⟩,⟨871697, by decide⟩]) unmarked_context_12_112659_871698 node_context_12_112659_871698
  intro a
  fin_cases a
  · exact context_13_450636_871642
  · exact context_13_450637_871671
  · exact context_13_450638_871688
  · exact context_13_450639_871697

theorem unmarked_context_11_28164_871699 : frontier 10 ⟨871699, by decide⟩
    (prefixCache 11 28164) (prefixPartial 11 28164) = false := by
  decide +kernel

theorem node_context_11_28164_871699 : EJMOriginalGlobalDAGData.nodes 10 ⟨871699, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨871523, by decide⟩,⟨871608, by decide⟩,⟨871698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28164_871699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28164 ⟨871699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28164
    ⟨871699, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨871523, by decide⟩,⟨871608, by decide⟩,⟨871698, by decide⟩]) unmarked_context_11_28164_871699 node_context_11_28164_871699
  intro a
  fin_cases a
  · exact context_12_112656_307381
  · exact context_12_112657_871523
  · exact context_12_112658_871608
  · exact context_12_112659_871698

theorem selected_cut_33841 : selected 8 ⟨871720, by decide⟩
    (prefixPartial 13 450640) = some ⟨13, 2, 0, 871720, 450640, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_450640_871720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450640 ⟨871720, by decide⟩ :=
  accepted_of_selected 13 450640 ⟨871720, by decide⟩ ⟨13, 2, 0, 871720, 450640, 1173, 16384⟩
    (by decide) selected_cut_33841

theorem selected_cut_33842 : selected 8 ⟨871746, by decide⟩
    (prefixPartial 13 450641) = some ⟨13, 2, 0, 871746, 450641, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_450641_871746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450641 ⟨871746, by decide⟩ :=
  accepted_of_selected 13 450641 ⟨871746, by decide⟩ ⟨13, 2, 0, 871746, 450641, 1773, 16384⟩
    (by decide) selected_cut_33842

theorem selected_cut_33843 : selected 8 ⟨871769, by decide⟩
    (prefixPartial 13 450642) = some ⟨13, 2, 0, 871769, 450642, 917, 16384⟩ := by
  decide +kernel

theorem context_13_450642_871769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450642 ⟨871769, by decide⟩ :=
  accepted_of_selected 13 450642 ⟨871769, by decide⟩ ⟨13, 2, 0, 871769, 450642, 917, 16384⟩
    (by decide) selected_cut_33843

theorem selected_cut_33844 : selected 8 ⟨871781, by decide⟩
    (prefixPartial 13 450643) = some ⟨13, 2, 0, 871781, 450643, 757, 16384⟩ := by
  decide +kernel

theorem context_13_450643_871781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450643 ⟨871781, by decide⟩ :=
  accepted_of_selected 13 450643 ⟨871781, by decide⟩ ⟨13, 2, 0, 871781, 450643, 757, 16384⟩
    (by decide) selected_cut_33844

theorem unmarked_context_12_112660_871782 : frontier 9 ⟨871782, by decide⟩
    (prefixCache 12 112660) (prefixPartial 12 112660) = false := by
  decide +kernel

theorem node_context_12_112660_871782 : EJMOriginalGlobalDAGData.nodes 9 ⟨871782, by decide⟩ =
    .split (coordinate 12) (![⟨871720, by decide⟩,⟨871746, by decide⟩,⟨871769, by decide⟩,⟨871781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112660_871782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112660 ⟨871782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112660
    ⟨871782, by decide⟩ (by decide) (![⟨871720, by decide⟩,⟨871746, by decide⟩,⟨871769, by decide⟩,⟨871781, by decide⟩]) unmarked_context_12_112660_871782 node_context_12_112660_871782
  intro a
  fin_cases a
  · exact context_13_450640_871720
  · exact context_13_450641_871746
  · exact context_13_450642_871769
  · exact context_13_450643_871781

theorem selected_cut_33845 : selected 8 ⟨871820, by decide⟩
    (prefixPartial 13 450644) = some ⟨13, 2, 0, 871820, 450644, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_450644_871820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450644 ⟨871820, by decide⟩ :=
  accepted_of_selected 13 450644 ⟨871820, by decide⟩ ⟨13, 2, 0, 871820, 450644, 1857, 16384⟩
    (by decide) selected_cut_33845

theorem selected_cut_33846 : selected 8 ⟨871854, by decide⟩
    (prefixPartial 13 450645) = some ⟨13, 2, 0, 871854, 450645, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_450645_871854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450645 ⟨871854, by decide⟩ :=
  accepted_of_selected 13 450645 ⟨871854, by decide⟩ ⟨13, 2, 0, 871854, 450645, 2037, 16384⟩
    (by decide) selected_cut_33846

theorem selected_cut_33847 : selected 8 ⟨871881, by decide⟩
    (prefixPartial 13 450646) = some ⟨13, 2, 0, 871881, 450646, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_450646_871881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450646 ⟨871881, by decide⟩ :=
  accepted_of_selected 13 450646 ⟨871881, by decide⟩ ⟨13, 2, 0, 871881, 450646, 1285, 16384⟩
    (by decide) selected_cut_33847

theorem selected_cut_33848 : selected 8 ⟨871899, by decide⟩
    (prefixPartial 13 450647) = some ⟨13, 2, 0, 871899, 450647, 989, 16384⟩ := by
  decide +kernel

theorem context_13_450647_871899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450647 ⟨871899, by decide⟩ :=
  accepted_of_selected 13 450647 ⟨871899, by decide⟩ ⟨13, 2, 0, 871899, 450647, 989, 16384⟩
    (by decide) selected_cut_33848

theorem unmarked_context_12_112661_871900 : frontier 9 ⟨871900, by decide⟩
    (prefixCache 12 112661) (prefixPartial 12 112661) = false := by
  decide +kernel

theorem node_context_12_112661_871900 : EJMOriginalGlobalDAGData.nodes 9 ⟨871900, by decide⟩ =
    .split (coordinate 12) (![⟨871820, by decide⟩,⟨871854, by decide⟩,⟨871881, by decide⟩,⟨871899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112661_871900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112661 ⟨871900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112661
    ⟨871900, by decide⟩ (by decide) (![⟨871820, by decide⟩,⟨871854, by decide⟩,⟨871881, by decide⟩,⟨871899, by decide⟩]) unmarked_context_12_112661_871900 node_context_12_112661_871900
  intro a
  fin_cases a
  · exact context_13_450644_871820
  · exact context_13_450645_871854
  · exact context_13_450646_871881
  · exact context_13_450647_871899

theorem selected_cut_33849 : selected 8 ⟨871934, by decide⟩
    (prefixPartial 13 450648) = some ⟨13, 2, 0, 871934, 450648, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_450648_871934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450648 ⟨871934, by decide⟩ :=
  accepted_of_selected 13 450648 ⟨871934, by decide⟩ ⟨13, 2, 0, 871934, 450648, 1749, 16384⟩
    (by decide) selected_cut_33849

theorem selected_cut_33850 : selected 8 ⟨871959, by decide⟩
    (prefixPartial 13 450649) = some ⟨13, 2, 0, 871959, 450649, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_450649_871959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450649 ⟨871959, by decide⟩ :=
  accepted_of_selected 13 450649 ⟨871959, by decide⟩ ⟨13, 2, 0, 871959, 450649, 1729, 16384⟩
    (by decide) selected_cut_33850

theorem selected_cut_33851 : selected 8 ⟨871980, by decide⟩
    (prefixPartial 13 450650) = some ⟨13, 2, 0, 871980, 450650, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_450650_871980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450650 ⟨871980, by decide⟩ :=
  accepted_of_selected 13 450650 ⟨871980, by decide⟩ ⟨13, 2, 0, 871980, 450650, 1121, 16384⟩
    (by decide) selected_cut_33851

theorem selected_cut_33852 : selected 8 ⟨871990, by decide⟩
    (prefixPartial 13 450651) = some ⟨13, 2, 0, 871990, 450651, 865, 16384⟩ := by
  decide +kernel

theorem context_13_450651_871990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450651 ⟨871990, by decide⟩ :=
  accepted_of_selected 13 450651 ⟨871990, by decide⟩ ⟨13, 2, 0, 871990, 450651, 865, 16384⟩
    (by decide) selected_cut_33852

theorem unmarked_context_12_112662_871991 : frontier 9 ⟨871991, by decide⟩
    (prefixCache 12 112662) (prefixPartial 12 112662) = false := by
  decide +kernel

theorem node_context_12_112662_871991 : EJMOriginalGlobalDAGData.nodes 9 ⟨871991, by decide⟩ =
    .split (coordinate 12) (![⟨871934, by decide⟩,⟨871959, by decide⟩,⟨871980, by decide⟩,⟨871990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112662_871991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112662 ⟨871991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112662
    ⟨871991, by decide⟩ (by decide) (![⟨871934, by decide⟩,⟨871959, by decide⟩,⟨871980, by decide⟩,⟨871990, by decide⟩]) unmarked_context_12_112662_871991 node_context_12_112662_871991
  intro a
  fin_cases a
  · exact context_13_450648_871934
  · exact context_13_450649_871959
  · exact context_13_450650_871980
  · exact context_13_450651_871990

theorem selected_cut_33853 : selected 8 ⟨872019, by decide⟩
    (prefixPartial 13 450652) = some ⟨13, 2, 0, 872019, 450652, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_450652_872019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450652 ⟨872019, by decide⟩ :=
  accepted_of_selected 13 450652 ⟨872019, by decide⟩ ⟨13, 2, 0, 872019, 450652, 1821, 16384⟩
    (by decide) selected_cut_33853

theorem selected_cut_33854 : selected 8 ⟨872045, by decide⟩
    (prefixPartial 13 450653) = some ⟨13, 2, 0, 872045, 450653, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_450653_872045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450653 ⟨872045, by decide⟩ :=
  accepted_of_selected 13 450653 ⟨872045, by decide⟩ ⟨13, 2, 0, 872045, 450653, 2081, 16384⟩
    (by decide) selected_cut_33854

theorem selected_cut_33855 : selected 8 ⟨872068, by decide⟩
    (prefixPartial 13 450654) = some ⟨13, 2, 0, 872068, 450654, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_450654_872068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450654 ⟨872068, by decide⟩ :=
  accepted_of_selected 13 450654 ⟨872068, by decide⟩ ⟨13, 2, 0, 872068, 450654, 1073, 16384⟩
    (by decide) selected_cut_33855

theorem selected_cut_33856 : selected 8 ⟨872077, by decide⟩
    (prefixPartial 13 450655) = some ⟨13, 2, 0, 872077, 450655, 717, 16384⟩ := by
  decide +kernel

theorem context_13_450655_872077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450655 ⟨872077, by decide⟩ :=
  accepted_of_selected 13 450655 ⟨872077, by decide⟩ ⟨13, 2, 0, 872077, 450655, 717, 16384⟩
    (by decide) selected_cut_33856

theorem unmarked_context_12_112663_872078 : frontier 9 ⟨872078, by decide⟩
    (prefixCache 12 112663) (prefixPartial 12 112663) = false := by
  decide +kernel

theorem node_context_12_112663_872078 : EJMOriginalGlobalDAGData.nodes 9 ⟨872078, by decide⟩ =
    .split (coordinate 12) (![⟨872019, by decide⟩,⟨872045, by decide⟩,⟨872068, by decide⟩,⟨872077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112663_872078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112663 ⟨872078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112663
    ⟨872078, by decide⟩ (by decide) (![⟨872019, by decide⟩,⟨872045, by decide⟩,⟨872068, by decide⟩,⟨872077, by decide⟩]) unmarked_context_12_112663_872078 node_context_12_112663_872078
  intro a
  fin_cases a
  · exact context_13_450652_872019
  · exact context_13_450653_872045
  · exact context_13_450654_872068
  · exact context_13_450655_872077

theorem unmarked_context_11_28165_872079 : frontier 10 ⟨872079, by decide⟩
    (prefixCache 11 28165) (prefixPartial 11 28165) = false := by
  decide +kernel

theorem node_context_11_28165_872079 : EJMOriginalGlobalDAGData.nodes 10 ⟨872079, by decide⟩ =
    .split (coordinate 11) (![⟨871782, by decide⟩,⟨871900, by decide⟩,⟨871991, by decide⟩,⟨872078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28165_872079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28165 ⟨872079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28165
    ⟨872079, by decide⟩ (by decide) (![⟨871782, by decide⟩,⟨871900, by decide⟩,⟨871991, by decide⟩,⟨872078, by decide⟩]) unmarked_context_11_28165_872079 node_context_11_28165_872079
  intro a
  fin_cases a
  · exact context_12_112660_871782
  · exact context_12_112661_871900
  · exact context_12_112662_871991
  · exact context_12_112663_872078

theorem selected_cut_33857 : selected 8 ⟨872096, by decide⟩
    (prefixPartial 13 450656) = some ⟨13, 2, 0, 872096, 450656, 985, 16384⟩ := by
  decide +kernel

theorem context_13_450656_872096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450656 ⟨872096, by decide⟩ :=
  accepted_of_selected 13 450656 ⟨872096, by decide⟩ ⟨13, 2, 0, 872096, 450656, 985, 16384⟩
    (by decide) selected_cut_33857

theorem selected_cut_33858 : selected 8 ⟨872124, by decide⟩
    (prefixPartial 13 450657) = some ⟨13, 2, 0, 872124, 450657, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_450657_872124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450657 ⟨872124, by decide⟩ :=
  accepted_of_selected 13 450657 ⟨872124, by decide⟩ ⟨13, 2, 0, 872124, 450657, 1901, 16384⟩
    (by decide) selected_cut_33858

theorem selected_cut_33859 : selected 8 ⟨872139, by decide⟩
    (prefixPartial 13 450658) = some ⟨13, 2, 0, 872139, 450658, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_450658_872139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450658 ⟨872139, by decide⟩ :=
  accepted_of_selected 13 450658 ⟨872139, by decide⟩ ⟨13, 2, 0, 872139, 450658, 1005, 16384⟩
    (by decide) selected_cut_33859

theorem selected_cut_33860 : selected 8 ⟨872147, by decide⟩
    (prefixPartial 13 450659) = some ⟨13, 2, 0, 872147, 450659, 637, 16384⟩ := by
  decide +kernel

theorem context_13_450659_872147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450659 ⟨872147, by decide⟩ :=
  accepted_of_selected 13 450659 ⟨872147, by decide⟩ ⟨13, 2, 0, 872147, 450659, 637, 16384⟩
    (by decide) selected_cut_33860

theorem unmarked_context_12_112664_872148 : frontier 9 ⟨872148, by decide⟩
    (prefixCache 12 112664) (prefixPartial 12 112664) = false := by
  decide +kernel

theorem node_context_12_112664_872148 : EJMOriginalGlobalDAGData.nodes 9 ⟨872148, by decide⟩ =
    .split (coordinate 12) (![⟨872096, by decide⟩,⟨872124, by decide⟩,⟨872139, by decide⟩,⟨872147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112664_872148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112664 ⟨872148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112664
    ⟨872148, by decide⟩ (by decide) (![⟨872096, by decide⟩,⟨872124, by decide⟩,⟨872139, by decide⟩,⟨872147, by decide⟩]) unmarked_context_12_112664_872148 node_context_12_112664_872148
  intro a
  fin_cases a
  · exact context_13_450656_872096
  · exact context_13_450657_872124
  · exact context_13_450658_872139
  · exact context_13_450659_872147

theorem selected_cut_33861 : selected 8 ⟨872180, by decide⟩
    (prefixPartial 13 450660) = some ⟨13, 2, 0, 872180, 450660, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_450660_872180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450660 ⟨872180, by decide⟩ :=
  accepted_of_selected 13 450660 ⟨872180, by decide⟩ ⟨13, 2, 0, 872180, 450660, 1709, 16384⟩
    (by decide) selected_cut_33861

theorem selected_cut_33862 : selected 8 ⟨872225, by decide⟩
    (prefixPartial 13 450661) = some ⟨13, 2, 0, 872225, 450661, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_450661_872225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450661 ⟨872225, by decide⟩ :=
  accepted_of_selected 13 450661 ⟨872225, by decide⟩ ⟨13, 2, 0, 872225, 450661, 2553, 16384⟩
    (by decide) selected_cut_33862

theorem selected_cut_33863 : selected 8 ⟨872257, by decide⟩
    (prefixPartial 13 450662) = some ⟨13, 2, 0, 872257, 450662, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_450662_872257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450662 ⟨872257, by decide⟩ :=
  accepted_of_selected 13 450662 ⟨872257, by decide⟩ ⟨13, 2, 0, 872257, 450662, 1417, 16384⟩
    (by decide) selected_cut_33863

theorem selected_cut_33864 : selected 8 ⟨872276, by decide⟩
    (prefixPartial 13 450663) = some ⟨13, 2, 0, 872276, 450663, 805, 16384⟩ := by
  decide +kernel

theorem context_13_450663_872276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450663 ⟨872276, by decide⟩ :=
  accepted_of_selected 13 450663 ⟨872276, by decide⟩ ⟨13, 2, 0, 872276, 450663, 805, 16384⟩
    (by decide) selected_cut_33864

theorem unmarked_context_12_112665_872277 : frontier 9 ⟨872277, by decide⟩
    (prefixCache 12 112665) (prefixPartial 12 112665) = false := by
  decide +kernel

theorem node_context_12_112665_872277 : EJMOriginalGlobalDAGData.nodes 9 ⟨872277, by decide⟩ =
    .split (coordinate 12) (![⟨872180, by decide⟩,⟨872225, by decide⟩,⟨872257, by decide⟩,⟨872276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112665_872277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112665 ⟨872277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112665
    ⟨872277, by decide⟩ (by decide) (![⟨872180, by decide⟩,⟨872225, by decide⟩,⟨872257, by decide⟩,⟨872276, by decide⟩]) unmarked_context_12_112665_872277 node_context_12_112665_872277
  intro a
  fin_cases a
  · exact context_13_450660_872180
  · exact context_13_450661_872225
  · exact context_13_450662_872257
  · exact context_13_450663_872276

theorem selected_cut_33865 : selected 8 ⟨872308, by decide⟩
    (prefixPartial 13 450664) = some ⟨13, 2, 0, 872308, 450664, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_450664_872308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450664 ⟨872308, by decide⟩ :=
  accepted_of_selected 13 450664 ⟨872308, by decide⟩ ⟨13, 2, 0, 872308, 450664, 1261, 16384⟩
    (by decide) selected_cut_33865

theorem selected_cut_33866 : selected 8 ⟨872333, by decide⟩
    (prefixPartial 13 450665) = some ⟨13, 2, 0, 872333, 450665, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_450665_872333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450665 ⟨872333, by decide⟩ :=
  accepted_of_selected 13 450665 ⟨872333, by decide⟩ ⟨13, 2, 0, 872333, 450665, 1805, 16384⟩
    (by decide) selected_cut_33866

theorem selected_cut_33867 : selected 8 ⟨872350, by decide⟩
    (prefixPartial 13 450666) = some ⟨13, 2, 0, 872350, 450666, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_450666_872350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450666 ⟨872350, by decide⟩ :=
  accepted_of_selected 13 450666 ⟨872350, by decide⟩ ⟨13, 2, 0, 872350, 450666, 1081, 16384⟩
    (by decide) selected_cut_33867

theorem selected_cut_33868 : selected 8 ⟨872362, by decide⟩
    (prefixPartial 13 450667) = some ⟨13, 2, 0, 872362, 450667, 677, 16384⟩ := by
  decide +kernel

theorem context_13_450667_872362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450667 ⟨872362, by decide⟩ :=
  accepted_of_selected 13 450667 ⟨872362, by decide⟩ ⟨13, 2, 0, 872362, 450667, 677, 16384⟩
    (by decide) selected_cut_33868

theorem unmarked_context_12_112666_872363 : frontier 9 ⟨872363, by decide⟩
    (prefixCache 12 112666) (prefixPartial 12 112666) = false := by
  decide +kernel

theorem node_context_12_112666_872363 : EJMOriginalGlobalDAGData.nodes 9 ⟨872363, by decide⟩ =
    .split (coordinate 12) (![⟨872308, by decide⟩,⟨872333, by decide⟩,⟨872350, by decide⟩,⟨872362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112666_872363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112666 ⟨872363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112666
    ⟨872363, by decide⟩ (by decide) (![⟨872308, by decide⟩,⟨872333, by decide⟩,⟨872350, by decide⟩,⟨872362, by decide⟩]) unmarked_context_12_112666_872363 node_context_12_112666_872363
  intro a
  fin_cases a
  · exact context_13_450664_872308
  · exact context_13_450665_872333
  · exact context_13_450666_872350
  · exact context_13_450667_872362

theorem selected_cut_33869 : selected 8 ⟨872385, by decide⟩
    (prefixPartial 13 450668) = some ⟨13, 2, 0, 872385, 450668, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_450668_872385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450668 ⟨872385, by decide⟩ :=
  accepted_of_selected 13 450668 ⟨872385, by decide⟩ ⟨13, 2, 0, 872385, 450668, 1361, 16384⟩
    (by decide) selected_cut_33869

theorem selected_cut_33870 : selected 8 ⟨872416, by decide⟩
    (prefixPartial 13 450669) = some ⟨13, 2, 0, 872416, 450669, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_450669_872416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450669 ⟨872416, by decide⟩ :=
  accepted_of_selected 13 450669 ⟨872416, by decide⟩ ⟨13, 2, 0, 872416, 450669, 2277, 16384⟩
    (by decide) selected_cut_33870

theorem selected_cut_33871 : selected 8 ⟨872438, by decide⟩
    (prefixPartial 13 450670) = some ⟨13, 2, 0, 872438, 450670, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_450670_872438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450670 ⟨872438, by decide⟩ :=
  accepted_of_selected 13 450670 ⟨872438, by decide⟩ ⟨13, 2, 0, 872438, 450670, 1173, 16384⟩
    (by decide) selected_cut_33871

theorem selected_cut_33872 : selected 8 ⟨872448, by decide⟩
    (prefixPartial 13 450671) = some ⟨13, 2, 0, 872448, 450671, 609, 16384⟩ := by
  decide +kernel

theorem context_13_450671_872448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450671 ⟨872448, by decide⟩ :=
  accepted_of_selected 13 450671 ⟨872448, by decide⟩ ⟨13, 2, 0, 872448, 450671, 609, 16384⟩
    (by decide) selected_cut_33872

theorem unmarked_context_12_112667_872449 : frontier 9 ⟨872449, by decide⟩
    (prefixCache 12 112667) (prefixPartial 12 112667) = false := by
  decide +kernel

theorem node_context_12_112667_872449 : EJMOriginalGlobalDAGData.nodes 9 ⟨872449, by decide⟩ =
    .split (coordinate 12) (![⟨872385, by decide⟩,⟨872416, by decide⟩,⟨872438, by decide⟩,⟨872448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112667_872449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112667 ⟨872449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112667
    ⟨872449, by decide⟩ (by decide) (![⟨872385, by decide⟩,⟨872416, by decide⟩,⟨872438, by decide⟩,⟨872448, by decide⟩]) unmarked_context_12_112667_872449 node_context_12_112667_872449
  intro a
  fin_cases a
  · exact context_13_450668_872385
  · exact context_13_450669_872416
  · exact context_13_450670_872438
  · exact context_13_450671_872448

theorem unmarked_context_11_28166_872450 : frontier 10 ⟨872450, by decide⟩
    (prefixCache 11 28166) (prefixPartial 11 28166) = false := by
  decide +kernel

theorem node_context_11_28166_872450 : EJMOriginalGlobalDAGData.nodes 10 ⟨872450, by decide⟩ =
    .split (coordinate 11) (![⟨872148, by decide⟩,⟨872277, by decide⟩,⟨872363, by decide⟩,⟨872449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28166_872450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28166 ⟨872450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28166
    ⟨872450, by decide⟩ (by decide) (![⟨872148, by decide⟩,⟨872277, by decide⟩,⟨872363, by decide⟩,⟨872449, by decide⟩]) unmarked_context_11_28166_872450 node_context_11_28166_872450
  intro a
  fin_cases a
  · exact context_12_112664_872148
  · exact context_12_112665_872277
  · exact context_12_112666_872363
  · exact context_12_112667_872449

theorem selected_cut_33873 : selected 8 ⟨872468, by decide⟩
    (prefixPartial 13 450672) = some ⟨13, 2, 0, 872468, 450672, 925, 16384⟩ := by
  decide +kernel

theorem context_13_450672_872468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450672 ⟨872468, by decide⟩ :=
  accepted_of_selected 13 450672 ⟨872468, by decide⟩ ⟨13, 2, 0, 872468, 450672, 925, 16384⟩
    (by decide) selected_cut_33873

theorem selected_cut_33874 : selected 8 ⟨872508, by decide⟩
    (prefixPartial 13 450673) = some ⟨13, 2, 0, 872508, 450673, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_450673_872508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450673 ⟨872508, by decide⟩ :=
  accepted_of_selected 13 450673 ⟨872508, by decide⟩ ⟨13, 2, 0, 872508, 450673, 2333, 16384⟩
    (by decide) selected_cut_33874

theorem selected_cut_33875 : selected 8 ⟨872545, by decide⟩
    (prefixPartial 13 450674) = some ⟨13, 2, 0, 872545, 450674, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_450674_872545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450674 ⟨872545, by decide⟩ :=
  accepted_of_selected 13 450674 ⟨872545, by decide⟩ ⟨13, 2, 0, 872545, 450674, 1169, 16384⟩
    (by decide) selected_cut_33875

theorem selected_cut_33876 : selected 8 ⟨872559, by decide⟩
    (prefixPartial 13 450675) = some ⟨13, 2, 0, 872559, 450675, 657, 16384⟩ := by
  decide +kernel

theorem context_13_450675_872559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450675 ⟨872559, by decide⟩ :=
  accepted_of_selected 13 450675 ⟨872559, by decide⟩ ⟨13, 2, 0, 872559, 450675, 657, 16384⟩
    (by decide) selected_cut_33876

theorem unmarked_context_12_112668_872560 : frontier 9 ⟨872560, by decide⟩
    (prefixCache 12 112668) (prefixPartial 12 112668) = false := by
  decide +kernel

theorem node_context_12_112668_872560 : EJMOriginalGlobalDAGData.nodes 9 ⟨872560, by decide⟩ =
    .split (coordinate 12) (![⟨872468, by decide⟩,⟨872508, by decide⟩,⟨872545, by decide⟩,⟨872559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112668_872560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112668 ⟨872560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112668
    ⟨872560, by decide⟩ (by decide) (![⟨872468, by decide⟩,⟨872508, by decide⟩,⟨872545, by decide⟩,⟨872559, by decide⟩]) unmarked_context_12_112668_872560 node_context_12_112668_872560
  intro a
  fin_cases a
  · exact context_13_450672_872468
  · exact context_13_450673_872508
  · exact context_13_450674_872545
  · exact context_13_450675_872559

theorem selected_cut_33877 : selected 8 ⟨872597, by decide⟩
    (prefixPartial 13 450676) = some ⟨13, 2, 0, 872597, 450676, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_450676_872597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450676 ⟨872597, by decide⟩ :=
  accepted_of_selected 13 450676 ⟨872597, by decide⟩ ⟨13, 2, 0, 872597, 450676, 1749, 16384⟩
    (by decide) selected_cut_33877

theorem selected_cut_33878 : selected 8 ⟨872650, by decide⟩
    (prefixPartial 13 450677) = some ⟨13, 2, 0, 872650, 450677, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_450677_872650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450677 ⟨872650, by decide⟩ :=
  accepted_of_selected 13 450677 ⟨872650, by decide⟩ ⟨13, 2, 0, 872650, 450677, 2809, 16384⟩
    (by decide) selected_cut_33878

theorem selected_cut_33879 : selected 8 ⟨872706, by decide⟩
    (prefixPartial 13 450678) = some ⟨13, 2, 0, 872706, 450678, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_450678_872706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450678 ⟨872706, by decide⟩ :=
  accepted_of_selected 13 450678 ⟨872706, by decide⟩ ⟨13, 2, 0, 872706, 450678, 1761, 16384⟩
    (by decide) selected_cut_33879

theorem selected_cut_33880 : selected 8 ⟨872732, by decide⟩
    (prefixPartial 13 450679) = some ⟨13, 2, 0, 872732, 450679, 865, 16384⟩ := by
  decide +kernel

theorem context_13_450679_872732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450679 ⟨872732, by decide⟩ :=
  accepted_of_selected 13 450679 ⟨872732, by decide⟩ ⟨13, 2, 0, 872732, 450679, 865, 16384⟩
    (by decide) selected_cut_33880

theorem unmarked_context_12_112669_872733 : frontier 9 ⟨872733, by decide⟩
    (prefixCache 12 112669) (prefixPartial 12 112669) = false := by
  decide +kernel

theorem node_context_12_112669_872733 : EJMOriginalGlobalDAGData.nodes 9 ⟨872733, by decide⟩ =
    .split (coordinate 12) (![⟨872597, by decide⟩,⟨872650, by decide⟩,⟨872706, by decide⟩,⟨872732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112669_872733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112669 ⟨872733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112669
    ⟨872733, by decide⟩ (by decide) (![⟨872597, by decide⟩,⟨872650, by decide⟩,⟨872706, by decide⟩,⟨872732, by decide⟩]) unmarked_context_12_112669_872733 node_context_12_112669_872733
  intro a
  fin_cases a
  · exact context_13_450676_872597
  · exact context_13_450677_872650
  · exact context_13_450678_872706
  · exact context_13_450679_872732

theorem selected_cut_33881 : selected 8 ⟨872765, by decide⟩
    (prefixPartial 13 450680) = some ⟨13, 2, 0, 872765, 450680, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_450680_872765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450680 ⟨872765, by decide⟩ :=
  accepted_of_selected 13 450680 ⟨872765, by decide⟩ ⟨13, 2, 0, 872765, 450680, 1325, 16384⟩
    (by decide) selected_cut_33881

theorem selected_cut_33882 : selected 8 ⟨872799, by decide⟩
    (prefixPartial 13 450681) = some ⟨13, 2, 0, 872799, 450681, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_450681_872799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450681 ⟨872799, by decide⟩ :=
  accepted_of_selected 13 450681 ⟨872799, by decide⟩ ⟨13, 2, 0, 872799, 450681, 2245, 16384⟩
    (by decide) selected_cut_33882

theorem selected_cut_33883 : selected 8 ⟨872834, by decide⟩
    (prefixPartial 13 450682) = some ⟨13, 2, 0, 872834, 450682, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_450682_872834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450682 ⟨872834, by decide⟩ :=
  accepted_of_selected 13 450682 ⟨872834, by decide⟩ ⟨13, 2, 0, 872834, 450682, 1345, 16384⟩
    (by decide) selected_cut_33883

theorem selected_cut_33884 : selected 8 ⟨872845, by decide⟩
    (prefixPartial 13 450683) = some ⟨13, 2, 0, 872845, 450683, 705, 16384⟩ := by
  decide +kernel

theorem context_13_450683_872845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450683 ⟨872845, by decide⟩ :=
  accepted_of_selected 13 450683 ⟨872845, by decide⟩ ⟨13, 2, 0, 872845, 450683, 705, 16384⟩
    (by decide) selected_cut_33884

theorem unmarked_context_12_112670_872846 : frontier 9 ⟨872846, by decide⟩
    (prefixCache 12 112670) (prefixPartial 12 112670) = false := by
  decide +kernel

theorem node_context_12_112670_872846 : EJMOriginalGlobalDAGData.nodes 9 ⟨872846, by decide⟩ =
    .split (coordinate 12) (![⟨872765, by decide⟩,⟨872799, by decide⟩,⟨872834, by decide⟩,⟨872845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112670_872846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112670 ⟨872846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112670
    ⟨872846, by decide⟩ (by decide) (![⟨872765, by decide⟩,⟨872799, by decide⟩,⟨872834, by decide⟩,⟨872845, by decide⟩]) unmarked_context_12_112670_872846 node_context_12_112670_872846
  intro a
  fin_cases a
  · exact context_13_450680_872765
  · exact context_13_450681_872799
  · exact context_13_450682_872834
  · exact context_13_450683_872845

theorem selected_cut_33885 : selected 8 ⟨872868, by decide⟩
    (prefixPartial 13 450684) = some ⟨13, 2, 0, 872868, 450684, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_450684_872868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450684 ⟨872868, by decide⟩ :=
  accepted_of_selected 13 450684 ⟨872868, by decide⟩ ⟨13, 2, 0, 872868, 450684, 1125, 16384⟩
    (by decide) selected_cut_33885

theorem selected_cut_33886 : selected 8 ⟨872897, by decide⟩
    (prefixPartial 13 450685) = some ⟨13, 2, 0, 872897, 450685, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_450685_872897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450685 ⟨872897, by decide⟩ :=
  accepted_of_selected 13 450685 ⟨872897, by decide⟩ ⟨13, 2, 0, 872897, 450685, 2257, 16384⟩
    (by decide) selected_cut_33886

theorem selected_cut_33887 : selected 8 ⟨872917, by decide⟩
    (prefixPartial 13 450686) = some ⟨13, 2, 0, 872917, 450686, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_450686_872917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450686 ⟨872917, by decide⟩ :=
  accepted_of_selected 13 450686 ⟨872917, by decide⟩ ⟨13, 2, 0, 872917, 450686, 1197, 16384⟩
    (by decide) selected_cut_33887

theorem selected_cut_33888 : selected 8 ⟨872924, by decide⟩
    (prefixPartial 13 450687) = some ⟨13, 2, 0, 872924, 450687, 609, 16384⟩ := by
  decide +kernel

theorem context_13_450687_872924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450687 ⟨872924, by decide⟩ :=
  accepted_of_selected 13 450687 ⟨872924, by decide⟩ ⟨13, 2, 0, 872924, 450687, 609, 16384⟩
    (by decide) selected_cut_33888

theorem unmarked_context_12_112671_872925 : frontier 9 ⟨872925, by decide⟩
    (prefixCache 12 112671) (prefixPartial 12 112671) = false := by
  decide +kernel

theorem node_context_12_112671_872925 : EJMOriginalGlobalDAGData.nodes 9 ⟨872925, by decide⟩ =
    .split (coordinate 12) (![⟨872868, by decide⟩,⟨872897, by decide⟩,⟨872917, by decide⟩,⟨872924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112671_872925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112671 ⟨872925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112671
    ⟨872925, by decide⟩ (by decide) (![⟨872868, by decide⟩,⟨872897, by decide⟩,⟨872917, by decide⟩,⟨872924, by decide⟩]) unmarked_context_12_112671_872925 node_context_12_112671_872925
  intro a
  fin_cases a
  · exact context_13_450684_872868
  · exact context_13_450685_872897
  · exact context_13_450686_872917
  · exact context_13_450687_872924

theorem unmarked_context_11_28167_872926 : frontier 10 ⟨872926, by decide⟩
    (prefixCache 11 28167) (prefixPartial 11 28167) = false := by
  decide +kernel

theorem node_context_11_28167_872926 : EJMOriginalGlobalDAGData.nodes 10 ⟨872926, by decide⟩ =
    .split (coordinate 11) (![⟨872560, by decide⟩,⟨872733, by decide⟩,⟨872846, by decide⟩,⟨872925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28167_872926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28167 ⟨872926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28167
    ⟨872926, by decide⟩ (by decide) (![⟨872560, by decide⟩,⟨872733, by decide⟩,⟨872846, by decide⟩,⟨872925, by decide⟩]) unmarked_context_11_28167_872926 node_context_11_28167_872926
  intro a
  fin_cases a
  · exact context_12_112668_872560
  · exact context_12_112669_872733
  · exact context_12_112670_872846
  · exact context_12_112671_872925

theorem unmarked_context_10_7041_872927 : frontier 11 ⟨872927, by decide⟩
    (prefixCache 10 7041) (prefixPartial 10 7041) = false := by
  decide +kernel

theorem node_context_10_7041_872927 : EJMOriginalGlobalDAGData.nodes 11 ⟨872927, by decide⟩ =
    .split (coordinate 10) (![⟨871699, by decide⟩,⟨872079, by decide⟩,⟨872450, by decide⟩,⟨872926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7041_872927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7041 ⟨872927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7041
    ⟨872927, by decide⟩ (by decide) (![⟨871699, by decide⟩,⟨872079, by decide⟩,⟨872450, by decide⟩,⟨872926, by decide⟩]) unmarked_context_10_7041_872927 node_context_10_7041_872927
  intro a
  fin_cases a
  · exact context_11_28164_871699
  · exact context_11_28165_872079
  · exact context_11_28166_872450
  · exact context_11_28167_872926

theorem selected_cut_33889 : selected 9 ⟨765706, by decide⟩
    (prefixPartial 12 112672) = some ⟨12, 1, 0, 765706, 112672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112672_765706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112672 ⟨765706, by decide⟩ :=
  accepted_of_selected 12 112672 ⟨765706, by decide⟩ ⟨12, 1, 0, 765706, 112672, 1, 65536⟩
    (by decide) selected_cut_33889

theorem selected_cut_33890 : selected 8 ⟨872967, by decide⟩
    (prefixPartial 13 450692) = some ⟨13, 2, 0, 872967, 450692, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_450692_872967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 450692 ⟨872967, by decide⟩ :=
  accepted_of_selected 13 450692 ⟨872967, by decide⟩ ⟨13, 2, 0, 872967, 450692, 1069, 16384⟩
    (by decide) selected_cut_33890

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
