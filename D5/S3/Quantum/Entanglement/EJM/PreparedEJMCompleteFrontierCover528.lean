/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover527
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_50691 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 440592) = some ⟨12, 1, 0, 435790, 440592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440592_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440592 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 440592 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 440592, 1, 65536⟩
    (by decide) selected_cut_50691

theorem selected_cut_50692 : selected 9 ⟨1450708, by decide⟩
    (prefixPartial 12 440593) = some ⟨12, 2, 0, 1450708, 440593, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_440593_1450708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440593 ⟨1450708, by decide⟩ :=
  accepted_of_selected 12 440593 ⟨1450708, by decide⟩ ⟨12, 2, 0, 1450708, 440593, 1937, 65536⟩
    (by decide) selected_cut_50692

theorem selected_cut_50693 : selected 9 ⟨1450760, by decide⟩
    (prefixPartial 12 440594) = some ⟨12, 2, 0, 1450760, 440594, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_440594_1450760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440594 ⟨1450760, by decide⟩ :=
  accepted_of_selected 12 440594 ⟨1450760, by decide⟩ ⟨12, 2, 0, 1450760, 440594, 1933, 65536⟩
    (by decide) selected_cut_50693

theorem selected_cut_50694 : selected 9 ⟨1450804, by decide⟩
    (prefixPartial 12 440595) = some ⟨12, 2, 0, 1450804, 440595, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_440595_1450804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440595 ⟨1450804, by decide⟩ :=
  accepted_of_selected 12 440595 ⟨1450804, by decide⟩ ⟨12, 2, 0, 1450804, 440595, 1753, 65536⟩
    (by decide) selected_cut_50694

theorem unmarked_context_11_110148_1450805 : frontier 10 ⟨1450805, by decide⟩
    (prefixCache 11 110148) (prefixPartial 11 110148) = false := by
  decide +kernel

theorem node_context_11_110148_1450805 : EJMOriginalGlobalDAGData.nodes 10 ⟨1450805, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1450708, by decide⟩,⟨1450760, by decide⟩,⟨1450804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110148_1450805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110148 ⟨1450805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110148
    ⟨1450805, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1450708, by decide⟩,⟨1450760, by decide⟩,⟨1450804, by decide⟩]) unmarked_context_11_110148_1450805 node_context_11_110148_1450805
  intro a
  fin_cases a
  · exact context_12_440592_435790
  · exact context_12_440593_1450708
  · exact context_12_440594_1450760
  · exact context_12_440595_1450804

theorem selected_cut_50695 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 110149) = some ⟨11, 1, 0, 1192826, 110149, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110149_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110149 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 110149 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 110149, 1, 262144⟩
    (by decide) selected_cut_50695

theorem selected_cut_50696 : selected 10 ⟨1450887, by decide⟩
    (prefixPartial 11 110150) = some ⟨11, 2, 0, 1450887, 110150, 3221, 262144⟩ := by
  decide +kernel

theorem context_11_110150_1450887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110150 ⟨1450887, by decide⟩ :=
  accepted_of_selected 11 110150 ⟨1450887, by decide⟩ ⟨11, 2, 0, 1450887, 110150, 3221, 262144⟩
    (by decide) selected_cut_50696

theorem selected_cut_50697 : selected 9 ⟨1450922, by decide⟩
    (prefixPartial 12 440604) = some ⟨12, 2, 0, 1450922, 440604, 913, 65536⟩ := by
  decide +kernel

theorem context_12_440604_1450922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440604 ⟨1450922, by decide⟩ :=
  accepted_of_selected 12 440604 ⟨1450922, by decide⟩ ⟨12, 2, 0, 1450922, 440604, 913, 65536⟩
    (by decide) selected_cut_50697

theorem selected_cut_50698 : selected 9 ⟨1450964, by decide⟩
    (prefixPartial 12 440605) = some ⟨12, 2, 0, 1450964, 440605, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_440605_1450964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440605 ⟨1450964, by decide⟩ :=
  accepted_of_selected 12 440605 ⟨1450964, by decide⟩ ⟨12, 2, 0, 1450964, 440605, 1817, 65536⟩
    (by decide) selected_cut_50698

theorem selected_cut_50699 : selected 9 ⟨1451008, by decide⟩
    (prefixPartial 12 440606) = some ⟨12, 2, 0, 1451008, 440606, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_440606_1451008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440606 ⟨1451008, by decide⟩ :=
  accepted_of_selected 12 440606 ⟨1451008, by decide⟩ ⟨12, 2, 0, 1451008, 440606, 1937, 65536⟩
    (by decide) selected_cut_50699

theorem selected_cut_50700 : selected 9 ⟨1365011, by decide⟩
    (prefixPartial 12 440607) = some ⟨12, 1, 0, 1365011, 440607, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440607_1365011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440607 ⟨1365011, by decide⟩ :=
  accepted_of_selected 12 440607 ⟨1365011, by decide⟩ ⟨12, 1, 0, 1365011, 440607, 1, 65536⟩
    (by decide) selected_cut_50700

theorem unmarked_context_11_110151_1451009 : frontier 10 ⟨1451009, by decide⟩
    (prefixCache 11 110151) (prefixPartial 11 110151) = false := by
  decide +kernel

theorem node_context_11_110151_1451009 : EJMOriginalGlobalDAGData.nodes 10 ⟨1451009, by decide⟩ =
    .split (coordinate 11) (![⟨1450922, by decide⟩,⟨1450964, by decide⟩,⟨1451008, by decide⟩,⟨1365011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110151_1451009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110151 ⟨1451009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110151
    ⟨1451009, by decide⟩ (by decide) (![⟨1450922, by decide⟩,⟨1450964, by decide⟩,⟨1451008, by decide⟩,⟨1365011, by decide⟩]) unmarked_context_11_110151_1451009 node_context_11_110151_1451009
  intro a
  fin_cases a
  · exact context_12_440604_1450922
  · exact context_12_440605_1450964
  · exact context_12_440606_1451008
  · exact context_12_440607_1365011

theorem unmarked_context_10_27537_1451010 : frontier 11 ⟨1451010, by decide⟩
    (prefixCache 10 27537) (prefixPartial 10 27537) = false := by
  decide +kernel

theorem node_context_10_27537_1451010 : EJMOriginalGlobalDAGData.nodes 11 ⟨1451010, by decide⟩ =
    .split (coordinate 10) (![⟨1450805, by decide⟩,⟨1192826, by decide⟩,⟨1450887, by decide⟩,⟨1451009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27537_1451010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27537 ⟨1451010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27537
    ⟨1451010, by decide⟩ (by decide) (![⟨1450805, by decide⟩,⟨1192826, by decide⟩,⟨1450887, by decide⟩,⟨1451009, by decide⟩]) unmarked_context_10_27537_1451010 node_context_10_27537_1451010
  intro a
  fin_cases a
  · exact context_11_110148_1450805
  · exact context_11_110149_1192826
  · exact context_11_110150_1450887
  · exact context_11_110151_1451009

theorem selected_cut_50701 : selected 9 ⟨1448897, by decide⟩
    (prefixPartial 12 440608) = some ⟨12, 1, 0, 1448897, 440608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440608_1448897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440608 ⟨1448897, by decide⟩ :=
  accepted_of_selected 12 440608 ⟨1448897, by decide⟩ ⟨12, 1, 0, 1448897, 440608, 1, 65536⟩
    (by decide) selected_cut_50701

theorem selected_cut_50702 : selected 9 ⟨1451057, by decide⟩
    (prefixPartial 12 440609) = some ⟨12, 2, 0, 1451057, 440609, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_440609_1451057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440609 ⟨1451057, by decide⟩ :=
  accepted_of_selected 12 440609 ⟨1451057, by decide⟩ ⟨12, 2, 0, 1451057, 440609, 1753, 65536⟩
    (by decide) selected_cut_50702

theorem selected_cut_50703 : selected 9 ⟨1451101, by decide⟩
    (prefixPartial 12 440610) = some ⟨12, 2, 0, 1451101, 440610, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_440610_1451101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440610 ⟨1451101, by decide⟩ :=
  accepted_of_selected 12 440610 ⟨1451101, by decide⟩ ⟨12, 2, 0, 1451101, 440610, 1769, 65536⟩
    (by decide) selected_cut_50703

theorem selected_cut_50704 : selected 9 ⟨1451140, by decide⟩
    (prefixPartial 12 440611) = some ⟨12, 2, 0, 1451140, 440611, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_440611_1451140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440611 ⟨1451140, by decide⟩ :=
  accepted_of_selected 12 440611 ⟨1451140, by decide⟩ ⟨12, 2, 0, 1451140, 440611, 1657, 65536⟩
    (by decide) selected_cut_50704

theorem unmarked_context_11_110152_1451141 : frontier 10 ⟨1451141, by decide⟩
    (prefixCache 11 110152) (prefixPartial 11 110152) = false := by
  decide +kernel

theorem node_context_11_110152_1451141 : EJMOriginalGlobalDAGData.nodes 10 ⟨1451141, by decide⟩ =
    .split (coordinate 11) (![⟨1448897, by decide⟩,⟨1451057, by decide⟩,⟨1451101, by decide⟩,⟨1451140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110152_1451141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110152 ⟨1451141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110152
    ⟨1451141, by decide⟩ (by decide) (![⟨1448897, by decide⟩,⟨1451057, by decide⟩,⟨1451101, by decide⟩,⟨1451140, by decide⟩]) unmarked_context_11_110152_1451141 node_context_11_110152_1451141
  intro a
  fin_cases a
  · exact context_12_440608_1448897
  · exact context_12_440609_1451057
  · exact context_12_440610_1451101
  · exact context_12_440611_1451140

theorem selected_cut_50705 : selected 10 ⟨1451205, by decide⟩
    (prefixPartial 11 110153) = some ⟨11, 2, 0, 1451205, 110153, 3365, 262144⟩ := by
  decide +kernel

theorem context_11_110153_1451205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110153 ⟨1451205, by decide⟩ :=
  accepted_of_selected 11 110153 ⟨1451205, by decide⟩ ⟨11, 2, 0, 1451205, 110153, 3365, 262144⟩
    (by decide) selected_cut_50705

theorem selected_cut_50706 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110154) = some ⟨11, 1, 0, 900587, 110154, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110154_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110154 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110154 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110154, 1, 262144⟩
    (by decide) selected_cut_50706

theorem selected_cut_50707 : selected 9 ⟨1448897, by decide⟩
    (prefixPartial 12 440620) = some ⟨12, 1, 0, 1448897, 440620, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440620_1448897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440620 ⟨1448897, by decide⟩ :=
  accepted_of_selected 12 440620 ⟨1448897, by decide⟩ ⟨12, 1, 0, 1448897, 440620, 1, 65536⟩
    (by decide) selected_cut_50707

theorem selected_cut_50708 : selected 9 ⟨1451249, by decide⟩
    (prefixPartial 12 440621) = some ⟨12, 2, 0, 1451249, 440621, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_440621_1451249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440621 ⟨1451249, by decide⟩ :=
  accepted_of_selected 12 440621 ⟨1451249, by decide⟩ ⟨12, 2, 0, 1451249, 440621, 1681, 65536⟩
    (by decide) selected_cut_50708

theorem selected_cut_50709 : selected 9 ⟨1451288, by decide⟩
    (prefixPartial 12 440622) = some ⟨12, 2, 0, 1451288, 440622, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_440622_1451288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440622 ⟨1451288, by decide⟩ :=
  accepted_of_selected 12 440622 ⟨1451288, by decide⟩ ⟨12, 2, 0, 1451288, 440622, 1789, 65536⟩
    (by decide) selected_cut_50709

theorem selected_cut_50710 : selected 9 ⟨1451349, by decide⟩
    (prefixPartial 12 440623) = some ⟨12, 2, 0, 1451349, 440623, 961, 65536⟩ := by
  decide +kernel

theorem context_12_440623_1451349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440623 ⟨1451349, by decide⟩ :=
  accepted_of_selected 12 440623 ⟨1451349, by decide⟩ ⟨12, 2, 0, 1451349, 440623, 961, 65536⟩
    (by decide) selected_cut_50710

theorem unmarked_context_11_110155_1451350 : frontier 10 ⟨1451350, by decide⟩
    (prefixCache 11 110155) (prefixPartial 11 110155) = false := by
  decide +kernel

theorem node_context_11_110155_1451350 : EJMOriginalGlobalDAGData.nodes 10 ⟨1451350, by decide⟩ =
    .split (coordinate 11) (![⟨1448897, by decide⟩,⟨1451249, by decide⟩,⟨1451288, by decide⟩,⟨1451349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110155_1451350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110155 ⟨1451350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110155
    ⟨1451350, by decide⟩ (by decide) (![⟨1448897, by decide⟩,⟨1451249, by decide⟩,⟨1451288, by decide⟩,⟨1451349, by decide⟩]) unmarked_context_11_110155_1451350 node_context_11_110155_1451350
  intro a
  fin_cases a
  · exact context_12_440620_1448897
  · exact context_12_440621_1451249
  · exact context_12_440622_1451288
  · exact context_12_440623_1451349

theorem unmarked_context_10_27538_1451351 : frontier 11 ⟨1451351, by decide⟩
    (prefixCache 10 27538) (prefixPartial 10 27538) = false := by
  decide +kernel

theorem node_context_10_27538_1451351 : EJMOriginalGlobalDAGData.nodes 11 ⟨1451351, by decide⟩ =
    .split (coordinate 10) (![⟨1451141, by decide⟩,⟨1451205, by decide⟩,⟨900587, by decide⟩,⟨1451350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27538_1451351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27538 ⟨1451351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27538
    ⟨1451351, by decide⟩ (by decide) (![⟨1451141, by decide⟩,⟨1451205, by decide⟩,⟨900587, by decide⟩,⟨1451350, by decide⟩]) unmarked_context_10_27538_1451351 node_context_10_27538_1451351
  intro a
  fin_cases a
  · exact context_11_110152_1451141
  · exact context_11_110153_1451205
  · exact context_11_110154_900587
  · exact context_11_110155_1451350

theorem selected_cut_50711 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 440624) = some ⟨12, 1, 0, 1255011, 440624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440624_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440624 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 440624 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 440624, 1, 65536⟩
    (by decide) selected_cut_50711

theorem selected_cut_50712 : selected 9 ⟨1451393, by decide⟩
    (prefixPartial 12 440625) = some ⟨12, 2, 0, 1451393, 440625, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_440625_1451393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440625 ⟨1451393, by decide⟩ :=
  accepted_of_selected 12 440625 ⟨1451393, by decide⟩ ⟨12, 2, 0, 1451393, 440625, 1701, 65536⟩
    (by decide) selected_cut_50712

theorem selected_cut_50713 : selected 9 ⟨1451428, by decide⟩
    (prefixPartial 12 440626) = some ⟨12, 2, 0, 1451428, 440626, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_440626_1451428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440626 ⟨1451428, by decide⟩ :=
  accepted_of_selected 12 440626 ⟨1451428, by decide⟩ ⟨12, 2, 0, 1451428, 440626, 1501, 65536⟩
    (by decide) selected_cut_50713

theorem selected_cut_50714 : selected 9 ⟨1451473, by decide⟩
    (prefixPartial 12 440627) = some ⟨12, 2, 0, 1451473, 440627, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_440627_1451473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440627 ⟨1451473, by decide⟩ :=
  accepted_of_selected 12 440627 ⟨1451473, by decide⟩ ⟨12, 2, 0, 1451473, 440627, 1501, 65536⟩
    (by decide) selected_cut_50714

theorem unmarked_context_11_110156_1451474 : frontier 10 ⟨1451474, by decide⟩
    (prefixCache 11 110156) (prefixPartial 11 110156) = false := by
  decide +kernel

theorem node_context_11_110156_1451474 : EJMOriginalGlobalDAGData.nodes 10 ⟨1451474, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1451393, by decide⟩,⟨1451428, by decide⟩,⟨1451473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110156_1451474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110156 ⟨1451474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110156
    ⟨1451474, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1451393, by decide⟩,⟨1451428, by decide⟩,⟨1451473, by decide⟩]) unmarked_context_11_110156_1451474 node_context_11_110156_1451474
  intro a
  fin_cases a
  · exact context_12_440624_1255011
  · exact context_12_440625_1451393
  · exact context_12_440626_1451428
  · exact context_12_440627_1451473

theorem selected_cut_50715 : selected 10 ⟨1451598, by decide⟩
    (prefixPartial 11 110157) = some ⟨11, 2, 0, 1451598, 110157, 4053, 262144⟩ := by
  decide +kernel

theorem context_11_110157_1451598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110157 ⟨1451598, by decide⟩ :=
  accepted_of_selected 11 110157 ⟨1451598, by decide⟩ ⟨11, 2, 0, 1451598, 110157, 4053, 262144⟩
    (by decide) selected_cut_50715

theorem selected_cut_50716 : selected 10 ⟨1451658, by decide⟩
    (prefixPartial 11 110158) = some ⟨11, 2, 0, 1451658, 110158, 2409, 262144⟩ := by
  decide +kernel

theorem context_11_110158_1451658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110158 ⟨1451658, by decide⟩ :=
  accepted_of_selected 11 110158 ⟨1451658, by decide⟩ ⟨11, 2, 0, 1451658, 110158, 2409, 262144⟩
    (by decide) selected_cut_50716

theorem selected_cut_50717 : selected 10 ⟨1451744, by decide⟩
    (prefixPartial 11 110159) = some ⟨11, 2, 0, 1451744, 110159, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_110159_1451744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110159 ⟨1451744, by decide⟩ :=
  accepted_of_selected 11 110159 ⟨1451744, by decide⟩ ⟨11, 2, 0, 1451744, 110159, 1857, 262144⟩
    (by decide) selected_cut_50717

theorem unmarked_context_10_27539_1451745 : frontier 11 ⟨1451745, by decide⟩
    (prefixCache 10 27539) (prefixPartial 10 27539) = false := by
  decide +kernel

theorem node_context_10_27539_1451745 : EJMOriginalGlobalDAGData.nodes 11 ⟨1451745, by decide⟩ =
    .split (coordinate 10) (![⟨1451474, by decide⟩,⟨1451598, by decide⟩,⟨1451658, by decide⟩,⟨1451744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27539_1451745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27539 ⟨1451745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27539
    ⟨1451745, by decide⟩ (by decide) (![⟨1451474, by decide⟩,⟨1451598, by decide⟩,⟨1451658, by decide⟩,⟨1451744, by decide⟩]) unmarked_context_10_27539_1451745 node_context_10_27539_1451745
  intro a
  fin_cases a
  · exact context_11_110156_1451474
  · exact context_11_110157_1451598
  · exact context_11_110158_1451658
  · exact context_11_110159_1451744

theorem unmarked_context_9_6884_1451746 : frontier 12 ⟨1451746, by decide⟩
    (prefixCache 9 6884) (prefixPartial 9 6884) = false := by
  decide +kernel

theorem node_context_9_6884_1451746 : EJMOriginalGlobalDAGData.nodes 12 ⟨1451746, by decide⟩ =
    .split (coordinate 9) (![⟨1450656, by decide⟩,⟨1451010, by decide⟩,⟨1451351, by decide⟩,⟨1451745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6884_1451746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6884 ⟨1451746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6884
    ⟨1451746, by decide⟩ (by decide) (![⟨1450656, by decide⟩,⟨1451010, by decide⟩,⟨1451351, by decide⟩,⟨1451745, by decide⟩]) unmarked_context_9_6884_1451746 node_context_9_6884_1451746
  intro a
  fin_cases a
  · exact context_10_27536_1450656
  · exact context_10_27537_1451010
  · exact context_10_27538_1451351
  · exact context_10_27539_1451745

theorem selected_cut_50718 : selected 10 ⟨1451747, by decide⟩
    (prefixPartial 11 110160) = some ⟨11, 2, 0, 1451747, 110160, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110160_1451747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110160 ⟨1451747, by decide⟩ :=
  accepted_of_selected 11 110160 ⟨1451747, by decide⟩ ⟨11, 2, 0, 1451747, 110160, 5, 262144⟩
    (by decide) selected_cut_50718

theorem selected_cut_50719 : selected 10 ⟨1451840, by decide⟩
    (prefixPartial 11 110161) = some ⟨11, 2, 0, 1451840, 110161, 3577, 262144⟩ := by
  decide +kernel

theorem context_11_110161_1451840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110161 ⟨1451840, by decide⟩ :=
  accepted_of_selected 11 110161 ⟨1451840, by decide⟩ ⟨11, 2, 0, 1451840, 110161, 3577, 262144⟩
    (by decide) selected_cut_50719

theorem selected_cut_50720 : selected 10 ⟨1451892, by decide⟩
    (prefixPartial 11 110162) = some ⟨11, 2, 0, 1451892, 110162, 2069, 262144⟩ := by
  decide +kernel

theorem context_11_110162_1451892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110162 ⟨1451892, by decide⟩ :=
  accepted_of_selected 11 110162 ⟨1451892, by decide⟩ ⟨11, 2, 0, 1451892, 110162, 2069, 262144⟩
    (by decide) selected_cut_50720

theorem selected_cut_50721 : selected 10 ⟨1451958, by decide⟩
    (prefixPartial 11 110163) = some ⟨11, 2, 0, 1451958, 110163, 2533, 262144⟩ := by
  decide +kernel

theorem context_11_110163_1451958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110163 ⟨1451958, by decide⟩ :=
  accepted_of_selected 11 110163 ⟨1451958, by decide⟩ ⟨11, 2, 0, 1451958, 110163, 2533, 262144⟩
    (by decide) selected_cut_50721

theorem unmarked_context_10_27540_1451959 : frontier 11 ⟨1451959, by decide⟩
    (prefixCache 10 27540) (prefixPartial 10 27540) = false := by
  decide +kernel

theorem node_context_10_27540_1451959 : EJMOriginalGlobalDAGData.nodes 11 ⟨1451959, by decide⟩ =
    .split (coordinate 10) (![⟨1451747, by decide⟩,⟨1451840, by decide⟩,⟨1451892, by decide⟩,⟨1451958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27540_1451959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27540 ⟨1451959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27540
    ⟨1451959, by decide⟩ (by decide) (![⟨1451747, by decide⟩,⟨1451840, by decide⟩,⟨1451892, by decide⟩,⟨1451958, by decide⟩]) unmarked_context_10_27540_1451959 node_context_10_27540_1451959
  intro a
  fin_cases a
  · exact context_11_110160_1451747
  · exact context_11_110161_1451840
  · exact context_11_110162_1451892
  · exact context_11_110163_1451958

theorem selected_cut_50722 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 27541) = some ⟨10, 1, 0, 893098, 27541, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27541_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27541 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 27541 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 27541, 1, 1048576⟩
    (by decide) selected_cut_50722

theorem selected_cut_50723 : selected 10 ⟨1452010, by decide⟩
    (prefixPartial 11 110168) = some ⟨11, 2, 0, 1452010, 110168, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_110168_1452010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110168 ⟨1452010, by decide⟩ :=
  accepted_of_selected 11 110168 ⟨1452010, by decide⟩ ⟨11, 2, 0, 1452010, 110168, 1929, 262144⟩
    (by decide) selected_cut_50723

theorem selected_cut_50724 : selected 10 ⟨1452072, by decide⟩
    (prefixPartial 11 110169) = some ⟨11, 2, 0, 1452072, 110169, 2633, 262144⟩ := by
  decide +kernel

theorem context_11_110169_1452072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110169 ⟨1452072, by decide⟩ :=
  accepted_of_selected 11 110169 ⟨1452072, by decide⟩ ⟨11, 2, 0, 1452072, 110169, 2633, 262144⟩
    (by decide) selected_cut_50724

theorem selected_cut_50725 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110170) = some ⟨11, 1, 0, 900587, 110170, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110170_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110170 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110170 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110170, 1, 262144⟩
    (by decide) selected_cut_50725

theorem selected_cut_50726 : selected 10 ⟨1452119, by decide⟩
    (prefixPartial 11 110171) = some ⟨11, 2, 0, 1452119, 110171, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_110171_1452119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110171 ⟨1452119, by decide⟩ :=
  accepted_of_selected 11 110171 ⟨1452119, by decide⟩ ⟨11, 2, 0, 1452119, 110171, 1805, 262144⟩
    (by decide) selected_cut_50726

theorem unmarked_context_10_27542_1452120 : frontier 11 ⟨1452120, by decide⟩
    (prefixCache 10 27542) (prefixPartial 10 27542) = false := by
  decide +kernel

theorem node_context_10_27542_1452120 : EJMOriginalGlobalDAGData.nodes 11 ⟨1452120, by decide⟩ =
    .split (coordinate 10) (![⟨1452010, by decide⟩,⟨1452072, by decide⟩,⟨900587, by decide⟩,⟨1452119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27542_1452120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27542 ⟨1452120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27542
    ⟨1452120, by decide⟩ (by decide) (![⟨1452010, by decide⟩,⟨1452072, by decide⟩,⟨900587, by decide⟩,⟨1452119, by decide⟩]) unmarked_context_10_27542_1452120 node_context_10_27542_1452120
  intro a
  fin_cases a
  · exact context_11_110168_1452010
  · exact context_11_110169_1452072
  · exact context_11_110170_900587
  · exact context_11_110171_1452119

theorem selected_cut_50727 : selected 10 ⟨1452160, by decide⟩
    (prefixPartial 11 110172) = some ⟨11, 2, 0, 1452160, 110172, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_110172_1452160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110172 ⟨1452160, by decide⟩ :=
  accepted_of_selected 11 110172 ⟨1452160, by decide⟩ ⟨11, 2, 0, 1452160, 110172, 1609, 262144⟩
    (by decide) selected_cut_50727

theorem selected_cut_50728 : selected 10 ⟨1452221, by decide⟩
    (prefixPartial 11 110173) = some ⟨11, 2, 0, 1452221, 110173, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_110173_1452221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110173 ⟨1452221, by decide⟩ :=
  accepted_of_selected 11 110173 ⟨1452221, by decide⟩ ⟨11, 2, 0, 1452221, 110173, 2265, 262144⟩
    (by decide) selected_cut_50728

theorem selected_cut_50729 : selected 10 ⟨1452251, by decide⟩
    (prefixPartial 11 110174) = some ⟨11, 2, 0, 1452251, 110174, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_110174_1452251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110174 ⟨1452251, by decide⟩ :=
  accepted_of_selected 11 110174 ⟨1452251, by decide⟩ ⟨11, 2, 0, 1452251, 110174, 1289, 262144⟩
    (by decide) selected_cut_50729

theorem selected_cut_50730 : selected 10 ⟨1452295, by decide⟩
    (prefixPartial 11 110175) = some ⟨11, 2, 0, 1452295, 110175, 461, 262144⟩ := by
  decide +kernel

theorem context_11_110175_1452295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110175 ⟨1452295, by decide⟩ :=
  accepted_of_selected 11 110175 ⟨1452295, by decide⟩ ⟨11, 2, 0, 1452295, 110175, 461, 262144⟩
    (by decide) selected_cut_50730

theorem unmarked_context_10_27543_1452296 : frontier 11 ⟨1452296, by decide⟩
    (prefixCache 10 27543) (prefixPartial 10 27543) = false := by
  decide +kernel

theorem node_context_10_27543_1452296 : EJMOriginalGlobalDAGData.nodes 11 ⟨1452296, by decide⟩ =
    .split (coordinate 10) (![⟨1452160, by decide⟩,⟨1452221, by decide⟩,⟨1452251, by decide⟩,⟨1452295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27543_1452296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27543 ⟨1452296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27543
    ⟨1452296, by decide⟩ (by decide) (![⟨1452160, by decide⟩,⟨1452221, by decide⟩,⟨1452251, by decide⟩,⟨1452295, by decide⟩]) unmarked_context_10_27543_1452296 node_context_10_27543_1452296
  intro a
  fin_cases a
  · exact context_11_110172_1452160
  · exact context_11_110173_1452221
  · exact context_11_110174_1452251
  · exact context_11_110175_1452295

theorem unmarked_context_9_6885_1452297 : frontier 12 ⟨1452297, by decide⟩
    (prefixCache 9 6885) (prefixPartial 9 6885) = false := by
  decide +kernel

theorem node_context_9_6885_1452297 : EJMOriginalGlobalDAGData.nodes 12 ⟨1452297, by decide⟩ =
    .split (coordinate 9) (![⟨1451959, by decide⟩,⟨893098, by decide⟩,⟨1452120, by decide⟩,⟨1452296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6885_1452297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6885 ⟨1452297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6885
    ⟨1452297, by decide⟩ (by decide) (![⟨1451959, by decide⟩,⟨893098, by decide⟩,⟨1452120, by decide⟩,⟨1452296, by decide⟩]) unmarked_context_9_6885_1452297 node_context_9_6885_1452297
  intro a
  fin_cases a
  · exact context_10_27540_1451959
  · exact context_10_27541_893098
  · exact context_10_27542_1452120
  · exact context_10_27543_1452296

theorem selected_cut_50731 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 110176) = some ⟨11, 1, 0, 1375697, 110176, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110176_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110176 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 110176 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 110176, 1, 262144⟩
    (by decide) selected_cut_50731

theorem selected_cut_50732 : selected 10 ⟨1452332, by decide⟩
    (prefixPartial 11 110177) = some ⟨11, 2, 0, 1452332, 110177, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_110177_1452332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110177 ⟨1452332, by decide⟩ :=
  accepted_of_selected 11 110177 ⟨1452332, by decide⟩ ⟨11, 2, 0, 1452332, 110177, 1449, 262144⟩
    (by decide) selected_cut_50732

theorem selected_cut_50733 : selected 10 ⟨1452378, by decide⟩
    (prefixPartial 11 110178) = some ⟨11, 2, 0, 1452378, 110178, 1989, 262144⟩ := by
  decide +kernel

theorem context_11_110178_1452378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110178 ⟨1452378, by decide⟩ :=
  accepted_of_selected 11 110178 ⟨1452378, by decide⟩ ⟨11, 2, 0, 1452378, 110178, 1989, 262144⟩
    (by decide) selected_cut_50733

theorem selected_cut_50734 : selected 10 ⟨1452429, by decide⟩
    (prefixPartial 11 110179) = some ⟨11, 2, 0, 1452429, 110179, 1677, 262144⟩ := by
  decide +kernel

theorem context_11_110179_1452429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110179 ⟨1452429, by decide⟩ :=
  accepted_of_selected 11 110179 ⟨1452429, by decide⟩ ⟨11, 2, 0, 1452429, 110179, 1677, 262144⟩
    (by decide) selected_cut_50734

theorem unmarked_context_10_27544_1452430 : frontier 11 ⟨1452430, by decide⟩
    (prefixCache 10 27544) (prefixPartial 10 27544) = false := by
  decide +kernel

theorem node_context_10_27544_1452430 : EJMOriginalGlobalDAGData.nodes 11 ⟨1452430, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1452332, by decide⟩,⟨1452378, by decide⟩,⟨1452429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27544_1452430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27544 ⟨1452430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27544
    ⟨1452430, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1452332, by decide⟩,⟨1452378, by decide⟩,⟨1452429, by decide⟩]) unmarked_context_10_27544_1452430 node_context_10_27544_1452430
  intro a
  fin_cases a
  · exact context_11_110176_1375697
  · exact context_11_110177_1452332
  · exact context_11_110178_1452378
  · exact context_11_110179_1452429

theorem selected_cut_50735 : selected 11 ⟨1452521, by decide⟩
    (prefixPartial 10 27545) = some ⟨10, 2, 0, 1452521, 27545, 3341, 1048576⟩ := by
  decide +kernel

theorem context_10_27545_1452521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27545 ⟨1452521, by decide⟩ :=
  accepted_of_selected 10 27545 ⟨1452521, by decide⟩ ⟨10, 2, 0, 1452521, 27545, 3341, 1048576⟩
    (by decide) selected_cut_50735

theorem selected_cut_50736 : selected 11 ⟨1432895, by decide⟩
    (prefixPartial 10 27546) = some ⟨10, 2, 0, 1432895, 27546, 5, 1048576⟩ := by
  decide +kernel

theorem context_10_27546_1432895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27546 ⟨1432895, by decide⟩ :=
  accepted_of_selected 10 27546 ⟨1432895, by decide⟩ ⟨10, 2, 0, 1432895, 27546, 5, 1048576⟩
    (by decide) selected_cut_50736

theorem selected_cut_50737 : selected 11 ⟨1452583, by decide⟩
    (prefixPartial 10 27547) = some ⟨10, 2, 0, 1452583, 27547, 2289, 1048576⟩ := by
  decide +kernel

theorem context_10_27547_1452583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27547 ⟨1452583, by decide⟩ :=
  accepted_of_selected 10 27547 ⟨1452583, by decide⟩ ⟨10, 2, 0, 1452583, 27547, 2289, 1048576⟩
    (by decide) selected_cut_50737

theorem unmarked_context_9_6886_1452584 : frontier 12 ⟨1452584, by decide⟩
    (prefixCache 9 6886) (prefixPartial 9 6886) = false := by
  decide +kernel

theorem node_context_9_6886_1452584 : EJMOriginalGlobalDAGData.nodes 12 ⟨1452584, by decide⟩ =
    .split (coordinate 9) (![⟨1452430, by decide⟩,⟨1452521, by decide⟩,⟨1432895, by decide⟩,⟨1452583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6886_1452584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6886 ⟨1452584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6886
    ⟨1452584, by decide⟩ (by decide) (![⟨1452430, by decide⟩,⟨1452521, by decide⟩,⟨1432895, by decide⟩,⟨1452583, by decide⟩]) unmarked_context_9_6886_1452584 node_context_9_6886_1452584
  intro a
  fin_cases a
  · exact context_10_27544_1452430
  · exact context_10_27545_1452521
  · exact context_10_27546_1432895
  · exact context_10_27547_1452583

theorem selected_cut_50738 : selected 11 ⟨1452669, by decide⟩
    (prefixPartial 10 27548) = some ⟨10, 2, 0, 1452669, 27548, 2513, 1048576⟩ := by
  decide +kernel

theorem context_10_27548_1452669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27548 ⟨1452669, by decide⟩ :=
  accepted_of_selected 10 27548 ⟨1452669, by decide⟩ ⟨10, 2, 0, 1452669, 27548, 2513, 1048576⟩
    (by decide) selected_cut_50738

theorem selected_cut_50739 : selected 11 ⟨1452715, by decide⟩
    (prefixPartial 10 27549) = some ⟨10, 2, 0, 1452715, 27549, 1361, 1048576⟩ := by
  decide +kernel

theorem context_10_27549_1452715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27549 ⟨1452715, by decide⟩ :=
  accepted_of_selected 10 27549 ⟨1452715, by decide⟩ ⟨10, 2, 0, 1452715, 27549, 1361, 1048576⟩
    (by decide) selected_cut_50739

theorem selected_cut_50740 : selected 11 ⟨1452749, by decide⟩
    (prefixPartial 10 27550) = some ⟨10, 2, 0, 1452749, 27550, 681, 1048576⟩ := by
  decide +kernel

theorem context_10_27550_1452749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27550 ⟨1452749, by decide⟩ :=
  accepted_of_selected 10 27550 ⟨1452749, by decide⟩ ⟨10, 2, 0, 1452749, 27550, 681, 1048576⟩
    (by decide) selected_cut_50740

theorem selected_cut_50741 : selected 11 ⟨1452753, by decide⟩
    (prefixPartial 10 27551) = some ⟨10, 2, 0, 1452753, 27551, 53, 1048576⟩ := by
  decide +kernel

theorem context_10_27551_1452753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27551 ⟨1452753, by decide⟩ :=
  accepted_of_selected 10 27551 ⟨1452753, by decide⟩ ⟨10, 2, 0, 1452753, 27551, 53, 1048576⟩
    (by decide) selected_cut_50741

theorem unmarked_context_9_6887_1452754 : frontier 12 ⟨1452754, by decide⟩
    (prefixCache 9 6887) (prefixPartial 9 6887) = false := by
  decide +kernel

theorem node_context_9_6887_1452754 : EJMOriginalGlobalDAGData.nodes 12 ⟨1452754, by decide⟩ =
    .split (coordinate 9) (![⟨1452669, by decide⟩,⟨1452715, by decide⟩,⟨1452749, by decide⟩,⟨1452753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6887_1452754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6887 ⟨1452754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6887
    ⟨1452754, by decide⟩ (by decide) (![⟨1452669, by decide⟩,⟨1452715, by decide⟩,⟨1452749, by decide⟩,⟨1452753, by decide⟩]) unmarked_context_9_6887_1452754 node_context_9_6887_1452754
  intro a
  fin_cases a
  · exact context_10_27548_1452669
  · exact context_10_27549_1452715
  · exact context_10_27550_1452749
  · exact context_10_27551_1452753

theorem unmarked_context_8_1721_1452755 : frontier 13 ⟨1452755, by decide⟩
    (prefixCache 8 1721) (prefixPartial 8 1721) = false := by
  decide +kernel

theorem node_context_8_1721_1452755 : EJMOriginalGlobalDAGData.nodes 13 ⟨1452755, by decide⟩ =
    .split (coordinate 8) (![⟨1451746, by decide⟩,⟨1452297, by decide⟩,⟨1452584, by decide⟩,⟨1452754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1721_1452755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1721 ⟨1452755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1721
    ⟨1452755, by decide⟩ (by decide) (![⟨1451746, by decide⟩,⟨1452297, by decide⟩,⟨1452584, by decide⟩,⟨1452754, by decide⟩]) unmarked_context_8_1721_1452755 node_context_8_1721_1452755
  intro a
  fin_cases a
  · exact context_9_6884_1451746
  · exact context_9_6885_1452297
  · exact context_9_6886_1452584
  · exact context_9_6887_1452754

theorem selected_cut_50742 : selected 11 ⟨1452889, by decide⟩
    (prefixPartial 10 27552) = some ⟨10, 2, 0, 1452889, 27552, 3533, 1048576⟩ := by
  decide +kernel

theorem context_10_27552_1452889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27552 ⟨1452889, by decide⟩ :=
  accepted_of_selected 10 27552 ⟨1452889, by decide⟩ ⟨10, 2, 0, 1452889, 27552, 3533, 1048576⟩
    (by decide) selected_cut_50742

theorem selected_cut_50743 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 440848) = some ⟨12, 1, 0, 435790, 440848, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440848_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440848 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 440848 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 440848, 1, 65536⟩
    (by decide) selected_cut_50743

theorem selected_cut_50744 : selected 9 ⟨1452957, by decide⟩
    (prefixPartial 12 440849) = some ⟨12, 2, 0, 1452957, 440849, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_440849_1452957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440849 ⟨1452957, by decide⟩ :=
  accepted_of_selected 12 440849 ⟨1452957, by decide⟩ ⟨12, 2, 0, 1452957, 440849, 2297, 65536⟩
    (by decide) selected_cut_50744

theorem selected_cut_50745 : selected 9 ⟨1453018, by decide⟩
    (prefixPartial 12 440850) = some ⟨12, 2, 0, 1453018, 440850, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_440850_1453018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440850 ⟨1453018, by decide⟩ :=
  accepted_of_selected 12 440850 ⟨1453018, by decide⟩ ⟨12, 2, 0, 1453018, 440850, 1965, 65536⟩
    (by decide) selected_cut_50745

theorem selected_cut_50746 : selected 9 ⟨1453073, by decide⟩
    (prefixPartial 12 440851) = some ⟨12, 2, 0, 1453073, 440851, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_440851_1453073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440851 ⟨1453073, by decide⟩ :=
  accepted_of_selected 12 440851 ⟨1453073, by decide⟩ ⟨12, 2, 0, 1453073, 440851, 2013, 65536⟩
    (by decide) selected_cut_50746

theorem unmarked_context_11_110212_1453074 : frontier 10 ⟨1453074, by decide⟩
    (prefixCache 11 110212) (prefixPartial 11 110212) = false := by
  decide +kernel

theorem node_context_11_110212_1453074 : EJMOriginalGlobalDAGData.nodes 10 ⟨1453074, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1452957, by decide⟩,⟨1453018, by decide⟩,⟨1453073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110212_1453074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110212 ⟨1453074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110212
    ⟨1453074, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1452957, by decide⟩,⟨1453018, by decide⟩,⟨1453073, by decide⟩]) unmarked_context_11_110212_1453074 node_context_11_110212_1453074
  intro a
  fin_cases a
  · exact context_12_440848_435790
  · exact context_12_440849_1452957
  · exact context_12_440850_1453018
  · exact context_12_440851_1453073

theorem selected_cut_50747 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 110213) = some ⟨11, 1, 0, 1192826, 110213, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110213_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110213 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 110213 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 110213, 1, 262144⟩
    (by decide) selected_cut_50747

theorem selected_cut_50748 : selected 10 ⟨1453154, by decide⟩
    (prefixPartial 11 110214) = some ⟨11, 2, 0, 1453154, 110214, 3117, 262144⟩ := by
  decide +kernel

theorem context_11_110214_1453154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110214 ⟨1453154, by decide⟩ :=
  accepted_of_selected 11 110214 ⟨1453154, by decide⟩ ⟨11, 2, 0, 1453154, 110214, 3117, 262144⟩
    (by decide) selected_cut_50748

theorem selected_cut_50749 : selected 10 ⟨1453270, by decide⟩
    (prefixPartial 11 110215) = some ⟨11, 2, 0, 1453270, 110215, 3977, 262144⟩ := by
  decide +kernel

theorem context_11_110215_1453270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110215 ⟨1453270, by decide⟩ :=
  accepted_of_selected 11 110215 ⟨1453270, by decide⟩ ⟨11, 2, 0, 1453270, 110215, 3977, 262144⟩
    (by decide) selected_cut_50749

theorem unmarked_context_10_27553_1453271 : frontier 11 ⟨1453271, by decide⟩
    (prefixCache 10 27553) (prefixPartial 10 27553) = false := by
  decide +kernel

theorem node_context_10_27553_1453271 : EJMOriginalGlobalDAGData.nodes 11 ⟨1453271, by decide⟩ =
    .split (coordinate 10) (![⟨1453074, by decide⟩,⟨1192826, by decide⟩,⟨1453154, by decide⟩,⟨1453270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27553_1453271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27553 ⟨1453271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27553
    ⟨1453271, by decide⟩ (by decide) (![⟨1453074, by decide⟩,⟨1192826, by decide⟩,⟨1453154, by decide⟩,⟨1453270, by decide⟩]) unmarked_context_10_27553_1453271 node_context_10_27553_1453271
  intro a
  fin_cases a
  · exact context_11_110212_1453074
  · exact context_11_110213_1192826
  · exact context_11_110214_1453154
  · exact context_11_110215_1453270

theorem selected_cut_50750 : selected 9 ⟨1448897, by decide⟩
    (prefixPartial 12 440864) = some ⟨12, 1, 0, 1448897, 440864, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440864_1448897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440864 ⟨1448897, by decide⟩ :=
  accepted_of_selected 12 440864 ⟨1448897, by decide⟩ ⟨12, 1, 0, 1448897, 440864, 1, 65536⟩
    (by decide) selected_cut_50750

theorem selected_cut_50751 : selected 9 ⟨1453318, by decide⟩
    (prefixPartial 12 440865) = some ⟨12, 2, 0, 1453318, 440865, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_440865_1453318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440865 ⟨1453318, by decide⟩ :=
  accepted_of_selected 12 440865 ⟨1453318, by decide⟩ ⟨12, 2, 0, 1453318, 440865, 1741, 65536⟩
    (by decide) selected_cut_50751

theorem selected_cut_50752 : selected 9 ⟨1453353, by decide⟩
    (prefixPartial 12 440866) = some ⟨12, 2, 0, 1453353, 440866, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_440866_1453353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440866 ⟨1453353, by decide⟩ :=
  accepted_of_selected 12 440866 ⟨1453353, by decide⟩ ⟨12, 2, 0, 1453353, 440866, 1481, 65536⟩
    (by decide) selected_cut_50752

theorem selected_cut_50753 : selected 9 ⟨1453385, by decide⟩
    (prefixPartial 12 440867) = some ⟨12, 2, 0, 1453385, 440867, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_440867_1453385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440867 ⟨1453385, by decide⟩ :=
  accepted_of_selected 12 440867 ⟨1453385, by decide⟩ ⟨12, 2, 0, 1453385, 440867, 1553, 65536⟩
    (by decide) selected_cut_50753

theorem unmarked_context_11_110216_1453386 : frontier 10 ⟨1453386, by decide⟩
    (prefixCache 11 110216) (prefixPartial 11 110216) = false := by
  decide +kernel

theorem node_context_11_110216_1453386 : EJMOriginalGlobalDAGData.nodes 10 ⟨1453386, by decide⟩ =
    .split (coordinate 11) (![⟨1448897, by decide⟩,⟨1453318, by decide⟩,⟨1453353, by decide⟩,⟨1453385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110216_1453386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110216 ⟨1453386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110216
    ⟨1453386, by decide⟩ (by decide) (![⟨1448897, by decide⟩,⟨1453318, by decide⟩,⟨1453353, by decide⟩,⟨1453385, by decide⟩]) unmarked_context_11_110216_1453386 node_context_11_110216_1453386
  intro a
  fin_cases a
  · exact context_12_440864_1448897
  · exact context_12_440865_1453318
  · exact context_12_440866_1453353
  · exact context_12_440867_1453385

theorem selected_cut_50754 : selected 10 ⟨1453452, by decide⟩
    (prefixPartial 11 110217) = some ⟨11, 2, 0, 1453452, 110217, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_110217_1453452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110217 ⟨1453452, by decide⟩ :=
  accepted_of_selected 11 110217 ⟨1453452, by decide⟩ ⟨11, 2, 0, 1453452, 110217, 2873, 262144⟩
    (by decide) selected_cut_50754

theorem selected_cut_50755 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110218) = some ⟨11, 1, 0, 900587, 110218, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110218_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110218 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110218 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110218, 1, 262144⟩
    (by decide) selected_cut_50755

theorem selected_cut_50756 : selected 10 ⟨1453532, by decide⟩
    (prefixPartial 11 110219) = some ⟨11, 2, 0, 1453532, 110219, 2977, 262144⟩ := by
  decide +kernel

theorem context_11_110219_1453532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110219 ⟨1453532, by decide⟩ :=
  accepted_of_selected 11 110219 ⟨1453532, by decide⟩ ⟨11, 2, 0, 1453532, 110219, 2977, 262144⟩
    (by decide) selected_cut_50756

theorem unmarked_context_10_27554_1453533 : frontier 11 ⟨1453533, by decide⟩
    (prefixCache 10 27554) (prefixPartial 10 27554) = false := by
  decide +kernel

theorem node_context_10_27554_1453533 : EJMOriginalGlobalDAGData.nodes 11 ⟨1453533, by decide⟩ =
    .split (coordinate 10) (![⟨1453386, by decide⟩,⟨1453452, by decide⟩,⟨900587, by decide⟩,⟨1453532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27554_1453533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27554 ⟨1453533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27554
    ⟨1453533, by decide⟩ (by decide) (![⟨1453386, by decide⟩,⟨1453452, by decide⟩,⟨900587, by decide⟩,⟨1453532, by decide⟩]) unmarked_context_10_27554_1453533 node_context_10_27554_1453533
  intro a
  fin_cases a
  · exact context_11_110216_1453386
  · exact context_11_110217_1453452
  · exact context_11_110218_900587
  · exact context_11_110219_1453532

theorem selected_cut_50757 : selected 9 ⟨1453534, by decide⟩
    (prefixPartial 12 440880) = some ⟨12, 1, 0, 1453534, 440880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_440880_1453534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440880 ⟨1453534, by decide⟩ :=
  accepted_of_selected 12 440880 ⟨1453534, by decide⟩ ⟨12, 1, 0, 1453534, 440880, 1, 65536⟩
    (by decide) selected_cut_50757

theorem selected_cut_50758 : selected 9 ⟨1453580, by decide⟩
    (prefixPartial 12 440881) = some ⟨12, 2, 0, 1453580, 440881, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_440881_1453580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440881 ⟨1453580, by decide⟩ :=
  accepted_of_selected 12 440881 ⟨1453580, by decide⟩ ⟨12, 2, 0, 1453580, 440881, 1817, 65536⟩
    (by decide) selected_cut_50758

theorem selected_cut_50759 : selected 9 ⟨1453612, by decide⟩
    (prefixPartial 12 440882) = some ⟨12, 2, 0, 1453612, 440882, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_440882_1453612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440882 ⟨1453612, by decide⟩ :=
  accepted_of_selected 12 440882 ⟨1453612, by decide⟩ ⟨12, 2, 0, 1453612, 440882, 1409, 65536⟩
    (by decide) selected_cut_50759

theorem selected_cut_50760 : selected 9 ⟨1453647, by decide⟩
    (prefixPartial 12 440883) = some ⟨12, 2, 0, 1453647, 440883, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_440883_1453647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 440883 ⟨1453647, by decide⟩ :=
  accepted_of_selected 12 440883 ⟨1453647, by decide⟩ ⟨12, 2, 0, 1453647, 440883, 1525, 65536⟩
    (by decide) selected_cut_50760

theorem unmarked_context_11_110220_1453648 : frontier 10 ⟨1453648, by decide⟩
    (prefixCache 11 110220) (prefixPartial 11 110220) = false := by
  decide +kernel

theorem node_context_11_110220_1453648 : EJMOriginalGlobalDAGData.nodes 10 ⟨1453648, by decide⟩ =
    .split (coordinate 11) (![⟨1453534, by decide⟩,⟨1453580, by decide⟩,⟨1453612, by decide⟩,⟨1453647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_110220_1453648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110220 ⟨1453648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 110220
    ⟨1453648, by decide⟩ (by decide) (![⟨1453534, by decide⟩,⟨1453580, by decide⟩,⟨1453612, by decide⟩,⟨1453647, by decide⟩]) unmarked_context_11_110220_1453648 node_context_11_110220_1453648
  intro a
  fin_cases a
  · exact context_12_440880_1453534
  · exact context_12_440881_1453580
  · exact context_12_440882_1453612
  · exact context_12_440883_1453647

theorem selected_cut_50761 : selected 10 ⟨1453713, by decide⟩
    (prefixPartial 11 110221) = some ⟨11, 2, 0, 1453713, 110221, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_110221_1453713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110221 ⟨1453713, by decide⟩ :=
  accepted_of_selected 11 110221 ⟨1453713, by decide⟩ ⟨11, 2, 0, 1453713, 110221, 2665, 262144⟩
    (by decide) selected_cut_50761

theorem selected_cut_50762 : selected 10 ⟨1453757, by decide⟩
    (prefixPartial 11 110222) = some ⟨11, 2, 0, 1453757, 110222, 2201, 262144⟩ := by
  decide +kernel

theorem context_11_110222_1453757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110222 ⟨1453757, by decide⟩ :=
  accepted_of_selected 11 110222 ⟨1453757, by decide⟩ ⟨11, 2, 0, 1453757, 110222, 2201, 262144⟩
    (by decide) selected_cut_50762

theorem selected_cut_50763 : selected 10 ⟨1453758, by decide⟩
    (prefixPartial 11 110223) = some ⟨11, 2, 0, 1453758, 110223, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110223_1453758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110223 ⟨1453758, by decide⟩ :=
  accepted_of_selected 11 110223 ⟨1453758, by decide⟩ ⟨11, 2, 0, 1453758, 110223, 5, 262144⟩
    (by decide) selected_cut_50763

theorem unmarked_context_10_27555_1453759 : frontier 11 ⟨1453759, by decide⟩
    (prefixCache 10 27555) (prefixPartial 10 27555) = false := by
  decide +kernel

theorem node_context_10_27555_1453759 : EJMOriginalGlobalDAGData.nodes 11 ⟨1453759, by decide⟩ =
    .split (coordinate 10) (![⟨1453648, by decide⟩,⟨1453713, by decide⟩,⟨1453757, by decide⟩,⟨1453758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27555_1453759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27555 ⟨1453759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27555
    ⟨1453759, by decide⟩ (by decide) (![⟨1453648, by decide⟩,⟨1453713, by decide⟩,⟨1453757, by decide⟩,⟨1453758, by decide⟩]) unmarked_context_10_27555_1453759 node_context_10_27555_1453759
  intro a
  fin_cases a
  · exact context_11_110220_1453648
  · exact context_11_110221_1453713
  · exact context_11_110222_1453757
  · exact context_11_110223_1453758

theorem unmarked_context_9_6888_1453760 : frontier 12 ⟨1453760, by decide⟩
    (prefixCache 9 6888) (prefixPartial 9 6888) = false := by
  decide +kernel

theorem node_context_9_6888_1453760 : EJMOriginalGlobalDAGData.nodes 12 ⟨1453760, by decide⟩ =
    .split (coordinate 9) (![⟨1452889, by decide⟩,⟨1453271, by decide⟩,⟨1453533, by decide⟩,⟨1453759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6888_1453760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6888 ⟨1453760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6888
    ⟨1453760, by decide⟩ (by decide) (![⟨1452889, by decide⟩,⟨1453271, by decide⟩,⟨1453533, by decide⟩,⟨1453759, by decide⟩]) unmarked_context_9_6888_1453760 node_context_9_6888_1453760
  intro a
  fin_cases a
  · exact context_10_27552_1452889
  · exact context_10_27553_1453271
  · exact context_10_27554_1453533
  · exact context_10_27555_1453759

theorem selected_cut_50764 : selected 10 ⟨1449508, by decide⟩
    (prefixPartial 11 110224) = some ⟨11, 2, 0, 1449508, 110224, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110224_1449508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110224 ⟨1449508, by decide⟩ :=
  accepted_of_selected 11 110224 ⟨1449508, by decide⟩ ⟨11, 2, 0, 1449508, 110224, 5, 262144⟩
    (by decide) selected_cut_50764

theorem selected_cut_50765 : selected 10 ⟨1453846, by decide⟩
    (prefixPartial 11 110225) = some ⟨11, 2, 0, 1453846, 110225, 3633, 262144⟩ := by
  decide +kernel

theorem context_11_110225_1453846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110225 ⟨1453846, by decide⟩ :=
  accepted_of_selected 11 110225 ⟨1453846, by decide⟩ ⟨11, 2, 0, 1453846, 110225, 3633, 262144⟩
    (by decide) selected_cut_50765

theorem selected_cut_50766 : selected 10 ⟨1453891, by decide⟩
    (prefixPartial 11 110226) = some ⟨11, 2, 0, 1453891, 110226, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_110226_1453891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110226 ⟨1453891, by decide⟩ :=
  accepted_of_selected 11 110226 ⟨1453891, by decide⟩ ⟨11, 2, 0, 1453891, 110226, 2009, 262144⟩
    (by decide) selected_cut_50766

theorem selected_cut_50767 : selected 10 ⟨1453956, by decide⟩
    (prefixPartial 11 110227) = some ⟨11, 2, 0, 1453956, 110227, 2525, 262144⟩ := by
  decide +kernel

theorem context_11_110227_1453956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110227 ⟨1453956, by decide⟩ :=
  accepted_of_selected 11 110227 ⟨1453956, by decide⟩ ⟨11, 2, 0, 1453956, 110227, 2525, 262144⟩
    (by decide) selected_cut_50767

theorem unmarked_context_10_27556_1453957 : frontier 11 ⟨1453957, by decide⟩
    (prefixCache 10 27556) (prefixPartial 10 27556) = false := by
  decide +kernel

theorem node_context_10_27556_1453957 : EJMOriginalGlobalDAGData.nodes 11 ⟨1453957, by decide⟩ =
    .split (coordinate 10) (![⟨1449508, by decide⟩,⟨1453846, by decide⟩,⟨1453891, by decide⟩,⟨1453956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27556_1453957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27556 ⟨1453957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27556
    ⟨1453957, by decide⟩ (by decide) (![⟨1449508, by decide⟩,⟨1453846, by decide⟩,⟨1453891, by decide⟩,⟨1453956, by decide⟩]) unmarked_context_10_27556_1453957 node_context_10_27556_1453957
  intro a
  fin_cases a
  · exact context_11_110224_1449508
  · exact context_11_110225_1453846
  · exact context_11_110226_1453891
  · exact context_11_110227_1453956

theorem selected_cut_50768 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 27557) = some ⟨10, 1, 0, 893098, 27557, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_27557_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27557 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 27557 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 27557, 1, 1048576⟩
    (by decide) selected_cut_50768

theorem selected_cut_50769 : selected 10 ⟨1453993, by decide⟩
    (prefixPartial 11 110232) = some ⟨11, 2, 0, 1453993, 110232, 1677, 262144⟩ := by
  decide +kernel

theorem context_11_110232_1453993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110232 ⟨1453993, by decide⟩ :=
  accepted_of_selected 11 110232 ⟨1453993, by decide⟩ ⟨11, 2, 0, 1453993, 110232, 1677, 262144⟩
    (by decide) selected_cut_50769

theorem selected_cut_50770 : selected 10 ⟨1454052, by decide⟩
    (prefixPartial 11 110233) = some ⟨11, 2, 0, 1454052, 110233, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_110233_1454052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110233 ⟨1454052, by decide⟩ :=
  accepted_of_selected 11 110233 ⟨1454052, by decide⟩ ⟨11, 2, 0, 1454052, 110233, 2321, 262144⟩
    (by decide) selected_cut_50770

theorem selected_cut_50771 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 110234) = some ⟨11, 1, 0, 900587, 110234, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110234_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110234 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 110234 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 110234, 1, 262144⟩
    (by decide) selected_cut_50771

theorem selected_cut_50772 : selected 10 ⟨1454090, by decide⟩
    (prefixPartial 11 110235) = some ⟨11, 2, 0, 1454090, 110235, 1509, 262144⟩ := by
  decide +kernel

theorem context_11_110235_1454090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110235 ⟨1454090, by decide⟩ :=
  accepted_of_selected 11 110235 ⟨1454090, by decide⟩ ⟨11, 2, 0, 1454090, 110235, 1509, 262144⟩
    (by decide) selected_cut_50772

theorem unmarked_context_10_27558_1454091 : frontier 11 ⟨1454091, by decide⟩
    (prefixCache 10 27558) (prefixPartial 10 27558) = false := by
  decide +kernel

theorem node_context_10_27558_1454091 : EJMOriginalGlobalDAGData.nodes 11 ⟨1454091, by decide⟩ =
    .split (coordinate 10) (![⟨1453993, by decide⟩,⟨1454052, by decide⟩,⟨900587, by decide⟩,⟨1454090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27558_1454091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27558 ⟨1454091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27558
    ⟨1454091, by decide⟩ (by decide) (![⟨1453993, by decide⟩,⟨1454052, by decide⟩,⟨900587, by decide⟩,⟨1454090, by decide⟩]) unmarked_context_10_27558_1454091 node_context_10_27558_1454091
  intro a
  fin_cases a
  · exact context_11_110232_1453993
  · exact context_11_110233_1454052
  · exact context_11_110234_900587
  · exact context_11_110235_1454090

theorem selected_cut_50773 : selected 10 ⟨1454119, by decide⟩
    (prefixPartial 11 110236) = some ⟨11, 2, 0, 1454119, 110236, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_110236_1454119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110236 ⟨1454119, by decide⟩ :=
  accepted_of_selected 11 110236 ⟨1454119, by decide⟩ ⟨11, 2, 0, 1454119, 110236, 1465, 262144⟩
    (by decide) selected_cut_50773

theorem selected_cut_50774 : selected 10 ⟨1454161, by decide⟩
    (prefixPartial 11 110237) = some ⟨11, 2, 0, 1454161, 110237, 2029, 262144⟩ := by
  decide +kernel

theorem context_11_110237_1454161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110237 ⟨1454161, by decide⟩ :=
  accepted_of_selected 11 110237 ⟨1454161, by decide⟩ ⟨11, 2, 0, 1454161, 110237, 2029, 262144⟩
    (by decide) selected_cut_50774

theorem selected_cut_50775 : selected 10 ⟨1454187, by decide⟩
    (prefixPartial 11 110238) = some ⟨11, 2, 0, 1454187, 110238, 1145, 262144⟩ := by
  decide +kernel

theorem context_11_110238_1454187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110238 ⟨1454187, by decide⟩ :=
  accepted_of_selected 11 110238 ⟨1454187, by decide⟩ ⟨11, 2, 0, 1454187, 110238, 1145, 262144⟩
    (by decide) selected_cut_50775

theorem selected_cut_50776 : selected 10 ⟨1454188, by decide⟩
    (prefixPartial 11 110239) = some ⟨11, 2, 0, 1454188, 110239, 5, 262144⟩ := by
  decide +kernel

theorem context_11_110239_1454188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110239 ⟨1454188, by decide⟩ :=
  accepted_of_selected 11 110239 ⟨1454188, by decide⟩ ⟨11, 2, 0, 1454188, 110239, 5, 262144⟩
    (by decide) selected_cut_50776

theorem unmarked_context_10_27559_1454189 : frontier 11 ⟨1454189, by decide⟩
    (prefixCache 10 27559) (prefixPartial 10 27559) = false := by
  decide +kernel

theorem node_context_10_27559_1454189 : EJMOriginalGlobalDAGData.nodes 11 ⟨1454189, by decide⟩ =
    .split (coordinate 10) (![⟨1454119, by decide⟩,⟨1454161, by decide⟩,⟨1454187, by decide⟩,⟨1454188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27559_1454189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27559 ⟨1454189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27559
    ⟨1454189, by decide⟩ (by decide) (![⟨1454119, by decide⟩,⟨1454161, by decide⟩,⟨1454187, by decide⟩,⟨1454188, by decide⟩]) unmarked_context_10_27559_1454189 node_context_10_27559_1454189
  intro a
  fin_cases a
  · exact context_11_110236_1454119
  · exact context_11_110237_1454161
  · exact context_11_110238_1454187
  · exact context_11_110239_1454188

theorem unmarked_context_9_6889_1454190 : frontier 12 ⟨1454190, by decide⟩
    (prefixCache 9 6889) (prefixPartial 9 6889) = false := by
  decide +kernel

theorem node_context_9_6889_1454190 : EJMOriginalGlobalDAGData.nodes 12 ⟨1454190, by decide⟩ =
    .split (coordinate 9) (![⟨1453957, by decide⟩,⟨893098, by decide⟩,⟨1454091, by decide⟩,⟨1454189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6889_1454190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6889 ⟨1454190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6889
    ⟨1454190, by decide⟩ (by decide) (![⟨1453957, by decide⟩,⟨893098, by decide⟩,⟨1454091, by decide⟩,⟨1454189, by decide⟩]) unmarked_context_9_6889_1454190 node_context_9_6889_1454190
  intro a
  fin_cases a
  · exact context_10_27556_1453957
  · exact context_10_27557_893098
  · exact context_10_27558_1454091
  · exact context_10_27559_1454189

theorem selected_cut_50777 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 110240) = some ⟨11, 1, 0, 1375697, 110240, 1, 262144⟩ := by
  decide +kernel

theorem context_11_110240_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110240 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 110240 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 110240, 1, 262144⟩
    (by decide) selected_cut_50777

theorem selected_cut_50778 : selected 10 ⟨1454228, by decide⟩
    (prefixPartial 11 110241) = some ⟨11, 2, 0, 1454228, 110241, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_110241_1454228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110241 ⟨1454228, by decide⟩ :=
  accepted_of_selected 11 110241 ⟨1454228, by decide⟩ ⟨11, 2, 0, 1454228, 110241, 1425, 262144⟩
    (by decide) selected_cut_50778

theorem selected_cut_50779 : selected 10 ⟨1454268, by decide⟩
    (prefixPartial 11 110242) = some ⟨11, 2, 0, 1454268, 110242, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_110242_1454268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110242 ⟨1454268, by decide⟩ :=
  accepted_of_selected 11 110242 ⟨1454268, by decide⟩ ⟨11, 2, 0, 1454268, 110242, 1645, 262144⟩
    (by decide) selected_cut_50779

theorem selected_cut_50780 : selected 10 ⟨1454298, by decide⟩
    (prefixPartial 11 110243) = some ⟨11, 2, 0, 1454298, 110243, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_110243_1454298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 110243 ⟨1454298, by decide⟩ :=
  accepted_of_selected 11 110243 ⟨1454298, by decide⟩ ⟨11, 2, 0, 1454298, 110243, 1413, 262144⟩
    (by decide) selected_cut_50780

theorem unmarked_context_10_27560_1454299 : frontier 11 ⟨1454299, by decide⟩
    (prefixCache 10 27560) (prefixPartial 10 27560) = false := by
  decide +kernel

theorem node_context_10_27560_1454299 : EJMOriginalGlobalDAGData.nodes 11 ⟨1454299, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1454228, by decide⟩,⟨1454268, by decide⟩,⟨1454298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_27560_1454299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27560 ⟨1454299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 27560
    ⟨1454299, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1454228, by decide⟩,⟨1454268, by decide⟩,⟨1454298, by decide⟩]) unmarked_context_10_27560_1454299 node_context_10_27560_1454299
  intro a
  fin_cases a
  · exact context_11_110240_1375697
  · exact context_11_110241_1454228
  · exact context_11_110242_1454268
  · exact context_11_110243_1454298

theorem selected_cut_50781 : selected 11 ⟨1454377, by decide⟩
    (prefixPartial 10 27561) = some ⟨10, 2, 0, 1454377, 27561, 3101, 1048576⟩ := by
  decide +kernel

theorem context_10_27561_1454377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27561 ⟨1454377, by decide⟩ :=
  accepted_of_selected 10 27561 ⟨1454377, by decide⟩ ⟨10, 2, 0, 1454377, 27561, 3101, 1048576⟩
    (by decide) selected_cut_50781

theorem selected_cut_50782 : selected 11 ⟨1432895, by decide⟩
    (prefixPartial 10 27562) = some ⟨10, 2, 0, 1432895, 27562, 5, 1048576⟩ := by
  decide +kernel

theorem context_10_27562_1432895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27562 ⟨1432895, by decide⟩ :=
  accepted_of_selected 10 27562 ⟨1432895, by decide⟩ ⟨10, 2, 0, 1432895, 27562, 5, 1048576⟩
    (by decide) selected_cut_50782

theorem selected_cut_50783 : selected 11 ⟨1454432, by decide⟩
    (prefixPartial 10 27563) = some ⟨10, 2, 0, 1454432, 27563, 2309, 1048576⟩ := by
  decide +kernel

theorem context_10_27563_1454432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27563 ⟨1454432, by decide⟩ :=
  accepted_of_selected 10 27563 ⟨1454432, by decide⟩ ⟨10, 2, 0, 1454432, 27563, 2309, 1048576⟩
    (by decide) selected_cut_50783

theorem unmarked_context_9_6890_1454433 : frontier 12 ⟨1454433, by decide⟩
    (prefixCache 9 6890) (prefixPartial 9 6890) = false := by
  decide +kernel

theorem node_context_9_6890_1454433 : EJMOriginalGlobalDAGData.nodes 12 ⟨1454433, by decide⟩ =
    .split (coordinate 9) (![⟨1454299, by decide⟩,⟨1454377, by decide⟩,⟨1432895, by decide⟩,⟨1454432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6890_1454433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6890 ⟨1454433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6890
    ⟨1454433, by decide⟩ (by decide) (![⟨1454299, by decide⟩,⟨1454377, by decide⟩,⟨1432895, by decide⟩,⟨1454432, by decide⟩]) unmarked_context_9_6890_1454433 node_context_9_6890_1454433
  intro a
  fin_cases a
  · exact context_10_27560_1454299
  · exact context_10_27561_1454377
  · exact context_10_27562_1432895
  · exact context_10_27563_1454432

theorem selected_cut_50784 : selected 12 ⟨1454554, by decide⟩
    (prefixPartial 9 6891) = some ⟨9, 2, 0, 1454554, 6891, 3793, 4194304⟩ := by
  decide +kernel

theorem context_9_6891_1454554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6891 ⟨1454554, by decide⟩ :=
  accepted_of_selected 9 6891 ⟨1454554, by decide⟩ ⟨9, 2, 0, 1454554, 6891, 3793, 4194304⟩
    (by decide) selected_cut_50784

theorem unmarked_context_8_1722_1454555 : frontier 13 ⟨1454555, by decide⟩
    (prefixCache 8 1722) (prefixPartial 8 1722) = false := by
  decide +kernel

theorem node_context_8_1722_1454555 : EJMOriginalGlobalDAGData.nodes 13 ⟨1454555, by decide⟩ =
    .split (coordinate 8) (![⟨1453760, by decide⟩,⟨1454190, by decide⟩,⟨1454433, by decide⟩,⟨1454554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1722_1454555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1722 ⟨1454555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1722
    ⟨1454555, by decide⟩ (by decide) (![⟨1453760, by decide⟩,⟨1454190, by decide⟩,⟨1454433, by decide⟩,⟨1454554, by decide⟩]) unmarked_context_8_1722_1454555 node_context_8_1722_1454555
  intro a
  fin_cases a
  · exact context_9_6888_1453760
  · exact context_9_6889_1454190
  · exact context_9_6890_1454433
  · exact context_9_6891_1454554

theorem selected_cut_50785 : selected 11 ⟨1454691, by decide⟩
    (prefixPartial 10 27568) = some ⟨10, 2, 0, 1454691, 27568, 3529, 1048576⟩ := by
  decide +kernel

theorem context_10_27568_1454691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 27568 ⟨1454691, by decide⟩ :=
  accepted_of_selected 10 27568 ⟨1454691, by decide⟩ ⟨10, 2, 0, 1454691, 27568, 3529, 1048576⟩
    (by decide) selected_cut_50785

theorem selected_cut_50786 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 441104) = some ⟨12, 1, 0, 435790, 441104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_441104_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441104 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 441104 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 441104, 1, 65536⟩
    (by decide) selected_cut_50786

theorem selected_cut_50787 : selected 9 ⟨1454742, by decide⟩
    (prefixPartial 12 441105) = some ⟨12, 2, 0, 1454742, 441105, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_441105_1454742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 441105 ⟨1454742, by decide⟩ :=
  accepted_of_selected 12 441105 ⟨1454742, by decide⟩ ⟨12, 2, 0, 1454742, 441105, 2185, 65536⟩
    (by decide) selected_cut_50787

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
