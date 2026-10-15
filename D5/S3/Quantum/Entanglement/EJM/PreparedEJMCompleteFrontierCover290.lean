/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover289
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_27843 : selected 8 ⟨703898, by decide⟩
    (prefixPartial 13 367716) = some ⟨13, 2, 0, 703898, 367716, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_367716_703898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367716 ⟨703898, by decide⟩ :=
  accepted_of_selected 13 367716 ⟨703898, by decide⟩ ⟨13, 2, 0, 703898, 367716, 1777, 16384⟩
    (by decide) selected_cut_27843

theorem selected_cut_27844 : selected 8 ⟨703932, by decide⟩
    (prefixPartial 13 367717) = some ⟨13, 2, 0, 703932, 367717, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_367717_703932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367717 ⟨703932, by decide⟩ :=
  accepted_of_selected 13 367717 ⟨703932, by decide⟩ ⟨13, 2, 0, 703932, 367717, 1681, 16384⟩
    (by decide) selected_cut_27844

theorem selected_cut_27845 : selected 8 ⟨703958, by decide⟩
    (prefixPartial 13 367718) = some ⟨13, 2, 0, 703958, 367718, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_367718_703958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367718 ⟨703958, by decide⟩ :=
  accepted_of_selected 13 367718 ⟨703958, by decide⟩ ⟨13, 2, 0, 703958, 367718, 1765, 16384⟩
    (by decide) selected_cut_27845

theorem selected_cut_27846 : selected 8 ⟨703965, by decide⟩
    (prefixPartial 13 367719) = some ⟨13, 2, 0, 703965, 367719, 673, 16384⟩ := by
  decide +kernel

theorem context_13_367719_703965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367719 ⟨703965, by decide⟩ :=
  accepted_of_selected 13 367719 ⟨703965, by decide⟩ ⟨13, 2, 0, 703965, 367719, 673, 16384⟩
    (by decide) selected_cut_27846

theorem unmarked_context_12_91929_703966 : frontier 9 ⟨703966, by decide⟩
    (prefixCache 12 91929) (prefixPartial 12 91929) = false := by
  decide +kernel

theorem node_context_12_91929_703966 : EJMOriginalGlobalDAGData.nodes 9 ⟨703966, by decide⟩ =
    .split (coordinate 12) (![⟨703898, by decide⟩,⟨703932, by decide⟩,⟨703958, by decide⟩,⟨703965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91929_703966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91929 ⟨703966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91929
    ⟨703966, by decide⟩ (by decide) (![⟨703898, by decide⟩,⟨703932, by decide⟩,⟨703958, by decide⟩,⟨703965, by decide⟩]) unmarked_context_12_91929_703966 node_context_12_91929_703966
  intro a
  fin_cases a
  · exact context_13_367716_703898
  · exact context_13_367717_703932
  · exact context_13_367718_703958
  · exact context_13_367719_703965

theorem selected_cut_27847 : selected 8 ⟨703991, by decide⟩
    (prefixPartial 13 367720) = some ⟨13, 2, 0, 703991, 367720, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_367720_703991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367720 ⟨703991, by decide⟩ :=
  accepted_of_selected 13 367720 ⟨703991, by decide⟩ ⟨13, 2, 0, 703991, 367720, 1445, 16384⟩
    (by decide) selected_cut_27847

theorem selected_cut_27848 : selected 8 ⟨704017, by decide⟩
    (prefixPartial 13 367721) = some ⟨13, 2, 0, 704017, 367721, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_367721_704017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367721 ⟨704017, by decide⟩ :=
  accepted_of_selected 13 367721 ⟨704017, by decide⟩ ⟨13, 2, 0, 704017, 367721, 1589, 16384⟩
    (by decide) selected_cut_27848

theorem selected_cut_27849 : selected 8 ⟨704038, by decide⟩
    (prefixPartial 13 367722) = some ⟨13, 2, 0, 704038, 367722, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_367722_704038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367722 ⟨704038, by decide⟩ :=
  accepted_of_selected 13 367722 ⟨704038, by decide⟩ ⟨13, 2, 0, 704038, 367722, 1653, 16384⟩
    (by decide) selected_cut_27849

theorem selected_cut_27850 : selected 8 ⟨704044, by decide⟩
    (prefixPartial 13 367723) = some ⟨13, 2, 0, 704044, 367723, 761, 16384⟩ := by
  decide +kernel

theorem context_13_367723_704044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367723 ⟨704044, by decide⟩ :=
  accepted_of_selected 13 367723 ⟨704044, by decide⟩ ⟨13, 2, 0, 704044, 367723, 761, 16384⟩
    (by decide) selected_cut_27850

theorem unmarked_context_12_91930_704045 : frontier 9 ⟨704045, by decide⟩
    (prefixCache 12 91930) (prefixPartial 12 91930) = false := by
  decide +kernel

theorem node_context_12_91930_704045 : EJMOriginalGlobalDAGData.nodes 9 ⟨704045, by decide⟩ =
    .split (coordinate 12) (![⟨703991, by decide⟩,⟨704017, by decide⟩,⟨704038, by decide⟩,⟨704044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91930_704045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91930 ⟨704045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91930
    ⟨704045, by decide⟩ (by decide) (![⟨703991, by decide⟩,⟨704017, by decide⟩,⟨704038, by decide⟩,⟨704044, by decide⟩]) unmarked_context_12_91930_704045 node_context_12_91930_704045
  intro a
  fin_cases a
  · exact context_13_367720_703991
  · exact context_13_367721_704017
  · exact context_13_367722_704038
  · exact context_13_367723_704044

theorem selected_cut_27851 : selected 8 ⟨704064, by decide⟩
    (prefixPartial 13 367724) = some ⟨13, 2, 0, 704064, 367724, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_367724_704064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367724 ⟨704064, by decide⟩ :=
  accepted_of_selected 13 367724 ⟨704064, by decide⟩ ⟨13, 2, 0, 704064, 367724, 1337, 16384⟩
    (by decide) selected_cut_27851

theorem selected_cut_27852 : selected 8 ⟨704094, by decide⟩
    (prefixPartial 13 367725) = some ⟨13, 2, 0, 704094, 367725, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_367725_704094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367725 ⟨704094, by decide⟩ :=
  accepted_of_selected 13 367725 ⟨704094, by decide⟩ ⟨13, 2, 0, 704094, 367725, 1721, 16384⟩
    (by decide) selected_cut_27852

theorem selected_cut_27853 : selected 8 ⟨704115, by decide⟩
    (prefixPartial 13 367726) = some ⟨13, 2, 0, 704115, 367726, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_367726_704115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367726 ⟨704115, by decide⟩ :=
  accepted_of_selected 13 367726 ⟨704115, by decide⟩ ⟨13, 2, 0, 704115, 367726, 1709, 16384⟩
    (by decide) selected_cut_27853

theorem selected_cut_27854 : selected 8 ⟨704120, by decide⟩
    (prefixPartial 13 367727) = some ⟨13, 2, 0, 704120, 367727, 657, 16384⟩ := by
  decide +kernel

theorem context_13_367727_704120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367727 ⟨704120, by decide⟩ :=
  accepted_of_selected 13 367727 ⟨704120, by decide⟩ ⟨13, 2, 0, 704120, 367727, 657, 16384⟩
    (by decide) selected_cut_27854

theorem unmarked_context_12_91931_704121 : frontier 9 ⟨704121, by decide⟩
    (prefixCache 12 91931) (prefixPartial 12 91931) = false := by
  decide +kernel

theorem node_context_12_91931_704121 : EJMOriginalGlobalDAGData.nodes 9 ⟨704121, by decide⟩ =
    .split (coordinate 12) (![⟨704064, by decide⟩,⟨704094, by decide⟩,⟨704115, by decide⟩,⟨704120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91931_704121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91931 ⟨704121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91931
    ⟨704121, by decide⟩ (by decide) (![⟨704064, by decide⟩,⟨704094, by decide⟩,⟨704115, by decide⟩,⟨704120, by decide⟩]) unmarked_context_12_91931_704121 node_context_12_91931_704121
  intro a
  fin_cases a
  · exact context_13_367724_704064
  · exact context_13_367725_704094
  · exact context_13_367726_704115
  · exact context_13_367727_704120

theorem unmarked_context_11_22982_704122 : frontier 10 ⟨704122, by decide⟩
    (prefixCache 11 22982) (prefixPartial 11 22982) = false := by
  decide +kernel

theorem node_context_11_22982_704122 : EJMOriginalGlobalDAGData.nodes 10 ⟨704122, by decide⟩ =
    .split (coordinate 11) (![⟨703876, by decide⟩,⟨703966, by decide⟩,⟨704045, by decide⟩,⟨704121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22982_704122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22982 ⟨704122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22982
    ⟨704122, by decide⟩ (by decide) (![⟨703876, by decide⟩,⟨703966, by decide⟩,⟨704045, by decide⟩,⟨704121, by decide⟩]) unmarked_context_11_22982_704122 node_context_11_22982_704122
  intro a
  fin_cases a
  · exact context_12_91928_703876
  · exact context_12_91929_703966
  · exact context_12_91930_704045
  · exact context_12_91931_704121

theorem selected_cut_27855 : selected 8 ⟨704139, by decide⟩
    (prefixPartial 13 367728) = some ⟨13, 2, 0, 704139, 367728, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_367728_704139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367728 ⟨704139, by decide⟩ :=
  accepted_of_selected 13 367728 ⟨704139, by decide⟩ ⟨13, 2, 0, 704139, 367728, 1285, 16384⟩
    (by decide) selected_cut_27855

theorem selected_cut_27856 : selected 8 ⟨704160, by decide⟩
    (prefixPartial 13 367729) = some ⟨13, 2, 0, 704160, 367729, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_367729_704160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367729 ⟨704160, by decide⟩ :=
  accepted_of_selected 13 367729 ⟨704160, by decide⟩ ⟨13, 2, 0, 704160, 367729, 1401, 16384⟩
    (by decide) selected_cut_27856

theorem selected_cut_27857 : selected 8 ⟨704177, by decide⟩
    (prefixPartial 13 367730) = some ⟨13, 2, 0, 704177, 367730, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_367730_704177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367730 ⟨704177, by decide⟩ :=
  accepted_of_selected 13 367730 ⟨704177, by decide⟩ ⟨13, 2, 0, 704177, 367730, 1241, 16384⟩
    (by decide) selected_cut_27857

theorem selected_cut_27858 : selected 8 ⟨704182, by decide⟩
    (prefixPartial 13 367731) = some ⟨13, 2, 0, 704182, 367731, 649, 16384⟩ := by
  decide +kernel

theorem context_13_367731_704182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367731 ⟨704182, by decide⟩ :=
  accepted_of_selected 13 367731 ⟨704182, by decide⟩ ⟨13, 2, 0, 704182, 367731, 649, 16384⟩
    (by decide) selected_cut_27858

theorem unmarked_context_12_91932_704183 : frontier 9 ⟨704183, by decide⟩
    (prefixCache 12 91932) (prefixPartial 12 91932) = false := by
  decide +kernel

theorem node_context_12_91932_704183 : EJMOriginalGlobalDAGData.nodes 9 ⟨704183, by decide⟩ =
    .split (coordinate 12) (![⟨704139, by decide⟩,⟨704160, by decide⟩,⟨704177, by decide⟩,⟨704182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91932_704183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91932 ⟨704183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91932
    ⟨704183, by decide⟩ (by decide) (![⟨704139, by decide⟩,⟨704160, by decide⟩,⟨704177, by decide⟩,⟨704182, by decide⟩]) unmarked_context_12_91932_704183 node_context_12_91932_704183
  intro a
  fin_cases a
  · exact context_13_367728_704139
  · exact context_13_367729_704160
  · exact context_13_367730_704177
  · exact context_13_367731_704182

theorem selected_cut_27859 : selected 8 ⟨704206, by decide⟩
    (prefixPartial 13 367732) = some ⟨13, 2, 0, 704206, 367732, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_367732_704206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367732 ⟨704206, by decide⟩ :=
  accepted_of_selected 13 367732 ⟨704206, by decide⟩ ⟨13, 2, 0, 704206, 367732, 1421, 16384⟩
    (by decide) selected_cut_27859

theorem selected_cut_27860 : selected 8 ⟨704241, by decide⟩
    (prefixPartial 13 367733) = some ⟨13, 2, 0, 704241, 367733, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_367733_704241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367733 ⟨704241, by decide⟩ :=
  accepted_of_selected 13 367733 ⟨704241, by decide⟩ ⟨13, 2, 0, 704241, 367733, 1565, 16384⟩
    (by decide) selected_cut_27860

theorem selected_cut_27861 : selected 8 ⟨704259, by decide⟩
    (prefixPartial 13 367734) = some ⟨13, 2, 0, 704259, 367734, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_367734_704259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367734 ⟨704259, by decide⟩ :=
  accepted_of_selected 13 367734 ⟨704259, by decide⟩ ⟨13, 2, 0, 704259, 367734, 1493, 16384⟩
    (by decide) selected_cut_27861

theorem selected_cut_27862 : selected 8 ⟨704264, by decide⟩
    (prefixPartial 13 367735) = some ⟨13, 2, 0, 704264, 367735, 573, 16384⟩ := by
  decide +kernel

theorem context_13_367735_704264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367735 ⟨704264, by decide⟩ :=
  accepted_of_selected 13 367735 ⟨704264, by decide⟩ ⟨13, 2, 0, 704264, 367735, 573, 16384⟩
    (by decide) selected_cut_27862

theorem unmarked_context_12_91933_704265 : frontier 9 ⟨704265, by decide⟩
    (prefixCache 12 91933) (prefixPartial 12 91933) = false := by
  decide +kernel

theorem node_context_12_91933_704265 : EJMOriginalGlobalDAGData.nodes 9 ⟨704265, by decide⟩ =
    .split (coordinate 12) (![⟨704206, by decide⟩,⟨704241, by decide⟩,⟨704259, by decide⟩,⟨704264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91933_704265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91933 ⟨704265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91933
    ⟨704265, by decide⟩ (by decide) (![⟨704206, by decide⟩,⟨704241, by decide⟩,⟨704259, by decide⟩,⟨704264, by decide⟩]) unmarked_context_12_91933_704265 node_context_12_91933_704265
  intro a
  fin_cases a
  · exact context_13_367732_704206
  · exact context_13_367733_704241
  · exact context_13_367734_704259
  · exact context_13_367735_704264

theorem selected_cut_27863 : selected 8 ⟨704283, by decide⟩
    (prefixPartial 13 367736) = some ⟨13, 2, 0, 704283, 367736, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_367736_704283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367736 ⟨704283, by decide⟩ :=
  accepted_of_selected 13 367736 ⟨704283, by decide⟩ ⟨13, 2, 0, 704283, 367736, 1221, 16384⟩
    (by decide) selected_cut_27863

theorem selected_cut_27864 : selected 8 ⟨704308, by decide⟩
    (prefixPartial 13 367737) = some ⟨13, 2, 0, 704308, 367737, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_367737_704308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367737 ⟨704308, by decide⟩ :=
  accepted_of_selected 13 367737 ⟨704308, by decide⟩ ⟨13, 2, 0, 704308, 367737, 1529, 16384⟩
    (by decide) selected_cut_27864

theorem selected_cut_27865 : selected 8 ⟨704325, by decide⟩
    (prefixPartial 13 367738) = some ⟨13, 2, 0, 704325, 367738, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_367738_704325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367738 ⟨704325, by decide⟩ :=
  accepted_of_selected 13 367738 ⟨704325, by decide⟩ ⟨13, 2, 0, 704325, 367738, 1253, 16384⟩
    (by decide) selected_cut_27865

theorem selected_cut_27866 : selected 8 ⟨704332, by decide⟩
    (prefixPartial 13 367739) = some ⟨13, 2, 0, 704332, 367739, 681, 16384⟩ := by
  decide +kernel

theorem context_13_367739_704332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367739 ⟨704332, by decide⟩ :=
  accepted_of_selected 13 367739 ⟨704332, by decide⟩ ⟨13, 2, 0, 704332, 367739, 681, 16384⟩
    (by decide) selected_cut_27866

theorem unmarked_context_12_91934_704333 : frontier 9 ⟨704333, by decide⟩
    (prefixCache 12 91934) (prefixPartial 12 91934) = false := by
  decide +kernel

theorem node_context_12_91934_704333 : EJMOriginalGlobalDAGData.nodes 9 ⟨704333, by decide⟩ =
    .split (coordinate 12) (![⟨704283, by decide⟩,⟨704308, by decide⟩,⟨704325, by decide⟩,⟨704332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91934_704333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91934 ⟨704333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91934
    ⟨704333, by decide⟩ (by decide) (![⟨704283, by decide⟩,⟨704308, by decide⟩,⟨704325, by decide⟩,⟨704332, by decide⟩]) unmarked_context_12_91934_704333 node_context_12_91934_704333
  intro a
  fin_cases a
  · exact context_13_367736_704283
  · exact context_13_367737_704308
  · exact context_13_367738_704325
  · exact context_13_367739_704332

theorem selected_cut_27867 : selected 9 ⟨340831, by decide⟩
    (prefixPartial 12 91935) = some ⟨12, 1, 0, 340831, 91935, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91935_340831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91935 ⟨340831, by decide⟩ :=
  accepted_of_selected 12 91935 ⟨340831, by decide⟩ ⟨12, 1, 0, 340831, 91935, 1, 65536⟩
    (by decide) selected_cut_27867

theorem unmarked_context_11_22983_704334 : frontier 10 ⟨704334, by decide⟩
    (prefixCache 11 22983) (prefixPartial 11 22983) = false := by
  decide +kernel

theorem node_context_11_22983_704334 : EJMOriginalGlobalDAGData.nodes 10 ⟨704334, by decide⟩ =
    .split (coordinate 11) (![⟨704183, by decide⟩,⟨704265, by decide⟩,⟨704333, by decide⟩,⟨340831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22983_704334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22983 ⟨704334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22983
    ⟨704334, by decide⟩ (by decide) (![⟨704183, by decide⟩,⟨704265, by decide⟩,⟨704333, by decide⟩,⟨340831, by decide⟩]) unmarked_context_11_22983_704334 node_context_11_22983_704334
  intro a
  fin_cases a
  · exact context_12_91932_704183
  · exact context_12_91933_704265
  · exact context_12_91934_704333
  · exact context_12_91935_340831

theorem unmarked_context_10_5745_704335 : frontier 11 ⟨704335, by decide⟩
    (prefixCache 10 5745) (prefixPartial 10 5745) = false := by
  decide +kernel

theorem node_context_10_5745_704335 : EJMOriginalGlobalDAGData.nodes 11 ⟨704335, by decide⟩ =
    .split (coordinate 10) (![⟨703474, by decide⟩,⟨703797, by decide⟩,⟨704122, by decide⟩,⟨704334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5745_704335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5745 ⟨704335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5745
    ⟨704335, by decide⟩ (by decide) (![⟨703474, by decide⟩,⟨703797, by decide⟩,⟨704122, by decide⟩,⟨704334, by decide⟩]) unmarked_context_10_5745_704335 node_context_10_5745_704335
  intro a
  fin_cases a
  · exact context_11_22980_703474
  · exact context_11_22981_703797
  · exact context_11_22982_704122
  · exact context_11_22983_704334

theorem selected_cut_27868 : selected 8 ⟨704355, by decide⟩
    (prefixPartial 13 367744) = some ⟨13, 2, 0, 704355, 367744, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_367744_704355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367744 ⟨704355, by decide⟩ :=
  accepted_of_selected 13 367744 ⟨704355, by decide⟩ ⟨13, 2, 0, 704355, 367744, 1245, 16384⟩
    (by decide) selected_cut_27868

theorem selected_cut_27869 : selected 8 ⟨704384, by decide⟩
    (prefixPartial 13 367745) = some ⟨13, 2, 0, 704384, 367745, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_367745_704384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367745 ⟨704384, by decide⟩ :=
  accepted_of_selected 13 367745 ⟨704384, by decide⟩ ⟨13, 2, 0, 704384, 367745, 1637, 16384⟩
    (by decide) selected_cut_27869

theorem selected_cut_27870 : selected 8 ⟨704395, by decide⟩
    (prefixPartial 13 367746) = some ⟨13, 2, 0, 704395, 367746, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_367746_704395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367746 ⟨704395, by decide⟩ :=
  accepted_of_selected 13 367746 ⟨704395, by decide⟩ ⟨13, 2, 0, 704395, 367746, 1037, 16384⟩
    (by decide) selected_cut_27870

theorem selected_cut_27871 : selected 8 ⟨704402, by decide⟩
    (prefixPartial 13 367747) = some ⟨13, 2, 0, 704402, 367747, 697, 16384⟩ := by
  decide +kernel

theorem context_13_367747_704402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367747 ⟨704402, by decide⟩ :=
  accepted_of_selected 13 367747 ⟨704402, by decide⟩ ⟨13, 2, 0, 704402, 367747, 697, 16384⟩
    (by decide) selected_cut_27871

theorem unmarked_context_12_91936_704403 : frontier 9 ⟨704403, by decide⟩
    (prefixCache 12 91936) (prefixPartial 12 91936) = false := by
  decide +kernel

theorem node_context_12_91936_704403 : EJMOriginalGlobalDAGData.nodes 9 ⟨704403, by decide⟩ =
    .split (coordinate 12) (![⟨704355, by decide⟩,⟨704384, by decide⟩,⟨704395, by decide⟩,⟨704402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91936_704403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91936 ⟨704403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91936
    ⟨704403, by decide⟩ (by decide) (![⟨704355, by decide⟩,⟨704384, by decide⟩,⟨704395, by decide⟩,⟨704402, by decide⟩]) unmarked_context_12_91936_704403 node_context_12_91936_704403
  intro a
  fin_cases a
  · exact context_13_367744_704355
  · exact context_13_367745_704384
  · exact context_13_367746_704395
  · exact context_13_367747_704402

theorem selected_cut_27872 : selected 8 ⟨704425, by decide⟩
    (prefixPartial 13 367748) = some ⟨13, 2, 0, 704425, 367748, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_367748_704425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367748 ⟨704425, by decide⟩ :=
  accepted_of_selected 13 367748 ⟨704425, by decide⟩ ⟨13, 2, 0, 704425, 367748, 1569, 16384⟩
    (by decide) selected_cut_27872

theorem selected_cut_27873 : selected 8 ⟨704453, by decide⟩
    (prefixPartial 13 367749) = some ⟨13, 2, 0, 704453, 367749, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_367749_704453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367749 ⟨704453, by decide⟩ :=
  accepted_of_selected 13 367749 ⟨704453, by decide⟩ ⟨13, 2, 0, 704453, 367749, 1829, 16384⟩
    (by decide) selected_cut_27873

theorem selected_cut_27874 : selected 8 ⟨704468, by decide⟩
    (prefixPartial 13 367750) = some ⟨13, 2, 0, 704468, 367750, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_367750_704468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367750 ⟨704468, by decide⟩ :=
  accepted_of_selected 13 367750 ⟨704468, by decide⟩ ⟨13, 2, 0, 704468, 367750, 1405, 16384⟩
    (by decide) selected_cut_27874

theorem selected_cut_27875 : selected 8 ⟨704474, by decide⟩
    (prefixPartial 13 367751) = some ⟨13, 2, 0, 704474, 367751, 581, 16384⟩ := by
  decide +kernel

theorem context_13_367751_704474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367751 ⟨704474, by decide⟩ :=
  accepted_of_selected 13 367751 ⟨704474, by decide⟩ ⟨13, 2, 0, 704474, 367751, 581, 16384⟩
    (by decide) selected_cut_27875

theorem unmarked_context_12_91937_704475 : frontier 9 ⟨704475, by decide⟩
    (prefixCache 12 91937) (prefixPartial 12 91937) = false := by
  decide +kernel

theorem node_context_12_91937_704475 : EJMOriginalGlobalDAGData.nodes 9 ⟨704475, by decide⟩ =
    .split (coordinate 12) (![⟨704425, by decide⟩,⟨704453, by decide⟩,⟨704468, by decide⟩,⟨704474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91937_704475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91937 ⟨704475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91937
    ⟨704475, by decide⟩ (by decide) (![⟨704425, by decide⟩,⟨704453, by decide⟩,⟨704468, by decide⟩,⟨704474, by decide⟩]) unmarked_context_12_91937_704475 node_context_12_91937_704475
  intro a
  fin_cases a
  · exact context_13_367748_704425
  · exact context_13_367749_704453
  · exact context_13_367750_704468
  · exact context_13_367751_704474

theorem selected_cut_27876 : selected 8 ⟨704498, by decide⟩
    (prefixPartial 13 367752) = some ⟨13, 2, 0, 704498, 367752, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_367752_704498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367752 ⟨704498, by decide⟩ :=
  accepted_of_selected 13 367752 ⟨704498, by decide⟩ ⟨13, 2, 0, 704498, 367752, 1409, 16384⟩
    (by decide) selected_cut_27876

theorem selected_cut_27877 : selected 8 ⟨704528, by decide⟩
    (prefixPartial 13 367753) = some ⟨13, 2, 0, 704528, 367753, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_367753_704528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367753 ⟨704528, by decide⟩ :=
  accepted_of_selected 13 367753 ⟨704528, by decide⟩ ⟨13, 2, 0, 704528, 367753, 1785, 16384⟩
    (by decide) selected_cut_27877

theorem selected_cut_27878 : selected 8 ⟨704546, by decide⟩
    (prefixPartial 13 367754) = some ⟨13, 2, 0, 704546, 367754, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_367754_704546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367754 ⟨704546, by decide⟩ :=
  accepted_of_selected 13 367754 ⟨704546, by decide⟩ ⟨13, 2, 0, 704546, 367754, 1273, 16384⟩
    (by decide) selected_cut_27878

theorem selected_cut_27879 : selected 8 ⟨704553, by decide⟩
    (prefixPartial 13 367755) = some ⟨13, 2, 0, 704553, 367755, 665, 16384⟩ := by
  decide +kernel

theorem context_13_367755_704553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367755 ⟨704553, by decide⟩ :=
  accepted_of_selected 13 367755 ⟨704553, by decide⟩ ⟨13, 2, 0, 704553, 367755, 665, 16384⟩
    (by decide) selected_cut_27879

theorem unmarked_context_12_91938_704554 : frontier 9 ⟨704554, by decide⟩
    (prefixCache 12 91938) (prefixPartial 12 91938) = false := by
  decide +kernel

theorem node_context_12_91938_704554 : EJMOriginalGlobalDAGData.nodes 9 ⟨704554, by decide⟩ =
    .split (coordinate 12) (![⟨704498, by decide⟩,⟨704528, by decide⟩,⟨704546, by decide⟩,⟨704553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91938_704554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91938 ⟨704554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91938
    ⟨704554, by decide⟩ (by decide) (![⟨704498, by decide⟩,⟨704528, by decide⟩,⟨704546, by decide⟩,⟨704553, by decide⟩]) unmarked_context_12_91938_704554 node_context_12_91938_704554
  intro a
  fin_cases a
  · exact context_13_367752_704498
  · exact context_13_367753_704528
  · exact context_13_367754_704546
  · exact context_13_367755_704553

theorem selected_cut_27880 : selected 8 ⟨704570, by decide⟩
    (prefixPartial 13 367756) = some ⟨13, 2, 0, 704570, 367756, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_367756_704570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367756 ⟨704570, by decide⟩ :=
  accepted_of_selected 13 367756 ⟨704570, by decide⟩ ⟨13, 2, 0, 704570, 367756, 1225, 16384⟩
    (by decide) selected_cut_27880

theorem selected_cut_27881 : selected 8 ⟨704600, by decide⟩
    (prefixPartial 13 367757) = some ⟨13, 2, 0, 704600, 367757, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_367757_704600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367757 ⟨704600, by decide⟩ :=
  accepted_of_selected 13 367757 ⟨704600, by decide⟩ ⟨13, 2, 0, 704600, 367757, 1797, 16384⟩
    (by decide) selected_cut_27881

theorem selected_cut_27882 : selected 8 ⟨704618, by decide⟩
    (prefixPartial 13 367758) = some ⟨13, 2, 0, 704618, 367758, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_367758_704618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367758 ⟨704618, by decide⟩ :=
  accepted_of_selected 13 367758 ⟨704618, by decide⟩ ⟨13, 2, 0, 704618, 367758, 1333, 16384⟩
    (by decide) selected_cut_27882

theorem selected_cut_27883 : selected 8 ⟨704621, by decide⟩
    (prefixPartial 13 367759) = some ⟨13, 2, 0, 704621, 367759, 545, 16384⟩ := by
  decide +kernel

theorem context_13_367759_704621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367759 ⟨704621, by decide⟩ :=
  accepted_of_selected 13 367759 ⟨704621, by decide⟩ ⟨13, 2, 0, 704621, 367759, 545, 16384⟩
    (by decide) selected_cut_27883

theorem unmarked_context_12_91939_704622 : frontier 9 ⟨704622, by decide⟩
    (prefixCache 12 91939) (prefixPartial 12 91939) = false := by
  decide +kernel

theorem node_context_12_91939_704622 : EJMOriginalGlobalDAGData.nodes 9 ⟨704622, by decide⟩ =
    .split (coordinate 12) (![⟨704570, by decide⟩,⟨704600, by decide⟩,⟨704618, by decide⟩,⟨704621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91939_704622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91939 ⟨704622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91939
    ⟨704622, by decide⟩ (by decide) (![⟨704570, by decide⟩,⟨704600, by decide⟩,⟨704618, by decide⟩,⟨704621, by decide⟩]) unmarked_context_12_91939_704622 node_context_12_91939_704622
  intro a
  fin_cases a
  · exact context_13_367756_704570
  · exact context_13_367757_704600
  · exact context_13_367758_704618
  · exact context_13_367759_704621

theorem unmarked_context_11_22984_704623 : frontier 10 ⟨704623, by decide⟩
    (prefixCache 11 22984) (prefixPartial 11 22984) = false := by
  decide +kernel

theorem node_context_11_22984_704623 : EJMOriginalGlobalDAGData.nodes 10 ⟨704623, by decide⟩ =
    .split (coordinate 11) (![⟨704403, by decide⟩,⟨704475, by decide⟩,⟨704554, by decide⟩,⟨704622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22984_704623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22984 ⟨704623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22984
    ⟨704623, by decide⟩ (by decide) (![⟨704403, by decide⟩,⟨704475, by decide⟩,⟨704554, by decide⟩,⟨704622, by decide⟩]) unmarked_context_11_22984_704623 node_context_11_22984_704623
  intro a
  fin_cases a
  · exact context_12_91936_704403
  · exact context_12_91937_704475
  · exact context_12_91938_704554
  · exact context_12_91939_704622

theorem selected_cut_27884 : selected 8 ⟨704635, by decide⟩
    (prefixPartial 13 367760) = some ⟨13, 2, 0, 704635, 367760, 805, 16384⟩ := by
  decide +kernel

theorem context_13_367760_704635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367760 ⟨704635, by decide⟩ :=
  accepted_of_selected 13 367760 ⟨704635, by decide⟩ ⟨13, 2, 0, 704635, 367760, 805, 16384⟩
    (by decide) selected_cut_27884

theorem selected_cut_27885 : selected 8 ⟨704668, by decide⟩
    (prefixPartial 13 367761) = some ⟨13, 2, 0, 704668, 367761, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_367761_704668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367761 ⟨704668, by decide⟩ :=
  accepted_of_selected 13 367761 ⟨704668, by decide⟩ ⟨13, 2, 0, 704668, 367761, 1601, 16384⟩
    (by decide) selected_cut_27885

theorem selected_cut_27886 : selected 8 ⟨704683, by decide⟩
    (prefixPartial 13 367762) = some ⟨13, 2, 0, 704683, 367762, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_367762_704683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367762 ⟨704683, by decide⟩ :=
  accepted_of_selected 13 367762 ⟨704683, by decide⟩ ⟨13, 2, 0, 704683, 367762, 1097, 16384⟩
    (by decide) selected_cut_27886

theorem selected_cut_27887 : selected 8 ⟨704687, by decide⟩
    (prefixPartial 13 367763) = some ⟨13, 2, 0, 704687, 367763, 745, 16384⟩ := by
  decide +kernel

theorem context_13_367763_704687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367763 ⟨704687, by decide⟩ :=
  accepted_of_selected 13 367763 ⟨704687, by decide⟩ ⟨13, 2, 0, 704687, 367763, 745, 16384⟩
    (by decide) selected_cut_27887

theorem unmarked_context_12_91940_704688 : frontier 9 ⟨704688, by decide⟩
    (prefixCache 12 91940) (prefixPartial 12 91940) = false := by
  decide +kernel

theorem node_context_12_91940_704688 : EJMOriginalGlobalDAGData.nodes 9 ⟨704688, by decide⟩ =
    .split (coordinate 12) (![⟨704635, by decide⟩,⟨704668, by decide⟩,⟨704683, by decide⟩,⟨704687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91940_704688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91940 ⟨704688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91940
    ⟨704688, by decide⟩ (by decide) (![⟨704635, by decide⟩,⟨704668, by decide⟩,⟨704683, by decide⟩,⟨704687, by decide⟩]) unmarked_context_12_91940_704688 node_context_12_91940_704688
  intro a
  fin_cases a
  · exact context_13_367760_704635
  · exact context_13_367761_704668
  · exact context_13_367762_704683
  · exact context_13_367763_704687

theorem selected_cut_27888 : selected 8 ⟨704706, by decide⟩
    (prefixPartial 13 367764) = some ⟨13, 2, 0, 704706, 367764, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_367764_704706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367764 ⟨704706, by decide⟩ :=
  accepted_of_selected 13 367764 ⟨704706, by decide⟩ ⟨13, 2, 0, 704706, 367764, 1033, 16384⟩
    (by decide) selected_cut_27888

theorem selected_cut_27889 : selected 8 ⟨704728, by decide⟩
    (prefixPartial 13 367765) = some ⟨13, 2, 0, 704728, 367765, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_367765_704728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367765 ⟨704728, by decide⟩ :=
  accepted_of_selected 13 367765 ⟨704728, by decide⟩ ⟨13, 2, 0, 704728, 367765, 1525, 16384⟩
    (by decide) selected_cut_27889

theorem selected_cut_27890 : selected 8 ⟨704742, by decide⟩
    (prefixPartial 13 367766) = some ⟨13, 2, 0, 704742, 367766, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_367766_704742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367766 ⟨704742, by decide⟩ :=
  accepted_of_selected 13 367766 ⟨704742, by decide⟩ ⟨13, 2, 0, 704742, 367766, 1233, 16384⟩
    (by decide) selected_cut_27890

theorem selected_cut_27891 : selected 8 ⟨704747, by decide⟩
    (prefixPartial 13 367767) = some ⟨13, 2, 0, 704747, 367767, 585, 16384⟩ := by
  decide +kernel

theorem context_13_367767_704747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367767 ⟨704747, by decide⟩ :=
  accepted_of_selected 13 367767 ⟨704747, by decide⟩ ⟨13, 2, 0, 704747, 367767, 585, 16384⟩
    (by decide) selected_cut_27891

theorem unmarked_context_12_91941_704748 : frontier 9 ⟨704748, by decide⟩
    (prefixCache 12 91941) (prefixPartial 12 91941) = false := by
  decide +kernel

theorem node_context_12_91941_704748 : EJMOriginalGlobalDAGData.nodes 9 ⟨704748, by decide⟩ =
    .split (coordinate 12) (![⟨704706, by decide⟩,⟨704728, by decide⟩,⟨704742, by decide⟩,⟨704747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91941_704748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91941 ⟨704748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91941
    ⟨704748, by decide⟩ (by decide) (![⟨704706, by decide⟩,⟨704728, by decide⟩,⟨704742, by decide⟩,⟨704747, by decide⟩]) unmarked_context_12_91941_704748 node_context_12_91941_704748
  intro a
  fin_cases a
  · exact context_13_367764_704706
  · exact context_13_367765_704728
  · exact context_13_367766_704742
  · exact context_13_367767_704747

theorem selected_cut_27892 : selected 8 ⟨704762, by decide⟩
    (prefixPartial 13 367768) = some ⟨13, 2, 0, 704762, 367768, 945, 16384⟩ := by
  decide +kernel

theorem context_13_367768_704762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367768 ⟨704762, by decide⟩ :=
  accepted_of_selected 13 367768 ⟨704762, by decide⟩ ⟨13, 2, 0, 704762, 367768, 945, 16384⟩
    (by decide) selected_cut_27892

theorem selected_cut_27893 : selected 8 ⟨704795, by decide⟩
    (prefixPartial 13 367769) = some ⟨13, 2, 0, 704795, 367769, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_367769_704795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367769 ⟨704795, by decide⟩ :=
  accepted_of_selected 13 367769 ⟨704795, by decide⟩ ⟨13, 2, 0, 704795, 367769, 1673, 16384⟩
    (by decide) selected_cut_27893

theorem selected_cut_27894 : selected 8 ⟨704809, by decide⟩
    (prefixPartial 13 367770) = some ⟨13, 2, 0, 704809, 367770, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_367770_704809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367770 ⟨704809, by decide⟩ :=
  accepted_of_selected 13 367770 ⟨704809, by decide⟩ ⟨13, 2, 0, 704809, 367770, 1081, 16384⟩
    (by decide) selected_cut_27894

theorem selected_cut_27895 : selected 8 ⟨704816, by decide⟩
    (prefixPartial 13 367771) = some ⟨13, 2, 0, 704816, 367771, 753, 16384⟩ := by
  decide +kernel

theorem context_13_367771_704816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367771 ⟨704816, by decide⟩ :=
  accepted_of_selected 13 367771 ⟨704816, by decide⟩ ⟨13, 2, 0, 704816, 367771, 753, 16384⟩
    (by decide) selected_cut_27895

theorem unmarked_context_12_91942_704817 : frontier 9 ⟨704817, by decide⟩
    (prefixCache 12 91942) (prefixPartial 12 91942) = false := by
  decide +kernel

theorem node_context_12_91942_704817 : EJMOriginalGlobalDAGData.nodes 9 ⟨704817, by decide⟩ =
    .split (coordinate 12) (![⟨704762, by decide⟩,⟨704795, by decide⟩,⟨704809, by decide⟩,⟨704816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91942_704817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91942 ⟨704817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91942
    ⟨704817, by decide⟩ (by decide) (![⟨704762, by decide⟩,⟨704795, by decide⟩,⟨704809, by decide⟩,⟨704816, by decide⟩]) unmarked_context_12_91942_704817 node_context_12_91942_704817
  intro a
  fin_cases a
  · exact context_13_367768_704762
  · exact context_13_367769_704795
  · exact context_13_367770_704809
  · exact context_13_367771_704816

theorem selected_cut_27896 : selected 8 ⟨704830, by decide⟩
    (prefixPartial 13 367772) = some ⟨13, 2, 0, 704830, 367772, 905, 16384⟩ := by
  decide +kernel

theorem context_13_367772_704830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367772 ⟨704830, by decide⟩ :=
  accepted_of_selected 13 367772 ⟨704830, by decide⟩ ⟨13, 2, 0, 704830, 367772, 905, 16384⟩
    (by decide) selected_cut_27896

theorem selected_cut_27897 : selected 8 ⟨704857, by decide⟩
    (prefixPartial 13 367773) = some ⟨13, 2, 0, 704857, 367773, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_367773_704857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367773 ⟨704857, by decide⟩ :=
  accepted_of_selected 13 367773 ⟨704857, by decide⟩ ⟨13, 2, 0, 704857, 367773, 1605, 16384⟩
    (by decide) selected_cut_27897

theorem selected_cut_27898 : selected 8 ⟨704875, by decide⟩
    (prefixPartial 13 367774) = some ⟨13, 2, 0, 704875, 367774, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_367774_704875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367774 ⟨704875, by decide⟩ :=
  accepted_of_selected 13 367774 ⟨704875, by decide⟩ ⟨13, 2, 0, 704875, 367774, 1293, 16384⟩
    (by decide) selected_cut_27898

theorem selected_cut_27899 : selected 8 ⟨704879, by decide⟩
    (prefixPartial 13 367775) = some ⟨13, 2, 0, 704879, 367775, 593, 16384⟩ := by
  decide +kernel

theorem context_13_367775_704879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367775 ⟨704879, by decide⟩ :=
  accepted_of_selected 13 367775 ⟨704879, by decide⟩ ⟨13, 2, 0, 704879, 367775, 593, 16384⟩
    (by decide) selected_cut_27899

theorem unmarked_context_12_91943_704880 : frontier 9 ⟨704880, by decide⟩
    (prefixCache 12 91943) (prefixPartial 12 91943) = false := by
  decide +kernel

theorem node_context_12_91943_704880 : EJMOriginalGlobalDAGData.nodes 9 ⟨704880, by decide⟩ =
    .split (coordinate 12) (![⟨704830, by decide⟩,⟨704857, by decide⟩,⟨704875, by decide⟩,⟨704879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91943_704880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91943 ⟨704880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91943
    ⟨704880, by decide⟩ (by decide) (![⟨704830, by decide⟩,⟨704857, by decide⟩,⟨704875, by decide⟩,⟨704879, by decide⟩]) unmarked_context_12_91943_704880 node_context_12_91943_704880
  intro a
  fin_cases a
  · exact context_13_367772_704830
  · exact context_13_367773_704857
  · exact context_13_367774_704875
  · exact context_13_367775_704879

theorem unmarked_context_11_22985_704881 : frontier 10 ⟨704881, by decide⟩
    (prefixCache 11 22985) (prefixPartial 11 22985) = false := by
  decide +kernel

theorem node_context_11_22985_704881 : EJMOriginalGlobalDAGData.nodes 10 ⟨704881, by decide⟩ =
    .split (coordinate 11) (![⟨704688, by decide⟩,⟨704748, by decide⟩,⟨704817, by decide⟩,⟨704880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22985_704881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22985 ⟨704881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22985
    ⟨704881, by decide⟩ (by decide) (![⟨704688, by decide⟩,⟨704748, by decide⟩,⟨704817, by decide⟩,⟨704880, by decide⟩]) unmarked_context_11_22985_704881 node_context_11_22985_704881
  intro a
  fin_cases a
  · exact context_12_91940_704688
  · exact context_12_91941_704748
  · exact context_12_91942_704817
  · exact context_12_91943_704880

theorem selected_cut_27900 : selected 8 ⟨704890, by decide⟩
    (prefixPartial 13 367776) = some ⟨13, 2, 0, 704890, 367776, 725, 16384⟩ := by
  decide +kernel

theorem context_13_367776_704890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367776 ⟨704890, by decide⟩ :=
  accepted_of_selected 13 367776 ⟨704890, by decide⟩ ⟨13, 2, 0, 704890, 367776, 725, 16384⟩
    (by decide) selected_cut_27900

theorem selected_cut_27901 : selected 8 ⟨704921, by decide⟩
    (prefixPartial 13 367777) = some ⟨13, 2, 0, 704921, 367777, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_367777_704921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367777 ⟨704921, by decide⟩ :=
  accepted_of_selected 13 367777 ⟨704921, by decide⟩ ⟨13, 2, 0, 704921, 367777, 1761, 16384⟩
    (by decide) selected_cut_27901

theorem selected_cut_27902 : selected 8 ⟨704936, by decide⟩
    (prefixPartial 13 367778) = some ⟨13, 2, 0, 704936, 367778, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_367778_704936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367778 ⟨704936, by decide⟩ :=
  accepted_of_selected 13 367778 ⟨704936, by decide⟩ ⟨13, 2, 0, 704936, 367778, 1221, 16384⟩
    (by decide) selected_cut_27902

theorem selected_cut_27903 : selected 8 ⟨704943, by decide⟩
    (prefixPartial 13 367779) = some ⟨13, 2, 0, 704943, 367779, 817, 16384⟩ := by
  decide +kernel

theorem context_13_367779_704943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367779 ⟨704943, by decide⟩ :=
  accepted_of_selected 13 367779 ⟨704943, by decide⟩ ⟨13, 2, 0, 704943, 367779, 817, 16384⟩
    (by decide) selected_cut_27903

theorem unmarked_context_12_91944_704944 : frontier 9 ⟨704944, by decide⟩
    (prefixCache 12 91944) (prefixPartial 12 91944) = false := by
  decide +kernel

theorem node_context_12_91944_704944 : EJMOriginalGlobalDAGData.nodes 9 ⟨704944, by decide⟩ =
    .split (coordinate 12) (![⟨704890, by decide⟩,⟨704921, by decide⟩,⟨704936, by decide⟩,⟨704943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91944_704944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91944 ⟨704944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91944
    ⟨704944, by decide⟩ (by decide) (![⟨704890, by decide⟩,⟨704921, by decide⟩,⟨704936, by decide⟩,⟨704943, by decide⟩]) unmarked_context_12_91944_704944 node_context_12_91944_704944
  intro a
  fin_cases a
  · exact context_13_367776_704890
  · exact context_13_367777_704921
  · exact context_13_367778_704936
  · exact context_13_367779_704943

theorem selected_cut_27904 : selected 8 ⟨704957, by decide⟩
    (prefixPartial 13 367780) = some ⟨13, 2, 0, 704957, 367780, 969, 16384⟩ := by
  decide +kernel

theorem context_13_367780_704957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367780 ⟨704957, by decide⟩ :=
  accepted_of_selected 13 367780 ⟨704957, by decide⟩ ⟨13, 2, 0, 704957, 367780, 969, 16384⟩
    (by decide) selected_cut_27904

theorem selected_cut_27905 : selected 8 ⟨704986, by decide⟩
    (prefixPartial 13 367781) = some ⟨13, 2, 0, 704986, 367781, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_367781_704986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367781 ⟨704986, by decide⟩ :=
  accepted_of_selected 13 367781 ⟨704986, by decide⟩ ⟨13, 2, 0, 704986, 367781, 1745, 16384⟩
    (by decide) selected_cut_27905

theorem selected_cut_27906 : selected 8 ⟨705005, by decide⟩
    (prefixPartial 13 367782) = some ⟨13, 2, 0, 705005, 367782, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_367782_705005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367782 ⟨705005, by decide⟩ :=
  accepted_of_selected 13 367782 ⟨705005, by decide⟩ ⟨13, 2, 0, 705005, 367782, 1473, 16384⟩
    (by decide) selected_cut_27906

theorem selected_cut_27907 : selected 8 ⟨705011, by decide⟩
    (prefixPartial 13 367783) = some ⟨13, 2, 0, 705011, 367783, 709, 16384⟩ := by
  decide +kernel

theorem context_13_367783_705011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367783 ⟨705011, by decide⟩ :=
  accepted_of_selected 13 367783 ⟨705011, by decide⟩ ⟨13, 2, 0, 705011, 367783, 709, 16384⟩
    (by decide) selected_cut_27907

theorem unmarked_context_12_91945_705012 : frontier 9 ⟨705012, by decide⟩
    (prefixCache 12 91945) (prefixPartial 12 91945) = false := by
  decide +kernel

theorem node_context_12_91945_705012 : EJMOriginalGlobalDAGData.nodes 9 ⟨705012, by decide⟩ =
    .split (coordinate 12) (![⟨704957, by decide⟩,⟨704986, by decide⟩,⟨705005, by decide⟩,⟨705011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91945_705012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91945 ⟨705012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91945
    ⟨705012, by decide⟩ (by decide) (![⟨704957, by decide⟩,⟨704986, by decide⟩,⟨705005, by decide⟩,⟨705011, by decide⟩]) unmarked_context_12_91945_705012 node_context_12_91945_705012
  intro a
  fin_cases a
  · exact context_13_367780_704957
  · exact context_13_367781_704986
  · exact context_13_367782_705005
  · exact context_13_367783_705011

theorem selected_cut_27908 : selected 8 ⟨705022, by decide⟩
    (prefixPartial 13 367784) = some ⟨13, 2, 0, 705022, 367784, 761, 16384⟩ := by
  decide +kernel

theorem context_13_367784_705022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367784 ⟨705022, by decide⟩ :=
  accepted_of_selected 13 367784 ⟨705022, by decide⟩ ⟨13, 2, 0, 705022, 367784, 761, 16384⟩
    (by decide) selected_cut_27908

theorem selected_cut_27909 : selected 8 ⟨705057, by decide⟩
    (prefixPartial 13 367785) = some ⟨13, 2, 0, 705057, 367785, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_367785_705057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367785 ⟨705057, by decide⟩ :=
  accepted_of_selected 13 367785 ⟨705057, by decide⟩ ⟨13, 2, 0, 705057, 367785, 1825, 16384⟩
    (by decide) selected_cut_27909

theorem selected_cut_27910 : selected 8 ⟨705070, by decide⟩
    (prefixPartial 13 367786) = some ⟨13, 2, 0, 705070, 367786, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_367786_705070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367786 ⟨705070, by decide⟩ :=
  accepted_of_selected 13 367786 ⟨705070, by decide⟩ ⟨13, 2, 0, 705070, 367786, 1197, 16384⟩
    (by decide) selected_cut_27910

theorem selected_cut_27911 : selected 8 ⟨705077, by decide⟩
    (prefixPartial 13 367787) = some ⟨13, 2, 0, 705077, 367787, 765, 16384⟩ := by
  decide +kernel

theorem context_13_367787_705077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367787 ⟨705077, by decide⟩ :=
  accepted_of_selected 13 367787 ⟨705077, by decide⟩ ⟨13, 2, 0, 705077, 367787, 765, 16384⟩
    (by decide) selected_cut_27911

theorem unmarked_context_12_91946_705078 : frontier 9 ⟨705078, by decide⟩
    (prefixCache 12 91946) (prefixPartial 12 91946) = false := by
  decide +kernel

theorem node_context_12_91946_705078 : EJMOriginalGlobalDAGData.nodes 9 ⟨705078, by decide⟩ =
    .split (coordinate 12) (![⟨705022, by decide⟩,⟨705057, by decide⟩,⟨705070, by decide⟩,⟨705077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91946_705078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91946 ⟨705078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91946
    ⟨705078, by decide⟩ (by decide) (![⟨705022, by decide⟩,⟨705057, by decide⟩,⟨705070, by decide⟩,⟨705077, by decide⟩]) unmarked_context_12_91946_705078 node_context_12_91946_705078
  intro a
  fin_cases a
  · exact context_13_367784_705022
  · exact context_13_367785_705057
  · exact context_13_367786_705070
  · exact context_13_367787_705077

theorem selected_cut_27912 : selected 8 ⟨705087, by decide⟩
    (prefixPartial 13 367788) = some ⟨13, 2, 0, 705087, 367788, 705, 16384⟩ := by
  decide +kernel

theorem context_13_367788_705087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367788 ⟨705087, by decide⟩ :=
  accepted_of_selected 13 367788 ⟨705087, by decide⟩ ⟨13, 2, 0, 705087, 367788, 705, 16384⟩
    (by decide) selected_cut_27912

theorem selected_cut_27913 : selected 8 ⟨705127, by decide⟩
    (prefixPartial 13 367789) = some ⟨13, 2, 0, 705127, 367789, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_367789_705127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367789 ⟨705127, by decide⟩ :=
  accepted_of_selected 13 367789 ⟨705127, by decide⟩ ⟨13, 2, 0, 705127, 367789, 1853, 16384⟩
    (by decide) selected_cut_27913

theorem selected_cut_27914 : selected 8 ⟨705146, by decide⟩
    (prefixPartial 13 367790) = some ⟨13, 2, 0, 705146, 367790, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_367790_705146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367790 ⟨705146, by decide⟩ :=
  accepted_of_selected 13 367790 ⟨705146, by decide⟩ ⟨13, 2, 0, 705146, 367790, 1253, 16384⟩
    (by decide) selected_cut_27914

theorem selected_cut_27915 : selected 8 ⟨705150, by decide⟩
    (prefixPartial 13 367791) = some ⟨13, 2, 0, 705150, 367791, 605, 16384⟩ := by
  decide +kernel

theorem context_13_367791_705150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367791 ⟨705150, by decide⟩ :=
  accepted_of_selected 13 367791 ⟨705150, by decide⟩ ⟨13, 2, 0, 705150, 367791, 605, 16384⟩
    (by decide) selected_cut_27915

theorem unmarked_context_12_91947_705151 : frontier 9 ⟨705151, by decide⟩
    (prefixCache 12 91947) (prefixPartial 12 91947) = false := by
  decide +kernel

theorem node_context_12_91947_705151 : EJMOriginalGlobalDAGData.nodes 9 ⟨705151, by decide⟩ =
    .split (coordinate 12) (![⟨705087, by decide⟩,⟨705127, by decide⟩,⟨705146, by decide⟩,⟨705150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91947_705151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91947 ⟨705151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91947
    ⟨705151, by decide⟩ (by decide) (![⟨705087, by decide⟩,⟨705127, by decide⟩,⟨705146, by decide⟩,⟨705150, by decide⟩]) unmarked_context_12_91947_705151 node_context_12_91947_705151
  intro a
  fin_cases a
  · exact context_13_367788_705087
  · exact context_13_367789_705127
  · exact context_13_367790_705146
  · exact context_13_367791_705150

theorem unmarked_context_11_22986_705152 : frontier 10 ⟨705152, by decide⟩
    (prefixCache 11 22986) (prefixPartial 11 22986) = false := by
  decide +kernel

theorem node_context_11_22986_705152 : EJMOriginalGlobalDAGData.nodes 10 ⟨705152, by decide⟩ =
    .split (coordinate 11) (![⟨704944, by decide⟩,⟨705012, by decide⟩,⟨705078, by decide⟩,⟨705151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22986_705152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22986 ⟨705152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22986
    ⟨705152, by decide⟩ (by decide) (![⟨704944, by decide⟩,⟨705012, by decide⟩,⟨705078, by decide⟩,⟨705151, by decide⟩]) unmarked_context_11_22986_705152 node_context_11_22986_705152
  intro a
  fin_cases a
  · exact context_12_91944_704944
  · exact context_12_91945_705012
  · exact context_12_91946_705078
  · exact context_12_91947_705151

theorem selected_cut_27916 : selected 9 ⟨705212, by decide⟩
    (prefixPartial 12 91948) = some ⟨12, 2, 0, 705212, 91948, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_91948_705212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91948 ⟨705212, by decide⟩ :=
  accepted_of_selected 12 91948 ⟨705212, by decide⟩ ⟨12, 2, 0, 705212, 91948, 4077, 65536⟩
    (by decide) selected_cut_27916

theorem selected_cut_27917 : selected 8 ⟨705223, by decide⟩
    (prefixPartial 13 367796) = some ⟨13, 2, 0, 705223, 367796, 797, 16384⟩ := by
  decide +kernel

theorem context_13_367796_705223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367796 ⟨705223, by decide⟩ :=
  accepted_of_selected 13 367796 ⟨705223, by decide⟩ ⟨13, 2, 0, 705223, 367796, 797, 16384⟩
    (by decide) selected_cut_27917

theorem selected_cut_27918 : selected 8 ⟨705252, by decide⟩
    (prefixPartial 13 367797) = some ⟨13, 2, 0, 705252, 367797, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_367797_705252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367797 ⟨705252, by decide⟩ :=
  accepted_of_selected 13 367797 ⟨705252, by decide⟩ ⟨13, 2, 0, 705252, 367797, 1757, 16384⟩
    (by decide) selected_cut_27918

theorem selected_cut_27919 : selected 8 ⟨705269, by decide⟩
    (prefixPartial 13 367798) = some ⟨13, 2, 0, 705269, 367798, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_367798_705269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367798 ⟨705269, by decide⟩ :=
  accepted_of_selected 13 367798 ⟨705269, by decide⟩ ⟨13, 2, 0, 705269, 367798, 1293, 16384⟩
    (by decide) selected_cut_27919

theorem selected_cut_27920 : selected 8 ⟨705276, by decide⟩
    (prefixPartial 13 367799) = some ⟨13, 2, 0, 705276, 367799, 633, 16384⟩ := by
  decide +kernel

theorem context_13_367799_705276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367799 ⟨705276, by decide⟩ :=
  accepted_of_selected 13 367799 ⟨705276, by decide⟩ ⟨13, 2, 0, 705276, 367799, 633, 16384⟩
    (by decide) selected_cut_27920

theorem unmarked_context_12_91949_705277 : frontier 9 ⟨705277, by decide⟩
    (prefixCache 12 91949) (prefixPartial 12 91949) = false := by
  decide +kernel

theorem node_context_12_91949_705277 : EJMOriginalGlobalDAGData.nodes 9 ⟨705277, by decide⟩ =
    .split (coordinate 12) (![⟨705223, by decide⟩,⟨705252, by decide⟩,⟨705269, by decide⟩,⟨705276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91949_705277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91949 ⟨705277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91949
    ⟨705277, by decide⟩ (by decide) (![⟨705223, by decide⟩,⟨705252, by decide⟩,⟨705269, by decide⟩,⟨705276, by decide⟩]) unmarked_context_12_91949_705277 node_context_12_91949_705277
  intro a
  fin_cases a
  · exact context_13_367796_705223
  · exact context_13_367797_705252
  · exact context_13_367798_705269
  · exact context_13_367799_705276

theorem selected_cut_27921 : selected 8 ⟨705289, by decide⟩
    (prefixPartial 13 367800) = some ⟨13, 2, 0, 705289, 367800, 713, 16384⟩ := by
  decide +kernel

theorem context_13_367800_705289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367800 ⟨705289, by decide⟩ :=
  accepted_of_selected 13 367800 ⟨705289, by decide⟩ ⟨13, 2, 0, 705289, 367800, 713, 16384⟩
    (by decide) selected_cut_27921

theorem selected_cut_27922 : selected 8 ⟨705323, by decide⟩
    (prefixPartial 13 367801) = some ⟨13, 2, 0, 705323, 367801, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_367801_705323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367801 ⟨705323, by decide⟩ :=
  accepted_of_selected 13 367801 ⟨705323, by decide⟩ ⟨13, 2, 0, 705323, 367801, 1881, 16384⟩
    (by decide) selected_cut_27922

theorem selected_cut_27923 : selected 8 ⟨705339, by decide⟩
    (prefixPartial 13 367802) = some ⟨13, 2, 0, 705339, 367802, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_367802_705339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367802 ⟨705339, by decide⟩ :=
  accepted_of_selected 13 367802 ⟨705339, by decide⟩ ⟨13, 2, 0, 705339, 367802, 1081, 16384⟩
    (by decide) selected_cut_27923

theorem selected_cut_27924 : selected 8 ⟨705344, by decide⟩
    (prefixPartial 13 367803) = some ⟨13, 2, 0, 705344, 367803, 701, 16384⟩ := by
  decide +kernel

theorem context_13_367803_705344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367803 ⟨705344, by decide⟩ :=
  accepted_of_selected 13 367803 ⟨705344, by decide⟩ ⟨13, 2, 0, 705344, 367803, 701, 16384⟩
    (by decide) selected_cut_27924

theorem unmarked_context_12_91950_705345 : frontier 9 ⟨705345, by decide⟩
    (prefixCache 12 91950) (prefixPartial 12 91950) = false := by
  decide +kernel

theorem node_context_12_91950_705345 : EJMOriginalGlobalDAGData.nodes 9 ⟨705345, by decide⟩ =
    .split (coordinate 12) (![⟨705289, by decide⟩,⟨705323, by decide⟩,⟨705339, by decide⟩,⟨705344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91950_705345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91950 ⟨705345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91950
    ⟨705345, by decide⟩ (by decide) (![⟨705289, by decide⟩,⟨705323, by decide⟩,⟨705339, by decide⟩,⟨705344, by decide⟩]) unmarked_context_12_91950_705345 node_context_12_91950_705345
  intro a
  fin_cases a
  · exact context_13_367800_705289
  · exact context_13_367801_705323
  · exact context_13_367802_705339
  · exact context_13_367803_705344

theorem selected_cut_27925 : selected 8 ⟨705362, by decide⟩
    (prefixPartial 13 367804) = some ⟨13, 2, 0, 705362, 367804, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_367804_705362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367804 ⟨705362, by decide⟩ :=
  accepted_of_selected 13 367804 ⟨705362, by decide⟩ ⟨13, 2, 0, 705362, 367804, 1025, 16384⟩
    (by decide) selected_cut_27925

theorem selected_cut_27926 : selected 8 ⟨705435, by decide⟩
    (prefixPartial 13 367805) = some ⟨13, 2, 0, 705435, 367805, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_367805_705435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367805 ⟨705435, by decide⟩ :=
  accepted_of_selected 13 367805 ⟨705435, by decide⟩ ⟨13, 2, 0, 705435, 367805, 3073, 16384⟩
    (by decide) selected_cut_27926

theorem selected_cut_27927 : selected 8 ⟨705458, by decide⟩
    (prefixPartial 13 367806) = some ⟨13, 2, 0, 705458, 367806, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_367806_705458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367806 ⟨705458, by decide⟩ :=
  accepted_of_selected 13 367806 ⟨705458, by decide⟩ ⟨13, 2, 0, 705458, 367806, 2021, 16384⟩
    (by decide) selected_cut_27927

theorem selected_cut_27928 : selected 8 ⟨705464, by decide⟩
    (prefixPartial 13 367807) = some ⟨13, 2, 0, 705464, 367807, 873, 16384⟩ := by
  decide +kernel

theorem context_13_367807_705464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367807 ⟨705464, by decide⟩ :=
  accepted_of_selected 13 367807 ⟨705464, by decide⟩ ⟨13, 2, 0, 705464, 367807, 873, 16384⟩
    (by decide) selected_cut_27928

theorem unmarked_context_12_91951_705465 : frontier 9 ⟨705465, by decide⟩
    (prefixCache 12 91951) (prefixPartial 12 91951) = false := by
  decide +kernel

theorem node_context_12_91951_705465 : EJMOriginalGlobalDAGData.nodes 9 ⟨705465, by decide⟩ =
    .split (coordinate 12) (![⟨705362, by decide⟩,⟨705435, by decide⟩,⟨705458, by decide⟩,⟨705464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91951_705465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91951 ⟨705465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91951
    ⟨705465, by decide⟩ (by decide) (![⟨705362, by decide⟩,⟨705435, by decide⟩,⟨705458, by decide⟩,⟨705464, by decide⟩]) unmarked_context_12_91951_705465 node_context_12_91951_705465
  intro a
  fin_cases a
  · exact context_13_367804_705362
  · exact context_13_367805_705435
  · exact context_13_367806_705458
  · exact context_13_367807_705464

theorem unmarked_context_11_22987_705466 : frontier 10 ⟨705466, by decide⟩
    (prefixCache 11 22987) (prefixPartial 11 22987) = false := by
  decide +kernel

theorem node_context_11_22987_705466 : EJMOriginalGlobalDAGData.nodes 10 ⟨705466, by decide⟩ =
    .split (coordinate 11) (![⟨705212, by decide⟩,⟨705277, by decide⟩,⟨705345, by decide⟩,⟨705465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22987_705466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22987 ⟨705466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22987
    ⟨705466, by decide⟩ (by decide) (![⟨705212, by decide⟩,⟨705277, by decide⟩,⟨705345, by decide⟩,⟨705465, by decide⟩]) unmarked_context_11_22987_705466 node_context_11_22987_705466
  intro a
  fin_cases a
  · exact context_12_91948_705212
  · exact context_12_91949_705277
  · exact context_12_91950_705345
  · exact context_12_91951_705465

theorem unmarked_context_10_5746_705467 : frontier 11 ⟨705467, by decide⟩
    (prefixCache 10 5746) (prefixPartial 10 5746) = false := by
  decide +kernel

theorem node_context_10_5746_705467 : EJMOriginalGlobalDAGData.nodes 11 ⟨705467, by decide⟩ =
    .split (coordinate 10) (![⟨704623, by decide⟩,⟨704881, by decide⟩,⟨705152, by decide⟩,⟨705466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5746_705467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5746 ⟨705467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5746
    ⟨705467, by decide⟩ (by decide) (![⟨704623, by decide⟩,⟨704881, by decide⟩,⟨705152, by decide⟩,⟨705466, by decide⟩]) unmarked_context_10_5746_705467 node_context_10_5746_705467
  intro a
  fin_cases a
  · exact context_11_22984_704623
  · exact context_11_22985_704881
  · exact context_11_22986_705152
  · exact context_11_22987_705466

theorem selected_cut_27929 : selected 8 ⟨705473, by decide⟩
    (prefixPartial 13 367808) = some ⟨13, 2, 0, 705473, 367808, 521, 16384⟩ := by
  decide +kernel

theorem context_13_367808_705473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367808 ⟨705473, by decide⟩ :=
  accepted_of_selected 13 367808 ⟨705473, by decide⟩ ⟨13, 2, 0, 705473, 367808, 521, 16384⟩
    (by decide) selected_cut_27929

theorem selected_cut_27930 : selected 8 ⟨705497, by decide⟩
    (prefixPartial 13 367809) = some ⟨13, 2, 0, 705497, 367809, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_367809_705497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367809 ⟨705497, by decide⟩ :=
  accepted_of_selected 13 367809 ⟨705497, by decide⟩ ⟨13, 2, 0, 705497, 367809, 1857, 16384⟩
    (by decide) selected_cut_27930

theorem selected_cut_27931 : selected 8 ⟨705515, by decide⟩
    (prefixPartial 13 367810) = some ⟨13, 2, 0, 705515, 367810, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_367810_705515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367810 ⟨705515, by decide⟩ :=
  accepted_of_selected 13 367810 ⟨705515, by decide⟩ ⟨13, 2, 0, 705515, 367810, 1421, 16384⟩
    (by decide) selected_cut_27931

theorem selected_cut_27932 : selected 8 ⟨705524, by decide⟩
    (prefixPartial 13 367811) = some ⟨13, 2, 0, 705524, 367811, 889, 16384⟩ := by
  decide +kernel

theorem context_13_367811_705524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367811 ⟨705524, by decide⟩ :=
  accepted_of_selected 13 367811 ⟨705524, by decide⟩ ⟨13, 2, 0, 705524, 367811, 889, 16384⟩
    (by decide) selected_cut_27932

theorem unmarked_context_12_91952_705525 : frontier 9 ⟨705525, by decide⟩
    (prefixCache 12 91952) (prefixPartial 12 91952) = false := by
  decide +kernel

theorem node_context_12_91952_705525 : EJMOriginalGlobalDAGData.nodes 9 ⟨705525, by decide⟩ =
    .split (coordinate 12) (![⟨705473, by decide⟩,⟨705497, by decide⟩,⟨705515, by decide⟩,⟨705524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91952_705525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91952 ⟨705525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91952
    ⟨705525, by decide⟩ (by decide) (![⟨705473, by decide⟩,⟨705497, by decide⟩,⟨705515, by decide⟩,⟨705524, by decide⟩]) unmarked_context_12_91952_705525 node_context_12_91952_705525
  intro a
  fin_cases a
  · exact context_13_367808_705473
  · exact context_13_367809_705497
  · exact context_13_367810_705515
  · exact context_13_367811_705524

theorem selected_cut_27933 : selected 8 ⟨705533, by decide⟩
    (prefixPartial 13 367812) = some ⟨13, 2, 0, 705533, 367812, 649, 16384⟩ := by
  decide +kernel

theorem context_13_367812_705533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367812 ⟨705533, by decide⟩ :=
  accepted_of_selected 13 367812 ⟨705533, by decide⟩ ⟨13, 2, 0, 705533, 367812, 649, 16384⟩
    (by decide) selected_cut_27933

theorem selected_cut_27934 : selected 8 ⟨705563, by decide⟩
    (prefixPartial 13 367813) = some ⟨13, 2, 0, 705563, 367813, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_367813_705563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367813 ⟨705563, by decide⟩ :=
  accepted_of_selected 13 367813 ⟨705563, by decide⟩ ⟨13, 2, 0, 705563, 367813, 2145, 16384⟩
    (by decide) selected_cut_27934

theorem selected_cut_27935 : selected 8 ⟨705587, by decide⟩
    (prefixPartial 13 367814) = some ⟨13, 2, 0, 705587, 367814, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_367814_705587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367814 ⟨705587, by decide⟩ :=
  accepted_of_selected 13 367814 ⟨705587, by decide⟩ ⟨13, 2, 0, 705587, 367814, 1605, 16384⟩
    (by decide) selected_cut_27935

theorem selected_cut_27936 : selected 8 ⟨705597, by decide⟩
    (prefixPartial 13 367815) = some ⟨13, 2, 0, 705597, 367815, 757, 16384⟩ := by
  decide +kernel

theorem context_13_367815_705597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367815 ⟨705597, by decide⟩ :=
  accepted_of_selected 13 367815 ⟨705597, by decide⟩ ⟨13, 2, 0, 705597, 367815, 757, 16384⟩
    (by decide) selected_cut_27936

theorem unmarked_context_12_91953_705598 : frontier 9 ⟨705598, by decide⟩
    (prefixCache 12 91953) (prefixPartial 12 91953) = false := by
  decide +kernel

theorem node_context_12_91953_705598 : EJMOriginalGlobalDAGData.nodes 9 ⟨705598, by decide⟩ =
    .split (coordinate 12) (![⟨705533, by decide⟩,⟨705563, by decide⟩,⟨705587, by decide⟩,⟨705597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91953_705598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91953 ⟨705598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91953
    ⟨705598, by decide⟩ (by decide) (![⟨705533, by decide⟩,⟨705563, by decide⟩,⟨705587, by decide⟩,⟨705597, by decide⟩]) unmarked_context_12_91953_705598 node_context_12_91953_705598
  intro a
  fin_cases a
  · exact context_13_367812_705533
  · exact context_13_367813_705563
  · exact context_13_367814_705587
  · exact context_13_367815_705597

theorem selected_cut_27937 : selected 8 ⟨705605, by decide⟩
    (prefixPartial 13 367816) = some ⟨13, 2, 0, 705605, 367816, 561, 16384⟩ := by
  decide +kernel

theorem context_13_367816_705605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367816 ⟨705605, by decide⟩ :=
  accepted_of_selected 13 367816 ⟨705605, by decide⟩ ⟨13, 2, 0, 705605, 367816, 561, 16384⟩
    (by decide) selected_cut_27937

theorem selected_cut_27938 : selected 8 ⟨705630, by decide⟩
    (prefixPartial 13 367817) = some ⟨13, 2, 0, 705630, 367817, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_367817_705630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367817 ⟨705630, by decide⟩ :=
  accepted_of_selected 13 367817 ⟨705630, by decide⟩ ⟨13, 2, 0, 705630, 367817, 1957, 16384⟩
    (by decide) selected_cut_27938

theorem selected_cut_27939 : selected 8 ⟨705646, by decide⟩
    (prefixPartial 13 367818) = some ⟨13, 2, 0, 705646, 367818, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_367818_705646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 367818 ⟨705646, by decide⟩ :=
  accepted_of_selected 13 367818 ⟨705646, by decide⟩ ⟨13, 2, 0, 705646, 367818, 1465, 16384⟩
    (by decide) selected_cut_27939

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
