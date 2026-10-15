/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover548
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_52706 : selected 11 ⟨1545688, by decide⟩
    (prefixPartial 10 74801) = some ⟨10, 2, 0, 1545688, 74801, 2417, 1048576⟩ := by
  decide +kernel

theorem context_10_74801_1545688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74801 ⟨1545688, by decide⟩ :=
  accepted_of_selected 10 74801 ⟨1545688, by decide⟩ ⟨10, 2, 0, 1545688, 74801, 2417, 1048576⟩
    (by decide) selected_cut_52706

theorem selected_cut_52707 : selected 11 ⟨1545774, by decide⟩
    (prefixPartial 10 74802) = some ⟨10, 2, 0, 1545774, 74802, 1501, 1048576⟩ := by
  decide +kernel

theorem context_10_74802_1545774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74802 ⟨1545774, by decide⟩ :=
  accepted_of_selected 10 74802 ⟨1545774, by decide⟩ ⟨10, 2, 0, 1545774, 74802, 1501, 1048576⟩
    (by decide) selected_cut_52707

theorem selected_cut_52708 : selected 11 ⟨1545886, by decide⟩
    (prefixPartial 10 74803) = some ⟨10, 2, 0, 1545886, 74803, 1665, 1048576⟩ := by
  decide +kernel

theorem context_10_74803_1545886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74803 ⟨1545886, by decide⟩ :=
  accepted_of_selected 10 74803 ⟨1545886, by decide⟩ ⟨10, 2, 0, 1545886, 74803, 1665, 1048576⟩
    (by decide) selected_cut_52708

theorem unmarked_context_9_18700_1545887 : frontier 12 ⟨1545887, by decide⟩
    (prefixCache 9 18700) (prefixPartial 9 18700) = false := by
  decide +kernel

theorem node_context_9_18700_1545887 : EJMOriginalGlobalDAGData.nodes 12 ⟨1545887, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1545688, by decide⟩,⟨1545774, by decide⟩,⟨1545886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18700_1545887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18700 ⟨1545887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18700
    ⟨1545887, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1545688, by decide⟩,⟨1545774, by decide⟩,⟨1545886, by decide⟩]) unmarked_context_9_18700_1545887 node_context_9_18700_1545887
  intro a
  fin_cases a
  · exact context_10_74800_1468246
  · exact context_10_74801_1545688
  · exact context_10_74802_1545774
  · exact context_10_74803_1545886

theorem selected_cut_52709 : selected 12 ⟨1545995, by decide⟩
    (prefixPartial 9 18701) = some ⟨9, 2, 0, 1545995, 18701, 2969, 4194304⟩ := by
  decide +kernel

theorem context_9_18701_1545995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18701 ⟨1545995, by decide⟩ :=
  accepted_of_selected 9 18701 ⟨1545995, by decide⟩ ⟨9, 2, 0, 1545995, 18701, 2969, 4194304⟩
    (by decide) selected_cut_52709

theorem selected_cut_52710 : selected 12 ⟨1546055, by decide⟩
    (prefixPartial 9 18702) = some ⟨9, 2, 0, 1546055, 18702, 1625, 4194304⟩ := by
  decide +kernel

theorem context_9_18702_1546055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18702 ⟨1546055, by decide⟩ :=
  accepted_of_selected 9 18702 ⟨1546055, by decide⟩ ⟨9, 2, 0, 1546055, 18702, 1625, 4194304⟩
    (by decide) selected_cut_52710

theorem selected_cut_52711 : selected 12 ⟨1546093, by decide⟩
    (prefixPartial 9 18703) = some ⟨9, 2, 0, 1546093, 18703, 677, 4194304⟩ := by
  decide +kernel

theorem context_9_18703_1546093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18703 ⟨1546093, by decide⟩ :=
  accepted_of_selected 9 18703 ⟨1546093, by decide⟩ ⟨9, 2, 0, 1546093, 18703, 677, 4194304⟩
    (by decide) selected_cut_52711

theorem unmarked_context_8_4675_1546094 : frontier 13 ⟨1546094, by decide⟩
    (prefixCache 8 4675) (prefixPartial 8 4675) = false := by
  decide +kernel

theorem node_context_8_4675_1546094 : EJMOriginalGlobalDAGData.nodes 13 ⟨1546094, by decide⟩ =
    .split (coordinate 8) (![⟨1545887, by decide⟩,⟨1545995, by decide⟩,⟨1546055, by decide⟩,⟨1546093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4675_1546094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4675 ⟨1546094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4675
    ⟨1546094, by decide⟩ (by decide) (![⟨1545887, by decide⟩,⟨1545995, by decide⟩,⟨1546055, by decide⟩,⟨1546093, by decide⟩]) unmarked_context_8_4675_1546094 node_context_8_4675_1546094
  intro a
  fin_cases a
  · exact context_9_18700_1545887
  · exact context_9_18701_1545995
  · exact context_9_18702_1546055
  · exact context_9_18703_1546093

theorem unmarked_context_7_1168_1546095 : frontier 14 ⟨1546095, by decide⟩
    (prefixCache 7 1168) (prefixPartial 7 1168) = false := by
  decide +kernel

theorem node_context_7_1168_1546095 : EJMOriginalGlobalDAGData.nodes 14 ⟨1546095, by decide⟩ =
    .split (coordinate 7) (![⟨1487329, by decide⟩,⟨1545547, by decide⟩,⟨1364555, by decide⟩,⟨1546094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1168_1546095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1168 ⟨1546095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1168
    ⟨1546095, by decide⟩ (by decide) (![⟨1487329, by decide⟩,⟨1545547, by decide⟩,⟨1364555, by decide⟩,⟨1546094, by decide⟩]) unmarked_context_7_1168_1546095 node_context_7_1168_1546095
  intro a
  fin_cases a
  · exact context_8_4672_1487329
  · exact context_8_4673_1545547
  · exact context_8_4674_1364555
  · exact context_8_4675_1546094

theorem selected_cut_52712 : selected 14 ⟨1539247, by decide⟩
    (prefixPartial 7 1169) = some ⟨7, 1, 0, 1539247, 1169, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_1169_1539247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1169 ⟨1539247, by decide⟩ :=
  accepted_of_selected 7 1169 ⟨1539247, by decide⟩ ⟨7, 1, 0, 1539247, 1169, 1, 67108864⟩
    (by decide) selected_cut_52712

theorem selected_cut_52713 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 74880) = some ⟨10, 1, 0, 1468246, 74880, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74880_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74880 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 74880 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 74880, 1, 1048576⟩
    (by decide) selected_cut_52713

theorem selected_cut_52714 : selected 11 ⟨1546298, by decide⟩
    (prefixPartial 10 74881) = some ⟨10, 2, 0, 1546298, 74881, 3157, 1048576⟩ := by
  decide +kernel

theorem context_10_74881_1546298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74881 ⟨1546298, by decide⟩ :=
  accepted_of_selected 10 74881 ⟨1546298, by decide⟩ ⟨10, 2, 0, 1546298, 74881, 3157, 1048576⟩
    (by decide) selected_cut_52714

theorem selected_cut_52715 : selected 11 ⟨1546359, by decide⟩
    (prefixPartial 10 74882) = some ⟨10, 2, 0, 1546359, 74882, 1217, 1048576⟩ := by
  decide +kernel

theorem context_10_74882_1546359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74882 ⟨1546359, by decide⟩ :=
  accepted_of_selected 10 74882 ⟨1546359, by decide⟩ ⟨10, 2, 0, 1546359, 74882, 1217, 1048576⟩
    (by decide) selected_cut_52715

theorem selected_cut_52716 : selected 11 ⟨1546411, by decide⟩
    (prefixPartial 10 74883) = some ⟨10, 2, 0, 1546411, 74883, 1045, 1048576⟩ := by
  decide +kernel

theorem context_10_74883_1546411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74883 ⟨1546411, by decide⟩ :=
  accepted_of_selected 10 74883 ⟨1546411, by decide⟩ ⟨10, 2, 0, 1546411, 74883, 1045, 1048576⟩
    (by decide) selected_cut_52716

theorem unmarked_context_9_18720_1546412 : frontier 12 ⟨1546412, by decide⟩
    (prefixCache 9 18720) (prefixPartial 9 18720) = false := by
  decide +kernel

theorem node_context_9_18720_1546412 : EJMOriginalGlobalDAGData.nodes 12 ⟨1546412, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1546298, by decide⟩,⟨1546359, by decide⟩,⟨1546411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18720_1546412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18720 ⟨1546412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18720
    ⟨1546412, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1546298, by decide⟩,⟨1546359, by decide⟩,⟨1546411, by decide⟩]) unmarked_context_9_18720_1546412 node_context_9_18720_1546412
  intro a
  fin_cases a
  · exact context_10_74880_1468246
  · exact context_10_74881_1546298
  · exact context_10_74882_1546359
  · exact context_10_74883_1546411

theorem selected_cut_52717 : selected 12 ⟨1546498, by decide⟩
    (prefixPartial 9 18721) = some ⟨9, 2, 0, 1546498, 18721, 1273, 4194304⟩ := by
  decide +kernel

theorem context_9_18721_1546498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18721 ⟨1546498, by decide⟩ :=
  accepted_of_selected 9 18721 ⟨1546498, by decide⟩ ⟨9, 2, 0, 1546498, 18721, 1273, 4194304⟩
    (by decide) selected_cut_52717

theorem selected_cut_52718 : selected 12 ⟨1546605, by decide⟩
    (prefixPartial 9 18722) = some ⟨9, 2, 0, 1546605, 18722, 1005, 4194304⟩ := by
  decide +kernel

theorem context_9_18722_1546605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18722 ⟨1546605, by decide⟩ :=
  accepted_of_selected 9 18722 ⟨1546605, by decide⟩ ⟨9, 2, 0, 1546605, 18722, 1005, 4194304⟩
    (by decide) selected_cut_52718

theorem selected_cut_52719 : selected 12 ⟨1546614, by decide⟩
    (prefixPartial 9 18723) = some ⟨9, 2, 0, 1546614, 18723, 53, 4194304⟩ := by
  decide +kernel

theorem context_9_18723_1546614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18723 ⟨1546614, by decide⟩ :=
  accepted_of_selected 9 18723 ⟨1546614, by decide⟩ ⟨9, 2, 0, 1546614, 18723, 53, 4194304⟩
    (by decide) selected_cut_52719

theorem unmarked_context_8_4680_1546615 : frontier 13 ⟨1546615, by decide⟩
    (prefixCache 8 4680) (prefixPartial 8 4680) = false := by
  decide +kernel

theorem node_context_8_4680_1546615 : EJMOriginalGlobalDAGData.nodes 13 ⟨1546615, by decide⟩ =
    .split (coordinate 8) (![⟨1546412, by decide⟩,⟨1546498, by decide⟩,⟨1546605, by decide⟩,⟨1546614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4680_1546615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4680 ⟨1546615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4680
    ⟨1546615, by decide⟩ (by decide) (![⟨1546412, by decide⟩,⟨1546498, by decide⟩,⟨1546605, by decide⟩,⟨1546614, by decide⟩]) unmarked_context_8_4680_1546615 node_context_8_4680_1546615
  intro a
  fin_cases a
  · exact context_9_18720_1546412
  · exact context_9_18721_1546498
  · exact context_9_18722_1546605
  · exact context_9_18723_1546614

theorem selected_cut_52720 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 74896) = some ⟨10, 1, 0, 1468246, 74896, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74896_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74896 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 74896 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 74896, 1, 1048576⟩
    (by decide) selected_cut_52720

theorem selected_cut_52721 : selected 11 ⟨1546774, by decide⟩
    (prefixPartial 10 74897) = some ⟨10, 2, 0, 1546774, 74897, 3041, 1048576⟩ := by
  decide +kernel

theorem context_10_74897_1546774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74897 ⟨1546774, by decide⟩ :=
  accepted_of_selected 10 74897 ⟨1546774, by decide⟩ ⟨10, 2, 0, 1546774, 74897, 3041, 1048576⟩
    (by decide) selected_cut_52721

theorem selected_cut_52722 : selected 11 ⟨1546812, by decide⟩
    (prefixPartial 10 74898) = some ⟨10, 2, 0, 1546812, 74898, 709, 1048576⟩ := by
  decide +kernel

theorem context_10_74898_1546812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74898 ⟨1546812, by decide⟩ :=
  accepted_of_selected 10 74898 ⟨1546812, by decide⟩ ⟨10, 2, 0, 1546812, 74898, 709, 1048576⟩
    (by decide) selected_cut_52722

theorem selected_cut_52723 : selected 11 ⟨1546876, by decide⟩
    (prefixPartial 10 74899) = some ⟨10, 2, 0, 1546876, 74899, 1269, 1048576⟩ := by
  decide +kernel

theorem context_10_74899_1546876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74899 ⟨1546876, by decide⟩ :=
  accepted_of_selected 10 74899 ⟨1546876, by decide⟩ ⟨10, 2, 0, 1546876, 74899, 1269, 1048576⟩
    (by decide) selected_cut_52723

theorem unmarked_context_9_18724_1546877 : frontier 12 ⟨1546877, by decide⟩
    (prefixCache 9 18724) (prefixPartial 9 18724) = false := by
  decide +kernel

theorem node_context_9_18724_1546877 : EJMOriginalGlobalDAGData.nodes 12 ⟨1546877, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1546774, by decide⟩,⟨1546812, by decide⟩,⟨1546876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18724_1546877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18724 ⟨1546877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18724
    ⟨1546877, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1546774, by decide⟩,⟨1546812, by decide⟩,⟨1546876, by decide⟩]) unmarked_context_9_18724_1546877 node_context_9_18724_1546877
  intro a
  fin_cases a
  · exact context_10_74896_1468246
  · exact context_10_74897_1546774
  · exact context_10_74898_1546812
  · exact context_10_74899_1546876

theorem selected_cut_52724 : selected 12 ⟨1546989, by decide⟩
    (prefixPartial 9 18725) = some ⟨9, 2, 0, 1546989, 18725, 2641, 4194304⟩ := by
  decide +kernel

theorem context_9_18725_1546989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18725 ⟨1546989, by decide⟩ :=
  accepted_of_selected 9 18725 ⟨1546989, by decide⟩ ⟨9, 2, 0, 1546989, 18725, 2641, 4194304⟩
    (by decide) selected_cut_52724

theorem selected_cut_52725 : selected 12 ⟨1547080, by decide⟩
    (prefixPartial 9 18726) = some ⟨9, 2, 0, 1547080, 18726, 2117, 4194304⟩ := by
  decide +kernel

theorem context_9_18726_1547080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18726 ⟨1547080, by decide⟩ :=
  accepted_of_selected 9 18726 ⟨1547080, by decide⟩ ⟨9, 2, 0, 1547080, 18726, 2117, 4194304⟩
    (by decide) selected_cut_52725

theorem selected_cut_52726 : selected 12 ⟨1547114, by decide⟩
    (prefixPartial 9 18727) = some ⟨9, 2, 0, 1547114, 18727, 549, 4194304⟩ := by
  decide +kernel

theorem context_9_18727_1547114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18727 ⟨1547114, by decide⟩ :=
  accepted_of_selected 9 18727 ⟨1547114, by decide⟩ ⟨9, 2, 0, 1547114, 18727, 549, 4194304⟩
    (by decide) selected_cut_52726

theorem unmarked_context_8_4681_1547115 : frontier 13 ⟨1547115, by decide⟩
    (prefixCache 8 4681) (prefixPartial 8 4681) = false := by
  decide +kernel

theorem node_context_8_4681_1547115 : EJMOriginalGlobalDAGData.nodes 13 ⟨1547115, by decide⟩ =
    .split (coordinate 8) (![⟨1546877, by decide⟩,⟨1546989, by decide⟩,⟨1547080, by decide⟩,⟨1547114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4681_1547115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4681 ⟨1547115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4681
    ⟨1547115, by decide⟩ (by decide) (![⟨1546877, by decide⟩,⟨1546989, by decide⟩,⟨1547080, by decide⟩,⟨1547114, by decide⟩]) unmarked_context_8_4681_1547115 node_context_8_4681_1547115
  intro a
  fin_cases a
  · exact context_9_18724_1546877
  · exact context_9_18725_1546989
  · exact context_9_18726_1547080
  · exact context_9_18727_1547114

theorem selected_cut_52727 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 4682) = some ⟨8, 1, 0, 1364555, 4682, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4682_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4682 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 4682 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 4682, 1, 16777216⟩
    (by decide) selected_cut_52727

theorem selected_cut_52728 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 74928) = some ⟨10, 1, 0, 1468246, 74928, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74928_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74928 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 74928 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 74928, 1, 1048576⟩
    (by decide) selected_cut_52728

theorem selected_cut_52729 : selected 11 ⟨1547228, by decide⟩
    (prefixPartial 10 74929) = some ⟨10, 2, 0, 1547228, 74929, 3057, 1048576⟩ := by
  decide +kernel

theorem context_10_74929_1547228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74929 ⟨1547228, by decide⟩ :=
  accepted_of_selected 10 74929 ⟨1547228, by decide⟩ ⟨10, 2, 0, 1547228, 74929, 3057, 1048576⟩
    (by decide) selected_cut_52729

theorem selected_cut_52730 : selected 11 ⟨1547311, by decide⟩
    (prefixPartial 10 74930) = some ⟨10, 2, 0, 1547311, 74930, 1829, 1048576⟩ := by
  decide +kernel

theorem context_10_74930_1547311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74930 ⟨1547311, by decide⟩ :=
  accepted_of_selected 10 74930 ⟨1547311, by decide⟩ ⟨10, 2, 0, 1547311, 74930, 1829, 1048576⟩
    (by decide) selected_cut_52730

theorem selected_cut_52731 : selected 11 ⟨1547400, by decide⟩
    (prefixPartial 10 74931) = some ⟨10, 2, 0, 1547400, 74931, 2297, 1048576⟩ := by
  decide +kernel

theorem context_10_74931_1547400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74931 ⟨1547400, by decide⟩ :=
  accepted_of_selected 10 74931 ⟨1547400, by decide⟩ ⟨10, 2, 0, 1547400, 74931, 2297, 1048576⟩
    (by decide) selected_cut_52731

theorem unmarked_context_9_18732_1547401 : frontier 12 ⟨1547401, by decide⟩
    (prefixCache 9 18732) (prefixPartial 9 18732) = false := by
  decide +kernel

theorem node_context_9_18732_1547401 : EJMOriginalGlobalDAGData.nodes 12 ⟨1547401, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1547228, by decide⟩,⟨1547311, by decide⟩,⟨1547400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18732_1547401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18732 ⟨1547401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18732
    ⟨1547401, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1547228, by decide⟩,⟨1547311, by decide⟩,⟨1547400, by decide⟩]) unmarked_context_9_18732_1547401 node_context_9_18732_1547401
  intro a
  fin_cases a
  · exact context_10_74928_1468246
  · exact context_10_74929_1547228
  · exact context_10_74930_1547311
  · exact context_10_74931_1547400

theorem selected_cut_52732 : selected 12 ⟨1547538, by decide⟩
    (prefixPartial 9 18733) = some ⟨9, 2, 0, 1547538, 18733, 3777, 4194304⟩ := by
  decide +kernel

theorem context_9_18733_1547538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18733 ⟨1547538, by decide⟩ :=
  accepted_of_selected 9 18733 ⟨1547538, by decide⟩ ⟨9, 2, 0, 1547538, 18733, 3777, 4194304⟩
    (by decide) selected_cut_52732

theorem selected_cut_52733 : selected 12 ⟨1547686, by decide⟩
    (prefixPartial 9 18734) = some ⟨9, 2, 0, 1547686, 18734, 3181, 4194304⟩ := by
  decide +kernel

theorem context_9_18734_1547686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18734 ⟨1547686, by decide⟩ :=
  accepted_of_selected 9 18734 ⟨1547686, by decide⟩ ⟨9, 2, 0, 1547686, 18734, 3181, 4194304⟩
    (by decide) selected_cut_52733

theorem selected_cut_52734 : selected 12 ⟨1547742, by decide⟩
    (prefixPartial 9 18735) = some ⟨9, 2, 0, 1547742, 18735, 873, 4194304⟩ := by
  decide +kernel

theorem context_9_18735_1547742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18735 ⟨1547742, by decide⟩ :=
  accepted_of_selected 9 18735 ⟨1547742, by decide⟩ ⟨9, 2, 0, 1547742, 18735, 873, 4194304⟩
    (by decide) selected_cut_52734

theorem unmarked_context_8_4683_1547743 : frontier 13 ⟨1547743, by decide⟩
    (prefixCache 8 4683) (prefixPartial 8 4683) = false := by
  decide +kernel

theorem node_context_8_4683_1547743 : EJMOriginalGlobalDAGData.nodes 13 ⟨1547743, by decide⟩ =
    .split (coordinate 8) (![⟨1547401, by decide⟩,⟨1547538, by decide⟩,⟨1547686, by decide⟩,⟨1547742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4683_1547743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4683 ⟨1547743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4683
    ⟨1547743, by decide⟩ (by decide) (![⟨1547401, by decide⟩,⟨1547538, by decide⟩,⟨1547686, by decide⟩,⟨1547742, by decide⟩]) unmarked_context_8_4683_1547743 node_context_8_4683_1547743
  intro a
  fin_cases a
  · exact context_9_18732_1547401
  · exact context_9_18733_1547538
  · exact context_9_18734_1547686
  · exact context_9_18735_1547742

theorem unmarked_context_7_1170_1547744 : frontier 14 ⟨1547744, by decide⟩
    (prefixCache 7 1170) (prefixPartial 7 1170) = false := by
  decide +kernel

theorem node_context_7_1170_1547744 : EJMOriginalGlobalDAGData.nodes 14 ⟨1547744, by decide⟩ =
    .split (coordinate 7) (![⟨1546615, by decide⟩,⟨1547115, by decide⟩,⟨1364555, by decide⟩,⟨1547743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1170_1547744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1170 ⟨1547744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1170
    ⟨1547744, by decide⟩ (by decide) (![⟨1546615, by decide⟩,⟨1547115, by decide⟩,⟨1364555, by decide⟩,⟨1547743, by decide⟩]) unmarked_context_7_1170_1547744 node_context_7_1170_1547744
  intro a
  fin_cases a
  · exact context_8_4680_1546615
  · exact context_8_4681_1547115
  · exact context_8_4682_1364555
  · exact context_8_4683_1547743

theorem selected_cut_52735 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 74944) = some ⟨10, 1, 0, 1468246, 74944, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74944_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74944 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 74944 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 74944, 1, 1048576⟩
    (by decide) selected_cut_52735

theorem selected_cut_52736 : selected 11 ⟨1547869, by decide⟩
    (prefixPartial 10 74945) = some ⟨10, 2, 0, 1547869, 74945, 2493, 1048576⟩ := by
  decide +kernel

theorem context_10_74945_1547869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74945 ⟨1547869, by decide⟩ :=
  accepted_of_selected 10 74945 ⟨1547869, by decide⟩ ⟨10, 2, 0, 1547869, 74945, 2493, 1048576⟩
    (by decide) selected_cut_52736

theorem selected_cut_52737 : selected 11 ⟨1547962, by decide⟩
    (prefixPartial 10 74946) = some ⟨10, 2, 0, 1547962, 74946, 1657, 1048576⟩ := by
  decide +kernel

theorem context_10_74946_1547962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74946 ⟨1547962, by decide⟩ :=
  accepted_of_selected 10 74946 ⟨1547962, by decide⟩ ⟨10, 2, 0, 1547962, 74946, 1657, 1048576⟩
    (by decide) selected_cut_52737

theorem selected_cut_52738 : selected 11 ⟨1548007, by decide⟩
    (prefixPartial 10 74947) = some ⟨10, 2, 0, 1548007, 74947, 1157, 1048576⟩ := by
  decide +kernel

theorem context_10_74947_1548007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74947 ⟨1548007, by decide⟩ :=
  accepted_of_selected 10 74947 ⟨1548007, by decide⟩ ⟨10, 2, 0, 1548007, 74947, 1157, 1048576⟩
    (by decide) selected_cut_52738

theorem unmarked_context_9_18736_1548008 : frontier 12 ⟨1548008, by decide⟩
    (prefixCache 9 18736) (prefixPartial 9 18736) = false := by
  decide +kernel

theorem node_context_9_18736_1548008 : EJMOriginalGlobalDAGData.nodes 12 ⟨1548008, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1547869, by decide⟩,⟨1547962, by decide⟩,⟨1548007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18736_1548008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18736 ⟨1548008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18736
    ⟨1548008, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1547869, by decide⟩,⟨1547962, by decide⟩,⟨1548007, by decide⟩]) unmarked_context_9_18736_1548008 node_context_9_18736_1548008
  intro a
  fin_cases a
  · exact context_10_74944_1468246
  · exact context_10_74945_1547869
  · exact context_10_74946_1547962
  · exact context_10_74947_1548007

theorem selected_cut_52739 : selected 12 ⟨1548118, by decide⟩
    (prefixPartial 9 18737) = some ⟨9, 2, 0, 1548118, 18737, 2749, 4194304⟩ := by
  decide +kernel

theorem context_9_18737_1548118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18737 ⟨1548118, by decide⟩ :=
  accepted_of_selected 9 18737 ⟨1548118, by decide⟩ ⟨9, 2, 0, 1548118, 18737, 2749, 4194304⟩
    (by decide) selected_cut_52739

theorem selected_cut_52740 : selected 12 ⟨1548200, by decide⟩
    (prefixPartial 9 18738) = some ⟨9, 2, 0, 1548200, 18738, 2029, 4194304⟩ := by
  decide +kernel

theorem context_9_18738_1548200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18738 ⟨1548200, by decide⟩ :=
  accepted_of_selected 9 18738 ⟨1548200, by decide⟩ ⟨9, 2, 0, 1548200, 18738, 2029, 4194304⟩
    (by decide) selected_cut_52740

theorem selected_cut_52741 : selected 12 ⟨1548243, by decide⟩
    (prefixPartial 9 18739) = some ⟨9, 2, 0, 1548243, 18739, 789, 4194304⟩ := by
  decide +kernel

theorem context_9_18739_1548243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18739 ⟨1548243, by decide⟩ :=
  accepted_of_selected 9 18739 ⟨1548243, by decide⟩ ⟨9, 2, 0, 1548243, 18739, 789, 4194304⟩
    (by decide) selected_cut_52741

theorem unmarked_context_8_4684_1548244 : frontier 13 ⟨1548244, by decide⟩
    (prefixCache 8 4684) (prefixPartial 8 4684) = false := by
  decide +kernel

theorem node_context_8_4684_1548244 : EJMOriginalGlobalDAGData.nodes 13 ⟨1548244, by decide⟩ =
    .split (coordinate 8) (![⟨1548008, by decide⟩,⟨1548118, by decide⟩,⟨1548200, by decide⟩,⟨1548243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4684_1548244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4684 ⟨1548244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4684
    ⟨1548244, by decide⟩ (by decide) (![⟨1548008, by decide⟩,⟨1548118, by decide⟩,⟨1548200, by decide⟩,⟨1548243, by decide⟩]) unmarked_context_8_4684_1548244 node_context_8_4684_1548244
  intro a
  fin_cases a
  · exact context_9_18736_1548008
  · exact context_9_18737_1548118
  · exact context_9_18738_1548200
  · exact context_9_18739_1548243

theorem selected_cut_52742 : selected 12 ⟨1548433, by decide⟩
    (prefixPartial 9 18740) = some ⟨9, 2, 0, 1548433, 18740, 4025, 4194304⟩ := by
  decide +kernel

theorem context_9_18740_1548433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18740 ⟨1548433, by decide⟩ :=
  accepted_of_selected 9 18740 ⟨1548433, by decide⟩ ⟨9, 2, 0, 1548433, 18740, 4025, 4194304⟩
    (by decide) selected_cut_52742

theorem selected_cut_52743 : selected 12 ⟨1548538, by decide⟩
    (prefixPartial 9 18741) = some ⟨9, 2, 0, 1548538, 18741, 2457, 4194304⟩ := by
  decide +kernel

theorem context_9_18741_1548538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18741 ⟨1548538, by decide⟩ :=
  accepted_of_selected 9 18741 ⟨1548538, by decide⟩ ⟨9, 2, 0, 1548538, 18741, 2457, 4194304⟩
    (by decide) selected_cut_52743

theorem selected_cut_52744 : selected 12 ⟨1548601, by decide⟩
    (prefixPartial 9 18742) = some ⟨9, 2, 0, 1548601, 18742, 1597, 4194304⟩ := by
  decide +kernel

theorem context_9_18742_1548601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18742 ⟨1548601, by decide⟩ :=
  accepted_of_selected 9 18742 ⟨1548601, by decide⟩ ⟨9, 2, 0, 1548601, 18742, 1597, 4194304⟩
    (by decide) selected_cut_52744

theorem selected_cut_52745 : selected 12 ⟨1548638, by decide⟩
    (prefixPartial 9 18743) = some ⟨9, 2, 0, 1548638, 18743, 573, 4194304⟩ := by
  decide +kernel

theorem context_9_18743_1548638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18743 ⟨1548638, by decide⟩ :=
  accepted_of_selected 9 18743 ⟨1548638, by decide⟩ ⟨9, 2, 0, 1548638, 18743, 573, 4194304⟩
    (by decide) selected_cut_52745

theorem unmarked_context_8_4685_1548639 : frontier 13 ⟨1548639, by decide⟩
    (prefixCache 8 4685) (prefixPartial 8 4685) = false := by
  decide +kernel

theorem node_context_8_4685_1548639 : EJMOriginalGlobalDAGData.nodes 13 ⟨1548639, by decide⟩ =
    .split (coordinate 8) (![⟨1548433, by decide⟩,⟨1548538, by decide⟩,⟨1548601, by decide⟩,⟨1548638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4685_1548639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4685 ⟨1548639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4685
    ⟨1548639, by decide⟩ (by decide) (![⟨1548433, by decide⟩,⟨1548538, by decide⟩,⟨1548601, by decide⟩,⟨1548638, by decide⟩]) unmarked_context_8_4685_1548639 node_context_8_4685_1548639
  intro a
  fin_cases a
  · exact context_9_18740_1548433
  · exact context_9_18741_1548538
  · exact context_9_18742_1548601
  · exact context_9_18743_1548638

theorem selected_cut_52746 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 4686) = some ⟨8, 1, 0, 1364555, 4686, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4686_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4686 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 4686 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 4686, 1, 16777216⟩
    (by decide) selected_cut_52746

theorem selected_cut_52747 : selected 12 ⟨1548816, by decide⟩
    (prefixPartial 9 18748) = some ⟨9, 2, 0, 1548816, 18748, 3345, 4194304⟩ := by
  decide +kernel

theorem context_9_18748_1548816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18748 ⟨1548816, by decide⟩ :=
  accepted_of_selected 9 18748 ⟨1548816, by decide⟩ ⟨9, 2, 0, 1548816, 18748, 3345, 4194304⟩
    (by decide) selected_cut_52747

theorem selected_cut_52748 : selected 12 ⟨1548901, by decide⟩
    (prefixPartial 9 18749) = some ⟨9, 2, 0, 1548901, 18749, 1673, 4194304⟩ := by
  decide +kernel

theorem context_9_18749_1548901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18749 ⟨1548901, by decide⟩ :=
  accepted_of_selected 9 18749 ⟨1548901, by decide⟩ ⟨9, 2, 0, 1548901, 18749, 1673, 4194304⟩
    (by decide) selected_cut_52748

theorem selected_cut_52749 : selected 12 ⟨1548972, by decide⟩
    (prefixPartial 9 18750) = some ⟨9, 2, 0, 1548972, 18750, 1681, 4194304⟩ := by
  decide +kernel

theorem context_9_18750_1548972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18750 ⟨1548972, by decide⟩ :=
  accepted_of_selected 9 18750 ⟨1548972, by decide⟩ ⟨9, 2, 0, 1548972, 18750, 1681, 4194304⟩
    (by decide) selected_cut_52749

theorem selected_cut_52750 : selected 12 ⟨1549008, by decide⟩
    (prefixPartial 9 18751) = some ⟨9, 2, 0, 1549008, 18751, 601, 4194304⟩ := by
  decide +kernel

theorem context_9_18751_1549008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18751 ⟨1549008, by decide⟩ :=
  accepted_of_selected 9 18751 ⟨1549008, by decide⟩ ⟨9, 2, 0, 1549008, 18751, 601, 4194304⟩
    (by decide) selected_cut_52750

theorem unmarked_context_8_4687_1549009 : frontier 13 ⟨1549009, by decide⟩
    (prefixCache 8 4687) (prefixPartial 8 4687) = false := by
  decide +kernel

theorem node_context_8_4687_1549009 : EJMOriginalGlobalDAGData.nodes 13 ⟨1549009, by decide⟩ =
    .split (coordinate 8) (![⟨1548816, by decide⟩,⟨1548901, by decide⟩,⟨1548972, by decide⟩,⟨1549008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4687_1549009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4687 ⟨1549009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4687
    ⟨1549009, by decide⟩ (by decide) (![⟨1548816, by decide⟩,⟨1548901, by decide⟩,⟨1548972, by decide⟩,⟨1549008, by decide⟩]) unmarked_context_8_4687_1549009 node_context_8_4687_1549009
  intro a
  fin_cases a
  · exact context_9_18748_1548816
  · exact context_9_18749_1548901
  · exact context_9_18750_1548972
  · exact context_9_18751_1549008

theorem unmarked_context_7_1171_1549010 : frontier 14 ⟨1549010, by decide⟩
    (prefixCache 7 1171) (prefixPartial 7 1171) = false := by
  decide +kernel

theorem node_context_7_1171_1549010 : EJMOriginalGlobalDAGData.nodes 14 ⟨1549010, by decide⟩ =
    .split (coordinate 7) (![⟨1548244, by decide⟩,⟨1548639, by decide⟩,⟨1364555, by decide⟩,⟨1549009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1171_1549010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1171 ⟨1549010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1171
    ⟨1549010, by decide⟩ (by decide) (![⟨1548244, by decide⟩,⟨1548639, by decide⟩,⟨1364555, by decide⟩,⟨1549009, by decide⟩]) unmarked_context_7_1171_1549010 node_context_7_1171_1549010
  intro a
  fin_cases a
  · exact context_8_4684_1548244
  · exact context_8_4685_1548639
  · exact context_8_4686_1364555
  · exact context_8_4687_1549009

theorem unmarked_context_6_292_1549011 : frontier 15 ⟨1549011, by decide⟩
    (prefixCache 6 292) (prefixPartial 6 292) = false := by
  decide +kernel

theorem node_context_6_292_1549011 : EJMOriginalGlobalDAGData.nodes 15 ⟨1549011, by decide⟩ =
    .split (coordinate 6) (![⟨1546095, by decide⟩,⟨1539247, by decide⟩,⟨1547744, by decide⟩,⟨1549010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_292_1549011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 292 ⟨1549011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 292
    ⟨1549011, by decide⟩ (by decide) (![⟨1546095, by decide⟩,⟨1539247, by decide⟩,⟨1547744, by decide⟩,⟨1549010, by decide⟩]) unmarked_context_6_292_1549011 node_context_6_292_1549011
  intro a
  fin_cases a
  · exact context_7_1168_1546095
  · exact context_7_1169_1539247
  · exact context_7_1170_1547744
  · exact context_7_1171_1549010

theorem selected_cut_52751 : selected 15 ⟨1475984, by decide⟩
    (prefixPartial 6 293) = some ⟨6, 1, 0, 1475984, 293, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_293_1475984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 293 ⟨1475984, by decide⟩ :=
  accepted_of_selected 6 293 ⟨1475984, by decide⟩ ⟨6, 1, 0, 1475984, 293, 1, 268435456⟩
    (by decide) selected_cut_52751

theorem selected_cut_52752 : selected 15 ⟨1549012, by decide⟩
    (prefixPartial 6 294) = some ⟨6, 1, 0, 1549012, 294, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_294_1549012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 294 ⟨1549012, by decide⟩ :=
  accepted_of_selected 6 294 ⟨1549012, by decide⟩ ⟨6, 1, 0, 1549012, 294, 1, 268435456⟩
    (by decide) selected_cut_52752

theorem selected_cut_52753 : selected 12 ⟨1549163, by decide⟩
    (prefixPartial 9 18880) = some ⟨9, 2, 0, 1549163, 18880, 2653, 4194304⟩ := by
  decide +kernel

theorem context_9_18880_1549163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18880 ⟨1549163, by decide⟩ :=
  accepted_of_selected 9 18880 ⟨1549163, by decide⟩ ⟨9, 2, 0, 1549163, 18880, 2653, 4194304⟩
    (by decide) selected_cut_52753

theorem selected_cut_52754 : selected 12 ⟨1549228, by decide⟩
    (prefixPartial 9 18881) = some ⟨9, 2, 0, 1549228, 18881, 1277, 4194304⟩ := by
  decide +kernel

theorem context_9_18881_1549228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18881 ⟨1549228, by decide⟩ :=
  accepted_of_selected 9 18881 ⟨1549228, by decide⟩ ⟨9, 2, 0, 1549228, 18881, 1277, 4194304⟩
    (by decide) selected_cut_52754

theorem selected_cut_52755 : selected 12 ⟨1549281, by decide⟩
    (prefixPartial 9 18882) = some ⟨9, 2, 0, 1549281, 18882, 1025, 4194304⟩ := by
  decide +kernel

theorem context_9_18882_1549281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18882 ⟨1549281, by decide⟩ :=
  accepted_of_selected 9 18882 ⟨1549281, by decide⟩ ⟨9, 2, 0, 1549281, 18882, 1025, 4194304⟩
    (by decide) selected_cut_52755

theorem selected_cut_52756 : selected 12 ⟨1549307, by decide⟩
    (prefixPartial 9 18883) = some ⟨9, 2, 0, 1549307, 18883, 409, 4194304⟩ := by
  decide +kernel

theorem context_9_18883_1549307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18883 ⟨1549307, by decide⟩ :=
  accepted_of_selected 9 18883 ⟨1549307, by decide⟩ ⟨9, 2, 0, 1549307, 18883, 409, 4194304⟩
    (by decide) selected_cut_52756

theorem unmarked_context_8_4720_1549308 : frontier 13 ⟨1549308, by decide⟩
    (prefixCache 8 4720) (prefixPartial 8 4720) = false := by
  decide +kernel

theorem node_context_8_4720_1549308 : EJMOriginalGlobalDAGData.nodes 13 ⟨1549308, by decide⟩ =
    .split (coordinate 8) (![⟨1549163, by decide⟩,⟨1549228, by decide⟩,⟨1549281, by decide⟩,⟨1549307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4720_1549308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4720 ⟨1549308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4720
    ⟨1549308, by decide⟩ (by decide) (![⟨1549163, by decide⟩,⟨1549228, by decide⟩,⟨1549281, by decide⟩,⟨1549307, by decide⟩]) unmarked_context_8_4720_1549308 node_context_8_4720_1549308
  intro a
  fin_cases a
  · exact context_9_18880_1549163
  · exact context_9_18881_1549228
  · exact context_9_18882_1549281
  · exact context_9_18883_1549307

theorem selected_cut_52757 : selected 12 ⟨1549521, by decide⟩
    (prefixPartial 9 18884) = some ⟨9, 2, 0, 1549521, 18884, 3661, 4194304⟩ := by
  decide +kernel

theorem context_9_18884_1549521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18884 ⟨1549521, by decide⟩ :=
  accepted_of_selected 9 18884 ⟨1549521, by decide⟩ ⟨9, 2, 0, 1549521, 18884, 3661, 4194304⟩
    (by decide) selected_cut_52757

theorem selected_cut_52758 : selected 12 ⟨1549634, by decide⟩
    (prefixPartial 9 18885) = some ⟨9, 2, 0, 1549634, 18885, 1761, 4194304⟩ := by
  decide +kernel

theorem context_9_18885_1549634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18885 ⟨1549634, by decide⟩ :=
  accepted_of_selected 9 18885 ⟨1549634, by decide⟩ ⟨9, 2, 0, 1549634, 18885, 1761, 4194304⟩
    (by decide) selected_cut_52758

theorem selected_cut_52759 : selected 12 ⟨1549716, by decide⟩
    (prefixPartial 9 18886) = some ⟨9, 2, 0, 1549716, 18886, 1221, 4194304⟩ := by
  decide +kernel

theorem context_9_18886_1549716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18886 ⟨1549716, by decide⟩ :=
  accepted_of_selected 9 18886 ⟨1549716, by decide⟩ ⟨9, 2, 0, 1549716, 18886, 1221, 4194304⟩
    (by decide) selected_cut_52759

theorem selected_cut_52760 : selected 12 ⟨1549741, by decide⟩
    (prefixPartial 9 18887) = some ⟨9, 2, 0, 1549741, 18887, 445, 4194304⟩ := by
  decide +kernel

theorem context_9_18887_1549741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18887 ⟨1549741, by decide⟩ :=
  accepted_of_selected 9 18887 ⟨1549741, by decide⟩ ⟨9, 2, 0, 1549741, 18887, 445, 4194304⟩
    (by decide) selected_cut_52760

theorem unmarked_context_8_4721_1549742 : frontier 13 ⟨1549742, by decide⟩
    (prefixCache 8 4721) (prefixPartial 8 4721) = false := by
  decide +kernel

theorem node_context_8_4721_1549742 : EJMOriginalGlobalDAGData.nodes 13 ⟨1549742, by decide⟩ =
    .split (coordinate 8) (![⟨1549521, by decide⟩,⟨1549634, by decide⟩,⟨1549716, by decide⟩,⟨1549741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4721_1549742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4721 ⟨1549742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4721
    ⟨1549742, by decide⟩ (by decide) (![⟨1549521, by decide⟩,⟨1549634, by decide⟩,⟨1549716, by decide⟩,⟨1549741, by decide⟩]) unmarked_context_8_4721_1549742 node_context_8_4721_1549742
  intro a
  fin_cases a
  · exact context_9_18884_1549521
  · exact context_9_18885_1549634
  · exact context_9_18886_1549716
  · exact context_9_18887_1549741

theorem selected_cut_52761 : selected 12 ⟨1549940, by decide⟩
    (prefixPartial 9 18888) = some ⟨9, 2, 0, 1549940, 18888, 3613, 4194304⟩ := by
  decide +kernel

theorem context_9_18888_1549940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18888 ⟨1549940, by decide⟩ :=
  accepted_of_selected 9 18888 ⟨1549940, by decide⟩ ⟨9, 2, 0, 1549940, 18888, 3613, 4194304⟩
    (by decide) selected_cut_52761

theorem selected_cut_52762 : selected 12 ⟨1550012, by decide⟩
    (prefixPartial 9 18889) = some ⟨9, 2, 0, 1550012, 18889, 1677, 4194304⟩ := by
  decide +kernel

theorem context_9_18889_1550012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18889 ⟨1550012, by decide⟩ :=
  accepted_of_selected 9 18889 ⟨1550012, by decide⟩ ⟨9, 2, 0, 1550012, 18889, 1677, 4194304⟩
    (by decide) selected_cut_52762

theorem selected_cut_52763 : selected 12 ⟨1550081, by decide⟩
    (prefixPartial 9 18890) = some ⟨9, 2, 0, 1550081, 18890, 1253, 4194304⟩ := by
  decide +kernel

theorem context_9_18890_1550081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18890 ⟨1550081, by decide⟩ :=
  accepted_of_selected 9 18890 ⟨1550081, by decide⟩ ⟨9, 2, 0, 1550081, 18890, 1253, 4194304⟩
    (by decide) selected_cut_52763

theorem selected_cut_52764 : selected 12 ⟨1550107, by decide⟩
    (prefixPartial 9 18891) = some ⟨9, 2, 0, 1550107, 18891, 353, 4194304⟩ := by
  decide +kernel

theorem context_9_18891_1550107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18891 ⟨1550107, by decide⟩ :=
  accepted_of_selected 9 18891 ⟨1550107, by decide⟩ ⟨9, 2, 0, 1550107, 18891, 353, 4194304⟩
    (by decide) selected_cut_52764

theorem unmarked_context_8_4722_1550108 : frontier 13 ⟨1550108, by decide⟩
    (prefixCache 8 4722) (prefixPartial 8 4722) = false := by
  decide +kernel

theorem node_context_8_4722_1550108 : EJMOriginalGlobalDAGData.nodes 13 ⟨1550108, by decide⟩ =
    .split (coordinate 8) (![⟨1549940, by decide⟩,⟨1550012, by decide⟩,⟨1550081, by decide⟩,⟨1550107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4722_1550108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4722 ⟨1550108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4722
    ⟨1550108, by decide⟩ (by decide) (![⟨1549940, by decide⟩,⟨1550012, by decide⟩,⟨1550081, by decide⟩,⟨1550107, by decide⟩]) unmarked_context_8_4722_1550108 node_context_8_4722_1550108
  intro a
  fin_cases a
  · exact context_9_18888_1549940
  · exact context_9_18889_1550012
  · exact context_9_18890_1550081
  · exact context_9_18891_1550107

theorem selected_cut_52765 : selected 12 ⟨1550247, by decide⟩
    (prefixPartial 9 18892) = some ⟨9, 2, 0, 1550247, 18892, 2857, 4194304⟩ := by
  decide +kernel

theorem context_9_18892_1550247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18892 ⟨1550247, by decide⟩ :=
  accepted_of_selected 9 18892 ⟨1550247, by decide⟩ ⟨9, 2, 0, 1550247, 18892, 2857, 4194304⟩
    (by decide) selected_cut_52765

theorem selected_cut_52766 : selected 12 ⟨1550326, by decide⟩
    (prefixPartial 9 18893) = some ⟨9, 2, 0, 1550326, 18893, 1457, 4194304⟩ := by
  decide +kernel

theorem context_9_18893_1550326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18893 ⟨1550326, by decide⟩ :=
  accepted_of_selected 9 18893 ⟨1550326, by decide⟩ ⟨9, 2, 0, 1550326, 18893, 1457, 4194304⟩
    (by decide) selected_cut_52766

theorem selected_cut_52767 : selected 12 ⟨1550368, by decide⟩
    (prefixPartial 9 18894) = some ⟨9, 2, 0, 1550368, 18894, 961, 4194304⟩ := by
  decide +kernel

theorem context_9_18894_1550368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18894 ⟨1550368, by decide⟩ :=
  accepted_of_selected 9 18894 ⟨1550368, by decide⟩ ⟨9, 2, 0, 1550368, 18894, 961, 4194304⟩
    (by decide) selected_cut_52767

theorem selected_cut_52768 : selected 12 ⟨1550395, by decide⟩
    (prefixPartial 9 18895) = some ⟨9, 2, 0, 1550395, 18895, 413, 4194304⟩ := by
  decide +kernel

theorem context_9_18895_1550395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18895 ⟨1550395, by decide⟩ :=
  accepted_of_selected 9 18895 ⟨1550395, by decide⟩ ⟨9, 2, 0, 1550395, 18895, 413, 4194304⟩
    (by decide) selected_cut_52768

theorem unmarked_context_8_4723_1550396 : frontier 13 ⟨1550396, by decide⟩
    (prefixCache 8 4723) (prefixPartial 8 4723) = false := by
  decide +kernel

theorem node_context_8_4723_1550396 : EJMOriginalGlobalDAGData.nodes 13 ⟨1550396, by decide⟩ =
    .split (coordinate 8) (![⟨1550247, by decide⟩,⟨1550326, by decide⟩,⟨1550368, by decide⟩,⟨1550395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4723_1550396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4723 ⟨1550396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4723
    ⟨1550396, by decide⟩ (by decide) (![⟨1550247, by decide⟩,⟨1550326, by decide⟩,⟨1550368, by decide⟩,⟨1550395, by decide⟩]) unmarked_context_8_4723_1550396 node_context_8_4723_1550396
  intro a
  fin_cases a
  · exact context_9_18892_1550247
  · exact context_9_18893_1550326
  · exact context_9_18894_1550368
  · exact context_9_18895_1550395

theorem unmarked_context_7_1180_1550397 : frontier 14 ⟨1550397, by decide⟩
    (prefixCache 7 1180) (prefixPartial 7 1180) = false := by
  decide +kernel

theorem node_context_7_1180_1550397 : EJMOriginalGlobalDAGData.nodes 14 ⟨1550397, by decide⟩ =
    .split (coordinate 7) (![⟨1549308, by decide⟩,⟨1549742, by decide⟩,⟨1550108, by decide⟩,⟨1550396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1180_1550397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1180 ⟨1550397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1180
    ⟨1550397, by decide⟩ (by decide) (![⟨1549308, by decide⟩,⟨1549742, by decide⟩,⟨1550108, by decide⟩,⟨1550396, by decide⟩]) unmarked_context_7_1180_1550397 node_context_7_1180_1550397
  intro a
  fin_cases a
  · exact context_8_4720_1549308
  · exact context_8_4721_1549742
  · exact context_8_4722_1550108
  · exact context_8_4723_1550396

theorem selected_cut_52769 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 75584) = some ⟨10, 1, 0, 1468246, 75584, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_75584_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75584 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 75584 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 75584, 1, 1048576⟩
    (by decide) selected_cut_52769

theorem selected_cut_52770 : selected 11 ⟨1550481, by decide⟩
    (prefixPartial 10 75585) = some ⟨10, 2, 0, 1550481, 75585, 1257, 1048576⟩ := by
  decide +kernel

theorem context_10_75585_1550481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75585 ⟨1550481, by decide⟩ :=
  accepted_of_selected 10 75585 ⟨1550481, by decide⟩ ⟨10, 2, 0, 1550481, 75585, 1257, 1048576⟩
    (by decide) selected_cut_52770

theorem selected_cut_52771 : selected 11 ⟨1550565, by decide⟩
    (prefixPartial 10 75586) = some ⟨10, 2, 0, 1550565, 75586, 1769, 1048576⟩ := by
  decide +kernel

theorem context_10_75586_1550565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75586 ⟨1550565, by decide⟩ :=
  accepted_of_selected 10 75586 ⟨1550565, by decide⟩ ⟨10, 2, 0, 1550565, 75586, 1769, 1048576⟩
    (by decide) selected_cut_52771

theorem selected_cut_52772 : selected 11 ⟨1550647, by decide⟩
    (prefixPartial 10 75587) = some ⟨10, 2, 0, 1550647, 75587, 1497, 1048576⟩ := by
  decide +kernel

theorem context_10_75587_1550647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75587 ⟨1550647, by decide⟩ :=
  accepted_of_selected 10 75587 ⟨1550647, by decide⟩ ⟨10, 2, 0, 1550647, 75587, 1497, 1048576⟩
    (by decide) selected_cut_52772

theorem unmarked_context_9_18896_1550648 : frontier 12 ⟨1550648, by decide⟩
    (prefixCache 9 18896) (prefixPartial 9 18896) = false := by
  decide +kernel

theorem node_context_9_18896_1550648 : EJMOriginalGlobalDAGData.nodes 12 ⟨1550648, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1550481, by decide⟩,⟨1550565, by decide⟩,⟨1550647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18896_1550648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18896 ⟨1550648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18896
    ⟨1550648, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1550481, by decide⟩,⟨1550565, by decide⟩,⟨1550647, by decide⟩]) unmarked_context_9_18896_1550648 node_context_9_18896_1550648
  intro a
  fin_cases a
  · exact context_10_75584_1468246
  · exact context_10_75585_1550481
  · exact context_10_75586_1550565
  · exact context_10_75587_1550647

theorem selected_cut_52773 : selected 12 ⟨1550768, by decide⟩
    (prefixPartial 9 18897) = some ⟨9, 2, 0, 1550768, 18897, 1857, 4194304⟩ := by
  decide +kernel

theorem context_9_18897_1550768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18897 ⟨1550768, by decide⟩ :=
  accepted_of_selected 9 18897 ⟨1550768, by decide⟩ ⟨9, 2, 0, 1550768, 18897, 1857, 4194304⟩
    (by decide) selected_cut_52773

theorem selected_cut_52774 : selected 12 ⟨1550834, by decide⟩
    (prefixPartial 9 18898) = some ⟨9, 2, 0, 1550834, 18898, 1261, 4194304⟩ := by
  decide +kernel

theorem context_9_18898_1550834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18898 ⟨1550834, by decide⟩ :=
  accepted_of_selected 9 18898 ⟨1550834, by decide⟩ ⟨9, 2, 0, 1550834, 18898, 1261, 4194304⟩
    (by decide) selected_cut_52774

theorem selected_cut_52775 : selected 12 ⟨1550864, by decide⟩
    (prefixPartial 9 18899) = some ⟨9, 2, 0, 1550864, 18899, 453, 4194304⟩ := by
  decide +kernel

theorem context_9_18899_1550864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18899 ⟨1550864, by decide⟩ :=
  accepted_of_selected 9 18899 ⟨1550864, by decide⟩ ⟨9, 2, 0, 1550864, 18899, 453, 4194304⟩
    (by decide) selected_cut_52775

theorem unmarked_context_8_4724_1550865 : frontier 13 ⟨1550865, by decide⟩
    (prefixCache 8 4724) (prefixPartial 8 4724) = false := by
  decide +kernel

theorem node_context_8_4724_1550865 : EJMOriginalGlobalDAGData.nodes 13 ⟨1550865, by decide⟩ =
    .split (coordinate 8) (![⟨1550648, by decide⟩,⟨1550768, by decide⟩,⟨1550834, by decide⟩,⟨1550864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4724_1550865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4724 ⟨1550865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4724
    ⟨1550865, by decide⟩ (by decide) (![⟨1550648, by decide⟩,⟨1550768, by decide⟩,⟨1550834, by decide⟩,⟨1550864, by decide⟩]) unmarked_context_8_4724_1550865 node_context_8_4724_1550865
  intro a
  fin_cases a
  · exact context_9_18896_1550648
  · exact context_9_18897_1550768
  · exact context_9_18898_1550834
  · exact context_9_18899_1550864

theorem selected_cut_52776 : selected 13 ⟨1551075, by decide⟩
    (prefixPartial 8 4725) = some ⟨8, 2, 0, 1551075, 4725, 3677, 16777216⟩ := by
  decide +kernel

theorem context_8_4725_1551075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4725 ⟨1551075, by decide⟩ :=
  accepted_of_selected 8 4725 ⟨1551075, by decide⟩ ⟨8, 2, 0, 1551075, 4725, 3677, 16777216⟩
    (by decide) selected_cut_52776

theorem selected_cut_52777 : selected 12 ⟨1551241, by decide⟩
    (prefixPartial 9 18904) = some ⟨9, 2, 0, 1551241, 18904, 3925, 4194304⟩ := by
  decide +kernel

theorem context_9_18904_1551241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18904 ⟨1551241, by decide⟩ :=
  accepted_of_selected 9 18904 ⟨1551241, by decide⟩ ⟨9, 2, 0, 1551241, 18904, 3925, 4194304⟩
    (by decide) selected_cut_52777

theorem selected_cut_52778 : selected 12 ⟨1551309, by decide⟩
    (prefixPartial 9 18905) = some ⟨9, 2, 0, 1551309, 18905, 1901, 4194304⟩ := by
  decide +kernel

theorem context_9_18905_1551309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18905 ⟨1551309, by decide⟩ :=
  accepted_of_selected 9 18905 ⟨1551309, by decide⟩ ⟨9, 2, 0, 1551309, 18905, 1901, 4194304⟩
    (by decide) selected_cut_52778

theorem selected_cut_52779 : selected 12 ⟨1551374, by decide⟩
    (prefixPartial 9 18906) = some ⟨9, 2, 0, 1551374, 18906, 1993, 4194304⟩ := by
  decide +kernel

theorem context_9_18906_1551374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18906 ⟨1551374, by decide⟩ :=
  accepted_of_selected 9 18906 ⟨1551374, by decide⟩ ⟨9, 2, 0, 1551374, 18906, 1993, 4194304⟩
    (by decide) selected_cut_52779

theorem selected_cut_52780 : selected 12 ⟨1551408, by decide⟩
    (prefixPartial 9 18907) = some ⟨9, 2, 0, 1551408, 18907, 517, 4194304⟩ := by
  decide +kernel

theorem context_9_18907_1551408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18907 ⟨1551408, by decide⟩ :=
  accepted_of_selected 9 18907 ⟨1551408, by decide⟩ ⟨9, 2, 0, 1551408, 18907, 517, 4194304⟩
    (by decide) selected_cut_52780

theorem unmarked_context_8_4726_1551409 : frontier 13 ⟨1551409, by decide⟩
    (prefixCache 8 4726) (prefixPartial 8 4726) = false := by
  decide +kernel

theorem node_context_8_4726_1551409 : EJMOriginalGlobalDAGData.nodes 13 ⟨1551409, by decide⟩ =
    .split (coordinate 8) (![⟨1551241, by decide⟩,⟨1551309, by decide⟩,⟨1551374, by decide⟩,⟨1551408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4726_1551409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4726 ⟨1551409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4726
    ⟨1551409, by decide⟩ (by decide) (![⟨1551241, by decide⟩,⟨1551309, by decide⟩,⟨1551374, by decide⟩,⟨1551408, by decide⟩]) unmarked_context_8_4726_1551409 node_context_8_4726_1551409
  intro a
  fin_cases a
  · exact context_9_18904_1551241
  · exact context_9_18905_1551309
  · exact context_9_18906_1551374
  · exact context_9_18907_1551408

theorem selected_cut_52781 : selected 12 ⟨1551536, by decide⟩
    (prefixPartial 9 18908) = some ⟨9, 2, 0, 1551536, 18908, 2605, 4194304⟩ := by
  decide +kernel

theorem context_9_18908_1551536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18908 ⟨1551536, by decide⟩ :=
  accepted_of_selected 9 18908 ⟨1551536, by decide⟩ ⟨9, 2, 0, 1551536, 18908, 2605, 4194304⟩
    (by decide) selected_cut_52781

theorem selected_cut_52782 : selected 12 ⟨1551606, by decide⟩
    (prefixPartial 9 18909) = some ⟨9, 2, 0, 1551606, 18909, 1441, 4194304⟩ := by
  decide +kernel

theorem context_9_18909_1551606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18909 ⟨1551606, by decide⟩ :=
  accepted_of_selected 9 18909 ⟨1551606, by decide⟩ ⟨9, 2, 0, 1551606, 18909, 1441, 4194304⟩
    (by decide) selected_cut_52782

theorem selected_cut_52783 : selected 12 ⟨1551674, by decide⟩
    (prefixPartial 9 18910) = some ⟨9, 2, 0, 1551674, 18910, 1521, 4194304⟩ := by
  decide +kernel

theorem context_9_18910_1551674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18910 ⟨1551674, by decide⟩ :=
  accepted_of_selected 9 18910 ⟨1551674, by decide⟩ ⟨9, 2, 0, 1551674, 18910, 1521, 4194304⟩
    (by decide) selected_cut_52783

theorem selected_cut_52784 : selected 12 ⟨1551712, by decide⟩
    (prefixPartial 9 18911) = some ⟨9, 2, 0, 1551712, 18911, 721, 4194304⟩ := by
  decide +kernel

theorem context_9_18911_1551712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18911 ⟨1551712, by decide⟩ :=
  accepted_of_selected 9 18911 ⟨1551712, by decide⟩ ⟨9, 2, 0, 1551712, 18911, 721, 4194304⟩
    (by decide) selected_cut_52784

theorem unmarked_context_8_4727_1551713 : frontier 13 ⟨1551713, by decide⟩
    (prefixCache 8 4727) (prefixPartial 8 4727) = false := by
  decide +kernel

theorem node_context_8_4727_1551713 : EJMOriginalGlobalDAGData.nodes 13 ⟨1551713, by decide⟩ =
    .split (coordinate 8) (![⟨1551536, by decide⟩,⟨1551606, by decide⟩,⟨1551674, by decide⟩,⟨1551712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4727_1551713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4727 ⟨1551713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4727
    ⟨1551713, by decide⟩ (by decide) (![⟨1551536, by decide⟩,⟨1551606, by decide⟩,⟨1551674, by decide⟩,⟨1551712, by decide⟩]) unmarked_context_8_4727_1551713 node_context_8_4727_1551713
  intro a
  fin_cases a
  · exact context_9_18908_1551536
  · exact context_9_18909_1551606
  · exact context_9_18910_1551674
  · exact context_9_18911_1551712

theorem unmarked_context_7_1181_1551714 : frontier 14 ⟨1551714, by decide⟩
    (prefixCache 7 1181) (prefixPartial 7 1181) = false := by
  decide +kernel

theorem node_context_7_1181_1551714 : EJMOriginalGlobalDAGData.nodes 14 ⟨1551714, by decide⟩ =
    .split (coordinate 7) (![⟨1550865, by decide⟩,⟨1551075, by decide⟩,⟨1551409, by decide⟩,⟨1551713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1181_1551714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1181 ⟨1551714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1181
    ⟨1551714, by decide⟩ (by decide) (![⟨1550865, by decide⟩,⟨1551075, by decide⟩,⟨1551409, by decide⟩,⟨1551713, by decide⟩]) unmarked_context_7_1181_1551714 node_context_7_1181_1551714
  intro a
  fin_cases a
  · exact context_8_4724_1550865
  · exact context_8_4725_1551075
  · exact context_8_4726_1551409
  · exact context_8_4727_1551713

theorem selected_cut_52785 : selected 12 ⟨1551844, by decide⟩
    (prefixPartial 9 18912) = some ⟨9, 2, 0, 1551844, 18912, 2393, 4194304⟩ := by
  decide +kernel

theorem context_9_18912_1551844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18912 ⟨1551844, by decide⟩ :=
  accepted_of_selected 9 18912 ⟨1551844, by decide⟩ ⟨9, 2, 0, 1551844, 18912, 2393, 4194304⟩
    (by decide) selected_cut_52785

theorem selected_cut_52786 : selected 12 ⟨1551898, by decide⟩
    (prefixPartial 9 18913) = some ⟨9, 2, 0, 1551898, 18913, 1089, 4194304⟩ := by
  decide +kernel

theorem context_9_18913_1551898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18913 ⟨1551898, by decide⟩ :=
  accepted_of_selected 9 18913 ⟨1551898, by decide⟩ ⟨9, 2, 0, 1551898, 18913, 1089, 4194304⟩
    (by decide) selected_cut_52786

theorem selected_cut_52787 : selected 12 ⟨1552003, by decide⟩
    (prefixPartial 9 18914) = some ⟨9, 2, 0, 1552003, 18914, 1865, 4194304⟩ := by
  decide +kernel

theorem context_9_18914_1552003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18914 ⟨1552003, by decide⟩ :=
  accepted_of_selected 9 18914 ⟨1552003, by decide⟩ ⟨9, 2, 0, 1552003, 18914, 1865, 4194304⟩
    (by decide) selected_cut_52787

theorem selected_cut_52788 : selected 12 ⟨1552031, by decide⟩
    (prefixPartial 9 18915) = some ⟨9, 2, 0, 1552031, 18915, 397, 4194304⟩ := by
  decide +kernel

theorem context_9_18915_1552031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18915 ⟨1552031, by decide⟩ :=
  accepted_of_selected 9 18915 ⟨1552031, by decide⟩ ⟨9, 2, 0, 1552031, 18915, 397, 4194304⟩
    (by decide) selected_cut_52788

theorem unmarked_context_8_4728_1552032 : frontier 13 ⟨1552032, by decide⟩
    (prefixCache 8 4728) (prefixPartial 8 4728) = false := by
  decide +kernel

theorem node_context_8_4728_1552032 : EJMOriginalGlobalDAGData.nodes 13 ⟨1552032, by decide⟩ =
    .split (coordinate 8) (![⟨1551844, by decide⟩,⟨1551898, by decide⟩,⟨1552003, by decide⟩,⟨1552031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4728_1552032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4728 ⟨1552032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4728
    ⟨1552032, by decide⟩ (by decide) (![⟨1551844, by decide⟩,⟨1551898, by decide⟩,⟨1552003, by decide⟩,⟨1552031, by decide⟩]) unmarked_context_8_4728_1552032 node_context_8_4728_1552032
  intro a
  fin_cases a
  · exact context_9_18912_1551844
  · exact context_9_18913_1551898
  · exact context_9_18914_1552003
  · exact context_9_18915_1552031

theorem selected_cut_52789 : selected 12 ⟨1552146, by decide⟩
    (prefixPartial 9 18916) = some ⟨9, 2, 0, 1552146, 18916, 2169, 4194304⟩ := by
  decide +kernel

theorem context_9_18916_1552146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18916 ⟨1552146, by decide⟩ :=
  accepted_of_selected 9 18916 ⟨1552146, by decide⟩ ⟨9, 2, 0, 1552146, 18916, 2169, 4194304⟩
    (by decide) selected_cut_52789

theorem selected_cut_52790 : selected 12 ⟨1552215, by decide⟩
    (prefixPartial 9 18917) = some ⟨9, 2, 0, 1552215, 18917, 1405, 4194304⟩ := by
  decide +kernel

theorem context_9_18917_1552215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18917 ⟨1552215, by decide⟩ :=
  accepted_of_selected 9 18917 ⟨1552215, by decide⟩ ⟨9, 2, 0, 1552215, 18917, 1405, 4194304⟩
    (by decide) selected_cut_52790

theorem selected_cut_52791 : selected 12 ⟨1552264, by decide⟩
    (prefixPartial 9 18918) = some ⟨9, 2, 0, 1552264, 18918, 1125, 4194304⟩ := by
  decide +kernel

theorem context_9_18918_1552264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18918 ⟨1552264, by decide⟩ :=
  accepted_of_selected 9 18918 ⟨1552264, by decide⟩ ⟨9, 2, 0, 1552264, 18918, 1125, 4194304⟩
    (by decide) selected_cut_52791

theorem selected_cut_52792 : selected 12 ⟨1552288, by decide⟩
    (prefixPartial 9 18919) = some ⟨9, 2, 0, 1552288, 18919, 297, 4194304⟩ := by
  decide +kernel

theorem context_9_18919_1552288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18919 ⟨1552288, by decide⟩ :=
  accepted_of_selected 9 18919 ⟨1552288, by decide⟩ ⟨9, 2, 0, 1552288, 18919, 297, 4194304⟩
    (by decide) selected_cut_52792

theorem unmarked_context_8_4729_1552289 : frontier 13 ⟨1552289, by decide⟩
    (prefixCache 8 4729) (prefixPartial 8 4729) = false := by
  decide +kernel

theorem node_context_8_4729_1552289 : EJMOriginalGlobalDAGData.nodes 13 ⟨1552289, by decide⟩ =
    .split (coordinate 8) (![⟨1552146, by decide⟩,⟨1552215, by decide⟩,⟨1552264, by decide⟩,⟨1552288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4729_1552289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4729 ⟨1552289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4729
    ⟨1552289, by decide⟩ (by decide) (![⟨1552146, by decide⟩,⟨1552215, by decide⟩,⟨1552264, by decide⟩,⟨1552288, by decide⟩]) unmarked_context_8_4729_1552289 node_context_8_4729_1552289
  intro a
  fin_cases a
  · exact context_9_18916_1552146
  · exact context_9_18917_1552215
  · exact context_9_18918_1552264
  · exact context_9_18919_1552288

theorem selected_cut_52793 : selected 12 ⟨1552398, by decide⟩
    (prefixPartial 9 18920) = some ⟨9, 2, 0, 1552398, 18920, 1569, 4194304⟩ := by
  decide +kernel

theorem context_9_18920_1552398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18920 ⟨1552398, by decide⟩ :=
  accepted_of_selected 9 18920 ⟨1552398, by decide⟩ ⟨9, 2, 0, 1552398, 18920, 1569, 4194304⟩
    (by decide) selected_cut_52793

theorem selected_cut_52794 : selected 12 ⟨1552451, by decide⟩
    (prefixPartial 9 18921) = some ⟨9, 2, 0, 1552451, 18921, 881, 4194304⟩ := by
  decide +kernel

theorem context_9_18921_1552451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18921 ⟨1552451, by decide⟩ :=
  accepted_of_selected 9 18921 ⟨1552451, by decide⟩ ⟨9, 2, 0, 1552451, 18921, 881, 4194304⟩
    (by decide) selected_cut_52794

theorem selected_cut_52795 : selected 12 ⟨1552509, by decide⟩
    (prefixPartial 9 18922) = some ⟨9, 2, 0, 1552509, 18922, 1305, 4194304⟩ := by
  decide +kernel

theorem context_9_18922_1552509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18922 ⟨1552509, by decide⟩ :=
  accepted_of_selected 9 18922 ⟨1552509, by decide⟩ ⟨9, 2, 0, 1552509, 18922, 1305, 4194304⟩
    (by decide) selected_cut_52795

theorem selected_cut_52796 : selected 12 ⟨1552535, by decide⟩
    (prefixPartial 9 18923) = some ⟨9, 2, 0, 1552535, 18923, 381, 4194304⟩ := by
  decide +kernel

theorem context_9_18923_1552535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18923 ⟨1552535, by decide⟩ :=
  accepted_of_selected 9 18923 ⟨1552535, by decide⟩ ⟨9, 2, 0, 1552535, 18923, 381, 4194304⟩
    (by decide) selected_cut_52796

theorem unmarked_context_8_4730_1552536 : frontier 13 ⟨1552536, by decide⟩
    (prefixCache 8 4730) (prefixPartial 8 4730) = false := by
  decide +kernel

theorem node_context_8_4730_1552536 : EJMOriginalGlobalDAGData.nodes 13 ⟨1552536, by decide⟩ =
    .split (coordinate 8) (![⟨1552398, by decide⟩,⟨1552451, by decide⟩,⟨1552509, by decide⟩,⟨1552535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4730_1552536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4730 ⟨1552536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4730
    ⟨1552536, by decide⟩ (by decide) (![⟨1552398, by decide⟩,⟨1552451, by decide⟩,⟨1552509, by decide⟩,⟨1552535, by decide⟩]) unmarked_context_8_4730_1552536 node_context_8_4730_1552536
  intro a
  fin_cases a
  · exact context_9_18920_1552398
  · exact context_9_18921_1552451
  · exact context_9_18922_1552509
  · exact context_9_18923_1552535

theorem selected_cut_52797 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 75696) = some ⟨10, 1, 0, 1468246, 75696, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_75696_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75696 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 75696 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 75696, 1, 1048576⟩
    (by decide) selected_cut_52797

theorem selected_cut_52798 : selected 11 ⟨1552665, by decide⟩
    (prefixPartial 10 75697) = some ⟨10, 2, 0, 1552665, 75697, 1489, 1048576⟩ := by
  decide +kernel

theorem context_10_75697_1552665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75697 ⟨1552665, by decide⟩ :=
  accepted_of_selected 10 75697 ⟨1552665, by decide⟩ ⟨10, 2, 0, 1552665, 75697, 1489, 1048576⟩
    (by decide) selected_cut_52798

theorem selected_cut_52799 : selected 11 ⟨1552741, by decide⟩
    (prefixPartial 10 75698) = some ⟨10, 2, 0, 1552741, 75698, 1177, 1048576⟩ := by
  decide +kernel

theorem context_10_75698_1552741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75698 ⟨1552741, by decide⟩ :=
  accepted_of_selected 10 75698 ⟨1552741, by decide⟩ ⟨10, 2, 0, 1552741, 75698, 1177, 1048576⟩
    (by decide) selected_cut_52799

theorem selected_cut_52800 : selected 11 ⟨1552816, by decide⟩
    (prefixPartial 10 75699) = some ⟨10, 2, 0, 1552816, 75699, 1741, 1048576⟩ := by
  decide +kernel

theorem context_10_75699_1552816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 75699 ⟨1552816, by decide⟩ :=
  accepted_of_selected 10 75699 ⟨1552816, by decide⟩ ⟨10, 2, 0, 1552816, 75699, 1741, 1048576⟩
    (by decide) selected_cut_52800

theorem unmarked_context_9_18924_1552817 : frontier 12 ⟨1552817, by decide⟩
    (prefixCache 9 18924) (prefixPartial 9 18924) = false := by
  decide +kernel

theorem node_context_9_18924_1552817 : EJMOriginalGlobalDAGData.nodes 12 ⟨1552817, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1552665, by decide⟩,⟨1552741, by decide⟩,⟨1552816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18924_1552817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18924 ⟨1552817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18924
    ⟨1552817, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1552665, by decide⟩,⟨1552741, by decide⟩,⟨1552816, by decide⟩]) unmarked_context_9_18924_1552817 node_context_9_18924_1552817
  intro a
  fin_cases a
  · exact context_10_75696_1468246
  · exact context_10_75697_1552665
  · exact context_10_75698_1552741
  · exact context_10_75699_1552816

theorem selected_cut_52801 : selected 12 ⟨1552933, by decide⟩
    (prefixPartial 9 18925) = some ⟨9, 2, 0, 1552933, 18925, 1277, 4194304⟩ := by
  decide +kernel

theorem context_9_18925_1552933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18925 ⟨1552933, by decide⟩ :=
  accepted_of_selected 9 18925 ⟨1552933, by decide⟩ ⟨9, 2, 0, 1552933, 18925, 1277, 4194304⟩
    (by decide) selected_cut_52801

theorem selected_cut_52802 : selected 12 ⟨1553038, by decide⟩
    (prefixPartial 9 18926) = some ⟨9, 2, 0, 1553038, 18926, 929, 4194304⟩ := by
  decide +kernel

theorem context_9_18926_1553038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18926 ⟨1553038, by decide⟩ :=
  accepted_of_selected 9 18926 ⟨1553038, by decide⟩ ⟨9, 2, 0, 1553038, 18926, 929, 4194304⟩
    (by decide) selected_cut_52802

theorem selected_cut_52803 : selected 12 ⟨1553051, by decide⟩
    (prefixPartial 9 18927) = some ⟨9, 2, 0, 1553051, 18927, 77, 4194304⟩ := by
  decide +kernel

theorem context_9_18927_1553051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18927 ⟨1553051, by decide⟩ :=
  accepted_of_selected 9 18927 ⟨1553051, by decide⟩ ⟨9, 2, 0, 1553051, 18927, 77, 4194304⟩
    (by decide) selected_cut_52803

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
