/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover225
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21700 : selected 9 ⟨555073, by decide⟩
    (prefixPartial 12 75199) = some ⟨12, 2, 0, 555073, 75199, 957, 65536⟩ := by
  decide +kernel

theorem context_12_75199_555073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75199 ⟨555073, by decide⟩ :=
  accepted_of_selected 12 75199 ⟨555073, by decide⟩ ⟨12, 2, 0, 555073, 75199, 957, 65536⟩
    (by decide) selected_cut_21700

theorem unmarked_context_11_18799_555074 : frontier 10 ⟨555074, by decide⟩
    (prefixCache 11 18799) (prefixPartial 11 18799) = false := by
  decide +kernel

theorem node_context_11_18799_555074 : EJMOriginalGlobalDAGData.nodes 10 ⟨555074, by decide⟩ =
    .split (coordinate 11) (![⟨555038, by decide⟩,⟨555047, by decide⟩,⟨555062, by decide⟩,⟨555073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18799_555074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18799 ⟨555074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18799
    ⟨555074, by decide⟩ (by decide) (![⟨555038, by decide⟩,⟨555047, by decide⟩,⟨555062, by decide⟩,⟨555073, by decide⟩]) unmarked_context_11_18799_555074 node_context_11_18799_555074
  intro a
  fin_cases a
  · exact context_12_75196_555038
  · exact context_12_75197_555047
  · exact context_12_75198_555062
  · exact context_12_75199_555073

theorem unmarked_context_10_4699_555075 : frontier 11 ⟨555075, by decide⟩
    (prefixCache 10 4699) (prefixPartial 10 4699) = false := by
  decide +kernel

theorem node_context_10_4699_555075 : EJMOriginalGlobalDAGData.nodes 11 ⟨555075, by decide⟩ =
    .split (coordinate 10) (![⟨554883, by decide⟩,⟨554947, by decide⟩,⟨555028, by decide⟩,⟨555074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4699_555075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4699 ⟨555075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4699
    ⟨555075, by decide⟩ (by decide) (![⟨554883, by decide⟩,⟨554947, by decide⟩,⟨555028, by decide⟩,⟨555074, by decide⟩]) unmarked_context_10_4699_555075 node_context_10_4699_555075
  intro a
  fin_cases a
  · exact context_11_18796_554883
  · exact context_11_18797_554947
  · exact context_11_18798_555028
  · exact context_11_18799_555074

theorem unmarked_context_9_1174_555076 : frontier 12 ⟨555076, by decide⟩
    (prefixCache 9 1174) (prefixPartial 9 1174) = false := by
  decide +kernel

theorem node_context_9_1174_555076 : EJMOriginalGlobalDAGData.nodes 12 ⟨555076, by decide⟩ =
    .split (coordinate 9) (![⟨554133, by decide⟩,⟨554519, by decide⟩,⟨554821, by decide⟩,⟨555075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1174_555076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1174 ⟨555076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1174
    ⟨555076, by decide⟩ (by decide) (![⟨554133, by decide⟩,⟨554519, by decide⟩,⟨554821, by decide⟩,⟨555075, by decide⟩]) unmarked_context_9_1174_555076 node_context_9_1174_555076
  intro a
  fin_cases a
  · exact context_10_4696_554133
  · exact context_10_4697_554519
  · exact context_10_4698_554821
  · exact context_10_4699_555075

theorem selected_cut_21701 : selected 10 ⟨555109, by decide⟩
    (prefixPartial 11 18800) = some ⟨11, 2, 0, 555109, 18800, 3509, 262144⟩ := by
  decide +kernel

theorem context_11_18800_555109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18800 ⟨555109, by decide⟩ :=
  accepted_of_selected 11 18800 ⟨555109, by decide⟩ ⟨11, 2, 0, 555109, 18800, 3509, 262144⟩
    (by decide) selected_cut_21701

theorem selected_cut_21702 : selected 10 ⟨555159, by decide⟩
    (prefixPartial 11 18801) = some ⟨11, 2, 0, 555159, 18801, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_18801_555159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18801 ⟨555159, by decide⟩ :=
  accepted_of_selected 11 18801 ⟨555159, by decide⟩ ⟨11, 2, 0, 555159, 18801, 2413, 262144⟩
    (by decide) selected_cut_21702

theorem selected_cut_21703 : selected 10 ⟨555197, by decide⟩
    (prefixPartial 11 18802) = some ⟨11, 2, 0, 555197, 18802, 3149, 262144⟩ := by
  decide +kernel

theorem context_11_18802_555197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18802 ⟨555197, by decide⟩ :=
  accepted_of_selected 11 18802 ⟨555197, by decide⟩ ⟨11, 2, 0, 555197, 18802, 3149, 262144⟩
    (by decide) selected_cut_21703

theorem selected_cut_21704 : selected 10 ⟨555243, by decide⟩
    (prefixPartial 11 18803) = some ⟨11, 2, 0, 555243, 18803, 3073, 262144⟩ := by
  decide +kernel

theorem context_11_18803_555243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18803 ⟨555243, by decide⟩ :=
  accepted_of_selected 11 18803 ⟨555243, by decide⟩ ⟨11, 2, 0, 555243, 18803, 3073, 262144⟩
    (by decide) selected_cut_21704

theorem unmarked_context_10_4700_555244 : frontier 11 ⟨555244, by decide⟩
    (prefixCache 10 4700) (prefixPartial 10 4700) = false := by
  decide +kernel

theorem node_context_10_4700_555244 : EJMOriginalGlobalDAGData.nodes 11 ⟨555244, by decide⟩ =
    .split (coordinate 10) (![⟨555109, by decide⟩,⟨555159, by decide⟩,⟨555197, by decide⟩,⟨555243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4700_555244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4700 ⟨555244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4700
    ⟨555244, by decide⟩ (by decide) (![⟨555109, by decide⟩,⟨555159, by decide⟩,⟨555197, by decide⟩,⟨555243, by decide⟩]) unmarked_context_10_4700_555244 node_context_10_4700_555244
  intro a
  fin_cases a
  · exact context_11_18800_555109
  · exact context_11_18801_555159
  · exact context_11_18802_555197
  · exact context_11_18803_555243

theorem selected_cut_21705 : selected 10 ⟨555266, by decide⟩
    (prefixPartial 11 18804) = some ⟨11, 2, 0, 555266, 18804, 2493, 262144⟩ := by
  decide +kernel

theorem context_11_18804_555266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18804 ⟨555266, by decide⟩ :=
  accepted_of_selected 11 18804 ⟨555266, by decide⟩ ⟨11, 2, 0, 555266, 18804, 2493, 262144⟩
    (by decide) selected_cut_21705

theorem selected_cut_21706 : selected 10 ⟨555278, by decide⟩
    (prefixPartial 11 18805) = some ⟨11, 2, 0, 555278, 18805, 845, 262144⟩ := by
  decide +kernel

theorem context_11_18805_555278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18805 ⟨555278, by decide⟩ :=
  accepted_of_selected 11 18805 ⟨555278, by decide⟩ ⟨11, 2, 0, 555278, 18805, 845, 262144⟩
    (by decide) selected_cut_21706

theorem selected_cut_21707 : selected 10 ⟨555302, by decide⟩
    (prefixPartial 11 18806) = some ⟨11, 2, 0, 555302, 18806, 2213, 262144⟩ := by
  decide +kernel

theorem context_11_18806_555302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18806 ⟨555302, by decide⟩ :=
  accepted_of_selected 11 18806 ⟨555302, by decide⟩ ⟨11, 2, 0, 555302, 18806, 2213, 262144⟩
    (by decide) selected_cut_21707

theorem selected_cut_21708 : selected 10 ⟨555324, by decide⟩
    (prefixPartial 11 18807) = some ⟨11, 2, 0, 555324, 18807, 2053, 262144⟩ := by
  decide +kernel

theorem context_11_18807_555324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18807 ⟨555324, by decide⟩ :=
  accepted_of_selected 11 18807 ⟨555324, by decide⟩ ⟨11, 2, 0, 555324, 18807, 2053, 262144⟩
    (by decide) selected_cut_21708

theorem unmarked_context_10_4701_555325 : frontier 11 ⟨555325, by decide⟩
    (prefixCache 10 4701) (prefixPartial 10 4701) = false := by
  decide +kernel

theorem node_context_10_4701_555325 : EJMOriginalGlobalDAGData.nodes 11 ⟨555325, by decide⟩ =
    .split (coordinate 10) (![⟨555266, by decide⟩,⟨555278, by decide⟩,⟨555302, by decide⟩,⟨555324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4701_555325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4701 ⟨555325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4701
    ⟨555325, by decide⟩ (by decide) (![⟨555266, by decide⟩,⟨555278, by decide⟩,⟨555302, by decide⟩,⟨555324, by decide⟩]) unmarked_context_10_4701_555325 node_context_10_4701_555325
  intro a
  fin_cases a
  · exact context_11_18804_555266
  · exact context_11_18805_555278
  · exact context_11_18806_555302
  · exact context_11_18807_555324

theorem selected_cut_21709 : selected 10 ⟨555341, by decide⟩
    (prefixPartial 11 18808) = some ⟨11, 2, 0, 555341, 18808, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_18808_555341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18808 ⟨555341, by decide⟩ :=
  accepted_of_selected 11 18808 ⟨555341, by decide⟩ ⟨11, 2, 0, 555341, 18808, 1465, 262144⟩
    (by decide) selected_cut_21709

theorem selected_cut_21710 : selected 10 ⟨555359, by decide⟩
    (prefixPartial 11 18809) = some ⟨11, 2, 0, 555359, 18809, 1453, 262144⟩ := by
  decide +kernel

theorem context_11_18809_555359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18809 ⟨555359, by decide⟩ :=
  accepted_of_selected 11 18809 ⟨555359, by decide⟩ ⟨11, 2, 0, 555359, 18809, 1453, 262144⟩
    (by decide) selected_cut_21710

theorem selected_cut_21711 : selected 10 ⟨555375, by decide⟩
    (prefixPartial 11 18810) = some ⟨11, 2, 0, 555375, 18810, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_18810_555375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18810 ⟨555375, by decide⟩ :=
  accepted_of_selected 11 18810 ⟨555375, by decide⟩ ⟨11, 2, 0, 555375, 18810, 1093, 262144⟩
    (by decide) selected_cut_21711

theorem selected_cut_21712 : selected 10 ⟨555389, by decide⟩
    (prefixPartial 11 18811) = some ⟨11, 2, 0, 555389, 18811, 949, 262144⟩ := by
  decide +kernel

theorem context_11_18811_555389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18811 ⟨555389, by decide⟩ :=
  accepted_of_selected 11 18811 ⟨555389, by decide⟩ ⟨11, 2, 0, 555389, 18811, 949, 262144⟩
    (by decide) selected_cut_21712

theorem unmarked_context_10_4702_555390 : frontier 11 ⟨555390, by decide⟩
    (prefixCache 10 4702) (prefixPartial 10 4702) = false := by
  decide +kernel

theorem node_context_10_4702_555390 : EJMOriginalGlobalDAGData.nodes 11 ⟨555390, by decide⟩ =
    .split (coordinate 10) (![⟨555341, by decide⟩,⟨555359, by decide⟩,⟨555375, by decide⟩,⟨555389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4702_555390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4702 ⟨555390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4702
    ⟨555390, by decide⟩ (by decide) (![⟨555341, by decide⟩,⟨555359, by decide⟩,⟨555375, by decide⟩,⟨555389, by decide⟩]) unmarked_context_10_4702_555390 node_context_10_4702_555390
  intro a
  fin_cases a
  · exact context_11_18808_555341
  · exact context_11_18809_555359
  · exact context_11_18810_555375
  · exact context_11_18811_555389

theorem selected_cut_21713 : selected 11 ⟨555421, by decide⟩
    (prefixPartial 10 4703) = some ⟨10, 2, 0, 555421, 4703, 1613, 1048576⟩ := by
  decide +kernel

theorem context_10_4703_555421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4703 ⟨555421, by decide⟩ :=
  accepted_of_selected 10 4703 ⟨555421, by decide⟩ ⟨10, 2, 0, 555421, 4703, 1613, 1048576⟩
    (by decide) selected_cut_21713

theorem unmarked_context_9_1175_555422 : frontier 12 ⟨555422, by decide⟩
    (prefixCache 9 1175) (prefixPartial 9 1175) = false := by
  decide +kernel

theorem node_context_9_1175_555422 : EJMOriginalGlobalDAGData.nodes 12 ⟨555422, by decide⟩ =
    .split (coordinate 9) (![⟨555244, by decide⟩,⟨555325, by decide⟩,⟨555390, by decide⟩,⟨555421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1175_555422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1175 ⟨555422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1175
    ⟨555422, by decide⟩ (by decide) (![⟨555244, by decide⟩,⟨555325, by decide⟩,⟨555390, by decide⟩,⟨555421, by decide⟩]) unmarked_context_9_1175_555422 node_context_9_1175_555422
  intro a
  fin_cases a
  · exact context_10_4700_555244
  · exact context_10_4701_555325
  · exact context_10_4702_555390
  · exact context_10_4703_555421

theorem unmarked_context_8_293_555423 : frontier 13 ⟨555423, by decide⟩
    (prefixCache 8 293) (prefixPartial 8 293) = false := by
  decide +kernel

theorem node_context_8_293_555423 : EJMOriginalGlobalDAGData.nodes 13 ⟨555423, by decide⟩ =
    .split (coordinate 8) (![⟨550733, by decide⟩,⟨553564, by decide⟩,⟨555076, by decide⟩,⟨555422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_293_555423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 293 ⟨555423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 293
    ⟨555423, by decide⟩ (by decide) (![⟨550733, by decide⟩,⟨553564, by decide⟩,⟨555076, by decide⟩,⟨555422, by decide⟩]) unmarked_context_8_293_555423 node_context_8_293_555423
  intro a
  fin_cases a
  · exact context_9_1172_550733
  · exact context_9_1173_553564
  · exact context_9_1174_555076
  · exact context_9_1175_555422

theorem selected_cut_21714 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18816) = some ⟨11, 1, 0, 434745, 18816, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18816_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18816 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18816 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18816, 1, 262144⟩
    (by decide) selected_cut_21714

theorem selected_cut_21715 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75268) = some ⟨12, 1, 0, 448748, 75268, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75268_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75268 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75268 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75268, 1, 65536⟩
    (by decide) selected_cut_21715

theorem selected_cut_21716 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 75269) = some ⟨12, 1, 0, 34034, 75269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75269_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75269 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 75269 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 75269, 1, 65536⟩
    (by decide) selected_cut_21716

theorem selected_cut_21717 : selected 8 ⟨555479, by decide⟩
    (prefixPartial 13 301080) = some ⟨13, 2, 0, 555479, 301080, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_301080_555479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301080 ⟨555479, by decide⟩ :=
  accepted_of_selected 13 301080 ⟨555479, by decide⟩ ⟨13, 2, 0, 555479, 301080, 2637, 16384⟩
    (by decide) selected_cut_21717

theorem selected_cut_21718 : selected 8 ⟨555509, by decide⟩
    (prefixPartial 13 301081) = some ⟨13, 2, 0, 555509, 301081, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_301081_555509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301081 ⟨555509, by decide⟩ :=
  accepted_of_selected 13 301081 ⟨555509, by decide⟩ ⟨13, 2, 0, 555509, 301081, 2589, 16384⟩
    (by decide) selected_cut_21718

theorem selected_cut_21719 : selected 8 ⟨555526, by decide⟩
    (prefixPartial 13 301082) = some ⟨13, 2, 0, 555526, 301082, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_301082_555526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301082 ⟨555526, by decide⟩ :=
  accepted_of_selected 13 301082 ⟨555526, by decide⟩ ⟨13, 2, 0, 555526, 301082, 1629, 16384⟩
    (by decide) selected_cut_21719

theorem selected_cut_21720 : selected 8 ⟨555533, by decide⟩
    (prefixPartial 13 301083) = some ⟨13, 2, 0, 555533, 301083, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_301083_555533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301083 ⟨555533, by decide⟩ :=
  accepted_of_selected 13 301083 ⟨555533, by decide⟩ ⟨13, 2, 0, 555533, 301083, 1113, 16384⟩
    (by decide) selected_cut_21720

theorem unmarked_context_12_75270_555534 : frontier 9 ⟨555534, by decide⟩
    (prefixCache 12 75270) (prefixPartial 12 75270) = false := by
  decide +kernel

theorem node_context_12_75270_555534 : EJMOriginalGlobalDAGData.nodes 9 ⟨555534, by decide⟩ =
    .split (coordinate 12) (![⟨555479, by decide⟩,⟨555509, by decide⟩,⟨555526, by decide⟩,⟨555533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75270_555534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75270 ⟨555534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75270
    ⟨555534, by decide⟩ (by decide) (![⟨555479, by decide⟩,⟨555509, by decide⟩,⟨555526, by decide⟩,⟨555533, by decide⟩]) unmarked_context_12_75270_555534 node_context_12_75270_555534
  intro a
  fin_cases a
  · exact context_13_301080_555479
  · exact context_13_301081_555509
  · exact context_13_301082_555526
  · exact context_13_301083_555533

theorem selected_cut_21721 : selected 8 ⟨555605, by decide⟩
    (prefixPartial 13 301084) = some ⟨13, 2, 0, 555605, 301084, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_301084_555605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301084 ⟨555605, by decide⟩ :=
  accepted_of_selected 13 301084 ⟨555605, by decide⟩ ⟨13, 2, 0, 555605, 301084, 3421, 16384⟩
    (by decide) selected_cut_21721

theorem selected_cut_21722 : selected 8 ⟨555645, by decide⟩
    (prefixPartial 13 301085) = some ⟨13, 2, 0, 555645, 301085, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_301085_555645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301085 ⟨555645, by decide⟩ :=
  accepted_of_selected 13 301085 ⟨555645, by decide⟩ ⟨13, 2, 0, 555645, 301085, 3097, 16384⟩
    (by decide) selected_cut_21722

theorem selected_cut_21723 : selected 8 ⟨555669, by decide⟩
    (prefixPartial 13 301086) = some ⟨13, 2, 0, 555669, 301086, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_301086_555669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301086 ⟨555669, by decide⟩ :=
  accepted_of_selected 13 301086 ⟨555669, by decide⟩ ⟨13, 2, 0, 555669, 301086, 1945, 16384⟩
    (by decide) selected_cut_21723

theorem selected_cut_21724 : selected 8 ⟨555679, by decide⟩
    (prefixPartial 13 301087) = some ⟨13, 2, 0, 555679, 301087, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_301087_555679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301087 ⟨555679, by decide⟩ :=
  accepted_of_selected 13 301087 ⟨555679, by decide⟩ ⟨13, 2, 0, 555679, 301087, 1253, 16384⟩
    (by decide) selected_cut_21724

theorem unmarked_context_12_75271_555680 : frontier 9 ⟨555680, by decide⟩
    (prefixCache 12 75271) (prefixPartial 12 75271) = false := by
  decide +kernel

theorem node_context_12_75271_555680 : EJMOriginalGlobalDAGData.nodes 9 ⟨555680, by decide⟩ =
    .split (coordinate 12) (![⟨555605, by decide⟩,⟨555645, by decide⟩,⟨555669, by decide⟩,⟨555679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75271_555680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75271 ⟨555680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75271
    ⟨555680, by decide⟩ (by decide) (![⟨555605, by decide⟩,⟨555645, by decide⟩,⟨555669, by decide⟩,⟨555679, by decide⟩]) unmarked_context_12_75271_555680 node_context_12_75271_555680
  intro a
  fin_cases a
  · exact context_13_301084_555605
  · exact context_13_301085_555645
  · exact context_13_301086_555669
  · exact context_13_301087_555679

theorem unmarked_context_11_18817_555681 : frontier 10 ⟨555681, by decide⟩
    (prefixCache 11 18817) (prefixPartial 11 18817) = false := by
  decide +kernel

theorem node_context_11_18817_555681 : EJMOriginalGlobalDAGData.nodes 10 ⟨555681, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨555534, by decide⟩,⟨555680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18817_555681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18817 ⟨555681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18817
    ⟨555681, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨555534, by decide⟩,⟨555680, by decide⟩]) unmarked_context_11_18817_555681 node_context_11_18817_555681
  intro a
  fin_cases a
  · exact context_12_75268_448748
  · exact context_12_75269_34034
  · exact context_12_75270_555534
  · exact context_12_75271_555680

theorem selected_cut_21725 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75272) = some ⟨12, 1, 0, 448748, 75272, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75272_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75272 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75272 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75272, 1, 65536⟩
    (by decide) selected_cut_21725

theorem selected_cut_21726 : selected 8 ⟨555745, by decide⟩
    (prefixPartial 13 301092) = some ⟨13, 2, 0, 555745, 301092, 2997, 16384⟩ := by
  decide +kernel

theorem context_13_301092_555745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301092 ⟨555745, by decide⟩ :=
  accepted_of_selected 13 301092 ⟨555745, by decide⟩ ⟨13, 2, 0, 555745, 301092, 2997, 16384⟩
    (by decide) selected_cut_21726

theorem selected_cut_21727 : selected 8 ⟨555801, by decide⟩
    (prefixPartial 13 301093) = some ⟨13, 2, 0, 555801, 301093, 3125, 16384⟩ := by
  decide +kernel

theorem context_13_301093_555801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301093 ⟨555801, by decide⟩ :=
  accepted_of_selected 13 301093 ⟨555801, by decide⟩ ⟨13, 2, 0, 555801, 301093, 3125, 16384⟩
    (by decide) selected_cut_21727

theorem selected_cut_21728 : selected 8 ⟨555823, by decide⟩
    (prefixPartial 13 301094) = some ⟨13, 2, 0, 555823, 301094, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_301094_555823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301094 ⟨555823, by decide⟩ :=
  accepted_of_selected 13 301094 ⟨555823, by decide⟩ ⟨13, 2, 0, 555823, 301094, 1725, 16384⟩
    (by decide) selected_cut_21728

theorem selected_cut_21729 : selected 8 ⟨555848, by decide⟩
    (prefixPartial 13 301095) = some ⟨13, 2, 0, 555848, 301095, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_301095_555848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301095 ⟨555848, by decide⟩ :=
  accepted_of_selected 13 301095 ⟨555848, by decide⟩ ⟨13, 2, 0, 555848, 301095, 1193, 16384⟩
    (by decide) selected_cut_21729

theorem unmarked_context_12_75273_555849 : frontier 9 ⟨555849, by decide⟩
    (prefixCache 12 75273) (prefixPartial 12 75273) = false := by
  decide +kernel

theorem node_context_12_75273_555849 : EJMOriginalGlobalDAGData.nodes 9 ⟨555849, by decide⟩ =
    .split (coordinate 12) (![⟨555745, by decide⟩,⟨555801, by decide⟩,⟨555823, by decide⟩,⟨555848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75273_555849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75273 ⟨555849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75273
    ⟨555849, by decide⟩ (by decide) (![⟨555745, by decide⟩,⟨555801, by decide⟩,⟨555823, by decide⟩,⟨555848, by decide⟩]) unmarked_context_12_75273_555849 node_context_12_75273_555849
  intro a
  fin_cases a
  · exact context_13_301092_555745
  · exact context_13_301093_555801
  · exact context_13_301094_555823
  · exact context_13_301095_555848

theorem selected_cut_21730 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 75274) = some ⟨12, 1, 0, 524302, 75274, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75274_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75274 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 75274 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 75274, 1, 65536⟩
    (by decide) selected_cut_21730

theorem selected_cut_21731 : selected 8 ⟨555921, by decide⟩
    (prefixPartial 13 301100) = some ⟨13, 2, 0, 555921, 301100, 3517, 16384⟩ := by
  decide +kernel

theorem context_13_301100_555921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301100 ⟨555921, by decide⟩ :=
  accepted_of_selected 13 301100 ⟨555921, by decide⟩ ⟨13, 2, 0, 555921, 301100, 3517, 16384⟩
    (by decide) selected_cut_21731

theorem selected_cut_21732 : selected 8 ⟨555983, by decide⟩
    (prefixPartial 13 301101) = some ⟨13, 2, 0, 555983, 301101, 3689, 16384⟩ := by
  decide +kernel

theorem context_13_301101_555983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301101 ⟨555983, by decide⟩ :=
  accepted_of_selected 13 301101 ⟨555983, by decide⟩ ⟨13, 2, 0, 555983, 301101, 3689, 16384⟩
    (by decide) selected_cut_21732

theorem selected_cut_21733 : selected 8 ⟨556005, by decide⟩
    (prefixPartial 13 301102) = some ⟨13, 2, 0, 556005, 301102, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_301102_556005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301102 ⟨556005, by decide⟩ :=
  accepted_of_selected 13 301102 ⟨556005, by decide⟩ ⟨13, 2, 0, 556005, 301102, 1925, 16384⟩
    (by decide) selected_cut_21733

theorem selected_cut_21734 : selected 8 ⟨556023, by decide⟩
    (prefixPartial 13 301103) = some ⟨13, 2, 0, 556023, 301103, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_301103_556023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301103 ⟨556023, by decide⟩ :=
  accepted_of_selected 13 301103 ⟨556023, by decide⟩ ⟨13, 2, 0, 556023, 301103, 1181, 16384⟩
    (by decide) selected_cut_21734

theorem unmarked_context_12_75275_556024 : frontier 9 ⟨556024, by decide⟩
    (prefixCache 12 75275) (prefixPartial 12 75275) = false := by
  decide +kernel

theorem node_context_12_75275_556024 : EJMOriginalGlobalDAGData.nodes 9 ⟨556024, by decide⟩ =
    .split (coordinate 12) (![⟨555921, by decide⟩,⟨555983, by decide⟩,⟨556005, by decide⟩,⟨556023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75275_556024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75275 ⟨556024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75275
    ⟨556024, by decide⟩ (by decide) (![⟨555921, by decide⟩,⟨555983, by decide⟩,⟨556005, by decide⟩,⟨556023, by decide⟩]) unmarked_context_12_75275_556024 node_context_12_75275_556024
  intro a
  fin_cases a
  · exact context_13_301100_555921
  · exact context_13_301101_555983
  · exact context_13_301102_556005
  · exact context_13_301103_556023

theorem unmarked_context_11_18818_556025 : frontier 10 ⟨556025, by decide⟩
    (prefixCache 11 18818) (prefixPartial 11 18818) = false := by
  decide +kernel

theorem node_context_11_18818_556025 : EJMOriginalGlobalDAGData.nodes 10 ⟨556025, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨555849, by decide⟩,⟨524302, by decide⟩,⟨556024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18818_556025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18818 ⟨556025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18818
    ⟨556025, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨555849, by decide⟩,⟨524302, by decide⟩,⟨556024, by decide⟩]) unmarked_context_11_18818_556025 node_context_11_18818_556025
  intro a
  fin_cases a
  · exact context_12_75272_448748
  · exact context_12_75273_555849
  · exact context_12_75274_524302
  · exact context_12_75275_556024

theorem selected_cut_21735 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75276) = some ⟨12, 1, 0, 448748, 75276, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75276_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75276 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75276 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75276, 1, 65536⟩
    (by decide) selected_cut_21735

theorem selected_cut_21736 : selected 8 ⟨556072, by decide⟩
    (prefixPartial 13 301108) = some ⟨13, 2, 0, 556072, 301108, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_301108_556072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301108 ⟨556072, by decide⟩ :=
  accepted_of_selected 13 301108 ⟨556072, by decide⟩ ⟨13, 2, 0, 556072, 301108, 2549, 16384⟩
    (by decide) selected_cut_21736

theorem selected_cut_21737 : selected 8 ⟨556138, by decide⟩
    (prefixPartial 13 301109) = some ⟨13, 2, 0, 556138, 301109, 3433, 16384⟩ := by
  decide +kernel

theorem context_13_301109_556138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301109 ⟨556138, by decide⟩ :=
  accepted_of_selected 13 301109 ⟨556138, by decide⟩ ⟨13, 2, 0, 556138, 301109, 3433, 16384⟩
    (by decide) selected_cut_21737

theorem selected_cut_21738 : selected 8 ⟨556157, by decide⟩
    (prefixPartial 13 301110) = some ⟨13, 2, 0, 556157, 301110, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_301110_556157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301110 ⟨556157, by decide⟩ :=
  accepted_of_selected 13 301110 ⟨556157, by decide⟩ ⟨13, 2, 0, 556157, 301110, 1593, 16384⟩
    (by decide) selected_cut_21738

theorem selected_cut_21739 : selected 8 ⟨556173, by decide⟩
    (prefixPartial 13 301111) = some ⟨13, 2, 0, 556173, 301111, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_301111_556173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301111 ⟨556173, by decide⟩ :=
  accepted_of_selected 13 301111 ⟨556173, by decide⟩ ⟨13, 2, 0, 556173, 301111, 1065, 16384⟩
    (by decide) selected_cut_21739

theorem unmarked_context_12_75277_556174 : frontier 9 ⟨556174, by decide⟩
    (prefixCache 12 75277) (prefixPartial 12 75277) = false := by
  decide +kernel

theorem node_context_12_75277_556174 : EJMOriginalGlobalDAGData.nodes 9 ⟨556174, by decide⟩ =
    .split (coordinate 12) (![⟨556072, by decide⟩,⟨556138, by decide⟩,⟨556157, by decide⟩,⟨556173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75277_556174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75277 ⟨556174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75277
    ⟨556174, by decide⟩ (by decide) (![⟨556072, by decide⟩,⟨556138, by decide⟩,⟨556157, by decide⟩,⟨556173, by decide⟩]) unmarked_context_12_75277_556174 node_context_12_75277_556174
  intro a
  fin_cases a
  · exact context_13_301108_556072
  · exact context_13_301109_556138
  · exact context_13_301110_556157
  · exact context_13_301111_556173

theorem selected_cut_21740 : selected 8 ⟨556214, by decide⟩
    (prefixPartial 13 301112) = some ⟨13, 2, 0, 556214, 301112, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_301112_556214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301112 ⟨556214, by decide⟩ :=
  accepted_of_selected 13 301112 ⟨556214, by decide⟩ ⟨13, 2, 0, 556214, 301112, 2365, 16384⟩
    (by decide) selected_cut_21740

theorem selected_cut_21741 : selected 8 ⟨556258, by decide⟩
    (prefixPartial 13 301113) = some ⟨13, 2, 0, 556258, 301113, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_301113_556258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301113 ⟨556258, by decide⟩ :=
  accepted_of_selected 13 301113 ⟨556258, by decide⟩ ⟨13, 2, 0, 556258, 301113, 3077, 16384⟩
    (by decide) selected_cut_21741

theorem selected_cut_21742 : selected 8 ⟨556279, by decide⟩
    (prefixPartial 13 301114) = some ⟨13, 2, 0, 556279, 301114, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_301114_556279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301114 ⟨556279, by decide⟩ :=
  accepted_of_selected 13 301114 ⟨556279, by decide⟩ ⟨13, 2, 0, 556279, 301114, 1569, 16384⟩
    (by decide) selected_cut_21742

theorem selected_cut_21743 : selected 8 ⟨556293, by decide⟩
    (prefixPartial 13 301115) = some ⟨13, 2, 0, 556293, 301115, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_301115_556293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301115 ⟨556293, by decide⟩ :=
  accepted_of_selected 13 301115 ⟨556293, by decide⟩ ⟨13, 2, 0, 556293, 301115, 1117, 16384⟩
    (by decide) selected_cut_21743

theorem unmarked_context_12_75278_556294 : frontier 9 ⟨556294, by decide⟩
    (prefixCache 12 75278) (prefixPartial 12 75278) = false := by
  decide +kernel

theorem node_context_12_75278_556294 : EJMOriginalGlobalDAGData.nodes 9 ⟨556294, by decide⟩ =
    .split (coordinate 12) (![⟨556214, by decide⟩,⟨556258, by decide⟩,⟨556279, by decide⟩,⟨556293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75278_556294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75278 ⟨556294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75278
    ⟨556294, by decide⟩ (by decide) (![⟨556214, by decide⟩,⟨556258, by decide⟩,⟨556279, by decide⟩,⟨556293, by decide⟩]) unmarked_context_12_75278_556294 node_context_12_75278_556294
  intro a
  fin_cases a
  · exact context_13_301112_556214
  · exact context_13_301113_556258
  · exact context_13_301114_556279
  · exact context_13_301115_556293

theorem selected_cut_21744 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 75279) = some ⟨12, 1, 0, 518278, 75279, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75279_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75279 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 75279 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 75279, 1, 65536⟩
    (by decide) selected_cut_21744

theorem unmarked_context_11_18819_556295 : frontier 10 ⟨556295, by decide⟩
    (prefixCache 11 18819) (prefixPartial 11 18819) = false := by
  decide +kernel

theorem node_context_11_18819_556295 : EJMOriginalGlobalDAGData.nodes 10 ⟨556295, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨556174, by decide⟩,⟨556294, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18819_556295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18819 ⟨556295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18819
    ⟨556295, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨556174, by decide⟩,⟨556294, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_18819_556295 node_context_11_18819_556295
  intro a
  fin_cases a
  · exact context_12_75276_448748
  · exact context_12_75277_556174
  · exact context_12_75278_556294
  · exact context_12_75279_518278

theorem unmarked_context_10_4704_556296 : frontier 11 ⟨556296, by decide⟩
    (prefixCache 10 4704) (prefixPartial 10 4704) = false := by
  decide +kernel

theorem node_context_10_4704_556296 : EJMOriginalGlobalDAGData.nodes 11 ⟨556296, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨555681, by decide⟩,⟨556025, by decide⟩,⟨556295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4704_556296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4704 ⟨556296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4704
    ⟨556296, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨555681, by decide⟩,⟨556025, by decide⟩,⟨556295, by decide⟩]) unmarked_context_10_4704_556296 node_context_10_4704_556296
  intro a
  fin_cases a
  · exact context_11_18816_434745
  · exact context_11_18817_555681
  · exact context_11_18818_556025
  · exact context_11_18819_556295

theorem selected_cut_21745 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75280) = some ⟨12, 1, 0, 435160, 75280, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75280_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75280 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75280 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75280, 1, 65536⟩
    (by decide) selected_cut_21745

theorem selected_cut_21746 : selected 8 ⟨556321, by decide⟩
    (prefixPartial 13 301124) = some ⟨13, 2, 0, 556321, 301124, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_301124_556321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301124 ⟨556321, by decide⟩ :=
  accepted_of_selected 13 301124 ⟨556321, by decide⟩ ⟨13, 2, 0, 556321, 301124, 1445, 16384⟩
    (by decide) selected_cut_21746

theorem selected_cut_21747 : selected 8 ⟨556346, by decide⟩
    (prefixPartial 13 301125) = some ⟨13, 2, 0, 556346, 301125, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_301125_556346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301125 ⟨556346, by decide⟩ :=
  accepted_of_selected 13 301125 ⟨556346, by decide⟩ ⟨13, 2, 0, 556346, 301125, 2089, 16384⟩
    (by decide) selected_cut_21747

theorem selected_cut_21748 : selected 8 ⟨556363, by decide⟩
    (prefixPartial 13 301126) = some ⟨13, 2, 0, 556363, 301126, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_301126_556363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301126 ⟨556363, by decide⟩ :=
  accepted_of_selected 13 301126 ⟨556363, by decide⟩ ⟨13, 2, 0, 556363, 301126, 1181, 16384⟩
    (by decide) selected_cut_21748

theorem selected_cut_21749 : selected 8 ⟨556369, by decide⟩
    (prefixPartial 13 301127) = some ⟨13, 2, 0, 556369, 301127, 841, 16384⟩ := by
  decide +kernel

theorem context_13_301127_556369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301127 ⟨556369, by decide⟩ :=
  accepted_of_selected 13 301127 ⟨556369, by decide⟩ ⟨13, 2, 0, 556369, 301127, 841, 16384⟩
    (by decide) selected_cut_21749

theorem unmarked_context_12_75281_556370 : frontier 9 ⟨556370, by decide⟩
    (prefixCache 12 75281) (prefixPartial 12 75281) = false := by
  decide +kernel

theorem node_context_12_75281_556370 : EJMOriginalGlobalDAGData.nodes 9 ⟨556370, by decide⟩ =
    .split (coordinate 12) (![⟨556321, by decide⟩,⟨556346, by decide⟩,⟨556363, by decide⟩,⟨556369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75281_556370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75281 ⟨556370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75281
    ⟨556370, by decide⟩ (by decide) (![⟨556321, by decide⟩,⟨556346, by decide⟩,⟨556363, by decide⟩,⟨556369, by decide⟩]) unmarked_context_12_75281_556370 node_context_12_75281_556370
  intro a
  fin_cases a
  · exact context_13_301124_556321
  · exact context_13_301125_556346
  · exact context_13_301126_556363
  · exact context_13_301127_556369

theorem selected_cut_21750 : selected 8 ⟨556395, by decide⟩
    (prefixPartial 13 301128) = some ⟨13, 2, 0, 556395, 301128, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_301128_556395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301128 ⟨556395, by decide⟩ :=
  accepted_of_selected 13 301128 ⟨556395, by decide⟩ ⟨13, 2, 0, 556395, 301128, 1285, 16384⟩
    (by decide) selected_cut_21750

theorem selected_cut_21751 : selected 8 ⟨556413, by decide⟩
    (prefixPartial 13 301129) = some ⟨13, 2, 0, 556413, 301129, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_301129_556413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301129 ⟨556413, by decide⟩ :=
  accepted_of_selected 13 301129 ⟨556413, by decide⟩ ⟨13, 2, 0, 556413, 301129, 1781, 16384⟩
    (by decide) selected_cut_21751

theorem selected_cut_21752 : selected 8 ⟨556428, by decide⟩
    (prefixPartial 13 301130) = some ⟨13, 2, 0, 556428, 301130, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_301130_556428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301130 ⟨556428, by decide⟩ :=
  accepted_of_selected 13 301130 ⟨556428, by decide⟩ ⟨13, 2, 0, 556428, 301130, 1093, 16384⟩
    (by decide) selected_cut_21752

theorem selected_cut_21753 : selected 8 ⟨556436, by decide⟩
    (prefixPartial 13 301131) = some ⟨13, 2, 0, 556436, 301131, 761, 16384⟩ := by
  decide +kernel

theorem context_13_301131_556436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301131 ⟨556436, by decide⟩ :=
  accepted_of_selected 13 301131 ⟨556436, by decide⟩ ⟨13, 2, 0, 556436, 301131, 761, 16384⟩
    (by decide) selected_cut_21753

theorem unmarked_context_12_75282_556437 : frontier 9 ⟨556437, by decide⟩
    (prefixCache 12 75282) (prefixPartial 12 75282) = false := by
  decide +kernel

theorem node_context_12_75282_556437 : EJMOriginalGlobalDAGData.nodes 9 ⟨556437, by decide⟩ =
    .split (coordinate 12) (![⟨556395, by decide⟩,⟨556413, by decide⟩,⟨556428, by decide⟩,⟨556436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75282_556437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75282 ⟨556437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75282
    ⟨556437, by decide⟩ (by decide) (![⟨556395, by decide⟩,⟨556413, by decide⟩,⟨556428, by decide⟩,⟨556436, by decide⟩]) unmarked_context_12_75282_556437 node_context_12_75282_556437
  intro a
  fin_cases a
  · exact context_13_301128_556395
  · exact context_13_301129_556413
  · exact context_13_301130_556428
  · exact context_13_301131_556436

theorem selected_cut_21754 : selected 8 ⟨556470, by decide⟩
    (prefixPartial 13 301132) = some ⟨13, 2, 0, 556470, 301132, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_301132_556470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301132 ⟨556470, by decide⟩ :=
  accepted_of_selected 13 301132 ⟨556470, by decide⟩ ⟨13, 2, 0, 556470, 301132, 1785, 16384⟩
    (by decide) selected_cut_21754

theorem selected_cut_21755 : selected 8 ⟨556503, by decide⟩
    (prefixPartial 13 301133) = some ⟨13, 2, 0, 556503, 301133, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_301133_556503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301133 ⟨556503, by decide⟩ :=
  accepted_of_selected 13 301133 ⟨556503, by decide⟩ ⟨13, 2, 0, 556503, 301133, 2513, 16384⟩
    (by decide) selected_cut_21755

theorem selected_cut_21756 : selected 8 ⟨556524, by decide⟩
    (prefixPartial 13 301134) = some ⟨13, 2, 0, 556524, 301134, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_301134_556524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301134 ⟨556524, by decide⟩ :=
  accepted_of_selected 13 301134 ⟨556524, by decide⟩ ⟨13, 2, 0, 556524, 301134, 1517, 16384⟩
    (by decide) selected_cut_21756

theorem selected_cut_21757 : selected 8 ⟨556533, by decide⟩
    (prefixPartial 13 301135) = some ⟨13, 2, 0, 556533, 301135, 881, 16384⟩ := by
  decide +kernel

theorem context_13_301135_556533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301135 ⟨556533, by decide⟩ :=
  accepted_of_selected 13 301135 ⟨556533, by decide⟩ ⟨13, 2, 0, 556533, 301135, 881, 16384⟩
    (by decide) selected_cut_21757

theorem unmarked_context_12_75283_556534 : frontier 9 ⟨556534, by decide⟩
    (prefixCache 12 75283) (prefixPartial 12 75283) = false := by
  decide +kernel

theorem node_context_12_75283_556534 : EJMOriginalGlobalDAGData.nodes 9 ⟨556534, by decide⟩ =
    .split (coordinate 12) (![⟨556470, by decide⟩,⟨556503, by decide⟩,⟨556524, by decide⟩,⟨556533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75283_556534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75283 ⟨556534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75283
    ⟨556534, by decide⟩ (by decide) (![⟨556470, by decide⟩,⟨556503, by decide⟩,⟨556524, by decide⟩,⟨556533, by decide⟩]) unmarked_context_12_75283_556534 node_context_12_75283_556534
  intro a
  fin_cases a
  · exact context_13_301132_556470
  · exact context_13_301133_556503
  · exact context_13_301134_556524
  · exact context_13_301135_556533

theorem unmarked_context_11_18820_556535 : frontier 10 ⟨556535, by decide⟩
    (prefixCache 11 18820) (prefixPartial 11 18820) = false := by
  decide +kernel

theorem node_context_11_18820_556535 : EJMOriginalGlobalDAGData.nodes 10 ⟨556535, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨556370, by decide⟩,⟨556437, by decide⟩,⟨556534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18820_556535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18820 ⟨556535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18820
    ⟨556535, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨556370, by decide⟩,⟨556437, by decide⟩,⟨556534, by decide⟩]) unmarked_context_11_18820_556535 node_context_11_18820_556535
  intro a
  fin_cases a
  · exact context_12_75280_435160
  · exact context_12_75281_556370
  · exact context_12_75282_556437
  · exact context_12_75283_556534

theorem selected_cut_21758 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75284) = some ⟨12, 1, 0, 435160, 75284, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75284_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75284 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75284 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75284, 1, 65536⟩
    (by decide) selected_cut_21758

theorem selected_cut_21759 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 75285) = some ⟨12, 1, 0, 449506, 75285, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75285_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75285 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 75285 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 75285, 1, 65536⟩
    (by decide) selected_cut_21759

theorem selected_cut_21760 : selected 8 ⟨556573, by decide⟩
    (prefixPartial 13 301144) = some ⟨13, 2, 0, 556573, 301144, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_301144_556573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301144 ⟨556573, by decide⟩ :=
  accepted_of_selected 13 301144 ⟨556573, by decide⟩ ⟨13, 2, 0, 556573, 301144, 2309, 16384⟩
    (by decide) selected_cut_21760

theorem selected_cut_21761 : selected 8 ⟨556597, by decide⟩
    (prefixPartial 13 301145) = some ⟨13, 2, 0, 556597, 301145, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_301145_556597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301145 ⟨556597, by decide⟩ :=
  accepted_of_selected 13 301145 ⟨556597, by decide⟩ ⟨13, 2, 0, 556597, 301145, 2305, 16384⟩
    (by decide) selected_cut_21761

theorem selected_cut_21762 : selected 8 ⟨556616, by decide⟩
    (prefixPartial 13 301146) = some ⟨13, 2, 0, 556616, 301146, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_301146_556616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301146 ⟨556616, by decide⟩ :=
  accepted_of_selected 13 301146 ⟨556616, by decide⟩ ⟨13, 2, 0, 556616, 301146, 1685, 16384⟩
    (by decide) selected_cut_21762

theorem selected_cut_21763 : selected 8 ⟨556622, by decide⟩
    (prefixPartial 13 301147) = some ⟨13, 2, 0, 556622, 301147, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_301147_556622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301147 ⟨556622, by decide⟩ :=
  accepted_of_selected 13 301147 ⟨556622, by decide⟩ ⟨13, 2, 0, 556622, 301147, 1117, 16384⟩
    (by decide) selected_cut_21763

theorem unmarked_context_12_75286_556623 : frontier 9 ⟨556623, by decide⟩
    (prefixCache 12 75286) (prefixPartial 12 75286) = false := by
  decide +kernel

theorem node_context_12_75286_556623 : EJMOriginalGlobalDAGData.nodes 9 ⟨556623, by decide⟩ =
    .split (coordinate 12) (![⟨556573, by decide⟩,⟨556597, by decide⟩,⟨556616, by decide⟩,⟨556622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75286_556623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75286 ⟨556623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75286
    ⟨556623, by decide⟩ (by decide) (![⟨556573, by decide⟩,⟨556597, by decide⟩,⟨556616, by decide⟩,⟨556622, by decide⟩]) unmarked_context_12_75286_556623 node_context_12_75286_556623
  intro a
  fin_cases a
  · exact context_13_301144_556573
  · exact context_13_301145_556597
  · exact context_13_301146_556616
  · exact context_13_301147_556622

theorem selected_cut_21764 : selected 8 ⟨556671, by decide⟩
    (prefixPartial 13 301148) = some ⟨13, 2, 0, 556671, 301148, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_301148_556671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301148 ⟨556671, by decide⟩ :=
  accepted_of_selected 13 301148 ⟨556671, by decide⟩ ⟨13, 2, 0, 556671, 301148, 3033, 16384⟩
    (by decide) selected_cut_21764

theorem selected_cut_21765 : selected 8 ⟨556715, by decide⟩
    (prefixPartial 13 301149) = some ⟨13, 2, 0, 556715, 301149, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_301149_556715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301149 ⟨556715, by decide⟩ :=
  accepted_of_selected 13 301149 ⟨556715, by decide⟩ ⟨13, 2, 0, 556715, 301149, 3085, 16384⟩
    (by decide) selected_cut_21765

theorem selected_cut_21766 : selected 8 ⟨556752, by decide⟩
    (prefixPartial 13 301150) = some ⟨13, 2, 0, 556752, 301150, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_301150_556752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301150 ⟨556752, by decide⟩ :=
  accepted_of_selected 13 301150 ⟨556752, by decide⟩ ⟨13, 2, 0, 556752, 301150, 2409, 16384⟩
    (by decide) selected_cut_21766

theorem selected_cut_21767 : selected 8 ⟨556769, by decide⟩
    (prefixPartial 13 301151) = some ⟨13, 2, 0, 556769, 301151, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_301151_556769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301151 ⟨556769, by decide⟩ :=
  accepted_of_selected 13 301151 ⟨556769, by decide⟩ ⟨13, 2, 0, 556769, 301151, 1253, 16384⟩
    (by decide) selected_cut_21767

theorem unmarked_context_12_75287_556770 : frontier 9 ⟨556770, by decide⟩
    (prefixCache 12 75287) (prefixPartial 12 75287) = false := by
  decide +kernel

theorem node_context_12_75287_556770 : EJMOriginalGlobalDAGData.nodes 9 ⟨556770, by decide⟩ =
    .split (coordinate 12) (![⟨556671, by decide⟩,⟨556715, by decide⟩,⟨556752, by decide⟩,⟨556769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75287_556770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75287 ⟨556770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75287
    ⟨556770, by decide⟩ (by decide) (![⟨556671, by decide⟩,⟨556715, by decide⟩,⟨556752, by decide⟩,⟨556769, by decide⟩]) unmarked_context_12_75287_556770 node_context_12_75287_556770
  intro a
  fin_cases a
  · exact context_13_301148_556671
  · exact context_13_301149_556715
  · exact context_13_301150_556752
  · exact context_13_301151_556769

theorem unmarked_context_11_18821_556771 : frontier 10 ⟨556771, by decide⟩
    (prefixCache 11 18821) (prefixPartial 11 18821) = false := by
  decide +kernel

theorem node_context_11_18821_556771 : EJMOriginalGlobalDAGData.nodes 10 ⟨556771, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨556623, by decide⟩,⟨556770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18821_556771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18821 ⟨556771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18821
    ⟨556771, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨556623, by decide⟩,⟨556770, by decide⟩]) unmarked_context_11_18821_556771 node_context_11_18821_556771
  intro a
  fin_cases a
  · exact context_12_75284_435160
  · exact context_12_75285_449506
  · exact context_12_75286_556623
  · exact context_12_75287_556770

theorem selected_cut_21768 : selected 8 ⟨556803, by decide⟩
    (prefixPartial 13 301152) = some ⟨13, 2, 0, 556803, 301152, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_301152_556803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301152 ⟨556803, by decide⟩ :=
  accepted_of_selected 13 301152 ⟨556803, by decide⟩ ⟨13, 2, 0, 556803, 301152, 1953, 16384⟩
    (by decide) selected_cut_21768

theorem selected_cut_21769 : selected 8 ⟨556831, by decide⟩
    (prefixPartial 13 301153) = some ⟨13, 2, 0, 556831, 301153, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_301153_556831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301153 ⟨556831, by decide⟩ :=
  accepted_of_selected 13 301153 ⟨556831, by decide⟩ ⟨13, 2, 0, 556831, 301153, 2653, 16384⟩
    (by decide) selected_cut_21769

theorem selected_cut_21770 : selected 8 ⟨556851, by decide⟩
    (prefixPartial 13 301154) = some ⟨13, 2, 0, 556851, 301154, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_301154_556851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301154 ⟨556851, by decide⟩ :=
  accepted_of_selected 13 301154 ⟨556851, by decide⟩ ⟨13, 2, 0, 556851, 301154, 1937, 16384⟩
    (by decide) selected_cut_21770

theorem selected_cut_21771 : selected 8 ⟨556863, by decide⟩
    (prefixPartial 13 301155) = some ⟨13, 2, 0, 556863, 301155, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_301155_556863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301155 ⟨556863, by decide⟩ :=
  accepted_of_selected 13 301155 ⟨556863, by decide⟩ ⟨13, 2, 0, 556863, 301155, 1193, 16384⟩
    (by decide) selected_cut_21771

theorem unmarked_context_12_75288_556864 : frontier 9 ⟨556864, by decide⟩
    (prefixCache 12 75288) (prefixPartial 12 75288) = false := by
  decide +kernel

theorem node_context_12_75288_556864 : EJMOriginalGlobalDAGData.nodes 9 ⟨556864, by decide⟩ =
    .split (coordinate 12) (![⟨556803, by decide⟩,⟨556831, by decide⟩,⟨556851, by decide⟩,⟨556863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75288_556864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75288 ⟨556864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75288
    ⟨556864, by decide⟩ (by decide) (![⟨556803, by decide⟩,⟨556831, by decide⟩,⟨556851, by decide⟩,⟨556863, by decide⟩]) unmarked_context_12_75288_556864 node_context_12_75288_556864
  intro a
  fin_cases a
  · exact context_13_301152_556803
  · exact context_13_301153_556831
  · exact context_13_301154_556851
  · exact context_13_301155_556863

theorem selected_cut_21772 : selected 8 ⟨556889, by decide⟩
    (prefixPartial 13 301156) = some ⟨13, 2, 0, 556889, 301156, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_301156_556889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301156 ⟨556889, by decide⟩ :=
  accepted_of_selected 13 301156 ⟨556889, by decide⟩ ⟨13, 2, 0, 556889, 301156, 1441, 16384⟩
    (by decide) selected_cut_21772

theorem selected_cut_21773 : selected 8 ⟨556914, by decide⟩
    (prefixPartial 13 301157) = some ⟨13, 2, 0, 556914, 301157, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_301157_556914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301157 ⟨556914, by decide⟩ :=
  accepted_of_selected 13 301157 ⟨556914, by decide⟩ ⟨13, 2, 0, 556914, 301157, 1853, 16384⟩
    (by decide) selected_cut_21773

theorem selected_cut_21774 : selected 8 ⟨556929, by decide⟩
    (prefixPartial 13 301158) = some ⟨13, 2, 0, 556929, 301158, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_301158_556929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301158 ⟨556929, by decide⟩ :=
  accepted_of_selected 13 301158 ⟨556929, by decide⟩ ⟨13, 2, 0, 556929, 301158, 1373, 16384⟩
    (by decide) selected_cut_21774

theorem selected_cut_21775 : selected 8 ⟨556939, by decide⟩
    (prefixPartial 13 301159) = some ⟨13, 2, 0, 556939, 301159, 933, 16384⟩ := by
  decide +kernel

theorem context_13_301159_556939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301159 ⟨556939, by decide⟩ :=
  accepted_of_selected 13 301159 ⟨556939, by decide⟩ ⟨13, 2, 0, 556939, 301159, 933, 16384⟩
    (by decide) selected_cut_21775

theorem unmarked_context_12_75289_556940 : frontier 9 ⟨556940, by decide⟩
    (prefixCache 12 75289) (prefixPartial 12 75289) = false := by
  decide +kernel

theorem node_context_12_75289_556940 : EJMOriginalGlobalDAGData.nodes 9 ⟨556940, by decide⟩ =
    .split (coordinate 12) (![⟨556889, by decide⟩,⟨556914, by decide⟩,⟨556929, by decide⟩,⟨556939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75289_556940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75289 ⟨556940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75289
    ⟨556940, by decide⟩ (by decide) (![⟨556889, by decide⟩,⟨556914, by decide⟩,⟨556929, by decide⟩,⟨556939, by decide⟩]) unmarked_context_12_75289_556940 node_context_12_75289_556940
  intro a
  fin_cases a
  · exact context_13_301156_556889
  · exact context_13_301157_556914
  · exact context_13_301158_556929
  · exact context_13_301159_556939

theorem selected_cut_21776 : selected 8 ⟨556972, by decide⟩
    (prefixPartial 13 301160) = some ⟨13, 2, 0, 556972, 301160, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_301160_556972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301160 ⟨556972, by decide⟩ :=
  accepted_of_selected 13 301160 ⟨556972, by decide⟩ ⟨13, 2, 0, 556972, 301160, 2237, 16384⟩
    (by decide) selected_cut_21776

theorem selected_cut_21777 : selected 8 ⟨557008, by decide⟩
    (prefixPartial 13 301161) = some ⟨13, 2, 0, 557008, 301161, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_301161_557008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301161 ⟨557008, by decide⟩ :=
  accepted_of_selected 13 301161 ⟨557008, by decide⟩ ⟨13, 2, 0, 557008, 301161, 3077, 16384⟩
    (by decide) selected_cut_21777

theorem selected_cut_21778 : selected 8 ⟨557031, by decide⟩
    (prefixPartial 13 301162) = some ⟨13, 2, 0, 557031, 301162, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_301162_557031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301162 ⟨557031, by decide⟩ :=
  accepted_of_selected 13 301162 ⟨557031, by decide⟩ ⟨13, 2, 0, 557031, 301162, 2157, 16384⟩
    (by decide) selected_cut_21778

theorem selected_cut_21779 : selected 8 ⟨557045, by decide⟩
    (prefixPartial 13 301163) = some ⟨13, 2, 0, 557045, 301163, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_301163_557045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301163 ⟨557045, by decide⟩ :=
  accepted_of_selected 13 301163 ⟨557045, by decide⟩ ⟨13, 2, 0, 557045, 301163, 1309, 16384⟩
    (by decide) selected_cut_21779

theorem unmarked_context_12_75290_557046 : frontier 9 ⟨557046, by decide⟩
    (prefixCache 12 75290) (prefixPartial 12 75290) = false := by
  decide +kernel

theorem node_context_12_75290_557046 : EJMOriginalGlobalDAGData.nodes 9 ⟨557046, by decide⟩ =
    .split (coordinate 12) (![⟨556972, by decide⟩,⟨557008, by decide⟩,⟨557031, by decide⟩,⟨557045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75290_557046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75290 ⟨557046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75290
    ⟨557046, by decide⟩ (by decide) (![⟨556972, by decide⟩,⟨557008, by decide⟩,⟨557031, by decide⟩,⟨557045, by decide⟩]) unmarked_context_12_75290_557046 node_context_12_75290_557046
  intro a
  fin_cases a
  · exact context_13_301160_556972
  · exact context_13_301161_557008
  · exact context_13_301162_557031
  · exact context_13_301163_557045

theorem selected_cut_21780 : selected 8 ⟨557082, by decide⟩
    (prefixPartial 13 301164) = some ⟨13, 2, 0, 557082, 301164, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_301164_557082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301164 ⟨557082, by decide⟩ :=
  accepted_of_selected 13 301164 ⟨557082, by decide⟩ ⟨13, 2, 0, 557082, 301164, 1513, 16384⟩
    (by decide) selected_cut_21780

theorem selected_cut_21781 : selected 8 ⟨557114, by decide⟩
    (prefixPartial 13 301165) = some ⟨13, 2, 0, 557114, 301165, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_301165_557114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301165 ⟨557114, by decide⟩ :=
  accepted_of_selected 13 301165 ⟨557114, by decide⟩ ⟨13, 2, 0, 557114, 301165, 2269, 16384⟩
    (by decide) selected_cut_21781

theorem selected_cut_21782 : selected 8 ⟨557134, by decide⟩
    (prefixPartial 13 301166) = some ⟨13, 2, 0, 557134, 301166, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_301166_557134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301166 ⟨557134, by decide⟩ :=
  accepted_of_selected 13 301166 ⟨557134, by decide⟩ ⟨13, 2, 0, 557134, 301166, 1677, 16384⟩
    (by decide) selected_cut_21782

theorem selected_cut_21783 : selected 8 ⟨557140, by decide⟩
    (prefixPartial 13 301167) = some ⟨13, 2, 0, 557140, 301167, 885, 16384⟩ := by
  decide +kernel

theorem context_13_301167_557140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301167 ⟨557140, by decide⟩ :=
  accepted_of_selected 13 301167 ⟨557140, by decide⟩ ⟨13, 2, 0, 557140, 301167, 885, 16384⟩
    (by decide) selected_cut_21783

theorem unmarked_context_12_75291_557141 : frontier 9 ⟨557141, by decide⟩
    (prefixCache 12 75291) (prefixPartial 12 75291) = false := by
  decide +kernel

theorem node_context_12_75291_557141 : EJMOriginalGlobalDAGData.nodes 9 ⟨557141, by decide⟩ =
    .split (coordinate 12) (![⟨557082, by decide⟩,⟨557114, by decide⟩,⟨557134, by decide⟩,⟨557140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75291_557141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75291 ⟨557141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75291
    ⟨557141, by decide⟩ (by decide) (![⟨557082, by decide⟩,⟨557114, by decide⟩,⟨557134, by decide⟩,⟨557140, by decide⟩]) unmarked_context_12_75291_557141 node_context_12_75291_557141
  intro a
  fin_cases a
  · exact context_13_301164_557082
  · exact context_13_301165_557114
  · exact context_13_301166_557134
  · exact context_13_301167_557140

theorem unmarked_context_11_18822_557142 : frontier 10 ⟨557142, by decide⟩
    (prefixCache 11 18822) (prefixPartial 11 18822) = false := by
  decide +kernel

theorem node_context_11_18822_557142 : EJMOriginalGlobalDAGData.nodes 10 ⟨557142, by decide⟩ =
    .split (coordinate 11) (![⟨556864, by decide⟩,⟨556940, by decide⟩,⟨557046, by decide⟩,⟨557141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18822_557142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18822 ⟨557142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18822
    ⟨557142, by decide⟩ (by decide) (![⟨556864, by decide⟩,⟨556940, by decide⟩,⟨557046, by decide⟩,⟨557141, by decide⟩]) unmarked_context_11_18822_557142 node_context_11_18822_557142
  intro a
  fin_cases a
  · exact context_12_75288_556864
  · exact context_12_75289_556940
  · exact context_12_75290_557046
  · exact context_12_75291_557141

theorem selected_cut_21784 : selected 8 ⟨557180, by decide⟩
    (prefixPartial 13 301168) = some ⟨13, 2, 0, 557180, 301168, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_301168_557180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301168 ⟨557180, by decide⟩ :=
  accepted_of_selected 13 301168 ⟨557180, by decide⟩ ⟨13, 2, 0, 557180, 301168, 1853, 16384⟩
    (by decide) selected_cut_21784

theorem selected_cut_21785 : selected 8 ⟨557220, by decide⟩
    (prefixPartial 13 301169) = some ⟨13, 2, 0, 557220, 301169, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_301169_557220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301169 ⟨557220, by decide⟩ :=
  accepted_of_selected 13 301169 ⟨557220, by decide⟩ ⟨13, 2, 0, 557220, 301169, 3161, 16384⟩
    (by decide) selected_cut_21785

theorem selected_cut_21786 : selected 8 ⟨557249, by decide⟩
    (prefixPartial 13 301170) = some ⟨13, 2, 0, 557249, 301170, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_301170_557249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301170 ⟨557249, by decide⟩ :=
  accepted_of_selected 13 301170 ⟨557249, by decide⟩ ⟨13, 2, 0, 557249, 301170, 1961, 16384⟩
    (by decide) selected_cut_21786

theorem selected_cut_21787 : selected 8 ⟨557262, by decide⟩
    (prefixPartial 13 301171) = some ⟨13, 2, 0, 557262, 301171, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_301171_557262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301171 ⟨557262, by decide⟩ :=
  accepted_of_selected 13 301171 ⟨557262, by decide⟩ ⟨13, 2, 0, 557262, 301171, 1117, 16384⟩
    (by decide) selected_cut_21787

theorem unmarked_context_12_75292_557263 : frontier 9 ⟨557263, by decide⟩
    (prefixCache 12 75292) (prefixPartial 12 75292) = false := by
  decide +kernel

theorem node_context_12_75292_557263 : EJMOriginalGlobalDAGData.nodes 9 ⟨557263, by decide⟩ =
    .split (coordinate 12) (![⟨557180, by decide⟩,⟨557220, by decide⟩,⟨557249, by decide⟩,⟨557262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75292_557263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75292 ⟨557263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75292
    ⟨557263, by decide⟩ (by decide) (![⟨557180, by decide⟩,⟨557220, by decide⟩,⟨557249, by decide⟩,⟨557262, by decide⟩]) unmarked_context_12_75292_557263 node_context_12_75292_557263
  intro a
  fin_cases a
  · exact context_13_301168_557180
  · exact context_13_301169_557220
  · exact context_13_301170_557249
  · exact context_13_301171_557262

theorem selected_cut_21788 : selected 8 ⟨557284, by decide⟩
    (prefixPartial 13 301172) = some ⟨13, 2, 0, 557284, 301172, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_301172_557284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301172 ⟨557284, by decide⟩ :=
  accepted_of_selected 13 301172 ⟨557284, by decide⟩ ⟨13, 2, 0, 557284, 301172, 1165, 16384⟩
    (by decide) selected_cut_21788

theorem selected_cut_21789 : selected 8 ⟨557312, by decide⟩
    (prefixPartial 13 301173) = some ⟨13, 2, 0, 557312, 301173, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_301173_557312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301173 ⟨557312, by decide⟩ :=
  accepted_of_selected 13 301173 ⟨557312, by decide⟩ ⟨13, 2, 0, 557312, 301173, 2285, 16384⟩
    (by decide) selected_cut_21789

theorem selected_cut_21790 : selected 8 ⟨557325, by decide⟩
    (prefixPartial 13 301174) = some ⟨13, 2, 0, 557325, 301174, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_301174_557325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301174 ⟨557325, by decide⟩ :=
  accepted_of_selected 13 301174 ⟨557325, by decide⟩ ⟨13, 2, 0, 557325, 301174, 1209, 16384⟩
    (by decide) selected_cut_21790

theorem selected_cut_21791 : selected 8 ⟨557330, by decide⟩
    (prefixPartial 13 301175) = some ⟨13, 2, 0, 557330, 301175, 809, 16384⟩ := by
  decide +kernel

theorem context_13_301175_557330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301175 ⟨557330, by decide⟩ :=
  accepted_of_selected 13 301175 ⟨557330, by decide⟩ ⟨13, 2, 0, 557330, 301175, 809, 16384⟩
    (by decide) selected_cut_21791

theorem unmarked_context_12_75293_557331 : frontier 9 ⟨557331, by decide⟩
    (prefixCache 12 75293) (prefixPartial 12 75293) = false := by
  decide +kernel

theorem node_context_12_75293_557331 : EJMOriginalGlobalDAGData.nodes 9 ⟨557331, by decide⟩ =
    .split (coordinate 12) (![⟨557284, by decide⟩,⟨557312, by decide⟩,⟨557325, by decide⟩,⟨557330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75293_557331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75293 ⟨557331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75293
    ⟨557331, by decide⟩ (by decide) (![⟨557284, by decide⟩,⟨557312, by decide⟩,⟨557325, by decide⟩,⟨557330, by decide⟩]) unmarked_context_12_75293_557331 node_context_12_75293_557331
  intro a
  fin_cases a
  · exact context_13_301172_557284
  · exact context_13_301173_557312
  · exact context_13_301174_557325
  · exact context_13_301175_557330

theorem selected_cut_21792 : selected 8 ⟨557353, by decide⟩
    (prefixPartial 13 301176) = some ⟨13, 2, 0, 557353, 301176, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_301176_557353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301176 ⟨557353, by decide⟩ :=
  accepted_of_selected 13 301176 ⟨557353, by decide⟩ ⟨13, 2, 0, 557353, 301176, 1013, 16384⟩
    (by decide) selected_cut_21792

theorem selected_cut_21793 : selected 8 ⟨557381, by decide⟩
    (prefixPartial 13 301177) = some ⟨13, 2, 0, 557381, 301177, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_301177_557381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301177 ⟨557381, by decide⟩ :=
  accepted_of_selected 13 301177 ⟨557381, by decide⟩ ⟨13, 2, 0, 557381, 301177, 2117, 16384⟩
    (by decide) selected_cut_21793

theorem selected_cut_21794 : selected 8 ⟨557396, by decide⟩
    (prefixPartial 13 301178) = some ⟨13, 2, 0, 557396, 301178, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_301178_557396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301178 ⟨557396, by decide⟩ :=
  accepted_of_selected 13 301178 ⟨557396, by decide⟩ ⟨13, 2, 0, 557396, 301178, 1117, 16384⟩
    (by decide) selected_cut_21794

theorem selected_cut_21795 : selected 8 ⟨557402, by decide⟩
    (prefixPartial 13 301179) = some ⟨13, 2, 0, 557402, 301179, 813, 16384⟩ := by
  decide +kernel

theorem context_13_301179_557402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301179 ⟨557402, by decide⟩ :=
  accepted_of_selected 13 301179 ⟨557402, by decide⟩ ⟨13, 2, 0, 557402, 301179, 813, 16384⟩
    (by decide) selected_cut_21795

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
