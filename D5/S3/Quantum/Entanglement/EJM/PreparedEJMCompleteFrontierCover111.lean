/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover110
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_6290_288096 : frontier 10 ⟨288096, by decide⟩
    (prefixCache 11 6290) (prefixPartial 11 6290) = false := by
  decide +kernel

theorem node_context_11_6290_288096 : EJMOriginalGlobalDAGData.nodes 10 ⟨288096, by decide⟩ =
    .split (coordinate 11) (![⟨287944, by decide⟩,⟨287992, by decide⟩,⟨288049, by decide⟩,⟨288095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6290_288096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6290 ⟨288096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6290
    ⟨288096, by decide⟩ (by decide) (![⟨287944, by decide⟩,⟨287992, by decide⟩,⟨288049, by decide⟩,⟨288095, by decide⟩]) unmarked_context_11_6290_288096 node_context_11_6290_288096
  intro a
  fin_cases a
  · exact context_12_25160_287944
  · exact context_12_25161_287992
  · exact context_12_25162_288049
  · exact context_12_25163_288095

theorem selected_cut_10659 : selected 9 ⟨288135, by decide⟩
    (prefixPartial 12 25164) = some ⟨12, 2, 0, 288135, 25164, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_25164_288135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25164 ⟨288135, by decide⟩ :=
  accepted_of_selected 12 25164 ⟨288135, by decide⟩ ⟨12, 2, 0, 288135, 25164, 3117, 65536⟩
    (by decide) selected_cut_10659

theorem selected_cut_10660 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100660) = some ⟨13, 1, 0, 3444, 100660, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100660_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100660 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100660 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100660, 1, 16384⟩
    (by decide) selected_cut_10660

theorem selected_cut_10661 : selected 8 ⟨288154, by decide⟩
    (prefixPartial 13 100661) = some ⟨13, 2, 0, 288154, 100661, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_100661_288154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100661 ⟨288154, by decide⟩ :=
  accepted_of_selected 13 100661 ⟨288154, by decide⟩ ⟨13, 2, 0, 288154, 100661, 2253, 16384⟩
    (by decide) selected_cut_10661

theorem selected_cut_10662 : selected 8 ⟨288182, by decide⟩
    (prefixPartial 13 100662) = some ⟨13, 2, 0, 288182, 100662, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_100662_288182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100662 ⟨288182, by decide⟩ :=
  accepted_of_selected 13 100662 ⟨288182, by decide⟩ ⟨13, 2, 0, 288182, 100662, 1993, 16384⟩
    (by decide) selected_cut_10662

theorem selected_cut_10663 : selected 8 ⟨288190, by decide⟩
    (prefixPartial 13 100663) = some ⟨13, 2, 0, 288190, 100663, 993, 16384⟩ := by
  decide +kernel

theorem context_13_100663_288190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100663 ⟨288190, by decide⟩ :=
  accepted_of_selected 13 100663 ⟨288190, by decide⟩ ⟨13, 2, 0, 288190, 100663, 993, 16384⟩
    (by decide) selected_cut_10663

theorem unmarked_context_12_25165_288191 : frontier 9 ⟨288191, by decide⟩
    (prefixCache 12 25165) (prefixPartial 12 25165) = false := by
  decide +kernel

theorem node_context_12_25165_288191 : EJMOriginalGlobalDAGData.nodes 9 ⟨288191, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288154, by decide⟩,⟨288182, by decide⟩,⟨288190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25165_288191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25165 ⟨288191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25165
    ⟨288191, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288154, by decide⟩,⟨288182, by decide⟩,⟨288190, by decide⟩]) unmarked_context_12_25165_288191 node_context_12_25165_288191
  intro a
  fin_cases a
  · exact context_13_100660_3444
  · exact context_13_100661_288154
  · exact context_13_100662_288182
  · exact context_13_100663_288190

theorem selected_cut_10664 : selected 9 ⟨288239, by decide⟩
    (prefixPartial 12 25166) = some ⟨12, 2, 0, 288239, 25166, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_25166_288239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25166 ⟨288239, by decide⟩ :=
  accepted_of_selected 12 25166 ⟨288239, by decide⟩ ⟨12, 2, 0, 288239, 25166, 3505, 65536⟩
    (by decide) selected_cut_10664

theorem selected_cut_10665 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100668) = some ⟨13, 1, 0, 3444, 100668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100668, 1, 16384⟩
    (by decide) selected_cut_10665

theorem selected_cut_10666 : selected 8 ⟨288256, by decide⟩
    (prefixPartial 13 100669) = some ⟨13, 2, 0, 288256, 100669, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_100669_288256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100669 ⟨288256, by decide⟩ :=
  accepted_of_selected 13 100669 ⟨288256, by decide⟩ ⟨13, 2, 0, 288256, 100669, 1613, 16384⟩
    (by decide) selected_cut_10666

theorem selected_cut_10667 : selected 8 ⟨288277, by decide⟩
    (prefixPartial 13 100670) = some ⟨13, 2, 0, 288277, 100670, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_100670_288277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100670 ⟨288277, by decide⟩ :=
  accepted_of_selected 13 100670 ⟨288277, by decide⟩ ⟨13, 2, 0, 288277, 100670, 1633, 16384⟩
    (by decide) selected_cut_10667

theorem selected_cut_10668 : selected 8 ⟨288284, by decide⟩
    (prefixPartial 13 100671) = some ⟨13, 2, 0, 288284, 100671, 913, 16384⟩ := by
  decide +kernel

theorem context_13_100671_288284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100671 ⟨288284, by decide⟩ :=
  accepted_of_selected 13 100671 ⟨288284, by decide⟩ ⟨13, 2, 0, 288284, 100671, 913, 16384⟩
    (by decide) selected_cut_10668

theorem unmarked_context_12_25167_288285 : frontier 9 ⟨288285, by decide⟩
    (prefixCache 12 25167) (prefixPartial 12 25167) = false := by
  decide +kernel

theorem node_context_12_25167_288285 : EJMOriginalGlobalDAGData.nodes 9 ⟨288285, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288256, by decide⟩,⟨288277, by decide⟩,⟨288284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25167_288285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25167 ⟨288285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25167
    ⟨288285, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288256, by decide⟩,⟨288277, by decide⟩,⟨288284, by decide⟩]) unmarked_context_12_25167_288285 node_context_12_25167_288285
  intro a
  fin_cases a
  · exact context_13_100668_3444
  · exact context_13_100669_288256
  · exact context_13_100670_288277
  · exact context_13_100671_288284

theorem unmarked_context_11_6291_288286 : frontier 10 ⟨288286, by decide⟩
    (prefixCache 11 6291) (prefixPartial 11 6291) = false := by
  decide +kernel

theorem node_context_11_6291_288286 : EJMOriginalGlobalDAGData.nodes 10 ⟨288286, by decide⟩ =
    .split (coordinate 11) (![⟨288135, by decide⟩,⟨288191, by decide⟩,⟨288239, by decide⟩,⟨288285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6291_288286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6291 ⟨288286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6291
    ⟨288286, by decide⟩ (by decide) (![⟨288135, by decide⟩,⟨288191, by decide⟩,⟨288239, by decide⟩,⟨288285, by decide⟩]) unmarked_context_11_6291_288286 node_context_11_6291_288286
  intro a
  fin_cases a
  · exact context_12_25164_288135
  · exact context_12_25165_288191
  · exact context_12_25166_288239
  · exact context_12_25167_288285

theorem unmarked_context_10_1572_288287 : frontier 11 ⟨288287, by decide⟩
    (prefixCache 10 1572) (prefixPartial 10 1572) = false := by
  decide +kernel

theorem node_context_10_1572_288287 : EJMOriginalGlobalDAGData.nodes 11 ⟨288287, by decide⟩ =
    .split (coordinate 10) (![⟨287691, by decide⟩,⟨287909, by decide⟩,⟨288096, by decide⟩,⟨288286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1572_288287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1572 ⟨288287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1572
    ⟨288287, by decide⟩ (by decide) (![⟨287691, by decide⟩,⟨287909, by decide⟩,⟨288096, by decide⟩,⟨288286, by decide⟩]) unmarked_context_10_1572_288287 node_context_10_1572_288287
  intro a
  fin_cases a
  · exact context_11_6288_287691
  · exact context_11_6289_287909
  · exact context_11_6290_288096
  · exact context_11_6291_288286

theorem selected_cut_10669 : selected 9 ⟨288319, by decide⟩
    (prefixPartial 12 25168) = some ⟨12, 2, 0, 288319, 25168, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_25168_288319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25168 ⟨288319, by decide⟩ :=
  accepted_of_selected 12 25168 ⟨288319, by decide⟩ ⟨12, 2, 0, 288319, 25168, 2785, 65536⟩
    (by decide) selected_cut_10669

theorem selected_cut_10670 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 25169) = some ⟨12, 1, 0, 170504, 25169, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25169_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25169 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 25169 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 25169, 1, 65536⟩
    (by decide) selected_cut_10670

theorem selected_cut_10671 : selected 9 ⟨288360, by decide⟩
    (prefixPartial 12 25170) = some ⟨12, 2, 0, 288360, 25170, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_25170_288360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25170 ⟨288360, by decide⟩ :=
  accepted_of_selected 12 25170 ⟨288360, by decide⟩ ⟨12, 2, 0, 288360, 25170, 3397, 65536⟩
    (by decide) selected_cut_10671

theorem selected_cut_10672 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100684) = some ⟨13, 1, 0, 3444, 100684, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100684_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100684 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100684 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100684, 1, 16384⟩
    (by decide) selected_cut_10672

theorem selected_cut_10673 : selected 8 ⟨288379, by decide⟩
    (prefixPartial 13 100685) = some ⟨13, 2, 0, 288379, 100685, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_100685_288379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100685 ⟨288379, by decide⟩ :=
  accepted_of_selected 13 100685 ⟨288379, by decide⟩ ⟨13, 2, 0, 288379, 100685, 1681, 16384⟩
    (by decide) selected_cut_10673

theorem selected_cut_10674 : selected 8 ⟨288404, by decide⟩
    (prefixPartial 13 100686) = some ⟨13, 2, 0, 288404, 100686, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_100686_288404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100686 ⟨288404, by decide⟩ :=
  accepted_of_selected 13 100686 ⟨288404, by decide⟩ ⟨13, 2, 0, 288404, 100686, 1749, 16384⟩
    (by decide) selected_cut_10674

theorem selected_cut_10675 : selected 8 ⟨288408, by decide⟩
    (prefixPartial 13 100687) = some ⟨13, 2, 0, 288408, 100687, 849, 16384⟩ := by
  decide +kernel

theorem context_13_100687_288408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100687 ⟨288408, by decide⟩ :=
  accepted_of_selected 13 100687 ⟨288408, by decide⟩ ⟨13, 2, 0, 288408, 100687, 849, 16384⟩
    (by decide) selected_cut_10675

theorem unmarked_context_12_25171_288409 : frontier 9 ⟨288409, by decide⟩
    (prefixCache 12 25171) (prefixPartial 12 25171) = false := by
  decide +kernel

theorem node_context_12_25171_288409 : EJMOriginalGlobalDAGData.nodes 9 ⟨288409, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288379, by decide⟩,⟨288404, by decide⟩,⟨288408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25171_288409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25171 ⟨288409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25171
    ⟨288409, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288379, by decide⟩,⟨288404, by decide⟩,⟨288408, by decide⟩]) unmarked_context_12_25171_288409 node_context_12_25171_288409
  intro a
  fin_cases a
  · exact context_13_100684_3444
  · exact context_13_100685_288379
  · exact context_13_100686_288404
  · exact context_13_100687_288408

theorem unmarked_context_11_6292_288410 : frontier 10 ⟨288410, by decide⟩
    (prefixCache 11 6292) (prefixPartial 11 6292) = false := by
  decide +kernel

theorem node_context_11_6292_288410 : EJMOriginalGlobalDAGData.nodes 10 ⟨288410, by decide⟩ =
    .split (coordinate 11) (![⟨288319, by decide⟩,⟨170504, by decide⟩,⟨288360, by decide⟩,⟨288409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6292_288410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6292 ⟨288410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6292
    ⟨288410, by decide⟩ (by decide) (![⟨288319, by decide⟩,⟨170504, by decide⟩,⟨288360, by decide⟩,⟨288409, by decide⟩]) unmarked_context_11_6292_288410 node_context_11_6292_288410
  intro a
  fin_cases a
  · exact context_12_25168_288319
  · exact context_12_25169_170504
  · exact context_12_25170_288360
  · exact context_12_25171_288409

theorem selected_cut_10676 : selected 9 ⟨288447, by decide⟩
    (prefixPartial 12 25172) = some ⟨12, 2, 0, 288447, 25172, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_25172_288447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25172 ⟨288447, by decide⟩ :=
  accepted_of_selected 12 25172 ⟨288447, by decide⟩ ⟨12, 2, 0, 288447, 25172, 3061, 65536⟩
    (by decide) selected_cut_10676

theorem selected_cut_10677 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 25173) = some ⟨12, 1, 0, 170504, 25173, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25173_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25173 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 25173 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 25173, 1, 65536⟩
    (by decide) selected_cut_10677

theorem selected_cut_10678 : selected 9 ⟨288492, by decide⟩
    (prefixPartial 12 25174) = some ⟨12, 2, 0, 288492, 25174, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_25174_288492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25174 ⟨288492, by decide⟩ :=
  accepted_of_selected 12 25174 ⟨288492, by decide⟩ ⟨12, 2, 0, 288492, 25174, 3877, 65536⟩
    (by decide) selected_cut_10678

theorem selected_cut_10679 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100700) = some ⟨13, 1, 0, 3444, 100700, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100700_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100700 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100700 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100700, 1, 16384⟩
    (by decide) selected_cut_10679

theorem selected_cut_10680 : selected 8 ⟨288511, by decide⟩
    (prefixPartial 13 100701) = some ⟨13, 2, 0, 288511, 100701, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_100701_288511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100701 ⟨288511, by decide⟩ :=
  accepted_of_selected 13 100701 ⟨288511, by decide⟩ ⟨13, 2, 0, 288511, 100701, 1661, 16384⟩
    (by decide) selected_cut_10680

theorem selected_cut_10681 : selected 8 ⟨288537, by decide⟩
    (prefixPartial 13 100702) = some ⟨13, 2, 0, 288537, 100702, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_100702_288537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100702 ⟨288537, by decide⟩ :=
  accepted_of_selected 13 100702 ⟨288537, by decide⟩ ⟨13, 2, 0, 288537, 100702, 1945, 16384⟩
    (by decide) selected_cut_10681

theorem selected_cut_10682 : selected 8 ⟨288548, by decide⟩
    (prefixPartial 13 100703) = some ⟨13, 2, 0, 288548, 100703, 993, 16384⟩ := by
  decide +kernel

theorem context_13_100703_288548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100703 ⟨288548, by decide⟩ :=
  accepted_of_selected 13 100703 ⟨288548, by decide⟩ ⟨13, 2, 0, 288548, 100703, 993, 16384⟩
    (by decide) selected_cut_10682

theorem unmarked_context_12_25175_288549 : frontier 9 ⟨288549, by decide⟩
    (prefixCache 12 25175) (prefixPartial 12 25175) = false := by
  decide +kernel

theorem node_context_12_25175_288549 : EJMOriginalGlobalDAGData.nodes 9 ⟨288549, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288511, by decide⟩,⟨288537, by decide⟩,⟨288548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25175_288549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25175 ⟨288549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25175
    ⟨288549, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288511, by decide⟩,⟨288537, by decide⟩,⟨288548, by decide⟩]) unmarked_context_12_25175_288549 node_context_12_25175_288549
  intro a
  fin_cases a
  · exact context_13_100700_3444
  · exact context_13_100701_288511
  · exact context_13_100702_288537
  · exact context_13_100703_288548

theorem unmarked_context_11_6293_288550 : frontier 10 ⟨288550, by decide⟩
    (prefixCache 11 6293) (prefixPartial 11 6293) = false := by
  decide +kernel

theorem node_context_11_6293_288550 : EJMOriginalGlobalDAGData.nodes 10 ⟨288550, by decide⟩ =
    .split (coordinate 11) (![⟨288447, by decide⟩,⟨170504, by decide⟩,⟨288492, by decide⟩,⟨288549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6293_288550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6293 ⟨288550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6293
    ⟨288550, by decide⟩ (by decide) (![⟨288447, by decide⟩,⟨170504, by decide⟩,⟨288492, by decide⟩,⟨288549, by decide⟩]) unmarked_context_11_6293_288550 node_context_11_6293_288550
  intro a
  fin_cases a
  · exact context_12_25172_288447
  · exact context_12_25173_170504
  · exact context_12_25174_288492
  · exact context_12_25175_288549

theorem selected_cut_10683 : selected 9 ⟨288580, by decide⟩
    (prefixPartial 12 25176) = some ⟨12, 2, 0, 288580, 25176, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_25176_288580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25176 ⟨288580, by decide⟩ :=
  accepted_of_selected 12 25176 ⟨288580, by decide⟩ ⟨12, 2, 0, 288580, 25176, 2417, 65536⟩
    (by decide) selected_cut_10683

theorem selected_cut_10684 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100708) = some ⟨13, 1, 0, 3444, 100708, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100708_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100708 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100708 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100708, 1, 16384⟩
    (by decide) selected_cut_10684

theorem selected_cut_10685 : selected 8 ⟨288600, by decide⟩
    (prefixPartial 13 100709) = some ⟨13, 2, 0, 288600, 100709, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_100709_288600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100709 ⟨288600, by decide⟩ :=
  accepted_of_selected 13 100709 ⟨288600, by decide⟩ ⟨13, 2, 0, 288600, 100709, 1505, 16384⟩
    (by decide) selected_cut_10685

theorem selected_cut_10686 : selected 8 ⟨288621, by decide⟩
    (prefixPartial 13 100710) = some ⟨13, 2, 0, 288621, 100710, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_100710_288621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100710 ⟨288621, by decide⟩ :=
  accepted_of_selected 13 100710 ⟨288621, by decide⟩ ⟨13, 2, 0, 288621, 100710, 2041, 16384⟩
    (by decide) selected_cut_10686

theorem selected_cut_10687 : selected 8 ⟨288629, by decide⟩
    (prefixPartial 13 100711) = some ⟨13, 2, 0, 288629, 100711, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_100711_288629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100711 ⟨288629, by decide⟩ :=
  accepted_of_selected 13 100711 ⟨288629, by decide⟩ ⟨13, 2, 0, 288629, 100711, 1025, 16384⟩
    (by decide) selected_cut_10687

theorem unmarked_context_12_25177_288630 : frontier 9 ⟨288630, by decide⟩
    (prefixCache 12 25177) (prefixPartial 12 25177) = false := by
  decide +kernel

theorem node_context_12_25177_288630 : EJMOriginalGlobalDAGData.nodes 9 ⟨288630, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288600, by decide⟩,⟨288621, by decide⟩,⟨288629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25177_288630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25177 ⟨288630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25177
    ⟨288630, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288600, by decide⟩,⟨288621, by decide⟩,⟨288629, by decide⟩]) unmarked_context_12_25177_288630 node_context_12_25177_288630
  intro a
  fin_cases a
  · exact context_13_100708_3444
  · exact context_13_100709_288600
  · exact context_13_100710_288621
  · exact context_13_100711_288629

theorem selected_cut_10688 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100712) = some ⟨13, 1, 0, 3444, 100712, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100712_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100712 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100712 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100712, 1, 16384⟩
    (by decide) selected_cut_10688

theorem selected_cut_10689 : selected 8 ⟨288650, by decide⟩
    (prefixPartial 13 100713) = some ⟨13, 2, 0, 288650, 100713, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_100713_288650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100713 ⟨288650, by decide⟩ :=
  accepted_of_selected 13 100713 ⟨288650, by decide⟩ ⟨13, 2, 0, 288650, 100713, 1809, 16384⟩
    (by decide) selected_cut_10689

theorem selected_cut_10690 : selected 8 ⟨288672, by decide⟩
    (prefixPartial 13 100714) = some ⟨13, 2, 0, 288672, 100714, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_100714_288672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100714 ⟨288672, by decide⟩ :=
  accepted_of_selected 13 100714 ⟨288672, by decide⟩ ⟨13, 2, 0, 288672, 100714, 2225, 16384⟩
    (by decide) selected_cut_10690

theorem selected_cut_10691 : selected 8 ⟨288680, by decide⟩
    (prefixPartial 13 100715) = some ⟨13, 2, 0, 288680, 100715, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_100715_288680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100715 ⟨288680, by decide⟩ :=
  accepted_of_selected 13 100715 ⟨288680, by decide⟩ ⟨13, 2, 0, 288680, 100715, 1185, 16384⟩
    (by decide) selected_cut_10691

theorem unmarked_context_12_25178_288681 : frontier 9 ⟨288681, by decide⟩
    (prefixCache 12 25178) (prefixPartial 12 25178) = false := by
  decide +kernel

theorem node_context_12_25178_288681 : EJMOriginalGlobalDAGData.nodes 9 ⟨288681, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288650, by decide⟩,⟨288672, by decide⟩,⟨288680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25178_288681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25178 ⟨288681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25178
    ⟨288681, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288650, by decide⟩,⟨288672, by decide⟩,⟨288680, by decide⟩]) unmarked_context_12_25178_288681 node_context_12_25178_288681
  intro a
  fin_cases a
  · exact context_13_100712_3444
  · exact context_13_100713_288650
  · exact context_13_100714_288672
  · exact context_13_100715_288680

theorem selected_cut_10692 : selected 9 ⟨288725, by decide⟩
    (prefixPartial 12 25179) = some ⟨12, 2, 0, 288725, 25179, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_25179_288725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25179 ⟨288725, by decide⟩ :=
  accepted_of_selected 12 25179 ⟨288725, by decide⟩ ⟨12, 2, 0, 288725, 25179, 3497, 65536⟩
    (by decide) selected_cut_10692

theorem unmarked_context_11_6294_288726 : frontier 10 ⟨288726, by decide⟩
    (prefixCache 11 6294) (prefixPartial 11 6294) = false := by
  decide +kernel

theorem node_context_11_6294_288726 : EJMOriginalGlobalDAGData.nodes 10 ⟨288726, by decide⟩ =
    .split (coordinate 11) (![⟨288580, by decide⟩,⟨288630, by decide⟩,⟨288681, by decide⟩,⟨288725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6294_288726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6294 ⟨288726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6294
    ⟨288726, by decide⟩ (by decide) (![⟨288580, by decide⟩,⟨288630, by decide⟩,⟨288681, by decide⟩,⟨288725, by decide⟩]) unmarked_context_11_6294_288726 node_context_11_6294_288726
  intro a
  fin_cases a
  · exact context_12_25176_288580
  · exact context_12_25177_288630
  · exact context_12_25178_288681
  · exact context_12_25179_288725

theorem selected_cut_10693 : selected 9 ⟨288759, by decide⟩
    (prefixPartial 12 25180) = some ⟨12, 2, 0, 288759, 25180, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_25180_288759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25180 ⟨288759, by decide⟩ :=
  accepted_of_selected 12 25180 ⟨288759, by decide⟩ ⟨12, 2, 0, 288759, 25180, 2769, 65536⟩
    (by decide) selected_cut_10693

theorem selected_cut_10694 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100724) = some ⟨13, 1, 0, 3444, 100724, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100724_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100724 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100724 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100724, 1, 16384⟩
    (by decide) selected_cut_10694

theorem selected_cut_10695 : selected 8 ⟨288775, by decide⟩
    (prefixPartial 13 100725) = some ⟨13, 2, 0, 288775, 100725, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_100725_288775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100725 ⟨288775, by decide⟩ :=
  accepted_of_selected 13 100725 ⟨288775, by decide⟩ ⟨13, 2, 0, 288775, 100725, 1533, 16384⟩
    (by decide) selected_cut_10695

theorem selected_cut_10696 : selected 8 ⟨288806, by decide⟩
    (prefixPartial 13 100726) = some ⟨13, 2, 0, 288806, 100726, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_100726_288806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100726 ⟨288806, by decide⟩ :=
  accepted_of_selected 13 100726 ⟨288806, by decide⟩ ⟨13, 2, 0, 288806, 100726, 2293, 16384⟩
    (by decide) selected_cut_10696

theorem selected_cut_10697 : selected 8 ⟨288814, by decide⟩
    (prefixPartial 13 100727) = some ⟨13, 2, 0, 288814, 100727, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_100727_288814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100727 ⟨288814, by decide⟩ :=
  accepted_of_selected 13 100727 ⟨288814, by decide⟩ ⟨13, 2, 0, 288814, 100727, 1073, 16384⟩
    (by decide) selected_cut_10697

theorem unmarked_context_12_25181_288815 : frontier 9 ⟨288815, by decide⟩
    (prefixCache 12 25181) (prefixPartial 12 25181) = false := by
  decide +kernel

theorem node_context_12_25181_288815 : EJMOriginalGlobalDAGData.nodes 9 ⟨288815, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288775, by decide⟩,⟨288806, by decide⟩,⟨288814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25181_288815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25181 ⟨288815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25181
    ⟨288815, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288775, by decide⟩,⟨288806, by decide⟩,⟨288814, by decide⟩]) unmarked_context_12_25181_288815 node_context_12_25181_288815
  intro a
  fin_cases a
  · exact context_13_100724_3444
  · exact context_13_100725_288775
  · exact context_13_100726_288806
  · exact context_13_100727_288814

theorem selected_cut_10698 : selected 9 ⟨288852, by decide⟩
    (prefixPartial 12 25182) = some ⟨12, 2, 0, 288852, 25182, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_25182_288852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25182 ⟨288852, by decide⟩ :=
  accepted_of_selected 12 25182 ⟨288852, by decide⟩ ⟨12, 2, 0, 288852, 25182, 3145, 65536⟩
    (by decide) selected_cut_10698

theorem selected_cut_10699 : selected 9 ⟨288899, by decide⟩
    (prefixPartial 12 25183) = some ⟨12, 2, 0, 288899, 25183, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_25183_288899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25183 ⟨288899, by decide⟩ :=
  accepted_of_selected 12 25183 ⟨288899, by decide⟩ ⟨12, 2, 0, 288899, 25183, 3769, 65536⟩
    (by decide) selected_cut_10699

theorem unmarked_context_11_6295_288900 : frontier 10 ⟨288900, by decide⟩
    (prefixCache 11 6295) (prefixPartial 11 6295) = false := by
  decide +kernel

theorem node_context_11_6295_288900 : EJMOriginalGlobalDAGData.nodes 10 ⟨288900, by decide⟩ =
    .split (coordinate 11) (![⟨288759, by decide⟩,⟨288815, by decide⟩,⟨288852, by decide⟩,⟨288899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6295_288900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6295 ⟨288900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6295
    ⟨288900, by decide⟩ (by decide) (![⟨288759, by decide⟩,⟨288815, by decide⟩,⟨288852, by decide⟩,⟨288899, by decide⟩]) unmarked_context_11_6295_288900 node_context_11_6295_288900
  intro a
  fin_cases a
  · exact context_12_25180_288759
  · exact context_12_25181_288815
  · exact context_12_25182_288852
  · exact context_12_25183_288899

theorem unmarked_context_10_1573_288901 : frontier 11 ⟨288901, by decide⟩
    (prefixCache 10 1573) (prefixPartial 10 1573) = false := by
  decide +kernel

theorem node_context_10_1573_288901 : EJMOriginalGlobalDAGData.nodes 11 ⟨288901, by decide⟩ =
    .split (coordinate 10) (![⟨288410, by decide⟩,⟨288550, by decide⟩,⟨288726, by decide⟩,⟨288900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1573_288901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1573 ⟨288901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1573
    ⟨288901, by decide⟩ (by decide) (![⟨288410, by decide⟩,⟨288550, by decide⟩,⟨288726, by decide⟩,⟨288900, by decide⟩]) unmarked_context_10_1573_288901 node_context_10_1573_288901
  intro a
  fin_cases a
  · exact context_11_6292_288410
  · exact context_11_6293_288550
  · exact context_11_6294_288726
  · exact context_11_6295_288900

theorem selected_cut_10700 : selected 9 ⟨288932, by decide⟩
    (prefixPartial 12 25184) = some ⟨12, 2, 0, 288932, 25184, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_25184_288932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25184 ⟨288932, by decide⟩ :=
  accepted_of_selected 12 25184 ⟨288932, by decide⟩ ⟨12, 2, 0, 288932, 25184, 2733, 65536⟩
    (by decide) selected_cut_10700

theorem selected_cut_10701 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100740) = some ⟨13, 1, 0, 3444, 100740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100740, 1, 16384⟩
    (by decide) selected_cut_10701

theorem selected_cut_10702 : selected 8 ⟨288951, by decide⟩
    (prefixPartial 13 100741) = some ⟨13, 2, 0, 288951, 100741, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_100741_288951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100741 ⟨288951, by decide⟩ :=
  accepted_of_selected 13 100741 ⟨288951, by decide⟩ ⟨13, 2, 0, 288951, 100741, 1609, 16384⟩
    (by decide) selected_cut_10702

theorem selected_cut_10703 : selected 8 ⟨288979, by decide⟩
    (prefixPartial 13 100742) = some ⟨13, 2, 0, 288979, 100742, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_100742_288979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100742 ⟨288979, by decide⟩ :=
  accepted_of_selected 13 100742 ⟨288979, by decide⟩ ⟨13, 2, 0, 288979, 100742, 2197, 16384⟩
    (by decide) selected_cut_10703

theorem selected_cut_10704 : selected 8 ⟨288990, by decide⟩
    (prefixPartial 13 100743) = some ⟨13, 2, 0, 288990, 100743, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_100743_288990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100743 ⟨288990, by decide⟩ :=
  accepted_of_selected 13 100743 ⟨288990, by decide⟩ ⟨13, 2, 0, 288990, 100743, 1037, 16384⟩
    (by decide) selected_cut_10704

theorem unmarked_context_12_25185_288991 : frontier 9 ⟨288991, by decide⟩
    (prefixCache 12 25185) (prefixPartial 12 25185) = false := by
  decide +kernel

theorem node_context_12_25185_288991 : EJMOriginalGlobalDAGData.nodes 9 ⟨288991, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨288951, by decide⟩,⟨288979, by decide⟩,⟨288990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25185_288991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25185 ⟨288991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25185
    ⟨288991, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨288951, by decide⟩,⟨288979, by decide⟩,⟨288990, by decide⟩]) unmarked_context_12_25185_288991 node_context_12_25185_288991
  intro a
  fin_cases a
  · exact context_13_100740_3444
  · exact context_13_100741_288951
  · exact context_13_100742_288979
  · exact context_13_100743_288990

theorem selected_cut_10705 : selected 9 ⟨289021, by decide⟩
    (prefixPartial 12 25186) = some ⟨12, 2, 0, 289021, 25186, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_25186_289021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25186 ⟨289021, by decide⟩ :=
  accepted_of_selected 12 25186 ⟨289021, by decide⟩ ⟨12, 2, 0, 289021, 25186, 2849, 65536⟩
    (by decide) selected_cut_10705

theorem selected_cut_10706 : selected 9 ⟨289062, by decide⟩
    (prefixPartial 12 25187) = some ⟨12, 2, 0, 289062, 25187, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_25187_289062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25187 ⟨289062, by decide⟩ :=
  accepted_of_selected 12 25187 ⟨289062, by decide⟩ ⟨12, 2, 0, 289062, 25187, 3805, 65536⟩
    (by decide) selected_cut_10706

theorem unmarked_context_11_6296_289063 : frontier 10 ⟨289063, by decide⟩
    (prefixCache 11 6296) (prefixPartial 11 6296) = false := by
  decide +kernel

theorem node_context_11_6296_289063 : EJMOriginalGlobalDAGData.nodes 10 ⟨289063, by decide⟩ =
    .split (coordinate 11) (![⟨288932, by decide⟩,⟨288991, by decide⟩,⟨289021, by decide⟩,⟨289062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6296_289063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6296 ⟨289063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6296
    ⟨289063, by decide⟩ (by decide) (![⟨288932, by decide⟩,⟨288991, by decide⟩,⟨289021, by decide⟩,⟨289062, by decide⟩]) unmarked_context_11_6296_289063 node_context_11_6296_289063
  intro a
  fin_cases a
  · exact context_12_25184_288932
  · exact context_12_25185_288991
  · exact context_12_25186_289021
  · exact context_12_25187_289062

theorem selected_cut_10707 : selected 9 ⟨289097, by decide⟩
    (prefixPartial 12 25188) = some ⟨12, 2, 0, 289097, 25188, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_25188_289097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25188 ⟨289097, by decide⟩ :=
  accepted_of_selected 12 25188 ⟨289097, by decide⟩ ⟨12, 2, 0, 289097, 25188, 2885, 65536⟩
    (by decide) selected_cut_10707

theorem selected_cut_10708 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 25189) = some ⟨12, 1, 0, 289098, 25189, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25189_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25189 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 25189 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 25189, 1, 65536⟩
    (by decide) selected_cut_10708

theorem selected_cut_10709 : selected 9 ⟨289134, by decide⟩
    (prefixPartial 12 25190) = some ⟨12, 2, 0, 289134, 25190, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_25190_289134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25190 ⟨289134, by decide⟩ :=
  accepted_of_selected 12 25190 ⟨289134, by decide⟩ ⟨12, 2, 0, 289134, 25190, 3165, 65536⟩
    (by decide) selected_cut_10709

theorem selected_cut_10710 : selected 9 ⟨289182, by decide⟩
    (prefixPartial 12 25191) = some ⟨12, 2, 0, 289182, 25191, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_25191_289182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25191 ⟨289182, by decide⟩ :=
  accepted_of_selected 12 25191 ⟨289182, by decide⟩ ⟨12, 2, 0, 289182, 25191, 4009, 65536⟩
    (by decide) selected_cut_10710

theorem unmarked_context_11_6297_289183 : frontier 10 ⟨289183, by decide⟩
    (prefixCache 11 6297) (prefixPartial 11 6297) = false := by
  decide +kernel

theorem node_context_11_6297_289183 : EJMOriginalGlobalDAGData.nodes 10 ⟨289183, by decide⟩ =
    .split (coordinate 11) (![⟨289097, by decide⟩,⟨289098, by decide⟩,⟨289134, by decide⟩,⟨289182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6297_289183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6297 ⟨289183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6297
    ⟨289183, by decide⟩ (by decide) (![⟨289097, by decide⟩,⟨289098, by decide⟩,⟨289134, by decide⟩,⟨289182, by decide⟩]) unmarked_context_11_6297_289183 node_context_11_6297_289183
  intro a
  fin_cases a
  · exact context_12_25188_289097
  · exact context_12_25189_289098
  · exact context_12_25190_289134
  · exact context_12_25191_289182

theorem selected_cut_10711 : selected 9 ⟨289214, by decide⟩
    (prefixPartial 12 25192) = some ⟨12, 2, 0, 289214, 25192, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_25192_289214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25192 ⟨289214, by decide⟩ :=
  accepted_of_selected 12 25192 ⟨289214, by decide⟩ ⟨12, 2, 0, 289214, 25192, 2409, 65536⟩
    (by decide) selected_cut_10711

theorem selected_cut_10712 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100772) = some ⟨13, 1, 0, 3444, 100772, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100772_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100772 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100772 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100772, 1, 16384⟩
    (by decide) selected_cut_10712

theorem selected_cut_10713 : selected 8 ⟨289225, by decide⟩
    (prefixPartial 13 100773) = some ⟨13, 2, 0, 289225, 100773, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_100773_289225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100773 ⟨289225, by decide⟩ :=
  accepted_of_selected 13 100773 ⟨289225, by decide⟩ ⟨13, 2, 0, 289225, 100773, 1053, 16384⟩
    (by decide) selected_cut_10713

theorem selected_cut_10714 : selected 8 ⟨289246, by decide⟩
    (prefixPartial 13 100774) = some ⟨13, 2, 0, 289246, 100774, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_100774_289246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100774 ⟨289246, by decide⟩ :=
  accepted_of_selected 13 100774 ⟨289246, by decide⟩ ⟨13, 2, 0, 289246, 100774, 2193, 16384⟩
    (by decide) selected_cut_10714

theorem selected_cut_10715 : selected 8 ⟨289250, by decide⟩
    (prefixPartial 13 100775) = some ⟨13, 2, 0, 289250, 100775, 925, 16384⟩ := by
  decide +kernel

theorem context_13_100775_289250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100775 ⟨289250, by decide⟩ :=
  accepted_of_selected 13 100775 ⟨289250, by decide⟩ ⟨13, 2, 0, 289250, 100775, 925, 16384⟩
    (by decide) selected_cut_10715

theorem unmarked_context_12_25193_289251 : frontier 9 ⟨289251, by decide⟩
    (prefixCache 12 25193) (prefixPartial 12 25193) = false := by
  decide +kernel

theorem node_context_12_25193_289251 : EJMOriginalGlobalDAGData.nodes 9 ⟨289251, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨289225, by decide⟩,⟨289246, by decide⟩,⟨289250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25193_289251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25193 ⟨289251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25193
    ⟨289251, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨289225, by decide⟩,⟨289246, by decide⟩,⟨289250, by decide⟩]) unmarked_context_12_25193_289251 node_context_12_25193_289251
  intro a
  fin_cases a
  · exact context_13_100772_3444
  · exact context_13_100773_289225
  · exact context_13_100774_289246
  · exact context_13_100775_289250

theorem selected_cut_10716 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100776) = some ⟨13, 1, 0, 3444, 100776, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100776_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100776 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100776 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100776, 1, 16384⟩
    (by decide) selected_cut_10716

theorem selected_cut_10717 : selected 8 ⟨289267, by decide⟩
    (prefixPartial 13 100777) = some ⟨13, 2, 0, 289267, 100777, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_100777_289267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100777 ⟨289267, by decide⟩ :=
  accepted_of_selected 13 100777 ⟨289267, by decide⟩ ⟨13, 2, 0, 289267, 100777, 1205, 16384⟩
    (by decide) selected_cut_10717

theorem selected_cut_10718 : selected 8 ⟨289286, by decide⟩
    (prefixPartial 13 100778) = some ⟨13, 2, 0, 289286, 100778, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_100778_289286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100778 ⟨289286, by decide⟩ :=
  accepted_of_selected 13 100778 ⟨289286, by decide⟩ ⟨13, 2, 0, 289286, 100778, 2201, 16384⟩
    (by decide) selected_cut_10718

theorem selected_cut_10719 : selected 8 ⟨289292, by decide⟩
    (prefixPartial 13 100779) = some ⟨13, 2, 0, 289292, 100779, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_100779_289292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100779 ⟨289292, by decide⟩ :=
  accepted_of_selected 13 100779 ⟨289292, by decide⟩ ⟨13, 2, 0, 289292, 100779, 1005, 16384⟩
    (by decide) selected_cut_10719

theorem unmarked_context_12_25194_289293 : frontier 9 ⟨289293, by decide⟩
    (prefixCache 12 25194) (prefixPartial 12 25194) = false := by
  decide +kernel

theorem node_context_12_25194_289293 : EJMOriginalGlobalDAGData.nodes 9 ⟨289293, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨289267, by decide⟩,⟨289286, by decide⟩,⟨289292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25194_289293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25194 ⟨289293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25194
    ⟨289293, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨289267, by decide⟩,⟨289286, by decide⟩,⟨289292, by decide⟩]) unmarked_context_12_25194_289293 node_context_12_25194_289293
  intro a
  fin_cases a
  · exact context_13_100776_3444
  · exact context_13_100777_289267
  · exact context_13_100778_289286
  · exact context_13_100779_289292

theorem selected_cut_10720 : selected 9 ⟨289328, by decide⟩
    (prefixPartial 12 25195) = some ⟨12, 2, 0, 289328, 25195, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_25195_289328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25195 ⟨289328, by decide⟩ :=
  accepted_of_selected 12 25195 ⟨289328, by decide⟩ ⟨12, 2, 0, 289328, 25195, 3141, 65536⟩
    (by decide) selected_cut_10720

theorem unmarked_context_11_6298_289329 : frontier 10 ⟨289329, by decide⟩
    (prefixCache 11 6298) (prefixPartial 11 6298) = false := by
  decide +kernel

theorem node_context_11_6298_289329 : EJMOriginalGlobalDAGData.nodes 10 ⟨289329, by decide⟩ =
    .split (coordinate 11) (![⟨289214, by decide⟩,⟨289251, by decide⟩,⟨289293, by decide⟩,⟨289328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6298_289329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6298 ⟨289329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6298
    ⟨289329, by decide⟩ (by decide) (![⟨289214, by decide⟩,⟨289251, by decide⟩,⟨289293, by decide⟩,⟨289328, by decide⟩]) unmarked_context_11_6298_289329 node_context_11_6298_289329
  intro a
  fin_cases a
  · exact context_12_25192_289214
  · exact context_12_25193_289251
  · exact context_12_25194_289293
  · exact context_12_25195_289328

theorem selected_cut_10721 : selected 9 ⟨289364, by decide⟩
    (prefixPartial 12 25196) = some ⟨12, 2, 0, 289364, 25196, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_25196_289364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25196 ⟨289364, by decide⟩ :=
  accepted_of_selected 12 25196 ⟨289364, by decide⟩ ⟨12, 2, 0, 289364, 25196, 2833, 65536⟩
    (by decide) selected_cut_10721

theorem selected_cut_10722 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 100788) = some ⟨13, 1, 0, 3444, 100788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_100788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 100788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 100788, 1, 16384⟩
    (by decide) selected_cut_10722

theorem selected_cut_10723 : selected 8 ⟨289379, by decide⟩
    (prefixPartial 13 100789) = some ⟨13, 2, 0, 289379, 100789, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_100789_289379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100789 ⟨289379, by decide⟩ :=
  accepted_of_selected 13 100789 ⟨289379, by decide⟩ ⟨13, 2, 0, 289379, 100789, 1013, 16384⟩
    (by decide) selected_cut_10723

theorem selected_cut_10724 : selected 8 ⟨289413, by decide⟩
    (prefixPartial 13 100790) = some ⟨13, 2, 0, 289413, 100790, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_100790_289413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100790 ⟨289413, by decide⟩ :=
  accepted_of_selected 13 100790 ⟨289413, by decide⟩ ⟨13, 2, 0, 289413, 100790, 2541, 16384⟩
    (by decide) selected_cut_10724

theorem selected_cut_10725 : selected 8 ⟨289426, by decide⟩
    (prefixPartial 13 100791) = some ⟨13, 2, 0, 289426, 100791, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_100791_289426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100791 ⟨289426, by decide⟩ :=
  accepted_of_selected 13 100791 ⟨289426, by decide⟩ ⟨13, 2, 0, 289426, 100791, 1213, 16384⟩
    (by decide) selected_cut_10725

theorem unmarked_context_12_25197_289427 : frontier 9 ⟨289427, by decide⟩
    (prefixCache 12 25197) (prefixPartial 12 25197) = false := by
  decide +kernel

theorem node_context_12_25197_289427 : EJMOriginalGlobalDAGData.nodes 9 ⟨289427, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨289379, by decide⟩,⟨289413, by decide⟩,⟨289426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25197_289427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25197 ⟨289427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25197
    ⟨289427, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨289379, by decide⟩,⟨289413, by decide⟩,⟨289426, by decide⟩]) unmarked_context_12_25197_289427 node_context_12_25197_289427
  intro a
  fin_cases a
  · exact context_13_100788_3444
  · exact context_13_100789_289379
  · exact context_13_100790_289413
  · exact context_13_100791_289426

theorem selected_cut_10726 : selected 9 ⟨289460, by decide⟩
    (prefixPartial 12 25198) = some ⟨12, 2, 0, 289460, 25198, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_25198_289460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25198 ⟨289460, by decide⟩ :=
  accepted_of_selected 12 25198 ⟨289460, by decide⟩ ⟨12, 2, 0, 289460, 25198, 2777, 65536⟩
    (by decide) selected_cut_10726

theorem selected_cut_10727 : selected 9 ⟨289499, by decide⟩
    (prefixPartial 12 25199) = some ⟨12, 2, 0, 289499, 25199, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_25199_289499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25199 ⟨289499, by decide⟩ :=
  accepted_of_selected 12 25199 ⟨289499, by decide⟩ ⟨12, 2, 0, 289499, 25199, 3609, 65536⟩
    (by decide) selected_cut_10727

theorem unmarked_context_11_6299_289500 : frontier 10 ⟨289500, by decide⟩
    (prefixCache 11 6299) (prefixPartial 11 6299) = false := by
  decide +kernel

theorem node_context_11_6299_289500 : EJMOriginalGlobalDAGData.nodes 10 ⟨289500, by decide⟩ =
    .split (coordinate 11) (![⟨289364, by decide⟩,⟨289427, by decide⟩,⟨289460, by decide⟩,⟨289499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6299_289500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6299 ⟨289500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6299
    ⟨289500, by decide⟩ (by decide) (![⟨289364, by decide⟩,⟨289427, by decide⟩,⟨289460, by decide⟩,⟨289499, by decide⟩]) unmarked_context_11_6299_289500 node_context_11_6299_289500
  intro a
  fin_cases a
  · exact context_12_25196_289364
  · exact context_12_25197_289427
  · exact context_12_25198_289460
  · exact context_12_25199_289499

theorem unmarked_context_10_1574_289501 : frontier 11 ⟨289501, by decide⟩
    (prefixCache 10 1574) (prefixPartial 10 1574) = false := by
  decide +kernel

theorem node_context_10_1574_289501 : EJMOriginalGlobalDAGData.nodes 11 ⟨289501, by decide⟩ =
    .split (coordinate 10) (![⟨289063, by decide⟩,⟨289183, by decide⟩,⟨289329, by decide⟩,⟨289500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1574_289501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1574 ⟨289501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1574
    ⟨289501, by decide⟩ (by decide) (![⟨289063, by decide⟩,⟨289183, by decide⟩,⟨289329, by decide⟩,⟨289500, by decide⟩]) unmarked_context_10_1574_289501 node_context_10_1574_289501
  intro a
  fin_cases a
  · exact context_11_6296_289063
  · exact context_11_6297_289183
  · exact context_11_6298_289329
  · exact context_11_6299_289500

theorem selected_cut_10728 : selected 9 ⟨289521, by decide⟩
    (prefixPartial 12 25200) = some ⟨12, 2, 0, 289521, 25200, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_25200_289521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25200 ⟨289521, by decide⟩ :=
  accepted_of_selected 12 25200 ⟨289521, by decide⟩ ⟨12, 2, 0, 289521, 25200, 2293, 65536⟩
    (by decide) selected_cut_10728

theorem selected_cut_10729 : selected 9 ⟨289576, by decide⟩
    (prefixPartial 12 25201) = some ⟨12, 2, 0, 289576, 25201, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_25201_289576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25201 ⟨289576, by decide⟩ :=
  accepted_of_selected 12 25201 ⟨289576, by decide⟩ ⟨12, 2, 0, 289576, 25201, 3957, 65536⟩
    (by decide) selected_cut_10729

theorem selected_cut_10730 : selected 9 ⟨289600, by decide⟩
    (prefixPartial 12 25202) = some ⟨12, 2, 0, 289600, 25202, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_25202_289600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25202 ⟨289600, by decide⟩ :=
  accepted_of_selected 12 25202 ⟨289600, by decide⟩ ⟨12, 2, 0, 289600, 25202, 2397, 65536⟩
    (by decide) selected_cut_10730

theorem selected_cut_10731 : selected 9 ⟨289638, by decide⟩
    (prefixPartial 12 25203) = some ⟨12, 2, 0, 289638, 25203, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_25203_289638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25203 ⟨289638, by decide⟩ :=
  accepted_of_selected 12 25203 ⟨289638, by decide⟩ ⟨12, 2, 0, 289638, 25203, 3273, 65536⟩
    (by decide) selected_cut_10731

theorem unmarked_context_11_6300_289639 : frontier 10 ⟨289639, by decide⟩
    (prefixCache 11 6300) (prefixPartial 11 6300) = false := by
  decide +kernel

theorem node_context_11_6300_289639 : EJMOriginalGlobalDAGData.nodes 10 ⟨289639, by decide⟩ =
    .split (coordinate 11) (![⟨289521, by decide⟩,⟨289576, by decide⟩,⟨289600, by decide⟩,⟨289638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6300_289639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6300 ⟨289639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6300
    ⟨289639, by decide⟩ (by decide) (![⟨289521, by decide⟩,⟨289576, by decide⟩,⟨289600, by decide⟩,⟨289638, by decide⟩]) unmarked_context_11_6300_289639 node_context_11_6300_289639
  intro a
  fin_cases a
  · exact context_12_25200_289521
  · exact context_12_25201_289576
  · exact context_12_25202_289600
  · exact context_12_25203_289638

theorem selected_cut_10732 : selected 9 ⟨289663, by decide⟩
    (prefixPartial 12 25204) = some ⟨12, 2, 0, 289663, 25204, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_25204_289663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25204 ⟨289663, by decide⟩ :=
  accepted_of_selected 12 25204 ⟨289663, by decide⟩ ⟨12, 2, 0, 289663, 25204, 2305, 65536⟩
    (by decide) selected_cut_10732

theorem selected_cut_10733 : selected 9 ⟨289713, by decide⟩
    (prefixPartial 12 25205) = some ⟨12, 2, 0, 289713, 25205, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_25205_289713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25205 ⟨289713, by decide⟩ :=
  accepted_of_selected 12 25205 ⟨289713, by decide⟩ ⟨12, 2, 0, 289713, 25205, 4077, 65536⟩
    (by decide) selected_cut_10733

theorem selected_cut_10734 : selected 9 ⟨289745, by decide⟩
    (prefixPartial 12 25206) = some ⟨12, 2, 0, 289745, 25206, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_25206_289745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25206 ⟨289745, by decide⟩ :=
  accepted_of_selected 12 25206 ⟨289745, by decide⟩ ⟨12, 2, 0, 289745, 25206, 2661, 65536⟩
    (by decide) selected_cut_10734

theorem selected_cut_10735 : selected 9 ⟨289783, by decide⟩
    (prefixPartial 12 25207) = some ⟨12, 2, 0, 289783, 25207, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_25207_289783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25207 ⟨289783, by decide⟩ :=
  accepted_of_selected 12 25207 ⟨289783, by decide⟩ ⟨12, 2, 0, 289783, 25207, 3405, 65536⟩
    (by decide) selected_cut_10735

theorem unmarked_context_11_6301_289784 : frontier 10 ⟨289784, by decide⟩
    (prefixCache 11 6301) (prefixPartial 11 6301) = false := by
  decide +kernel

theorem node_context_11_6301_289784 : EJMOriginalGlobalDAGData.nodes 10 ⟨289784, by decide⟩ =
    .split (coordinate 11) (![⟨289663, by decide⟩,⟨289713, by decide⟩,⟨289745, by decide⟩,⟨289783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6301_289784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6301 ⟨289784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6301
    ⟨289784, by decide⟩ (by decide) (![⟨289663, by decide⟩,⟨289713, by decide⟩,⟨289745, by decide⟩,⟨289783, by decide⟩]) unmarked_context_11_6301_289784 node_context_11_6301_289784
  intro a
  fin_cases a
  · exact context_12_25204_289663
  · exact context_12_25205_289713
  · exact context_12_25206_289745
  · exact context_12_25207_289783

theorem selected_cut_10736 : selected 9 ⟨289809, by decide⟩
    (prefixPartial 12 25208) = some ⟨12, 2, 0, 289809, 25208, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_25208_289809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25208 ⟨289809, by decide⟩ :=
  accepted_of_selected 12 25208 ⟨289809, by decide⟩ ⟨12, 2, 0, 289809, 25208, 2081, 65536⟩
    (by decide) selected_cut_10736

theorem selected_cut_10737 : selected 9 ⟨289852, by decide⟩
    (prefixPartial 12 25209) = some ⟨12, 2, 0, 289852, 25209, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_25209_289852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25209 ⟨289852, by decide⟩ :=
  accepted_of_selected 12 25209 ⟨289852, by decide⟩ ⟨12, 2, 0, 289852, 25209, 3529, 65536⟩
    (by decide) selected_cut_10737

theorem selected_cut_10738 : selected 9 ⟨289890, by decide⟩
    (prefixPartial 12 25210) = some ⟨12, 2, 0, 289890, 25210, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_25210_289890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25210 ⟨289890, by decide⟩ :=
  accepted_of_selected 12 25210 ⟨289890, by decide⟩ ⟨12, 2, 0, 289890, 25210, 3861, 65536⟩
    (by decide) selected_cut_10738

theorem selected_cut_10739 : selected 9 ⟨289923, by decide⟩
    (prefixPartial 12 25211) = some ⟨12, 2, 0, 289923, 25211, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_25211_289923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25211 ⟨289923, by decide⟩ :=
  accepted_of_selected 12 25211 ⟨289923, by decide⟩ ⟨12, 2, 0, 289923, 25211, 2741, 65536⟩
    (by decide) selected_cut_10739

theorem unmarked_context_11_6302_289924 : frontier 10 ⟨289924, by decide⟩
    (prefixCache 11 6302) (prefixPartial 11 6302) = false := by
  decide +kernel

theorem node_context_11_6302_289924 : EJMOriginalGlobalDAGData.nodes 10 ⟨289924, by decide⟩ =
    .split (coordinate 11) (![⟨289809, by decide⟩,⟨289852, by decide⟩,⟨289890, by decide⟩,⟨289923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6302_289924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6302 ⟨289924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6302
    ⟨289924, by decide⟩ (by decide) (![⟨289809, by decide⟩,⟨289852, by decide⟩,⟨289890, by decide⟩,⟨289923, by decide⟩]) unmarked_context_11_6302_289924 node_context_11_6302_289924
  intro a
  fin_cases a
  · exact context_12_25208_289809
  · exact context_12_25209_289852
  · exact context_12_25210_289890
  · exact context_12_25211_289923

theorem selected_cut_10740 : selected 9 ⟨289946, by decide⟩
    (prefixPartial 12 25212) = some ⟨12, 2, 0, 289946, 25212, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_25212_289946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25212 ⟨289946, by decide⟩ :=
  accepted_of_selected 12 25212 ⟨289946, by decide⟩ ⟨12, 2, 0, 289946, 25212, 2173, 65536⟩
    (by decide) selected_cut_10740

theorem selected_cut_10741 : selected 9 ⟨289993, by decide⟩
    (prefixPartial 12 25213) = some ⟨12, 2, 0, 289993, 25213, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_25213_289993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25213 ⟨289993, by decide⟩ :=
  accepted_of_selected 12 25213 ⟨289993, by decide⟩ ⟨12, 2, 0, 289993, 25213, 3785, 65536⟩
    (by decide) selected_cut_10741

theorem selected_cut_10742 : selected 9 ⟨290023, by decide⟩
    (prefixPartial 12 25214) = some ⟨12, 2, 0, 290023, 25214, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_25214_290023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25214 ⟨290023, by decide⟩ :=
  accepted_of_selected 12 25214 ⟨290023, by decide⟩ ⟨12, 2, 0, 290023, 25214, 2165, 65536⟩
    (by decide) selected_cut_10742

theorem selected_cut_10743 : selected 9 ⟨290052, by decide⟩
    (prefixPartial 12 25215) = some ⟨12, 2, 0, 290052, 25215, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_25215_290052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25215 ⟨290052, by decide⟩ :=
  accepted_of_selected 12 25215 ⟨290052, by decide⟩ ⟨12, 2, 0, 290052, 25215, 2957, 65536⟩
    (by decide) selected_cut_10743

theorem unmarked_context_11_6303_290053 : frontier 10 ⟨290053, by decide⟩
    (prefixCache 11 6303) (prefixPartial 11 6303) = false := by
  decide +kernel

theorem node_context_11_6303_290053 : EJMOriginalGlobalDAGData.nodes 10 ⟨290053, by decide⟩ =
    .split (coordinate 11) (![⟨289946, by decide⟩,⟨289993, by decide⟩,⟨290023, by decide⟩,⟨290052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6303_290053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6303 ⟨290053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6303
    ⟨290053, by decide⟩ (by decide) (![⟨289946, by decide⟩,⟨289993, by decide⟩,⟨290023, by decide⟩,⟨290052, by decide⟩]) unmarked_context_11_6303_290053 node_context_11_6303_290053
  intro a
  fin_cases a
  · exact context_12_25212_289946
  · exact context_12_25213_289993
  · exact context_12_25214_290023
  · exact context_12_25215_290052

theorem unmarked_context_10_1575_290054 : frontier 11 ⟨290054, by decide⟩
    (prefixCache 10 1575) (prefixPartial 10 1575) = false := by
  decide +kernel

theorem node_context_10_1575_290054 : EJMOriginalGlobalDAGData.nodes 11 ⟨290054, by decide⟩ =
    .split (coordinate 10) (![⟨289639, by decide⟩,⟨289784, by decide⟩,⟨289924, by decide⟩,⟨290053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1575_290054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1575 ⟨290054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1575
    ⟨290054, by decide⟩ (by decide) (![⟨289639, by decide⟩,⟨289784, by decide⟩,⟨289924, by decide⟩,⟨290053, by decide⟩]) unmarked_context_10_1575_290054 node_context_10_1575_290054
  intro a
  fin_cases a
  · exact context_11_6300_289639
  · exact context_11_6301_289784
  · exact context_11_6302_289924
  · exact context_11_6303_290053

theorem unmarked_context_9_393_290055 : frontier 12 ⟨290055, by decide⟩
    (prefixCache 9 393) (prefixPartial 9 393) = false := by
  decide +kernel

theorem node_context_9_393_290055 : EJMOriginalGlobalDAGData.nodes 12 ⟨290055, by decide⟩ =
    .split (coordinate 9) (![⟨288287, by decide⟩,⟨288901, by decide⟩,⟨289501, by decide⟩,⟨290054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_393_290055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 393 ⟨290055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 393
    ⟨290055, by decide⟩ (by decide) (![⟨288287, by decide⟩,⟨288901, by decide⟩,⟨289501, by decide⟩,⟨290054, by decide⟩]) unmarked_context_9_393_290055 node_context_9_393_290055
  intro a
  fin_cases a
  · exact context_10_1572_288287
  · exact context_10_1573_288901
  · exact context_10_1574_289501
  · exact context_10_1575_290054

theorem selected_cut_10744 : selected 9 ⟨290056, by decide⟩
    (prefixPartial 12 25216) = some ⟨12, 1, 0, 290056, 25216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25216_290056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25216 ⟨290056, by decide⟩ :=
  accepted_of_selected 12 25216 ⟨290056, by decide⟩ ⟨12, 1, 0, 290056, 25216, 1, 65536⟩
    (by decide) selected_cut_10744

theorem selected_cut_10745 : selected 9 ⟨290090, by decide⟩
    (prefixPartial 12 25217) = some ⟨12, 2, 0, 290090, 25217, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_25217_290090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25217 ⟨290090, by decide⟩ :=
  accepted_of_selected 12 25217 ⟨290090, by decide⟩ ⟨12, 2, 0, 290090, 25217, 2873, 65536⟩
    (by decide) selected_cut_10745

theorem selected_cut_10746 : selected 9 ⟨290118, by decide⟩
    (prefixPartial 12 25218) = some ⟨12, 2, 0, 290118, 25218, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_25218_290118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25218 ⟨290118, by decide⟩ :=
  accepted_of_selected 12 25218 ⟨290118, by decide⟩ ⟨12, 2, 0, 290118, 25218, 2641, 65536⟩
    (by decide) selected_cut_10746

theorem selected_cut_10747 : selected 9 ⟨290149, by decide⟩
    (prefixPartial 12 25219) = some ⟨12, 2, 0, 290149, 25219, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_25219_290149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25219 ⟨290149, by decide⟩ :=
  accepted_of_selected 12 25219 ⟨290149, by decide⟩ ⟨12, 2, 0, 290149, 25219, 3049, 65536⟩
    (by decide) selected_cut_10747

theorem unmarked_context_11_6304_290150 : frontier 10 ⟨290150, by decide⟩
    (prefixCache 11 6304) (prefixPartial 11 6304) = false := by
  decide +kernel

theorem node_context_11_6304_290150 : EJMOriginalGlobalDAGData.nodes 10 ⟨290150, by decide⟩ =
    .split (coordinate 11) (![⟨290056, by decide⟩,⟨290090, by decide⟩,⟨290118, by decide⟩,⟨290149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6304_290150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6304 ⟨290150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6304
    ⟨290150, by decide⟩ (by decide) (![⟨290056, by decide⟩,⟨290090, by decide⟩,⟨290118, by decide⟩,⟨290149, by decide⟩]) unmarked_context_11_6304_290150 node_context_11_6304_290150
  intro a
  fin_cases a
  · exact context_12_25216_290056
  · exact context_12_25217_290090
  · exact context_12_25218_290118
  · exact context_12_25219_290149

theorem selected_cut_10748 : selected 9 ⟨290178, by decide⟩
    (prefixPartial 12 25220) = some ⟨12, 2, 0, 290178, 25220, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_25220_290178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25220 ⟨290178, by decide⟩ :=
  accepted_of_selected 12 25220 ⟨290178, by decide⟩ ⟨12, 2, 0, 290178, 25220, 1881, 65536⟩
    (by decide) selected_cut_10748

theorem selected_cut_10749 : selected 9 ⟨290205, by decide⟩
    (prefixPartial 12 25221) = some ⟨12, 2, 0, 290205, 25221, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_25221_290205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25221 ⟨290205, by decide⟩ :=
  accepted_of_selected 12 25221 ⟨290205, by decide⟩ ⟨12, 2, 0, 290205, 25221, 2077, 65536⟩
    (by decide) selected_cut_10749

theorem selected_cut_10750 : selected 9 ⟨290232, by decide⟩
    (prefixPartial 12 25222) = some ⟨12, 2, 0, 290232, 25222, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_25222_290232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25222 ⟨290232, by decide⟩ :=
  accepted_of_selected 12 25222 ⟨290232, by decide⟩ ⟨12, 2, 0, 290232, 25222, 2073, 65536⟩
    (by decide) selected_cut_10750

theorem selected_cut_10751 : selected 9 ⟨290258, by decide⟩
    (prefixPartial 12 25223) = some ⟨12, 2, 0, 290258, 25223, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_25223_290258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25223 ⟨290258, by decide⟩ :=
  accepted_of_selected 12 25223 ⟨290258, by decide⟩ ⟨12, 2, 0, 290258, 25223, 2401, 65536⟩
    (by decide) selected_cut_10751

theorem unmarked_context_11_6305_290259 : frontier 10 ⟨290259, by decide⟩
    (prefixCache 11 6305) (prefixPartial 11 6305) = false := by
  decide +kernel

theorem node_context_11_6305_290259 : EJMOriginalGlobalDAGData.nodes 10 ⟨290259, by decide⟩ =
    .split (coordinate 11) (![⟨290178, by decide⟩,⟨290205, by decide⟩,⟨290232, by decide⟩,⟨290258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6305_290259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6305 ⟨290259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6305
    ⟨290259, by decide⟩ (by decide) (![⟨290178, by decide⟩,⟨290205, by decide⟩,⟨290232, by decide⟩,⟨290258, by decide⟩]) unmarked_context_11_6305_290259 node_context_11_6305_290259
  intro a
  fin_cases a
  · exact context_12_25220_290178
  · exact context_12_25221_290205
  · exact context_12_25222_290232
  · exact context_12_25223_290258

theorem selected_cut_10752 : selected 9 ⟨290278, by decide⟩
    (prefixPartial 12 25224) = some ⟨12, 2, 0, 290278, 25224, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_25224_290278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25224 ⟨290278, by decide⟩ :=
  accepted_of_selected 12 25224 ⟨290278, by decide⟩ ⟨12, 2, 0, 290278, 25224, 1745, 65536⟩
    (by decide) selected_cut_10752

theorem selected_cut_10753 : selected 9 ⟨290306, by decide⟩
    (prefixPartial 12 25225) = some ⟨12, 2, 0, 290306, 25225, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_25225_290306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25225 ⟨290306, by decide⟩ :=
  accepted_of_selected 12 25225 ⟨290306, by decide⟩ ⟨12, 2, 0, 290306, 25225, 2037, 65536⟩
    (by decide) selected_cut_10753

theorem selected_cut_10754 : selected 9 ⟨290332, by decide⟩
    (prefixPartial 12 25226) = some ⟨12, 2, 0, 290332, 25226, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_25226_290332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25226 ⟨290332, by decide⟩ :=
  accepted_of_selected 12 25226 ⟨290332, by decide⟩ ⟨12, 2, 0, 290332, 25226, 3097, 65536⟩
    (by decide) selected_cut_10754

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
