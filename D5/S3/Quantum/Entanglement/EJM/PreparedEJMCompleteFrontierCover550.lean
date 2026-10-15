/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover549
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_8_4731_1553052 : frontier 13 ⟨1553052, by decide⟩
    (prefixCache 8 4731) (prefixPartial 8 4731) = false := by
  decide +kernel

theorem node_context_8_4731_1553052 : EJMOriginalGlobalDAGData.nodes 13 ⟨1553052, by decide⟩ =
    .split (coordinate 8) (![⟨1552817, by decide⟩,⟨1552933, by decide⟩,⟨1553038, by decide⟩,⟨1553051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4731_1553052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4731 ⟨1553052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4731
    ⟨1553052, by decide⟩ (by decide) (![⟨1552817, by decide⟩,⟨1552933, by decide⟩,⟨1553038, by decide⟩,⟨1553051, by decide⟩]) unmarked_context_8_4731_1553052 node_context_8_4731_1553052
  intro a
  fin_cases a
  · exact context_9_18924_1552817
  · exact context_9_18925_1552933
  · exact context_9_18926_1553038
  · exact context_9_18927_1553051

theorem unmarked_context_7_1182_1553053 : frontier 14 ⟨1553053, by decide⟩
    (prefixCache 7 1182) (prefixPartial 7 1182) = false := by
  decide +kernel

theorem node_context_7_1182_1553053 : EJMOriginalGlobalDAGData.nodes 14 ⟨1553053, by decide⟩ =
    .split (coordinate 7) (![⟨1552032, by decide⟩,⟨1552289, by decide⟩,⟨1552536, by decide⟩,⟨1553052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1182_1553053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1182 ⟨1553053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1182
    ⟨1553053, by decide⟩ (by decide) (![⟨1552032, by decide⟩,⟨1552289, by decide⟩,⟨1552536, by decide⟩,⟨1553052, by decide⟩]) unmarked_context_7_1182_1553053 node_context_7_1182_1553053
  intro a
  fin_cases a
  · exact context_8_4728_1552032
  · exact context_8_4729_1552289
  · exact context_8_4730_1552536
  · exact context_8_4731_1553052

theorem selected_cut_52804 : selected 13 ⟨1553253, by decide⟩
    (prefixPartial 8 4732) = some ⟨8, 2, 0, 1553253, 4732, 3517, 16777216⟩ := by
  decide +kernel

theorem context_8_4732_1553253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4732 ⟨1553253, by decide⟩ :=
  accepted_of_selected 8 4732 ⟨1553253, by decide⟩ ⟨8, 2, 0, 1553253, 4732, 3517, 16777216⟩
    (by decide) selected_cut_52804

theorem selected_cut_52805 : selected 13 ⟨1553460, by decide⟩
    (prefixPartial 8 4733) = some ⟨8, 2, 0, 1553460, 4733, 1925, 16777216⟩ := by
  decide +kernel

theorem context_8_4733_1553460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4733 ⟨1553460, by decide⟩ :=
  accepted_of_selected 8 4733 ⟨1553460, by decide⟩ ⟨8, 2, 0, 1553460, 4733, 1925, 16777216⟩
    (by decide) selected_cut_52805

theorem selected_cut_52806 : selected 12 ⟨1553654, by decide⟩
    (prefixPartial 9 18936) = some ⟨9, 2, 0, 1553654, 18936, 3205, 4194304⟩ := by
  decide +kernel

theorem context_9_18936_1553654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18936 ⟨1553654, by decide⟩ :=
  accepted_of_selected 9 18936 ⟨1553654, by decide⟩ ⟨9, 2, 0, 1553654, 18936, 3205, 4194304⟩
    (by decide) selected_cut_52806

theorem selected_cut_52807 : selected 12 ⟨1553757, by decide⟩
    (prefixPartial 9 18937) = some ⟨9, 2, 0, 1553757, 18937, 1653, 4194304⟩ := by
  decide +kernel

theorem context_9_18937_1553757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18937 ⟨1553757, by decide⟩ :=
  accepted_of_selected 9 18937 ⟨1553757, by decide⟩ ⟨9, 2, 0, 1553757, 18937, 1653, 4194304⟩
    (by decide) selected_cut_52807

theorem selected_cut_52808 : selected 12 ⟨1553814, by decide⟩
    (prefixPartial 9 18938) = some ⟨9, 2, 0, 1553814, 18938, 1621, 4194304⟩ := by
  decide +kernel

theorem context_9_18938_1553814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18938 ⟨1553814, by decide⟩ :=
  accepted_of_selected 9 18938 ⟨1553814, by decide⟩ ⟨9, 2, 0, 1553814, 18938, 1621, 4194304⟩
    (by decide) selected_cut_52808

theorem selected_cut_52809 : selected 12 ⟨1553849, by decide⟩
    (prefixPartial 9 18939) = some ⟨9, 2, 0, 1553849, 18939, 533, 4194304⟩ := by
  decide +kernel

theorem context_9_18939_1553849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18939 ⟨1553849, by decide⟩ :=
  accepted_of_selected 9 18939 ⟨1553849, by decide⟩ ⟨9, 2, 0, 1553849, 18939, 533, 4194304⟩
    (by decide) selected_cut_52809

theorem unmarked_context_8_4734_1553850 : frontier 13 ⟨1553850, by decide⟩
    (prefixCache 8 4734) (prefixPartial 8 4734) = false := by
  decide +kernel

theorem node_context_8_4734_1553850 : EJMOriginalGlobalDAGData.nodes 13 ⟨1553850, by decide⟩ =
    .split (coordinate 8) (![⟨1553654, by decide⟩,⟨1553757, by decide⟩,⟨1553814, by decide⟩,⟨1553849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4734_1553850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4734 ⟨1553850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4734
    ⟨1553850, by decide⟩ (by decide) (![⟨1553654, by decide⟩,⟨1553757, by decide⟩,⟨1553814, by decide⟩,⟨1553849, by decide⟩]) unmarked_context_8_4734_1553850 node_context_8_4734_1553850
  intro a
  fin_cases a
  · exact context_9_18936_1553654
  · exact context_9_18937_1553757
  · exact context_9_18938_1553814
  · exact context_9_18939_1553849

theorem selected_cut_52810 : selected 13 ⟨1553851, by decide⟩
    (prefixPartial 8 4735) = some ⟨8, 1, 0, 1553851, 4735, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4735_1553851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4735 ⟨1553851, by decide⟩ :=
  accepted_of_selected 8 4735 ⟨1553851, by decide⟩ ⟨8, 1, 0, 1553851, 4735, 1, 16777216⟩
    (by decide) selected_cut_52810

theorem unmarked_context_7_1183_1553852 : frontier 14 ⟨1553852, by decide⟩
    (prefixCache 7 1183) (prefixPartial 7 1183) = false := by
  decide +kernel

theorem node_context_7_1183_1553852 : EJMOriginalGlobalDAGData.nodes 14 ⟨1553852, by decide⟩ =
    .split (coordinate 7) (![⟨1553253, by decide⟩,⟨1553460, by decide⟩,⟨1553850, by decide⟩,⟨1553851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1183_1553852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1183 ⟨1553852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1183
    ⟨1553852, by decide⟩ (by decide) (![⟨1553253, by decide⟩,⟨1553460, by decide⟩,⟨1553850, by decide⟩,⟨1553851, by decide⟩]) unmarked_context_7_1183_1553852 node_context_7_1183_1553852
  intro a
  fin_cases a
  · exact context_8_4732_1553253
  · exact context_8_4733_1553460
  · exact context_8_4734_1553850
  · exact context_8_4735_1553851

theorem unmarked_context_6_295_1553853 : frontier 15 ⟨1553853, by decide⟩
    (prefixCache 6 295) (prefixPartial 6 295) = false := by
  decide +kernel

theorem node_context_6_295_1553853 : EJMOriginalGlobalDAGData.nodes 15 ⟨1553853, by decide⟩ =
    .split (coordinate 6) (![⟨1550397, by decide⟩,⟨1551714, by decide⟩,⟨1553053, by decide⟩,⟨1553852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_295_1553853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 295 ⟨1553853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 295
    ⟨1553853, by decide⟩ (by decide) (![⟨1550397, by decide⟩,⟨1551714, by decide⟩,⟨1553053, by decide⟩,⟨1553852, by decide⟩]) unmarked_context_6_295_1553853 node_context_6_295_1553853
  intro a
  fin_cases a
  · exact context_7_1180_1550397
  · exact context_7_1181_1551714
  · exact context_7_1182_1553053
  · exact context_7_1183_1553852

theorem unmarked_context_5_73_1553854 : frontier 16 ⟨1553854, by decide⟩
    (prefixCache 5 73) (prefixPartial 5 73) = false := by
  decide +kernel

theorem node_context_5_73_1553854 : EJMOriginalGlobalDAGData.nodes 16 ⟨1553854, by decide⟩ =
    .split (coordinate 5) (![⟨1549011, by decide⟩,⟨1475984, by decide⟩,⟨1549012, by decide⟩,⟨1553853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_73_1553854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 73 ⟨1553854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 73
    ⟨1553854, by decide⟩ (by decide) (![⟨1549011, by decide⟩,⟨1475984, by decide⟩,⟨1549012, by decide⟩,⟨1553853, by decide⟩]) unmarked_context_5_73_1553854 node_context_5_73_1553854
  intro a
  fin_cases a
  · exact context_6_292_1549011
  · exact context_6_293_1475984
  · exact context_6_294_1549012
  · exact context_6_295_1553853

theorem selected_cut_52811 : selected 15 ⟨1553855, by decide⟩
    (prefixPartial 6 296) = some ⟨6, 1, 0, 1553855, 296, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_296_1553855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 296 ⟨1553855, by decide⟩ :=
  accepted_of_selected 6 296 ⟨1553855, by decide⟩ ⟨6, 1, 0, 1553855, 296, 1, 268435456⟩
    (by decide) selected_cut_52811

theorem selected_cut_52812 : selected 15 ⟨1475984, by decide⟩
    (prefixPartial 6 297) = some ⟨6, 1, 0, 1475984, 297, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_297_1475984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 297 ⟨1475984, by decide⟩ :=
  accepted_of_selected 6 297 ⟨1475984, by decide⟩ ⟨6, 1, 0, 1475984, 297, 1, 268435456⟩
    (by decide) selected_cut_52812

theorem selected_cut_52813 : selected 15 ⟨1553855, by decide⟩
    (prefixPartial 6 298) = some ⟨6, 1, 0, 1553855, 298, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_298_1553855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 298 ⟨1553855, by decide⟩ :=
  accepted_of_selected 6 298 ⟨1553855, by decide⟩ ⟨6, 1, 0, 1553855, 298, 1, 268435456⟩
    (by decide) selected_cut_52813

theorem selected_cut_52814 : selected 13 ⟨1553856, by decide⟩
    (prefixPartial 8 4784) = some ⟨8, 1, 0, 1553856, 4784, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4784_1553856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4784 ⟨1553856, by decide⟩ :=
  accepted_of_selected 8 4784 ⟨1553856, by decide⟩ ⟨8, 1, 0, 1553856, 4784, 1, 16777216⟩
    (by decide) selected_cut_52814

theorem selected_cut_52815 : selected 13 ⟨1554095, by decide⟩
    (prefixPartial 8 4785) = some ⟨8, 2, 0, 1554095, 4785, 3449, 16777216⟩ := by
  decide +kernel

theorem context_8_4785_1554095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4785 ⟨1554095, by decide⟩ :=
  accepted_of_selected 8 4785 ⟨1554095, by decide⟩ ⟨8, 2, 0, 1554095, 4785, 3449, 16777216⟩
    (by decide) selected_cut_52815

theorem selected_cut_52816 : selected 13 ⟨1553856, by decide⟩
    (prefixPartial 8 4786) = some ⟨8, 1, 0, 1553856, 4786, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4786_1553856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4786 ⟨1553856, by decide⟩ :=
  accepted_of_selected 8 4786 ⟨1553856, by decide⟩ ⟨8, 1, 0, 1553856, 4786, 1, 16777216⟩
    (by decide) selected_cut_52816

theorem selected_cut_52817 : selected 13 ⟨1554283, by decide⟩
    (prefixPartial 8 4787) = some ⟨8, 2, 0, 1554283, 4787, 2233, 16777216⟩ := by
  decide +kernel

theorem context_8_4787_1554283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4787 ⟨1554283, by decide⟩ :=
  accepted_of_selected 8 4787 ⟨1554283, by decide⟩ ⟨8, 2, 0, 1554283, 4787, 2233, 16777216⟩
    (by decide) selected_cut_52817

theorem unmarked_context_7_1196_1554284 : frontier 14 ⟨1554284, by decide⟩
    (prefixCache 7 1196) (prefixPartial 7 1196) = false := by
  decide +kernel

theorem node_context_7_1196_1554284 : EJMOriginalGlobalDAGData.nodes 14 ⟨1554284, by decide⟩ =
    .split (coordinate 7) (![⟨1553856, by decide⟩,⟨1554095, by decide⟩,⟨1553856, by decide⟩,⟨1554283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1196_1554284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1196 ⟨1554284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1196
    ⟨1554284, by decide⟩ (by decide) (![⟨1553856, by decide⟩,⟨1554095, by decide⟩,⟨1553856, by decide⟩,⟨1554283, by decide⟩]) unmarked_context_7_1196_1554284 node_context_7_1196_1554284
  intro a
  fin_cases a
  · exact context_8_4784_1553856
  · exact context_8_4785_1554095
  · exact context_8_4786_1553856
  · exact context_8_4787_1554283

theorem selected_cut_52818 : selected 14 ⟨1554552, by decide⟩
    (prefixPartial 7 1197) = some ⟨7, 2, 0, 1554552, 1197, 1841, 67108864⟩ := by
  decide +kernel

theorem context_7_1197_1554552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1197 ⟨1554552, by decide⟩ :=
  accepted_of_selected 7 1197 ⟨1554552, by decide⟩ ⟨7, 2, 0, 1554552, 1197, 1841, 67108864⟩
    (by decide) selected_cut_52818

theorem selected_cut_52819 : selected 14 ⟨1554770, by decide⟩
    (prefixPartial 7 1198) = some ⟨7, 2, 0, 1554770, 1198, 2897, 67108864⟩ := by
  decide +kernel

theorem context_7_1198_1554770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1198 ⟨1554770, by decide⟩ :=
  accepted_of_selected 7 1198 ⟨1554770, by decide⟩ ⟨7, 2, 0, 1554770, 1198, 2897, 67108864⟩
    (by decide) selected_cut_52819

theorem selected_cut_52820 : selected 14 ⟨1554771, by decide⟩
    (prefixPartial 7 1199) = some ⟨7, 2, 0, 1554771, 1199, 5, 67108864⟩ := by
  decide +kernel

theorem context_7_1199_1554771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1199 ⟨1554771, by decide⟩ :=
  accepted_of_selected 7 1199 ⟨1554771, by decide⟩ ⟨7, 2, 0, 1554771, 1199, 5, 67108864⟩
    (by decide) selected_cut_52820

theorem unmarked_context_6_299_1554772 : frontier 15 ⟨1554772, by decide⟩
    (prefixCache 6 299) (prefixPartial 6 299) = false := by
  decide +kernel

theorem node_context_6_299_1554772 : EJMOriginalGlobalDAGData.nodes 15 ⟨1554772, by decide⟩ =
    .split (coordinate 6) (![⟨1554284, by decide⟩,⟨1554552, by decide⟩,⟨1554770, by decide⟩,⟨1554771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_299_1554772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 299 ⟨1554772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 299
    ⟨1554772, by decide⟩ (by decide) (![⟨1554284, by decide⟩,⟨1554552, by decide⟩,⟨1554770, by decide⟩,⟨1554771, by decide⟩]) unmarked_context_6_299_1554772 node_context_6_299_1554772
  intro a
  fin_cases a
  · exact context_7_1196_1554284
  · exact context_7_1197_1554552
  · exact context_7_1198_1554770
  · exact context_7_1199_1554771

theorem unmarked_context_5_74_1554773 : frontier 16 ⟨1554773, by decide⟩
    (prefixCache 5 74) (prefixPartial 5 74) = false := by
  decide +kernel

theorem node_context_5_74_1554773 : EJMOriginalGlobalDAGData.nodes 16 ⟨1554773, by decide⟩ =
    .split (coordinate 5) (![⟨1553855, by decide⟩,⟨1475984, by decide⟩,⟨1553855, by decide⟩,⟨1554772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_74_1554773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 74 ⟨1554773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 74
    ⟨1554773, by decide⟩ (by decide) (![⟨1553855, by decide⟩,⟨1475984, by decide⟩,⟨1553855, by decide⟩,⟨1554772, by decide⟩]) unmarked_context_5_74_1554773 node_context_5_74_1554773
  intro a
  fin_cases a
  · exact context_6_296_1553855
  · exact context_6_297_1475984
  · exact context_6_298_1553855
  · exact context_6_299_1554772

theorem selected_cut_52821 : selected 13 ⟨1487329, by decide⟩
    (prefixPartial 8 4800) = some ⟨8, 1, 0, 1487329, 4800, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4800_1487329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4800 ⟨1487329, by decide⟩ :=
  accepted_of_selected 8 4800 ⟨1487329, by decide⟩ ⟨8, 1, 0, 1487329, 4800, 1, 16777216⟩
    (by decide) selected_cut_52821

theorem selected_cut_52822 : selected 13 ⟨1487329, by decide⟩
    (prefixPartial 8 4801) = some ⟨8, 1, 0, 1487329, 4801, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4801_1487329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4801 ⟨1487329, by decide⟩ :=
  accepted_of_selected 8 4801 ⟨1487329, by decide⟩ ⟨8, 1, 0, 1487329, 4801, 1, 16777216⟩
    (by decide) selected_cut_52822

theorem selected_cut_52823 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 4802) = some ⟨8, 1, 0, 1364555, 4802, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4802_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4802 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 4802 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 4802, 1, 16777216⟩
    (by decide) selected_cut_52823

theorem selected_cut_52824 : selected 12 ⟨1554970, by decide⟩
    (prefixPartial 9 19212) = some ⟨9, 2, 0, 1554970, 19212, 2073, 4194304⟩ := by
  decide +kernel

theorem context_9_19212_1554970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19212 ⟨1554970, by decide⟩ :=
  accepted_of_selected 9 19212 ⟨1554970, by decide⟩ ⟨9, 2, 0, 1554970, 19212, 2073, 4194304⟩
    (by decide) selected_cut_52824

theorem selected_cut_52825 : selected 12 ⟨1555106, by decide⟩
    (prefixPartial 9 19213) = some ⟨9, 2, 0, 1555106, 19213, 1573, 4194304⟩ := by
  decide +kernel

theorem context_9_19213_1555106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19213 ⟨1555106, by decide⟩ :=
  accepted_of_selected 9 19213 ⟨1555106, by decide⟩ ⟨9, 2, 0, 1555106, 19213, 1573, 4194304⟩
    (by decide) selected_cut_52825

theorem selected_cut_52826 : selected 12 ⟨1555135, by decide⟩
    (prefixPartial 9 19214) = some ⟨9, 2, 0, 1555135, 19214, 481, 4194304⟩ := by
  decide +kernel

theorem context_9_19214_1555135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19214 ⟨1555135, by decide⟩ :=
  accepted_of_selected 9 19214 ⟨1555135, by decide⟩ ⟨9, 2, 0, 1555135, 19214, 481, 4194304⟩
    (by decide) selected_cut_52826

theorem selected_cut_52827 : selected 12 ⟨1555142, by decide⟩
    (prefixPartial 9 19215) = some ⟨9, 2, 0, 1555142, 19215, 33, 4194304⟩ := by
  decide +kernel

theorem context_9_19215_1555142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19215 ⟨1555142, by decide⟩ :=
  accepted_of_selected 9 19215 ⟨1555142, by decide⟩ ⟨9, 2, 0, 1555142, 19215, 33, 4194304⟩
    (by decide) selected_cut_52827

theorem unmarked_context_8_4803_1555143 : frontier 13 ⟨1555143, by decide⟩
    (prefixCache 8 4803) (prefixPartial 8 4803) = false := by
  decide +kernel

theorem node_context_8_4803_1555143 : EJMOriginalGlobalDAGData.nodes 13 ⟨1555143, by decide⟩ =
    .split (coordinate 8) (![⟨1554970, by decide⟩,⟨1555106, by decide⟩,⟨1555135, by decide⟩,⟨1555142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4803_1555143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4803 ⟨1555143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4803
    ⟨1555143, by decide⟩ (by decide) (![⟨1554970, by decide⟩,⟨1555106, by decide⟩,⟨1555135, by decide⟩,⟨1555142, by decide⟩]) unmarked_context_8_4803_1555143 node_context_8_4803_1555143
  intro a
  fin_cases a
  · exact context_9_19212_1554970
  · exact context_9_19213_1555106
  · exact context_9_19214_1555135
  · exact context_9_19215_1555142

theorem unmarked_context_7_1200_1555144 : frontier 14 ⟨1555144, by decide⟩
    (prefixCache 7 1200) (prefixPartial 7 1200) = false := by
  decide +kernel

theorem node_context_7_1200_1555144 : EJMOriginalGlobalDAGData.nodes 14 ⟨1555144, by decide⟩ =
    .split (coordinate 7) (![⟨1487329, by decide⟩,⟨1487329, by decide⟩,⟨1364555, by decide⟩,⟨1555143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1200_1555144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1200 ⟨1555144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1200
    ⟨1555144, by decide⟩ (by decide) (![⟨1487329, by decide⟩,⟨1487329, by decide⟩,⟨1364555, by decide⟩,⟨1555143, by decide⟩]) unmarked_context_7_1200_1555144 node_context_7_1200_1555144
  intro a
  fin_cases a
  · exact context_8_4800_1487329
  · exact context_8_4801_1487329
  · exact context_8_4802_1364555
  · exact context_8_4803_1555143

theorem selected_cut_52828 : selected 14 ⟨1539247, by decide⟩
    (prefixPartial 7 1201) = some ⟨7, 1, 0, 1539247, 1201, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_1201_1539247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1201 ⟨1539247, by decide⟩ :=
  accepted_of_selected 7 1201 ⟨1539247, by decide⟩ ⟨7, 1, 0, 1539247, 1201, 1, 67108864⟩
    (by decide) selected_cut_52828

theorem selected_cut_52829 : selected 13 ⟨1555145, by decide⟩
    (prefixPartial 8 4808) = some ⟨8, 1, 0, 1555145, 4808, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4808_1555145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4808 ⟨1555145, by decide⟩ :=
  accepted_of_selected 8 4808 ⟨1555145, by decide⟩ ⟨8, 1, 0, 1555145, 4808, 1, 16777216⟩
    (by decide) selected_cut_52829

theorem selected_cut_52830 : selected 12 ⟨1555242, by decide⟩
    (prefixPartial 9 19236) = some ⟨9, 2, 0, 1555242, 19236, 1221, 4194304⟩ := by
  decide +kernel

theorem context_9_19236_1555242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19236 ⟨1555242, by decide⟩ :=
  accepted_of_selected 9 19236 ⟨1555242, by decide⟩ ⟨9, 2, 0, 1555242, 19236, 1221, 4194304⟩
    (by decide) selected_cut_52830

theorem selected_cut_52831 : selected 12 ⟨1555452, by decide⟩
    (prefixPartial 9 19237) = some ⟨9, 2, 0, 1555452, 19237, 2049, 4194304⟩ := by
  decide +kernel

theorem context_9_19237_1555452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19237 ⟨1555452, by decide⟩ :=
  accepted_of_selected 9 19237 ⟨1555452, by decide⟩ ⟨9, 2, 0, 1555452, 19237, 2049, 4194304⟩
    (by decide) selected_cut_52831

theorem selected_cut_52832 : selected 12 ⟨1555522, by decide⟩
    (prefixPartial 9 19238) = some ⟨9, 2, 0, 1555522, 19238, 829, 4194304⟩ := by
  decide +kernel

theorem context_9_19238_1555522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19238 ⟨1555522, by decide⟩ :=
  accepted_of_selected 9 19238 ⟨1555522, by decide⟩ ⟨9, 2, 0, 1555522, 19238, 829, 4194304⟩
    (by decide) selected_cut_52832

theorem selected_cut_52833 : selected 12 ⟨1555535, by decide⟩
    (prefixPartial 9 19239) = some ⟨9, 2, 0, 1555535, 19239, 81, 4194304⟩ := by
  decide +kernel

theorem context_9_19239_1555535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 19239 ⟨1555535, by decide⟩ :=
  accepted_of_selected 9 19239 ⟨1555535, by decide⟩ ⟨9, 2, 0, 1555535, 19239, 81, 4194304⟩
    (by decide) selected_cut_52833

theorem unmarked_context_8_4809_1555536 : frontier 13 ⟨1555536, by decide⟩
    (prefixCache 8 4809) (prefixPartial 8 4809) = false := by
  decide +kernel

theorem node_context_8_4809_1555536 : EJMOriginalGlobalDAGData.nodes 13 ⟨1555536, by decide⟩ =
    .split (coordinate 8) (![⟨1555242, by decide⟩,⟨1555452, by decide⟩,⟨1555522, by decide⟩,⟨1555535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4809_1555536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4809 ⟨1555536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4809
    ⟨1555536, by decide⟩ (by decide) (![⟨1555242, by decide⟩,⟨1555452, by decide⟩,⟨1555522, by decide⟩,⟨1555535, by decide⟩]) unmarked_context_8_4809_1555536 node_context_8_4809_1555536
  intro a
  fin_cases a
  · exact context_9_19236_1555242
  · exact context_9_19237_1555452
  · exact context_9_19238_1555522
  · exact context_9_19239_1555535

theorem selected_cut_52834 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 4810) = some ⟨8, 1, 0, 1364555, 4810, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4810_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4810 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 4810 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 4810, 1, 16777216⟩
    (by decide) selected_cut_52834

theorem selected_cut_52835 : selected 13 ⟨1555705, by decide⟩
    (prefixPartial 8 4811) = some ⟨8, 2, 0, 1555705, 4811, 2217, 16777216⟩ := by
  decide +kernel

theorem context_8_4811_1555705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4811 ⟨1555705, by decide⟩ :=
  accepted_of_selected 8 4811 ⟨1555705, by decide⟩ ⟨8, 2, 0, 1555705, 4811, 2217, 16777216⟩
    (by decide) selected_cut_52835

theorem unmarked_context_7_1202_1555706 : frontier 14 ⟨1555706, by decide⟩
    (prefixCache 7 1202) (prefixPartial 7 1202) = false := by
  decide +kernel

theorem node_context_7_1202_1555706 : EJMOriginalGlobalDAGData.nodes 14 ⟨1555706, by decide⟩ =
    .split (coordinate 7) (![⟨1555145, by decide⟩,⟨1555536, by decide⟩,⟨1364555, by decide⟩,⟨1555705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1202_1555706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1202 ⟨1555706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1202
    ⟨1555706, by decide⟩ (by decide) (![⟨1555145, by decide⟩,⟨1555536, by decide⟩,⟨1364555, by decide⟩,⟨1555705, by decide⟩]) unmarked_context_7_1202_1555706 node_context_7_1202_1555706
  intro a
  fin_cases a
  · exact context_8_4808_1555145
  · exact context_8_4809_1555536
  · exact context_8_4810_1364555
  · exact context_8_4811_1555705

theorem selected_cut_52836 : selected 13 ⟨1555957, by decide⟩
    (prefixPartial 8 4812) = some ⟨8, 2, 0, 1555957, 4812, 2077, 16777216⟩ := by
  decide +kernel

theorem context_8_4812_1555957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4812 ⟨1555957, by decide⟩ :=
  accepted_of_selected 8 4812 ⟨1555957, by decide⟩ ⟨8, 2, 0, 1555957, 4812, 2077, 16777216⟩
    (by decide) selected_cut_52836

theorem selected_cut_52837 : selected 13 ⟨1556171, by decide⟩
    (prefixPartial 8 4813) = some ⟨8, 2, 0, 1556171, 4813, 2053, 16777216⟩ := by
  decide +kernel

theorem context_8_4813_1556171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4813 ⟨1556171, by decide⟩ :=
  accepted_of_selected 8 4813 ⟨1556171, by decide⟩ ⟨8, 2, 0, 1556171, 4813, 2053, 16777216⟩
    (by decide) selected_cut_52837

theorem selected_cut_52838 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 4814) = some ⟨8, 1, 0, 1364555, 4814, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4814_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4814 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 4814 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 4814, 1, 16777216⟩
    (by decide) selected_cut_52838

theorem selected_cut_52839 : selected 13 ⟨1556412, by decide⟩
    (prefixPartial 8 4815) = some ⟨8, 2, 0, 1556412, 4815, 3393, 16777216⟩ := by
  decide +kernel

theorem context_8_4815_1556412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4815 ⟨1556412, by decide⟩ :=
  accepted_of_selected 8 4815 ⟨1556412, by decide⟩ ⟨8, 2, 0, 1556412, 4815, 3393, 16777216⟩
    (by decide) selected_cut_52839

theorem unmarked_context_7_1203_1556413 : frontier 14 ⟨1556413, by decide⟩
    (prefixCache 7 1203) (prefixPartial 7 1203) = false := by
  decide +kernel

theorem node_context_7_1203_1556413 : EJMOriginalGlobalDAGData.nodes 14 ⟨1556413, by decide⟩ =
    .split (coordinate 7) (![⟨1555957, by decide⟩,⟨1556171, by decide⟩,⟨1364555, by decide⟩,⟨1556412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1203_1556413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1203 ⟨1556413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1203
    ⟨1556413, by decide⟩ (by decide) (![⟨1555957, by decide⟩,⟨1556171, by decide⟩,⟨1364555, by decide⟩,⟨1556412, by decide⟩]) unmarked_context_7_1203_1556413 node_context_7_1203_1556413
  intro a
  fin_cases a
  · exact context_8_4812_1555957
  · exact context_8_4813_1556171
  · exact context_8_4814_1364555
  · exact context_8_4815_1556412

theorem unmarked_context_6_300_1556414 : frontier 15 ⟨1556414, by decide⟩
    (prefixCache 6 300) (prefixPartial 6 300) = false := by
  decide +kernel

theorem node_context_6_300_1556414 : EJMOriginalGlobalDAGData.nodes 15 ⟨1556414, by decide⟩ =
    .split (coordinate 6) (![⟨1555144, by decide⟩,⟨1539247, by decide⟩,⟨1555706, by decide⟩,⟨1556413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_300_1556414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 300 ⟨1556414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 300
    ⟨1556414, by decide⟩ (by decide) (![⟨1555144, by decide⟩,⟨1539247, by decide⟩,⟨1555706, by decide⟩,⟨1556413, by decide⟩]) unmarked_context_6_300_1556414 node_context_6_300_1556414
  intro a
  fin_cases a
  · exact context_7_1200_1555144
  · exact context_7_1201_1539247
  · exact context_7_1202_1555706
  · exact context_7_1203_1556413

theorem selected_cut_52840 : selected 15 ⟨1475984, by decide⟩
    (prefixPartial 6 301) = some ⟨6, 1, 0, 1475984, 301, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_301_1475984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 301 ⟨1475984, by decide⟩ :=
  accepted_of_selected 6 301 ⟨1475984, by decide⟩ ⟨6, 1, 0, 1475984, 301, 1, 268435456⟩
    (by decide) selected_cut_52840

theorem selected_cut_52841 : selected 15 ⟨1549012, by decide⟩
    (prefixPartial 6 302) = some ⟨6, 1, 0, 1549012, 302, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_302_1549012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 302 ⟨1549012, by decide⟩ :=
  accepted_of_selected 6 302 ⟨1549012, by decide⟩ ⟨6, 1, 0, 1549012, 302, 1, 268435456⟩
    (by decide) selected_cut_52841

theorem selected_cut_52842 : selected 13 ⟨1556594, by decide⟩
    (prefixPartial 8 4848) = some ⟨8, 2, 0, 1556594, 4848, 2301, 16777216⟩ := by
  decide +kernel

theorem context_8_4848_1556594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4848 ⟨1556594, by decide⟩ :=
  accepted_of_selected 8 4848 ⟨1556594, by decide⟩ ⟨8, 2, 0, 1556594, 4848, 2301, 16777216⟩
    (by decide) selected_cut_52842

theorem selected_cut_52843 : selected 13 ⟨1556745, by decide⟩
    (prefixPartial 8 4849) = some ⟨8, 2, 0, 1556745, 4849, 1941, 16777216⟩ := by
  decide +kernel

theorem context_8_4849_1556745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4849 ⟨1556745, by decide⟩ :=
  accepted_of_selected 8 4849 ⟨1556745, by decide⟩ ⟨8, 2, 0, 1556745, 4849, 1941, 16777216⟩
    (by decide) selected_cut_52843

theorem selected_cut_52844 : selected 13 ⟨1448345, by decide⟩
    (prefixPartial 8 4850) = some ⟨8, 1, 0, 1448345, 4850, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4850_1448345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4850 ⟨1448345, by decide⟩ :=
  accepted_of_selected 8 4850 ⟨1448345, by decide⟩ ⟨8, 1, 0, 1448345, 4850, 1, 16777216⟩
    (by decide) selected_cut_52844

theorem selected_cut_52845 : selected 13 ⟨1556953, by decide⟩
    (prefixPartial 8 4851) = some ⟨8, 2, 0, 1556953, 4851, 2197, 16777216⟩ := by
  decide +kernel

theorem context_8_4851_1556953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4851 ⟨1556953, by decide⟩ :=
  accepted_of_selected 8 4851 ⟨1556953, by decide⟩ ⟨8, 2, 0, 1556953, 4851, 2197, 16777216⟩
    (by decide) selected_cut_52845

theorem unmarked_context_7_1212_1556954 : frontier 14 ⟨1556954, by decide⟩
    (prefixCache 7 1212) (prefixPartial 7 1212) = false := by
  decide +kernel

theorem node_context_7_1212_1556954 : EJMOriginalGlobalDAGData.nodes 14 ⟨1556954, by decide⟩ =
    .split (coordinate 7) (![⟨1556594, by decide⟩,⟨1556745, by decide⟩,⟨1448345, by decide⟩,⟨1556953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1212_1556954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1212 ⟨1556954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1212
    ⟨1556954, by decide⟩ (by decide) (![⟨1556594, by decide⟩,⟨1556745, by decide⟩,⟨1448345, by decide⟩,⟨1556953, by decide⟩]) unmarked_context_7_1212_1556954 node_context_7_1212_1556954
  intro a
  fin_cases a
  · exact context_8_4848_1556594
  · exact context_8_4849_1556745
  · exact context_8_4850_1448345
  · exact context_8_4851_1556953

theorem selected_cut_52846 : selected 14 ⟨1556955, by decide⟩
    (prefixPartial 7 1213) = some ⟨7, 1, 0, 1556955, 1213, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_1213_1556955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1213 ⟨1556955, by decide⟩ :=
  accepted_of_selected 7 1213 ⟨1556955, by decide⟩ ⟨7, 1, 0, 1556955, 1213, 1, 67108864⟩
    (by decide) selected_cut_52846

theorem selected_cut_52847 : selected 14 ⟨1557190, by decide⟩
    (prefixPartial 7 1214) = some ⟨7, 2, 0, 1557190, 1214, 2325, 67108864⟩ := by
  decide +kernel

theorem context_7_1214_1557190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1214 ⟨1557190, by decide⟩ :=
  accepted_of_selected 7 1214 ⟨1557190, by decide⟩ ⟨7, 2, 0, 1557190, 1214, 2325, 67108864⟩
    (by decide) selected_cut_52847

theorem selected_cut_52848 : selected 14 ⟨1557334, by decide⟩
    (prefixPartial 7 1215) = some ⟨7, 2, 0, 1557334, 1215, 925, 67108864⟩ := by
  decide +kernel

theorem context_7_1215_1557334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1215 ⟨1557334, by decide⟩ :=
  accepted_of_selected 7 1215 ⟨1557334, by decide⟩ ⟨7, 2, 0, 1557334, 1215, 925, 67108864⟩
    (by decide) selected_cut_52848

theorem unmarked_context_6_303_1557335 : frontier 15 ⟨1557335, by decide⟩
    (prefixCache 6 303) (prefixPartial 6 303) = false := by
  decide +kernel

theorem node_context_6_303_1557335 : EJMOriginalGlobalDAGData.nodes 15 ⟨1557335, by decide⟩ =
    .split (coordinate 6) (![⟨1556954, by decide⟩,⟨1556955, by decide⟩,⟨1557190, by decide⟩,⟨1557334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_303_1557335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 303 ⟨1557335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 303
    ⟨1557335, by decide⟩ (by decide) (![⟨1556954, by decide⟩,⟨1556955, by decide⟩,⟨1557190, by decide⟩,⟨1557334, by decide⟩]) unmarked_context_6_303_1557335 node_context_6_303_1557335
  intro a
  fin_cases a
  · exact context_7_1212_1556954
  · exact context_7_1213_1556955
  · exact context_7_1214_1557190
  · exact context_7_1215_1557334

theorem unmarked_context_5_75_1557336 : frontier 16 ⟨1557336, by decide⟩
    (prefixCache 5 75) (prefixPartial 5 75) = false := by
  decide +kernel

theorem node_context_5_75_1557336 : EJMOriginalGlobalDAGData.nodes 16 ⟨1557336, by decide⟩ =
    .split (coordinate 5) (![⟨1556414, by decide⟩,⟨1475984, by decide⟩,⟨1549012, by decide⟩,⟨1557335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_75_1557336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 75 ⟨1557336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 75
    ⟨1557336, by decide⟩ (by decide) (![⟨1556414, by decide⟩,⟨1475984, by decide⟩,⟨1549012, by decide⟩,⟨1557335, by decide⟩]) unmarked_context_5_75_1557336 node_context_5_75_1557336
  intro a
  fin_cases a
  · exact context_6_300_1556414
  · exact context_6_301_1475984
  · exact context_6_302_1549012
  · exact context_6_303_1557335

theorem unmarked_context_4_18_1557337 : frontier 17 ⟨1557337, by decide⟩
    (prefixCache 4 18) (prefixPartial 4 18) = false := by
  decide +kernel

theorem node_context_4_18_1557337 : EJMOriginalGlobalDAGData.nodes 17 ⟨1557337, by decide⟩ =
    .split (coordinate 4) (![⟨1544921, by decide⟩,⟨1553854, by decide⟩,⟨1554773, by decide⟩,⟨1557336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_18_1557337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 18 ⟨1557337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 18
    ⟨1557337, by decide⟩ (by decide) (![⟨1544921, by decide⟩,⟨1553854, by decide⟩,⟨1554773, by decide⟩,⟨1557336, by decide⟩]) unmarked_context_4_18_1557337 node_context_4_18_1557337
  intro a
  fin_cases a
  · exact context_5_72_1544921
  · exact context_5_73_1553854
  · exact context_5_74_1554773
  · exact context_5_75_1557336

theorem selected_cut_52849 : selected 17 ⟨891585, by decide⟩
    (prefixPartial 4 19) = some ⟨4, 1, 0, 891585, 19, 1, 4294967296⟩ := by
  decide +kernel

theorem context_4_19_891585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 19 ⟨891585, by decide⟩ :=
  accepted_of_selected 4 19 ⟨891585, by decide⟩ ⟨4, 1, 0, 891585, 19, 1, 4294967296⟩
    (by decide) selected_cut_52849

theorem unmarked_context_3_4_1557338 : frontier 18 ⟨1557338, by decide⟩
    (prefixCache 3 4) (prefixPartial 3 4) = false := by
  decide +kernel

theorem node_context_3_4_1557338 : EJMOriginalGlobalDAGData.nodes 18 ⟨1557338, by decide⟩ =
    .split (coordinate 3) (![⟨1468245, by decide⟩,⟨1537656, by decide⟩,⟨1557337, by decide⟩,⟨891585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_3_4_1557338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 4 ⟨1557338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 3 4
    ⟨1557338, by decide⟩ (by decide) (![⟨1468245, by decide⟩,⟨1537656, by decide⟩,⟨1557337, by decide⟩,⟨891585, by decide⟩]) unmarked_context_3_4_1557338 node_context_3_4_1557338
  intro a
  fin_cases a
  · exact context_4_16_1468245
  · exact context_4_17_1537656
  · exact context_4_18_1557337
  · exact context_4_19_891585

theorem selected_cut_52850 : selected 18 ⟨1557339, by decide⟩
    (prefixPartial 3 5) = some ⟨3, 1, 0, 1557339, 5, 1, 17179869184⟩ := by
  decide +kernel

theorem context_3_5_1557339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 5 ⟨1557339, by decide⟩ :=
  accepted_of_selected 3 5 ⟨1557339, by decide⟩ ⟨3, 1, 0, 1557339, 5, 1, 17179869184⟩
    (by decide) selected_cut_52850

theorem selected_cut_52851 : selected 17 ⟨1468245, by decide⟩
    (prefixPartial 4 24) = some ⟨4, 1, 0, 1468245, 24, 1, 4294967296⟩ := by
  decide +kernel

theorem context_4_24_1468245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 24 ⟨1468245, by decide⟩ :=
  accepted_of_selected 4 24 ⟨1468245, by decide⟩ ⟨4, 1, 0, 1468245, 24, 1, 4294967296⟩
    (by decide) selected_cut_52851

theorem selected_cut_52852 : selected 16 ⟨891587, by decide⟩
    (prefixPartial 5 100) = some ⟨5, 1, 0, 891587, 100, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_100_891587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 100 ⟨891587, by decide⟩ :=
  accepted_of_selected 5 100 ⟨891587, by decide⟩ ⟨5, 1, 0, 891587, 100, 1, 1073741824⟩
    (by decide) selected_cut_52852

theorem selected_cut_52853 : selected 16 ⟨891587, by decide⟩
    (prefixPartial 5 101) = some ⟨5, 1, 0, 891587, 101, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_101_891587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 101 ⟨891587, by decide⟩ :=
  accepted_of_selected 5 101 ⟨891587, by decide⟩ ⟨5, 1, 0, 891587, 101, 1, 1073741824⟩
    (by decide) selected_cut_52853

theorem selected_cut_52854 : selected 15 ⟨1557954, by decide⟩
    (prefixPartial 6 408) = some ⟨6, 2, 0, 1557954, 408, 2669, 268435456⟩ := by
  decide +kernel

theorem context_6_408_1557954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 408 ⟨1557954, by decide⟩ :=
  accepted_of_selected 6 408 ⟨1557954, by decide⟩ ⟨6, 2, 0, 1557954, 408, 2669, 268435456⟩
    (by decide) selected_cut_52854

theorem selected_cut_52855 : selected 15 ⟨1557955, by decide⟩
    (prefixPartial 6 409) = some ⟨6, 1, 0, 1557955, 409, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_409_1557955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 409 ⟨1557955, by decide⟩ :=
  accepted_of_selected 6 409 ⟨1557955, by decide⟩ ⟨6, 1, 0, 1557955, 409, 1, 268435456⟩
    (by decide) selected_cut_52855

theorem selected_cut_52856 : selected 15 ⟨1558208, by decide⟩
    (prefixPartial 6 410) = some ⟨6, 2, 0, 1558208, 410, 1709, 268435456⟩ := by
  decide +kernel

theorem context_6_410_1558208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 410 ⟨1558208, by decide⟩ :=
  accepted_of_selected 6 410 ⟨1558208, by decide⟩ ⟨6, 2, 0, 1558208, 410, 1709, 268435456⟩
    (by decide) selected_cut_52856

theorem selected_cut_52857 : selected 15 ⟨1558437, by decide⟩
    (prefixPartial 6 411) = some ⟨6, 2, 0, 1558437, 411, 1109, 268435456⟩ := by
  decide +kernel

theorem context_6_411_1558437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 411 ⟨1558437, by decide⟩ :=
  accepted_of_selected 6 411 ⟨1558437, by decide⟩ ⟨6, 2, 0, 1558437, 411, 1109, 268435456⟩
    (by decide) selected_cut_52857

theorem unmarked_context_5_102_1558438 : frontier 16 ⟨1558438, by decide⟩
    (prefixCache 5 102) (prefixPartial 5 102) = false := by
  decide +kernel

theorem node_context_5_102_1558438 : EJMOriginalGlobalDAGData.nodes 16 ⟨1558438, by decide⟩ =
    .split (coordinate 5) (![⟨1557954, by decide⟩,⟨1557955, by decide⟩,⟨1558208, by decide⟩,⟨1558437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_102_1558438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 102 ⟨1558438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 102
    ⟨1558438, by decide⟩ (by decide) (![⟨1557954, by decide⟩,⟨1557955, by decide⟩,⟨1558208, by decide⟩,⟨1558437, by decide⟩]) unmarked_context_5_102_1558438 node_context_5_102_1558438
  intro a
  fin_cases a
  · exact context_6_408_1557954
  · exact context_6_409_1557955
  · exact context_6_410_1558208
  · exact context_6_411_1558437

theorem selected_cut_52858 : selected 16 ⟨1558610, by decide⟩
    (prefixPartial 5 103) = some ⟨5, 2, 0, 1558610, 103, 857, 1073741824⟩ := by
  decide +kernel

theorem context_5_103_1558610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 103 ⟨1558610, by decide⟩ :=
  accepted_of_selected 5 103 ⟨1558610, by decide⟩ ⟨5, 2, 0, 1558610, 103, 857, 1073741824⟩
    (by decide) selected_cut_52858

theorem unmarked_context_4_25_1558611 : frontier 17 ⟨1558611, by decide⟩
    (prefixCache 4 25) (prefixPartial 4 25) = false := by
  decide +kernel

theorem node_context_4_25_1558611 : EJMOriginalGlobalDAGData.nodes 17 ⟨1558611, by decide⟩ =
    .split (coordinate 4) (![⟨891587, by decide⟩,⟨891587, by decide⟩,⟨1558438, by decide⟩,⟨1558610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_25_1558611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 25 ⟨1558611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 25
    ⟨1558611, by decide⟩ (by decide) (![⟨891587, by decide⟩,⟨891587, by decide⟩,⟨1558438, by decide⟩,⟨1558610, by decide⟩]) unmarked_context_4_25_1558611 node_context_4_25_1558611
  intro a
  fin_cases a
  · exact context_5_100_891587
  · exact context_5_101_891587
  · exact context_5_102_1558438
  · exact context_5_103_1558610

theorem selected_cut_52859 : selected 17 ⟨1558762, by decide⟩
    (prefixPartial 4 26) = some ⟨4, 2, 0, 1558762, 26, 777, 4294967296⟩ := by
  decide +kernel

theorem context_4_26_1558762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 26 ⟨1558762, by decide⟩ :=
  accepted_of_selected 4 26 ⟨1558762, by decide⟩ ⟨4, 2, 0, 1558762, 26, 777, 4294967296⟩
    (by decide) selected_cut_52859

theorem selected_cut_52860 : selected 17 ⟨1558767, by decide⟩
    (prefixPartial 4 27) = some ⟨4, 2, 0, 1558767, 27, 9, 4294967296⟩ := by
  decide +kernel

theorem context_4_27_1558767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 27 ⟨1558767, by decide⟩ :=
  accepted_of_selected 4 27 ⟨1558767, by decide⟩ ⟨4, 2, 0, 1558767, 27, 9, 4294967296⟩
    (by decide) selected_cut_52860

theorem unmarked_context_3_6_1558768 : frontier 18 ⟨1558768, by decide⟩
    (prefixCache 3 6) (prefixPartial 3 6) = false := by
  decide +kernel

theorem node_context_3_6_1558768 : EJMOriginalGlobalDAGData.nodes 18 ⟨1558768, by decide⟩ =
    .split (coordinate 3) (![⟨1468245, by decide⟩,⟨1558611, by decide⟩,⟨1558762, by decide⟩,⟨1558767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_3_6_1558768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 6 ⟨1558768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 3 6
    ⟨1558768, by decide⟩ (by decide) (![⟨1468245, by decide⟩,⟨1558611, by decide⟩,⟨1558762, by decide⟩,⟨1558767, by decide⟩]) unmarked_context_3_6_1558768 node_context_3_6_1558768
  intro a
  fin_cases a
  · exact context_4_24_1468245
  · exact context_4_25_1558611
  · exact context_4_26_1558762
  · exact context_4_27_1558767

theorem selected_cut_52861 : selected 18 ⟨1468243, by decide⟩
    (prefixPartial 3 7) = some ⟨3, 1, 0, 1468243, 7, 1, 17179869184⟩ := by
  decide +kernel

theorem context_3_7_1468243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 7 ⟨1468243, by decide⟩ :=
  accepted_of_selected 3 7 ⟨1468243, by decide⟩ ⟨3, 1, 0, 1468243, 7, 1, 17179869184⟩
    (by decide) selected_cut_52861

theorem unmarked_context_2_1_1558769 : frontier 19 ⟨1558769, by decide⟩
    (prefixCache 2 1) (prefixPartial 2 1) = false := by
  decide +kernel

theorem node_context_2_1_1558769 : EJMOriginalGlobalDAGData.nodes 19 ⟨1558769, by decide⟩ =
    .split (coordinate 2) (![⟨1557338, by decide⟩,⟨1557339, by decide⟩,⟨1558768, by decide⟩,⟨1468243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_2_1_1558769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 2 1 ⟨1558769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 2 1
    ⟨1558769, by decide⟩ (by decide) (![⟨1557338, by decide⟩,⟨1557339, by decide⟩,⟨1558768, by decide⟩,⟨1468243, by decide⟩]) unmarked_context_2_1_1558769 node_context_2_1_1558769
  intro a
  fin_cases a
  · exact context_3_4_1557338
  · exact context_3_5_1557339
  · exact context_3_6_1558768
  · exact context_3_7_1468243

theorem selected_cut_52862 : selected 19 ⟨1558770, by decide⟩
    (prefixPartial 2 2) = some ⟨2, 1, 0, 1558770, 2, 1, 68719476736⟩ := by
  decide +kernel

theorem context_2_2_1558770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 2 2 ⟨1558770, by decide⟩ :=
  accepted_of_selected 2 2 ⟨1558770, by decide⟩ ⟨2, 1, 0, 1558770, 2, 1, 68719476736⟩
    (by decide) selected_cut_52862

theorem selected_cut_52863 : selected 19 ⟨1558771, by decide⟩
    (prefixPartial 2 3) = some ⟨2, 1, 0, 1558771, 3, 1, 68719476736⟩ := by
  decide +kernel

theorem context_2_3_1558771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 2 3 ⟨1558771, by decide⟩ :=
  accepted_of_selected 2 3 ⟨1558771, by decide⟩ ⟨2, 1, 0, 1558771, 3, 1, 68719476736⟩
    (by decide) selected_cut_52863

theorem unmarked_context_1_0_1558772 : frontier 20 ⟨1558772, by decide⟩
    (prefixCache 1 0) (prefixPartial 1 0) = false := by
  decide +kernel

theorem node_context_1_0_1558772 : EJMOriginalGlobalDAGData.nodes 20 ⟨1558772, by decide⟩ =
    .split (coordinate 1) (![⟨1468244, by decide⟩,⟨1558769, by decide⟩,⟨1558770, by decide⟩,⟨1558771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_1_0_1558772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 1 0 ⟨1558772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 1 0
    ⟨1558772, by decide⟩ (by decide) (![⟨1468244, by decide⟩,⟨1558769, by decide⟩,⟨1558770, by decide⟩,⟨1558771, by decide⟩]) unmarked_context_1_0_1558772 node_context_1_0_1558772
  intro a
  fin_cases a
  · exact context_2_0_1468244
  · exact context_2_1_1558769
  · exact context_2_2_1558770
  · exact context_2_3_1558771

theorem selected_cut_52864 : selected 20 ⟨1558773, by decide⟩
    (prefixPartial 1 1) = some ⟨1, 1, 0, 1558773, 1, 1, 274877906944⟩ := by
  decide +kernel

theorem context_1_1_1558773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 1 1 ⟨1558773, by decide⟩ :=
  accepted_of_selected 1 1 ⟨1558773, by decide⟩ ⟨1, 1, 0, 1558773, 1, 1, 274877906944⟩
    (by decide) selected_cut_52864

theorem selected_cut_52865 : selected 20 ⟨1558774, by decide⟩
    (prefixPartial 1 2) = some ⟨1, 1, 0, 1558774, 2, 1, 274877906944⟩ := by
  decide +kernel

theorem context_1_2_1558774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 1 2 ⟨1558774, by decide⟩ :=
  accepted_of_selected 1 2 ⟨1558774, by decide⟩ ⟨1, 1, 0, 1558774, 2, 1, 274877906944⟩
    (by decide) selected_cut_52865

theorem selected_cut_52866 : selected 20 ⟨1558775, by decide⟩
    (prefixPartial 1 3) = some ⟨1, 1, 0, 1558775, 3, 1, 274877906944⟩ := by
  decide +kernel

theorem context_1_3_1558775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 1 3 ⟨1558775, by decide⟩ :=
  accepted_of_selected 1 3 ⟨1558775, by decide⟩ ⟨1, 1, 0, 1558775, 3, 1, 274877906944⟩
    (by decide) selected_cut_52866

theorem unmarked_context_0_0_1558776 : frontier 21 ⟨1558776, by decide⟩
    (prefixCache 0 0) (prefixPartial 0 0) = false := by
  decide +kernel

theorem node_context_0_0_1558776 : EJMOriginalGlobalDAGData.nodes 21 ⟨1558776, by decide⟩ =
    .split (coordinate 0) (![⟨1558772, by decide⟩,⟨1558773, by decide⟩,⟨1558774, by decide⟩,⟨1558775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_0_0_1558776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 0 0 ⟨1558776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 0 0
    ⟨1558776, by decide⟩ (by decide) (![⟨1558772, by decide⟩,⟨1558773, by decide⟩,⟨1558774, by decide⟩,⟨1558775, by decide⟩]) unmarked_context_0_0_1558776 node_context_0_0_1558776
  intro a
  fin_cases a
  · exact context_1_0_1558772
  · exact context_1_1_1558773
  · exact context_1_2_1558774
  · exact context_1_3_1558775

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
