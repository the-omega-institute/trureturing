/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover272
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26212 : selected 8 ⟨662920, by decide⟩
    (prefixPartial 13 354553) = some ⟨13, 2, 0, 662920, 354553, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_354553_662920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354553 ⟨662920, by decide⟩ :=
  accepted_of_selected 13 354553 ⟨662920, by decide⟩ ⟨13, 2, 0, 662920, 354553, 2553, 16384⟩
    (by decide) selected_cut_26212

theorem selected_cut_26213 : selected 8 ⟨662952, by decide⟩
    (prefixPartial 13 354554) = some ⟨13, 2, 0, 662952, 354554, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_354554_662952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354554 ⟨662952, by decide⟩ :=
  accepted_of_selected 13 354554 ⟨662952, by decide⟩ ⟨13, 2, 0, 662952, 354554, 1633, 16384⟩
    (by decide) selected_cut_26213

theorem selected_cut_26214 : selected 8 ⟨662958, by decide⟩
    (prefixPartial 13 354555) = some ⟨13, 2, 0, 662958, 354555, 857, 16384⟩ := by
  decide +kernel

theorem context_13_354555_662958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354555 ⟨662958, by decide⟩ :=
  accepted_of_selected 13 354555 ⟨662958, by decide⟩ ⟨13, 2, 0, 662958, 354555, 857, 16384⟩
    (by decide) selected_cut_26214

theorem unmarked_context_12_88638_662959 : frontier 9 ⟨662959, by decide⟩
    (prefixCache 12 88638) (prefixPartial 12 88638) = false := by
  decide +kernel

theorem node_context_12_88638_662959 : EJMOriginalGlobalDAGData.nodes 9 ⟨662959, by decide⟩ =
    .split (coordinate 12) (![⟨662880, by decide⟩,⟨662920, by decide⟩,⟨662952, by decide⟩,⟨662958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88638_662959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88638 ⟨662959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88638
    ⟨662959, by decide⟩ (by decide) (![⟨662880, by decide⟩,⟨662920, by decide⟩,⟨662952, by decide⟩,⟨662958, by decide⟩]) unmarked_context_12_88638_662959 node_context_12_88638_662959
  intro a
  fin_cases a
  · exact context_13_354552_662880
  · exact context_13_354553_662920
  · exact context_13_354554_662952
  · exact context_13_354555_662958

theorem selected_cut_26215 : selected 8 ⟨662964, by decide⟩
    (prefixPartial 13 354556) = some ⟨13, 2, 0, 662964, 354556, 77, 16384⟩ := by
  decide +kernel

theorem context_13_354556_662964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354556 ⟨662964, by decide⟩ :=
  accepted_of_selected 13 354556 ⟨662964, by decide⟩ ⟨13, 2, 0, 662964, 354556, 77, 16384⟩
    (by decide) selected_cut_26215

theorem selected_cut_26216 : selected 8 ⟨663010, by decide⟩
    (prefixPartial 13 354557) = some ⟨13, 2, 0, 663010, 354557, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_354557_663010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354557 ⟨663010, by decide⟩ :=
  accepted_of_selected 13 354557 ⟨663010, by decide⟩ ⟨13, 2, 0, 663010, 354557, 2653, 16384⟩
    (by decide) selected_cut_26216

theorem selected_cut_26217 : selected 8 ⟨663030, by decide⟩
    (prefixPartial 13 354558) = some ⟨13, 2, 0, 663030, 354558, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_354558_663030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354558 ⟨663030, by decide⟩ :=
  accepted_of_selected 13 354558 ⟨663030, by decide⟩ ⟨13, 2, 0, 663030, 354558, 1841, 16384⟩
    (by decide) selected_cut_26217

theorem selected_cut_26218 : selected 8 ⟨663038, by decide⟩
    (prefixPartial 13 354559) = some ⟨13, 2, 0, 663038, 354559, 929, 16384⟩ := by
  decide +kernel

theorem context_13_354559_663038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354559 ⟨663038, by decide⟩ :=
  accepted_of_selected 13 354559 ⟨663038, by decide⟩ ⟨13, 2, 0, 663038, 354559, 929, 16384⟩
    (by decide) selected_cut_26218

theorem unmarked_context_12_88639_663039 : frontier 9 ⟨663039, by decide⟩
    (prefixCache 12 88639) (prefixPartial 12 88639) = false := by
  decide +kernel

theorem node_context_12_88639_663039 : EJMOriginalGlobalDAGData.nodes 9 ⟨663039, by decide⟩ =
    .split (coordinate 12) (![⟨662964, by decide⟩,⟨663010, by decide⟩,⟨663030, by decide⟩,⟨663038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88639_663039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88639 ⟨663039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88639
    ⟨663039, by decide⟩ (by decide) (![⟨662964, by decide⟩,⟨663010, by decide⟩,⟨663030, by decide⟩,⟨663038, by decide⟩]) unmarked_context_12_88639_663039 node_context_12_88639_663039
  intro a
  fin_cases a
  · exact context_13_354556_662964
  · exact context_13_354557_663010
  · exact context_13_354558_663030
  · exact context_13_354559_663038

theorem unmarked_context_11_22159_663040 : frontier 10 ⟨663040, by decide⟩
    (prefixCache 11 22159) (prefixPartial 11 22159) = false := by
  decide +kernel

theorem node_context_11_22159_663040 : EJMOriginalGlobalDAGData.nodes 10 ⟨663040, by decide⟩ =
    .split (coordinate 11) (![⟨662814, by decide⟩,⟨662875, by decide⟩,⟨662959, by decide⟩,⟨663039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22159_663040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22159 ⟨663040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22159
    ⟨663040, by decide⟩ (by decide) (![⟨662814, by decide⟩,⟨662875, by decide⟩,⟨662959, by decide⟩,⟨663039, by decide⟩]) unmarked_context_11_22159_663040 node_context_11_22159_663040
  intro a
  fin_cases a
  · exact context_12_88636_662814
  · exact context_12_88637_662875
  · exact context_12_88638_662959
  · exact context_12_88639_663039

theorem unmarked_context_10_5539_663041 : frontier 11 ⟨663041, by decide⟩
    (prefixCache 10 5539) (prefixPartial 10 5539) = false := by
  decide +kernel

theorem node_context_10_5539_663041 : EJMOriginalGlobalDAGData.nodes 11 ⟨663041, by decide⟩ =
    .split (coordinate 10) (![⟨662242, by decide⟩,⟨662534, by decide⟩,⟨662734, by decide⟩,⟨663040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5539_663041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5539 ⟨663041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5539
    ⟨663041, by decide⟩ (by decide) (![⟨662242, by decide⟩,⟨662534, by decide⟩,⟨662734, by decide⟩,⟨663040, by decide⟩]) unmarked_context_10_5539_663041 node_context_10_5539_663041
  intro a
  fin_cases a
  · exact context_11_22156_662242
  · exact context_11_22157_662534
  · exact context_11_22158_662734
  · exact context_11_22159_663040

theorem unmarked_context_9_1384_663042 : frontier 12 ⟨663042, by decide⟩
    (prefixCache 9 1384) (prefixPartial 9 1384) = false := by
  decide +kernel

theorem node_context_9_1384_663042 : EJMOriginalGlobalDAGData.nodes 12 ⟨663042, by decide⟩ =
    .split (coordinate 9) (![⟨659648, by decide⟩,⟨661150, by decide⟩,⟨661945, by decide⟩,⟨663041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1384_663042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1384 ⟨663042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1384
    ⟨663042, by decide⟩ (by decide) (![⟨659648, by decide⟩,⟨661150, by decide⟩,⟨661945, by decide⟩,⟨663041, by decide⟩]) unmarked_context_9_1384_663042 node_context_9_1384_663042
  intro a
  fin_cases a
  · exact context_10_5536_659648
  · exact context_10_5537_661150
  · exact context_10_5538_661945
  · exact context_10_5539_663041

theorem selected_cut_26219 : selected 9 ⟨663088, by decide⟩
    (prefixPartial 12 88640) = some ⟨12, 2, 0, 663088, 88640, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_88640_663088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88640 ⟨663088, by decide⟩ :=
  accepted_of_selected 12 88640 ⟨663088, by decide⟩ ⟨12, 2, 0, 663088, 88640, 3869, 65536⟩
    (by decide) selected_cut_26219

theorem selected_cut_26220 : selected 9 ⟨663149, by decide⟩
    (prefixPartial 12 88641) = some ⟨12, 2, 0, 663149, 88641, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_88641_663149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88641 ⟨663149, by decide⟩ :=
  accepted_of_selected 12 88641 ⟨663149, by decide⟩ ⟨12, 2, 0, 663149, 88641, 1645, 65536⟩
    (by decide) selected_cut_26220

theorem selected_cut_26221 : selected 9 ⟨663202, by decide⟩
    (prefixPartial 12 88642) = some ⟨12, 2, 0, 663202, 88642, 4025, 65536⟩ := by
  decide +kernel

theorem context_12_88642_663202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88642 ⟨663202, by decide⟩ :=
  accepted_of_selected 12 88642 ⟨663202, by decide⟩ ⟨12, 2, 0, 663202, 88642, 4025, 65536⟩
    (by decide) selected_cut_26221

theorem selected_cut_26222 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354572) = some ⟨13, 1, 0, 3444, 354572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354572, 1, 16384⟩
    (by decide) selected_cut_26222

theorem selected_cut_26223 : selected 8 ⟨663240, by decide⟩
    (prefixPartial 13 354573) = some ⟨13, 2, 0, 663240, 354573, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_354573_663240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354573 ⟨663240, by decide⟩ :=
  accepted_of_selected 13 354573 ⟨663240, by decide⟩ ⟨13, 2, 0, 663240, 354573, 2541, 16384⟩
    (by decide) selected_cut_26223

theorem selected_cut_26224 : selected 8 ⟨663258, by decide⟩
    (prefixPartial 13 354574) = some ⟨13, 2, 0, 663258, 354574, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_354574_663258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354574 ⟨663258, by decide⟩ :=
  accepted_of_selected 13 354574 ⟨663258, by decide⟩ ⟨13, 2, 0, 663258, 354574, 1165, 16384⟩
    (by decide) selected_cut_26224

theorem selected_cut_26225 : selected 8 ⟨663266, by decide⟩
    (prefixPartial 13 354575) = some ⟨13, 2, 0, 663266, 354575, 769, 16384⟩ := by
  decide +kernel

theorem context_13_354575_663266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354575 ⟨663266, by decide⟩ :=
  accepted_of_selected 13 354575 ⟨663266, by decide⟩ ⟨13, 2, 0, 663266, 354575, 769, 16384⟩
    (by decide) selected_cut_26225

theorem unmarked_context_12_88643_663267 : frontier 9 ⟨663267, by decide⟩
    (prefixCache 12 88643) (prefixPartial 12 88643) = false := by
  decide +kernel

theorem node_context_12_88643_663267 : EJMOriginalGlobalDAGData.nodes 9 ⟨663267, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨663240, by decide⟩,⟨663258, by decide⟩,⟨663266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88643_663267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88643 ⟨663267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88643
    ⟨663267, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨663240, by decide⟩,⟨663258, by decide⟩,⟨663266, by decide⟩]) unmarked_context_12_88643_663267 node_context_12_88643_663267
  intro a
  fin_cases a
  · exact context_13_354572_3444
  · exact context_13_354573_663240
  · exact context_13_354574_663258
  · exact context_13_354575_663266

theorem unmarked_context_11_22160_663268 : frontier 10 ⟨663268, by decide⟩
    (prefixCache 11 22160) (prefixPartial 11 22160) = false := by
  decide +kernel

theorem node_context_11_22160_663268 : EJMOriginalGlobalDAGData.nodes 10 ⟨663268, by decide⟩ =
    .split (coordinate 11) (![⟨663088, by decide⟩,⟨663149, by decide⟩,⟨663202, by decide⟩,⟨663267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22160_663268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22160 ⟨663268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22160
    ⟨663268, by decide⟩ (by decide) (![⟨663088, by decide⟩,⟨663149, by decide⟩,⟨663202, by decide⟩,⟨663267, by decide⟩]) unmarked_context_11_22160_663268 node_context_11_22160_663268
  intro a
  fin_cases a
  · exact context_12_88640_663088
  · exact context_12_88641_663149
  · exact context_12_88642_663202
  · exact context_12_88643_663267

theorem selected_cut_26226 : selected 9 ⟨663326, by decide⟩
    (prefixPartial 12 88644) = some ⟨12, 2, 0, 663326, 88644, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_88644_663326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88644 ⟨663326, by decide⟩ :=
  accepted_of_selected 12 88644 ⟨663326, by decide⟩ ⟨12, 2, 0, 663326, 88644, 3981, 65536⟩
    (by decide) selected_cut_26226

theorem selected_cut_26227 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 88645) = some ⟨12, 1, 0, 170504, 88645, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88645_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88645 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 88645 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 88645, 1, 65536⟩
    (by decide) selected_cut_26227

theorem selected_cut_26228 : selected 9 ⟨663388, by decide⟩
    (prefixPartial 12 88646) = some ⟨12, 2, 0, 663388, 88646, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_88646_663388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88646 ⟨663388, by decide⟩ :=
  accepted_of_selected 12 88646 ⟨663388, by decide⟩ ⟨12, 2, 0, 663388, 88646, 3713, 65536⟩
    (by decide) selected_cut_26228

theorem selected_cut_26229 : selected 9 ⟨663442, by decide⟩
    (prefixPartial 12 88647) = some ⟨12, 2, 0, 663442, 88647, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_88647_663442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88647 ⟨663442, by decide⟩ :=
  accepted_of_selected 12 88647 ⟨663442, by decide⟩ ⟨12, 2, 0, 663442, 88647, 3885, 65536⟩
    (by decide) selected_cut_26229

theorem unmarked_context_11_22161_663443 : frontier 10 ⟨663443, by decide⟩
    (prefixCache 11 22161) (prefixPartial 11 22161) = false := by
  decide +kernel

theorem node_context_11_22161_663443 : EJMOriginalGlobalDAGData.nodes 10 ⟨663443, by decide⟩ =
    .split (coordinate 11) (![⟨663326, by decide⟩,⟨170504, by decide⟩,⟨663388, by decide⟩,⟨663442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22161_663443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22161 ⟨663443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22161
    ⟨663443, by decide⟩ (by decide) (![⟨663326, by decide⟩,⟨170504, by decide⟩,⟨663388, by decide⟩,⟨663442, by decide⟩]) unmarked_context_11_22161_663443 node_context_11_22161_663443
  intro a
  fin_cases a
  · exact context_12_88644_663326
  · exact context_12_88645_170504
  · exact context_12_88646_663388
  · exact context_12_88647_663442

theorem selected_cut_26230 : selected 9 ⟨663492, by decide⟩
    (prefixPartial 12 88648) = some ⟨12, 2, 0, 663492, 88648, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_88648_663492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88648 ⟨663492, by decide⟩ :=
  accepted_of_selected 12 88648 ⟨663492, by decide⟩ ⟨12, 2, 0, 663492, 88648, 3469, 65536⟩
    (by decide) selected_cut_26230

theorem selected_cut_26231 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354596) = some ⟨13, 1, 0, 3444, 354596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354596, 1, 16384⟩
    (by decide) selected_cut_26231

theorem selected_cut_26232 : selected 8 ⟨663529, by decide⟩
    (prefixPartial 13 354597) = some ⟨13, 2, 0, 663529, 354597, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_354597_663529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354597 ⟨663529, by decide⟩ :=
  accepted_of_selected 13 354597 ⟨663529, by decide⟩ ⟨13, 2, 0, 663529, 354597, 2189, 16384⟩
    (by decide) selected_cut_26232

theorem selected_cut_26233 : selected 8 ⟨663546, by decide⟩
    (prefixPartial 13 354598) = some ⟨13, 2, 0, 663546, 354598, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_354598_663546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354598 ⟨663546, by decide⟩ :=
  accepted_of_selected 13 354598 ⟨663546, by decide⟩ ⟨13, 2, 0, 663546, 354598, 1581, 16384⟩
    (by decide) selected_cut_26233

theorem selected_cut_26234 : selected 8 ⟨663552, by decide⟩
    (prefixPartial 13 354599) = some ⟨13, 2, 0, 663552, 354599, 989, 16384⟩ := by
  decide +kernel

theorem context_13_354599_663552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354599 ⟨663552, by decide⟩ :=
  accepted_of_selected 13 354599 ⟨663552, by decide⟩ ⟨13, 2, 0, 663552, 354599, 989, 16384⟩
    (by decide) selected_cut_26234

theorem unmarked_context_12_88649_663553 : frontier 9 ⟨663553, by decide⟩
    (prefixCache 12 88649) (prefixPartial 12 88649) = false := by
  decide +kernel

theorem node_context_12_88649_663553 : EJMOriginalGlobalDAGData.nodes 9 ⟨663553, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨663529, by decide⟩,⟨663546, by decide⟩,⟨663552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88649_663553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88649 ⟨663553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88649
    ⟨663553, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨663529, by decide⟩,⟨663546, by decide⟩,⟨663552, by decide⟩]) unmarked_context_12_88649_663553 node_context_12_88649_663553
  intro a
  fin_cases a
  · exact context_13_354596_3444
  · exact context_13_354597_663529
  · exact context_13_354598_663546
  · exact context_13_354599_663552

theorem selected_cut_26235 : selected 9 ⟨663554, by decide⟩
    (prefixPartial 12 88650) = some ⟨12, 1, 0, 663554, 88650, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88650_663554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88650 ⟨663554, by decide⟩ :=
  accepted_of_selected 12 88650 ⟨663554, by decide⟩ ⟨12, 1, 0, 663554, 88650, 1, 65536⟩
    (by decide) selected_cut_26235

theorem selected_cut_26236 : selected 9 ⟨663607, by decide⟩
    (prefixPartial 12 88651) = some ⟨12, 2, 0, 663607, 88651, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_88651_663607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88651 ⟨663607, by decide⟩ :=
  accepted_of_selected 12 88651 ⟨663607, by decide⟩ ⟨12, 2, 0, 663607, 88651, 3705, 65536⟩
    (by decide) selected_cut_26236

theorem unmarked_context_11_22162_663608 : frontier 10 ⟨663608, by decide⟩
    (prefixCache 11 22162) (prefixPartial 11 22162) = false := by
  decide +kernel

theorem node_context_11_22162_663608 : EJMOriginalGlobalDAGData.nodes 10 ⟨663608, by decide⟩ =
    .split (coordinate 11) (![⟨663492, by decide⟩,⟨663553, by decide⟩,⟨663554, by decide⟩,⟨663607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22162_663608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22162 ⟨663608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22162
    ⟨663608, by decide⟩ (by decide) (![⟨663492, by decide⟩,⟨663553, by decide⟩,⟨663554, by decide⟩,⟨663607, by decide⟩]) unmarked_context_11_22162_663608 node_context_11_22162_663608
  intro a
  fin_cases a
  · exact context_12_88648_663492
  · exact context_12_88649_663553
  · exact context_12_88650_663554
  · exact context_12_88651_663607

theorem selected_cut_26237 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354608) = some ⟨13, 1, 0, 3444, 354608, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354608_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354608 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354608 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354608, 1, 16384⟩
    (by decide) selected_cut_26237

theorem selected_cut_26238 : selected 8 ⟨663638, by decide⟩
    (prefixPartial 13 354609) = some ⟨13, 2, 0, 663638, 354609, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_354609_663638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354609 ⟨663638, by decide⟩ :=
  accepted_of_selected 13 354609 ⟨663638, by decide⟩ ⟨13, 2, 0, 663638, 354609, 1969, 16384⟩
    (by decide) selected_cut_26238

theorem selected_cut_26239 : selected 8 ⟨663658, by decide⟩
    (prefixPartial 13 354610) = some ⟨13, 2, 0, 663658, 354610, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_354610_663658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354610 ⟨663658, by decide⟩ :=
  accepted_of_selected 13 354610 ⟨663658, by decide⟩ ⟨13, 2, 0, 663658, 354610, 1565, 16384⟩
    (by decide) selected_cut_26239

theorem selected_cut_26240 : selected 8 ⟨663666, by decide⟩
    (prefixPartial 13 354611) = some ⟨13, 2, 0, 663666, 354611, 969, 16384⟩ := by
  decide +kernel

theorem context_13_354611_663666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354611 ⟨663666, by decide⟩ :=
  accepted_of_selected 13 354611 ⟨663666, by decide⟩ ⟨13, 2, 0, 663666, 354611, 969, 16384⟩
    (by decide) selected_cut_26240

theorem unmarked_context_12_88652_663667 : frontier 9 ⟨663667, by decide⟩
    (prefixCache 12 88652) (prefixPartial 12 88652) = false := by
  decide +kernel

theorem node_context_12_88652_663667 : EJMOriginalGlobalDAGData.nodes 9 ⟨663667, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨663638, by decide⟩,⟨663658, by decide⟩,⟨663666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88652_663667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88652 ⟨663667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88652
    ⟨663667, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨663638, by decide⟩,⟨663658, by decide⟩,⟨663666, by decide⟩]) unmarked_context_12_88652_663667 node_context_12_88652_663667
  intro a
  fin_cases a
  · exact context_13_354608_3444
  · exact context_13_354609_663638
  · exact context_13_354610_663658
  · exact context_13_354611_663666

theorem selected_cut_26241 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354612) = some ⟨13, 1, 0, 3444, 354612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354612, 1, 16384⟩
    (by decide) selected_cut_26241

theorem selected_cut_26242 : selected 8 ⟨663710, by decide⟩
    (prefixPartial 13 354613) = some ⟨13, 2, 0, 663710, 354613, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_354613_663710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354613 ⟨663710, by decide⟩ :=
  accepted_of_selected 13 354613 ⟨663710, by decide⟩ ⟨13, 2, 0, 663710, 354613, 2501, 16384⟩
    (by decide) selected_cut_26242

theorem selected_cut_26243 : selected 8 ⟨663730, by decide⟩
    (prefixPartial 13 354614) = some ⟨13, 2, 0, 663730, 354614, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_354614_663730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354614 ⟨663730, by decide⟩ :=
  accepted_of_selected 13 354614 ⟨663730, by decide⟩ ⟨13, 2, 0, 663730, 354614, 1741, 16384⟩
    (by decide) selected_cut_26243

theorem selected_cut_26244 : selected 8 ⟨663748, by decide⟩
    (prefixPartial 13 354615) = some ⟨13, 2, 0, 663748, 354615, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_354615_663748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354615 ⟨663748, by decide⟩ :=
  accepted_of_selected 13 354615 ⟨663748, by decide⟩ ⟨13, 2, 0, 663748, 354615, 1229, 16384⟩
    (by decide) selected_cut_26244

theorem unmarked_context_12_88653_663749 : frontier 9 ⟨663749, by decide⟩
    (prefixCache 12 88653) (prefixPartial 12 88653) = false := by
  decide +kernel

theorem node_context_12_88653_663749 : EJMOriginalGlobalDAGData.nodes 9 ⟨663749, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨663710, by decide⟩,⟨663730, by decide⟩,⟨663748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88653_663749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88653 ⟨663749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88653
    ⟨663749, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨663710, by decide⟩,⟨663730, by decide⟩,⟨663748, by decide⟩]) unmarked_context_12_88653_663749 node_context_12_88653_663749
  intro a
  fin_cases a
  · exact context_13_354612_3444
  · exact context_13_354613_663710
  · exact context_13_354614_663730
  · exact context_13_354615_663748

theorem selected_cut_26245 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354616) = some ⟨13, 1, 0, 3444, 354616, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354616_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354616 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354616 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354616, 1, 16384⟩
    (by decide) selected_cut_26245

theorem selected_cut_26246 : selected 8 ⟨663774, by decide⟩
    (prefixPartial 13 354617) = some ⟨13, 2, 0, 663774, 354617, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_354617_663774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354617 ⟨663774, by decide⟩ :=
  accepted_of_selected 13 354617 ⟨663774, by decide⟩ ⟨13, 2, 0, 663774, 354617, 1837, 16384⟩
    (by decide) selected_cut_26246

theorem selected_cut_26247 : selected 8 ⟨663793, by decide⟩
    (prefixPartial 13 354618) = some ⟨13, 2, 0, 663793, 354618, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_354618_663793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354618 ⟨663793, by decide⟩ :=
  accepted_of_selected 13 354618 ⟨663793, by decide⟩ ⟨13, 2, 0, 663793, 354618, 1513, 16384⟩
    (by decide) selected_cut_26247

theorem selected_cut_26248 : selected 8 ⟨663802, by decide⟩
    (prefixPartial 13 354619) = some ⟨13, 2, 0, 663802, 354619, 857, 16384⟩ := by
  decide +kernel

theorem context_13_354619_663802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354619 ⟨663802, by decide⟩ :=
  accepted_of_selected 13 354619 ⟨663802, by decide⟩ ⟨13, 2, 0, 663802, 354619, 857, 16384⟩
    (by decide) selected_cut_26248

theorem unmarked_context_12_88654_663803 : frontier 9 ⟨663803, by decide⟩
    (prefixCache 12 88654) (prefixPartial 12 88654) = false := by
  decide +kernel

theorem node_context_12_88654_663803 : EJMOriginalGlobalDAGData.nodes 9 ⟨663803, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨663774, by decide⟩,⟨663793, by decide⟩,⟨663802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88654_663803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88654 ⟨663803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88654
    ⟨663803, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨663774, by decide⟩,⟨663793, by decide⟩,⟨663802, by decide⟩]) unmarked_context_12_88654_663803 node_context_12_88654_663803
  intro a
  fin_cases a
  · exact context_13_354616_3444
  · exact context_13_354617_663774
  · exact context_13_354618_663793
  · exact context_13_354619_663802

theorem selected_cut_26249 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354620) = some ⟨13, 1, 0, 3444, 354620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354620, 1, 16384⟩
    (by decide) selected_cut_26249

theorem selected_cut_26250 : selected 8 ⟨663832, by decide⟩
    (prefixPartial 13 354621) = some ⟨13, 2, 0, 663832, 354621, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_354621_663832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354621 ⟨663832, by decide⟩ :=
  accepted_of_selected 13 354621 ⟨663832, by decide⟩ ⟨13, 2, 0, 663832, 354621, 1905, 16384⟩
    (by decide) selected_cut_26250

theorem selected_cut_26251 : selected 8 ⟨663849, by decide⟩
    (prefixPartial 13 354622) = some ⟨13, 2, 0, 663849, 354622, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_354622_663849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354622 ⟨663849, by decide⟩ :=
  accepted_of_selected 13 354622 ⟨663849, by decide⟩ ⟨13, 2, 0, 663849, 354622, 1493, 16384⟩
    (by decide) selected_cut_26251

theorem selected_cut_26252 : selected 8 ⟨663857, by decide⟩
    (prefixPartial 13 354623) = some ⟨13, 2, 0, 663857, 354623, 957, 16384⟩ := by
  decide +kernel

theorem context_13_354623_663857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354623 ⟨663857, by decide⟩ :=
  accepted_of_selected 13 354623 ⟨663857, by decide⟩ ⟨13, 2, 0, 663857, 354623, 957, 16384⟩
    (by decide) selected_cut_26252

theorem unmarked_context_12_88655_663858 : frontier 9 ⟨663858, by decide⟩
    (prefixCache 12 88655) (prefixPartial 12 88655) = false := by
  decide +kernel

theorem node_context_12_88655_663858 : EJMOriginalGlobalDAGData.nodes 9 ⟨663858, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨663832, by decide⟩,⟨663849, by decide⟩,⟨663857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88655_663858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88655 ⟨663858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88655
    ⟨663858, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨663832, by decide⟩,⟨663849, by decide⟩,⟨663857, by decide⟩]) unmarked_context_12_88655_663858 node_context_12_88655_663858
  intro a
  fin_cases a
  · exact context_13_354620_3444
  · exact context_13_354621_663832
  · exact context_13_354622_663849
  · exact context_13_354623_663857

theorem unmarked_context_11_22163_663859 : frontier 10 ⟨663859, by decide⟩
    (prefixCache 11 22163) (prefixPartial 11 22163) = false := by
  decide +kernel

theorem node_context_11_22163_663859 : EJMOriginalGlobalDAGData.nodes 10 ⟨663859, by decide⟩ =
    .split (coordinate 11) (![⟨663667, by decide⟩,⟨663749, by decide⟩,⟨663803, by decide⟩,⟨663858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22163_663859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22163 ⟨663859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22163
    ⟨663859, by decide⟩ (by decide) (![⟨663667, by decide⟩,⟨663749, by decide⟩,⟨663803, by decide⟩,⟨663858, by decide⟩]) unmarked_context_11_22163_663859 node_context_11_22163_663859
  intro a
  fin_cases a
  · exact context_12_88652_663667
  · exact context_12_88653_663749
  · exact context_12_88654_663803
  · exact context_12_88655_663858

theorem unmarked_context_10_5540_663860 : frontier 11 ⟨663860, by decide⟩
    (prefixCache 10 5540) (prefixPartial 10 5540) = false := by
  decide +kernel

theorem node_context_10_5540_663860 : EJMOriginalGlobalDAGData.nodes 11 ⟨663860, by decide⟩ =
    .split (coordinate 10) (![⟨663268, by decide⟩,⟨663443, by decide⟩,⟨663608, by decide⟩,⟨663859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5540_663860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5540 ⟨663860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5540
    ⟨663860, by decide⟩ (by decide) (![⟨663268, by decide⟩,⟨663443, by decide⟩,⟨663608, by decide⟩,⟨663859, by decide⟩]) unmarked_context_10_5540_663860 node_context_10_5540_663860
  intro a
  fin_cases a
  · exact context_11_22160_663268
  · exact context_11_22161_663443
  · exact context_11_22162_663608
  · exact context_11_22163_663859

theorem selected_cut_26253 : selected 9 ⟨663912, by decide⟩
    (prefixPartial 12 88656) = some ⟨12, 2, 0, 663912, 88656, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_88656_663912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88656 ⟨663912, by decide⟩ :=
  accepted_of_selected 12 88656 ⟨663912, by decide⟩ ⟨12, 2, 0, 663912, 88656, 3413, 65536⟩
    (by decide) selected_cut_26253

theorem selected_cut_26254 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88657) = some ⟨12, 1, 0, 642341, 88657, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88657_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88657 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88657 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88657, 1, 65536⟩
    (by decide) selected_cut_26254

theorem selected_cut_26255 : selected 9 ⟨663957, by decide⟩
    (prefixPartial 12 88658) = some ⟨12, 2, 0, 663957, 88658, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_88658_663957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88658 ⟨663957, by decide⟩ :=
  accepted_of_selected 12 88658 ⟨663957, by decide⟩ ⟨12, 2, 0, 663957, 88658, 3609, 65536⟩
    (by decide) selected_cut_26255

theorem selected_cut_26256 : selected 9 ⟨664013, by decide⟩
    (prefixPartial 12 88659) = some ⟨12, 2, 0, 664013, 88659, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_88659_664013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88659 ⟨664013, by decide⟩ :=
  accepted_of_selected 12 88659 ⟨664013, by decide⟩ ⟨12, 2, 0, 664013, 88659, 3993, 65536⟩
    (by decide) selected_cut_26256

theorem unmarked_context_11_22164_664014 : frontier 10 ⟨664014, by decide⟩
    (prefixCache 11 22164) (prefixPartial 11 22164) = false := by
  decide +kernel

theorem node_context_11_22164_664014 : EJMOriginalGlobalDAGData.nodes 10 ⟨664014, by decide⟩ =
    .split (coordinate 11) (![⟨663912, by decide⟩,⟨642341, by decide⟩,⟨663957, by decide⟩,⟨664013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22164_664014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22164 ⟨664014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22164
    ⟨664014, by decide⟩ (by decide) (![⟨663912, by decide⟩,⟨642341, by decide⟩,⟨663957, by decide⟩,⟨664013, by decide⟩]) unmarked_context_11_22164_664014 node_context_11_22164_664014
  intro a
  fin_cases a
  · exact context_12_88656_663912
  · exact context_12_88657_642341
  · exact context_12_88658_663957
  · exact context_12_88659_664013

theorem selected_cut_26257 : selected 9 ⟨664058, by decide⟩
    (prefixPartial 12 88660) = some ⟨12, 2, 0, 664058, 88660, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_88660_664058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88660 ⟨664058, by decide⟩ :=
  accepted_of_selected 12 88660 ⟨664058, by decide⟩ ⟨12, 2, 0, 664058, 88660, 3649, 65536⟩
    (by decide) selected_cut_26257

theorem selected_cut_26258 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88661) = some ⟨12, 1, 0, 642341, 88661, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88661_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88661 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88661 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88661, 1, 65536⟩
    (by decide) selected_cut_26258

theorem selected_cut_26259 : selected 9 ⟨664108, by decide⟩
    (prefixPartial 12 88662) = some ⟨12, 2, 0, 664108, 88662, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_88662_664108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88662 ⟨664108, by decide⟩ :=
  accepted_of_selected 12 88662 ⟨664108, by decide⟩ ⟨12, 2, 0, 664108, 88662, 3421, 65536⟩
    (by decide) selected_cut_26259

theorem selected_cut_26260 : selected 9 ⟨664152, by decide⟩
    (prefixPartial 12 88663) = some ⟨12, 2, 0, 664152, 88663, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_88663_664152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88663 ⟨664152, by decide⟩ :=
  accepted_of_selected 12 88663 ⟨664152, by decide⟩ ⟨12, 2, 0, 664152, 88663, 3637, 65536⟩
    (by decide) selected_cut_26260

theorem unmarked_context_11_22165_664153 : frontier 10 ⟨664153, by decide⟩
    (prefixCache 11 22165) (prefixPartial 11 22165) = false := by
  decide +kernel

theorem node_context_11_22165_664153 : EJMOriginalGlobalDAGData.nodes 10 ⟨664153, by decide⟩ =
    .split (coordinate 11) (![⟨664058, by decide⟩,⟨642341, by decide⟩,⟨664108, by decide⟩,⟨664152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22165_664153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22165 ⟨664153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22165
    ⟨664153, by decide⟩ (by decide) (![⟨664058, by decide⟩,⟨642341, by decide⟩,⟨664108, by decide⟩,⟨664152, by decide⟩]) unmarked_context_11_22165_664153 node_context_11_22165_664153
  intro a
  fin_cases a
  · exact context_12_88660_664058
  · exact context_12_88661_642341
  · exact context_12_88662_664108
  · exact context_12_88663_664152

theorem selected_cut_26261 : selected 9 ⟨664192, by decide⟩
    (prefixPartial 12 88664) = some ⟨12, 2, 0, 664192, 88664, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_88664_664192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88664 ⟨664192, by decide⟩ :=
  accepted_of_selected 12 88664 ⟨664192, by decide⟩ ⟨12, 2, 0, 664192, 88664, 3237, 65536⟩
    (by decide) selected_cut_26261

theorem selected_cut_26262 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88665) = some ⟨12, 1, 0, 642341, 88665, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88665_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88665 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88665 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88665, 1, 65536⟩
    (by decide) selected_cut_26262

theorem selected_cut_26263 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 88666) = some ⟨12, 1, 0, 660636, 88666, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88666_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88666 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 88666 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 88666, 1, 65536⟩
    (by decide) selected_cut_26263

theorem selected_cut_26264 : selected 9 ⟨664243, by decide⟩
    (prefixPartial 12 88667) = some ⟨12, 2, 0, 664243, 88667, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_88667_664243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88667 ⟨664243, by decide⟩ :=
  accepted_of_selected 12 88667 ⟨664243, by decide⟩ ⟨12, 2, 0, 664243, 88667, 3545, 65536⟩
    (by decide) selected_cut_26264

theorem unmarked_context_11_22166_664244 : frontier 10 ⟨664244, by decide⟩
    (prefixCache 11 22166) (prefixPartial 11 22166) = false := by
  decide +kernel

theorem node_context_11_22166_664244 : EJMOriginalGlobalDAGData.nodes 10 ⟨664244, by decide⟩ =
    .split (coordinate 11) (![⟨664192, by decide⟩,⟨642341, by decide⟩,⟨660636, by decide⟩,⟨664243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22166_664244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22166 ⟨664244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22166
    ⟨664244, by decide⟩ (by decide) (![⟨664192, by decide⟩,⟨642341, by decide⟩,⟨660636, by decide⟩,⟨664243, by decide⟩]) unmarked_context_11_22166_664244 node_context_11_22166_664244
  intro a
  fin_cases a
  · exact context_12_88664_664192
  · exact context_12_88665_642341
  · exact context_12_88666_660636
  · exact context_12_88667_664243

theorem selected_cut_26265 : selected 9 ⟨664296, by decide⟩
    (prefixPartial 12 88668) = some ⟨12, 2, 0, 664296, 88668, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_88668_664296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88668 ⟨664296, by decide⟩ :=
  accepted_of_selected 12 88668 ⟨664296, by decide⟩ ⟨12, 2, 0, 664296, 88668, 3977, 65536⟩
    (by decide) selected_cut_26265

theorem selected_cut_26266 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 88669) = some ⟨12, 1, 0, 642341, 88669, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88669_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88669 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 88669 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 88669, 1, 65536⟩
    (by decide) selected_cut_26266

theorem selected_cut_26267 : selected 9 ⟨664346, by decide⟩
    (prefixPartial 12 88670) = some ⟨12, 2, 0, 664346, 88670, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_88670_664346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88670 ⟨664346, by decide⟩ :=
  accepted_of_selected 12 88670 ⟨664346, by decide⟩ ⟨12, 2, 0, 664346, 88670, 3801, 65536⟩
    (by decide) selected_cut_26267

theorem selected_cut_26268 : selected 9 ⟨664396, by decide⟩
    (prefixPartial 12 88671) = some ⟨12, 2, 0, 664396, 88671, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_88671_664396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88671 ⟨664396, by decide⟩ :=
  accepted_of_selected 12 88671 ⟨664396, by decide⟩ ⟨12, 2, 0, 664396, 88671, 3989, 65536⟩
    (by decide) selected_cut_26268

theorem unmarked_context_11_22167_664397 : frontier 10 ⟨664397, by decide⟩
    (prefixCache 11 22167) (prefixPartial 11 22167) = false := by
  decide +kernel

theorem node_context_11_22167_664397 : EJMOriginalGlobalDAGData.nodes 10 ⟨664397, by decide⟩ =
    .split (coordinate 11) (![⟨664296, by decide⟩,⟨642341, by decide⟩,⟨664346, by decide⟩,⟨664396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22167_664397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22167 ⟨664397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22167
    ⟨664397, by decide⟩ (by decide) (![⟨664296, by decide⟩,⟨642341, by decide⟩,⟨664346, by decide⟩,⟨664396, by decide⟩]) unmarked_context_11_22167_664397 node_context_11_22167_664397
  intro a
  fin_cases a
  · exact context_12_88668_664296
  · exact context_12_88669_642341
  · exact context_12_88670_664346
  · exact context_12_88671_664396

theorem unmarked_context_10_5541_664398 : frontier 11 ⟨664398, by decide⟩
    (prefixCache 10 5541) (prefixPartial 10 5541) = false := by
  decide +kernel

theorem node_context_10_5541_664398 : EJMOriginalGlobalDAGData.nodes 11 ⟨664398, by decide⟩ =
    .split (coordinate 10) (![⟨664014, by decide⟩,⟨664153, by decide⟩,⟨664244, by decide⟩,⟨664397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5541_664398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5541 ⟨664398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5541
    ⟨664398, by decide⟩ (by decide) (![⟨664014, by decide⟩,⟨664153, by decide⟩,⟨664244, by decide⟩,⟨664397, by decide⟩]) unmarked_context_10_5541_664398 node_context_10_5541_664398
  intro a
  fin_cases a
  · exact context_11_22164_664014
  · exact context_11_22165_664153
  · exact context_11_22166_664244
  · exact context_11_22167_664397

theorem selected_cut_26269 : selected 9 ⟨664436, by decide⟩
    (prefixPartial 12 88672) = some ⟨12, 2, 0, 664436, 88672, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_88672_664436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88672 ⟨664436, by decide⟩ :=
  accepted_of_selected 12 88672 ⟨664436, by decide⟩ ⟨12, 2, 0, 664436, 88672, 3201, 65536⟩
    (by decide) selected_cut_26269

theorem selected_cut_26270 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354692) = some ⟨13, 1, 0, 3444, 354692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354692, 1, 16384⟩
    (by decide) selected_cut_26270

theorem selected_cut_26271 : selected 8 ⟨664465, by decide⟩
    (prefixPartial 13 354693) = some ⟨13, 2, 0, 664465, 354693, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_354693_664465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354693 ⟨664465, by decide⟩ :=
  accepted_of_selected 13 354693 ⟨664465, by decide⟩ ⟨13, 2, 0, 664465, 354693, 1573, 16384⟩
    (by decide) selected_cut_26271

theorem selected_cut_26272 : selected 8 ⟨664487, by decide⟩
    (prefixPartial 13 354694) = some ⟨13, 2, 0, 664487, 354694, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_354694_664487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354694 ⟨664487, by decide⟩ :=
  accepted_of_selected 13 354694 ⟨664487, by decide⟩ ⟨13, 2, 0, 664487, 354694, 1753, 16384⟩
    (by decide) selected_cut_26272

theorem selected_cut_26273 : selected 8 ⟨664507, by decide⟩
    (prefixPartial 13 354695) = some ⟨13, 2, 0, 664507, 354695, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_354695_664507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354695 ⟨664507, by decide⟩ :=
  accepted_of_selected 13 354695 ⟨664507, by decide⟩ ⟨13, 2, 0, 664507, 354695, 1077, 16384⟩
    (by decide) selected_cut_26273

theorem unmarked_context_12_88673_664508 : frontier 9 ⟨664508, by decide⟩
    (prefixCache 12 88673) (prefixPartial 12 88673) = false := by
  decide +kernel

theorem node_context_12_88673_664508 : EJMOriginalGlobalDAGData.nodes 9 ⟨664508, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨664465, by decide⟩,⟨664487, by decide⟩,⟨664507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88673_664508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88673 ⟨664508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88673
    ⟨664508, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨664465, by decide⟩,⟨664487, by decide⟩,⟨664507, by decide⟩]) unmarked_context_12_88673_664508 node_context_12_88673_664508
  intro a
  fin_cases a
  · exact context_13_354692_3444
  · exact context_13_354693_664465
  · exact context_13_354694_664487
  · exact context_13_354695_664507

theorem selected_cut_26274 : selected 9 ⟨664544, by decide⟩
    (prefixPartial 12 88674) = some ⟨12, 2, 0, 664544, 88674, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_88674_664544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88674 ⟨664544, by decide⟩ :=
  accepted_of_selected 12 88674 ⟨664544, by decide⟩ ⟨12, 2, 0, 664544, 88674, 3005, 65536⟩
    (by decide) selected_cut_26274

theorem selected_cut_26275 : selected 9 ⟨664584, by decide⟩
    (prefixPartial 12 88675) = some ⟨12, 2, 0, 664584, 88675, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_88675_664584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88675 ⟨664584, by decide⟩ :=
  accepted_of_selected 12 88675 ⟨664584, by decide⟩ ⟨12, 2, 0, 664584, 88675, 3429, 65536⟩
    (by decide) selected_cut_26275

theorem unmarked_context_11_22168_664585 : frontier 10 ⟨664585, by decide⟩
    (prefixCache 11 22168) (prefixPartial 11 22168) = false := by
  decide +kernel

theorem node_context_11_22168_664585 : EJMOriginalGlobalDAGData.nodes 10 ⟨664585, by decide⟩ =
    .split (coordinate 11) (![⟨664436, by decide⟩,⟨664508, by decide⟩,⟨664544, by decide⟩,⟨664584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22168_664585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22168 ⟨664585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22168
    ⟨664585, by decide⟩ (by decide) (![⟨664436, by decide⟩,⟨664508, by decide⟩,⟨664544, by decide⟩,⟨664584, by decide⟩]) unmarked_context_11_22168_664585 node_context_11_22168_664585
  intro a
  fin_cases a
  · exact context_12_88672_664436
  · exact context_12_88673_664508
  · exact context_12_88674_664544
  · exact context_12_88675_664584

theorem selected_cut_26276 : selected 9 ⟨664623, by decide⟩
    (prefixPartial 12 88676) = some ⟨12, 2, 0, 664623, 88676, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_88676_664623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88676 ⟨664623, by decide⟩ :=
  accepted_of_selected 12 88676 ⟨664623, by decide⟩ ⟨12, 2, 0, 664623, 88676, 3173, 65536⟩
    (by decide) selected_cut_26276

theorem selected_cut_26277 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 88677) = some ⟨12, 1, 0, 642794, 88677, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88677_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88677 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 88677 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 88677, 1, 65536⟩
    (by decide) selected_cut_26277

theorem selected_cut_26278 : selected 9 ⟨664659, by decide⟩
    (prefixPartial 12 88678) = some ⟨12, 2, 0, 664659, 88678, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_88678_664659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88678 ⟨664659, by decide⟩ :=
  accepted_of_selected 12 88678 ⟨664659, by decide⟩ ⟨12, 2, 0, 664659, 88678, 2757, 65536⟩
    (by decide) selected_cut_26278

theorem selected_cut_26279 : selected 9 ⟨664697, by decide⟩
    (prefixPartial 12 88679) = some ⟨12, 2, 0, 664697, 88679, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_88679_664697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88679 ⟨664697, by decide⟩ :=
  accepted_of_selected 12 88679 ⟨664697, by decide⟩ ⟨12, 2, 0, 664697, 88679, 3021, 65536⟩
    (by decide) selected_cut_26279

theorem unmarked_context_11_22169_664698 : frontier 10 ⟨664698, by decide⟩
    (prefixCache 11 22169) (prefixPartial 11 22169) = false := by
  decide +kernel

theorem node_context_11_22169_664698 : EJMOriginalGlobalDAGData.nodes 10 ⟨664698, by decide⟩ =
    .split (coordinate 11) (![⟨664623, by decide⟩,⟨642794, by decide⟩,⟨664659, by decide⟩,⟨664697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22169_664698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22169 ⟨664698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22169
    ⟨664698, by decide⟩ (by decide) (![⟨664623, by decide⟩,⟨642794, by decide⟩,⟨664659, by decide⟩,⟨664697, by decide⟩]) unmarked_context_11_22169_664698 node_context_11_22169_664698
  intro a
  fin_cases a
  · exact context_12_88676_664623
  · exact context_12_88677_642794
  · exact context_12_88678_664659
  · exact context_12_88679_664697

theorem selected_cut_26280 : selected 10 ⟨664699, by decide⟩
    (prefixPartial 11 22170) = some ⟨11, 2, 0, 664699, 22170, 5, 262144⟩ := by
  decide +kernel

theorem context_11_22170_664699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22170 ⟨664699, by decide⟩ :=
  accepted_of_selected 11 22170 ⟨664699, by decide⟩ ⟨11, 2, 0, 664699, 22170, 5, 262144⟩
    (by decide) selected_cut_26280

theorem selected_cut_26281 : selected 9 ⟨664749, by decide⟩
    (prefixPartial 12 88684) = some ⟨12, 2, 0, 664749, 88684, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_88684_664749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88684 ⟨664749, by decide⟩ :=
  accepted_of_selected 12 88684 ⟨664749, by decide⟩ ⟨12, 2, 0, 664749, 88684, 3705, 65536⟩
    (by decide) selected_cut_26281

theorem selected_cut_26282 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 354740) = some ⟨13, 1, 0, 3444, 354740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_354740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 354740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 354740, 1, 16384⟩
    (by decide) selected_cut_26282

theorem selected_cut_26283 : selected 8 ⟨664766, by decide⟩
    (prefixPartial 13 354741) = some ⟨13, 2, 0, 664766, 354741, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_354741_664766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354741 ⟨664766, by decide⟩ :=
  accepted_of_selected 13 354741 ⟨664766, by decide⟩ ⟨13, 2, 0, 664766, 354741, 1001, 16384⟩
    (by decide) selected_cut_26283

theorem selected_cut_26284 : selected 8 ⟨664788, by decide⟩
    (prefixPartial 13 354742) = some ⟨13, 2, 0, 664788, 354742, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_354742_664788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354742 ⟨664788, by decide⟩ :=
  accepted_of_selected 13 354742 ⟨664788, by decide⟩ ⟨13, 2, 0, 664788, 354742, 2105, 16384⟩
    (by decide) selected_cut_26284

theorem selected_cut_26285 : selected 8 ⟨664809, by decide⟩
    (prefixPartial 13 354743) = some ⟨13, 2, 0, 664809, 354743, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_354743_664809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 354743 ⟨664809, by decide⟩ :=
  accepted_of_selected 13 354743 ⟨664809, by decide⟩ ⟨13, 2, 0, 664809, 354743, 1177, 16384⟩
    (by decide) selected_cut_26285

theorem unmarked_context_12_88685_664810 : frontier 9 ⟨664810, by decide⟩
    (prefixCache 12 88685) (prefixPartial 12 88685) = false := by
  decide +kernel

theorem node_context_12_88685_664810 : EJMOriginalGlobalDAGData.nodes 9 ⟨664810, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨664766, by decide⟩,⟨664788, by decide⟩,⟨664809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88685_664810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88685 ⟨664810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88685
    ⟨664810, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨664766, by decide⟩,⟨664788, by decide⟩,⟨664809, by decide⟩]) unmarked_context_12_88685_664810 node_context_12_88685_664810
  intro a
  fin_cases a
  · exact context_13_354740_3444
  · exact context_13_354741_664766
  · exact context_13_354742_664788
  · exact context_13_354743_664809

theorem selected_cut_26286 : selected 9 ⟨664845, by decide⟩
    (prefixPartial 12 88686) = some ⟨12, 2, 0, 664845, 88686, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_88686_664845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88686 ⟨664845, by decide⟩ :=
  accepted_of_selected 12 88686 ⟨664845, by decide⟩ ⟨12, 2, 0, 664845, 88686, 3189, 65536⟩
    (by decide) selected_cut_26286

theorem selected_cut_26287 : selected 9 ⟨664880, by decide⟩
    (prefixPartial 12 88687) = some ⟨12, 2, 0, 664880, 88687, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_88687_664880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88687 ⟨664880, by decide⟩ :=
  accepted_of_selected 12 88687 ⟨664880, by decide⟩ ⟨12, 2, 0, 664880, 88687, 3489, 65536⟩
    (by decide) selected_cut_26287

theorem unmarked_context_11_22171_664881 : frontier 10 ⟨664881, by decide⟩
    (prefixCache 11 22171) (prefixPartial 11 22171) = false := by
  decide +kernel

theorem node_context_11_22171_664881 : EJMOriginalGlobalDAGData.nodes 10 ⟨664881, by decide⟩ =
    .split (coordinate 11) (![⟨664749, by decide⟩,⟨664810, by decide⟩,⟨664845, by decide⟩,⟨664880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22171_664881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22171 ⟨664881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22171
    ⟨664881, by decide⟩ (by decide) (![⟨664749, by decide⟩,⟨664810, by decide⟩,⟨664845, by decide⟩,⟨664880, by decide⟩]) unmarked_context_11_22171_664881 node_context_11_22171_664881
  intro a
  fin_cases a
  · exact context_12_88684_664749
  · exact context_12_88685_664810
  · exact context_12_88686_664845
  · exact context_12_88687_664880

theorem unmarked_context_10_5542_664882 : frontier 11 ⟨664882, by decide⟩
    (prefixCache 10 5542) (prefixPartial 10 5542) = false := by
  decide +kernel

theorem node_context_10_5542_664882 : EJMOriginalGlobalDAGData.nodes 11 ⟨664882, by decide⟩ =
    .split (coordinate 10) (![⟨664585, by decide⟩,⟨664698, by decide⟩,⟨664699, by decide⟩,⟨664881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5542_664882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5542 ⟨664882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5542
    ⟨664882, by decide⟩ (by decide) (![⟨664585, by decide⟩,⟨664698, by decide⟩,⟨664699, by decide⟩,⟨664881, by decide⟩]) unmarked_context_10_5542_664882 node_context_10_5542_664882
  intro a
  fin_cases a
  · exact context_11_22168_664585
  · exact context_11_22169_664698
  · exact context_11_22170_664699
  · exact context_11_22171_664881

theorem selected_cut_26288 : selected 9 ⟨664914, by decide⟩
    (prefixPartial 12 88688) = some ⟨12, 2, 0, 664914, 88688, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_88688_664914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88688 ⟨664914, by decide⟩ :=
  accepted_of_selected 12 88688 ⟨664914, by decide⟩ ⟨12, 2, 0, 664914, 88688, 2441, 65536⟩
    (by decide) selected_cut_26288

theorem selected_cut_26289 : selected 9 ⟨664968, by decide⟩
    (prefixPartial 12 88689) = some ⟨12, 2, 0, 664968, 88689, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_88689_664968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88689 ⟨664968, by decide⟩ :=
  accepted_of_selected 12 88689 ⟨664968, by decide⟩ ⟨12, 2, 0, 664968, 88689, 3565, 65536⟩
    (by decide) selected_cut_26289

theorem selected_cut_26290 : selected 9 ⟨664996, by decide⟩
    (prefixPartial 12 88690) = some ⟨12, 2, 0, 664996, 88690, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_88690_664996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88690 ⟨664996, by decide⟩ :=
  accepted_of_selected 12 88690 ⟨664996, by decide⟩ ⟨12, 2, 0, 664996, 88690, 2477, 65536⟩
    (by decide) selected_cut_26290

theorem selected_cut_26291 : selected 9 ⟨665033, by decide⟩
    (prefixPartial 12 88691) = some ⟨12, 2, 0, 665033, 88691, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_88691_665033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88691 ⟨665033, by decide⟩ :=
  accepted_of_selected 12 88691 ⟨665033, by decide⟩ ⟨12, 2, 0, 665033, 88691, 2817, 65536⟩
    (by decide) selected_cut_26291

theorem unmarked_context_11_22172_665034 : frontier 10 ⟨665034, by decide⟩
    (prefixCache 11 22172) (prefixPartial 11 22172) = false := by
  decide +kernel

theorem node_context_11_22172_665034 : EJMOriginalGlobalDAGData.nodes 10 ⟨665034, by decide⟩ =
    .split (coordinate 11) (![⟨664914, by decide⟩,⟨664968, by decide⟩,⟨664996, by decide⟩,⟨665033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22172_665034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22172 ⟨665034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22172
    ⟨665034, by decide⟩ (by decide) (![⟨664914, by decide⟩,⟨664968, by decide⟩,⟨664996, by decide⟩,⟨665033, by decide⟩]) unmarked_context_11_22172_665034 node_context_11_22172_665034
  intro a
  fin_cases a
  · exact context_12_88688_664914
  · exact context_12_88689_664968
  · exact context_12_88690_664996
  · exact context_12_88691_665033

theorem selected_cut_26292 : selected 9 ⟨665067, by decide⟩
    (prefixPartial 12 88692) = some ⟨12, 2, 0, 665067, 88692, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_88692_665067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88692 ⟨665067, by decide⟩ :=
  accepted_of_selected 12 88692 ⟨665067, by decide⟩ ⟨12, 2, 0, 665067, 88692, 2649, 65536⟩
    (by decide) selected_cut_26292

theorem selected_cut_26293 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 88693) = some ⟨12, 1, 0, 642794, 88693, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88693_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88693 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 88693 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 88693, 1, 65536⟩
    (by decide) selected_cut_26293

theorem selected_cut_26294 : selected 9 ⟨665096, by decide⟩
    (prefixPartial 12 88694) = some ⟨12, 2, 0, 665096, 88694, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_88694_665096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88694 ⟨665096, by decide⟩ :=
  accepted_of_selected 12 88694 ⟨665096, by decide⟩ ⟨12, 2, 0, 665096, 88694, 2461, 65536⟩
    (by decide) selected_cut_26294

theorem selected_cut_26295 : selected 9 ⟨665139, by decide⟩
    (prefixPartial 12 88695) = some ⟨12, 2, 0, 665139, 88695, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_88695_665139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88695 ⟨665139, by decide⟩ :=
  accepted_of_selected 12 88695 ⟨665139, by decide⟩ ⟨12, 2, 0, 665139, 88695, 2709, 65536⟩
    (by decide) selected_cut_26295

theorem unmarked_context_11_22173_665140 : frontier 10 ⟨665140, by decide⟩
    (prefixCache 11 22173) (prefixPartial 11 22173) = false := by
  decide +kernel

theorem node_context_11_22173_665140 : EJMOriginalGlobalDAGData.nodes 10 ⟨665140, by decide⟩ =
    .split (coordinate 11) (![⟨665067, by decide⟩,⟨642794, by decide⟩,⟨665096, by decide⟩,⟨665139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22173_665140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22173 ⟨665140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22173
    ⟨665140, by decide⟩ (by decide) (![⟨665067, by decide⟩,⟨642794, by decide⟩,⟨665096, by decide⟩,⟨665139, by decide⟩]) unmarked_context_11_22173_665140 node_context_11_22173_665140
  intro a
  fin_cases a
  · exact context_12_88692_665067
  · exact context_12_88693_642794
  · exact context_12_88694_665096
  · exact context_12_88695_665139

theorem selected_cut_26296 : selected 9 ⟨665170, by decide⟩
    (prefixPartial 12 88696) = some ⟨12, 2, 0, 665170, 88696, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_88696_665170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88696 ⟨665170, by decide⟩ :=
  accepted_of_selected 12 88696 ⟨665170, by decide⟩ ⟨12, 2, 0, 665170, 88696, 2533, 65536⟩
    (by decide) selected_cut_26296

theorem selected_cut_26297 : selected 9 ⟨665205, by decide⟩
    (prefixPartial 12 88697) = some ⟨12, 2, 0, 665205, 88697, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_88697_665205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88697 ⟨665205, by decide⟩ :=
  accepted_of_selected 12 88697 ⟨665205, by decide⟩ ⟨12, 2, 0, 665205, 88697, 3129, 65536⟩
    (by decide) selected_cut_26297

theorem selected_cut_26298 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 88698) = some ⟨12, 1, 0, 662655, 88698, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88698_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88698 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 88698 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 88698, 1, 65536⟩
    (by decide) selected_cut_26298

theorem selected_cut_26299 : selected 9 ⟨665235, by decide⟩
    (prefixPartial 12 88699) = some ⟨12, 2, 0, 665235, 88699, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_88699_665235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88699 ⟨665235, by decide⟩ :=
  accepted_of_selected 12 88699 ⟨665235, by decide⟩ ⟨12, 2, 0, 665235, 88699, 2617, 65536⟩
    (by decide) selected_cut_26299

theorem unmarked_context_11_22174_665236 : frontier 10 ⟨665236, by decide⟩
    (prefixCache 11 22174) (prefixPartial 11 22174) = false := by
  decide +kernel

theorem node_context_11_22174_665236 : EJMOriginalGlobalDAGData.nodes 10 ⟨665236, by decide⟩ =
    .split (coordinate 11) (![⟨665170, by decide⟩,⟨665205, by decide⟩,⟨662655, by decide⟩,⟨665235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22174_665236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22174 ⟨665236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22174
    ⟨665236, by decide⟩ (by decide) (![⟨665170, by decide⟩,⟨665205, by decide⟩,⟨662655, by decide⟩,⟨665235, by decide⟩]) unmarked_context_11_22174_665236 node_context_11_22174_665236
  intro a
  fin_cases a
  · exact context_12_88696_665170
  · exact context_12_88697_665205
  · exact context_12_88698_662655
  · exact context_12_88699_665235

theorem selected_cut_26300 : selected 9 ⟨665268, by decide⟩
    (prefixPartial 12 88700) = some ⟨12, 2, 0, 665268, 88700, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_88700_665268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88700 ⟨665268, by decide⟩ :=
  accepted_of_selected 12 88700 ⟨665268, by decide⟩ ⟨12, 2, 0, 665268, 88700, 2749, 65536⟩
    (by decide) selected_cut_26300

theorem selected_cut_26301 : selected 9 ⟨665311, by decide⟩
    (prefixPartial 12 88701) = some ⟨12, 2, 0, 665311, 88701, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_88701_665311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88701 ⟨665311, by decide⟩ :=
  accepted_of_selected 12 88701 ⟨665311, by decide⟩ ⟨12, 2, 0, 665311, 88701, 3221, 65536⟩
    (by decide) selected_cut_26301

theorem selected_cut_26302 : selected 9 ⟨665348, by decide⟩
    (prefixPartial 12 88702) = some ⟨12, 2, 0, 665348, 88702, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_88702_665348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88702 ⟨665348, by decide⟩ :=
  accepted_of_selected 12 88702 ⟨665348, by decide⟩ ⟨12, 2, 0, 665348, 88702, 2489, 65536⟩
    (by decide) selected_cut_26302

theorem selected_cut_26303 : selected 9 ⟨665382, by decide⟩
    (prefixPartial 12 88703) = some ⟨12, 2, 0, 665382, 88703, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_88703_665382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88703 ⟨665382, by decide⟩ :=
  accepted_of_selected 12 88703 ⟨665382, by decide⟩ ⟨12, 2, 0, 665382, 88703, 2773, 65536⟩
    (by decide) selected_cut_26303

theorem unmarked_context_11_22175_665383 : frontier 10 ⟨665383, by decide⟩
    (prefixCache 11 22175) (prefixPartial 11 22175) = false := by
  decide +kernel

theorem node_context_11_22175_665383 : EJMOriginalGlobalDAGData.nodes 10 ⟨665383, by decide⟩ =
    .split (coordinate 11) (![⟨665268, by decide⟩,⟨665311, by decide⟩,⟨665348, by decide⟩,⟨665382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22175_665383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22175 ⟨665383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22175
    ⟨665383, by decide⟩ (by decide) (![⟨665268, by decide⟩,⟨665311, by decide⟩,⟨665348, by decide⟩,⟨665382, by decide⟩]) unmarked_context_11_22175_665383 node_context_11_22175_665383
  intro a
  fin_cases a
  · exact context_12_88700_665268
  · exact context_12_88701_665311
  · exact context_12_88702_665348
  · exact context_12_88703_665382

theorem unmarked_context_10_5543_665384 : frontier 11 ⟨665384, by decide⟩
    (prefixCache 10 5543) (prefixPartial 10 5543) = false := by
  decide +kernel

theorem node_context_10_5543_665384 : EJMOriginalGlobalDAGData.nodes 11 ⟨665384, by decide⟩ =
    .split (coordinate 10) (![⟨665034, by decide⟩,⟨665140, by decide⟩,⟨665236, by decide⟩,⟨665383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5543_665384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5543 ⟨665384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5543
    ⟨665384, by decide⟩ (by decide) (![⟨665034, by decide⟩,⟨665140, by decide⟩,⟨665236, by decide⟩,⟨665383, by decide⟩]) unmarked_context_10_5543_665384 node_context_10_5543_665384
  intro a
  fin_cases a
  · exact context_11_22172_665034
  · exact context_11_22173_665140
  · exact context_11_22174_665236
  · exact context_11_22175_665383

theorem unmarked_context_9_1385_665385 : frontier 12 ⟨665385, by decide⟩
    (prefixCache 9 1385) (prefixPartial 9 1385) = false := by
  decide +kernel

theorem node_context_9_1385_665385 : EJMOriginalGlobalDAGData.nodes 12 ⟨665385, by decide⟩ =
    .split (coordinate 9) (![⟨663860, by decide⟩,⟨664398, by decide⟩,⟨664882, by decide⟩,⟨665384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1385_665385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1385 ⟨665385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1385
    ⟨665385, by decide⟩ (by decide) (![⟨663860, by decide⟩,⟨664398, by decide⟩,⟨664882, by decide⟩,⟨665384, by decide⟩]) unmarked_context_9_1385_665385 node_context_9_1385_665385
  intro a
  fin_cases a
  · exact context_10_5540_663860
  · exact context_10_5541_664398
  · exact context_10_5542_664882
  · exact context_10_5543_665384

theorem selected_cut_26304 : selected 9 ⟨665402, by decide⟩
    (prefixPartial 12 88704) = some ⟨12, 2, 0, 665402, 88704, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_88704_665402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88704 ⟨665402, by decide⟩ :=
  accepted_of_selected 12 88704 ⟨665402, by decide⟩ ⟨12, 2, 0, 665402, 88704, 1445, 65536⟩
    (by decide) selected_cut_26304

theorem selected_cut_26305 : selected 9 ⟨665425, by decide⟩
    (prefixPartial 12 88705) = some ⟨12, 2, 0, 665425, 88705, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_88705_665425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88705 ⟨665425, by decide⟩ :=
  accepted_of_selected 12 88705 ⟨665425, by decide⟩ ⟨12, 2, 0, 665425, 88705, 1629, 65536⟩
    (by decide) selected_cut_26305

theorem selected_cut_26306 : selected 9 ⟨665447, by decide⟩
    (prefixPartial 12 88706) = some ⟨12, 2, 0, 665447, 88706, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_88706_665447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88706 ⟨665447, by decide⟩ :=
  accepted_of_selected 12 88706 ⟨665447, by decide⟩ ⟨12, 2, 0, 665447, 88706, 1601, 65536⟩
    (by decide) selected_cut_26306

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
