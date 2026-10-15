/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover547
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_52610 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 73904) = some ⟨10, 1, 0, 1468246, 73904, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_73904_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73904 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 73904 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 73904, 1, 1048576⟩
    (by decide) selected_cut_52610

theorem selected_cut_52611 : selected 11 ⟨1539832, by decide⟩
    (prefixPartial 10 73905) = some ⟨10, 2, 0, 1539832, 73905, 2389, 1048576⟩ := by
  decide +kernel

theorem context_10_73905_1539832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73905 ⟨1539832, by decide⟩ :=
  accepted_of_selected 10 73905 ⟨1539832, by decide⟩ ⟨10, 2, 0, 1539832, 73905, 2389, 1048576⟩
    (by decide) selected_cut_52611

theorem selected_cut_52612 : selected 11 ⟨1539877, by decide⟩
    (prefixPartial 10 73906) = some ⟨10, 2, 0, 1539877, 73906, 1341, 1048576⟩ := by
  decide +kernel

theorem context_10_73906_1539877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73906 ⟨1539877, by decide⟩ :=
  accepted_of_selected 10 73906 ⟨1539877, by decide⟩ ⟨10, 2, 0, 1539877, 73906, 1341, 1048576⟩
    (by decide) selected_cut_52612

theorem selected_cut_52613 : selected 11 ⟨1539943, by decide⟩
    (prefixPartial 10 73907) = some ⟨10, 2, 0, 1539943, 73907, 1677, 1048576⟩ := by
  decide +kernel

theorem context_10_73907_1539943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73907 ⟨1539943, by decide⟩ :=
  accepted_of_selected 10 73907 ⟨1539943, by decide⟩ ⟨10, 2, 0, 1539943, 73907, 1677, 1048576⟩
    (by decide) selected_cut_52613

theorem unmarked_context_9_18476_1539944 : frontier 12 ⟨1539944, by decide⟩
    (prefixCache 9 18476) (prefixPartial 9 18476) = false := by
  decide +kernel

theorem node_context_9_18476_1539944 : EJMOriginalGlobalDAGData.nodes 12 ⟨1539944, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1539832, by decide⟩,⟨1539877, by decide⟩,⟨1539943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18476_1539944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18476 ⟨1539944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18476
    ⟨1539944, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1539832, by decide⟩,⟨1539877, by decide⟩,⟨1539943, by decide⟩]) unmarked_context_9_18476_1539944 node_context_9_18476_1539944
  intro a
  fin_cases a
  · exact context_10_73904_1468246
  · exact context_10_73905_1539832
  · exact context_10_73906_1539877
  · exact context_10_73907_1539943

theorem selected_cut_52614 : selected 11 ⟨1539991, by decide⟩
    (prefixPartial 10 73908) = some ⟨10, 2, 0, 1539991, 73908, 1181, 1048576⟩ := by
  decide +kernel

theorem context_10_73908_1539991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73908 ⟨1539991, by decide⟩ :=
  accepted_of_selected 10 73908 ⟨1539991, by decide⟩ ⟨10, 2, 0, 1539991, 73908, 1181, 1048576⟩
    (by decide) selected_cut_52614

theorem selected_cut_52615 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 73909) = some ⟨10, 1, 0, 1468874, 73909, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_73909_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73909 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 73909 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 73909, 1, 1048576⟩
    (by decide) selected_cut_52615

theorem selected_cut_52616 : selected 11 ⟨1540042, by decide⟩
    (prefixPartial 10 73910) = some ⟨10, 2, 0, 1540042, 73910, 1313, 1048576⟩ := by
  decide +kernel

theorem context_10_73910_1540042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73910 ⟨1540042, by decide⟩ :=
  accepted_of_selected 10 73910 ⟨1540042, by decide⟩ ⟨10, 2, 0, 1540042, 73910, 1313, 1048576⟩
    (by decide) selected_cut_52616

theorem selected_cut_52617 : selected 11 ⟨1540102, by decide⟩
    (prefixPartial 10 73911) = some ⟨10, 2, 0, 1540102, 73911, 1697, 1048576⟩ := by
  decide +kernel

theorem context_10_73911_1540102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73911 ⟨1540102, by decide⟩ :=
  accepted_of_selected 10 73911 ⟨1540102, by decide⟩ ⟨10, 2, 0, 1540102, 73911, 1697, 1048576⟩
    (by decide) selected_cut_52617

theorem unmarked_context_9_18477_1540103 : frontier 12 ⟨1540103, by decide⟩
    (prefixCache 9 18477) (prefixPartial 9 18477) = false := by
  decide +kernel

theorem node_context_9_18477_1540103 : EJMOriginalGlobalDAGData.nodes 12 ⟨1540103, by decide⟩ =
    .split (coordinate 9) (![⟨1539991, by decide⟩,⟨1468874, by decide⟩,⟨1540042, by decide⟩,⟨1540102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18477_1540103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18477 ⟨1540103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18477
    ⟨1540103, by decide⟩ (by decide) (![⟨1539991, by decide⟩,⟨1468874, by decide⟩,⟨1540042, by decide⟩,⟨1540102, by decide⟩]) unmarked_context_9_18477_1540103 node_context_9_18477_1540103
  intro a
  fin_cases a
  · exact context_10_73908_1539991
  · exact context_10_73909_1468874
  · exact context_10_73910_1540042
  · exact context_10_73911_1540102

theorem selected_cut_52618 : selected 12 ⟨1540209, by decide⟩
    (prefixPartial 9 18478) = some ⟨9, 2, 0, 1540209, 18478, 3009, 4194304⟩ := by
  decide +kernel

theorem context_9_18478_1540209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18478 ⟨1540209, by decide⟩ :=
  accepted_of_selected 9 18478 ⟨1540209, by decide⟩ ⟨9, 2, 0, 1540209, 18478, 3009, 4194304⟩
    (by decide) selected_cut_52618

theorem selected_cut_52619 : selected 12 ⟨1540260, by decide⟩
    (prefixPartial 9 18479) = some ⟨9, 2, 0, 1540260, 18479, 937, 4194304⟩ := by
  decide +kernel

theorem context_9_18479_1540260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18479 ⟨1540260, by decide⟩ :=
  accepted_of_selected 9 18479 ⟨1540260, by decide⟩ ⟨9, 2, 0, 1540260, 18479, 937, 4194304⟩
    (by decide) selected_cut_52619

theorem unmarked_context_8_4619_1540261 : frontier 13 ⟨1540261, by decide⟩
    (prefixCache 8 4619) (prefixPartial 8 4619) = false := by
  decide +kernel

theorem node_context_8_4619_1540261 : EJMOriginalGlobalDAGData.nodes 13 ⟨1540261, by decide⟩ =
    .split (coordinate 8) (![⟨1539944, by decide⟩,⟨1540103, by decide⟩,⟨1540209, by decide⟩,⟨1540260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4619_1540261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4619 ⟨1540261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4619
    ⟨1540261, by decide⟩ (by decide) (![⟨1539944, by decide⟩,⟨1540103, by decide⟩,⟨1540209, by decide⟩,⟨1540260, by decide⟩]) unmarked_context_8_4619_1540261 node_context_8_4619_1540261
  intro a
  fin_cases a
  · exact context_9_18476_1539944
  · exact context_9_18477_1540103
  · exact context_9_18478_1540209
  · exact context_9_18479_1540260

theorem unmarked_context_7_1154_1540262 : frontier 14 ⟨1540262, by decide⟩
    (prefixCache 7 1154) (prefixPartial 7 1154) = false := by
  decide +kernel

theorem node_context_7_1154_1540262 : EJMOriginalGlobalDAGData.nodes 14 ⟨1540262, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨1539727, by decide⟩,⟨979897, by decide⟩,⟨1540261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1154_1540262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1154 ⟨1540262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1154
    ⟨1540262, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨1539727, by decide⟩,⟨979897, by decide⟩,⟨1540261, by decide⟩]) unmarked_context_7_1154_1540262 node_context_7_1154_1540262
  intro a
  fin_cases a
  · exact context_8_4616_979897
  · exact context_8_4617_1539727
  · exact context_8_4618_979897
  · exact context_8_4619_1540261

theorem selected_cut_52620 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4620) = some ⟨8, 1, 0, 979897, 4620, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4620_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4620 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4620 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4620, 1, 16777216⟩
    (by decide) selected_cut_52620

theorem selected_cut_52621 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4621) = some ⟨8, 1, 0, 979897, 4621, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4621_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4621 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4621 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4621, 1, 16777216⟩
    (by decide) selected_cut_52621

theorem selected_cut_52622 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4622) = some ⟨8, 1, 0, 979897, 4622, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4622_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4622 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4622 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4622, 1, 16777216⟩
    (by decide) selected_cut_52622

theorem selected_cut_52623 : selected 12 ⟨1540491, by decide⟩
    (prefixPartial 9 18492) = some ⟨9, 2, 0, 1540491, 18492, 3621, 4194304⟩ := by
  decide +kernel

theorem context_9_18492_1540491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18492 ⟨1540491, by decide⟩ :=
  accepted_of_selected 9 18492 ⟨1540491, by decide⟩ ⟨9, 2, 0, 1540491, 18492, 3621, 4194304⟩
    (by decide) selected_cut_52623

theorem selected_cut_52624 : selected 11 ⟨1540586, by decide⟩
    (prefixPartial 10 73972) = some ⟨10, 2, 0, 1540586, 73972, 1777, 1048576⟩ := by
  decide +kernel

theorem context_10_73972_1540586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73972 ⟨1540586, by decide⟩ :=
  accepted_of_selected 10 73972 ⟨1540586, by decide⟩ ⟨10, 2, 0, 1540586, 73972, 1777, 1048576⟩
    (by decide) selected_cut_52624

theorem selected_cut_52625 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 73973) = some ⟨10, 1, 0, 1468874, 73973, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_73973_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73973 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 73973 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 73973, 1, 1048576⟩
    (by decide) selected_cut_52625

theorem selected_cut_52626 : selected 11 ⟨1540679, by decide⟩
    (prefixPartial 10 73974) = some ⟨10, 2, 0, 1540679, 73974, 1813, 1048576⟩ := by
  decide +kernel

theorem context_10_73974_1540679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73974 ⟨1540679, by decide⟩ :=
  accepted_of_selected 10 73974 ⟨1540679, by decide⟩ ⟨10, 2, 0, 1540679, 73974, 1813, 1048576⟩
    (by decide) selected_cut_52626

theorem selected_cut_52627 : selected 11 ⟨1540736, by decide⟩
    (prefixPartial 10 73975) = some ⟨10, 2, 0, 1540736, 73975, 1069, 1048576⟩ := by
  decide +kernel

theorem context_10_73975_1540736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73975 ⟨1540736, by decide⟩ :=
  accepted_of_selected 10 73975 ⟨1540736, by decide⟩ ⟨10, 2, 0, 1540736, 73975, 1069, 1048576⟩
    (by decide) selected_cut_52627

theorem unmarked_context_9_18493_1540737 : frontier 12 ⟨1540737, by decide⟩
    (prefixCache 9 18493) (prefixPartial 9 18493) = false := by
  decide +kernel

theorem node_context_9_18493_1540737 : EJMOriginalGlobalDAGData.nodes 12 ⟨1540737, by decide⟩ =
    .split (coordinate 9) (![⟨1540586, by decide⟩,⟨1468874, by decide⟩,⟨1540679, by decide⟩,⟨1540736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18493_1540737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18493 ⟨1540737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18493
    ⟨1540737, by decide⟩ (by decide) (![⟨1540586, by decide⟩,⟨1468874, by decide⟩,⟨1540679, by decide⟩,⟨1540736, by decide⟩]) unmarked_context_9_18493_1540737 node_context_9_18493_1540737
  intro a
  fin_cases a
  · exact context_10_73972_1540586
  · exact context_10_73973_1468874
  · exact context_10_73974_1540679
  · exact context_10_73975_1540736

theorem selected_cut_52628 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 18494) = some ⟨9, 1, 0, 33466, 18494, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_18494_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18494 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 18494 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 18494, 1, 4194304⟩
    (by decide) selected_cut_52628

theorem selected_cut_52629 : selected 12 ⟨1540795, by decide⟩
    (prefixPartial 9 18495) = some ⟨9, 2, 0, 1540795, 18495, 709, 4194304⟩ := by
  decide +kernel

theorem context_9_18495_1540795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18495 ⟨1540795, by decide⟩ :=
  accepted_of_selected 9 18495 ⟨1540795, by decide⟩ ⟨9, 2, 0, 1540795, 18495, 709, 4194304⟩
    (by decide) selected_cut_52629

theorem unmarked_context_8_4623_1540796 : frontier 13 ⟨1540796, by decide⟩
    (prefixCache 8 4623) (prefixPartial 8 4623) = false := by
  decide +kernel

theorem node_context_8_4623_1540796 : EJMOriginalGlobalDAGData.nodes 13 ⟨1540796, by decide⟩ =
    .split (coordinate 8) (![⟨1540491, by decide⟩,⟨1540737, by decide⟩,⟨33466, by decide⟩,⟨1540795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4623_1540796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4623 ⟨1540796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4623
    ⟨1540796, by decide⟩ (by decide) (![⟨1540491, by decide⟩,⟨1540737, by decide⟩,⟨33466, by decide⟩,⟨1540795, by decide⟩]) unmarked_context_8_4623_1540796 node_context_8_4623_1540796
  intro a
  fin_cases a
  · exact context_9_18492_1540491
  · exact context_9_18493_1540737
  · exact context_9_18494_33466
  · exact context_9_18495_1540795

theorem unmarked_context_7_1155_1540797 : frontier 14 ⟨1540797, by decide⟩
    (prefixCache 7 1155) (prefixPartial 7 1155) = false := by
  decide +kernel

theorem node_context_7_1155_1540797 : EJMOriginalGlobalDAGData.nodes 14 ⟨1540797, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨979897, by decide⟩,⟨979897, by decide⟩,⟨1540796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1155_1540797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1155 ⟨1540797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1155
    ⟨1540797, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨979897, by decide⟩,⟨979897, by decide⟩,⟨1540796, by decide⟩]) unmarked_context_7_1155_1540797 node_context_7_1155_1540797
  intro a
  fin_cases a
  · exact context_8_4620_979897
  · exact context_8_4621_979897
  · exact context_8_4622_979897
  · exact context_8_4623_1540796

theorem unmarked_context_6_288_1540798 : frontier 15 ⟨1540798, by decide⟩
    (prefixCache 6 288) (prefixPartial 6 288) = false := by
  decide +kernel

theorem node_context_6_288_1540798 : EJMOriginalGlobalDAGData.nodes 15 ⟨1540798, by decide⟩ =
    .split (coordinate 6) (![⟨1539246, by decide⟩,⟨1539247, by decide⟩,⟨1540262, by decide⟩,⟨1540797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_288_1540798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 288 ⟨1540798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 288
    ⟨1540798, by decide⟩ (by decide) (![⟨1539246, by decide⟩,⟨1539247, by decide⟩,⟨1540262, by decide⟩,⟨1540797, by decide⟩]) unmarked_context_6_288_1540798 node_context_6_288_1540798
  intro a
  fin_cases a
  · exact context_7_1152_1539246
  · exact context_7_1153_1539247
  · exact context_7_1154_1540262
  · exact context_7_1155_1540797

theorem selected_cut_52630 : selected 15 ⟨1475984, by decide⟩
    (prefixPartial 6 289) = some ⟨6, 1, 0, 1475984, 289, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_289_1475984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 289 ⟨1475984, by decide⟩ :=
  accepted_of_selected 6 289 ⟨1475984, by decide⟩ ⟨6, 1, 0, 1475984, 289, 1, 268435456⟩
    (by decide) selected_cut_52630

theorem selected_cut_52631 : selected 15 ⟨1070118, by decide⟩
    (prefixPartial 6 290) = some ⟨6, 1, 0, 1070118, 290, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_290_1070118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 290 ⟨1070118, by decide⟩ :=
  accepted_of_selected 6 290 ⟨1070118, by decide⟩ ⟨6, 1, 0, 1070118, 290, 1, 268435456⟩
    (by decide) selected_cut_52631

theorem selected_cut_52632 : selected 12 ⟨1540931, by decide⟩
    (prefixPartial 9 18624) = some ⟨9, 2, 0, 1540931, 18624, 1845, 4194304⟩ := by
  decide +kernel

theorem context_9_18624_1540931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18624 ⟨1540931, by decide⟩ :=
  accepted_of_selected 9 18624 ⟨1540931, by decide⟩ ⟨9, 2, 0, 1540931, 18624, 1845, 4194304⟩
    (by decide) selected_cut_52632

theorem selected_cut_52633 : selected 11 ⟨1540972, by decide⟩
    (prefixPartial 10 74500) = some ⟨10, 2, 0, 1540972, 74500, 601, 1048576⟩ := by
  decide +kernel

theorem context_10_74500_1540972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74500 ⟨1540972, by decide⟩ :=
  accepted_of_selected 10 74500 ⟨1540972, by decide⟩ ⟨10, 2, 0, 1540972, 74500, 601, 1048576⟩
    (by decide) selected_cut_52633

theorem selected_cut_52634 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 74501) = some ⟨10, 1, 0, 1468874, 74501, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74501_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74501 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 74501 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 74501, 1, 1048576⟩
    (by decide) selected_cut_52634

theorem selected_cut_52635 : selected 11 ⟨1541166, by decide⟩
    (prefixPartial 10 74502) = some ⟨10, 2, 0, 1541166, 74502, 2445, 1048576⟩ := by
  decide +kernel

theorem context_10_74502_1541166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74502 ⟨1541166, by decide⟩ :=
  accepted_of_selected 10 74502 ⟨1541166, by decide⟩ ⟨10, 2, 0, 1541166, 74502, 2445, 1048576⟩
    (by decide) selected_cut_52635

theorem selected_cut_52636 : selected 11 ⟨1541290, by decide⟩
    (prefixPartial 10 74503) = some ⟨10, 2, 0, 1541290, 74503, 1329, 1048576⟩ := by
  decide +kernel

theorem context_10_74503_1541290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74503 ⟨1541290, by decide⟩ :=
  accepted_of_selected 10 74503 ⟨1541290, by decide⟩ ⟨10, 2, 0, 1541290, 74503, 1329, 1048576⟩
    (by decide) selected_cut_52636

theorem unmarked_context_9_18625_1541291 : frontier 12 ⟨1541291, by decide⟩
    (prefixCache 9 18625) (prefixPartial 9 18625) = false := by
  decide +kernel

theorem node_context_9_18625_1541291 : EJMOriginalGlobalDAGData.nodes 12 ⟨1541291, by decide⟩ =
    .split (coordinate 9) (![⟨1540972, by decide⟩,⟨1468874, by decide⟩,⟨1541166, by decide⟩,⟨1541290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18625_1541291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18625 ⟨1541291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18625
    ⟨1541291, by decide⟩ (by decide) (![⟨1540972, by decide⟩,⟨1468874, by decide⟩,⟨1541166, by decide⟩,⟨1541290, by decide⟩]) unmarked_context_9_18625_1541291 node_context_9_18625_1541291
  intro a
  fin_cases a
  · exact context_10_74500_1540972
  · exact context_10_74501_1468874
  · exact context_10_74502_1541166
  · exact context_10_74503_1541290

theorem selected_cut_52637 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 18626) = some ⟨9, 1, 0, 33466, 18626, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_18626_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18626 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 18626 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 18626, 1, 4194304⟩
    (by decide) selected_cut_52637

theorem selected_cut_52638 : selected 12 ⟨1541336, by decide⟩
    (prefixPartial 9 18627) = some ⟨9, 2, 0, 1541336, 18627, 469, 4194304⟩ := by
  decide +kernel

theorem context_9_18627_1541336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18627 ⟨1541336, by decide⟩ :=
  accepted_of_selected 9 18627 ⟨1541336, by decide⟩ ⟨9, 2, 0, 1541336, 18627, 469, 4194304⟩
    (by decide) selected_cut_52638

theorem unmarked_context_8_4656_1541337 : frontier 13 ⟨1541337, by decide⟩
    (prefixCache 8 4656) (prefixPartial 8 4656) = false := by
  decide +kernel

theorem node_context_8_4656_1541337 : EJMOriginalGlobalDAGData.nodes 13 ⟨1541337, by decide⟩ =
    .split (coordinate 8) (![⟨1540931, by decide⟩,⟨1541291, by decide⟩,⟨33466, by decide⟩,⟨1541336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4656_1541337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4656 ⟨1541337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4656
    ⟨1541337, by decide⟩ (by decide) (![⟨1540931, by decide⟩,⟨1541291, by decide⟩,⟨33466, by decide⟩,⟨1541336, by decide⟩]) unmarked_context_8_4656_1541337 node_context_8_4656_1541337
  intro a
  fin_cases a
  · exact context_9_18624_1540931
  · exact context_9_18625_1541291
  · exact context_9_18626_33466
  · exact context_9_18627_1541336

theorem selected_cut_52639 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 74512) = some ⟨10, 1, 0, 1468246, 74512, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74512_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74512 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 74512 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 74512, 1, 1048576⟩
    (by decide) selected_cut_52639

theorem selected_cut_52640 : selected 11 ⟨1541432, by decide⟩
    (prefixPartial 10 74513) = some ⟨10, 2, 0, 1541432, 74513, 1581, 1048576⟩ := by
  decide +kernel

theorem context_10_74513_1541432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74513 ⟨1541432, by decide⟩ :=
  accepted_of_selected 10 74513 ⟨1541432, by decide⟩ ⟨10, 2, 0, 1541432, 74513, 1581, 1048576⟩
    (by decide) selected_cut_52640

theorem selected_cut_52641 : selected 11 ⟨1541489, by decide⟩
    (prefixPartial 10 74514) = some ⟨10, 2, 0, 1541489, 74514, 1469, 1048576⟩ := by
  decide +kernel

theorem context_10_74514_1541489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74514 ⟨1541489, by decide⟩ :=
  accepted_of_selected 10 74514 ⟨1541489, by decide⟩ ⟨10, 2, 0, 1541489, 74514, 1469, 1048576⟩
    (by decide) selected_cut_52641

theorem selected_cut_52642 : selected 11 ⟨1541542, by decide⟩
    (prefixPartial 10 74515) = some ⟨10, 2, 0, 1541542, 74515, 1385, 1048576⟩ := by
  decide +kernel

theorem context_10_74515_1541542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74515 ⟨1541542, by decide⟩ :=
  accepted_of_selected 10 74515 ⟨1541542, by decide⟩ ⟨10, 2, 0, 1541542, 74515, 1385, 1048576⟩
    (by decide) selected_cut_52642

theorem unmarked_context_9_18628_1541543 : frontier 12 ⟨1541543, by decide⟩
    (prefixCache 9 18628) (prefixPartial 9 18628) = false := by
  decide +kernel

theorem node_context_9_18628_1541543 : EJMOriginalGlobalDAGData.nodes 12 ⟨1541543, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1541432, by decide⟩,⟨1541489, by decide⟩,⟨1541542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18628_1541543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18628 ⟨1541543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18628
    ⟨1541543, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1541432, by decide⟩,⟨1541489, by decide⟩,⟨1541542, by decide⟩]) unmarked_context_9_18628_1541543 node_context_9_18628_1541543
  intro a
  fin_cases a
  · exact context_10_74512_1468246
  · exact context_10_74513_1541432
  · exact context_10_74514_1541489
  · exact context_10_74515_1541542

theorem selected_cut_52643 : selected 11 ⟨1541583, by decide⟩
    (prefixPartial 10 74516) = some ⟨10, 2, 0, 1541583, 74516, 597, 1048576⟩ := by
  decide +kernel

theorem context_10_74516_1541583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74516 ⟨1541583, by decide⟩ :=
  accepted_of_selected 10 74516 ⟨1541583, by decide⟩ ⟨10, 2, 0, 1541583, 74516, 597, 1048576⟩
    (by decide) selected_cut_52643

theorem selected_cut_52644 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 74517) = some ⟨10, 1, 0, 1468874, 74517, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74517_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74517 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 74517 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 74517, 1, 1048576⟩
    (by decide) selected_cut_52644

theorem selected_cut_52645 : selected 11 ⟨1541668, by decide⟩
    (prefixPartial 10 74518) = some ⟨10, 2, 0, 1541668, 74518, 2253, 1048576⟩ := by
  decide +kernel

theorem context_10_74518_1541668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74518 ⟨1541668, by decide⟩ :=
  accepted_of_selected 10 74518 ⟨1541668, by decide⟩ ⟨10, 2, 0, 1541668, 74518, 2253, 1048576⟩
    (by decide) selected_cut_52645

theorem selected_cut_52646 : selected 11 ⟨1541748, by decide⟩
    (prefixPartial 10 74519) = some ⟨10, 2, 0, 1541748, 74519, 1889, 1048576⟩ := by
  decide +kernel

theorem context_10_74519_1541748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74519 ⟨1541748, by decide⟩ :=
  accepted_of_selected 10 74519 ⟨1541748, by decide⟩ ⟨10, 2, 0, 1541748, 74519, 1889, 1048576⟩
    (by decide) selected_cut_52646

theorem unmarked_context_9_18629_1541749 : frontier 12 ⟨1541749, by decide⟩
    (prefixCache 9 18629) (prefixPartial 9 18629) = false := by
  decide +kernel

theorem node_context_9_18629_1541749 : EJMOriginalGlobalDAGData.nodes 12 ⟨1541749, by decide⟩ =
    .split (coordinate 9) (![⟨1541583, by decide⟩,⟨1468874, by decide⟩,⟨1541668, by decide⟩,⟨1541748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18629_1541749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18629 ⟨1541749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18629
    ⟨1541749, by decide⟩ (by decide) (![⟨1541583, by decide⟩,⟨1468874, by decide⟩,⟨1541668, by decide⟩,⟨1541748, by decide⟩]) unmarked_context_9_18629_1541749 node_context_9_18629_1541749
  intro a
  fin_cases a
  · exact context_10_74516_1541583
  · exact context_10_74517_1468874
  · exact context_10_74518_1541668
  · exact context_10_74519_1541748

theorem selected_cut_52647 : selected 12 ⟨1541816, by decide⟩
    (prefixPartial 9 18630) = some ⟨9, 2, 0, 1541816, 18630, 2193, 4194304⟩ := by
  decide +kernel

theorem context_9_18630_1541816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18630 ⟨1541816, by decide⟩ :=
  accepted_of_selected 9 18630 ⟨1541816, by decide⟩ ⟨9, 2, 0, 1541816, 18630, 2193, 4194304⟩
    (by decide) selected_cut_52647

theorem selected_cut_52648 : selected 12 ⟨1541847, by decide⟩
    (prefixPartial 9 18631) = some ⟨9, 2, 0, 1541847, 18631, 785, 4194304⟩ := by
  decide +kernel

theorem context_9_18631_1541847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18631 ⟨1541847, by decide⟩ :=
  accepted_of_selected 9 18631 ⟨1541847, by decide⟩ ⟨9, 2, 0, 1541847, 18631, 785, 4194304⟩
    (by decide) selected_cut_52648

theorem unmarked_context_8_4657_1541848 : frontier 13 ⟨1541848, by decide⟩
    (prefixCache 8 4657) (prefixPartial 8 4657) = false := by
  decide +kernel

theorem node_context_8_4657_1541848 : EJMOriginalGlobalDAGData.nodes 13 ⟨1541848, by decide⟩ =
    .split (coordinate 8) (![⟨1541543, by decide⟩,⟨1541749, by decide⟩,⟨1541816, by decide⟩,⟨1541847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4657_1541848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4657 ⟨1541848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4657
    ⟨1541848, by decide⟩ (by decide) (![⟨1541543, by decide⟩,⟨1541749, by decide⟩,⟨1541816, by decide⟩,⟨1541847, by decide⟩]) unmarked_context_8_4657_1541848 node_context_8_4657_1541848
  intro a
  fin_cases a
  · exact context_9_18628_1541543
  · exact context_9_18629_1541749
  · exact context_9_18630_1541816
  · exact context_9_18631_1541847

theorem selected_cut_52649 : selected 12 ⟨1541992, by decide⟩
    (prefixPartial 9 18632) = some ⟨9, 2, 0, 1541992, 18632, 2553, 4194304⟩ := by
  decide +kernel

theorem context_9_18632_1541992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18632 ⟨1541992, by decide⟩ :=
  accepted_of_selected 9 18632 ⟨1541992, by decide⟩ ⟨9, 2, 0, 1541992, 18632, 2553, 4194304⟩
    (by decide) selected_cut_52649

theorem selected_cut_52650 : selected 12 ⟨1542119, by decide⟩
    (prefixPartial 9 18633) = some ⟨9, 2, 0, 1542119, 18633, 3569, 4194304⟩ := by
  decide +kernel

theorem context_9_18633_1542119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18633 ⟨1542119, by decide⟩ :=
  accepted_of_selected 9 18633 ⟨1542119, by decide⟩ ⟨9, 2, 0, 1542119, 18633, 3569, 4194304⟩
    (by decide) selected_cut_52650

theorem selected_cut_52651 : selected 12 ⟨1542205, by decide⟩
    (prefixPartial 9 18634) = some ⟨9, 2, 0, 1542205, 18634, 2117, 4194304⟩ := by
  decide +kernel

theorem context_9_18634_1542205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18634 ⟨1542205, by decide⟩ :=
  accepted_of_selected 9 18634 ⟨1542205, by decide⟩ ⟨9, 2, 0, 1542205, 18634, 2117, 4194304⟩
    (by decide) selected_cut_52651

theorem selected_cut_52652 : selected 12 ⟨1542249, by decide⟩
    (prefixPartial 9 18635) = some ⟨9, 2, 0, 1542249, 18635, 669, 4194304⟩ := by
  decide +kernel

theorem context_9_18635_1542249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18635 ⟨1542249, by decide⟩ :=
  accepted_of_selected 9 18635 ⟨1542249, by decide⟩ ⟨9, 2, 0, 1542249, 18635, 669, 4194304⟩
    (by decide) selected_cut_52652

theorem unmarked_context_8_4658_1542250 : frontier 13 ⟨1542250, by decide⟩
    (prefixCache 8 4658) (prefixPartial 8 4658) = false := by
  decide +kernel

theorem node_context_8_4658_1542250 : EJMOriginalGlobalDAGData.nodes 13 ⟨1542250, by decide⟩ =
    .split (coordinate 8) (![⟨1541992, by decide⟩,⟨1542119, by decide⟩,⟨1542205, by decide⟩,⟨1542249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4658_1542250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4658 ⟨1542250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4658
    ⟨1542250, by decide⟩ (by decide) (![⟨1541992, by decide⟩,⟨1542119, by decide⟩,⟨1542205, by decide⟩,⟨1542249, by decide⟩]) unmarked_context_8_4658_1542250 node_context_8_4658_1542250
  intro a
  fin_cases a
  · exact context_9_18632_1541992
  · exact context_9_18633_1542119
  · exact context_9_18634_1542205
  · exact context_9_18635_1542249

theorem selected_cut_52653 : selected 12 ⟨1542320, by decide⟩
    (prefixPartial 9 18636) = some ⟨9, 2, 0, 1542320, 18636, 1057, 4194304⟩ := by
  decide +kernel

theorem context_9_18636_1542320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18636 ⟨1542320, by decide⟩ :=
  accepted_of_selected 9 18636 ⟨1542320, by decide⟩ ⟨9, 2, 0, 1542320, 18636, 1057, 4194304⟩
    (by decide) selected_cut_52653

theorem selected_cut_52654 : selected 12 ⟨1542418, by decide⟩
    (prefixPartial 9 18637) = some ⟨9, 2, 0, 1542418, 18637, 3017, 4194304⟩ := by
  decide +kernel

theorem context_9_18637_1542418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18637 ⟨1542418, by decide⟩ :=
  accepted_of_selected 9 18637 ⟨1542418, by decide⟩ ⟨9, 2, 0, 1542418, 18637, 3017, 4194304⟩
    (by decide) selected_cut_52654

theorem selected_cut_52655 : selected 12 ⟨1542494, by decide⟩
    (prefixPartial 9 18638) = some ⟨9, 2, 0, 1542494, 18638, 1885, 4194304⟩ := by
  decide +kernel

theorem context_9_18638_1542494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18638 ⟨1542494, by decide⟩ :=
  accepted_of_selected 9 18638 ⟨1542494, by decide⟩ ⟨9, 2, 0, 1542494, 18638, 1885, 4194304⟩
    (by decide) selected_cut_52655

theorem selected_cut_52656 : selected 12 ⟨1542526, by decide⟩
    (prefixPartial 9 18639) = some ⟨9, 2, 0, 1542526, 18639, 605, 4194304⟩ := by
  decide +kernel

theorem context_9_18639_1542526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18639 ⟨1542526, by decide⟩ :=
  accepted_of_selected 9 18639 ⟨1542526, by decide⟩ ⟨9, 2, 0, 1542526, 18639, 605, 4194304⟩
    (by decide) selected_cut_52656

theorem unmarked_context_8_4659_1542527 : frontier 13 ⟨1542527, by decide⟩
    (prefixCache 8 4659) (prefixPartial 8 4659) = false := by
  decide +kernel

theorem node_context_8_4659_1542527 : EJMOriginalGlobalDAGData.nodes 13 ⟨1542527, by decide⟩ =
    .split (coordinate 8) (![⟨1542320, by decide⟩,⟨1542418, by decide⟩,⟨1542494, by decide⟩,⟨1542526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4659_1542527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4659 ⟨1542527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4659
    ⟨1542527, by decide⟩ (by decide) (![⟨1542320, by decide⟩,⟨1542418, by decide⟩,⟨1542494, by decide⟩,⟨1542526, by decide⟩]) unmarked_context_8_4659_1542527 node_context_8_4659_1542527
  intro a
  fin_cases a
  · exact context_9_18636_1542320
  · exact context_9_18637_1542418
  · exact context_9_18638_1542494
  · exact context_9_18639_1542526

theorem unmarked_context_7_1164_1542528 : frontier 14 ⟨1542528, by decide⟩
    (prefixCache 7 1164) (prefixPartial 7 1164) = false := by
  decide +kernel

theorem node_context_7_1164_1542528 : EJMOriginalGlobalDAGData.nodes 14 ⟨1542528, by decide⟩ =
    .split (coordinate 7) (![⟨1541337, by decide⟩,⟨1541848, by decide⟩,⟨1542250, by decide⟩,⟨1542527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1164_1542528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1164 ⟨1542528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1164
    ⟨1542528, by decide⟩ (by decide) (![⟨1541337, by decide⟩,⟨1541848, by decide⟩,⟨1542250, by decide⟩,⟨1542527, by decide⟩]) unmarked_context_7_1164_1542528 node_context_7_1164_1542528
  intro a
  fin_cases a
  · exact context_8_4656_1541337
  · exact context_8_4657_1541848
  · exact context_8_4658_1542250
  · exact context_8_4659_1542527

theorem selected_cut_52657 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4660) = some ⟨8, 1, 0, 979897, 4660, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4660_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4660 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4660 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4660, 1, 16777216⟩
    (by decide) selected_cut_52657

theorem selected_cut_52658 : selected 12 ⟨1542771, by decide⟩
    (prefixPartial 9 18644) = some ⟨9, 2, 0, 1542771, 18644, 3921, 4194304⟩ := by
  decide +kernel

theorem context_9_18644_1542771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18644 ⟨1542771, by decide⟩ :=
  accepted_of_selected 9 18644 ⟨1542771, by decide⟩ ⟨9, 2, 0, 1542771, 18644, 3921, 4194304⟩
    (by decide) selected_cut_52658

theorem selected_cut_52659 : selected 11 ⟨1542899, by decide⟩
    (prefixPartial 10 74580) = some ⟨10, 2, 0, 1542899, 74580, 2693, 1048576⟩ := by
  decide +kernel

theorem context_10_74580_1542899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74580 ⟨1542899, by decide⟩ :=
  accepted_of_selected 10 74580 ⟨1542899, by decide⟩ ⟨10, 2, 0, 1542899, 74580, 2693, 1048576⟩
    (by decide) selected_cut_52659

theorem selected_cut_52660 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 74581) = some ⟨10, 1, 0, 1468874, 74581, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74581_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74581 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 74581 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 74581, 1, 1048576⟩
    (by decide) selected_cut_52660

theorem selected_cut_52661 : selected 11 ⟨1542994, by decide⟩
    (prefixPartial 10 74582) = some ⟨10, 2, 0, 1542994, 74582, 2365, 1048576⟩ := by
  decide +kernel

theorem context_10_74582_1542994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74582 ⟨1542994, by decide⟩ :=
  accepted_of_selected 10 74582 ⟨1542994, by decide⟩ ⟨10, 2, 0, 1542994, 74582, 2365, 1048576⟩
    (by decide) selected_cut_52661

theorem selected_cut_52662 : selected 11 ⟨1543073, by decide⟩
    (prefixPartial 10 74583) = some ⟨10, 2, 0, 1543073, 74583, 1901, 1048576⟩ := by
  decide +kernel

theorem context_10_74583_1543073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74583 ⟨1543073, by decide⟩ :=
  accepted_of_selected 10 74583 ⟨1543073, by decide⟩ ⟨10, 2, 0, 1543073, 74583, 1901, 1048576⟩
    (by decide) selected_cut_52662

theorem unmarked_context_9_18645_1543074 : frontier 12 ⟨1543074, by decide⟩
    (prefixCache 9 18645) (prefixPartial 9 18645) = false := by
  decide +kernel

theorem node_context_9_18645_1543074 : EJMOriginalGlobalDAGData.nodes 12 ⟨1543074, by decide⟩ =
    .split (coordinate 9) (![⟨1542899, by decide⟩,⟨1468874, by decide⟩,⟨1542994, by decide⟩,⟨1543073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18645_1543074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18645 ⟨1543074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18645
    ⟨1543074, by decide⟩ (by decide) (![⟨1542899, by decide⟩,⟨1468874, by decide⟩,⟨1542994, by decide⟩,⟨1543073, by decide⟩]) unmarked_context_9_18645_1543074 node_context_9_18645_1543074
  intro a
  fin_cases a
  · exact context_10_74580_1542899
  · exact context_10_74581_1468874
  · exact context_10_74582_1542994
  · exact context_10_74583_1543073

theorem selected_cut_52663 : selected 12 ⟨1543185, by decide⟩
    (prefixPartial 9 18646) = some ⟨9, 2, 0, 1543185, 18646, 2561, 4194304⟩ := by
  decide +kernel

theorem context_9_18646_1543185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18646 ⟨1543185, by decide⟩ :=
  accepted_of_selected 9 18646 ⟨1543185, by decide⟩ ⟨9, 2, 0, 1543185, 18646, 2561, 4194304⟩
    (by decide) selected_cut_52663

theorem selected_cut_52664 : selected 12 ⟨1543237, by decide⟩
    (prefixPartial 9 18647) = some ⟨9, 2, 0, 1543237, 18647, 793, 4194304⟩ := by
  decide +kernel

theorem context_9_18647_1543237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18647 ⟨1543237, by decide⟩ :=
  accepted_of_selected 9 18647 ⟨1543237, by decide⟩ ⟨9, 2, 0, 1543237, 18647, 793, 4194304⟩
    (by decide) selected_cut_52664

theorem unmarked_context_8_4661_1543238 : frontier 13 ⟨1543238, by decide⟩
    (prefixCache 8 4661) (prefixPartial 8 4661) = false := by
  decide +kernel

theorem node_context_8_4661_1543238 : EJMOriginalGlobalDAGData.nodes 13 ⟨1543238, by decide⟩ =
    .split (coordinate 8) (![⟨1542771, by decide⟩,⟨1543074, by decide⟩,⟨1543185, by decide⟩,⟨1543237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4661_1543238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4661 ⟨1543238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4661
    ⟨1543238, by decide⟩ (by decide) (![⟨1542771, by decide⟩,⟨1543074, by decide⟩,⟨1543185, by decide⟩,⟨1543237, by decide⟩]) unmarked_context_8_4661_1543238 node_context_8_4661_1543238
  intro a
  fin_cases a
  · exact context_9_18644_1542771
  · exact context_9_18645_1543074
  · exact context_9_18646_1543185
  · exact context_9_18647_1543237

theorem selected_cut_52665 : selected 12 ⟨1543346, by decide⟩
    (prefixPartial 9 18648) = some ⟨9, 2, 0, 1543346, 18648, 2405, 4194304⟩ := by
  decide +kernel

theorem context_9_18648_1543346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18648 ⟨1543346, by decide⟩ :=
  accepted_of_selected 9 18648 ⟨1543346, by decide⟩ ⟨9, 2, 0, 1543346, 18648, 2405, 4194304⟩
    (by decide) selected_cut_52665

theorem selected_cut_52666 : selected 11 ⟨1543425, by decide⟩
    (prefixPartial 10 74596) = some ⟨10, 2, 0, 1543425, 74596, 1881, 1048576⟩ := by
  decide +kernel

theorem context_10_74596_1543425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74596 ⟨1543425, by decide⟩ :=
  accepted_of_selected 10 74596 ⟨1543425, by decide⟩ ⟨10, 2, 0, 1543425, 74596, 1881, 1048576⟩
    (by decide) selected_cut_52666

theorem selected_cut_52667 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 74597) = some ⟨10, 1, 0, 1468874, 74597, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74597_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74597 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 74597 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 74597, 1, 1048576⟩
    (by decide) selected_cut_52667

theorem selected_cut_52668 : selected 11 ⟨1543504, by decide⟩
    (prefixPartial 10 74598) = some ⟨10, 2, 0, 1543504, 74598, 2053, 1048576⟩ := by
  decide +kernel

theorem context_10_74598_1543504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74598 ⟨1543504, by decide⟩ :=
  accepted_of_selected 10 74598 ⟨1543504, by decide⟩ ⟨10, 2, 0, 1543504, 74598, 2053, 1048576⟩
    (by decide) selected_cut_52668

theorem selected_cut_52669 : selected 11 ⟨1543534, by decide⟩
    (prefixPartial 10 74599) = some ⟨10, 2, 0, 1543534, 74599, 765, 1048576⟩ := by
  decide +kernel

theorem context_10_74599_1543534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74599 ⟨1543534, by decide⟩ :=
  accepted_of_selected 10 74599 ⟨1543534, by decide⟩ ⟨10, 2, 0, 1543534, 74599, 765, 1048576⟩
    (by decide) selected_cut_52669

theorem unmarked_context_9_18649_1543535 : frontier 12 ⟨1543535, by decide⟩
    (prefixCache 9 18649) (prefixPartial 9 18649) = false := by
  decide +kernel

theorem node_context_9_18649_1543535 : EJMOriginalGlobalDAGData.nodes 12 ⟨1543535, by decide⟩ =
    .split (coordinate 9) (![⟨1543425, by decide⟩,⟨1468874, by decide⟩,⟨1543504, by decide⟩,⟨1543534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18649_1543535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18649 ⟨1543535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18649
    ⟨1543535, by decide⟩ (by decide) (![⟨1543425, by decide⟩,⟨1468874, by decide⟩,⟨1543504, by decide⟩,⟨1543534, by decide⟩]) unmarked_context_9_18649_1543535 node_context_9_18649_1543535
  intro a
  fin_cases a
  · exact context_10_74596_1543425
  · exact context_10_74597_1468874
  · exact context_10_74598_1543504
  · exact context_10_74599_1543534

theorem selected_cut_52670 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 18650) = some ⟨9, 1, 0, 33466, 18650, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_18650_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18650 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 18650 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 18650, 1, 4194304⟩
    (by decide) selected_cut_52670

theorem selected_cut_52671 : selected 12 ⟨1543577, by decide⟩
    (prefixPartial 9 18651) = some ⟨9, 2, 0, 1543577, 18651, 481, 4194304⟩ := by
  decide +kernel

theorem context_9_18651_1543577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18651 ⟨1543577, by decide⟩ :=
  accepted_of_selected 9 18651 ⟨1543577, by decide⟩ ⟨9, 2, 0, 1543577, 18651, 481, 4194304⟩
    (by decide) selected_cut_52671

theorem unmarked_context_8_4662_1543578 : frontier 13 ⟨1543578, by decide⟩
    (prefixCache 8 4662) (prefixPartial 8 4662) = false := by
  decide +kernel

theorem node_context_8_4662_1543578 : EJMOriginalGlobalDAGData.nodes 13 ⟨1543578, by decide⟩ =
    .split (coordinate 8) (![⟨1543346, by decide⟩,⟨1543535, by decide⟩,⟨33466, by decide⟩,⟨1543577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4662_1543578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4662 ⟨1543578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4662
    ⟨1543578, by decide⟩ (by decide) (![⟨1543346, by decide⟩,⟨1543535, by decide⟩,⟨33466, by decide⟩,⟨1543577, by decide⟩]) unmarked_context_8_4662_1543578 node_context_8_4662_1543578
  intro a
  fin_cases a
  · exact context_9_18648_1543346
  · exact context_9_18649_1543535
  · exact context_9_18650_33466
  · exact context_9_18651_1543577

theorem selected_cut_52672 : selected 12 ⟨1543710, by decide⟩
    (prefixPartial 9 18652) = some ⟨9, 2, 0, 1543710, 18652, 3233, 4194304⟩ := by
  decide +kernel

theorem context_9_18652_1543710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18652 ⟨1543710, by decide⟩ :=
  accepted_of_selected 9 18652 ⟨1543710, by decide⟩ ⟨9, 2, 0, 1543710, 18652, 3233, 4194304⟩
    (by decide) selected_cut_52672

theorem selected_cut_52673 : selected 11 ⟨1543763, by decide⟩
    (prefixPartial 10 74612) = some ⟨10, 2, 0, 1543763, 74612, 1789, 1048576⟩ := by
  decide +kernel

theorem context_10_74612_1543763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74612 ⟨1543763, by decide⟩ :=
  accepted_of_selected 10 74612 ⟨1543763, by decide⟩ ⟨10, 2, 0, 1543763, 74612, 1789, 1048576⟩
    (by decide) selected_cut_52673

theorem selected_cut_52674 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 74613) = some ⟨10, 1, 0, 1468874, 74613, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74613_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74613 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 74613 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 74613, 1, 1048576⟩
    (by decide) selected_cut_52674

theorem selected_cut_52675 : selected 11 ⟨1543800, by decide⟩
    (prefixPartial 10 74614) = some ⟨10, 2, 0, 1543800, 74614, 1445, 1048576⟩ := by
  decide +kernel

theorem context_10_74614_1543800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74614 ⟨1543800, by decide⟩ :=
  accepted_of_selected 10 74614 ⟨1543800, by decide⟩ ⟨10, 2, 0, 1543800, 74614, 1445, 1048576⟩
    (by decide) selected_cut_52675

theorem selected_cut_52676 : selected 11 ⟨1543852, by decide⟩
    (prefixPartial 10 74615) = some ⟨10, 2, 0, 1543852, 74615, 1985, 1048576⟩ := by
  decide +kernel

theorem context_10_74615_1543852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74615 ⟨1543852, by decide⟩ :=
  accepted_of_selected 10 74615 ⟨1543852, by decide⟩ ⟨10, 2, 0, 1543852, 74615, 1985, 1048576⟩
    (by decide) selected_cut_52676

theorem unmarked_context_9_18653_1543853 : frontier 12 ⟨1543853, by decide⟩
    (prefixCache 9 18653) (prefixPartial 9 18653) = false := by
  decide +kernel

theorem node_context_9_18653_1543853 : EJMOriginalGlobalDAGData.nodes 12 ⟨1543853, by decide⟩ =
    .split (coordinate 9) (![⟨1543763, by decide⟩,⟨1468874, by decide⟩,⟨1543800, by decide⟩,⟨1543852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18653_1543853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18653 ⟨1543853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18653
    ⟨1543853, by decide⟩ (by decide) (![⟨1543763, by decide⟩,⟨1468874, by decide⟩,⟨1543800, by decide⟩,⟨1543852, by decide⟩]) unmarked_context_9_18653_1543853 node_context_9_18653_1543853
  intro a
  fin_cases a
  · exact context_10_74612_1543763
  · exact context_10_74613_1468874
  · exact context_10_74614_1543800
  · exact context_10_74615_1543852

theorem selected_cut_52677 : selected 12 ⟨1543921, by decide⟩
    (prefixPartial 9 18654) = some ⟨9, 2, 0, 1543921, 18654, 2485, 4194304⟩ := by
  decide +kernel

theorem context_9_18654_1543921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18654 ⟨1543921, by decide⟩ :=
  accepted_of_selected 9 18654 ⟨1543921, by decide⟩ ⟨9, 2, 0, 1543921, 18654, 2485, 4194304⟩
    (by decide) selected_cut_52677

theorem selected_cut_52678 : selected 12 ⟨1543961, by decide⟩
    (prefixPartial 9 18655) = some ⟨9, 2, 0, 1543961, 18655, 945, 4194304⟩ := by
  decide +kernel

theorem context_9_18655_1543961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18655 ⟨1543961, by decide⟩ :=
  accepted_of_selected 9 18655 ⟨1543961, by decide⟩ ⟨9, 2, 0, 1543961, 18655, 945, 4194304⟩
    (by decide) selected_cut_52678

theorem unmarked_context_8_4663_1543962 : frontier 13 ⟨1543962, by decide⟩
    (prefixCache 8 4663) (prefixPartial 8 4663) = false := by
  decide +kernel

theorem node_context_8_4663_1543962 : EJMOriginalGlobalDAGData.nodes 13 ⟨1543962, by decide⟩ =
    .split (coordinate 8) (![⟨1543710, by decide⟩,⟨1543853, by decide⟩,⟨1543921, by decide⟩,⟨1543961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4663_1543962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4663 ⟨1543962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4663
    ⟨1543962, by decide⟩ (by decide) (![⟨1543710, by decide⟩,⟨1543853, by decide⟩,⟨1543921, by decide⟩,⟨1543961, by decide⟩]) unmarked_context_8_4663_1543962 node_context_8_4663_1543962
  intro a
  fin_cases a
  · exact context_9_18652_1543710
  · exact context_9_18653_1543853
  · exact context_9_18654_1543921
  · exact context_9_18655_1543961

theorem unmarked_context_7_1165_1543963 : frontier 14 ⟨1543963, by decide⟩
    (prefixCache 7 1165) (prefixPartial 7 1165) = false := by
  decide +kernel

theorem node_context_7_1165_1543963 : EJMOriginalGlobalDAGData.nodes 14 ⟨1543963, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨1543238, by decide⟩,⟨1543578, by decide⟩,⟨1543962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1165_1543963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1165 ⟨1543963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1165
    ⟨1543963, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨1543238, by decide⟩,⟨1543578, by decide⟩,⟨1543962, by decide⟩]) unmarked_context_7_1165_1543963 node_context_7_1165_1543963
  intro a
  fin_cases a
  · exact context_8_4660_979897
  · exact context_8_4661_1543238
  · exact context_8_4662_1543578
  · exact context_8_4663_1543962

theorem selected_cut_52679 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4664) = some ⟨8, 1, 0, 979897, 4664, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4664_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4664 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4664 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4664, 1, 16777216⟩
    (by decide) selected_cut_52679

theorem selected_cut_52680 : selected 12 ⟨1544043, by decide⟩
    (prefixPartial 9 18660) = some ⟨9, 2, 0, 1544043, 18660, 1473, 4194304⟩ := by
  decide +kernel

theorem context_9_18660_1544043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18660 ⟨1544043, by decide⟩ :=
  accepted_of_selected 9 18660 ⟨1544043, by decide⟩ ⟨9, 2, 0, 1544043, 18660, 1473, 4194304⟩
    (by decide) selected_cut_52680

theorem selected_cut_52681 : selected 11 ⟨1544116, by decide⟩
    (prefixPartial 10 74644) = some ⟨10, 2, 0, 1544116, 74644, 1949, 1048576⟩ := by
  decide +kernel

theorem context_10_74644_1544116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74644 ⟨1544116, by decide⟩ :=
  accepted_of_selected 10 74644 ⟨1544116, by decide⟩ ⟨10, 2, 0, 1544116, 74644, 1949, 1048576⟩
    (by decide) selected_cut_52681

theorem selected_cut_52682 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 74645) = some ⟨10, 1, 0, 1468874, 74645, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74645_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74645 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 74645 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 74645, 1, 1048576⟩
    (by decide) selected_cut_52682

theorem selected_cut_52683 : selected 11 ⟨1544186, by decide⟩
    (prefixPartial 10 74646) = some ⟨10, 2, 0, 1544186, 74646, 1917, 1048576⟩ := by
  decide +kernel

theorem context_10_74646_1544186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74646 ⟨1544186, by decide⟩ :=
  accepted_of_selected 10 74646 ⟨1544186, by decide⟩ ⟨10, 2, 0, 1544186, 74646, 1917, 1048576⟩
    (by decide) selected_cut_52683

theorem selected_cut_52684 : selected 11 ⟨1544242, by decide⟩
    (prefixPartial 10 74647) = some ⟨10, 2, 0, 1544242, 74647, 1257, 1048576⟩ := by
  decide +kernel

theorem context_10_74647_1544242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74647 ⟨1544242, by decide⟩ :=
  accepted_of_selected 10 74647 ⟨1544242, by decide⟩ ⟨10, 2, 0, 1544242, 74647, 1257, 1048576⟩
    (by decide) selected_cut_52684

theorem unmarked_context_9_18661_1544243 : frontier 12 ⟨1544243, by decide⟩
    (prefixCache 9 18661) (prefixPartial 9 18661) = false := by
  decide +kernel

theorem node_context_9_18661_1544243 : EJMOriginalGlobalDAGData.nodes 12 ⟨1544243, by decide⟩ =
    .split (coordinate 9) (![⟨1544116, by decide⟩,⟨1468874, by decide⟩,⟨1544186, by decide⟩,⟨1544242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18661_1544243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18661 ⟨1544243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18661
    ⟨1544243, by decide⟩ (by decide) (![⟨1544116, by decide⟩,⟨1468874, by decide⟩,⟨1544186, by decide⟩,⟨1544242, by decide⟩]) unmarked_context_9_18661_1544243 node_context_9_18661_1544243
  intro a
  fin_cases a
  · exact context_10_74644_1544116
  · exact context_10_74645_1468874
  · exact context_10_74646_1544186
  · exact context_10_74647_1544242

theorem selected_cut_52685 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 18662) = some ⟨9, 1, 0, 33466, 18662, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_18662_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18662 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 18662 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 18662, 1, 4194304⟩
    (by decide) selected_cut_52685

theorem selected_cut_52686 : selected 12 ⟨1544269, by decide⟩
    (prefixPartial 9 18663) = some ⟨9, 2, 0, 1544269, 18663, 521, 4194304⟩ := by
  decide +kernel

theorem context_9_18663_1544269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18663 ⟨1544269, by decide⟩ :=
  accepted_of_selected 9 18663 ⟨1544269, by decide⟩ ⟨9, 2, 0, 1544269, 18663, 521, 4194304⟩
    (by decide) selected_cut_52686

theorem unmarked_context_8_4665_1544270 : frontier 13 ⟨1544270, by decide⟩
    (prefixCache 8 4665) (prefixPartial 8 4665) = false := by
  decide +kernel

theorem node_context_8_4665_1544270 : EJMOriginalGlobalDAGData.nodes 13 ⟨1544270, by decide⟩ =
    .split (coordinate 8) (![⟨1544043, by decide⟩,⟨1544243, by decide⟩,⟨33466, by decide⟩,⟨1544269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4665_1544270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4665 ⟨1544270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4665
    ⟨1544270, by decide⟩ (by decide) (![⟨1544043, by decide⟩,⟨1544243, by decide⟩,⟨33466, by decide⟩,⟨1544269, by decide⟩]) unmarked_context_8_4665_1544270 node_context_8_4665_1544270
  intro a
  fin_cases a
  · exact context_9_18660_1544043
  · exact context_9_18661_1544243
  · exact context_9_18662_33466
  · exact context_9_18663_1544269

theorem selected_cut_52687 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4666) = some ⟨8, 1, 0, 979897, 4666, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4666_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4666 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4666 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4666, 1, 16777216⟩
    (by decide) selected_cut_52687

theorem selected_cut_52688 : selected 12 ⟨1544327, by decide⟩
    (prefixPartial 9 18668) = some ⟨9, 2, 0, 1544327, 18668, 1201, 4194304⟩ := by
  decide +kernel

theorem context_9_18668_1544327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18668 ⟨1544327, by decide⟩ :=
  accepted_of_selected 9 18668 ⟨1544327, by decide⟩ ⟨9, 2, 0, 1544327, 18668, 1201, 4194304⟩
    (by decide) selected_cut_52688

theorem selected_cut_52689 : selected 11 ⟨1544356, by decide⟩
    (prefixPartial 10 74676) = some ⟨10, 2, 0, 1544356, 74676, 1133, 1048576⟩ := by
  decide +kernel

theorem context_10_74676_1544356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74676 ⟨1544356, by decide⟩ :=
  accepted_of_selected 10 74676 ⟨1544356, by decide⟩ ⟨10, 2, 0, 1544356, 74676, 1133, 1048576⟩
    (by decide) selected_cut_52689

theorem selected_cut_52690 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 74677) = some ⟨10, 1, 0, 1468874, 74677, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74677_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74677 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 74677 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 74677, 1, 1048576⟩
    (by decide) selected_cut_52690

theorem selected_cut_52691 : selected 11 ⟨1544383, by decide⟩
    (prefixPartial 10 74678) = some ⟨10, 2, 0, 1544383, 74678, 1421, 1048576⟩ := by
  decide +kernel

theorem context_10_74678_1544383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74678 ⟨1544383, by decide⟩ :=
  accepted_of_selected 10 74678 ⟨1544383, by decide⟩ ⟨10, 2, 0, 1544383, 74678, 1421, 1048576⟩
    (by decide) selected_cut_52691

theorem selected_cut_52692 : selected 11 ⟨1544433, by decide⟩
    (prefixPartial 10 74679) = some ⟨10, 2, 0, 1544433, 74679, 1749, 1048576⟩ := by
  decide +kernel

theorem context_10_74679_1544433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74679 ⟨1544433, by decide⟩ :=
  accepted_of_selected 10 74679 ⟨1544433, by decide⟩ ⟨10, 2, 0, 1544433, 74679, 1749, 1048576⟩
    (by decide) selected_cut_52692

theorem unmarked_context_9_18669_1544434 : frontier 12 ⟨1544434, by decide⟩
    (prefixCache 9 18669) (prefixPartial 9 18669) = false := by
  decide +kernel

theorem node_context_9_18669_1544434 : EJMOriginalGlobalDAGData.nodes 12 ⟨1544434, by decide⟩ =
    .split (coordinate 9) (![⟨1544356, by decide⟩,⟨1468874, by decide⟩,⟨1544383, by decide⟩,⟨1544433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18669_1544434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18669 ⟨1544434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18669
    ⟨1544434, by decide⟩ (by decide) (![⟨1544356, by decide⟩,⟨1468874, by decide⟩,⟨1544383, by decide⟩,⟨1544433, by decide⟩]) unmarked_context_9_18669_1544434 node_context_9_18669_1544434
  intro a
  fin_cases a
  · exact context_10_74676_1544356
  · exact context_10_74677_1468874
  · exact context_10_74678_1544383
  · exact context_10_74679_1544433

theorem selected_cut_52693 : selected 12 ⟨1544563, by decide⟩
    (prefixPartial 9 18670) = some ⟨9, 2, 0, 1544563, 18670, 3765, 4194304⟩ := by
  decide +kernel

theorem context_9_18670_1544563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18670 ⟨1544563, by decide⟩ :=
  accepted_of_selected 9 18670 ⟨1544563, by decide⟩ ⟨9, 2, 0, 1544563, 18670, 3765, 4194304⟩
    (by decide) selected_cut_52693

theorem selected_cut_52694 : selected 12 ⟨1544605, by decide⟩
    (prefixPartial 9 18671) = some ⟨9, 2, 0, 1544605, 18671, 945, 4194304⟩ := by
  decide +kernel

theorem context_9_18671_1544605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18671 ⟨1544605, by decide⟩ :=
  accepted_of_selected 9 18671 ⟨1544605, by decide⟩ ⟨9, 2, 0, 1544605, 18671, 945, 4194304⟩
    (by decide) selected_cut_52694

theorem unmarked_context_8_4667_1544606 : frontier 13 ⟨1544606, by decide⟩
    (prefixCache 8 4667) (prefixPartial 8 4667) = false := by
  decide +kernel

theorem node_context_8_4667_1544606 : EJMOriginalGlobalDAGData.nodes 13 ⟨1544606, by decide⟩ =
    .split (coordinate 8) (![⟨1544327, by decide⟩,⟨1544434, by decide⟩,⟨1544563, by decide⟩,⟨1544605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4667_1544606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4667 ⟨1544606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4667
    ⟨1544606, by decide⟩ (by decide) (![⟨1544327, by decide⟩,⟨1544434, by decide⟩,⟨1544563, by decide⟩,⟨1544605, by decide⟩]) unmarked_context_8_4667_1544606 node_context_8_4667_1544606
  intro a
  fin_cases a
  · exact context_9_18668_1544327
  · exact context_9_18669_1544434
  · exact context_9_18670_1544563
  · exact context_9_18671_1544605

theorem unmarked_context_7_1166_1544607 : frontier 14 ⟨1544607, by decide⟩
    (prefixCache 7 1166) (prefixPartial 7 1166) = false := by
  decide +kernel

theorem node_context_7_1166_1544607 : EJMOriginalGlobalDAGData.nodes 14 ⟨1544607, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨1544270, by decide⟩,⟨979897, by decide⟩,⟨1544606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1166_1544607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1166 ⟨1544607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1166
    ⟨1544607, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨1544270, by decide⟩,⟨979897, by decide⟩,⟨1544606, by decide⟩]) unmarked_context_7_1166_1544607 node_context_7_1166_1544607
  intro a
  fin_cases a
  · exact context_8_4664_979897
  · exact context_8_4665_1544270
  · exact context_8_4666_979897
  · exact context_8_4667_1544606

theorem selected_cut_52695 : selected 14 ⟨1544919, by decide⟩
    (prefixPartial 7 1167) = some ⟨7, 2, 0, 1544919, 1167, 3245, 67108864⟩ := by
  decide +kernel

theorem context_7_1167_1544919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1167 ⟨1544919, by decide⟩ :=
  accepted_of_selected 7 1167 ⟨1544919, by decide⟩ ⟨7, 2, 0, 1544919, 1167, 3245, 67108864⟩
    (by decide) selected_cut_52695

theorem unmarked_context_6_291_1544920 : frontier 15 ⟨1544920, by decide⟩
    (prefixCache 6 291) (prefixPartial 6 291) = false := by
  decide +kernel

theorem node_context_6_291_1544920 : EJMOriginalGlobalDAGData.nodes 15 ⟨1544920, by decide⟩ =
    .split (coordinate 6) (![⟨1542528, by decide⟩,⟨1543963, by decide⟩,⟨1544607, by decide⟩,⟨1544919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_291_1544920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 291 ⟨1544920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 291
    ⟨1544920, by decide⟩ (by decide) (![⟨1542528, by decide⟩,⟨1543963, by decide⟩,⟨1544607, by decide⟩,⟨1544919, by decide⟩]) unmarked_context_6_291_1544920 node_context_6_291_1544920
  intro a
  fin_cases a
  · exact context_7_1164_1542528
  · exact context_7_1165_1543963
  · exact context_7_1166_1544607
  · exact context_7_1167_1544919

theorem unmarked_context_5_72_1544921 : frontier 16 ⟨1544921, by decide⟩
    (prefixCache 5 72) (prefixPartial 5 72) = false := by
  decide +kernel

theorem node_context_5_72_1544921 : EJMOriginalGlobalDAGData.nodes 16 ⟨1544921, by decide⟩ =
    .split (coordinate 5) (![⟨1540798, by decide⟩,⟨1475984, by decide⟩,⟨1070118, by decide⟩,⟨1544920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_72_1544921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 72 ⟨1544921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 72
    ⟨1544921, by decide⟩ (by decide) (![⟨1540798, by decide⟩,⟨1475984, by decide⟩,⟨1070118, by decide⟩,⟨1544920, by decide⟩]) unmarked_context_5_72_1544921 node_context_5_72_1544921
  intro a
  fin_cases a
  · exact context_6_288_1540798
  · exact context_6_289_1475984
  · exact context_6_290_1070118
  · exact context_6_291_1544920

theorem selected_cut_52696 : selected 13 ⟨1487329, by decide⟩
    (prefixPartial 8 4672) = some ⟨8, 1, 0, 1487329, 4672, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4672_1487329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4672 ⟨1487329, by decide⟩ :=
  accepted_of_selected 8 4672 ⟨1487329, by decide⟩ ⟨8, 1, 0, 1487329, 4672, 1, 16777216⟩
    (by decide) selected_cut_52696

theorem selected_cut_52697 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 74768) = some ⟨10, 1, 0, 1468246, 74768, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74768_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74768 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 74768 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 74768, 1, 1048576⟩
    (by decide) selected_cut_52697

theorem selected_cut_52698 : selected 11 ⟨1545152, by decide⟩
    (prefixPartial 10 74769) = some ⟨10, 2, 0, 1545152, 74769, 2461, 1048576⟩ := by
  decide +kernel

theorem context_10_74769_1545152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74769 ⟨1545152, by decide⟩ :=
  accepted_of_selected 10 74769 ⟨1545152, by decide⟩ ⟨10, 2, 0, 1545152, 74769, 2461, 1048576⟩
    (by decide) selected_cut_52698

theorem selected_cut_52699 : selected 11 ⟨1545243, by decide⟩
    (prefixPartial 10 74770) = some ⟨10, 2, 0, 1545243, 74770, 1245, 1048576⟩ := by
  decide +kernel

theorem context_10_74770_1545243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74770 ⟨1545243, by decide⟩ :=
  accepted_of_selected 10 74770 ⟨1545243, by decide⟩ ⟨10, 2, 0, 1545243, 74770, 1245, 1048576⟩
    (by decide) selected_cut_52699

theorem selected_cut_52700 : selected 11 ⟨1545335, by decide⟩
    (prefixPartial 10 74771) = some ⟨10, 2, 0, 1545335, 74771, 1045, 1048576⟩ := by
  decide +kernel

theorem context_10_74771_1545335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74771 ⟨1545335, by decide⟩ :=
  accepted_of_selected 10 74771 ⟨1545335, by decide⟩ ⟨10, 2, 0, 1545335, 74771, 1045, 1048576⟩
    (by decide) selected_cut_52700

theorem unmarked_context_9_18692_1545336 : frontier 12 ⟨1545336, by decide⟩
    (prefixCache 9 18692) (prefixPartial 9 18692) = false := by
  decide +kernel

theorem node_context_9_18692_1545336 : EJMOriginalGlobalDAGData.nodes 12 ⟨1545336, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1545152, by decide⟩,⟨1545243, by decide⟩,⟨1545335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18692_1545336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18692 ⟨1545336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18692
    ⟨1545336, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1545152, by decide⟩,⟨1545243, by decide⟩,⟨1545335, by decide⟩]) unmarked_context_9_18692_1545336 node_context_9_18692_1545336
  intro a
  fin_cases a
  · exact context_10_74768_1468246
  · exact context_10_74769_1545152
  · exact context_10_74770_1545243
  · exact context_10_74771_1545335

theorem selected_cut_52701 : selected 12 ⟨1545467, by decide⟩
    (prefixPartial 9 18693) = some ⟨9, 2, 0, 1545467, 18693, 1517, 4194304⟩ := by
  decide +kernel

theorem context_9_18693_1545467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18693 ⟨1545467, by decide⟩ :=
  accepted_of_selected 9 18693 ⟨1545467, by decide⟩ ⟨9, 2, 0, 1545467, 18693, 1517, 4194304⟩
    (by decide) selected_cut_52701

theorem selected_cut_52702 : selected 12 ⟨1545530, by decide⟩
    (prefixPartial 9 18694) = some ⟨9, 2, 0, 1545530, 18694, 721, 4194304⟩ := by
  decide +kernel

theorem context_9_18694_1545530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18694 ⟨1545530, by decide⟩ :=
  accepted_of_selected 9 18694 ⟨1545530, by decide⟩ ⟨9, 2, 0, 1545530, 18694, 721, 4194304⟩
    (by decide) selected_cut_52702

theorem selected_cut_52703 : selected 12 ⟨1545546, by decide⟩
    (prefixPartial 9 18695) = some ⟨9, 2, 0, 1545546, 18695, 205, 4194304⟩ := by
  decide +kernel

theorem context_9_18695_1545546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18695 ⟨1545546, by decide⟩ :=
  accepted_of_selected 9 18695 ⟨1545546, by decide⟩ ⟨9, 2, 0, 1545546, 18695, 205, 4194304⟩
    (by decide) selected_cut_52703

theorem unmarked_context_8_4673_1545547 : frontier 13 ⟨1545547, by decide⟩
    (prefixCache 8 4673) (prefixPartial 8 4673) = false := by
  decide +kernel

theorem node_context_8_4673_1545547 : EJMOriginalGlobalDAGData.nodes 13 ⟨1545547, by decide⟩ =
    .split (coordinate 8) (![⟨1545336, by decide⟩,⟨1545467, by decide⟩,⟨1545530, by decide⟩,⟨1545546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4673_1545547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4673 ⟨1545547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4673
    ⟨1545547, by decide⟩ (by decide) (![⟨1545336, by decide⟩,⟨1545467, by decide⟩,⟨1545530, by decide⟩,⟨1545546, by decide⟩]) unmarked_context_8_4673_1545547 node_context_8_4673_1545547
  intro a
  fin_cases a
  · exact context_9_18692_1545336
  · exact context_9_18693_1545467
  · exact context_9_18694_1545530
  · exact context_9_18695_1545546

theorem selected_cut_52704 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 4674) = some ⟨8, 1, 0, 1364555, 4674, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4674_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4674 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 4674 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 4674, 1, 16777216⟩
    (by decide) selected_cut_52704

theorem selected_cut_52705 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 74800) = some ⟨10, 1, 0, 1468246, 74800, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_74800_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 74800 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 74800 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 74800, 1, 1048576⟩
    (by decide) selected_cut_52705

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
