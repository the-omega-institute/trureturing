/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover135
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_13059 : selected 9 ⟨343617, by decide⟩
    (prefixPartial 12 26466) = some ⟨12, 2, 0, 343617, 26466, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_26466_343617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26466 ⟨343617, by decide⟩ :=
  accepted_of_selected 12 26466 ⟨343617, by decide⟩ ⟨12, 2, 0, 343617, 26466, 3989, 65536⟩
    (by decide) selected_cut_13059

theorem selected_cut_13060 : selected 9 ⟨343672, by decide⟩
    (prefixPartial 12 26467) = some ⟨12, 2, 0, 343672, 26467, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_26467_343672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26467 ⟨343672, by decide⟩ :=
  accepted_of_selected 12 26467 ⟨343672, by decide⟩ ⟨12, 2, 0, 343672, 26467, 3953, 65536⟩
    (by decide) selected_cut_13060

theorem unmarked_context_11_6616_343673 : frontier 10 ⟨343673, by decide⟩
    (prefixCache 11 6616) (prefixPartial 11 6616) = false := by
  decide +kernel

theorem node_context_11_6616_343673 : EJMOriginalGlobalDAGData.nodes 10 ⟨343673, by decide⟩ =
    .split (coordinate 11) (![⟨343431, by decide⟩,⟨343550, by decide⟩,⟨343617, by decide⟩,⟨343672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6616_343673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6616 ⟨343673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6616
    ⟨343673, by decide⟩ (by decide) (![⟨343431, by decide⟩,⟨343550, by decide⟩,⟨343617, by decide⟩,⟨343672, by decide⟩]) unmarked_context_11_6616_343673 node_context_11_6616_343673
  intro a
  fin_cases a
  · exact context_12_26464_343431
  · exact context_12_26465_343550
  · exact context_12_26466_343617
  · exact context_12_26467_343672

theorem selected_cut_13061 : selected 9 ⟨343712, by decide⟩
    (prefixPartial 12 26468) = some ⟨12, 2, 0, 343712, 26468, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_26468_343712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26468 ⟨343712, by decide⟩ :=
  accepted_of_selected 12 26468 ⟨343712, by decide⟩ ⟨12, 2, 0, 343712, 26468, 3453, 65536⟩
    (by decide) selected_cut_13061

theorem selected_cut_13062 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105876) = some ⟨13, 1, 0, 3444, 105876, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105876_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105876 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105876 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105876, 1, 16384⟩
    (by decide) selected_cut_13062

theorem selected_cut_13063 : selected 8 ⟨343748, by decide⟩
    (prefixPartial 13 105877) = some ⟨13, 2, 0, 343748, 105877, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_105877_343748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105877 ⟨343748, by decide⟩ :=
  accepted_of_selected 13 105877 ⟨343748, by decide⟩ ⟨13, 2, 0, 343748, 105877, 1761, 16384⟩
    (by decide) selected_cut_13063

theorem selected_cut_13064 : selected 8 ⟨343792, by decide⟩
    (prefixPartial 13 105878) = some ⟨13, 2, 0, 343792, 105878, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_105878_343792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105878 ⟨343792, by decide⟩ :=
  accepted_of_selected 13 105878 ⟨343792, by decide⟩ ⟨13, 2, 0, 343792, 105878, 2557, 16384⟩
    (by decide) selected_cut_13064

theorem selected_cut_13065 : selected 8 ⟨343806, by decide⟩
    (prefixPartial 13 105879) = some ⟨13, 2, 0, 343806, 105879, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_105879_343806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105879 ⟨343806, by decide⟩ :=
  accepted_of_selected 13 105879 ⟨343806, by decide⟩ ⟨13, 2, 0, 343806, 105879, 1017, 16384⟩
    (by decide) selected_cut_13065

theorem unmarked_context_12_26469_343807 : frontier 9 ⟨343807, by decide⟩
    (prefixCache 12 26469) (prefixPartial 12 26469) = false := by
  decide +kernel

theorem node_context_12_26469_343807 : EJMOriginalGlobalDAGData.nodes 9 ⟨343807, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨343748, by decide⟩,⟨343792, by decide⟩,⟨343806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26469_343807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26469 ⟨343807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26469
    ⟨343807, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨343748, by decide⟩,⟨343792, by decide⟩,⟨343806, by decide⟩]) unmarked_context_12_26469_343807 node_context_12_26469_343807
  intro a
  fin_cases a
  · exact context_13_105876_3444
  · exact context_13_105877_343748
  · exact context_13_105878_343792
  · exact context_13_105879_343806

theorem selected_cut_13066 : selected 9 ⟨343874, by decide⟩
    (prefixPartial 12 26470) = some ⟨12, 2, 0, 343874, 26470, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_26470_343874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26470 ⟨343874, by decide⟩ :=
  accepted_of_selected 12 26470 ⟨343874, by decide⟩ ⟨12, 2, 0, 343874, 26470, 3741, 65536⟩
    (by decide) selected_cut_13066

theorem selected_cut_13067 : selected 9 ⟨343919, by decide⟩
    (prefixPartial 12 26471) = some ⟨12, 2, 0, 343919, 26471, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_26471_343919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26471 ⟨343919, by decide⟩ :=
  accepted_of_selected 12 26471 ⟨343919, by decide⟩ ⟨12, 2, 0, 343919, 26471, 3581, 65536⟩
    (by decide) selected_cut_13067

theorem unmarked_context_11_6617_343920 : frontier 10 ⟨343920, by decide⟩
    (prefixCache 11 6617) (prefixPartial 11 6617) = false := by
  decide +kernel

theorem node_context_11_6617_343920 : EJMOriginalGlobalDAGData.nodes 10 ⟨343920, by decide⟩ =
    .split (coordinate 11) (![⟨343712, by decide⟩,⟨343807, by decide⟩,⟨343874, by decide⟩,⟨343919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6617_343920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6617 ⟨343920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6617
    ⟨343920, by decide⟩ (by decide) (![⟨343712, by decide⟩,⟨343807, by decide⟩,⟨343874, by decide⟩,⟨343919, by decide⟩]) unmarked_context_11_6617_343920 node_context_11_6617_343920
  intro a
  fin_cases a
  · exact context_12_26468_343712
  · exact context_12_26469_343807
  · exact context_12_26470_343874
  · exact context_12_26471_343919

theorem selected_cut_13068 : selected 9 ⟨343970, by decide⟩
    (prefixPartial 12 26472) = some ⟨12, 2, 0, 343970, 26472, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_26472_343970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26472 ⟨343970, by decide⟩ :=
  accepted_of_selected 12 26472 ⟨343970, by decide⟩ ⟨12, 2, 0, 343970, 26472, 3705, 65536⟩
    (by decide) selected_cut_13068

theorem selected_cut_13069 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105892) = some ⟨13, 1, 0, 3444, 105892, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105892_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105892 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105892 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105892, 1, 16384⟩
    (by decide) selected_cut_13069

theorem selected_cut_13070 : selected 8 ⟨343997, by decide⟩
    (prefixPartial 13 105893) = some ⟨13, 2, 0, 343997, 105893, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_105893_343997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105893 ⟨343997, by decide⟩ :=
  accepted_of_selected 13 105893 ⟨343997, by decide⟩ ⟨13, 2, 0, 343997, 105893, 1549, 16384⟩
    (by decide) selected_cut_13070

theorem selected_cut_13071 : selected 8 ⟨344066, by decide⟩
    (prefixPartial 13 105894) = some ⟨13, 2, 0, 344066, 105894, 2961, 16384⟩ := by
  decide +kernel

theorem context_13_105894_344066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105894 ⟨344066, by decide⟩ :=
  accepted_of_selected 13 105894 ⟨344066, by decide⟩ ⟨13, 2, 0, 344066, 105894, 2961, 16384⟩
    (by decide) selected_cut_13071

theorem selected_cut_13072 : selected 8 ⟨344097, by decide⟩
    (prefixPartial 13 105895) = some ⟨13, 2, 0, 344097, 105895, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_105895_344097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105895 ⟨344097, by decide⟩ :=
  accepted_of_selected 13 105895 ⟨344097, by decide⟩ ⟨13, 2, 0, 344097, 105895, 1345, 16384⟩
    (by decide) selected_cut_13072

theorem unmarked_context_12_26473_344098 : frontier 9 ⟨344098, by decide⟩
    (prefixCache 12 26473) (prefixPartial 12 26473) = false := by
  decide +kernel

theorem node_context_12_26473_344098 : EJMOriginalGlobalDAGData.nodes 9 ⟨344098, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨343997, by decide⟩,⟨344066, by decide⟩,⟨344097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26473_344098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26473 ⟨344098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26473
    ⟨344098, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨343997, by decide⟩,⟨344066, by decide⟩,⟨344097, by decide⟩]) unmarked_context_12_26473_344098 node_context_12_26473_344098
  intro a
  fin_cases a
  · exact context_13_105892_3444
  · exact context_13_105893_343997
  · exact context_13_105894_344066
  · exact context_13_105895_344097

theorem selected_cut_13073 : selected 9 ⟨344151, by decide⟩
    (prefixPartial 12 26474) = some ⟨12, 2, 0, 344151, 26474, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_26474_344151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26474 ⟨344151, by decide⟩ :=
  accepted_of_selected 12 26474 ⟨344151, by decide⟩ ⟨12, 2, 0, 344151, 26474, 3777, 65536⟩
    (by decide) selected_cut_13073

theorem selected_cut_13074 : selected 9 ⟨344192, by decide⟩
    (prefixPartial 12 26475) = some ⟨12, 2, 0, 344192, 26475, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_26475_344192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26475 ⟨344192, by decide⟩ :=
  accepted_of_selected 12 26475 ⟨344192, by decide⟩ ⟨12, 2, 0, 344192, 26475, 3473, 65536⟩
    (by decide) selected_cut_13074

theorem unmarked_context_11_6618_344193 : frontier 10 ⟨344193, by decide⟩
    (prefixCache 11 6618) (prefixPartial 11 6618) = false := by
  decide +kernel

theorem node_context_11_6618_344193 : EJMOriginalGlobalDAGData.nodes 10 ⟨344193, by decide⟩ =
    .split (coordinate 11) (![⟨343970, by decide⟩,⟨344098, by decide⟩,⟨344151, by decide⟩,⟨344192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6618_344193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6618 ⟨344193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6618
    ⟨344193, by decide⟩ (by decide) (![⟨343970, by decide⟩,⟨344098, by decide⟩,⟨344151, by decide⟩,⟨344192, by decide⟩]) unmarked_context_11_6618_344193 node_context_11_6618_344193
  intro a
  fin_cases a
  · exact context_12_26472_343970
  · exact context_12_26473_344098
  · exact context_12_26474_344151
  · exact context_12_26475_344192

theorem selected_cut_13075 : selected 9 ⟨344233, by decide⟩
    (prefixPartial 12 26476) = some ⟨12, 2, 0, 344233, 26476, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_26476_344233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26476 ⟨344233, by decide⟩ :=
  accepted_of_selected 12 26476 ⟨344233, by decide⟩ ⟨12, 2, 0, 344233, 26476, 2821, 65536⟩
    (by decide) selected_cut_13075

theorem selected_cut_13076 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105908) = some ⟨13, 1, 0, 3444, 105908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105908, 1, 16384⟩
    (by decide) selected_cut_13076

theorem selected_cut_13077 : selected 8 ⟨344259, by decide⟩
    (prefixPartial 13 105909) = some ⟨13, 2, 0, 344259, 105909, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_105909_344259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105909 ⟨344259, by decide⟩ :=
  accepted_of_selected 13 105909 ⟨344259, by decide⟩ ⟨13, 2, 0, 344259, 105909, 1233, 16384⟩
    (by decide) selected_cut_13077

theorem selected_cut_13078 : selected 8 ⟨344311, by decide⟩
    (prefixPartial 13 105910) = some ⟨13, 2, 0, 344311, 105910, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_105910_344311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105910 ⟨344311, by decide⟩ :=
  accepted_of_selected 13 105910 ⟨344311, by decide⟩ ⟨13, 2, 0, 344311, 105910, 2673, 16384⟩
    (by decide) selected_cut_13078

theorem selected_cut_13079 : selected 8 ⟨344335, by decide⟩
    (prefixPartial 13 105911) = some ⟨13, 2, 0, 344335, 105911, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_105911_344335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105911 ⟨344335, by decide⟩ :=
  accepted_of_selected 13 105911 ⟨344335, by decide⟩ ⟨13, 2, 0, 344335, 105911, 1089, 16384⟩
    (by decide) selected_cut_13079

theorem unmarked_context_12_26477_344336 : frontier 9 ⟨344336, by decide⟩
    (prefixCache 12 26477) (prefixPartial 12 26477) = false := by
  decide +kernel

theorem node_context_12_26477_344336 : EJMOriginalGlobalDAGData.nodes 9 ⟨344336, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨344259, by decide⟩,⟨344311, by decide⟩,⟨344335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26477_344336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26477 ⟨344336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26477
    ⟨344336, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨344259, by decide⟩,⟨344311, by decide⟩,⟨344335, by decide⟩]) unmarked_context_12_26477_344336 node_context_12_26477_344336
  intro a
  fin_cases a
  · exact context_13_105908_3444
  · exact context_13_105909_344259
  · exact context_13_105910_344311
  · exact context_13_105911_344335

theorem selected_cut_13080 : selected 9 ⟨344377, by decide⟩
    (prefixPartial 12 26478) = some ⟨12, 2, 0, 344377, 26478, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_26478_344377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26478 ⟨344377, by decide⟩ :=
  accepted_of_selected 12 26478 ⟨344377, by decide⟩ ⟨12, 2, 0, 344377, 26478, 2957, 65536⟩
    (by decide) selected_cut_13080

theorem selected_cut_13081 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105916) = some ⟨13, 1, 0, 3444, 105916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105916, 1, 16384⟩
    (by decide) selected_cut_13081

theorem selected_cut_13082 : selected 8 ⟨344402, by decide⟩
    (prefixPartial 13 105917) = some ⟨13, 2, 0, 344402, 105917, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_105917_344402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105917 ⟨344402, by decide⟩ :=
  accepted_of_selected 13 105917 ⟨344402, by decide⟩ ⟨13, 2, 0, 344402, 105917, 1157, 16384⟩
    (by decide) selected_cut_13082

theorem selected_cut_13083 : selected 8 ⟨344447, by decide⟩
    (prefixPartial 13 105918) = some ⟨13, 2, 0, 344447, 105918, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_105918_344447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105918 ⟨344447, by decide⟩ :=
  accepted_of_selected 13 105918 ⟨344447, by decide⟩ ⟨13, 2, 0, 344447, 105918, 2625, 16384⟩
    (by decide) selected_cut_13083

theorem selected_cut_13084 : selected 8 ⟨344479, by decide⟩
    (prefixPartial 13 105919) = some ⟨13, 2, 0, 344479, 105919, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_105919_344479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105919 ⟨344479, by decide⟩ :=
  accepted_of_selected 13 105919 ⟨344479, by decide⟩ ⟨13, 2, 0, 344479, 105919, 1201, 16384⟩
    (by decide) selected_cut_13084

theorem unmarked_context_12_26479_344480 : frontier 9 ⟨344480, by decide⟩
    (prefixCache 12 26479) (prefixPartial 12 26479) = false := by
  decide +kernel

theorem node_context_12_26479_344480 : EJMOriginalGlobalDAGData.nodes 9 ⟨344480, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨344402, by decide⟩,⟨344447, by decide⟩,⟨344479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26479_344480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26479 ⟨344480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26479
    ⟨344480, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨344402, by decide⟩,⟨344447, by decide⟩,⟨344479, by decide⟩]) unmarked_context_12_26479_344480 node_context_12_26479_344480
  intro a
  fin_cases a
  · exact context_13_105916_3444
  · exact context_13_105917_344402
  · exact context_13_105918_344447
  · exact context_13_105919_344479

theorem unmarked_context_11_6619_344481 : frontier 10 ⟨344481, by decide⟩
    (prefixCache 11 6619) (prefixPartial 11 6619) = false := by
  decide +kernel

theorem node_context_11_6619_344481 : EJMOriginalGlobalDAGData.nodes 10 ⟨344481, by decide⟩ =
    .split (coordinate 11) (![⟨344233, by decide⟩,⟨344336, by decide⟩,⟨344377, by decide⟩,⟨344480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6619_344481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6619 ⟨344481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6619
    ⟨344481, by decide⟩ (by decide) (![⟨344233, by decide⟩,⟨344336, by decide⟩,⟨344377, by decide⟩,⟨344480, by decide⟩]) unmarked_context_11_6619_344481 node_context_11_6619_344481
  intro a
  fin_cases a
  · exact context_12_26476_344233
  · exact context_12_26477_344336
  · exact context_12_26478_344377
  · exact context_12_26479_344480

theorem unmarked_context_10_1654_344482 : frontier 11 ⟨344482, by decide⟩
    (prefixCache 10 1654) (prefixPartial 10 1654) = false := by
  decide +kernel

theorem node_context_10_1654_344482 : EJMOriginalGlobalDAGData.nodes 11 ⟨344482, by decide⟩ =
    .split (coordinate 10) (![⟨343673, by decide⟩,⟨343920, by decide⟩,⟨344193, by decide⟩,⟨344481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1654_344482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1654 ⟨344482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1654
    ⟨344482, by decide⟩ (by decide) (![⟨343673, by decide⟩,⟨343920, by decide⟩,⟨344193, by decide⟩,⟨344481, by decide⟩]) unmarked_context_10_1654_344482 node_context_10_1654_344482
  intro a
  fin_cases a
  · exact context_11_6616_343673
  · exact context_11_6617_343920
  · exact context_11_6618_344193
  · exact context_11_6619_344481

theorem selected_cut_13085 : selected 9 ⟨344524, by decide⟩
    (prefixPartial 12 26480) = some ⟨12, 2, 0, 344524, 26480, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_26480_344524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26480 ⟨344524, by decide⟩ :=
  accepted_of_selected 12 26480 ⟨344524, by decide⟩ ⟨12, 2, 0, 344524, 26480, 3165, 65536⟩
    (by decide) selected_cut_13085

theorem selected_cut_13086 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105924) = some ⟨13, 1, 0, 3444, 105924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105924, 1, 16384⟩
    (by decide) selected_cut_13086

theorem selected_cut_13087 : selected 8 ⟨344547, by decide⟩
    (prefixPartial 13 105925) = some ⟨13, 2, 0, 344547, 105925, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_105925_344547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105925 ⟨344547, by decide⟩ :=
  accepted_of_selected 13 105925 ⟨344547, by decide⟩ ⟨13, 2, 0, 344547, 105925, 1009, 16384⟩
    (by decide) selected_cut_13087

theorem selected_cut_13088 : selected 8 ⟨344616, by decide⟩
    (prefixPartial 13 105926) = some ⟨13, 2, 0, 344616, 105926, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_105926_344616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105926 ⟨344616, by decide⟩ :=
  accepted_of_selected 13 105926 ⟨344616, by decide⟩ ⟨13, 2, 0, 344616, 105926, 3033, 16384⟩
    (by decide) selected_cut_13088

theorem selected_cut_13089 : selected 8 ⟨344633, by decide⟩
    (prefixPartial 13 105927) = some ⟨13, 2, 0, 344633, 105927, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_105927_344633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105927 ⟨344633, by decide⟩ :=
  accepted_of_selected 13 105927 ⟨344633, by decide⟩ ⟨13, 2, 0, 344633, 105927, 1041, 16384⟩
    (by decide) selected_cut_13089

theorem unmarked_context_12_26481_344634 : frontier 9 ⟨344634, by decide⟩
    (prefixCache 12 26481) (prefixPartial 12 26481) = false := by
  decide +kernel

theorem node_context_12_26481_344634 : EJMOriginalGlobalDAGData.nodes 9 ⟨344634, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨344547, by decide⟩,⟨344616, by decide⟩,⟨344633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26481_344634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26481 ⟨344634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26481
    ⟨344634, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨344547, by decide⟩,⟨344616, by decide⟩,⟨344633, by decide⟩]) unmarked_context_12_26481_344634 node_context_12_26481_344634
  intro a
  fin_cases a
  · exact context_13_105924_3444
  · exact context_13_105925_344547
  · exact context_13_105926_344616
  · exact context_13_105927_344633

theorem selected_cut_13090 : selected 9 ⟨344697, by decide⟩
    (prefixPartial 12 26482) = some ⟨12, 2, 0, 344697, 26482, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_26482_344697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26482 ⟨344697, by decide⟩ :=
  accepted_of_selected 12 26482 ⟨344697, by decide⟩ ⟨12, 2, 0, 344697, 26482, 3573, 65536⟩
    (by decide) selected_cut_13090

theorem selected_cut_13091 : selected 9 ⟨344739, by decide⟩
    (prefixPartial 12 26483) = some ⟨12, 2, 0, 344739, 26483, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_26483_344739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26483 ⟨344739, by decide⟩ :=
  accepted_of_selected 12 26483 ⟨344739, by decide⟩ ⟨12, 2, 0, 344739, 26483, 3329, 65536⟩
    (by decide) selected_cut_13091

theorem unmarked_context_11_6620_344740 : frontier 10 ⟨344740, by decide⟩
    (prefixCache 11 6620) (prefixPartial 11 6620) = false := by
  decide +kernel

theorem node_context_11_6620_344740 : EJMOriginalGlobalDAGData.nodes 10 ⟨344740, by decide⟩ =
    .split (coordinate 11) (![⟨344524, by decide⟩,⟨344634, by decide⟩,⟨344697, by decide⟩,⟨344739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6620_344740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6620 ⟨344740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6620
    ⟨344740, by decide⟩ (by decide) (![⟨344524, by decide⟩,⟨344634, by decide⟩,⟨344697, by decide⟩,⟨344739, by decide⟩]) unmarked_context_11_6620_344740 node_context_11_6620_344740
  intro a
  fin_cases a
  · exact context_12_26480_344524
  · exact context_12_26481_344634
  · exact context_12_26482_344697
  · exact context_12_26483_344739

theorem selected_cut_13092 : selected 9 ⟨344782, by decide⟩
    (prefixPartial 12 26484) = some ⟨12, 2, 0, 344782, 26484, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_26484_344782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26484 ⟨344782, by decide⟩ :=
  accepted_of_selected 12 26484 ⟨344782, by decide⟩ ⟨12, 2, 0, 344782, 26484, 2821, 65536⟩
    (by decide) selected_cut_13092

theorem selected_cut_13093 : selected 9 ⟨299350, by decide⟩
    (prefixPartial 12 26485) = some ⟨12, 1, 0, 299350, 26485, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26485_299350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26485 ⟨299350, by decide⟩ :=
  accepted_of_selected 12 26485 ⟨299350, by decide⟩ ⟨12, 1, 0, 299350, 26485, 1, 65536⟩
    (by decide) selected_cut_13093

theorem selected_cut_13094 : selected 9 ⟨344833, by decide⟩
    (prefixPartial 12 26486) = some ⟨12, 2, 0, 344833, 26486, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_26486_344833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26486 ⟨344833, by decide⟩ :=
  accepted_of_selected 12 26486 ⟨344833, by decide⟩ ⟨12, 2, 0, 344833, 26486, 3305, 65536⟩
    (by decide) selected_cut_13094

theorem selected_cut_13095 : selected 9 ⟨344869, by decide⟩
    (prefixPartial 12 26487) = some ⟨12, 2, 0, 344869, 26487, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_26487_344869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26487 ⟨344869, by decide⟩ :=
  accepted_of_selected 12 26487 ⟨344869, by decide⟩ ⟨12, 2, 0, 344869, 26487, 2865, 65536⟩
    (by decide) selected_cut_13095

theorem unmarked_context_11_6621_344870 : frontier 10 ⟨344870, by decide⟩
    (prefixCache 11 6621) (prefixPartial 11 6621) = false := by
  decide +kernel

theorem node_context_11_6621_344870 : EJMOriginalGlobalDAGData.nodes 10 ⟨344870, by decide⟩ =
    .split (coordinate 11) (![⟨344782, by decide⟩,⟨299350, by decide⟩,⟨344833, by decide⟩,⟨344869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6621_344870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6621 ⟨344870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6621
    ⟨344870, by decide⟩ (by decide) (![⟨344782, by decide⟩,⟨299350, by decide⟩,⟨344833, by decide⟩,⟨344869, by decide⟩]) unmarked_context_11_6621_344870 node_context_11_6621_344870
  intro a
  fin_cases a
  · exact context_12_26484_344782
  · exact context_12_26485_299350
  · exact context_12_26486_344833
  · exact context_12_26487_344869

theorem selected_cut_13096 : selected 9 ⟨344909, by decide⟩
    (prefixPartial 12 26488) = some ⟨12, 2, 0, 344909, 26488, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_26488_344909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26488 ⟨344909, by decide⟩ :=
  accepted_of_selected 12 26488 ⟨344909, by decide⟩ ⟨12, 2, 0, 344909, 26488, 3233, 65536⟩
    (by decide) selected_cut_13096

theorem selected_cut_13097 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 105956) = some ⟨13, 1, 0, 3444, 105956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_105956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 105956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 105956, 1, 16384⟩
    (by decide) selected_cut_13097

theorem selected_cut_13098 : selected 8 ⟨344921, by decide⟩
    (prefixPartial 13 105957) = some ⟨13, 2, 0, 344921, 105957, 461, 16384⟩ := by
  decide +kernel

theorem context_13_105957_344921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105957 ⟨344921, by decide⟩ :=
  accepted_of_selected 13 105957 ⟨344921, by decide⟩ ⟨13, 2, 0, 344921, 105957, 461, 16384⟩
    (by decide) selected_cut_13098

theorem selected_cut_13099 : selected 8 ⟨345006, by decide⟩
    (prefixPartial 13 105958) = some ⟨13, 2, 0, 345006, 105958, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_105958_345006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105958 ⟨345006, by decide⟩ :=
  accepted_of_selected 13 105958 ⟨345006, by decide⟩ ⟨13, 2, 0, 345006, 105958, 3137, 16384⟩
    (by decide) selected_cut_13099

theorem selected_cut_13100 : selected 8 ⟨345059, by decide⟩
    (prefixPartial 13 105959) = some ⟨13, 2, 0, 345059, 105959, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_105959_345059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 105959 ⟨345059, by decide⟩ :=
  accepted_of_selected 13 105959 ⟨345059, by decide⟩ ⟨13, 2, 0, 345059, 105959, 1325, 16384⟩
    (by decide) selected_cut_13100

theorem unmarked_context_12_26489_345060 : frontier 9 ⟨345060, by decide⟩
    (prefixCache 12 26489) (prefixPartial 12 26489) = false := by
  decide +kernel

theorem node_context_12_26489_345060 : EJMOriginalGlobalDAGData.nodes 9 ⟨345060, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨344921, by decide⟩,⟨345006, by decide⟩,⟨345059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26489_345060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26489 ⟨345060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26489
    ⟨345060, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨344921, by decide⟩,⟨345006, by decide⟩,⟨345059, by decide⟩]) unmarked_context_12_26489_345060 node_context_12_26489_345060
  intro a
  fin_cases a
  · exact context_13_105956_3444
  · exact context_13_105957_344921
  · exact context_13_105958_345006
  · exact context_13_105959_345059

theorem selected_cut_13101 : selected 9 ⟨345103, by decide⟩
    (prefixPartial 12 26490) = some ⟨12, 2, 0, 345103, 26490, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_26490_345103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26490 ⟨345103, by decide⟩ :=
  accepted_of_selected 12 26490 ⟨345103, by decide⟩ ⟨12, 2, 0, 345103, 26490, 3373, 65536⟩
    (by decide) selected_cut_13101

theorem selected_cut_13102 : selected 9 ⟨345142, by decide⟩
    (prefixPartial 12 26491) = some ⟨12, 2, 0, 345142, 26491, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_26491_345142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26491 ⟨345142, by decide⟩ :=
  accepted_of_selected 12 26491 ⟨345142, by decide⟩ ⟨12, 2, 0, 345142, 26491, 2877, 65536⟩
    (by decide) selected_cut_13102

theorem unmarked_context_11_6622_345143 : frontier 10 ⟨345143, by decide⟩
    (prefixCache 11 6622) (prefixPartial 11 6622) = false := by
  decide +kernel

theorem node_context_11_6622_345143 : EJMOriginalGlobalDAGData.nodes 10 ⟨345143, by decide⟩ =
    .split (coordinate 11) (![⟨344909, by decide⟩,⟨345060, by decide⟩,⟨345103, by decide⟩,⟨345142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6622_345143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6622 ⟨345143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6622
    ⟨345143, by decide⟩ (by decide) (![⟨344909, by decide⟩,⟨345060, by decide⟩,⟨345103, by decide⟩,⟨345142, by decide⟩]) unmarked_context_11_6622_345143 node_context_11_6622_345143
  intro a
  fin_cases a
  · exact context_12_26488_344909
  · exact context_12_26489_345060
  · exact context_12_26490_345103
  · exact context_12_26491_345142

theorem selected_cut_13103 : selected 9 ⟨345173, by decide⟩
    (prefixPartial 12 26492) = some ⟨12, 2, 0, 345173, 26492, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_26492_345173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26492 ⟨345173, by decide⟩ :=
  accepted_of_selected 12 26492 ⟨345173, by decide⟩ ⟨12, 2, 0, 345173, 26492, 2477, 65536⟩
    (by decide) selected_cut_13103

theorem selected_cut_13104 : selected 9 ⟨345249, by decide⟩
    (prefixPartial 12 26493) = some ⟨12, 2, 0, 345249, 26493, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_26493_345249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26493 ⟨345249, by decide⟩ :=
  accepted_of_selected 12 26493 ⟨345249, by decide⟩ ⟨12, 2, 0, 345249, 26493, 3933, 65536⟩
    (by decide) selected_cut_13104

theorem selected_cut_13105 : selected 9 ⟨345283, by decide⟩
    (prefixPartial 12 26494) = some ⟨12, 2, 0, 345283, 26494, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_26494_345283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26494 ⟨345283, by decide⟩ :=
  accepted_of_selected 12 26494 ⟨345283, by decide⟩ ⟨12, 2, 0, 345283, 26494, 2649, 65536⟩
    (by decide) selected_cut_13105

theorem selected_cut_13106 : selected 9 ⟨345284, by decide⟩
    (prefixPartial 12 26495) = some ⟨12, 1, 0, 345284, 26495, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26495_345284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26495 ⟨345284, by decide⟩ :=
  accepted_of_selected 12 26495 ⟨345284, by decide⟩ ⟨12, 1, 0, 345284, 26495, 1, 65536⟩
    (by decide) selected_cut_13106

theorem unmarked_context_11_6623_345285 : frontier 10 ⟨345285, by decide⟩
    (prefixCache 11 6623) (prefixPartial 11 6623) = false := by
  decide +kernel

theorem node_context_11_6623_345285 : EJMOriginalGlobalDAGData.nodes 10 ⟨345285, by decide⟩ =
    .split (coordinate 11) (![⟨345173, by decide⟩,⟨345249, by decide⟩,⟨345283, by decide⟩,⟨345284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6623_345285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6623 ⟨345285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6623
    ⟨345285, by decide⟩ (by decide) (![⟨345173, by decide⟩,⟨345249, by decide⟩,⟨345283, by decide⟩,⟨345284, by decide⟩]) unmarked_context_11_6623_345285 node_context_11_6623_345285
  intro a
  fin_cases a
  · exact context_12_26492_345173
  · exact context_12_26493_345249
  · exact context_12_26494_345283
  · exact context_12_26495_345284

theorem unmarked_context_10_1655_345286 : frontier 11 ⟨345286, by decide⟩
    (prefixCache 10 1655) (prefixPartial 10 1655) = false := by
  decide +kernel

theorem node_context_10_1655_345286 : EJMOriginalGlobalDAGData.nodes 11 ⟨345286, by decide⟩ =
    .split (coordinate 10) (![⟨344740, by decide⟩,⟨344870, by decide⟩,⟨345143, by decide⟩,⟨345285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1655_345286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1655 ⟨345286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1655
    ⟨345286, by decide⟩ (by decide) (![⟨344740, by decide⟩,⟨344870, by decide⟩,⟨345143, by decide⟩,⟨345285, by decide⟩]) unmarked_context_10_1655_345286 node_context_10_1655_345286
  intro a
  fin_cases a
  · exact context_11_6620_344740
  · exact context_11_6621_344870
  · exact context_11_6622_345143
  · exact context_11_6623_345285

theorem unmarked_context_9_413_345287 : frontier 12 ⟨345287, by decide⟩
    (prefixCache 9 413) (prefixPartial 9 413) = false := by
  decide +kernel

theorem node_context_9_413_345287 : EJMOriginalGlobalDAGData.nodes 12 ⟨345287, by decide⟩ =
    .split (coordinate 9) (![⟨342365, by decide⟩,⟨343388, by decide⟩,⟨344482, by decide⟩,⟨345286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_413_345287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 413 ⟨345287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 413
    ⟨345287, by decide⟩ (by decide) (![⟨342365, by decide⟩,⟨343388, by decide⟩,⟨344482, by decide⟩,⟨345286, by decide⟩]) unmarked_context_9_413_345287 node_context_9_413_345287
  intro a
  fin_cases a
  · exact context_10_1652_342365
  · exact context_10_1653_343388
  · exact context_10_1654_344482
  · exact context_10_1655_345286

theorem selected_cut_13107 : selected 9 ⟨345315, by decide⟩
    (prefixPartial 12 26496) = some ⟨12, 2, 0, 345315, 26496, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_26496_345315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26496 ⟨345315, by decide⟩ :=
  accepted_of_selected 12 26496 ⟨345315, by decide⟩ ⟨12, 2, 0, 345315, 26496, 2969, 65536⟩
    (by decide) selected_cut_13107

theorem selected_cut_13108 : selected 9 ⟨345353, by decide⟩
    (prefixPartial 12 26497) = some ⟨12, 2, 0, 345353, 26497, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_26497_345353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26497 ⟨345353, by decide⟩ :=
  accepted_of_selected 12 26497 ⟨345353, by decide⟩ ⟨12, 2, 0, 345353, 26497, 2881, 65536⟩
    (by decide) selected_cut_13108

theorem selected_cut_13109 : selected 9 ⟨345385, by decide⟩
    (prefixPartial 12 26498) = some ⟨12, 2, 0, 345385, 26498, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_26498_345385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26498 ⟨345385, by decide⟩ :=
  accepted_of_selected 12 26498 ⟨345385, by decide⟩ ⟨12, 2, 0, 345385, 26498, 2733, 65536⟩
    (by decide) selected_cut_13109

theorem selected_cut_13110 : selected 9 ⟨345421, by decide⟩
    (prefixPartial 12 26499) = some ⟨12, 2, 0, 345421, 26499, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_26499_345421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26499 ⟨345421, by decide⟩ :=
  accepted_of_selected 12 26499 ⟨345421, by decide⟩ ⟨12, 2, 0, 345421, 26499, 2769, 65536⟩
    (by decide) selected_cut_13110

theorem unmarked_context_11_6624_345422 : frontier 10 ⟨345422, by decide⟩
    (prefixCache 11 6624) (prefixPartial 11 6624) = false := by
  decide +kernel

theorem node_context_11_6624_345422 : EJMOriginalGlobalDAGData.nodes 10 ⟨345422, by decide⟩ =
    .split (coordinate 11) (![⟨345315, by decide⟩,⟨345353, by decide⟩,⟨345385, by decide⟩,⟨345421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6624_345422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6624 ⟨345422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6624
    ⟨345422, by decide⟩ (by decide) (![⟨345315, by decide⟩,⟨345353, by decide⟩,⟨345385, by decide⟩,⟨345421, by decide⟩]) unmarked_context_11_6624_345422 node_context_11_6624_345422
  intro a
  fin_cases a
  · exact context_12_26496_345315
  · exact context_12_26497_345353
  · exact context_12_26498_345385
  · exact context_12_26499_345421

theorem selected_cut_13111 : selected 9 ⟨345455, by decide⟩
    (prefixPartial 12 26500) = some ⟨12, 2, 0, 345455, 26500, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_26500_345455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26500 ⟨345455, by decide⟩ :=
  accepted_of_selected 12 26500 ⟨345455, by decide⟩ ⟨12, 2, 0, 345455, 26500, 2901, 65536⟩
    (by decide) selected_cut_13111

theorem selected_cut_13112 : selected 9 ⟨345484, by decide⟩
    (prefixPartial 12 26501) = some ⟨12, 2, 0, 345484, 26501, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_26501_345484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26501 ⟨345484, by decide⟩ :=
  accepted_of_selected 12 26501 ⟨345484, by decide⟩ ⟨12, 2, 0, 345484, 26501, 2665, 65536⟩
    (by decide) selected_cut_13112

theorem selected_cut_13113 : selected 9 ⟨345518, by decide⟩
    (prefixPartial 12 26502) = some ⟨12, 2, 0, 345518, 26502, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_26502_345518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26502 ⟨345518, by decide⟩ :=
  accepted_of_selected 12 26502 ⟨345518, by decide⟩ ⟨12, 2, 0, 345518, 26502, 2781, 65536⟩
    (by decide) selected_cut_13113

theorem selected_cut_13114 : selected 9 ⟨345550, by decide⟩
    (prefixPartial 12 26503) = some ⟨12, 2, 0, 345550, 26503, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_26503_345550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26503 ⟨345550, by decide⟩ :=
  accepted_of_selected 12 26503 ⟨345550, by decide⟩ ⟨12, 2, 0, 345550, 26503, 2701, 65536⟩
    (by decide) selected_cut_13114

theorem unmarked_context_11_6625_345551 : frontier 10 ⟨345551, by decide⟩
    (prefixCache 11 6625) (prefixPartial 11 6625) = false := by
  decide +kernel

theorem node_context_11_6625_345551 : EJMOriginalGlobalDAGData.nodes 10 ⟨345551, by decide⟩ =
    .split (coordinate 11) (![⟨345455, by decide⟩,⟨345484, by decide⟩,⟨345518, by decide⟩,⟨345550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6625_345551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6625 ⟨345551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6625
    ⟨345551, by decide⟩ (by decide) (![⟨345455, by decide⟩,⟨345484, by decide⟩,⟨345518, by decide⟩,⟨345550, by decide⟩]) unmarked_context_11_6625_345551 node_context_11_6625_345551
  intro a
  fin_cases a
  · exact context_12_26500_345455
  · exact context_12_26501_345484
  · exact context_12_26502_345518
  · exact context_12_26503_345550

theorem selected_cut_13115 : selected 9 ⟨345609, by decide⟩
    (prefixPartial 12 26504) = some ⟨12, 2, 0, 345609, 26504, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_26504_345609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26504 ⟨345609, by decide⟩ :=
  accepted_of_selected 12 26504 ⟨345609, by decide⟩ ⟨12, 2, 0, 345609, 26504, 3009, 65536⟩
    (by decide) selected_cut_13115

theorem selected_cut_13116 : selected 9 ⟨345656, by decide⟩
    (prefixPartial 12 26505) = some ⟨12, 2, 0, 345656, 26505, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_26505_345656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26505 ⟨345656, by decide⟩ :=
  accepted_of_selected 12 26505 ⟨345656, by decide⟩ ⟨12, 2, 0, 345656, 26505, 2793, 65536⟩
    (by decide) selected_cut_13116

theorem selected_cut_13117 : selected 9 ⟨345687, by decide⟩
    (prefixPartial 12 26506) = some ⟨12, 2, 0, 345687, 26506, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_26506_345687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26506 ⟨345687, by decide⟩ :=
  accepted_of_selected 12 26506 ⟨345687, by decide⟩ ⟨12, 2, 0, 345687, 26506, 2561, 65536⟩
    (by decide) selected_cut_13117

theorem selected_cut_13118 : selected 9 ⟨345727, by decide⟩
    (prefixPartial 12 26507) = some ⟨12, 2, 0, 345727, 26507, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_26507_345727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26507 ⟨345727, by decide⟩ :=
  accepted_of_selected 12 26507 ⟨345727, by decide⟩ ⟨12, 2, 0, 345727, 26507, 2437, 65536⟩
    (by decide) selected_cut_13118

theorem unmarked_context_11_6626_345728 : frontier 10 ⟨345728, by decide⟩
    (prefixCache 11 6626) (prefixPartial 11 6626) = false := by
  decide +kernel

theorem node_context_11_6626_345728 : EJMOriginalGlobalDAGData.nodes 10 ⟨345728, by decide⟩ =
    .split (coordinate 11) (![⟨345609, by decide⟩,⟨345656, by decide⟩,⟨345687, by decide⟩,⟨345727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6626_345728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6626 ⟨345728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6626
    ⟨345728, by decide⟩ (by decide) (![⟨345609, by decide⟩,⟨345656, by decide⟩,⟨345687, by decide⟩,⟨345727, by decide⟩]) unmarked_context_11_6626_345728 node_context_11_6626_345728
  intro a
  fin_cases a
  · exact context_12_26504_345609
  · exact context_12_26505_345656
  · exact context_12_26506_345687
  · exact context_12_26507_345727

theorem selected_cut_13119 : selected 9 ⟨345757, by decide⟩
    (prefixPartial 12 26508) = some ⟨12, 2, 0, 345757, 26508, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_26508_345757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26508 ⟨345757, by decide⟩ :=
  accepted_of_selected 12 26508 ⟨345757, by decide⟩ ⟨12, 2, 0, 345757, 26508, 2249, 65536⟩
    (by decide) selected_cut_13119

theorem selected_cut_13120 : selected 9 ⟨345789, by decide⟩
    (prefixPartial 12 26509) = some ⟨12, 2, 0, 345789, 26509, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_26509_345789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26509 ⟨345789, by decide⟩ :=
  accepted_of_selected 12 26509 ⟨345789, by decide⟩ ⟨12, 2, 0, 345789, 26509, 2253, 65536⟩
    (by decide) selected_cut_13120

theorem selected_cut_13121 : selected 9 ⟨345816, by decide⟩
    (prefixPartial 12 26510) = some ⟨12, 2, 0, 345816, 26510, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_26510_345816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26510 ⟨345816, by decide⟩ :=
  accepted_of_selected 12 26510 ⟨345816, by decide⟩ ⟨12, 2, 0, 345816, 26510, 2057, 65536⟩
    (by decide) selected_cut_13121

theorem selected_cut_13122 : selected 9 ⟨345885, by decide⟩
    (prefixPartial 12 26511) = some ⟨12, 2, 0, 345885, 26511, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_26511_345885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26511 ⟨345885, by decide⟩ :=
  accepted_of_selected 12 26511 ⟨345885, by decide⟩ ⟨12, 2, 0, 345885, 26511, 3405, 65536⟩
    (by decide) selected_cut_13122

theorem unmarked_context_11_6627_345886 : frontier 10 ⟨345886, by decide⟩
    (prefixCache 11 6627) (prefixPartial 11 6627) = false := by
  decide +kernel

theorem node_context_11_6627_345886 : EJMOriginalGlobalDAGData.nodes 10 ⟨345886, by decide⟩ =
    .split (coordinate 11) (![⟨345757, by decide⟩,⟨345789, by decide⟩,⟨345816, by decide⟩,⟨345885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6627_345886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6627 ⟨345886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6627
    ⟨345886, by decide⟩ (by decide) (![⟨345757, by decide⟩,⟨345789, by decide⟩,⟨345816, by decide⟩,⟨345885, by decide⟩]) unmarked_context_11_6627_345886 node_context_11_6627_345886
  intro a
  fin_cases a
  · exact context_12_26508_345757
  · exact context_12_26509_345789
  · exact context_12_26510_345816
  · exact context_12_26511_345885

theorem unmarked_context_10_1656_345887 : frontier 11 ⟨345887, by decide⟩
    (prefixCache 10 1656) (prefixPartial 10 1656) = false := by
  decide +kernel

theorem node_context_10_1656_345887 : EJMOriginalGlobalDAGData.nodes 11 ⟨345887, by decide⟩ =
    .split (coordinate 10) (![⟨345422, by decide⟩,⟨345551, by decide⟩,⟨345728, by decide⟩,⟨345886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1656_345887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1656 ⟨345887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1656
    ⟨345887, by decide⟩ (by decide) (![⟨345422, by decide⟩,⟨345551, by decide⟩,⟨345728, by decide⟩,⟨345886, by decide⟩]) unmarked_context_10_1656_345887 node_context_10_1656_345887
  intro a
  fin_cases a
  · exact context_11_6624_345422
  · exact context_11_6625_345551
  · exact context_11_6626_345728
  · exact context_11_6627_345886

theorem selected_cut_13123 : selected 9 ⟨345908, by decide⟩
    (prefixPartial 12 26512) = some ⟨12, 2, 0, 345908, 26512, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_26512_345908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26512 ⟨345908, by decide⟩ :=
  accepted_of_selected 12 26512 ⟨345908, by decide⟩ ⟨12, 2, 0, 345908, 26512, 2089, 65536⟩
    (by decide) selected_cut_13123

theorem selected_cut_13124 : selected 9 ⟨345938, by decide⟩
    (prefixPartial 12 26513) = some ⟨12, 2, 0, 345938, 26513, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_26513_345938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26513 ⟨345938, by decide⟩ :=
  accepted_of_selected 12 26513 ⟨345938, by decide⟩ ⟨12, 2, 0, 345938, 26513, 2133, 65536⟩
    (by decide) selected_cut_13124

theorem selected_cut_13125 : selected 9 ⟨345966, by decide⟩
    (prefixPartial 12 26514) = some ⟨12, 2, 0, 345966, 26514, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_26514_345966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26514 ⟨345966, by decide⟩ :=
  accepted_of_selected 12 26514 ⟨345966, by decide⟩ ⟨12, 2, 0, 345966, 26514, 2109, 65536⟩
    (by decide) selected_cut_13125

theorem selected_cut_13126 : selected 9 ⟨345990, by decide⟩
    (prefixPartial 12 26515) = some ⟨12, 2, 0, 345990, 26515, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_26515_345990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26515 ⟨345990, by decide⟩ :=
  accepted_of_selected 12 26515 ⟨345990, by decide⟩ ⟨12, 2, 0, 345990, 26515, 2005, 65536⟩
    (by decide) selected_cut_13126

theorem unmarked_context_11_6628_345991 : frontier 10 ⟨345991, by decide⟩
    (prefixCache 11 6628) (prefixPartial 11 6628) = false := by
  decide +kernel

theorem node_context_11_6628_345991 : EJMOriginalGlobalDAGData.nodes 10 ⟨345991, by decide⟩ =
    .split (coordinate 11) (![⟨345908, by decide⟩,⟨345938, by decide⟩,⟨345966, by decide⟩,⟨345990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6628_345991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6628 ⟨345991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6628
    ⟨345991, by decide⟩ (by decide) (![⟨345908, by decide⟩,⟨345938, by decide⟩,⟨345966, by decide⟩,⟨345990, by decide⟩]) unmarked_context_11_6628_345991 node_context_11_6628_345991
  intro a
  fin_cases a
  · exact context_12_26512_345908
  · exact context_12_26513_345938
  · exact context_12_26514_345966
  · exact context_12_26515_345990

theorem selected_cut_13127 : selected 9 ⟨346047, by decide⟩
    (prefixPartial 12 26516) = some ⟨12, 2, 0, 346047, 26516, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_26516_346047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26516 ⟨346047, by decide⟩ :=
  accepted_of_selected 12 26516 ⟨346047, by decide⟩ ⟨12, 2, 0, 346047, 26516, 2785, 65536⟩
    (by decide) selected_cut_13127

theorem selected_cut_13128 : selected 9 ⟨346104, by decide⟩
    (prefixPartial 12 26517) = some ⟨12, 2, 0, 346104, 26517, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_26517_346104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26517 ⟨346104, by decide⟩ :=
  accepted_of_selected 12 26517 ⟨346104, by decide⟩ ⟨12, 2, 0, 346104, 26517, 2741, 65536⟩
    (by decide) selected_cut_13128

theorem selected_cut_13129 : selected 9 ⟨346180, by decide⟩
    (prefixPartial 12 26518) = some ⟨12, 2, 0, 346180, 26518, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_26518_346180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26518 ⟨346180, by decide⟩ :=
  accepted_of_selected 12 26518 ⟨346180, by decide⟩ ⟨12, 2, 0, 346180, 26518, 2957, 65536⟩
    (by decide) selected_cut_13129

theorem selected_cut_13130 : selected 9 ⟨346218, by decide⟩
    (prefixPartial 12 26519) = some ⟨12, 2, 0, 346218, 26519, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_26519_346218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26519 ⟨346218, by decide⟩ :=
  accepted_of_selected 12 26519 ⟨346218, by decide⟩ ⟨12, 2, 0, 346218, 26519, 2717, 65536⟩
    (by decide) selected_cut_13130

theorem unmarked_context_11_6629_346219 : frontier 10 ⟨346219, by decide⟩
    (prefixCache 11 6629) (prefixPartial 11 6629) = false := by
  decide +kernel

theorem node_context_11_6629_346219 : EJMOriginalGlobalDAGData.nodes 10 ⟨346219, by decide⟩ =
    .split (coordinate 11) (![⟨346047, by decide⟩,⟨346104, by decide⟩,⟨346180, by decide⟩,⟨346218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6629_346219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6629 ⟨346219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6629
    ⟨346219, by decide⟩ (by decide) (![⟨346047, by decide⟩,⟨346104, by decide⟩,⟨346180, by decide⟩,⟨346218, by decide⟩]) unmarked_context_11_6629_346219 node_context_11_6629_346219
  intro a
  fin_cases a
  · exact context_12_26516_346047
  · exact context_12_26517_346104
  · exact context_12_26518_346180
  · exact context_12_26519_346218

theorem selected_cut_13131 : selected 9 ⟨346254, by decide⟩
    (prefixPartial 12 26520) = some ⟨12, 2, 0, 346254, 26520, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_26520_346254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26520 ⟨346254, by decide⟩ :=
  accepted_of_selected 12 26520 ⟨346254, by decide⟩ ⟨12, 2, 0, 346254, 26520, 2185, 65536⟩
    (by decide) selected_cut_13131

theorem selected_cut_13132 : selected 9 ⟨346288, by decide⟩
    (prefixPartial 12 26521) = some ⟨12, 2, 0, 346288, 26521, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_26521_346288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26521 ⟨346288, by decide⟩ :=
  accepted_of_selected 12 26521 ⟨346288, by decide⟩ ⟨12, 2, 0, 346288, 26521, 2153, 65536⟩
    (by decide) selected_cut_13132

theorem selected_cut_13133 : selected 9 ⟨346314, by decide⟩
    (prefixPartial 12 26522) = some ⟨12, 2, 0, 346314, 26522, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_26522_346314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26522 ⟨346314, by decide⟩ :=
  accepted_of_selected 12 26522 ⟨346314, by decide⟩ ⟨12, 2, 0, 346314, 26522, 2045, 65536⟩
    (by decide) selected_cut_13133

theorem selected_cut_13134 : selected 9 ⟨346345, by decide⟩
    (prefixPartial 12 26523) = some ⟨12, 2, 0, 346345, 26523, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_26523_346345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26523 ⟨346345, by decide⟩ :=
  accepted_of_selected 12 26523 ⟨346345, by decide⟩ ⟨12, 2, 0, 346345, 26523, 1845, 65536⟩
    (by decide) selected_cut_13134

theorem unmarked_context_11_6630_346346 : frontier 10 ⟨346346, by decide⟩
    (prefixCache 11 6630) (prefixPartial 11 6630) = false := by
  decide +kernel

theorem node_context_11_6630_346346 : EJMOriginalGlobalDAGData.nodes 10 ⟨346346, by decide⟩ =
    .split (coordinate 11) (![⟨346254, by decide⟩,⟨346288, by decide⟩,⟨346314, by decide⟩,⟨346345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6630_346346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6630 ⟨346346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6630
    ⟨346346, by decide⟩ (by decide) (![⟨346254, by decide⟩,⟨346288, by decide⟩,⟨346314, by decide⟩,⟨346345, by decide⟩]) unmarked_context_11_6630_346346 node_context_11_6630_346346
  intro a
  fin_cases a
  · exact context_12_26520_346254
  · exact context_12_26521_346288
  · exact context_12_26522_346314
  · exact context_12_26523_346345

theorem selected_cut_13135 : selected 9 ⟨346364, by decide⟩
    (prefixPartial 12 26524) = some ⟨12, 2, 0, 346364, 26524, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_26524_346364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26524 ⟨346364, by decide⟩ :=
  accepted_of_selected 12 26524 ⟨346364, by decide⟩ ⟨12, 2, 0, 346364, 26524, 1625, 65536⟩
    (by decide) selected_cut_13135

theorem selected_cut_13136 : selected 9 ⟨346388, by decide⟩
    (prefixPartial 12 26525) = some ⟨12, 2, 0, 346388, 26525, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_26525_346388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26525 ⟨346388, by decide⟩ :=
  accepted_of_selected 12 26525 ⟨346388, by decide⟩ ⟨12, 2, 0, 346388, 26525, 1721, 65536⟩
    (by decide) selected_cut_13136

theorem selected_cut_13137 : selected 9 ⟨346408, by decide⟩
    (prefixPartial 12 26526) = some ⟨12, 2, 0, 346408, 26526, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_26526_346408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26526 ⟨346408, by decide⟩ :=
  accepted_of_selected 12 26526 ⟨346408, by decide⟩ ⟨12, 2, 0, 346408, 26526, 1577, 65536⟩
    (by decide) selected_cut_13137

theorem selected_cut_13138 : selected 9 ⟨346448, by decide⟩
    (prefixPartial 12 26527) = some ⟨12, 2, 0, 346448, 26527, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_26527_346448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26527 ⟨346448, by decide⟩ :=
  accepted_of_selected 12 26527 ⟨346448, by decide⟩ ⟨12, 2, 0, 346448, 26527, 2457, 65536⟩
    (by decide) selected_cut_13138

theorem unmarked_context_11_6631_346449 : frontier 10 ⟨346449, by decide⟩
    (prefixCache 11 6631) (prefixPartial 11 6631) = false := by
  decide +kernel

theorem node_context_11_6631_346449 : EJMOriginalGlobalDAGData.nodes 10 ⟨346449, by decide⟩ =
    .split (coordinate 11) (![⟨346364, by decide⟩,⟨346388, by decide⟩,⟨346408, by decide⟩,⟨346448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6631_346449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6631 ⟨346449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6631
    ⟨346449, by decide⟩ (by decide) (![⟨346364, by decide⟩,⟨346388, by decide⟩,⟨346408, by decide⟩,⟨346448, by decide⟩]) unmarked_context_11_6631_346449 node_context_11_6631_346449
  intro a
  fin_cases a
  · exact context_12_26524_346364
  · exact context_12_26525_346388
  · exact context_12_26526_346408
  · exact context_12_26527_346448

theorem unmarked_context_10_1657_346450 : frontier 11 ⟨346450, by decide⟩
    (prefixCache 10 1657) (prefixPartial 10 1657) = false := by
  decide +kernel

theorem node_context_10_1657_346450 : EJMOriginalGlobalDAGData.nodes 11 ⟨346450, by decide⟩ =
    .split (coordinate 10) (![⟨345991, by decide⟩,⟨346219, by decide⟩,⟨346346, by decide⟩,⟨346449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1657_346450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1657 ⟨346450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1657
    ⟨346450, by decide⟩ (by decide) (![⟨345991, by decide⟩,⟨346219, by decide⟩,⟨346346, by decide⟩,⟨346449, by decide⟩]) unmarked_context_10_1657_346450 node_context_10_1657_346450
  intro a
  fin_cases a
  · exact context_11_6628_345991
  · exact context_11_6629_346219
  · exact context_11_6630_346346
  · exact context_11_6631_346449

theorem selected_cut_13139 : selected 9 ⟨346471, by decide⟩
    (prefixPartial 12 26528) = some ⟨12, 2, 0, 346471, 26528, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_26528_346471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26528 ⟨346471, by decide⟩ :=
  accepted_of_selected 12 26528 ⟨346471, by decide⟩ ⟨12, 2, 0, 346471, 26528, 1445, 65536⟩
    (by decide) selected_cut_13139

theorem selected_cut_13140 : selected 9 ⟨346495, by decide⟩
    (prefixPartial 12 26529) = some ⟨12, 2, 0, 346495, 26529, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_26529_346495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26529 ⟨346495, by decide⟩ :=
  accepted_of_selected 12 26529 ⟨346495, by decide⟩ ⟨12, 2, 0, 346495, 26529, 1549, 65536⟩
    (by decide) selected_cut_13140

theorem selected_cut_13141 : selected 9 ⟨346512, by decide⟩
    (prefixPartial 12 26530) = some ⟨12, 2, 0, 346512, 26530, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_26530_346512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26530 ⟨346512, by decide⟩ :=
  accepted_of_selected 12 26530 ⟨346512, by decide⟩ ⟨12, 2, 0, 346512, 26530, 1345, 65536⟩
    (by decide) selected_cut_13141

theorem selected_cut_13142 : selected 9 ⟨346530, by decide⟩
    (prefixPartial 12 26531) = some ⟨12, 2, 0, 346530, 26531, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_26531_346530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26531 ⟨346530, by decide⟩ :=
  accepted_of_selected 12 26531 ⟨346530, by decide⟩ ⟨12, 2, 0, 346530, 26531, 1313, 65536⟩
    (by decide) selected_cut_13142

theorem unmarked_context_11_6632_346531 : frontier 10 ⟨346531, by decide⟩
    (prefixCache 11 6632) (prefixPartial 11 6632) = false := by
  decide +kernel

theorem node_context_11_6632_346531 : EJMOriginalGlobalDAGData.nodes 10 ⟨346531, by decide⟩ =
    .split (coordinate 11) (![⟨346471, by decide⟩,⟨346495, by decide⟩,⟨346512, by decide⟩,⟨346530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6632_346531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6632 ⟨346531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6632
    ⟨346531, by decide⟩ (by decide) (![⟨346471, by decide⟩,⟨346495, by decide⟩,⟨346512, by decide⟩,⟨346530, by decide⟩]) unmarked_context_11_6632_346531 node_context_11_6632_346531
  intro a
  fin_cases a
  · exact context_12_26528_346471
  · exact context_12_26529_346495
  · exact context_12_26530_346512
  · exact context_12_26531_346530

theorem selected_cut_13143 : selected 9 ⟨346551, by decide⟩
    (prefixPartial 12 26532) = some ⟨12, 2, 0, 346551, 26532, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_26532_346551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26532 ⟨346551, by decide⟩ :=
  accepted_of_selected 12 26532 ⟨346551, by decide⟩ ⟨12, 2, 0, 346551, 26532, 1409, 65536⟩
    (by decide) selected_cut_13143

theorem selected_cut_13144 : selected 9 ⟨346568, by decide⟩
    (prefixPartial 12 26533) = some ⟨12, 2, 0, 346568, 26533, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_26533_346568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26533 ⟨346568, by decide⟩ :=
  accepted_of_selected 12 26533 ⟨346568, by decide⟩ ⟨12, 2, 0, 346568, 26533, 1453, 65536⟩
    (by decide) selected_cut_13144

theorem selected_cut_13145 : selected 9 ⟨346588, by decide⟩
    (prefixPartial 12 26534) = some ⟨12, 2, 0, 346588, 26534, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_26534_346588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26534 ⟨346588, by decide⟩ :=
  accepted_of_selected 12 26534 ⟨346588, by decide⟩ ⟨12, 2, 0, 346588, 26534, 1353, 65536⟩
    (by decide) selected_cut_13145

theorem selected_cut_13146 : selected 9 ⟨346604, by decide⟩
    (prefixPartial 12 26535) = some ⟨12, 2, 0, 346604, 26535, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_26535_346604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26535 ⟨346604, by decide⟩ :=
  accepted_of_selected 12 26535 ⟨346604, by decide⟩ ⟨12, 2, 0, 346604, 26535, 1345, 65536⟩
    (by decide) selected_cut_13146

theorem unmarked_context_11_6633_346605 : frontier 10 ⟨346605, by decide⟩
    (prefixCache 11 6633) (prefixPartial 11 6633) = false := by
  decide +kernel

theorem node_context_11_6633_346605 : EJMOriginalGlobalDAGData.nodes 10 ⟨346605, by decide⟩ =
    .split (coordinate 11) (![⟨346551, by decide⟩,⟨346568, by decide⟩,⟨346588, by decide⟩,⟨346604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6633_346605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6633 ⟨346605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6633
    ⟨346605, by decide⟩ (by decide) (![⟨346551, by decide⟩,⟨346568, by decide⟩,⟨346588, by decide⟩,⟨346604, by decide⟩]) unmarked_context_11_6633_346605 node_context_11_6633_346605
  intro a
  fin_cases a
  · exact context_12_26532_346551
  · exact context_12_26533_346568
  · exact context_12_26534_346588
  · exact context_12_26535_346604

theorem selected_cut_13147 : selected 9 ⟨346626, by decide⟩
    (prefixPartial 12 26536) = some ⟨12, 2, 0, 346626, 26536, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_26536_346626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26536 ⟨346626, by decide⟩ :=
  accepted_of_selected 12 26536 ⟨346626, by decide⟩ ⟨12, 2, 0, 346626, 26536, 1533, 65536⟩
    (by decide) selected_cut_13147

theorem selected_cut_13148 : selected 9 ⟨346650, by decide⟩
    (prefixPartial 12 26537) = some ⟨12, 2, 0, 346650, 26537, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_26537_346650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26537 ⟨346650, by decide⟩ :=
  accepted_of_selected 12 26537 ⟨346650, by decide⟩ ⟨12, 2, 0, 346650, 26537, 1521, 65536⟩
    (by decide) selected_cut_13148

theorem selected_cut_13149 : selected 9 ⟨346664, by decide⟩
    (prefixPartial 12 26538) = some ⟨12, 2, 0, 346664, 26538, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_26538_346664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26538 ⟨346664, by decide⟩ :=
  accepted_of_selected 12 26538 ⟨346664, by decide⟩ ⟨12, 2, 0, 346664, 26538, 1349, 65536⟩
    (by decide) selected_cut_13149

theorem selected_cut_13150 : selected 9 ⟨346678, by decide⟩
    (prefixPartial 12 26539) = some ⟨12, 2, 0, 346678, 26539, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_26539_346678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26539 ⟨346678, by decide⟩ :=
  accepted_of_selected 12 26539 ⟨346678, by decide⟩ ⟨12, 2, 0, 346678, 26539, 1185, 65536⟩
    (by decide) selected_cut_13150

theorem unmarked_context_11_6634_346679 : frontier 10 ⟨346679, by decide⟩
    (prefixCache 11 6634) (prefixPartial 11 6634) = false := by
  decide +kernel

theorem node_context_11_6634_346679 : EJMOriginalGlobalDAGData.nodes 10 ⟨346679, by decide⟩ =
    .split (coordinate 11) (![⟨346626, by decide⟩,⟨346650, by decide⟩,⟨346664, by decide⟩,⟨346678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6634_346679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6634 ⟨346679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6634
    ⟨346679, by decide⟩ (by decide) (![⟨346626, by decide⟩,⟨346650, by decide⟩,⟨346664, by decide⟩,⟨346678, by decide⟩]) unmarked_context_11_6634_346679 node_context_11_6634_346679
  intro a
  fin_cases a
  · exact context_12_26536_346626
  · exact context_12_26537_346650
  · exact context_12_26538_346664
  · exact context_12_26539_346678

theorem selected_cut_13151 : selected 9 ⟨346698, by decide⟩
    (prefixPartial 12 26540) = some ⟨12, 2, 0, 346698, 26540, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_26540_346698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26540 ⟨346698, by decide⟩ :=
  accepted_of_selected 12 26540 ⟨346698, by decide⟩ ⟨12, 2, 0, 346698, 26540, 1257, 65536⟩
    (by decide) selected_cut_13151

theorem selected_cut_13152 : selected 9 ⟨346722, by decide⟩
    (prefixPartial 12 26541) = some ⟨12, 2, 0, 346722, 26541, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_26541_346722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26541 ⟨346722, by decide⟩ :=
  accepted_of_selected 12 26541 ⟨346722, by decide⟩ ⟨12, 2, 0, 346722, 26541, 1313, 65536⟩
    (by decide) selected_cut_13152

theorem selected_cut_13153 : selected 9 ⟨346738, by decide⟩
    (prefixPartial 12 26542) = some ⟨12, 2, 0, 346738, 26542, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_26542_346738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26542 ⟨346738, by decide⟩ :=
  accepted_of_selected 12 26542 ⟨346738, by decide⟩ ⟨12, 2, 0, 346738, 26542, 1149, 65536⟩
    (by decide) selected_cut_13153

theorem selected_cut_13154 : selected 9 ⟨346780, by decide⟩
    (prefixPartial 12 26543) = some ⟨12, 2, 0, 346780, 26543, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_26543_346780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26543 ⟨346780, by decide⟩ :=
  accepted_of_selected 12 26543 ⟨346780, by decide⟩ ⟨12, 2, 0, 346780, 26543, 1789, 65536⟩
    (by decide) selected_cut_13154

theorem unmarked_context_11_6635_346781 : frontier 10 ⟨346781, by decide⟩
    (prefixCache 11 6635) (prefixPartial 11 6635) = false := by
  decide +kernel

theorem node_context_11_6635_346781 : EJMOriginalGlobalDAGData.nodes 10 ⟨346781, by decide⟩ =
    .split (coordinate 11) (![⟨346698, by decide⟩,⟨346722, by decide⟩,⟨346738, by decide⟩,⟨346780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6635_346781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6635 ⟨346781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6635
    ⟨346781, by decide⟩ (by decide) (![⟨346698, by decide⟩,⟨346722, by decide⟩,⟨346738, by decide⟩,⟨346780, by decide⟩]) unmarked_context_11_6635_346781 node_context_11_6635_346781
  intro a
  fin_cases a
  · exact context_12_26540_346698
  · exact context_12_26541_346722
  · exact context_12_26542_346738
  · exact context_12_26543_346780

theorem unmarked_context_10_1658_346782 : frontier 11 ⟨346782, by decide⟩
    (prefixCache 10 1658) (prefixPartial 10 1658) = false := by
  decide +kernel

theorem node_context_10_1658_346782 : EJMOriginalGlobalDAGData.nodes 11 ⟨346782, by decide⟩ =
    .split (coordinate 10) (![⟨346531, by decide⟩,⟨346605, by decide⟩,⟨346679, by decide⟩,⟨346781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1658_346782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1658 ⟨346782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1658
    ⟨346782, by decide⟩ (by decide) (![⟨346531, by decide⟩,⟨346605, by decide⟩,⟨346679, by decide⟩,⟨346781, by decide⟩]) unmarked_context_10_1658_346782 node_context_10_1658_346782
  intro a
  fin_cases a
  · exact context_11_6632_346531
  · exact context_11_6633_346605
  · exact context_11_6634_346679
  · exact context_11_6635_346781

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
