/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover331
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31876 : selected 8 ⟨817866, by decide⟩
    (prefixPartial 13 430267) = some ⟨13, 2, 0, 817866, 430267, 825, 16384⟩ := by
  decide +kernel

theorem context_13_430267_817866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430267 ⟨817866, by decide⟩ :=
  accepted_of_selected 13 430267 ⟨817866, by decide⟩ ⟨13, 2, 0, 817866, 430267, 825, 16384⟩
    (by decide) selected_cut_31876

theorem unmarked_context_12_107566_817867 : frontier 9 ⟨817867, by decide⟩
    (prefixCache 12 107566) (prefixPartial 12 107566) = false := by
  decide +kernel

theorem node_context_12_107566_817867 : EJMOriginalGlobalDAGData.nodes 9 ⟨817867, by decide⟩ =
    .split (coordinate 12) (![⟨817796, by decide⟩,⟨817845, by decide⟩,⟨817859, by decide⟩,⟨817866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107566_817867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107566 ⟨817867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107566
    ⟨817867, by decide⟩ (by decide) (![⟨817796, by decide⟩,⟨817845, by decide⟩,⟨817859, by decide⟩,⟨817866, by decide⟩]) unmarked_context_12_107566_817867 node_context_12_107566_817867
  intro a
  fin_cases a
  · exact context_13_430264_817796
  · exact context_13_430265_817845
  · exact context_13_430266_817859
  · exact context_13_430267_817866

theorem selected_cut_31877 : selected 8 ⟨817881, by decide⟩
    (prefixPartial 13 430268) = some ⟨13, 2, 0, 817881, 430268, 701, 16384⟩ := by
  decide +kernel

theorem context_13_430268_817881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430268 ⟨817881, by decide⟩ :=
  accepted_of_selected 13 430268 ⟨817881, by decide⟩ ⟨13, 2, 0, 817881, 430268, 701, 16384⟩
    (by decide) selected_cut_31877

theorem selected_cut_31878 : selected 8 ⟨817924, by decide⟩
    (prefixPartial 13 430269) = some ⟨13, 2, 0, 817924, 430269, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_430269_817924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430269 ⟨817924, by decide⟩ :=
  accepted_of_selected 13 430269 ⟨817924, by decide⟩ ⟨13, 2, 0, 817924, 430269, 2205, 16384⟩
    (by decide) selected_cut_31878

theorem selected_cut_31879 : selected 8 ⟨817940, by decide⟩
    (prefixPartial 13 430270) = some ⟨13, 2, 0, 817940, 430270, 933, 16384⟩ := by
  decide +kernel

theorem context_13_430270_817940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430270 ⟨817940, by decide⟩ :=
  accepted_of_selected 13 430270 ⟨817940, by decide⟩ ⟨13, 2, 0, 817940, 430270, 933, 16384⟩
    (by decide) selected_cut_31879

theorem selected_cut_31880 : selected 8 ⟨817946, by decide⟩
    (prefixPartial 13 430271) = some ⟨13, 2, 0, 817946, 430271, 753, 16384⟩ := by
  decide +kernel

theorem context_13_430271_817946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430271 ⟨817946, by decide⟩ :=
  accepted_of_selected 13 430271 ⟨817946, by decide⟩ ⟨13, 2, 0, 817946, 430271, 753, 16384⟩
    (by decide) selected_cut_31880

theorem unmarked_context_12_107567_817947 : frontier 9 ⟨817947, by decide⟩
    (prefixCache 12 107567) (prefixPartial 12 107567) = false := by
  decide +kernel

theorem node_context_12_107567_817947 : EJMOriginalGlobalDAGData.nodes 9 ⟨817947, by decide⟩ =
    .split (coordinate 12) (![⟨817881, by decide⟩,⟨817924, by decide⟩,⟨817940, by decide⟩,⟨817946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107567_817947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107567 ⟨817947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107567
    ⟨817947, by decide⟩ (by decide) (![⟨817881, by decide⟩,⟨817924, by decide⟩,⟨817940, by decide⟩,⟨817946, by decide⟩]) unmarked_context_12_107567_817947 node_context_12_107567_817947
  intro a
  fin_cases a
  · exact context_13_430268_817881
  · exact context_13_430269_817924
  · exact context_13_430270_817940
  · exact context_13_430271_817946

theorem unmarked_context_11_26891_817948 : frontier 10 ⟨817948, by decide⟩
    (prefixCache 11 26891) (prefixPartial 11 26891) = false := by
  decide +kernel

theorem node_context_11_26891_817948 : EJMOriginalGlobalDAGData.nodes 10 ⟨817948, by decide⟩ =
    .split (coordinate 11) (![⟨817687, by decide⟩,⟨817782, by decide⟩,⟨817867, by decide⟩,⟨817947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26891_817948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26891 ⟨817948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26891
    ⟨817948, by decide⟩ (by decide) (![⟨817687, by decide⟩,⟨817782, by decide⟩,⟨817867, by decide⟩,⟨817947, by decide⟩]) unmarked_context_11_26891_817948 node_context_11_26891_817948
  intro a
  fin_cases a
  · exact context_12_107564_817687
  · exact context_12_107565_817782
  · exact context_12_107566_817867
  · exact context_12_107567_817947

theorem unmarked_context_10_6722_817949 : frontier 11 ⟨817949, by decide⟩
    (prefixCache 10 6722) (prefixPartial 10 6722) = false := by
  decide +kernel

theorem node_context_10_6722_817949 : EJMOriginalGlobalDAGData.nodes 11 ⟨817949, by decide⟩ =
    .split (coordinate 10) (![⟨816852, by decide⟩,⟨817290, by decide⟩,⟨817590, by decide⟩,⟨817948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6722_817949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6722 ⟨817949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6722
    ⟨817949, by decide⟩ (by decide) (![⟨816852, by decide⟩,⟨817290, by decide⟩,⟨817590, by decide⟩,⟨817948, by decide⟩]) unmarked_context_10_6722_817949 node_context_10_6722_817949
  intro a
  fin_cases a
  · exact context_11_26888_816852
  · exact context_11_26889_817290
  · exact context_11_26890_817590
  · exact context_11_26891_817948

theorem selected_cut_31881 : selected 9 ⟨399079, by decide⟩
    (prefixPartial 12 107568) = some ⟨12, 1, 0, 399079, 107568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107568_399079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107568 ⟨399079, by decide⟩ :=
  accepted_of_selected 12 107568 ⟨399079, by decide⟩ ⟨12, 1, 0, 399079, 107568, 1, 65536⟩
    (by decide) selected_cut_31881

theorem selected_cut_31882 : selected 9 ⟨818022, by decide⟩
    (prefixPartial 12 107569) = some ⟨12, 2, 0, 818022, 107569, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_107569_818022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107569 ⟨818022, by decide⟩ :=
  accepted_of_selected 12 107569 ⟨818022, by decide⟩ ⟨12, 2, 0, 818022, 107569, 3849, 65536⟩
    (by decide) selected_cut_31882

theorem selected_cut_31883 : selected 9 ⟨818078, by decide⟩
    (prefixPartial 12 107570) = some ⟨12, 2, 0, 818078, 107570, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_107570_818078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107570 ⟨818078, by decide⟩ :=
  accepted_of_selected 12 107570 ⟨818078, by decide⟩ ⟨12, 2, 0, 818078, 107570, 3721, 65536⟩
    (by decide) selected_cut_31883

theorem selected_cut_31884 : selected 8 ⟨818093, by decide⟩
    (prefixPartial 13 430284) = some ⟨13, 2, 0, 818093, 430284, 625, 16384⟩ := by
  decide +kernel

theorem context_13_430284_818093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430284 ⟨818093, by decide⟩ :=
  accepted_of_selected 13 430284 ⟨818093, by decide⟩ ⟨13, 2, 0, 818093, 430284, 625, 16384⟩
    (by decide) selected_cut_31884

theorem selected_cut_31885 : selected 8 ⟨818131, by decide⟩
    (prefixPartial 13 430285) = some ⟨13, 2, 0, 818131, 430285, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_430285_818131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430285 ⟨818131, by decide⟩ :=
  accepted_of_selected 13 430285 ⟨818131, by decide⟩ ⟨13, 2, 0, 818131, 430285, 2149, 16384⟩
    (by decide) selected_cut_31885

theorem selected_cut_31886 : selected 8 ⟨818148, by decide⟩
    (prefixPartial 13 430286) = some ⟨13, 2, 0, 818148, 430286, 909, 16384⟩ := by
  decide +kernel

theorem context_13_430286_818148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430286 ⟨818148, by decide⟩ :=
  accepted_of_selected 13 430286 ⟨818148, by decide⟩ ⟨13, 2, 0, 818148, 430286, 909, 16384⟩
    (by decide) selected_cut_31886

theorem selected_cut_31887 : selected 8 ⟨818153, by decide⟩
    (prefixPartial 13 430287) = some ⟨13, 2, 0, 818153, 430287, 645, 16384⟩ := by
  decide +kernel

theorem context_13_430287_818153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430287 ⟨818153, by decide⟩ :=
  accepted_of_selected 13 430287 ⟨818153, by decide⟩ ⟨13, 2, 0, 818153, 430287, 645, 16384⟩
    (by decide) selected_cut_31887

theorem unmarked_context_12_107571_818154 : frontier 9 ⟨818154, by decide⟩
    (prefixCache 12 107571) (prefixPartial 12 107571) = false := by
  decide +kernel

theorem node_context_12_107571_818154 : EJMOriginalGlobalDAGData.nodes 9 ⟨818154, by decide⟩ =
    .split (coordinate 12) (![⟨818093, by decide⟩,⟨818131, by decide⟩,⟨818148, by decide⟩,⟨818153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107571_818154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107571 ⟨818154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107571
    ⟨818154, by decide⟩ (by decide) (![⟨818093, by decide⟩,⟨818131, by decide⟩,⟨818148, by decide⟩,⟨818153, by decide⟩]) unmarked_context_12_107571_818154 node_context_12_107571_818154
  intro a
  fin_cases a
  · exact context_13_430284_818093
  · exact context_13_430285_818131
  · exact context_13_430286_818148
  · exact context_13_430287_818153

theorem unmarked_context_11_26892_818155 : frontier 10 ⟨818155, by decide⟩
    (prefixCache 11 26892) (prefixPartial 11 26892) = false := by
  decide +kernel

theorem node_context_11_26892_818155 : EJMOriginalGlobalDAGData.nodes 10 ⟨818155, by decide⟩ =
    .split (coordinate 11) (![⟨399079, by decide⟩,⟨818022, by decide⟩,⟨818078, by decide⟩,⟨818154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26892_818155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26892 ⟨818155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26892
    ⟨818155, by decide⟩ (by decide) (![⟨399079, by decide⟩,⟨818022, by decide⟩,⟨818078, by decide⟩,⟨818154, by decide⟩]) unmarked_context_11_26892_818155 node_context_11_26892_818155
  intro a
  fin_cases a
  · exact context_12_107568_399079
  · exact context_12_107569_818022
  · exact context_12_107570_818078
  · exact context_12_107571_818154

theorem selected_cut_31888 : selected 9 ⟨818240, by decide⟩
    (prefixPartial 12 107572) = some ⟨12, 2, 0, 818240, 107572, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_107572_818240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107572 ⟨818240, by decide⟩ :=
  accepted_of_selected 12 107572 ⟨818240, by decide⟩ ⟨12, 2, 0, 818240, 107572, 3953, 65536⟩
    (by decide) selected_cut_31888

theorem selected_cut_31889 : selected 9 ⟨818318, by decide⟩
    (prefixPartial 12 107573) = some ⟨12, 2, 0, 818318, 107573, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_107573_818318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107573 ⟨818318, by decide⟩ :=
  accepted_of_selected 12 107573 ⟨818318, by decide⟩ ⟨12, 2, 0, 818318, 107573, 3613, 65536⟩
    (by decide) selected_cut_31889

theorem selected_cut_31890 : selected 9 ⟨818392, by decide⟩
    (prefixPartial 12 107574) = some ⟨12, 2, 0, 818392, 107574, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_107574_818392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107574 ⟨818392, by decide⟩ :=
  accepted_of_selected 12 107574 ⟨818392, by decide⟩ ⟨12, 2, 0, 818392, 107574, 3737, 65536⟩
    (by decide) selected_cut_31890

theorem selected_cut_31891 : selected 8 ⟨818404, by decide⟩
    (prefixPartial 13 430300) = some ⟨13, 2, 0, 818404, 430300, 521, 16384⟩ := by
  decide +kernel

theorem context_13_430300_818404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430300 ⟨818404, by decide⟩ :=
  accepted_of_selected 13 430300 ⟨818404, by decide⟩ ⟨13, 2, 0, 818404, 430300, 521, 16384⟩
    (by decide) selected_cut_31891

theorem selected_cut_31892 : selected 8 ⟨818463, by decide⟩
    (prefixPartial 13 430301) = some ⟨13, 2, 0, 818463, 430301, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_430301_818463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430301 ⟨818463, by decide⟩ :=
  accepted_of_selected 13 430301 ⟨818463, by decide⟩ ⟨13, 2, 0, 818463, 430301, 2297, 16384⟩
    (by decide) selected_cut_31892

theorem selected_cut_31893 : selected 8 ⟨818484, by decide⟩
    (prefixPartial 13 430302) = some ⟨13, 2, 0, 818484, 430302, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_430302_818484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430302 ⟨818484, by decide⟩ :=
  accepted_of_selected 13 430302 ⟨818484, by decide⟩ ⟨13, 2, 0, 818484, 430302, 1109, 16384⟩
    (by decide) selected_cut_31893

theorem selected_cut_31894 : selected 8 ⟨818493, by decide⟩
    (prefixPartial 13 430303) = some ⟨13, 2, 0, 818493, 430303, 665, 16384⟩ := by
  decide +kernel

theorem context_13_430303_818493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430303 ⟨818493, by decide⟩ :=
  accepted_of_selected 13 430303 ⟨818493, by decide⟩ ⟨13, 2, 0, 818493, 430303, 665, 16384⟩
    (by decide) selected_cut_31894

theorem unmarked_context_12_107575_818494 : frontier 9 ⟨818494, by decide⟩
    (prefixCache 12 107575) (prefixPartial 12 107575) = false := by
  decide +kernel

theorem node_context_12_107575_818494 : EJMOriginalGlobalDAGData.nodes 9 ⟨818494, by decide⟩ =
    .split (coordinate 12) (![⟨818404, by decide⟩,⟨818463, by decide⟩,⟨818484, by decide⟩,⟨818493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107575_818494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107575 ⟨818494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107575
    ⟨818494, by decide⟩ (by decide) (![⟨818404, by decide⟩,⟨818463, by decide⟩,⟨818484, by decide⟩,⟨818493, by decide⟩]) unmarked_context_12_107575_818494 node_context_12_107575_818494
  intro a
  fin_cases a
  · exact context_13_430300_818404
  · exact context_13_430301_818463
  · exact context_13_430302_818484
  · exact context_13_430303_818493

theorem unmarked_context_11_26893_818495 : frontier 10 ⟨818495, by decide⟩
    (prefixCache 11 26893) (prefixPartial 11 26893) = false := by
  decide +kernel

theorem node_context_11_26893_818495 : EJMOriginalGlobalDAGData.nodes 10 ⟨818495, by decide⟩ =
    .split (coordinate 11) (![⟨818240, by decide⟩,⟨818318, by decide⟩,⟨818392, by decide⟩,⟨818494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26893_818495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26893 ⟨818495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26893
    ⟨818495, by decide⟩ (by decide) (![⟨818240, by decide⟩,⟨818318, by decide⟩,⟨818392, by decide⟩,⟨818494, by decide⟩]) unmarked_context_11_26893_818495 node_context_11_26893_818495
  intro a
  fin_cases a
  · exact context_12_107572_818240
  · exact context_12_107573_818318
  · exact context_12_107574_818392
  · exact context_12_107575_818494

theorem selected_cut_31895 : selected 9 ⟨818561, by decide⟩
    (prefixPartial 12 107576) = some ⟨12, 2, 0, 818561, 107576, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_107576_818561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107576 ⟨818561, by decide⟩ :=
  accepted_of_selected 12 107576 ⟨818561, by decide⟩ ⟨12, 2, 0, 818561, 107576, 3869, 65536⟩
    (by decide) selected_cut_31895

theorem selected_cut_31896 : selected 9 ⟨818617, by decide⟩
    (prefixPartial 12 107577) = some ⟨12, 2, 0, 818617, 107577, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_107577_818617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107577 ⟨818617, by decide⟩ :=
  accepted_of_selected 12 107577 ⟨818617, by decide⟩ ⟨12, 2, 0, 818617, 107577, 3761, 65536⟩
    (by decide) selected_cut_31896

theorem selected_cut_31897 : selected 9 ⟨818664, by decide⟩
    (prefixPartial 12 107578) = some ⟨12, 2, 0, 818664, 107578, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_107578_818664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107578 ⟨818664, by decide⟩ :=
  accepted_of_selected 12 107578 ⟨818664, by decide⟩ ⟨12, 2, 0, 818664, 107578, 3497, 65536⟩
    (by decide) selected_cut_31897

theorem selected_cut_31898 : selected 8 ⟨818671, by decide⟩
    (prefixPartial 13 430316) = some ⟨13, 2, 0, 818671, 430316, 269, 16384⟩ := by
  decide +kernel

theorem context_13_430316_818671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430316 ⟨818671, by decide⟩ :=
  accepted_of_selected 13 430316 ⟨818671, by decide⟩ ⟨13, 2, 0, 818671, 430316, 269, 16384⟩
    (by decide) selected_cut_31898

theorem selected_cut_31899 : selected 8 ⟨818713, by decide⟩
    (prefixPartial 13 430317) = some ⟨13, 2, 0, 818713, 430317, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_430317_818713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430317 ⟨818713, by decide⟩ :=
  accepted_of_selected 13 430317 ⟨818713, by decide⟩ ⟨13, 2, 0, 818713, 430317, 2209, 16384⟩
    (by decide) selected_cut_31899

theorem selected_cut_31900 : selected 8 ⟨818726, by decide⟩
    (prefixPartial 13 430318) = some ⟨13, 2, 0, 818726, 430318, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_430318_818726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430318 ⟨818726, by decide⟩ :=
  accepted_of_selected 13 430318 ⟨818726, by decide⟩ ⟨13, 2, 0, 818726, 430318, 1109, 16384⟩
    (by decide) selected_cut_31900

theorem selected_cut_31901 : selected 8 ⟨818733, by decide⟩
    (prefixPartial 13 430319) = some ⟨13, 2, 0, 818733, 430319, 601, 16384⟩ := by
  decide +kernel

theorem context_13_430319_818733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430319 ⟨818733, by decide⟩ :=
  accepted_of_selected 13 430319 ⟨818733, by decide⟩ ⟨13, 2, 0, 818733, 430319, 601, 16384⟩
    (by decide) selected_cut_31901

theorem unmarked_context_12_107579_818734 : frontier 9 ⟨818734, by decide⟩
    (prefixCache 12 107579) (prefixPartial 12 107579) = false := by
  decide +kernel

theorem node_context_12_107579_818734 : EJMOriginalGlobalDAGData.nodes 9 ⟨818734, by decide⟩ =
    .split (coordinate 12) (![⟨818671, by decide⟩,⟨818713, by decide⟩,⟨818726, by decide⟩,⟨818733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107579_818734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107579 ⟨818734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107579
    ⟨818734, by decide⟩ (by decide) (![⟨818671, by decide⟩,⟨818713, by decide⟩,⟨818726, by decide⟩,⟨818733, by decide⟩]) unmarked_context_12_107579_818734 node_context_12_107579_818734
  intro a
  fin_cases a
  · exact context_13_430316_818671
  · exact context_13_430317_818713
  · exact context_13_430318_818726
  · exact context_13_430319_818733

theorem unmarked_context_11_26894_818735 : frontier 10 ⟨818735, by decide⟩
    (prefixCache 11 26894) (prefixPartial 11 26894) = false := by
  decide +kernel

theorem node_context_11_26894_818735 : EJMOriginalGlobalDAGData.nodes 10 ⟨818735, by decide⟩ =
    .split (coordinate 11) (![⟨818561, by decide⟩,⟨818617, by decide⟩,⟨818664, by decide⟩,⟨818734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26894_818735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26894 ⟨818735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26894
    ⟨818735, by decide⟩ (by decide) (![⟨818561, by decide⟩,⟨818617, by decide⟩,⟨818664, by decide⟩,⟨818734, by decide⟩]) unmarked_context_11_26894_818735 node_context_11_26894_818735
  intro a
  fin_cases a
  · exact context_12_107576_818561
  · exact context_12_107577_818617
  · exact context_12_107578_818664
  · exact context_12_107579_818734

theorem selected_cut_31902 : selected 9 ⟨818814, by decide⟩
    (prefixPartial 12 107580) = some ⟨12, 2, 0, 818814, 107580, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_107580_818814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107580 ⟨818814, by decide⟩ :=
  accepted_of_selected 12 107580 ⟨818814, by decide⟩ ⟨12, 2, 0, 818814, 107580, 3677, 65536⟩
    (by decide) selected_cut_31902

theorem selected_cut_31903 : selected 9 ⟨818899, by decide⟩
    (prefixPartial 12 107581) = some ⟨12, 2, 0, 818899, 107581, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_107581_818899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107581 ⟨818899, by decide⟩ :=
  accepted_of_selected 12 107581 ⟨818899, by decide⟩ ⟨12, 2, 0, 818899, 107581, 3553, 65536⟩
    (by decide) selected_cut_31903

theorem selected_cut_31904 : selected 9 ⟨818961, by decide⟩
    (prefixPartial 12 107582) = some ⟨12, 2, 0, 818961, 107582, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_107582_818961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107582 ⟨818961, by decide⟩ :=
  accepted_of_selected 12 107582 ⟨818961, by decide⟩ ⟨12, 2, 0, 818961, 107582, 3545, 65536⟩
    (by decide) selected_cut_31904

theorem selected_cut_31905 : selected 9 ⟨819035, by decide⟩
    (prefixPartial 12 107583) = some ⟨12, 2, 0, 819035, 107583, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_107583_819035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107583 ⟨819035, by decide⟩ :=
  accepted_of_selected 12 107583 ⟨819035, by decide⟩ ⟨12, 2, 0, 819035, 107583, 3889, 65536⟩
    (by decide) selected_cut_31905

theorem unmarked_context_11_26895_819036 : frontier 10 ⟨819036, by decide⟩
    (prefixCache 11 26895) (prefixPartial 11 26895) = false := by
  decide +kernel

theorem node_context_11_26895_819036 : EJMOriginalGlobalDAGData.nodes 10 ⟨819036, by decide⟩ =
    .split (coordinate 11) (![⟨818814, by decide⟩,⟨818899, by decide⟩,⟨818961, by decide⟩,⟨819035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26895_819036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26895 ⟨819036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26895
    ⟨819036, by decide⟩ (by decide) (![⟨818814, by decide⟩,⟨818899, by decide⟩,⟨818961, by decide⟩,⟨819035, by decide⟩]) unmarked_context_11_26895_819036 node_context_11_26895_819036
  intro a
  fin_cases a
  · exact context_12_107580_818814
  · exact context_12_107581_818899
  · exact context_12_107582_818961
  · exact context_12_107583_819035

theorem unmarked_context_10_6723_819037 : frontier 11 ⟨819037, by decide⟩
    (prefixCache 10 6723) (prefixPartial 10 6723) = false := by
  decide +kernel

theorem node_context_10_6723_819037 : EJMOriginalGlobalDAGData.nodes 11 ⟨819037, by decide⟩ =
    .split (coordinate 10) (![⟨818155, by decide⟩,⟨818495, by decide⟩,⟨818735, by decide⟩,⟨819036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6723_819037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6723 ⟨819037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6723
    ⟨819037, by decide⟩ (by decide) (![⟨818155, by decide⟩,⟨818495, by decide⟩,⟨818735, by decide⟩,⟨819036, by decide⟩]) unmarked_context_10_6723_819037 node_context_10_6723_819037
  intro a
  fin_cases a
  · exact context_11_26892_818155
  · exact context_11_26893_818495
  · exact context_11_26894_818735
  · exact context_11_26895_819036

theorem unmarked_context_9_1680_819038 : frontier 12 ⟨819038, by decide⟩
    (prefixCache 9 1680) (prefixPartial 9 1680) = false := by
  decide +kernel

theorem node_context_9_1680_819038 : EJMOriginalGlobalDAGData.nodes 12 ⟨819038, by decide⟩ =
    .split (coordinate 9) (![⟨815336, by decide⟩,⟨816532, by decide⟩,⟨817949, by decide⟩,⟨819037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1680_819038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1680 ⟨819038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1680
    ⟨819038, by decide⟩ (by decide) (![⟨815336, by decide⟩,⟨816532, by decide⟩,⟨817949, by decide⟩,⟨819037, by decide⟩]) unmarked_context_9_1680_819038 node_context_9_1680_819038
  intro a
  fin_cases a
  · exact context_10_6720_815336
  · exact context_10_6721_816532
  · exact context_10_6722_817949
  · exact context_10_6723_819037

theorem selected_cut_31906 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 6724) = some ⟨10, 1, 0, 145424, 6724, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6724_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6724 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 6724 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 6724, 1, 1048576⟩
    (by decide) selected_cut_31906

theorem selected_cut_31907 : selected 9 ⟨815337, by decide⟩
    (prefixPartial 12 107600) = some ⟨12, 1, 0, 815337, 107600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107600_815337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107600 ⟨815337, by decide⟩ :=
  accepted_of_selected 12 107600 ⟨815337, by decide⟩ ⟨12, 1, 0, 815337, 107600, 1, 65536⟩
    (by decide) selected_cut_31907

theorem selected_cut_31908 : selected 9 ⟨819091, by decide⟩
    (prefixPartial 12 107601) = some ⟨12, 2, 0, 819091, 107601, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_107601_819091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107601 ⟨819091, by decide⟩ :=
  accepted_of_selected 12 107601 ⟨819091, by decide⟩ ⟨12, 2, 0, 819091, 107601, 3145, 65536⟩
    (by decide) selected_cut_31908

theorem selected_cut_31909 : selected 9 ⟨819139, by decide⟩
    (prefixPartial 12 107602) = some ⟨12, 2, 0, 819139, 107602, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_107602_819139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107602 ⟨819139, by decide⟩ :=
  accepted_of_selected 12 107602 ⟨819139, by decide⟩ ⟨12, 2, 0, 819139, 107602, 3265, 65536⟩
    (by decide) selected_cut_31909

theorem selected_cut_31910 : selected 9 ⟨819209, by decide⟩
    (prefixPartial 12 107603) = some ⟨12, 2, 0, 819209, 107603, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_107603_819209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107603 ⟨819209, by decide⟩ :=
  accepted_of_selected 12 107603 ⟨819209, by decide⟩ ⟨12, 2, 0, 819209, 107603, 3281, 65536⟩
    (by decide) selected_cut_31910

theorem unmarked_context_11_26900_819210 : frontier 10 ⟨819210, by decide⟩
    (prefixCache 11 26900) (prefixPartial 11 26900) = false := by
  decide +kernel

theorem node_context_11_26900_819210 : EJMOriginalGlobalDAGData.nodes 10 ⟨819210, by decide⟩ =
    .split (coordinate 11) (![⟨815337, by decide⟩,⟨819091, by decide⟩,⟨819139, by decide⟩,⟨819209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26900_819210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26900 ⟨819210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26900
    ⟨819210, by decide⟩ (by decide) (![⟨815337, by decide⟩,⟨819091, by decide⟩,⟨819139, by decide⟩,⟨819209, by decide⟩]) unmarked_context_11_26900_819210 node_context_11_26900_819210
  intro a
  fin_cases a
  · exact context_12_107600_815337
  · exact context_12_107601_819091
  · exact context_12_107602_819139
  · exact context_12_107603_819209

theorem selected_cut_31911 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 26901) = some ⟨11, 1, 0, 451541, 26901, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26901_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26901 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 26901 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 26901, 1, 262144⟩
    (by decide) selected_cut_31911

theorem selected_cut_31912 : selected 9 ⟨819263, by decide⟩
    (prefixPartial 12 107608) = some ⟨12, 2, 0, 819263, 107608, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_107608_819263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107608 ⟨819263, by decide⟩ :=
  accepted_of_selected 12 107608 ⟨819263, by decide⟩ ⟨12, 2, 0, 819263, 107608, 2897, 65536⟩
    (by decide) selected_cut_31912

theorem selected_cut_31913 : selected 9 ⟨819309, by decide⟩
    (prefixPartial 12 107609) = some ⟨12, 2, 0, 819309, 107609, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_107609_819309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107609 ⟨819309, by decide⟩ :=
  accepted_of_selected 12 107609 ⟨819309, by decide⟩ ⟨12, 2, 0, 819309, 107609, 2721, 65536⟩
    (by decide) selected_cut_31913

theorem selected_cut_31914 : selected 9 ⟨819360, by decide⟩
    (prefixPartial 12 107610) = some ⟨12, 2, 0, 819360, 107610, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_107610_819360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107610 ⟨819360, by decide⟩ :=
  accepted_of_selected 12 107610 ⟨819360, by decide⟩ ⟨12, 2, 0, 819360, 107610, 2873, 65536⟩
    (by decide) selected_cut_31914

theorem selected_cut_31915 : selected 9 ⟨819425, by decide⟩
    (prefixPartial 12 107611) = some ⟨12, 2, 0, 819425, 107611, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_107611_819425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107611 ⟨819425, by decide⟩ :=
  accepted_of_selected 12 107611 ⟨819425, by decide⟩ ⟨12, 2, 0, 819425, 107611, 2969, 65536⟩
    (by decide) selected_cut_31915

theorem unmarked_context_11_26902_819426 : frontier 10 ⟨819426, by decide⟩
    (prefixCache 11 26902) (prefixPartial 11 26902) = false := by
  decide +kernel

theorem node_context_11_26902_819426 : EJMOriginalGlobalDAGData.nodes 10 ⟨819426, by decide⟩ =
    .split (coordinate 11) (![⟨819263, by decide⟩,⟨819309, by decide⟩,⟨819360, by decide⟩,⟨819425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26902_819426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26902 ⟨819426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26902
    ⟨819426, by decide⟩ (by decide) (![⟨819263, by decide⟩,⟨819309, by decide⟩,⟨819360, by decide⟩,⟨819425, by decide⟩]) unmarked_context_11_26902_819426 node_context_11_26902_819426
  intro a
  fin_cases a
  · exact context_12_107608_819263
  · exact context_12_107609_819309
  · exact context_12_107610_819360
  · exact context_12_107611_819425

theorem selected_cut_31916 : selected 9 ⟨819487, by decide⟩
    (prefixPartial 12 107612) = some ⟨12, 2, 0, 819487, 107612, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_107612_819487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107612 ⟨819487, by decide⟩ :=
  accepted_of_selected 12 107612 ⟨819487, by decide⟩ ⟨12, 2, 0, 819487, 107612, 2793, 65536⟩
    (by decide) selected_cut_31916

theorem selected_cut_31917 : selected 9 ⟨819538, by decide⟩
    (prefixPartial 12 107613) = some ⟨12, 2, 0, 819538, 107613, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_107613_819538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107613 ⟨819538, by decide⟩ :=
  accepted_of_selected 12 107613 ⟨819538, by decide⟩ ⟨12, 2, 0, 819538, 107613, 2817, 65536⟩
    (by decide) selected_cut_31917

theorem selected_cut_31918 : selected 9 ⟨819592, by decide⟩
    (prefixPartial 12 107614) = some ⟨12, 2, 0, 819592, 107614, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_107614_819592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107614 ⟨819592, by decide⟩ :=
  accepted_of_selected 12 107614 ⟨819592, by decide⟩ ⟨12, 2, 0, 819592, 107614, 2981, 65536⟩
    (by decide) selected_cut_31918

theorem selected_cut_31919 : selected 9 ⟨819659, by decide⟩
    (prefixPartial 12 107615) = some ⟨12, 2, 0, 819659, 107615, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_107615_819659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107615 ⟨819659, by decide⟩ :=
  accepted_of_selected 12 107615 ⟨819659, by decide⟩ ⟨12, 2, 0, 819659, 107615, 2917, 65536⟩
    (by decide) selected_cut_31919

theorem unmarked_context_11_26903_819660 : frontier 10 ⟨819660, by decide⟩
    (prefixCache 11 26903) (prefixPartial 11 26903) = false := by
  decide +kernel

theorem node_context_11_26903_819660 : EJMOriginalGlobalDAGData.nodes 10 ⟨819660, by decide⟩ =
    .split (coordinate 11) (![⟨819487, by decide⟩,⟨819538, by decide⟩,⟨819592, by decide⟩,⟨819659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26903_819660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26903 ⟨819660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26903
    ⟨819660, by decide⟩ (by decide) (![⟨819487, by decide⟩,⟨819538, by decide⟩,⟨819592, by decide⟩,⟨819659, by decide⟩]) unmarked_context_11_26903_819660 node_context_11_26903_819660
  intro a
  fin_cases a
  · exact context_12_107612_819487
  · exact context_12_107613_819538
  · exact context_12_107614_819592
  · exact context_12_107615_819659

theorem unmarked_context_10_6725_819661 : frontier 11 ⟨819661, by decide⟩
    (prefixCache 10 6725) (prefixPartial 10 6725) = false := by
  decide +kernel

theorem node_context_10_6725_819661 : EJMOriginalGlobalDAGData.nodes 11 ⟨819661, by decide⟩ =
    .split (coordinate 10) (![⟨819210, by decide⟩,⟨451541, by decide⟩,⟨819426, by decide⟩,⟨819660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6725_819661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6725 ⟨819661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6725
    ⟨819661, by decide⟩ (by decide) (![⟨819210, by decide⟩,⟨451541, by decide⟩,⟨819426, by decide⟩,⟨819660, by decide⟩]) unmarked_context_10_6725_819661 node_context_10_6725_819661
  intro a
  fin_cases a
  · exact context_11_26900_819210
  · exact context_11_26901_451541
  · exact context_11_26902_819426
  · exact context_11_26903_819660

theorem selected_cut_31920 : selected 9 ⟨819709, by decide⟩
    (prefixPartial 12 107616) = some ⟨12, 2, 0, 819709, 107616, 701, 65536⟩ := by
  decide +kernel

theorem context_12_107616_819709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107616 ⟨819709, by decide⟩ :=
  accepted_of_selected 12 107616 ⟨819709, by decide⟩ ⟨12, 2, 0, 819709, 107616, 701, 65536⟩
    (by decide) selected_cut_31920

theorem selected_cut_31921 : selected 9 ⟨819752, by decide⟩
    (prefixPartial 12 107617) = some ⟨12, 2, 0, 819752, 107617, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_107617_819752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107617 ⟨819752, by decide⟩ :=
  accepted_of_selected 12 107617 ⟨819752, by decide⟩ ⟨12, 2, 0, 819752, 107617, 2405, 65536⟩
    (by decide) selected_cut_31921

theorem selected_cut_31922 : selected 9 ⟨819797, by decide⟩
    (prefixPartial 12 107618) = some ⟨12, 2, 0, 819797, 107618, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_107618_819797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107618 ⟨819797, by decide⟩ :=
  accepted_of_selected 12 107618 ⟨819797, by decide⟩ ⟨12, 2, 0, 819797, 107618, 2497, 65536⟩
    (by decide) selected_cut_31922

theorem selected_cut_31923 : selected 9 ⟨819848, by decide⟩
    (prefixPartial 12 107619) = some ⟨12, 2, 0, 819848, 107619, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_107619_819848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107619 ⟨819848, by decide⟩ :=
  accepted_of_selected 12 107619 ⟨819848, by decide⟩ ⟨12, 2, 0, 819848, 107619, 2361, 65536⟩
    (by decide) selected_cut_31923

theorem unmarked_context_11_26904_819849 : frontier 10 ⟨819849, by decide⟩
    (prefixCache 11 26904) (prefixPartial 11 26904) = false := by
  decide +kernel

theorem node_context_11_26904_819849 : EJMOriginalGlobalDAGData.nodes 10 ⟨819849, by decide⟩ =
    .split (coordinate 11) (![⟨819709, by decide⟩,⟨819752, by decide⟩,⟨819797, by decide⟩,⟨819848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26904_819849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26904 ⟨819849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26904
    ⟨819849, by decide⟩ (by decide) (![⟨819709, by decide⟩,⟨819752, by decide⟩,⟨819797, by decide⟩,⟨819848, by decide⟩]) unmarked_context_11_26904_819849 node_context_11_26904_819849
  intro a
  fin_cases a
  · exact context_12_107616_819709
  · exact context_12_107617_819752
  · exact context_12_107618_819797
  · exact context_12_107619_819848

theorem selected_cut_31924 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 107620) = some ⟨12, 1, 0, 4595, 107620, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107620_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107620 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 107620 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 107620, 1, 65536⟩
    (by decide) selected_cut_31924

theorem selected_cut_31925 : selected 9 ⟨819891, by decide⟩
    (prefixPartial 12 107621) = some ⟨12, 2, 0, 819891, 107621, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_107621_819891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107621 ⟨819891, by decide⟩ :=
  accepted_of_selected 12 107621 ⟨819891, by decide⟩ ⟨12, 2, 0, 819891, 107621, 2213, 65536⟩
    (by decide) selected_cut_31925

theorem selected_cut_31926 : selected 9 ⟨819937, by decide⟩
    (prefixPartial 12 107622) = some ⟨12, 2, 0, 819937, 107622, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_107622_819937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107622 ⟨819937, by decide⟩ :=
  accepted_of_selected 12 107622 ⟨819937, by decide⟩ ⟨12, 2, 0, 819937, 107622, 1553, 65536⟩
    (by decide) selected_cut_31926

theorem selected_cut_31927 : selected 9 ⟨820000, by decide⟩
    (prefixPartial 12 107623) = some ⟨12, 2, 0, 820000, 107623, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_107623_820000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107623 ⟨820000, by decide⟩ :=
  accepted_of_selected 12 107623 ⟨820000, by decide⟩ ⟨12, 2, 0, 820000, 107623, 2433, 65536⟩
    (by decide) selected_cut_31927

theorem unmarked_context_11_26905_820001 : frontier 10 ⟨820001, by decide⟩
    (prefixCache 11 26905) (prefixPartial 11 26905) = false := by
  decide +kernel

theorem node_context_11_26905_820001 : EJMOriginalGlobalDAGData.nodes 10 ⟨820001, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨819891, by decide⟩,⟨819937, by decide⟩,⟨820000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26905_820001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26905 ⟨820001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26905
    ⟨820001, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨819891, by decide⟩,⟨819937, by decide⟩,⟨820000, by decide⟩]) unmarked_context_11_26905_820001 node_context_11_26905_820001
  intro a
  fin_cases a
  · exact context_12_107620_4595
  · exact context_12_107621_819891
  · exact context_12_107622_819937
  · exact context_12_107623_820000

theorem selected_cut_31928 : selected 10 ⟨820065, by decide⟩
    (prefixPartial 11 26906) = some ⟨11, 2, 0, 820065, 26906, 3353, 262144⟩ := by
  decide +kernel

theorem context_11_26906_820065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26906 ⟨820065, by decide⟩ :=
  accepted_of_selected 11 26906 ⟨820065, by decide⟩ ⟨11, 2, 0, 820065, 26906, 3353, 262144⟩
    (by decide) selected_cut_31928

theorem selected_cut_31929 : selected 10 ⟨820108, by decide⟩
    (prefixPartial 11 26907) = some ⟨11, 2, 0, 820108, 26907, 1377, 262144⟩ := by
  decide +kernel

theorem context_11_26907_820108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26907 ⟨820108, by decide⟩ :=
  accepted_of_selected 11 26907 ⟨820108, by decide⟩ ⟨11, 2, 0, 820108, 26907, 1377, 262144⟩
    (by decide) selected_cut_31929

theorem unmarked_context_10_6726_820109 : frontier 11 ⟨820109, by decide⟩
    (prefixCache 10 6726) (prefixPartial 10 6726) = false := by
  decide +kernel

theorem node_context_10_6726_820109 : EJMOriginalGlobalDAGData.nodes 11 ⟨820109, by decide⟩ =
    .split (coordinate 10) (![⟨819849, by decide⟩,⟨820001, by decide⟩,⟨820065, by decide⟩,⟨820108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6726_820109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6726 ⟨820109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6726
    ⟨820109, by decide⟩ (by decide) (![⟨819849, by decide⟩,⟨820001, by decide⟩,⟨820065, by decide⟩,⟨820108, by decide⟩]) unmarked_context_10_6726_820109 node_context_10_6726_820109
  intro a
  fin_cases a
  · exact context_11_26904_819849
  · exact context_11_26905_820001
  · exact context_11_26906_820065
  · exact context_11_26907_820108

theorem selected_cut_31930 : selected 9 ⟨820208, by decide⟩
    (prefixPartial 12 107632) = some ⟨12, 2, 0, 820208, 107632, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_107632_820208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107632 ⟨820208, by decide⟩ :=
  accepted_of_selected 12 107632 ⟨820208, by decide⟩ ⟨12, 2, 0, 820208, 107632, 2889, 65536⟩
    (by decide) selected_cut_31930

theorem selected_cut_31931 : selected 9 ⟨820246, by decide⟩
    (prefixPartial 12 107633) = some ⟨12, 2, 0, 820246, 107633, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_107633_820246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107633 ⟨820246, by decide⟩ :=
  accepted_of_selected 12 107633 ⟨820246, by decide⟩ ⟨12, 2, 0, 820246, 107633, 1821, 65536⟩
    (by decide) selected_cut_31931

theorem selected_cut_31932 : selected 9 ⟨820283, by decide⟩
    (prefixPartial 12 107634) = some ⟨12, 2, 0, 820283, 107634, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_107634_820283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107634 ⟨820283, by decide⟩ :=
  accepted_of_selected 12 107634 ⟨820283, by decide⟩ ⟨12, 2, 0, 820283, 107634, 1865, 65536⟩
    (by decide) selected_cut_31932

theorem selected_cut_31933 : selected 9 ⟨820317, by decide⟩
    (prefixPartial 12 107635) = some ⟨12, 2, 0, 820317, 107635, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_107635_820317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107635 ⟨820317, by decide⟩ :=
  accepted_of_selected 12 107635 ⟨820317, by decide⟩ ⟨12, 2, 0, 820317, 107635, 1889, 65536⟩
    (by decide) selected_cut_31933

theorem unmarked_context_11_26908_820318 : frontier 10 ⟨820318, by decide⟩
    (prefixCache 11 26908) (prefixPartial 11 26908) = false := by
  decide +kernel

theorem node_context_11_26908_820318 : EJMOriginalGlobalDAGData.nodes 10 ⟨820318, by decide⟩ =
    .split (coordinate 11) (![⟨820208, by decide⟩,⟨820246, by decide⟩,⟨820283, by decide⟩,⟨820317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26908_820318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26908 ⟨820318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26908
    ⟨820318, by decide⟩ (by decide) (![⟨820208, by decide⟩,⟨820246, by decide⟩,⟨820283, by decide⟩,⟨820317, by decide⟩]) unmarked_context_11_26908_820318 node_context_11_26908_820318
  intro a
  fin_cases a
  · exact context_12_107632_820208
  · exact context_12_107633_820246
  · exact context_12_107634_820283
  · exact context_12_107635_820317

theorem selected_cut_31934 : selected 9 ⟨820348, by decide⟩
    (prefixPartial 12 107636) = some ⟨12, 2, 0, 820348, 107636, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_107636_820348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107636 ⟨820348, by decide⟩ :=
  accepted_of_selected 12 107636 ⟨820348, by decide⟩ ⟨12, 2, 0, 820348, 107636, 1657, 65536⟩
    (by decide) selected_cut_31934

theorem selected_cut_31935 : selected 9 ⟨820387, by decide⟩
    (prefixPartial 12 107637) = some ⟨12, 2, 0, 820387, 107637, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_107637_820387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107637 ⟨820387, by decide⟩ :=
  accepted_of_selected 12 107637 ⟨820387, by decide⟩ ⟨12, 2, 0, 820387, 107637, 1501, 65536⟩
    (by decide) selected_cut_31935

theorem selected_cut_31936 : selected 9 ⟨820417, by decide⟩
    (prefixPartial 12 107638) = some ⟨12, 2, 0, 820417, 107638, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_107638_820417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107638 ⟨820417, by decide⟩ :=
  accepted_of_selected 12 107638 ⟨820417, by decide⟩ ⟨12, 2, 0, 820417, 107638, 1653, 65536⟩
    (by decide) selected_cut_31936

theorem selected_cut_31937 : selected 9 ⟨820457, by decide⟩
    (prefixPartial 12 107639) = some ⟨12, 2, 0, 820457, 107639, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_107639_820457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107639 ⟨820457, by decide⟩ :=
  accepted_of_selected 12 107639 ⟨820457, by decide⟩ ⟨12, 2, 0, 820457, 107639, 1717, 65536⟩
    (by decide) selected_cut_31937

theorem unmarked_context_11_26909_820458 : frontier 10 ⟨820458, by decide⟩
    (prefixCache 11 26909) (prefixPartial 11 26909) = false := by
  decide +kernel

theorem node_context_11_26909_820458 : EJMOriginalGlobalDAGData.nodes 10 ⟨820458, by decide⟩ =
    .split (coordinate 11) (![⟨820348, by decide⟩,⟨820387, by decide⟩,⟨820417, by decide⟩,⟨820457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26909_820458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26909 ⟨820458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26909
    ⟨820458, by decide⟩ (by decide) (![⟨820348, by decide⟩,⟨820387, by decide⟩,⟨820417, by decide⟩,⟨820457, by decide⟩]) unmarked_context_11_26909_820458 node_context_11_26909_820458
  intro a
  fin_cases a
  · exact context_12_107636_820348
  · exact context_12_107637_820387
  · exact context_12_107638_820417
  · exact context_12_107639_820457

theorem selected_cut_31938 : selected 9 ⟨820488, by decide⟩
    (prefixPartial 12 107640) = some ⟨12, 2, 0, 820488, 107640, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_107640_820488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107640 ⟨820488, by decide⟩ :=
  accepted_of_selected 12 107640 ⟨820488, by decide⟩ ⟨12, 2, 0, 820488, 107640, 1449, 65536⟩
    (by decide) selected_cut_31938

theorem selected_cut_31939 : selected 9 ⟨820508, by decide⟩
    (prefixPartial 12 107641) = some ⟨12, 2, 0, 820508, 107641, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_107641_820508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107641 ⟨820508, by decide⟩ :=
  accepted_of_selected 12 107641 ⟨820508, by decide⟩ ⟨12, 2, 0, 820508, 107641, 1405, 65536⟩
    (by decide) selected_cut_31939

theorem selected_cut_31940 : selected 9 ⟨820531, by decide⟩
    (prefixPartial 12 107642) = some ⟨12, 2, 0, 820531, 107642, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_107642_820531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107642 ⟨820531, by decide⟩ :=
  accepted_of_selected 12 107642 ⟨820531, by decide⟩ ⟨12, 2, 0, 820531, 107642, 1345, 65536⟩
    (by decide) selected_cut_31940

theorem selected_cut_31941 : selected 9 ⟨820554, by decide⟩
    (prefixPartial 12 107643) = some ⟨12, 2, 0, 820554, 107643, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_107643_820554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107643 ⟨820554, by decide⟩ :=
  accepted_of_selected 12 107643 ⟨820554, by decide⟩ ⟨12, 2, 0, 820554, 107643, 1381, 65536⟩
    (by decide) selected_cut_31941

theorem unmarked_context_11_26910_820555 : frontier 10 ⟨820555, by decide⟩
    (prefixCache 11 26910) (prefixPartial 11 26910) = false := by
  decide +kernel

theorem node_context_11_26910_820555 : EJMOriginalGlobalDAGData.nodes 10 ⟨820555, by decide⟩ =
    .split (coordinate 11) (![⟨820488, by decide⟩,⟨820508, by decide⟩,⟨820531, by decide⟩,⟨820554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26910_820555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26910 ⟨820555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26910
    ⟨820555, by decide⟩ (by decide) (![⟨820488, by decide⟩,⟨820508, by decide⟩,⟨820531, by decide⟩,⟨820554, by decide⟩]) unmarked_context_11_26910_820555 node_context_11_26910_820555
  intro a
  fin_cases a
  · exact context_12_107640_820488
  · exact context_12_107641_820508
  · exact context_12_107642_820531
  · exact context_12_107643_820554

theorem selected_cut_31942 : selected 9 ⟨820583, by decide⟩
    (prefixPartial 12 107644) = some ⟨12, 2, 0, 820583, 107644, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_107644_820583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107644 ⟨820583, by decide⟩ :=
  accepted_of_selected 12 107644 ⟨820583, by decide⟩ ⟨12, 2, 0, 820583, 107644, 1257, 65536⟩
    (by decide) selected_cut_31942

theorem selected_cut_31943 : selected 9 ⟨820611, by decide⟩
    (prefixPartial 12 107645) = some ⟨12, 2, 0, 820611, 107645, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_107645_820611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107645 ⟨820611, by decide⟩ :=
  accepted_of_selected 12 107645 ⟨820611, by decide⟩ ⟨12, 2, 0, 820611, 107645, 1153, 65536⟩
    (by decide) selected_cut_31943

theorem selected_cut_31944 : selected 9 ⟨820632, by decide⟩
    (prefixPartial 12 107646) = some ⟨12, 2, 0, 820632, 107646, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_107646_820632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107646 ⟨820632, by decide⟩ :=
  accepted_of_selected 12 107646 ⟨820632, by decide⟩ ⟨12, 2, 0, 820632, 107646, 1197, 65536⟩
    (by decide) selected_cut_31944

theorem selected_cut_31945 : selected 9 ⟨820656, by decide⟩
    (prefixPartial 12 107647) = some ⟨12, 2, 0, 820656, 107647, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_107647_820656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107647 ⟨820656, by decide⟩ :=
  accepted_of_selected 12 107647 ⟨820656, by decide⟩ ⟨12, 2, 0, 820656, 107647, 1205, 65536⟩
    (by decide) selected_cut_31945

theorem unmarked_context_11_26911_820657 : frontier 10 ⟨820657, by decide⟩
    (prefixCache 11 26911) (prefixPartial 11 26911) = false := by
  decide +kernel

theorem node_context_11_26911_820657 : EJMOriginalGlobalDAGData.nodes 10 ⟨820657, by decide⟩ =
    .split (coordinate 11) (![⟨820583, by decide⟩,⟨820611, by decide⟩,⟨820632, by decide⟩,⟨820656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26911_820657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26911 ⟨820657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26911
    ⟨820657, by decide⟩ (by decide) (![⟨820583, by decide⟩,⟨820611, by decide⟩,⟨820632, by decide⟩,⟨820656, by decide⟩]) unmarked_context_11_26911_820657 node_context_11_26911_820657
  intro a
  fin_cases a
  · exact context_12_107644_820583
  · exact context_12_107645_820611
  · exact context_12_107646_820632
  · exact context_12_107647_820656

theorem unmarked_context_10_6727_820658 : frontier 11 ⟨820658, by decide⟩
    (prefixCache 10 6727) (prefixPartial 10 6727) = false := by
  decide +kernel

theorem node_context_10_6727_820658 : EJMOriginalGlobalDAGData.nodes 11 ⟨820658, by decide⟩ =
    .split (coordinate 10) (![⟨820318, by decide⟩,⟨820458, by decide⟩,⟨820555, by decide⟩,⟨820657, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6727_820658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6727 ⟨820658, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6727
    ⟨820658, by decide⟩ (by decide) (![⟨820318, by decide⟩,⟨820458, by decide⟩,⟨820555, by decide⟩,⟨820657, by decide⟩]) unmarked_context_10_6727_820658 node_context_10_6727_820658
  intro a
  fin_cases a
  · exact context_11_26908_820318
  · exact context_11_26909_820458
  · exact context_11_26910_820555
  · exact context_11_26911_820657

theorem unmarked_context_9_1681_820659 : frontier 12 ⟨820659, by decide⟩
    (prefixCache 9 1681) (prefixPartial 9 1681) = false := by
  decide +kernel

theorem node_context_9_1681_820659 : EJMOriginalGlobalDAGData.nodes 12 ⟨820659, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨819661, by decide⟩,⟨820109, by decide⟩,⟨820658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1681_820659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1681 ⟨820659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1681
    ⟨820659, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨819661, by decide⟩,⟨820109, by decide⟩,⟨820658, by decide⟩]) unmarked_context_9_1681_820659 node_context_9_1681_820659
  intro a
  fin_cases a
  · exact context_10_6724_145424
  · exact context_10_6725_819661
  · exact context_10_6726_820109
  · exact context_10_6727_820658

theorem selected_cut_31946 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 6728) = some ⟨10, 1, 0, 145424, 6728, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6728_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6728 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 6728 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 6728, 1, 1048576⟩
    (by decide) selected_cut_31946

theorem selected_cut_31947 : selected 10 ⟨820697, by decide⟩
    (prefixPartial 11 26916) = some ⟨11, 2, 0, 820697, 26916, 1725, 262144⟩ := by
  decide +kernel

theorem context_11_26916_820697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26916 ⟨820697, by decide⟩ :=
  accepted_of_selected 11 26916 ⟨820697, by decide⟩ ⟨11, 2, 0, 820697, 26916, 1725, 262144⟩
    (by decide) selected_cut_31947

theorem selected_cut_31948 : selected 10 ⟨820732, by decide⟩
    (prefixPartial 11 26917) = some ⟨11, 2, 0, 820732, 26917, 1073, 262144⟩ := by
  decide +kernel

theorem context_11_26917_820732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26917 ⟨820732, by decide⟩ :=
  accepted_of_selected 11 26917 ⟨820732, by decide⟩ ⟨11, 2, 0, 820732, 26917, 1073, 262144⟩
    (by decide) selected_cut_31948

theorem selected_cut_31949 : selected 10 ⟨820755, by decide⟩
    (prefixPartial 11 26918) = some ⟨11, 2, 0, 820755, 26918, 1229, 262144⟩ := by
  decide +kernel

theorem context_11_26918_820755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26918 ⟨820755, by decide⟩ :=
  accepted_of_selected 11 26918 ⟨820755, by decide⟩ ⟨11, 2, 0, 820755, 26918, 1229, 262144⟩
    (by decide) selected_cut_31949

theorem selected_cut_31950 : selected 10 ⟨820764, by decide⟩
    (prefixPartial 11 26919) = some ⟨11, 2, 0, 820764, 26919, 473, 262144⟩ := by
  decide +kernel

theorem context_11_26919_820764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26919 ⟨820764, by decide⟩ :=
  accepted_of_selected 11 26919 ⟨820764, by decide⟩ ⟨11, 2, 0, 820764, 26919, 473, 262144⟩
    (by decide) selected_cut_31950

theorem unmarked_context_10_6729_820765 : frontier 11 ⟨820765, by decide⟩
    (prefixCache 10 6729) (prefixPartial 10 6729) = false := by
  decide +kernel

theorem node_context_10_6729_820765 : EJMOriginalGlobalDAGData.nodes 11 ⟨820765, by decide⟩ =
    .split (coordinate 10) (![⟨820697, by decide⟩,⟨820732, by decide⟩,⟨820755, by decide⟩,⟨820764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6729_820765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6729 ⟨820765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6729
    ⟨820765, by decide⟩ (by decide) (![⟨820697, by decide⟩,⟨820732, by decide⟩,⟨820755, by decide⟩,⟨820764, by decide⟩]) unmarked_context_10_6729_820765 node_context_10_6729_820765
  intro a
  fin_cases a
  · exact context_11_26916_820697
  · exact context_11_26917_820732
  · exact context_11_26918_820755
  · exact context_11_26919_820764

theorem selected_cut_31951 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 6730) = some ⟨10, 1, 0, 145424, 6730, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6730_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6730 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 6730 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 6730, 1, 1048576⟩
    (by decide) selected_cut_31951

theorem selected_cut_31952 : selected 10 ⟨820786, by decide⟩
    (prefixPartial 11 26924) = some ⟨11, 2, 0, 820786, 26924, 1189, 262144⟩ := by
  decide +kernel

theorem context_11_26924_820786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26924 ⟨820786, by decide⟩ :=
  accepted_of_selected 11 26924 ⟨820786, by decide⟩ ⟨11, 2, 0, 820786, 26924, 1189, 262144⟩
    (by decide) selected_cut_31952

theorem selected_cut_31953 : selected 10 ⟨820837, by decide⟩
    (prefixPartial 11 26925) = some ⟨11, 2, 0, 820837, 26925, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_26925_820837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26925 ⟨820837, by decide⟩ :=
  accepted_of_selected 11 26925 ⟨820837, by decide⟩ ⟨11, 2, 0, 820837, 26925, 2061, 262144⟩
    (by decide) selected_cut_31953

theorem selected_cut_31954 : selected 10 ⟨820874, by decide⟩
    (prefixPartial 11 26926) = some ⟨11, 2, 0, 820874, 26926, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_26926_820874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26926 ⟨820874, by decide⟩ :=
  accepted_of_selected 11 26926 ⟨820874, by decide⟩ ⟨11, 2, 0, 820874, 26926, 1093, 262144⟩
    (by decide) selected_cut_31954

theorem selected_cut_31955 : selected 10 ⟨820892, by decide⟩
    (prefixPartial 11 26927) = some ⟨11, 2, 0, 820892, 26927, 765, 262144⟩ := by
  decide +kernel

theorem context_11_26927_820892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26927 ⟨820892, by decide⟩ :=
  accepted_of_selected 11 26927 ⟨820892, by decide⟩ ⟨11, 2, 0, 820892, 26927, 765, 262144⟩
    (by decide) selected_cut_31955

theorem unmarked_context_10_6731_820893 : frontier 11 ⟨820893, by decide⟩
    (prefixCache 10 6731) (prefixPartial 10 6731) = false := by
  decide +kernel

theorem node_context_10_6731_820893 : EJMOriginalGlobalDAGData.nodes 11 ⟨820893, by decide⟩ =
    .split (coordinate 10) (![⟨820786, by decide⟩,⟨820837, by decide⟩,⟨820874, by decide⟩,⟨820892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6731_820893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6731 ⟨820893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6731
    ⟨820893, by decide⟩ (by decide) (![⟨820786, by decide⟩,⟨820837, by decide⟩,⟨820874, by decide⟩,⟨820892, by decide⟩]) unmarked_context_10_6731_820893 node_context_10_6731_820893
  intro a
  fin_cases a
  · exact context_11_26924_820786
  · exact context_11_26925_820837
  · exact context_11_26926_820874
  · exact context_11_26927_820892

theorem unmarked_context_9_1682_820894 : frontier 12 ⟨820894, by decide⟩
    (prefixCache 9 1682) (prefixPartial 9 1682) = false := by
  decide +kernel

theorem node_context_9_1682_820894 : EJMOriginalGlobalDAGData.nodes 12 ⟨820894, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨820765, by decide⟩,⟨145424, by decide⟩,⟨820893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1682_820894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1682 ⟨820894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1682
    ⟨820894, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨820765, by decide⟩,⟨145424, by decide⟩,⟨820893, by decide⟩]) unmarked_context_9_1682_820894 node_context_9_1682_820894
  intro a
  fin_cases a
  · exact context_10_6728_145424
  · exact context_10_6729_820765
  · exact context_10_6730_145424
  · exact context_10_6731_820893

theorem selected_cut_31956 : selected 12 ⟨820920, by decide⟩
    (prefixPartial 9 1683) = some ⟨9, 2, 0, 820920, 1683, 765, 4194304⟩ := by
  decide +kernel

theorem context_9_1683_820920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1683 ⟨820920, by decide⟩ :=
  accepted_of_selected 9 1683 ⟨820920, by decide⟩ ⟨9, 2, 0, 820920, 1683, 765, 4194304⟩
    (by decide) selected_cut_31956

theorem unmarked_context_8_420_820921 : frontier 13 ⟨820921, by decide⟩
    (prefixCache 8 420) (prefixPartial 8 420) = false := by
  decide +kernel

theorem node_context_8_420_820921 : EJMOriginalGlobalDAGData.nodes 13 ⟨820921, by decide⟩ =
    .split (coordinate 8) (![⟨819038, by decide⟩,⟨820659, by decide⟩,⟨820894, by decide⟩,⟨820920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_420_820921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 420 ⟨820921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 420
    ⟨820921, by decide⟩ (by decide) (![⟨819038, by decide⟩,⟨820659, by decide⟩,⟨820894, by decide⟩,⟨820920, by decide⟩]) unmarked_context_8_420_820921 node_context_8_420_820921
  intro a
  fin_cases a
  · exact context_9_1680_819038
  · exact context_9_1681_820659
  · exact context_9_1682_820894
  · exact context_9_1683_820920

theorem selected_cut_31957 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26944) = some ⟨11, 1, 0, 434745, 26944, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26944_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26944 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26944 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26944, 1, 262144⟩
    (by decide) selected_cut_31957

theorem selected_cut_31958 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 26945) = some ⟨11, 1, 0, 167448, 26945, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26945_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26945 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 26945 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 26945, 1, 262144⟩
    (by decide) selected_cut_31958

theorem selected_cut_31959 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 107784) = some ⟨12, 1, 0, 448748, 107784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107784_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107784 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 107784 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 107784, 1, 65536⟩
    (by decide) selected_cut_31959

theorem selected_cut_31960 : selected 8 ⟨821019, by decide⟩
    (prefixPartial 13 431140) = some ⟨13, 2, 0, 821019, 431140, 3625, 16384⟩ := by
  decide +kernel

theorem context_13_431140_821019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431140 ⟨821019, by decide⟩ :=
  accepted_of_selected 13 431140 ⟨821019, by decide⟩ ⟨13, 2, 0, 821019, 431140, 3625, 16384⟩
    (by decide) selected_cut_31960

theorem selected_cut_31961 : selected 8 ⟨821107, by decide⟩
    (prefixPartial 13 431141) = some ⟨13, 2, 0, 821107, 431141, 3129, 16384⟩ := by
  decide +kernel

theorem context_13_431141_821107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431141 ⟨821107, by decide⟩ :=
  accepted_of_selected 13 431141 ⟨821107, by decide⟩ ⟨13, 2, 0, 821107, 431141, 3129, 16384⟩
    (by decide) selected_cut_31961

theorem selected_cut_31962 : selected 8 ⟨821195, by decide⟩
    (prefixPartial 13 431142) = some ⟨13, 2, 0, 821195, 431142, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_431142_821195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431142 ⟨821195, by decide⟩ :=
  accepted_of_selected 13 431142 ⟨821195, by decide⟩ ⟨13, 2, 0, 821195, 431142, 2069, 16384⟩
    (by decide) selected_cut_31962

theorem selected_cut_31963 : selected 8 ⟨821228, by decide⟩
    (prefixPartial 13 431143) = some ⟨13, 2, 0, 821228, 431143, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_431143_821228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431143 ⟨821228, by decide⟩ :=
  accepted_of_selected 13 431143 ⟨821228, by decide⟩ ⟨13, 2, 0, 821228, 431143, 1177, 16384⟩
    (by decide) selected_cut_31963

theorem unmarked_context_12_107785_821229 : frontier 9 ⟨821229, by decide⟩
    (prefixCache 12 107785) (prefixPartial 12 107785) = false := by
  decide +kernel

theorem node_context_12_107785_821229 : EJMOriginalGlobalDAGData.nodes 9 ⟨821229, by decide⟩ =
    .split (coordinate 12) (![⟨821019, by decide⟩,⟨821107, by decide⟩,⟨821195, by decide⟩,⟨821228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107785_821229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107785 ⟨821229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107785
    ⟨821229, by decide⟩ (by decide) (![⟨821019, by decide⟩,⟨821107, by decide⟩,⟨821195, by decide⟩,⟨821228, by decide⟩]) unmarked_context_12_107785_821229 node_context_12_107785_821229
  intro a
  fin_cases a
  · exact context_13_431140_821019
  · exact context_13_431141_821107
  · exact context_13_431142_821195
  · exact context_13_431143_821228

theorem selected_cut_31964 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 107786) = some ⟨12, 1, 0, 763842, 107786, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107786_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107786 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 107786 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 107786, 1, 65536⟩
    (by decide) selected_cut_31964

theorem selected_cut_31965 : selected 7 ⟨821245, by decide⟩
    (prefixPartial 14 1724592) = some ⟨14, 2, 0, 821245, 1724592, 373, 4096⟩ := by
  decide +kernel

theorem context_14_1724592_821245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1724592 ⟨821245, by decide⟩ :=
  accepted_of_selected 14 1724592 ⟨821245, by decide⟩ ⟨14, 2, 0, 821245, 1724592, 373, 4096⟩
    (by decide) selected_cut_31965

theorem selected_cut_31966 : selected 7 ⟨821261, by decide⟩
    (prefixPartial 14 1724593) = some ⟨14, 2, 0, 821261, 1724593, 873, 4096⟩ := by
  decide +kernel

theorem context_14_1724593_821261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1724593 ⟨821261, by decide⟩ :=
  accepted_of_selected 14 1724593 ⟨821261, by decide⟩ ⟨14, 2, 0, 821261, 1724593, 873, 4096⟩
    (by decide) selected_cut_31966

theorem selected_cut_31967 : selected 7 ⟨821299, by decide⟩
    (prefixPartial 14 1724594) = some ⟨14, 2, 0, 821299, 1724594, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_1724594_821299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1724594 ⟨821299, by decide⟩ :=
  accepted_of_selected 14 1724594 ⟨821299, by decide⟩ ⟨14, 2, 0, 821299, 1724594, 1433, 4096⟩
    (by decide) selected_cut_31967

theorem selected_cut_31968 : selected 7 ⟨821327, by decide⟩
    (prefixPartial 14 1724595) = some ⟨14, 2, 0, 821327, 1724595, 1481, 4096⟩ := by
  decide +kernel

theorem context_14_1724595_821327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1724595 ⟨821327, by decide⟩ :=
  accepted_of_selected 14 1724595 ⟨821327, by decide⟩ ⟨14, 2, 0, 821327, 1724595, 1481, 4096⟩
    (by decide) selected_cut_31968

theorem unmarked_context_13_431148_821328 : frontier 8 ⟨821328, by decide⟩
    (prefixCache 13 431148) (prefixPartial 13 431148) = false := by
  decide +kernel

theorem node_context_13_431148_821328 : EJMOriginalGlobalDAGData.nodes 8 ⟨821328, by decide⟩ =
    .split (coordinate 13) (![⟨821245, by decide⟩,⟨821261, by decide⟩,⟨821299, by decide⟩,⟨821327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_431148_821328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431148 ⟨821328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 431148
    ⟨821328, by decide⟩ (by decide) (![⟨821245, by decide⟩,⟨821261, by decide⟩,⟨821299, by decide⟩,⟨821327, by decide⟩]) unmarked_context_13_431148_821328 node_context_13_431148_821328
  intro a
  fin_cases a
  · exact context_14_1724592_821245
  · exact context_14_1724593_821261
  · exact context_14_1724594_821299
  · exact context_14_1724595_821327

theorem selected_cut_31969 : selected 8 ⟨821417, by decide⟩
    (prefixPartial 13 431149) = some ⟨13, 2, 0, 821417, 431149, 3773, 16384⟩ := by
  decide +kernel

theorem context_13_431149_821417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431149 ⟨821417, by decide⟩ :=
  accepted_of_selected 13 431149 ⟨821417, by decide⟩ ⟨13, 2, 0, 821417, 431149, 3773, 16384⟩
    (by decide) selected_cut_31969

theorem selected_cut_31970 : selected 8 ⟨821520, by decide⟩
    (prefixPartial 13 431150) = some ⟨13, 2, 0, 821520, 431150, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_431150_821520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431150 ⟨821520, by decide⟩ :=
  accepted_of_selected 13 431150 ⟨821520, by decide⟩ ⟨13, 2, 0, 821520, 431150, 2497, 16384⟩
    (by decide) selected_cut_31970

theorem selected_cut_31971 : selected 8 ⟨821555, by decide⟩
    (prefixPartial 13 431151) = some ⟨13, 2, 0, 821555, 431151, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_431151_821555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431151 ⟨821555, by decide⟩ :=
  accepted_of_selected 13 431151 ⟨821555, by decide⟩ ⟨13, 2, 0, 821555, 431151, 1217, 16384⟩
    (by decide) selected_cut_31971

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
