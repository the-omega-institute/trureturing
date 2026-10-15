/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover457
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43971 : selected 10 ⟨1206494, by decide⟩
    (prefixPartial 11 88233) = some ⟨11, 2, 0, 1206494, 88233, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_88233_1206494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88233 ⟨1206494, by decide⟩ :=
  accepted_of_selected 11 88233 ⟨1206494, by decide⟩ ⟨11, 2, 0, 1206494, 88233, 2085, 262144⟩
    (by decide) selected_cut_43971

theorem selected_cut_43972 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 88234) = some ⟨11, 1, 0, 1109453, 88234, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88234_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88234 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 88234 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 88234, 1, 262144⟩
    (by decide) selected_cut_43972

theorem selected_cut_43973 : selected 10 ⟨1206547, by decide⟩
    (prefixPartial 11 88235) = some ⟨11, 2, 0, 1206547, 88235, 2881, 262144⟩ := by
  decide +kernel

theorem context_11_88235_1206547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88235 ⟨1206547, by decide⟩ :=
  accepted_of_selected 11 88235 ⟨1206547, by decide⟩ ⟨11, 2, 0, 1206547, 88235, 2881, 262144⟩
    (by decide) selected_cut_43973

theorem unmarked_context_10_22058_1206548 : frontier 11 ⟨1206548, by decide⟩
    (prefixCache 10 22058) (prefixPartial 10 22058) = false := by
  decide +kernel

theorem node_context_10_22058_1206548 : EJMOriginalGlobalDAGData.nodes 11 ⟨1206548, by decide⟩ =
    .split (coordinate 10) (![⟨1206453, by decide⟩,⟨1206494, by decide⟩,⟨1109453, by decide⟩,⟨1206547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22058_1206548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22058 ⟨1206548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22058
    ⟨1206548, by decide⟩ (by decide) (![⟨1206453, by decide⟩,⟨1206494, by decide⟩,⟨1109453, by decide⟩,⟨1206547, by decide⟩]) unmarked_context_10_22058_1206548 node_context_10_22058_1206548
  intro a
  fin_cases a
  · exact context_11_88232_1206453
  · exact context_11_88233_1206494
  · exact context_11_88234_1109453
  · exact context_11_88235_1206547

theorem selected_cut_43974 : selected 10 ⟨1206584, by decide⟩
    (prefixPartial 11 88236) = some ⟨11, 2, 0, 1206584, 88236, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_88236_1206584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88236 ⟨1206584, by decide⟩ :=
  accepted_of_selected 11 88236 ⟨1206584, by decide⟩ ⟨11, 2, 0, 1206584, 88236, 2565, 262144⟩
    (by decide) selected_cut_43974

theorem selected_cut_43975 : selected 10 ⟨1206609, by decide⟩
    (prefixPartial 11 88237) = some ⟨11, 2, 0, 1206609, 88237, 1445, 262144⟩ := by
  decide +kernel

theorem context_11_88237_1206609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88237 ⟨1206609, by decide⟩ :=
  accepted_of_selected 11 88237 ⟨1206609, by decide⟩ ⟨11, 2, 0, 1206609, 88237, 1445, 262144⟩
    (by decide) selected_cut_43975

theorem selected_cut_43976 : selected 10 ⟨1206639, by decide⟩
    (prefixPartial 11 88238) = some ⟨11, 2, 0, 1206639, 88238, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_88238_1206639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88238 ⟨1206639, by decide⟩ :=
  accepted_of_selected 11 88238 ⟨1206639, by decide⟩ ⟨11, 2, 0, 1206639, 88238, 1749, 262144⟩
    (by decide) selected_cut_43976

theorem selected_cut_43977 : selected 10 ⟨1206666, by decide⟩
    (prefixPartial 11 88239) = some ⟨11, 2, 0, 1206666, 88239, 1557, 262144⟩ := by
  decide +kernel

theorem context_11_88239_1206666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88239 ⟨1206666, by decide⟩ :=
  accepted_of_selected 11 88239 ⟨1206666, by decide⟩ ⟨11, 2, 0, 1206666, 88239, 1557, 262144⟩
    (by decide) selected_cut_43977

theorem unmarked_context_10_22059_1206667 : frontier 11 ⟨1206667, by decide⟩
    (prefixCache 10 22059) (prefixPartial 10 22059) = false := by
  decide +kernel

theorem node_context_10_22059_1206667 : EJMOriginalGlobalDAGData.nodes 11 ⟨1206667, by decide⟩ =
    .split (coordinate 10) (![⟨1206584, by decide⟩,⟨1206609, by decide⟩,⟨1206639, by decide⟩,⟨1206666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22059_1206667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22059 ⟨1206667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22059
    ⟨1206667, by decide⟩ (by decide) (![⟨1206584, by decide⟩,⟨1206609, by decide⟩,⟨1206639, by decide⟩,⟨1206666, by decide⟩]) unmarked_context_10_22059_1206667 node_context_10_22059_1206667
  intro a
  fin_cases a
  · exact context_11_88236_1206584
  · exact context_11_88237_1206609
  · exact context_11_88238_1206639
  · exact context_11_88239_1206666

theorem unmarked_context_9_5514_1206668 : frontier 12 ⟨1206668, by decide⟩
    (prefixCache 9 5514) (prefixPartial 9 5514) = false := by
  decide +kernel

theorem node_context_9_5514_1206668 : EJMOriginalGlobalDAGData.nodes 12 ⟨1206668, by decide⟩ =
    .split (coordinate 9) (![⟨1206153, by decide⟩,⟨1206422, by decide⟩,⟨1206548, by decide⟩,⟨1206667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5514_1206668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5514 ⟨1206668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5514
    ⟨1206668, by decide⟩ (by decide) (![⟨1206153, by decide⟩,⟨1206422, by decide⟩,⟨1206548, by decide⟩,⟨1206667, by decide⟩]) unmarked_context_9_5514_1206668 node_context_9_5514_1206668
  intro a
  fin_cases a
  · exact context_10_22056_1206153
  · exact context_10_22057_1206422
  · exact context_10_22058_1206548
  · exact context_10_22059_1206667

theorem selected_cut_43978 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88240) = some ⟨11, 1, 0, 907917, 88240, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88240_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88240 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88240 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88240, 1, 262144⟩
    (by decide) selected_cut_43978

theorem selected_cut_43979 : selected 10 ⟨1206698, by decide⟩
    (prefixPartial 11 88241) = some ⟨11, 2, 0, 1206698, 88241, 1841, 262144⟩ := by
  decide +kernel

theorem context_11_88241_1206698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88241 ⟨1206698, by decide⟩ :=
  accepted_of_selected 11 88241 ⟨1206698, by decide⟩ ⟨11, 2, 0, 1206698, 88241, 1841, 262144⟩
    (by decide) selected_cut_43979

theorem selected_cut_43980 : selected 10 ⟨1206715, by decide⟩
    (prefixPartial 11 88242) = some ⟨11, 2, 0, 1206715, 88242, 1269, 262144⟩ := by
  decide +kernel

theorem context_11_88242_1206715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88242 ⟨1206715, by decide⟩ :=
  accepted_of_selected 11 88242 ⟨1206715, by decide⟩ ⟨11, 2, 0, 1206715, 88242, 1269, 262144⟩
    (by decide) selected_cut_43980

theorem selected_cut_43981 : selected 10 ⟨1206732, by decide⟩
    (prefixPartial 11 88243) = some ⟨11, 2, 0, 1206732, 88243, 1181, 262144⟩ := by
  decide +kernel

theorem context_11_88243_1206732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88243 ⟨1206732, by decide⟩ :=
  accepted_of_selected 11 88243 ⟨1206732, by decide⟩ ⟨11, 2, 0, 1206732, 88243, 1181, 262144⟩
    (by decide) selected_cut_43981

theorem unmarked_context_10_22060_1206733 : frontier 11 ⟨1206733, by decide⟩
    (prefixCache 10 22060) (prefixPartial 10 22060) = false := by
  decide +kernel

theorem node_context_10_22060_1206733 : EJMOriginalGlobalDAGData.nodes 11 ⟨1206733, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1206698, by decide⟩,⟨1206715, by decide⟩,⟨1206732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22060_1206733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22060 ⟨1206733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22060
    ⟨1206733, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1206698, by decide⟩,⟨1206715, by decide⟩,⟨1206732, by decide⟩]) unmarked_context_10_22060_1206733 node_context_10_22060_1206733
  intro a
  fin_cases a
  · exact context_11_88240_907917
  · exact context_11_88241_1206698
  · exact context_11_88242_1206715
  · exact context_11_88243_1206732

theorem selected_cut_43982 : selected 11 ⟨1206795, by decide⟩
    (prefixPartial 10 22061) = some ⟨10, 2, 0, 1206795, 22061, 3725, 1048576⟩ := by
  decide +kernel

theorem context_10_22061_1206795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22061 ⟨1206795, by decide⟩ :=
  accepted_of_selected 10 22061 ⟨1206795, by decide⟩ ⟨10, 2, 0, 1206795, 22061, 3725, 1048576⟩
    (by decide) selected_cut_43982

theorem selected_cut_43983 : selected 11 ⟨1206836, by decide⟩
    (prefixPartial 10 22062) = some ⟨10, 2, 0, 1206836, 22062, 1913, 1048576⟩ := by
  decide +kernel

theorem context_10_22062_1206836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22062 ⟨1206836, by decide⟩ :=
  accepted_of_selected 10 22062 ⟨1206836, by decide⟩ ⟨10, 2, 0, 1206836, 22062, 1913, 1048576⟩
    (by decide) selected_cut_43983

theorem selected_cut_43984 : selected 11 ⟨1206850, by decide⟩
    (prefixPartial 10 22063) = some ⟨10, 2, 0, 1206850, 22063, 401, 1048576⟩ := by
  decide +kernel

theorem context_10_22063_1206850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22063 ⟨1206850, by decide⟩ :=
  accepted_of_selected 10 22063 ⟨1206850, by decide⟩ ⟨10, 2, 0, 1206850, 22063, 401, 1048576⟩
    (by decide) selected_cut_43984

theorem unmarked_context_9_5515_1206851 : frontier 12 ⟨1206851, by decide⟩
    (prefixCache 9 5515) (prefixPartial 9 5515) = false := by
  decide +kernel

theorem node_context_9_5515_1206851 : EJMOriginalGlobalDAGData.nodes 12 ⟨1206851, by decide⟩ =
    .split (coordinate 9) (![⟨1206733, by decide⟩,⟨1206795, by decide⟩,⟨1206836, by decide⟩,⟨1206850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5515_1206851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5515 ⟨1206851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5515
    ⟨1206851, by decide⟩ (by decide) (![⟨1206733, by decide⟩,⟨1206795, by decide⟩,⟨1206836, by decide⟩,⟨1206850, by decide⟩]) unmarked_context_9_5515_1206851 node_context_9_5515_1206851
  intro a
  fin_cases a
  · exact context_10_22060_1206733
  · exact context_10_22061_1206795
  · exact context_10_22062_1206836
  · exact context_10_22063_1206850

theorem unmarked_context_8_1378_1206852 : frontier 13 ⟨1206852, by decide⟩
    (prefixCache 8 1378) (prefixPartial 8 1378) = false := by
  decide +kernel

theorem node_context_8_1378_1206852 : EJMOriginalGlobalDAGData.nodes 13 ⟨1206852, by decide⟩ =
    .split (coordinate 8) (![⟨1205297, by decide⟩,⟨1205939, by decide⟩,⟨1206668, by decide⟩,⟨1206851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1378_1206852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1378 ⟨1206852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1378
    ⟨1206852, by decide⟩ (by decide) (![⟨1205297, by decide⟩,⟨1205939, by decide⟩,⟨1206668, by decide⟩,⟨1206851, by decide⟩]) unmarked_context_8_1378_1206852 node_context_8_1378_1206852
  intro a
  fin_cases a
  · exact context_9_5512_1205297
  · exact context_9_5513_1205939
  · exact context_9_5514_1206668
  · exact context_9_5515_1206851

theorem selected_cut_43985 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88256) = some ⟨11, 1, 0, 434745, 88256, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88256_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88256 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88256 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88256, 1, 262144⟩
    (by decide) selected_cut_43985

theorem selected_cut_43986 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 88257) = some ⟨11, 1, 0, 167448, 88257, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88257_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88257 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 88257 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 88257, 1, 262144⟩
    (by decide) selected_cut_43986

theorem selected_cut_43987 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 353032) = some ⟨12, 1, 0, 448748, 353032, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353032_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353032 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 353032 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 353032, 1, 65536⟩
    (by decide) selected_cut_43987

theorem selected_cut_43988 : selected 9 ⟨1206925, by decide⟩
    (prefixPartial 12 353033) = some ⟨12, 2, 0, 1206925, 353033, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_353033_1206925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353033 ⟨1206925, by decide⟩ :=
  accepted_of_selected 12 353033 ⟨1206925, by decide⟩ ⟨12, 2, 0, 1206925, 353033, 3101, 65536⟩
    (by decide) selected_cut_43988

theorem selected_cut_43989 : selected 9 ⟨1206980, by decide⟩
    (prefixPartial 12 353034) = some ⟨12, 2, 0, 1206980, 353034, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_353034_1206980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353034 ⟨1206980, by decide⟩ :=
  accepted_of_selected 12 353034 ⟨1206980, by decide⟩ ⟨12, 2, 0, 1206980, 353034, 2925, 65536⟩
    (by decide) selected_cut_43989

theorem selected_cut_43990 : selected 9 ⟨1207049, by decide⟩
    (prefixPartial 12 353035) = some ⟨12, 2, 0, 1207049, 353035, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_353035_1207049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353035 ⟨1207049, by decide⟩ :=
  accepted_of_selected 12 353035 ⟨1207049, by decide⟩ ⟨12, 2, 0, 1207049, 353035, 3449, 65536⟩
    (by decide) selected_cut_43990

theorem unmarked_context_11_88258_1207050 : frontier 10 ⟨1207050, by decide⟩
    (prefixCache 11 88258) (prefixPartial 11 88258) = false := by
  decide +kernel

theorem node_context_11_88258_1207050 : EJMOriginalGlobalDAGData.nodes 10 ⟨1207050, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1206925, by decide⟩,⟨1206980, by decide⟩,⟨1207049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88258_1207050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88258 ⟨1207050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88258
    ⟨1207050, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1206925, by decide⟩,⟨1206980, by decide⟩,⟨1207049, by decide⟩]) unmarked_context_11_88258_1207050 node_context_11_88258_1207050
  intro a
  fin_cases a
  · exact context_12_353032_448748
  · exact context_12_353033_1206925
  · exact context_12_353034_1206980
  · exact context_12_353035_1207049

theorem selected_cut_43991 : selected 10 ⟨1207100, by decide⟩
    (prefixPartial 11 88259) = some ⟨11, 2, 0, 1207100, 88259, 2681, 262144⟩ := by
  decide +kernel

theorem context_11_88259_1207100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88259 ⟨1207100, by decide⟩ :=
  accepted_of_selected 11 88259 ⟨1207100, by decide⟩ ⟨11, 2, 0, 1207100, 88259, 2681, 262144⟩
    (by decide) selected_cut_43991

theorem unmarked_context_10_22064_1207101 : frontier 11 ⟨1207101, by decide⟩
    (prefixCache 10 22064) (prefixPartial 10 22064) = false := by
  decide +kernel

theorem node_context_10_22064_1207101 : EJMOriginalGlobalDAGData.nodes 11 ⟨1207101, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1207050, by decide⟩,⟨1207100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22064_1207101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22064 ⟨1207101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22064
    ⟨1207101, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1207050, by decide⟩,⟨1207100, by decide⟩]) unmarked_context_10_22064_1207101 node_context_10_22064_1207101
  intro a
  fin_cases a
  · exact context_11_88256_434745
  · exact context_11_88257_167448
  · exact context_11_88258_1207050
  · exact context_11_88259_1207100

theorem selected_cut_43992 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 353040) = some ⟨12, 1, 0, 435160, 353040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353040_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353040 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 353040 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 353040, 1, 65536⟩
    (by decide) selected_cut_43992

theorem selected_cut_43993 : selected 9 ⟨1207146, by decide⟩
    (prefixPartial 12 353041) = some ⟨12, 2, 0, 1207146, 353041, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_353041_1207146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353041 ⟨1207146, by decide⟩ :=
  accepted_of_selected 12 353041 ⟨1207146, by decide⟩ ⟨12, 2, 0, 1207146, 353041, 2609, 65536⟩
    (by decide) selected_cut_43993

theorem selected_cut_43994 : selected 9 ⟨1207201, by decide⟩
    (prefixPartial 12 353042) = some ⟨12, 2, 0, 1207201, 353042, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_353042_1207201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353042 ⟨1207201, by decide⟩ :=
  accepted_of_selected 12 353042 ⟨1207201, by decide⟩ ⟨12, 2, 0, 1207201, 353042, 2917, 65536⟩
    (by decide) selected_cut_43994

theorem selected_cut_43995 : selected 9 ⟨1207254, by decide⟩
    (prefixPartial 12 353043) = some ⟨12, 2, 0, 1207254, 353043, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_353043_1207254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353043 ⟨1207254, by decide⟩ :=
  accepted_of_selected 12 353043 ⟨1207254, by decide⟩ ⟨12, 2, 0, 1207254, 353043, 2925, 65536⟩
    (by decide) selected_cut_43995

theorem unmarked_context_11_88260_1207255 : frontier 10 ⟨1207255, by decide⟩
    (prefixCache 11 88260) (prefixPartial 11 88260) = false := by
  decide +kernel

theorem node_context_11_88260_1207255 : EJMOriginalGlobalDAGData.nodes 10 ⟨1207255, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1207146, by decide⟩,⟨1207201, by decide⟩,⟨1207254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88260_1207255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88260 ⟨1207255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88260
    ⟨1207255, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1207146, by decide⟩,⟨1207201, by decide⟩,⟨1207254, by decide⟩]) unmarked_context_11_88260_1207255 node_context_11_88260_1207255
  intro a
  fin_cases a
  · exact context_12_353040_435160
  · exact context_12_353041_1207146
  · exact context_12_353042_1207201
  · exact context_12_353043_1207254

theorem selected_cut_43996 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 88261) = some ⟨11, 1, 0, 815620, 88261, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88261_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88261 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 88261 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 88261, 1, 262144⟩
    (by decide) selected_cut_43996

theorem selected_cut_43997 : selected 9 ⟨1207330, by decide⟩
    (prefixPartial 12 353048) = some ⟨12, 2, 0, 1207330, 353048, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_353048_1207330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353048 ⟨1207330, by decide⟩ :=
  accepted_of_selected 12 353048 ⟨1207330, by decide⟩ ⟨12, 2, 0, 1207330, 353048, 3649, 65536⟩
    (by decide) selected_cut_43997

theorem selected_cut_43998 : selected 9 ⟨1207396, by decide⟩
    (prefixPartial 12 353049) = some ⟨12, 2, 0, 1207396, 353049, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_353049_1207396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353049 ⟨1207396, by decide⟩ :=
  accepted_of_selected 12 353049 ⟨1207396, by decide⟩ ⟨12, 2, 0, 1207396, 353049, 3229, 65536⟩
    (by decide) selected_cut_43998

theorem selected_cut_43999 : selected 9 ⟨1207477, by decide⟩
    (prefixPartial 12 353050) = some ⟨12, 2, 0, 1207477, 353050, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_353050_1207477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353050 ⟨1207477, by decide⟩ :=
  accepted_of_selected 12 353050 ⟨1207477, by decide⟩ ⟨12, 2, 0, 1207477, 353050, 3257, 65536⟩
    (by decide) selected_cut_43999

theorem selected_cut_44000 : selected 9 ⟨1207548, by decide⟩
    (prefixPartial 12 353051) = some ⟨12, 2, 0, 1207548, 353051, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_353051_1207548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353051 ⟨1207548, by decide⟩ :=
  accepted_of_selected 12 353051 ⟨1207548, by decide⟩ ⟨12, 2, 0, 1207548, 353051, 3497, 65536⟩
    (by decide) selected_cut_44000

theorem unmarked_context_11_88262_1207549 : frontier 10 ⟨1207549, by decide⟩
    (prefixCache 11 88262) (prefixPartial 11 88262) = false := by
  decide +kernel

theorem node_context_11_88262_1207549 : EJMOriginalGlobalDAGData.nodes 10 ⟨1207549, by decide⟩ =
    .split (coordinate 11) (![⟨1207330, by decide⟩,⟨1207396, by decide⟩,⟨1207477, by decide⟩,⟨1207548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88262_1207549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88262 ⟨1207549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88262
    ⟨1207549, by decide⟩ (by decide) (![⟨1207330, by decide⟩,⟨1207396, by decide⟩,⟨1207477, by decide⟩,⟨1207548, by decide⟩]) unmarked_context_11_88262_1207549 node_context_11_88262_1207549
  intro a
  fin_cases a
  · exact context_12_353048_1207330
  · exact context_12_353049_1207396
  · exact context_12_353050_1207477
  · exact context_12_353051_1207548

theorem selected_cut_44001 : selected 9 ⟨1207604, by decide⟩
    (prefixPartial 12 353052) = some ⟨12, 2, 0, 1207604, 353052, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_353052_1207604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353052 ⟨1207604, by decide⟩ :=
  accepted_of_selected 12 353052 ⟨1207604, by decide⟩ ⟨12, 2, 0, 1207604, 353052, 3105, 65536⟩
    (by decide) selected_cut_44001

theorem selected_cut_44002 : selected 9 ⟨1207647, by decide⟩
    (prefixPartial 12 353053) = some ⟨12, 2, 0, 1207647, 353053, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_353053_1207647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353053 ⟨1207647, by decide⟩ :=
  accepted_of_selected 12 353053 ⟨1207647, by decide⟩ ⟨12, 2, 0, 1207647, 353053, 2577, 65536⟩
    (by decide) selected_cut_44002

theorem selected_cut_44003 : selected 9 ⟨1207702, by decide⟩
    (prefixPartial 12 353054) = some ⟨12, 2, 0, 1207702, 353054, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_353054_1207702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353054 ⟨1207702, by decide⟩ :=
  accepted_of_selected 12 353054 ⟨1207702, by decide⟩ ⟨12, 2, 0, 1207702, 353054, 3093, 65536⟩
    (by decide) selected_cut_44003

theorem selected_cut_44004 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 353055) = some ⟨12, 1, 0, 903806, 353055, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353055_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353055 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 353055 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 353055, 1, 65536⟩
    (by decide) selected_cut_44004

theorem unmarked_context_11_88263_1207703 : frontier 10 ⟨1207703, by decide⟩
    (prefixCache 11 88263) (prefixPartial 11 88263) = false := by
  decide +kernel

theorem node_context_11_88263_1207703 : EJMOriginalGlobalDAGData.nodes 10 ⟨1207703, by decide⟩ =
    .split (coordinate 11) (![⟨1207604, by decide⟩,⟨1207647, by decide⟩,⟨1207702, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88263_1207703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88263 ⟨1207703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88263
    ⟨1207703, by decide⟩ (by decide) (![⟨1207604, by decide⟩,⟨1207647, by decide⟩,⟨1207702, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_88263_1207703 node_context_11_88263_1207703
  intro a
  fin_cases a
  · exact context_12_353052_1207604
  · exact context_12_353053_1207647
  · exact context_12_353054_1207702
  · exact context_12_353055_903806

theorem unmarked_context_10_22065_1207704 : frontier 11 ⟨1207704, by decide⟩
    (prefixCache 10 22065) (prefixPartial 10 22065) = false := by
  decide +kernel

theorem node_context_10_22065_1207704 : EJMOriginalGlobalDAGData.nodes 11 ⟨1207704, by decide⟩ =
    .split (coordinate 10) (![⟨1207255, by decide⟩,⟨815620, by decide⟩,⟨1207549, by decide⟩,⟨1207703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22065_1207704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22065 ⟨1207704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22065
    ⟨1207704, by decide⟩ (by decide) (![⟨1207255, by decide⟩,⟨815620, by decide⟩,⟨1207549, by decide⟩,⟨1207703, by decide⟩]) unmarked_context_10_22065_1207704 node_context_10_22065_1207704
  intro a
  fin_cases a
  · exact context_11_88260_1207255
  · exact context_11_88261_815620
  · exact context_11_88262_1207549
  · exact context_11_88263_1207703

theorem selected_cut_44005 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 353056) = some ⟨12, 1, 0, 1187656, 353056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353056_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353056 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 353056 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 353056, 1, 65536⟩
    (by decide) selected_cut_44005

theorem selected_cut_44006 : selected 9 ⟨1207742, by decide⟩
    (prefixPartial 12 353057) = some ⟨12, 2, 0, 1207742, 353057, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_353057_1207742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353057 ⟨1207742, by decide⟩ :=
  accepted_of_selected 12 353057 ⟨1207742, by decide⟩ ⟨12, 2, 0, 1207742, 353057, 2477, 65536⟩
    (by decide) selected_cut_44006

theorem selected_cut_44007 : selected 9 ⟨1207783, by decide⟩
    (prefixPartial 12 353058) = some ⟨12, 2, 0, 1207783, 353058, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_353058_1207783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353058 ⟨1207783, by decide⟩ :=
  accepted_of_selected 12 353058 ⟨1207783, by decide⟩ ⟨12, 2, 0, 1207783, 353058, 2525, 65536⟩
    (by decide) selected_cut_44007

theorem selected_cut_44008 : selected 9 ⟨1207826, by decide⟩
    (prefixPartial 12 353059) = some ⟨12, 2, 0, 1207826, 353059, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_353059_1207826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353059 ⟨1207826, by decide⟩ :=
  accepted_of_selected 12 353059 ⟨1207826, by decide⟩ ⟨12, 2, 0, 1207826, 353059, 2617, 65536⟩
    (by decide) selected_cut_44008

theorem unmarked_context_11_88264_1207827 : frontier 10 ⟨1207827, by decide⟩
    (prefixCache 11 88264) (prefixPartial 11 88264) = false := by
  decide +kernel

theorem node_context_11_88264_1207827 : EJMOriginalGlobalDAGData.nodes 10 ⟨1207827, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1207742, by decide⟩,⟨1207783, by decide⟩,⟨1207826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88264_1207827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88264 ⟨1207827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88264
    ⟨1207827, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1207742, by decide⟩,⟨1207783, by decide⟩,⟨1207826, by decide⟩]) unmarked_context_11_88264_1207827 node_context_11_88264_1207827
  intro a
  fin_cases a
  · exact context_12_353056_1187656
  · exact context_12_353057_1207742
  · exact context_12_353058_1207783
  · exact context_12_353059_1207826

theorem selected_cut_44009 : selected 9 ⟨1207880, by decide⟩
    (prefixPartial 12 353060) = some ⟨12, 2, 0, 1207880, 353060, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_353060_1207880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353060 ⟨1207880, by decide⟩ :=
  accepted_of_selected 12 353060 ⟨1207880, by decide⟩ ⟨12, 2, 0, 1207880, 353060, 3157, 65536⟩
    (by decide) selected_cut_44009

theorem selected_cut_44010 : selected 9 ⟨1207916, by decide⟩
    (prefixPartial 12 353061) = some ⟨12, 2, 0, 1207916, 353061, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_353061_1207916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353061 ⟨1207916, by decide⟩ :=
  accepted_of_selected 12 353061 ⟨1207916, by decide⟩ ⟨12, 2, 0, 1207916, 353061, 2533, 65536⟩
    (by decide) selected_cut_44010

theorem selected_cut_44011 : selected 9 ⟨1207955, by decide⟩
    (prefixPartial 12 353062) = some ⟨12, 2, 0, 1207955, 353062, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_353062_1207955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353062 ⟨1207955, by decide⟩ :=
  accepted_of_selected 12 353062 ⟨1207955, by decide⟩ ⟨12, 2, 0, 1207955, 353062, 2605, 65536⟩
    (by decide) selected_cut_44011

theorem selected_cut_44012 : selected 9 ⟨1207995, by decide⟩
    (prefixPartial 12 353063) = some ⟨12, 2, 0, 1207995, 353063, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_353063_1207995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353063 ⟨1207995, by decide⟩ :=
  accepted_of_selected 12 353063 ⟨1207995, by decide⟩ ⟨12, 2, 0, 1207995, 353063, 2733, 65536⟩
    (by decide) selected_cut_44012

theorem unmarked_context_11_88265_1207996 : frontier 10 ⟨1207996, by decide⟩
    (prefixCache 11 88265) (prefixPartial 11 88265) = false := by
  decide +kernel

theorem node_context_11_88265_1207996 : EJMOriginalGlobalDAGData.nodes 10 ⟨1207996, by decide⟩ =
    .split (coordinate 11) (![⟨1207880, by decide⟩,⟨1207916, by decide⟩,⟨1207955, by decide⟩,⟨1207995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88265_1207996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88265 ⟨1207996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88265
    ⟨1207996, by decide⟩ (by decide) (![⟨1207880, by decide⟩,⟨1207916, by decide⟩,⟨1207955, by decide⟩,⟨1207995, by decide⟩]) unmarked_context_11_88265_1207996 node_context_11_88265_1207996
  intro a
  fin_cases a
  · exact context_12_353060_1207880
  · exact context_12_353061_1207916
  · exact context_12_353062_1207955
  · exact context_12_353063_1207995

theorem selected_cut_44013 : selected 9 ⟨1208049, by decide⟩
    (prefixPartial 12 353064) = some ⟨12, 2, 0, 1208049, 353064, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_353064_1208049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353064 ⟨1208049, by decide⟩ :=
  accepted_of_selected 12 353064 ⟨1208049, by decide⟩ ⟨12, 2, 0, 1208049, 353064, 3141, 65536⟩
    (by decide) selected_cut_44013

theorem selected_cut_44014 : selected 9 ⟨1208089, by decide⟩
    (prefixPartial 12 353065) = some ⟨12, 2, 0, 1208089, 353065, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_353065_1208089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353065 ⟨1208089, by decide⟩ :=
  accepted_of_selected 12 353065 ⟨1208089, by decide⟩ ⟨12, 2, 0, 1208089, 353065, 2633, 65536⟩
    (by decide) selected_cut_44014

theorem selected_cut_44015 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 353066) = some ⟨12, 1, 0, 474208, 353066, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353066_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353066 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 353066 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 353066, 1, 65536⟩
    (by decide) selected_cut_44015

theorem selected_cut_44016 : selected 9 ⟨1208141, by decide⟩
    (prefixPartial 12 353067) = some ⟨12, 2, 0, 1208141, 353067, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_353067_1208141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353067 ⟨1208141, by decide⟩ :=
  accepted_of_selected 12 353067 ⟨1208141, by decide⟩ ⟨12, 2, 0, 1208141, 353067, 2689, 65536⟩
    (by decide) selected_cut_44016

theorem unmarked_context_11_88266_1208142 : frontier 10 ⟨1208142, by decide⟩
    (prefixCache 11 88266) (prefixPartial 11 88266) = false := by
  decide +kernel

theorem node_context_11_88266_1208142 : EJMOriginalGlobalDAGData.nodes 10 ⟨1208142, by decide⟩ =
    .split (coordinate 11) (![⟨1208049, by decide⟩,⟨1208089, by decide⟩,⟨474208, by decide⟩,⟨1208141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88266_1208142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88266 ⟨1208142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88266
    ⟨1208142, by decide⟩ (by decide) (![⟨1208049, by decide⟩,⟨1208089, by decide⟩,⟨474208, by decide⟩,⟨1208141, by decide⟩]) unmarked_context_11_88266_1208142 node_context_11_88266_1208142
  intro a
  fin_cases a
  · exact context_12_353064_1208049
  · exact context_12_353065_1208089
  · exact context_12_353066_474208
  · exact context_12_353067_1208141

theorem selected_cut_44017 : selected 9 ⟨1208188, by decide⟩
    (prefixPartial 12 353068) = some ⟨12, 2, 0, 1208188, 353068, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_353068_1208188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353068 ⟨1208188, by decide⟩ :=
  accepted_of_selected 12 353068 ⟨1208188, by decide⟩ ⟨12, 2, 0, 1208188, 353068, 2733, 65536⟩
    (by decide) selected_cut_44017

theorem selected_cut_44018 : selected 9 ⟨1208225, by decide⟩
    (prefixPartial 12 353069) = some ⟨12, 2, 0, 1208225, 353069, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_353069_1208225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353069 ⟨1208225, by decide⟩ :=
  accepted_of_selected 12 353069 ⟨1208225, by decide⟩ ⟨12, 2, 0, 1208225, 353069, 2193, 65536⟩
    (by decide) selected_cut_44018

theorem selected_cut_44019 : selected 9 ⟨1208272, by decide⟩
    (prefixPartial 12 353070) = some ⟨12, 2, 0, 1208272, 353070, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_353070_1208272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353070 ⟨1208272, by decide⟩ :=
  accepted_of_selected 12 353070 ⟨1208272, by decide⟩ ⟨12, 2, 0, 1208272, 353070, 2465, 65536⟩
    (by decide) selected_cut_44019

theorem selected_cut_44020 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 353071) = some ⟨12, 1, 0, 903806, 353071, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353071_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353071 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 353071 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 353071, 1, 65536⟩
    (by decide) selected_cut_44020

theorem unmarked_context_11_88267_1208273 : frontier 10 ⟨1208273, by decide⟩
    (prefixCache 11 88267) (prefixPartial 11 88267) = false := by
  decide +kernel

theorem node_context_11_88267_1208273 : EJMOriginalGlobalDAGData.nodes 10 ⟨1208273, by decide⟩ =
    .split (coordinate 11) (![⟨1208188, by decide⟩,⟨1208225, by decide⟩,⟨1208272, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88267_1208273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88267 ⟨1208273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88267
    ⟨1208273, by decide⟩ (by decide) (![⟨1208188, by decide⟩,⟨1208225, by decide⟩,⟨1208272, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_88267_1208273 node_context_11_88267_1208273
  intro a
  fin_cases a
  · exact context_12_353068_1208188
  · exact context_12_353069_1208225
  · exact context_12_353070_1208272
  · exact context_12_353071_903806

theorem unmarked_context_10_22066_1208274 : frontier 11 ⟨1208274, by decide⟩
    (prefixCache 10 22066) (prefixPartial 10 22066) = false := by
  decide +kernel

theorem node_context_10_22066_1208274 : EJMOriginalGlobalDAGData.nodes 11 ⟨1208274, by decide⟩ =
    .split (coordinate 10) (![⟨1207827, by decide⟩,⟨1207996, by decide⟩,⟨1208142, by decide⟩,⟨1208273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22066_1208274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22066 ⟨1208274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22066
    ⟨1208274, by decide⟩ (by decide) (![⟨1207827, by decide⟩,⟨1207996, by decide⟩,⟨1208142, by decide⟩,⟨1208273, by decide⟩]) unmarked_context_10_22066_1208274 node_context_10_22066_1208274
  intro a
  fin_cases a
  · exact context_11_88264_1207827
  · exact context_11_88265_1207996
  · exact context_11_88266_1208142
  · exact context_11_88267_1208273

theorem selected_cut_44021 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 353072) = some ⟨12, 1, 0, 792260, 353072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353072_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353072 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 353072 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 353072, 1, 65536⟩
    (by decide) selected_cut_44021

theorem selected_cut_44022 : selected 9 ⟨1208311, by decide⟩
    (prefixPartial 12 353073) = some ⟨12, 2, 0, 1208311, 353073, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_353073_1208311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353073 ⟨1208311, by decide⟩ :=
  accepted_of_selected 12 353073 ⟨1208311, by decide⟩ ⟨12, 2, 0, 1208311, 353073, 2253, 65536⟩
    (by decide) selected_cut_44022

theorem selected_cut_44023 : selected 9 ⟨1208356, by decide⟩
    (prefixPartial 12 353074) = some ⟨12, 2, 0, 1208356, 353074, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_353074_1208356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353074 ⟨1208356, by decide⟩ :=
  accepted_of_selected 12 353074 ⟨1208356, by decide⟩ ⟨12, 2, 0, 1208356, 353074, 2389, 65536⟩
    (by decide) selected_cut_44023

theorem selected_cut_44024 : selected 9 ⟨1208392, by decide⟩
    (prefixPartial 12 353075) = some ⟨12, 2, 0, 1208392, 353075, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_353075_1208392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353075 ⟨1208392, by decide⟩ :=
  accepted_of_selected 12 353075 ⟨1208392, by decide⟩ ⟨12, 2, 0, 1208392, 353075, 2241, 65536⟩
    (by decide) selected_cut_44024

theorem unmarked_context_11_88268_1208393 : frontier 10 ⟨1208393, by decide⟩
    (prefixCache 11 88268) (prefixPartial 11 88268) = false := by
  decide +kernel

theorem node_context_11_88268_1208393 : EJMOriginalGlobalDAGData.nodes 10 ⟨1208393, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨1208311, by decide⟩,⟨1208356, by decide⟩,⟨1208392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88268_1208393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88268 ⟨1208393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88268
    ⟨1208393, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨1208311, by decide⟩,⟨1208356, by decide⟩,⟨1208392, by decide⟩]) unmarked_context_11_88268_1208393 node_context_11_88268_1208393
  intro a
  fin_cases a
  · exact context_12_353072_792260
  · exact context_12_353073_1208311
  · exact context_12_353074_1208356
  · exact context_12_353075_1208392

theorem selected_cut_44025 : selected 9 ⟨1208448, by decide⟩
    (prefixPartial 12 353076) = some ⟨12, 2, 0, 1208448, 353076, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_353076_1208448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353076 ⟨1208448, by decide⟩ :=
  accepted_of_selected 12 353076 ⟨1208448, by decide⟩ ⟨12, 2, 0, 1208448, 353076, 2909, 65536⟩
    (by decide) selected_cut_44025

theorem selected_cut_44026 : selected 9 ⟨1208490, by decide⟩
    (prefixPartial 12 353077) = some ⟨12, 2, 0, 1208490, 353077, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_353077_1208490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353077 ⟨1208490, by decide⟩ :=
  accepted_of_selected 12 353077 ⟨1208490, by decide⟩ ⟨12, 2, 0, 1208490, 353077, 2329, 65536⟩
    (by decide) selected_cut_44026

theorem selected_cut_44027 : selected 9 ⟨1208538, by decide⟩
    (prefixPartial 12 353078) = some ⟨12, 2, 0, 1208538, 353078, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_353078_1208538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353078 ⟨1208538, by decide⟩ :=
  accepted_of_selected 12 353078 ⟨1208538, by decide⟩ ⟨12, 2, 0, 1208538, 353078, 2401, 65536⟩
    (by decide) selected_cut_44027

theorem selected_cut_44028 : selected 9 ⟨1208579, by decide⟩
    (prefixPartial 12 353079) = some ⟨12, 2, 0, 1208579, 353079, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_353079_1208579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353079 ⟨1208579, by decide⟩ :=
  accepted_of_selected 12 353079 ⟨1208579, by decide⟩ ⟨12, 2, 0, 1208579, 353079, 2373, 65536⟩
    (by decide) selected_cut_44028

theorem unmarked_context_11_88269_1208580 : frontier 10 ⟨1208580, by decide⟩
    (prefixCache 11 88269) (prefixPartial 11 88269) = false := by
  decide +kernel

theorem node_context_11_88269_1208580 : EJMOriginalGlobalDAGData.nodes 10 ⟨1208580, by decide⟩ =
    .split (coordinate 11) (![⟨1208448, by decide⟩,⟨1208490, by decide⟩,⟨1208538, by decide⟩,⟨1208579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88269_1208580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88269 ⟨1208580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88269
    ⟨1208580, by decide⟩ (by decide) (![⟨1208448, by decide⟩,⟨1208490, by decide⟩,⟨1208538, by decide⟩,⟨1208579, by decide⟩]) unmarked_context_11_88269_1208580 node_context_11_88269_1208580
  intro a
  fin_cases a
  · exact context_12_353076_1208448
  · exact context_12_353077_1208490
  · exact context_12_353078_1208538
  · exact context_12_353079_1208579

theorem selected_cut_44029 : selected 9 ⟨1208644, by decide⟩
    (prefixPartial 12 353080) = some ⟨12, 2, 0, 1208644, 353080, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_353080_1208644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353080 ⟨1208644, by decide⟩ :=
  accepted_of_selected 12 353080 ⟨1208644, by decide⟩ ⟨12, 2, 0, 1208644, 353080, 2977, 65536⟩
    (by decide) selected_cut_44029

theorem selected_cut_44030 : selected 9 ⟨1208701, by decide⟩
    (prefixPartial 12 353081) = some ⟨12, 2, 0, 1208701, 353081, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_353081_1208701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353081 ⟨1208701, by decide⟩ :=
  accepted_of_selected 12 353081 ⟨1208701, by decide⟩ ⟨12, 2, 0, 1208701, 353081, 2493, 65536⟩
    (by decide) selected_cut_44030

theorem selected_cut_44031 : selected 9 ⟨1208748, by decide⟩
    (prefixPartial 12 353082) = some ⟨12, 2, 0, 1208748, 353082, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_353082_1208748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353082 ⟨1208748, by decide⟩ :=
  accepted_of_selected 12 353082 ⟨1208748, by decide⟩ ⟨12, 2, 0, 1208748, 353082, 2481, 65536⟩
    (by decide) selected_cut_44031

theorem selected_cut_44032 : selected 9 ⟨1208799, by decide⟩
    (prefixPartial 12 353083) = some ⟨12, 2, 0, 1208799, 353083, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_353083_1208799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353083 ⟨1208799, by decide⟩ :=
  accepted_of_selected 12 353083 ⟨1208799, by decide⟩ ⟨12, 2, 0, 1208799, 353083, 2453, 65536⟩
    (by decide) selected_cut_44032

theorem unmarked_context_11_88270_1208800 : frontier 10 ⟨1208800, by decide⟩
    (prefixCache 11 88270) (prefixPartial 11 88270) = false := by
  decide +kernel

theorem node_context_11_88270_1208800 : EJMOriginalGlobalDAGData.nodes 10 ⟨1208800, by decide⟩ =
    .split (coordinate 11) (![⟨1208644, by decide⟩,⟨1208701, by decide⟩,⟨1208748, by decide⟩,⟨1208799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88270_1208800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88270 ⟨1208800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88270
    ⟨1208800, by decide⟩ (by decide) (![⟨1208644, by decide⟩,⟨1208701, by decide⟩,⟨1208748, by decide⟩,⟨1208799, by decide⟩]) unmarked_context_11_88270_1208800 node_context_11_88270_1208800
  intro a
  fin_cases a
  · exact context_12_353080_1208644
  · exact context_12_353081_1208701
  · exact context_12_353082_1208748
  · exact context_12_353083_1208799

theorem selected_cut_44033 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 353084) = some ⟨12, 1, 0, 429285, 353084, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353084_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353084 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 353084 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 353084, 1, 65536⟩
    (by decide) selected_cut_44033

theorem selected_cut_44034 : selected 9 ⟨1208829, by decide⟩
    (prefixPartial 12 353085) = some ⟨12, 2, 0, 1208829, 353085, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_353085_1208829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353085 ⟨1208829, by decide⟩ :=
  accepted_of_selected 12 353085 ⟨1208829, by decide⟩ ⟨12, 2, 0, 1208829, 353085, 2029, 65536⟩
    (by decide) selected_cut_44034

theorem selected_cut_44035 : selected 9 ⟨1208870, by decide⟩
    (prefixPartial 12 353086) = some ⟨12, 2, 0, 1208870, 353086, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_353086_1208870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353086 ⟨1208870, by decide⟩ :=
  accepted_of_selected 12 353086 ⟨1208870, by decide⟩ ⟨12, 2, 0, 1208870, 353086, 2257, 65536⟩
    (by decide) selected_cut_44035

theorem selected_cut_44036 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 353087) = some ⟨12, 1, 0, 607719, 353087, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353087_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353087 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 353087 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 353087, 1, 65536⟩
    (by decide) selected_cut_44036

theorem unmarked_context_11_88271_1208871 : frontier 10 ⟨1208871, by decide⟩
    (prefixCache 11 88271) (prefixPartial 11 88271) = false := by
  decide +kernel

theorem node_context_11_88271_1208871 : EJMOriginalGlobalDAGData.nodes 10 ⟨1208871, by decide⟩ =
    .split (coordinate 11) (![⟨429285, by decide⟩,⟨1208829, by decide⟩,⟨1208870, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88271_1208871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88271 ⟨1208871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88271
    ⟨1208871, by decide⟩ (by decide) (![⟨429285, by decide⟩,⟨1208829, by decide⟩,⟨1208870, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_88271_1208871 node_context_11_88271_1208871
  intro a
  fin_cases a
  · exact context_12_353084_429285
  · exact context_12_353085_1208829
  · exact context_12_353086_1208870
  · exact context_12_353087_607719

theorem unmarked_context_10_22067_1208872 : frontier 11 ⟨1208872, by decide⟩
    (prefixCache 10 22067) (prefixPartial 10 22067) = false := by
  decide +kernel

theorem node_context_10_22067_1208872 : EJMOriginalGlobalDAGData.nodes 11 ⟨1208872, by decide⟩ =
    .split (coordinate 10) (![⟨1208393, by decide⟩,⟨1208580, by decide⟩,⟨1208800, by decide⟩,⟨1208871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22067_1208872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22067 ⟨1208872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22067
    ⟨1208872, by decide⟩ (by decide) (![⟨1208393, by decide⟩,⟨1208580, by decide⟩,⟨1208800, by decide⟩,⟨1208871, by decide⟩]) unmarked_context_10_22067_1208872 node_context_10_22067_1208872
  intro a
  fin_cases a
  · exact context_11_88268_1208393
  · exact context_11_88269_1208580
  · exact context_11_88270_1208800
  · exact context_11_88271_1208871

theorem unmarked_context_9_5516_1208873 : frontier 12 ⟨1208873, by decide⟩
    (prefixCache 9 5516) (prefixPartial 9 5516) = false := by
  decide +kernel

theorem node_context_9_5516_1208873 : EJMOriginalGlobalDAGData.nodes 12 ⟨1208873, by decide⟩ =
    .split (coordinate 9) (![⟨1207101, by decide⟩,⟨1207704, by decide⟩,⟨1208274, by decide⟩,⟨1208872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5516_1208873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5516 ⟨1208873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5516
    ⟨1208873, by decide⟩ (by decide) (![⟨1207101, by decide⟩,⟨1207704, by decide⟩,⟨1208274, by decide⟩,⟨1208872, by decide⟩]) unmarked_context_9_5516_1208873 node_context_9_5516_1208873
  intro a
  fin_cases a
  · exact context_10_22064_1207101
  · exact context_10_22065_1207704
  · exact context_10_22066_1208274
  · exact context_10_22067_1208872

theorem selected_cut_44037 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88272) = some ⟨11, 1, 0, 907917, 88272, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88272_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88272 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88272 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88272, 1, 262144⟩
    (by decide) selected_cut_44037

theorem selected_cut_44038 : selected 9 ⟨1208903, by decide⟩
    (prefixPartial 12 353092) = some ⟨12, 2, 0, 1208903, 353092, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_353092_1208903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353092 ⟨1208903, by decide⟩ :=
  accepted_of_selected 12 353092 ⟨1208903, by decide⟩ ⟨12, 2, 0, 1208903, 353092, 1649, 65536⟩
    (by decide) selected_cut_44038

theorem selected_cut_44039 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353093) = some ⟨12, 1, 0, 896706, 353093, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353093_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353093 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353093 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353093, 1, 65536⟩
    (by decide) selected_cut_44039

theorem selected_cut_44040 : selected 9 ⟨1208925, by decide⟩
    (prefixPartial 12 353094) = some ⟨12, 2, 0, 1208925, 353094, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_353094_1208925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353094 ⟨1208925, by decide⟩ :=
  accepted_of_selected 12 353094 ⟨1208925, by decide⟩ ⟨12, 2, 0, 1208925, 353094, 1449, 65536⟩
    (by decide) selected_cut_44040

theorem selected_cut_44041 : selected 9 ⟨1208952, by decide⟩
    (prefixPartial 12 353095) = some ⟨12, 2, 0, 1208952, 353095, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_353095_1208952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353095 ⟨1208952, by decide⟩ :=
  accepted_of_selected 12 353095 ⟨1208952, by decide⟩ ⟨12, 2, 0, 1208952, 353095, 1573, 65536⟩
    (by decide) selected_cut_44041

theorem unmarked_context_11_88273_1208953 : frontier 10 ⟨1208953, by decide⟩
    (prefixCache 11 88273) (prefixPartial 11 88273) = false := by
  decide +kernel

theorem node_context_11_88273_1208953 : EJMOriginalGlobalDAGData.nodes 10 ⟨1208953, by decide⟩ =
    .split (coordinate 11) (![⟨1208903, by decide⟩,⟨896706, by decide⟩,⟨1208925, by decide⟩,⟨1208952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88273_1208953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88273 ⟨1208953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88273
    ⟨1208953, by decide⟩ (by decide) (![⟨1208903, by decide⟩,⟨896706, by decide⟩,⟨1208925, by decide⟩,⟨1208952, by decide⟩]) unmarked_context_11_88273_1208953 node_context_11_88273_1208953
  intro a
  fin_cases a
  · exact context_12_353092_1208903
  · exact context_12_353093_896706
  · exact context_12_353094_1208925
  · exact context_12_353095_1208952

theorem selected_cut_44042 : selected 9 ⟨1208985, by decide⟩
    (prefixPartial 12 353096) = some ⟨12, 2, 0, 1208985, 353096, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_353096_1208985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353096 ⟨1208985, by decide⟩ :=
  accepted_of_selected 12 353096 ⟨1208985, by decide⟩ ⟨12, 2, 0, 1208985, 353096, 1853, 65536⟩
    (by decide) selected_cut_44042

theorem selected_cut_44043 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353097) = some ⟨12, 1, 0, 896706, 353097, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353097_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353097 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353097 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353097, 1, 65536⟩
    (by decide) selected_cut_44043

theorem selected_cut_44044 : selected 9 ⟨1209012, by decide⟩
    (prefixPartial 12 353098) = some ⟨12, 2, 0, 1209012, 353098, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_353098_1209012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353098 ⟨1209012, by decide⟩ :=
  accepted_of_selected 12 353098 ⟨1209012, by decide⟩ ⟨12, 2, 0, 1209012, 353098, 1633, 65536⟩
    (by decide) selected_cut_44044

theorem selected_cut_44045 : selected 9 ⟨1209041, by decide⟩
    (prefixPartial 12 353099) = some ⟨12, 2, 0, 1209041, 353099, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_353099_1209041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353099 ⟨1209041, by decide⟩ :=
  accepted_of_selected 12 353099 ⟨1209041, by decide⟩ ⟨12, 2, 0, 1209041, 353099, 1741, 65536⟩
    (by decide) selected_cut_44045

theorem unmarked_context_11_88274_1209042 : frontier 10 ⟨1209042, by decide⟩
    (prefixCache 11 88274) (prefixPartial 11 88274) = false := by
  decide +kernel

theorem node_context_11_88274_1209042 : EJMOriginalGlobalDAGData.nodes 10 ⟨1209042, by decide⟩ =
    .split (coordinate 11) (![⟨1208985, by decide⟩,⟨896706, by decide⟩,⟨1209012, by decide⟩,⟨1209041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88274_1209042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88274 ⟨1209042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88274
    ⟨1209042, by decide⟩ (by decide) (![⟨1208985, by decide⟩,⟨896706, by decide⟩,⟨1209012, by decide⟩,⟨1209041, by decide⟩]) unmarked_context_11_88274_1209042 node_context_11_88274_1209042
  intro a
  fin_cases a
  · exact context_12_353096_1208985
  · exact context_12_353097_896706
  · exact context_12_353098_1209012
  · exact context_12_353099_1209041

theorem selected_cut_44046 : selected 10 ⟨1209089, by decide⟩
    (prefixPartial 11 88275) = some ⟨11, 2, 0, 1209089, 88275, 2997, 262144⟩ := by
  decide +kernel

theorem context_11_88275_1209089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88275 ⟨1209089, by decide⟩ :=
  accepted_of_selected 11 88275 ⟨1209089, by decide⟩ ⟨11, 2, 0, 1209089, 88275, 2997, 262144⟩
    (by decide) selected_cut_44046

theorem unmarked_context_10_22068_1209090 : frontier 11 ⟨1209090, by decide⟩
    (prefixCache 10 22068) (prefixPartial 10 22068) = false := by
  decide +kernel

theorem node_context_10_22068_1209090 : EJMOriginalGlobalDAGData.nodes 11 ⟨1209090, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1208953, by decide⟩,⟨1209042, by decide⟩,⟨1209089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22068_1209090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22068 ⟨1209090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22068
    ⟨1209090, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1208953, by decide⟩,⟨1209042, by decide⟩,⟨1209089, by decide⟩]) unmarked_context_10_22068_1209090 node_context_10_22068_1209090
  intro a
  fin_cases a
  · exact context_11_88272_907917
  · exact context_11_88273_1208953
  · exact context_11_88274_1209042
  · exact context_11_88275_1209089

theorem selected_cut_44047 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22069) = some ⟨10, 1, 0, 893098, 22069, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22069_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22069 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22069 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22069, 1, 1048576⟩
    (by decide) selected_cut_44047

theorem selected_cut_44048 : selected 9 ⟨1209109, by decide⟩
    (prefixPartial 12 353120) = some ⟨12, 2, 0, 1209109, 353120, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_353120_1209109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353120 ⟨1209109, by decide⟩ :=
  accepted_of_selected 12 353120 ⟨1209109, by decide⟩ ⟨12, 2, 0, 1209109, 353120, 1409, 65536⟩
    (by decide) selected_cut_44048

theorem selected_cut_44049 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353121) = some ⟨12, 1, 0, 896706, 353121, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353121_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353121 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353121 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353121, 1, 65536⟩
    (by decide) selected_cut_44049

theorem selected_cut_44050 : selected 9 ⟨1209132, by decide⟩
    (prefixPartial 12 353122) = some ⟨12, 2, 0, 1209132, 353122, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_353122_1209132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353122 ⟨1209132, by decide⟩ :=
  accepted_of_selected 12 353122 ⟨1209132, by decide⟩ ⟨12, 2, 0, 1209132, 353122, 1425, 65536⟩
    (by decide) selected_cut_44050

theorem selected_cut_44051 : selected 9 ⟨1209150, by decide⟩
    (prefixPartial 12 353123) = some ⟨12, 2, 0, 1209150, 353123, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_353123_1209150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353123 ⟨1209150, by decide⟩ :=
  accepted_of_selected 12 353123 ⟨1209150, by decide⟩ ⟨12, 2, 0, 1209150, 353123, 1417, 65536⟩
    (by decide) selected_cut_44051

theorem unmarked_context_11_88280_1209151 : frontier 10 ⟨1209151, by decide⟩
    (prefixCache 11 88280) (prefixPartial 11 88280) = false := by
  decide +kernel

theorem node_context_11_88280_1209151 : EJMOriginalGlobalDAGData.nodes 10 ⟨1209151, by decide⟩ =
    .split (coordinate 11) (![⟨1209109, by decide⟩,⟨896706, by decide⟩,⟨1209132, by decide⟩,⟨1209150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88280_1209151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88280 ⟨1209151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88280
    ⟨1209151, by decide⟩ (by decide) (![⟨1209109, by decide⟩,⟨896706, by decide⟩,⟨1209132, by decide⟩,⟨1209150, by decide⟩]) unmarked_context_11_88280_1209151 node_context_11_88280_1209151
  intro a
  fin_cases a
  · exact context_12_353120_1209109
  · exact context_12_353121_896706
  · exact context_12_353122_1209132
  · exact context_12_353123_1209150

theorem selected_cut_44052 : selected 9 ⟨1209165, by decide⟩
    (prefixPartial 12 353124) = some ⟨12, 2, 0, 1209165, 353124, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_353124_1209165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353124 ⟨1209165, by decide⟩ :=
  accepted_of_selected 12 353124 ⟨1209165, by decide⟩ ⟨12, 2, 0, 1209165, 353124, 1449, 65536⟩
    (by decide) selected_cut_44052

theorem selected_cut_44053 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353125) = some ⟨12, 1, 0, 896706, 353125, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353125_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353125 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353125 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353125, 1, 65536⟩
    (by decide) selected_cut_44053

theorem selected_cut_44054 : selected 9 ⟨1209181, by decide⟩
    (prefixPartial 12 353126) = some ⟨12, 2, 0, 1209181, 353126, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_353126_1209181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353126 ⟨1209181, by decide⟩ :=
  accepted_of_selected 12 353126 ⟨1209181, by decide⟩ ⟨12, 2, 0, 1209181, 353126, 1321, 65536⟩
    (by decide) selected_cut_44054

theorem selected_cut_44055 : selected 9 ⟨1209199, by decide⟩
    (prefixPartial 12 353127) = some ⟨12, 2, 0, 1209199, 353127, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_353127_1209199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353127 ⟨1209199, by decide⟩ :=
  accepted_of_selected 12 353127 ⟨1209199, by decide⟩ ⟨12, 2, 0, 1209199, 353127, 1369, 65536⟩
    (by decide) selected_cut_44055

theorem unmarked_context_11_88281_1209200 : frontier 10 ⟨1209200, by decide⟩
    (prefixCache 11 88281) (prefixPartial 11 88281) = false := by
  decide +kernel

theorem node_context_11_88281_1209200 : EJMOriginalGlobalDAGData.nodes 10 ⟨1209200, by decide⟩ =
    .split (coordinate 11) (![⟨1209165, by decide⟩,⟨896706, by decide⟩,⟨1209181, by decide⟩,⟨1209199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88281_1209200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88281 ⟨1209200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88281
    ⟨1209200, by decide⟩ (by decide) (![⟨1209165, by decide⟩,⟨896706, by decide⟩,⟨1209181, by decide⟩,⟨1209199, by decide⟩]) unmarked_context_11_88281_1209200 node_context_11_88281_1209200
  intro a
  fin_cases a
  · exact context_12_353124_1209165
  · exact context_12_353125_896706
  · exact context_12_353126_1209181
  · exact context_12_353127_1209199

theorem selected_cut_44056 : selected 10 ⟨1209242, by decide⟩
    (prefixPartial 11 88282) = some ⟨11, 2, 0, 1209242, 88282, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_88282_1209242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88282 ⟨1209242, by decide⟩ :=
  accepted_of_selected 11 88282 ⟨1209242, by decide⟩ ⟨11, 2, 0, 1209242, 88282, 2825, 262144⟩
    (by decide) selected_cut_44056

theorem selected_cut_44057 : selected 10 ⟨1209291, by decide⟩
    (prefixPartial 11 88283) = some ⟨11, 2, 0, 1209291, 88283, 2777, 262144⟩ := by
  decide +kernel

theorem context_11_88283_1209291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88283 ⟨1209291, by decide⟩ :=
  accepted_of_selected 11 88283 ⟨1209291, by decide⟩ ⟨11, 2, 0, 1209291, 88283, 2777, 262144⟩
    (by decide) selected_cut_44057

theorem unmarked_context_10_22070_1209292 : frontier 11 ⟨1209292, by decide⟩
    (prefixCache 10 22070) (prefixPartial 10 22070) = false := by
  decide +kernel

theorem node_context_10_22070_1209292 : EJMOriginalGlobalDAGData.nodes 11 ⟨1209292, by decide⟩ =
    .split (coordinate 10) (![⟨1209151, by decide⟩,⟨1209200, by decide⟩,⟨1209242, by decide⟩,⟨1209291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22070_1209292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22070 ⟨1209292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22070
    ⟨1209292, by decide⟩ (by decide) (![⟨1209151, by decide⟩,⟨1209200, by decide⟩,⟨1209242, by decide⟩,⟨1209291, by decide⟩]) unmarked_context_10_22070_1209292 node_context_10_22070_1209292
  intro a
  fin_cases a
  · exact context_11_88280_1209151
  · exact context_11_88281_1209200
  · exact context_11_88282_1209242
  · exact context_11_88283_1209291

theorem selected_cut_44058 : selected 10 ⟨1209341, by decide⟩
    (prefixPartial 11 88284) = some ⟨11, 2, 0, 1209341, 88284, 2901, 262144⟩ := by
  decide +kernel

theorem context_11_88284_1209341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88284 ⟨1209341, by decide⟩ :=
  accepted_of_selected 11 88284 ⟨1209341, by decide⟩ ⟨11, 2, 0, 1209341, 88284, 2901, 262144⟩
    (by decide) selected_cut_44058

theorem selected_cut_44059 : selected 9 ⟨1209366, by decide⟩
    (prefixPartial 12 353140) = some ⟨12, 2, 0, 1209366, 353140, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_353140_1209366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353140 ⟨1209366, by decide⟩ :=
  accepted_of_selected 12 353140 ⟨1209366, by decide⟩ ⟨12, 2, 0, 1209366, 353140, 1569, 65536⟩
    (by decide) selected_cut_44059

theorem selected_cut_44060 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353141) = some ⟨12, 1, 0, 896706, 353141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353141_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353141 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353141 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353141, 1, 65536⟩
    (by decide) selected_cut_44060

theorem selected_cut_44061 : selected 9 ⟨1209385, by decide⟩
    (prefixPartial 12 353142) = some ⟨12, 2, 0, 1209385, 353142, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_353142_1209385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353142 ⟨1209385, by decide⟩ :=
  accepted_of_selected 12 353142 ⟨1209385, by decide⟩ ⟨12, 2, 0, 1209385, 353142, 1341, 65536⟩
    (by decide) selected_cut_44061

theorem selected_cut_44062 : selected 9 ⟨1209407, by decide⟩
    (prefixPartial 12 353143) = some ⟨12, 2, 0, 1209407, 353143, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_353143_1209407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353143 ⟨1209407, by decide⟩ :=
  accepted_of_selected 12 353143 ⟨1209407, by decide⟩ ⟨12, 2, 0, 1209407, 353143, 1317, 65536⟩
    (by decide) selected_cut_44062

theorem unmarked_context_11_88285_1209408 : frontier 10 ⟨1209408, by decide⟩
    (prefixCache 11 88285) (prefixPartial 11 88285) = false := by
  decide +kernel

theorem node_context_11_88285_1209408 : EJMOriginalGlobalDAGData.nodes 10 ⟨1209408, by decide⟩ =
    .split (coordinate 11) (![⟨1209366, by decide⟩,⟨896706, by decide⟩,⟨1209385, by decide⟩,⟨1209407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88285_1209408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88285 ⟨1209408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88285
    ⟨1209408, by decide⟩ (by decide) (![⟨1209366, by decide⟩,⟨896706, by decide⟩,⟨1209385, by decide⟩,⟨1209407, by decide⟩]) unmarked_context_11_88285_1209408 node_context_11_88285_1209408
  intro a
  fin_cases a
  · exact context_12_353140_1209366
  · exact context_12_353141_896706
  · exact context_12_353142_1209385
  · exact context_12_353143_1209407

theorem selected_cut_44063 : selected 9 ⟨1209436, by decide⟩
    (prefixPartial 12 353144) = some ⟨12, 2, 0, 1209436, 353144, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_353144_1209436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353144 ⟨1209436, by decide⟩ :=
  accepted_of_selected 12 353144 ⟨1209436, by decide⟩ ⟨12, 2, 0, 1209436, 353144, 1633, 65536⟩
    (by decide) selected_cut_44063

theorem selected_cut_44064 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 353145) = some ⟨12, 1, 0, 896706, 353145, 1, 65536⟩ := by
  decide +kernel

theorem context_12_353145_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353145 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 353145 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 353145, 1, 65536⟩
    (by decide) selected_cut_44064

theorem selected_cut_44065 : selected 9 ⟨1209461, by decide⟩
    (prefixPartial 12 353146) = some ⟨12, 2, 0, 1209461, 353146, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_353146_1209461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353146 ⟨1209461, by decide⟩ :=
  accepted_of_selected 12 353146 ⟨1209461, by decide⟩ ⟨12, 2, 0, 1209461, 353146, 1377, 65536⟩
    (by decide) selected_cut_44065

theorem selected_cut_44066 : selected 9 ⟨1209482, by decide⟩
    (prefixPartial 12 353147) = some ⟨12, 2, 0, 1209482, 353147, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_353147_1209482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 353147 ⟨1209482, by decide⟩ :=
  accepted_of_selected 12 353147 ⟨1209482, by decide⟩ ⟨12, 2, 0, 1209482, 353147, 1289, 65536⟩
    (by decide) selected_cut_44066

theorem unmarked_context_11_88286_1209483 : frontier 10 ⟨1209483, by decide⟩
    (prefixCache 11 88286) (prefixPartial 11 88286) = false := by
  decide +kernel

theorem node_context_11_88286_1209483 : EJMOriginalGlobalDAGData.nodes 10 ⟨1209483, by decide⟩ =
    .split (coordinate 11) (![⟨1209436, by decide⟩,⟨896706, by decide⟩,⟨1209461, by decide⟩,⟨1209482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88286_1209483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88286 ⟨1209483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88286
    ⟨1209483, by decide⟩ (by decide) (![⟨1209436, by decide⟩,⟨896706, by decide⟩,⟨1209461, by decide⟩,⟨1209482, by decide⟩]) unmarked_context_11_88286_1209483 node_context_11_88286_1209483
  intro a
  fin_cases a
  · exact context_12_353144_1209436
  · exact context_12_353145_896706
  · exact context_12_353146_1209461
  · exact context_12_353147_1209482

theorem selected_cut_44067 : selected 10 ⟨1209510, by decide⟩
    (prefixPartial 11 88287) = some ⟨11, 2, 0, 1209510, 88287, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_88287_1209510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88287 ⟨1209510, by decide⟩ :=
  accepted_of_selected 11 88287 ⟨1209510, by decide⟩ ⟨11, 2, 0, 1209510, 88287, 1293, 262144⟩
    (by decide) selected_cut_44067

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
