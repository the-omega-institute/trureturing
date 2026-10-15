/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover519
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_49923 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 104901) = some ⟨11, 1, 0, 892405, 104901, 1, 262144⟩ := by
  decide +kernel

theorem context_11_104901_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104901 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 104901 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 104901, 1, 262144⟩
    (by decide) selected_cut_49923

theorem selected_cut_49924 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 419608) = some ⟨12, 1, 0, 1415033, 419608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419608_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419608 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 419608 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 419608, 1, 65536⟩
    (by decide) selected_cut_49924

theorem selected_cut_49925 : selected 9 ⟨1417096, by decide⟩
    (prefixPartial 12 419609) = some ⟨12, 2, 0, 1417096, 419609, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_419609_1417096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419609 ⟨1417096, by decide⟩ :=
  accepted_of_selected 12 419609 ⟨1417096, by decide⟩ ⟨12, 2, 0, 1417096, 419609, 1965, 65536⟩
    (by decide) selected_cut_49925

theorem selected_cut_49926 : selected 9 ⟨1417163, by decide⟩
    (prefixPartial 12 419610) = some ⟨12, 2, 0, 1417163, 419610, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_419610_1417163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419610 ⟨1417163, by decide⟩ :=
  accepted_of_selected 12 419610 ⟨1417163, by decide⟩ ⟨12, 2, 0, 1417163, 419610, 2237, 65536⟩
    (by decide) selected_cut_49926

theorem selected_cut_49927 : selected 9 ⟨1417235, by decide⟩
    (prefixPartial 12 419611) = some ⟨12, 2, 0, 1417235, 419611, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_419611_1417235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419611 ⟨1417235, by decide⟩ :=
  accepted_of_selected 12 419611 ⟨1417235, by decide⟩ ⟨12, 2, 0, 1417235, 419611, 2357, 65536⟩
    (by decide) selected_cut_49927

theorem unmarked_context_11_104902_1417236 : frontier 10 ⟨1417236, by decide⟩
    (prefixCache 11 104902) (prefixPartial 11 104902) = false := by
  decide +kernel

theorem node_context_11_104902_1417236 : EJMOriginalGlobalDAGData.nodes 10 ⟨1417236, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1417096, by decide⟩,⟨1417163, by decide⟩,⟨1417235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104902_1417236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104902 ⟨1417236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104902
    ⟨1417236, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1417096, by decide⟩,⟨1417163, by decide⟩,⟨1417235, by decide⟩]) unmarked_context_11_104902_1417236 node_context_11_104902_1417236
  intro a
  fin_cases a
  · exact context_12_419608_1415033
  · exact context_12_419609_1417096
  · exact context_12_419610_1417163
  · exact context_12_419611_1417235

theorem selected_cut_49928 : selected 10 ⟨1417338, by decide⟩
    (prefixPartial 11 104903) = some ⟨11, 2, 0, 1417338, 104903, 3881, 262144⟩ := by
  decide +kernel

theorem context_11_104903_1417338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104903 ⟨1417338, by decide⟩ :=
  accepted_of_selected 11 104903 ⟨1417338, by decide⟩ ⟨11, 2, 0, 1417338, 104903, 3881, 262144⟩
    (by decide) selected_cut_49928

theorem unmarked_context_10_26225_1417339 : frontier 11 ⟨1417339, by decide⟩
    (prefixCache 10 26225) (prefixPartial 10 26225) = false := by
  decide +kernel

theorem node_context_10_26225_1417339 : EJMOriginalGlobalDAGData.nodes 11 ⟨1417339, by decide⟩ =
    .split (coordinate 10) (![⟨1417040, by decide⟩,⟨892405, by decide⟩,⟨1417236, by decide⟩,⟨1417338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26225_1417339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26225 ⟨1417339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26225
    ⟨1417339, by decide⟩ (by decide) (![⟨1417040, by decide⟩,⟨892405, by decide⟩,⟨1417236, by decide⟩,⟨1417338, by decide⟩]) unmarked_context_10_26225_1417339 node_context_10_26225_1417339
  intro a
  fin_cases a
  · exact context_11_104900_1417040
  · exact context_11_104901_892405
  · exact context_11_104902_1417236
  · exact context_11_104903_1417338

theorem selected_cut_49929 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 419616) = some ⟨12, 1, 0, 435160, 419616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419616_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419616 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 419616 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 419616, 1, 65536⟩
    (by decide) selected_cut_49929

theorem selected_cut_49930 : selected 9 ⟨1417393, by decide⟩
    (prefixPartial 12 419617) = some ⟨12, 2, 0, 1417393, 419617, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_419617_1417393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419617 ⟨1417393, by decide⟩ :=
  accepted_of_selected 12 419617 ⟨1417393, by decide⟩ ⟨12, 2, 0, 1417393, 419617, 1881, 65536⟩
    (by decide) selected_cut_49930

theorem selected_cut_49931 : selected 9 ⟨1417458, by decide⟩
    (prefixPartial 12 419618) = some ⟨12, 2, 0, 1417458, 419618, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_419618_1417458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419618 ⟨1417458, by decide⟩ :=
  accepted_of_selected 12 419618 ⟨1417458, by decide⟩ ⟨12, 2, 0, 1417458, 419618, 2149, 65536⟩
    (by decide) selected_cut_49931

theorem selected_cut_49932 : selected 9 ⟨1417514, by decide⟩
    (prefixPartial 12 419619) = some ⟨12, 2, 0, 1417514, 419619, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_419619_1417514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419619 ⟨1417514, by decide⟩ :=
  accepted_of_selected 12 419619 ⟨1417514, by decide⟩ ⟨12, 2, 0, 1417514, 419619, 2173, 65536⟩
    (by decide) selected_cut_49932

theorem unmarked_context_11_104904_1417515 : frontier 10 ⟨1417515, by decide⟩
    (prefixCache 11 104904) (prefixPartial 11 104904) = false := by
  decide +kernel

theorem node_context_11_104904_1417515 : EJMOriginalGlobalDAGData.nodes 10 ⟨1417515, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1417393, by decide⟩,⟨1417458, by decide⟩,⟨1417514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104904_1417515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104904 ⟨1417515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104904
    ⟨1417515, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1417393, by decide⟩,⟨1417458, by decide⟩,⟨1417514, by decide⟩]) unmarked_context_11_104904_1417515 node_context_11_104904_1417515
  intro a
  fin_cases a
  · exact context_12_419616_435160
  · exact context_12_419617_1417393
  · exact context_12_419618_1417458
  · exact context_12_419619_1417514

theorem selected_cut_49933 : selected 10 ⟨1417597, by decide⟩
    (prefixPartial 11 104905) = some ⟨11, 2, 0, 1417597, 104905, 3149, 262144⟩ := by
  decide +kernel

theorem context_11_104905_1417597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104905 ⟨1417597, by decide⟩ :=
  accepted_of_selected 11 104905 ⟨1417597, by decide⟩ ⟨11, 2, 0, 1417597, 104905, 3149, 262144⟩
    (by decide) selected_cut_49933

theorem selected_cut_49934 : selected 10 ⟨1417683, by decide⟩
    (prefixPartial 11 104906) = some ⟨11, 2, 0, 1417683, 104906, 3069, 262144⟩ := by
  decide +kernel

theorem context_11_104906_1417683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104906 ⟨1417683, by decide⟩ :=
  accepted_of_selected 11 104906 ⟨1417683, by decide⟩ ⟨11, 2, 0, 1417683, 104906, 3069, 262144⟩
    (by decide) selected_cut_49934

theorem selected_cut_49935 : selected 9 ⟨1417734, by decide⟩
    (prefixPartial 12 419628) = some ⟨12, 2, 0, 1417734, 419628, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_419628_1417734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419628 ⟨1417734, by decide⟩ :=
  accepted_of_selected 12 419628 ⟨1417734, by decide⟩ ⟨12, 2, 0, 1417734, 419628, 1641, 65536⟩
    (by decide) selected_cut_49935

theorem selected_cut_49936 : selected 9 ⟨1417774, by decide⟩
    (prefixPartial 12 419629) = some ⟨12, 2, 0, 1417774, 419629, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_419629_1417774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419629 ⟨1417774, by decide⟩ :=
  accepted_of_selected 12 419629 ⟨1417774, by decide⟩ ⟨12, 2, 0, 1417774, 419629, 1501, 65536⟩
    (by decide) selected_cut_49936

theorem selected_cut_49937 : selected 9 ⟨1417820, by decide⟩
    (prefixPartial 12 419630) = some ⟨12, 2, 0, 1417820, 419630, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_419630_1417820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419630 ⟨1417820, by decide⟩ :=
  accepted_of_selected 12 419630 ⟨1417820, by decide⟩ ⟨12, 2, 0, 1417820, 419630, 1749, 65536⟩
    (by decide) selected_cut_49937

theorem selected_cut_49938 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 419631) = some ⟨12, 1, 0, 903806, 419631, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419631_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419631 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 419631 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 419631, 1, 65536⟩
    (by decide) selected_cut_49938

theorem unmarked_context_11_104907_1417821 : frontier 10 ⟨1417821, by decide⟩
    (prefixCache 11 104907) (prefixPartial 11 104907) = false := by
  decide +kernel

theorem node_context_11_104907_1417821 : EJMOriginalGlobalDAGData.nodes 10 ⟨1417821, by decide⟩ =
    .split (coordinate 11) (![⟨1417734, by decide⟩,⟨1417774, by decide⟩,⟨1417820, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104907_1417821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104907 ⟨1417821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104907
    ⟨1417821, by decide⟩ (by decide) (![⟨1417734, by decide⟩,⟨1417774, by decide⟩,⟨1417820, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_104907_1417821 node_context_11_104907_1417821
  intro a
  fin_cases a
  · exact context_12_419628_1417734
  · exact context_12_419629_1417774
  · exact context_12_419630_1417820
  · exact context_12_419631_903806

theorem unmarked_context_10_26226_1417822 : frontier 11 ⟨1417822, by decide⟩
    (prefixCache 10 26226) (prefixPartial 10 26226) = false := by
  decide +kernel

theorem node_context_10_26226_1417822 : EJMOriginalGlobalDAGData.nodes 11 ⟨1417822, by decide⟩ =
    .split (coordinate 10) (![⟨1417515, by decide⟩,⟨1417597, by decide⟩,⟨1417683, by decide⟩,⟨1417821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26226_1417822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26226 ⟨1417822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26226
    ⟨1417822, by decide⟩ (by decide) (![⟨1417515, by decide⟩,⟨1417597, by decide⟩,⟨1417683, by decide⟩,⟨1417821, by decide⟩]) unmarked_context_10_26226_1417822 node_context_10_26226_1417822
  intro a
  fin_cases a
  · exact context_11_104904_1417515
  · exact context_11_104905_1417597
  · exact context_11_104906_1417683
  · exact context_11_104907_1417821

theorem selected_cut_49939 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 419632) = some ⟨12, 1, 0, 1416143, 419632, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419632_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419632 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 419632 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 419632, 1, 65536⟩
    (by decide) selected_cut_49939

theorem selected_cut_49940 : selected 9 ⟨1417869, by decide⟩
    (prefixPartial 12 419633) = some ⟨12, 2, 0, 1417869, 419633, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_419633_1417869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419633 ⟨1417869, by decide⟩ :=
  accepted_of_selected 12 419633 ⟨1417869, by decide⟩ ⟨12, 2, 0, 1417869, 419633, 1505, 65536⟩
    (by decide) selected_cut_49940

theorem selected_cut_49941 : selected 9 ⟨1417924, by decide⟩
    (prefixPartial 12 419634) = some ⟨12, 2, 0, 1417924, 419634, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_419634_1417924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419634 ⟨1417924, by decide⟩ :=
  accepted_of_selected 12 419634 ⟨1417924, by decide⟩ ⟨12, 2, 0, 1417924, 419634, 1641, 65536⟩
    (by decide) selected_cut_49941

theorem selected_cut_49942 : selected 9 ⟨1417971, by decide⟩
    (prefixPartial 12 419635) = some ⟨12, 2, 0, 1417971, 419635, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_419635_1417971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419635 ⟨1417971, by decide⟩ :=
  accepted_of_selected 12 419635 ⟨1417971, by decide⟩ ⟨12, 2, 0, 1417971, 419635, 1605, 65536⟩
    (by decide) selected_cut_49942

theorem unmarked_context_11_104908_1417972 : frontier 10 ⟨1417972, by decide⟩
    (prefixCache 11 104908) (prefixPartial 11 104908) = false := by
  decide +kernel

theorem node_context_11_104908_1417972 : EJMOriginalGlobalDAGData.nodes 10 ⟨1417972, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1417869, by decide⟩,⟨1417924, by decide⟩,⟨1417971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104908_1417972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104908 ⟨1417972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104908
    ⟨1417972, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1417869, by decide⟩,⟨1417924, by decide⟩,⟨1417971, by decide⟩]) unmarked_context_11_104908_1417972 node_context_11_104908_1417972
  intro a
  fin_cases a
  · exact context_12_419632_1416143
  · exact context_12_419633_1417869
  · exact context_12_419634_1417924
  · exact context_12_419635_1417971

theorem selected_cut_49943 : selected 10 ⟨1418050, by decide⟩
    (prefixPartial 11 104909) = some ⟨11, 2, 0, 1418050, 104909, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_104909_1418050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104909 ⟨1418050, by decide⟩ :=
  accepted_of_selected 11 104909 ⟨1418050, by decide⟩ ⟨11, 2, 0, 1418050, 104909, 2657, 262144⟩
    (by decide) selected_cut_49943

theorem selected_cut_49944 : selected 10 ⟨1418181, by decide⟩
    (prefixPartial 11 104910) = some ⟨11, 2, 0, 1418181, 104910, 3765, 262144⟩ := by
  decide +kernel

theorem context_11_104910_1418181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104910 ⟨1418181, by decide⟩ :=
  accepted_of_selected 11 104910 ⟨1418181, by decide⟩ ⟨11, 2, 0, 1418181, 104910, 3765, 262144⟩
    (by decide) selected_cut_49944

theorem selected_cut_49945 : selected 10 ⟨1418183, by decide⟩
    (prefixPartial 11 104911) = some ⟨11, 2, 0, 1418183, 104911, 5, 262144⟩ := by
  decide +kernel

theorem context_11_104911_1418183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104911 ⟨1418183, by decide⟩ :=
  accepted_of_selected 11 104911 ⟨1418183, by decide⟩ ⟨11, 2, 0, 1418183, 104911, 5, 262144⟩
    (by decide) selected_cut_49945

theorem unmarked_context_10_26227_1418184 : frontier 11 ⟨1418184, by decide⟩
    (prefixCache 10 26227) (prefixPartial 10 26227) = false := by
  decide +kernel

theorem node_context_10_26227_1418184 : EJMOriginalGlobalDAGData.nodes 11 ⟨1418184, by decide⟩ =
    .split (coordinate 10) (![⟨1417972, by decide⟩,⟨1418050, by decide⟩,⟨1418181, by decide⟩,⟨1418183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26227_1418184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26227 ⟨1418184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26227
    ⟨1418184, by decide⟩ (by decide) (![⟨1417972, by decide⟩,⟨1418050, by decide⟩,⟨1418181, by decide⟩,⟨1418183, by decide⟩]) unmarked_context_10_26227_1418184 node_context_10_26227_1418184
  intro a
  fin_cases a
  · exact context_11_104908_1417972
  · exact context_11_104909_1418050
  · exact context_11_104910_1418181
  · exact context_11_104911_1418183

theorem unmarked_context_9_6556_1418185 : frontier 12 ⟨1418185, by decide⟩
    (prefixCache 9 6556) (prefixPartial 9 6556) = false := by
  decide +kernel

theorem node_context_9_6556_1418185 : EJMOriginalGlobalDAGData.nodes 12 ⟨1418185, by decide⟩ =
    .split (coordinate 9) (![⟨1416846, by decide⟩,⟨1417339, by decide⟩,⟨1417822, by decide⟩,⟨1418184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6556_1418185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6556 ⟨1418185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6556
    ⟨1418185, by decide⟩ (by decide) (![⟨1416846, by decide⟩,⟨1417339, by decide⟩,⟨1417822, by decide⟩,⟨1418184, by decide⟩]) unmarked_context_9_6556_1418185 node_context_9_6556_1418185
  intro a
  fin_cases a
  · exact context_10_26224_1416846
  · exact context_10_26225_1417339
  · exact context_10_26226_1417822
  · exact context_10_26227_1418184

theorem selected_cut_49946 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 26228) = some ⟨10, 1, 0, 3442, 26228, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26228_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26228 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 26228 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 26228, 1, 1048576⟩
    (by decide) selected_cut_49946

theorem selected_cut_49947 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26229) = some ⟨10, 1, 0, 893098, 26229, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26229_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26229 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26229 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26229, 1, 1048576⟩
    (by decide) selected_cut_49947

theorem selected_cut_49948 : selected 10 ⟨1418299, by decide⟩
    (prefixPartial 11 104920) = some ⟨11, 2, 0, 1418299, 104920, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_104920_1418299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104920 ⟨1418299, by decide⟩ :=
  accepted_of_selected 11 104920 ⟨1418299, by decide⟩ ⟨11, 2, 0, 1418299, 104920, 2837, 262144⟩
    (by decide) selected_cut_49948

theorem selected_cut_49949 : selected 10 ⟨1418370, by decide⟩
    (prefixPartial 11 104921) = some ⟨11, 2, 0, 1418370, 104921, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_104921_1418370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104921 ⟨1418370, by decide⟩ :=
  accepted_of_selected 11 104921 ⟨1418370, by decide⟩ ⟨11, 2, 0, 1418370, 104921, 1917, 262144⟩
    (by decide) selected_cut_49949

theorem selected_cut_49950 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 104922) = some ⟨11, 1, 0, 1369759, 104922, 1, 262144⟩ := by
  decide +kernel

theorem context_11_104922_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104922 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 104922 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 104922, 1, 262144⟩
    (by decide) selected_cut_49950

theorem selected_cut_49951 : selected 10 ⟨1418419, by decide⟩
    (prefixPartial 11 104923) = some ⟨11, 2, 0, 1418419, 104923, 1421, 262144⟩ := by
  decide +kernel

theorem context_11_104923_1418419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104923 ⟨1418419, by decide⟩ :=
  accepted_of_selected 11 104923 ⟨1418419, by decide⟩ ⟨11, 2, 0, 1418419, 104923, 1421, 262144⟩
    (by decide) selected_cut_49951

theorem unmarked_context_10_26230_1418420 : frontier 11 ⟨1418420, by decide⟩
    (prefixCache 10 26230) (prefixPartial 10 26230) = false := by
  decide +kernel

theorem node_context_10_26230_1418420 : EJMOriginalGlobalDAGData.nodes 11 ⟨1418420, by decide⟩ =
    .split (coordinate 10) (![⟨1418299, by decide⟩,⟨1418370, by decide⟩,⟨1369759, by decide⟩,⟨1418419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26230_1418420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26230 ⟨1418420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26230
    ⟨1418420, by decide⟩ (by decide) (![⟨1418299, by decide⟩,⟨1418370, by decide⟩,⟨1369759, by decide⟩,⟨1418419, by decide⟩]) unmarked_context_10_26230_1418420 node_context_10_26230_1418420
  intro a
  fin_cases a
  · exact context_11_104920_1418299
  · exact context_11_104921_1418370
  · exact context_11_104922_1369759
  · exact context_11_104923_1418419

theorem selected_cut_49952 : selected 11 ⟨1418551, by decide⟩
    (prefixPartial 10 26231) = some ⟨10, 2, 0, 1418551, 26231, 3605, 1048576⟩ := by
  decide +kernel

theorem context_10_26231_1418551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26231 ⟨1418551, by decide⟩ :=
  accepted_of_selected 10 26231 ⟨1418551, by decide⟩ ⟨10, 2, 0, 1418551, 26231, 3605, 1048576⟩
    (by decide) selected_cut_49952

theorem unmarked_context_9_6557_1418552 : frontier 12 ⟨1418552, by decide⟩
    (prefixCache 9 6557) (prefixPartial 9 6557) = false := by
  decide +kernel

theorem node_context_9_6557_1418552 : EJMOriginalGlobalDAGData.nodes 12 ⟨1418552, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1418420, by decide⟩,⟨1418551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6557_1418552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6557 ⟨1418552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6557
    ⟨1418552, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1418420, by decide⟩,⟨1418551, by decide⟩]) unmarked_context_9_6557_1418552 node_context_9_6557_1418552
  intro a
  fin_cases a
  · exact context_10_26228_3442
  · exact context_10_26229_893098
  · exact context_10_26230_1418420
  · exact context_10_26231_1418551

theorem selected_cut_49953 : selected 12 ⟨1418667, by decide⟩
    (prefixPartial 9 6558) = some ⟨9, 2, 0, 1418667, 6558, 2017, 4194304⟩ := by
  decide +kernel

theorem context_9_6558_1418667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6558 ⟨1418667, by decide⟩ :=
  accepted_of_selected 9 6558 ⟨1418667, by decide⟩ ⟨9, 2, 0, 1418667, 6558, 2017, 4194304⟩
    (by decide) selected_cut_49953

theorem selected_cut_49954 : selected 12 ⟨1418678, by decide⟩
    (prefixPartial 9 6559) = some ⟨9, 2, 0, 1418678, 6559, 65, 4194304⟩ := by
  decide +kernel

theorem context_9_6559_1418678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6559 ⟨1418678, by decide⟩ :=
  accepted_of_selected 9 6559 ⟨1418678, by decide⟩ ⟨9, 2, 0, 1418678, 6559, 65, 4194304⟩
    (by decide) selected_cut_49954

theorem unmarked_context_8_1639_1418679 : frontier 13 ⟨1418679, by decide⟩
    (prefixCache 8 1639) (prefixPartial 8 1639) = false := by
  decide +kernel

theorem node_context_8_1639_1418679 : EJMOriginalGlobalDAGData.nodes 13 ⟨1418679, by decide⟩ =
    .split (coordinate 8) (![⟨1418185, by decide⟩,⟨1418552, by decide⟩,⟨1418667, by decide⟩,⟨1418678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1639_1418679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1639 ⟨1418679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1639
    ⟨1418679, by decide⟩ (by decide) (![⟨1418185, by decide⟩,⟨1418552, by decide⟩,⟨1418667, by decide⟩,⟨1418678, by decide⟩]) unmarked_context_8_1639_1418679 node_context_8_1639_1418679
  intro a
  fin_cases a
  · exact context_9_6556_1418185
  · exact context_9_6557_1418552
  · exact context_9_6558_1418667
  · exact context_9_6559_1418678

theorem unmarked_context_7_409_1418680 : frontier 14 ⟨1418680, by decide⟩
    (prefixCache 7 409) (prefixPartial 7 409) = false := by
  decide +kernel

theorem node_context_7_409_1418680 : EJMOriginalGlobalDAGData.nodes 14 ⟨1418680, by decide⟩ =
    .split (coordinate 7) (![⟨1364555, by decide⟩,⟨1416683, by decide⟩,⟨1366235, by decide⟩,⟨1418679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_409_1418680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 409 ⟨1418680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 409
    ⟨1418680, by decide⟩ (by decide) (![⟨1364555, by decide⟩,⟨1416683, by decide⟩,⟨1366235, by decide⟩,⟨1418679, by decide⟩]) unmarked_context_7_409_1418680 node_context_7_409_1418680
  intro a
  fin_cases a
  · exact context_8_1636_1364555
  · exact context_8_1637_1416683
  · exact context_8_1638_1366235
  · exact context_8_1639_1418679

theorem selected_cut_49955 : selected 14 ⟨1418683, by decide⟩
    (prefixPartial 7 410) = some ⟨7, 2, 0, 1418683, 410, 5, 67108864⟩ := by
  decide +kernel

theorem context_7_410_1418683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 410 ⟨1418683, by decide⟩ :=
  accepted_of_selected 7 410 ⟨1418683, by decide⟩ ⟨7, 2, 0, 1418683, 410, 5, 67108864⟩
    (by decide) selected_cut_49955

theorem selected_cut_49956 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 1644) = some ⟨8, 1, 0, 1364555, 1644, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1644_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1644 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 1644 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 1644, 1, 16777216⟩
    (by decide) selected_cut_49956

theorem selected_cut_49957 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105280) = some ⟨11, 1, 0, 434745, 105280, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105280_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105280 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105280 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105280, 1, 262144⟩
    (by decide) selected_cut_49957

theorem selected_cut_49958 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105281) = some ⟨11, 1, 0, 434745, 105281, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105281_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105281 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105281 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105281, 1, 262144⟩
    (by decide) selected_cut_49958

theorem selected_cut_49959 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 421128) = some ⟨12, 1, 0, 448748, 421128, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421128_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421128 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 421128 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 421128, 1, 65536⟩
    (by decide) selected_cut_49959

theorem selected_cut_49960 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 421129) = some ⟨12, 1, 0, 448748, 421129, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421129_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421129 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 421129 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 421129, 1, 65536⟩
    (by decide) selected_cut_49960

theorem selected_cut_49961 : selected 9 ⟨1418773, by decide⟩
    (prefixPartial 12 421130) = some ⟨12, 2, 0, 1418773, 421130, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_421130_1418773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421130 ⟨1418773, by decide⟩ :=
  accepted_of_selected 12 421130 ⟨1418773, by decide⟩ ⟨12, 2, 0, 1418773, 421130, 1545, 65536⟩
    (by decide) selected_cut_49961

theorem selected_cut_49962 : selected 9 ⟨1418886, by decide⟩
    (prefixPartial 12 421131) = some ⟨12, 2, 0, 1418886, 421131, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_421131_1418886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421131 ⟨1418886, by decide⟩ :=
  accepted_of_selected 12 421131 ⟨1418886, by decide⟩ ⟨12, 2, 0, 1418886, 421131, 2689, 65536⟩
    (by decide) selected_cut_49962

theorem unmarked_context_11_105282_1418887 : frontier 10 ⟨1418887, by decide⟩
    (prefixCache 11 105282) (prefixPartial 11 105282) = false := by
  decide +kernel

theorem node_context_11_105282_1418887 : EJMOriginalGlobalDAGData.nodes 10 ⟨1418887, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1418773, by decide⟩,⟨1418886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105282_1418887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105282 ⟨1418887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105282
    ⟨1418887, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1418773, by decide⟩,⟨1418886, by decide⟩]) unmarked_context_11_105282_1418887 node_context_11_105282_1418887
  intro a
  fin_cases a
  · exact context_12_421128_448748
  · exact context_12_421129_448748
  · exact context_12_421130_1418773
  · exact context_12_421131_1418886

theorem selected_cut_49963 : selected 10 ⟨1418960, by decide⟩
    (prefixPartial 11 105283) = some ⟨11, 2, 0, 1418960, 105283, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_105283_1418960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105283 ⟨1418960, by decide⟩ :=
  accepted_of_selected 11 105283 ⟨1418960, by decide⟩ ⟨11, 2, 0, 1418960, 105283, 2377, 262144⟩
    (by decide) selected_cut_49963

theorem unmarked_context_10_26320_1418961 : frontier 11 ⟨1418961, by decide⟩
    (prefixCache 10 26320) (prefixPartial 10 26320) = false := by
  decide +kernel

theorem node_context_10_26320_1418961 : EJMOriginalGlobalDAGData.nodes 11 ⟨1418961, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1418887, by decide⟩,⟨1418960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26320_1418961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26320 ⟨1418961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26320
    ⟨1418961, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1418887, by decide⟩,⟨1418960, by decide⟩]) unmarked_context_10_26320_1418961 node_context_10_26320_1418961
  intro a
  fin_cases a
  · exact context_11_105280_434745
  · exact context_11_105281_434745
  · exact context_11_105282_1418887
  · exact context_11_105283_1418960

theorem selected_cut_49964 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 421136) = some ⟨12, 1, 0, 1415033, 421136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421136_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421136 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 421136 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 421136, 1, 65536⟩
    (by decide) selected_cut_49964

theorem selected_cut_49965 : selected 9 ⟨1419026, by decide⟩
    (prefixPartial 12 421137) = some ⟨12, 2, 0, 1419026, 421137, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_421137_1419026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421137 ⟨1419026, by decide⟩ :=
  accepted_of_selected 12 421137 ⟨1419026, by decide⟩ ⟨12, 2, 0, 1419026, 421137, 2185, 65536⟩
    (by decide) selected_cut_49965

theorem selected_cut_49966 : selected 9 ⟨1419089, by decide⟩
    (prefixPartial 12 421138) = some ⟨12, 2, 0, 1419089, 421138, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_421138_1419089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421138 ⟨1419089, by decide⟩ :=
  accepted_of_selected 12 421138 ⟨1419089, by decide⟩ ⟨12, 2, 0, 1419089, 421138, 2121, 65536⟩
    (by decide) selected_cut_49966

theorem selected_cut_49967 : selected 9 ⟨1419158, by decide⟩
    (prefixPartial 12 421139) = some ⟨12, 2, 0, 1419158, 421139, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_421139_1419158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421139 ⟨1419158, by decide⟩ :=
  accepted_of_selected 12 421139 ⟨1419158, by decide⟩ ⟨12, 2, 0, 1419158, 421139, 2289, 65536⟩
    (by decide) selected_cut_49967

theorem unmarked_context_11_105284_1419159 : frontier 10 ⟨1419159, by decide⟩
    (prefixCache 11 105284) (prefixPartial 11 105284) = false := by
  decide +kernel

theorem node_context_11_105284_1419159 : EJMOriginalGlobalDAGData.nodes 10 ⟨1419159, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1419026, by decide⟩,⟨1419089, by decide⟩,⟨1419158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105284_1419159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105284 ⟨1419159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105284
    ⟨1419159, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1419026, by decide⟩,⟨1419089, by decide⟩,⟨1419158, by decide⟩]) unmarked_context_11_105284_1419159 node_context_11_105284_1419159
  intro a
  fin_cases a
  · exact context_12_421136_1415033
  · exact context_12_421137_1419026
  · exact context_12_421138_1419089
  · exact context_12_421139_1419158

theorem selected_cut_49968 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 105285) = some ⟨11, 1, 0, 1241271, 105285, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105285_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105285 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 105285 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 105285, 1, 262144⟩
    (by decide) selected_cut_49968

theorem selected_cut_49969 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 421144) = some ⟨12, 1, 0, 1415033, 421144, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421144_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421144 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 421144 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 421144, 1, 65536⟩
    (by decide) selected_cut_49969

theorem selected_cut_49970 : selected 9 ⟨1419214, by decide⟩
    (prefixPartial 12 421145) = some ⟨12, 2, 0, 1419214, 421145, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_421145_1419214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421145 ⟨1419214, by decide⟩ :=
  accepted_of_selected 12 421145 ⟨1419214, by decide⟩ ⟨12, 2, 0, 1419214, 421145, 1913, 65536⟩
    (by decide) selected_cut_49970

theorem selected_cut_49971 : selected 9 ⟨1415270, by decide⟩
    (prefixPartial 12 421146) = some ⟨12, 1, 0, 1415270, 421146, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421146_1415270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421146 ⟨1415270, by decide⟩ :=
  accepted_of_selected 12 421146 ⟨1415270, by decide⟩ ⟨12, 1, 0, 1415270, 421146, 1, 65536⟩
    (by decide) selected_cut_49971

theorem selected_cut_49972 : selected 9 ⟨1419288, by decide⟩
    (prefixPartial 12 421147) = some ⟨12, 2, 0, 1419288, 421147, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_421147_1419288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421147 ⟨1419288, by decide⟩ :=
  accepted_of_selected 12 421147 ⟨1419288, by decide⟩ ⟨12, 2, 0, 1419288, 421147, 2337, 65536⟩
    (by decide) selected_cut_49972

theorem unmarked_context_11_105286_1419289 : frontier 10 ⟨1419289, by decide⟩
    (prefixCache 11 105286) (prefixPartial 11 105286) = false := by
  decide +kernel

theorem node_context_11_105286_1419289 : EJMOriginalGlobalDAGData.nodes 10 ⟨1419289, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1419214, by decide⟩,⟨1415270, by decide⟩,⟨1419288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105286_1419289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105286 ⟨1419289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105286
    ⟨1419289, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1419214, by decide⟩,⟨1415270, by decide⟩,⟨1419288, by decide⟩]) unmarked_context_11_105286_1419289 node_context_11_105286_1419289
  intro a
  fin_cases a
  · exact context_12_421144_1415033
  · exact context_12_421145_1419214
  · exact context_12_421146_1415270
  · exact context_12_421147_1419288

theorem selected_cut_49973 : selected 10 ⟨1419381, by decide⟩
    (prefixPartial 11 105287) = some ⟨11, 2, 0, 1419381, 105287, 3717, 262144⟩ := by
  decide +kernel

theorem context_11_105287_1419381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105287 ⟨1419381, by decide⟩ :=
  accepted_of_selected 11 105287 ⟨1419381, by decide⟩ ⟨11, 2, 0, 1419381, 105287, 3717, 262144⟩
    (by decide) selected_cut_49973

theorem unmarked_context_10_26321_1419382 : frontier 11 ⟨1419382, by decide⟩
    (prefixCache 10 26321) (prefixPartial 10 26321) = false := by
  decide +kernel

theorem node_context_10_26321_1419382 : EJMOriginalGlobalDAGData.nodes 11 ⟨1419382, by decide⟩ =
    .split (coordinate 10) (![⟨1419159, by decide⟩,⟨1241271, by decide⟩,⟨1419289, by decide⟩,⟨1419381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26321_1419382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26321 ⟨1419382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26321
    ⟨1419382, by decide⟩ (by decide) (![⟨1419159, by decide⟩,⟨1241271, by decide⟩,⟨1419289, by decide⟩,⟨1419381, by decide⟩]) unmarked_context_10_26321_1419382 node_context_10_26321_1419382
  intro a
  fin_cases a
  · exact context_11_105284_1419159
  · exact context_11_105285_1241271
  · exact context_11_105286_1419289
  · exact context_11_105287_1419381

theorem selected_cut_49974 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 421152) = some ⟨12, 1, 0, 435160, 421152, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421152_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421152 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 421152 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 421152, 1, 65536⟩
    (by decide) selected_cut_49974

theorem selected_cut_49975 : selected 9 ⟨1419474, by decide⟩
    (prefixPartial 12 421153) = some ⟨12, 2, 0, 1419474, 421153, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_421153_1419474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421153 ⟨1419474, by decide⟩ :=
  accepted_of_selected 12 421153 ⟨1419474, by decide⟩ ⟨12, 2, 0, 1419474, 421153, 2325, 65536⟩
    (by decide) selected_cut_49975

theorem selected_cut_49976 : selected 9 ⟨1419537, by decide⟩
    (prefixPartial 12 421154) = some ⟨12, 2, 0, 1419537, 421154, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_421154_1419537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421154 ⟨1419537, by decide⟩ :=
  accepted_of_selected 12 421154 ⟨1419537, by decide⟩ ⟨12, 2, 0, 1419537, 421154, 1445, 65536⟩
    (by decide) selected_cut_49976

theorem selected_cut_49977 : selected 9 ⟨1419612, by decide⟩
    (prefixPartial 12 421155) = some ⟨12, 2, 0, 1419612, 421155, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_421155_1419612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421155 ⟨1419612, by decide⟩ :=
  accepted_of_selected 12 421155 ⟨1419612, by decide⟩ ⟨12, 2, 0, 1419612, 421155, 2077, 65536⟩
    (by decide) selected_cut_49977

theorem unmarked_context_11_105288_1419613 : frontier 10 ⟨1419613, by decide⟩
    (prefixCache 11 105288) (prefixPartial 11 105288) = false := by
  decide +kernel

theorem node_context_11_105288_1419613 : EJMOriginalGlobalDAGData.nodes 10 ⟨1419613, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1419474, by decide⟩,⟨1419537, by decide⟩,⟨1419612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105288_1419613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105288 ⟨1419613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105288
    ⟨1419613, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1419474, by decide⟩,⟨1419537, by decide⟩,⟨1419612, by decide⟩]) unmarked_context_11_105288_1419613 node_context_11_105288_1419613
  intro a
  fin_cases a
  · exact context_12_421152_435160
  · exact context_12_421153_1419474
  · exact context_12_421154_1419537
  · exact context_12_421155_1419612

theorem selected_cut_49978 : selected 10 ⟨1419676, by decide⟩
    (prefixPartial 11 105289) = some ⟨11, 2, 0, 1419676, 105289, 1921, 262144⟩ := by
  decide +kernel

theorem context_11_105289_1419676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105289 ⟨1419676, by decide⟩ :=
  accepted_of_selected 11 105289 ⟨1419676, by decide⟩ ⟨11, 2, 0, 1419676, 105289, 1921, 262144⟩
    (by decide) selected_cut_49978

theorem selected_cut_49979 : selected 10 ⟨1419744, by decide⟩
    (prefixPartial 11 105290) = some ⟨11, 2, 0, 1419744, 105290, 1913, 262144⟩ := by
  decide +kernel

theorem context_11_105290_1419744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105290 ⟨1419744, by decide⟩ :=
  accepted_of_selected 11 105290 ⟨1419744, by decide⟩ ⟨11, 2, 0, 1419744, 105290, 1913, 262144⟩
    (by decide) selected_cut_49979

theorem selected_cut_49980 : selected 9 ⟨1419794, by decide⟩
    (prefixPartial 12 421164) = some ⟨12, 2, 0, 1419794, 421164, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_421164_1419794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421164 ⟨1419794, by decide⟩ :=
  accepted_of_selected 12 421164 ⟨1419794, by decide⟩ ⟨12, 2, 0, 1419794, 421164, 1589, 65536⟩
    (by decide) selected_cut_49980

theorem selected_cut_49981 : selected 9 ⟨1419842, by decide⟩
    (prefixPartial 12 421165) = some ⟨12, 2, 0, 1419842, 421165, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_421165_1419842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421165 ⟨1419842, by decide⟩ :=
  accepted_of_selected 12 421165 ⟨1419842, by decide⟩ ⟨12, 2, 0, 1419842, 421165, 1761, 65536⟩
    (by decide) selected_cut_49981

theorem selected_cut_49982 : selected 9 ⟨1419889, by decide⟩
    (prefixPartial 12 421166) = some ⟨12, 2, 0, 1419889, 421166, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_421166_1419889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421166 ⟨1419889, by decide⟩ :=
  accepted_of_selected 12 421166 ⟨1419889, by decide⟩ ⟨12, 2, 0, 1419889, 421166, 1593, 65536⟩
    (by decide) selected_cut_49982

theorem selected_cut_49983 : selected 9 ⟨1419890, by decide⟩
    (prefixPartial 12 421167) = some ⟨12, 1, 0, 1419890, 421167, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421167_1419890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421167 ⟨1419890, by decide⟩ :=
  accepted_of_selected 12 421167 ⟨1419890, by decide⟩ ⟨12, 1, 0, 1419890, 421167, 1, 65536⟩
    (by decide) selected_cut_49983

theorem unmarked_context_11_105291_1419891 : frontier 10 ⟨1419891, by decide⟩
    (prefixCache 11 105291) (prefixPartial 11 105291) = false := by
  decide +kernel

theorem node_context_11_105291_1419891 : EJMOriginalGlobalDAGData.nodes 10 ⟨1419891, by decide⟩ =
    .split (coordinate 11) (![⟨1419794, by decide⟩,⟨1419842, by decide⟩,⟨1419889, by decide⟩,⟨1419890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105291_1419891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105291 ⟨1419891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105291
    ⟨1419891, by decide⟩ (by decide) (![⟨1419794, by decide⟩,⟨1419842, by decide⟩,⟨1419889, by decide⟩,⟨1419890, by decide⟩]) unmarked_context_11_105291_1419891 node_context_11_105291_1419891
  intro a
  fin_cases a
  · exact context_12_421164_1419794
  · exact context_12_421165_1419842
  · exact context_12_421166_1419889
  · exact context_12_421167_1419890

theorem unmarked_context_10_26322_1419892 : frontier 11 ⟨1419892, by decide⟩
    (prefixCache 10 26322) (prefixPartial 10 26322) = false := by
  decide +kernel

theorem node_context_10_26322_1419892 : EJMOriginalGlobalDAGData.nodes 11 ⟨1419892, by decide⟩ =
    .split (coordinate 10) (![⟨1419613, by decide⟩,⟨1419676, by decide⟩,⟨1419744, by decide⟩,⟨1419891, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26322_1419892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26322 ⟨1419892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26322
    ⟨1419892, by decide⟩ (by decide) (![⟨1419613, by decide⟩,⟨1419676, by decide⟩,⟨1419744, by decide⟩,⟨1419891, by decide⟩]) unmarked_context_10_26322_1419892 node_context_10_26322_1419892
  intro a
  fin_cases a
  · exact context_11_105288_1419613
  · exact context_11_105289_1419676
  · exact context_11_105290_1419744
  · exact context_11_105291_1419891

theorem selected_cut_49984 : selected 10 ⟨1420004, by decide⟩
    (prefixPartial 11 105292) = some ⟨11, 2, 0, 1420004, 105292, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_105292_1420004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105292 ⟨1420004, by decide⟩ :=
  accepted_of_selected 11 105292 ⟨1420004, by decide⟩ ⟨11, 2, 0, 1420004, 105292, 3249, 262144⟩
    (by decide) selected_cut_49984

theorem selected_cut_49985 : selected 10 ⟨1420050, by decide⟩
    (prefixPartial 11 105293) = some ⟨11, 2, 0, 1420050, 105293, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_105293_1420050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105293 ⟨1420050, by decide⟩ :=
  accepted_of_selected 11 105293 ⟨1420050, by decide⟩ ⟨11, 2, 0, 1420050, 105293, 1465, 262144⟩
    (by decide) selected_cut_49985

theorem selected_cut_49986 : selected 10 ⟨1420185, by decide⟩
    (prefixPartial 11 105294) = some ⟨11, 2, 0, 1420185, 105294, 3893, 262144⟩ := by
  decide +kernel

theorem context_11_105294_1420185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105294 ⟨1420185, by decide⟩ :=
  accepted_of_selected 11 105294 ⟨1420185, by decide⟩ ⟨11, 2, 0, 1420185, 105294, 3893, 262144⟩
    (by decide) selected_cut_49986

theorem selected_cut_49987 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 105295) = some ⟨11, 1, 0, 977886, 105295, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105295_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105295 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 105295 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 105295, 1, 262144⟩
    (by decide) selected_cut_49987

theorem unmarked_context_10_26323_1420186 : frontier 11 ⟨1420186, by decide⟩
    (prefixCache 10 26323) (prefixPartial 10 26323) = false := by
  decide +kernel

theorem node_context_10_26323_1420186 : EJMOriginalGlobalDAGData.nodes 11 ⟨1420186, by decide⟩ =
    .split (coordinate 10) (![⟨1420004, by decide⟩,⟨1420050, by decide⟩,⟨1420185, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26323_1420186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26323 ⟨1420186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26323
    ⟨1420186, by decide⟩ (by decide) (![⟨1420004, by decide⟩,⟨1420050, by decide⟩,⟨1420185, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26323_1420186 node_context_10_26323_1420186
  intro a
  fin_cases a
  · exact context_11_105292_1420004
  · exact context_11_105293_1420050
  · exact context_11_105294_1420185
  · exact context_11_105295_977886

theorem unmarked_context_9_6580_1420187 : frontier 12 ⟨1420187, by decide⟩
    (prefixCache 9 6580) (prefixPartial 9 6580) = false := by
  decide +kernel

theorem node_context_9_6580_1420187 : EJMOriginalGlobalDAGData.nodes 12 ⟨1420187, by decide⟩ =
    .split (coordinate 9) (![⟨1418961, by decide⟩,⟨1419382, by decide⟩,⟨1419892, by decide⟩,⟨1420186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6580_1420187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6580 ⟨1420187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6580
    ⟨1420187, by decide⟩ (by decide) (![⟨1418961, by decide⟩,⟨1419382, by decide⟩,⟨1419892, by decide⟩,⟨1420186, by decide⟩]) unmarked_context_9_6580_1420187 node_context_9_6580_1420187
  intro a
  fin_cases a
  · exact context_10_26320_1418961
  · exact context_10_26321_1419382
  · exact context_10_26322_1419892
  · exact context_10_26323_1420186

theorem selected_cut_49988 : selected 10 ⟨1420188, by decide⟩
    (prefixPartial 11 105296) = some ⟨11, 2, 0, 1420188, 105296, 5, 262144⟩ := by
  decide +kernel

theorem context_11_105296_1420188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105296 ⟨1420188, by decide⟩ :=
  accepted_of_selected 11 105296 ⟨1420188, by decide⟩ ⟨11, 2, 0, 1420188, 105296, 5, 262144⟩
    (by decide) selected_cut_49988

theorem selected_cut_49989 : selected 10 ⟨1420272, by decide⟩
    (prefixPartial 11 105297) = some ⟨11, 2, 0, 1420272, 105297, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_105297_1420272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105297 ⟨1420272, by decide⟩ :=
  accepted_of_selected 11 105297 ⟨1420272, by decide⟩ ⟨11, 2, 0, 1420272, 105297, 2169, 262144⟩
    (by decide) selected_cut_49989

theorem selected_cut_49990 : selected 10 ⟨1420360, by decide⟩
    (prefixPartial 11 105298) = some ⟨11, 2, 0, 1420360, 105298, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_105298_1420360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105298 ⟨1420360, by decide⟩ :=
  accepted_of_selected 11 105298 ⟨1420360, by decide⟩ ⟨11, 2, 0, 1420360, 105298, 2369, 262144⟩
    (by decide) selected_cut_49990

theorem selected_cut_49991 : selected 10 ⟨1420390, by decide⟩
    (prefixPartial 11 105299) = some ⟨11, 2, 0, 1420390, 105299, 969, 262144⟩ := by
  decide +kernel

theorem context_11_105299_1420390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105299 ⟨1420390, by decide⟩ :=
  accepted_of_selected 11 105299 ⟨1420390, by decide⟩ ⟨11, 2, 0, 1420390, 105299, 969, 262144⟩
    (by decide) selected_cut_49991

theorem unmarked_context_10_26324_1420391 : frontier 11 ⟨1420391, by decide⟩
    (prefixCache 10 26324) (prefixPartial 10 26324) = false := by
  decide +kernel

theorem node_context_10_26324_1420391 : EJMOriginalGlobalDAGData.nodes 11 ⟨1420391, by decide⟩ =
    .split (coordinate 10) (![⟨1420188, by decide⟩,⟨1420272, by decide⟩,⟨1420360, by decide⟩,⟨1420390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26324_1420391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26324 ⟨1420391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26324
    ⟨1420391, by decide⟩ (by decide) (![⟨1420188, by decide⟩,⟨1420272, by decide⟩,⟨1420360, by decide⟩,⟨1420390, by decide⟩]) unmarked_context_10_26324_1420391 node_context_10_26324_1420391
  intro a
  fin_cases a
  · exact context_11_105296_1420188
  · exact context_11_105297_1420272
  · exact context_11_105298_1420360
  · exact context_11_105299_1420390

theorem selected_cut_49992 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26325) = some ⟨10, 1, 0, 893098, 26325, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26325_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26325 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26325 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26325, 1, 1048576⟩
    (by decide) selected_cut_49992

theorem selected_cut_49993 : selected 10 ⟨1420451, by decide⟩
    (prefixPartial 11 105304) = some ⟨11, 2, 0, 1420451, 105304, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_105304_1420451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105304 ⟨1420451, by decide⟩ :=
  accepted_of_selected 11 105304 ⟨1420451, by decide⟩ ⟨11, 2, 0, 1420451, 105304, 1101, 262144⟩
    (by decide) selected_cut_49993

theorem selected_cut_49994 : selected 10 ⟨1420524, by decide⟩
    (prefixPartial 11 105305) = some ⟨11, 2, 0, 1420524, 105305, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_105305_1420524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105305 ⟨1420524, by decide⟩ :=
  accepted_of_selected 11 105305 ⟨1420524, by decide⟩ ⟨11, 2, 0, 1420524, 105305, 1661, 262144⟩
    (by decide) selected_cut_49994

theorem selected_cut_49995 : selected 10 ⟨1420557, by decide⟩
    (prefixPartial 11 105306) = some ⟨11, 2, 0, 1420557, 105306, 849, 262144⟩ := by
  decide +kernel

theorem context_11_105306_1420557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105306 ⟨1420557, by decide⟩ :=
  accepted_of_selected 11 105306 ⟨1420557, by decide⟩ ⟨11, 2, 0, 1420557, 105306, 849, 262144⟩
    (by decide) selected_cut_49995

theorem selected_cut_49996 : selected 10 ⟨1420586, by decide⟩
    (prefixPartial 11 105307) = some ⟨11, 2, 0, 1420586, 105307, 725, 262144⟩ := by
  decide +kernel

theorem context_11_105307_1420586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105307 ⟨1420586, by decide⟩ :=
  accepted_of_selected 11 105307 ⟨1420586, by decide⟩ ⟨11, 2, 0, 1420586, 105307, 725, 262144⟩
    (by decide) selected_cut_49996

theorem unmarked_context_10_26326_1420587 : frontier 11 ⟨1420587, by decide⟩
    (prefixCache 10 26326) (prefixPartial 10 26326) = false := by
  decide +kernel

theorem node_context_10_26326_1420587 : EJMOriginalGlobalDAGData.nodes 11 ⟨1420587, by decide⟩ =
    .split (coordinate 10) (![⟨1420451, by decide⟩,⟨1420524, by decide⟩,⟨1420557, by decide⟩,⟨1420586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26326_1420587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26326 ⟨1420587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26326
    ⟨1420587, by decide⟩ (by decide) (![⟨1420451, by decide⟩,⟨1420524, by decide⟩,⟨1420557, by decide⟩,⟨1420586, by decide⟩]) unmarked_context_10_26326_1420587 node_context_10_26326_1420587
  intro a
  fin_cases a
  · exact context_11_105304_1420451
  · exact context_11_105305_1420524
  · exact context_11_105306_1420557
  · exact context_11_105307_1420586

theorem selected_cut_49997 : selected 11 ⟨1420742, by decide⟩
    (prefixPartial 10 26327) = some ⟨10, 2, 0, 1420742, 26327, 3621, 1048576⟩ := by
  decide +kernel

theorem context_10_26327_1420742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26327 ⟨1420742, by decide⟩ :=
  accepted_of_selected 10 26327 ⟨1420742, by decide⟩ ⟨10, 2, 0, 1420742, 26327, 3621, 1048576⟩
    (by decide) selected_cut_49997

theorem unmarked_context_9_6581_1420743 : frontier 12 ⟨1420743, by decide⟩
    (prefixCache 9 6581) (prefixPartial 9 6581) = false := by
  decide +kernel

theorem node_context_9_6581_1420743 : EJMOriginalGlobalDAGData.nodes 12 ⟨1420743, by decide⟩ =
    .split (coordinate 9) (![⟨1420391, by decide⟩,⟨893098, by decide⟩,⟨1420587, by decide⟩,⟨1420742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6581_1420743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6581 ⟨1420743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6581
    ⟨1420743, by decide⟩ (by decide) (![⟨1420391, by decide⟩,⟨893098, by decide⟩,⟨1420587, by decide⟩,⟨1420742, by decide⟩]) unmarked_context_9_6581_1420743 node_context_9_6581_1420743
  intro a
  fin_cases a
  · exact context_10_26324_1420391
  · exact context_10_26325_893098
  · exact context_10_26326_1420587
  · exact context_10_26327_1420742

theorem selected_cut_49998 : selected 11 ⟨1420859, by decide⟩
    (prefixPartial 10 26328) = some ⟨10, 2, 0, 1420859, 26328, 2457, 1048576⟩ := by
  decide +kernel

theorem context_10_26328_1420859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26328 ⟨1420859, by decide⟩ :=
  accepted_of_selected 10 26328 ⟨1420859, by decide⟩ ⟨10, 2, 0, 1420859, 26328, 2457, 1048576⟩
    (by decide) selected_cut_49998

theorem selected_cut_49999 : selected 11 ⟨1420910, by decide⟩
    (prefixPartial 10 26329) = some ⟨10, 2, 0, 1420910, 26329, 1045, 1048576⟩ := by
  decide +kernel

theorem context_10_26329_1420910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26329 ⟨1420910, by decide⟩ :=
  accepted_of_selected 10 26329 ⟨1420910, by decide⟩ ⟨10, 2, 0, 1420910, 26329, 1045, 1048576⟩
    (by decide) selected_cut_49999

theorem selected_cut_50000 : selected 11 ⟨1420948, by decide⟩
    (prefixPartial 10 26330) = some ⟨10, 2, 0, 1420948, 26330, 565, 1048576⟩ := by
  decide +kernel

theorem context_10_26330_1420948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26330 ⟨1420948, by decide⟩ :=
  accepted_of_selected 10 26330 ⟨1420948, by decide⟩ ⟨10, 2, 0, 1420948, 26330, 565, 1048576⟩
    (by decide) selected_cut_50000

theorem selected_cut_50001 : selected 11 ⟨1420976, by decide⟩
    (prefixPartial 10 26331) = some ⟨10, 2, 0, 1420976, 26331, 513, 1048576⟩ := by
  decide +kernel

theorem context_10_26331_1420976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26331 ⟨1420976, by decide⟩ :=
  accepted_of_selected 10 26331 ⟨1420976, by decide⟩ ⟨10, 2, 0, 1420976, 26331, 513, 1048576⟩
    (by decide) selected_cut_50001

theorem unmarked_context_9_6582_1420977 : frontier 12 ⟨1420977, by decide⟩
    (prefixCache 9 6582) (prefixPartial 9 6582) = false := by
  decide +kernel

theorem node_context_9_6582_1420977 : EJMOriginalGlobalDAGData.nodes 12 ⟨1420977, by decide⟩ =
    .split (coordinate 9) (![⟨1420859, by decide⟩,⟨1420910, by decide⟩,⟨1420948, by decide⟩,⟨1420976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6582_1420977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6582 ⟨1420977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6582
    ⟨1420977, by decide⟩ (by decide) (![⟨1420859, by decide⟩,⟨1420910, by decide⟩,⟨1420948, by decide⟩,⟨1420976, by decide⟩]) unmarked_context_9_6582_1420977 node_context_9_6582_1420977
  intro a
  fin_cases a
  · exact context_10_26328_1420859
  · exact context_10_26329_1420910
  · exact context_10_26330_1420948
  · exact context_10_26331_1420976

theorem selected_cut_50002 : selected 12 ⟨1420999, by decide⟩
    (prefixPartial 9 6583) = some ⟨9, 2, 0, 1420999, 6583, 201, 4194304⟩ := by
  decide +kernel

theorem context_9_6583_1420999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6583 ⟨1420999, by decide⟩ :=
  accepted_of_selected 9 6583 ⟨1420999, by decide⟩ ⟨9, 2, 0, 1420999, 6583, 201, 4194304⟩
    (by decide) selected_cut_50002

theorem unmarked_context_8_1645_1421000 : frontier 13 ⟨1421000, by decide⟩
    (prefixCache 8 1645) (prefixPartial 8 1645) = false := by
  decide +kernel

theorem node_context_8_1645_1421000 : EJMOriginalGlobalDAGData.nodes 13 ⟨1421000, by decide⟩ =
    .split (coordinate 8) (![⟨1420187, by decide⟩,⟨1420743, by decide⟩,⟨1420977, by decide⟩,⟨1420999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1645_1421000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1645 ⟨1421000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1645
    ⟨1421000, by decide⟩ (by decide) (![⟨1420187, by decide⟩,⟨1420743, by decide⟩,⟨1420977, by decide⟩,⟨1420999, by decide⟩]) unmarked_context_8_1645_1421000 node_context_8_1645_1421000
  intro a
  fin_cases a
  · exact context_9_6580_1420187
  · exact context_9_6581_1420743
  · exact context_9_6582_1420977
  · exact context_9_6583_1420999

theorem selected_cut_50003 : selected 13 ⟨1366235, by decide⟩
    (prefixPartial 8 1646) = some ⟨8, 1, 0, 1366235, 1646, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1646_1366235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1646 ⟨1366235, by decide⟩ :=
  accepted_of_selected 8 1646 ⟨1366235, by decide⟩ ⟨8, 1, 0, 1366235, 1646, 1, 16777216⟩
    (by decide) selected_cut_50003

theorem selected_cut_50004 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105408) = some ⟨11, 1, 0, 434745, 105408, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105408_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105408 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105408 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105408, 1, 262144⟩
    (by decide) selected_cut_50004

theorem selected_cut_50005 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105409) = some ⟨11, 1, 0, 434745, 105409, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105409_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105409 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105409 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105409, 1, 262144⟩
    (by decide) selected_cut_50005

theorem selected_cut_50006 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 421640) = some ⟨12, 1, 0, 448748, 421640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421640_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421640 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 421640 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 421640, 1, 65536⟩
    (by decide) selected_cut_50006

theorem selected_cut_50007 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 421641) = some ⟨12, 1, 0, 448748, 421641, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421641_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421641 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 421641 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 421641, 1, 65536⟩
    (by decide) selected_cut_50007

theorem selected_cut_50008 : selected 9 ⟨1421117, by decide⟩
    (prefixPartial 12 421642) = some ⟨12, 2, 0, 1421117, 421642, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_421642_1421117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421642 ⟨1421117, by decide⟩ :=
  accepted_of_selected 12 421642 ⟨1421117, by decide⟩ ⟨12, 2, 0, 1421117, 421642, 1805, 65536⟩
    (by decide) selected_cut_50008

theorem selected_cut_50009 : selected 9 ⟨1421205, by decide⟩
    (prefixPartial 12 421643) = some ⟨12, 2, 0, 1421205, 421643, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_421643_1421205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421643 ⟨1421205, by decide⟩ :=
  accepted_of_selected 12 421643 ⟨1421205, by decide⟩ ⟨12, 2, 0, 1421205, 421643, 2829, 65536⟩
    (by decide) selected_cut_50009

theorem unmarked_context_11_105410_1421206 : frontier 10 ⟨1421206, by decide⟩
    (prefixCache 11 105410) (prefixPartial 11 105410) = false := by
  decide +kernel

theorem node_context_11_105410_1421206 : EJMOriginalGlobalDAGData.nodes 10 ⟨1421206, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1421117, by decide⟩,⟨1421205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105410_1421206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105410 ⟨1421206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105410
    ⟨1421206, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1421117, by decide⟩,⟨1421205, by decide⟩]) unmarked_context_11_105410_1421206 node_context_11_105410_1421206
  intro a
  fin_cases a
  · exact context_12_421640_448748
  · exact context_12_421641_448748
  · exact context_12_421642_1421117
  · exact context_12_421643_1421205

theorem selected_cut_50010 : selected 10 ⟨1421291, by decide⟩
    (prefixPartial 11 105411) = some ⟨11, 2, 0, 1421291, 105411, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_105411_1421291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105411 ⟨1421291, by decide⟩ :=
  accepted_of_selected 11 105411 ⟨1421291, by decide⟩ ⟨11, 2, 0, 1421291, 105411, 2649, 262144⟩
    (by decide) selected_cut_50010

theorem unmarked_context_10_26352_1421292 : frontier 11 ⟨1421292, by decide⟩
    (prefixCache 10 26352) (prefixPartial 10 26352) = false := by
  decide +kernel

theorem node_context_10_26352_1421292 : EJMOriginalGlobalDAGData.nodes 11 ⟨1421292, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1421206, by decide⟩,⟨1421291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26352_1421292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26352 ⟨1421292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26352
    ⟨1421292, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1421206, by decide⟩,⟨1421291, by decide⟩]) unmarked_context_10_26352_1421292 node_context_10_26352_1421292
  intro a
  fin_cases a
  · exact context_11_105408_434745
  · exact context_11_105409_434745
  · exact context_11_105410_1421206
  · exact context_11_105411_1421291

theorem selected_cut_50011 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 421648) = some ⟨12, 1, 0, 1415033, 421648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421648_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421648 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 421648 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 421648, 1, 65536⟩
    (by decide) selected_cut_50011

theorem selected_cut_50012 : selected 9 ⟨1421377, by decide⟩
    (prefixPartial 12 421649) = some ⟨12, 2, 0, 1421377, 421649, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_421649_1421377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421649 ⟨1421377, by decide⟩ :=
  accepted_of_selected 12 421649 ⟨1421377, by decide⟩ ⟨12, 2, 0, 1421377, 421649, 2945, 65536⟩
    (by decide) selected_cut_50012

theorem selected_cut_50013 : selected 9 ⟨1421468, by decide⟩
    (prefixPartial 12 421650) = some ⟨12, 2, 0, 1421468, 421650, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_421650_1421468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421650 ⟨1421468, by decide⟩ :=
  accepted_of_selected 12 421650 ⟨1421468, by decide⟩ ⟨12, 2, 0, 1421468, 421650, 3069, 65536⟩
    (by decide) selected_cut_50013

theorem selected_cut_50014 : selected 9 ⟨1421561, by decide⟩
    (prefixPartial 12 421651) = some ⟨12, 2, 0, 1421561, 421651, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_421651_1421561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421651 ⟨1421561, by decide⟩ :=
  accepted_of_selected 12 421651 ⟨1421561, by decide⟩ ⟨12, 2, 0, 1421561, 421651, 3301, 65536⟩
    (by decide) selected_cut_50014

theorem unmarked_context_11_105412_1421562 : frontier 10 ⟨1421562, by decide⟩
    (prefixCache 11 105412) (prefixPartial 11 105412) = false := by
  decide +kernel

theorem node_context_11_105412_1421562 : EJMOriginalGlobalDAGData.nodes 10 ⟨1421562, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1421377, by decide⟩,⟨1421468, by decide⟩,⟨1421561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105412_1421562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105412 ⟨1421562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105412
    ⟨1421562, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1421377, by decide⟩,⟨1421468, by decide⟩,⟨1421561, by decide⟩]) unmarked_context_11_105412_1421562 node_context_11_105412_1421562
  intro a
  fin_cases a
  · exact context_12_421648_1415033
  · exact context_12_421649_1421377
  · exact context_12_421650_1421468
  · exact context_12_421651_1421561

theorem selected_cut_50015 : selected 10 ⟨1241271, by decide⟩
    (prefixPartial 11 105413) = some ⟨11, 1, 0, 1241271, 105413, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105413_1241271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105413 ⟨1241271, by decide⟩ :=
  accepted_of_selected 11 105413 ⟨1241271, by decide⟩ ⟨11, 1, 0, 1241271, 105413, 1, 262144⟩
    (by decide) selected_cut_50015

theorem selected_cut_50016 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 421656) = some ⟨12, 1, 0, 1415033, 421656, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421656_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421656 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 421656 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 421656, 1, 65536⟩
    (by decide) selected_cut_50016

theorem selected_cut_50017 : selected 9 ⟨1421655, by decide⟩
    (prefixPartial 12 421657) = some ⟨12, 2, 0, 1421655, 421657, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_421657_1421655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421657 ⟨1421655, by decide⟩ :=
  accepted_of_selected 12 421657 ⟨1421655, by decide⟩ ⟨12, 2, 0, 1421655, 421657, 2841, 65536⟩
    (by decide) selected_cut_50017

theorem selected_cut_50018 : selected 9 ⟨1376651, by decide⟩
    (prefixPartial 12 421658) = some ⟨12, 1, 0, 1376651, 421658, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421658_1376651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421658 ⟨1376651, by decide⟩ :=
  accepted_of_selected 12 421658 ⟨1376651, by decide⟩ ⟨12, 1, 0, 1376651, 421658, 1, 65536⟩
    (by decide) selected_cut_50018

theorem selected_cut_50019 : selected 9 ⟨1421781, by decide⟩
    (prefixPartial 12 421659) = some ⟨12, 2, 0, 1421781, 421659, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_421659_1421781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421659 ⟨1421781, by decide⟩ :=
  accepted_of_selected 12 421659 ⟨1421781, by decide⟩ ⟨12, 2, 0, 1421781, 421659, 2197, 65536⟩
    (by decide) selected_cut_50019

theorem unmarked_context_11_105414_1421782 : frontier 10 ⟨1421782, by decide⟩
    (prefixCache 11 105414) (prefixPartial 11 105414) = false := by
  decide +kernel

theorem node_context_11_105414_1421782 : EJMOriginalGlobalDAGData.nodes 10 ⟨1421782, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1421655, by decide⟩,⟨1376651, by decide⟩,⟨1421781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105414_1421782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105414 ⟨1421782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105414
    ⟨1421782, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1421655, by decide⟩,⟨1376651, by decide⟩,⟨1421781, by decide⟩]) unmarked_context_11_105414_1421782 node_context_11_105414_1421782
  intro a
  fin_cases a
  · exact context_12_421656_1415033
  · exact context_12_421657_1421655
  · exact context_12_421658_1376651
  · exact context_12_421659_1421781

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
