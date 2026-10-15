/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover318
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30627 : selected 8 ⟨778027, by decide⟩
    (prefixPartial 13 419910) = some ⟨13, 2, 0, 778027, 419910, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_419910_778027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419910 ⟨778027, by decide⟩ :=
  accepted_of_selected 13 419910 ⟨778027, by decide⟩ ⟨13, 2, 0, 778027, 419910, 1349, 16384⟩
    (by decide) selected_cut_30627

theorem selected_cut_30628 : selected 8 ⟨778056, by decide⟩
    (prefixPartial 13 419911) = some ⟨13, 2, 0, 778056, 419911, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_419911_778056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419911 ⟨778056, by decide⟩ :=
  accepted_of_selected 13 419911 ⟨778056, by decide⟩ ⟨13, 2, 0, 778056, 419911, 1137, 16384⟩
    (by decide) selected_cut_30628

theorem unmarked_context_12_104977_778057 : frontier 9 ⟨778057, by decide⟩
    (prefixCache 12 104977) (prefixPartial 12 104977) = false := by
  decide +kernel

theorem node_context_12_104977_778057 : EJMOriginalGlobalDAGData.nodes 9 ⟨778057, by decide⟩ =
    .split (coordinate 12) (![⟨777957, by decide⟩,⟨777996, by decide⟩,⟨778027, by decide⟩,⟨778056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104977_778057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104977 ⟨778057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104977
    ⟨778057, by decide⟩ (by decide) (![⟨777957, by decide⟩,⟨777996, by decide⟩,⟨778027, by decide⟩,⟨778056, by decide⟩]) unmarked_context_12_104977_778057 node_context_12_104977_778057
  intro a
  fin_cases a
  · exact context_13_419908_777957
  · exact context_13_419909_777996
  · exact context_13_419910_778027
  · exact context_13_419911_778056

theorem selected_cut_30629 : selected 8 ⟨778097, by decide⟩
    (prefixPartial 13 419912) = some ⟨13, 2, 0, 778097, 419912, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_419912_778097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419912 ⟨778097, by decide⟩ :=
  accepted_of_selected 13 419912 ⟨778097, by decide⟩ ⟨13, 2, 0, 778097, 419912, 2245, 16384⟩
    (by decide) selected_cut_30629

theorem selected_cut_30630 : selected 8 ⟨778120, by decide⟩
    (prefixPartial 13 419913) = some ⟨13, 2, 0, 778120, 419913, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_419913_778120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419913 ⟨778120, by decide⟩ :=
  accepted_of_selected 13 419913 ⟨778120, by decide⟩ ⟨13, 2, 0, 778120, 419913, 2089, 16384⟩
    (by decide) selected_cut_30630

theorem selected_cut_30631 : selected 8 ⟨778142, by decide⟩
    (prefixPartial 13 419914) = some ⟨13, 2, 0, 778142, 419914, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_419914_778142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419914 ⟨778142, by decide⟩ :=
  accepted_of_selected 13 419914 ⟨778142, by decide⟩ ⟨13, 2, 0, 778142, 419914, 1081, 16384⟩
    (by decide) selected_cut_30631

theorem selected_cut_30632 : selected 8 ⟨778153, by decide⟩
    (prefixPartial 13 419915) = some ⟨13, 2, 0, 778153, 419915, 993, 16384⟩ := by
  decide +kernel

theorem context_13_419915_778153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419915 ⟨778153, by decide⟩ :=
  accepted_of_selected 13 419915 ⟨778153, by decide⟩ ⟨13, 2, 0, 778153, 419915, 993, 16384⟩
    (by decide) selected_cut_30632

theorem unmarked_context_12_104978_778154 : frontier 9 ⟨778154, by decide⟩
    (prefixCache 12 104978) (prefixPartial 12 104978) = false := by
  decide +kernel

theorem node_context_12_104978_778154 : EJMOriginalGlobalDAGData.nodes 9 ⟨778154, by decide⟩ =
    .split (coordinate 12) (![⟨778097, by decide⟩,⟨778120, by decide⟩,⟨778142, by decide⟩,⟨778153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104978_778154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104978 ⟨778154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104978
    ⟨778154, by decide⟩ (by decide) (![⟨778097, by decide⟩,⟨778120, by decide⟩,⟨778142, by decide⟩,⟨778153, by decide⟩]) unmarked_context_12_104978_778154 node_context_12_104978_778154
  intro a
  fin_cases a
  · exact context_13_419912_778097
  · exact context_13_419913_778120
  · exact context_13_419914_778142
  · exact context_13_419915_778153

theorem selected_cut_30633 : selected 8 ⟨778212, by decide⟩
    (prefixPartial 13 419916) = some ⟨13, 2, 0, 778212, 419916, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_419916_778212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419916 ⟨778212, by decide⟩ :=
  accepted_of_selected 13 419916 ⟨778212, by decide⟩ ⟨13, 2, 0, 778212, 419916, 2777, 16384⟩
    (by decide) selected_cut_30633

theorem selected_cut_30634 : selected 8 ⟨778249, by decide⟩
    (prefixPartial 13 419917) = some ⟨13, 2, 0, 778249, 419917, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_419917_778249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419917 ⟨778249, by decide⟩ :=
  accepted_of_selected 13 419917 ⟨778249, by decide⟩ ⟨13, 2, 0, 778249, 419917, 2557, 16384⟩
    (by decide) selected_cut_30634

theorem selected_cut_30635 : selected 8 ⟨778277, by decide⟩
    (prefixPartial 13 419918) = some ⟨13, 2, 0, 778277, 419918, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_419918_778277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419918 ⟨778277, by decide⟩ :=
  accepted_of_selected 13 419918 ⟨778277, by decide⟩ ⟨13, 2, 0, 778277, 419918, 1445, 16384⟩
    (by decide) selected_cut_30635

theorem selected_cut_30636 : selected 8 ⟨778296, by decide⟩
    (prefixPartial 13 419919) = some ⟨13, 2, 0, 778296, 419919, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_419919_778296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419919 ⟨778296, by decide⟩ :=
  accepted_of_selected 13 419919 ⟨778296, by decide⟩ ⟨13, 2, 0, 778296, 419919, 1069, 16384⟩
    (by decide) selected_cut_30636

theorem unmarked_context_12_104979_778297 : frontier 9 ⟨778297, by decide⟩
    (prefixCache 12 104979) (prefixPartial 12 104979) = false := by
  decide +kernel

theorem node_context_12_104979_778297 : EJMOriginalGlobalDAGData.nodes 9 ⟨778297, by decide⟩ =
    .split (coordinate 12) (![⟨778212, by decide⟩,⟨778249, by decide⟩,⟨778277, by decide⟩,⟨778296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104979_778297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104979 ⟨778297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104979
    ⟨778297, by decide⟩ (by decide) (![⟨778212, by decide⟩,⟨778249, by decide⟩,⟨778277, by decide⟩,⟨778296, by decide⟩]) unmarked_context_12_104979_778297 node_context_12_104979_778297
  intro a
  fin_cases a
  · exact context_13_419916_778212
  · exact context_13_419917_778249
  · exact context_13_419918_778277
  · exact context_13_419919_778296

theorem unmarked_context_11_26244_778298 : frontier 10 ⟨778298, by decide⟩
    (prefixCache 11 26244) (prefixPartial 11 26244) = false := by
  decide +kernel

theorem node_context_11_26244_778298 : EJMOriginalGlobalDAGData.nodes 10 ⟨778298, by decide⟩ =
    .split (coordinate 11) (![⟨777901, by decide⟩,⟨778057, by decide⟩,⟨778154, by decide⟩,⟨778297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26244_778298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26244 ⟨778298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26244
    ⟨778298, by decide⟩ (by decide) (![⟨777901, by decide⟩,⟨778057, by decide⟩,⟨778154, by decide⟩,⟨778297, by decide⟩]) unmarked_context_11_26244_778298 node_context_11_26244_778298
  intro a
  fin_cases a
  · exact context_12_104976_777901
  · exact context_12_104977_778057
  · exact context_12_104978_778154
  · exact context_12_104979_778297

theorem selected_cut_30637 : selected 8 ⟨778328, by decide⟩
    (prefixPartial 13 419920) = some ⟨13, 2, 0, 778328, 419920, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_419920_778328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419920 ⟨778328, by decide⟩ :=
  accepted_of_selected 13 419920 ⟨778328, by decide⟩ ⟨13, 2, 0, 778328, 419920, 1773, 16384⟩
    (by decide) selected_cut_30637

theorem selected_cut_30638 : selected 8 ⟨778353, by decide⟩
    (prefixPartial 13 419921) = some ⟨13, 2, 0, 778353, 419921, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_419921_778353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419921 ⟨778353, by decide⟩ :=
  accepted_of_selected 13 419921 ⟨778353, by decide⟩ ⟨13, 2, 0, 778353, 419921, 2061, 16384⟩
    (by decide) selected_cut_30638

theorem selected_cut_30639 : selected 8 ⟨778374, by decide⟩
    (prefixPartial 13 419922) = some ⟨13, 2, 0, 778374, 419922, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_419922_778374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419922 ⟨778374, by decide⟩ :=
  accepted_of_selected 13 419922 ⟨778374, by decide⟩ ⟨13, 2, 0, 778374, 419922, 1109, 16384⟩
    (by decide) selected_cut_30639

theorem selected_cut_30640 : selected 8 ⟨778390, by decide⟩
    (prefixPartial 13 419923) = some ⟨13, 2, 0, 778390, 419923, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_419923_778390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419923 ⟨778390, by decide⟩ :=
  accepted_of_selected 13 419923 ⟨778390, by decide⟩ ⟨13, 2, 0, 778390, 419923, 1009, 16384⟩
    (by decide) selected_cut_30640

theorem unmarked_context_12_104980_778391 : frontier 9 ⟨778391, by decide⟩
    (prefixCache 12 104980) (prefixPartial 12 104980) = false := by
  decide +kernel

theorem node_context_12_104980_778391 : EJMOriginalGlobalDAGData.nodes 9 ⟨778391, by decide⟩ =
    .split (coordinate 12) (![⟨778328, by decide⟩,⟨778353, by decide⟩,⟨778374, by decide⟩,⟨778390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104980_778391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104980 ⟨778391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104980
    ⟨778391, by decide⟩ (by decide) (![⟨778328, by decide⟩,⟨778353, by decide⟩,⟨778374, by decide⟩,⟨778390, by decide⟩]) unmarked_context_12_104980_778391 node_context_12_104980_778391
  intro a
  fin_cases a
  · exact context_13_419920_778328
  · exact context_13_419921_778353
  · exact context_13_419922_778374
  · exact context_13_419923_778390

theorem selected_cut_30641 : selected 8 ⟨778432, by decide⟩
    (prefixPartial 13 419924) = some ⟨13, 2, 0, 778432, 419924, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_419924_778432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419924 ⟨778432, by decide⟩ :=
  accepted_of_selected 13 419924 ⟨778432, by decide⟩ ⟨13, 2, 0, 778432, 419924, 2169, 16384⟩
    (by decide) selected_cut_30641

theorem selected_cut_30642 : selected 8 ⟨778462, by decide⟩
    (prefixPartial 13 419925) = some ⟨13, 2, 0, 778462, 419925, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_419925_778462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419925 ⟨778462, by decide⟩ :=
  accepted_of_selected 13 419925 ⟨778462, by decide⟩ ⟨13, 2, 0, 778462, 419925, 2081, 16384⟩
    (by decide) selected_cut_30642

theorem selected_cut_30643 : selected 8 ⟨778484, by decide⟩
    (prefixPartial 13 419926) = some ⟨13, 2, 0, 778484, 419926, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_419926_778484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419926 ⟨778484, by decide⟩ :=
  accepted_of_selected 13 419926 ⟨778484, by decide⟩ ⟨13, 2, 0, 778484, 419926, 1125, 16384⟩
    (by decide) selected_cut_30643

theorem selected_cut_30644 : selected 8 ⟨778497, by decide⟩
    (prefixPartial 13 419927) = some ⟨13, 2, 0, 778497, 419927, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_419927_778497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419927 ⟨778497, by decide⟩ :=
  accepted_of_selected 13 419927 ⟨778497, by decide⟩ ⟨13, 2, 0, 778497, 419927, 1033, 16384⟩
    (by decide) selected_cut_30644

theorem unmarked_context_12_104981_778498 : frontier 9 ⟨778498, by decide⟩
    (prefixCache 12 104981) (prefixPartial 12 104981) = false := by
  decide +kernel

theorem node_context_12_104981_778498 : EJMOriginalGlobalDAGData.nodes 9 ⟨778498, by decide⟩ =
    .split (coordinate 12) (![⟨778432, by decide⟩,⟨778462, by decide⟩,⟨778484, by decide⟩,⟨778497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104981_778498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104981 ⟨778498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104981
    ⟨778498, by decide⟩ (by decide) (![⟨778432, by decide⟩,⟨778462, by decide⟩,⟨778484, by decide⟩,⟨778497, by decide⟩]) unmarked_context_12_104981_778498 node_context_12_104981_778498
  intro a
  fin_cases a
  · exact context_13_419924_778432
  · exact context_13_419925_778462
  · exact context_13_419926_778484
  · exact context_13_419927_778497

theorem selected_cut_30645 : selected 8 ⟨778525, by decide⟩
    (prefixPartial 13 419928) = some ⟨13, 2, 0, 778525, 419928, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_419928_778525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419928 ⟨778525, by decide⟩ :=
  accepted_of_selected 13 419928 ⟨778525, by decide⟩ ⟨13, 2, 0, 778525, 419928, 1885, 16384⟩
    (by decide) selected_cut_30645

theorem selected_cut_30646 : selected 8 ⟨778552, by decide⟩
    (prefixPartial 13 419929) = some ⟨13, 2, 0, 778552, 419929, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_419929_778552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419929 ⟨778552, by decide⟩ :=
  accepted_of_selected 13 419929 ⟨778552, by decide⟩ ⟨13, 2, 0, 778552, 419929, 1945, 16384⟩
    (by decide) selected_cut_30646

theorem selected_cut_30647 : selected 8 ⟨778572, by decide⟩
    (prefixPartial 13 419930) = some ⟨13, 2, 0, 778572, 419930, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_419930_778572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419930 ⟨778572, by decide⟩ :=
  accepted_of_selected 13 419930 ⟨778572, by decide⟩ ⟨13, 2, 0, 778572, 419930, 1033, 16384⟩
    (by decide) selected_cut_30647

theorem selected_cut_30648 : selected 8 ⟨778582, by decide⟩
    (prefixPartial 13 419931) = some ⟨13, 2, 0, 778582, 419931, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_419931_778582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419931 ⟨778582, by decide⟩ :=
  accepted_of_selected 13 419931 ⟨778582, by decide⟩ ⟨13, 2, 0, 778582, 419931, 1029, 16384⟩
    (by decide) selected_cut_30648

theorem unmarked_context_12_104982_778583 : frontier 9 ⟨778583, by decide⟩
    (prefixCache 12 104982) (prefixPartial 12 104982) = false := by
  decide +kernel

theorem node_context_12_104982_778583 : EJMOriginalGlobalDAGData.nodes 9 ⟨778583, by decide⟩ =
    .split (coordinate 12) (![⟨778525, by decide⟩,⟨778552, by decide⟩,⟨778572, by decide⟩,⟨778582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104982_778583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104982 ⟨778583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104982
    ⟨778583, by decide⟩ (by decide) (![⟨778525, by decide⟩,⟨778552, by decide⟩,⟨778572, by decide⟩,⟨778582, by decide⟩]) unmarked_context_12_104982_778583 node_context_12_104982_778583
  intro a
  fin_cases a
  · exact context_13_419928_778525
  · exact context_13_419929_778552
  · exact context_13_419930_778572
  · exact context_13_419931_778582

theorem selected_cut_30649 : selected 8 ⟨778625, by decide⟩
    (prefixPartial 13 419932) = some ⟨13, 2, 0, 778625, 419932, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_419932_778625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419932 ⟨778625, by decide⟩ :=
  accepted_of_selected 13 419932 ⟨778625, by decide⟩ ⟨13, 2, 0, 778625, 419932, 2281, 16384⟩
    (by decide) selected_cut_30649

theorem selected_cut_30650 : selected 8 ⟨778659, by decide⟩
    (prefixPartial 13 419933) = some ⟨13, 2, 0, 778659, 419933, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_419933_778659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419933 ⟨778659, by decide⟩ :=
  accepted_of_selected 13 419933 ⟨778659, by decide⟩ ⟨13, 2, 0, 778659, 419933, 2293, 16384⟩
    (by decide) selected_cut_30650

theorem selected_cut_30651 : selected 8 ⟨778684, by decide⟩
    (prefixPartial 13 419934) = some ⟨13, 2, 0, 778684, 419934, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_419934_778684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419934 ⟨778684, by decide⟩ :=
  accepted_of_selected 13 419934 ⟨778684, by decide⟩ ⟨13, 2, 0, 778684, 419934, 1281, 16384⟩
    (by decide) selected_cut_30651

theorem selected_cut_30652 : selected 8 ⟨778702, by decide⟩
    (prefixPartial 13 419935) = some ⟨13, 2, 0, 778702, 419935, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_419935_778702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419935 ⟨778702, by decide⟩ :=
  accepted_of_selected 13 419935 ⟨778702, by decide⟩ ⟨13, 2, 0, 778702, 419935, 1089, 16384⟩
    (by decide) selected_cut_30652

theorem unmarked_context_12_104983_778703 : frontier 9 ⟨778703, by decide⟩
    (prefixCache 12 104983) (prefixPartial 12 104983) = false := by
  decide +kernel

theorem node_context_12_104983_778703 : EJMOriginalGlobalDAGData.nodes 9 ⟨778703, by decide⟩ =
    .split (coordinate 12) (![⟨778625, by decide⟩,⟨778659, by decide⟩,⟨778684, by decide⟩,⟨778702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104983_778703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104983 ⟨778703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104983
    ⟨778703, by decide⟩ (by decide) (![⟨778625, by decide⟩,⟨778659, by decide⟩,⟨778684, by decide⟩,⟨778702, by decide⟩]) unmarked_context_12_104983_778703 node_context_12_104983_778703
  intro a
  fin_cases a
  · exact context_13_419932_778625
  · exact context_13_419933_778659
  · exact context_13_419934_778684
  · exact context_13_419935_778702

theorem unmarked_context_11_26245_778704 : frontier 10 ⟨778704, by decide⟩
    (prefixCache 11 26245) (prefixPartial 11 26245) = false := by
  decide +kernel

theorem node_context_11_26245_778704 : EJMOriginalGlobalDAGData.nodes 10 ⟨778704, by decide⟩ =
    .split (coordinate 11) (![⟨778391, by decide⟩,⟨778498, by decide⟩,⟨778583, by decide⟩,⟨778703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26245_778704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26245 ⟨778704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26245
    ⟨778704, by decide⟩ (by decide) (![⟨778391, by decide⟩,⟨778498, by decide⟩,⟨778583, by decide⟩,⟨778703, by decide⟩]) unmarked_context_11_26245_778704 node_context_11_26245_778704
  intro a
  fin_cases a
  · exact context_12_104980_778391
  · exact context_12_104981_778498
  · exact context_12_104982_778583
  · exact context_12_104983_778703

theorem selected_cut_30653 : selected 8 ⟨778732, by decide⟩
    (prefixPartial 13 419936) = some ⟨13, 2, 0, 778732, 419936, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_419936_778732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419936 ⟨778732, by decide⟩ :=
  accepted_of_selected 13 419936 ⟨778732, by decide⟩ ⟨13, 2, 0, 778732, 419936, 1397, 16384⟩
    (by decide) selected_cut_30653

theorem selected_cut_30654 : selected 8 ⟨778752, by decide⟩
    (prefixPartial 13 419937) = some ⟨13, 2, 0, 778752, 419937, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_419937_778752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419937 ⟨778752, by decide⟩ :=
  accepted_of_selected 13 419937 ⟨778752, by decide⟩ ⟨13, 2, 0, 778752, 419937, 1469, 16384⟩
    (by decide) selected_cut_30654

theorem selected_cut_30655 : selected 8 ⟨778774, by decide⟩
    (prefixPartial 13 419938) = some ⟨13, 2, 0, 778774, 419938, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_419938_778774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419938 ⟨778774, by decide⟩ :=
  accepted_of_selected 13 419938 ⟨778774, by decide⟩ ⟨13, 2, 0, 778774, 419938, 1165, 16384⟩
    (by decide) selected_cut_30655

theorem selected_cut_30656 : selected 8 ⟨778782, by decide⟩
    (prefixPartial 13 419939) = some ⟨13, 2, 0, 778782, 419939, 881, 16384⟩ := by
  decide +kernel

theorem context_13_419939_778782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419939 ⟨778782, by decide⟩ :=
  accepted_of_selected 13 419939 ⟨778782, by decide⟩ ⟨13, 2, 0, 778782, 419939, 881, 16384⟩
    (by decide) selected_cut_30656

theorem unmarked_context_12_104984_778783 : frontier 9 ⟨778783, by decide⟩
    (prefixCache 12 104984) (prefixPartial 12 104984) = false := by
  decide +kernel

theorem node_context_12_104984_778783 : EJMOriginalGlobalDAGData.nodes 9 ⟨778783, by decide⟩ =
    .split (coordinate 12) (![⟨778732, by decide⟩,⟨778752, by decide⟩,⟨778774, by decide⟩,⟨778782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104984_778783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104984 ⟨778783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104984
    ⟨778783, by decide⟩ (by decide) (![⟨778732, by decide⟩,⟨778752, by decide⟩,⟨778774, by decide⟩,⟨778782, by decide⟩]) unmarked_context_12_104984_778783 node_context_12_104984_778783
  intro a
  fin_cases a
  · exact context_13_419936_778732
  · exact context_13_419937_778752
  · exact context_13_419938_778774
  · exact context_13_419939_778782

theorem selected_cut_30657 : selected 8 ⟨778812, by decide⟩
    (prefixPartial 13 419940) = some ⟨13, 2, 0, 778812, 419940, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_419940_778812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419940 ⟨778812, by decide⟩ :=
  accepted_of_selected 13 419940 ⟨778812, by decide⟩ ⟨13, 2, 0, 778812, 419940, 1649, 16384⟩
    (by decide) selected_cut_30657

theorem selected_cut_30658 : selected 8 ⟨778832, by decide⟩
    (prefixPartial 13 419941) = some ⟨13, 2, 0, 778832, 419941, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_419941_778832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419941 ⟨778832, by decide⟩ :=
  accepted_of_selected 13 419941 ⟨778832, by decide⟩ ⟨13, 2, 0, 778832, 419941, 1673, 16384⟩
    (by decide) selected_cut_30658

theorem selected_cut_30659 : selected 8 ⟨778858, by decide⟩
    (prefixPartial 13 419942) = some ⟨13, 2, 0, 778858, 419942, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_419942_778858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419942 ⟨778858, by decide⟩ :=
  accepted_of_selected 13 419942 ⟨778858, by decide⟩ ⟨13, 2, 0, 778858, 419942, 1205, 16384⟩
    (by decide) selected_cut_30659

theorem selected_cut_30660 : selected 8 ⟨778868, by decide⟩
    (prefixPartial 13 419943) = some ⟨13, 2, 0, 778868, 419943, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_419943_778868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419943 ⟨778868, by decide⟩ :=
  accepted_of_selected 13 419943 ⟨778868, by decide⟩ ⟨13, 2, 0, 778868, 419943, 1013, 16384⟩
    (by decide) selected_cut_30660

theorem unmarked_context_12_104985_778869 : frontier 9 ⟨778869, by decide⟩
    (prefixCache 12 104985) (prefixPartial 12 104985) = false := by
  decide +kernel

theorem node_context_12_104985_778869 : EJMOriginalGlobalDAGData.nodes 9 ⟨778869, by decide⟩ =
    .split (coordinate 12) (![⟨778812, by decide⟩,⟨778832, by decide⟩,⟨778858, by decide⟩,⟨778868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104985_778869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104985 ⟨778869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104985
    ⟨778869, by decide⟩ (by decide) (![⟨778812, by decide⟩,⟨778832, by decide⟩,⟨778858, by decide⟩,⟨778868, by decide⟩]) unmarked_context_12_104985_778869 node_context_12_104985_778869
  intro a
  fin_cases a
  · exact context_13_419940_778812
  · exact context_13_419941_778832
  · exact context_13_419942_778858
  · exact context_13_419943_778868

theorem selected_cut_30661 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 104986) = some ⟨12, 1, 0, 660636, 104986, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104986_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104986 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 104986 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 104986, 1, 65536⟩
    (by decide) selected_cut_30661

theorem selected_cut_30662 : selected 8 ⟨778897, by decide⟩
    (prefixPartial 13 419948) = some ⟨13, 2, 0, 778897, 419948, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_419948_778897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419948 ⟨778897, by decide⟩ :=
  accepted_of_selected 13 419948 ⟨778897, by decide⟩ ⟨13, 2, 0, 778897, 419948, 1789, 16384⟩
    (by decide) selected_cut_30662

theorem selected_cut_30663 : selected 8 ⟨778921, by decide⟩
    (prefixPartial 13 419949) = some ⟨13, 2, 0, 778921, 419949, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_419949_778921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419949 ⟨778921, by decide⟩ :=
  accepted_of_selected 13 419949 ⟨778921, by decide⟩ ⟨13, 2, 0, 778921, 419949, 2069, 16384⟩
    (by decide) selected_cut_30663

theorem selected_cut_30664 : selected 8 ⟨778941, by decide⟩
    (prefixPartial 13 419950) = some ⟨13, 2, 0, 778941, 419950, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_419950_778941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419950 ⟨778941, by decide⟩ :=
  accepted_of_selected 13 419950 ⟨778941, by decide⟩ ⟨13, 2, 0, 778941, 419950, 1309, 16384⟩
    (by decide) selected_cut_30664

theorem selected_cut_30665 : selected 8 ⟨778951, by decide⟩
    (prefixPartial 13 419951) = some ⟨13, 2, 0, 778951, 419951, 953, 16384⟩ := by
  decide +kernel

theorem context_13_419951_778951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419951 ⟨778951, by decide⟩ :=
  accepted_of_selected 13 419951 ⟨778951, by decide⟩ ⟨13, 2, 0, 778951, 419951, 953, 16384⟩
    (by decide) selected_cut_30665

theorem unmarked_context_12_104987_778952 : frontier 9 ⟨778952, by decide⟩
    (prefixCache 12 104987) (prefixPartial 12 104987) = false := by
  decide +kernel

theorem node_context_12_104987_778952 : EJMOriginalGlobalDAGData.nodes 9 ⟨778952, by decide⟩ =
    .split (coordinate 12) (![⟨778897, by decide⟩,⟨778921, by decide⟩,⟨778941, by decide⟩,⟨778951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104987_778952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104987 ⟨778952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104987
    ⟨778952, by decide⟩ (by decide) (![⟨778897, by decide⟩,⟨778921, by decide⟩,⟨778941, by decide⟩,⟨778951, by decide⟩]) unmarked_context_12_104987_778952 node_context_12_104987_778952
  intro a
  fin_cases a
  · exact context_13_419948_778897
  · exact context_13_419949_778921
  · exact context_13_419950_778941
  · exact context_13_419951_778951

theorem unmarked_context_11_26246_778953 : frontier 10 ⟨778953, by decide⟩
    (prefixCache 11 26246) (prefixPartial 11 26246) = false := by
  decide +kernel

theorem node_context_11_26246_778953 : EJMOriginalGlobalDAGData.nodes 10 ⟨778953, by decide⟩ =
    .split (coordinate 11) (![⟨778783, by decide⟩,⟨778869, by decide⟩,⟨660636, by decide⟩,⟨778952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26246_778953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26246 ⟨778953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26246
    ⟨778953, by decide⟩ (by decide) (![⟨778783, by decide⟩,⟨778869, by decide⟩,⟨660636, by decide⟩,⟨778952, by decide⟩]) unmarked_context_11_26246_778953 node_context_11_26246_778953
  intro a
  fin_cases a
  · exact context_12_104984_778783
  · exact context_12_104985_778869
  · exact context_12_104986_660636
  · exact context_12_104987_778952

theorem selected_cut_30666 : selected 8 ⟨778981, by decide⟩
    (prefixPartial 13 419952) = some ⟨13, 2, 0, 778981, 419952, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_419952_778981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419952 ⟨778981, by decide⟩ :=
  accepted_of_selected 13 419952 ⟨778981, by decide⟩ ⟨13, 2, 0, 778981, 419952, 1513, 16384⟩
    (by decide) selected_cut_30666

theorem selected_cut_30667 : selected 8 ⟨779007, by decide⟩
    (prefixPartial 13 419953) = some ⟨13, 2, 0, 779007, 419953, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_419953_779007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419953 ⟨779007, by decide⟩ :=
  accepted_of_selected 13 419953 ⟨779007, by decide⟩ ⟨13, 2, 0, 779007, 419953, 1617, 16384⟩
    (by decide) selected_cut_30667

theorem selected_cut_30668 : selected 8 ⟨779030, by decide⟩
    (prefixPartial 13 419954) = some ⟨13, 2, 0, 779030, 419954, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_419954_779030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419954 ⟨779030, by decide⟩ :=
  accepted_of_selected 13 419954 ⟨779030, by decide⟩ ⟨13, 2, 0, 779030, 419954, 1397, 16384⟩
    (by decide) selected_cut_30668

theorem selected_cut_30669 : selected 8 ⟨779039, by decide⟩
    (prefixPartial 13 419955) = some ⟨13, 2, 0, 779039, 419955, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_419955_779039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419955 ⟨779039, by decide⟩ :=
  accepted_of_selected 13 419955 ⟨779039, by decide⟩ ⟨13, 2, 0, 779039, 419955, 1097, 16384⟩
    (by decide) selected_cut_30669

theorem unmarked_context_12_104988_779040 : frontier 9 ⟨779040, by decide⟩
    (prefixCache 12 104988) (prefixPartial 12 104988) = false := by
  decide +kernel

theorem node_context_12_104988_779040 : EJMOriginalGlobalDAGData.nodes 9 ⟨779040, by decide⟩ =
    .split (coordinate 12) (![⟨778981, by decide⟩,⟨779007, by decide⟩,⟨779030, by decide⟩,⟨779039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104988_779040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104988 ⟨779040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104988
    ⟨779040, by decide⟩ (by decide) (![⟨778981, by decide⟩,⟨779007, by decide⟩,⟨779030, by decide⟩,⟨779039, by decide⟩]) unmarked_context_12_104988_779040 node_context_12_104988_779040
  intro a
  fin_cases a
  · exact context_13_419952_778981
  · exact context_13_419953_779007
  · exact context_13_419954_779030
  · exact context_13_419955_779039

theorem selected_cut_30670 : selected 8 ⟨779075, by decide⟩
    (prefixPartial 13 419956) = some ⟨13, 2, 0, 779075, 419956, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_419956_779075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419956 ⟨779075, by decide⟩ :=
  accepted_of_selected 13 419956 ⟨779075, by decide⟩ ⟨13, 2, 0, 779075, 419956, 1857, 16384⟩
    (by decide) selected_cut_30670

theorem selected_cut_30671 : selected 8 ⟨779104, by decide⟩
    (prefixPartial 13 419957) = some ⟨13, 2, 0, 779104, 419957, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_419957_779104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419957 ⟨779104, by decide⟩ :=
  accepted_of_selected 13 419957 ⟨779104, by decide⟩ ⟨13, 2, 0, 779104, 419957, 1785, 16384⟩
    (by decide) selected_cut_30671

theorem selected_cut_30672 : selected 8 ⟨779125, by decide⟩
    (prefixPartial 13 419958) = some ⟨13, 2, 0, 779125, 419958, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_419958_779125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419958 ⟨779125, by decide⟩ :=
  accepted_of_selected 13 419958 ⟨779125, by decide⟩ ⟨13, 2, 0, 779125, 419958, 1353, 16384⟩
    (by decide) selected_cut_30672

theorem selected_cut_30673 : selected 8 ⟨779150, by decide⟩
    (prefixPartial 13 419959) = some ⟨13, 2, 0, 779150, 419959, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_419959_779150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419959 ⟨779150, by decide⟩ :=
  accepted_of_selected 13 419959 ⟨779150, by decide⟩ ⟨13, 2, 0, 779150, 419959, 1233, 16384⟩
    (by decide) selected_cut_30673

theorem unmarked_context_12_104989_779151 : frontier 9 ⟨779151, by decide⟩
    (prefixCache 12 104989) (prefixPartial 12 104989) = false := by
  decide +kernel

theorem node_context_12_104989_779151 : EJMOriginalGlobalDAGData.nodes 9 ⟨779151, by decide⟩ =
    .split (coordinate 12) (![⟨779075, by decide⟩,⟨779104, by decide⟩,⟨779125, by decide⟩,⟨779150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104989_779151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104989 ⟨779151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104989
    ⟨779151, by decide⟩ (by decide) (![⟨779075, by decide⟩,⟨779104, by decide⟩,⟨779125, by decide⟩,⟨779150, by decide⟩]) unmarked_context_12_104989_779151 node_context_12_104989_779151
  intro a
  fin_cases a
  · exact context_13_419956_779075
  · exact context_13_419957_779104
  · exact context_13_419958_779125
  · exact context_13_419959_779150

theorem selected_cut_30674 : selected 8 ⟨779171, by decide⟩
    (prefixPartial 13 419960) = some ⟨13, 2, 0, 779171, 419960, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_419960_779171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419960 ⟨779171, by decide⟩ :=
  accepted_of_selected 13 419960 ⟨779171, by decide⟩ ⟨13, 2, 0, 779171, 419960, 1613, 16384⟩
    (by decide) selected_cut_30674

theorem selected_cut_30675 : selected 8 ⟨779193, by decide⟩
    (prefixPartial 13 419961) = some ⟨13, 2, 0, 779193, 419961, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_419961_779193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419961 ⟨779193, by decide⟩ :=
  accepted_of_selected 13 419961 ⟨779193, by decide⟩ ⟨13, 2, 0, 779193, 419961, 1761, 16384⟩
    (by decide) selected_cut_30675

theorem selected_cut_30676 : selected 8 ⟨779212, by decide⟩
    (prefixPartial 13 419962) = some ⟨13, 2, 0, 779212, 419962, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_419962_779212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419962 ⟨779212, by decide⟩ :=
  accepted_of_selected 13 419962 ⟨779212, by decide⟩ ⟨13, 2, 0, 779212, 419962, 1285, 16384⟩
    (by decide) selected_cut_30676

theorem selected_cut_30677 : selected 8 ⟨779231, by decide⟩
    (prefixPartial 13 419963) = some ⟨13, 2, 0, 779231, 419963, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_419963_779231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419963 ⟨779231, by decide⟩ :=
  accepted_of_selected 13 419963 ⟨779231, by decide⟩ ⟨13, 2, 0, 779231, 419963, 1101, 16384⟩
    (by decide) selected_cut_30677

theorem unmarked_context_12_104990_779232 : frontier 9 ⟨779232, by decide⟩
    (prefixCache 12 104990) (prefixPartial 12 104990) = false := by
  decide +kernel

theorem node_context_12_104990_779232 : EJMOriginalGlobalDAGData.nodes 9 ⟨779232, by decide⟩ =
    .split (coordinate 12) (![⟨779171, by decide⟩,⟨779193, by decide⟩,⟨779212, by decide⟩,⟨779231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104990_779232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104990 ⟨779232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104990
    ⟨779232, by decide⟩ (by decide) (![⟨779171, by decide⟩,⟨779193, by decide⟩,⟨779212, by decide⟩,⟨779231, by decide⟩]) unmarked_context_12_104990_779232 node_context_12_104990_779232
  intro a
  fin_cases a
  · exact context_13_419960_779171
  · exact context_13_419961_779193
  · exact context_13_419962_779212
  · exact context_13_419963_779231

theorem selected_cut_30678 : selected 8 ⟨779272, by decide⟩
    (prefixPartial 13 419964) = some ⟨13, 2, 0, 779272, 419964, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_419964_779272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419964 ⟨779272, by decide⟩ :=
  accepted_of_selected 13 419964 ⟨779272, by decide⟩ ⟨13, 2, 0, 779272, 419964, 1893, 16384⟩
    (by decide) selected_cut_30678

theorem selected_cut_30679 : selected 8 ⟨779294, by decide⟩
    (prefixPartial 13 419965) = some ⟨13, 2, 0, 779294, 419965, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_419965_779294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419965 ⟨779294, by decide⟩ :=
  accepted_of_selected 13 419965 ⟨779294, by decide⟩ ⟨13, 2, 0, 779294, 419965, 1909, 16384⟩
    (by decide) selected_cut_30679

theorem selected_cut_30680 : selected 8 ⟨779316, by decide⟩
    (prefixPartial 13 419966) = some ⟨13, 2, 0, 779316, 419966, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_419966_779316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419966 ⟨779316, by decide⟩ :=
  accepted_of_selected 13 419966 ⟨779316, by decide⟩ ⟨13, 2, 0, 779316, 419966, 1553, 16384⟩
    (by decide) selected_cut_30680

theorem selected_cut_30681 : selected 8 ⟨779331, by decide⟩
    (prefixPartial 13 419967) = some ⟨13, 2, 0, 779331, 419967, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_419967_779331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419967 ⟨779331, by decide⟩ :=
  accepted_of_selected 13 419967 ⟨779331, by decide⟩ ⟨13, 2, 0, 779331, 419967, 1181, 16384⟩
    (by decide) selected_cut_30681

theorem unmarked_context_12_104991_779332 : frontier 9 ⟨779332, by decide⟩
    (prefixCache 12 104991) (prefixPartial 12 104991) = false := by
  decide +kernel

theorem node_context_12_104991_779332 : EJMOriginalGlobalDAGData.nodes 9 ⟨779332, by decide⟩ =
    .split (coordinate 12) (![⟨779272, by decide⟩,⟨779294, by decide⟩,⟨779316, by decide⟩,⟨779331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104991_779332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104991 ⟨779332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104991
    ⟨779332, by decide⟩ (by decide) (![⟨779272, by decide⟩,⟨779294, by decide⟩,⟨779316, by decide⟩,⟨779331, by decide⟩]) unmarked_context_12_104991_779332 node_context_12_104991_779332
  intro a
  fin_cases a
  · exact context_13_419964_779272
  · exact context_13_419965_779294
  · exact context_13_419966_779316
  · exact context_13_419967_779331

theorem unmarked_context_11_26247_779333 : frontier 10 ⟨779333, by decide⟩
    (prefixCache 11 26247) (prefixPartial 11 26247) = false := by
  decide +kernel

theorem node_context_11_26247_779333 : EJMOriginalGlobalDAGData.nodes 10 ⟨779333, by decide⟩ =
    .split (coordinate 11) (![⟨779040, by decide⟩,⟨779151, by decide⟩,⟨779232, by decide⟩,⟨779332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26247_779333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26247 ⟨779333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26247
    ⟨779333, by decide⟩ (by decide) (![⟨779040, by decide⟩,⟨779151, by decide⟩,⟨779232, by decide⟩,⟨779332, by decide⟩]) unmarked_context_11_26247_779333 node_context_11_26247_779333
  intro a
  fin_cases a
  · exact context_12_104988_779040
  · exact context_12_104989_779151
  · exact context_12_104990_779232
  · exact context_12_104991_779332

theorem unmarked_context_10_6561_779334 : frontier 11 ⟨779334, by decide⟩
    (prefixCache 10 6561) (prefixPartial 10 6561) = false := by
  decide +kernel

theorem node_context_10_6561_779334 : EJMOriginalGlobalDAGData.nodes 11 ⟨779334, by decide⟩ =
    .split (coordinate 10) (![⟨778298, by decide⟩,⟨778704, by decide⟩,⟨778953, by decide⟩,⟨779333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6561_779334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6561 ⟨779334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6561
    ⟨779334, by decide⟩ (by decide) (![⟨778298, by decide⟩,⟨778704, by decide⟩,⟨778953, by decide⟩,⟨779333, by decide⟩]) unmarked_context_10_6561_779334 node_context_10_6561_779334
  intro a
  fin_cases a
  · exact context_11_26244_778298
  · exact context_11_26245_778704
  · exact context_11_26246_778953
  · exact context_11_26247_779333

theorem selected_cut_30682 : selected 9 ⟨779393, by decide⟩
    (prefixPartial 12 104992) = some ⟨12, 2, 0, 779393, 104992, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_104992_779393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104992 ⟨779393, by decide⟩ :=
  accepted_of_selected 12 104992 ⟨779393, by decide⟩ ⟨12, 2, 0, 779393, 104992, 3461, 65536⟩
    (by decide) selected_cut_30682

theorem selected_cut_30683 : selected 8 ⟨779421, by decide⟩
    (prefixPartial 13 419972) = some ⟨13, 2, 0, 779421, 419972, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_419972_779421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419972 ⟨779421, by decide⟩ :=
  accepted_of_selected 13 419972 ⟨779421, by decide⟩ ⟨13, 2, 0, 779421, 419972, 1021, 16384⟩
    (by decide) selected_cut_30683

theorem selected_cut_30684 : selected 8 ⟨779444, by decide⟩
    (prefixPartial 13 419973) = some ⟨13, 2, 0, 779444, 419973, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_419973_779444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419973 ⟨779444, by decide⟩ :=
  accepted_of_selected 13 419973 ⟨779444, by decide⟩ ⟨13, 2, 0, 779444, 419973, 1637, 16384⟩
    (by decide) selected_cut_30684

theorem selected_cut_30685 : selected 8 ⟨779459, by decide⟩
    (prefixPartial 13 419974) = some ⟨13, 2, 0, 779459, 419974, 885, 16384⟩ := by
  decide +kernel

theorem context_13_419974_779459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419974 ⟨779459, by decide⟩ :=
  accepted_of_selected 13 419974 ⟨779459, by decide⟩ ⟨13, 2, 0, 779459, 419974, 885, 16384⟩
    (by decide) selected_cut_30685

theorem selected_cut_30686 : selected 8 ⟨779471, by decide⟩
    (prefixPartial 13 419975) = some ⟨13, 2, 0, 779471, 419975, 909, 16384⟩ := by
  decide +kernel

theorem context_13_419975_779471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419975 ⟨779471, by decide⟩ :=
  accepted_of_selected 13 419975 ⟨779471, by decide⟩ ⟨13, 2, 0, 779471, 419975, 909, 16384⟩
    (by decide) selected_cut_30686

theorem unmarked_context_12_104993_779472 : frontier 9 ⟨779472, by decide⟩
    (prefixCache 12 104993) (prefixPartial 12 104993) = false := by
  decide +kernel

theorem node_context_12_104993_779472 : EJMOriginalGlobalDAGData.nodes 9 ⟨779472, by decide⟩ =
    .split (coordinate 12) (![⟨779421, by decide⟩,⟨779444, by decide⟩,⟨779459, by decide⟩,⟨779471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104993_779472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104993 ⟨779472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104993
    ⟨779472, by decide⟩ (by decide) (![⟨779421, by decide⟩,⟨779444, by decide⟩,⟨779459, by decide⟩,⟨779471, by decide⟩]) unmarked_context_12_104993_779472 node_context_12_104993_779472
  intro a
  fin_cases a
  · exact context_13_419972_779421
  · exact context_13_419973_779444
  · exact context_13_419974_779459
  · exact context_13_419975_779471

theorem selected_cut_30687 : selected 9 ⟨779528, by decide⟩
    (prefixPartial 12 104994) = some ⟨12, 2, 0, 779528, 104994, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_104994_779528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104994 ⟨779528, by decide⟩ :=
  accepted_of_selected 12 104994 ⟨779528, by decide⟩ ⟨12, 2, 0, 779528, 104994, 3109, 65536⟩
    (by decide) selected_cut_30687

theorem selected_cut_30688 : selected 8 ⟨779553, by decide⟩
    (prefixPartial 13 419980) = some ⟨13, 2, 0, 779553, 419980, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_419980_779553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419980 ⟨779553, by decide⟩ :=
  accepted_of_selected 13 419980 ⟨779553, by decide⟩ ⟨13, 2, 0, 779553, 419980, 1037, 16384⟩
    (by decide) selected_cut_30688

theorem selected_cut_30689 : selected 8 ⟨779570, by decide⟩
    (prefixPartial 13 419981) = some ⟨13, 2, 0, 779570, 419981, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_419981_779570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419981 ⟨779570, by decide⟩ :=
  accepted_of_selected 13 419981 ⟨779570, by decide⟩ ⟨13, 2, 0, 779570, 419981, 1641, 16384⟩
    (by decide) selected_cut_30689

theorem selected_cut_30690 : selected 8 ⟨779587, by decide⟩
    (prefixPartial 13 419982) = some ⟨13, 2, 0, 779587, 419982, 905, 16384⟩ := by
  decide +kernel

theorem context_13_419982_779587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419982 ⟨779587, by decide⟩ :=
  accepted_of_selected 13 419982 ⟨779587, by decide⟩ ⟨13, 2, 0, 779587, 419982, 905, 16384⟩
    (by decide) selected_cut_30690

theorem selected_cut_30691 : selected 8 ⟨779596, by decide⟩
    (prefixPartial 13 419983) = some ⟨13, 2, 0, 779596, 419983, 833, 16384⟩ := by
  decide +kernel

theorem context_13_419983_779596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419983 ⟨779596, by decide⟩ :=
  accepted_of_selected 13 419983 ⟨779596, by decide⟩ ⟨13, 2, 0, 779596, 419983, 833, 16384⟩
    (by decide) selected_cut_30691

theorem unmarked_context_12_104995_779597 : frontier 9 ⟨779597, by decide⟩
    (prefixCache 12 104995) (prefixPartial 12 104995) = false := by
  decide +kernel

theorem node_context_12_104995_779597 : EJMOriginalGlobalDAGData.nodes 9 ⟨779597, by decide⟩ =
    .split (coordinate 12) (![⟨779553, by decide⟩,⟨779570, by decide⟩,⟨779587, by decide⟩,⟨779596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104995_779597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104995 ⟨779597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104995
    ⟨779597, by decide⟩ (by decide) (![⟨779553, by decide⟩,⟨779570, by decide⟩,⟨779587, by decide⟩,⟨779596, by decide⟩]) unmarked_context_12_104995_779597 node_context_12_104995_779597
  intro a
  fin_cases a
  · exact context_13_419980_779553
  · exact context_13_419981_779570
  · exact context_13_419982_779587
  · exact context_13_419983_779596

theorem unmarked_context_11_26248_779598 : frontier 10 ⟨779598, by decide⟩
    (prefixCache 11 26248) (prefixPartial 11 26248) = false := by
  decide +kernel

theorem node_context_11_26248_779598 : EJMOriginalGlobalDAGData.nodes 10 ⟨779598, by decide⟩ =
    .split (coordinate 11) (![⟨779393, by decide⟩,⟨779472, by decide⟩,⟨779528, by decide⟩,⟨779597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26248_779598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26248 ⟨779598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26248
    ⟨779598, by decide⟩ (by decide) (![⟨779393, by decide⟩,⟨779472, by decide⟩,⟨779528, by decide⟩,⟨779597, by decide⟩]) unmarked_context_11_26248_779598 node_context_11_26248_779598
  intro a
  fin_cases a
  · exact context_12_104992_779393
  · exact context_12_104993_779472
  · exact context_12_104994_779528
  · exact context_12_104995_779597

theorem selected_cut_30692 : selected 8 ⟨779622, by decide⟩
    (prefixPartial 13 419984) = some ⟨13, 2, 0, 779622, 419984, 825, 16384⟩ := by
  decide +kernel

theorem context_13_419984_779622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419984 ⟨779622, by decide⟩ :=
  accepted_of_selected 13 419984 ⟨779622, by decide⟩ ⟨13, 2, 0, 779622, 419984, 825, 16384⟩
    (by decide) selected_cut_30692

theorem selected_cut_30693 : selected 8 ⟨779646, by decide⟩
    (prefixPartial 13 419985) = some ⟨13, 2, 0, 779646, 419985, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_419985_779646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419985 ⟨779646, by decide⟩ :=
  accepted_of_selected 13 419985 ⟨779646, by decide⟩ ⟨13, 2, 0, 779646, 419985, 1565, 16384⟩
    (by decide) selected_cut_30693

theorem selected_cut_30694 : selected 8 ⟨779665, by decide⟩
    (prefixPartial 13 419986) = some ⟨13, 2, 0, 779665, 419986, 909, 16384⟩ := by
  decide +kernel

theorem context_13_419986_779665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419986 ⟨779665, by decide⟩ :=
  accepted_of_selected 13 419986 ⟨779665, by decide⟩ ⟨13, 2, 0, 779665, 419986, 909, 16384⟩
    (by decide) selected_cut_30694

theorem selected_cut_30695 : selected 8 ⟨779674, by decide⟩
    (prefixPartial 13 419987) = some ⟨13, 2, 0, 779674, 419987, 865, 16384⟩ := by
  decide +kernel

theorem context_13_419987_779674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419987 ⟨779674, by decide⟩ :=
  accepted_of_selected 13 419987 ⟨779674, by decide⟩ ⟨13, 2, 0, 779674, 419987, 865, 16384⟩
    (by decide) selected_cut_30695

theorem unmarked_context_12_104996_779675 : frontier 9 ⟨779675, by decide⟩
    (prefixCache 12 104996) (prefixPartial 12 104996) = false := by
  decide +kernel

theorem node_context_12_104996_779675 : EJMOriginalGlobalDAGData.nodes 9 ⟨779675, by decide⟩ =
    .split (coordinate 12) (![⟨779622, by decide⟩,⟨779646, by decide⟩,⟨779665, by decide⟩,⟨779674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104996_779675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104996 ⟨779675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104996
    ⟨779675, by decide⟩ (by decide) (![⟨779622, by decide⟩,⟨779646, by decide⟩,⟨779665, by decide⟩,⟨779674, by decide⟩]) unmarked_context_12_104996_779675 node_context_12_104996_779675
  intro a
  fin_cases a
  · exact context_13_419984_779622
  · exact context_13_419985_779646
  · exact context_13_419986_779665
  · exact context_13_419987_779674

theorem selected_cut_30696 : selected 8 ⟨779700, by decide⟩
    (prefixPartial 13 419988) = some ⟨13, 2, 0, 779700, 419988, 961, 16384⟩ := by
  decide +kernel

theorem context_13_419988_779700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419988 ⟨779700, by decide⟩ :=
  accepted_of_selected 13 419988 ⟨779700, by decide⟩ ⟨13, 2, 0, 779700, 419988, 961, 16384⟩
    (by decide) selected_cut_30696

theorem selected_cut_30697 : selected 8 ⟨779724, by decide⟩
    (prefixPartial 13 419989) = some ⟨13, 2, 0, 779724, 419989, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_419989_779724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419989 ⟨779724, by decide⟩ :=
  accepted_of_selected 13 419989 ⟨779724, by decide⟩ ⟨13, 2, 0, 779724, 419989, 1485, 16384⟩
    (by decide) selected_cut_30697

theorem selected_cut_30698 : selected 8 ⟨779740, by decide⟩
    (prefixPartial 13 419990) = some ⟨13, 2, 0, 779740, 419990, 833, 16384⟩ := by
  decide +kernel

theorem context_13_419990_779740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419990 ⟨779740, by decide⟩ :=
  accepted_of_selected 13 419990 ⟨779740, by decide⟩ ⟨13, 2, 0, 779740, 419990, 833, 16384⟩
    (by decide) selected_cut_30698

theorem selected_cut_30699 : selected 8 ⟨779750, by decide⟩
    (prefixPartial 13 419991) = some ⟨13, 2, 0, 779750, 419991, 881, 16384⟩ := by
  decide +kernel

theorem context_13_419991_779750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419991 ⟨779750, by decide⟩ :=
  accepted_of_selected 13 419991 ⟨779750, by decide⟩ ⟨13, 2, 0, 779750, 419991, 881, 16384⟩
    (by decide) selected_cut_30699

theorem unmarked_context_12_104997_779751 : frontier 9 ⟨779751, by decide⟩
    (prefixCache 12 104997) (prefixPartial 12 104997) = false := by
  decide +kernel

theorem node_context_12_104997_779751 : EJMOriginalGlobalDAGData.nodes 9 ⟨779751, by decide⟩ =
    .split (coordinate 12) (![⟨779700, by decide⟩,⟨779724, by decide⟩,⟨779740, by decide⟩,⟨779750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104997_779751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104997 ⟨779751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104997
    ⟨779751, by decide⟩ (by decide) (![⟨779700, by decide⟩,⟨779724, by decide⟩,⟨779740, by decide⟩,⟨779750, by decide⟩]) unmarked_context_12_104997_779751 node_context_12_104997_779751
  intro a
  fin_cases a
  · exact context_13_419988_779700
  · exact context_13_419989_779724
  · exact context_13_419990_779740
  · exact context_13_419991_779750

theorem selected_cut_30700 : selected 9 ⟨779810, by decide⟩
    (prefixPartial 12 104998) = some ⟨12, 2, 0, 779810, 104998, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_104998_779810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104998 ⟨779810, by decide⟩ :=
  accepted_of_selected 12 104998 ⟨779810, by decide⟩ ⟨12, 2, 0, 779810, 104998, 3461, 65536⟩
    (by decide) selected_cut_30700

theorem selected_cut_30701 : selected 8 ⟨779831, by decide⟩
    (prefixPartial 13 419996) = some ⟨13, 2, 0, 779831, 419996, 925, 16384⟩ := by
  decide +kernel

theorem context_13_419996_779831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419996 ⟨779831, by decide⟩ :=
  accepted_of_selected 13 419996 ⟨779831, by decide⟩ ⟨13, 2, 0, 779831, 419996, 925, 16384⟩
    (by decide) selected_cut_30701

theorem selected_cut_30702 : selected 8 ⟨779855, by decide⟩
    (prefixPartial 13 419997) = some ⟨13, 2, 0, 779855, 419997, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_419997_779855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419997 ⟨779855, by decide⟩ :=
  accepted_of_selected 13 419997 ⟨779855, by decide⟩ ⟨13, 2, 0, 779855, 419997, 1597, 16384⟩
    (by decide) selected_cut_30702

theorem selected_cut_30703 : selected 8 ⟨779874, by decide⟩
    (prefixPartial 13 419998) = some ⟨13, 2, 0, 779874, 419998, 957, 16384⟩ := by
  decide +kernel

theorem context_13_419998_779874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419998 ⟨779874, by decide⟩ :=
  accepted_of_selected 13 419998 ⟨779874, by decide⟩ ⟨13, 2, 0, 779874, 419998, 957, 16384⟩
    (by decide) selected_cut_30703

theorem selected_cut_30704 : selected 8 ⟨779882, by decide⟩
    (prefixPartial 13 419999) = some ⟨13, 2, 0, 779882, 419999, 901, 16384⟩ := by
  decide +kernel

theorem context_13_419999_779882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419999 ⟨779882, by decide⟩ :=
  accepted_of_selected 13 419999 ⟨779882, by decide⟩ ⟨13, 2, 0, 779882, 419999, 901, 16384⟩
    (by decide) selected_cut_30704

theorem unmarked_context_12_104999_779883 : frontier 9 ⟨779883, by decide⟩
    (prefixCache 12 104999) (prefixPartial 12 104999) = false := by
  decide +kernel

theorem node_context_12_104999_779883 : EJMOriginalGlobalDAGData.nodes 9 ⟨779883, by decide⟩ =
    .split (coordinate 12) (![⟨779831, by decide⟩,⟨779855, by decide⟩,⟨779874, by decide⟩,⟨779882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104999_779883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104999 ⟨779883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104999
    ⟨779883, by decide⟩ (by decide) (![⟨779831, by decide⟩,⟨779855, by decide⟩,⟨779874, by decide⟩,⟨779882, by decide⟩]) unmarked_context_12_104999_779883 node_context_12_104999_779883
  intro a
  fin_cases a
  · exact context_13_419996_779831
  · exact context_13_419997_779855
  · exact context_13_419998_779874
  · exact context_13_419999_779882

theorem unmarked_context_11_26249_779884 : frontier 10 ⟨779884, by decide⟩
    (prefixCache 11 26249) (prefixPartial 11 26249) = false := by
  decide +kernel

theorem node_context_11_26249_779884 : EJMOriginalGlobalDAGData.nodes 10 ⟨779884, by decide⟩ =
    .split (coordinate 11) (![⟨779675, by decide⟩,⟨779751, by decide⟩,⟨779810, by decide⟩,⟨779883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26249_779884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26249 ⟨779884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26249
    ⟨779884, by decide⟩ (by decide) (![⟨779675, by decide⟩,⟨779751, by decide⟩,⟨779810, by decide⟩,⟨779883, by decide⟩]) unmarked_context_11_26249_779884 node_context_11_26249_779884
  intro a
  fin_cases a
  · exact context_12_104996_779675
  · exact context_12_104997_779751
  · exact context_12_104998_779810
  · exact context_12_104999_779883

theorem selected_cut_30705 : selected 10 ⟨766338, by decide⟩
    (prefixPartial 11 26250) = some ⟨11, 1, 0, 766338, 26250, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26250_766338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26250 ⟨766338, by decide⟩ :=
  accepted_of_selected 11 26250 ⟨766338, by decide⟩ ⟨11, 1, 0, 766338, 26250, 1, 262144⟩
    (by decide) selected_cut_30705

theorem selected_cut_30706 : selected 9 ⟨779961, by decide⟩
    (prefixPartial 12 105004) = some ⟨12, 2, 0, 779961, 105004, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_105004_779961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105004 ⟨779961, by decide⟩ :=
  accepted_of_selected 12 105004 ⟨779961, by decide⟩ ⟨12, 2, 0, 779961, 105004, 3965, 65536⟩
    (by decide) selected_cut_30706

theorem selected_cut_30707 : selected 8 ⟨779982, by decide⟩
    (prefixPartial 13 420020) = some ⟨13, 2, 0, 779982, 420020, 833, 16384⟩ := by
  decide +kernel

theorem context_13_420020_779982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420020 ⟨779982, by decide⟩ :=
  accepted_of_selected 13 420020 ⟨779982, by decide⟩ ⟨13, 2, 0, 779982, 420020, 833, 16384⟩
    (by decide) selected_cut_30707

theorem selected_cut_30708 : selected 8 ⟨780003, by decide⟩
    (prefixPartial 13 420021) = some ⟨13, 2, 0, 780003, 420021, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_420021_780003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420021 ⟨780003, by decide⟩ :=
  accepted_of_selected 13 420021 ⟨780003, by decide⟩ ⟨13, 2, 0, 780003, 420021, 1405, 16384⟩
    (by decide) selected_cut_30708

theorem selected_cut_30709 : selected 8 ⟨780020, by decide⟩
    (prefixPartial 13 420022) = some ⟨13, 2, 0, 780020, 420022, 921, 16384⟩ := by
  decide +kernel

theorem context_13_420022_780020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420022 ⟨780020, by decide⟩ :=
  accepted_of_selected 13 420022 ⟨780020, by decide⟩ ⟨13, 2, 0, 780020, 420022, 921, 16384⟩
    (by decide) selected_cut_30709

theorem selected_cut_30710 : selected 8 ⟨780035, by decide⟩
    (prefixPartial 13 420023) = some ⟨13, 2, 0, 780035, 420023, 981, 16384⟩ := by
  decide +kernel

theorem context_13_420023_780035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420023 ⟨780035, by decide⟩ :=
  accepted_of_selected 13 420023 ⟨780035, by decide⟩ ⟨13, 2, 0, 780035, 420023, 981, 16384⟩
    (by decide) selected_cut_30710

theorem unmarked_context_12_105005_780036 : frontier 9 ⟨780036, by decide⟩
    (prefixCache 12 105005) (prefixPartial 12 105005) = false := by
  decide +kernel

theorem node_context_12_105005_780036 : EJMOriginalGlobalDAGData.nodes 9 ⟨780036, by decide⟩ =
    .split (coordinate 12) (![⟨779982, by decide⟩,⟨780003, by decide⟩,⟨780020, by decide⟩,⟨780035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105005_780036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105005 ⟨780036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105005
    ⟨780036, by decide⟩ (by decide) (![⟨779982, by decide⟩,⟨780003, by decide⟩,⟨780020, by decide⟩,⟨780035, by decide⟩]) unmarked_context_12_105005_780036 node_context_12_105005_780036
  intro a
  fin_cases a
  · exact context_13_420020_779982
  · exact context_13_420021_780003
  · exact context_13_420022_780020
  · exact context_13_420023_780035

theorem selected_cut_30711 : selected 9 ⟨780093, by decide⟩
    (prefixPartial 12 105006) = some ⟨12, 2, 0, 780093, 105006, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_105006_780093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105006 ⟨780093, by decide⟩ :=
  accepted_of_selected 12 105006 ⟨780093, by decide⟩ ⟨12, 2, 0, 780093, 105006, 3257, 65536⟩
    (by decide) selected_cut_30711

theorem selected_cut_30712 : selected 8 ⟨780113, by decide⟩
    (prefixPartial 13 420028) = some ⟨13, 2, 0, 780113, 420028, 749, 16384⟩ := by
  decide +kernel

theorem context_13_420028_780113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420028 ⟨780113, by decide⟩ :=
  accepted_of_selected 13 420028 ⟨780113, by decide⟩ ⟨13, 2, 0, 780113, 420028, 749, 16384⟩
    (by decide) selected_cut_30712

theorem selected_cut_30713 : selected 8 ⟨780134, by decide⟩
    (prefixPartial 13 420029) = some ⟨13, 2, 0, 780134, 420029, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_420029_780134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420029 ⟨780134, by decide⟩ :=
  accepted_of_selected 13 420029 ⟨780134, by decide⟩ ⟨13, 2, 0, 780134, 420029, 1501, 16384⟩
    (by decide) selected_cut_30713

theorem selected_cut_30714 : selected 8 ⟨780149, by decide⟩
    (prefixPartial 13 420030) = some ⟨13, 2, 0, 780149, 420030, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_420030_780149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420030 ⟨780149, by decide⟩ :=
  accepted_of_selected 13 420030 ⟨780149, by decide⟩ ⟨13, 2, 0, 780149, 420030, 1061, 16384⟩
    (by decide) selected_cut_30714

theorem selected_cut_30715 : selected 8 ⟨780159, by decide⟩
    (prefixPartial 13 420031) = some ⟨13, 2, 0, 780159, 420031, 985, 16384⟩ := by
  decide +kernel

theorem context_13_420031_780159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420031 ⟨780159, by decide⟩ :=
  accepted_of_selected 13 420031 ⟨780159, by decide⟩ ⟨13, 2, 0, 780159, 420031, 985, 16384⟩
    (by decide) selected_cut_30715

theorem unmarked_context_12_105007_780160 : frontier 9 ⟨780160, by decide⟩
    (prefixCache 12 105007) (prefixPartial 12 105007) = false := by
  decide +kernel

theorem node_context_12_105007_780160 : EJMOriginalGlobalDAGData.nodes 9 ⟨780160, by decide⟩ =
    .split (coordinate 12) (![⟨780113, by decide⟩,⟨780134, by decide⟩,⟨780149, by decide⟩,⟨780159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105007_780160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105007 ⟨780160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105007
    ⟨780160, by decide⟩ (by decide) (![⟨780113, by decide⟩,⟨780134, by decide⟩,⟨780149, by decide⟩,⟨780159, by decide⟩]) unmarked_context_12_105007_780160 node_context_12_105007_780160
  intro a
  fin_cases a
  · exact context_13_420028_780113
  · exact context_13_420029_780134
  · exact context_13_420030_780149
  · exact context_13_420031_780159

theorem unmarked_context_11_26251_780161 : frontier 10 ⟨780161, by decide⟩
    (prefixCache 11 26251) (prefixPartial 11 26251) = false := by
  decide +kernel

theorem node_context_11_26251_780161 : EJMOriginalGlobalDAGData.nodes 10 ⟨780161, by decide⟩ =
    .split (coordinate 11) (![⟨779961, by decide⟩,⟨780036, by decide⟩,⟨780093, by decide⟩,⟨780160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26251_780161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26251 ⟨780161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26251
    ⟨780161, by decide⟩ (by decide) (![⟨779961, by decide⟩,⟨780036, by decide⟩,⟨780093, by decide⟩,⟨780160, by decide⟩]) unmarked_context_11_26251_780161 node_context_11_26251_780161
  intro a
  fin_cases a
  · exact context_12_105004_779961
  · exact context_12_105005_780036
  · exact context_12_105006_780093
  · exact context_12_105007_780160

theorem unmarked_context_10_6562_780162 : frontier 11 ⟨780162, by decide⟩
    (prefixCache 10 6562) (prefixPartial 10 6562) = false := by
  decide +kernel

theorem node_context_10_6562_780162 : EJMOriginalGlobalDAGData.nodes 11 ⟨780162, by decide⟩ =
    .split (coordinate 10) (![⟨779598, by decide⟩,⟨779884, by decide⟩,⟨766338, by decide⟩,⟨780161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6562_780162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6562 ⟨780162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6562
    ⟨780162, by decide⟩ (by decide) (![⟨779598, by decide⟩,⟨779884, by decide⟩,⟨766338, by decide⟩,⟨780161, by decide⟩]) unmarked_context_10_6562_780162 node_context_10_6562_780162
  intro a
  fin_cases a
  · exact context_11_26248_779598
  · exact context_11_26249_779884
  · exact context_11_26250_766338
  · exact context_11_26251_780161

theorem selected_cut_30716 : selected 8 ⟨780180, by decide⟩
    (prefixPartial 13 420032) = some ⟨13, 2, 0, 780180, 420032, 881, 16384⟩ := by
  decide +kernel

theorem context_13_420032_780180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420032 ⟨780180, by decide⟩ :=
  accepted_of_selected 13 420032 ⟨780180, by decide⟩ ⟨13, 2, 0, 780180, 420032, 881, 16384⟩
    (by decide) selected_cut_30716

theorem selected_cut_30717 : selected 8 ⟨780210, by decide⟩
    (prefixPartial 13 420033) = some ⟨13, 2, 0, 780210, 420033, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_420033_780210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420033 ⟨780210, by decide⟩ :=
  accepted_of_selected 13 420033 ⟨780210, by decide⟩ ⟨13, 2, 0, 780210, 420033, 1725, 16384⟩
    (by decide) selected_cut_30717

theorem selected_cut_30718 : selected 8 ⟨780225, by decide⟩
    (prefixPartial 13 420034) = some ⟨13, 2, 0, 780225, 420034, 777, 16384⟩ := by
  decide +kernel

theorem context_13_420034_780225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420034 ⟨780225, by decide⟩ :=
  accepted_of_selected 13 420034 ⟨780225, by decide⟩ ⟨13, 2, 0, 780225, 420034, 777, 16384⟩
    (by decide) selected_cut_30718

theorem selected_cut_30719 : selected 8 ⟨780235, by decide⟩
    (prefixPartial 13 420035) = some ⟨13, 2, 0, 780235, 420035, 849, 16384⟩ := by
  decide +kernel

theorem context_13_420035_780235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420035 ⟨780235, by decide⟩ :=
  accepted_of_selected 13 420035 ⟨780235, by decide⟩ ⟨13, 2, 0, 780235, 420035, 849, 16384⟩
    (by decide) selected_cut_30719

theorem unmarked_context_12_105008_780236 : frontier 9 ⟨780236, by decide⟩
    (prefixCache 12 105008) (prefixPartial 12 105008) = false := by
  decide +kernel

theorem node_context_12_105008_780236 : EJMOriginalGlobalDAGData.nodes 9 ⟨780236, by decide⟩ =
    .split (coordinate 12) (![⟨780180, by decide⟩,⟨780210, by decide⟩,⟨780225, by decide⟩,⟨780235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105008_780236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105008 ⟨780236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105008
    ⟨780236, by decide⟩ (by decide) (![⟨780180, by decide⟩,⟨780210, by decide⟩,⟨780225, by decide⟩,⟨780235, by decide⟩]) unmarked_context_12_105008_780236 node_context_12_105008_780236
  intro a
  fin_cases a
  · exact context_13_420032_780180
  · exact context_13_420033_780210
  · exact context_13_420034_780225
  · exact context_13_420035_780235

theorem selected_cut_30720 : selected 8 ⟨780258, by decide⟩
    (prefixPartial 13 420036) = some ⟨13, 2, 0, 780258, 420036, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_420036_780258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420036 ⟨780258, by decide⟩ :=
  accepted_of_selected 13 420036 ⟨780258, by decide⟩ ⟨13, 2, 0, 780258, 420036, 1021, 16384⟩
    (by decide) selected_cut_30720

theorem selected_cut_30721 : selected 8 ⟨780303, by decide⟩
    (prefixPartial 13 420037) = some ⟨13, 2, 0, 780303, 420037, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_420037_780303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420037 ⟨780303, by decide⟩ :=
  accepted_of_selected 13 420037 ⟨780303, by decide⟩ ⟨13, 2, 0, 780303, 420037, 2221, 16384⟩
    (by decide) selected_cut_30721

theorem selected_cut_30722 : selected 8 ⟨780318, by decide⟩
    (prefixPartial 13 420038) = some ⟨13, 2, 0, 780318, 420038, 841, 16384⟩ := by
  decide +kernel

theorem context_13_420038_780318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420038 ⟨780318, by decide⟩ :=
  accepted_of_selected 13 420038 ⟨780318, by decide⟩ ⟨13, 2, 0, 780318, 420038, 841, 16384⟩
    (by decide) selected_cut_30722

theorem selected_cut_30723 : selected 8 ⟨780334, by decide⟩
    (prefixPartial 13 420039) = some ⟨13, 2, 0, 780334, 420039, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_420039_780334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 420039 ⟨780334, by decide⟩ :=
  accepted_of_selected 13 420039 ⟨780334, by decide⟩ ⟨13, 2, 0, 780334, 420039, 1113, 16384⟩
    (by decide) selected_cut_30723

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
