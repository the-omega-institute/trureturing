/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover446
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_84747_1173118 : frontier 10 ⟨1173118, by decide⟩
    (prefixCache 11 84747) (prefixPartial 11 84747) = false := by
  decide +kernel

theorem node_context_11_84747_1173118 : EJMOriginalGlobalDAGData.nodes 10 ⟨1173118, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1173014, by decide⟩,⟨1173066, by decide⟩,⟨1173117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84747_1173118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84747 ⟨1173118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84747
    ⟨1173118, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1173014, by decide⟩,⟨1173066, by decide⟩,⟨1173117, by decide⟩]) unmarked_context_11_84747_1173118 node_context_11_84747_1173118
  intro a
  fin_cases a
  · exact context_12_338988_1108174
  · exact context_12_338989_1173014
  · exact context_12_338990_1173066
  · exact context_12_338991_1173117

theorem unmarked_context_10_21186_1173119 : frontier 11 ⟨1173119, by decide⟩
    (prefixCache 10 21186) (prefixPartial 10 21186) = false := by
  decide +kernel

theorem node_context_10_21186_1173119 : EJMOriginalGlobalDAGData.nodes 11 ⟨1173119, by decide⟩ =
    .split (coordinate 10) (![⟨1172638, by decide⟩,⟨1172857, by decide⟩,⟨1172974, by decide⟩,⟨1173118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21186_1173119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21186 ⟨1173119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21186
    ⟨1173119, by decide⟩ (by decide) (![⟨1172638, by decide⟩,⟨1172857, by decide⟩,⟨1172974, by decide⟩,⟨1173118, by decide⟩]) unmarked_context_10_21186_1173119 node_context_10_21186_1173119
  intro a
  fin_cases a
  · exact context_11_84744_1172638
  · exact context_11_84745_1172857
  · exact context_11_84746_1172974
  · exact context_11_84747_1173118

theorem selected_cut_42916 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338992) = some ⟨12, 1, 0, 1108174, 338992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338992_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338992 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338992 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338992, 1, 65536⟩
    (by decide) selected_cut_42916

theorem selected_cut_42917 : selected 9 ⟨1173161, by decide⟩
    (prefixPartial 12 338993) = some ⟨12, 2, 0, 1173161, 338993, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_338993_1173161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338993 ⟨1173161, by decide⟩ :=
  accepted_of_selected 12 338993 ⟨1173161, by decide⟩ ⟨12, 2, 0, 1173161, 338993, 2301, 65536⟩
    (by decide) selected_cut_42917

theorem selected_cut_42918 : selected 9 ⟨1173199, by decide⟩
    (prefixPartial 12 338994) = some ⟨12, 2, 0, 1173199, 338994, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_338994_1173199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338994 ⟨1173199, by decide⟩ :=
  accepted_of_selected 12 338994 ⟨1173199, by decide⟩ ⟨12, 2, 0, 1173199, 338994, 2177, 65536⟩
    (by decide) selected_cut_42918

theorem selected_cut_42919 : selected 9 ⟨1173253, by decide⟩
    (prefixPartial 12 338995) = some ⟨12, 2, 0, 1173253, 338995, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_338995_1173253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338995 ⟨1173253, by decide⟩ :=
  accepted_of_selected 12 338995 ⟨1173253, by decide⟩ ⟨12, 2, 0, 1173253, 338995, 2645, 65536⟩
    (by decide) selected_cut_42919

theorem unmarked_context_11_84748_1173254 : frontier 10 ⟨1173254, by decide⟩
    (prefixCache 11 84748) (prefixPartial 11 84748) = false := by
  decide +kernel

theorem node_context_11_84748_1173254 : EJMOriginalGlobalDAGData.nodes 10 ⟨1173254, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1173161, by decide⟩,⟨1173199, by decide⟩,⟨1173253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84748_1173254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84748 ⟨1173254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84748
    ⟨1173254, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1173161, by decide⟩,⟨1173199, by decide⟩,⟨1173253, by decide⟩]) unmarked_context_11_84748_1173254 node_context_11_84748_1173254
  intro a
  fin_cases a
  · exact context_12_338992_1108174
  · exact context_12_338993_1173161
  · exact context_12_338994_1173199
  · exact context_12_338995_1173253

theorem selected_cut_42920 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338996) = some ⟨12, 1, 0, 1108174, 338996, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338996_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338996 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338996 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338996, 1, 65536⟩
    (by decide) selected_cut_42920

theorem selected_cut_42921 : selected 9 ⟨1173309, by decide⟩
    (prefixPartial 12 338997) = some ⟨12, 2, 0, 1173309, 338997, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_338997_1173309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338997 ⟨1173309, by decide⟩ :=
  accepted_of_selected 12 338997 ⟨1173309, by decide⟩ ⟨12, 2, 0, 1173309, 338997, 2525, 65536⟩
    (by decide) selected_cut_42921

theorem selected_cut_42922 : selected 9 ⟨1173370, by decide⟩
    (prefixPartial 12 338998) = some ⟨12, 2, 0, 1173370, 338998, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_338998_1173370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338998 ⟨1173370, by decide⟩ :=
  accepted_of_selected 12 338998 ⟨1173370, by decide⟩ ⟨12, 2, 0, 1173370, 338998, 2573, 65536⟩
    (by decide) selected_cut_42922

theorem selected_cut_42923 : selected 9 ⟨1173426, by decide⟩
    (prefixPartial 12 338999) = some ⟨12, 2, 0, 1173426, 338999, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_338999_1173426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338999 ⟨1173426, by decide⟩ :=
  accepted_of_selected 12 338999 ⟨1173426, by decide⟩ ⟨12, 2, 0, 1173426, 338999, 3017, 65536⟩
    (by decide) selected_cut_42923

theorem unmarked_context_11_84749_1173427 : frontier 10 ⟨1173427, by decide⟩
    (prefixCache 11 84749) (prefixPartial 11 84749) = false := by
  decide +kernel

theorem node_context_11_84749_1173427 : EJMOriginalGlobalDAGData.nodes 10 ⟨1173427, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1173309, by decide⟩,⟨1173370, by decide⟩,⟨1173426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84749_1173427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84749 ⟨1173427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84749
    ⟨1173427, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1173309, by decide⟩,⟨1173370, by decide⟩,⟨1173426, by decide⟩]) unmarked_context_11_84749_1173427 node_context_11_84749_1173427
  intro a
  fin_cases a
  · exact context_12_338996_1108174
  · exact context_12_338997_1173309
  · exact context_12_338998_1173370
  · exact context_12_338999_1173426

theorem selected_cut_42924 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339000) = some ⟨12, 1, 0, 1108174, 339000, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339000_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339000 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339000 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339000, 1, 65536⟩
    (by decide) selected_cut_42924

theorem selected_cut_42925 : selected 9 ⟨1173459, by decide⟩
    (prefixPartial 12 339001) = some ⟨12, 2, 0, 1173459, 339001, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_339001_1173459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339001 ⟨1173459, by decide⟩ :=
  accepted_of_selected 12 339001 ⟨1173459, by decide⟩ ⟨12, 2, 0, 1173459, 339001, 2257, 65536⟩
    (by decide) selected_cut_42925

theorem selected_cut_42926 : selected 9 ⟨1173502, by decide⟩
    (prefixPartial 12 339002) = some ⟨12, 2, 0, 1173502, 339002, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_339002_1173502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339002 ⟨1173502, by decide⟩ :=
  accepted_of_selected 12 339002 ⟨1173502, by decide⟩ ⟨12, 2, 0, 1173502, 339002, 2141, 65536⟩
    (by decide) selected_cut_42926

theorem selected_cut_42927 : selected 9 ⟨1173552, by decide⟩
    (prefixPartial 12 339003) = some ⟨12, 2, 0, 1173552, 339003, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_339003_1173552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339003 ⟨1173552, by decide⟩ :=
  accepted_of_selected 12 339003 ⟨1173552, by decide⟩ ⟨12, 2, 0, 1173552, 339003, 2641, 65536⟩
    (by decide) selected_cut_42927

theorem unmarked_context_11_84750_1173553 : frontier 10 ⟨1173553, by decide⟩
    (prefixCache 11 84750) (prefixPartial 11 84750) = false := by
  decide +kernel

theorem node_context_11_84750_1173553 : EJMOriginalGlobalDAGData.nodes 10 ⟨1173553, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1173459, by decide⟩,⟨1173502, by decide⟩,⟨1173552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84750_1173553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84750 ⟨1173553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84750
    ⟨1173553, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1173459, by decide⟩,⟨1173502, by decide⟩,⟨1173552, by decide⟩]) unmarked_context_11_84750_1173553 node_context_11_84750_1173553
  intro a
  fin_cases a
  · exact context_12_339000_1108174
  · exact context_12_339001_1173459
  · exact context_12_339002_1173502
  · exact context_12_339003_1173552

theorem selected_cut_42928 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84751) = some ⟨11, 1, 0, 977886, 84751, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84751_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84751 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84751 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84751, 1, 262144⟩
    (by decide) selected_cut_42928

theorem unmarked_context_10_21187_1173554 : frontier 11 ⟨1173554, by decide⟩
    (prefixCache 10 21187) (prefixPartial 10 21187) = false := by
  decide +kernel

theorem node_context_10_21187_1173554 : EJMOriginalGlobalDAGData.nodes 11 ⟨1173554, by decide⟩ =
    .split (coordinate 10) (![⟨1173254, by decide⟩,⟨1173427, by decide⟩,⟨1173553, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21187_1173554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21187 ⟨1173554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21187
    ⟨1173554, by decide⟩ (by decide) (![⟨1173254, by decide⟩,⟨1173427, by decide⟩,⟨1173553, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21187_1173554 node_context_10_21187_1173554
  intro a
  fin_cases a
  · exact context_11_84748_1173254
  · exact context_11_84749_1173427
  · exact context_11_84750_1173553
  · exact context_11_84751_977886

theorem unmarked_context_9_5296_1173555 : frontier 12 ⟨1173555, by decide⟩
    (prefixCache 9 5296) (prefixPartial 9 5296) = false := by
  decide +kernel

theorem node_context_9_5296_1173555 : EJMOriginalGlobalDAGData.nodes 12 ⟨1173555, by decide⟩ =
    .split (coordinate 9) (![⟨1171825, by decide⟩,⟨1172463, by decide⟩,⟨1173119, by decide⟩,⟨1173554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5296_1173555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5296 ⟨1173555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5296
    ⟨1173555, by decide⟩ (by decide) (![⟨1171825, by decide⟩,⟨1172463, by decide⟩,⟨1173119, by decide⟩,⟨1173554, by decide⟩]) unmarked_context_9_5296_1173555 node_context_9_5296_1173555
  intro a
  fin_cases a
  · exact context_10_21184_1171825
  · exact context_10_21185_1172463
  · exact context_10_21186_1173119
  · exact context_10_21187_1173554

theorem selected_cut_42929 : selected 10 ⟨1173597, by decide⟩
    (prefixPartial 11 84752) = some ⟨11, 2, 0, 1173597, 84752, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_84752_1173597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84752 ⟨1173597, by decide⟩ :=
  accepted_of_selected 11 84752 ⟨1173597, by decide⟩ ⟨11, 2, 0, 1173597, 84752, 2089, 262144⟩
    (by decide) selected_cut_42929

theorem selected_cut_42930 : selected 9 ⟨1173630, by decide⟩
    (prefixPartial 12 339012) = some ⟨12, 2, 0, 1173630, 339012, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_339012_1173630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339012 ⟨1173630, by decide⟩ :=
  accepted_of_selected 12 339012 ⟨1173630, by decide⟩ ⟨12, 2, 0, 1173630, 339012, 1797, 65536⟩
    (by decide) selected_cut_42930

theorem selected_cut_42931 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 339013) = some ⟨12, 1, 0, 170504, 339013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339013_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339013 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 339013 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 339013, 1, 65536⟩
    (by decide) selected_cut_42931

theorem selected_cut_42932 : selected 9 ⟨1173667, by decide⟩
    (prefixPartial 12 339014) = some ⟨12, 2, 0, 1173667, 339014, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_339014_1173667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339014 ⟨1173667, by decide⟩ :=
  accepted_of_selected 12 339014 ⟨1173667, by decide⟩ ⟨12, 2, 0, 1173667, 339014, 2125, 65536⟩
    (by decide) selected_cut_42932

theorem selected_cut_42933 : selected 9 ⟨1173706, by decide⟩
    (prefixPartial 12 339015) = some ⟨12, 2, 0, 1173706, 339015, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_339015_1173706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339015 ⟨1173706, by decide⟩ :=
  accepted_of_selected 12 339015 ⟨1173706, by decide⟩ ⟨12, 2, 0, 1173706, 339015, 2117, 65536⟩
    (by decide) selected_cut_42933

theorem unmarked_context_11_84753_1173707 : frontier 10 ⟨1173707, by decide⟩
    (prefixCache 11 84753) (prefixPartial 11 84753) = false := by
  decide +kernel

theorem node_context_11_84753_1173707 : EJMOriginalGlobalDAGData.nodes 10 ⟨1173707, by decide⟩ =
    .split (coordinate 11) (![⟨1173630, by decide⟩,⟨170504, by decide⟩,⟨1173667, by decide⟩,⟨1173706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84753_1173707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84753 ⟨1173707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84753
    ⟨1173707, by decide⟩ (by decide) (![⟨1173630, by decide⟩,⟨170504, by decide⟩,⟨1173667, by decide⟩,⟨1173706, by decide⟩]) unmarked_context_11_84753_1173707 node_context_11_84753_1173707
  intro a
  fin_cases a
  · exact context_12_339012_1173630
  · exact context_12_339013_170504
  · exact context_12_339014_1173667
  · exact context_12_339015_1173706

theorem selected_cut_42934 : selected 9 ⟨1173733, by decide⟩
    (prefixPartial 12 339016) = some ⟨12, 2, 0, 1173733, 339016, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_339016_1173733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339016 ⟨1173733, by decide⟩ :=
  accepted_of_selected 12 339016 ⟨1173733, by decide⟩ ⟨12, 2, 0, 1173733, 339016, 1657, 65536⟩
    (by decide) selected_cut_42934

theorem selected_cut_42935 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 339017) = some ⟨12, 1, 0, 126371, 339017, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339017_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339017 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 339017 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 339017, 1, 65536⟩
    (by decide) selected_cut_42935

theorem selected_cut_42936 : selected 9 ⟨1173768, by decide⟩
    (prefixPartial 12 339018) = some ⟨12, 2, 0, 1173768, 339018, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_339018_1173768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339018 ⟨1173768, by decide⟩ :=
  accepted_of_selected 12 339018 ⟨1173768, by decide⟩ ⟨12, 2, 0, 1173768, 339018, 1917, 65536⟩
    (by decide) selected_cut_42936

theorem selected_cut_42937 : selected 9 ⟨1173804, by decide⟩
    (prefixPartial 12 339019) = some ⟨12, 2, 0, 1173804, 339019, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_339019_1173804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339019 ⟨1173804, by decide⟩ :=
  accepted_of_selected 12 339019 ⟨1173804, by decide⟩ ⟨12, 2, 0, 1173804, 339019, 2021, 65536⟩
    (by decide) selected_cut_42937

theorem unmarked_context_11_84754_1173805 : frontier 10 ⟨1173805, by decide⟩
    (prefixCache 11 84754) (prefixPartial 11 84754) = false := by
  decide +kernel

theorem node_context_11_84754_1173805 : EJMOriginalGlobalDAGData.nodes 10 ⟨1173805, by decide⟩ =
    .split (coordinate 11) (![⟨1173733, by decide⟩,⟨126371, by decide⟩,⟨1173768, by decide⟩,⟨1173804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84754_1173805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84754 ⟨1173805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84754
    ⟨1173805, by decide⟩ (by decide) (![⟨1173733, by decide⟩,⟨126371, by decide⟩,⟨1173768, by decide⟩,⟨1173804, by decide⟩]) unmarked_context_11_84754_1173805 node_context_11_84754_1173805
  intro a
  fin_cases a
  · exact context_12_339016_1173733
  · exact context_12_339017_126371
  · exact context_12_339018_1173768
  · exact context_12_339019_1173804

theorem selected_cut_42938 : selected 10 ⟨1173852, by decide⟩
    (prefixPartial 11 84755) = some ⟨11, 2, 0, 1173852, 84755, 3173, 262144⟩ := by
  decide +kernel

theorem context_11_84755_1173852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84755 ⟨1173852, by decide⟩ :=
  accepted_of_selected 11 84755 ⟨1173852, by decide⟩ ⟨11, 2, 0, 1173852, 84755, 3173, 262144⟩
    (by decide) selected_cut_42938

theorem unmarked_context_10_21188_1173853 : frontier 11 ⟨1173853, by decide⟩
    (prefixCache 10 21188) (prefixPartial 10 21188) = false := by
  decide +kernel

theorem node_context_10_21188_1173853 : EJMOriginalGlobalDAGData.nodes 11 ⟨1173853, by decide⟩ =
    .split (coordinate 10) (![⟨1173597, by decide⟩,⟨1173707, by decide⟩,⟨1173805, by decide⟩,⟨1173852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21188_1173853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21188 ⟨1173853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21188
    ⟨1173853, by decide⟩ (by decide) (![⟨1173597, by decide⟩,⟨1173707, by decide⟩,⟨1173805, by decide⟩,⟨1173852, by decide⟩]) unmarked_context_10_21188_1173853 node_context_10_21188_1173853
  intro a
  fin_cases a
  · exact context_11_84752_1173597
  · exact context_11_84753_1173707
  · exact context_11_84754_1173805
  · exact context_11_84755_1173852

theorem selected_cut_42939 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21189) = some ⟨10, 1, 0, 893098, 21189, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21189_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21189 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21189 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21189, 1, 1048576⟩
    (by decide) selected_cut_42939

theorem selected_cut_42940 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 339040) = some ⟨12, 1, 0, 985390, 339040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339040_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339040 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 339040 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 339040, 1, 65536⟩
    (by decide) selected_cut_42940

theorem selected_cut_42941 : selected 9 ⟨1173883, by decide⟩
    (prefixPartial 12 339041) = some ⟨12, 2, 0, 1173883, 339041, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_339041_1173883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339041 ⟨1173883, by decide⟩ :=
  accepted_of_selected 12 339041 ⟨1173883, by decide⟩ ⟨12, 2, 0, 1173883, 339041, 1673, 65536⟩
    (by decide) selected_cut_42941

theorem selected_cut_42942 : selected 9 ⟨1173916, by decide⟩
    (prefixPartial 12 339042) = some ⟨12, 2, 0, 1173916, 339042, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_339042_1173916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339042 ⟨1173916, by decide⟩ :=
  accepted_of_selected 12 339042 ⟨1173916, by decide⟩ ⟨12, 2, 0, 1173916, 339042, 1817, 65536⟩
    (by decide) selected_cut_42942

theorem selected_cut_42943 : selected 9 ⟨1173947, by decide⟩
    (prefixPartial 12 339043) = some ⟨12, 2, 0, 1173947, 339043, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_339043_1173947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339043 ⟨1173947, by decide⟩ :=
  accepted_of_selected 12 339043 ⟨1173947, by decide⟩ ⟨12, 2, 0, 1173947, 339043, 1833, 65536⟩
    (by decide) selected_cut_42943

theorem unmarked_context_11_84760_1173948 : frontier 10 ⟨1173948, by decide⟩
    (prefixCache 11 84760) (prefixPartial 11 84760) = false := by
  decide +kernel

theorem node_context_11_84760_1173948 : EJMOriginalGlobalDAGData.nodes 10 ⟨1173948, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1173883, by decide⟩,⟨1173916, by decide⟩,⟨1173947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84760_1173948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84760 ⟨1173948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84760
    ⟨1173948, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1173883, by decide⟩,⟨1173916, by decide⟩,⟨1173947, by decide⟩]) unmarked_context_11_84760_1173948 node_context_11_84760_1173948
  intro a
  fin_cases a
  · exact context_12_339040_985390
  · exact context_12_339041_1173883
  · exact context_12_339042_1173916
  · exact context_12_339043_1173947

theorem selected_cut_42944 : selected 9 ⟨1173981, by decide⟩
    (prefixPartial 12 339044) = some ⟨12, 2, 0, 1173981, 339044, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_339044_1173981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339044 ⟨1173981, by decide⟩ :=
  accepted_of_selected 12 339044 ⟨1173981, by decide⟩ ⟨12, 2, 0, 1173981, 339044, 1757, 65536⟩
    (by decide) selected_cut_42944

theorem selected_cut_42945 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 339045) = some ⟨12, 1, 0, 642794, 339045, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339045_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339045 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 339045 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 339045, 1, 65536⟩
    (by decide) selected_cut_42945

theorem selected_cut_42946 : selected 9 ⟨1174017, by decide⟩
    (prefixPartial 12 339046) = some ⟨12, 2, 0, 1174017, 339046, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_339046_1174017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339046 ⟨1174017, by decide⟩ :=
  accepted_of_selected 12 339046 ⟨1174017, by decide⟩ ⟨12, 2, 0, 1174017, 339046, 1945, 65536⟩
    (by decide) selected_cut_42946

theorem selected_cut_42947 : selected 9 ⟨1174048, by decide⟩
    (prefixPartial 12 339047) = some ⟨12, 2, 0, 1174048, 339047, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_339047_1174048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339047 ⟨1174048, by decide⟩ :=
  accepted_of_selected 12 339047 ⟨1174048, by decide⟩ ⟨12, 2, 0, 1174048, 339047, 1929, 65536⟩
    (by decide) selected_cut_42947

theorem unmarked_context_11_84761_1174049 : frontier 10 ⟨1174049, by decide⟩
    (prefixCache 11 84761) (prefixPartial 11 84761) = false := by
  decide +kernel

theorem node_context_11_84761_1174049 : EJMOriginalGlobalDAGData.nodes 10 ⟨1174049, by decide⟩ =
    .split (coordinate 11) (![⟨1173981, by decide⟩,⟨642794, by decide⟩,⟨1174017, by decide⟩,⟨1174048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84761_1174049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84761 ⟨1174049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84761
    ⟨1174049, by decide⟩ (by decide) (![⟨1173981, by decide⟩,⟨642794, by decide⟩,⟨1174017, by decide⟩,⟨1174048, by decide⟩]) unmarked_context_11_84761_1174049 node_context_11_84761_1174049
  intro a
  fin_cases a
  · exact context_12_339044_1173981
  · exact context_12_339045_642794
  · exact context_12_339046_1174017
  · exact context_12_339047_1174048

theorem selected_cut_42948 : selected 9 ⟨1174067, by decide⟩
    (prefixPartial 12 339048) = some ⟨12, 2, 0, 1174067, 339048, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_339048_1174067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339048 ⟨1174067, by decide⟩ :=
  accepted_of_selected 12 339048 ⟨1174067, by decide⟩ ⟨12, 2, 0, 1174067, 339048, 1425, 65536⟩
    (by decide) selected_cut_42948

theorem selected_cut_42949 : selected 9 ⟨1174089, by decide⟩
    (prefixPartial 12 339049) = some ⟨12, 2, 0, 1174089, 339049, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_339049_1174089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339049 ⟨1174089, by decide⟩ :=
  accepted_of_selected 12 339049 ⟨1174089, by decide⟩ ⟨12, 2, 0, 1174089, 339049, 1581, 65536⟩
    (by decide) selected_cut_42949

theorem selected_cut_42950 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 339050) = some ⟨12, 1, 0, 1172910, 339050, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339050_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339050 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 339050 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 339050, 1, 65536⟩
    (by decide) selected_cut_42950

theorem selected_cut_42951 : selected 9 ⟨1174120, by decide⟩
    (prefixPartial 12 339051) = some ⟨12, 2, 0, 1174120, 339051, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_339051_1174120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339051 ⟨1174120, by decide⟩ :=
  accepted_of_selected 12 339051 ⟨1174120, by decide⟩ ⟨12, 2, 0, 1174120, 339051, 1845, 65536⟩
    (by decide) selected_cut_42951

theorem unmarked_context_11_84762_1174121 : frontier 10 ⟨1174121, by decide⟩
    (prefixCache 11 84762) (prefixPartial 11 84762) = false := by
  decide +kernel

theorem node_context_11_84762_1174121 : EJMOriginalGlobalDAGData.nodes 10 ⟨1174121, by decide⟩ =
    .split (coordinate 11) (![⟨1174067, by decide⟩,⟨1174089, by decide⟩,⟨1172910, by decide⟩,⟨1174120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84762_1174121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84762 ⟨1174121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84762
    ⟨1174121, by decide⟩ (by decide) (![⟨1174067, by decide⟩,⟨1174089, by decide⟩,⟨1172910, by decide⟩,⟨1174120, by decide⟩]) unmarked_context_11_84762_1174121 node_context_11_84762_1174121
  intro a
  fin_cases a
  · exact context_12_339048_1174067
  · exact context_12_339049_1174089
  · exact context_12_339050_1172910
  · exact context_12_339051_1174120

theorem selected_cut_42952 : selected 9 ⟨1174137, by decide⟩
    (prefixPartial 12 339052) = some ⟨12, 2, 0, 1174137, 339052, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_339052_1174137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339052 ⟨1174137, by decide⟩ :=
  accepted_of_selected 12 339052 ⟨1174137, by decide⟩ ⟨12, 2, 0, 1174137, 339052, 1357, 65536⟩
    (by decide) selected_cut_42952

theorem selected_cut_42953 : selected 9 ⟨1174158, by decide⟩
    (prefixPartial 12 339053) = some ⟨12, 2, 0, 1174158, 339053, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_339053_1174158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339053 ⟨1174158, by decide⟩ :=
  accepted_of_selected 12 339053 ⟨1174158, by decide⟩ ⟨12, 2, 0, 1174158, 339053, 1417, 65536⟩
    (by decide) selected_cut_42953

theorem selected_cut_42954 : selected 9 ⟨1174181, by decide⟩
    (prefixPartial 12 339054) = some ⟨12, 2, 0, 1174181, 339054, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_339054_1174181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339054 ⟨1174181, by decide⟩ :=
  accepted_of_selected 12 339054 ⟨1174181, by decide⟩ ⟨12, 2, 0, 1174181, 339054, 1473, 65536⟩
    (by decide) selected_cut_42954

theorem selected_cut_42955 : selected 9 ⟨1174207, by decide⟩
    (prefixPartial 12 339055) = some ⟨12, 2, 0, 1174207, 339055, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_339055_1174207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339055 ⟨1174207, by decide⟩ :=
  accepted_of_selected 12 339055 ⟨1174207, by decide⟩ ⟨12, 2, 0, 1174207, 339055, 1541, 65536⟩
    (by decide) selected_cut_42955

theorem unmarked_context_11_84763_1174208 : frontier 10 ⟨1174208, by decide⟩
    (prefixCache 11 84763) (prefixPartial 11 84763) = false := by
  decide +kernel

theorem node_context_11_84763_1174208 : EJMOriginalGlobalDAGData.nodes 10 ⟨1174208, by decide⟩ =
    .split (coordinate 11) (![⟨1174137, by decide⟩,⟨1174158, by decide⟩,⟨1174181, by decide⟩,⟨1174207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84763_1174208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84763 ⟨1174208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84763
    ⟨1174208, by decide⟩ (by decide) (![⟨1174137, by decide⟩,⟨1174158, by decide⟩,⟨1174181, by decide⟩,⟨1174207, by decide⟩]) unmarked_context_11_84763_1174208 node_context_11_84763_1174208
  intro a
  fin_cases a
  · exact context_12_339052_1174137
  · exact context_12_339053_1174158
  · exact context_12_339054_1174181
  · exact context_12_339055_1174207

theorem unmarked_context_10_21190_1174209 : frontier 11 ⟨1174209, by decide⟩
    (prefixCache 10 21190) (prefixPartial 10 21190) = false := by
  decide +kernel

theorem node_context_10_21190_1174209 : EJMOriginalGlobalDAGData.nodes 11 ⟨1174209, by decide⟩ =
    .split (coordinate 10) (![⟨1173948, by decide⟩,⟨1174049, by decide⟩,⟨1174121, by decide⟩,⟨1174208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21190_1174209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21190 ⟨1174209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21190
    ⟨1174209, by decide⟩ (by decide) (![⟨1173948, by decide⟩,⟨1174049, by decide⟩,⟨1174121, by decide⟩,⟨1174208, by decide⟩]) unmarked_context_10_21190_1174209 node_context_10_21190_1174209
  intro a
  fin_cases a
  · exact context_11_84760_1173948
  · exact context_11_84761_1174049
  · exact context_11_84762_1174121
  · exact context_11_84763_1174208

theorem selected_cut_42956 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 339056) = some ⟨12, 1, 0, 985390, 339056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339056_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339056 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 339056 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 339056, 1, 65536⟩
    (by decide) selected_cut_42956

theorem selected_cut_42957 : selected 9 ⟨1174233, by decide⟩
    (prefixPartial 12 339057) = some ⟨12, 2, 0, 1174233, 339057, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_339057_1174233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339057 ⟨1174233, by decide⟩ :=
  accepted_of_selected 12 339057 ⟨1174233, by decide⟩ ⟨12, 2, 0, 1174233, 339057, 1569, 65536⟩
    (by decide) selected_cut_42957

theorem selected_cut_42958 : selected 9 ⟨1174259, by decide⟩
    (prefixPartial 12 339058) = some ⟨12, 2, 0, 1174259, 339058, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_339058_1174259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339058 ⟨1174259, by decide⟩ :=
  accepted_of_selected 12 339058 ⟨1174259, by decide⟩ ⟨12, 2, 0, 1174259, 339058, 1629, 65536⟩
    (by decide) selected_cut_42958

theorem selected_cut_42959 : selected 9 ⟨1174292, by decide⟩
    (prefixPartial 12 339059) = some ⟨12, 2, 0, 1174292, 339059, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_339059_1174292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339059 ⟨1174292, by decide⟩ :=
  accepted_of_selected 12 339059 ⟨1174292, by decide⟩ ⟨12, 2, 0, 1174292, 339059, 1793, 65536⟩
    (by decide) selected_cut_42959

theorem unmarked_context_11_84764_1174293 : frontier 10 ⟨1174293, by decide⟩
    (prefixCache 11 84764) (prefixPartial 11 84764) = false := by
  decide +kernel

theorem node_context_11_84764_1174293 : EJMOriginalGlobalDAGData.nodes 10 ⟨1174293, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1174233, by decide⟩,⟨1174259, by decide⟩,⟨1174292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84764_1174293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84764 ⟨1174293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84764
    ⟨1174293, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1174233, by decide⟩,⟨1174259, by decide⟩,⟨1174292, by decide⟩]) unmarked_context_11_84764_1174293 node_context_11_84764_1174293
  intro a
  fin_cases a
  · exact context_12_339056_985390
  · exact context_12_339057_1174233
  · exact context_12_339058_1174259
  · exact context_12_339059_1174292

theorem selected_cut_42960 : selected 9 ⟨1174324, by decide⟩
    (prefixPartial 12 339060) = some ⟨12, 2, 0, 1174324, 339060, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_339060_1174324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339060 ⟨1174324, by decide⟩ :=
  accepted_of_selected 12 339060 ⟨1174324, by decide⟩ ⟨12, 2, 0, 1174324, 339060, 1541, 65536⟩
    (by decide) selected_cut_42960

theorem selected_cut_42961 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 339061) = some ⟨12, 1, 0, 642794, 339061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339061_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339061 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 339061 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 339061, 1, 65536⟩
    (by decide) selected_cut_42961

theorem selected_cut_42962 : selected 9 ⟨1174355, by decide⟩
    (prefixPartial 12 339062) = some ⟨12, 2, 0, 1174355, 339062, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_339062_1174355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339062 ⟨1174355, by decide⟩ :=
  accepted_of_selected 12 339062 ⟨1174355, by decide⟩ ⟨12, 2, 0, 1174355, 339062, 1649, 65536⟩
    (by decide) selected_cut_42962

theorem selected_cut_42963 : selected 9 ⟨1174398, by decide⟩
    (prefixPartial 12 339063) = some ⟨12, 2, 0, 1174398, 339063, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_339063_1174398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339063 ⟨1174398, by decide⟩ :=
  accepted_of_selected 12 339063 ⟨1174398, by decide⟩ ⟨12, 2, 0, 1174398, 339063, 1805, 65536⟩
    (by decide) selected_cut_42963

theorem unmarked_context_11_84765_1174399 : frontier 10 ⟨1174399, by decide⟩
    (prefixCache 11 84765) (prefixPartial 11 84765) = false := by
  decide +kernel

theorem node_context_11_84765_1174399 : EJMOriginalGlobalDAGData.nodes 10 ⟨1174399, by decide⟩ =
    .split (coordinate 11) (![⟨1174324, by decide⟩,⟨642794, by decide⟩,⟨1174355, by decide⟩,⟨1174398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84765_1174399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84765 ⟨1174399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84765
    ⟨1174399, by decide⟩ (by decide) (![⟨1174324, by decide⟩,⟨642794, by decide⟩,⟨1174355, by decide⟩,⟨1174398, by decide⟩]) unmarked_context_11_84765_1174399 node_context_11_84765_1174399
  intro a
  fin_cases a
  · exact context_12_339060_1174324
  · exact context_12_339061_642794
  · exact context_12_339062_1174355
  · exact context_12_339063_1174398

theorem selected_cut_42964 : selected 9 ⟨1174420, by decide⟩
    (prefixPartial 12 339064) = some ⟨12, 2, 0, 1174420, 339064, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_339064_1174420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339064 ⟨1174420, by decide⟩ :=
  accepted_of_selected 12 339064 ⟨1174420, by decide⟩ ⟨12, 2, 0, 1174420, 339064, 1221, 65536⟩
    (by decide) selected_cut_42964

theorem selected_cut_42965 : selected 9 ⟨1174439, by decide⟩
    (prefixPartial 12 339065) = some ⟨12, 2, 0, 1174439, 339065, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_339065_1174439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339065 ⟨1174439, by decide⟩ :=
  accepted_of_selected 12 339065 ⟨1174439, by decide⟩ ⟨12, 2, 0, 1174439, 339065, 1341, 65536⟩
    (by decide) selected_cut_42965

theorem selected_cut_42966 : selected 9 ⟨1174456, by decide⟩
    (prefixPartial 12 339066) = some ⟨12, 2, 0, 1174456, 339066, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_339066_1174456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339066 ⟨1174456, by decide⟩ :=
  accepted_of_selected 12 339066 ⟨1174456, by decide⟩ ⟨12, 2, 0, 1174456, 339066, 1225, 65536⟩
    (by decide) selected_cut_42966

theorem selected_cut_42967 : selected 9 ⟨1174482, by decide⟩
    (prefixPartial 12 339067) = some ⟨12, 2, 0, 1174482, 339067, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_339067_1174482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339067 ⟨1174482, by decide⟩ :=
  accepted_of_selected 12 339067 ⟨1174482, by decide⟩ ⟨12, 2, 0, 1174482, 339067, 1513, 65536⟩
    (by decide) selected_cut_42967

theorem unmarked_context_11_84766_1174483 : frontier 10 ⟨1174483, by decide⟩
    (prefixCache 11 84766) (prefixPartial 11 84766) = false := by
  decide +kernel

theorem node_context_11_84766_1174483 : EJMOriginalGlobalDAGData.nodes 10 ⟨1174483, by decide⟩ =
    .split (coordinate 11) (![⟨1174420, by decide⟩,⟨1174439, by decide⟩,⟨1174456, by decide⟩,⟨1174482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84766_1174483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84766 ⟨1174483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84766
    ⟨1174483, by decide⟩ (by decide) (![⟨1174420, by decide⟩,⟨1174439, by decide⟩,⟨1174456, by decide⟩,⟨1174482, by decide⟩]) unmarked_context_11_84766_1174483 node_context_11_84766_1174483
  intro a
  fin_cases a
  · exact context_12_339064_1174420
  · exact context_12_339065_1174439
  · exact context_12_339066_1174456
  · exact context_12_339067_1174482

theorem selected_cut_42968 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84767) = some ⟨11, 1, 0, 977886, 84767, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84767_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84767 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84767 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84767, 1, 262144⟩
    (by decide) selected_cut_42968

theorem unmarked_context_10_21191_1174484 : frontier 11 ⟨1174484, by decide⟩
    (prefixCache 10 21191) (prefixPartial 10 21191) = false := by
  decide +kernel

theorem node_context_10_21191_1174484 : EJMOriginalGlobalDAGData.nodes 11 ⟨1174484, by decide⟩ =
    .split (coordinate 10) (![⟨1174293, by decide⟩,⟨1174399, by decide⟩,⟨1174483, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21191_1174484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21191 ⟨1174484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21191
    ⟨1174484, by decide⟩ (by decide) (![⟨1174293, by decide⟩,⟨1174399, by decide⟩,⟨1174483, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21191_1174484 node_context_10_21191_1174484
  intro a
  fin_cases a
  · exact context_11_84764_1174293
  · exact context_11_84765_1174399
  · exact context_11_84766_1174483
  · exact context_11_84767_977886

theorem unmarked_context_9_5297_1174485 : frontier 12 ⟨1174485, by decide⟩
    (prefixCache 9 5297) (prefixPartial 9 5297) = false := by
  decide +kernel

theorem node_context_9_5297_1174485 : EJMOriginalGlobalDAGData.nodes 12 ⟨1174485, by decide⟩ =
    .split (coordinate 9) (![⟨1173853, by decide⟩,⟨893098, by decide⟩,⟨1174209, by decide⟩,⟨1174484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5297_1174485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5297 ⟨1174485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5297
    ⟨1174485, by decide⟩ (by decide) (![⟨1173853, by decide⟩,⟨893098, by decide⟩,⟨1174209, by decide⟩,⟨1174484, by decide⟩]) unmarked_context_9_5297_1174485 node_context_9_5297_1174485
  intro a
  fin_cases a
  · exact context_10_21188_1173853
  · exact context_10_21189_893098
  · exact context_10_21190_1174209
  · exact context_10_21191_1174484

theorem selected_cut_42969 : selected 10 ⟨1174569, by decide⟩
    (prefixPartial 11 84768) = some ⟨11, 2, 0, 1174569, 84768, 3401, 262144⟩ := by
  decide +kernel

theorem context_11_84768_1174569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84768 ⟨1174569, by decide⟩ :=
  accepted_of_selected 11 84768 ⟨1174569, by decide⟩ ⟨11, 2, 0, 1174569, 84768, 3401, 262144⟩
    (by decide) selected_cut_42969

theorem selected_cut_42970 : selected 9 ⟨1174589, by decide⟩
    (prefixPartial 12 339076) = some ⟨12, 2, 0, 1174589, 339076, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_339076_1174589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339076 ⟨1174589, by decide⟩ :=
  accepted_of_selected 12 339076 ⟨1174589, by decide⟩ ⟨12, 2, 0, 1174589, 339076, 1317, 65536⟩
    (by decide) selected_cut_42970

theorem selected_cut_42971 : selected 9 ⟨1174607, by decide⟩
    (prefixPartial 12 339077) = some ⟨12, 2, 0, 1174607, 339077, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_339077_1174607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339077 ⟨1174607, by decide⟩ :=
  accepted_of_selected 12 339077 ⟨1174607, by decide⟩ ⟨12, 2, 0, 1174607, 339077, 1409, 65536⟩
    (by decide) selected_cut_42971

theorem selected_cut_42972 : selected 9 ⟨1174629, by decide⟩
    (prefixPartial 12 339078) = some ⟨12, 2, 0, 1174629, 339078, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_339078_1174629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339078 ⟨1174629, by decide⟩ :=
  accepted_of_selected 12 339078 ⟨1174629, by decide⟩ ⟨12, 2, 0, 1174629, 339078, 1409, 65536⟩
    (by decide) selected_cut_42972

theorem selected_cut_42973 : selected 9 ⟨1174659, by decide⟩
    (prefixPartial 12 339079) = some ⟨12, 2, 0, 1174659, 339079, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_339079_1174659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339079 ⟨1174659, by decide⟩ :=
  accepted_of_selected 12 339079 ⟨1174659, by decide⟩ ⟨12, 2, 0, 1174659, 339079, 1589, 65536⟩
    (by decide) selected_cut_42973

theorem unmarked_context_11_84769_1174660 : frontier 10 ⟨1174660, by decide⟩
    (prefixCache 11 84769) (prefixPartial 11 84769) = false := by
  decide +kernel

theorem node_context_11_84769_1174660 : EJMOriginalGlobalDAGData.nodes 10 ⟨1174660, by decide⟩ =
    .split (coordinate 11) (![⟨1174589, by decide⟩,⟨1174607, by decide⟩,⟨1174629, by decide⟩,⟨1174659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84769_1174660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84769 ⟨1174660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84769
    ⟨1174660, by decide⟩ (by decide) (![⟨1174589, by decide⟩,⟨1174607, by decide⟩,⟨1174629, by decide⟩,⟨1174659, by decide⟩]) unmarked_context_11_84769_1174660 node_context_11_84769_1174660
  intro a
  fin_cases a
  · exact context_12_339076_1174589
  · exact context_12_339077_1174607
  · exact context_12_339078_1174629
  · exact context_12_339079_1174659

theorem selected_cut_42974 : selected 10 ⟨1174722, by decide⟩
    (prefixPartial 11 84770) = some ⟨11, 2, 0, 1174722, 84770, 3993, 262144⟩ := by
  decide +kernel

theorem context_11_84770_1174722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84770 ⟨1174722, by decide⟩ :=
  accepted_of_selected 11 84770 ⟨1174722, by decide⟩ ⟨11, 2, 0, 1174722, 84770, 3993, 262144⟩
    (by decide) selected_cut_42974

theorem selected_cut_42975 : selected 10 ⟨1174776, by decide⟩
    (prefixPartial 11 84771) = some ⟨11, 2, 0, 1174776, 84771, 3457, 262144⟩ := by
  decide +kernel

theorem context_11_84771_1174776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84771 ⟨1174776, by decide⟩ :=
  accepted_of_selected 11 84771 ⟨1174776, by decide⟩ ⟨11, 2, 0, 1174776, 84771, 3457, 262144⟩
    (by decide) selected_cut_42975

theorem unmarked_context_10_21192_1174777 : frontier 11 ⟨1174777, by decide⟩
    (prefixCache 10 21192) (prefixPartial 10 21192) = false := by
  decide +kernel

theorem node_context_10_21192_1174777 : EJMOriginalGlobalDAGData.nodes 11 ⟨1174777, by decide⟩ =
    .split (coordinate 10) (![⟨1174569, by decide⟩,⟨1174660, by decide⟩,⟨1174722, by decide⟩,⟨1174776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21192_1174777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21192 ⟨1174777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21192
    ⟨1174777, by decide⟩ (by decide) (![⟨1174569, by decide⟩,⟨1174660, by decide⟩,⟨1174722, by decide⟩,⟨1174776, by decide⟩]) unmarked_context_10_21192_1174777 node_context_10_21192_1174777
  intro a
  fin_cases a
  · exact context_11_84768_1174569
  · exact context_11_84769_1174660
  · exact context_11_84770_1174722
  · exact context_11_84771_1174776

theorem selected_cut_42976 : selected 10 ⟨1174835, by decide⟩
    (prefixPartial 11 84772) = some ⟨11, 2, 0, 1174835, 84772, 3581, 262144⟩ := by
  decide +kernel

theorem context_11_84772_1174835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84772 ⟨1174835, by decide⟩ :=
  accepted_of_selected 11 84772 ⟨1174835, by decide⟩ ⟨11, 2, 0, 1174835, 84772, 3581, 262144⟩
    (by decide) selected_cut_42976

theorem selected_cut_42977 : selected 10 ⟨1174892, by decide⟩
    (prefixPartial 11 84773) = some ⟨11, 2, 0, 1174892, 84773, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_84773_1174892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84773 ⟨1174892, by decide⟩ :=
  accepted_of_selected 11 84773 ⟨1174892, by decide⟩ ⟨11, 2, 0, 1174892, 84773, 3537, 262144⟩
    (by decide) selected_cut_42977

theorem selected_cut_42978 : selected 10 ⟨1174942, by decide⟩
    (prefixPartial 11 84774) = some ⟨11, 2, 0, 1174942, 84774, 3221, 262144⟩ := by
  decide +kernel

theorem context_11_84774_1174942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84774 ⟨1174942, by decide⟩ :=
  accepted_of_selected 11 84774 ⟨1174942, by decide⟩ ⟨11, 2, 0, 1174942, 84774, 3221, 262144⟩
    (by decide) selected_cut_42978

theorem selected_cut_42979 : selected 10 ⟨1175014, by decide⟩
    (prefixPartial 11 84775) = some ⟨11, 2, 0, 1175014, 84775, 3933, 262144⟩ := by
  decide +kernel

theorem context_11_84775_1175014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84775 ⟨1175014, by decide⟩ :=
  accepted_of_selected 11 84775 ⟨1175014, by decide⟩ ⟨11, 2, 0, 1175014, 84775, 3933, 262144⟩
    (by decide) selected_cut_42979

theorem unmarked_context_10_21193_1175015 : frontier 11 ⟨1175015, by decide⟩
    (prefixCache 10 21193) (prefixPartial 10 21193) = false := by
  decide +kernel

theorem node_context_10_21193_1175015 : EJMOriginalGlobalDAGData.nodes 11 ⟨1175015, by decide⟩ =
    .split (coordinate 10) (![⟨1174835, by decide⟩,⟨1174892, by decide⟩,⟨1174942, by decide⟩,⟨1175014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21193_1175015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21193 ⟨1175015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21193
    ⟨1175015, by decide⟩ (by decide) (![⟨1174835, by decide⟩,⟨1174892, by decide⟩,⟨1174942, by decide⟩,⟨1175014, by decide⟩]) unmarked_context_10_21193_1175015 node_context_10_21193_1175015
  intro a
  fin_cases a
  · exact context_11_84772_1174835
  · exact context_11_84773_1174892
  · exact context_11_84774_1174942
  · exact context_11_84775_1175014

theorem selected_cut_42980 : selected 10 ⟨1175046, by decide⟩
    (prefixPartial 11 84776) = some ⟨11, 2, 0, 1175046, 84776, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_84776_1175046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84776 ⟨1175046, by decide⟩ :=
  accepted_of_selected 11 84776 ⟨1175046, by decide⟩ ⟨11, 2, 0, 1175046, 84776, 1889, 262144⟩
    (by decide) selected_cut_42980

theorem selected_cut_42981 : selected 10 ⟨1175102, by decide⟩
    (prefixPartial 11 84777) = some ⟨11, 2, 0, 1175102, 84777, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_84777_1175102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84777 ⟨1175102, by decide⟩ :=
  accepted_of_selected 11 84777 ⟨1175102, by decide⟩ ⟨11, 2, 0, 1175102, 84777, 2961, 262144⟩
    (by decide) selected_cut_42981

theorem selected_cut_42982 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84778) = some ⟨11, 1, 0, 1109453, 84778, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84778_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84778 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84778 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84778, 1, 262144⟩
    (by decide) selected_cut_42982

theorem selected_cut_42983 : selected 10 ⟨1175147, by decide⟩
    (prefixPartial 11 84779) = some ⟨11, 2, 0, 1175147, 84779, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_84779_1175147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84779 ⟨1175147, by decide⟩ :=
  accepted_of_selected 11 84779 ⟨1175147, by decide⟩ ⟨11, 2, 0, 1175147, 84779, 2445, 262144⟩
    (by decide) selected_cut_42983

theorem unmarked_context_10_21194_1175148 : frontier 11 ⟨1175148, by decide⟩
    (prefixCache 10 21194) (prefixPartial 10 21194) = false := by
  decide +kernel

theorem node_context_10_21194_1175148 : EJMOriginalGlobalDAGData.nodes 11 ⟨1175148, by decide⟩ =
    .split (coordinate 10) (![⟨1175046, by decide⟩,⟨1175102, by decide⟩,⟨1109453, by decide⟩,⟨1175147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21194_1175148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21194 ⟨1175148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21194
    ⟨1175148, by decide⟩ (by decide) (![⟨1175046, by decide⟩,⟨1175102, by decide⟩,⟨1109453, by decide⟩,⟨1175147, by decide⟩]) unmarked_context_10_21194_1175148 node_context_10_21194_1175148
  intro a
  fin_cases a
  · exact context_11_84776_1175046
  · exact context_11_84777_1175102
  · exact context_11_84778_1109453
  · exact context_11_84779_1175147

theorem selected_cut_42984 : selected 10 ⟨1175189, by decide⟩
    (prefixPartial 11 84780) = some ⟨11, 2, 0, 1175189, 84780, 2421, 262144⟩ := by
  decide +kernel

theorem context_11_84780_1175189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84780 ⟨1175189, by decide⟩ :=
  accepted_of_selected 11 84780 ⟨1175189, by decide⟩ ⟨11, 2, 0, 1175189, 84780, 2421, 262144⟩
    (by decide) selected_cut_42984

theorem selected_cut_42985 : selected 10 ⟨1175233, by decide⟩
    (prefixPartial 11 84781) = some ⟨11, 2, 0, 1175233, 84781, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_84781_1175233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84781 ⟨1175233, by decide⟩ :=
  accepted_of_selected 11 84781 ⟨1175233, by decide⟩ ⟨11, 2, 0, 1175233, 84781, 2825, 262144⟩
    (by decide) selected_cut_42985

theorem selected_cut_42986 : selected 10 ⟨1175263, by decide⟩
    (prefixPartial 11 84782) = some ⟨11, 2, 0, 1175263, 84782, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_84782_1175263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84782 ⟨1175263, by decide⟩ :=
  accepted_of_selected 11 84782 ⟨1175263, by decide⟩ ⟨11, 2, 0, 1175263, 84782, 1861, 262144⟩
    (by decide) selected_cut_42986

theorem selected_cut_42987 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84783) = some ⟨11, 1, 0, 977886, 84783, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84783_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84783 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84783 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84783, 1, 262144⟩
    (by decide) selected_cut_42987

theorem unmarked_context_10_21195_1175264 : frontier 11 ⟨1175264, by decide⟩
    (prefixCache 10 21195) (prefixPartial 10 21195) = false := by
  decide +kernel

theorem node_context_10_21195_1175264 : EJMOriginalGlobalDAGData.nodes 11 ⟨1175264, by decide⟩ =
    .split (coordinate 10) (![⟨1175189, by decide⟩,⟨1175233, by decide⟩,⟨1175263, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21195_1175264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21195 ⟨1175264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21195
    ⟨1175264, by decide⟩ (by decide) (![⟨1175189, by decide⟩,⟨1175233, by decide⟩,⟨1175263, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21195_1175264 node_context_10_21195_1175264
  intro a
  fin_cases a
  · exact context_11_84780_1175189
  · exact context_11_84781_1175233
  · exact context_11_84782_1175263
  · exact context_11_84783_977886

theorem unmarked_context_9_5298_1175265 : frontier 12 ⟨1175265, by decide⟩
    (prefixCache 9 5298) (prefixPartial 9 5298) = false := by
  decide +kernel

theorem node_context_9_5298_1175265 : EJMOriginalGlobalDAGData.nodes 12 ⟨1175265, by decide⟩ =
    .split (coordinate 9) (![⟨1174777, by decide⟩,⟨1175015, by decide⟩,⟨1175148, by decide⟩,⟨1175264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5298_1175265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5298 ⟨1175265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5298
    ⟨1175265, by decide⟩ (by decide) (![⟨1174777, by decide⟩,⟨1175015, by decide⟩,⟨1175148, by decide⟩,⟨1175264, by decide⟩]) unmarked_context_9_5298_1175265 node_context_9_5298_1175265
  intro a
  fin_cases a
  · exact context_10_21192_1174777
  · exact context_10_21193_1175015
  · exact context_10_21194_1175148
  · exact context_10_21195_1175264

theorem selected_cut_42988 : selected 10 ⟨1175280, by decide⟩
    (prefixPartial 11 84784) = some ⟨11, 2, 0, 1175280, 84784, 1045, 262144⟩ := by
  decide +kernel

theorem context_11_84784_1175280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84784 ⟨1175280, by decide⟩ :=
  accepted_of_selected 11 84784 ⟨1175280, by decide⟩ ⟨11, 2, 0, 1175280, 84784, 1045, 262144⟩
    (by decide) selected_cut_42988

theorem selected_cut_42989 : selected 10 ⟨1175305, by decide⟩
    (prefixPartial 11 84785) = some ⟨11, 2, 0, 1175305, 84785, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_84785_1175305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84785 ⟨1175305, by decide⟩ :=
  accepted_of_selected 11 84785 ⟨1175305, by decide⟩ ⟨11, 2, 0, 1175305, 84785, 1905, 262144⟩
    (by decide) selected_cut_42989

theorem selected_cut_42990 : selected 10 ⟨1175333, by decide⟩
    (prefixPartial 11 84786) = some ⟨11, 2, 0, 1175333, 84786, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_84786_1175333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84786 ⟨1175333, by decide⟩ :=
  accepted_of_selected 11 84786 ⟨1175333, by decide⟩ ⟨11, 2, 0, 1175333, 84786, 1805, 262144⟩
    (by decide) selected_cut_42990

theorem selected_cut_42991 : selected 10 ⟨1175355, by decide⟩
    (prefixPartial 11 84787) = some ⟨11, 2, 0, 1175355, 84787, 1133, 262144⟩ := by
  decide +kernel

theorem context_11_84787_1175355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84787 ⟨1175355, by decide⟩ :=
  accepted_of_selected 11 84787 ⟨1175355, by decide⟩ ⟨11, 2, 0, 1175355, 84787, 1133, 262144⟩
    (by decide) selected_cut_42991

theorem unmarked_context_10_21196_1175356 : frontier 11 ⟨1175356, by decide⟩
    (prefixCache 10 21196) (prefixPartial 10 21196) = false := by
  decide +kernel

theorem node_context_10_21196_1175356 : EJMOriginalGlobalDAGData.nodes 11 ⟨1175356, by decide⟩ =
    .split (coordinate 10) (![⟨1175280, by decide⟩,⟨1175305, by decide⟩,⟨1175333, by decide⟩,⟨1175355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21196_1175356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21196 ⟨1175356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21196
    ⟨1175356, by decide⟩ (by decide) (![⟨1175280, by decide⟩,⟨1175305, by decide⟩,⟨1175333, by decide⟩,⟨1175355, by decide⟩]) unmarked_context_10_21196_1175356 node_context_10_21196_1175356
  intro a
  fin_cases a
  · exact context_11_84784_1175280
  · exact context_11_84785_1175305
  · exact context_11_84786_1175333
  · exact context_11_84787_1175355

theorem selected_cut_42992 : selected 11 ⟨1175404, by decide⟩
    (prefixPartial 10 21197) = some ⟨10, 2, 0, 1175404, 21197, 3241, 1048576⟩ := by
  decide +kernel

theorem context_10_21197_1175404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21197 ⟨1175404, by decide⟩ :=
  accepted_of_selected 10 21197 ⟨1175404, by decide⟩ ⟨10, 2, 0, 1175404, 21197, 3241, 1048576⟩
    (by decide) selected_cut_42992

theorem selected_cut_42993 : selected 11 ⟨1175458, by decide⟩
    (prefixPartial 10 21198) = some ⟨10, 2, 0, 1175458, 21198, 2185, 1048576⟩ := by
  decide +kernel

theorem context_10_21198_1175458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21198 ⟨1175458, by decide⟩ :=
  accepted_of_selected 10 21198 ⟨1175458, by decide⟩ ⟨10, 2, 0, 1175458, 21198, 2185, 1048576⟩
    (by decide) selected_cut_42993

theorem selected_cut_42994 : selected 11 ⟨1175468, by decide⟩
    (prefixPartial 10 21199) = some ⟨10, 2, 0, 1175468, 21199, 313, 1048576⟩ := by
  decide +kernel

theorem context_10_21199_1175468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21199 ⟨1175468, by decide⟩ :=
  accepted_of_selected 10 21199 ⟨1175468, by decide⟩ ⟨10, 2, 0, 1175468, 21199, 313, 1048576⟩
    (by decide) selected_cut_42994

theorem unmarked_context_9_5299_1175469 : frontier 12 ⟨1175469, by decide⟩
    (prefixCache 9 5299) (prefixPartial 9 5299) = false := by
  decide +kernel

theorem node_context_9_5299_1175469 : EJMOriginalGlobalDAGData.nodes 12 ⟨1175469, by decide⟩ =
    .split (coordinate 9) (![⟨1175356, by decide⟩,⟨1175404, by decide⟩,⟨1175458, by decide⟩,⟨1175468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5299_1175469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5299 ⟨1175469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5299
    ⟨1175469, by decide⟩ (by decide) (![⟨1175356, by decide⟩,⟨1175404, by decide⟩,⟨1175458, by decide⟩,⟨1175468, by decide⟩]) unmarked_context_9_5299_1175469 node_context_9_5299_1175469
  intro a
  fin_cases a
  · exact context_10_21196_1175356
  · exact context_10_21197_1175404
  · exact context_10_21198_1175458
  · exact context_10_21199_1175468

theorem unmarked_context_8_1324_1175470 : frontier 13 ⟨1175470, by decide⟩
    (prefixCache 8 1324) (prefixPartial 8 1324) = false := by
  decide +kernel

theorem node_context_8_1324_1175470 : EJMOriginalGlobalDAGData.nodes 13 ⟨1175470, by decide⟩ =
    .split (coordinate 8) (![⟨1173555, by decide⟩,⟨1174485, by decide⟩,⟨1175265, by decide⟩,⟨1175469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1324_1175470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1324 ⟨1175470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1324
    ⟨1175470, by decide⟩ (by decide) (![⟨1173555, by decide⟩,⟨1174485, by decide⟩,⟨1175265, by decide⟩,⟨1175469, by decide⟩]) unmarked_context_8_1324_1175470 node_context_8_1324_1175470
  intro a
  fin_cases a
  · exact context_9_5296_1173555
  · exact context_9_5297_1174485
  · exact context_9_5298_1175265
  · exact context_9_5299_1175469

theorem selected_cut_42995 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84800) = some ⟨11, 1, 0, 434745, 84800, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84800_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84800 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84800 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84800, 1, 262144⟩
    (by decide) selected_cut_42995

theorem selected_cut_42996 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339204) = some ⟨12, 1, 0, 448748, 339204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339204_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339204 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339204 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339204, 1, 65536⟩
    (by decide) selected_cut_42996

theorem selected_cut_42997 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 339205) = some ⟨12, 1, 0, 34034, 339205, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339205_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339205 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 339205 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 339205, 1, 65536⟩
    (by decide) selected_cut_42997

theorem selected_cut_42998 : selected 9 ⟨1175529, by decide⟩
    (prefixPartial 12 339206) = some ⟨12, 2, 0, 1175529, 339206, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_339206_1175529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339206 ⟨1175529, by decide⟩ :=
  accepted_of_selected 12 339206 ⟨1175529, by decide⟩ ⟨12, 2, 0, 1175529, 339206, 2565, 65536⟩
    (by decide) selected_cut_42998

theorem selected_cut_42999 : selected 9 ⟨1175589, by decide⟩
    (prefixPartial 12 339207) = some ⟨12, 2, 0, 1175589, 339207, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_339207_1175589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339207 ⟨1175589, by decide⟩ :=
  accepted_of_selected 12 339207 ⟨1175589, by decide⟩ ⟨12, 2, 0, 1175589, 339207, 2937, 65536⟩
    (by decide) selected_cut_42999

theorem unmarked_context_11_84801_1175590 : frontier 10 ⟨1175590, by decide⟩
    (prefixCache 11 84801) (prefixPartial 11 84801) = false := by
  decide +kernel

theorem node_context_11_84801_1175590 : EJMOriginalGlobalDAGData.nodes 10 ⟨1175590, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1175529, by decide⟩,⟨1175589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84801_1175590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84801 ⟨1175590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84801
    ⟨1175590, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1175529, by decide⟩,⟨1175589, by decide⟩]) unmarked_context_11_84801_1175590 node_context_11_84801_1175590
  intro a
  fin_cases a
  · exact context_12_339204_448748
  · exact context_12_339205_34034
  · exact context_12_339206_1175529
  · exact context_12_339207_1175589

theorem selected_cut_43000 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339208) = some ⟨12, 1, 0, 448748, 339208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339208_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339208 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339208 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339208, 1, 65536⟩
    (by decide) selected_cut_43000

theorem selected_cut_43001 : selected 9 ⟨1175667, by decide⟩
    (prefixPartial 12 339209) = some ⟨12, 2, 0, 1175667, 339209, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_339209_1175667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339209 ⟨1175667, by decide⟩ :=
  accepted_of_selected 12 339209 ⟨1175667, by decide⟩ ⟨12, 2, 0, 1175667, 339209, 3101, 65536⟩
    (by decide) selected_cut_43001

theorem selected_cut_43002 : selected 9 ⟨1175716, by decide⟩
    (prefixPartial 12 339210) = some ⟨12, 2, 0, 1175716, 339210, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_339210_1175716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339210 ⟨1175716, by decide⟩ :=
  accepted_of_selected 12 339210 ⟨1175716, by decide⟩ ⟨12, 2, 0, 1175716, 339210, 2625, 65536⟩
    (by decide) selected_cut_43002

theorem selected_cut_43003 : selected 9 ⟨1175776, by decide⟩
    (prefixPartial 12 339211) = some ⟨12, 2, 0, 1175776, 339211, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_339211_1175776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339211 ⟨1175776, by decide⟩ :=
  accepted_of_selected 12 339211 ⟨1175776, by decide⟩ ⟨12, 2, 0, 1175776, 339211, 3021, 65536⟩
    (by decide) selected_cut_43003

theorem unmarked_context_11_84802_1175777 : frontier 10 ⟨1175777, by decide⟩
    (prefixCache 11 84802) (prefixPartial 11 84802) = false := by
  decide +kernel

theorem node_context_11_84802_1175777 : EJMOriginalGlobalDAGData.nodes 10 ⟨1175777, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1175667, by decide⟩,⟨1175716, by decide⟩,⟨1175776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84802_1175777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84802 ⟨1175777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84802
    ⟨1175777, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1175667, by decide⟩,⟨1175716, by decide⟩,⟨1175776, by decide⟩]) unmarked_context_11_84802_1175777 node_context_11_84802_1175777
  intro a
  fin_cases a
  · exact context_12_339208_448748
  · exact context_12_339209_1175667
  · exact context_12_339210_1175716
  · exact context_12_339211_1175776

theorem selected_cut_43004 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 339212) = some ⟨12, 1, 0, 448748, 339212, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339212_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339212 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 339212 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 339212, 1, 65536⟩
    (by decide) selected_cut_43004

theorem selected_cut_43005 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 339213) = some ⟨12, 1, 0, 390434, 339213, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339213_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339213 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 339213 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 339213, 1, 65536⟩
    (by decide) selected_cut_43005

theorem selected_cut_43006 : selected 9 ⟨1175817, by decide⟩
    (prefixPartial 12 339214) = some ⟨12, 2, 0, 1175817, 339214, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_339214_1175817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339214 ⟨1175817, by decide⟩ :=
  accepted_of_selected 12 339214 ⟨1175817, by decide⟩ ⟨12, 2, 0, 1175817, 339214, 2273, 65536⟩
    (by decide) selected_cut_43006

theorem selected_cut_43007 : selected 9 ⟨1175871, by decide⟩
    (prefixPartial 12 339215) = some ⟨12, 2, 0, 1175871, 339215, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_339215_1175871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339215 ⟨1175871, by decide⟩ :=
  accepted_of_selected 12 339215 ⟨1175871, by decide⟩ ⟨12, 2, 0, 1175871, 339215, 2669, 65536⟩
    (by decide) selected_cut_43007

theorem unmarked_context_11_84803_1175872 : frontier 10 ⟨1175872, by decide⟩
    (prefixCache 11 84803) (prefixPartial 11 84803) = false := by
  decide +kernel

theorem node_context_11_84803_1175872 : EJMOriginalGlobalDAGData.nodes 10 ⟨1175872, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1175817, by decide⟩,⟨1175871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84803_1175872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84803 ⟨1175872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84803
    ⟨1175872, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1175817, by decide⟩,⟨1175871, by decide⟩]) unmarked_context_11_84803_1175872 node_context_11_84803_1175872
  intro a
  fin_cases a
  · exact context_12_339212_448748
  · exact context_12_339213_390434
  · exact context_12_339214_1175817
  · exact context_12_339215_1175871

theorem unmarked_context_10_21200_1175873 : frontier 11 ⟨1175873, by decide⟩
    (prefixCache 10 21200) (prefixPartial 10 21200) = false := by
  decide +kernel

theorem node_context_10_21200_1175873 : EJMOriginalGlobalDAGData.nodes 11 ⟨1175873, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1175590, by decide⟩,⟨1175777, by decide⟩,⟨1175872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21200_1175873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21200 ⟨1175873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21200
    ⟨1175873, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1175590, by decide⟩,⟨1175777, by decide⟩,⟨1175872, by decide⟩]) unmarked_context_10_21200_1175873 node_context_10_21200_1175873
  intro a
  fin_cases a
  · exact context_11_84800_434745
  · exact context_11_84801_1175590
  · exact context_11_84802_1175777
  · exact context_11_84803_1175872

theorem selected_cut_43008 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339216) = some ⟨12, 1, 0, 1108174, 339216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339216_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339216 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339216 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339216, 1, 65536⟩
    (by decide) selected_cut_43008

theorem selected_cut_43009 : selected 9 ⟨1175939, by decide⟩
    (prefixPartial 12 339217) = some ⟨12, 2, 0, 1175939, 339217, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_339217_1175939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339217 ⟨1175939, by decide⟩ :=
  accepted_of_selected 12 339217 ⟨1175939, by decide⟩ ⟨12, 2, 0, 1175939, 339217, 2989, 65536⟩
    (by decide) selected_cut_43009

theorem selected_cut_43010 : selected 9 ⟨1175993, by decide⟩
    (prefixPartial 12 339218) = some ⟨12, 2, 0, 1175993, 339218, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_339218_1175993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339218 ⟨1175993, by decide⟩ :=
  accepted_of_selected 12 339218 ⟨1175993, by decide⟩ ⟨12, 2, 0, 1175993, 339218, 2589, 65536⟩
    (by decide) selected_cut_43010

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
