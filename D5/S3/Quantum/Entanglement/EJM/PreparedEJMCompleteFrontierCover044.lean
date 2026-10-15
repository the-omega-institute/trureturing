/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover043
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04226 : selected 9 ⟨133683, by decide⟩
    (prefixPartial 12 18005) = some ⟨12, 2, 0, 133683, 18005, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_18005_133683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18005 ⟨133683, by decide⟩ :=
  accepted_of_selected 12 18005 ⟨133683, by decide⟩ ⟨12, 2, 0, 133683, 18005, 3537, 65536⟩
    (by decide) selected_cut_04226

theorem selected_cut_04227 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 72024) = some ⟨13, 1, 0, 3444, 72024, 1, 16384⟩ := by
  decide +kernel

theorem context_13_72024_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72024 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 72024 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 72024, 1, 16384⟩
    (by decide) selected_cut_04227

theorem selected_cut_04228 : selected 8 ⟨133757, by decide⟩
    (prefixPartial 13 72025) = some ⟨13, 2, 0, 133757, 72025, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_72025_133757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72025 ⟨133757, by decide⟩ :=
  accepted_of_selected 13 72025 ⟨133757, by decide⟩ ⟨13, 2, 0, 133757, 72025, 2629, 16384⟩
    (by decide) selected_cut_04228

theorem selected_cut_04229 : selected 8 ⟨133778, by decide⟩
    (prefixPartial 13 72026) = some ⟨13, 2, 0, 133778, 72026, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_72026_133778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72026 ⟨133778, by decide⟩ :=
  accepted_of_selected 13 72026 ⟨133778, by decide⟩ ⟨13, 2, 0, 133778, 72026, 1353, 16384⟩
    (by decide) selected_cut_04229

theorem selected_cut_04230 : selected 8 ⟨133786, by decide⟩
    (prefixPartial 13 72027) = some ⟨13, 2, 0, 133786, 72027, 881, 16384⟩ := by
  decide +kernel

theorem context_13_72027_133786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72027 ⟨133786, by decide⟩ :=
  accepted_of_selected 13 72027 ⟨133786, by decide⟩ ⟨13, 2, 0, 133786, 72027, 881, 16384⟩
    (by decide) selected_cut_04230

theorem unmarked_context_12_18006_133787 : frontier 9 ⟨133787, by decide⟩
    (prefixCache 12 18006) (prefixPartial 12 18006) = false := by
  decide +kernel

theorem node_context_12_18006_133787 : EJMOriginalGlobalDAGData.nodes 9 ⟨133787, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨133757, by decide⟩,⟨133778, by decide⟩,⟨133786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18006_133787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18006 ⟨133787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18006
    ⟨133787, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨133757, by decide⟩,⟨133778, by decide⟩,⟨133786, by decide⟩]) unmarked_context_12_18006_133787 node_context_12_18006_133787
  intro a
  fin_cases a
  · exact context_13_72024_3444
  · exact context_13_72025_133757
  · exact context_13_72026_133778
  · exact context_13_72027_133786

theorem selected_cut_04231 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 72028) = some ⟨13, 1, 0, 3444, 72028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_72028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 72028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 72028, 1, 16384⟩
    (by decide) selected_cut_04231

theorem selected_cut_04232 : selected 8 ⟨133868, by decide⟩
    (prefixPartial 13 72029) = some ⟨13, 2, 0, 133868, 72029, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_72029_133868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72029 ⟨133868, by decide⟩ :=
  accepted_of_selected 13 72029 ⟨133868, by decide⟩ ⟨13, 2, 0, 133868, 72029, 2685, 16384⟩
    (by decide) selected_cut_04232

theorem selected_cut_04233 : selected 8 ⟨133904, by decide⟩
    (prefixPartial 13 72030) = some ⟨13, 2, 0, 133904, 72030, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_72030_133904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72030 ⟨133904, by decide⟩ :=
  accepted_of_selected 13 72030 ⟨133904, by decide⟩ ⟨13, 2, 0, 133904, 72030, 1601, 16384⟩
    (by decide) selected_cut_04233

theorem selected_cut_04234 : selected 8 ⟨133913, by decide⟩
    (prefixPartial 13 72031) = some ⟨13, 2, 0, 133913, 72031, 881, 16384⟩ := by
  decide +kernel

theorem context_13_72031_133913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72031 ⟨133913, by decide⟩ :=
  accepted_of_selected 13 72031 ⟨133913, by decide⟩ ⟨13, 2, 0, 133913, 72031, 881, 16384⟩
    (by decide) selected_cut_04234

theorem unmarked_context_12_18007_133914 : frontier 9 ⟨133914, by decide⟩
    (prefixCache 12 18007) (prefixPartial 12 18007) = false := by
  decide +kernel

theorem node_context_12_18007_133914 : EJMOriginalGlobalDAGData.nodes 9 ⟨133914, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨133868, by decide⟩,⟨133904, by decide⟩,⟨133913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18007_133914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18007 ⟨133914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18007
    ⟨133914, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨133868, by decide⟩,⟨133904, by decide⟩,⟨133913, by decide⟩]) unmarked_context_12_18007_133914 node_context_12_18007_133914
  intro a
  fin_cases a
  · exact context_13_72028_3444
  · exact context_13_72029_133868
  · exact context_13_72030_133904
  · exact context_13_72031_133913

theorem unmarked_context_11_4501_133915 : frontier 10 ⟨133915, by decide⟩
    (prefixCache 11 4501) (prefixPartial 11 4501) = false := by
  decide +kernel

theorem node_context_11_4501_133915 : EJMOriginalGlobalDAGData.nodes 10 ⟨133915, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨133683, by decide⟩,⟨133787, by decide⟩,⟨133914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4501_133915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4501 ⟨133915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4501
    ⟨133915, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨133683, by decide⟩,⟨133787, by decide⟩,⟨133914, by decide⟩]) unmarked_context_11_4501_133915 node_context_11_4501_133915
  intro a
  fin_cases a
  · exact context_12_18004_895
  · exact context_12_18005_133683
  · exact context_12_18006_133787
  · exact context_12_18007_133914

theorem selected_cut_04235 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 18008) = some ⟨12, 1, 0, 895, 18008, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18008_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18008 ⟨895, by decide⟩ :=
  accepted_of_selected 12 18008 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 18008, 1, 65536⟩
    (by decide) selected_cut_04235

theorem selected_cut_04236 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 18009) = some ⟨12, 1, 0, 895, 18009, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18009_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18009 ⟨895, by decide⟩ :=
  accepted_of_selected 12 18009 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 18009, 1, 65536⟩
    (by decide) selected_cut_04236

theorem selected_cut_04237 : selected 9 ⟨133996, by decide⟩
    (prefixPartial 12 18010) = some ⟨12, 2, 0, 133996, 18010, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_18010_133996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18010 ⟨133996, by decide⟩ :=
  accepted_of_selected 12 18010 ⟨133996, by decide⟩ ⟨12, 2, 0, 133996, 18010, 2617, 65536⟩
    (by decide) selected_cut_04237

theorem selected_cut_04238 : selected 9 ⟨134070, by decide⟩
    (prefixPartial 12 18011) = some ⟨12, 2, 0, 134070, 18011, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_18011_134070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18011 ⟨134070, by decide⟩ :=
  accepted_of_selected 12 18011 ⟨134070, by decide⟩ ⟨12, 2, 0, 134070, 18011, 3345, 65536⟩
    (by decide) selected_cut_04238

theorem unmarked_context_11_4502_134071 : frontier 10 ⟨134071, by decide⟩
    (prefixCache 11 4502) (prefixPartial 11 4502) = false := by
  decide +kernel

theorem node_context_11_4502_134071 : EJMOriginalGlobalDAGData.nodes 10 ⟨134071, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨133996, by decide⟩,⟨134070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4502_134071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4502 ⟨134071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4502
    ⟨134071, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨133996, by decide⟩,⟨134070, by decide⟩]) unmarked_context_11_4502_134071 node_context_11_4502_134071
  intro a
  fin_cases a
  · exact context_12_18008_895
  · exact context_12_18009_895
  · exact context_12_18010_133996
  · exact context_12_18011_134070

theorem selected_cut_04239 : selected 10 ⟨134128, by decide⟩
    (prefixPartial 11 4503) = some ⟨11, 2, 0, 134128, 4503, 2013, 262144⟩ := by
  decide +kernel

theorem context_11_4503_134128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4503 ⟨134128, by decide⟩ :=
  accepted_of_selected 11 4503 ⟨134128, by decide⟩ ⟨11, 2, 0, 134128, 4503, 2013, 262144⟩
    (by decide) selected_cut_04239

theorem unmarked_context_10_1125_134129 : frontier 11 ⟨134129, by decide⟩
    (prefixCache 10 1125) (prefixPartial 10 1125) = false := by
  decide +kernel

theorem node_context_10_1125_134129 : EJMOriginalGlobalDAGData.nodes 11 ⟨134129, by decide⟩ =
    .split (coordinate 10) (![⟨133577, by decide⟩,⟨133915, by decide⟩,⟨134071, by decide⟩,⟨134128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1125_134129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1125 ⟨134129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1125
    ⟨134129, by decide⟩ (by decide) (![⟨133577, by decide⟩,⟨133915, by decide⟩,⟨134071, by decide⟩,⟨134128, by decide⟩]) unmarked_context_10_1125_134129 node_context_10_1125_134129
  intro a
  fin_cases a
  · exact context_11_4500_133577
  · exact context_11_4501_133915
  · exact context_11_4502_134071
  · exact context_11_4503_134128

theorem selected_cut_04240 : selected 9 ⟨134185, by decide⟩
    (prefixPartial 12 18016) = some ⟨12, 2, 0, 134185, 18016, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_18016_134185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18016 ⟨134185, by decide⟩ :=
  accepted_of_selected 12 18016 ⟨134185, by decide⟩ ⟨12, 2, 0, 134185, 18016, 3141, 65536⟩
    (by decide) selected_cut_04240

theorem selected_cut_04241 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 72068) = some ⟨13, 1, 0, 3444, 72068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_72068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 72068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 72068, 1, 16384⟩
    (by decide) selected_cut_04241

theorem selected_cut_04242 : selected 8 ⟨134226, by decide⟩
    (prefixPartial 13 72069) = some ⟨13, 2, 0, 134226, 72069, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_72069_134226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72069 ⟨134226, by decide⟩ :=
  accepted_of_selected 13 72069 ⟨134226, by decide⟩ ⟨13, 2, 0, 134226, 72069, 1869, 16384⟩
    (by decide) selected_cut_04242

theorem selected_cut_04243 : selected 8 ⟨134251, by decide⟩
    (prefixPartial 13 72070) = some ⟨13, 2, 0, 134251, 72070, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_72070_134251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72070 ⟨134251, by decide⟩ :=
  accepted_of_selected 13 72070 ⟨134251, by decide⟩ ⟨13, 2, 0, 134251, 72070, 1265, 16384⟩
    (by decide) selected_cut_04243

theorem selected_cut_04244 : selected 8 ⟨134265, by decide⟩
    (prefixPartial 13 72071) = some ⟨13, 2, 0, 134265, 72071, 981, 16384⟩ := by
  decide +kernel

theorem context_13_72071_134265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72071 ⟨134265, by decide⟩ :=
  accepted_of_selected 13 72071 ⟨134265, by decide⟩ ⟨13, 2, 0, 134265, 72071, 981, 16384⟩
    (by decide) selected_cut_04244

theorem unmarked_context_12_18017_134266 : frontier 9 ⟨134266, by decide⟩
    (prefixCache 12 18017) (prefixPartial 12 18017) = false := by
  decide +kernel

theorem node_context_12_18017_134266 : EJMOriginalGlobalDAGData.nodes 9 ⟨134266, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨134226, by decide⟩,⟨134251, by decide⟩,⟨134265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18017_134266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18017 ⟨134266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18017
    ⟨134266, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨134226, by decide⟩,⟨134251, by decide⟩,⟨134265, by decide⟩]) unmarked_context_12_18017_134266 node_context_12_18017_134266
  intro a
  fin_cases a
  · exact context_13_72068_3444
  · exact context_13_72069_134226
  · exact context_13_72070_134251
  · exact context_13_72071_134265

theorem selected_cut_04245 : selected 9 ⟨134317, by decide⟩
    (prefixPartial 12 18018) = some ⟨12, 2, 0, 134317, 18018, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_18018_134317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18018 ⟨134317, by decide⟩ :=
  accepted_of_selected 12 18018 ⟨134317, by decide⟩ ⟨12, 2, 0, 134317, 18018, 2729, 65536⟩
    (by decide) selected_cut_04245

theorem selected_cut_04246 : selected 9 ⟨134377, by decide⟩
    (prefixPartial 12 18019) = some ⟨12, 2, 0, 134377, 18019, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_18019_134377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18019 ⟨134377, by decide⟩ :=
  accepted_of_selected 12 18019 ⟨134377, by decide⟩ ⟨12, 2, 0, 134377, 18019, 3165, 65536⟩
    (by decide) selected_cut_04246

theorem unmarked_context_11_4504_134378 : frontier 10 ⟨134378, by decide⟩
    (prefixCache 11 4504) (prefixPartial 11 4504) = false := by
  decide +kernel

theorem node_context_11_4504_134378 : EJMOriginalGlobalDAGData.nodes 10 ⟨134378, by decide⟩ =
    .split (coordinate 11) (![⟨134185, by decide⟩,⟨134266, by decide⟩,⟨134317, by decide⟩,⟨134377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4504_134378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4504 ⟨134378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4504
    ⟨134378, by decide⟩ (by decide) (![⟨134185, by decide⟩,⟨134266, by decide⟩,⟨134317, by decide⟩,⟨134377, by decide⟩]) unmarked_context_11_4504_134378 node_context_11_4504_134378
  intro a
  fin_cases a
  · exact context_12_18016_134185
  · exact context_12_18017_134266
  · exact context_12_18018_134317
  · exact context_12_18019_134377

theorem selected_cut_04247 : selected 9 ⟨134423, by decide⟩
    (prefixPartial 12 18020) = some ⟨12, 2, 0, 134423, 18020, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_18020_134423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18020 ⟨134423, by decide⟩ :=
  accepted_of_selected 12 18020 ⟨134423, by decide⟩ ⟨12, 2, 0, 134423, 18020, 2785, 65536⟩
    (by decide) selected_cut_04247

theorem selected_cut_04248 : selected 9 ⟨134487, by decide⟩
    (prefixPartial 12 18021) = some ⟨12, 2, 0, 134487, 18021, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_18021_134487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18021 ⟨134487, by decide⟩ :=
  accepted_of_selected 12 18021 ⟨134487, by decide⟩ ⟨12, 2, 0, 134487, 18021, 3633, 65536⟩
    (by decide) selected_cut_04248

theorem selected_cut_04249 : selected 9 ⟨134535, by decide⟩
    (prefixPartial 12 18022) = some ⟨12, 2, 0, 134535, 18022, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_18022_134535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18022 ⟨134535, by decide⟩ :=
  accepted_of_selected 12 18022 ⟨134535, by decide⟩ ⟨12, 2, 0, 134535, 18022, 2685, 65536⟩
    (by decide) selected_cut_04249

theorem selected_cut_04250 : selected 9 ⟨134583, by decide⟩
    (prefixPartial 12 18023) = some ⟨12, 2, 0, 134583, 18023, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_18023_134583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18023 ⟨134583, by decide⟩ :=
  accepted_of_selected 12 18023 ⟨134583, by decide⟩ ⟨12, 2, 0, 134583, 18023, 3033, 65536⟩
    (by decide) selected_cut_04250

theorem unmarked_context_11_4505_134584 : frontier 10 ⟨134584, by decide⟩
    (prefixCache 11 4505) (prefixPartial 11 4505) = false := by
  decide +kernel

theorem node_context_11_4505_134584 : EJMOriginalGlobalDAGData.nodes 10 ⟨134584, by decide⟩ =
    .split (coordinate 11) (![⟨134423, by decide⟩,⟨134487, by decide⟩,⟨134535, by decide⟩,⟨134583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4505_134584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4505 ⟨134584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4505
    ⟨134584, by decide⟩ (by decide) (![⟨134423, by decide⟩,⟨134487, by decide⟩,⟨134535, by decide⟩,⟨134583, by decide⟩]) unmarked_context_11_4505_134584 node_context_11_4505_134584
  intro a
  fin_cases a
  · exact context_12_18020_134423
  · exact context_12_18021_134487
  · exact context_12_18022_134535
  · exact context_12_18023_134583

theorem selected_cut_04251 : selected 9 ⟨134621, by decide⟩
    (prefixPartial 12 18024) = some ⟨12, 2, 0, 134621, 18024, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_18024_134621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18024 ⟨134621, by decide⟩ :=
  accepted_of_selected 12 18024 ⟨134621, by decide⟩ ⟨12, 2, 0, 134621, 18024, 2341, 65536⟩
    (by decide) selected_cut_04251

theorem selected_cut_04252 : selected 9 ⟨134689, by decide⟩
    (prefixPartial 12 18025) = some ⟨12, 2, 0, 134689, 18025, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_18025_134689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18025 ⟨134689, by decide⟩ :=
  accepted_of_selected 12 18025 ⟨134689, by decide⟩ ⟨12, 2, 0, 134689, 18025, 3373, 65536⟩
    (by decide) selected_cut_04252

theorem selected_cut_04253 : selected 9 ⟨134739, by decide⟩
    (prefixPartial 12 18026) = some ⟨12, 2, 0, 134739, 18026, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_18026_134739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18026 ⟨134739, by decide⟩ :=
  accepted_of_selected 12 18026 ⟨134739, by decide⟩ ⟨12, 2, 0, 134739, 18026, 3149, 65536⟩
    (by decide) selected_cut_04253

theorem selected_cut_04254 : selected 9 ⟨134787, by decide⟩
    (prefixPartial 12 18027) = some ⟨12, 2, 0, 134787, 18027, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_18027_134787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18027 ⟨134787, by decide⟩ :=
  accepted_of_selected 12 18027 ⟨134787, by decide⟩ ⟨12, 2, 0, 134787, 18027, 2501, 65536⟩
    (by decide) selected_cut_04254

theorem unmarked_context_11_4506_134788 : frontier 10 ⟨134788, by decide⟩
    (prefixCache 11 4506) (prefixPartial 11 4506) = false := by
  decide +kernel

theorem node_context_11_4506_134788 : EJMOriginalGlobalDAGData.nodes 10 ⟨134788, by decide⟩ =
    .split (coordinate 11) (![⟨134621, by decide⟩,⟨134689, by decide⟩,⟨134739, by decide⟩,⟨134787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4506_134788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4506 ⟨134788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4506
    ⟨134788, by decide⟩ (by decide) (![⟨134621, by decide⟩,⟨134689, by decide⟩,⟨134739, by decide⟩,⟨134787, by decide⟩]) unmarked_context_11_4506_134788 node_context_11_4506_134788
  intro a
  fin_cases a
  · exact context_12_18024_134621
  · exact context_12_18025_134689
  · exact context_12_18026_134739
  · exact context_12_18027_134787

theorem selected_cut_04255 : selected 9 ⟨134820, by decide⟩
    (prefixPartial 12 18028) = some ⟨12, 2, 0, 134820, 18028, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_18028_134820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18028 ⟨134820, by decide⟩ :=
  accepted_of_selected 12 18028 ⟨134820, by decide⟩ ⟨12, 2, 0, 134820, 18028, 2433, 65536⟩
    (by decide) selected_cut_04255

theorem selected_cut_04256 : selected 9 ⟨134891, by decide⟩
    (prefixPartial 12 18029) = some ⟨12, 2, 0, 134891, 18029, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_18029_134891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18029 ⟨134891, by decide⟩ :=
  accepted_of_selected 12 18029 ⟨134891, by decide⟩ ⟨12, 2, 0, 134891, 18029, 3357, 65536⟩
    (by decide) selected_cut_04256

theorem selected_cut_04257 : selected 9 ⟨134923, by decide⟩
    (prefixPartial 12 18030) = some ⟨12, 2, 0, 134923, 18030, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_18030_134923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18030 ⟨134923, by decide⟩ :=
  accepted_of_selected 12 18030 ⟨134923, by decide⟩ ⟨12, 2, 0, 134923, 18030, 2193, 65536⟩
    (by decide) selected_cut_04257

theorem selected_cut_04258 : selected 9 ⟨134953, by decide⟩
    (prefixPartial 12 18031) = some ⟨12, 2, 0, 134953, 18031, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_18031_134953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18031 ⟨134953, by decide⟩ :=
  accepted_of_selected 12 18031 ⟨134953, by decide⟩ ⟨12, 2, 0, 134953, 18031, 2261, 65536⟩
    (by decide) selected_cut_04258

theorem unmarked_context_11_4507_134954 : frontier 10 ⟨134954, by decide⟩
    (prefixCache 11 4507) (prefixPartial 11 4507) = false := by
  decide +kernel

theorem node_context_11_4507_134954 : EJMOriginalGlobalDAGData.nodes 10 ⟨134954, by decide⟩ =
    .split (coordinate 11) (![⟨134820, by decide⟩,⟨134891, by decide⟩,⟨134923, by decide⟩,⟨134953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4507_134954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4507 ⟨134954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4507
    ⟨134954, by decide⟩ (by decide) (![⟨134820, by decide⟩,⟨134891, by decide⟩,⟨134923, by decide⟩,⟨134953, by decide⟩]) unmarked_context_11_4507_134954 node_context_11_4507_134954
  intro a
  fin_cases a
  · exact context_12_18028_134820
  · exact context_12_18029_134891
  · exact context_12_18030_134923
  · exact context_12_18031_134953

theorem unmarked_context_10_1126_134955 : frontier 11 ⟨134955, by decide⟩
    (prefixCache 10 1126) (prefixPartial 10 1126) = false := by
  decide +kernel

theorem node_context_10_1126_134955 : EJMOriginalGlobalDAGData.nodes 11 ⟨134955, by decide⟩ =
    .split (coordinate 10) (![⟨134378, by decide⟩,⟨134584, by decide⟩,⟨134788, by decide⟩,⟨134954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1126_134955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1126 ⟨134955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1126
    ⟨134955, by decide⟩ (by decide) (![⟨134378, by decide⟩,⟨134584, by decide⟩,⟨134788, by decide⟩,⟨134954, by decide⟩]) unmarked_context_10_1126_134955 node_context_10_1126_134955
  intro a
  fin_cases a
  · exact context_11_4504_134378
  · exact context_11_4505_134584
  · exact context_11_4506_134788
  · exact context_11_4507_134954

theorem selected_cut_04259 : selected 9 ⟨134996, by decide⟩
    (prefixPartial 12 18032) = some ⟨12, 2, 0, 134996, 18032, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_18032_134996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18032 ⟨134996, by decide⟩ :=
  accepted_of_selected 12 18032 ⟨134996, by decide⟩ ⟨12, 2, 0, 134996, 18032, 2177, 65536⟩
    (by decide) selected_cut_04259

theorem selected_cut_04260 : selected 9 ⟨135050, by decide⟩
    (prefixPartial 12 18033) = some ⟨12, 2, 0, 135050, 18033, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_18033_135050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18033 ⟨135050, by decide⟩ :=
  accepted_of_selected 12 18033 ⟨135050, by decide⟩ ⟨12, 2, 0, 135050, 18033, 2633, 65536⟩
    (by decide) selected_cut_04260

theorem selected_cut_04261 : selected 9 ⟨135081, by decide⟩
    (prefixPartial 12 18034) = some ⟨12, 2, 0, 135081, 18034, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_18034_135081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18034 ⟨135081, by decide⟩ :=
  accepted_of_selected 12 18034 ⟨135081, by decide⟩ ⟨12, 2, 0, 135081, 18034, 1945, 65536⟩
    (by decide) selected_cut_04261

theorem selected_cut_04262 : selected 9 ⟨135123, by decide⟩
    (prefixPartial 12 18035) = some ⟨12, 2, 0, 135123, 18035, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_18035_135123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18035 ⟨135123, by decide⟩ :=
  accepted_of_selected 12 18035 ⟨135123, by decide⟩ ⟨12, 2, 0, 135123, 18035, 2113, 65536⟩
    (by decide) selected_cut_04262

theorem unmarked_context_11_4508_135124 : frontier 10 ⟨135124, by decide⟩
    (prefixCache 11 4508) (prefixPartial 11 4508) = false := by
  decide +kernel

theorem node_context_11_4508_135124 : EJMOriginalGlobalDAGData.nodes 10 ⟨135124, by decide⟩ =
    .split (coordinate 11) (![⟨134996, by decide⟩,⟨135050, by decide⟩,⟨135081, by decide⟩,⟨135123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4508_135124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4508 ⟨135124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4508
    ⟨135124, by decide⟩ (by decide) (![⟨134996, by decide⟩,⟨135050, by decide⟩,⟨135081, by decide⟩,⟨135123, by decide⟩]) unmarked_context_11_4508_135124 node_context_11_4508_135124
  intro a
  fin_cases a
  · exact context_12_18032_134996
  · exact context_12_18033_135050
  · exact context_12_18034_135081
  · exact context_12_18035_135123

theorem selected_cut_04263 : selected 9 ⟨135165, by decide⟩
    (prefixPartial 12 18036) = some ⟨12, 2, 0, 135165, 18036, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_18036_135165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18036 ⟨135165, by decide⟩ :=
  accepted_of_selected 12 18036 ⟨135165, by decide⟩ ⟨12, 2, 0, 135165, 18036, 2009, 65536⟩
    (by decide) selected_cut_04263

theorem selected_cut_04264 : selected 9 ⟨135231, by decide⟩
    (prefixPartial 12 18037) = some ⟨12, 2, 0, 135231, 18037, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_18037_135231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18037 ⟨135231, by decide⟩ :=
  accepted_of_selected 12 18037 ⟨135231, by decide⟩ ⟨12, 2, 0, 135231, 18037, 2453, 65536⟩
    (by decide) selected_cut_04264

theorem selected_cut_04265 : selected 9 ⟨135263, by decide⟩
    (prefixPartial 12 18038) = some ⟨12, 2, 0, 135263, 18038, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_18038_135263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18038 ⟨135263, by decide⟩ :=
  accepted_of_selected 12 18038 ⟨135263, by decide⟩ ⟨12, 2, 0, 135263, 18038, 1981, 65536⟩
    (by decide) selected_cut_04265

theorem selected_cut_04266 : selected 9 ⟨135301, by decide⟩
    (prefixPartial 12 18039) = some ⟨12, 2, 0, 135301, 18039, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_18039_135301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18039 ⟨135301, by decide⟩ :=
  accepted_of_selected 12 18039 ⟨135301, by decide⟩ ⟨12, 2, 0, 135301, 18039, 2021, 65536⟩
    (by decide) selected_cut_04266

theorem unmarked_context_11_4509_135302 : frontier 10 ⟨135302, by decide⟩
    (prefixCache 11 4509) (prefixPartial 11 4509) = false := by
  decide +kernel

theorem node_context_11_4509_135302 : EJMOriginalGlobalDAGData.nodes 10 ⟨135302, by decide⟩ =
    .split (coordinate 11) (![⟨135165, by decide⟩,⟨135231, by decide⟩,⟨135263, by decide⟩,⟨135301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4509_135302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4509 ⟨135302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4509
    ⟨135302, by decide⟩ (by decide) (![⟨135165, by decide⟩,⟨135231, by decide⟩,⟨135263, by decide⟩,⟨135301, by decide⟩]) unmarked_context_11_4509_135302 node_context_11_4509_135302
  intro a
  fin_cases a
  · exact context_12_18036_135165
  · exact context_12_18037_135231
  · exact context_12_18038_135263
  · exact context_12_18039_135301

theorem selected_cut_04267 : selected 9 ⟨135329, by decide⟩
    (prefixPartial 12 18040) = some ⟨12, 2, 0, 135329, 18040, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_18040_135329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18040 ⟨135329, by decide⟩ :=
  accepted_of_selected 12 18040 ⟨135329, by decide⟩ ⟨12, 2, 0, 135329, 18040, 1625, 65536⟩
    (by decide) selected_cut_04267

theorem selected_cut_04268 : selected 9 ⟨135383, by decide⟩
    (prefixPartial 12 18041) = some ⟨12, 2, 0, 135383, 18041, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_18041_135383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18041 ⟨135383, by decide⟩ :=
  accepted_of_selected 12 18041 ⟨135383, by decide⟩ ⟨12, 2, 0, 135383, 18041, 2137, 65536⟩
    (by decide) selected_cut_04268

theorem selected_cut_04269 : selected 9 ⟨135430, by decide⟩
    (prefixPartial 12 18042) = some ⟨12, 2, 0, 135430, 18042, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_18042_135430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18042 ⟨135430, by decide⟩ :=
  accepted_of_selected 12 18042 ⟨135430, by decide⟩ ⟨12, 2, 0, 135430, 18042, 2085, 65536⟩
    (by decide) selected_cut_04269

theorem selected_cut_04270 : selected 9 ⟨135462, by decide⟩
    (prefixPartial 12 18043) = some ⟨12, 2, 0, 135462, 18043, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_18043_135462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18043 ⟨135462, by decide⟩ :=
  accepted_of_selected 12 18043 ⟨135462, by decide⟩ ⟨12, 2, 0, 135462, 18043, 1565, 65536⟩
    (by decide) selected_cut_04270

theorem unmarked_context_11_4510_135463 : frontier 10 ⟨135463, by decide⟩
    (prefixCache 11 4510) (prefixPartial 11 4510) = false := by
  decide +kernel

theorem node_context_11_4510_135463 : EJMOriginalGlobalDAGData.nodes 10 ⟨135463, by decide⟩ =
    .split (coordinate 11) (![⟨135329, by decide⟩,⟨135383, by decide⟩,⟨135430, by decide⟩,⟨135462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4510_135463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4510 ⟨135463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4510
    ⟨135463, by decide⟩ (by decide) (![⟨135329, by decide⟩,⟨135383, by decide⟩,⟨135430, by decide⟩,⟨135462, by decide⟩]) unmarked_context_11_4510_135463 node_context_11_4510_135463
  intro a
  fin_cases a
  · exact context_12_18040_135329
  · exact context_12_18041_135383
  · exact context_12_18042_135430
  · exact context_12_18043_135462

theorem selected_cut_04271 : selected 9 ⟨135490, by decide⟩
    (prefixPartial 12 18044) = some ⟨12, 2, 0, 135490, 18044, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_18044_135490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18044 ⟨135490, by decide⟩ :=
  accepted_of_selected 12 18044 ⟨135490, by decide⟩ ⟨12, 2, 0, 135490, 18044, 1601, 65536⟩
    (by decide) selected_cut_04271

theorem selected_cut_04272 : selected 9 ⟨135551, by decide⟩
    (prefixPartial 12 18045) = some ⟨12, 2, 0, 135551, 18045, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_18045_135551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18045 ⟨135551, by decide⟩ :=
  accepted_of_selected 12 18045 ⟨135551, by decide⟩ ⟨12, 2, 0, 135551, 18045, 1961, 65536⟩
    (by decide) selected_cut_04272

theorem selected_cut_04273 : selected 9 ⟨135573, by decide⟩
    (prefixPartial 12 18046) = some ⟨12, 2, 0, 135573, 18046, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_18046_135573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18046 ⟨135573, by decide⟩ :=
  accepted_of_selected 12 18046 ⟨135573, by decide⟩ ⟨12, 2, 0, 135573, 18046, 1393, 65536⟩
    (by decide) selected_cut_04273

theorem selected_cut_04274 : selected 9 ⟨135594, by decide⟩
    (prefixPartial 12 18047) = some ⟨12, 2, 0, 135594, 18047, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_18047_135594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18047 ⟨135594, by decide⟩ :=
  accepted_of_selected 12 18047 ⟨135594, by decide⟩ ⟨12, 2, 0, 135594, 18047, 1441, 65536⟩
    (by decide) selected_cut_04274

theorem unmarked_context_11_4511_135595 : frontier 10 ⟨135595, by decide⟩
    (prefixCache 11 4511) (prefixPartial 11 4511) = false := by
  decide +kernel

theorem node_context_11_4511_135595 : EJMOriginalGlobalDAGData.nodes 10 ⟨135595, by decide⟩ =
    .split (coordinate 11) (![⟨135490, by decide⟩,⟨135551, by decide⟩,⟨135573, by decide⟩,⟨135594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4511_135595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4511 ⟨135595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4511
    ⟨135595, by decide⟩ (by decide) (![⟨135490, by decide⟩,⟨135551, by decide⟩,⟨135573, by decide⟩,⟨135594, by decide⟩]) unmarked_context_11_4511_135595 node_context_11_4511_135595
  intro a
  fin_cases a
  · exact context_12_18044_135490
  · exact context_12_18045_135551
  · exact context_12_18046_135573
  · exact context_12_18047_135594

theorem unmarked_context_10_1127_135596 : frontier 11 ⟨135596, by decide⟩
    (prefixCache 10 1127) (prefixPartial 10 1127) = false := by
  decide +kernel

theorem node_context_10_1127_135596 : EJMOriginalGlobalDAGData.nodes 11 ⟨135596, by decide⟩ =
    .split (coordinate 10) (![⟨135124, by decide⟩,⟨135302, by decide⟩,⟨135463, by decide⟩,⟨135595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1127_135596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1127 ⟨135596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1127
    ⟨135596, by decide⟩ (by decide) (![⟨135124, by decide⟩,⟨135302, by decide⟩,⟨135463, by decide⟩,⟨135595, by decide⟩]) unmarked_context_10_1127_135596 node_context_10_1127_135596
  intro a
  fin_cases a
  · exact context_11_4508_135124
  · exact context_11_4509_135302
  · exact context_11_4510_135463
  · exact context_11_4511_135595

theorem unmarked_context_9_281_135597 : frontier 12 ⟨135597, by decide⟩
    (prefixCache 9 281) (prefixPartial 9 281) = false := by
  decide +kernel

theorem node_context_9_281_135597 : EJMOriginalGlobalDAGData.nodes 12 ⟨135597, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨134129, by decide⟩,⟨134955, by decide⟩,⟨135596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_281_135597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 281 ⟨135597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 281
    ⟨135597, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨134129, by decide⟩,⟨134955, by decide⟩,⟨135596, by decide⟩]) unmarked_context_9_281_135597 node_context_9_281_135597
  intro a
  fin_cases a
  · exact context_10_1124_3442
  · exact context_10_1125_134129
  · exact context_10_1126_134955
  · exact context_10_1127_135596

theorem selected_cut_04275 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 1128) = some ⟨10, 1, 0, 3442, 1128, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1128_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1128 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 1128 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 1128, 1, 1048576⟩
    (by decide) selected_cut_04275

theorem selected_cut_04276 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 1129) = some ⟨10, 1, 0, 3442, 1129, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1129_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1129 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 1129 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 1129, 1, 1048576⟩
    (by decide) selected_cut_04276

theorem selected_cut_04277 : selected 10 ⟨135668, by decide⟩
    (prefixPartial 11 4520) = some ⟨11, 2, 0, 135668, 4520, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_4520_135668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4520 ⟨135668, by decide⟩ :=
  accepted_of_selected 11 4520 ⟨135668, by decide⟩ ⟨11, 2, 0, 135668, 4520, 2885, 262144⟩
    (by decide) selected_cut_04277

theorem selected_cut_04278 : selected 10 ⟨135720, by decide⟩
    (prefixPartial 11 4521) = some ⟨11, 2, 0, 135720, 4521, 2213, 262144⟩ := by
  decide +kernel

theorem context_11_4521_135720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4521 ⟨135720, by decide⟩ :=
  accepted_of_selected 11 4521 ⟨135720, by decide⟩ ⟨11, 2, 0, 135720, 4521, 2213, 262144⟩
    (by decide) selected_cut_04278

theorem selected_cut_04279 : selected 10 ⟨135752, by decide⟩
    (prefixPartial 11 4522) = some ⟨11, 2, 0, 135752, 4522, 833, 262144⟩ := by
  decide +kernel

theorem context_11_4522_135752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4522 ⟨135752, by decide⟩ :=
  accepted_of_selected 11 4522 ⟨135752, by decide⟩ ⟨11, 2, 0, 135752, 4522, 833, 262144⟩
    (by decide) selected_cut_04279

theorem selected_cut_04280 : selected 10 ⟨135764, by decide⟩
    (prefixPartial 11 4523) = some ⟨11, 2, 0, 135764, 4523, 445, 262144⟩ := by
  decide +kernel

theorem context_11_4523_135764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4523 ⟨135764, by decide⟩ :=
  accepted_of_selected 11 4523 ⟨135764, by decide⟩ ⟨11, 2, 0, 135764, 4523, 445, 262144⟩
    (by decide) selected_cut_04280

theorem unmarked_context_10_1130_135765 : frontier 11 ⟨135765, by decide⟩
    (prefixCache 10 1130) (prefixPartial 10 1130) = false := by
  decide +kernel

theorem node_context_10_1130_135765 : EJMOriginalGlobalDAGData.nodes 11 ⟨135765, by decide⟩ =
    .split (coordinate 10) (![⟨135668, by decide⟩,⟨135720, by decide⟩,⟨135752, by decide⟩,⟨135764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1130_135765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1130 ⟨135765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1130
    ⟨135765, by decide⟩ (by decide) (![⟨135668, by decide⟩,⟨135720, by decide⟩,⟨135752, by decide⟩,⟨135764, by decide⟩]) unmarked_context_10_1130_135765 node_context_10_1130_135765
  intro a
  fin_cases a
  · exact context_11_4520_135668
  · exact context_11_4521_135720
  · exact context_11_4522_135752
  · exact context_11_4523_135764

theorem selected_cut_04281 : selected 10 ⟨135825, by decide⟩
    (prefixPartial 11 4524) = some ⟨11, 2, 0, 135825, 4524, 2641, 262144⟩ := by
  decide +kernel

theorem context_11_4524_135825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4524 ⟨135825, by decide⟩ :=
  accepted_of_selected 11 4524 ⟨135825, by decide⟩ ⟨11, 2, 0, 135825, 4524, 2641, 262144⟩
    (by decide) selected_cut_04281

theorem selected_cut_04282 : selected 10 ⟨135874, by decide⟩
    (prefixPartial 11 4525) = some ⟨11, 2, 0, 135874, 4525, 2525, 262144⟩ := by
  decide +kernel

theorem context_11_4525_135874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4525 ⟨135874, by decide⟩ :=
  accepted_of_selected 11 4525 ⟨135874, by decide⟩ ⟨11, 2, 0, 135874, 4525, 2525, 262144⟩
    (by decide) selected_cut_04282

theorem selected_cut_04283 : selected 10 ⟨135925, by decide⟩
    (prefixPartial 11 4526) = some ⟨11, 2, 0, 135925, 4526, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_4526_135925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4526 ⟨135925, by decide⟩ :=
  accepted_of_selected 11 4526 ⟨135925, by decide⟩ ⟨11, 2, 0, 135925, 4526, 1877, 262144⟩
    (by decide) selected_cut_04283

theorem selected_cut_04284 : selected 10 ⟨135956, by decide⟩
    (prefixPartial 11 4527) = some ⟨11, 2, 0, 135956, 4527, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_4527_135956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4527 ⟨135956, by decide⟩ :=
  accepted_of_selected 11 4527 ⟨135956, by decide⟩ ⟨11, 2, 0, 135956, 4527, 1309, 262144⟩
    (by decide) selected_cut_04284

theorem unmarked_context_10_1131_135957 : frontier 11 ⟨135957, by decide⟩
    (prefixCache 10 1131) (prefixPartial 10 1131) = false := by
  decide +kernel

theorem node_context_10_1131_135957 : EJMOriginalGlobalDAGData.nodes 11 ⟨135957, by decide⟩ =
    .split (coordinate 10) (![⟨135825, by decide⟩,⟨135874, by decide⟩,⟨135925, by decide⟩,⟨135956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1131_135957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1131 ⟨135957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1131
    ⟨135957, by decide⟩ (by decide) (![⟨135825, by decide⟩,⟨135874, by decide⟩,⟨135925, by decide⟩,⟨135956, by decide⟩]) unmarked_context_10_1131_135957 node_context_10_1131_135957
  intro a
  fin_cases a
  · exact context_11_4524_135825
  · exact context_11_4525_135874
  · exact context_11_4526_135925
  · exact context_11_4527_135956

theorem unmarked_context_9_282_135958 : frontier 12 ⟨135958, by decide⟩
    (prefixCache 9 282) (prefixPartial 9 282) = false := by
  decide +kernel

theorem node_context_9_282_135958 : EJMOriginalGlobalDAGData.nodes 12 ⟨135958, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨135765, by decide⟩,⟨135957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_282_135958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 282 ⟨135958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 282
    ⟨135958, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨135765, by decide⟩,⟨135957, by decide⟩]) unmarked_context_9_282_135958 node_context_9_282_135958
  intro a
  fin_cases a
  · exact context_10_1128_3442
  · exact context_10_1129_3442
  · exact context_10_1130_135765
  · exact context_10_1131_135957

theorem selected_cut_04285 : selected 12 ⟨136004, by decide⟩
    (prefixPartial 9 283) = some ⟨9, 2, 0, 136004, 283, 1149, 4194304⟩ := by
  decide +kernel

theorem context_9_283_136004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 283 ⟨136004, by decide⟩ :=
  accepted_of_selected 9 283 ⟨136004, by decide⟩ ⟨9, 2, 0, 136004, 283, 1149, 4194304⟩
    (by decide) selected_cut_04285

theorem unmarked_context_8_70_136005 : frontier 13 ⟨136005, by decide⟩
    (prefixCache 8 70) (prefixPartial 8 70) = false := by
  decide +kernel

theorem node_context_8_70_136005 : EJMOriginalGlobalDAGData.nodes 13 ⟨136005, by decide⟩ =
    .split (coordinate 8) (![⟨133280, by decide⟩,⟨135597, by decide⟩,⟨135958, by decide⟩,⟨136004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_70_136005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 70 ⟨136005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 70
    ⟨136005, by decide⟩ (by decide) (![⟨133280, by decide⟩,⟨135597, by decide⟩,⟨135958, by decide⟩,⟨136004, by decide⟩]) unmarked_context_8_70_136005 node_context_8_70_136005
  intro a
  fin_cases a
  · exact context_9_280_133280
  · exact context_9_281_135597
  · exact context_9_282_135958
  · exact context_9_283_136004

theorem selected_cut_04286 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 71) = some ⟨8, 1, 0, 14298, 71, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_71_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 71 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 71 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 71, 1, 16777216⟩
    (by decide) selected_cut_04286

theorem unmarked_context_7_17_136006 : frontier 14 ⟨136006, by decide⟩
    (prefixCache 7 17) (prefixPartial 7 17) = false := by
  decide +kernel

theorem node_context_7_17_136006 : EJMOriginalGlobalDAGData.nodes 14 ⟨136006, by decide⟩ =
    .split (coordinate 7) (![⟨122919, by decide⟩,⟨127626, by decide⟩,⟨136005, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_17_136006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 17 ⟨136006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 17
    ⟨136006, by decide⟩ (by decide) (![⟨122919, by decide⟩,⟨127626, by decide⟩,⟨136005, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_17_136006 node_context_7_17_136006
  intro a
  fin_cases a
  · exact context_8_68_122919
  · exact context_8_69_127626
  · exact context_8_70_136005
  · exact context_8_71_14298

theorem selected_cut_04287 : selected 7 ⟨136075, by decide⟩
    (prefixPartial 14 294912) = some ⟨14, 2, 0, 136075, 294912, 1629, 4096⟩ := by
  decide +kernel

theorem context_14_294912_136075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294912 ⟨136075, by decide⟩ :=
  accepted_of_selected 14 294912 ⟨136075, by decide⟩ ⟨14, 2, 0, 136075, 294912, 1629, 4096⟩
    (by decide) selected_cut_04287

theorem selected_cut_04288 : selected 7 ⟨136166, by decide⟩
    (prefixPartial 14 294913) = some ⟨14, 2, 0, 136166, 294913, 2037, 4096⟩ := by
  decide +kernel

theorem context_14_294913_136166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294913 ⟨136166, by decide⟩ :=
  accepted_of_selected 14 294913 ⟨136166, by decide⟩ ⟨14, 2, 0, 136166, 294913, 2037, 4096⟩
    (by decide) selected_cut_04288

theorem selected_cut_04289 : selected 7 ⟨136275, by decide⟩
    (prefixPartial 14 294914) = some ⟨14, 2, 0, 136275, 294914, 2069, 4096⟩ := by
  decide +kernel

theorem context_14_294914_136275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294914 ⟨136275, by decide⟩ :=
  accepted_of_selected 14 294914 ⟨136275, by decide⟩ ⟨14, 2, 0, 136275, 294914, 2069, 4096⟩
    (by decide) selected_cut_04289

theorem selected_cut_04290 : selected 7 ⟨136362, by decide⟩
    (prefixPartial 14 294915) = some ⟨14, 2, 0, 136362, 294915, 1457, 4096⟩ := by
  decide +kernel

theorem context_14_294915_136362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294915 ⟨136362, by decide⟩ :=
  accepted_of_selected 14 294915 ⟨136362, by decide⟩ ⟨14, 2, 0, 136362, 294915, 1457, 4096⟩
    (by decide) selected_cut_04290

theorem unmarked_context_13_73728_136363 : frontier 8 ⟨136363, by decide⟩
    (prefixCache 13 73728) (prefixPartial 13 73728) = false := by
  decide +kernel

theorem node_context_13_73728_136363 : EJMOriginalGlobalDAGData.nodes 8 ⟨136363, by decide⟩ =
    .split (coordinate 13) (![⟨136075, by decide⟩,⟨136166, by decide⟩,⟨136275, by decide⟩,⟨136362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73728_136363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73728 ⟨136363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73728
    ⟨136363, by decide⟩ (by decide) (![⟨136075, by decide⟩,⟨136166, by decide⟩,⟨136275, by decide⟩,⟨136362, by decide⟩]) unmarked_context_13_73728_136363 node_context_13_73728_136363
  intro a
  fin_cases a
  · exact context_14_294912_136075
  · exact context_14_294913_136166
  · exact context_14_294914_136275
  · exact context_14_294915_136362

theorem selected_cut_04291 : selected 8 ⟨136533, by decide⟩
    (prefixPartial 13 73729) = some ⟨13, 2, 0, 136533, 73729, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_73729_136533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73729 ⟨136533, by decide⟩ :=
  accepted_of_selected 13 73729 ⟨136533, by decide⟩ ⟨13, 2, 0, 136533, 73729, 1889, 16384⟩
    (by decide) selected_cut_04291

theorem selected_cut_04292 : selected 8 ⟨136566, by decide⟩
    (prefixPartial 13 73730) = some ⟨13, 2, 0, 136566, 73730, 209, 16384⟩ := by
  decide +kernel

theorem context_13_73730_136566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73730 ⟨136566, by decide⟩ :=
  accepted_of_selected 13 73730 ⟨136566, by decide⟩ ⟨13, 2, 0, 136566, 73730, 209, 16384⟩
    (by decide) selected_cut_04292

theorem selected_cut_04293 : selected 8 ⟨136569, by decide⟩
    (prefixPartial 13 73731) = some ⟨13, 2, 0, 136569, 73731, 29, 16384⟩ := by
  decide +kernel

theorem context_13_73731_136569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73731 ⟨136569, by decide⟩ :=
  accepted_of_selected 13 73731 ⟨136569, by decide⟩ ⟨13, 2, 0, 136569, 73731, 29, 16384⟩
    (by decide) selected_cut_04293

theorem unmarked_context_12_18432_136570 : frontier 9 ⟨136570, by decide⟩
    (prefixCache 12 18432) (prefixPartial 12 18432) = false := by
  decide +kernel

theorem node_context_12_18432_136570 : EJMOriginalGlobalDAGData.nodes 9 ⟨136570, by decide⟩ =
    .split (coordinate 12) (![⟨136363, by decide⟩,⟨136533, by decide⟩,⟨136566, by decide⟩,⟨136569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18432_136570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18432 ⟨136570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18432
    ⟨136570, by decide⟩ (by decide) (![⟨136363, by decide⟩,⟨136533, by decide⟩,⟨136566, by decide⟩,⟨136569, by decide⟩]) unmarked_context_12_18432_136570 node_context_12_18432_136570
  intro a
  fin_cases a
  · exact context_13_73728_136363
  · exact context_13_73729_136533
  · exact context_13_73730_136566
  · exact context_13_73731_136569

theorem selected_cut_04294 : selected 7 ⟨136616, by decide⟩
    (prefixPartial 14 294928) = some ⟨14, 2, 0, 136616, 294928, 1761, 4096⟩ := by
  decide +kernel

theorem context_14_294928_136616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294928 ⟨136616, by decide⟩ :=
  accepted_of_selected 14 294928 ⟨136616, by decide⟩ ⟨14, 2, 0, 136616, 294928, 1761, 4096⟩
    (by decide) selected_cut_04294

theorem selected_cut_04295 : selected 7 ⟨136641, by decide⟩
    (prefixPartial 14 294929) = some ⟨14, 2, 0, 136641, 294929, 1629, 4096⟩ := by
  decide +kernel

theorem context_14_294929_136641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294929 ⟨136641, by decide⟩ :=
  accepted_of_selected 14 294929 ⟨136641, by decide⟩ ⟨14, 2, 0, 136641, 294929, 1629, 4096⟩
    (by decide) selected_cut_04295

theorem selected_cut_04296 : selected 7 ⟨136671, by decide⟩
    (prefixPartial 14 294930) = some ⟨14, 2, 0, 136671, 294930, 1721, 4096⟩ := by
  decide +kernel

theorem context_14_294930_136671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294930 ⟨136671, by decide⟩ :=
  accepted_of_selected 14 294930 ⟨136671, by decide⟩ ⟨14, 2, 0, 136671, 294930, 1721, 4096⟩
    (by decide) selected_cut_04296

theorem selected_cut_04297 : selected 7 ⟨136701, by decide⟩
    (prefixPartial 14 294931) = some ⟨14, 2, 0, 136701, 294931, 1617, 4096⟩ := by
  decide +kernel

theorem context_14_294931_136701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294931 ⟨136701, by decide⟩ :=
  accepted_of_selected 14 294931 ⟨136701, by decide⟩ ⟨14, 2, 0, 136701, 294931, 1617, 4096⟩
    (by decide) selected_cut_04297

theorem unmarked_context_13_73732_136702 : frontier 8 ⟨136702, by decide⟩
    (prefixCache 13 73732) (prefixPartial 13 73732) = false := by
  decide +kernel

theorem node_context_13_73732_136702 : EJMOriginalGlobalDAGData.nodes 8 ⟨136702, by decide⟩ =
    .split (coordinate 13) (![⟨136616, by decide⟩,⟨136641, by decide⟩,⟨136671, by decide⟩,⟨136701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73732_136702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73732 ⟨136702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73732
    ⟨136702, by decide⟩ (by decide) (![⟨136616, by decide⟩,⟨136641, by decide⟩,⟨136671, by decide⟩,⟨136701, by decide⟩]) unmarked_context_13_73732_136702 node_context_13_73732_136702
  intro a
  fin_cases a
  · exact context_14_294928_136616
  · exact context_14_294929_136641
  · exact context_14_294930_136671
  · exact context_14_294931_136701

theorem selected_cut_04298 : selected 7 ⟨136710, by decide⟩
    (prefixPartial 14 294932) = some ⟨14, 2, 0, 136710, 294932, 633, 4096⟩ := by
  decide +kernel

theorem context_14_294932_136710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294932 ⟨136710, by decide⟩ :=
  accepted_of_selected 14 294932 ⟨136710, by decide⟩ ⟨14, 2, 0, 136710, 294932, 633, 4096⟩
    (by decide) selected_cut_04298

theorem selected_cut_04299 : selected 7 ⟨136745, by decide⟩
    (prefixPartial 14 294933) = some ⟨14, 2, 0, 136745, 294933, 1465, 4096⟩ := by
  decide +kernel

theorem context_14_294933_136745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294933 ⟨136745, by decide⟩ :=
  accepted_of_selected 14 294933 ⟨136745, by decide⟩ ⟨14, 2, 0, 136745, 294933, 1465, 4096⟩
    (by decide) selected_cut_04299

theorem selected_cut_04300 : selected 7 ⟨136779, by decide⟩
    (prefixPartial 14 294934) = some ⟨14, 2, 0, 136779, 294934, 1705, 4096⟩ := by
  decide +kernel

theorem context_14_294934_136779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294934 ⟨136779, by decide⟩ :=
  accepted_of_selected 14 294934 ⟨136779, by decide⟩ ⟨14, 2, 0, 136779, 294934, 1705, 4096⟩
    (by decide) selected_cut_04300

theorem selected_cut_04301 : selected 7 ⟨136807, by decide⟩
    (prefixPartial 14 294935) = some ⟨14, 2, 0, 136807, 294935, 1373, 4096⟩ := by
  decide +kernel

theorem context_14_294935_136807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294935 ⟨136807, by decide⟩ :=
  accepted_of_selected 14 294935 ⟨136807, by decide⟩ ⟨14, 2, 0, 136807, 294935, 1373, 4096⟩
    (by decide) selected_cut_04301

theorem unmarked_context_13_73733_136808 : frontier 8 ⟨136808, by decide⟩
    (prefixCache 13 73733) (prefixPartial 13 73733) = false := by
  decide +kernel

theorem node_context_13_73733_136808 : EJMOriginalGlobalDAGData.nodes 8 ⟨136808, by decide⟩ =
    .split (coordinate 13) (![⟨136710, by decide⟩,⟨136745, by decide⟩,⟨136779, by decide⟩,⟨136807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73733_136808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73733 ⟨136808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73733
    ⟨136808, by decide⟩ (by decide) (![⟨136710, by decide⟩,⟨136745, by decide⟩,⟨136779, by decide⟩,⟨136807, by decide⟩]) unmarked_context_13_73733_136808 node_context_13_73733_136808
  intro a
  fin_cases a
  · exact context_14_294932_136710
  · exact context_14_294933_136745
  · exact context_14_294934_136779
  · exact context_14_294935_136807

theorem selected_cut_04302 : selected 8 ⟨136876, by decide⟩
    (prefixPartial 13 73734) = some ⟨13, 2, 0, 136876, 73734, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_73734_136876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73734 ⟨136876, by decide⟩ :=
  accepted_of_selected 13 73734 ⟨136876, by decide⟩ ⟨13, 2, 0, 136876, 73734, 3089, 16384⟩
    (by decide) selected_cut_04302

theorem selected_cut_04303 : selected 8 ⟨136903, by decide⟩
    (prefixPartial 13 73735) = some ⟨13, 2, 0, 136903, 73735, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_73735_136903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73735 ⟨136903, by decide⟩ :=
  accepted_of_selected 13 73735 ⟨136903, by decide⟩ ⟨13, 2, 0, 136903, 73735, 1441, 16384⟩
    (by decide) selected_cut_04303

theorem unmarked_context_12_18433_136904 : frontier 9 ⟨136904, by decide⟩
    (prefixCache 12 18433) (prefixPartial 12 18433) = false := by
  decide +kernel

theorem node_context_12_18433_136904 : EJMOriginalGlobalDAGData.nodes 9 ⟨136904, by decide⟩ =
    .split (coordinate 12) (![⟨136702, by decide⟩,⟨136808, by decide⟩,⟨136876, by decide⟩,⟨136903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18433_136904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18433 ⟨136904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18433
    ⟨136904, by decide⟩ (by decide) (![⟨136702, by decide⟩,⟨136808, by decide⟩,⟨136876, by decide⟩,⟨136903, by decide⟩]) unmarked_context_12_18433_136904 node_context_12_18433_136904
  intro a
  fin_cases a
  · exact context_13_73732_136702
  · exact context_13_73733_136808
  · exact context_13_73734_136876
  · exact context_13_73735_136903

theorem selected_cut_04304 : selected 7 ⟨136941, by decide⟩
    (prefixPartial 14 294944) = some ⟨14, 2, 0, 136941, 294944, 1581, 4096⟩ := by
  decide +kernel

theorem context_14_294944_136941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294944 ⟨136941, by decide⟩ :=
  accepted_of_selected 14 294944 ⟨136941, by decide⟩ ⟨14, 2, 0, 136941, 294944, 1581, 4096⟩
    (by decide) selected_cut_04304

theorem selected_cut_04305 : selected 7 ⟨136965, by decide⟩
    (prefixPartial 14 294945) = some ⟨14, 2, 0, 136965, 294945, 1369, 4096⟩ := by
  decide +kernel

theorem context_14_294945_136965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294945 ⟨136965, by decide⟩ :=
  accepted_of_selected 14 294945 ⟨136965, by decide⟩ ⟨14, 2, 0, 136965, 294945, 1369, 4096⟩
    (by decide) selected_cut_04305

theorem selected_cut_04306 : selected 7 ⟨136990, by decide⟩
    (prefixPartial 14 294946) = some ⟨14, 2, 0, 136990, 294946, 1549, 4096⟩ := by
  decide +kernel

theorem context_14_294946_136990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294946 ⟨136990, by decide⟩ :=
  accepted_of_selected 14 294946 ⟨136990, by decide⟩ ⟨14, 2, 0, 136990, 294946, 1549, 4096⟩
    (by decide) selected_cut_04306

theorem selected_cut_04307 : selected 7 ⟨137011, by decide⟩
    (prefixPartial 14 294947) = some ⟨14, 2, 0, 137011, 294947, 1465, 4096⟩ := by
  decide +kernel

theorem context_14_294947_137011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294947 ⟨137011, by decide⟩ :=
  accepted_of_selected 14 294947 ⟨137011, by decide⟩ ⟨14, 2, 0, 137011, 294947, 1465, 4096⟩
    (by decide) selected_cut_04307

theorem unmarked_context_13_73736_137012 : frontier 8 ⟨137012, by decide⟩
    (prefixCache 13 73736) (prefixPartial 13 73736) = false := by
  decide +kernel

theorem node_context_13_73736_137012 : EJMOriginalGlobalDAGData.nodes 8 ⟨137012, by decide⟩ =
    .split (coordinate 13) (![⟨136941, by decide⟩,⟨136965, by decide⟩,⟨136990, by decide⟩,⟨137011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73736_137012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73736 ⟨137012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73736
    ⟨137012, by decide⟩ (by decide) (![⟨136941, by decide⟩,⟨136965, by decide⟩,⟨136990, by decide⟩,⟨137011, by decide⟩]) unmarked_context_13_73736_137012 node_context_13_73736_137012
  intro a
  fin_cases a
  · exact context_14_294944_136941
  · exact context_14_294945_136965
  · exact context_14_294946_136990
  · exact context_14_294947_137011

theorem selected_cut_04308 : selected 7 ⟨137031, by decide⟩
    (prefixPartial 14 294948) = some ⟨14, 2, 0, 137031, 294948, 909, 4096⟩ := by
  decide +kernel

theorem context_14_294948_137031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294948 ⟨137031, by decide⟩ :=
  accepted_of_selected 14 294948 ⟨137031, by decide⟩ ⟨14, 2, 0, 137031, 294948, 909, 4096⟩
    (by decide) selected_cut_04308

theorem selected_cut_04309 : selected 7 ⟨137067, by decide⟩
    (prefixPartial 14 294949) = some ⟨14, 2, 0, 137067, 294949, 1641, 4096⟩ := by
  decide +kernel

theorem context_14_294949_137067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294949 ⟨137067, by decide⟩ :=
  accepted_of_selected 14 294949 ⟨137067, by decide⟩ ⟨14, 2, 0, 137067, 294949, 1641, 4096⟩
    (by decide) selected_cut_04309

theorem selected_cut_04310 : selected 7 ⟨137099, by decide⟩
    (prefixPartial 14 294950) = some ⟨14, 2, 0, 137099, 294950, 1789, 4096⟩ := by
  decide +kernel

theorem context_14_294950_137099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294950 ⟨137099, by decide⟩ :=
  accepted_of_selected 14 294950 ⟨137099, by decide⟩ ⟨14, 2, 0, 137099, 294950, 1789, 4096⟩
    (by decide) selected_cut_04310

theorem selected_cut_04311 : selected 7 ⟨137130, by decide⟩
    (prefixPartial 14 294951) = some ⟨14, 2, 0, 137130, 294951, 1453, 4096⟩ := by
  decide +kernel

theorem context_14_294951_137130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294951 ⟨137130, by decide⟩ :=
  accepted_of_selected 14 294951 ⟨137130, by decide⟩ ⟨14, 2, 0, 137130, 294951, 1453, 4096⟩
    (by decide) selected_cut_04311

theorem unmarked_context_13_73737_137131 : frontier 8 ⟨137131, by decide⟩
    (prefixCache 13 73737) (prefixPartial 13 73737) = false := by
  decide +kernel

theorem node_context_13_73737_137131 : EJMOriginalGlobalDAGData.nodes 8 ⟨137131, by decide⟩ =
    .split (coordinate 13) (![⟨137031, by decide⟩,⟨137067, by decide⟩,⟨137099, by decide⟩,⟨137130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73737_137131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73737 ⟨137131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73737
    ⟨137131, by decide⟩ (by decide) (![⟨137031, by decide⟩,⟨137067, by decide⟩,⟨137099, by decide⟩,⟨137130, by decide⟩]) unmarked_context_13_73737_137131 node_context_13_73737_137131
  intro a
  fin_cases a
  · exact context_14_294948_137031
  · exact context_14_294949_137067
  · exact context_14_294950_137099
  · exact context_14_294951_137130

theorem selected_cut_04312 : selected 8 ⟨137192, by decide⟩
    (prefixPartial 13 73738) = some ⟨13, 2, 0, 137192, 73738, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_73738_137192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73738 ⟨137192, by decide⟩ :=
  accepted_of_selected 13 73738 ⟨137192, by decide⟩ ⟨13, 2, 0, 137192, 73738, 2865, 16384⟩
    (by decide) selected_cut_04312

theorem selected_cut_04313 : selected 8 ⟨137221, by decide⟩
    (prefixPartial 13 73739) = some ⟨13, 2, 0, 137221, 73739, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_73739_137221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73739 ⟨137221, by decide⟩ :=
  accepted_of_selected 13 73739 ⟨137221, by decide⟩ ⟨13, 2, 0, 137221, 73739, 1417, 16384⟩
    (by decide) selected_cut_04313

theorem unmarked_context_12_18434_137222 : frontier 9 ⟨137222, by decide⟩
    (prefixCache 12 18434) (prefixPartial 12 18434) = false := by
  decide +kernel

theorem node_context_12_18434_137222 : EJMOriginalGlobalDAGData.nodes 9 ⟨137222, by decide⟩ =
    .split (coordinate 12) (![⟨137012, by decide⟩,⟨137131, by decide⟩,⟨137192, by decide⟩,⟨137221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18434_137222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18434 ⟨137222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18434
    ⟨137222, by decide⟩ (by decide) (![⟨137012, by decide⟩,⟨137131, by decide⟩,⟨137192, by decide⟩,⟨137221, by decide⟩]) unmarked_context_12_18434_137222 node_context_12_18434_137222
  intro a
  fin_cases a
  · exact context_13_73736_137012
  · exact context_13_73737_137131
  · exact context_13_73738_137192
  · exact context_13_73739_137221

theorem selected_cut_04314 : selected 7 ⟨137259, by decide⟩
    (prefixPartial 14 294960) = some ⟨14, 2, 0, 137259, 294960, 1493, 4096⟩ := by
  decide +kernel

theorem context_14_294960_137259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294960 ⟨137259, by decide⟩ :=
  accepted_of_selected 14 294960 ⟨137259, by decide⟩ ⟨14, 2, 0, 137259, 294960, 1493, 4096⟩
    (by decide) selected_cut_04314

theorem selected_cut_04315 : selected 7 ⟨137285, by decide⟩
    (prefixPartial 14 294961) = some ⟨14, 2, 0, 137285, 294961, 1485, 4096⟩ := by
  decide +kernel

theorem context_14_294961_137285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294961 ⟨137285, by decide⟩ :=
  accepted_of_selected 14 294961 ⟨137285, by decide⟩ ⟨14, 2, 0, 137285, 294961, 1485, 4096⟩
    (by decide) selected_cut_04315

theorem selected_cut_04316 : selected 7 ⟨137318, by decide⟩
    (prefixPartial 14 294962) = some ⟨14, 2, 0, 137318, 294962, 1817, 4096⟩ := by
  decide +kernel

theorem context_14_294962_137318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294962 ⟨137318, by decide⟩ :=
  accepted_of_selected 14 294962 ⟨137318, by decide⟩ ⟨14, 2, 0, 137318, 294962, 1817, 4096⟩
    (by decide) selected_cut_04316

theorem selected_cut_04317 : selected 7 ⟨137351, by decide⟩
    (prefixPartial 14 294963) = some ⟨14, 2, 0, 137351, 294963, 1573, 4096⟩ := by
  decide +kernel

theorem context_14_294963_137351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294963 ⟨137351, by decide⟩ :=
  accepted_of_selected 14 294963 ⟨137351, by decide⟩ ⟨14, 2, 0, 137351, 294963, 1573, 4096⟩
    (by decide) selected_cut_04317

theorem unmarked_context_13_73740_137352 : frontier 8 ⟨137352, by decide⟩
    (prefixCache 13 73740) (prefixPartial 13 73740) = false := by
  decide +kernel

theorem node_context_13_73740_137352 : EJMOriginalGlobalDAGData.nodes 8 ⟨137352, by decide⟩ =
    .split (coordinate 13) (![⟨137259, by decide⟩,⟨137285, by decide⟩,⟨137318, by decide⟩,⟨137351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73740_137352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73740 ⟨137352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73740
    ⟨137352, by decide⟩ (by decide) (![⟨137259, by decide⟩,⟨137285, by decide⟩,⟨137318, by decide⟩,⟨137351, by decide⟩]) unmarked_context_13_73740_137352 node_context_13_73740_137352
  intro a
  fin_cases a
  · exact context_14_294960_137259
  · exact context_14_294961_137285
  · exact context_14_294962_137318
  · exact context_14_294963_137351

theorem selected_cut_04318 : selected 7 ⟨137377, by decide⟩
    (prefixPartial 14 294964) = some ⟨14, 2, 0, 137377, 294964, 937, 4096⟩ := by
  decide +kernel

theorem context_14_294964_137377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294964 ⟨137377, by decide⟩ :=
  accepted_of_selected 14 294964 ⟨137377, by decide⟩ ⟨14, 2, 0, 137377, 294964, 937, 4096⟩
    (by decide) selected_cut_04318

theorem selected_cut_04319 : selected 7 ⟨137413, by decide⟩
    (prefixPartial 14 294965) = some ⟨14, 2, 0, 137413, 294965, 1641, 4096⟩ := by
  decide +kernel

theorem context_14_294965_137413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294965 ⟨137413, by decide⟩ :=
  accepted_of_selected 14 294965 ⟨137413, by decide⟩ ⟨14, 2, 0, 137413, 294965, 1641, 4096⟩
    (by decide) selected_cut_04319

theorem selected_cut_04320 : selected 7 ⟨137451, by decide⟩
    (prefixPartial 14 294966) = some ⟨14, 2, 0, 137451, 294966, 1857, 4096⟩ := by
  decide +kernel

theorem context_14_294966_137451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294966 ⟨137451, by decide⟩ :=
  accepted_of_selected 14 294966 ⟨137451, by decide⟩ ⟨14, 2, 0, 137451, 294966, 1857, 4096⟩
    (by decide) selected_cut_04320

theorem selected_cut_04321 : selected 7 ⟨137476, by decide⟩
    (prefixPartial 14 294967) = some ⟨14, 2, 0, 137476, 294967, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_294967_137476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294967 ⟨137476, by decide⟩ :=
  accepted_of_selected 14 294967 ⟨137476, by decide⟩ ⟨14, 2, 0, 137476, 294967, 1357, 4096⟩
    (by decide) selected_cut_04321

theorem unmarked_context_13_73741_137477 : frontier 8 ⟨137477, by decide⟩
    (prefixCache 13 73741) (prefixPartial 13 73741) = false := by
  decide +kernel

theorem node_context_13_73741_137477 : EJMOriginalGlobalDAGData.nodes 8 ⟨137477, by decide⟩ =
    .split (coordinate 13) (![⟨137377, by decide⟩,⟨137413, by decide⟩,⟨137451, by decide⟩,⟨137476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73741_137477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73741 ⟨137477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73741
    ⟨137477, by decide⟩ (by decide) (![⟨137377, by decide⟩,⟨137413, by decide⟩,⟨137451, by decide⟩,⟨137476, by decide⟩]) unmarked_context_13_73741_137477 node_context_13_73741_137477
  intro a
  fin_cases a
  · exact context_14_294964_137377
  · exact context_14_294965_137413
  · exact context_14_294966_137451
  · exact context_14_294967_137476

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
