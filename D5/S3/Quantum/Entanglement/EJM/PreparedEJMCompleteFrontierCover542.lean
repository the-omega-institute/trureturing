/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover541
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_52033 : selected 13 ⟨1487329, by decide⟩
    (prefixPartial 8 4480) = some ⟨8, 1, 0, 1487329, 4480, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4480_1487329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4480 ⟨1487329, by decide⟩ :=
  accepted_of_selected 8 4480 ⟨1487329, by decide⟩ ⟨8, 1, 0, 1487329, 4480, 1, 16777216⟩
    (by decide) selected_cut_52033

theorem selected_cut_52034 : selected 13 ⟨1487329, by decide⟩
    (prefixPartial 8 4481) = some ⟨8, 1, 0, 1487329, 4481, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4481_1487329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4481 ⟨1487329, by decide⟩ :=
  accepted_of_selected 8 4481 ⟨1487329, by decide⟩ ⟨8, 1, 0, 1487329, 4481, 1, 16777216⟩
    (by decide) selected_cut_52034

theorem selected_cut_52035 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71712) = some ⟨10, 1, 0, 1468246, 71712, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71712_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71712 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71712 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71712, 1, 1048576⟩
    (by decide) selected_cut_52035

theorem selected_cut_52036 : selected 10 ⟨1507607, by decide⟩
    (prefixPartial 11 286852) = some ⟨11, 2, 0, 1507607, 286852, 2973, 262144⟩ := by
  decide +kernel

theorem context_11_286852_1507607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286852 ⟨1507607, by decide⟩ :=
  accepted_of_selected 11 286852 ⟨1507607, by decide⟩ ⟨11, 2, 0, 1507607, 286852, 2973, 262144⟩
    (by decide) selected_cut_52036

theorem selected_cut_52037 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 286853) = some ⟨11, 1, 0, 1468419, 286853, 1, 262144⟩ := by
  decide +kernel

theorem context_11_286853_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286853 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 286853 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 286853, 1, 262144⟩
    (by decide) selected_cut_52037

theorem selected_cut_52038 : selected 10 ⟨1507806, by decide⟩
    (prefixPartial 11 286854) = some ⟨11, 2, 0, 1507806, 286854, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_286854_1507806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286854 ⟨1507806, by decide⟩ :=
  accepted_of_selected 11 286854 ⟨1507806, by decide⟩ ⟨11, 2, 0, 1507806, 286854, 3469, 262144⟩
    (by decide) selected_cut_52038

theorem selected_cut_52039 : selected 10 ⟨1507976, by decide⟩
    (prefixPartial 11 286855) = some ⟨11, 2, 0, 1507976, 286855, 3397, 262144⟩ := by
  decide +kernel

theorem context_11_286855_1507976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286855 ⟨1507976, by decide⟩ :=
  accepted_of_selected 11 286855 ⟨1507976, by decide⟩ ⟨11, 2, 0, 1507976, 286855, 3397, 262144⟩
    (by decide) selected_cut_52039

theorem unmarked_context_10_71713_1507977 : frontier 11 ⟨1507977, by decide⟩
    (prefixCache 10 71713) (prefixPartial 10 71713) = false := by
  decide +kernel

theorem node_context_10_71713_1507977 : EJMOriginalGlobalDAGData.nodes 11 ⟨1507977, by decide⟩ =
    .split (coordinate 10) (![⟨1507607, by decide⟩,⟨1468419, by decide⟩,⟨1507806, by decide⟩,⟨1507976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71713_1507977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71713 ⟨1507977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71713
    ⟨1507977, by decide⟩ (by decide) (![⟨1507607, by decide⟩,⟨1468419, by decide⟩,⟨1507806, by decide⟩,⟨1507976, by decide⟩]) unmarked_context_10_71713_1507977 node_context_10_71713_1507977
  intro a
  fin_cases a
  · exact context_11_286852_1507607
  · exact context_11_286853_1468419
  · exact context_11_286854_1507806
  · exact context_11_286855_1507976

theorem selected_cut_52040 : selected 10 ⟨1508088, by decide⟩
    (prefixPartial 11 286856) = some ⟨11, 2, 0, 1508088, 286856, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_286856_1508088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286856 ⟨1508088, by decide⟩ :=
  accepted_of_selected 11 286856 ⟨1508088, by decide⟩ ⟨11, 2, 0, 1508088, 286856, 1897, 262144⟩
    (by decide) selected_cut_52040

theorem selected_cut_52041 : selected 10 ⟨1508158, by decide⟩
    (prefixPartial 11 286857) = some ⟨11, 2, 0, 1508158, 286857, 1177, 262144⟩ := by
  decide +kernel

theorem context_11_286857_1508158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286857 ⟨1508158, by decide⟩ :=
  accepted_of_selected 11 286857 ⟨1508158, by decide⟩ ⟨11, 2, 0, 1508158, 286857, 1177, 262144⟩
    (by decide) selected_cut_52041

theorem selected_cut_52042 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 286858) = some ⟨11, 1, 0, 1468743, 286858, 1, 262144⟩ := by
  decide +kernel

theorem context_11_286858_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286858 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 286858 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 286858, 1, 262144⟩
    (by decide) selected_cut_52042

theorem selected_cut_52043 : selected 10 ⟨1508226, by decide⟩
    (prefixPartial 11 286859) = some ⟨11, 2, 0, 1508226, 286859, 1245, 262144⟩ := by
  decide +kernel

theorem context_11_286859_1508226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286859 ⟨1508226, by decide⟩ :=
  accepted_of_selected 11 286859 ⟨1508226, by decide⟩ ⟨11, 2, 0, 1508226, 286859, 1245, 262144⟩
    (by decide) selected_cut_52043

theorem unmarked_context_10_71714_1508227 : frontier 11 ⟨1508227, by decide⟩
    (prefixCache 10 71714) (prefixPartial 10 71714) = false := by
  decide +kernel

theorem node_context_10_71714_1508227 : EJMOriginalGlobalDAGData.nodes 11 ⟨1508227, by decide⟩ =
    .split (coordinate 10) (![⟨1508088, by decide⟩,⟨1508158, by decide⟩,⟨1468743, by decide⟩,⟨1508226, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71714_1508227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71714 ⟨1508227, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71714
    ⟨1508227, by decide⟩ (by decide) (![⟨1508088, by decide⟩,⟨1508158, by decide⟩,⟨1468743, by decide⟩,⟨1508226, by decide⟩]) unmarked_context_10_71714_1508227 node_context_10_71714_1508227
  intro a
  fin_cases a
  · exact context_11_286856_1508088
  · exact context_11_286857_1508158
  · exact context_11_286858_1468743
  · exact context_11_286859_1508226

theorem selected_cut_52044 : selected 10 ⟨1508339, by decide⟩
    (prefixPartial 11 286860) = some ⟨11, 2, 0, 1508339, 286860, 1357, 262144⟩ := by
  decide +kernel

theorem context_11_286860_1508339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286860 ⟨1508339, by decide⟩ :=
  accepted_of_selected 11 286860 ⟨1508339, by decide⟩ ⟨11, 2, 0, 1508339, 286860, 1357, 262144⟩
    (by decide) selected_cut_52044

theorem selected_cut_52045 : selected 10 ⟨1508441, by decide⟩
    (prefixPartial 11 286861) = some ⟨11, 2, 0, 1508441, 286861, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_286861_1508441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286861 ⟨1508441, by decide⟩ :=
  accepted_of_selected 11 286861 ⟨1508441, by decide⟩ ⟨11, 2, 0, 1508441, 286861, 2041, 262144⟩
    (by decide) selected_cut_52045

theorem selected_cut_52046 : selected 10 ⟨1508540, by decide⟩
    (prefixPartial 11 286862) = some ⟨11, 2, 0, 1508540, 286862, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_286862_1508540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286862 ⟨1508540, by decide⟩ :=
  accepted_of_selected 11 286862 ⟨1508540, by decide⟩ ⟨11, 2, 0, 1508540, 286862, 1941, 262144⟩
    (by decide) selected_cut_52046

theorem selected_cut_52047 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 286863) = some ⟨11, 1, 0, 1470044, 286863, 1, 262144⟩ := by
  decide +kernel

theorem context_11_286863_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286863 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 286863 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 286863, 1, 262144⟩
    (by decide) selected_cut_52047

theorem unmarked_context_10_71715_1508541 : frontier 11 ⟨1508541, by decide⟩
    (prefixCache 10 71715) (prefixPartial 10 71715) = false := by
  decide +kernel

theorem node_context_10_71715_1508541 : EJMOriginalGlobalDAGData.nodes 11 ⟨1508541, by decide⟩ =
    .split (coordinate 10) (![⟨1508339, by decide⟩,⟨1508441, by decide⟩,⟨1508540, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71715_1508541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71715 ⟨1508541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71715
    ⟨1508541, by decide⟩ (by decide) (![⟨1508339, by decide⟩,⟨1508441, by decide⟩,⟨1508540, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71715_1508541 node_context_10_71715_1508541
  intro a
  fin_cases a
  · exact context_11_286860_1508339
  · exact context_11_286861_1508441
  · exact context_11_286862_1508540
  · exact context_11_286863_1470044

theorem unmarked_context_9_17928_1508542 : frontier 12 ⟨1508542, by decide⟩
    (prefixCache 9 17928) (prefixPartial 9 17928) = false := by
  decide +kernel

theorem node_context_9_17928_1508542 : EJMOriginalGlobalDAGData.nodes 12 ⟨1508542, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1507977, by decide⟩,⟨1508227, by decide⟩,⟨1508541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17928_1508542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17928 ⟨1508542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17928
    ⟨1508542, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1507977, by decide⟩,⟨1508227, by decide⟩,⟨1508541, by decide⟩]) unmarked_context_9_17928_1508542 node_context_9_17928_1508542
  intro a
  fin_cases a
  · exact context_10_71712_1468246
  · exact context_10_71713_1507977
  · exact context_10_71714_1508227
  · exact context_10_71715_1508541

theorem selected_cut_52048 : selected 11 ⟨1508684, by decide⟩
    (prefixPartial 10 71716) = some ⟨10, 2, 0, 1508684, 71716, 1997, 1048576⟩ := by
  decide +kernel

theorem context_10_71716_1508684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71716 ⟨1508684, by decide⟩ :=
  accepted_of_selected 10 71716 ⟨1508684, by decide⟩ ⟨10, 2, 0, 1508684, 71716, 1997, 1048576⟩
    (by decide) selected_cut_52048

theorem selected_cut_52049 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71717) = some ⟨10, 1, 0, 1468874, 71717, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71717_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71717 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71717 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71717, 1, 1048576⟩
    (by decide) selected_cut_52049

theorem selected_cut_52050 : selected 11 ⟨1508845, by decide⟩
    (prefixPartial 10 71718) = some ⟨10, 2, 0, 1508845, 71718, 2141, 1048576⟩ := by
  decide +kernel

theorem context_10_71718_1508845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71718 ⟨1508845, by decide⟩ :=
  accepted_of_selected 10 71718 ⟨1508845, by decide⟩ ⟨10, 2, 0, 1508845, 71718, 2141, 1048576⟩
    (by decide) selected_cut_52050

theorem selected_cut_52051 : selected 11 ⟨1508966, by decide⟩
    (prefixPartial 10 71719) = some ⟨10, 2, 0, 1508966, 71719, 1721, 1048576⟩ := by
  decide +kernel

theorem context_10_71719_1508966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71719 ⟨1508966, by decide⟩ :=
  accepted_of_selected 10 71719 ⟨1508966, by decide⟩ ⟨10, 2, 0, 1508966, 71719, 1721, 1048576⟩
    (by decide) selected_cut_52051

theorem unmarked_context_9_17929_1508967 : frontier 12 ⟨1508967, by decide⟩
    (prefixCache 9 17929) (prefixPartial 9 17929) = false := by
  decide +kernel

theorem node_context_9_17929_1508967 : EJMOriginalGlobalDAGData.nodes 12 ⟨1508967, by decide⟩ =
    .split (coordinate 9) (![⟨1508684, by decide⟩,⟨1468874, by decide⟩,⟨1508845, by decide⟩,⟨1508966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17929_1508967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17929 ⟨1508967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17929
    ⟨1508967, by decide⟩ (by decide) (![⟨1508684, by decide⟩,⟨1468874, by decide⟩,⟨1508845, by decide⟩,⟨1508966, by decide⟩]) unmarked_context_9_17929_1508967 node_context_9_17929_1508967
  intro a
  fin_cases a
  · exact context_10_71716_1508684
  · exact context_10_71717_1468874
  · exact context_10_71718_1508845
  · exact context_10_71719_1508966

theorem selected_cut_52052 : selected 12 ⟨1509081, by decide⟩
    (prefixPartial 9 17930) = some ⟨9, 2, 0, 1509081, 17930, 1429, 4194304⟩ := by
  decide +kernel

theorem context_9_17930_1509081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17930 ⟨1509081, by decide⟩ :=
  accepted_of_selected 9 17930 ⟨1509081, by decide⟩ ⟨9, 2, 0, 1509081, 17930, 1429, 4194304⟩
    (by decide) selected_cut_52052

theorem selected_cut_52053 : selected 12 ⟨1509102, by decide⟩
    (prefixPartial 9 17931) = some ⟨9, 2, 0, 1509102, 17931, 209, 4194304⟩ := by
  decide +kernel

theorem context_9_17931_1509102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17931 ⟨1509102, by decide⟩ :=
  accepted_of_selected 9 17931 ⟨1509102, by decide⟩ ⟨9, 2, 0, 1509102, 17931, 209, 4194304⟩
    (by decide) selected_cut_52053

theorem unmarked_context_8_4482_1509103 : frontier 13 ⟨1509103, by decide⟩
    (prefixCache 8 4482) (prefixPartial 8 4482) = false := by
  decide +kernel

theorem node_context_8_4482_1509103 : EJMOriginalGlobalDAGData.nodes 13 ⟨1509103, by decide⟩ =
    .split (coordinate 8) (![⟨1508542, by decide⟩,⟨1508967, by decide⟩,⟨1509081, by decide⟩,⟨1509102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4482_1509103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4482 ⟨1509103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4482
    ⟨1509103, by decide⟩ (by decide) (![⟨1508542, by decide⟩,⟨1508967, by decide⟩,⟨1509081, by decide⟩,⟨1509102, by decide⟩]) unmarked_context_8_4482_1509103 node_context_8_4482_1509103
  intro a
  fin_cases a
  · exact context_9_17928_1508542
  · exact context_9_17929_1508967
  · exact context_9_17930_1509081
  · exact context_9_17931_1509102

theorem selected_cut_52054 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71728) = some ⟨10, 1, 0, 1468246, 71728, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71728_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71728 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71728 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71728, 1, 1048576⟩
    (by decide) selected_cut_52054

theorem selected_cut_52055 : selected 10 ⟨1509317, by decide⟩
    (prefixPartial 11 286916) = some ⟨11, 2, 0, 1509317, 286916, 2993, 262144⟩ := by
  decide +kernel

theorem context_11_286916_1509317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286916 ⟨1509317, by decide⟩ :=
  accepted_of_selected 11 286916 ⟨1509317, by decide⟩ ⟨11, 2, 0, 1509317, 286916, 2993, 262144⟩
    (by decide) selected_cut_52055

theorem selected_cut_52056 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 286917) = some ⟨11, 1, 0, 1468419, 286917, 1, 262144⟩ := by
  decide +kernel

theorem context_11_286917_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286917 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 286917 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 286917, 1, 262144⟩
    (by decide) selected_cut_52056

theorem selected_cut_52057 : selected 10 ⟨1509462, by decide⟩
    (prefixPartial 11 286918) = some ⟨11, 2, 0, 1509462, 286918, 3505, 262144⟩ := by
  decide +kernel

theorem context_11_286918_1509462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286918 ⟨1509462, by decide⟩ :=
  accepted_of_selected 11 286918 ⟨1509462, by decide⟩ ⟨11, 2, 0, 1509462, 286918, 3505, 262144⟩
    (by decide) selected_cut_52057

theorem selected_cut_52058 : selected 10 ⟨1509614, by decide⟩
    (prefixPartial 11 286919) = some ⟨11, 2, 0, 1509614, 286919, 3277, 262144⟩ := by
  decide +kernel

theorem context_11_286919_1509614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286919 ⟨1509614, by decide⟩ :=
  accepted_of_selected 11 286919 ⟨1509614, by decide⟩ ⟨11, 2, 0, 1509614, 286919, 3277, 262144⟩
    (by decide) selected_cut_52058

theorem unmarked_context_10_71729_1509615 : frontier 11 ⟨1509615, by decide⟩
    (prefixCache 10 71729) (prefixPartial 10 71729) = false := by
  decide +kernel

theorem node_context_10_71729_1509615 : EJMOriginalGlobalDAGData.nodes 11 ⟨1509615, by decide⟩ =
    .split (coordinate 10) (![⟨1509317, by decide⟩,⟨1468419, by decide⟩,⟨1509462, by decide⟩,⟨1509614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71729_1509615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71729 ⟨1509615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71729
    ⟨1509615, by decide⟩ (by decide) (![⟨1509317, by decide⟩,⟨1468419, by decide⟩,⟨1509462, by decide⟩,⟨1509614, by decide⟩]) unmarked_context_10_71729_1509615 node_context_10_71729_1509615
  intro a
  fin_cases a
  · exact context_11_286916_1509317
  · exact context_11_286917_1468419
  · exact context_11_286918_1509462
  · exact context_11_286919_1509614

theorem selected_cut_52059 : selected 10 ⟨1509721, by decide⟩
    (prefixPartial 11 286920) = some ⟨11, 2, 0, 1509721, 286920, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_286920_1509721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286920 ⟨1509721, by decide⟩ :=
  accepted_of_selected 11 286920 ⟨1509721, by decide⟩ ⟨11, 2, 0, 1509721, 286920, 2361, 262144⟩
    (by decide) selected_cut_52059

theorem selected_cut_52060 : selected 10 ⟨1509768, by decide⟩
    (prefixPartial 11 286921) = some ⟨11, 2, 0, 1509768, 286921, 1053, 262144⟩ := by
  decide +kernel

theorem context_11_286921_1509768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286921 ⟨1509768, by decide⟩ :=
  accepted_of_selected 11 286921 ⟨1509768, by decide⟩ ⟨11, 2, 0, 1509768, 286921, 1053, 262144⟩
    (by decide) selected_cut_52060

theorem selected_cut_52061 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 286922) = some ⟨11, 1, 0, 1468743, 286922, 1, 262144⟩ := by
  decide +kernel

theorem context_11_286922_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286922 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 286922 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 286922, 1, 262144⟩
    (by decide) selected_cut_52061

theorem selected_cut_52062 : selected 10 ⟨1509818, by decide⟩
    (prefixPartial 11 286923) = some ⟨11, 2, 0, 1509818, 286923, 1161, 262144⟩ := by
  decide +kernel

theorem context_11_286923_1509818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 286923 ⟨1509818, by decide⟩ :=
  accepted_of_selected 11 286923 ⟨1509818, by decide⟩ ⟨11, 2, 0, 1509818, 286923, 1161, 262144⟩
    (by decide) selected_cut_52062

theorem unmarked_context_10_71730_1509819 : frontier 11 ⟨1509819, by decide⟩
    (prefixCache 10 71730) (prefixPartial 10 71730) = false := by
  decide +kernel

theorem node_context_10_71730_1509819 : EJMOriginalGlobalDAGData.nodes 11 ⟨1509819, by decide⟩ =
    .split (coordinate 10) (![⟨1509721, by decide⟩,⟨1509768, by decide⟩,⟨1468743, by decide⟩,⟨1509818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71730_1509819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71730 ⟨1509819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71730
    ⟨1509819, by decide⟩ (by decide) (![⟨1509721, by decide⟩,⟨1509768, by decide⟩,⟨1468743, by decide⟩,⟨1509818, by decide⟩]) unmarked_context_10_71730_1509819 node_context_10_71730_1509819
  intro a
  fin_cases a
  · exact context_11_286920_1509721
  · exact context_11_286921_1509768
  · exact context_11_286922_1468743
  · exact context_11_286923_1509818

theorem selected_cut_52063 : selected 11 ⟨1509991, by decide⟩
    (prefixPartial 10 71731) = some ⟨10, 2, 0, 1509991, 71731, 3809, 1048576⟩ := by
  decide +kernel

theorem context_10_71731_1509991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71731 ⟨1509991, by decide⟩ :=
  accepted_of_selected 10 71731 ⟨1509991, by decide⟩ ⟨10, 2, 0, 1509991, 71731, 3809, 1048576⟩
    (by decide) selected_cut_52063

theorem unmarked_context_9_17932_1509992 : frontier 12 ⟨1509992, by decide⟩
    (prefixCache 9 17932) (prefixPartial 9 17932) = false := by
  decide +kernel

theorem node_context_9_17932_1509992 : EJMOriginalGlobalDAGData.nodes 12 ⟨1509992, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1509615, by decide⟩,⟨1509819, by decide⟩,⟨1509991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17932_1509992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17932 ⟨1509992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17932
    ⟨1509992, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1509615, by decide⟩,⟨1509819, by decide⟩,⟨1509991, by decide⟩]) unmarked_context_9_17932_1509992 node_context_9_17932_1509992
  intro a
  fin_cases a
  · exact context_10_71728_1468246
  · exact context_10_71729_1509615
  · exact context_10_71730_1509819
  · exact context_10_71731_1509991

theorem selected_cut_52064 : selected 11 ⟨1510118, by decide⟩
    (prefixPartial 10 71732) = some ⟨10, 2, 0, 1510118, 71732, 1909, 1048576⟩ := by
  decide +kernel

theorem context_10_71732_1510118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71732 ⟨1510118, by decide⟩ :=
  accepted_of_selected 10 71732 ⟨1510118, by decide⟩ ⟨10, 2, 0, 1510118, 71732, 1909, 1048576⟩
    (by decide) selected_cut_52064

theorem selected_cut_52065 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71733) = some ⟨10, 1, 0, 1468874, 71733, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71733_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71733 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71733 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71733, 1, 1048576⟩
    (by decide) selected_cut_52065

theorem selected_cut_52066 : selected 11 ⟨1510265, by decide⟩
    (prefixPartial 10 71734) = some ⟨10, 2, 0, 1510265, 71734, 2573, 1048576⟩ := by
  decide +kernel

theorem context_10_71734_1510265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71734 ⟨1510265, by decide⟩ :=
  accepted_of_selected 10 71734 ⟨1510265, by decide⟩ ⟨10, 2, 0, 1510265, 71734, 2573, 1048576⟩
    (by decide) selected_cut_52066

theorem selected_cut_52067 : selected 11 ⟨1510304, by decide⟩
    (prefixPartial 10 71735) = some ⟨10, 2, 0, 1510304, 71735, 753, 1048576⟩ := by
  decide +kernel

theorem context_10_71735_1510304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71735 ⟨1510304, by decide⟩ :=
  accepted_of_selected 10 71735 ⟨1510304, by decide⟩ ⟨10, 2, 0, 1510304, 71735, 753, 1048576⟩
    (by decide) selected_cut_52067

theorem unmarked_context_9_17933_1510305 : frontier 12 ⟨1510305, by decide⟩
    (prefixCache 9 17933) (prefixPartial 9 17933) = false := by
  decide +kernel

theorem node_context_9_17933_1510305 : EJMOriginalGlobalDAGData.nodes 12 ⟨1510305, by decide⟩ =
    .split (coordinate 9) (![⟨1510118, by decide⟩,⟨1468874, by decide⟩,⟨1510265, by decide⟩,⟨1510304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17933_1510305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17933 ⟨1510305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17933
    ⟨1510305, by decide⟩ (by decide) (![⟨1510118, by decide⟩,⟨1468874, by decide⟩,⟨1510265, by decide⟩,⟨1510304, by decide⟩]) unmarked_context_9_17933_1510305 node_context_9_17933_1510305
  intro a
  fin_cases a
  · exact context_10_71732_1510118
  · exact context_10_71733_1468874
  · exact context_10_71734_1510265
  · exact context_10_71735_1510304

theorem selected_cut_52068 : selected 12 ⟨1510436, by decide⟩
    (prefixPartial 9 17934) = some ⟨9, 2, 0, 1510436, 17934, 1521, 4194304⟩ := by
  decide +kernel

theorem context_9_17934_1510436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17934 ⟨1510436, by decide⟩ :=
  accepted_of_selected 9 17934 ⟨1510436, by decide⟩ ⟨9, 2, 0, 1510436, 17934, 1521, 4194304⟩
    (by decide) selected_cut_52068

theorem selected_cut_52069 : selected 12 ⟨1510457, by decide⟩
    (prefixPartial 9 17935) = some ⟨9, 2, 0, 1510457, 17935, 213, 4194304⟩ := by
  decide +kernel

theorem context_9_17935_1510457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17935 ⟨1510457, by decide⟩ :=
  accepted_of_selected 9 17935 ⟨1510457, by decide⟩ ⟨9, 2, 0, 1510457, 17935, 213, 4194304⟩
    (by decide) selected_cut_52069

theorem unmarked_context_8_4483_1510458 : frontier 13 ⟨1510458, by decide⟩
    (prefixCache 8 4483) (prefixPartial 8 4483) = false := by
  decide +kernel

theorem node_context_8_4483_1510458 : EJMOriginalGlobalDAGData.nodes 13 ⟨1510458, by decide⟩ =
    .split (coordinate 8) (![⟨1509992, by decide⟩,⟨1510305, by decide⟩,⟨1510436, by decide⟩,⟨1510457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4483_1510458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4483 ⟨1510458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4483
    ⟨1510458, by decide⟩ (by decide) (![⟨1509992, by decide⟩,⟨1510305, by decide⟩,⟨1510436, by decide⟩,⟨1510457, by decide⟩]) unmarked_context_8_4483_1510458 node_context_8_4483_1510458
  intro a
  fin_cases a
  · exact context_9_17932_1509992
  · exact context_9_17933_1510305
  · exact context_9_17934_1510436
  · exact context_9_17935_1510457

theorem unmarked_context_7_1120_1510459 : frontier 14 ⟨1510459, by decide⟩
    (prefixCache 7 1120) (prefixPartial 7 1120) = false := by
  decide +kernel

theorem node_context_7_1120_1510459 : EJMOriginalGlobalDAGData.nodes 14 ⟨1510459, by decide⟩ =
    .split (coordinate 7) (![⟨1487329, by decide⟩,⟨1487329, by decide⟩,⟨1509103, by decide⟩,⟨1510458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1120_1510459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1120 ⟨1510459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1120
    ⟨1510459, by decide⟩ (by decide) (![⟨1487329, by decide⟩,⟨1487329, by decide⟩,⟨1509103, by decide⟩,⟨1510458, by decide⟩]) unmarked_context_7_1120_1510459 node_context_7_1120_1510459
  intro a
  fin_cases a
  · exact context_8_4480_1487329
  · exact context_8_4481_1487329
  · exact context_8_4482_1509103
  · exact context_8_4483_1510458

theorem selected_cut_52070 : selected 14 ⟨1510460, by decide⟩
    (prefixPartial 7 1121) = some ⟨7, 1, 0, 1510460, 1121, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_1121_1510460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1121 ⟨1510460, by decide⟩ :=
  accepted_of_selected 7 1121 ⟨1510460, by decide⟩ ⟨7, 1, 0, 1510460, 1121, 1, 67108864⟩
    (by decide) selected_cut_52070

theorem selected_cut_52071 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71808) = some ⟨10, 1, 0, 1468246, 71808, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71808_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71808 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71808 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71808, 1, 1048576⟩
    (by decide) selected_cut_52071

theorem selected_cut_52072 : selected 10 ⟨1510638, by decide⟩
    (prefixPartial 11 287236) = some ⟨11, 2, 0, 1510638, 287236, 2813, 262144⟩ := by
  decide +kernel

theorem context_11_287236_1510638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287236 ⟨1510638, by decide⟩ :=
  accepted_of_selected 11 287236 ⟨1510638, by decide⟩ ⟨11, 2, 0, 1510638, 287236, 2813, 262144⟩
    (by decide) selected_cut_52072

theorem selected_cut_52073 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287237) = some ⟨11, 1, 0, 1468419, 287237, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287237_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287237 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287237 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287237, 1, 262144⟩
    (by decide) selected_cut_52073

theorem selected_cut_52074 : selected 10 ⟨1510720, by decide⟩
    (prefixPartial 11 287238) = some ⟨11, 2, 0, 1510720, 287238, 2505, 262144⟩ := by
  decide +kernel

theorem context_11_287238_1510720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287238 ⟨1510720, by decide⟩ :=
  accepted_of_selected 11 287238 ⟨1510720, by decide⟩ ⟨11, 2, 0, 1510720, 287238, 2505, 262144⟩
    (by decide) selected_cut_52074

theorem selected_cut_52075 : selected 10 ⟨1510804, by decide⟩
    (prefixPartial 11 287239) = some ⟨11, 2, 0, 1510804, 287239, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_287239_1510804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287239 ⟨1510804, by decide⟩ :=
  accepted_of_selected 11 287239 ⟨1510804, by decide⟩ ⟨11, 2, 0, 1510804, 287239, 2489, 262144⟩
    (by decide) selected_cut_52075

theorem unmarked_context_10_71809_1510805 : frontier 11 ⟨1510805, by decide⟩
    (prefixCache 10 71809) (prefixPartial 10 71809) = false := by
  decide +kernel

theorem node_context_10_71809_1510805 : EJMOriginalGlobalDAGData.nodes 11 ⟨1510805, by decide⟩ =
    .split (coordinate 10) (![⟨1510638, by decide⟩,⟨1468419, by decide⟩,⟨1510720, by decide⟩,⟨1510804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71809_1510805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71809 ⟨1510805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71809
    ⟨1510805, by decide⟩ (by decide) (![⟨1510638, by decide⟩,⟨1468419, by decide⟩,⟨1510720, by decide⟩,⟨1510804, by decide⟩]) unmarked_context_10_71809_1510805 node_context_10_71809_1510805
  intro a
  fin_cases a
  · exact context_11_287236_1510638
  · exact context_11_287237_1468419
  · exact context_11_287238_1510720
  · exact context_11_287239_1510804

theorem selected_cut_52076 : selected 11 ⟨1510871, by decide⟩
    (prefixPartial 10 71810) = some ⟨10, 2, 0, 1510871, 71810, 1897, 1048576⟩ := by
  decide +kernel

theorem context_10_71810_1510871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71810 ⟨1510871, by decide⟩ :=
  accepted_of_selected 10 71810 ⟨1510871, by decide⟩ ⟨10, 2, 0, 1510871, 71810, 1897, 1048576⟩
    (by decide) selected_cut_52076

theorem selected_cut_52077 : selected 11 ⟨1511006, by decide⟩
    (prefixPartial 10 71811) = some ⟨10, 2, 0, 1511006, 71811, 3513, 1048576⟩ := by
  decide +kernel

theorem context_10_71811_1511006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71811 ⟨1511006, by decide⟩ :=
  accepted_of_selected 10 71811 ⟨1511006, by decide⟩ ⟨10, 2, 0, 1511006, 71811, 3513, 1048576⟩
    (by decide) selected_cut_52077

theorem unmarked_context_9_17952_1511007 : frontier 12 ⟨1511007, by decide⟩
    (prefixCache 9 17952) (prefixPartial 9 17952) = false := by
  decide +kernel

theorem node_context_9_17952_1511007 : EJMOriginalGlobalDAGData.nodes 12 ⟨1511007, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1510805, by decide⟩,⟨1510871, by decide⟩,⟨1511006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17952_1511007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17952 ⟨1511007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17952
    ⟨1511007, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1510805, by decide⟩,⟨1510871, by decide⟩,⟨1511006, by decide⟩]) unmarked_context_9_17952_1511007 node_context_9_17952_1511007
  intro a
  fin_cases a
  · exact context_10_71808_1468246
  · exact context_10_71809_1510805
  · exact context_10_71810_1510871
  · exact context_10_71811_1511006

theorem selected_cut_52078 : selected 11 ⟨1511134, by decide⟩
    (prefixPartial 10 71812) = some ⟨10, 2, 0, 1511134, 71812, 2485, 1048576⟩ := by
  decide +kernel

theorem context_10_71812_1511134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71812 ⟨1511134, by decide⟩ :=
  accepted_of_selected 10 71812 ⟨1511134, by decide⟩ ⟨10, 2, 0, 1511134, 71812, 2485, 1048576⟩
    (by decide) selected_cut_52078

theorem selected_cut_52079 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71813) = some ⟨10, 1, 0, 1468874, 71813, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71813_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71813 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71813 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71813, 1, 1048576⟩
    (by decide) selected_cut_52079

theorem selected_cut_52080 : selected 11 ⟨1511215, by decide⟩
    (prefixPartial 10 71814) = some ⟨10, 2, 0, 1511215, 71814, 1269, 1048576⟩ := by
  decide +kernel

theorem context_10_71814_1511215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71814 ⟨1511215, by decide⟩ :=
  accepted_of_selected 10 71814 ⟨1511215, by decide⟩ ⟨10, 2, 0, 1511215, 71814, 1269, 1048576⟩
    (by decide) selected_cut_52080

theorem selected_cut_52081 : selected 11 ⟨1511281, by decide⟩
    (prefixPartial 10 71815) = some ⟨10, 2, 0, 1511281, 71815, 889, 1048576⟩ := by
  decide +kernel

theorem context_10_71815_1511281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71815 ⟨1511281, by decide⟩ :=
  accepted_of_selected 10 71815 ⟨1511281, by decide⟩ ⟨10, 2, 0, 1511281, 71815, 889, 1048576⟩
    (by decide) selected_cut_52081

theorem unmarked_context_9_17953_1511282 : frontier 12 ⟨1511282, by decide⟩
    (prefixCache 9 17953) (prefixPartial 9 17953) = false := by
  decide +kernel

theorem node_context_9_17953_1511282 : EJMOriginalGlobalDAGData.nodes 12 ⟨1511282, by decide⟩ =
    .split (coordinate 9) (![⟨1511134, by decide⟩,⟨1468874, by decide⟩,⟨1511215, by decide⟩,⟨1511281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17953_1511282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17953 ⟨1511282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17953
    ⟨1511282, by decide⟩ (by decide) (![⟨1511134, by decide⟩,⟨1468874, by decide⟩,⟨1511215, by decide⟩,⟨1511281, by decide⟩]) unmarked_context_9_17953_1511282 node_context_9_17953_1511282
  intro a
  fin_cases a
  · exact context_10_71812_1511134
  · exact context_10_71813_1468874
  · exact context_10_71814_1511215
  · exact context_10_71815_1511281

theorem selected_cut_52082 : selected 12 ⟨1511384, by decide⟩
    (prefixPartial 9 17954) = some ⟨9, 2, 0, 1511384, 17954, 977, 4194304⟩ := by
  decide +kernel

theorem context_9_17954_1511384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17954 ⟨1511384, by decide⟩ :=
  accepted_of_selected 9 17954 ⟨1511384, by decide⟩ ⟨9, 2, 0, 1511384, 17954, 977, 4194304⟩
    (by decide) selected_cut_52082

theorem selected_cut_52083 : selected 12 ⟨1511435, by decide⟩
    (prefixPartial 9 17955) = some ⟨9, 2, 0, 1511435, 17955, 441, 4194304⟩ := by
  decide +kernel

theorem context_9_17955_1511435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17955 ⟨1511435, by decide⟩ :=
  accepted_of_selected 9 17955 ⟨1511435, by decide⟩ ⟨9, 2, 0, 1511435, 17955, 441, 4194304⟩
    (by decide) selected_cut_52083

theorem unmarked_context_8_4488_1511436 : frontier 13 ⟨1511436, by decide⟩
    (prefixCache 8 4488) (prefixPartial 8 4488) = false := by
  decide +kernel

theorem node_context_8_4488_1511436 : EJMOriginalGlobalDAGData.nodes 13 ⟨1511436, by decide⟩ =
    .split (coordinate 8) (![⟨1511007, by decide⟩,⟨1511282, by decide⟩,⟨1511384, by decide⟩,⟨1511435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4488_1511436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4488 ⟨1511436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4488
    ⟨1511436, by decide⟩ (by decide) (![⟨1511007, by decide⟩,⟨1511282, by decide⟩,⟨1511384, by decide⟩,⟨1511435, by decide⟩]) unmarked_context_8_4488_1511436 node_context_8_4488_1511436
  intro a
  fin_cases a
  · exact context_9_17952_1511007
  · exact context_9_17953_1511282
  · exact context_9_17954_1511384
  · exact context_9_17955_1511435

theorem selected_cut_52084 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71824) = some ⟨10, 1, 0, 1468246, 71824, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71824_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71824 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71824 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71824, 1, 1048576⟩
    (by decide) selected_cut_52084

theorem selected_cut_52085 : selected 10 ⟨1511567, by decide⟩
    (prefixPartial 11 287300) = some ⟨11, 2, 0, 1511567, 287300, 3853, 262144⟩ := by
  decide +kernel

theorem context_11_287300_1511567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287300 ⟨1511567, by decide⟩ :=
  accepted_of_selected 11 287300 ⟨1511567, by decide⟩ ⟨11, 2, 0, 1511567, 287300, 3853, 262144⟩
    (by decide) selected_cut_52085

theorem selected_cut_52086 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287301) = some ⟨11, 1, 0, 1468419, 287301, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287301_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287301 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287301 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287301, 1, 262144⟩
    (by decide) selected_cut_52086

theorem selected_cut_52087 : selected 10 ⟨1511604, by decide⟩
    (prefixPartial 11 287302) = some ⟨11, 2, 0, 1511604, 287302, 1297, 262144⟩ := by
  decide +kernel

theorem context_11_287302_1511604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287302 ⟨1511604, by decide⟩ :=
  accepted_of_selected 11 287302 ⟨1511604, by decide⟩ ⟨11, 2, 0, 1511604, 287302, 1297, 262144⟩
    (by decide) selected_cut_52087

theorem selected_cut_52088 : selected 10 ⟨1511671, by decide⟩
    (prefixPartial 11 287303) = some ⟨11, 2, 0, 1511671, 287303, 2681, 262144⟩ := by
  decide +kernel

theorem context_11_287303_1511671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287303 ⟨1511671, by decide⟩ :=
  accepted_of_selected 11 287303 ⟨1511671, by decide⟩ ⟨11, 2, 0, 1511671, 287303, 2681, 262144⟩
    (by decide) selected_cut_52088

theorem unmarked_context_10_71825_1511672 : frontier 11 ⟨1511672, by decide⟩
    (prefixCache 10 71825) (prefixPartial 10 71825) = false := by
  decide +kernel

theorem node_context_10_71825_1511672 : EJMOriginalGlobalDAGData.nodes 11 ⟨1511672, by decide⟩ =
    .split (coordinate 10) (![⟨1511567, by decide⟩,⟨1468419, by decide⟩,⟨1511604, by decide⟩,⟨1511671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71825_1511672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71825 ⟨1511672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71825
    ⟨1511672, by decide⟩ (by decide) (![⟨1511567, by decide⟩,⟨1468419, by decide⟩,⟨1511604, by decide⟩,⟨1511671, by decide⟩]) unmarked_context_10_71825_1511672 node_context_10_71825_1511672
  intro a
  fin_cases a
  · exact context_11_287300_1511567
  · exact context_11_287301_1468419
  · exact context_11_287302_1511604
  · exact context_11_287303_1511671

theorem selected_cut_52089 : selected 11 ⟨1511742, by decide⟩
    (prefixPartial 10 71826) = some ⟨10, 2, 0, 1511742, 71826, 2145, 1048576⟩ := by
  decide +kernel

theorem context_10_71826_1511742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71826 ⟨1511742, by decide⟩ :=
  accepted_of_selected 10 71826 ⟨1511742, by decide⟩ ⟨10, 2, 0, 1511742, 71826, 2145, 1048576⟩
    (by decide) selected_cut_52089

theorem selected_cut_52090 : selected 10 ⟨1511818, by decide⟩
    (prefixPartial 11 287308) = some ⟨11, 2, 0, 1511818, 287308, 2245, 262144⟩ := by
  decide +kernel

theorem context_11_287308_1511818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287308 ⟨1511818, by decide⟩ :=
  accepted_of_selected 11 287308 ⟨1511818, by decide⟩ ⟨11, 2, 0, 1511818, 287308, 2245, 262144⟩
    (by decide) selected_cut_52090

theorem selected_cut_52091 : selected 10 ⟨1511885, by decide⟩
    (prefixPartial 11 287309) = some ⟨11, 2, 0, 1511885, 287309, 1937, 262144⟩ := by
  decide +kernel

theorem context_11_287309_1511885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287309 ⟨1511885, by decide⟩ :=
  accepted_of_selected 11 287309 ⟨1511885, by decide⟩ ⟨11, 2, 0, 1511885, 287309, 1937, 262144⟩
    (by decide) selected_cut_52091

theorem selected_cut_52092 : selected 10 ⟨1511920, by decide⟩
    (prefixPartial 11 287310) = some ⟨11, 2, 0, 1511920, 287310, 1037, 262144⟩ := by
  decide +kernel

theorem context_11_287310_1511920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287310 ⟨1511920, by decide⟩ :=
  accepted_of_selected 11 287310 ⟨1511920, by decide⟩ ⟨11, 2, 0, 1511920, 287310, 1037, 262144⟩
    (by decide) selected_cut_52092

theorem selected_cut_52093 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 287311) = some ⟨11, 1, 0, 1470044, 287311, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287311_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287311 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 287311 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 287311, 1, 262144⟩
    (by decide) selected_cut_52093

theorem unmarked_context_10_71827_1511921 : frontier 11 ⟨1511921, by decide⟩
    (prefixCache 10 71827) (prefixPartial 10 71827) = false := by
  decide +kernel

theorem node_context_10_71827_1511921 : EJMOriginalGlobalDAGData.nodes 11 ⟨1511921, by decide⟩ =
    .split (coordinate 10) (![⟨1511818, by decide⟩,⟨1511885, by decide⟩,⟨1511920, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71827_1511921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71827 ⟨1511921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71827
    ⟨1511921, by decide⟩ (by decide) (![⟨1511818, by decide⟩,⟨1511885, by decide⟩,⟨1511920, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71827_1511921 node_context_10_71827_1511921
  intro a
  fin_cases a
  · exact context_11_287308_1511818
  · exact context_11_287309_1511885
  · exact context_11_287310_1511920
  · exact context_11_287311_1470044

theorem unmarked_context_9_17956_1511922 : frontier 12 ⟨1511922, by decide⟩
    (prefixCache 9 17956) (prefixPartial 9 17956) = false := by
  decide +kernel

theorem node_context_9_17956_1511922 : EJMOriginalGlobalDAGData.nodes 12 ⟨1511922, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1511672, by decide⟩,⟨1511742, by decide⟩,⟨1511921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17956_1511922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17956 ⟨1511922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17956
    ⟨1511922, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1511672, by decide⟩,⟨1511742, by decide⟩,⟨1511921, by decide⟩]) unmarked_context_9_17956_1511922 node_context_9_17956_1511922
  intro a
  fin_cases a
  · exact context_10_71824_1468246
  · exact context_10_71825_1511672
  · exact context_10_71826_1511742
  · exact context_10_71827_1511921

theorem selected_cut_52094 : selected 11 ⟨1512083, by decide⟩
    (prefixPartial 10 71828) = some ⟨10, 2, 0, 1512083, 71828, 3605, 1048576⟩ := by
  decide +kernel

theorem context_10_71828_1512083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71828 ⟨1512083, by decide⟩ :=
  accepted_of_selected 10 71828 ⟨1512083, by decide⟩ ⟨10, 2, 0, 1512083, 71828, 3605, 1048576⟩
    (by decide) selected_cut_52094

theorem selected_cut_52095 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71829) = some ⟨10, 1, 0, 1468874, 71829, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71829_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71829 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71829 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71829, 1, 1048576⟩
    (by decide) selected_cut_52095

theorem selected_cut_52096 : selected 11 ⟨1512193, by decide⟩
    (prefixPartial 10 71830) = some ⟨10, 2, 0, 1512193, 71830, 2585, 1048576⟩ := by
  decide +kernel

theorem context_10_71830_1512193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71830 ⟨1512193, by decide⟩ :=
  accepted_of_selected 10 71830 ⟨1512193, by decide⟩ ⟨10, 2, 0, 1512193, 71830, 2585, 1048576⟩
    (by decide) selected_cut_52096

theorem selected_cut_52097 : selected 11 ⟨1512280, by decide⟩
    (prefixPartial 10 71831) = some ⟨10, 2, 0, 1512280, 71831, 1561, 1048576⟩ := by
  decide +kernel

theorem context_10_71831_1512280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71831 ⟨1512280, by decide⟩ :=
  accepted_of_selected 10 71831 ⟨1512280, by decide⟩ ⟨10, 2, 0, 1512280, 71831, 1561, 1048576⟩
    (by decide) selected_cut_52097

theorem unmarked_context_9_17957_1512281 : frontier 12 ⟨1512281, by decide⟩
    (prefixCache 9 17957) (prefixPartial 9 17957) = false := by
  decide +kernel

theorem node_context_9_17957_1512281 : EJMOriginalGlobalDAGData.nodes 12 ⟨1512281, by decide⟩ =
    .split (coordinate 9) (![⟨1512083, by decide⟩,⟨1468874, by decide⟩,⟨1512193, by decide⟩,⟨1512280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17957_1512281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17957 ⟨1512281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17957
    ⟨1512281, by decide⟩ (by decide) (![⟨1512083, by decide⟩,⟨1468874, by decide⟩,⟨1512193, by decide⟩,⟨1512280, by decide⟩]) unmarked_context_9_17957_1512281 node_context_9_17957_1512281
  intro a
  fin_cases a
  · exact context_10_71828_1512083
  · exact context_10_71829_1468874
  · exact context_10_71830_1512193
  · exact context_10_71831_1512280

theorem selected_cut_52098 : selected 12 ⟨1512356, by decide⟩
    (prefixPartial 9 17958) = some ⟨9, 2, 0, 1512356, 17958, 1093, 4194304⟩ := by
  decide +kernel

theorem context_9_17958_1512356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17958 ⟨1512356, by decide⟩ :=
  accepted_of_selected 9 17958 ⟨1512356, by decide⟩ ⟨9, 2, 0, 1512356, 17958, 1093, 4194304⟩
    (by decide) selected_cut_52098

theorem selected_cut_52099 : selected 12 ⟨1512362, by decide⟩
    (prefixPartial 9 17959) = some ⟨9, 2, 0, 1512362, 17959, 53, 4194304⟩ := by
  decide +kernel

theorem context_9_17959_1512362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17959 ⟨1512362, by decide⟩ :=
  accepted_of_selected 9 17959 ⟨1512362, by decide⟩ ⟨9, 2, 0, 1512362, 17959, 53, 4194304⟩
    (by decide) selected_cut_52099

theorem unmarked_context_8_4489_1512363 : frontier 13 ⟨1512363, by decide⟩
    (prefixCache 8 4489) (prefixPartial 8 4489) = false := by
  decide +kernel

theorem node_context_8_4489_1512363 : EJMOriginalGlobalDAGData.nodes 13 ⟨1512363, by decide⟩ =
    .split (coordinate 8) (![⟨1511922, by decide⟩,⟨1512281, by decide⟩,⟨1512356, by decide⟩,⟨1512362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4489_1512363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4489 ⟨1512363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4489
    ⟨1512363, by decide⟩ (by decide) (![⟨1511922, by decide⟩,⟨1512281, by decide⟩,⟨1512356, by decide⟩,⟨1512362, by decide⟩]) unmarked_context_8_4489_1512363 node_context_8_4489_1512363
  intro a
  fin_cases a
  · exact context_9_17956_1511922
  · exact context_9_17957_1512281
  · exact context_9_17958_1512356
  · exact context_9_17959_1512362

theorem selected_cut_52100 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71840) = some ⟨10, 1, 0, 1468246, 71840, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71840_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71840 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71840 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71840, 1, 1048576⟩
    (by decide) selected_cut_52100

theorem selected_cut_52101 : selected 10 ⟨1512520, by decide⟩
    (prefixPartial 11 287364) = some ⟨11, 2, 0, 1512520, 287364, 3805, 262144⟩ := by
  decide +kernel

theorem context_11_287364_1512520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287364 ⟨1512520, by decide⟩ :=
  accepted_of_selected 11 287364 ⟨1512520, by decide⟩ ⟨11, 2, 0, 1512520, 287364, 3805, 262144⟩
    (by decide) selected_cut_52101

theorem selected_cut_52102 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287365) = some ⟨11, 1, 0, 1468419, 287365, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287365_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287365 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287365 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287365, 1, 262144⟩
    (by decide) selected_cut_52102

theorem selected_cut_52103 : selected 10 ⟨1512557, by decide⟩
    (prefixPartial 11 287366) = some ⟨11, 2, 0, 1512557, 287366, 1441, 262144⟩ := by
  decide +kernel

theorem context_11_287366_1512557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287366 ⟨1512557, by decide⟩ :=
  accepted_of_selected 11 287366 ⟨1512557, by decide⟩ ⟨11, 2, 0, 1512557, 287366, 1441, 262144⟩
    (by decide) selected_cut_52103

theorem selected_cut_52104 : selected 10 ⟨1512674, by decide⟩
    (prefixPartial 11 287367) = some ⟨11, 2, 0, 1512674, 287367, 3185, 262144⟩ := by
  decide +kernel

theorem context_11_287367_1512674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287367 ⟨1512674, by decide⟩ :=
  accepted_of_selected 11 287367 ⟨1512674, by decide⟩ ⟨11, 2, 0, 1512674, 287367, 3185, 262144⟩
    (by decide) selected_cut_52104

theorem unmarked_context_10_71841_1512675 : frontier 11 ⟨1512675, by decide⟩
    (prefixCache 10 71841) (prefixPartial 10 71841) = false := by
  decide +kernel

theorem node_context_10_71841_1512675 : EJMOriginalGlobalDAGData.nodes 11 ⟨1512675, by decide⟩ =
    .split (coordinate 10) (![⟨1512520, by decide⟩,⟨1468419, by decide⟩,⟨1512557, by decide⟩,⟨1512674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71841_1512675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71841 ⟨1512675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71841
    ⟨1512675, by decide⟩ (by decide) (![⟨1512520, by decide⟩,⟨1468419, by decide⟩,⟨1512557, by decide⟩,⟨1512674, by decide⟩]) unmarked_context_10_71841_1512675 node_context_10_71841_1512675
  intro a
  fin_cases a
  · exact context_11_287364_1512520
  · exact context_11_287365_1468419
  · exact context_11_287366_1512557
  · exact context_11_287367_1512674

theorem selected_cut_52105 : selected 11 ⟨1512737, by decide⟩
    (prefixPartial 10 71842) = some ⟨10, 2, 0, 1512737, 71842, 2185, 1048576⟩ := by
  decide +kernel

theorem context_10_71842_1512737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71842 ⟨1512737, by decide⟩ :=
  accepted_of_selected 10 71842 ⟨1512737, by decide⟩ ⟨10, 2, 0, 1512737, 71842, 2185, 1048576⟩
    (by decide) selected_cut_52105

theorem selected_cut_52106 : selected 10 ⟨1512821, by decide⟩
    (prefixPartial 11 287372) = some ⟨11, 2, 0, 1512821, 287372, 1957, 262144⟩ := by
  decide +kernel

theorem context_11_287372_1512821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287372 ⟨1512821, by decide⟩ :=
  accepted_of_selected 11 287372 ⟨1512821, by decide⟩ ⟨11, 2, 0, 1512821, 287372, 1957, 262144⟩
    (by decide) selected_cut_52106

theorem selected_cut_52107 : selected 10 ⟨1512882, by decide⟩
    (prefixPartial 11 287373) = some ⟨11, 2, 0, 1512882, 287373, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_287373_1512882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287373 ⟨1512882, by decide⟩ :=
  accepted_of_selected 11 287373 ⟨1512882, by decide⟩ ⟨11, 2, 0, 1512882, 287373, 2157, 262144⟩
    (by decide) selected_cut_52107

theorem selected_cut_52108 : selected 10 ⟨1512911, by decide⟩
    (prefixPartial 11 287374) = some ⟨11, 2, 0, 1512911, 287374, 1057, 262144⟩ := by
  decide +kernel

theorem context_11_287374_1512911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287374 ⟨1512911, by decide⟩ :=
  accepted_of_selected 11 287374 ⟨1512911, by decide⟩ ⟨11, 2, 0, 1512911, 287374, 1057, 262144⟩
    (by decide) selected_cut_52108

theorem selected_cut_52109 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 287375) = some ⟨11, 1, 0, 1470044, 287375, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287375_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287375 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 287375 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 287375, 1, 262144⟩
    (by decide) selected_cut_52109

theorem unmarked_context_10_71843_1512912 : frontier 11 ⟨1512912, by decide⟩
    (prefixCache 10 71843) (prefixPartial 10 71843) = false := by
  decide +kernel

theorem node_context_10_71843_1512912 : EJMOriginalGlobalDAGData.nodes 11 ⟨1512912, by decide⟩ =
    .split (coordinate 10) (![⟨1512821, by decide⟩,⟨1512882, by decide⟩,⟨1512911, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71843_1512912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71843 ⟨1512912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71843
    ⟨1512912, by decide⟩ (by decide) (![⟨1512821, by decide⟩,⟨1512882, by decide⟩,⟨1512911, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71843_1512912 node_context_10_71843_1512912
  intro a
  fin_cases a
  · exact context_11_287372_1512821
  · exact context_11_287373_1512882
  · exact context_11_287374_1512911
  · exact context_11_287375_1470044

theorem unmarked_context_9_17960_1512913 : frontier 12 ⟨1512913, by decide⟩
    (prefixCache 9 17960) (prefixPartial 9 17960) = false := by
  decide +kernel

theorem node_context_9_17960_1512913 : EJMOriginalGlobalDAGData.nodes 12 ⟨1512913, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1512675, by decide⟩,⟨1512737, by decide⟩,⟨1512912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17960_1512913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17960 ⟨1512913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17960
    ⟨1512913, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1512675, by decide⟩,⟨1512737, by decide⟩,⟨1512912, by decide⟩]) unmarked_context_9_17960_1512913 node_context_9_17960_1512913
  intro a
  fin_cases a
  · exact context_10_71840_1468246
  · exact context_10_71841_1512675
  · exact context_10_71842_1512737
  · exact context_10_71843_1512912

theorem selected_cut_52110 : selected 11 ⟨1513050, by decide⟩
    (prefixPartial 10 71844) = some ⟨10, 2, 0, 1513050, 71844, 4017, 1048576⟩ := by
  decide +kernel

theorem context_10_71844_1513050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71844 ⟨1513050, by decide⟩ :=
  accepted_of_selected 10 71844 ⟨1513050, by decide⟩ ⟨10, 2, 0, 1513050, 71844, 4017, 1048576⟩
    (by decide) selected_cut_52110

theorem selected_cut_52111 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71845) = some ⟨10, 1, 0, 1468874, 71845, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71845_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71845 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71845 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71845, 1, 1048576⟩
    (by decide) selected_cut_52111

theorem selected_cut_52112 : selected 10 ⟨1513096, by decide⟩
    (prefixPartial 11 287384) = some ⟨11, 2, 0, 1513096, 287384, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_287384_1513096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287384 ⟨1513096, by decide⟩ :=
  accepted_of_selected 11 287384 ⟨1513096, by decide⟩ ⟨11, 2, 0, 1513096, 287384, 1489, 262144⟩
    (by decide) selected_cut_52112

theorem selected_cut_52113 : selected 10 ⟨1513125, by decide⟩
    (prefixPartial 11 287385) = some ⟨11, 2, 0, 1513125, 287385, 1337, 262144⟩ := by
  decide +kernel

theorem context_11_287385_1513125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287385 ⟨1513125, by decide⟩ :=
  accepted_of_selected 11 287385 ⟨1513125, by decide⟩ ⟨11, 2, 0, 1513125, 287385, 1337, 262144⟩
    (by decide) selected_cut_52113

theorem selected_cut_52114 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 287386) = some ⟨11, 1, 0, 1468743, 287386, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287386_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287386 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 287386 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 287386, 1, 262144⟩
    (by decide) selected_cut_52114

theorem selected_cut_52115 : selected 10 ⟨1513161, by decide⟩
    (prefixPartial 11 287387) = some ⟨11, 2, 0, 1513161, 287387, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_287387_1513161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287387 ⟨1513161, by decide⟩ :=
  accepted_of_selected 11 287387 ⟨1513161, by decide⟩ ⟨11, 2, 0, 1513161, 287387, 1289, 262144⟩
    (by decide) selected_cut_52115

theorem unmarked_context_10_71846_1513162 : frontier 11 ⟨1513162, by decide⟩
    (prefixCache 10 71846) (prefixPartial 10 71846) = false := by
  decide +kernel

theorem node_context_10_71846_1513162 : EJMOriginalGlobalDAGData.nodes 11 ⟨1513162, by decide⟩ =
    .split (coordinate 10) (![⟨1513096, by decide⟩,⟨1513125, by decide⟩,⟨1468743, by decide⟩,⟨1513161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71846_1513162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71846 ⟨1513162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71846
    ⟨1513162, by decide⟩ (by decide) (![⟨1513096, by decide⟩,⟨1513125, by decide⟩,⟨1468743, by decide⟩,⟨1513161, by decide⟩]) unmarked_context_10_71846_1513162 node_context_10_71846_1513162
  intro a
  fin_cases a
  · exact context_11_287384_1513096
  · exact context_11_287385_1513125
  · exact context_11_287386_1468743
  · exact context_11_287387_1513161

theorem selected_cut_52116 : selected 11 ⟨1513261, by decide⟩
    (prefixPartial 10 71847) = some ⟨10, 2, 0, 1513261, 71847, 3381, 1048576⟩ := by
  decide +kernel

theorem context_10_71847_1513261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71847 ⟨1513261, by decide⟩ :=
  accepted_of_selected 10 71847 ⟨1513261, by decide⟩ ⟨10, 2, 0, 1513261, 71847, 3381, 1048576⟩
    (by decide) selected_cut_52116

theorem unmarked_context_9_17961_1513262 : frontier 12 ⟨1513262, by decide⟩
    (prefixCache 9 17961) (prefixPartial 9 17961) = false := by
  decide +kernel

theorem node_context_9_17961_1513262 : EJMOriginalGlobalDAGData.nodes 12 ⟨1513262, by decide⟩ =
    .split (coordinate 9) (![⟨1513050, by decide⟩,⟨1468874, by decide⟩,⟨1513162, by decide⟩,⟨1513261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17961_1513262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17961 ⟨1513262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17961
    ⟨1513262, by decide⟩ (by decide) (![⟨1513050, by decide⟩,⟨1468874, by decide⟩,⟨1513162, by decide⟩,⟨1513261, by decide⟩]) unmarked_context_9_17961_1513262 node_context_9_17961_1513262
  intro a
  fin_cases a
  · exact context_10_71844_1513050
  · exact context_10_71845_1468874
  · exact context_10_71846_1513162
  · exact context_10_71847_1513261

theorem selected_cut_52117 : selected 11 ⟨1513290, by decide⟩
    (prefixPartial 10 71848) = some ⟨10, 2, 0, 1513290, 71848, 993, 1048576⟩ := by
  decide +kernel

theorem context_10_71848_1513290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71848 ⟨1513290, by decide⟩ :=
  accepted_of_selected 10 71848 ⟨1513290, by decide⟩ ⟨10, 2, 0, 1513290, 71848, 993, 1048576⟩
    (by decide) selected_cut_52117

theorem selected_cut_52118 : selected 11 ⟨1513357, by decide⟩
    (prefixPartial 10 71849) = some ⟨10, 2, 0, 1513357, 71849, 2585, 1048576⟩ := by
  decide +kernel

theorem context_10_71849_1513357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71849 ⟨1513357, by decide⟩ :=
  accepted_of_selected 10 71849 ⟨1513357, by decide⟩ ⟨10, 2, 0, 1513357, 71849, 2585, 1048576⟩
    (by decide) selected_cut_52118

theorem selected_cut_52119 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71850) = some ⟨10, 1, 0, 1469103, 71850, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71850_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71850 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71850 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71850, 1, 1048576⟩
    (by decide) selected_cut_52119

theorem selected_cut_52120 : selected 11 ⟨1513395, by decide⟩
    (prefixPartial 10 71851) = some ⟨10, 2, 0, 1513395, 71851, 1673, 1048576⟩ := by
  decide +kernel

theorem context_10_71851_1513395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71851 ⟨1513395, by decide⟩ :=
  accepted_of_selected 10 71851 ⟨1513395, by decide⟩ ⟨10, 2, 0, 1513395, 71851, 1673, 1048576⟩
    (by decide) selected_cut_52120

theorem unmarked_context_9_17962_1513396 : frontier 12 ⟨1513396, by decide⟩
    (prefixCache 9 17962) (prefixPartial 9 17962) = false := by
  decide +kernel

theorem node_context_9_17962_1513396 : EJMOriginalGlobalDAGData.nodes 12 ⟨1513396, by decide⟩ =
    .split (coordinate 9) (![⟨1513290, by decide⟩,⟨1513357, by decide⟩,⟨1469103, by decide⟩,⟨1513395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17962_1513396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17962 ⟨1513396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17962
    ⟨1513396, by decide⟩ (by decide) (![⟨1513290, by decide⟩,⟨1513357, by decide⟩,⟨1469103, by decide⟩,⟨1513395, by decide⟩]) unmarked_context_9_17962_1513396 node_context_9_17962_1513396
  intro a
  fin_cases a
  · exact context_10_71848_1513290
  · exact context_10_71849_1513357
  · exact context_10_71850_1469103
  · exact context_10_71851_1513395

theorem selected_cut_52121 : selected 12 ⟨1513479, by decide⟩
    (prefixPartial 9 17963) = some ⟨9, 2, 0, 1513479, 17963, 2009, 4194304⟩ := by
  decide +kernel

theorem context_9_17963_1513479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17963 ⟨1513479, by decide⟩ :=
  accepted_of_selected 9 17963 ⟨1513479, by decide⟩ ⟨9, 2, 0, 1513479, 17963, 2009, 4194304⟩
    (by decide) selected_cut_52121

theorem unmarked_context_8_4490_1513480 : frontier 13 ⟨1513480, by decide⟩
    (prefixCache 8 4490) (prefixPartial 8 4490) = false := by
  decide +kernel

theorem node_context_8_4490_1513480 : EJMOriginalGlobalDAGData.nodes 13 ⟨1513480, by decide⟩ =
    .split (coordinate 8) (![⟨1512913, by decide⟩,⟨1513262, by decide⟩,⟨1513396, by decide⟩,⟨1513479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4490_1513480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4490 ⟨1513480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4490
    ⟨1513480, by decide⟩ (by decide) (![⟨1512913, by decide⟩,⟨1513262, by decide⟩,⟨1513396, by decide⟩,⟨1513479, by decide⟩]) unmarked_context_8_4490_1513480 node_context_8_4490_1513480
  intro a
  fin_cases a
  · exact context_9_17960_1512913
  · exact context_9_17961_1513262
  · exact context_9_17962_1513396
  · exact context_9_17963_1513479

theorem selected_cut_52122 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71856) = some ⟨10, 1, 0, 1468246, 71856, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71856_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71856 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71856 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71856, 1, 1048576⟩
    (by decide) selected_cut_52122

theorem selected_cut_52123 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 1149712) = some ⟨12, 1, 0, 448748, 1149712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1149712_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1149712 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 1149712 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 1149712, 1, 65536⟩
    (by decide) selected_cut_52123

theorem selected_cut_52124 : selected 9 ⟨1513584, by decide⟩
    (prefixPartial 12 1149713) = some ⟨12, 2, 0, 1513584, 1149713, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_1149713_1513584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1149713 ⟨1513584, by decide⟩ :=
  accepted_of_selected 12 1149713 ⟨1513584, by decide⟩ ⟨12, 2, 0, 1513584, 1149713, 2325, 65536⟩
    (by decide) selected_cut_52124

theorem selected_cut_52125 : selected 9 ⟨1513645, by decide⟩
    (prefixPartial 12 1149714) = some ⟨12, 2, 0, 1513645, 1149714, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_1149714_1513645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1149714 ⟨1513645, by decide⟩ :=
  accepted_of_selected 12 1149714 ⟨1513645, by decide⟩ ⟨12, 2, 0, 1513645, 1149714, 1905, 65536⟩
    (by decide) selected_cut_52125

theorem selected_cut_52126 : selected 9 ⟨1513688, by decide⟩
    (prefixPartial 12 1149715) = some ⟨12, 2, 0, 1513688, 1149715, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_1149715_1513688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1149715 ⟨1513688, by decide⟩ :=
  accepted_of_selected 12 1149715 ⟨1513688, by decide⟩ ⟨12, 2, 0, 1513688, 1149715, 1689, 65536⟩
    (by decide) selected_cut_52126

theorem unmarked_context_11_287428_1513689 : frontier 10 ⟨1513689, by decide⟩
    (prefixCache 11 287428) (prefixPartial 11 287428) = false := by
  decide +kernel

theorem node_context_11_287428_1513689 : EJMOriginalGlobalDAGData.nodes 10 ⟨1513689, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1513584, by decide⟩,⟨1513645, by decide⟩,⟨1513688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_287428_1513689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287428 ⟨1513689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 287428
    ⟨1513689, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1513584, by decide⟩,⟨1513645, by decide⟩,⟨1513688, by decide⟩]) unmarked_context_11_287428_1513689 node_context_11_287428_1513689
  intro a
  fin_cases a
  · exact context_12_1149712_448748
  · exact context_12_1149713_1513584
  · exact context_12_1149714_1513645
  · exact context_12_1149715_1513688

theorem selected_cut_52127 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287429) = some ⟨11, 1, 0, 1468419, 287429, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287429_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287429 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287429 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287429, 1, 262144⟩
    (by decide) selected_cut_52127

theorem selected_cut_52128 : selected 10 ⟨1513777, by decide⟩
    (prefixPartial 11 287430) = some ⟨11, 2, 0, 1513777, 287430, 3209, 262144⟩ := by
  decide +kernel

theorem context_11_287430_1513777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287430 ⟨1513777, by decide⟩ :=
  accepted_of_selected 11 287430 ⟨1513777, by decide⟩ ⟨11, 2, 0, 1513777, 287430, 3209, 262144⟩
    (by decide) selected_cut_52128

theorem selected_cut_52129 : selected 10 ⟨1513877, by decide⟩
    (prefixPartial 11 287431) = some ⟨11, 2, 0, 1513877, 287431, 3289, 262144⟩ := by
  decide +kernel

theorem context_11_287431_1513877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287431 ⟨1513877, by decide⟩ :=
  accepted_of_selected 11 287431 ⟨1513877, by decide⟩ ⟨11, 2, 0, 1513877, 287431, 3289, 262144⟩
    (by decide) selected_cut_52129

theorem unmarked_context_10_71857_1513878 : frontier 11 ⟨1513878, by decide⟩
    (prefixCache 10 71857) (prefixPartial 10 71857) = false := by
  decide +kernel

theorem node_context_10_71857_1513878 : EJMOriginalGlobalDAGData.nodes 11 ⟨1513878, by decide⟩ =
    .split (coordinate 10) (![⟨1513689, by decide⟩,⟨1468419, by decide⟩,⟨1513777, by decide⟩,⟨1513877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71857_1513878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71857 ⟨1513878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71857
    ⟨1513878, by decide⟩ (by decide) (![⟨1513689, by decide⟩,⟨1468419, by decide⟩,⟨1513777, by decide⟩,⟨1513877, by decide⟩]) unmarked_context_10_71857_1513878 node_context_10_71857_1513878
  intro a
  fin_cases a
  · exact context_11_287428_1513689
  · exact context_11_287429_1468419
  · exact context_11_287430_1513777
  · exact context_11_287431_1513877

theorem selected_cut_52130 : selected 11 ⟨1513932, by decide⟩
    (prefixPartial 10 71858) = some ⟨10, 2, 0, 1513932, 71858, 2269, 1048576⟩ := by
  decide +kernel

theorem context_10_71858_1513932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71858 ⟨1513932, by decide⟩ :=
  accepted_of_selected 10 71858 ⟨1513932, by decide⟩ ⟨10, 2, 0, 1513932, 71858, 2269, 1048576⟩
    (by decide) selected_cut_52130

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
