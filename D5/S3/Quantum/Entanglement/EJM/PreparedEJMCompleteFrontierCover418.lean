/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover417
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_40131 : selected 8 ⟨1089851, by decide⟩
    (prefixPartial 13 1234965) = some ⟨13, 2, 0, 1089851, 1234965, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_1234965_1089851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234965 ⟨1089851, by decide⟩ :=
  accepted_of_selected 13 1234965 ⟨1089851, by decide⟩ ⟨13, 2, 0, 1089851, 1234965, 1449, 16384⟩
    (by decide) selected_cut_40131

theorem selected_cut_40132 : selected 8 ⟨1089873, by decide⟩
    (prefixPartial 13 1234966) = some ⟨13, 2, 0, 1089873, 1234966, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_1234966_1089873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234966 ⟨1089873, by decide⟩ :=
  accepted_of_selected 13 1234966 ⟨1089873, by decide⟩ ⟨13, 2, 0, 1089873, 1234966, 1053, 16384⟩
    (by decide) selected_cut_40132

theorem selected_cut_40133 : selected 8 ⟨1089892, by decide⟩
    (prefixPartial 13 1234967) = some ⟨13, 2, 0, 1089892, 1234967, 753, 16384⟩ := by
  decide +kernel

theorem context_13_1234967_1089892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234967 ⟨1089892, by decide⟩ :=
  accepted_of_selected 13 1234967 ⟨1089892, by decide⟩ ⟨13, 2, 0, 1089892, 1234967, 753, 16384⟩
    (by decide) selected_cut_40133

theorem unmarked_context_12_308741_1089893 : frontier 9 ⟨1089893, by decide⟩
    (prefixCache 12 308741) (prefixPartial 12 308741) = false := by
  decide +kernel

theorem node_context_12_308741_1089893 : EJMOriginalGlobalDAGData.nodes 9 ⟨1089893, by decide⟩ =
    .split (coordinate 12) (![⟨1089828, by decide⟩,⟨1089851, by decide⟩,⟨1089873, by decide⟩,⟨1089892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308741_1089893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308741 ⟨1089893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308741
    ⟨1089893, by decide⟩ (by decide) (![⟨1089828, by decide⟩,⟨1089851, by decide⟩,⟨1089873, by decide⟩,⟨1089892, by decide⟩]) unmarked_context_12_308741_1089893 node_context_12_308741_1089893
  intro a
  fin_cases a
  · exact context_13_1234964_1089828
  · exact context_13_1234965_1089851
  · exact context_13_1234966_1089873
  · exact context_13_1234967_1089892

theorem selected_cut_40134 : selected 8 ⟨1089918, by decide⟩
    (prefixPartial 13 1234968) = some ⟨13, 2, 0, 1089918, 1234968, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_1234968_1089918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234968 ⟨1089918, by decide⟩ :=
  accepted_of_selected 13 1234968 ⟨1089918, by decide⟩ ⟨13, 2, 0, 1089918, 1234968, 1577, 16384⟩
    (by decide) selected_cut_40134

theorem selected_cut_40135 : selected 8 ⟨1089937, by decide⟩
    (prefixPartial 13 1234969) = some ⟨13, 2, 0, 1089937, 1234969, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_1234969_1089937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234969 ⟨1089937, by decide⟩ :=
  accepted_of_selected 13 1234969 ⟨1089937, by decide⟩ ⟨13, 2, 0, 1089937, 1234969, 1349, 16384⟩
    (by decide) selected_cut_40135

theorem selected_cut_40136 : selected 8 ⟨1089955, by decide⟩
    (prefixPartial 13 1234970) = some ⟨13, 2, 0, 1089955, 1234970, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1234970_1089955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234970 ⟨1089955, by decide⟩ :=
  accepted_of_selected 13 1234970 ⟨1089955, by decide⟩ ⟨13, 2, 0, 1089955, 1234970, 1101, 16384⟩
    (by decide) selected_cut_40136

theorem selected_cut_40137 : selected 8 ⟨1089963, by decide⟩
    (prefixPartial 13 1234971) = some ⟨13, 2, 0, 1089963, 1234971, 697, 16384⟩ := by
  decide +kernel

theorem context_13_1234971_1089963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234971 ⟨1089963, by decide⟩ :=
  accepted_of_selected 13 1234971 ⟨1089963, by decide⟩ ⟨13, 2, 0, 1089963, 1234971, 697, 16384⟩
    (by decide) selected_cut_40137

theorem unmarked_context_12_308742_1089964 : frontier 9 ⟨1089964, by decide⟩
    (prefixCache 12 308742) (prefixPartial 12 308742) = false := by
  decide +kernel

theorem node_context_12_308742_1089964 : EJMOriginalGlobalDAGData.nodes 9 ⟨1089964, by decide⟩ =
    .split (coordinate 12) (![⟨1089918, by decide⟩,⟨1089937, by decide⟩,⟨1089955, by decide⟩,⟨1089963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308742_1089964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308742 ⟨1089964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308742
    ⟨1089964, by decide⟩ (by decide) (![⟨1089918, by decide⟩,⟨1089937, by decide⟩,⟨1089955, by decide⟩,⟨1089963, by decide⟩]) unmarked_context_12_308742_1089964 node_context_12_308742_1089964
  intro a
  fin_cases a
  · exact context_13_1234968_1089918
  · exact context_13_1234969_1089937
  · exact context_13_1234970_1089955
  · exact context_13_1234971_1089963

theorem selected_cut_40138 : selected 8 ⟨1089989, by decide⟩
    (prefixPartial 13 1234972) = some ⟨13, 2, 0, 1089989, 1234972, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_1234972_1089989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234972 ⟨1089989, by decide⟩ :=
  accepted_of_selected 13 1234972 ⟨1089989, by decide⟩ ⟨13, 2, 0, 1089989, 1234972, 1541, 16384⟩
    (by decide) selected_cut_40138

theorem selected_cut_40139 : selected 8 ⟨1090010, by decide⟩
    (prefixPartial 13 1234973) = some ⟨13, 2, 0, 1090010, 1234973, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_1234973_1090010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234973 ⟨1090010, by decide⟩ :=
  accepted_of_selected 13 1234973 ⟨1090010, by decide⟩ ⟨13, 2, 0, 1090010, 1234973, 1377, 16384⟩
    (by decide) selected_cut_40139

theorem selected_cut_40140 : selected 8 ⟨1090034, by decide⟩
    (prefixPartial 13 1234974) = some ⟨13, 2, 0, 1090034, 1234974, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_1234974_1090034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234974 ⟨1090034, by decide⟩ :=
  accepted_of_selected 13 1234974 ⟨1090034, by decide⟩ ⟨13, 2, 0, 1090034, 1234974, 1141, 16384⟩
    (by decide) selected_cut_40140

theorem selected_cut_40141 : selected 8 ⟨1090040, by decide⟩
    (prefixPartial 13 1234975) = some ⟨13, 2, 0, 1090040, 1234975, 577, 16384⟩ := by
  decide +kernel

theorem context_13_1234975_1090040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234975 ⟨1090040, by decide⟩ :=
  accepted_of_selected 13 1234975 ⟨1090040, by decide⟩ ⟨13, 2, 0, 1090040, 1234975, 577, 16384⟩
    (by decide) selected_cut_40141

theorem unmarked_context_12_308743_1090041 : frontier 9 ⟨1090041, by decide⟩
    (prefixCache 12 308743) (prefixPartial 12 308743) = false := by
  decide +kernel

theorem node_context_12_308743_1090041 : EJMOriginalGlobalDAGData.nodes 9 ⟨1090041, by decide⟩ =
    .split (coordinate 12) (![⟨1089989, by decide⟩,⟨1090010, by decide⟩,⟨1090034, by decide⟩,⟨1090040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308743_1090041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308743 ⟨1090041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308743
    ⟨1090041, by decide⟩ (by decide) (![⟨1089989, by decide⟩,⟨1090010, by decide⟩,⟨1090034, by decide⟩,⟨1090040, by decide⟩]) unmarked_context_12_308743_1090041 node_context_12_308743_1090041
  intro a
  fin_cases a
  · exact context_13_1234972_1089989
  · exact context_13_1234973_1090010
  · exact context_13_1234974_1090034
  · exact context_13_1234975_1090040

theorem unmarked_context_11_77185_1090042 : frontier 10 ⟨1090042, by decide⟩
    (prefixCache 11 77185) (prefixPartial 11 77185) = false := by
  decide +kernel

theorem node_context_11_77185_1090042 : EJMOriginalGlobalDAGData.nodes 10 ⟨1090042, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1089893, by decide⟩,⟨1089964, by decide⟩,⟨1090041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77185_1090042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77185 ⟨1090042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77185
    ⟨1090042, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1089893, by decide⟩,⟨1089964, by decide⟩,⟨1090041, by decide⟩]) unmarked_context_11_77185_1090042 node_context_11_77185_1090042
  intro a
  fin_cases a
  · exact context_12_308740_34034
  · exact context_12_308741_1089893
  · exact context_12_308742_1089964
  · exact context_12_308743_1090041

theorem selected_cut_40142 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 308744) = some ⟨12, 1, 0, 3161, 308744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308744_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308744 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 308744 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 308744, 1, 65536⟩
    (by decide) selected_cut_40142

theorem selected_cut_40143 : selected 8 ⟨1090069, by decide⟩
    (prefixPartial 13 1234980) = some ⟨13, 2, 0, 1090069, 1234980, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_1234980_1090069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234980 ⟨1090069, by decide⟩ :=
  accepted_of_selected 13 1234980 ⟨1090069, by decide⟩ ⟨13, 2, 0, 1090069, 1234980, 1425, 16384⟩
    (by decide) selected_cut_40143

theorem selected_cut_40144 : selected 8 ⟨1090087, by decide⟩
    (prefixPartial 13 1234981) = some ⟨13, 2, 0, 1090087, 1234981, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_1234981_1090087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234981 ⟨1090087, by decide⟩ :=
  accepted_of_selected 13 1234981 ⟨1090087, by decide⟩ ⟨13, 2, 0, 1090087, 1234981, 1437, 16384⟩
    (by decide) selected_cut_40144

theorem selected_cut_40145 : selected 8 ⟨1090110, by decide⟩
    (prefixPartial 13 1234982) = some ⟨13, 2, 0, 1090110, 1234982, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_1234982_1090110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234982 ⟨1090110, by decide⟩ :=
  accepted_of_selected 13 1234982 ⟨1090110, by decide⟩ ⟨13, 2, 0, 1090110, 1234982, 1025, 16384⟩
    (by decide) selected_cut_40145

theorem selected_cut_40146 : selected 8 ⟨1090120, by decide⟩
    (prefixPartial 13 1234983) = some ⟨13, 2, 0, 1090120, 1234983, 685, 16384⟩ := by
  decide +kernel

theorem context_13_1234983_1090120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234983 ⟨1090120, by decide⟩ :=
  accepted_of_selected 13 1234983 ⟨1090120, by decide⟩ ⟨13, 2, 0, 1090120, 1234983, 685, 16384⟩
    (by decide) selected_cut_40146

theorem unmarked_context_12_308745_1090121 : frontier 9 ⟨1090121, by decide⟩
    (prefixCache 12 308745) (prefixPartial 12 308745) = false := by
  decide +kernel

theorem node_context_12_308745_1090121 : EJMOriginalGlobalDAGData.nodes 9 ⟨1090121, by decide⟩ =
    .split (coordinate 12) (![⟨1090069, by decide⟩,⟨1090087, by decide⟩,⟨1090110, by decide⟩,⟨1090120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308745_1090121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308745 ⟨1090121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308745
    ⟨1090121, by decide⟩ (by decide) (![⟨1090069, by decide⟩,⟨1090087, by decide⟩,⟨1090110, by decide⟩,⟨1090120, by decide⟩]) unmarked_context_12_308745_1090121 node_context_12_308745_1090121
  intro a
  fin_cases a
  · exact context_13_1234980_1090069
  · exact context_13_1234981_1090087
  · exact context_13_1234982_1090110
  · exact context_13_1234983_1090120

theorem selected_cut_40147 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 308746) = some ⟨12, 1, 0, 893903, 308746, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308746_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308746 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 308746 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 308746, 1, 65536⟩
    (by decide) selected_cut_40147

theorem selected_cut_40148 : selected 8 ⟨1090156, by decide⟩
    (prefixPartial 13 1234988) = some ⟨13, 2, 0, 1090156, 1234988, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_1234988_1090156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234988 ⟨1090156, by decide⟩ :=
  accepted_of_selected 13 1234988 ⟨1090156, by decide⟩ ⟨13, 2, 0, 1090156, 1234988, 1465, 16384⟩
    (by decide) selected_cut_40148

theorem selected_cut_40149 : selected 8 ⟨1090185, by decide⟩
    (prefixPartial 13 1234989) = some ⟨13, 2, 0, 1090185, 1234989, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_1234989_1090185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234989 ⟨1090185, by decide⟩ :=
  accepted_of_selected 13 1234989 ⟨1090185, by decide⟩ ⟨13, 2, 0, 1090185, 1234989, 1573, 16384⟩
    (by decide) selected_cut_40149

theorem selected_cut_40150 : selected 8 ⟨1090205, by decide⟩
    (prefixPartial 13 1234990) = some ⟨13, 2, 0, 1090205, 1234990, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_1234990_1090205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234990 ⟨1090205, by decide⟩ :=
  accepted_of_selected 13 1234990 ⟨1090205, by decide⟩ ⟨13, 2, 0, 1090205, 1234990, 1145, 16384⟩
    (by decide) selected_cut_40150

theorem selected_cut_40151 : selected 8 ⟨1090216, by decide⟩
    (prefixPartial 13 1234991) = some ⟨13, 2, 0, 1090216, 1234991, 581, 16384⟩ := by
  decide +kernel

theorem context_13_1234991_1090216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234991 ⟨1090216, by decide⟩ :=
  accepted_of_selected 13 1234991 ⟨1090216, by decide⟩ ⟨13, 2, 0, 1090216, 1234991, 581, 16384⟩
    (by decide) selected_cut_40151

theorem unmarked_context_12_308747_1090217 : frontier 9 ⟨1090217, by decide⟩
    (prefixCache 12 308747) (prefixPartial 12 308747) = false := by
  decide +kernel

theorem node_context_12_308747_1090217 : EJMOriginalGlobalDAGData.nodes 9 ⟨1090217, by decide⟩ =
    .split (coordinate 12) (![⟨1090156, by decide⟩,⟨1090185, by decide⟩,⟨1090205, by decide⟩,⟨1090216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308747_1090217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308747 ⟨1090217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308747
    ⟨1090217, by decide⟩ (by decide) (![⟨1090156, by decide⟩,⟨1090185, by decide⟩,⟨1090205, by decide⟩,⟨1090216, by decide⟩]) unmarked_context_12_308747_1090217 node_context_12_308747_1090217
  intro a
  fin_cases a
  · exact context_13_1234988_1090156
  · exact context_13_1234989_1090185
  · exact context_13_1234990_1090205
  · exact context_13_1234991_1090216

theorem unmarked_context_11_77186_1090218 : frontier 10 ⟨1090218, by decide⟩
    (prefixCache 11 77186) (prefixPartial 11 77186) = false := by
  decide +kernel

theorem node_context_11_77186_1090218 : EJMOriginalGlobalDAGData.nodes 10 ⟨1090218, by decide⟩ =
    .split (coordinate 11) (![⟨3161, by decide⟩,⟨1090121, by decide⟩,⟨893903, by decide⟩,⟨1090217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77186_1090218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77186 ⟨1090218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77186
    ⟨1090218, by decide⟩ (by decide) (![⟨3161, by decide⟩,⟨1090121, by decide⟩,⟨893903, by decide⟩,⟨1090217, by decide⟩]) unmarked_context_11_77186_1090218 node_context_11_77186_1090218
  intro a
  fin_cases a
  · exact context_12_308744_3161
  · exact context_12_308745_1090121
  · exact context_12_308746_893903
  · exact context_12_308747_1090217

theorem selected_cut_40152 : selected 9 ⟨1090333, by decide⟩
    (prefixPartial 12 308748) = some ⟨12, 2, 0, 1090333, 308748, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_308748_1090333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308748 ⟨1090333, by decide⟩ :=
  accepted_of_selected 12 308748 ⟨1090333, by decide⟩ ⟨12, 2, 0, 1090333, 308748, 3085, 65536⟩
    (by decide) selected_cut_40152

theorem selected_cut_40153 : selected 8 ⟨1090350, by decide⟩
    (prefixPartial 13 1234996) = some ⟨13, 2, 0, 1090350, 1234996, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_1234996_1090350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234996 ⟨1090350, by decide⟩ :=
  accepted_of_selected 13 1234996 ⟨1090350, by decide⟩ ⟨13, 2, 0, 1090350, 1234996, 1293, 16384⟩
    (by decide) selected_cut_40153

theorem selected_cut_40154 : selected 8 ⟨1090385, by decide⟩
    (prefixPartial 13 1234997) = some ⟨13, 2, 0, 1090385, 1234997, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_1234997_1090385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234997 ⟨1090385, by decide⟩ :=
  accepted_of_selected 13 1234997 ⟨1090385, by decide⟩ ⟨13, 2, 0, 1090385, 1234997, 1569, 16384⟩
    (by decide) selected_cut_40154

theorem selected_cut_40155 : selected 8 ⟨1090402, by decide⟩
    (prefixPartial 13 1234998) = some ⟨13, 2, 0, 1090402, 1234998, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_1234998_1090402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234998 ⟨1090402, by decide⟩ :=
  accepted_of_selected 13 1234998 ⟨1090402, by decide⟩ ⟨13, 2, 0, 1090402, 1234998, 1041, 16384⟩
    (by decide) selected_cut_40155

theorem selected_cut_40156 : selected 8 ⟨1090418, by decide⟩
    (prefixPartial 13 1234999) = some ⟨13, 2, 0, 1090418, 1234999, 745, 16384⟩ := by
  decide +kernel

theorem context_13_1234999_1090418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234999 ⟨1090418, by decide⟩ :=
  accepted_of_selected 13 1234999 ⟨1090418, by decide⟩ ⟨13, 2, 0, 1090418, 1234999, 745, 16384⟩
    (by decide) selected_cut_40156

theorem unmarked_context_12_308749_1090419 : frontier 9 ⟨1090419, by decide⟩
    (prefixCache 12 308749) (prefixPartial 12 308749) = false := by
  decide +kernel

theorem node_context_12_308749_1090419 : EJMOriginalGlobalDAGData.nodes 9 ⟨1090419, by decide⟩ =
    .split (coordinate 12) (![⟨1090350, by decide⟩,⟨1090385, by decide⟩,⟨1090402, by decide⟩,⟨1090418, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308749_1090419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308749 ⟨1090419, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308749
    ⟨1090419, by decide⟩ (by decide) (![⟨1090350, by decide⟩,⟨1090385, by decide⟩,⟨1090402, by decide⟩,⟨1090418, by decide⟩]) unmarked_context_12_308749_1090419 node_context_12_308749_1090419
  intro a
  fin_cases a
  · exact context_13_1234996_1090350
  · exact context_13_1234997_1090385
  · exact context_13_1234998_1090402
  · exact context_13_1234999_1090418

theorem selected_cut_40157 : selected 8 ⟨1090441, by decide⟩
    (prefixPartial 13 1235000) = some ⟨13, 2, 0, 1090441, 1235000, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_1235000_1090441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235000 ⟨1090441, by decide⟩ :=
  accepted_of_selected 13 1235000 ⟨1090441, by decide⟩ ⟨13, 2, 0, 1090441, 1235000, 1217, 16384⟩
    (by decide) selected_cut_40157

theorem selected_cut_40158 : selected 8 ⟨1090468, by decide⟩
    (prefixPartial 13 1235001) = some ⟨13, 2, 0, 1090468, 1235001, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_1235001_1090468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235001 ⟨1090468, by decide⟩ :=
  accepted_of_selected 13 1235001 ⟨1090468, by decide⟩ ⟨13, 2, 0, 1090468, 1235001, 1689, 16384⟩
    (by decide) selected_cut_40158

theorem selected_cut_40159 : selected 8 ⟨1090486, by decide⟩
    (prefixPartial 13 1235002) = some ⟨13, 2, 0, 1090486, 1235002, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_1235002_1090486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235002 ⟨1090486, by decide⟩ :=
  accepted_of_selected 13 1235002 ⟨1090486, by decide⟩ ⟨13, 2, 0, 1090486, 1235002, 1061, 16384⟩
    (by decide) selected_cut_40159

theorem selected_cut_40160 : selected 8 ⟨1090502, by decide⟩
    (prefixPartial 13 1235003) = some ⟨13, 2, 0, 1090502, 1235003, 821, 16384⟩ := by
  decide +kernel

theorem context_13_1235003_1090502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235003 ⟨1090502, by decide⟩ :=
  accepted_of_selected 13 1235003 ⟨1090502, by decide⟩ ⟨13, 2, 0, 1090502, 1235003, 821, 16384⟩
    (by decide) selected_cut_40160

theorem unmarked_context_12_308750_1090503 : frontier 9 ⟨1090503, by decide⟩
    (prefixCache 12 308750) (prefixPartial 12 308750) = false := by
  decide +kernel

theorem node_context_12_308750_1090503 : EJMOriginalGlobalDAGData.nodes 9 ⟨1090503, by decide⟩ =
    .split (coordinate 12) (![⟨1090441, by decide⟩,⟨1090468, by decide⟩,⟨1090486, by decide⟩,⟨1090502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308750_1090503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308750 ⟨1090503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308750
    ⟨1090503, by decide⟩ (by decide) (![⟨1090441, by decide⟩,⟨1090468, by decide⟩,⟨1090486, by decide⟩,⟨1090502, by decide⟩]) unmarked_context_12_308750_1090503 node_context_12_308750_1090503
  intro a
  fin_cases a
  · exact context_13_1235000_1090441
  · exact context_13_1235001_1090468
  · exact context_13_1235002_1090486
  · exact context_13_1235003_1090502

theorem selected_cut_40161 : selected 8 ⟨1090528, by decide⟩
    (prefixPartial 13 1235004) = some ⟨13, 2, 0, 1090528, 1235004, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_1235004_1090528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235004 ⟨1090528, by decide⟩ :=
  accepted_of_selected 13 1235004 ⟨1090528, by decide⟩ ⟨13, 2, 0, 1090528, 1235004, 1065, 16384⟩
    (by decide) selected_cut_40161

theorem selected_cut_40162 : selected 8 ⟨1090557, by decide⟩
    (prefixPartial 13 1235005) = some ⟨13, 2, 0, 1090557, 1235005, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_1235005_1090557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235005 ⟨1090557, by decide⟩ :=
  accepted_of_selected 13 1235005 ⟨1090557, by decide⟩ ⟨13, 2, 0, 1090557, 1235005, 1533, 16384⟩
    (by decide) selected_cut_40162

theorem selected_cut_40163 : selected 8 ⟨1090578, by decide⟩
    (prefixPartial 13 1235006) = some ⟨13, 2, 0, 1090578, 1235006, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_1235006_1090578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235006 ⟨1090578, by decide⟩ :=
  accepted_of_selected 13 1235006 ⟨1090578, by decide⟩ ⟨13, 2, 0, 1090578, 1235006, 1025, 16384⟩
    (by decide) selected_cut_40163

theorem selected_cut_40164 : selected 8 ⟨1090590, by decide⟩
    (prefixPartial 13 1235007) = some ⟨13, 2, 0, 1090590, 1235007, 681, 16384⟩ := by
  decide +kernel

theorem context_13_1235007_1090590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235007 ⟨1090590, by decide⟩ :=
  accepted_of_selected 13 1235007 ⟨1090590, by decide⟩ ⟨13, 2, 0, 1090590, 1235007, 681, 16384⟩
    (by decide) selected_cut_40164

theorem unmarked_context_12_308751_1090591 : frontier 9 ⟨1090591, by decide⟩
    (prefixCache 12 308751) (prefixPartial 12 308751) = false := by
  decide +kernel

theorem node_context_12_308751_1090591 : EJMOriginalGlobalDAGData.nodes 9 ⟨1090591, by decide⟩ =
    .split (coordinate 12) (![⟨1090528, by decide⟩,⟨1090557, by decide⟩,⟨1090578, by decide⟩,⟨1090590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308751_1090591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308751 ⟨1090591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308751
    ⟨1090591, by decide⟩ (by decide) (![⟨1090528, by decide⟩,⟨1090557, by decide⟩,⟨1090578, by decide⟩,⟨1090590, by decide⟩]) unmarked_context_12_308751_1090591 node_context_12_308751_1090591
  intro a
  fin_cases a
  · exact context_13_1235004_1090528
  · exact context_13_1235005_1090557
  · exact context_13_1235006_1090578
  · exact context_13_1235007_1090590

theorem unmarked_context_11_77187_1090592 : frontier 10 ⟨1090592, by decide⟩
    (prefixCache 11 77187) (prefixPartial 11 77187) = false := by
  decide +kernel

theorem node_context_11_77187_1090592 : EJMOriginalGlobalDAGData.nodes 10 ⟨1090592, by decide⟩ =
    .split (coordinate 11) (![⟨1090333, by decide⟩,⟨1090419, by decide⟩,⟨1090503, by decide⟩,⟨1090591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77187_1090592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77187 ⟨1090592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77187
    ⟨1090592, by decide⟩ (by decide) (![⟨1090333, by decide⟩,⟨1090419, by decide⟩,⟨1090503, by decide⟩,⟨1090591, by decide⟩]) unmarked_context_11_77187_1090592 node_context_11_77187_1090592
  intro a
  fin_cases a
  · exact context_12_308748_1090333
  · exact context_12_308749_1090419
  · exact context_12_308750_1090503
  · exact context_12_308751_1090591

theorem unmarked_context_10_19296_1090593 : frontier 11 ⟨1090593, by decide⟩
    (prefixCache 10 19296) (prefixPartial 10 19296) = false := by
  decide +kernel

theorem node_context_10_19296_1090593 : EJMOriginalGlobalDAGData.nodes 11 ⟨1090593, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1090042, by decide⟩,⟨1090218, by decide⟩,⟨1090592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19296_1090593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19296 ⟨1090593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19296
    ⟨1090593, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1090042, by decide⟩,⟨1090218, by decide⟩,⟨1090592, by decide⟩]) unmarked_context_10_19296_1090593 node_context_10_19296_1090593
  intro a
  fin_cases a
  · exact context_11_77184_167448
  · exact context_11_77185_1090042
  · exact context_11_77186_1090218
  · exact context_11_77187_1090592

theorem selected_cut_40165 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308752) = some ⟨12, 1, 0, 26677, 308752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308752_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308752 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308752 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308752, 1, 65536⟩
    (by decide) selected_cut_40165

theorem selected_cut_40166 : selected 9 ⟨1090655, by decide⟩
    (prefixPartial 12 308753) = some ⟨12, 2, 0, 1090655, 308753, 3561, 65536⟩ := by
  decide +kernel

theorem context_12_308753_1090655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308753 ⟨1090655, by decide⟩ :=
  accepted_of_selected 12 308753 ⟨1090655, by decide⟩ ⟨12, 2, 0, 1090655, 308753, 3561, 65536⟩
    (by decide) selected_cut_40166

theorem selected_cut_40167 : selected 9 ⟨1090698, by decide⟩
    (prefixPartial 12 308754) = some ⟨12, 2, 0, 1090698, 308754, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_308754_1090698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308754 ⟨1090698, by decide⟩ :=
  accepted_of_selected 12 308754 ⟨1090698, by decide⟩ ⟨12, 2, 0, 1090698, 308754, 2057, 65536⟩
    (by decide) selected_cut_40167

theorem selected_cut_40168 : selected 8 ⟨1090719, by decide⟩
    (prefixPartial 13 1235020) = some ⟨13, 2, 0, 1090719, 1235020, 953, 16384⟩ := by
  decide +kernel

theorem context_13_1235020_1090719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235020 ⟨1090719, by decide⟩ :=
  accepted_of_selected 13 1235020 ⟨1090719, by decide⟩ ⟨13, 2, 0, 1090719, 1235020, 953, 16384⟩
    (by decide) selected_cut_40168

theorem selected_cut_40169 : selected 8 ⟨1090744, by decide⟩
    (prefixPartial 13 1235021) = some ⟨13, 2, 0, 1090744, 1235021, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_1235021_1090744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235021 ⟨1090744, by decide⟩ :=
  accepted_of_selected 13 1235021 ⟨1090744, by decide⟩ ⟨13, 2, 0, 1090744, 1235021, 1477, 16384⟩
    (by decide) selected_cut_40169

theorem selected_cut_40170 : selected 8 ⟨1090767, by decide⟩
    (prefixPartial 13 1235022) = some ⟨13, 2, 0, 1090767, 1235022, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_1235022_1090767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235022 ⟨1090767, by decide⟩ :=
  accepted_of_selected 13 1235022 ⟨1090767, by decide⟩ ⟨13, 2, 0, 1090767, 1235022, 1209, 16384⟩
    (by decide) selected_cut_40170

theorem selected_cut_40171 : selected 8 ⟨1090771, by decide⟩
    (prefixPartial 13 1235023) = some ⟨13, 2, 0, 1090771, 1235023, 525, 16384⟩ := by
  decide +kernel

theorem context_13_1235023_1090771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1235023 ⟨1090771, by decide⟩ :=
  accepted_of_selected 13 1235023 ⟨1090771, by decide⟩ ⟨13, 2, 0, 1090771, 1235023, 525, 16384⟩
    (by decide) selected_cut_40171

theorem unmarked_context_12_308755_1090772 : frontier 9 ⟨1090772, by decide⟩
    (prefixCache 12 308755) (prefixPartial 12 308755) = false := by
  decide +kernel

theorem node_context_12_308755_1090772 : EJMOriginalGlobalDAGData.nodes 9 ⟨1090772, by decide⟩ =
    .split (coordinate 12) (![⟨1090719, by decide⟩,⟨1090744, by decide⟩,⟨1090767, by decide⟩,⟨1090771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_308755_1090772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308755 ⟨1090772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 308755
    ⟨1090772, by decide⟩ (by decide) (![⟨1090719, by decide⟩,⟨1090744, by decide⟩,⟨1090767, by decide⟩,⟨1090771, by decide⟩]) unmarked_context_12_308755_1090772 node_context_12_308755_1090772
  intro a
  fin_cases a
  · exact context_13_1235020_1090719
  · exact context_13_1235021_1090744
  · exact context_13_1235022_1090767
  · exact context_13_1235023_1090771

theorem unmarked_context_11_77188_1090773 : frontier 10 ⟨1090773, by decide⟩
    (prefixCache 11 77188) (prefixPartial 11 77188) = false := by
  decide +kernel

theorem node_context_11_77188_1090773 : EJMOriginalGlobalDAGData.nodes 10 ⟨1090773, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1090655, by decide⟩,⟨1090698, by decide⟩,⟨1090772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77188_1090773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77188 ⟨1090773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77188
    ⟨1090773, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1090655, by decide⟩,⟨1090698, by decide⟩,⟨1090772, by decide⟩]) unmarked_context_11_77188_1090773 node_context_11_77188_1090773
  intro a
  fin_cases a
  · exact context_12_308752_26677
  · exact context_12_308753_1090655
  · exact context_12_308754_1090698
  · exact context_12_308755_1090772

theorem selected_cut_40172 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 77189) = some ⟨11, 1, 0, 892405, 77189, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77189_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77189 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 77189 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 77189, 1, 262144⟩
    (by decide) selected_cut_40172

theorem selected_cut_40173 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308760) = some ⟨12, 1, 0, 26677, 308760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308760_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308760 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308760 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308760, 1, 65536⟩
    (by decide) selected_cut_40173

theorem selected_cut_40174 : selected 9 ⟨1090826, by decide⟩
    (prefixPartial 12 308761) = some ⟨12, 2, 0, 1090826, 308761, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_308761_1090826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308761 ⟨1090826, by decide⟩ :=
  accepted_of_selected 12 308761 ⟨1090826, by decide⟩ ⟨12, 2, 0, 1090826, 308761, 3473, 65536⟩
    (by decide) selected_cut_40174

theorem selected_cut_40175 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 308762) = some ⟨12, 1, 0, 3161, 308762, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308762_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308762 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 308762 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 308762, 1, 65536⟩
    (by decide) selected_cut_40175

theorem selected_cut_40176 : selected 9 ⟨1090892, by decide⟩
    (prefixPartial 12 308763) = some ⟨12, 2, 0, 1090892, 308763, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_308763_1090892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308763 ⟨1090892, by decide⟩ :=
  accepted_of_selected 12 308763 ⟨1090892, by decide⟩ ⟨12, 2, 0, 1090892, 308763, 3929, 65536⟩
    (by decide) selected_cut_40176

theorem unmarked_context_11_77190_1090893 : frontier 10 ⟨1090893, by decide⟩
    (prefixCache 11 77190) (prefixPartial 11 77190) = false := by
  decide +kernel

theorem node_context_11_77190_1090893 : EJMOriginalGlobalDAGData.nodes 10 ⟨1090893, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1090826, by decide⟩,⟨3161, by decide⟩,⟨1090892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77190_1090893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77190 ⟨1090893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77190
    ⟨1090893, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1090826, by decide⟩,⟨3161, by decide⟩,⟨1090892, by decide⟩]) unmarked_context_11_77190_1090893 node_context_11_77190_1090893
  intro a
  fin_cases a
  · exact context_12_308760_26677
  · exact context_12_308761_1090826
  · exact context_12_308762_3161
  · exact context_12_308763_1090892

theorem selected_cut_40177 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308764) = some ⟨12, 1, 0, 26677, 308764, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308764_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308764 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308764 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308764, 1, 65536⟩
    (by decide) selected_cut_40177

theorem selected_cut_40178 : selected 9 ⟨1090961, by decide⟩
    (prefixPartial 12 308765) = some ⟨12, 2, 0, 1090961, 308765, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_308765_1090961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308765 ⟨1090961, by decide⟩ :=
  accepted_of_selected 12 308765 ⟨1090961, by decide⟩ ⟨12, 2, 0, 1090961, 308765, 3853, 65536⟩
    (by decide) selected_cut_40178

theorem selected_cut_40179 : selected 9 ⟨1091011, by decide⟩
    (prefixPartial 12 308766) = some ⟨12, 2, 0, 1091011, 308766, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_308766_1091011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308766 ⟨1091011, by decide⟩ :=
  accepted_of_selected 12 308766 ⟨1091011, by decide⟩ ⟨12, 2, 0, 1091011, 308766, 2249, 65536⟩
    (by decide) selected_cut_40179

theorem selected_cut_40180 : selected 9 ⟨1091085, by decide⟩
    (prefixPartial 12 308767) = some ⟨12, 2, 0, 1091085, 308767, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_308767_1091085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308767 ⟨1091085, by decide⟩ :=
  accepted_of_selected 12 308767 ⟨1091085, by decide⟩ ⟨12, 2, 0, 1091085, 308767, 3717, 65536⟩
    (by decide) selected_cut_40180

theorem unmarked_context_11_77191_1091086 : frontier 10 ⟨1091086, by decide⟩
    (prefixCache 11 77191) (prefixPartial 11 77191) = false := by
  decide +kernel

theorem node_context_11_77191_1091086 : EJMOriginalGlobalDAGData.nodes 10 ⟨1091086, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1090961, by decide⟩,⟨1091011, by decide⟩,⟨1091085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77191_1091086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77191 ⟨1091086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77191
    ⟨1091086, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1090961, by decide⟩,⟨1091011, by decide⟩,⟨1091085, by decide⟩]) unmarked_context_11_77191_1091086 node_context_11_77191_1091086
  intro a
  fin_cases a
  · exact context_12_308764_26677
  · exact context_12_308765_1090961
  · exact context_12_308766_1091011
  · exact context_12_308767_1091085

theorem unmarked_context_10_19297_1091087 : frontier 11 ⟨1091087, by decide⟩
    (prefixCache 10 19297) (prefixPartial 10 19297) = false := by
  decide +kernel

theorem node_context_10_19297_1091087 : EJMOriginalGlobalDAGData.nodes 11 ⟨1091087, by decide⟩ =
    .split (coordinate 10) (![⟨1090773, by decide⟩,⟨892405, by decide⟩,⟨1090893, by decide⟩,⟨1091086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19297_1091087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19297 ⟨1091087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19297
    ⟨1091087, by decide⟩ (by decide) (![⟨1090773, by decide⟩,⟨892405, by decide⟩,⟨1090893, by decide⟩,⟨1091086, by decide⟩]) unmarked_context_10_19297_1091087 node_context_10_19297_1091087
  intro a
  fin_cases a
  · exact context_11_77188_1090773
  · exact context_11_77189_892405
  · exact context_11_77190_1090893
  · exact context_11_77191_1091086

theorem selected_cut_40181 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308768) = some ⟨12, 1, 0, 26677, 308768, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308768_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308768 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308768 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308768, 1, 65536⟩
    (by decide) selected_cut_40181

theorem selected_cut_40182 : selected 9 ⟨1091148, by decide⟩
    (prefixPartial 12 308769) = some ⟨12, 2, 0, 1091148, 308769, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_308769_1091148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308769 ⟨1091148, by decide⟩ :=
  accepted_of_selected 12 308769 ⟨1091148, by decide⟩ ⟨12, 2, 0, 1091148, 308769, 2193, 65536⟩
    (by decide) selected_cut_40182

theorem selected_cut_40183 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308770) = some ⟨12, 1, 0, 26677, 308770, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308770_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308770 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308770 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308770, 1, 65536⟩
    (by decide) selected_cut_40183

theorem selected_cut_40184 : selected 9 ⟨1091224, by decide⟩
    (prefixPartial 12 308771) = some ⟨12, 2, 0, 1091224, 308771, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_308771_1091224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308771 ⟨1091224, by decide⟩ :=
  accepted_of_selected 12 308771 ⟨1091224, by decide⟩ ⟨12, 2, 0, 1091224, 308771, 3745, 65536⟩
    (by decide) selected_cut_40184

theorem unmarked_context_11_77192_1091225 : frontier 10 ⟨1091225, by decide⟩
    (prefixCache 11 77192) (prefixPartial 11 77192) = false := by
  decide +kernel

theorem node_context_11_77192_1091225 : EJMOriginalGlobalDAGData.nodes 10 ⟨1091225, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1091148, by decide⟩,⟨26677, by decide⟩,⟨1091224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77192_1091225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77192 ⟨1091225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77192
    ⟨1091225, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1091148, by decide⟩,⟨26677, by decide⟩,⟨1091224, by decide⟩]) unmarked_context_11_77192_1091225 node_context_11_77192_1091225
  intro a
  fin_cases a
  · exact context_12_308768_26677
  · exact context_12_308769_1091148
  · exact context_12_308770_26677
  · exact context_12_308771_1091224

theorem selected_cut_40185 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308772) = some ⟨12, 1, 0, 26677, 308772, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308772_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308772 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308772 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308772, 1, 65536⟩
    (by decide) selected_cut_40185

theorem selected_cut_40186 : selected 9 ⟨1091293, by decide⟩
    (prefixPartial 12 308773) = some ⟨12, 2, 0, 1091293, 308773, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_308773_1091293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308773 ⟨1091293, by decide⟩ :=
  accepted_of_selected 12 308773 ⟨1091293, by decide⟩ ⟨12, 2, 0, 1091293, 308773, 3725, 65536⟩
    (by decide) selected_cut_40186

theorem selected_cut_40187 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308774) = some ⟨12, 1, 0, 26677, 308774, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308774_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308774 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308774 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308774, 1, 65536⟩
    (by decide) selected_cut_40187

theorem selected_cut_40188 : selected 9 ⟨1091365, by decide⟩
    (prefixPartial 12 308775) = some ⟨12, 2, 0, 1091365, 308775, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_308775_1091365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308775 ⟨1091365, by decide⟩ :=
  accepted_of_selected 12 308775 ⟨1091365, by decide⟩ ⟨12, 2, 0, 1091365, 308775, 3369, 65536⟩
    (by decide) selected_cut_40188

theorem unmarked_context_11_77193_1091366 : frontier 10 ⟨1091366, by decide⟩
    (prefixCache 11 77193) (prefixPartial 11 77193) = false := by
  decide +kernel

theorem node_context_11_77193_1091366 : EJMOriginalGlobalDAGData.nodes 10 ⟨1091366, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1091293, by decide⟩,⟨26677, by decide⟩,⟨1091365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77193_1091366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77193 ⟨1091366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77193
    ⟨1091366, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1091293, by decide⟩,⟨26677, by decide⟩,⟨1091365, by decide⟩]) unmarked_context_11_77193_1091366 node_context_11_77193_1091366
  intro a
  fin_cases a
  · exact context_12_308772_26677
  · exact context_12_308773_1091293
  · exact context_12_308774_26677
  · exact context_12_308775_1091365

theorem selected_cut_40189 : selected 10 ⟨1091423, by decide⟩
    (prefixPartial 11 77194) = some ⟨11, 2, 0, 1091423, 77194, 3601, 262144⟩ := by
  decide +kernel

theorem context_11_77194_1091423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77194 ⟨1091423, by decide⟩ :=
  accepted_of_selected 11 77194 ⟨1091423, by decide⟩ ⟨11, 2, 0, 1091423, 77194, 3601, 262144⟩
    (by decide) selected_cut_40189

theorem selected_cut_40190 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308780) = some ⟨12, 1, 0, 26677, 308780, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308780_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308780 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308780 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308780, 1, 65536⟩
    (by decide) selected_cut_40190

theorem selected_cut_40191 : selected 9 ⟨1091491, by decide⟩
    (prefixPartial 12 308781) = some ⟨12, 2, 0, 1091491, 308781, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_308781_1091491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308781 ⟨1091491, by decide⟩ :=
  accepted_of_selected 12 308781 ⟨1091491, by decide⟩ ⟨12, 2, 0, 1091491, 308781, 2185, 65536⟩
    (by decide) selected_cut_40191

theorem selected_cut_40192 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 308782) = some ⟨12, 1, 0, 26677, 308782, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308782_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308782 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 308782 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 308782, 1, 65536⟩
    (by decide) selected_cut_40192

theorem selected_cut_40193 : selected 9 ⟨1091550, by decide⟩
    (prefixPartial 12 308783) = some ⟨12, 2, 0, 1091550, 308783, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_308783_1091550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308783 ⟨1091550, by decide⟩ :=
  accepted_of_selected 12 308783 ⟨1091550, by decide⟩ ⟨12, 2, 0, 1091550, 308783, 3193, 65536⟩
    (by decide) selected_cut_40193

theorem unmarked_context_11_77195_1091551 : frontier 10 ⟨1091551, by decide⟩
    (prefixCache 11 77195) (prefixPartial 11 77195) = false := by
  decide +kernel

theorem node_context_11_77195_1091551 : EJMOriginalGlobalDAGData.nodes 10 ⟨1091551, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1091491, by decide⟩,⟨26677, by decide⟩,⟨1091550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77195_1091551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77195 ⟨1091551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77195
    ⟨1091551, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1091491, by decide⟩,⟨26677, by decide⟩,⟨1091550, by decide⟩]) unmarked_context_11_77195_1091551 node_context_11_77195_1091551
  intro a
  fin_cases a
  · exact context_12_308780_26677
  · exact context_12_308781_1091491
  · exact context_12_308782_26677
  · exact context_12_308783_1091550

theorem unmarked_context_10_19298_1091552 : frontier 11 ⟨1091552, by decide⟩
    (prefixCache 10 19298) (prefixPartial 10 19298) = false := by
  decide +kernel

theorem node_context_10_19298_1091552 : EJMOriginalGlobalDAGData.nodes 11 ⟨1091552, by decide⟩ =
    .split (coordinate 10) (![⟨1091225, by decide⟩,⟨1091366, by decide⟩,⟨1091423, by decide⟩,⟨1091551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19298_1091552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19298 ⟨1091552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19298
    ⟨1091552, by decide⟩ (by decide) (![⟨1091225, by decide⟩,⟨1091366, by decide⟩,⟨1091423, by decide⟩,⟨1091551, by decide⟩]) unmarked_context_10_19298_1091552 node_context_10_19298_1091552
  intro a
  fin_cases a
  · exact context_11_77192_1091225
  · exact context_11_77193_1091366
  · exact context_11_77194_1091423
  · exact context_11_77195_1091551

theorem selected_cut_40194 : selected 10 ⟨1091629, by decide⟩
    (prefixPartial 11 77196) = some ⟨11, 2, 0, 1091629, 77196, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_77196_1091629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77196 ⟨1091629, by decide⟩ :=
  accepted_of_selected 11 77196 ⟨1091629, by decide⟩ ⟨11, 2, 0, 1091629, 77196, 2117, 262144⟩
    (by decide) selected_cut_40194

theorem selected_cut_40195 : selected 10 ⟨1091678, by decide⟩
    (prefixPartial 11 77197) = some ⟨11, 2, 0, 1091678, 77197, 3209, 262144⟩ := by
  decide +kernel

theorem context_11_77197_1091678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77197 ⟨1091678, by decide⟩ :=
  accepted_of_selected 11 77197 ⟨1091678, by decide⟩ ⟨11, 2, 0, 1091678, 77197, 3209, 262144⟩
    (by decide) selected_cut_40195

theorem selected_cut_40196 : selected 10 ⟨29032, by decide⟩
    (prefixPartial 11 77198) = some ⟨11, 2, 0, 29032, 77198, 5, 262144⟩ := by
  decide +kernel

theorem context_11_77198_29032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77198 ⟨29032, by decide⟩ :=
  accepted_of_selected 11 77198 ⟨29032, by decide⟩ ⟨11, 2, 0, 29032, 77198, 5, 262144⟩
    (by decide) selected_cut_40196

theorem selected_cut_40197 : selected 10 ⟨1091757, by decide⟩
    (prefixPartial 11 77199) = some ⟨11, 2, 0, 1091757, 77199, 945, 262144⟩ := by
  decide +kernel

theorem context_11_77199_1091757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77199 ⟨1091757, by decide⟩ :=
  accepted_of_selected 11 77199 ⟨1091757, by decide⟩ ⟨11, 2, 0, 1091757, 77199, 945, 262144⟩
    (by decide) selected_cut_40197

theorem unmarked_context_10_19299_1091758 : frontier 11 ⟨1091758, by decide⟩
    (prefixCache 10 19299) (prefixPartial 10 19299) = false := by
  decide +kernel

theorem node_context_10_19299_1091758 : EJMOriginalGlobalDAGData.nodes 11 ⟨1091758, by decide⟩ =
    .split (coordinate 10) (![⟨1091629, by decide⟩,⟨1091678, by decide⟩,⟨29032, by decide⟩,⟨1091757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19299_1091758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19299 ⟨1091758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19299
    ⟨1091758, by decide⟩ (by decide) (![⟨1091629, by decide⟩,⟨1091678, by decide⟩,⟨29032, by decide⟩,⟨1091757, by decide⟩]) unmarked_context_10_19299_1091758 node_context_10_19299_1091758
  intro a
  fin_cases a
  · exact context_11_77196_1091629
  · exact context_11_77197_1091678
  · exact context_11_77198_29032
  · exact context_11_77199_1091757

theorem unmarked_context_9_4824_1091759 : frontier 12 ⟨1091759, by decide⟩
    (prefixCache 9 4824) (prefixPartial 9 4824) = false := by
  decide +kernel

theorem node_context_9_4824_1091759 : EJMOriginalGlobalDAGData.nodes 12 ⟨1091759, by decide⟩ =
    .split (coordinate 9) (![⟨1090593, by decide⟩,⟨1091087, by decide⟩,⟨1091552, by decide⟩,⟨1091758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4824_1091759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4824 ⟨1091759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4824
    ⟨1091759, by decide⟩ (by decide) (![⟨1090593, by decide⟩,⟨1091087, by decide⟩,⟨1091552, by decide⟩,⟨1091758, by decide⟩]) unmarked_context_9_4824_1091759 node_context_9_4824_1091759
  intro a
  fin_cases a
  · exact context_10_19296_1090593
  · exact context_10_19297_1091087
  · exact context_10_19298_1091552
  · exact context_10_19299_1091758

theorem selected_cut_40198 : selected 9 ⟨277904, by decide⟩
    (prefixPartial 12 308800) = some ⟨12, 1, 0, 277904, 308800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308800_277904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308800 ⟨277904, by decide⟩ :=
  accepted_of_selected 12 308800 ⟨277904, by decide⟩ ⟨12, 1, 0, 277904, 308800, 1, 65536⟩
    (by decide) selected_cut_40198

theorem selected_cut_40199 : selected 9 ⟨1091807, by decide⟩
    (prefixPartial 12 308801) = some ⟨12, 2, 0, 1091807, 308801, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_308801_1091807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308801 ⟨1091807, by decide⟩ :=
  accepted_of_selected 12 308801 ⟨1091807, by decide⟩ ⟨12, 2, 0, 1091807, 308801, 3149, 65536⟩
    (by decide) selected_cut_40199

theorem selected_cut_40200 : selected 9 ⟨1091851, by decide⟩
    (prefixPartial 12 308802) = some ⟨12, 2, 0, 1091851, 308802, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_308802_1091851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308802 ⟨1091851, by decide⟩ :=
  accepted_of_selected 12 308802 ⟨1091851, by decide⟩ ⟨12, 2, 0, 1091851, 308802, 3429, 65536⟩
    (by decide) selected_cut_40200

theorem selected_cut_40201 : selected 9 ⟨1091906, by decide⟩
    (prefixPartial 12 308803) = some ⟨12, 2, 0, 1091906, 308803, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_308803_1091906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308803 ⟨1091906, by decide⟩ :=
  accepted_of_selected 12 308803 ⟨1091906, by decide⟩ ⟨12, 2, 0, 1091906, 308803, 3437, 65536⟩
    (by decide) selected_cut_40201

theorem unmarked_context_11_77200_1091907 : frontier 10 ⟨1091907, by decide⟩
    (prefixCache 11 77200) (prefixPartial 11 77200) = false := by
  decide +kernel

theorem node_context_11_77200_1091907 : EJMOriginalGlobalDAGData.nodes 10 ⟨1091907, by decide⟩ =
    .split (coordinate 11) (![⟨277904, by decide⟩,⟨1091807, by decide⟩,⟨1091851, by decide⟩,⟨1091906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77200_1091907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77200 ⟨1091907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77200
    ⟨1091907, by decide⟩ (by decide) (![⟨277904, by decide⟩,⟨1091807, by decide⟩,⟨1091851, by decide⟩,⟨1091906, by decide⟩]) unmarked_context_11_77200_1091907 node_context_11_77200_1091907
  intro a
  fin_cases a
  · exact context_12_308800_277904
  · exact context_12_308801_1091807
  · exact context_12_308802_1091851
  · exact context_12_308803_1091906

theorem selected_cut_40202 : selected 9 ⟨1091969, by decide⟩
    (prefixPartial 12 308804) = some ⟨12, 2, 0, 1091969, 308804, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_308804_1091969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308804 ⟨1091969, by decide⟩ :=
  accepted_of_selected 12 308804 ⟨1091969, by decide⟩ ⟨12, 2, 0, 1091969, 308804, 3533, 65536⟩
    (by decide) selected_cut_40202

theorem selected_cut_40203 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 308805) = some ⟨12, 1, 0, 691709, 308805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308805_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308805 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 308805 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 308805, 1, 65536⟩
    (by decide) selected_cut_40203

theorem selected_cut_40204 : selected 9 ⟨1092016, by decide⟩
    (prefixPartial 12 308806) = some ⟨12, 2, 0, 1092016, 308806, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_308806_1092016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308806 ⟨1092016, by decide⟩ :=
  accepted_of_selected 12 308806 ⟨1092016, by decide⟩ ⟨12, 2, 0, 1092016, 308806, 2953, 65536⟩
    (by decide) selected_cut_40204

theorem selected_cut_40205 : selected 9 ⟨1092076, by decide⟩
    (prefixPartial 12 308807) = some ⟨12, 2, 0, 1092076, 308807, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_308807_1092076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308807 ⟨1092076, by decide⟩ :=
  accepted_of_selected 12 308807 ⟨1092076, by decide⟩ ⟨12, 2, 0, 1092076, 308807, 2917, 65536⟩
    (by decide) selected_cut_40205

theorem unmarked_context_11_77201_1092077 : frontier 10 ⟨1092077, by decide⟩
    (prefixCache 11 77201) (prefixPartial 11 77201) = false := by
  decide +kernel

theorem node_context_11_77201_1092077 : EJMOriginalGlobalDAGData.nodes 10 ⟨1092077, by decide⟩ =
    .split (coordinate 11) (![⟨1091969, by decide⟩,⟨691709, by decide⟩,⟨1092016, by decide⟩,⟨1092076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77201_1092077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77201 ⟨1092077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77201
    ⟨1092077, by decide⟩ (by decide) (![⟨1091969, by decide⟩,⟨691709, by decide⟩,⟨1092016, by decide⟩,⟨1092076, by decide⟩]) unmarked_context_11_77201_1092077 node_context_11_77201_1092077
  intro a
  fin_cases a
  · exact context_12_308804_1091969
  · exact context_12_308805_691709
  · exact context_12_308806_1092016
  · exact context_12_308807_1092076

theorem selected_cut_40206 : selected 9 ⟨1092150, by decide⟩
    (prefixPartial 12 308808) = some ⟨12, 2, 0, 1092150, 308808, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_308808_1092150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308808 ⟨1092150, by decide⟩ :=
  accepted_of_selected 12 308808 ⟨1092150, by decide⟩ ⟨12, 2, 0, 1092150, 308808, 3461, 65536⟩
    (by decide) selected_cut_40206

theorem selected_cut_40207 : selected 9 ⟨1092196, by decide⟩
    (prefixPartial 12 308809) = some ⟨12, 2, 0, 1092196, 308809, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_308809_1092196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308809 ⟨1092196, by decide⟩ :=
  accepted_of_selected 12 308809 ⟨1092196, by decide⟩ ⟨12, 2, 0, 1092196, 308809, 2701, 65536⟩
    (by decide) selected_cut_40207

theorem selected_cut_40208 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 308810) = some ⟨12, 1, 0, 893903, 308810, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308810_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308810 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 308810 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 308810, 1, 65536⟩
    (by decide) selected_cut_40208

theorem selected_cut_40209 : selected 9 ⟨1092264, by decide⟩
    (prefixPartial 12 308811) = some ⟨12, 2, 0, 1092264, 308811, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_308811_1092264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308811 ⟨1092264, by decide⟩ :=
  accepted_of_selected 12 308811 ⟨1092264, by decide⟩ ⟨12, 2, 0, 1092264, 308811, 3117, 65536⟩
    (by decide) selected_cut_40209

theorem unmarked_context_11_77202_1092265 : frontier 10 ⟨1092265, by decide⟩
    (prefixCache 11 77202) (prefixPartial 11 77202) = false := by
  decide +kernel

theorem node_context_11_77202_1092265 : EJMOriginalGlobalDAGData.nodes 10 ⟨1092265, by decide⟩ =
    .split (coordinate 11) (![⟨1092150, by decide⟩,⟨1092196, by decide⟩,⟨893903, by decide⟩,⟨1092264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77202_1092265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77202 ⟨1092265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77202
    ⟨1092265, by decide⟩ (by decide) (![⟨1092150, by decide⟩,⟨1092196, by decide⟩,⟨893903, by decide⟩,⟨1092264, by decide⟩]) unmarked_context_11_77202_1092265 node_context_11_77202_1092265
  intro a
  fin_cases a
  · exact context_12_308808_1092150
  · exact context_12_308809_1092196
  · exact context_12_308810_893903
  · exact context_12_308811_1092264

theorem selected_cut_40210 : selected 9 ⟨1092345, by decide⟩
    (prefixPartial 12 308812) = some ⟨12, 2, 0, 1092345, 308812, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_308812_1092345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308812 ⟨1092345, by decide⟩ :=
  accepted_of_selected 12 308812 ⟨1092345, by decide⟩ ⟨12, 2, 0, 1092345, 308812, 3413, 65536⟩
    (by decide) selected_cut_40210

theorem selected_cut_40211 : selected 9 ⟨1092397, by decide⟩
    (prefixPartial 12 308813) = some ⟨12, 2, 0, 1092397, 308813, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_308813_1092397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308813 ⟨1092397, by decide⟩ :=
  accepted_of_selected 12 308813 ⟨1092397, by decide⟩ ⟨12, 2, 0, 1092397, 308813, 2697, 65536⟩
    (by decide) selected_cut_40211

theorem selected_cut_40212 : selected 9 ⟨1092445, by decide⟩
    (prefixPartial 12 308814) = some ⟨12, 2, 0, 1092445, 308814, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_308814_1092445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308814 ⟨1092445, by decide⟩ :=
  accepted_of_selected 12 308814 ⟨1092445, by decide⟩ ⟨12, 2, 0, 1092445, 308814, 2941, 65536⟩
    (by decide) selected_cut_40212

theorem selected_cut_40213 : selected 9 ⟨1092494, by decide⟩
    (prefixPartial 12 308815) = some ⟨12, 2, 0, 1092494, 308815, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_308815_1092494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308815 ⟨1092494, by decide⟩ :=
  accepted_of_selected 12 308815 ⟨1092494, by decide⟩ ⟨12, 2, 0, 1092494, 308815, 2689, 65536⟩
    (by decide) selected_cut_40213

theorem unmarked_context_11_77203_1092495 : frontier 10 ⟨1092495, by decide⟩
    (prefixCache 11 77203) (prefixPartial 11 77203) = false := by
  decide +kernel

theorem node_context_11_77203_1092495 : EJMOriginalGlobalDAGData.nodes 10 ⟨1092495, by decide⟩ =
    .split (coordinate 11) (![⟨1092345, by decide⟩,⟨1092397, by decide⟩,⟨1092445, by decide⟩,⟨1092494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77203_1092495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77203 ⟨1092495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77203
    ⟨1092495, by decide⟩ (by decide) (![⟨1092345, by decide⟩,⟨1092397, by decide⟩,⟨1092445, by decide⟩,⟨1092494, by decide⟩]) unmarked_context_11_77203_1092495 node_context_11_77203_1092495
  intro a
  fin_cases a
  · exact context_12_308812_1092345
  · exact context_12_308813_1092397
  · exact context_12_308814_1092445
  · exact context_12_308815_1092494

theorem unmarked_context_10_19300_1092496 : frontier 11 ⟨1092496, by decide⟩
    (prefixCache 10 19300) (prefixPartial 10 19300) = false := by
  decide +kernel

theorem node_context_10_19300_1092496 : EJMOriginalGlobalDAGData.nodes 11 ⟨1092496, by decide⟩ =
    .split (coordinate 10) (![⟨1091907, by decide⟩,⟨1092077, by decide⟩,⟨1092265, by decide⟩,⟨1092495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19300_1092496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19300 ⟨1092496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19300
    ⟨1092496, by decide⟩ (by decide) (![⟨1091907, by decide⟩,⟨1092077, by decide⟩,⟨1092265, by decide⟩,⟨1092495, by decide⟩]) unmarked_context_10_19300_1092496 node_context_10_19300_1092496
  intro a
  fin_cases a
  · exact context_11_77200_1091907
  · exact context_11_77201_1092077
  · exact context_11_77202_1092265
  · exact context_11_77203_1092495

theorem selected_cut_40214 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19301) = some ⟨10, 1, 0, 893098, 19301, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19301_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19301 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19301 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19301, 1, 1048576⟩
    (by decide) selected_cut_40214

theorem selected_cut_40215 : selected 9 ⟨1092542, by decide⟩
    (prefixPartial 12 308832) = some ⟨12, 2, 0, 1092542, 308832, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_308832_1092542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308832 ⟨1092542, by decide⟩ :=
  accepted_of_selected 12 308832 ⟨1092542, by decide⟩ ⟨12, 2, 0, 1092542, 308832, 2453, 65536⟩
    (by decide) selected_cut_40215

theorem selected_cut_40216 : selected 9 ⟨1092584, by decide⟩
    (prefixPartial 12 308833) = some ⟨12, 2, 0, 1092584, 308833, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_308833_1092584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308833 ⟨1092584, by decide⟩ :=
  accepted_of_selected 12 308833 ⟨1092584, by decide⟩ ⟨12, 2, 0, 1092584, 308833, 2165, 65536⟩
    (by decide) selected_cut_40216

theorem selected_cut_40217 : selected 9 ⟨1092618, by decide⟩
    (prefixPartial 12 308834) = some ⟨12, 2, 0, 1092618, 308834, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_308834_1092618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308834 ⟨1092618, by decide⟩ :=
  accepted_of_selected 12 308834 ⟨1092618, by decide⟩ ⟨12, 2, 0, 1092618, 308834, 2165, 65536⟩
    (by decide) selected_cut_40217

theorem selected_cut_40218 : selected 9 ⟨1092667, by decide⟩
    (prefixPartial 12 308835) = some ⟨12, 2, 0, 1092667, 308835, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_308835_1092667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308835 ⟨1092667, by decide⟩ :=
  accepted_of_selected 12 308835 ⟨1092667, by decide⟩ ⟨12, 2, 0, 1092667, 308835, 2317, 65536⟩
    (by decide) selected_cut_40218

theorem unmarked_context_11_77208_1092668 : frontier 10 ⟨1092668, by decide⟩
    (prefixCache 11 77208) (prefixPartial 11 77208) = false := by
  decide +kernel

theorem node_context_11_77208_1092668 : EJMOriginalGlobalDAGData.nodes 10 ⟨1092668, by decide⟩ =
    .split (coordinate 11) (![⟨1092542, by decide⟩,⟨1092584, by decide⟩,⟨1092618, by decide⟩,⟨1092667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77208_1092668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77208 ⟨1092668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77208
    ⟨1092668, by decide⟩ (by decide) (![⟨1092542, by decide⟩,⟨1092584, by decide⟩,⟨1092618, by decide⟩,⟨1092667, by decide⟩]) unmarked_context_11_77208_1092668 node_context_11_77208_1092668
  intro a
  fin_cases a
  · exact context_12_308832_1092542
  · exact context_12_308833_1092584
  · exact context_12_308834_1092618
  · exact context_12_308835_1092667

theorem selected_cut_40219 : selected 9 ⟨1092700, by decide⟩
    (prefixPartial 12 308836) = some ⟨12, 2, 0, 1092700, 308836, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_308836_1092700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308836 ⟨1092700, by decide⟩ :=
  accepted_of_selected 12 308836 ⟨1092700, by decide⟩ ⟨12, 2, 0, 1092700, 308836, 1877, 65536⟩
    (by decide) selected_cut_40219

theorem selected_cut_40220 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 308837) = some ⟨12, 1, 0, 691709, 308837, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308837_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308837 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 308837 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 308837, 1, 65536⟩
    (by decide) selected_cut_40220

theorem selected_cut_40221 : selected 9 ⟨1092731, by decide⟩
    (prefixPartial 12 308838) = some ⟨12, 2, 0, 1092731, 308838, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_308838_1092731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308838 ⟨1092731, by decide⟩ :=
  accepted_of_selected 12 308838 ⟨1092731, by decide⟩ ⟨12, 2, 0, 1092731, 308838, 1637, 65536⟩
    (by decide) selected_cut_40221

theorem selected_cut_40222 : selected 9 ⟨1092764, by decide⟩
    (prefixPartial 12 308839) = some ⟨12, 2, 0, 1092764, 308839, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_308839_1092764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308839 ⟨1092764, by decide⟩ :=
  accepted_of_selected 12 308839 ⟨1092764, by decide⟩ ⟨12, 2, 0, 1092764, 308839, 1745, 65536⟩
    (by decide) selected_cut_40222

theorem unmarked_context_11_77209_1092765 : frontier 10 ⟨1092765, by decide⟩
    (prefixCache 11 77209) (prefixPartial 11 77209) = false := by
  decide +kernel

theorem node_context_11_77209_1092765 : EJMOriginalGlobalDAGData.nodes 10 ⟨1092765, by decide⟩ =
    .split (coordinate 11) (![⟨1092700, by decide⟩,⟨691709, by decide⟩,⟨1092731, by decide⟩,⟨1092764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77209_1092765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77209 ⟨1092765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77209
    ⟨1092765, by decide⟩ (by decide) (![⟨1092700, by decide⟩,⟨691709, by decide⟩,⟨1092731, by decide⟩,⟨1092764, by decide⟩]) unmarked_context_11_77209_1092765 node_context_11_77209_1092765
  intro a
  fin_cases a
  · exact context_12_308836_1092700
  · exact context_12_308837_691709
  · exact context_12_308838_1092731
  · exact context_12_308839_1092764

theorem selected_cut_40223 : selected 9 ⟨1092806, by decide⟩
    (prefixPartial 12 308840) = some ⟨12, 2, 0, 1092806, 308840, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_308840_1092806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308840 ⟨1092806, by decide⟩ :=
  accepted_of_selected 12 308840 ⟨1092806, by decide⟩ ⟨12, 2, 0, 1092806, 308840, 1973, 65536⟩
    (by decide) selected_cut_40223

theorem selected_cut_40224 : selected 9 ⟨1092846, by decide⟩
    (prefixPartial 12 308841) = some ⟨12, 2, 0, 1092846, 308841, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_308841_1092846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308841 ⟨1092846, by decide⟩ :=
  accepted_of_selected 12 308841 ⟨1092846, by decide⟩ ⟨12, 2, 0, 1092846, 308841, 1793, 65536⟩
    (by decide) selected_cut_40224

theorem selected_cut_40225 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 308842) = some ⟨12, 1, 0, 661671, 308842, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308842_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308842 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 308842 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 308842, 1, 65536⟩
    (by decide) selected_cut_40225

theorem selected_cut_40226 : selected 9 ⟨1092890, by decide⟩
    (prefixPartial 12 308843) = some ⟨12, 2, 0, 1092890, 308843, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_308843_1092890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308843 ⟨1092890, by decide⟩ :=
  accepted_of_selected 12 308843 ⟨1092890, by decide⟩ ⟨12, 2, 0, 1092890, 308843, 1821, 65536⟩
    (by decide) selected_cut_40226

theorem unmarked_context_11_77210_1092891 : frontier 10 ⟨1092891, by decide⟩
    (prefixCache 11 77210) (prefixPartial 11 77210) = false := by
  decide +kernel

theorem node_context_11_77210_1092891 : EJMOriginalGlobalDAGData.nodes 10 ⟨1092891, by decide⟩ =
    .split (coordinate 11) (![⟨1092806, by decide⟩,⟨1092846, by decide⟩,⟨661671, by decide⟩,⟨1092890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77210_1092891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77210 ⟨1092891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77210
    ⟨1092891, by decide⟩ (by decide) (![⟨1092806, by decide⟩,⟨1092846, by decide⟩,⟨661671, by decide⟩,⟨1092890, by decide⟩]) unmarked_context_11_77210_1092891 node_context_11_77210_1092891
  intro a
  fin_cases a
  · exact context_12_308840_1092806
  · exact context_12_308841_1092846
  · exact context_12_308842_661671
  · exact context_12_308843_1092890

theorem selected_cut_40227 : selected 9 ⟨1092920, by decide⟩
    (prefixPartial 12 308844) = some ⟨12, 2, 0, 1092920, 308844, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_308844_1092920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308844 ⟨1092920, by decide⟩ :=
  accepted_of_selected 12 308844 ⟨1092920, by decide⟩ ⟨12, 2, 0, 1092920, 308844, 1713, 65536⟩
    (by decide) selected_cut_40227

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
