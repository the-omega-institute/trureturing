/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover355
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34180 : selected 9 ⟨883121, by decide⟩
    (prefixPartial 12 113005) = some ⟨12, 2, 0, 883121, 113005, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_113005_883121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113005 ⟨883121, by decide⟩ :=
  accepted_of_selected 12 113005 ⟨883121, by decide⟩ ⟨12, 2, 0, 883121, 113005, 2633, 65536⟩
    (by decide) selected_cut_34180

theorem selected_cut_34181 : selected 9 ⟨883156, by decide⟩
    (prefixPartial 12 113006) = some ⟨12, 2, 0, 883156, 113006, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_113006_883156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113006 ⟨883156, by decide⟩ :=
  accepted_of_selected 12 113006 ⟨883156, by decide⟩ ⟨12, 2, 0, 883156, 113006, 2713, 65536⟩
    (by decide) selected_cut_34181

theorem selected_cut_34182 : selected 9 ⟨883186, by decide⟩
    (prefixPartial 12 113007) = some ⟨12, 2, 0, 883186, 113007, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_113007_883186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113007 ⟨883186, by decide⟩ :=
  accepted_of_selected 12 113007 ⟨883186, by decide⟩ ⟨12, 2, 0, 883186, 113007, 2533, 65536⟩
    (by decide) selected_cut_34182

theorem unmarked_context_11_28251_883187 : frontier 10 ⟨883187, by decide⟩
    (prefixCache 11 28251) (prefixPartial 11 28251) = false := by
  decide +kernel

theorem node_context_11_28251_883187 : EJMOriginalGlobalDAGData.nodes 10 ⟨883187, by decide⟩ =
    .split (coordinate 11) (![⟨883082, by decide⟩,⟨883121, by decide⟩,⟨883156, by decide⟩,⟨883186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28251_883187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28251 ⟨883187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28251
    ⟨883187, by decide⟩ (by decide) (![⟨883082, by decide⟩,⟨883121, by decide⟩,⟨883156, by decide⟩,⟨883186, by decide⟩]) unmarked_context_11_28251_883187 node_context_11_28251_883187
  intro a
  fin_cases a
  · exact context_12_113004_883082
  · exact context_12_113005_883121
  · exact context_12_113006_883156
  · exact context_12_113007_883186

theorem unmarked_context_10_7062_883188 : frontier 11 ⟨883188, by decide⟩
    (prefixCache 10 7062) (prefixPartial 10 7062) = false := by
  decide +kernel

theorem node_context_10_7062_883188 : EJMOriginalGlobalDAGData.nodes 11 ⟨883188, by decide⟩ =
    .split (coordinate 10) (![⟨882948, by decide⟩,⟨883047, by decide⟩,⟨883048, by decide⟩,⟨883187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7062_883188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7062 ⟨883188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7062
    ⟨883188, by decide⟩ (by decide) (![⟨882948, by decide⟩,⟨883047, by decide⟩,⟨883048, by decide⟩,⟨883187, by decide⟩]) unmarked_context_10_7062_883188 node_context_10_7062_883188
  intro a
  fin_cases a
  · exact context_11_28248_882948
  · exact context_11_28249_883047
  · exact context_11_28250_883048
  · exact context_11_28251_883187

theorem selected_cut_34183 : selected 9 ⟨883215, by decide⟩
    (prefixPartial 12 113008) = some ⟨12, 2, 0, 883215, 113008, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_113008_883215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113008 ⟨883215, by decide⟩ :=
  accepted_of_selected 12 113008 ⟨883215, by decide⟩ ⟨12, 2, 0, 883215, 113008, 2469, 65536⟩
    (by decide) selected_cut_34183

theorem selected_cut_34184 : selected 9 ⟨883243, by decide⟩
    (prefixPartial 12 113009) = some ⟨12, 2, 0, 883243, 113009, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_113009_883243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113009 ⟨883243, by decide⟩ :=
  accepted_of_selected 12 113009 ⟨883243, by decide⟩ ⟨12, 2, 0, 883243, 113009, 2517, 65536⟩
    (by decide) selected_cut_34184

theorem selected_cut_34185 : selected 9 ⟨883280, by decide⟩
    (prefixPartial 12 113010) = some ⟨12, 2, 0, 883280, 113010, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_113010_883280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113010 ⟨883280, by decide⟩ :=
  accepted_of_selected 12 113010 ⟨883280, by decide⟩ ⟨12, 2, 0, 883280, 113010, 2569, 65536⟩
    (by decide) selected_cut_34185

theorem selected_cut_34186 : selected 9 ⟨883312, by decide⟩
    (prefixPartial 12 113011) = some ⟨12, 2, 0, 883312, 113011, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_113011_883312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113011 ⟨883312, by decide⟩ :=
  accepted_of_selected 12 113011 ⟨883312, by decide⟩ ⟨12, 2, 0, 883312, 113011, 2601, 65536⟩
    (by decide) selected_cut_34186

theorem unmarked_context_11_28252_883313 : frontier 10 ⟨883313, by decide⟩
    (prefixCache 11 28252) (prefixPartial 11 28252) = false := by
  decide +kernel

theorem node_context_11_28252_883313 : EJMOriginalGlobalDAGData.nodes 10 ⟨883313, by decide⟩ =
    .split (coordinate 11) (![⟨883215, by decide⟩,⟨883243, by decide⟩,⟨883280, by decide⟩,⟨883312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28252_883313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28252 ⟨883313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28252
    ⟨883313, by decide⟩ (by decide) (![⟨883215, by decide⟩,⟨883243, by decide⟩,⟨883280, by decide⟩,⟨883312, by decide⟩]) unmarked_context_11_28252_883313 node_context_11_28252_883313
  intro a
  fin_cases a
  · exact context_12_113008_883215
  · exact context_12_113009_883243
  · exact context_12_113010_883280
  · exact context_12_113011_883312

theorem selected_cut_34187 : selected 9 ⟨883334, by decide⟩
    (prefixPartial 12 113012) = some ⟨12, 2, 0, 883334, 113012, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_113012_883334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113012 ⟨883334, by decide⟩ :=
  accepted_of_selected 12 113012 ⟨883334, by decide⟩ ⟨12, 2, 0, 883334, 113012, 2017, 65536⟩
    (by decide) selected_cut_34187

theorem selected_cut_34188 : selected 9 ⟨883335, by decide⟩
    (prefixPartial 12 113013) = some ⟨12, 1, 0, 883335, 113013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113013_883335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113013 ⟨883335, by decide⟩ :=
  accepted_of_selected 12 113013 ⟨883335, by decide⟩ ⟨12, 1, 0, 883335, 113013, 1, 65536⟩
    (by decide) selected_cut_34188

theorem selected_cut_34189 : selected 9 ⟨883366, by decide⟩
    (prefixPartial 12 113014) = some ⟨12, 2, 0, 883366, 113014, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_113014_883366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113014 ⟨883366, by decide⟩ :=
  accepted_of_selected 12 113014 ⟨883366, by decide⟩ ⟨12, 2, 0, 883366, 113014, 2217, 65536⟩
    (by decide) selected_cut_34189

theorem selected_cut_34190 : selected 9 ⟨883392, by decide⟩
    (prefixPartial 12 113015) = some ⟨12, 2, 0, 883392, 113015, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_113015_883392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113015 ⟨883392, by decide⟩ :=
  accepted_of_selected 12 113015 ⟨883392, by decide⟩ ⟨12, 2, 0, 883392, 113015, 2065, 65536⟩
    (by decide) selected_cut_34190

theorem unmarked_context_11_28253_883393 : frontier 10 ⟨883393, by decide⟩
    (prefixCache 11 28253) (prefixPartial 11 28253) = false := by
  decide +kernel

theorem node_context_11_28253_883393 : EJMOriginalGlobalDAGData.nodes 10 ⟨883393, by decide⟩ =
    .split (coordinate 11) (![⟨883334, by decide⟩,⟨883335, by decide⟩,⟨883366, by decide⟩,⟨883392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28253_883393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28253 ⟨883393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28253
    ⟨883393, by decide⟩ (by decide) (![⟨883334, by decide⟩,⟨883335, by decide⟩,⟨883366, by decide⟩,⟨883392, by decide⟩]) unmarked_context_11_28253_883393 node_context_11_28253_883393
  intro a
  fin_cases a
  · exact context_12_113012_883334
  · exact context_12_113013_883335
  · exact context_12_113014_883366
  · exact context_12_113015_883392

theorem selected_cut_34191 : selected 9 ⟨883427, by decide⟩
    (prefixPartial 12 113016) = some ⟨12, 2, 0, 883427, 113016, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_113016_883427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113016 ⟨883427, by decide⟩ :=
  accepted_of_selected 12 113016 ⟨883427, by decide⟩ ⟨12, 2, 0, 883427, 113016, 2357, 65536⟩
    (by decide) selected_cut_34191

theorem selected_cut_34192 : selected 9 ⟨883456, by decide⟩
    (prefixPartial 12 113017) = some ⟨12, 2, 0, 883456, 113017, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_113017_883456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113017 ⟨883456, by decide⟩ :=
  accepted_of_selected 12 113017 ⟨883456, by decide⟩ ⟨12, 2, 0, 883456, 113017, 2425, 65536⟩
    (by decide) selected_cut_34192

theorem selected_cut_34193 : selected 9 ⟨883491, by decide⟩
    (prefixPartial 12 113018) = some ⟨12, 2, 0, 883491, 113018, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_113018_883491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113018 ⟨883491, by decide⟩ :=
  accepted_of_selected 12 113018 ⟨883491, by decide⟩ ⟨12, 2, 0, 883491, 113018, 2461, 65536⟩
    (by decide) selected_cut_34193

theorem selected_cut_34194 : selected 9 ⟨883520, by decide⟩
    (prefixPartial 12 113019) = some ⟨12, 2, 0, 883520, 113019, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_113019_883520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113019 ⟨883520, by decide⟩ :=
  accepted_of_selected 12 113019 ⟨883520, by decide⟩ ⟨12, 2, 0, 883520, 113019, 2277, 65536⟩
    (by decide) selected_cut_34194

theorem unmarked_context_11_28254_883521 : frontier 10 ⟨883521, by decide⟩
    (prefixCache 11 28254) (prefixPartial 11 28254) = false := by
  decide +kernel

theorem node_context_11_28254_883521 : EJMOriginalGlobalDAGData.nodes 10 ⟨883521, by decide⟩ =
    .split (coordinate 11) (![⟨883427, by decide⟩,⟨883456, by decide⟩,⟨883491, by decide⟩,⟨883520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28254_883521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28254 ⟨883521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28254
    ⟨883521, by decide⟩ (by decide) (![⟨883427, by decide⟩,⟨883456, by decide⟩,⟨883491, by decide⟩,⟨883520, by decide⟩]) unmarked_context_11_28254_883521 node_context_11_28254_883521
  intro a
  fin_cases a
  · exact context_12_113016_883427
  · exact context_12_113017_883456
  · exact context_12_113018_883491
  · exact context_12_113019_883520

theorem selected_cut_34195 : selected 9 ⟨883549, by decide⟩
    (prefixPartial 12 113020) = some ⟨12, 2, 0, 883549, 113020, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_113020_883549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113020 ⟨883549, by decide⟩ :=
  accepted_of_selected 12 113020 ⟨883549, by decide⟩ ⟨12, 2, 0, 883549, 113020, 2221, 65536⟩
    (by decide) selected_cut_34195

theorem selected_cut_34196 : selected 9 ⟨883580, by decide⟩
    (prefixPartial 12 113021) = some ⟨12, 2, 0, 883580, 113021, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_113021_883580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113021 ⟨883580, by decide⟩ :=
  accepted_of_selected 12 113021 ⟨883580, by decide⟩ ⟨12, 2, 0, 883580, 113021, 2341, 65536⟩
    (by decide) selected_cut_34196

theorem selected_cut_34197 : selected 9 ⟨883614, by decide⟩
    (prefixPartial 12 113022) = some ⟨12, 2, 0, 883614, 113022, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_113022_883614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113022 ⟨883614, by decide⟩ :=
  accepted_of_selected 12 113022 ⟨883614, by decide⟩ ⟨12, 2, 0, 883614, 113022, 2313, 65536⟩
    (by decide) selected_cut_34197

theorem selected_cut_34198 : selected 9 ⟨883642, by decide⟩
    (prefixPartial 12 113023) = some ⟨12, 2, 0, 883642, 113023, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_113023_883642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113023 ⟨883642, by decide⟩ :=
  accepted_of_selected 12 113023 ⟨883642, by decide⟩ ⟨12, 2, 0, 883642, 113023, 2125, 65536⟩
    (by decide) selected_cut_34198

theorem unmarked_context_11_28255_883643 : frontier 10 ⟨883643, by decide⟩
    (prefixCache 11 28255) (prefixPartial 11 28255) = false := by
  decide +kernel

theorem node_context_11_28255_883643 : EJMOriginalGlobalDAGData.nodes 10 ⟨883643, by decide⟩ =
    .split (coordinate 11) (![⟨883549, by decide⟩,⟨883580, by decide⟩,⟨883614, by decide⟩,⟨883642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28255_883643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28255 ⟨883643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28255
    ⟨883643, by decide⟩ (by decide) (![⟨883549, by decide⟩,⟨883580, by decide⟩,⟨883614, by decide⟩,⟨883642, by decide⟩]) unmarked_context_11_28255_883643 node_context_11_28255_883643
  intro a
  fin_cases a
  · exact context_12_113020_883549
  · exact context_12_113021_883580
  · exact context_12_113022_883614
  · exact context_12_113023_883642

theorem unmarked_context_10_7063_883644 : frontier 11 ⟨883644, by decide⟩
    (prefixCache 10 7063) (prefixPartial 10 7063) = false := by
  decide +kernel

theorem node_context_10_7063_883644 : EJMOriginalGlobalDAGData.nodes 11 ⟨883644, by decide⟩ =
    .split (coordinate 10) (![⟨883313, by decide⟩,⟨883393, by decide⟩,⟨883521, by decide⟩,⟨883643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7063_883644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7063 ⟨883644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7063
    ⟨883644, by decide⟩ (by decide) (![⟨883313, by decide⟩,⟨883393, by decide⟩,⟨883521, by decide⟩,⟨883643, by decide⟩]) unmarked_context_10_7063_883644 node_context_10_7063_883644
  intro a
  fin_cases a
  · exact context_11_28252_883313
  · exact context_11_28253_883393
  · exact context_11_28254_883521
  · exact context_11_28255_883643

theorem unmarked_context_9_1765_883645 : frontier 12 ⟨883645, by decide⟩
    (prefixCache 9 1765) (prefixPartial 9 1765) = false := by
  decide +kernel

theorem node_context_9_1765_883645 : EJMOriginalGlobalDAGData.nodes 12 ⟨883645, by decide⟩ =
    .split (coordinate 9) (![⟨882199, by decide⟩,⟨882817, by decide⟩,⟨883188, by decide⟩,⟨883644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1765_883645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1765 ⟨883645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1765
    ⟨883645, by decide⟩ (by decide) (![⟨882199, by decide⟩,⟨882817, by decide⟩,⟨883188, by decide⟩,⟨883644, by decide⟩]) unmarked_context_9_1765_883645 node_context_9_1765_883645
  intro a
  fin_cases a
  · exact context_10_7060_882199
  · exact context_10_7061_882817
  · exact context_10_7062_883188
  · exact context_10_7063_883644

theorem selected_cut_34199 : selected 9 ⟨883666, by decide⟩
    (prefixPartial 12 113024) = some ⟨12, 2, 0, 883666, 113024, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_113024_883666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113024 ⟨883666, by decide⟩ :=
  accepted_of_selected 12 113024 ⟨883666, by decide⟩ ⟨12, 2, 0, 883666, 113024, 1877, 65536⟩
    (by decide) selected_cut_34199

theorem selected_cut_34200 : selected 9 ⟨883690, by decide⟩
    (prefixPartial 12 113025) = some ⟨12, 2, 0, 883690, 113025, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_113025_883690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113025 ⟨883690, by decide⟩ :=
  accepted_of_selected 12 113025 ⟨883690, by decide⟩ ⟨12, 2, 0, 883690, 113025, 1981, 65536⟩
    (by decide) selected_cut_34200

theorem selected_cut_34201 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 113026) = some ⟨12, 1, 0, 813440, 113026, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113026_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113026 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 113026 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 113026, 1, 65536⟩
    (by decide) selected_cut_34201

theorem selected_cut_34202 : selected 9 ⟨883718, by decide⟩
    (prefixPartial 12 113027) = some ⟨12, 2, 0, 883718, 113027, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_113027_883718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113027 ⟨883718, by decide⟩ :=
  accepted_of_selected 12 113027 ⟨883718, by decide⟩ ⟨12, 2, 0, 883718, 113027, 2069, 65536⟩
    (by decide) selected_cut_34202

theorem unmarked_context_11_28256_883719 : frontier 10 ⟨883719, by decide⟩
    (prefixCache 11 28256) (prefixPartial 11 28256) = false := by
  decide +kernel

theorem node_context_11_28256_883719 : EJMOriginalGlobalDAGData.nodes 10 ⟨883719, by decide⟩ =
    .split (coordinate 11) (![⟨883666, by decide⟩,⟨883690, by decide⟩,⟨813440, by decide⟩,⟨883718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28256_883719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28256 ⟨883719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28256
    ⟨883719, by decide⟩ (by decide) (![⟨883666, by decide⟩,⟨883690, by decide⟩,⟨813440, by decide⟩,⟨883718, by decide⟩]) unmarked_context_11_28256_883719 node_context_11_28256_883719
  intro a
  fin_cases a
  · exact context_12_113024_883666
  · exact context_12_113025_883690
  · exact context_12_113026_813440
  · exact context_12_113027_883718

theorem selected_cut_34203 : selected 10 ⟨883767, by decide⟩
    (prefixPartial 11 28257) = some ⟨11, 2, 0, 883767, 28257, 3129, 262144⟩ := by
  decide +kernel

theorem context_11_28257_883767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28257 ⟨883767, by decide⟩ :=
  accepted_of_selected 11 28257 ⟨883767, by decide⟩ ⟨11, 2, 0, 883767, 28257, 3129, 262144⟩
    (by decide) selected_cut_34203

theorem selected_cut_34204 : selected 9 ⟨883802, by decide⟩
    (prefixPartial 12 113032) = some ⟨12, 2, 0, 883802, 113032, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_113032_883802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113032 ⟨883802, by decide⟩ :=
  accepted_of_selected 12 113032 ⟨883802, by decide⟩ ⟨12, 2, 0, 883802, 113032, 1849, 65536⟩
    (by decide) selected_cut_34204

theorem selected_cut_34205 : selected 9 ⟨883835, by decide⟩
    (prefixPartial 12 113033) = some ⟨12, 2, 0, 883835, 113033, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_113033_883835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113033 ⟨883835, by decide⟩ :=
  accepted_of_selected 12 113033 ⟨883835, by decide⟩ ⟨12, 2, 0, 883835, 113033, 1949, 65536⟩
    (by decide) selected_cut_34205

theorem selected_cut_34206 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 113034) = some ⟨12, 1, 0, 813440, 113034, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113034_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113034 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 113034 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 113034, 1, 65536⟩
    (by decide) selected_cut_34206

theorem selected_cut_34207 : selected 9 ⟨883863, by decide⟩
    (prefixPartial 12 113035) = some ⟨12, 2, 0, 883863, 113035, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_113035_883863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113035 ⟨883863, by decide⟩ :=
  accepted_of_selected 12 113035 ⟨883863, by decide⟩ ⟨12, 2, 0, 883863, 113035, 1897, 65536⟩
    (by decide) selected_cut_34207

theorem unmarked_context_11_28258_883864 : frontier 10 ⟨883864, by decide⟩
    (prefixCache 11 28258) (prefixPartial 11 28258) = false := by
  decide +kernel

theorem node_context_11_28258_883864 : EJMOriginalGlobalDAGData.nodes 10 ⟨883864, by decide⟩ =
    .split (coordinate 11) (![⟨883802, by decide⟩,⟨883835, by decide⟩,⟨813440, by decide⟩,⟨883863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28258_883864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28258 ⟨883864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28258
    ⟨883864, by decide⟩ (by decide) (![⟨883802, by decide⟩,⟨883835, by decide⟩,⟨813440, by decide⟩,⟨883863, by decide⟩]) unmarked_context_11_28258_883864 node_context_11_28258_883864
  intro a
  fin_cases a
  · exact context_12_113032_883802
  · exact context_12_113033_883835
  · exact context_12_113034_813440
  · exact context_12_113035_883863

theorem selected_cut_34208 : selected 9 ⟨883889, by decide⟩
    (prefixPartial 12 113036) = some ⟨12, 2, 0, 883889, 113036, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_113036_883889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113036 ⟨883889, by decide⟩ :=
  accepted_of_selected 12 113036 ⟨883889, by decide⟩ ⟨12, 2, 0, 883889, 113036, 1757, 65536⟩
    (by decide) selected_cut_34208

theorem selected_cut_34209 : selected 9 ⟨883916, by decide⟩
    (prefixPartial 12 113037) = some ⟨12, 2, 0, 883916, 113037, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_113037_883916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113037 ⟨883916, by decide⟩ :=
  accepted_of_selected 12 113037 ⟨883916, by decide⟩ ⟨12, 2, 0, 883916, 113037, 1845, 65536⟩
    (by decide) selected_cut_34209

theorem selected_cut_34210 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 113038) = some ⟨12, 1, 0, 813440, 113038, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113038_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113038 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 113038 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 113038, 1, 65536⟩
    (by decide) selected_cut_34210

theorem selected_cut_34211 : selected 9 ⟨883943, by decide⟩
    (prefixPartial 12 113039) = some ⟨12, 2, 0, 883943, 113039, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_113039_883943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113039 ⟨883943, by decide⟩ :=
  accepted_of_selected 12 113039 ⟨883943, by decide⟩ ⟨12, 2, 0, 883943, 113039, 1761, 65536⟩
    (by decide) selected_cut_34211

theorem unmarked_context_11_28259_883944 : frontier 10 ⟨883944, by decide⟩
    (prefixCache 11 28259) (prefixPartial 11 28259) = false := by
  decide +kernel

theorem node_context_11_28259_883944 : EJMOriginalGlobalDAGData.nodes 10 ⟨883944, by decide⟩ =
    .split (coordinate 11) (![⟨883889, by decide⟩,⟨883916, by decide⟩,⟨813440, by decide⟩,⟨883943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28259_883944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28259 ⟨883944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28259
    ⟨883944, by decide⟩ (by decide) (![⟨883889, by decide⟩,⟨883916, by decide⟩,⟨813440, by decide⟩,⟨883943, by decide⟩]) unmarked_context_11_28259_883944 node_context_11_28259_883944
  intro a
  fin_cases a
  · exact context_12_113036_883889
  · exact context_12_113037_883916
  · exact context_12_113038_813440
  · exact context_12_113039_883943

theorem unmarked_context_10_7064_883945 : frontier 11 ⟨883945, by decide⟩
    (prefixCache 10 7064) (prefixPartial 10 7064) = false := by
  decide +kernel

theorem node_context_10_7064_883945 : EJMOriginalGlobalDAGData.nodes 11 ⟨883945, by decide⟩ =
    .split (coordinate 10) (![⟨883719, by decide⟩,⟨883767, by decide⟩,⟨883864, by decide⟩,⟨883944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7064_883945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7064 ⟨883945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7064
    ⟨883945, by decide⟩ (by decide) (![⟨883719, by decide⟩,⟨883767, by decide⟩,⟨883864, by decide⟩,⟨883944, by decide⟩]) unmarked_context_10_7064_883945 node_context_10_7064_883945
  intro a
  fin_cases a
  · exact context_11_28256_883719
  · exact context_11_28257_883767
  · exact context_11_28258_883864
  · exact context_11_28259_883944

theorem selected_cut_34212 : selected 9 ⟨883965, by decide⟩
    (prefixPartial 12 113040) = some ⟨12, 2, 0, 883965, 113040, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_113040_883965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113040 ⟨883965, by decide⟩ :=
  accepted_of_selected 12 113040 ⟨883965, by decide⟩ ⟨12, 2, 0, 883965, 113040, 1677, 65536⟩
    (by decide) selected_cut_34212

theorem selected_cut_34213 : selected 9 ⟨883988, by decide⟩
    (prefixPartial 12 113041) = some ⟨12, 2, 0, 883988, 113041, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_113041_883988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113041 ⟨883988, by decide⟩ :=
  accepted_of_selected 12 113041 ⟨883988, by decide⟩ ⟨12, 2, 0, 883988, 113041, 1901, 65536⟩
    (by decide) selected_cut_34213

theorem selected_cut_34214 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 113042) = some ⟨12, 1, 0, 813979, 113042, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113042_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113042 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 113042 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 113042, 1, 65536⟩
    (by decide) selected_cut_34214

theorem selected_cut_34215 : selected 9 ⟨884016, by decide⟩
    (prefixPartial 12 113043) = some ⟨12, 2, 0, 884016, 113043, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_113043_884016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113043 ⟨884016, by decide⟩ :=
  accepted_of_selected 12 113043 ⟨884016, by decide⟩ ⟨12, 2, 0, 884016, 113043, 1841, 65536⟩
    (by decide) selected_cut_34215

theorem unmarked_context_11_28260_884017 : frontier 10 ⟨884017, by decide⟩
    (prefixCache 11 28260) (prefixPartial 11 28260) = false := by
  decide +kernel

theorem node_context_11_28260_884017 : EJMOriginalGlobalDAGData.nodes 10 ⟨884017, by decide⟩ =
    .split (coordinate 11) (![⟨883965, by decide⟩,⟨883988, by decide⟩,⟨813979, by decide⟩,⟨884016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28260_884017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28260 ⟨884017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28260
    ⟨884017, by decide⟩ (by decide) (![⟨883965, by decide⟩,⟨883988, by decide⟩,⟨813979, by decide⟩,⟨884016, by decide⟩]) unmarked_context_11_28260_884017 node_context_11_28260_884017
  intro a
  fin_cases a
  · exact context_12_113040_883965
  · exact context_12_113041_883988
  · exact context_12_113042_813979
  · exact context_12_113043_884016

theorem selected_cut_34216 : selected 10 ⟨884051, by decide⟩
    (prefixPartial 11 28261) = some ⟨11, 2, 0, 884051, 28261, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_28261_884051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28261 ⟨884051, by decide⟩ :=
  accepted_of_selected 11 28261 ⟨884051, by decide⟩ ⟨11, 2, 0, 884051, 28261, 2433, 262144⟩
    (by decide) selected_cut_34216

theorem selected_cut_34217 : selected 9 ⟨884069, by decide⟩
    (prefixPartial 12 113048) = some ⟨12, 2, 0, 884069, 113048, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_113048_884069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113048 ⟨884069, by decide⟩ :=
  accepted_of_selected 12 113048 ⟨884069, by decide⟩ ⟨12, 2, 0, 884069, 113048, 1445, 65536⟩
    (by decide) selected_cut_34217

theorem selected_cut_34218 : selected 9 ⟨884085, by decide⟩
    (prefixPartial 12 113049) = some ⟨12, 2, 0, 884085, 113049, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_113049_884085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113049 ⟨884085, by decide⟩ :=
  accepted_of_selected 12 113049 ⟨884085, by decide⟩ ⟨12, 2, 0, 884085, 113049, 1597, 65536⟩
    (by decide) selected_cut_34218

theorem selected_cut_34219 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 113050) = some ⟨12, 1, 0, 813979, 113050, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113050_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113050 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 113050 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 113050, 1, 65536⟩
    (by decide) selected_cut_34219

theorem selected_cut_34220 : selected 9 ⟨884104, by decide⟩
    (prefixPartial 12 113051) = some ⟨12, 2, 0, 884104, 113051, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_113051_884104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113051 ⟨884104, by decide⟩ :=
  accepted_of_selected 12 113051 ⟨884104, by decide⟩ ⟨12, 2, 0, 884104, 113051, 1473, 65536⟩
    (by decide) selected_cut_34220

theorem unmarked_context_11_28262_884105 : frontier 10 ⟨884105, by decide⟩
    (prefixCache 11 28262) (prefixPartial 11 28262) = false := by
  decide +kernel

theorem node_context_11_28262_884105 : EJMOriginalGlobalDAGData.nodes 10 ⟨884105, by decide⟩ =
    .split (coordinate 11) (![⟨884069, by decide⟩,⟨884085, by decide⟩,⟨813979, by decide⟩,⟨884104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28262_884105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28262 ⟨884105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28262
    ⟨884105, by decide⟩ (by decide) (![⟨884069, by decide⟩,⟨884085, by decide⟩,⟨813979, by decide⟩,⟨884104, by decide⟩]) unmarked_context_11_28262_884105 node_context_11_28262_884105
  intro a
  fin_cases a
  · exact context_12_113048_884069
  · exact context_12_113049_884085
  · exact context_12_113050_813979
  · exact context_12_113051_884104

theorem selected_cut_34221 : selected 9 ⟨884124, by decide⟩
    (prefixPartial 12 113052) = some ⟨12, 2, 0, 884124, 113052, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_113052_884124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113052 ⟨884124, by decide⟩ :=
  accepted_of_selected 12 113052 ⟨884124, by decide⟩ ⟨12, 2, 0, 884124, 113052, 1453, 65536⟩
    (by decide) selected_cut_34221

theorem selected_cut_34222 : selected 9 ⟨884143, by decide⟩
    (prefixPartial 12 113053) = some ⟨12, 2, 0, 884143, 113053, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_113053_884143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113053 ⟨884143, by decide⟩ :=
  accepted_of_selected 12 113053 ⟨884143, by decide⟩ ⟨12, 2, 0, 884143, 113053, 1613, 65536⟩
    (by decide) selected_cut_34222

theorem selected_cut_34223 : selected 9 ⟨813889, by decide⟩
    (prefixPartial 12 113054) = some ⟨12, 1, 0, 813889, 113054, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113054_813889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113054 ⟨813889, by decide⟩ :=
  accepted_of_selected 12 113054 ⟨813889, by decide⟩ ⟨12, 1, 0, 813889, 113054, 1, 65536⟩
    (by decide) selected_cut_34223

theorem selected_cut_34224 : selected 9 ⟨884161, by decide⟩
    (prefixPartial 12 113055) = some ⟨12, 2, 0, 884161, 113055, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_113055_884161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113055 ⟨884161, by decide⟩ :=
  accepted_of_selected 12 113055 ⟨884161, by decide⟩ ⟨12, 2, 0, 884161, 113055, 1441, 65536⟩
    (by decide) selected_cut_34224

theorem unmarked_context_11_28263_884162 : frontier 10 ⟨884162, by decide⟩
    (prefixCache 11 28263) (prefixPartial 11 28263) = false := by
  decide +kernel

theorem node_context_11_28263_884162 : EJMOriginalGlobalDAGData.nodes 10 ⟨884162, by decide⟩ =
    .split (coordinate 11) (![⟨884124, by decide⟩,⟨884143, by decide⟩,⟨813889, by decide⟩,⟨884161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28263_884162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28263 ⟨884162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28263
    ⟨884162, by decide⟩ (by decide) (![⟨884124, by decide⟩,⟨884143, by decide⟩,⟨813889, by decide⟩,⟨884161, by decide⟩]) unmarked_context_11_28263_884162 node_context_11_28263_884162
  intro a
  fin_cases a
  · exact context_12_113052_884124
  · exact context_12_113053_884143
  · exact context_12_113054_813889
  · exact context_12_113055_884161

theorem unmarked_context_10_7065_884163 : frontier 11 ⟨884163, by decide⟩
    (prefixCache 10 7065) (prefixPartial 10 7065) = false := by
  decide +kernel

theorem node_context_10_7065_884163 : EJMOriginalGlobalDAGData.nodes 11 ⟨884163, by decide⟩ =
    .split (coordinate 10) (![⟨884017, by decide⟩,⟨884051, by decide⟩,⟨884105, by decide⟩,⟨884162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7065_884163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7065 ⟨884163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7065
    ⟨884163, by decide⟩ (by decide) (![⟨884017, by decide⟩,⟨884051, by decide⟩,⟨884105, by decide⟩,⟨884162, by decide⟩]) unmarked_context_10_7065_884163 node_context_10_7065_884163
  intro a
  fin_cases a
  · exact context_11_28260_884017
  · exact context_11_28261_884051
  · exact context_11_28262_884105
  · exact context_11_28263_884162

theorem selected_cut_34225 : selected 10 ⟨884203, by decide⟩
    (prefixPartial 11 28264) = some ⟨11, 2, 0, 884203, 28264, 3505, 262144⟩ := by
  decide +kernel

theorem context_11_28264_884203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28264 ⟨884203, by decide⟩ :=
  accepted_of_selected 11 28264 ⟨884203, by decide⟩ ⟨11, 2, 0, 884203, 28264, 3505, 262144⟩
    (by decide) selected_cut_34225

theorem selected_cut_34226 : selected 10 ⟨884228, by decide⟩
    (prefixPartial 11 28265) = some ⟨11, 2, 0, 884228, 28265, 1833, 262144⟩ := by
  decide +kernel

theorem context_11_28265_884228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28265 ⟨884228, by decide⟩ :=
  accepted_of_selected 11 28265 ⟨884228, by decide⟩ ⟨11, 2, 0, 884228, 28265, 1833, 262144⟩
    (by decide) selected_cut_34226

theorem selected_cut_34227 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 28266) = some ⟨11, 1, 0, 479708, 28266, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28266_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28266 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 28266 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 28266, 1, 262144⟩
    (by decide) selected_cut_34227

theorem selected_cut_34228 : selected 10 ⟨884273, by decide⟩
    (prefixPartial 11 28267) = some ⟨11, 2, 0, 884273, 28267, 3485, 262144⟩ := by
  decide +kernel

theorem context_11_28267_884273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28267 ⟨884273, by decide⟩ :=
  accepted_of_selected 11 28267 ⟨884273, by decide⟩ ⟨11, 2, 0, 884273, 28267, 3485, 262144⟩
    (by decide) selected_cut_34228

theorem unmarked_context_10_7066_884274 : frontier 11 ⟨884274, by decide⟩
    (prefixCache 10 7066) (prefixPartial 10 7066) = false := by
  decide +kernel

theorem node_context_10_7066_884274 : EJMOriginalGlobalDAGData.nodes 11 ⟨884274, by decide⟩ =
    .split (coordinate 10) (![⟨884203, by decide⟩,⟨884228, by decide⟩,⟨479708, by decide⟩,⟨884273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7066_884274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7066 ⟨884274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7066
    ⟨884274, by decide⟩ (by decide) (![⟨884203, by decide⟩,⟨884228, by decide⟩,⟨479708, by decide⟩,⟨884273, by decide⟩]) unmarked_context_10_7066_884274 node_context_10_7066_884274
  intro a
  fin_cases a
  · exact context_11_28264_884203
  · exact context_11_28265_884228
  · exact context_11_28266_479708
  · exact context_11_28267_884273

theorem selected_cut_34229 : selected 10 ⟨884305, by decide⟩
    (prefixPartial 11 28268) = some ⟨11, 2, 0, 884305, 28268, 2965, 262144⟩ := by
  decide +kernel

theorem context_11_28268_884305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28268 ⟨884305, by decide⟩ :=
  accepted_of_selected 11 28268 ⟨884305, by decide⟩ ⟨11, 2, 0, 884305, 28268, 2965, 262144⟩
    (by decide) selected_cut_34229

theorem selected_cut_34230 : selected 10 ⟨884320, by decide⟩
    (prefixPartial 11 28269) = some ⟨11, 2, 0, 884320, 28269, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_28269_884320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28269 ⟨884320, by decide⟩ :=
  accepted_of_selected 11 28269 ⟨884320, by decide⟩ ⟨11, 2, 0, 884320, 28269, 1549, 262144⟩
    (by decide) selected_cut_34230

theorem selected_cut_34231 : selected 10 ⟨884354, by decide⟩
    (prefixPartial 11 28270) = some ⟨11, 2, 0, 884354, 28270, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_28270_884354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28270 ⟨884354, by decide⟩ :=
  accepted_of_selected 11 28270 ⟨884354, by decide⟩ ⟨11, 2, 0, 884354, 28270, 2461, 262144⟩
    (by decide) selected_cut_34231

theorem selected_cut_34232 : selected 10 ⟨884389, by decide⟩
    (prefixPartial 11 28271) = some ⟨11, 2, 0, 884389, 28271, 2653, 262144⟩ := by
  decide +kernel

theorem context_11_28271_884389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28271 ⟨884389, by decide⟩ :=
  accepted_of_selected 11 28271 ⟨884389, by decide⟩ ⟨11, 2, 0, 884389, 28271, 2653, 262144⟩
    (by decide) selected_cut_34232

theorem unmarked_context_10_7067_884390 : frontier 11 ⟨884390, by decide⟩
    (prefixCache 10 7067) (prefixPartial 10 7067) = false := by
  decide +kernel

theorem node_context_10_7067_884390 : EJMOriginalGlobalDAGData.nodes 11 ⟨884390, by decide⟩ =
    .split (coordinate 10) (![⟨884305, by decide⟩,⟨884320, by decide⟩,⟨884354, by decide⟩,⟨884389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7067_884390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7067 ⟨884390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7067
    ⟨884390, by decide⟩ (by decide) (![⟨884305, by decide⟩,⟨884320, by decide⟩,⟨884354, by decide⟩,⟨884389, by decide⟩]) unmarked_context_10_7067_884390 node_context_10_7067_884390
  intro a
  fin_cases a
  · exact context_11_28268_884305
  · exact context_11_28269_884320
  · exact context_11_28270_884354
  · exact context_11_28271_884389

theorem unmarked_context_9_1766_884391 : frontier 12 ⟨884391, by decide⟩
    (prefixCache 9 1766) (prefixPartial 9 1766) = false := by
  decide +kernel

theorem node_context_9_1766_884391 : EJMOriginalGlobalDAGData.nodes 12 ⟨884391, by decide⟩ =
    .split (coordinate 9) (![⟨883945, by decide⟩,⟨884163, by decide⟩,⟨884274, by decide⟩,⟨884390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1766_884391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1766 ⟨884391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1766
    ⟨884391, by decide⟩ (by decide) (![⟨883945, by decide⟩,⟨884163, by decide⟩,⟨884274, by decide⟩,⟨884390, by decide⟩]) unmarked_context_9_1766_884391 node_context_9_1766_884391
  intro a
  fin_cases a
  · exact context_10_7064_883945
  · exact context_10_7065_884163
  · exact context_10_7066_884274
  · exact context_10_7067_884390

theorem selected_cut_34233 : selected 10 ⟨884421, by decide⟩
    (prefixPartial 11 28272) = some ⟨11, 2, 0, 884421, 28272, 3205, 262144⟩ := by
  decide +kernel

theorem context_11_28272_884421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28272 ⟨884421, by decide⟩ :=
  accepted_of_selected 11 28272 ⟨884421, by decide⟩ ⟨11, 2, 0, 884421, 28272, 3205, 262144⟩
    (by decide) selected_cut_34233

theorem selected_cut_34234 : selected 10 ⟨884481, by decide⟩
    (prefixPartial 11 28273) = some ⟨11, 2, 0, 884481, 28273, 2629, 262144⟩ := by
  decide +kernel

theorem context_11_28273_884481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28273 ⟨884481, by decide⟩ :=
  accepted_of_selected 11 28273 ⟨884481, by decide⟩ ⟨11, 2, 0, 884481, 28273, 2629, 262144⟩
    (by decide) selected_cut_34234

theorem selected_cut_34235 : selected 10 ⟨884506, by decide⟩
    (prefixPartial 11 28274) = some ⟨11, 2, 0, 884506, 28274, 2969, 262144⟩ := by
  decide +kernel

theorem context_11_28274_884506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28274 ⟨884506, by decide⟩ :=
  accepted_of_selected 11 28274 ⟨884506, by decide⟩ ⟨11, 2, 0, 884506, 28274, 2969, 262144⟩
    (by decide) selected_cut_34235

theorem selected_cut_34236 : selected 10 ⟨884555, by decide⟩
    (prefixPartial 11 28275) = some ⟨11, 2, 0, 884555, 28275, 2993, 262144⟩ := by
  decide +kernel

theorem context_11_28275_884555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28275 ⟨884555, by decide⟩ :=
  accepted_of_selected 11 28275 ⟨884555, by decide⟩ ⟨11, 2, 0, 884555, 28275, 2993, 262144⟩
    (by decide) selected_cut_34236

theorem unmarked_context_10_7068_884556 : frontier 11 ⟨884556, by decide⟩
    (prefixCache 10 7068) (prefixPartial 10 7068) = false := by
  decide +kernel

theorem node_context_10_7068_884556 : EJMOriginalGlobalDAGData.nodes 11 ⟨884556, by decide⟩ =
    .split (coordinate 10) (![⟨884421, by decide⟩,⟨884481, by decide⟩,⟨884506, by decide⟩,⟨884555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7068_884556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7068 ⟨884556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7068
    ⟨884556, by decide⟩ (by decide) (![⟨884421, by decide⟩,⟨884481, by decide⟩,⟨884506, by decide⟩,⟨884555, by decide⟩]) unmarked_context_10_7068_884556 node_context_10_7068_884556
  intro a
  fin_cases a
  · exact context_11_28272_884421
  · exact context_11_28273_884481
  · exact context_11_28274_884506
  · exact context_11_28275_884555

theorem selected_cut_34237 : selected 10 ⟨884576, by decide⟩
    (prefixPartial 11 28276) = some ⟨11, 2, 0, 884576, 28276, 2589, 262144⟩ := by
  decide +kernel

theorem context_11_28276_884576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28276 ⟨884576, by decide⟩ :=
  accepted_of_selected 11 28276 ⟨884576, by decide⟩ ⟨11, 2, 0, 884576, 28276, 2589, 262144⟩
    (by decide) selected_cut_34237

theorem selected_cut_34238 : selected 10 ⟨884593, by decide⟩
    (prefixPartial 11 28277) = some ⟨11, 2, 0, 884593, 28277, 1633, 262144⟩ := by
  decide +kernel

theorem context_11_28277_884593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28277 ⟨884593, by decide⟩ :=
  accepted_of_selected 11 28277 ⟨884593, by decide⟩ ⟨11, 2, 0, 884593, 28277, 1633, 262144⟩
    (by decide) selected_cut_34238

theorem selected_cut_34239 : selected 10 ⟨884613, by decide⟩
    (prefixPartial 11 28278) = some ⟨11, 2, 0, 884613, 28278, 1945, 262144⟩ := by
  decide +kernel

theorem context_11_28278_884613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28278 ⟨884613, by decide⟩ :=
  accepted_of_selected 11 28278 ⟨884613, by decide⟩ ⟨11, 2, 0, 884613, 28278, 1945, 262144⟩
    (by decide) selected_cut_34239

theorem selected_cut_34240 : selected 10 ⟨884641, by decide⟩
    (prefixPartial 11 28279) = some ⟨11, 2, 0, 884641, 28279, 1865, 262144⟩ := by
  decide +kernel

theorem context_11_28279_884641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28279 ⟨884641, by decide⟩ :=
  accepted_of_selected 11 28279 ⟨884641, by decide⟩ ⟨11, 2, 0, 884641, 28279, 1865, 262144⟩
    (by decide) selected_cut_34240

theorem unmarked_context_10_7069_884642 : frontier 11 ⟨884642, by decide⟩
    (prefixCache 10 7069) (prefixPartial 10 7069) = false := by
  decide +kernel

theorem node_context_10_7069_884642 : EJMOriginalGlobalDAGData.nodes 11 ⟨884642, by decide⟩ =
    .split (coordinate 10) (![⟨884576, by decide⟩,⟨884593, by decide⟩,⟨884613, by decide⟩,⟨884641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7069_884642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7069 ⟨884642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7069
    ⟨884642, by decide⟩ (by decide) (![⟨884576, by decide⟩,⟨884593, by decide⟩,⟨884613, by decide⟩,⟨884641, by decide⟩]) unmarked_context_10_7069_884642 node_context_10_7069_884642
  intro a
  fin_cases a
  · exact context_11_28276_884576
  · exact context_11_28277_884593
  · exact context_11_28278_884613
  · exact context_11_28279_884641

theorem selected_cut_34241 : selected 11 ⟨884691, by decide⟩
    (prefixPartial 10 7070) = some ⟨10, 2, 0, 884691, 7070, 3229, 1048576⟩ := by
  decide +kernel

theorem context_10_7070_884691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7070 ⟨884691, by decide⟩ :=
  accepted_of_selected 10 7070 ⟨884691, by decide⟩ ⟨10, 2, 0, 884691, 7070, 3229, 1048576⟩
    (by decide) selected_cut_34241

theorem selected_cut_34242 : selected 11 ⟨884721, by decide⟩
    (prefixPartial 10 7071) = some ⟨10, 2, 0, 884721, 7071, 1429, 1048576⟩ := by
  decide +kernel

theorem context_10_7071_884721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7071 ⟨884721, by decide⟩ :=
  accepted_of_selected 10 7071 ⟨884721, by decide⟩ ⟨10, 2, 0, 884721, 7071, 1429, 1048576⟩
    (by decide) selected_cut_34242

theorem unmarked_context_9_1767_884722 : frontier 12 ⟨884722, by decide⟩
    (prefixCache 9 1767) (prefixPartial 9 1767) = false := by
  decide +kernel

theorem node_context_9_1767_884722 : EJMOriginalGlobalDAGData.nodes 12 ⟨884722, by decide⟩ =
    .split (coordinate 9) (![⟨884556, by decide⟩,⟨884642, by decide⟩,⟨884691, by decide⟩,⟨884721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1767_884722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1767 ⟨884722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1767
    ⟨884722, by decide⟩ (by decide) (![⟨884556, by decide⟩,⟨884642, by decide⟩,⟨884691, by decide⟩,⟨884721, by decide⟩]) unmarked_context_9_1767_884722 node_context_9_1767_884722
  intro a
  fin_cases a
  · exact context_10_7068_884556
  · exact context_10_7069_884642
  · exact context_10_7070_884691
  · exact context_10_7071_884721

theorem unmarked_context_8_441_884723 : frontier 13 ⟨884723, by decide⟩
    (prefixCache 8 441) (prefixPartial 8 441) = false := by
  decide +kernel

theorem node_context_8_441_884723 : EJMOriginalGlobalDAGData.nodes 13 ⟨884723, by decide⟩ =
    .split (coordinate 8) (![⟨881476, by decide⟩,⟨883645, by decide⟩,⟨884391, by decide⟩,⟨884722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_441_884723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 441 ⟨884723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 441
    ⟨884723, by decide⟩ (by decide) (![⟨881476, by decide⟩,⟨883645, by decide⟩,⟨884391, by decide⟩,⟨884722, by decide⟩]) unmarked_context_8_441_884723 node_context_8_441_884723
  intro a
  fin_cases a
  · exact context_9_1764_881476
  · exact context_9_1765_883645
  · exact context_9_1766_884391
  · exact context_9_1767_884722

theorem selected_cut_34243 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 28288) = some ⟨11, 1, 0, 434745, 28288, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28288_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28288 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 28288 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 28288, 1, 262144⟩
    (by decide) selected_cut_34243

theorem selected_cut_34244 : selected 10 ⟨884883, by decide⟩
    (prefixPartial 11 28289) = some ⟨11, 2, 0, 884883, 28289, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_28289_884883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28289 ⟨884883, by decide⟩ :=
  accepted_of_selected 11 28289 ⟨884883, by decide⟩ ⟨11, 2, 0, 884883, 28289, 3417, 262144⟩
    (by decide) selected_cut_34244

theorem selected_cut_34245 : selected 10 ⟨764169, by decide⟩
    (prefixPartial 11 28290) = some ⟨11, 1, 0, 764169, 28290, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28290_764169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28290 ⟨764169, by decide⟩ :=
  accepted_of_selected 11 28290 ⟨764169, by decide⟩ ⟨11, 1, 0, 764169, 28290, 1, 262144⟩
    (by decide) selected_cut_34245

theorem selected_cut_34246 : selected 9 ⟨870856, by decide⟩
    (prefixPartial 12 113164) = some ⟨12, 1, 0, 870856, 113164, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113164_870856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113164 ⟨870856, by decide⟩ :=
  accepted_of_selected 12 113164 ⟨870856, by decide⟩ ⟨12, 1, 0, 870856, 113164, 1, 65536⟩
    (by decide) selected_cut_34246

theorem selected_cut_34247 : selected 8 ⟨885019, by decide⟩
    (prefixPartial 13 452660) = some ⟨13, 2, 0, 885019, 452660, 4093, 16384⟩ := by
  decide +kernel

theorem context_13_452660_885019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452660 ⟨885019, by decide⟩ :=
  accepted_of_selected 13 452660 ⟨885019, by decide⟩ ⟨13, 2, 0, 885019, 452660, 4093, 16384⟩
    (by decide) selected_cut_34247

theorem selected_cut_34248 : selected 8 ⟨885124, by decide⟩
    (prefixPartial 13 452661) = some ⟨13, 2, 0, 885124, 452661, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_452661_885124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452661 ⟨885124, by decide⟩ :=
  accepted_of_selected 13 452661 ⟨885124, by decide⟩ ⟨13, 2, 0, 885124, 452661, 2305, 16384⟩
    (by decide) selected_cut_34248

theorem selected_cut_34249 : selected 8 ⟨885188, by decide⟩
    (prefixPartial 13 452662) = some ⟨13, 2, 0, 885188, 452662, 677, 16384⟩ := by
  decide +kernel

theorem context_13_452662_885188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452662 ⟨885188, by decide⟩ :=
  accepted_of_selected 13 452662 ⟨885188, by decide⟩ ⟨13, 2, 0, 885188, 452662, 677, 16384⟩
    (by decide) selected_cut_34249

theorem selected_cut_34250 : selected 8 ⟨885212, by decide⟩
    (prefixPartial 13 452663) = some ⟨13, 2, 0, 885212, 452663, 205, 16384⟩ := by
  decide +kernel

theorem context_13_452663_885212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452663 ⟨885212, by decide⟩ :=
  accepted_of_selected 13 452663 ⟨885212, by decide⟩ ⟨13, 2, 0, 885212, 452663, 205, 16384⟩
    (by decide) selected_cut_34250

theorem unmarked_context_12_113165_885213 : frontier 9 ⟨885213, by decide⟩
    (prefixCache 12 113165) (prefixPartial 12 113165) = false := by
  decide +kernel

theorem node_context_12_113165_885213 : EJMOriginalGlobalDAGData.nodes 9 ⟨885213, by decide⟩ =
    .split (coordinate 12) (![⟨885019, by decide⟩,⟨885124, by decide⟩,⟨885188, by decide⟩,⟨885212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113165_885213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113165 ⟨885213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113165
    ⟨885213, by decide⟩ (by decide) (![⟨885019, by decide⟩,⟨885124, by decide⟩,⟨885188, by decide⟩,⟨885212, by decide⟩]) unmarked_context_12_113165_885213 node_context_12_113165_885213
  intro a
  fin_cases a
  · exact context_13_452660_885019
  · exact context_13_452661_885124
  · exact context_13_452662_885188
  · exact context_13_452663_885212

theorem selected_cut_34251 : selected 9 ⟨870856, by decide⟩
    (prefixPartial 12 113166) = some ⟨12, 1, 0, 870856, 113166, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113166_870856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113166 ⟨870856, by decide⟩ :=
  accepted_of_selected 12 113166 ⟨870856, by decide⟩ ⟨12, 1, 0, 870856, 113166, 1, 65536⟩
    (by decide) selected_cut_34251

theorem selected_cut_34252 : selected 9 ⟨870856, by decide⟩
    (prefixPartial 12 113167) = some ⟨12, 1, 0, 870856, 113167, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113167_870856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113167 ⟨870856, by decide⟩ :=
  accepted_of_selected 12 113167 ⟨870856, by decide⟩ ⟨12, 1, 0, 870856, 113167, 1, 65536⟩
    (by decide) selected_cut_34252

theorem unmarked_context_11_28291_885214 : frontier 10 ⟨885214, by decide⟩
    (prefixCache 11 28291) (prefixPartial 11 28291) = false := by
  decide +kernel

theorem node_context_11_28291_885214 : EJMOriginalGlobalDAGData.nodes 10 ⟨885214, by decide⟩ =
    .split (coordinate 11) (![⟨870856, by decide⟩,⟨885213, by decide⟩,⟨870856, by decide⟩,⟨870856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28291_885214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28291 ⟨885214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28291
    ⟨885214, by decide⟩ (by decide) (![⟨870856, by decide⟩,⟨885213, by decide⟩,⟨870856, by decide⟩,⟨870856, by decide⟩]) unmarked_context_11_28291_885214 node_context_11_28291_885214
  intro a
  fin_cases a
  · exact context_12_113164_870856
  · exact context_12_113165_885213
  · exact context_12_113166_870856
  · exact context_12_113167_870856

theorem unmarked_context_10_7072_885215 : frontier 11 ⟨885215, by decide⟩
    (prefixCache 10 7072) (prefixPartial 10 7072) = false := by
  decide +kernel

theorem node_context_10_7072_885215 : EJMOriginalGlobalDAGData.nodes 11 ⟨885215, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨884883, by decide⟩,⟨764169, by decide⟩,⟨885214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7072_885215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7072 ⟨885215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7072
    ⟨885215, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨884883, by decide⟩,⟨764169, by decide⟩,⟨885214, by decide⟩]) unmarked_context_10_7072_885215 node_context_10_7072_885215
  intro a
  fin_cases a
  · exact context_11_28288_434745
  · exact context_11_28289_884883
  · exact context_11_28290_764169
  · exact context_11_28291_885214

theorem selected_cut_34253 : selected 8 ⟨885249, by decide⟩
    (prefixPartial 13 452672) = some ⟨13, 2, 0, 885249, 452672, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_452672_885249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452672 ⟨885249, by decide⟩ :=
  accepted_of_selected 13 452672 ⟨885249, by decide⟩ ⟨13, 2, 0, 885249, 452672, 2433, 16384⟩
    (by decide) selected_cut_34253

theorem selected_cut_34254 : selected 8 ⟨885280, by decide⟩
    (prefixPartial 13 452673) = some ⟨13, 2, 0, 885280, 452673, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_452673_885280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452673 ⟨885280, by decide⟩ :=
  accepted_of_selected 13 452673 ⟨885280, by decide⟩ ⟨13, 2, 0, 885280, 452673, 2785, 16384⟩
    (by decide) selected_cut_34254

theorem selected_cut_34255 : selected 8 ⟨885299, by decide⟩
    (prefixPartial 13 452674) = some ⟨13, 2, 0, 885299, 452674, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_452674_885299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452674 ⟨885299, by decide⟩ :=
  accepted_of_selected 13 452674 ⟨885299, by decide⟩ ⟨13, 2, 0, 885299, 452674, 1381, 16384⟩
    (by decide) selected_cut_34255

theorem selected_cut_34256 : selected 8 ⟨885320, by decide⟩
    (prefixPartial 13 452675) = some ⟨13, 2, 0, 885320, 452675, 993, 16384⟩ := by
  decide +kernel

theorem context_13_452675_885320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452675 ⟨885320, by decide⟩ :=
  accepted_of_selected 13 452675 ⟨885320, by decide⟩ ⟨13, 2, 0, 885320, 452675, 993, 16384⟩
    (by decide) selected_cut_34256

theorem unmarked_context_12_113168_885321 : frontier 9 ⟨885321, by decide⟩
    (prefixCache 12 113168) (prefixPartial 12 113168) = false := by
  decide +kernel

theorem node_context_12_113168_885321 : EJMOriginalGlobalDAGData.nodes 9 ⟨885321, by decide⟩ =
    .split (coordinate 12) (![⟨885249, by decide⟩,⟨885280, by decide⟩,⟨885299, by decide⟩,⟨885320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113168_885321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113168 ⟨885321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113168
    ⟨885321, by decide⟩ (by decide) (![⟨885249, by decide⟩,⟨885280, by decide⟩,⟨885299, by decide⟩,⟨885320, by decide⟩]) unmarked_context_12_113168_885321 node_context_12_113168_885321
  intro a
  fin_cases a
  · exact context_13_452672_885249
  · exact context_13_452673_885280
  · exact context_13_452674_885299
  · exact context_13_452675_885320

theorem selected_cut_34257 : selected 8 ⟨885387, by decide⟩
    (prefixPartial 13 452676) = some ⟨13, 2, 0, 885387, 452676, 3153, 16384⟩ := by
  decide +kernel

theorem context_13_452676_885387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452676 ⟨885387, by decide⟩ :=
  accepted_of_selected 13 452676 ⟨885387, by decide⟩ ⟨13, 2, 0, 885387, 452676, 3153, 16384⟩
    (by decide) selected_cut_34257

theorem selected_cut_34258 : selected 8 ⟨885445, by decide⟩
    (prefixPartial 13 452677) = some ⟨13, 2, 0, 885445, 452677, 3265, 16384⟩ := by
  decide +kernel

theorem context_13_452677_885445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452677 ⟨885445, by decide⟩ :=
  accepted_of_selected 13 452677 ⟨885445, by decide⟩ ⟨13, 2, 0, 885445, 452677, 3265, 16384⟩
    (by decide) selected_cut_34258

theorem selected_cut_34259 : selected 8 ⟨885480, by decide⟩
    (prefixPartial 13 452678) = some ⟨13, 2, 0, 885480, 452678, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_452678_885480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452678 ⟨885480, by decide⟩ :=
  accepted_of_selected 13 452678 ⟨885480, by decide⟩ ⟨13, 2, 0, 885480, 452678, 1669, 16384⟩
    (by decide) selected_cut_34259

theorem selected_cut_34260 : selected 8 ⟨885524, by decide⟩
    (prefixPartial 13 452679) = some ⟨13, 2, 0, 885524, 452679, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_452679_885524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452679 ⟨885524, by decide⟩ :=
  accepted_of_selected 13 452679 ⟨885524, by decide⟩ ⟨13, 2, 0, 885524, 452679, 1237, 16384⟩
    (by decide) selected_cut_34260

theorem unmarked_context_12_113169_885525 : frontier 9 ⟨885525, by decide⟩
    (prefixCache 12 113169) (prefixPartial 12 113169) = false := by
  decide +kernel

theorem node_context_12_113169_885525 : EJMOriginalGlobalDAGData.nodes 9 ⟨885525, by decide⟩ =
    .split (coordinate 12) (![⟨885387, by decide⟩,⟨885445, by decide⟩,⟨885480, by decide⟩,⟨885524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113169_885525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113169 ⟨885525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113169
    ⟨885525, by decide⟩ (by decide) (![⟨885387, by decide⟩,⟨885445, by decide⟩,⟨885480, by decide⟩,⟨885524, by decide⟩]) unmarked_context_12_113169_885525 node_context_12_113169_885525
  intro a
  fin_cases a
  · exact context_13_452676_885387
  · exact context_13_452677_885445
  · exact context_13_452678_885480
  · exact context_13_452679_885524

theorem selected_cut_34261 : selected 8 ⟨885560, by decide⟩
    (prefixPartial 13 452680) = some ⟨13, 2, 0, 885560, 452680, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_452680_885560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452680 ⟨885560, by decide⟩ :=
  accepted_of_selected 13 452680 ⟨885560, by decide⟩ ⟨13, 2, 0, 885560, 452680, 2285, 16384⟩
    (by decide) selected_cut_34261

theorem selected_cut_34262 : selected 8 ⟨885584, by decide⟩
    (prefixPartial 13 452681) = some ⟨13, 2, 0, 885584, 452681, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_452681_885584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452681 ⟨885584, by decide⟩ :=
  accepted_of_selected 13 452681 ⟨885584, by decide⟩ ⟨13, 2, 0, 885584, 452681, 2557, 16384⟩
    (by decide) selected_cut_34262

theorem selected_cut_34263 : selected 8 ⟨885606, by decide⟩
    (prefixPartial 13 452682) = some ⟨13, 2, 0, 885606, 452682, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_452682_885606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452682 ⟨885606, by decide⟩ :=
  accepted_of_selected 13 452682 ⟨885606, by decide⟩ ⟨13, 2, 0, 885606, 452682, 1233, 16384⟩
    (by decide) selected_cut_34263

theorem selected_cut_34264 : selected 8 ⟨885626, by decide⟩
    (prefixPartial 13 452683) = some ⟨13, 2, 0, 885626, 452683, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_452683_885626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452683 ⟨885626, by decide⟩ :=
  accepted_of_selected 13 452683 ⟨885626, by decide⟩ ⟨13, 2, 0, 885626, 452683, 1101, 16384⟩
    (by decide) selected_cut_34264

theorem unmarked_context_12_113170_885627 : frontier 9 ⟨885627, by decide⟩
    (prefixCache 12 113170) (prefixPartial 12 113170) = false := by
  decide +kernel

theorem node_context_12_113170_885627 : EJMOriginalGlobalDAGData.nodes 9 ⟨885627, by decide⟩ =
    .split (coordinate 12) (![⟨885560, by decide⟩,⟨885584, by decide⟩,⟨885606, by decide⟩,⟨885626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113170_885627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113170 ⟨885627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113170
    ⟨885627, by decide⟩ (by decide) (![⟨885560, by decide⟩,⟨885584, by decide⟩,⟨885606, by decide⟩,⟨885626, by decide⟩]) unmarked_context_12_113170_885627 node_context_12_113170_885627
  intro a
  fin_cases a
  · exact context_13_452680_885560
  · exact context_13_452681_885584
  · exact context_13_452682_885606
  · exact context_13_452683_885626

theorem selected_cut_34265 : selected 8 ⟨885676, by decide⟩
    (prefixPartial 13 452684) = some ⟨13, 2, 0, 885676, 452684, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_452684_885676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452684 ⟨885676, by decide⟩ :=
  accepted_of_selected 13 452684 ⟨885676, by decide⟩ ⟨13, 2, 0, 885676, 452684, 2629, 16384⟩
    (by decide) selected_cut_34265

theorem selected_cut_34266 : selected 8 ⟨885729, by decide⟩
    (prefixPartial 13 452685) = some ⟨13, 2, 0, 885729, 452685, 3045, 16384⟩ := by
  decide +kernel

theorem context_13_452685_885729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452685 ⟨885729, by decide⟩ :=
  accepted_of_selected 13 452685 ⟨885729, by decide⟩ ⟨13, 2, 0, 885729, 452685, 3045, 16384⟩
    (by decide) selected_cut_34266

theorem selected_cut_34267 : selected 8 ⟨885772, by decide⟩
    (prefixPartial 13 452686) = some ⟨13, 2, 0, 885772, 452686, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_452686_885772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452686 ⟨885772, by decide⟩ :=
  accepted_of_selected 13 452686 ⟨885772, by decide⟩ ⟨13, 2, 0, 885772, 452686, 1461, 16384⟩
    (by decide) selected_cut_34267

theorem selected_cut_34268 : selected 8 ⟨885790, by decide⟩
    (prefixPartial 13 452687) = some ⟨13, 2, 0, 885790, 452687, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_452687_885790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452687 ⟨885790, by decide⟩ :=
  accepted_of_selected 13 452687 ⟨885790, by decide⟩ ⟨13, 2, 0, 885790, 452687, 1093, 16384⟩
    (by decide) selected_cut_34268

theorem unmarked_context_12_113171_885791 : frontier 9 ⟨885791, by decide⟩
    (prefixCache 12 113171) (prefixPartial 12 113171) = false := by
  decide +kernel

theorem node_context_12_113171_885791 : EJMOriginalGlobalDAGData.nodes 9 ⟨885791, by decide⟩ =
    .split (coordinate 12) (![⟨885676, by decide⟩,⟨885729, by decide⟩,⟨885772, by decide⟩,⟨885790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113171_885791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113171 ⟨885791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113171
    ⟨885791, by decide⟩ (by decide) (![⟨885676, by decide⟩,⟨885729, by decide⟩,⟨885772, by decide⟩,⟨885790, by decide⟩]) unmarked_context_12_113171_885791 node_context_12_113171_885791
  intro a
  fin_cases a
  · exact context_13_452684_885676
  · exact context_13_452685_885729
  · exact context_13_452686_885772
  · exact context_13_452687_885790

theorem unmarked_context_11_28292_885792 : frontier 10 ⟨885792, by decide⟩
    (prefixCache 11 28292) (prefixPartial 11 28292) = false := by
  decide +kernel

theorem node_context_11_28292_885792 : EJMOriginalGlobalDAGData.nodes 10 ⟨885792, by decide⟩ =
    .split (coordinate 11) (![⟨885321, by decide⟩,⟨885525, by decide⟩,⟨885627, by decide⟩,⟨885791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28292_885792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28292 ⟨885792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28292
    ⟨885792, by decide⟩ (by decide) (![⟨885321, by decide⟩,⟨885525, by decide⟩,⟨885627, by decide⟩,⟨885791, by decide⟩]) unmarked_context_11_28292_885792 node_context_11_28292_885792
  intro a
  fin_cases a
  · exact context_12_113168_885321
  · exact context_12_113169_885525
  · exact context_12_113170_885627
  · exact context_12_113171_885791

theorem selected_cut_34269 : selected 8 ⟨885820, by decide⟩
    (prefixPartial 13 452688) = some ⟨13, 2, 0, 885820, 452688, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_452688_885820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452688 ⟨885820, by decide⟩ :=
  accepted_of_selected 13 452688 ⟨885820, by decide⟩ ⟨13, 2, 0, 885820, 452688, 1845, 16384⟩
    (by decide) selected_cut_34269

theorem selected_cut_34270 : selected 8 ⟨885853, by decide⟩
    (prefixPartial 13 452689) = some ⟨13, 2, 0, 885853, 452689, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_452689_885853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452689 ⟨885853, by decide⟩ :=
  accepted_of_selected 13 452689 ⟨885853, by decide⟩ ⟨13, 2, 0, 885853, 452689, 2317, 16384⟩
    (by decide) selected_cut_34270

theorem selected_cut_34271 : selected 8 ⟨885873, by decide⟩
    (prefixPartial 13 452690) = some ⟨13, 2, 0, 885873, 452690, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_452690_885873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452690 ⟨885873, by decide⟩ :=
  accepted_of_selected 13 452690 ⟨885873, by decide⟩ ⟨13, 2, 0, 885873, 452690, 1153, 16384⟩
    (by decide) selected_cut_34271

theorem selected_cut_34272 : selected 8 ⟨885885, by decide⟩
    (prefixPartial 13 452691) = some ⟨13, 2, 0, 885885, 452691, 861, 16384⟩ := by
  decide +kernel

theorem context_13_452691_885885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452691 ⟨885885, by decide⟩ :=
  accepted_of_selected 13 452691 ⟨885885, by decide⟩ ⟨13, 2, 0, 885885, 452691, 861, 16384⟩
    (by decide) selected_cut_34272

theorem unmarked_context_12_113172_885886 : frontier 9 ⟨885886, by decide⟩
    (prefixCache 12 113172) (prefixPartial 12 113172) = false := by
  decide +kernel

theorem node_context_12_113172_885886 : EJMOriginalGlobalDAGData.nodes 9 ⟨885886, by decide⟩ =
    .split (coordinate 12) (![⟨885820, by decide⟩,⟨885853, by decide⟩,⟨885873, by decide⟩,⟨885885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113172_885886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113172 ⟨885886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113172
    ⟨885886, by decide⟩ (by decide) (![⟨885820, by decide⟩,⟨885853, by decide⟩,⟨885873, by decide⟩,⟨885885, by decide⟩]) unmarked_context_12_113172_885886 node_context_12_113172_885886
  intro a
  fin_cases a
  · exact context_13_452688_885820
  · exact context_13_452689_885853
  · exact context_13_452690_885873
  · exact context_13_452691_885885

theorem selected_cut_34273 : selected 8 ⟨885937, by decide⟩
    (prefixPartial 13 452692) = some ⟨13, 2, 0, 885937, 452692, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_452692_885937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452692 ⟨885937, by decide⟩ :=
  accepted_of_selected 13 452692 ⟨885937, by decide⟩ ⟨13, 2, 0, 885937, 452692, 2645, 16384⟩
    (by decide) selected_cut_34273

theorem selected_cut_34274 : selected 8 ⟨885965, by decide⟩
    (prefixPartial 13 452693) = some ⟨13, 2, 0, 885965, 452693, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_452693_885965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452693 ⟨885965, by decide⟩ :=
  accepted_of_selected 13 452693 ⟨885965, by decide⟩ ⟨13, 2, 0, 885965, 452693, 2589, 16384⟩
    (by decide) selected_cut_34274

theorem selected_cut_34275 : selected 8 ⟨885987, by decide⟩
    (prefixPartial 13 452694) = some ⟨13, 2, 0, 885987, 452694, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_452694_885987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452694 ⟨885987, by decide⟩ :=
  accepted_of_selected 13 452694 ⟨885987, by decide⟩ ⟨13, 2, 0, 885987, 452694, 1341, 16384⟩
    (by decide) selected_cut_34275

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
