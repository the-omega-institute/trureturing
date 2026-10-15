/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover054
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05283 : selected 8 ⟨163619, by decide⟩
    (prefixPartial 13 77001) = some ⟨13, 2, 0, 163619, 77001, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_77001_163619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77001 ⟨163619, by decide⟩ :=
  accepted_of_selected 13 77001 ⟨163619, by decide⟩ ⟨13, 2, 0, 163619, 77001, 2173, 16384⟩
    (by decide) selected_cut_05283

theorem selected_cut_05284 : selected 8 ⟨163637, by decide⟩
    (prefixPartial 13 77002) = some ⟨13, 2, 0, 163637, 77002, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_77002_163637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77002 ⟨163637, by decide⟩ :=
  accepted_of_selected 13 77002 ⟨163637, by decide⟩ ⟨13, 2, 0, 163637, 77002, 1341, 16384⟩
    (by decide) selected_cut_05284

theorem selected_cut_05285 : selected 8 ⟨163643, by decide⟩
    (prefixPartial 13 77003) = some ⟨13, 2, 0, 163643, 77003, 621, 16384⟩ := by
  decide +kernel

theorem context_13_77003_163643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77003 ⟨163643, by decide⟩ :=
  accepted_of_selected 13 77003 ⟨163643, by decide⟩ ⟨13, 2, 0, 163643, 77003, 621, 16384⟩
    (by decide) selected_cut_05285

theorem unmarked_context_12_19250_163644 : frontier 9 ⟨163644, by decide⟩
    (prefixCache 12 19250) (prefixPartial 12 19250) = false := by
  decide +kernel

theorem node_context_12_19250_163644 : EJMOriginalGlobalDAGData.nodes 9 ⟨163644, by decide⟩ =
    .split (coordinate 12) (![⟨163567, by decide⟩,⟨163619, by decide⟩,⟨163637, by decide⟩,⟨163643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19250_163644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19250 ⟨163644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19250
    ⟨163644, by decide⟩ (by decide) (![⟨163567, by decide⟩,⟨163619, by decide⟩,⟨163637, by decide⟩,⟨163643, by decide⟩]) unmarked_context_12_19250_163644 node_context_12_19250_163644
  intro a
  fin_cases a
  · exact context_13_77000_163567
  · exact context_13_77001_163619
  · exact context_13_77002_163637
  · exact context_13_77003_163643

theorem selected_cut_05286 : selected 9 ⟨163712, by decide⟩
    (prefixPartial 12 19251) = some ⟨12, 2, 0, 163712, 19251, 4029, 65536⟩ := by
  decide +kernel

theorem context_12_19251_163712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19251 ⟨163712, by decide⟩ :=
  accepted_of_selected 12 19251 ⟨163712, by decide⟩ ⟨12, 2, 0, 163712, 19251, 4029, 65536⟩
    (by decide) selected_cut_05286

theorem unmarked_context_11_4812_163713 : frontier 10 ⟨163713, by decide⟩
    (prefixCache 11 4812) (prefixPartial 11 4812) = false := by
  decide +kernel

theorem node_context_11_4812_163713 : EJMOriginalGlobalDAGData.nodes 10 ⟨163713, by decide⟩ =
    .split (coordinate 11) (![⟨163478, by decide⟩,⟨163561, by decide⟩,⟨163644, by decide⟩,⟨163712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4812_163713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4812 ⟨163713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4812
    ⟨163713, by decide⟩ (by decide) (![⟨163478, by decide⟩,⟨163561, by decide⟩,⟨163644, by decide⟩,⟨163712, by decide⟩]) unmarked_context_11_4812_163713 node_context_11_4812_163713
  intro a
  fin_cases a
  · exact context_12_19248_163478
  · exact context_12_19249_163561
  · exact context_12_19250_163644
  · exact context_12_19251_163712

theorem selected_cut_05287 : selected 8 ⟨163723, by decide⟩
    (prefixPartial 13 77008) = some ⟨13, 2, 0, 163723, 77008, 473, 16384⟩ := by
  decide +kernel

theorem context_13_77008_163723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77008 ⟨163723, by decide⟩ :=
  accepted_of_selected 13 77008 ⟨163723, by decide⟩ ⟨13, 2, 0, 163723, 77008, 473, 16384⟩
    (by decide) selected_cut_05287

theorem selected_cut_05288 : selected 8 ⟨163764, by decide⟩
    (prefixPartial 13 77009) = some ⟨13, 2, 0, 163764, 77009, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_77009_163764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77009 ⟨163764, by decide⟩ :=
  accepted_of_selected 13 77009 ⟨163764, by decide⟩ ⟨13, 2, 0, 163764, 77009, 1973, 16384⟩
    (by decide) selected_cut_05288

theorem selected_cut_05289 : selected 8 ⟨163777, by decide⟩
    (prefixPartial 13 77010) = some ⟨13, 2, 0, 163777, 77010, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_77010_163777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77010 ⟨163777, by decide⟩ :=
  accepted_of_selected 13 77010 ⟨163777, by decide⟩ ⟨13, 2, 0, 163777, 77010, 1081, 16384⟩
    (by decide) selected_cut_05289

theorem selected_cut_05290 : selected 8 ⟨163785, by decide⟩
    (prefixPartial 13 77011) = some ⟨13, 2, 0, 163785, 77011, 781, 16384⟩ := by
  decide +kernel

theorem context_13_77011_163785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77011 ⟨163785, by decide⟩ :=
  accepted_of_selected 13 77011 ⟨163785, by decide⟩ ⟨13, 2, 0, 163785, 77011, 781, 16384⟩
    (by decide) selected_cut_05290

theorem unmarked_context_12_19252_163786 : frontier 9 ⟨163786, by decide⟩
    (prefixCache 12 19252) (prefixPartial 12 19252) = false := by
  decide +kernel

theorem node_context_12_19252_163786 : EJMOriginalGlobalDAGData.nodes 9 ⟨163786, by decide⟩ =
    .split (coordinate 12) (![⟨163723, by decide⟩,⟨163764, by decide⟩,⟨163777, by decide⟩,⟨163785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19252_163786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19252 ⟨163786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19252
    ⟨163786, by decide⟩ (by decide) (![⟨163723, by decide⟩,⟨163764, by decide⟩,⟨163777, by decide⟩,⟨163785, by decide⟩]) unmarked_context_12_19252_163786 node_context_12_19252_163786
  intro a
  fin_cases a
  · exact context_13_77008_163723
  · exact context_13_77009_163764
  · exact context_13_77010_163777
  · exact context_13_77011_163785

theorem selected_cut_05291 : selected 9 ⟨163848, by decide⟩
    (prefixPartial 12 19253) = some ⟨12, 2, 0, 163848, 19253, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_19253_163848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19253 ⟨163848, by decide⟩ :=
  accepted_of_selected 12 19253 ⟨163848, by decide⟩ ⟨12, 2, 0, 163848, 19253, 4085, 65536⟩
    (by decide) selected_cut_05291

theorem selected_cut_05292 : selected 8 ⟨163855, by decide⟩
    (prefixPartial 13 77016) = some ⟨13, 2, 0, 163855, 77016, 425, 16384⟩ := by
  decide +kernel

theorem context_13_77016_163855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77016 ⟨163855, by decide⟩ :=
  accepted_of_selected 13 77016 ⟨163855, by decide⟩ ⟨13, 2, 0, 163855, 77016, 425, 16384⟩
    (by decide) selected_cut_05292

theorem selected_cut_05293 : selected 8 ⟨163892, by decide⟩
    (prefixPartial 13 77017) = some ⟨13, 2, 0, 163892, 77017, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_77017_163892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77017 ⟨163892, by decide⟩ :=
  accepted_of_selected 13 77017 ⟨163892, by decide⟩ ⟨13, 2, 0, 163892, 77017, 2109, 16384⟩
    (by decide) selected_cut_05293

theorem selected_cut_05294 : selected 8 ⟨163909, by decide⟩
    (prefixPartial 13 77018) = some ⟨13, 2, 0, 163909, 77018, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_77018_163909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77018 ⟨163909, by decide⟩ :=
  accepted_of_selected 13 77018 ⟨163909, by decide⟩ ⟨13, 2, 0, 163909, 77018, 1401, 16384⟩
    (by decide) selected_cut_05294

theorem selected_cut_05295 : selected 8 ⟨163917, by decide⟩
    (prefixPartial 13 77019) = some ⟨13, 2, 0, 163917, 77019, 749, 16384⟩ := by
  decide +kernel

theorem context_13_77019_163917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77019 ⟨163917, by decide⟩ :=
  accepted_of_selected 13 77019 ⟨163917, by decide⟩ ⟨13, 2, 0, 163917, 77019, 749, 16384⟩
    (by decide) selected_cut_05295

theorem unmarked_context_12_19254_163918 : frontier 9 ⟨163918, by decide⟩
    (prefixCache 12 19254) (prefixPartial 12 19254) = false := by
  decide +kernel

theorem node_context_12_19254_163918 : EJMOriginalGlobalDAGData.nodes 9 ⟨163918, by decide⟩ =
    .split (coordinate 12) (![⟨163855, by decide⟩,⟨163892, by decide⟩,⟨163909, by decide⟩,⟨163917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19254_163918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19254 ⟨163918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19254
    ⟨163918, by decide⟩ (by decide) (![⟨163855, by decide⟩,⟨163892, by decide⟩,⟨163909, by decide⟩,⟨163917, by decide⟩]) unmarked_context_12_19254_163918 node_context_12_19254_163918
  intro a
  fin_cases a
  · exact context_13_77016_163855
  · exact context_13_77017_163892
  · exact context_13_77018_163909
  · exact context_13_77019_163917

theorem selected_cut_05296 : selected 9 ⟨163984, by decide⟩
    (prefixPartial 12 19255) = some ⟨12, 2, 0, 163984, 19255, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_19255_163984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19255 ⟨163984, by decide⟩ :=
  accepted_of_selected 12 19255 ⟨163984, by decide⟩ ⟨12, 2, 0, 163984, 19255, 3921, 65536⟩
    (by decide) selected_cut_05296

theorem unmarked_context_11_4813_163985 : frontier 10 ⟨163985, by decide⟩
    (prefixCache 11 4813) (prefixPartial 11 4813) = false := by
  decide +kernel

theorem node_context_11_4813_163985 : EJMOriginalGlobalDAGData.nodes 10 ⟨163985, by decide⟩ =
    .split (coordinate 11) (![⟨163786, by decide⟩,⟨163848, by decide⟩,⟨163918, by decide⟩,⟨163984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4813_163985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4813 ⟨163985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4813
    ⟨163985, by decide⟩ (by decide) (![⟨163786, by decide⟩,⟨163848, by decide⟩,⟨163918, by decide⟩,⟨163984, by decide⟩]) unmarked_context_11_4813_163985 node_context_11_4813_163985
  intro a
  fin_cases a
  · exact context_12_19252_163786
  · exact context_12_19253_163848
  · exact context_12_19254_163918
  · exact context_12_19255_163984

theorem selected_cut_05297 : selected 8 ⟨163990, by decide⟩
    (prefixPartial 13 77024) = some ⟨13, 2, 0, 163990, 77024, 305, 16384⟩ := by
  decide +kernel

theorem context_13_77024_163990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77024 ⟨163990, by decide⟩ :=
  accepted_of_selected 13 77024 ⟨163990, by decide⟩ ⟨13, 2, 0, 163990, 77024, 305, 16384⟩
    (by decide) selected_cut_05297

theorem selected_cut_05298 : selected 8 ⟨164021, by decide⟩
    (prefixPartial 13 77025) = some ⟨13, 2, 0, 164021, 77025, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_77025_164021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77025 ⟨164021, by decide⟩ :=
  accepted_of_selected 13 77025 ⟨164021, by decide⟩ ⟨13, 2, 0, 164021, 77025, 1909, 16384⟩
    (by decide) selected_cut_05298

theorem selected_cut_05299 : selected 8 ⟨164032, by decide⟩
    (prefixPartial 13 77026) = some ⟨13, 2, 0, 164032, 77026, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_77026_164032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77026 ⟨164032, by decide⟩ :=
  accepted_of_selected 13 77026 ⟨164032, by decide⟩ ⟨13, 2, 0, 164032, 77026, 1137, 16384⟩
    (by decide) selected_cut_05299

theorem selected_cut_05300 : selected 8 ⟨164038, by decide⟩
    (prefixPartial 13 77027) = some ⟨13, 2, 0, 164038, 77027, 785, 16384⟩ := by
  decide +kernel

theorem context_13_77027_164038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77027 ⟨164038, by decide⟩ :=
  accepted_of_selected 13 77027 ⟨164038, by decide⟩ ⟨13, 2, 0, 164038, 77027, 785, 16384⟩
    (by decide) selected_cut_05300

theorem unmarked_context_12_19256_164039 : frontier 9 ⟨164039, by decide⟩
    (prefixCache 12 19256) (prefixPartial 12 19256) = false := by
  decide +kernel

theorem node_context_12_19256_164039 : EJMOriginalGlobalDAGData.nodes 9 ⟨164039, by decide⟩ =
    .split (coordinate 12) (![⟨163990, by decide⟩,⟨164021, by decide⟩,⟨164032, by decide⟩,⟨164038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19256_164039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19256 ⟨164039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19256
    ⟨164039, by decide⟩ (by decide) (![⟨163990, by decide⟩,⟨164021, by decide⟩,⟨164032, by decide⟩,⟨164038, by decide⟩]) unmarked_context_12_19256_164039 node_context_12_19256_164039
  intro a
  fin_cases a
  · exact context_13_77024_163990
  · exact context_13_77025_164021
  · exact context_13_77026_164032
  · exact context_13_77027_164038

theorem selected_cut_05301 : selected 8 ⟨164048, by decide⟩
    (prefixPartial 13 77028) = some ⟨13, 2, 0, 164048, 77028, 309, 16384⟩ := by
  decide +kernel

theorem context_13_77028_164048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77028 ⟨164048, by decide⟩ :=
  accepted_of_selected 13 77028 ⟨164048, by decide⟩ ⟨13, 2, 0, 164048, 77028, 309, 16384⟩
    (by decide) selected_cut_05301

theorem selected_cut_05302 : selected 8 ⟨164083, by decide⟩
    (prefixPartial 13 77029) = some ⟨13, 2, 0, 164083, 77029, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_77029_164083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77029 ⟨164083, by decide⟩ :=
  accepted_of_selected 13 77029 ⟨164083, by decide⟩ ⟨13, 2, 0, 164083, 77029, 2169, 16384⟩
    (by decide) selected_cut_05302

theorem selected_cut_05303 : selected 8 ⟨164101, by decide⟩
    (prefixPartial 13 77030) = some ⟨13, 2, 0, 164101, 77030, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_77030_164101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77030 ⟨164101, by decide⟩ :=
  accepted_of_selected 13 77030 ⟨164101, by decide⟩ ⟨13, 2, 0, 164101, 77030, 1213, 16384⟩
    (by decide) selected_cut_05303

theorem selected_cut_05304 : selected 8 ⟨164109, by decide⟩
    (prefixPartial 13 77031) = some ⟨13, 2, 0, 164109, 77031, 709, 16384⟩ := by
  decide +kernel

theorem context_13_77031_164109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77031 ⟨164109, by decide⟩ :=
  accepted_of_selected 13 77031 ⟨164109, by decide⟩ ⟨13, 2, 0, 164109, 77031, 709, 16384⟩
    (by decide) selected_cut_05304

theorem unmarked_context_12_19257_164110 : frontier 9 ⟨164110, by decide⟩
    (prefixCache 12 19257) (prefixPartial 12 19257) = false := by
  decide +kernel

theorem node_context_12_19257_164110 : EJMOriginalGlobalDAGData.nodes 9 ⟨164110, by decide⟩ =
    .split (coordinate 12) (![⟨164048, by decide⟩,⟨164083, by decide⟩,⟨164101, by decide⟩,⟨164109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19257_164110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19257 ⟨164110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19257
    ⟨164110, by decide⟩ (by decide) (![⟨164048, by decide⟩,⟨164083, by decide⟩,⟨164101, by decide⟩,⟨164109, by decide⟩]) unmarked_context_12_19257_164110 node_context_12_19257_164110
  intro a
  fin_cases a
  · exact context_13_77028_164048
  · exact context_13_77029_164083
  · exact context_13_77030_164101
  · exact context_13_77031_164109

theorem selected_cut_05305 : selected 8 ⟨164114, by decide⟩
    (prefixPartial 13 77032) = some ⟨13, 2, 0, 164114, 77032, 197, 16384⟩ := by
  decide +kernel

theorem context_13_77032_164114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77032 ⟨164114, by decide⟩ :=
  accepted_of_selected 13 77032 ⟨164114, by decide⟩ ⟨13, 2, 0, 164114, 77032, 197, 16384⟩
    (by decide) selected_cut_05305

theorem selected_cut_05306 : selected 8 ⟨164140, by decide⟩
    (prefixPartial 13 77033) = some ⟨13, 2, 0, 164140, 77033, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_77033_164140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77033 ⟨164140, by decide⟩ :=
  accepted_of_selected 13 77033 ⟨164140, by decide⟩ ⟨13, 2, 0, 164140, 77033, 2021, 16384⟩
    (by decide) selected_cut_05306

theorem selected_cut_05307 : selected 8 ⟨164156, by decide⟩
    (prefixPartial 13 77034) = some ⟨13, 2, 0, 164156, 77034, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_77034_164156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77034 ⟨164156, by decide⟩ :=
  accepted_of_selected 13 77034 ⟨164156, by decide⟩ ⟨13, 2, 0, 164156, 77034, 1261, 16384⟩
    (by decide) selected_cut_05307

theorem selected_cut_05308 : selected 8 ⟨164163, by decide⟩
    (prefixPartial 13 77035) = some ⟨13, 2, 0, 164163, 77035, 665, 16384⟩ := by
  decide +kernel

theorem context_13_77035_164163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77035 ⟨164163, by decide⟩ :=
  accepted_of_selected 13 77035 ⟨164163, by decide⟩ ⟨13, 2, 0, 164163, 77035, 665, 16384⟩
    (by decide) selected_cut_05308

theorem unmarked_context_12_19258_164164 : frontier 9 ⟨164164, by decide⟩
    (prefixCache 12 19258) (prefixPartial 12 19258) = false := by
  decide +kernel

theorem node_context_12_19258_164164 : EJMOriginalGlobalDAGData.nodes 9 ⟨164164, by decide⟩ =
    .split (coordinate 12) (![⟨164114, by decide⟩,⟨164140, by decide⟩,⟨164156, by decide⟩,⟨164163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19258_164164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19258 ⟨164164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19258
    ⟨164164, by decide⟩ (by decide) (![⟨164114, by decide⟩,⟨164140, by decide⟩,⟨164156, by decide⟩,⟨164163, by decide⟩]) unmarked_context_12_19258_164164 node_context_12_19258_164164
  intro a
  fin_cases a
  · exact context_13_77032_164114
  · exact context_13_77033_164140
  · exact context_13_77034_164156
  · exact context_13_77035_164163

theorem selected_cut_05309 : selected 9 ⟨164225, by decide⟩
    (prefixPartial 12 19259) = some ⟨12, 2, 0, 164225, 19259, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_19259_164225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19259 ⟨164225, by decide⟩ :=
  accepted_of_selected 12 19259 ⟨164225, by decide⟩ ⟨12, 2, 0, 164225, 19259, 3857, 65536⟩
    (by decide) selected_cut_05309

theorem unmarked_context_11_4814_164226 : frontier 10 ⟨164226, by decide⟩
    (prefixCache 11 4814) (prefixPartial 11 4814) = false := by
  decide +kernel

theorem node_context_11_4814_164226 : EJMOriginalGlobalDAGData.nodes 10 ⟨164226, by decide⟩ =
    .split (coordinate 11) (![⟨164039, by decide⟩,⟨164110, by decide⟩,⟨164164, by decide⟩,⟨164225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4814_164226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4814 ⟨164226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4814
    ⟨164226, by decide⟩ (by decide) (![⟨164039, by decide⟩,⟨164110, by decide⟩,⟨164164, by decide⟩,⟨164225, by decide⟩]) unmarked_context_11_4814_164226 node_context_11_4814_164226
  intro a
  fin_cases a
  · exact context_12_19256_164039
  · exact context_12_19257_164110
  · exact context_12_19258_164164
  · exact context_12_19259_164225

theorem selected_cut_05310 : selected 9 ⟨164274, by decide⟩
    (prefixPartial 12 19260) = some ⟨12, 2, 0, 164274, 19260, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_19260_164274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19260 ⟨164274, by decide⟩ :=
  accepted_of_selected 12 19260 ⟨164274, by decide⟩ ⟨12, 2, 0, 164274, 19260, 3389, 65536⟩
    (by decide) selected_cut_05310

theorem selected_cut_05311 : selected 9 ⟨164331, by decide⟩
    (prefixPartial 12 19261) = some ⟨12, 2, 0, 164331, 19261, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_19261_164331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19261 ⟨164331, by decide⟩ :=
  accepted_of_selected 12 19261 ⟨164331, by decide⟩ ⟨12, 2, 0, 164331, 19261, 3601, 65536⟩
    (by decide) selected_cut_05311

theorem selected_cut_05312 : selected 9 ⟨164393, by decide⟩
    (prefixPartial 12 19262) = some ⟨12, 2, 0, 164393, 19262, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_19262_164393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19262 ⟨164393, by decide⟩ :=
  accepted_of_selected 12 19262 ⟨164393, by decide⟩ ⟨12, 2, 0, 164393, 19262, 3773, 65536⟩
    (by decide) selected_cut_05312

theorem selected_cut_05313 : selected 8 ⟨164397, by decide⟩
    (prefixPartial 13 77052) = some ⟨13, 2, 0, 164397, 77052, 77, 16384⟩ := by
  decide +kernel

theorem context_13_77052_164397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77052 ⟨164397, by decide⟩ :=
  accepted_of_selected 13 77052 ⟨164397, by decide⟩ ⟨13, 2, 0, 164397, 77052, 77, 16384⟩
    (by decide) selected_cut_05313

theorem selected_cut_05314 : selected 8 ⟨164439, by decide⟩
    (prefixPartial 13 77053) = some ⟨13, 2, 0, 164439, 77053, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_77053_164439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77053 ⟨164439, by decide⟩ :=
  accepted_of_selected 13 77053 ⟨164439, by decide⟩ ⟨13, 2, 0, 164439, 77053, 2465, 16384⟩
    (by decide) selected_cut_05314

theorem selected_cut_05315 : selected 8 ⟨164464, by decide⟩
    (prefixPartial 13 77054) = some ⟨13, 2, 0, 164464, 77054, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_77054_164464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77054 ⟨164464, by decide⟩ :=
  accepted_of_selected 13 77054 ⟨164464, by decide⟩ ⟨13, 2, 0, 164464, 77054, 1573, 16384⟩
    (by decide) selected_cut_05315

theorem selected_cut_05316 : selected 8 ⟨164471, by decide⟩
    (prefixPartial 13 77055) = some ⟨13, 2, 0, 164471, 77055, 685, 16384⟩ := by
  decide +kernel

theorem context_13_77055_164471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77055 ⟨164471, by decide⟩ :=
  accepted_of_selected 13 77055 ⟨164471, by decide⟩ ⟨13, 2, 0, 164471, 77055, 685, 16384⟩
    (by decide) selected_cut_05316

theorem unmarked_context_12_19263_164472 : frontier 9 ⟨164472, by decide⟩
    (prefixCache 12 19263) (prefixPartial 12 19263) = false := by
  decide +kernel

theorem node_context_12_19263_164472 : EJMOriginalGlobalDAGData.nodes 9 ⟨164472, by decide⟩ =
    .split (coordinate 12) (![⟨164397, by decide⟩,⟨164439, by decide⟩,⟨164464, by decide⟩,⟨164471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19263_164472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19263 ⟨164472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19263
    ⟨164472, by decide⟩ (by decide) (![⟨164397, by decide⟩,⟨164439, by decide⟩,⟨164464, by decide⟩,⟨164471, by decide⟩]) unmarked_context_12_19263_164472 node_context_12_19263_164472
  intro a
  fin_cases a
  · exact context_13_77052_164397
  · exact context_13_77053_164439
  · exact context_13_77054_164464
  · exact context_13_77055_164471

theorem unmarked_context_11_4815_164473 : frontier 10 ⟨164473, by decide⟩
    (prefixCache 11 4815) (prefixPartial 11 4815) = false := by
  decide +kernel

theorem node_context_11_4815_164473 : EJMOriginalGlobalDAGData.nodes 10 ⟨164473, by decide⟩ =
    .split (coordinate 11) (![⟨164274, by decide⟩,⟨164331, by decide⟩,⟨164393, by decide⟩,⟨164472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4815_164473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4815 ⟨164473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4815
    ⟨164473, by decide⟩ (by decide) (![⟨164274, by decide⟩,⟨164331, by decide⟩,⟨164393, by decide⟩,⟨164472, by decide⟩]) unmarked_context_11_4815_164473 node_context_11_4815_164473
  intro a
  fin_cases a
  · exact context_12_19260_164274
  · exact context_12_19261_164331
  · exact context_12_19262_164393
  · exact context_12_19263_164472

theorem unmarked_context_10_1203_164474 : frontier 11 ⟨164474, by decide⟩
    (prefixCache 10 1203) (prefixPartial 10 1203) = false := by
  decide +kernel

theorem node_context_10_1203_164474 : EJMOriginalGlobalDAGData.nodes 11 ⟨164474, by decide⟩ =
    .split (coordinate 10) (![⟨163713, by decide⟩,⟨163985, by decide⟩,⟨164226, by decide⟩,⟨164473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1203_164474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1203 ⟨164474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1203
    ⟨164474, by decide⟩ (by decide) (![⟨163713, by decide⟩,⟨163985, by decide⟩,⟨164226, by decide⟩,⟨164473, by decide⟩]) unmarked_context_10_1203_164474 node_context_10_1203_164474
  intro a
  fin_cases a
  · exact context_11_4812_163713
  · exact context_11_4813_163985
  · exact context_11_4814_164226
  · exact context_11_4815_164473

theorem unmarked_context_9_300_164475 : frontier 12 ⟨164475, by decide⟩
    (prefixCache 9 300) (prefixPartial 9 300) = false := by
  decide +kernel

theorem node_context_9_300_164475 : EJMOriginalGlobalDAGData.nodes 12 ⟨164475, by decide⟩ =
    .split (coordinate 9) (![⟨160078, by decide⟩,⟨161662, by decide⟩,⟨163402, by decide⟩,⟨164474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_300_164475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 300 ⟨164475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 300
    ⟨164475, by decide⟩ (by decide) (![⟨160078, by decide⟩,⟨161662, by decide⟩,⟨163402, by decide⟩,⟨164474, by decide⟩]) unmarked_context_9_300_164475 node_context_9_300_164475
  intro a
  fin_cases a
  · exact context_10_1200_160078
  · exact context_10_1201_161662
  · exact context_10_1202_163402
  · exact context_10_1203_164474

theorem selected_cut_05317 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 1204) = some ⟨10, 1, 0, 145424, 1204, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1204_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1204 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 1204 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 1204, 1, 1048576⟩
    (by decide) selected_cut_05317

theorem selected_cut_05318 : selected 9 ⟨164593, by decide⟩
    (prefixPartial 12 19280) = some ⟨12, 2, 0, 164593, 19280, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_19280_164593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19280 ⟨164593, by decide⟩ :=
  accepted_of_selected 12 19280 ⟨164593, by decide⟩ ⟨12, 2, 0, 164593, 19280, 3917, 65536⟩
    (by decide) selected_cut_05318

theorem selected_cut_05319 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 77124) = some ⟨13, 1, 0, 3444, 77124, 1, 16384⟩ := by
  decide +kernel

theorem context_13_77124_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77124 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 77124 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 77124, 1, 16384⟩
    (by decide) selected_cut_05319

theorem selected_cut_05320 : selected 8 ⟨164693, by decide⟩
    (prefixPartial 13 77125) = some ⟨13, 2, 0, 164693, 77125, 2937, 16384⟩ := by
  decide +kernel

theorem context_13_77125_164693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77125 ⟨164693, by decide⟩ :=
  accepted_of_selected 13 77125 ⟨164693, by decide⟩ ⟨13, 2, 0, 164693, 77125, 2937, 16384⟩
    (by decide) selected_cut_05320

theorem selected_cut_05321 : selected 8 ⟨164736, by decide⟩
    (prefixPartial 13 77126) = some ⟨13, 2, 0, 164736, 77126, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_77126_164736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77126 ⟨164736, by decide⟩ :=
  accepted_of_selected 13 77126 ⟨164736, by decide⟩ ⟨13, 2, 0, 164736, 77126, 1441, 16384⟩
    (by decide) selected_cut_05321

theorem selected_cut_05322 : selected 8 ⟨164743, by decide⟩
    (prefixPartial 13 77127) = some ⟨13, 2, 0, 164743, 77127, 581, 16384⟩ := by
  decide +kernel

theorem context_13_77127_164743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77127 ⟨164743, by decide⟩ :=
  accepted_of_selected 13 77127 ⟨164743, by decide⟩ ⟨13, 2, 0, 164743, 77127, 581, 16384⟩
    (by decide) selected_cut_05322

theorem unmarked_context_12_19281_164744 : frontier 9 ⟨164744, by decide⟩
    (prefixCache 12 19281) (prefixPartial 12 19281) = false := by
  decide +kernel

theorem node_context_12_19281_164744 : EJMOriginalGlobalDAGData.nodes 9 ⟨164744, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨164693, by decide⟩,⟨164736, by decide⟩,⟨164743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19281_164744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19281 ⟨164744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19281
    ⟨164744, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨164693, by decide⟩,⟨164736, by decide⟩,⟨164743, by decide⟩]) unmarked_context_12_19281_164744 node_context_12_19281_164744
  intro a
  fin_cases a
  · exact context_13_77124_3444
  · exact context_13_77125_164693
  · exact context_13_77126_164736
  · exact context_13_77127_164743

theorem selected_cut_05323 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 77128) = some ⟨13, 1, 0, 3444, 77128, 1, 16384⟩ := by
  decide +kernel

theorem context_13_77128_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77128 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 77128 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 77128, 1, 16384⟩
    (by decide) selected_cut_05323

theorem selected_cut_05324 : selected 8 ⟨164812, by decide⟩
    (prefixPartial 13 77129) = some ⟨13, 2, 0, 164812, 77129, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_77129_164812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77129 ⟨164812, by decide⟩ :=
  accepted_of_selected 13 77129 ⟨164812, by decide⟩ ⟨13, 2, 0, 164812, 77129, 2513, 16384⟩
    (by decide) selected_cut_05324

theorem selected_cut_05325 : selected 8 ⟨164847, by decide⟩
    (prefixPartial 13 77130) = some ⟨13, 2, 0, 164847, 77130, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_77130_164847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77130 ⟨164847, by decide⟩ :=
  accepted_of_selected 13 77130 ⟨164847, by decide⟩ ⟨13, 2, 0, 164847, 77130, 1297, 16384⟩
    (by decide) selected_cut_05325

theorem selected_cut_05326 : selected 8 ⟨164857, by decide⟩
    (prefixPartial 13 77131) = some ⟨13, 2, 0, 164857, 77131, 509, 16384⟩ := by
  decide +kernel

theorem context_13_77131_164857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77131 ⟨164857, by decide⟩ :=
  accepted_of_selected 13 77131 ⟨164857, by decide⟩ ⟨13, 2, 0, 164857, 77131, 509, 16384⟩
    (by decide) selected_cut_05326

theorem unmarked_context_12_19282_164858 : frontier 9 ⟨164858, by decide⟩
    (prefixCache 12 19282) (prefixPartial 12 19282) = false := by
  decide +kernel

theorem node_context_12_19282_164858 : EJMOriginalGlobalDAGData.nodes 9 ⟨164858, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨164812, by decide⟩,⟨164847, by decide⟩,⟨164857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19282_164858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19282 ⟨164858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19282
    ⟨164858, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨164812, by decide⟩,⟨164847, by decide⟩,⟨164857, by decide⟩]) unmarked_context_12_19282_164858 node_context_12_19282_164858
  intro a
  fin_cases a
  · exact context_13_77128_3444
  · exact context_13_77129_164812
  · exact context_13_77130_164847
  · exact context_13_77131_164857

theorem selected_cut_05327 : selected 9 ⟨164940, by decide⟩
    (prefixPartial 12 19283) = some ⟨12, 2, 0, 164940, 19283, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_19283_164940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19283 ⟨164940, by decide⟩ :=
  accepted_of_selected 12 19283 ⟨164940, by decide⟩ ⟨12, 2, 0, 164940, 19283, 3849, 65536⟩
    (by decide) selected_cut_05327

theorem unmarked_context_11_4820_164941 : frontier 10 ⟨164941, by decide⟩
    (prefixCache 11 4820) (prefixPartial 11 4820) = false := by
  decide +kernel

theorem node_context_11_4820_164941 : EJMOriginalGlobalDAGData.nodes 10 ⟨164941, by decide⟩ =
    .split (coordinate 11) (![⟨164593, by decide⟩,⟨164744, by decide⟩,⟨164858, by decide⟩,⟨164940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4820_164941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4820 ⟨164941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4820
    ⟨164941, by decide⟩ (by decide) (![⟨164593, by decide⟩,⟨164744, by decide⟩,⟨164858, by decide⟩,⟨164940, by decide⟩]) unmarked_context_11_4820_164941 node_context_11_4820_164941
  intro a
  fin_cases a
  · exact context_12_19280_164593
  · exact context_12_19281_164744
  · exact context_12_19282_164858
  · exact context_12_19283_164940

theorem selected_cut_05328 : selected 9 ⟨165025, by decide⟩
    (prefixPartial 12 19284) = some ⟨12, 2, 0, 165025, 19284, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_19284_165025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19284 ⟨165025, by decide⟩ :=
  accepted_of_selected 12 19284 ⟨165025, by decide⟩ ⟨12, 2, 0, 165025, 19284, 3385, 65536⟩
    (by decide) selected_cut_05328

theorem selected_cut_05329 : selected 9 ⟨165055, by decide⟩
    (prefixPartial 12 19285) = some ⟨12, 2, 0, 165055, 19285, 853, 65536⟩ := by
  decide +kernel

theorem context_12_19285_165055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19285 ⟨165055, by decide⟩ :=
  accepted_of_selected 12 19285 ⟨165055, by decide⟩ ⟨12, 2, 0, 165055, 19285, 853, 65536⟩
    (by decide) selected_cut_05329

theorem selected_cut_05330 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 77144) = some ⟨13, 1, 0, 3444, 77144, 1, 16384⟩ := by
  decide +kernel

theorem context_13_77144_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77144 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 77144 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 77144, 1, 16384⟩
    (by decide) selected_cut_05330

theorem selected_cut_05331 : selected 8 ⟨165117, by decide⟩
    (prefixPartial 13 77145) = some ⟨13, 2, 0, 165117, 77145, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_77145_165117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77145 ⟨165117, by decide⟩ :=
  accepted_of_selected 13 77145 ⟨165117, by decide⟩ ⟨13, 2, 0, 165117, 77145, 2313, 16384⟩
    (by decide) selected_cut_05331

theorem selected_cut_05332 : selected 8 ⟨165142, by decide⟩
    (prefixPartial 13 77146) = some ⟨13, 2, 0, 165142, 77146, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_77146_165142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77146 ⟨165142, by decide⟩ :=
  accepted_of_selected 13 77146 ⟨165142, by decide⟩ ⟨13, 2, 0, 165142, 77146, 1217, 16384⟩
    (by decide) selected_cut_05332

theorem selected_cut_05333 : selected 8 ⟨165150, by decide⟩
    (prefixPartial 13 77147) = some ⟨13, 2, 0, 165150, 77147, 689, 16384⟩ := by
  decide +kernel

theorem context_13_77147_165150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77147 ⟨165150, by decide⟩ :=
  accepted_of_selected 13 77147 ⟨165150, by decide⟩ ⟨13, 2, 0, 165150, 77147, 689, 16384⟩
    (by decide) selected_cut_05333

theorem unmarked_context_12_19286_165151 : frontier 9 ⟨165151, by decide⟩
    (prefixCache 12 19286) (prefixPartial 12 19286) = false := by
  decide +kernel

theorem node_context_12_19286_165151 : EJMOriginalGlobalDAGData.nodes 9 ⟨165151, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨165117, by decide⟩,⟨165142, by decide⟩,⟨165150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19286_165151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19286 ⟨165151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19286
    ⟨165151, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨165117, by decide⟩,⟨165142, by decide⟩,⟨165150, by decide⟩]) unmarked_context_12_19286_165151 node_context_12_19286_165151
  intro a
  fin_cases a
  · exact context_13_77144_3444
  · exact context_13_77145_165117
  · exact context_13_77146_165142
  · exact context_13_77147_165150

theorem selected_cut_05334 : selected 9 ⟨165223, by decide⟩
    (prefixPartial 12 19287) = some ⟨12, 2, 0, 165223, 19287, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_19287_165223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19287 ⟨165223, by decide⟩ :=
  accepted_of_selected 12 19287 ⟨165223, by decide⟩ ⟨12, 2, 0, 165223, 19287, 3577, 65536⟩
    (by decide) selected_cut_05334

theorem unmarked_context_11_4821_165224 : frontier 10 ⟨165224, by decide⟩
    (prefixCache 11 4821) (prefixPartial 11 4821) = false := by
  decide +kernel

theorem node_context_11_4821_165224 : EJMOriginalGlobalDAGData.nodes 10 ⟨165224, by decide⟩ =
    .split (coordinate 11) (![⟨165025, by decide⟩,⟨165055, by decide⟩,⟨165151, by decide⟩,⟨165223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4821_165224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4821 ⟨165224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4821
    ⟨165224, by decide⟩ (by decide) (![⟨165025, by decide⟩,⟨165055, by decide⟩,⟨165151, by decide⟩,⟨165223, by decide⟩]) unmarked_context_11_4821_165224 node_context_11_4821_165224
  intro a
  fin_cases a
  · exact context_12_19284_165025
  · exact context_12_19285_165055
  · exact context_12_19286_165151
  · exact context_12_19287_165223

theorem selected_cut_05335 : selected 9 ⟨165286, by decide⟩
    (prefixPartial 12 19288) = some ⟨12, 2, 0, 165286, 19288, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_19288_165286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19288 ⟨165286, by decide⟩ :=
  accepted_of_selected 12 19288 ⟨165286, by decide⟩ ⟨12, 2, 0, 165286, 19288, 3241, 65536⟩
    (by decide) selected_cut_05335

theorem selected_cut_05336 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 77156) = some ⟨13, 1, 0, 3444, 77156, 1, 16384⟩ := by
  decide +kernel

theorem context_13_77156_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77156 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 77156 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 77156, 1, 16384⟩
    (by decide) selected_cut_05336

theorem selected_cut_05337 : selected 8 ⟨165343, by decide⟩
    (prefixPartial 13 77157) = some ⟨13, 2, 0, 165343, 77157, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_77157_165343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77157 ⟨165343, by decide⟩ :=
  accepted_of_selected 13 77157 ⟨165343, by decide⟩ ⟨13, 2, 0, 165343, 77157, 2325, 16384⟩
    (by decide) selected_cut_05337

theorem selected_cut_05338 : selected 8 ⟨165364, by decide⟩
    (prefixPartial 13 77158) = some ⟨13, 2, 0, 165364, 77158, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_77158_165364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77158 ⟨165364, by decide⟩ :=
  accepted_of_selected 13 77158 ⟨165364, by decide⟩ ⟨13, 2, 0, 165364, 77158, 1241, 16384⟩
    (by decide) selected_cut_05338

theorem selected_cut_05339 : selected 8 ⟨165370, by decide⟩
    (prefixPartial 13 77159) = some ⟨13, 2, 0, 165370, 77159, 757, 16384⟩ := by
  decide +kernel

theorem context_13_77159_165370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77159 ⟨165370, by decide⟩ :=
  accepted_of_selected 13 77159 ⟨165370, by decide⟩ ⟨13, 2, 0, 165370, 77159, 757, 16384⟩
    (by decide) selected_cut_05339

theorem unmarked_context_12_19289_165371 : frontier 9 ⟨165371, by decide⟩
    (prefixCache 12 19289) (prefixPartial 12 19289) = false := by
  decide +kernel

theorem node_context_12_19289_165371 : EJMOriginalGlobalDAGData.nodes 9 ⟨165371, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨165343, by decide⟩,⟨165364, by decide⟩,⟨165370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19289_165371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19289 ⟨165371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19289
    ⟨165371, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨165343, by decide⟩,⟨165364, by decide⟩,⟨165370, by decide⟩]) unmarked_context_12_19289_165371 node_context_12_19289_165371
  intro a
  fin_cases a
  · exact context_13_77156_3444
  · exact context_13_77157_165343
  · exact context_13_77158_165364
  · exact context_13_77159_165370

theorem selected_cut_05340 : selected 9 ⟨165427, by decide⟩
    (prefixPartial 12 19290) = some ⟨12, 2, 0, 165427, 19290, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_19290_165427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19290 ⟨165427, by decide⟩ :=
  accepted_of_selected 12 19290 ⟨165427, by decide⟩ ⟨12, 2, 0, 165427, 19290, 3493, 65536⟩
    (by decide) selected_cut_05340

theorem selected_cut_05341 : selected 9 ⟨165498, by decide⟩
    (prefixPartial 12 19291) = some ⟨12, 2, 0, 165498, 19291, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_19291_165498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19291 ⟨165498, by decide⟩ :=
  accepted_of_selected 12 19291 ⟨165498, by decide⟩ ⟨12, 2, 0, 165498, 19291, 3417, 65536⟩
    (by decide) selected_cut_05341

theorem unmarked_context_11_4822_165499 : frontier 10 ⟨165499, by decide⟩
    (prefixCache 11 4822) (prefixPartial 11 4822) = false := by
  decide +kernel

theorem node_context_11_4822_165499 : EJMOriginalGlobalDAGData.nodes 10 ⟨165499, by decide⟩ =
    .split (coordinate 11) (![⟨165286, by decide⟩,⟨165371, by decide⟩,⟨165427, by decide⟩,⟨165498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4822_165499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4822 ⟨165499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4822
    ⟨165499, by decide⟩ (by decide) (![⟨165286, by decide⟩,⟨165371, by decide⟩,⟨165427, by decide⟩,⟨165498, by decide⟩]) unmarked_context_11_4822_165499 node_context_11_4822_165499
  intro a
  fin_cases a
  · exact context_12_19288_165286
  · exact context_12_19289_165371
  · exact context_12_19290_165427
  · exact context_12_19291_165498

theorem selected_cut_05342 : selected 9 ⟨165542, by decide⟩
    (prefixPartial 12 19292) = some ⟨12, 2, 0, 165542, 19292, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_19292_165542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19292 ⟨165542, by decide⟩ :=
  accepted_of_selected 12 19292 ⟨165542, by decide⟩ ⟨12, 2, 0, 165542, 19292, 2665, 65536⟩
    (by decide) selected_cut_05342

theorem selected_cut_05343 : selected 9 ⟨165619, by decide⟩
    (prefixPartial 12 19293) = some ⟨12, 2, 0, 165619, 19293, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_19293_165619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19293 ⟨165619, by decide⟩ :=
  accepted_of_selected 12 19293 ⟨165619, by decide⟩ ⟨12, 2, 0, 165619, 19293, 3485, 65536⟩
    (by decide) selected_cut_05343

theorem selected_cut_05344 : selected 9 ⟨165677, by decide⟩
    (prefixPartial 12 19294) = some ⟨12, 2, 0, 165677, 19294, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_19294_165677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19294 ⟨165677, by decide⟩ :=
  accepted_of_selected 12 19294 ⟨165677, by decide⟩ ⟨12, 2, 0, 165677, 19294, 3097, 65536⟩
    (by decide) selected_cut_05344

theorem selected_cut_05345 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 77180) = some ⟨13, 1, 0, 3444, 77180, 1, 16384⟩ := by
  decide +kernel

theorem context_13_77180_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77180 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 77180 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 77180, 1, 16384⟩
    (by decide) selected_cut_05345

theorem selected_cut_05346 : selected 8 ⟨165742, by decide⟩
    (prefixPartial 13 77181) = some ⟨13, 2, 0, 165742, 77181, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_77181_165742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77181 ⟨165742, by decide⟩ :=
  accepted_of_selected 13 77181 ⟨165742, by decide⟩ ⟨13, 2, 0, 165742, 77181, 2181, 16384⟩
    (by decide) selected_cut_05346

theorem selected_cut_05347 : selected 8 ⟨165769, by decide⟩
    (prefixPartial 13 77182) = some ⟨13, 2, 0, 165769, 77182, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_77182_165769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77182 ⟨165769, by decide⟩ :=
  accepted_of_selected 13 77182 ⟨165769, by decide⟩ ⟨13, 2, 0, 165769, 77182, 1097, 16384⟩
    (by decide) selected_cut_05347

theorem selected_cut_05348 : selected 8 ⟨165780, by decide⟩
    (prefixPartial 13 77183) = some ⟨13, 2, 0, 165780, 77183, 817, 16384⟩ := by
  decide +kernel

theorem context_13_77183_165780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77183 ⟨165780, by decide⟩ :=
  accepted_of_selected 13 77183 ⟨165780, by decide⟩ ⟨13, 2, 0, 165780, 77183, 817, 16384⟩
    (by decide) selected_cut_05348

theorem unmarked_context_12_19295_165781 : frontier 9 ⟨165781, by decide⟩
    (prefixCache 12 19295) (prefixPartial 12 19295) = false := by
  decide +kernel

theorem node_context_12_19295_165781 : EJMOriginalGlobalDAGData.nodes 9 ⟨165781, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨165742, by decide⟩,⟨165769, by decide⟩,⟨165780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19295_165781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19295 ⟨165781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19295
    ⟨165781, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨165742, by decide⟩,⟨165769, by decide⟩,⟨165780, by decide⟩]) unmarked_context_12_19295_165781 node_context_12_19295_165781
  intro a
  fin_cases a
  · exact context_13_77180_3444
  · exact context_13_77181_165742
  · exact context_13_77182_165769
  · exact context_13_77183_165780

theorem unmarked_context_11_4823_165782 : frontier 10 ⟨165782, by decide⟩
    (prefixCache 11 4823) (prefixPartial 11 4823) = false := by
  decide +kernel

theorem node_context_11_4823_165782 : EJMOriginalGlobalDAGData.nodes 10 ⟨165782, by decide⟩ =
    .split (coordinate 11) (![⟨165542, by decide⟩,⟨165619, by decide⟩,⟨165677, by decide⟩,⟨165781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4823_165782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4823 ⟨165782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4823
    ⟨165782, by decide⟩ (by decide) (![⟨165542, by decide⟩,⟨165619, by decide⟩,⟨165677, by decide⟩,⟨165781, by decide⟩]) unmarked_context_11_4823_165782 node_context_11_4823_165782
  intro a
  fin_cases a
  · exact context_12_19292_165542
  · exact context_12_19293_165619
  · exact context_12_19294_165677
  · exact context_12_19295_165781

theorem unmarked_context_10_1205_165783 : frontier 11 ⟨165783, by decide⟩
    (prefixCache 10 1205) (prefixPartial 10 1205) = false := by
  decide +kernel

theorem node_context_10_1205_165783 : EJMOriginalGlobalDAGData.nodes 11 ⟨165783, by decide⟩ =
    .split (coordinate 10) (![⟨164941, by decide⟩,⟨165224, by decide⟩,⟨165499, by decide⟩,⟨165782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1205_165783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1205 ⟨165783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1205
    ⟨165783, by decide⟩ (by decide) (![⟨164941, by decide⟩,⟨165224, by decide⟩,⟨165499, by decide⟩,⟨165782, by decide⟩]) unmarked_context_10_1205_165783 node_context_10_1205_165783
  intro a
  fin_cases a
  · exact context_11_4820_164941
  · exact context_11_4821_165224
  · exact context_11_4822_165499
  · exact context_11_4823_165782

theorem selected_cut_05349 : selected 9 ⟨165820, by decide⟩
    (prefixPartial 12 19296) = some ⟨12, 2, 0, 165820, 19296, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_19296_165820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19296 ⟨165820, by decide⟩ :=
  accepted_of_selected 12 19296 ⟨165820, by decide⟩ ⟨12, 2, 0, 165820, 19296, 1685, 65536⟩
    (by decide) selected_cut_05349

theorem selected_cut_05350 : selected 9 ⟨165915, by decide⟩
    (prefixPartial 12 19297) = some ⟨12, 2, 0, 165915, 19297, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_19297_165915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19297 ⟨165915, by decide⟩ :=
  accepted_of_selected 12 19297 ⟨165915, by decide⟩ ⟨12, 2, 0, 165915, 19297, 3429, 65536⟩
    (by decide) selected_cut_05350

theorem selected_cut_05351 : selected 9 ⟨165970, by decide⟩
    (prefixPartial 12 19298) = some ⟨12, 2, 0, 165970, 19298, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_19298_165970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19298 ⟨165970, by decide⟩ :=
  accepted_of_selected 12 19298 ⟨165970, by decide⟩ ⟨12, 2, 0, 165970, 19298, 2765, 65536⟩
    (by decide) selected_cut_05351

theorem selected_cut_05352 : selected 9 ⟨166026, by decide⟩
    (prefixPartial 12 19299) = some ⟨12, 2, 0, 166026, 19299, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_19299_166026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19299 ⟨166026, by decide⟩ :=
  accepted_of_selected 12 19299 ⟨166026, by decide⟩ ⟨12, 2, 0, 166026, 19299, 2389, 65536⟩
    (by decide) selected_cut_05352

theorem unmarked_context_11_4824_166027 : frontier 10 ⟨166027, by decide⟩
    (prefixCache 11 4824) (prefixPartial 11 4824) = false := by
  decide +kernel

theorem node_context_11_4824_166027 : EJMOriginalGlobalDAGData.nodes 10 ⟨166027, by decide⟩ =
    .split (coordinate 11) (![⟨165820, by decide⟩,⟨165915, by decide⟩,⟨165970, by decide⟩,⟨166026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4824_166027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4824 ⟨166027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4824
    ⟨166027, by decide⟩ (by decide) (![⟨165820, by decide⟩,⟨165915, by decide⟩,⟨165970, by decide⟩,⟨166026, by decide⟩]) unmarked_context_11_4824_166027 node_context_11_4824_166027
  intro a
  fin_cases a
  · exact context_12_19296_165820
  · exact context_12_19297_165915
  · exact context_12_19298_165970
  · exact context_12_19299_166026

theorem selected_cut_05353 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19300) = some ⟨12, 1, 0, 4595, 19300, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19300_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19300 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19300 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19300, 1, 65536⟩
    (by decide) selected_cut_05353

theorem selected_cut_05354 : selected 9 ⟨166097, by decide⟩
    (prefixPartial 12 19301) = some ⟨12, 2, 0, 166097, 19301, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_19301_166097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19301 ⟨166097, by decide⟩ :=
  accepted_of_selected 12 19301 ⟨166097, by decide⟩ ⟨12, 2, 0, 166097, 19301, 3133, 65536⟩
    (by decide) selected_cut_05354

theorem selected_cut_05355 : selected 9 ⟨166139, by decide⟩
    (prefixPartial 12 19302) = some ⟨12, 2, 0, 166139, 19302, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_19302_166139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19302 ⟨166139, by decide⟩ :=
  accepted_of_selected 12 19302 ⟨166139, by decide⟩ ⟨12, 2, 0, 166139, 19302, 1797, 65536⟩
    (by decide) selected_cut_05355

theorem selected_cut_05356 : selected 9 ⟨166180, by decide⟩
    (prefixPartial 12 19303) = some ⟨12, 2, 0, 166180, 19303, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_19303_166180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19303 ⟨166180, by decide⟩ :=
  accepted_of_selected 12 19303 ⟨166180, by decide⟩ ⟨12, 2, 0, 166180, 19303, 2549, 65536⟩
    (by decide) selected_cut_05356

theorem unmarked_context_11_4825_166181 : frontier 10 ⟨166181, by decide⟩
    (prefixCache 11 4825) (prefixPartial 11 4825) = false := by
  decide +kernel

theorem node_context_11_4825_166181 : EJMOriginalGlobalDAGData.nodes 10 ⟨166181, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨166097, by decide⟩,⟨166139, by decide⟩,⟨166180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4825_166181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4825 ⟨166181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4825
    ⟨166181, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨166097, by decide⟩,⟨166139, by decide⟩,⟨166180, by decide⟩]) unmarked_context_11_4825_166181 node_context_11_4825_166181
  intro a
  fin_cases a
  · exact context_12_19300_4595
  · exact context_12_19301_166097
  · exact context_12_19302_166139
  · exact context_12_19303_166180

theorem selected_cut_05357 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19304) = some ⟨12, 1, 0, 4595, 19304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19304_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19304 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19304 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19304, 1, 65536⟩
    (by decide) selected_cut_05357

theorem selected_cut_05358 : selected 9 ⟨166289, by decide⟩
    (prefixPartial 12 19305) = some ⟨12, 2, 0, 166289, 19305, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_19305_166289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19305 ⟨166289, by decide⟩ :=
  accepted_of_selected 12 19305 ⟨166289, by decide⟩ ⟨12, 2, 0, 166289, 19305, 2573, 65536⟩
    (by decide) selected_cut_05358

theorem selected_cut_05359 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19306) = some ⟨12, 1, 0, 4595, 19306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19306_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19306 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19306 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19306, 1, 65536⟩
    (by decide) selected_cut_05359

theorem selected_cut_05360 : selected 9 ⟨166366, by decide⟩
    (prefixPartial 12 19307) = some ⟨12, 2, 0, 166366, 19307, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_19307_166366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19307 ⟨166366, by decide⟩ :=
  accepted_of_selected 12 19307 ⟨166366, by decide⟩ ⟨12, 2, 0, 166366, 19307, 2957, 65536⟩
    (by decide) selected_cut_05360

theorem unmarked_context_11_4826_166367 : frontier 10 ⟨166367, by decide⟩
    (prefixCache 11 4826) (prefixPartial 11 4826) = false := by
  decide +kernel

theorem node_context_11_4826_166367 : EJMOriginalGlobalDAGData.nodes 10 ⟨166367, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨166289, by decide⟩,⟨4595, by decide⟩,⟨166366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4826_166367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4826 ⟨166367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4826
    ⟨166367, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨166289, by decide⟩,⟨4595, by decide⟩,⟨166366, by decide⟩]) unmarked_context_11_4826_166367 node_context_11_4826_166367
  intro a
  fin_cases a
  · exact context_12_19304_4595
  · exact context_12_19305_166289
  · exact context_12_19306_4595
  · exact context_12_19307_166366

theorem selected_cut_05361 : selected 10 ⟨166432, by decide⟩
    (prefixPartial 11 4827) = some ⟨11, 2, 0, 166432, 4827, 1933, 262144⟩ := by
  decide +kernel

theorem context_11_4827_166432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4827 ⟨166432, by decide⟩ :=
  accepted_of_selected 11 4827 ⟨166432, by decide⟩ ⟨11, 2, 0, 166432, 4827, 1933, 262144⟩
    (by decide) selected_cut_05361

theorem unmarked_context_10_1206_166433 : frontier 11 ⟨166433, by decide⟩
    (prefixCache 10 1206) (prefixPartial 10 1206) = false := by
  decide +kernel

theorem node_context_10_1206_166433 : EJMOriginalGlobalDAGData.nodes 11 ⟨166433, by decide⟩ =
    .split (coordinate 10) (![⟨166027, by decide⟩,⟨166181, by decide⟩,⟨166367, by decide⟩,⟨166432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1206_166433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1206 ⟨166433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1206
    ⟨166433, by decide⟩ (by decide) (![⟨166027, by decide⟩,⟨166181, by decide⟩,⟨166367, by decide⟩,⟨166432, by decide⟩]) unmarked_context_10_1206_166433 node_context_10_1206_166433
  intro a
  fin_cases a
  · exact context_11_4824_166027
  · exact context_11_4825_166181
  · exact context_11_4826_166367
  · exact context_11_4827_166432

theorem selected_cut_05362 : selected 9 ⟨166469, by decide⟩
    (prefixPartial 12 19312) = some ⟨12, 2, 0, 166469, 19312, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_19312_166469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19312 ⟨166469, by decide⟩ :=
  accepted_of_selected 12 19312 ⟨166469, by decide⟩ ⟨12, 2, 0, 166469, 19312, 1833, 65536⟩
    (by decide) selected_cut_05362

theorem selected_cut_05363 : selected 9 ⟨166523, by decide⟩
    (prefixPartial 12 19313) = some ⟨12, 2, 0, 166523, 19313, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_19313_166523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19313 ⟨166523, by decide⟩ :=
  accepted_of_selected 12 19313 ⟨166523, by decide⟩ ⟨12, 2, 0, 166523, 19313, 2345, 65536⟩
    (by decide) selected_cut_05363

theorem selected_cut_05364 : selected 9 ⟨166561, by decide⟩
    (prefixPartial 12 19314) = some ⟨12, 2, 0, 166561, 19314, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_19314_166561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19314 ⟨166561, by decide⟩ :=
  accepted_of_selected 12 19314 ⟨166561, by decide⟩ ⟨12, 2, 0, 166561, 19314, 1893, 65536⟩
    (by decide) selected_cut_05364

theorem selected_cut_05365 : selected 9 ⟨166600, by decide⟩
    (prefixPartial 12 19315) = some ⟨12, 2, 0, 166600, 19315, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_19315_166600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19315 ⟨166600, by decide⟩ :=
  accepted_of_selected 12 19315 ⟨166600, by decide⟩ ⟨12, 2, 0, 166600, 19315, 1561, 65536⟩
    (by decide) selected_cut_05365

theorem unmarked_context_11_4828_166601 : frontier 10 ⟨166601, by decide⟩
    (prefixCache 11 4828) (prefixPartial 11 4828) = false := by
  decide +kernel

theorem node_context_11_4828_166601 : EJMOriginalGlobalDAGData.nodes 10 ⟨166601, by decide⟩ =
    .split (coordinate 11) (![⟨166469, by decide⟩,⟨166523, by decide⟩,⟨166561, by decide⟩,⟨166600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4828_166601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4828 ⟨166601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4828
    ⟨166601, by decide⟩ (by decide) (![⟨166469, by decide⟩,⟨166523, by decide⟩,⟨166561, by decide⟩,⟨166600, by decide⟩]) unmarked_context_11_4828_166601 node_context_11_4828_166601
  intro a
  fin_cases a
  · exact context_12_19312_166469
  · exact context_12_19313_166523
  · exact context_12_19314_166561
  · exact context_12_19315_166600

theorem selected_cut_05366 : selected 9 ⟨166633, by decide⟩
    (prefixPartial 12 19316) = some ⟨12, 2, 0, 166633, 19316, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_19316_166633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19316 ⟨166633, by decide⟩ :=
  accepted_of_selected 12 19316 ⟨166633, by decide⟩ ⟨12, 2, 0, 166633, 19316, 1593, 65536⟩
    (by decide) selected_cut_05366

theorem selected_cut_05367 : selected 9 ⟨166677, by decide⟩
    (prefixPartial 12 19317) = some ⟨12, 2, 0, 166677, 19317, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_19317_166677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19317 ⟨166677, by decide⟩ :=
  accepted_of_selected 12 19317 ⟨166677, by decide⟩ ⟨12, 2, 0, 166677, 19317, 2081, 65536⟩
    (by decide) selected_cut_05367

theorem selected_cut_05368 : selected 9 ⟨166719, by decide⟩
    (prefixPartial 12 19318) = some ⟨12, 2, 0, 166719, 19318, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_19318_166719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19318 ⟨166719, by decide⟩ :=
  accepted_of_selected 12 19318 ⟨166719, by decide⟩ ⟨12, 2, 0, 166719, 19318, 1977, 65536⟩
    (by decide) selected_cut_05368

theorem selected_cut_05369 : selected 9 ⟨166749, by decide⟩
    (prefixPartial 12 19319) = some ⟨12, 2, 0, 166749, 19319, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_19319_166749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19319 ⟨166749, by decide⟩ :=
  accepted_of_selected 12 19319 ⟨166749, by decide⟩ ⟨12, 2, 0, 166749, 19319, 1545, 65536⟩
    (by decide) selected_cut_05369

theorem unmarked_context_11_4829_166750 : frontier 10 ⟨166750, by decide⟩
    (prefixCache 11 4829) (prefixPartial 11 4829) = false := by
  decide +kernel

theorem node_context_11_4829_166750 : EJMOriginalGlobalDAGData.nodes 10 ⟨166750, by decide⟩ =
    .split (coordinate 11) (![⟨166633, by decide⟩,⟨166677, by decide⟩,⟨166719, by decide⟩,⟨166749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4829_166750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4829 ⟨166750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4829
    ⟨166750, by decide⟩ (by decide) (![⟨166633, by decide⟩,⟨166677, by decide⟩,⟨166719, by decide⟩,⟨166749, by decide⟩]) unmarked_context_11_4829_166750 node_context_11_4829_166750
  intro a
  fin_cases a
  · exact context_12_19316_166633
  · exact context_12_19317_166677
  · exact context_12_19318_166719
  · exact context_12_19319_166749

theorem selected_cut_05370 : selected 9 ⟨166776, by decide⟩
    (prefixPartial 12 19320) = some ⟨12, 2, 0, 166776, 19320, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_19320_166776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19320 ⟨166776, by decide⟩ :=
  accepted_of_selected 12 19320 ⟨166776, by decide⟩ ⟨12, 2, 0, 166776, 19320, 1465, 65536⟩
    (by decide) selected_cut_05370

theorem selected_cut_05371 : selected 9 ⟨166831, by decide⟩
    (prefixPartial 12 19321) = some ⟨12, 2, 0, 166831, 19321, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_19321_166831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19321 ⟨166831, by decide⟩ :=
  accepted_of_selected 12 19321 ⟨166831, by decide⟩ ⟨12, 2, 0, 166831, 19321, 2089, 65536⟩
    (by decide) selected_cut_05371

theorem selected_cut_05372 : selected 9 ⟨166862, by decide⟩
    (prefixPartial 12 19322) = some ⟨12, 2, 0, 166862, 19322, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_19322_166862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19322 ⟨166862, by decide⟩ :=
  accepted_of_selected 12 19322 ⟨166862, by decide⟩ ⟨12, 2, 0, 166862, 19322, 1593, 65536⟩
    (by decide) selected_cut_05372

theorem selected_cut_05373 : selected 9 ⟨166886, by decide⟩
    (prefixPartial 12 19323) = some ⟨12, 2, 0, 166886, 19323, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_19323_166886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19323 ⟨166886, by decide⟩ :=
  accepted_of_selected 12 19323 ⟨166886, by decide⟩ ⟨12, 2, 0, 166886, 19323, 1481, 65536⟩
    (by decide) selected_cut_05373

theorem unmarked_context_11_4830_166887 : frontier 10 ⟨166887, by decide⟩
    (prefixCache 11 4830) (prefixPartial 11 4830) = false := by
  decide +kernel

theorem node_context_11_4830_166887 : EJMOriginalGlobalDAGData.nodes 10 ⟨166887, by decide⟩ =
    .split (coordinate 11) (![⟨166776, by decide⟩,⟨166831, by decide⟩,⟨166862, by decide⟩,⟨166886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4830_166887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4830 ⟨166887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4830
    ⟨166887, by decide⟩ (by decide) (![⟨166776, by decide⟩,⟨166831, by decide⟩,⟨166862, by decide⟩,⟨166886, by decide⟩]) unmarked_context_11_4830_166887 node_context_11_4830_166887
  intro a
  fin_cases a
  · exact context_12_19320_166776
  · exact context_12_19321_166831
  · exact context_12_19322_166862
  · exact context_12_19323_166886

theorem selected_cut_05374 : selected 9 ⟨166908, by decide⟩
    (prefixPartial 12 19324) = some ⟨12, 2, 0, 166908, 19324, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_19324_166908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19324 ⟨166908, by decide⟩ :=
  accepted_of_selected 12 19324 ⟨166908, by decide⟩ ⟨12, 2, 0, 166908, 19324, 1145, 65536⟩
    (by decide) selected_cut_05374

theorem selected_cut_05375 : selected 9 ⟨166948, by decide⟩
    (prefixPartial 12 19325) = some ⟨12, 2, 0, 166948, 19325, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_19325_166948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19325 ⟨166948, by decide⟩ :=
  accepted_of_selected 12 19325 ⟨166948, by decide⟩ ⟨12, 2, 0, 166948, 19325, 1633, 65536⟩
    (by decide) selected_cut_05375

theorem selected_cut_05376 : selected 9 ⟨166974, by decide⟩
    (prefixPartial 12 19326) = some ⟨12, 2, 0, 166974, 19326, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_19326_166974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19326 ⟨166974, by decide⟩ :=
  accepted_of_selected 12 19326 ⟨166974, by decide⟩ ⟨12, 2, 0, 166974, 19326, 1317, 65536⟩
    (by decide) selected_cut_05376

theorem selected_cut_05377 : selected 9 ⟨167002, by decide⟩
    (prefixPartial 12 19327) = some ⟨12, 2, 0, 167002, 19327, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_19327_167002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19327 ⟨167002, by decide⟩ :=
  accepted_of_selected 12 19327 ⟨167002, by decide⟩ ⟨12, 2, 0, 167002, 19327, 1569, 65536⟩
    (by decide) selected_cut_05377

theorem unmarked_context_11_4831_167003 : frontier 10 ⟨167003, by decide⟩
    (prefixCache 11 4831) (prefixPartial 11 4831) = false := by
  decide +kernel

theorem node_context_11_4831_167003 : EJMOriginalGlobalDAGData.nodes 10 ⟨167003, by decide⟩ =
    .split (coordinate 11) (![⟨166908, by decide⟩,⟨166948, by decide⟩,⟨166974, by decide⟩,⟨167002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4831_167003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4831 ⟨167003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4831
    ⟨167003, by decide⟩ (by decide) (![⟨166908, by decide⟩,⟨166948, by decide⟩,⟨166974, by decide⟩,⟨167002, by decide⟩]) unmarked_context_11_4831_167003 node_context_11_4831_167003
  intro a
  fin_cases a
  · exact context_12_19324_166908
  · exact context_12_19325_166948
  · exact context_12_19326_166974
  · exact context_12_19327_167002

theorem unmarked_context_10_1207_167004 : frontier 11 ⟨167004, by decide⟩
    (prefixCache 10 1207) (prefixPartial 10 1207) = false := by
  decide +kernel

theorem node_context_10_1207_167004 : EJMOriginalGlobalDAGData.nodes 11 ⟨167004, by decide⟩ =
    .split (coordinate 10) (![⟨166601, by decide⟩,⟨166750, by decide⟩,⟨166887, by decide⟩,⟨167003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1207_167004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1207 ⟨167004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1207
    ⟨167004, by decide⟩ (by decide) (![⟨166601, by decide⟩,⟨166750, by decide⟩,⟨166887, by decide⟩,⟨167003, by decide⟩]) unmarked_context_10_1207_167004 node_context_10_1207_167004
  intro a
  fin_cases a
  · exact context_11_4828_166601
  · exact context_11_4829_166750
  · exact context_11_4830_166887
  · exact context_11_4831_167003

theorem unmarked_context_9_301_167005 : frontier 12 ⟨167005, by decide⟩
    (prefixCache 9 301) (prefixPartial 9 301) = false := by
  decide +kernel

theorem node_context_9_301_167005 : EJMOriginalGlobalDAGData.nodes 12 ⟨167005, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨165783, by decide⟩,⟨166433, by decide⟩,⟨167004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_301_167005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 301 ⟨167005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 301
    ⟨167005, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨165783, by decide⟩,⟨166433, by decide⟩,⟨167004, by decide⟩]) unmarked_context_9_301_167005 node_context_9_301_167005
  intro a
  fin_cases a
  · exact context_10_1204_145424
  · exact context_10_1205_165783
  · exact context_10_1206_166433
  · exact context_10_1207_167004

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
