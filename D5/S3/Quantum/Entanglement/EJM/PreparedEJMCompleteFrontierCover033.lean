/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover032
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03170 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6752) = some ⟨12, 1, 0, 1738, 6752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6752_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6752 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6752 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6752, 1, 65536⟩
    (by decide) selected_cut_03170

theorem selected_cut_03171 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6753) = some ⟨12, 1, 0, 1738, 6753, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6753_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6753 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6753 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6753, 1, 65536⟩
    (by decide) selected_cut_03171

theorem selected_cut_03172 : selected 9 ⟨98874, by decide⟩
    (prefixPartial 12 6754) = some ⟨12, 2, 0, 98874, 6754, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_6754_98874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6754 ⟨98874, by decide⟩ :=
  accepted_of_selected 12 6754 ⟨98874, by decide⟩ ⟨12, 2, 0, 98874, 6754, 2901, 65536⟩
    (by decide) selected_cut_03172

theorem selected_cut_03173 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27020) = some ⟨13, 1, 0, 3444, 27020, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27020_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27020 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27020 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27020, 1, 16384⟩
    (by decide) selected_cut_03173

theorem selected_cut_03174 : selected 8 ⟨98917, by decide⟩
    (prefixPartial 13 27021) = some ⟨13, 2, 0, 98917, 27021, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_27021_98917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27021 ⟨98917, by decide⟩ :=
  accepted_of_selected 13 27021 ⟨98917, by decide⟩ ⟨13, 2, 0, 98917, 27021, 1233, 16384⟩
    (by decide) selected_cut_03174

theorem selected_cut_03175 : selected 8 ⟨98949, by decide⟩
    (prefixPartial 13 27022) = some ⟨13, 2, 0, 98949, 27022, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_27022_98949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27022 ⟨98949, by decide⟩ :=
  accepted_of_selected 13 27022 ⟨98949, by decide⟩ ⟨13, 2, 0, 98949, 27022, 2313, 16384⟩
    (by decide) selected_cut_03175

theorem selected_cut_03176 : selected 8 ⟨98971, by decide⟩
    (prefixPartial 13 27023) = some ⟨13, 2, 0, 98971, 27023, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_27023_98971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27023 ⟨98971, by decide⟩ :=
  accepted_of_selected 13 27023 ⟨98971, by decide⟩ ⟨13, 2, 0, 98971, 27023, 1249, 16384⟩
    (by decide) selected_cut_03176

theorem unmarked_context_12_6755_98972 : frontier 9 ⟨98972, by decide⟩
    (prefixCache 12 6755) (prefixPartial 12 6755) = false := by
  decide +kernel

theorem node_context_12_6755_98972 : EJMOriginalGlobalDAGData.nodes 9 ⟨98972, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨98917, by decide⟩,⟨98949, by decide⟩,⟨98971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6755_98972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6755 ⟨98972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6755
    ⟨98972, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨98917, by decide⟩,⟨98949, by decide⟩,⟨98971, by decide⟩]) unmarked_context_12_6755_98972 node_context_12_6755_98972
  intro a
  fin_cases a
  · exact context_13_27020_3444
  · exact context_13_27021_98917
  · exact context_13_27022_98949
  · exact context_13_27023_98971

theorem unmarked_context_11_1688_98973 : frontier 10 ⟨98973, by decide⟩
    (prefixCache 11 1688) (prefixPartial 11 1688) = false := by
  decide +kernel

theorem node_context_11_1688_98973 : EJMOriginalGlobalDAGData.nodes 10 ⟨98973, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨98874, by decide⟩,⟨98972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1688_98973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1688 ⟨98973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1688
    ⟨98973, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨98874, by decide⟩,⟨98972, by decide⟩]) unmarked_context_11_1688_98973 node_context_11_1688_98973
  intro a
  fin_cases a
  · exact context_12_6752_1738
  · exact context_12_6753_1738
  · exact context_12_6754_98874
  · exact context_12_6755_98972

theorem selected_cut_03177 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6756) = some ⟨12, 1, 0, 1738, 6756, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6756_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6756 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6756 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6756, 1, 65536⟩
    (by decide) selected_cut_03177

theorem selected_cut_03178 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6757) = some ⟨12, 1, 0, 1738, 6757, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6757_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6757 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6757 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6757, 1, 65536⟩
    (by decide) selected_cut_03178

theorem selected_cut_03179 : selected 9 ⟨99048, by decide⟩
    (prefixPartial 12 6758) = some ⟨12, 2, 0, 99048, 6758, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_6758_99048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6758 ⟨99048, by decide⟩ :=
  accepted_of_selected 12 6758 ⟨99048, by decide⟩ ⟨12, 2, 0, 99048, 6758, 3173, 65536⟩
    (by decide) selected_cut_03179

theorem selected_cut_03180 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27036) = some ⟨13, 1, 0, 3444, 27036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27036, 1, 16384⟩
    (by decide) selected_cut_03180

theorem selected_cut_03181 : selected 8 ⟨99080, by decide⟩
    (prefixPartial 13 27037) = some ⟨13, 2, 0, 99080, 27037, 957, 16384⟩ := by
  decide +kernel

theorem context_13_27037_99080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27037 ⟨99080, by decide⟩ :=
  accepted_of_selected 13 27037 ⟨99080, by decide⟩ ⟨13, 2, 0, 99080, 27037, 957, 16384⟩
    (by decide) selected_cut_03181

theorem selected_cut_03182 : selected 8 ⟨99141, by decide⟩
    (prefixPartial 13 27038) = some ⟨13, 2, 0, 99141, 27038, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_27038_99141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27038 ⟨99141, by decide⟩ :=
  accepted_of_selected 13 27038 ⟨99141, by decide⟩ ⟨13, 2, 0, 99141, 27038, 3109, 16384⟩
    (by decide) selected_cut_03182

theorem selected_cut_03183 : selected 8 ⟨99163, by decide⟩
    (prefixPartial 13 27039) = some ⟨13, 2, 0, 99163, 27039, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_27039_99163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27039 ⟨99163, by decide⟩ :=
  accepted_of_selected 13 27039 ⟨99163, by decide⟩ ⟨13, 2, 0, 99163, 27039, 1385, 16384⟩
    (by decide) selected_cut_03183

theorem unmarked_context_12_6759_99164 : frontier 9 ⟨99164, by decide⟩
    (prefixCache 12 6759) (prefixPartial 12 6759) = false := by
  decide +kernel

theorem node_context_12_6759_99164 : EJMOriginalGlobalDAGData.nodes 9 ⟨99164, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨99080, by decide⟩,⟨99141, by decide⟩,⟨99163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6759_99164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6759 ⟨99164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6759
    ⟨99164, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨99080, by decide⟩,⟨99141, by decide⟩,⟨99163, by decide⟩]) unmarked_context_12_6759_99164 node_context_12_6759_99164
  intro a
  fin_cases a
  · exact context_13_27036_3444
  · exact context_13_27037_99080
  · exact context_13_27038_99141
  · exact context_13_27039_99163

theorem unmarked_context_11_1689_99165 : frontier 10 ⟨99165, by decide⟩
    (prefixCache 11 1689) (prefixPartial 11 1689) = false := by
  decide +kernel

theorem node_context_11_1689_99165 : EJMOriginalGlobalDAGData.nodes 10 ⟨99165, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨99048, by decide⟩,⟨99164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1689_99165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1689 ⟨99165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1689
    ⟨99165, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨99048, by decide⟩,⟨99164, by decide⟩]) unmarked_context_11_1689_99165 node_context_11_1689_99165
  intro a
  fin_cases a
  · exact context_12_6756_1738
  · exact context_12_6757_1738
  · exact context_12_6758_99048
  · exact context_12_6759_99164

theorem selected_cut_03184 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6760) = some ⟨12, 1, 0, 1738, 6760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6760_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6760 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6760 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6760, 1, 65536⟩
    (by decide) selected_cut_03184

theorem selected_cut_03185 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6761) = some ⟨12, 1, 0, 1738, 6761, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6761_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6761 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6761 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6761, 1, 65536⟩
    (by decide) selected_cut_03185

theorem selected_cut_03186 : selected 9 ⟨99360, by decide⟩
    (prefixPartial 12 6762) = some ⟨12, 2, 0, 99360, 6762, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_6762_99360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6762 ⟨99360, by decide⟩ :=
  accepted_of_selected 12 6762 ⟨99360, by decide⟩ ⟨12, 2, 0, 99360, 6762, 1797, 65536⟩
    (by decide) selected_cut_03186

theorem selected_cut_03187 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27052) = some ⟨13, 1, 0, 3444, 27052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27052, 1, 16384⟩
    (by decide) selected_cut_03187

theorem selected_cut_03188 : selected 8 ⟨99386, by decide⟩
    (prefixPartial 13 27053) = some ⟨13, 2, 0, 99386, 27053, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_27053_99386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27053 ⟨99386, by decide⟩ :=
  accepted_of_selected 13 27053 ⟨99386, by decide⟩ ⟨13, 2, 0, 99386, 27053, 1005, 16384⟩
    (by decide) selected_cut_03188

theorem selected_cut_03189 : selected 7 ⟨99416, by decide⟩
    (prefixPartial 14 108216) = some ⟨14, 2, 0, 99416, 108216, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_108216_99416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 108216 ⟨99416, by decide⟩ :=
  accepted_of_selected 14 108216 ⟨99416, by decide⟩ ⟨14, 2, 0, 99416, 108216, 1169, 4096⟩
    (by decide) selected_cut_03189

theorem selected_cut_03190 : selected 7 ⟨99450, by decide⟩
    (prefixPartial 14 108217) = some ⟨14, 2, 0, 99450, 108217, 1421, 4096⟩ := by
  decide +kernel

theorem context_14_108217_99450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 108217 ⟨99450, by decide⟩ :=
  accepted_of_selected 14 108217 ⟨99450, by decide⟩ ⟨14, 2, 0, 99450, 108217, 1421, 4096⟩
    (by decide) selected_cut_03190

theorem selected_cut_03191 : selected 7 ⟨99475, by decide⟩
    (prefixPartial 14 108218) = some ⟨14, 2, 0, 99475, 108218, 841, 4096⟩ := by
  decide +kernel

theorem context_14_108218_99475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 108218 ⟨99475, by decide⟩ :=
  accepted_of_selected 14 108218 ⟨99475, by decide⟩ ⟨14, 2, 0, 99475, 108218, 841, 4096⟩
    (by decide) selected_cut_03191

theorem selected_cut_03192 : selected 7 ⟨99493, by decide⟩
    (prefixPartial 14 108219) = some ⟨14, 2, 0, 99493, 108219, 833, 4096⟩ := by
  decide +kernel

theorem context_14_108219_99493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 108219 ⟨99493, by decide⟩ :=
  accepted_of_selected 14 108219 ⟨99493, by decide⟩ ⟨14, 2, 0, 99493, 108219, 833, 4096⟩
    (by decide) selected_cut_03192

theorem unmarked_context_13_27054_99494 : frontier 8 ⟨99494, by decide⟩
    (prefixCache 13 27054) (prefixPartial 13 27054) = false := by
  decide +kernel

theorem node_context_13_27054_99494 : EJMOriginalGlobalDAGData.nodes 8 ⟨99494, by decide⟩ =
    .split (coordinate 13) (![⟨99416, by decide⟩,⟨99450, by decide⟩,⟨99475, by decide⟩,⟨99493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27054_99494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27054 ⟨99494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27054
    ⟨99494, by decide⟩ (by decide) (![⟨99416, by decide⟩,⟨99450, by decide⟩,⟨99475, by decide⟩,⟨99493, by decide⟩]) unmarked_context_13_27054_99494 node_context_13_27054_99494
  intro a
  fin_cases a
  · exact context_14_108216_99416
  · exact context_14_108217_99450
  · exact context_14_108218_99475
  · exact context_14_108219_99493

theorem selected_cut_03193 : selected 8 ⟨99546, by decide⟩
    (prefixPartial 13 27055) = some ⟨13, 2, 0, 99546, 27055, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_27055_99546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27055 ⟨99546, by decide⟩ :=
  accepted_of_selected 13 27055 ⟨99546, by decide⟩ ⟨13, 2, 0, 99546, 27055, 1669, 16384⟩
    (by decide) selected_cut_03193

theorem unmarked_context_12_6763_99547 : frontier 9 ⟨99547, by decide⟩
    (prefixCache 12 6763) (prefixPartial 12 6763) = false := by
  decide +kernel

theorem node_context_12_6763_99547 : EJMOriginalGlobalDAGData.nodes 9 ⟨99547, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨99386, by decide⟩,⟨99494, by decide⟩,⟨99546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6763_99547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6763 ⟨99547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6763
    ⟨99547, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨99386, by decide⟩,⟨99494, by decide⟩,⟨99546, by decide⟩]) unmarked_context_12_6763_99547 node_context_12_6763_99547
  intro a
  fin_cases a
  · exact context_13_27052_3444
  · exact context_13_27053_99386
  · exact context_13_27054_99494
  · exact context_13_27055_99546

theorem unmarked_context_11_1690_99548 : frontier 10 ⟨99548, by decide⟩
    (prefixCache 11 1690) (prefixPartial 11 1690) = false := by
  decide +kernel

theorem node_context_11_1690_99548 : EJMOriginalGlobalDAGData.nodes 10 ⟨99548, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨99360, by decide⟩,⟨99547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1690_99548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1690 ⟨99548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1690
    ⟨99548, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨99360, by decide⟩,⟨99547, by decide⟩]) unmarked_context_11_1690_99548 node_context_11_1690_99548
  intro a
  fin_cases a
  · exact context_12_6760_1738
  · exact context_12_6761_1738
  · exact context_12_6762_99360
  · exact context_12_6763_99547

theorem selected_cut_03194 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6764) = some ⟨12, 1, 0, 1738, 6764, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6764_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6764 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6764 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6764, 1, 65536⟩
    (by decide) selected_cut_03194

theorem selected_cut_03195 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6765) = some ⟨12, 1, 0, 1738, 6765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6765_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6765 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6765 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6765, 1, 65536⟩
    (by decide) selected_cut_03195

theorem selected_cut_03196 : selected 9 ⟨99632, by decide⟩
    (prefixPartial 12 6766) = some ⟨12, 2, 0, 99632, 6766, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_6766_99632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6766 ⟨99632, by decide⟩ :=
  accepted_of_selected 12 6766 ⟨99632, by decide⟩ ⟨12, 2, 0, 99632, 6766, 2837, 65536⟩
    (by decide) selected_cut_03196

theorem selected_cut_03197 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 27068) = some ⟨13, 1, 0, 3444, 27068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_27068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 27068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 27068, 1, 16384⟩
    (by decide) selected_cut_03197

theorem selected_cut_03198 : selected 8 ⟨99644, by decide⟩
    (prefixPartial 13 27069) = some ⟨13, 2, 0, 99644, 27069, 389, 16384⟩ := by
  decide +kernel

theorem context_13_27069_99644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27069 ⟨99644, by decide⟩ :=
  accepted_of_selected 13 27069 ⟨99644, by decide⟩ ⟨13, 2, 0, 99644, 27069, 389, 16384⟩
    (by decide) selected_cut_03198

theorem selected_cut_03199 : selected 8 ⟨99683, by decide⟩
    (prefixPartial 13 27070) = some ⟨13, 2, 0, 99683, 27070, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_27070_99683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27070 ⟨99683, by decide⟩ :=
  accepted_of_selected 13 27070 ⟨99683, by decide⟩ ⟨13, 2, 0, 99683, 27070, 2717, 16384⟩
    (by decide) selected_cut_03199

theorem selected_cut_03200 : selected 8 ⟨99711, by decide⟩
    (prefixPartial 13 27071) = some ⟨13, 2, 0, 99711, 27071, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_27071_99711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27071 ⟨99711, by decide⟩ :=
  accepted_of_selected 13 27071 ⟨99711, by decide⟩ ⟨13, 2, 0, 99711, 27071, 1353, 16384⟩
    (by decide) selected_cut_03200

theorem unmarked_context_12_6767_99712 : frontier 9 ⟨99712, by decide⟩
    (prefixCache 12 6767) (prefixPartial 12 6767) = false := by
  decide +kernel

theorem node_context_12_6767_99712 : EJMOriginalGlobalDAGData.nodes 9 ⟨99712, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨99644, by decide⟩,⟨99683, by decide⟩,⟨99711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6767_99712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6767 ⟨99712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6767
    ⟨99712, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨99644, by decide⟩,⟨99683, by decide⟩,⟨99711, by decide⟩]) unmarked_context_12_6767_99712 node_context_12_6767_99712
  intro a
  fin_cases a
  · exact context_13_27068_3444
  · exact context_13_27069_99644
  · exact context_13_27070_99683
  · exact context_13_27071_99711

theorem unmarked_context_11_1691_99713 : frontier 10 ⟨99713, by decide⟩
    (prefixCache 11 1691) (prefixPartial 11 1691) = false := by
  decide +kernel

theorem node_context_11_1691_99713 : EJMOriginalGlobalDAGData.nodes 10 ⟨99713, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨99632, by decide⟩,⟨99712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1691_99713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1691 ⟨99713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1691
    ⟨99713, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨99632, by decide⟩,⟨99712, by decide⟩]) unmarked_context_11_1691_99713 node_context_11_1691_99713
  intro a
  fin_cases a
  · exact context_12_6764_1738
  · exact context_12_6765_1738
  · exact context_12_6766_99632
  · exact context_12_6767_99712

theorem unmarked_context_10_422_99714 : frontier 11 ⟨99714, by decide⟩
    (prefixCache 10 422) (prefixPartial 10 422) = false := by
  decide +kernel

theorem node_context_10_422_99714 : EJMOriginalGlobalDAGData.nodes 11 ⟨99714, by decide⟩ =
    .split (coordinate 10) (![⟨98973, by decide⟩,⟨99165, by decide⟩,⟨99548, by decide⟩,⟨99713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_422_99714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 422 ⟨99714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 422
    ⟨99714, by decide⟩ (by decide) (![⟨98973, by decide⟩,⟨99165, by decide⟩,⟨99548, by decide⟩,⟨99713, by decide⟩]) unmarked_context_10_422_99714 node_context_10_422_99714
  intro a
  fin_cases a
  · exact context_11_1688_98973
  · exact context_11_1689_99165
  · exact context_11_1690_99548
  · exact context_11_1691_99713

theorem selected_cut_03201 : selected 10 ⟨99832, by decide⟩
    (prefixPartial 11 1692) = some ⟨11, 2, 0, 99832, 1692, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_1692_99832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1692 ⟨99832, by decide⟩ :=
  accepted_of_selected 11 1692 ⟨99832, by decide⟩ ⟨11, 2, 0, 99832, 1692, 3137, 262144⟩
    (by decide) selected_cut_03201

theorem selected_cut_03202 : selected 10 ⟨99980, by decide⟩
    (prefixPartial 11 1693) = some ⟨11, 2, 0, 99980, 1693, 3869, 262144⟩ := by
  decide +kernel

theorem context_11_1693_99980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1693 ⟨99980, by decide⟩ :=
  accepted_of_selected 11 1693 ⟨99980, by decide⟩ ⟨11, 2, 0, 99980, 1693, 3869, 262144⟩
    (by decide) selected_cut_03202

theorem selected_cut_03203 : selected 10 ⟨100064, by decide⟩
    (prefixPartial 11 1694) = some ⟨11, 2, 0, 100064, 1694, 2833, 262144⟩ := by
  decide +kernel

theorem context_11_1694_100064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1694 ⟨100064, by decide⟩ :=
  accepted_of_selected 11 1694 ⟨100064, by decide⟩ ⟨11, 2, 0, 100064, 1694, 2833, 262144⟩
    (by decide) selected_cut_03203

theorem selected_cut_03204 : selected 10 ⟨100174, by decide⟩
    (prefixPartial 11 1695) = some ⟨11, 2, 0, 100174, 1695, 2977, 262144⟩ := by
  decide +kernel

theorem context_11_1695_100174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1695 ⟨100174, by decide⟩ :=
  accepted_of_selected 11 1695 ⟨100174, by decide⟩ ⟨11, 2, 0, 100174, 1695, 2977, 262144⟩
    (by decide) selected_cut_03204

theorem unmarked_context_10_423_100175 : frontier 11 ⟨100175, by decide⟩
    (prefixCache 10 423) (prefixPartial 10 423) = false := by
  decide +kernel

theorem node_context_10_423_100175 : EJMOriginalGlobalDAGData.nodes 11 ⟨100175, by decide⟩ =
    .split (coordinate 10) (![⟨99832, by decide⟩,⟨99980, by decide⟩,⟨100064, by decide⟩,⟨100174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_423_100175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 423 ⟨100175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 423
    ⟨100175, by decide⟩ (by decide) (![⟨99832, by decide⟩,⟨99980, by decide⟩,⟨100064, by decide⟩,⟨100174, by decide⟩]) unmarked_context_10_423_100175 node_context_10_423_100175
  intro a
  fin_cases a
  · exact context_11_1692_99832
  · exact context_11_1693_99980
  · exact context_11_1694_100064
  · exact context_11_1695_100174

theorem unmarked_context_9_105_100176 : frontier 12 ⟨100176, by decide⟩
    (prefixCache 9 105) (prefixPartial 9 105) = false := by
  decide +kernel

theorem node_context_9_105_100176 : EJMOriginalGlobalDAGData.nodes 12 ⟨100176, by decide⟩ =
    .split (coordinate 9) (![⟨97262, by decide⟩,⟨98790, by decide⟩,⟨99714, by decide⟩,⟨100175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_105_100176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 105 ⟨100176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 105
    ⟨100176, by decide⟩ (by decide) (![⟨97262, by decide⟩,⟨98790, by decide⟩,⟨99714, by decide⟩,⟨100175, by decide⟩]) unmarked_context_9_105_100176 node_context_9_105_100176
  intro a
  fin_cases a
  · exact context_10_420_97262
  · exact context_10_421_98790
  · exact context_10_422_99714
  · exact context_10_423_100175

theorem selected_cut_03205 : selected 9 ⟨100213, by decide⟩
    (prefixPartial 12 6784) = some ⟨12, 2, 0, 100213, 6784, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_6784_100213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6784 ⟨100213, by decide⟩ :=
  accepted_of_selected 12 6784 ⟨100213, by decide⟩ ⟨12, 2, 0, 100213, 6784, 1777, 65536⟩
    (by decide) selected_cut_03205

theorem selected_cut_03206 : selected 9 ⟨100266, by decide⟩
    (prefixPartial 12 6785) = some ⟨12, 2, 0, 100266, 6785, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_6785_100266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6785 ⟨100266, by decide⟩ :=
  accepted_of_selected 12 6785 ⟨100266, by decide⟩ ⟨12, 2, 0, 100266, 6785, 2937, 65536⟩
    (by decide) selected_cut_03206

theorem selected_cut_03207 : selected 9 ⟨100310, by decide⟩
    (prefixPartial 12 6786) = some ⟨12, 2, 0, 100310, 6786, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_6786_100310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6786 ⟨100310, by decide⟩ :=
  accepted_of_selected 12 6786 ⟨100310, by decide⟩ ⟨12, 2, 0, 100310, 6786, 2553, 65536⟩
    (by decide) selected_cut_03207

theorem selected_cut_03208 : selected 9 ⟨100354, by decide⟩
    (prefixPartial 12 6787) = some ⟨12, 2, 0, 100354, 6787, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_6787_100354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6787 ⟨100354, by decide⟩ :=
  accepted_of_selected 12 6787 ⟨100354, by decide⟩ ⟨12, 2, 0, 100354, 6787, 2741, 65536⟩
    (by decide) selected_cut_03208

theorem unmarked_context_11_1696_100355 : frontier 10 ⟨100355, by decide⟩
    (prefixCache 11 1696) (prefixPartial 11 1696) = false := by
  decide +kernel

theorem node_context_11_1696_100355 : EJMOriginalGlobalDAGData.nodes 10 ⟨100355, by decide⟩ =
    .split (coordinate 11) (![⟨100213, by decide⟩,⟨100266, by decide⟩,⟨100310, by decide⟩,⟨100354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1696_100355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1696 ⟨100355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1696
    ⟨100355, by decide⟩ (by decide) (![⟨100213, by decide⟩,⟨100266, by decide⟩,⟨100310, by decide⟩,⟨100354, by decide⟩]) unmarked_context_11_1696_100355 node_context_11_1696_100355
  intro a
  fin_cases a
  · exact context_12_6784_100213
  · exact context_12_6785_100266
  · exact context_12_6786_100310
  · exact context_12_6787_100354

theorem selected_cut_03209 : selected 9 ⟨100418, by decide⟩
    (prefixPartial 12 6788) = some ⟨12, 2, 0, 100418, 6788, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_6788_100418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6788 ⟨100418, by decide⟩ :=
  accepted_of_selected 12 6788 ⟨100418, by decide⟩ ⟨12, 2, 0, 100418, 6788, 2077, 65536⟩
    (by decide) selected_cut_03209

theorem selected_cut_03210 : selected 9 ⟨100480, by decide⟩
    (prefixPartial 12 6789) = some ⟨12, 2, 0, 100480, 6789, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_6789_100480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6789 ⟨100480, by decide⟩ :=
  accepted_of_selected 12 6789 ⟨100480, by decide⟩ ⟨12, 2, 0, 100480, 6789, 3301, 65536⟩
    (by decide) selected_cut_03210

theorem selected_cut_03211 : selected 9 ⟨100538, by decide⟩
    (prefixPartial 12 6790) = some ⟨12, 2, 0, 100538, 6790, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_6790_100538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6790 ⟨100538, by decide⟩ :=
  accepted_of_selected 12 6790 ⟨100538, by decide⟩ ⟨12, 2, 0, 100538, 6790, 3037, 65536⟩
    (by decide) selected_cut_03211

theorem selected_cut_03212 : selected 9 ⟨100588, by decide⟩
    (prefixPartial 12 6791) = some ⟨12, 2, 0, 100588, 6791, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_6791_100588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6791 ⟨100588, by decide⟩ :=
  accepted_of_selected 12 6791 ⟨100588, by decide⟩ ⟨12, 2, 0, 100588, 6791, 3189, 65536⟩
    (by decide) selected_cut_03212

theorem unmarked_context_11_1697_100589 : frontier 10 ⟨100589, by decide⟩
    (prefixCache 11 1697) (prefixPartial 11 1697) = false := by
  decide +kernel

theorem node_context_11_1697_100589 : EJMOriginalGlobalDAGData.nodes 10 ⟨100589, by decide⟩ =
    .split (coordinate 11) (![⟨100418, by decide⟩,⟨100480, by decide⟩,⟨100538, by decide⟩,⟨100588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1697_100589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1697 ⟨100589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1697
    ⟨100589, by decide⟩ (by decide) (![⟨100418, by decide⟩,⟨100480, by decide⟩,⟨100538, by decide⟩,⟨100588, by decide⟩]) unmarked_context_11_1697_100589 node_context_11_1697_100589
  intro a
  fin_cases a
  · exact context_12_6788_100418
  · exact context_12_6789_100480
  · exact context_12_6790_100538
  · exact context_12_6791_100588

theorem selected_cut_03213 : selected 9 ⟨100618, by decide⟩
    (prefixPartial 12 6792) = some ⟨12, 2, 0, 100618, 6792, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_6792_100618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6792 ⟨100618, by decide⟩ :=
  accepted_of_selected 12 6792 ⟨100618, by decide⟩ ⟨12, 2, 0, 100618, 6792, 1393, 65536⟩
    (by decide) selected_cut_03213

theorem selected_cut_03214 : selected 9 ⟨100670, by decide⟩
    (prefixPartial 12 6793) = some ⟨12, 2, 0, 100670, 6793, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_6793_100670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6793 ⟨100670, by decide⟩ :=
  accepted_of_selected 12 6793 ⟨100670, by decide⟩ ⟨12, 2, 0, 100670, 6793, 2521, 65536⟩
    (by decide) selected_cut_03214

theorem selected_cut_03215 : selected 9 ⟨100745, by decide⟩
    (prefixPartial 12 6794) = some ⟨12, 2, 0, 100745, 6794, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_6794_100745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6794 ⟨100745, by decide⟩ :=
  accepted_of_selected 12 6794 ⟨100745, by decide⟩ ⟨12, 2, 0, 100745, 6794, 3245, 65536⟩
    (by decide) selected_cut_03215

theorem selected_cut_03216 : selected 9 ⟨100784, by decide⟩
    (prefixPartial 12 6795) = some ⟨12, 2, 0, 100784, 6795, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_6795_100784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6795 ⟨100784, by decide⟩ :=
  accepted_of_selected 12 6795 ⟨100784, by decide⟩ ⟨12, 2, 0, 100784, 6795, 2177, 65536⟩
    (by decide) selected_cut_03216

theorem unmarked_context_11_1698_100785 : frontier 10 ⟨100785, by decide⟩
    (prefixCache 11 1698) (prefixPartial 11 1698) = false := by
  decide +kernel

theorem node_context_11_1698_100785 : EJMOriginalGlobalDAGData.nodes 10 ⟨100785, by decide⟩ =
    .split (coordinate 11) (![⟨100618, by decide⟩,⟨100670, by decide⟩,⟨100745, by decide⟩,⟨100784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1698_100785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1698 ⟨100785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1698
    ⟨100785, by decide⟩ (by decide) (![⟨100618, by decide⟩,⟨100670, by decide⟩,⟨100745, by decide⟩,⟨100784, by decide⟩]) unmarked_context_11_1698_100785 node_context_11_1698_100785
  intro a
  fin_cases a
  · exact context_12_6792_100618
  · exact context_12_6793_100670
  · exact context_12_6794_100745
  · exact context_12_6795_100784

theorem selected_cut_03217 : selected 9 ⟨100838, by decide⟩
    (prefixPartial 12 6796) = some ⟨12, 2, 0, 100838, 6796, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_6796_100838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6796 ⟨100838, by decide⟩ :=
  accepted_of_selected 12 6796 ⟨100838, by decide⟩ ⟨12, 2, 0, 100838, 6796, 1817, 65536⟩
    (by decide) selected_cut_03217

theorem selected_cut_03218 : selected 9 ⟨100894, by decide⟩
    (prefixPartial 12 6797) = some ⟨12, 2, 0, 100894, 6797, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_6797_100894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6797 ⟨100894, by decide⟩ :=
  accepted_of_selected 12 6797 ⟨100894, by decide⟩ ⟨12, 2, 0, 100894, 6797, 2865, 65536⟩
    (by decide) selected_cut_03218

theorem selected_cut_03219 : selected 9 ⟨100945, by decide⟩
    (prefixPartial 12 6798) = some ⟨12, 2, 0, 100945, 6798, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_6798_100945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6798 ⟨100945, by decide⟩ :=
  accepted_of_selected 12 6798 ⟨100945, by decide⟩ ⟨12, 2, 0, 100945, 6798, 2501, 65536⟩
    (by decide) selected_cut_03219

theorem selected_cut_03220 : selected 9 ⟨100989, by decide⟩
    (prefixPartial 12 6799) = some ⟨12, 2, 0, 100989, 6799, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_6799_100989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6799 ⟨100989, by decide⟩ :=
  accepted_of_selected 12 6799 ⟨100989, by decide⟩ ⟨12, 2, 0, 100989, 6799, 2585, 65536⟩
    (by decide) selected_cut_03220

theorem unmarked_context_11_1699_100990 : frontier 10 ⟨100990, by decide⟩
    (prefixCache 11 1699) (prefixPartial 11 1699) = false := by
  decide +kernel

theorem node_context_11_1699_100990 : EJMOriginalGlobalDAGData.nodes 10 ⟨100990, by decide⟩ =
    .split (coordinate 11) (![⟨100838, by decide⟩,⟨100894, by decide⟩,⟨100945, by decide⟩,⟨100989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1699_100990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1699 ⟨100990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1699
    ⟨100990, by decide⟩ (by decide) (![⟨100838, by decide⟩,⟨100894, by decide⟩,⟨100945, by decide⟩,⟨100989, by decide⟩]) unmarked_context_11_1699_100990 node_context_11_1699_100990
  intro a
  fin_cases a
  · exact context_12_6796_100838
  · exact context_12_6797_100894
  · exact context_12_6798_100945
  · exact context_12_6799_100989

theorem unmarked_context_10_424_100991 : frontier 11 ⟨100991, by decide⟩
    (prefixCache 10 424) (prefixPartial 10 424) = false := by
  decide +kernel

theorem node_context_10_424_100991 : EJMOriginalGlobalDAGData.nodes 11 ⟨100991, by decide⟩ =
    .split (coordinate 10) (![⟨100355, by decide⟩,⟨100589, by decide⟩,⟨100785, by decide⟩,⟨100990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_424_100991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 424 ⟨100991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 424
    ⟨100991, by decide⟩ (by decide) (![⟨100355, by decide⟩,⟨100589, by decide⟩,⟨100785, by decide⟩,⟨100990, by decide⟩]) unmarked_context_10_424_100991 node_context_10_424_100991
  intro a
  fin_cases a
  · exact context_11_1696_100355
  · exact context_11_1697_100589
  · exact context_11_1698_100785
  · exact context_11_1699_100990

theorem selected_cut_03221 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6800) = some ⟨12, 1, 0, 1738, 6800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6800_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6800 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6800 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6800, 1, 65536⟩
    (by decide) selected_cut_03221

theorem selected_cut_03222 : selected 9 ⟨101052, by decide⟩
    (prefixPartial 12 6801) = some ⟨12, 2, 0, 101052, 6801, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_6801_101052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6801 ⟨101052, by decide⟩ :=
  accepted_of_selected 12 6801 ⟨101052, by decide⟩ ⟨12, 2, 0, 101052, 6801, 1929, 65536⟩
    (by decide) selected_cut_03222

theorem selected_cut_03223 : selected 9 ⟨101096, by decide⟩
    (prefixPartial 12 6802) = some ⟨12, 2, 0, 101096, 6802, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_6802_101096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6802 ⟨101096, by decide⟩ :=
  accepted_of_selected 12 6802 ⟨101096, by decide⟩ ⟨12, 2, 0, 101096, 6802, 2373, 65536⟩
    (by decide) selected_cut_03223

theorem selected_cut_03224 : selected 9 ⟨101149, by decide⟩
    (prefixPartial 12 6803) = some ⟨12, 2, 0, 101149, 6803, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_6803_101149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6803 ⟨101149, by decide⟩ :=
  accepted_of_selected 12 6803 ⟨101149, by decide⟩ ⟨12, 2, 0, 101149, 6803, 2577, 65536⟩
    (by decide) selected_cut_03224

theorem unmarked_context_11_1700_101150 : frontier 10 ⟨101150, by decide⟩
    (prefixCache 11 1700) (prefixPartial 11 1700) = false := by
  decide +kernel

theorem node_context_11_1700_101150 : EJMOriginalGlobalDAGData.nodes 10 ⟨101150, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨101052, by decide⟩,⟨101096, by decide⟩,⟨101149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1700_101150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1700 ⟨101150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1700
    ⟨101150, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨101052, by decide⟩,⟨101096, by decide⟩,⟨101149, by decide⟩]) unmarked_context_11_1700_101150 node_context_11_1700_101150
  intro a
  fin_cases a
  · exact context_12_6800_1738
  · exact context_12_6801_101052
  · exact context_12_6802_101096
  · exact context_12_6803_101149

theorem selected_cut_03225 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6804) = some ⟨12, 1, 0, 1738, 6804, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6804_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6804 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6804 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6804, 1, 65536⟩
    (by decide) selected_cut_03225

theorem selected_cut_03226 : selected 9 ⟨101218, by decide⟩
    (prefixPartial 12 6805) = some ⟨12, 2, 0, 101218, 6805, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_6805_101218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6805 ⟨101218, by decide⟩ :=
  accepted_of_selected 12 6805 ⟨101218, by decide⟩ ⟨12, 2, 0, 101218, 6805, 1961, 65536⟩
    (by decide) selected_cut_03226

theorem selected_cut_03227 : selected 9 ⟨101274, by decide⟩
    (prefixPartial 12 6806) = some ⟨12, 2, 0, 101274, 6806, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_6806_101274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6806 ⟨101274, by decide⟩ :=
  accepted_of_selected 12 6806 ⟨101274, by decide⟩ ⟨12, 2, 0, 101274, 6806, 2513, 65536⟩
    (by decide) selected_cut_03227

theorem selected_cut_03228 : selected 9 ⟨101330, by decide⟩
    (prefixPartial 12 6807) = some ⟨12, 2, 0, 101330, 6807, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_6807_101330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6807 ⟨101330, by decide⟩ :=
  accepted_of_selected 12 6807 ⟨101330, by decide⟩ ⟨12, 2, 0, 101330, 6807, 2629, 65536⟩
    (by decide) selected_cut_03228

theorem unmarked_context_11_1701_101331 : frontier 10 ⟨101331, by decide⟩
    (prefixCache 11 1701) (prefixPartial 11 1701) = false := by
  decide +kernel

theorem node_context_11_1701_101331 : EJMOriginalGlobalDAGData.nodes 10 ⟨101331, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨101218, by decide⟩,⟨101274, by decide⟩,⟨101330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1701_101331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1701 ⟨101331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1701
    ⟨101331, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨101218, by decide⟩,⟨101274, by decide⟩,⟨101330, by decide⟩]) unmarked_context_11_1701_101331 node_context_11_1701_101331
  intro a
  fin_cases a
  · exact context_12_6804_1738
  · exact context_12_6805_101218
  · exact context_12_6806_101274
  · exact context_12_6807_101330

theorem selected_cut_03229 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6808) = some ⟨12, 1, 0, 1738, 6808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6808_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6808 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6808 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6808, 1, 65536⟩
    (by decide) selected_cut_03229

theorem selected_cut_03230 : selected 9 ⟨101389, by decide⟩
    (prefixPartial 12 6809) = some ⟨12, 2, 0, 101389, 6809, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_6809_101389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6809 ⟨101389, by decide⟩ :=
  accepted_of_selected 12 6809 ⟨101389, by decide⟩ ⟨12, 2, 0, 101389, 6809, 1709, 65536⟩
    (by decide) selected_cut_03230

theorem selected_cut_03231 : selected 9 ⟨101480, by decide⟩
    (prefixPartial 12 6810) = some ⟨12, 2, 0, 101480, 6810, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_6810_101480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6810 ⟨101480, by decide⟩ :=
  accepted_of_selected 12 6810 ⟨101480, by decide⟩ ⟨12, 2, 0, 101480, 6810, 2837, 65536⟩
    (by decide) selected_cut_03231

theorem selected_cut_03232 : selected 9 ⟨101523, by decide⟩
    (prefixPartial 12 6811) = some ⟨12, 2, 0, 101523, 6811, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_6811_101523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6811 ⟨101523, by decide⟩ :=
  accepted_of_selected 12 6811 ⟨101523, by decide⟩ ⟨12, 2, 0, 101523, 6811, 2129, 65536⟩
    (by decide) selected_cut_03232

theorem unmarked_context_11_1702_101524 : frontier 10 ⟨101524, by decide⟩
    (prefixCache 11 1702) (prefixPartial 11 1702) = false := by
  decide +kernel

theorem node_context_11_1702_101524 : EJMOriginalGlobalDAGData.nodes 10 ⟨101524, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨101389, by decide⟩,⟨101480, by decide⟩,⟨101523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1702_101524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1702 ⟨101524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1702
    ⟨101524, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨101389, by decide⟩,⟨101480, by decide⟩,⟨101523, by decide⟩]) unmarked_context_11_1702_101524 node_context_11_1702_101524
  intro a
  fin_cases a
  · exact context_12_6808_1738
  · exact context_12_6809_101389
  · exact context_12_6810_101480
  · exact context_12_6811_101523

theorem selected_cut_03233 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 6812) = some ⟨12, 1, 0, 1738, 6812, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6812_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6812 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 6812 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 6812, 1, 65536⟩
    (by decide) selected_cut_03233

theorem selected_cut_03234 : selected 9 ⟨101576, by decide⟩
    (prefixPartial 12 6813) = some ⟨12, 2, 0, 101576, 6813, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_6813_101576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6813 ⟨101576, by decide⟩ :=
  accepted_of_selected 12 6813 ⟨101576, by decide⟩ ⟨12, 2, 0, 101576, 6813, 1681, 65536⟩
    (by decide) selected_cut_03234

theorem selected_cut_03235 : selected 9 ⟨101612, by decide⟩
    (prefixPartial 12 6814) = some ⟨12, 2, 0, 101612, 6814, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_6814_101612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6814 ⟨101612, by decide⟩ :=
  accepted_of_selected 12 6814 ⟨101612, by decide⟩ ⟨12, 2, 0, 101612, 6814, 1997, 65536⟩
    (by decide) selected_cut_03235

theorem selected_cut_03236 : selected 9 ⟨101661, by decide⟩
    (prefixPartial 12 6815) = some ⟨12, 2, 0, 101661, 6815, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_6815_101661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6815 ⟨101661, by decide⟩ :=
  accepted_of_selected 12 6815 ⟨101661, by decide⟩ ⟨12, 2, 0, 101661, 6815, 2125, 65536⟩
    (by decide) selected_cut_03236

theorem unmarked_context_11_1703_101662 : frontier 10 ⟨101662, by decide⟩
    (prefixCache 11 1703) (prefixPartial 11 1703) = false := by
  decide +kernel

theorem node_context_11_1703_101662 : EJMOriginalGlobalDAGData.nodes 10 ⟨101662, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨101576, by decide⟩,⟨101612, by decide⟩,⟨101661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1703_101662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1703 ⟨101662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1703
    ⟨101662, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨101576, by decide⟩,⟨101612, by decide⟩,⟨101661, by decide⟩]) unmarked_context_11_1703_101662 node_context_11_1703_101662
  intro a
  fin_cases a
  · exact context_12_6812_1738
  · exact context_12_6813_101576
  · exact context_12_6814_101612
  · exact context_12_6815_101661

theorem unmarked_context_10_425_101663 : frontier 11 ⟨101663, by decide⟩
    (prefixCache 10 425) (prefixPartial 10 425) = false := by
  decide +kernel

theorem node_context_10_425_101663 : EJMOriginalGlobalDAGData.nodes 11 ⟨101663, by decide⟩ =
    .split (coordinate 10) (![⟨101150, by decide⟩,⟨101331, by decide⟩,⟨101524, by decide⟩,⟨101662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_425_101663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 425 ⟨101663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 425
    ⟨101663, by decide⟩ (by decide) (![⟨101150, by decide⟩,⟨101331, by decide⟩,⟨101524, by decide⟩,⟨101662, by decide⟩]) unmarked_context_10_425_101663 node_context_10_425_101663
  intro a
  fin_cases a
  · exact context_11_1700_101150
  · exact context_11_1701_101331
  · exact context_11_1702_101524
  · exact context_11_1703_101662

theorem selected_cut_03237 : selected 10 ⟨101724, by decide⟩
    (prefixPartial 11 1704) = some ⟨11, 2, 0, 101724, 1704, 2849, 262144⟩ := by
  decide +kernel

theorem context_11_1704_101724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1704 ⟨101724, by decide⟩ :=
  accepted_of_selected 11 1704 ⟨101724, by decide⟩ ⟨11, 2, 0, 101724, 1704, 2849, 262144⟩
    (by decide) selected_cut_03237

theorem selected_cut_03238 : selected 10 ⟨101802, by decide⟩
    (prefixPartial 11 1705) = some ⟨11, 2, 0, 101802, 1705, 3277, 262144⟩ := by
  decide +kernel

theorem context_11_1705_101802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1705 ⟨101802, by decide⟩ :=
  accepted_of_selected 11 1705 ⟨101802, by decide⟩ ⟨11, 2, 0, 101802, 1705, 3277, 262144⟩
    (by decide) selected_cut_03238

theorem selected_cut_03239 : selected 10 ⟨101855, by decide⟩
    (prefixPartial 11 1706) = some ⟨11, 2, 0, 101855, 1706, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_1706_101855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1706 ⟨101855, by decide⟩ :=
  accepted_of_selected 11 1706 ⟨101855, by decide⟩ ⟨11, 2, 0, 101855, 1706, 2061, 262144⟩
    (by decide) selected_cut_03239

theorem selected_cut_03240 : selected 10 ⟨101893, by decide⟩
    (prefixPartial 11 1707) = some ⟨11, 2, 0, 101893, 1707, 2549, 262144⟩ := by
  decide +kernel

theorem context_11_1707_101893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1707 ⟨101893, by decide⟩ :=
  accepted_of_selected 11 1707 ⟨101893, by decide⟩ ⟨11, 2, 0, 101893, 1707, 2549, 262144⟩
    (by decide) selected_cut_03240

theorem unmarked_context_10_426_101894 : frontier 11 ⟨101894, by decide⟩
    (prefixCache 10 426) (prefixPartial 10 426) = false := by
  decide +kernel

theorem node_context_10_426_101894 : EJMOriginalGlobalDAGData.nodes 11 ⟨101894, by decide⟩ =
    .split (coordinate 10) (![⟨101724, by decide⟩,⟨101802, by decide⟩,⟨101855, by decide⟩,⟨101893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_426_101894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 426 ⟨101894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 426
    ⟨101894, by decide⟩ (by decide) (![⟨101724, by decide⟩,⟨101802, by decide⟩,⟨101855, by decide⟩,⟨101893, by decide⟩]) unmarked_context_10_426_101894 node_context_10_426_101894
  intro a
  fin_cases a
  · exact context_11_1704_101724
  · exact context_11_1705_101802
  · exact context_11_1706_101855
  · exact context_11_1707_101893

theorem selected_cut_03241 : selected 10 ⟨101954, by decide⟩
    (prefixPartial 11 1708) = some ⟨11, 2, 0, 101954, 1708, 1173, 262144⟩ := by
  decide +kernel

theorem context_11_1708_101954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1708 ⟨101954, by decide⟩ :=
  accepted_of_selected 11 1708 ⟨101954, by decide⟩ ⟨11, 2, 0, 101954, 1708, 1173, 262144⟩
    (by decide) selected_cut_03241

theorem selected_cut_03242 : selected 10 ⟨102011, by decide⟩
    (prefixPartial 11 1709) = some ⟨11, 2, 0, 102011, 1709, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_1709_102011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1709 ⟨102011, by decide⟩ :=
  accepted_of_selected 11 1709 ⟨102011, by decide⟩ ⟨11, 2, 0, 102011, 1709, 1289, 262144⟩
    (by decide) selected_cut_03242

theorem selected_cut_03243 : selected 10 ⟨102042, by decide⟩
    (prefixPartial 11 1710) = some ⟨11, 2, 0, 102042, 1710, 1041, 262144⟩ := by
  decide +kernel

theorem context_11_1710_102042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1710 ⟨102042, by decide⟩ :=
  accepted_of_selected 11 1710 ⟨102042, by decide⟩ ⟨11, 2, 0, 102042, 1710, 1041, 262144⟩
    (by decide) selected_cut_03243

theorem selected_cut_03244 : selected 10 ⟨102068, by decide⟩
    (prefixPartial 11 1711) = some ⟨11, 2, 0, 102068, 1711, 1053, 262144⟩ := by
  decide +kernel

theorem context_11_1711_102068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1711 ⟨102068, by decide⟩ :=
  accepted_of_selected 11 1711 ⟨102068, by decide⟩ ⟨11, 2, 0, 102068, 1711, 1053, 262144⟩
    (by decide) selected_cut_03244

theorem unmarked_context_10_427_102069 : frontier 11 ⟨102069, by decide⟩
    (prefixCache 10 427) (prefixPartial 10 427) = false := by
  decide +kernel

theorem node_context_10_427_102069 : EJMOriginalGlobalDAGData.nodes 11 ⟨102069, by decide⟩ =
    .split (coordinate 10) (![⟨101954, by decide⟩,⟨102011, by decide⟩,⟨102042, by decide⟩,⟨102068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_427_102069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 427 ⟨102069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 427
    ⟨102069, by decide⟩ (by decide) (![⟨101954, by decide⟩,⟨102011, by decide⟩,⟨102042, by decide⟩,⟨102068, by decide⟩]) unmarked_context_10_427_102069 node_context_10_427_102069
  intro a
  fin_cases a
  · exact context_11_1708_101954
  · exact context_11_1709_102011
  · exact context_11_1710_102042
  · exact context_11_1711_102068

theorem unmarked_context_9_106_102070 : frontier 12 ⟨102070, by decide⟩
    (prefixCache 9 106) (prefixPartial 9 106) = false := by
  decide +kernel

theorem node_context_9_106_102070 : EJMOriginalGlobalDAGData.nodes 12 ⟨102070, by decide⟩ =
    .split (coordinate 9) (![⟨100991, by decide⟩,⟨101663, by decide⟩,⟨101894, by decide⟩,⟨102069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_106_102070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 106 ⟨102070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 106
    ⟨102070, by decide⟩ (by decide) (![⟨100991, by decide⟩,⟨101663, by decide⟩,⟨101894, by decide⟩,⟨102069, by decide⟩]) unmarked_context_9_106_102070 node_context_9_106_102070
  intro a
  fin_cases a
  · exact context_10_424_100991
  · exact context_10_425_101663
  · exact context_10_426_101894
  · exact context_10_427_102069

theorem selected_cut_03245 : selected 9 ⟨102084, by decide⟩
    (prefixPartial 12 6848) = some ⟨12, 2, 0, 102084, 6848, 897, 65536⟩ := by
  decide +kernel

theorem context_12_6848_102084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6848 ⟨102084, by decide⟩ :=
  accepted_of_selected 12 6848 ⟨102084, by decide⟩ ⟨12, 2, 0, 102084, 6848, 897, 65536⟩
    (by decide) selected_cut_03245

theorem selected_cut_03246 : selected 9 ⟨102105, by decide⟩
    (prefixPartial 12 6849) = some ⟨12, 2, 0, 102105, 6849, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_6849_102105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6849 ⟨102105, by decide⟩ :=
  accepted_of_selected 12 6849 ⟨102105, by decide⟩ ⟨12, 2, 0, 102105, 6849, 1321, 65536⟩
    (by decide) selected_cut_03246

theorem selected_cut_03247 : selected 9 ⟨102124, by decide⟩
    (prefixPartial 12 6850) = some ⟨12, 2, 0, 102124, 6850, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_6850_102124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6850 ⟨102124, by decide⟩ :=
  accepted_of_selected 12 6850 ⟨102124, by decide⟩ ⟨12, 2, 0, 102124, 6850, 1265, 65536⟩
    (by decide) selected_cut_03247

theorem selected_cut_03248 : selected 9 ⟨102136, by decide⟩
    (prefixPartial 12 6851) = some ⟨12, 2, 0, 102136, 6851, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_6851_102136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6851 ⟨102136, by decide⟩ :=
  accepted_of_selected 12 6851 ⟨102136, by decide⟩ ⟨12, 2, 0, 102136, 6851, 1165, 65536⟩
    (by decide) selected_cut_03248

theorem unmarked_context_11_1712_102137 : frontier 10 ⟨102137, by decide⟩
    (prefixCache 11 1712) (prefixPartial 11 1712) = false := by
  decide +kernel

theorem node_context_11_1712_102137 : EJMOriginalGlobalDAGData.nodes 10 ⟨102137, by decide⟩ =
    .split (coordinate 11) (![⟨102084, by decide⟩,⟨102105, by decide⟩,⟨102124, by decide⟩,⟨102136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1712_102137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1712 ⟨102137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1712
    ⟨102137, by decide⟩ (by decide) (![⟨102084, by decide⟩,⟨102105, by decide⟩,⟨102124, by decide⟩,⟨102136, by decide⟩]) unmarked_context_11_1712_102137 node_context_11_1712_102137
  intro a
  fin_cases a
  · exact context_12_6848_102084
  · exact context_12_6849_102105
  · exact context_12_6850_102124
  · exact context_12_6851_102136

theorem selected_cut_03249 : selected 9 ⟨102164, by decide⟩
    (prefixPartial 12 6852) = some ⟨12, 2, 0, 102164, 6852, 829, 65536⟩ := by
  decide +kernel

theorem context_12_6852_102164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6852 ⟨102164, by decide⟩ :=
  accepted_of_selected 12 6852 ⟨102164, by decide⟩ ⟨12, 2, 0, 102164, 6852, 829, 65536⟩
    (by decide) selected_cut_03249

theorem selected_cut_03250 : selected 9 ⟨102201, by decide⟩
    (prefixPartial 12 6853) = some ⟨12, 2, 0, 102201, 6853, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_6853_102201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6853 ⟨102201, by decide⟩ :=
  accepted_of_selected 12 6853 ⟨102201, by decide⟩ ⟨12, 2, 0, 102201, 6853, 1197, 65536⟩
    (by decide) selected_cut_03250

theorem selected_cut_03251 : selected 9 ⟨102230, by decide⟩
    (prefixPartial 12 6854) = some ⟨12, 2, 0, 102230, 6854, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_6854_102230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6854 ⟨102230, by decide⟩ :=
  accepted_of_selected 12 6854 ⟨102230, by decide⟩ ⟨12, 2, 0, 102230, 6854, 1141, 65536⟩
    (by decide) selected_cut_03251

theorem selected_cut_03252 : selected 9 ⟨102248, by decide⟩
    (prefixPartial 12 6855) = some ⟨12, 2, 0, 102248, 6855, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_6855_102248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6855 ⟨102248, by decide⟩ :=
  accepted_of_selected 12 6855 ⟨102248, by decide⟩ ⟨12, 2, 0, 102248, 6855, 1049, 65536⟩
    (by decide) selected_cut_03252

theorem unmarked_context_11_1713_102249 : frontier 10 ⟨102249, by decide⟩
    (prefixCache 11 1713) (prefixPartial 11 1713) = false := by
  decide +kernel

theorem node_context_11_1713_102249 : EJMOriginalGlobalDAGData.nodes 10 ⟨102249, by decide⟩ =
    .split (coordinate 11) (![⟨102164, by decide⟩,⟨102201, by decide⟩,⟨102230, by decide⟩,⟨102248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1713_102249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1713 ⟨102249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1713
    ⟨102249, by decide⟩ (by decide) (![⟨102164, by decide⟩,⟨102201, by decide⟩,⟨102230, by decide⟩,⟨102248, by decide⟩]) unmarked_context_11_1713_102249 node_context_11_1713_102249
  intro a
  fin_cases a
  · exact context_12_6852_102164
  · exact context_12_6853_102201
  · exact context_12_6854_102230
  · exact context_12_6855_102248

theorem selected_cut_03253 : selected 10 ⟨102344, by decide⟩
    (prefixPartial 11 1714) = some ⟨11, 2, 0, 102344, 1714, 3389, 262144⟩ := by
  decide +kernel

theorem context_11_1714_102344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1714 ⟨102344, by decide⟩ :=
  accepted_of_selected 11 1714 ⟨102344, by decide⟩ ⟨11, 2, 0, 102344, 1714, 3389, 262144⟩
    (by decide) selected_cut_03253

theorem selected_cut_03254 : selected 10 ⟨102496, by decide⟩
    (prefixPartial 11 1715) = some ⟨11, 2, 0, 102496, 1715, 3377, 262144⟩ := by
  decide +kernel

theorem context_11_1715_102496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1715 ⟨102496, by decide⟩ :=
  accepted_of_selected 11 1715 ⟨102496, by decide⟩ ⟨11, 2, 0, 102496, 1715, 3377, 262144⟩
    (by decide) selected_cut_03254

theorem unmarked_context_10_428_102497 : frontier 11 ⟨102497, by decide⟩
    (prefixCache 10 428) (prefixPartial 10 428) = false := by
  decide +kernel

theorem node_context_10_428_102497 : EJMOriginalGlobalDAGData.nodes 11 ⟨102497, by decide⟩ =
    .split (coordinate 10) (![⟨102137, by decide⟩,⟨102249, by decide⟩,⟨102344, by decide⟩,⟨102496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_428_102497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 428 ⟨102497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 428
    ⟨102497, by decide⟩ (by decide) (![⟨102137, by decide⟩,⟨102249, by decide⟩,⟨102344, by decide⟩,⟨102496, by decide⟩]) unmarked_context_10_428_102497 node_context_10_428_102497
  intro a
  fin_cases a
  · exact context_11_1712_102137
  · exact context_11_1713_102249
  · exact context_11_1714_102344
  · exact context_11_1715_102496

theorem selected_cut_03255 : selected 10 ⟨102585, by decide⟩
    (prefixPartial 11 1716) = some ⟨11, 2, 0, 102585, 1716, 2005, 262144⟩ := by
  decide +kernel

theorem context_11_1716_102585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1716 ⟨102585, by decide⟩ :=
  accepted_of_selected 11 1716 ⟨102585, by decide⟩ ⟨11, 2, 0, 102585, 1716, 2005, 262144⟩
    (by decide) selected_cut_03255

theorem selected_cut_03256 : selected 10 ⟨102646, by decide⟩
    (prefixPartial 11 1717) = some ⟨11, 2, 0, 102646, 1717, 1573, 262144⟩ := by
  decide +kernel

theorem context_11_1717_102646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1717 ⟨102646, by decide⟩ :=
  accepted_of_selected 11 1717 ⟨102646, by decide⟩ ⟨11, 2, 0, 102646, 1717, 1573, 262144⟩
    (by decide) selected_cut_03256

theorem selected_cut_03257 : selected 10 ⟨102718, by decide⟩
    (prefixPartial 11 1718) = some ⟨11, 2, 0, 102718, 1718, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_1718_102718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1718 ⟨102718, by decide⟩ :=
  accepted_of_selected 11 1718 ⟨102718, by decide⟩ ⟨11, 2, 0, 102718, 1718, 1397, 262144⟩
    (by decide) selected_cut_03257

theorem selected_cut_03258 : selected 10 ⟨102760, by decide⟩
    (prefixPartial 11 1719) = some ⟨11, 2, 0, 102760, 1719, 1033, 262144⟩ := by
  decide +kernel

theorem context_11_1719_102760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1719 ⟨102760, by decide⟩ :=
  accepted_of_selected 11 1719 ⟨102760, by decide⟩ ⟨11, 2, 0, 102760, 1719, 1033, 262144⟩
    (by decide) selected_cut_03258

theorem unmarked_context_10_429_102761 : frontier 11 ⟨102761, by decide⟩
    (prefixCache 10 429) (prefixPartial 10 429) = false := by
  decide +kernel

theorem node_context_10_429_102761 : EJMOriginalGlobalDAGData.nodes 11 ⟨102761, by decide⟩ =
    .split (coordinate 10) (![⟨102585, by decide⟩,⟨102646, by decide⟩,⟨102718, by decide⟩,⟨102760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_429_102761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 429 ⟨102761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 429
    ⟨102761, by decide⟩ (by decide) (![⟨102585, by decide⟩,⟨102646, by decide⟩,⟨102718, by decide⟩,⟨102760, by decide⟩]) unmarked_context_10_429_102761 node_context_10_429_102761
  intro a
  fin_cases a
  · exact context_11_1716_102585
  · exact context_11_1717_102646
  · exact context_11_1718_102718
  · exact context_11_1719_102760

theorem selected_cut_03259 : selected 11 ⟨102849, by decide⟩
    (prefixPartial 10 430) = some ⟨10, 2, 0, 102849, 430, 1357, 1048576⟩ := by
  decide +kernel

theorem context_10_430_102849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 430 ⟨102849, by decide⟩ :=
  accepted_of_selected 10 430 ⟨102849, by decide⟩ ⟨10, 2, 0, 102849, 430, 1357, 1048576⟩
    (by decide) selected_cut_03259

theorem selected_cut_03260 : selected 11 ⟨102864, by decide⟩
    (prefixPartial 10 431) = some ⟨10, 2, 0, 102864, 431, 253, 1048576⟩ := by
  decide +kernel

theorem context_10_431_102864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 431 ⟨102864, by decide⟩ :=
  accepted_of_selected 10 431 ⟨102864, by decide⟩ ⟨10, 2, 0, 102864, 431, 253, 1048576⟩
    (by decide) selected_cut_03260

theorem unmarked_context_9_107_102865 : frontier 12 ⟨102865, by decide⟩
    (prefixCache 9 107) (prefixPartial 9 107) = false := by
  decide +kernel

theorem node_context_9_107_102865 : EJMOriginalGlobalDAGData.nodes 12 ⟨102865, by decide⟩ =
    .split (coordinate 9) (![⟨102497, by decide⟩,⟨102761, by decide⟩,⟨102849, by decide⟩,⟨102864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_107_102865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 107 ⟨102865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 107
    ⟨102865, by decide⟩ (by decide) (![⟨102497, by decide⟩,⟨102761, by decide⟩,⟨102849, by decide⟩,⟨102864, by decide⟩]) unmarked_context_9_107_102865 node_context_9_107_102865
  intro a
  fin_cases a
  · exact context_10_428_102497
  · exact context_10_429_102761
  · exact context_10_430_102849
  · exact context_10_431_102864

theorem unmarked_context_8_26_102866 : frontier 13 ⟨102866, by decide⟩
    (prefixCache 8 26) (prefixPartial 8 26) = false := by
  decide +kernel

theorem node_context_8_26_102866 : EJMOriginalGlobalDAGData.nodes 13 ⟨102866, by decide⟩ =
    .split (coordinate 8) (![⟨95117, by decide⟩,⟨100176, by decide⟩,⟨102070, by decide⟩,⟨102865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_26_102866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 26 ⟨102866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 26
    ⟨102866, by decide⟩ (by decide) (![⟨95117, by decide⟩,⟨100176, by decide⟩,⟨102070, by decide⟩,⟨102865, by decide⟩]) unmarked_context_8_26_102866 node_context_8_26_102866
  intro a
  fin_cases a
  · exact context_9_104_95117
  · exact context_9_105_100176
  · exact context_9_106_102070
  · exact context_9_107_102865

theorem selected_cut_03261 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 6912) = some ⟨12, 1, 0, 34034, 6912, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6912_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6912 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 6912 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 6912, 1, 65536⟩
    (by decide) selected_cut_03261

theorem selected_cut_03262 : selected 7 ⟨102908, by decide⟩
    (prefixPartial 14 110608) = some ⟨14, 2, 0, 102908, 110608, 1609, 4096⟩ := by
  decide +kernel

theorem context_14_110608_102908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110608 ⟨102908, by decide⟩ :=
  accepted_of_selected 14 110608 ⟨102908, by decide⟩ ⟨14, 2, 0, 102908, 110608, 1609, 4096⟩
    (by decide) selected_cut_03262

theorem selected_cut_03263 : selected 7 ⟨102940, by decide⟩
    (prefixPartial 14 110609) = some ⟨14, 2, 0, 102940, 110609, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_110609_102940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110609 ⟨102940, by decide⟩ :=
  accepted_of_selected 14 110609 ⟨102940, by decide⟩ ⟨14, 2, 0, 102940, 110609, 1437, 4096⟩
    (by decide) selected_cut_03263

theorem selected_cut_03264 : selected 7 ⟨102965, by decide⟩
    (prefixPartial 14 110610) = some ⟨14, 2, 0, 102965, 110610, 1385, 4096⟩ := by
  decide +kernel

theorem context_14_110610_102965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110610 ⟨102965, by decide⟩ :=
  accepted_of_selected 14 110610 ⟨102965, by decide⟩ ⟨14, 2, 0, 102965, 110610, 1385, 4096⟩
    (by decide) selected_cut_03264

theorem selected_cut_03265 : selected 7 ⟨102989, by decide⟩
    (prefixPartial 14 110611) = some ⟨14, 2, 0, 102989, 110611, 1209, 4096⟩ := by
  decide +kernel

theorem context_14_110611_102989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 110611 ⟨102989, by decide⟩ :=
  accepted_of_selected 14 110611 ⟨102989, by decide⟩ ⟨14, 2, 0, 102989, 110611, 1209, 4096⟩
    (by decide) selected_cut_03265

theorem unmarked_context_13_27652_102990 : frontier 8 ⟨102990, by decide⟩
    (prefixCache 13 27652) (prefixPartial 13 27652) = false := by
  decide +kernel

theorem node_context_13_27652_102990 : EJMOriginalGlobalDAGData.nodes 8 ⟨102990, by decide⟩ =
    .split (coordinate 13) (![⟨102908, by decide⟩,⟨102940, by decide⟩,⟨102965, by decide⟩,⟨102989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_27652_102990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27652 ⟨102990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 27652
    ⟨102990, by decide⟩ (by decide) (![⟨102908, by decide⟩,⟨102940, by decide⟩,⟨102965, by decide⟩,⟨102989, by decide⟩]) unmarked_context_13_27652_102990 node_context_13_27652_102990
  intro a
  fin_cases a
  · exact context_14_110608_102908
  · exact context_14_110609_102940
  · exact context_14_110610_102965
  · exact context_14_110611_102989

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
