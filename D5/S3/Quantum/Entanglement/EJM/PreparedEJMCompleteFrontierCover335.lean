/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover334
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32163 : selected 9 ⟨826013, by decide⟩
    (prefixPartial 12 107847) = some ⟨12, 2, 0, 826013, 107847, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_107847_826013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107847 ⟨826013, by decide⟩ :=
  accepted_of_selected 12 107847 ⟨826013, by decide⟩ ⟨12, 2, 0, 826013, 107847, 3837, 65536⟩
    (by decide) selected_cut_32163

theorem unmarked_context_11_26961_826014 : frontier 10 ⟨826014, by decide⟩
    (prefixCache 11 26961) (prefixPartial 11 26961) = false := by
  decide +kernel

theorem node_context_11_26961_826014 : EJMOriginalGlobalDAGData.nodes 10 ⟨826014, by decide⟩ =
    .split (coordinate 11) (![⟨825888, by decide⟩,⟨692443, by decide⟩,⟨825934, by decide⟩,⟨826013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26961_826014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26961 ⟨826014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26961
    ⟨826014, by decide⟩ (by decide) (![⟨825888, by decide⟩,⟨692443, by decide⟩,⟨825934, by decide⟩,⟨826013, by decide⟩]) unmarked_context_11_26961_826014 node_context_11_26961_826014
  intro a
  fin_cases a
  · exact context_12_107844_825888
  · exact context_12_107845_692443
  · exact context_12_107846_825934
  · exact context_12_107847_826013

theorem selected_cut_32164 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431392) = some ⟨13, 1, 0, 3444, 431392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431392, 1, 16384⟩
    (by decide) selected_cut_32164

theorem selected_cut_32165 : selected 8 ⟨826045, by decide⟩
    (prefixPartial 13 431393) = some ⟨13, 2, 0, 826045, 431393, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_431393_826045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431393 ⟨826045, by decide⟩ :=
  accepted_of_selected 13 431393 ⟨826045, by decide⟩ ⟨13, 2, 0, 826045, 431393, 1849, 16384⟩
    (by decide) selected_cut_32165

theorem selected_cut_32166 : selected 8 ⟨826072, by decide⟩
    (prefixPartial 13 431394) = some ⟨13, 2, 0, 826072, 431394, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_431394_826072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431394 ⟨826072, by decide⟩ :=
  accepted_of_selected 13 431394 ⟨826072, by decide⟩ ⟨13, 2, 0, 826072, 431394, 1541, 16384⟩
    (by decide) selected_cut_32166

theorem selected_cut_32167 : selected 8 ⟨826082, by decide⟩
    (prefixPartial 13 431395) = some ⟨13, 2, 0, 826082, 431395, 865, 16384⟩ := by
  decide +kernel

theorem context_13_431395_826082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431395 ⟨826082, by decide⟩ :=
  accepted_of_selected 13 431395 ⟨826082, by decide⟩ ⟨13, 2, 0, 826082, 431395, 865, 16384⟩
    (by decide) selected_cut_32167

theorem unmarked_context_12_107848_826083 : frontier 9 ⟨826083, by decide⟩
    (prefixCache 12 107848) (prefixPartial 12 107848) = false := by
  decide +kernel

theorem node_context_12_107848_826083 : EJMOriginalGlobalDAGData.nodes 9 ⟨826083, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨826045, by decide⟩,⟨826072, by decide⟩,⟨826082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107848_826083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107848 ⟨826083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107848
    ⟨826083, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨826045, by decide⟩,⟨826072, by decide⟩,⟨826082, by decide⟩]) unmarked_context_12_107848_826083 node_context_12_107848_826083
  intro a
  fin_cases a
  · exact context_13_431392_3444
  · exact context_13_431393_826045
  · exact context_13_431394_826072
  · exact context_13_431395_826082

theorem selected_cut_32168 : selected 9 ⟨826134, by decide⟩
    (prefixPartial 12 107849) = some ⟨12, 2, 0, 826134, 107849, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_107849_826134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107849 ⟨826134, by decide⟩ :=
  accepted_of_selected 12 107849 ⟨826134, by decide⟩ ⟨12, 2, 0, 826134, 107849, 3433, 65536⟩
    (by decide) selected_cut_32168

theorem selected_cut_32169 : selected 9 ⟨826194, by decide⟩
    (prefixPartial 12 107850) = some ⟨12, 2, 0, 826194, 107850, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_107850_826194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107850 ⟨826194, by decide⟩ :=
  accepted_of_selected 12 107850 ⟨826194, by decide⟩ ⟨12, 2, 0, 826194, 107850, 3849, 65536⟩
    (by decide) selected_cut_32169

theorem selected_cut_32170 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431404) = some ⟨13, 1, 0, 3444, 431404, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431404_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431404 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431404 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431404, 1, 16384⟩
    (by decide) selected_cut_32170

theorem selected_cut_32171 : selected 8 ⟨826228, by decide⟩
    (prefixPartial 13 431405) = some ⟨13, 2, 0, 826228, 431405, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_431405_826228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431405 ⟨826228, by decide⟩ :=
  accepted_of_selected 13 431405 ⟨826228, by decide⟩ ⟨13, 2, 0, 826228, 431405, 1781, 16384⟩
    (by decide) selected_cut_32171

theorem selected_cut_32172 : selected 8 ⟨826258, by decide⟩
    (prefixPartial 13 431406) = some ⟨13, 2, 0, 826258, 431406, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_431406_826258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431406 ⟨826258, by decide⟩ :=
  accepted_of_selected 13 431406 ⟨826258, by decide⟩ ⟨13, 2, 0, 826258, 431406, 1685, 16384⟩
    (by decide) selected_cut_32172

theorem selected_cut_32173 : selected 8 ⟨826265, by decide⟩
    (prefixPartial 13 431407) = some ⟨13, 2, 0, 826265, 431407, 825, 16384⟩ := by
  decide +kernel

theorem context_13_431407_826265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431407 ⟨826265, by decide⟩ :=
  accepted_of_selected 13 431407 ⟨826265, by decide⟩ ⟨13, 2, 0, 826265, 431407, 825, 16384⟩
    (by decide) selected_cut_32173

theorem unmarked_context_12_107851_826266 : frontier 9 ⟨826266, by decide⟩
    (prefixCache 12 107851) (prefixPartial 12 107851) = false := by
  decide +kernel

theorem node_context_12_107851_826266 : EJMOriginalGlobalDAGData.nodes 9 ⟨826266, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨826228, by decide⟩,⟨826258, by decide⟩,⟨826265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107851_826266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107851 ⟨826266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107851
    ⟨826266, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨826228, by decide⟩,⟨826258, by decide⟩,⟨826265, by decide⟩]) unmarked_context_12_107851_826266 node_context_12_107851_826266
  intro a
  fin_cases a
  · exact context_13_431404_3444
  · exact context_13_431405_826228
  · exact context_13_431406_826258
  · exact context_13_431407_826265

theorem unmarked_context_11_26962_826267 : frontier 10 ⟨826267, by decide⟩
    (prefixCache 11 26962) (prefixPartial 11 26962) = false := by
  decide +kernel

theorem node_context_11_26962_826267 : EJMOriginalGlobalDAGData.nodes 10 ⟨826267, by decide⟩ =
    .split (coordinate 11) (![⟨826083, by decide⟩,⟨826134, by decide⟩,⟨826194, by decide⟩,⟨826266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26962_826267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26962 ⟨826267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26962
    ⟨826267, by decide⟩ (by decide) (![⟨826083, by decide⟩,⟨826134, by decide⟩,⟨826194, by decide⟩,⟨826266, by decide⟩]) unmarked_context_11_26962_826267 node_context_11_26962_826267
  intro a
  fin_cases a
  · exact context_12_107848_826083
  · exact context_12_107849_826134
  · exact context_12_107850_826194
  · exact context_12_107851_826266

theorem selected_cut_32174 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431408) = some ⟨13, 1, 0, 3444, 431408, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431408_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431408 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431408 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431408, 1, 16384⟩
    (by decide) selected_cut_32174

theorem selected_cut_32175 : selected 8 ⟨826298, by decide⟩
    (prefixPartial 13 431409) = some ⟨13, 2, 0, 826298, 431409, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_431409_826298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431409 ⟨826298, by decide⟩ :=
  accepted_of_selected 13 431409 ⟨826298, by decide⟩ ⟨13, 2, 0, 826298, 431409, 2133, 16384⟩
    (by decide) selected_cut_32175

theorem selected_cut_32176 : selected 8 ⟨826326, by decide⟩
    (prefixPartial 13 431410) = some ⟨13, 2, 0, 826326, 431410, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_431410_826326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431410 ⟨826326, by decide⟩ :=
  accepted_of_selected 13 431410 ⟨826326, by decide⟩ ⟨13, 2, 0, 826326, 431410, 1509, 16384⟩
    (by decide) selected_cut_32176

theorem selected_cut_32177 : selected 8 ⟨826333, by decide⟩
    (prefixPartial 13 431411) = some ⟨13, 2, 0, 826333, 431411, 917, 16384⟩ := by
  decide +kernel

theorem context_13_431411_826333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431411 ⟨826333, by decide⟩ :=
  accepted_of_selected 13 431411 ⟨826333, by decide⟩ ⟨13, 2, 0, 826333, 431411, 917, 16384⟩
    (by decide) selected_cut_32177

theorem unmarked_context_12_107852_826334 : frontier 9 ⟨826334, by decide⟩
    (prefixCache 12 107852) (prefixPartial 12 107852) = false := by
  decide +kernel

theorem node_context_12_107852_826334 : EJMOriginalGlobalDAGData.nodes 9 ⟨826334, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨826298, by decide⟩,⟨826326, by decide⟩,⟨826333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107852_826334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107852 ⟨826334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107852
    ⟨826334, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨826298, by decide⟩,⟨826326, by decide⟩,⟨826333, by decide⟩]) unmarked_context_12_107852_826334 node_context_12_107852_826334
  intro a
  fin_cases a
  · exact context_13_431408_3444
  · exact context_13_431409_826298
  · exact context_13_431410_826326
  · exact context_13_431411_826333

theorem selected_cut_32178 : selected 9 ⟨826386, by decide⟩
    (prefixPartial 12 107853) = some ⟨12, 2, 0, 826386, 107853, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_107853_826386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107853 ⟨826386, by decide⟩ :=
  accepted_of_selected 12 107853 ⟨826386, by decide⟩ ⟨12, 2, 0, 826386, 107853, 3565, 65536⟩
    (by decide) selected_cut_32178

theorem selected_cut_32179 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431416) = some ⟨13, 1, 0, 3444, 431416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431416, 1, 16384⟩
    (by decide) selected_cut_32179

theorem selected_cut_32180 : selected 8 ⟨826415, by decide⟩
    (prefixPartial 13 431417) = some ⟨13, 2, 0, 826415, 431417, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_431417_826415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431417 ⟨826415, by decide⟩ :=
  accepted_of_selected 13 431417 ⟨826415, by decide⟩ ⟨13, 2, 0, 826415, 431417, 1813, 16384⟩
    (by decide) selected_cut_32180

theorem selected_cut_32181 : selected 8 ⟨826437, by decide⟩
    (prefixPartial 13 431418) = some ⟨13, 2, 0, 826437, 431418, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_431418_826437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431418 ⟨826437, by decide⟩ :=
  accepted_of_selected 13 431418 ⟨826437, by decide⟩ ⟨13, 2, 0, 826437, 431418, 1401, 16384⟩
    (by decide) selected_cut_32181

theorem selected_cut_32182 : selected 8 ⟨826445, by decide⟩
    (prefixPartial 13 431419) = some ⟨13, 2, 0, 826445, 431419, 993, 16384⟩ := by
  decide +kernel

theorem context_13_431419_826445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431419 ⟨826445, by decide⟩ :=
  accepted_of_selected 13 431419 ⟨826445, by decide⟩ ⟨13, 2, 0, 826445, 431419, 993, 16384⟩
    (by decide) selected_cut_32182

theorem unmarked_context_12_107854_826446 : frontier 9 ⟨826446, by decide⟩
    (prefixCache 12 107854) (prefixPartial 12 107854) = false := by
  decide +kernel

theorem node_context_12_107854_826446 : EJMOriginalGlobalDAGData.nodes 9 ⟨826446, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨826415, by decide⟩,⟨826437, by decide⟩,⟨826445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107854_826446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107854 ⟨826446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107854
    ⟨826446, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨826415, by decide⟩,⟨826437, by decide⟩,⟨826445, by decide⟩]) unmarked_context_12_107854_826446 node_context_12_107854_826446
  intro a
  fin_cases a
  · exact context_13_431416_3444
  · exact context_13_431417_826415
  · exact context_13_431418_826437
  · exact context_13_431419_826445

theorem selected_cut_32183 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431420) = some ⟨13, 1, 0, 3444, 431420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431420, 1, 16384⟩
    (by decide) selected_cut_32183

theorem selected_cut_32184 : selected 8 ⟨826475, by decide⟩
    (prefixPartial 13 431421) = some ⟨13, 2, 0, 826475, 431421, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_431421_826475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431421 ⟨826475, by decide⟩ :=
  accepted_of_selected 13 431421 ⟨826475, by decide⟩ ⟨13, 2, 0, 826475, 431421, 1921, 16384⟩
    (by decide) selected_cut_32184

theorem selected_cut_32185 : selected 8 ⟨826505, by decide⟩
    (prefixPartial 13 431422) = some ⟨13, 2, 0, 826505, 431422, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_431422_826505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431422 ⟨826505, by decide⟩ :=
  accepted_of_selected 13 431422 ⟨826505, by decide⟩ ⟨13, 2, 0, 826505, 431422, 1657, 16384⟩
    (by decide) selected_cut_32185

theorem selected_cut_32186 : selected 8 ⟨826512, by decide⟩
    (prefixPartial 13 431423) = some ⟨13, 2, 0, 826512, 431423, 921, 16384⟩ := by
  decide +kernel

theorem context_13_431423_826512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431423 ⟨826512, by decide⟩ :=
  accepted_of_selected 13 431423 ⟨826512, by decide⟩ ⟨13, 2, 0, 826512, 431423, 921, 16384⟩
    (by decide) selected_cut_32186

theorem unmarked_context_12_107855_826513 : frontier 9 ⟨826513, by decide⟩
    (prefixCache 12 107855) (prefixPartial 12 107855) = false := by
  decide +kernel

theorem node_context_12_107855_826513 : EJMOriginalGlobalDAGData.nodes 9 ⟨826513, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨826475, by decide⟩,⟨826505, by decide⟩,⟨826512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107855_826513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107855 ⟨826513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107855
    ⟨826513, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨826475, by decide⟩,⟨826505, by decide⟩,⟨826512, by decide⟩]) unmarked_context_12_107855_826513 node_context_12_107855_826513
  intro a
  fin_cases a
  · exact context_13_431420_3444
  · exact context_13_431421_826475
  · exact context_13_431422_826505
  · exact context_13_431423_826512

theorem unmarked_context_11_26963_826514 : frontier 10 ⟨826514, by decide⟩
    (prefixCache 11 26963) (prefixPartial 11 26963) = false := by
  decide +kernel

theorem node_context_11_26963_826514 : EJMOriginalGlobalDAGData.nodes 10 ⟨826514, by decide⟩ =
    .split (coordinate 11) (![⟨826334, by decide⟩,⟨826386, by decide⟩,⟨826446, by decide⟩,⟨826513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26963_826514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26963 ⟨826514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26963
    ⟨826514, by decide⟩ (by decide) (![⟨826334, by decide⟩,⟨826386, by decide⟩,⟨826446, by decide⟩,⟨826513, by decide⟩]) unmarked_context_11_26963_826514 node_context_11_26963_826514
  intro a
  fin_cases a
  · exact context_12_107852_826334
  · exact context_12_107853_826386
  · exact context_12_107854_826446
  · exact context_12_107855_826513

theorem unmarked_context_10_6740_826515 : frontier 11 ⟨826515, by decide⟩
    (prefixCache 10 6740) (prefixPartial 10 6740) = false := by
  decide +kernel

theorem node_context_10_6740_826515 : EJMOriginalGlobalDAGData.nodes 11 ⟨826515, by decide⟩ =
    .split (coordinate 10) (![⟨825835, by decide⟩,⟨826014, by decide⟩,⟨826267, by decide⟩,⟨826514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6740_826515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6740 ⟨826515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6740
    ⟨826515, by decide⟩ (by decide) (![⟨825835, by decide⟩,⟨826014, by decide⟩,⟨826267, by decide⟩,⟨826514, by decide⟩]) unmarked_context_10_6740_826515 node_context_10_6740_826515
  intro a
  fin_cases a
  · exact context_11_26960_825835
  · exact context_11_26961_826014
  · exact context_11_26962_826267
  · exact context_11_26963_826514

theorem selected_cut_32187 : selected 9 ⟨826566, by decide⟩
    (prefixPartial 12 107856) = some ⟨12, 2, 0, 826566, 107856, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_107856_826566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107856 ⟨826566, by decide⟩ :=
  accepted_of_selected 12 107856 ⟨826566, by decide⟩ ⟨12, 2, 0, 826566, 107856, 3801, 65536⟩
    (by decide) selected_cut_32187

theorem selected_cut_32188 : selected 9 ⟨826608, by decide⟩
    (prefixPartial 12 107857) = some ⟨12, 2, 0, 826608, 107857, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_107857_826608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107857 ⟨826608, by decide⟩ :=
  accepted_of_selected 12 107857 ⟨826608, by decide⟩ ⟨12, 2, 0, 826608, 107857, 3209, 65536⟩
    (by decide) selected_cut_32188

theorem selected_cut_32189 : selected 9 ⟨826659, by decide⟩
    (prefixPartial 12 107858) = some ⟨12, 2, 0, 826659, 107858, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_107858_826659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107858 ⟨826659, by decide⟩ :=
  accepted_of_selected 12 107858 ⟨826659, by decide⟩ ⟨12, 2, 0, 826659, 107858, 3929, 65536⟩
    (by decide) selected_cut_32189

theorem selected_cut_32190 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431436) = some ⟨13, 1, 0, 3444, 431436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431436, 1, 16384⟩
    (by decide) selected_cut_32190

theorem selected_cut_32191 : selected 8 ⟨826684, by decide⟩
    (prefixPartial 13 431437) = some ⟨13, 2, 0, 826684, 431437, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_431437_826684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431437 ⟨826684, by decide⟩ :=
  accepted_of_selected 13 431437 ⟨826684, by decide⟩ ⟨13, 2, 0, 826684, 431437, 1777, 16384⟩
    (by decide) selected_cut_32191

theorem selected_cut_32192 : selected 8 ⟨826713, by decide⟩
    (prefixPartial 13 431438) = some ⟨13, 2, 0, 826713, 431438, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_431438_826713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431438 ⟨826713, by decide⟩ :=
  accepted_of_selected 13 431438 ⟨826713, by decide⟩ ⟨13, 2, 0, 826713, 431438, 1689, 16384⟩
    (by decide) selected_cut_32192

theorem selected_cut_32193 : selected 8 ⟨826721, by decide⟩
    (prefixPartial 13 431439) = some ⟨13, 2, 0, 826721, 431439, 829, 16384⟩ := by
  decide +kernel

theorem context_13_431439_826721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431439 ⟨826721, by decide⟩ :=
  accepted_of_selected 13 431439 ⟨826721, by decide⟩ ⟨13, 2, 0, 826721, 431439, 829, 16384⟩
    (by decide) selected_cut_32193

theorem unmarked_context_12_107859_826722 : frontier 9 ⟨826722, by decide⟩
    (prefixCache 12 107859) (prefixPartial 12 107859) = false := by
  decide +kernel

theorem node_context_12_107859_826722 : EJMOriginalGlobalDAGData.nodes 9 ⟨826722, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨826684, by decide⟩,⟨826713, by decide⟩,⟨826721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107859_826722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107859 ⟨826722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107859
    ⟨826722, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨826684, by decide⟩,⟨826713, by decide⟩,⟨826721, by decide⟩]) unmarked_context_12_107859_826722 node_context_12_107859_826722
  intro a
  fin_cases a
  · exact context_13_431436_3444
  · exact context_13_431437_826684
  · exact context_13_431438_826713
  · exact context_13_431439_826721

theorem unmarked_context_11_26964_826723 : frontier 10 ⟨826723, by decide⟩
    (prefixCache 11 26964) (prefixPartial 11 26964) = false := by
  decide +kernel

theorem node_context_11_26964_826723 : EJMOriginalGlobalDAGData.nodes 10 ⟨826723, by decide⟩ =
    .split (coordinate 11) (![⟨826566, by decide⟩,⟨826608, by decide⟩,⟨826659, by decide⟩,⟨826722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26964_826723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26964 ⟨826723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26964
    ⟨826723, by decide⟩ (by decide) (![⟨826566, by decide⟩,⟨826608, by decide⟩,⟨826659, by decide⟩,⟨826722, by decide⟩]) unmarked_context_11_26964_826723 node_context_11_26964_826723
  intro a
  fin_cases a
  · exact context_12_107856_826566
  · exact context_12_107857_826608
  · exact context_12_107858_826659
  · exact context_12_107859_826722

theorem selected_cut_32194 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 26965) = some ⟨11, 1, 0, 451541, 26965, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26965_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26965 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 26965 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 26965, 1, 262144⟩
    (by decide) selected_cut_32194

theorem selected_cut_32195 : selected 9 ⟨826766, by decide⟩
    (prefixPartial 12 107864) = some ⟨12, 2, 0, 826766, 107864, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_107864_826766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107864 ⟨826766, by decide⟩ :=
  accepted_of_selected 12 107864 ⟨826766, by decide⟩ ⟨12, 2, 0, 826766, 107864, 3693, 65536⟩
    (by decide) selected_cut_32195

theorem selected_cut_32196 : selected 9 ⟨826804, by decide⟩
    (prefixPartial 12 107865) = some ⟨12, 2, 0, 826804, 107865, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_107865_826804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107865 ⟨826804, by decide⟩ :=
  accepted_of_selected 12 107865 ⟨826804, by decide⟩ ⟨12, 2, 0, 826804, 107865, 3005, 65536⟩
    (by decide) selected_cut_32196

theorem selected_cut_32197 : selected 9 ⟨826843, by decide⟩
    (prefixPartial 12 107866) = some ⟨12, 2, 0, 826843, 107866, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_107866_826843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107866 ⟨826843, by decide⟩ :=
  accepted_of_selected 12 107866 ⟨826843, by decide⟩ ⟨12, 2, 0, 826843, 107866, 3501, 65536⟩
    (by decide) selected_cut_32197

theorem selected_cut_32198 : selected 9 ⟨826892, by decide⟩
    (prefixPartial 12 107867) = some ⟨12, 2, 0, 826892, 107867, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_107867_826892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107867 ⟨826892, by decide⟩ :=
  accepted_of_selected 12 107867 ⟨826892, by decide⟩ ⟨12, 2, 0, 826892, 107867, 3945, 65536⟩
    (by decide) selected_cut_32198

theorem unmarked_context_11_26966_826893 : frontier 10 ⟨826893, by decide⟩
    (prefixCache 11 26966) (prefixPartial 11 26966) = false := by
  decide +kernel

theorem node_context_11_26966_826893 : EJMOriginalGlobalDAGData.nodes 10 ⟨826893, by decide⟩ =
    .split (coordinate 11) (![⟨826766, by decide⟩,⟨826804, by decide⟩,⟨826843, by decide⟩,⟨826892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26966_826893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26966 ⟨826893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26966
    ⟨826893, by decide⟩ (by decide) (![⟨826766, by decide⟩,⟨826804, by decide⟩,⟨826843, by decide⟩,⟨826892, by decide⟩]) unmarked_context_11_26966_826893 node_context_11_26966_826893
  intro a
  fin_cases a
  · exact context_12_107864_826766
  · exact context_12_107865_826804
  · exact context_12_107866_826843
  · exact context_12_107867_826892

theorem selected_cut_32199 : selected 9 ⟨826944, by decide⟩
    (prefixPartial 12 107868) = some ⟨12, 2, 0, 826944, 107868, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_107868_826944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107868 ⟨826944, by decide⟩ :=
  accepted_of_selected 12 107868 ⟨826944, by decide⟩ ⟨12, 2, 0, 826944, 107868, 4061, 65536⟩
    (by decide) selected_cut_32199

theorem selected_cut_32200 : selected 9 ⟨826984, by decide⟩
    (prefixPartial 12 107869) = some ⟨12, 2, 0, 826984, 107869, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_107869_826984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107869 ⟨826984, by decide⟩ :=
  accepted_of_selected 12 107869 ⟨826984, by decide⟩ ⟨12, 2, 0, 826984, 107869, 3181, 65536⟩
    (by decide) selected_cut_32200

theorem selected_cut_32201 : selected 9 ⟨827028, by decide⟩
    (prefixPartial 12 107870) = some ⟨12, 2, 0, 827028, 107870, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_107870_827028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107870 ⟨827028, by decide⟩ :=
  accepted_of_selected 12 107870 ⟨827028, by decide⟩ ⟨12, 2, 0, 827028, 107870, 3837, 65536⟩
    (by decide) selected_cut_32201

theorem selected_cut_32202 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 431484) = some ⟨13, 1, 0, 3444, 431484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_431484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 431484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 431484, 1, 16384⟩
    (by decide) selected_cut_32202

theorem selected_cut_32203 : selected 8 ⟨827050, by decide⟩
    (prefixPartial 13 431485) = some ⟨13, 2, 0, 827050, 431485, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_431485_827050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431485 ⟨827050, by decide⟩ :=
  accepted_of_selected 13 431485 ⟨827050, by decide⟩ ⟨13, 2, 0, 827050, 431485, 1541, 16384⟩
    (by decide) selected_cut_32203

theorem selected_cut_32204 : selected 8 ⟨827072, by decide⟩
    (prefixPartial 13 431486) = some ⟨13, 2, 0, 827072, 431486, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_431486_827072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431486 ⟨827072, by decide⟩ :=
  accepted_of_selected 13 431486 ⟨827072, by decide⟩ ⟨13, 2, 0, 827072, 431486, 1737, 16384⟩
    (by decide) selected_cut_32204

theorem selected_cut_32205 : selected 8 ⟨827080, by decide⟩
    (prefixPartial 13 431487) = some ⟨13, 2, 0, 827080, 431487, 909, 16384⟩ := by
  decide +kernel

theorem context_13_431487_827080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 431487 ⟨827080, by decide⟩ :=
  accepted_of_selected 13 431487 ⟨827080, by decide⟩ ⟨13, 2, 0, 827080, 431487, 909, 16384⟩
    (by decide) selected_cut_32205

theorem unmarked_context_12_107871_827081 : frontier 9 ⟨827081, by decide⟩
    (prefixCache 12 107871) (prefixPartial 12 107871) = false := by
  decide +kernel

theorem node_context_12_107871_827081 : EJMOriginalGlobalDAGData.nodes 9 ⟨827081, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨827050, by decide⟩,⟨827072, by decide⟩,⟨827080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107871_827081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107871 ⟨827081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107871
    ⟨827081, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨827050, by decide⟩,⟨827072, by decide⟩,⟨827080, by decide⟩]) unmarked_context_12_107871_827081 node_context_12_107871_827081
  intro a
  fin_cases a
  · exact context_13_431484_3444
  · exact context_13_431485_827050
  · exact context_13_431486_827072
  · exact context_13_431487_827080

theorem unmarked_context_11_26967_827082 : frontier 10 ⟨827082, by decide⟩
    (prefixCache 11 26967) (prefixPartial 11 26967) = false := by
  decide +kernel

theorem node_context_11_26967_827082 : EJMOriginalGlobalDAGData.nodes 10 ⟨827082, by decide⟩ =
    .split (coordinate 11) (![⟨826944, by decide⟩,⟨826984, by decide⟩,⟨827028, by decide⟩,⟨827081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26967_827082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26967 ⟨827082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26967
    ⟨827082, by decide⟩ (by decide) (![⟨826944, by decide⟩,⟨826984, by decide⟩,⟨827028, by decide⟩,⟨827081, by decide⟩]) unmarked_context_11_26967_827082 node_context_11_26967_827082
  intro a
  fin_cases a
  · exact context_12_107868_826944
  · exact context_12_107869_826984
  · exact context_12_107870_827028
  · exact context_12_107871_827081

theorem unmarked_context_10_6741_827083 : frontier 11 ⟨827083, by decide⟩
    (prefixCache 10 6741) (prefixPartial 10 6741) = false := by
  decide +kernel

theorem node_context_10_6741_827083 : EJMOriginalGlobalDAGData.nodes 11 ⟨827083, by decide⟩ =
    .split (coordinate 10) (![⟨826723, by decide⟩,⟨451541, by decide⟩,⟨826893, by decide⟩,⟨827082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6741_827083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6741 ⟨827083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6741
    ⟨827083, by decide⟩ (by decide) (![⟨826723, by decide⟩,⟨451541, by decide⟩,⟨826893, by decide⟩,⟨827082, by decide⟩]) unmarked_context_10_6741_827083 node_context_10_6741_827083
  intro a
  fin_cases a
  · exact context_11_26964_826723
  · exact context_11_26965_451541
  · exact context_11_26966_826893
  · exact context_11_26967_827082

theorem selected_cut_32206 : selected 9 ⟨827148, by decide⟩
    (prefixPartial 12 107872) = some ⟨12, 2, 0, 827148, 107872, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_107872_827148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107872 ⟨827148, by decide⟩ :=
  accepted_of_selected 12 107872 ⟨827148, by decide⟩ ⟨12, 2, 0, 827148, 107872, 3577, 65536⟩
    (by decide) selected_cut_32206

theorem selected_cut_32207 : selected 9 ⟨827193, by decide⟩
    (prefixPartial 12 107873) = some ⟨12, 2, 0, 827193, 107873, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_107873_827193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107873 ⟨827193, by decide⟩ :=
  accepted_of_selected 12 107873 ⟨827193, by decide⟩ ⟨12, 2, 0, 827193, 107873, 2945, 65536⟩
    (by decide) selected_cut_32207

theorem selected_cut_32208 : selected 9 ⟨827251, by decide⟩
    (prefixPartial 12 107874) = some ⟨12, 2, 0, 827251, 107874, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_107874_827251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107874 ⟨827251, by decide⟩ :=
  accepted_of_selected 12 107874 ⟨827251, by decide⟩ ⟨12, 2, 0, 827251, 107874, 3429, 65536⟩
    (by decide) selected_cut_32208

theorem selected_cut_32209 : selected 9 ⟨827323, by decide⟩
    (prefixPartial 12 107875) = some ⟨12, 2, 0, 827323, 107875, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_107875_827323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107875 ⟨827323, by decide⟩ :=
  accepted_of_selected 12 107875 ⟨827323, by decide⟩ ⟨12, 2, 0, 827323, 107875, 3813, 65536⟩
    (by decide) selected_cut_32209

theorem unmarked_context_11_26968_827324 : frontier 10 ⟨827324, by decide⟩
    (prefixCache 11 26968) (prefixPartial 11 26968) = false := by
  decide +kernel

theorem node_context_11_26968_827324 : EJMOriginalGlobalDAGData.nodes 10 ⟨827324, by decide⟩ =
    .split (coordinate 11) (![⟨827148, by decide⟩,⟨827193, by decide⟩,⟨827251, by decide⟩,⟨827323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26968_827324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26968 ⟨827324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26968
    ⟨827324, by decide⟩ (by decide) (![⟨827148, by decide⟩,⟨827193, by decide⟩,⟨827251, by decide⟩,⟨827323, by decide⟩]) unmarked_context_11_26968_827324 node_context_11_26968_827324
  intro a
  fin_cases a
  · exact context_12_107872_827148
  · exact context_12_107873_827193
  · exact context_12_107874_827251
  · exact context_12_107875_827323

theorem selected_cut_32210 : selected 9 ⟨827378, by decide⟩
    (prefixPartial 12 107876) = some ⟨12, 2, 0, 827378, 107876, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_107876_827378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107876 ⟨827378, by decide⟩ :=
  accepted_of_selected 12 107876 ⟨827378, by decide⟩ ⟨12, 2, 0, 827378, 107876, 3325, 65536⟩
    (by decide) selected_cut_32210

theorem selected_cut_32211 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 107877) = some ⟨12, 1, 0, 688903, 107877, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107877_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107877 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 107877 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 107877, 1, 65536⟩
    (by decide) selected_cut_32211

theorem selected_cut_32212 : selected 9 ⟨827426, by decide⟩
    (prefixPartial 12 107878) = some ⟨12, 2, 0, 827426, 107878, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_107878_827426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107878 ⟨827426, by decide⟩ :=
  accepted_of_selected 12 107878 ⟨827426, by decide⟩ ⟨12, 2, 0, 827426, 107878, 2937, 65536⟩
    (by decide) selected_cut_32212

theorem selected_cut_32213 : selected 9 ⟨827490, by decide⟩
    (prefixPartial 12 107879) = some ⟨12, 2, 0, 827490, 107879, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_107879_827490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107879 ⟨827490, by decide⟩ :=
  accepted_of_selected 12 107879 ⟨827490, by decide⟩ ⟨12, 2, 0, 827490, 107879, 3473, 65536⟩
    (by decide) selected_cut_32213

theorem unmarked_context_11_26969_827491 : frontier 10 ⟨827491, by decide⟩
    (prefixCache 11 26969) (prefixPartial 11 26969) = false := by
  decide +kernel

theorem node_context_11_26969_827491 : EJMOriginalGlobalDAGData.nodes 10 ⟨827491, by decide⟩ =
    .split (coordinate 11) (![⟨827378, by decide⟩,⟨688903, by decide⟩,⟨827426, by decide⟩,⟨827490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26969_827491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26969 ⟨827491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26969
    ⟨827491, by decide⟩ (by decide) (![⟨827378, by decide⟩,⟨688903, by decide⟩,⟨827426, by decide⟩,⟨827490, by decide⟩]) unmarked_context_11_26969_827491 node_context_11_26969_827491
  intro a
  fin_cases a
  · exact context_12_107876_827378
  · exact context_12_107877_688903
  · exact context_12_107878_827426
  · exact context_12_107879_827490

theorem selected_cut_32214 : selected 9 ⟨827542, by decide⟩
    (prefixPartial 12 107880) = some ⟨12, 2, 0, 827542, 107880, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_107880_827542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107880 ⟨827542, by decide⟩ :=
  accepted_of_selected 12 107880 ⟨827542, by decide⟩ ⟨12, 2, 0, 827542, 107880, 3553, 65536⟩
    (by decide) selected_cut_32214

theorem selected_cut_32215 : selected 9 ⟨827577, by decide⟩
    (prefixPartial 12 107881) = some ⟨12, 2, 0, 827577, 107881, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_107881_827577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107881 ⟨827577, by decide⟩ :=
  accepted_of_selected 12 107881 ⟨827577, by decide⟩ ⟨12, 2, 0, 827577, 107881, 3049, 65536⟩
    (by decide) selected_cut_32215

theorem selected_cut_32216 : selected 9 ⟨827620, by decide⟩
    (prefixPartial 12 107882) = some ⟨12, 2, 0, 827620, 107882, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_107882_827620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107882 ⟨827620, by decide⟩ :=
  accepted_of_selected 12 107882 ⟨827620, by decide⟩ ⟨12, 2, 0, 827620, 107882, 3145, 65536⟩
    (by decide) selected_cut_32216

theorem selected_cut_32217 : selected 9 ⟨827667, by decide⟩
    (prefixPartial 12 107883) = some ⟨12, 2, 0, 827667, 107883, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_107883_827667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107883 ⟨827667, by decide⟩ :=
  accepted_of_selected 12 107883 ⟨827667, by decide⟩ ⟨12, 2, 0, 827667, 107883, 3541, 65536⟩
    (by decide) selected_cut_32217

theorem unmarked_context_11_26970_827668 : frontier 10 ⟨827668, by decide⟩
    (prefixCache 11 26970) (prefixPartial 11 26970) = false := by
  decide +kernel

theorem node_context_11_26970_827668 : EJMOriginalGlobalDAGData.nodes 10 ⟨827668, by decide⟩ =
    .split (coordinate 11) (![⟨827542, by decide⟩,⟨827577, by decide⟩,⟨827620, by decide⟩,⟨827667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26970_827668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26970 ⟨827668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26970
    ⟨827668, by decide⟩ (by decide) (![⟨827542, by decide⟩,⟨827577, by decide⟩,⟨827620, by decide⟩,⟨827667, by decide⟩]) unmarked_context_11_26970_827668 node_context_11_26970_827668
  intro a
  fin_cases a
  · exact context_12_107880_827542
  · exact context_12_107881_827577
  · exact context_12_107882_827620
  · exact context_12_107883_827667

theorem selected_cut_32218 : selected 9 ⟨827744, by decide⟩
    (prefixPartial 12 107884) = some ⟨12, 2, 0, 827744, 107884, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_107884_827744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107884 ⟨827744, by decide⟩ :=
  accepted_of_selected 12 107884 ⟨827744, by decide⟩ ⟨12, 2, 0, 827744, 107884, 3717, 65536⟩
    (by decide) selected_cut_32218

theorem selected_cut_32219 : selected 9 ⟨827792, by decide⟩
    (prefixPartial 12 107885) = some ⟨12, 2, 0, 827792, 107885, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_107885_827792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107885 ⟨827792, by decide⟩ :=
  accepted_of_selected 12 107885 ⟨827792, by decide⟩ ⟨12, 2, 0, 827792, 107885, 3017, 65536⟩
    (by decide) selected_cut_32219

theorem selected_cut_32220 : selected 9 ⟨827844, by decide⟩
    (prefixPartial 12 107886) = some ⟨12, 2, 0, 827844, 107886, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_107886_827844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107886 ⟨827844, by decide⟩ :=
  accepted_of_selected 12 107886 ⟨827844, by decide⟩ ⟨12, 2, 0, 827844, 107886, 3201, 65536⟩
    (by decide) selected_cut_32220

theorem selected_cut_32221 : selected 9 ⟨827914, by decide⟩
    (prefixPartial 12 107887) = some ⟨12, 2, 0, 827914, 107887, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_107887_827914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107887 ⟨827914, by decide⟩ :=
  accepted_of_selected 12 107887 ⟨827914, by decide⟩ ⟨12, 2, 0, 827914, 107887, 3649, 65536⟩
    (by decide) selected_cut_32221

theorem unmarked_context_11_26971_827915 : frontier 10 ⟨827915, by decide⟩
    (prefixCache 11 26971) (prefixPartial 11 26971) = false := by
  decide +kernel

theorem node_context_11_26971_827915 : EJMOriginalGlobalDAGData.nodes 10 ⟨827915, by decide⟩ =
    .split (coordinate 11) (![⟨827744, by decide⟩,⟨827792, by decide⟩,⟨827844, by decide⟩,⟨827914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26971_827915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26971 ⟨827915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26971
    ⟨827915, by decide⟩ (by decide) (![⟨827744, by decide⟩,⟨827792, by decide⟩,⟨827844, by decide⟩,⟨827914, by decide⟩]) unmarked_context_11_26971_827915 node_context_11_26971_827915
  intro a
  fin_cases a
  · exact context_12_107884_827744
  · exact context_12_107885_827792
  · exact context_12_107886_827844
  · exact context_12_107887_827914

theorem unmarked_context_10_6742_827916 : frontier 11 ⟨827916, by decide⟩
    (prefixCache 10 6742) (prefixPartial 10 6742) = false := by
  decide +kernel

theorem node_context_10_6742_827916 : EJMOriginalGlobalDAGData.nodes 11 ⟨827916, by decide⟩ =
    .split (coordinate 10) (![⟨827324, by decide⟩,⟨827491, by decide⟩,⟨827668, by decide⟩,⟨827915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6742_827916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6742 ⟨827916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6742
    ⟨827916, by decide⟩ (by decide) (![⟨827324, by decide⟩,⟨827491, by decide⟩,⟨827668, by decide⟩,⟨827915, by decide⟩]) unmarked_context_10_6742_827916 node_context_10_6742_827916
  intro a
  fin_cases a
  · exact context_11_26968_827324
  · exact context_11_26969_827491
  · exact context_11_26970_827668
  · exact context_11_26971_827915

theorem selected_cut_32222 : selected 9 ⟨827959, by decide⟩
    (prefixPartial 12 107888) = some ⟨12, 2, 0, 827959, 107888, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_107888_827959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107888 ⟨827959, by decide⟩ :=
  accepted_of_selected 12 107888 ⟨827959, by decide⟩ ⟨12, 2, 0, 827959, 107888, 3221, 65536⟩
    (by decide) selected_cut_32222

theorem selected_cut_32223 : selected 9 ⟨827993, by decide⟩
    (prefixPartial 12 107889) = some ⟨12, 2, 0, 827993, 107889, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_107889_827993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107889 ⟨827993, by decide⟩ :=
  accepted_of_selected 12 107889 ⟨827993, by decide⟩ ⟨12, 2, 0, 827993, 107889, 2633, 65536⟩
    (by decide) selected_cut_32223

theorem selected_cut_32224 : selected 9 ⟨828032, by decide⟩
    (prefixPartial 12 107890) = some ⟨12, 2, 0, 828032, 107890, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_107890_828032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107890 ⟨828032, by decide⟩ :=
  accepted_of_selected 12 107890 ⟨828032, by decide⟩ ⟨12, 2, 0, 828032, 107890, 3061, 65536⟩
    (by decide) selected_cut_32224

theorem selected_cut_32225 : selected 9 ⟨828073, by decide⟩
    (prefixPartial 12 107891) = some ⟨12, 2, 0, 828073, 107891, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_107891_828073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107891 ⟨828073, by decide⟩ :=
  accepted_of_selected 12 107891 ⟨828073, by decide⟩ ⟨12, 2, 0, 828073, 107891, 3157, 65536⟩
    (by decide) selected_cut_32225

theorem unmarked_context_11_26972_828074 : frontier 10 ⟨828074, by decide⟩
    (prefixCache 11 26972) (prefixPartial 11 26972) = false := by
  decide +kernel

theorem node_context_11_26972_828074 : EJMOriginalGlobalDAGData.nodes 10 ⟨828074, by decide⟩ =
    .split (coordinate 11) (![⟨827959, by decide⟩,⟨827993, by decide⟩,⟨828032, by decide⟩,⟨828073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26972_828074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26972 ⟨828074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26972
    ⟨828074, by decide⟩ (by decide) (![⟨827959, by decide⟩,⟨827993, by decide⟩,⟨828032, by decide⟩,⟨828073, by decide⟩]) unmarked_context_11_26972_828074 node_context_11_26972_828074
  intro a
  fin_cases a
  · exact context_12_107888_827959
  · exact context_12_107889_827993
  · exact context_12_107890_828032
  · exact context_12_107891_828073

theorem selected_cut_32226 : selected 9 ⟨828113, by decide⟩
    (prefixPartial 12 107892) = some ⟨12, 2, 0, 828113, 107892, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_107892_828113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107892 ⟨828113, by decide⟩ :=
  accepted_of_selected 12 107892 ⟨828113, by decide⟩ ⟨12, 2, 0, 828113, 107892, 2589, 65536⟩
    (by decide) selected_cut_32226

theorem selected_cut_32227 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 107893) = some ⟨12, 1, 0, 689956, 107893, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107893_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107893 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 107893 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 107893, 1, 65536⟩
    (by decide) selected_cut_32227

theorem selected_cut_32228 : selected 9 ⟨828150, by decide⟩
    (prefixPartial 12 107894) = some ⟨12, 2, 0, 828150, 107894, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_107894_828150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107894 ⟨828150, by decide⟩ :=
  accepted_of_selected 12 107894 ⟨828150, by decide⟩ ⟨12, 2, 0, 828150, 107894, 2405, 65536⟩
    (by decide) selected_cut_32228

theorem selected_cut_32229 : selected 9 ⟨828199, by decide⟩
    (prefixPartial 12 107895) = some ⟨12, 2, 0, 828199, 107895, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_107895_828199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107895 ⟨828199, by decide⟩ :=
  accepted_of_selected 12 107895 ⟨828199, by decide⟩ ⟨12, 2, 0, 828199, 107895, 2729, 65536⟩
    (by decide) selected_cut_32229

theorem unmarked_context_11_26973_828200 : frontier 10 ⟨828200, by decide⟩
    (prefixCache 11 26973) (prefixPartial 11 26973) = false := by
  decide +kernel

theorem node_context_11_26973_828200 : EJMOriginalGlobalDAGData.nodes 10 ⟨828200, by decide⟩ =
    .split (coordinate 11) (![⟨828113, by decide⟩,⟨689956, by decide⟩,⟨828150, by decide⟩,⟨828199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26973_828200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26973 ⟨828200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26973
    ⟨828200, by decide⟩ (by decide) (![⟨828113, by decide⟩,⟨689956, by decide⟩,⟨828150, by decide⟩,⟨828199, by decide⟩]) unmarked_context_11_26973_828200 node_context_11_26973_828200
  intro a
  fin_cases a
  · exact context_12_107892_828113
  · exact context_12_107893_689956
  · exact context_12_107894_828150
  · exact context_12_107895_828199

theorem selected_cut_32230 : selected 9 ⟨828248, by decide⟩
    (prefixPartial 12 107896) = some ⟨12, 2, 0, 828248, 107896, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_107896_828248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107896 ⟨828248, by decide⟩ :=
  accepted_of_selected 12 107896 ⟨828248, by decide⟩ ⟨12, 2, 0, 828248, 107896, 3153, 65536⟩
    (by decide) selected_cut_32230

theorem selected_cut_32231 : selected 9 ⟨828289, by decide⟩
    (prefixPartial 12 107897) = some ⟨12, 2, 0, 828289, 107897, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_107897_828289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107897 ⟨828289, by decide⟩ :=
  accepted_of_selected 12 107897 ⟨828289, by decide⟩ ⟨12, 2, 0, 828289, 107897, 2661, 65536⟩
    (by decide) selected_cut_32231

theorem selected_cut_32232 : selected 9 ⟨828327, by decide⟩
    (prefixPartial 12 107898) = some ⟨12, 2, 0, 828327, 107898, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_107898_828327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107898 ⟨828327, by decide⟩ :=
  accepted_of_selected 12 107898 ⟨828327, by decide⟩ ⟨12, 2, 0, 828327, 107898, 2697, 65536⟩
    (by decide) selected_cut_32232

theorem selected_cut_32233 : selected 9 ⟨828375, by decide⟩
    (prefixPartial 12 107899) = some ⟨12, 2, 0, 828375, 107899, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_107899_828375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107899 ⟨828375, by decide⟩ :=
  accepted_of_selected 12 107899 ⟨828375, by decide⟩ ⟨12, 2, 0, 828375, 107899, 2965, 65536⟩
    (by decide) selected_cut_32233

theorem unmarked_context_11_26974_828376 : frontier 10 ⟨828376, by decide⟩
    (prefixCache 11 26974) (prefixPartial 11 26974) = false := by
  decide +kernel

theorem node_context_11_26974_828376 : EJMOriginalGlobalDAGData.nodes 10 ⟨828376, by decide⟩ =
    .split (coordinate 11) (![⟨828248, by decide⟩,⟨828289, by decide⟩,⟨828327, by decide⟩,⟨828375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26974_828376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26974 ⟨828376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26974
    ⟨828376, by decide⟩ (by decide) (![⟨828248, by decide⟩,⟨828289, by decide⟩,⟨828327, by decide⟩,⟨828375, by decide⟩]) unmarked_context_11_26974_828376 node_context_11_26974_828376
  intro a
  fin_cases a
  · exact context_12_107896_828248
  · exact context_12_107897_828289
  · exact context_12_107898_828327
  · exact context_12_107899_828375

theorem selected_cut_32234 : selected 9 ⟨828424, by decide⟩
    (prefixPartial 12 107900) = some ⟨12, 2, 0, 828424, 107900, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_107900_828424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107900 ⟨828424, by decide⟩ :=
  accepted_of_selected 12 107900 ⟨828424, by decide⟩ ⟨12, 2, 0, 828424, 107900, 2837, 65536⟩
    (by decide) selected_cut_32234

theorem selected_cut_32235 : selected 9 ⟨828452, by decide⟩
    (prefixPartial 12 107901) = some ⟨12, 2, 0, 828452, 107901, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_107901_828452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107901 ⟨828452, by decide⟩ :=
  accepted_of_selected 12 107901 ⟨828452, by decide⟩ ⟨12, 2, 0, 828452, 107901, 2217, 65536⟩
    (by decide) selected_cut_32235

theorem selected_cut_32236 : selected 9 ⟨828482, by decide⟩
    (prefixPartial 12 107902) = some ⟨12, 2, 0, 828482, 107902, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_107902_828482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107902 ⟨828482, by decide⟩ :=
  accepted_of_selected 12 107902 ⟨828482, by decide⟩ ⟨12, 2, 0, 828482, 107902, 2465, 65536⟩
    (by decide) selected_cut_32236

theorem selected_cut_32237 : selected 9 ⟨828520, by decide⟩
    (prefixPartial 12 107903) = some ⟨12, 2, 0, 828520, 107903, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_107903_828520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107903 ⟨828520, by decide⟩ :=
  accepted_of_selected 12 107903 ⟨828520, by decide⟩ ⟨12, 2, 0, 828520, 107903, 2653, 65536⟩
    (by decide) selected_cut_32237

theorem unmarked_context_11_26975_828521 : frontier 10 ⟨828521, by decide⟩
    (prefixCache 11 26975) (prefixPartial 11 26975) = false := by
  decide +kernel

theorem node_context_11_26975_828521 : EJMOriginalGlobalDAGData.nodes 10 ⟨828521, by decide⟩ =
    .split (coordinate 11) (![⟨828424, by decide⟩,⟨828452, by decide⟩,⟨828482, by decide⟩,⟨828520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26975_828521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26975 ⟨828521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26975
    ⟨828521, by decide⟩ (by decide) (![⟨828424, by decide⟩,⟨828452, by decide⟩,⟨828482, by decide⟩,⟨828520, by decide⟩]) unmarked_context_11_26975_828521 node_context_11_26975_828521
  intro a
  fin_cases a
  · exact context_12_107900_828424
  · exact context_12_107901_828452
  · exact context_12_107902_828482
  · exact context_12_107903_828520

theorem unmarked_context_10_6743_828522 : frontier 11 ⟨828522, by decide⟩
    (prefixCache 10 6743) (prefixPartial 10 6743) = false := by
  decide +kernel

theorem node_context_10_6743_828522 : EJMOriginalGlobalDAGData.nodes 11 ⟨828522, by decide⟩ =
    .split (coordinate 10) (![⟨828074, by decide⟩,⟨828200, by decide⟩,⟨828376, by decide⟩,⟨828521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6743_828522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6743 ⟨828522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6743
    ⟨828522, by decide⟩ (by decide) (![⟨828074, by decide⟩,⟨828200, by decide⟩,⟨828376, by decide⟩,⟨828521, by decide⟩]) unmarked_context_10_6743_828522 node_context_10_6743_828522
  intro a
  fin_cases a
  · exact context_11_26972_828074
  · exact context_11_26973_828200
  · exact context_11_26974_828376
  · exact context_11_26975_828521

theorem unmarked_context_9_1685_828523 : frontier 12 ⟨828523, by decide⟩
    (prefixCache 9 1685) (prefixPartial 9 1685) = false := by
  decide +kernel

theorem node_context_9_1685_828523 : EJMOriginalGlobalDAGData.nodes 12 ⟨828523, by decide⟩ =
    .split (coordinate 9) (![⟨826515, by decide⟩,⟨827083, by decide⟩,⟨827916, by decide⟩,⟨828522, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1685_828523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1685 ⟨828523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1685
    ⟨828523, by decide⟩ (by decide) (![⟨826515, by decide⟩,⟨827083, by decide⟩,⟨827916, by decide⟩,⟨828522, by decide⟩]) unmarked_context_9_1685_828523 node_context_9_1685_828523
  intro a
  fin_cases a
  · exact context_10_6740_826515
  · exact context_10_6741_827083
  · exact context_10_6742_827916
  · exact context_10_6743_828522

theorem selected_cut_32238 : selected 9 ⟨828551, by decide⟩
    (prefixPartial 12 107904) = some ⟨12, 2, 0, 828551, 107904, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_107904_828551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107904 ⟨828551, by decide⟩ :=
  accepted_of_selected 12 107904 ⟨828551, by decide⟩ ⟨12, 2, 0, 828551, 107904, 2105, 65536⟩
    (by decide) selected_cut_32238

theorem selected_cut_32239 : selected 9 ⟨828578, by decide⟩
    (prefixPartial 12 107905) = some ⟨12, 2, 0, 828578, 107905, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_107905_828578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107905 ⟨828578, by decide⟩ :=
  accepted_of_selected 12 107905 ⟨828578, by decide⟩ ⟨12, 2, 0, 828578, 107905, 1753, 65536⟩
    (by decide) selected_cut_32239

theorem selected_cut_32240 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 107906) = some ⟨12, 1, 0, 813440, 107906, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107906_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107906 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 107906 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 107906, 1, 65536⟩
    (by decide) selected_cut_32240

theorem selected_cut_32241 : selected 9 ⟨828604, by decide⟩
    (prefixPartial 12 107907) = some ⟨12, 2, 0, 828604, 107907, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_107907_828604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107907 ⟨828604, by decide⟩ :=
  accepted_of_selected 12 107907 ⟨828604, by decide⟩ ⟨12, 2, 0, 828604, 107907, 2169, 65536⟩
    (by decide) selected_cut_32241

theorem unmarked_context_11_26976_828605 : frontier 10 ⟨828605, by decide⟩
    (prefixCache 11 26976) (prefixPartial 11 26976) = false := by
  decide +kernel

theorem node_context_11_26976_828605 : EJMOriginalGlobalDAGData.nodes 10 ⟨828605, by decide⟩ =
    .split (coordinate 11) (![⟨828551, by decide⟩,⟨828578, by decide⟩,⟨813440, by decide⟩,⟨828604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26976_828605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26976 ⟨828605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26976
    ⟨828605, by decide⟩ (by decide) (![⟨828551, by decide⟩,⟨828578, by decide⟩,⟨813440, by decide⟩,⟨828604, by decide⟩]) unmarked_context_11_26976_828605 node_context_11_26976_828605
  intro a
  fin_cases a
  · exact context_12_107904_828551
  · exact context_12_107905_828578
  · exact context_12_107906_813440
  · exact context_12_107907_828604

theorem selected_cut_32242 : selected 10 ⟨828660, by decide⟩
    (prefixPartial 11 26977) = some ⟨11, 2, 0, 828660, 26977, 3457, 262144⟩ := by
  decide +kernel

theorem context_11_26977_828660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26977 ⟨828660, by decide⟩ :=
  accepted_of_selected 11 26977 ⟨828660, by decide⟩ ⟨11, 2, 0, 828660, 26977, 3457, 262144⟩
    (by decide) selected_cut_32242

theorem selected_cut_32243 : selected 9 ⟨828700, by decide⟩
    (prefixPartial 12 107912) = some ⟨12, 2, 0, 828700, 107912, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_107912_828700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107912 ⟨828700, by decide⟩ :=
  accepted_of_selected 12 107912 ⟨828700, by decide⟩ ⟨12, 2, 0, 828700, 107912, 2213, 65536⟩
    (by decide) selected_cut_32243

theorem selected_cut_32244 : selected 9 ⟨828728, by decide⟩
    (prefixPartial 12 107913) = some ⟨12, 2, 0, 828728, 107913, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_107913_828728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107913 ⟨828728, by decide⟩ :=
  accepted_of_selected 12 107913 ⟨828728, by decide⟩ ⟨12, 2, 0, 828728, 107913, 1897, 65536⟩
    (by decide) selected_cut_32244

theorem selected_cut_32245 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 107914) = some ⟨12, 1, 0, 813440, 107914, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107914_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107914 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 107914 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 107914, 1, 65536⟩
    (by decide) selected_cut_32245

theorem selected_cut_32246 : selected 9 ⟨828766, by decide⟩
    (prefixPartial 12 107915) = some ⟨12, 2, 0, 828766, 107915, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_107915_828766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107915 ⟨828766, by decide⟩ :=
  accepted_of_selected 12 107915 ⟨828766, by decide⟩ ⟨12, 2, 0, 828766, 107915, 2125, 65536⟩
    (by decide) selected_cut_32246

theorem unmarked_context_11_26978_828767 : frontier 10 ⟨828767, by decide⟩
    (prefixCache 11 26978) (prefixPartial 11 26978) = false := by
  decide +kernel

theorem node_context_11_26978_828767 : EJMOriginalGlobalDAGData.nodes 10 ⟨828767, by decide⟩ =
    .split (coordinate 11) (![⟨828700, by decide⟩,⟨828728, by decide⟩,⟨813440, by decide⟩,⟨828766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26978_828767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26978 ⟨828767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26978
    ⟨828767, by decide⟩ (by decide) (![⟨828700, by decide⟩,⟨828728, by decide⟩,⟨813440, by decide⟩,⟨828766, by decide⟩]) unmarked_context_11_26978_828767 node_context_11_26978_828767
  intro a
  fin_cases a
  · exact context_12_107912_828700
  · exact context_12_107913_828728
  · exact context_12_107914_813440
  · exact context_12_107915_828766

theorem selected_cut_32247 : selected 9 ⟨828797, by decide⟩
    (prefixPartial 12 107916) = some ⟨12, 2, 0, 828797, 107916, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_107916_828797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107916 ⟨828797, by decide⟩ :=
  accepted_of_selected 12 107916 ⟨828797, by decide⟩ ⟨12, 2, 0, 828797, 107916, 2009, 65536⟩
    (by decide) selected_cut_32247

theorem selected_cut_32248 : selected 9 ⟨828819, by decide⟩
    (prefixPartial 12 107917) = some ⟨12, 2, 0, 828819, 107917, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_107917_828819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107917 ⟨828819, by decide⟩ :=
  accepted_of_selected 12 107917 ⟨828819, by decide⟩ ⟨12, 2, 0, 828819, 107917, 1621, 65536⟩
    (by decide) selected_cut_32248

theorem selected_cut_32249 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 107918) = some ⟨12, 1, 0, 813440, 107918, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107918_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107918 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 107918 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 107918, 1, 65536⟩
    (by decide) selected_cut_32249

theorem selected_cut_32250 : selected 9 ⟨828846, by decide⟩
    (prefixPartial 12 107919) = some ⟨12, 2, 0, 828846, 107919, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_107919_828846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107919 ⟨828846, by decide⟩ :=
  accepted_of_selected 12 107919 ⟨828846, by decide⟩ ⟨12, 2, 0, 828846, 107919, 1945, 65536⟩
    (by decide) selected_cut_32250

theorem unmarked_context_11_26979_828847 : frontier 10 ⟨828847, by decide⟩
    (prefixCache 11 26979) (prefixPartial 11 26979) = false := by
  decide +kernel

theorem node_context_11_26979_828847 : EJMOriginalGlobalDAGData.nodes 10 ⟨828847, by decide⟩ =
    .split (coordinate 11) (![⟨828797, by decide⟩,⟨828819, by decide⟩,⟨813440, by decide⟩,⟨828846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26979_828847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26979 ⟨828847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26979
    ⟨828847, by decide⟩ (by decide) (![⟨828797, by decide⟩,⟨828819, by decide⟩,⟨813440, by decide⟩,⟨828846, by decide⟩]) unmarked_context_11_26979_828847 node_context_11_26979_828847
  intro a
  fin_cases a
  · exact context_12_107916_828797
  · exact context_12_107917_828819
  · exact context_12_107918_813440
  · exact context_12_107919_828846

theorem unmarked_context_10_6744_828848 : frontier 11 ⟨828848, by decide⟩
    (prefixCache 10 6744) (prefixPartial 10 6744) = false := by
  decide +kernel

theorem node_context_10_6744_828848 : EJMOriginalGlobalDAGData.nodes 11 ⟨828848, by decide⟩ =
    .split (coordinate 10) (![⟨828605, by decide⟩,⟨828660, by decide⟩,⟨828767, by decide⟩,⟨828847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6744_828848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6744 ⟨828848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6744
    ⟨828848, by decide⟩ (by decide) (![⟨828605, by decide⟩,⟨828660, by decide⟩,⟨828767, by decide⟩,⟨828847, by decide⟩]) unmarked_context_10_6744_828848 node_context_10_6744_828848
  intro a
  fin_cases a
  · exact context_11_26976_828605
  · exact context_11_26977_828660
  · exact context_11_26978_828767
  · exact context_11_26979_828847

theorem selected_cut_32251 : selected 9 ⟨828869, by decide⟩
    (prefixPartial 12 107920) = some ⟨12, 2, 0, 828869, 107920, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_107920_828869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107920 ⟨828869, by decide⟩ :=
  accepted_of_selected 12 107920 ⟨828869, by decide⟩ ⟨12, 2, 0, 828869, 107920, 1869, 65536⟩
    (by decide) selected_cut_32251

theorem selected_cut_32252 : selected 9 ⟨828888, by decide⟩
    (prefixPartial 12 107921) = some ⟨12, 2, 0, 828888, 107921, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_107921_828888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107921 ⟨828888, by decide⟩ :=
  accepted_of_selected 12 107921 ⟨828888, by decide⟩ ⟨12, 2, 0, 828888, 107921, 1585, 65536⟩
    (by decide) selected_cut_32252

theorem selected_cut_32253 : selected 9 ⟨828934, by decide⟩
    (prefixPartial 12 107922) = some ⟨12, 2, 0, 828934, 107922, 693, 65536⟩ := by
  decide +kernel

theorem context_12_107922_828934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107922 ⟨828934, by decide⟩ :=
  accepted_of_selected 12 107922 ⟨828934, by decide⟩ ⟨12, 2, 0, 828934, 107922, 693, 65536⟩
    (by decide) selected_cut_32253

theorem selected_cut_32254 : selected 9 ⟨828956, by decide⟩
    (prefixPartial 12 107923) = some ⟨12, 2, 0, 828956, 107923, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_107923_828956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107923 ⟨828956, by decide⟩ :=
  accepted_of_selected 12 107923 ⟨828956, by decide⟩ ⟨12, 2, 0, 828956, 107923, 1921, 65536⟩
    (by decide) selected_cut_32254

theorem unmarked_context_11_26980_828957 : frontier 10 ⟨828957, by decide⟩
    (prefixCache 11 26980) (prefixPartial 11 26980) = false := by
  decide +kernel

theorem node_context_11_26980_828957 : EJMOriginalGlobalDAGData.nodes 10 ⟨828957, by decide⟩ =
    .split (coordinate 11) (![⟨828869, by decide⟩,⟨828888, by decide⟩,⟨828934, by decide⟩,⟨828956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26980_828957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26980 ⟨828957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26980
    ⟨828957, by decide⟩ (by decide) (![⟨828869, by decide⟩,⟨828888, by decide⟩,⟨828934, by decide⟩,⟨828956, by decide⟩]) unmarked_context_11_26980_828957 node_context_11_26980_828957
  intro a
  fin_cases a
  · exact context_12_107920_828869
  · exact context_12_107921_828888
  · exact context_12_107922_828934
  · exact context_12_107923_828956

theorem selected_cut_32255 : selected 10 ⟨828959, by decide⟩
    (prefixPartial 11 26981) = some ⟨11, 2, 0, 828959, 26981, 5, 262144⟩ := by
  decide +kernel

theorem context_11_26981_828959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26981 ⟨828959, by decide⟩ :=
  accepted_of_selected 11 26981 ⟨828959, by decide⟩ ⟨11, 2, 0, 828959, 26981, 5, 262144⟩
    (by decide) selected_cut_32255

theorem selected_cut_32256 : selected 9 ⟨828976, by decide⟩
    (prefixPartial 12 107928) = some ⟨12, 2, 0, 828976, 107928, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_107928_828976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107928 ⟨828976, by decide⟩ :=
  accepted_of_selected 12 107928 ⟨828976, by decide⟩ ⟨12, 2, 0, 828976, 107928, 1873, 65536⟩
    (by decide) selected_cut_32256

theorem selected_cut_32257 : selected 9 ⟨828995, by decide⟩
    (prefixPartial 12 107929) = some ⟨12, 2, 0, 828995, 107929, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_107929_828995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107929 ⟨828995, by decide⟩ :=
  accepted_of_selected 12 107929 ⟨828995, by decide⟩ ⟨12, 2, 0, 828995, 107929, 1589, 65536⟩
    (by decide) selected_cut_32257

theorem selected_cut_32258 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 107930) = some ⟨12, 1, 0, 813979, 107930, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107930_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107930 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 107930 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 107930, 1, 65536⟩
    (by decide) selected_cut_32258

theorem selected_cut_32259 : selected 9 ⟨829016, by decide⟩
    (prefixPartial 12 107931) = some ⟨12, 2, 0, 829016, 107931, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_107931_829016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107931 ⟨829016, by decide⟩ :=
  accepted_of_selected 12 107931 ⟨829016, by decide⟩ ⟨12, 2, 0, 829016, 107931, 1717, 65536⟩
    (by decide) selected_cut_32259

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
