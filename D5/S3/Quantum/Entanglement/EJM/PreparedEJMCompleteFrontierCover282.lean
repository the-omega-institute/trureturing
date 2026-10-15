/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover281
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_22820_685155 : frontier 10 ⟨685155, by decide⟩
    (prefixCache 11 22820) (prefixPartial 11 22820) = false := by
  decide +kernel

theorem node_context_11_22820_685155 : EJMOriginalGlobalDAGData.nodes 10 ⟨685155, by decide⟩ =
    .split (coordinate 11) (![⟨685077, by decide⟩,⟨685103, by decide⟩,⟨685131, by decide⟩,⟨685154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22820_685155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22820 ⟨685155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22820
    ⟨685155, by decide⟩ (by decide) (![⟨685077, by decide⟩,⟨685103, by decide⟩,⟨685131, by decide⟩,⟨685154, by decide⟩]) unmarked_context_11_22820_685155 node_context_11_22820_685155
  intro a
  fin_cases a
  · exact context_12_91280_685077
  · exact context_12_91281_685103
  · exact context_12_91282_685131
  · exact context_12_91283_685154

theorem selected_cut_27075 : selected 9 ⟨685191, by decide⟩
    (prefixPartial 12 91284) = some ⟨12, 2, 0, 685191, 91284, 781, 65536⟩ := by
  decide +kernel

theorem context_12_91284_685191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91284 ⟨685191, by decide⟩ :=
  accepted_of_selected 12 91284 ⟨685191, by decide⟩ ⟨12, 2, 0, 685191, 91284, 781, 65536⟩
    (by decide) selected_cut_27075

theorem selected_cut_27076 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 91285) = some ⟨12, 1, 0, 449506, 91285, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91285_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91285 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 91285 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 91285, 1, 65536⟩
    (by decide) selected_cut_27076

theorem selected_cut_27077 : selected 9 ⟨685234, by decide⟩
    (prefixPartial 12 91286) = some ⟨12, 2, 0, 685234, 91286, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_91286_685234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91286 ⟨685234, by decide⟩ :=
  accepted_of_selected 12 91286 ⟨685234, by decide⟩ ⟨12, 2, 0, 685234, 91286, 2869, 65536⟩
    (by decide) selected_cut_27077

theorem selected_cut_27078 : selected 9 ⟨685281, by decide⟩
    (prefixPartial 12 91287) = some ⟨12, 2, 0, 685281, 91287, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_91287_685281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91287 ⟨685281, by decide⟩ :=
  accepted_of_selected 12 91287 ⟨685281, by decide⟩ ⟨12, 2, 0, 685281, 91287, 3033, 65536⟩
    (by decide) selected_cut_27078

theorem unmarked_context_11_22821_685282 : frontier 10 ⟨685282, by decide⟩
    (prefixCache 11 22821) (prefixPartial 11 22821) = false := by
  decide +kernel

theorem node_context_11_22821_685282 : EJMOriginalGlobalDAGData.nodes 10 ⟨685282, by decide⟩ =
    .split (coordinate 11) (![⟨685191, by decide⟩,⟨449506, by decide⟩,⟨685234, by decide⟩,⟨685281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22821_685282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22821 ⟨685282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22821
    ⟨685282, by decide⟩ (by decide) (![⟨685191, by decide⟩,⟨449506, by decide⟩,⟨685234, by decide⟩,⟨685281, by decide⟩]) unmarked_context_11_22821_685282 node_context_11_22821_685282
  intro a
  fin_cases a
  · exact context_12_91284_685191
  · exact context_12_91285_449506
  · exact context_12_91286_685234
  · exact context_12_91287_685281

theorem selected_cut_27079 : selected 9 ⟨685315, by decide⟩
    (prefixPartial 12 91288) = some ⟨12, 2, 0, 685315, 91288, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_91288_685315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91288 ⟨685315, by decide⟩ :=
  accepted_of_selected 12 91288 ⟨685315, by decide⟩ ⟨12, 2, 0, 685315, 91288, 2101, 65536⟩
    (by decide) selected_cut_27079

theorem selected_cut_27080 : selected 9 ⟨685343, by decide⟩
    (prefixPartial 12 91289) = some ⟨12, 2, 0, 685343, 91289, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_91289_685343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91289 ⟨685343, by decide⟩ :=
  accepted_of_selected 12 91289 ⟨685343, by decide⟩ ⟨12, 2, 0, 685343, 91289, 2365, 65536⟩
    (by decide) selected_cut_27080

theorem selected_cut_27081 : selected 9 ⟨685369, by decide⟩
    (prefixPartial 12 91290) = some ⟨12, 2, 0, 685369, 91290, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_91290_685369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91290 ⟨685369, by decide⟩ :=
  accepted_of_selected 12 91290 ⟨685369, by decide⟩ ⟨12, 2, 0, 685369, 91290, 2161, 65536⟩
    (by decide) selected_cut_27081

theorem selected_cut_27082 : selected 9 ⟨685400, by decide⟩
    (prefixPartial 12 91291) = some ⟨12, 2, 0, 685400, 91291, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_91291_685400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91291 ⟨685400, by decide⟩ :=
  accepted_of_selected 12 91291 ⟨685400, by decide⟩ ⟨12, 2, 0, 685400, 91291, 2201, 65536⟩
    (by decide) selected_cut_27082

theorem unmarked_context_11_22822_685401 : frontier 10 ⟨685401, by decide⟩
    (prefixCache 11 22822) (prefixPartial 11 22822) = false := by
  decide +kernel

theorem node_context_11_22822_685401 : EJMOriginalGlobalDAGData.nodes 10 ⟨685401, by decide⟩ =
    .split (coordinate 11) (![⟨685315, by decide⟩,⟨685343, by decide⟩,⟨685369, by decide⟩,⟨685400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22822_685401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22822 ⟨685401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22822
    ⟨685401, by decide⟩ (by decide) (![⟨685315, by decide⟩,⟨685343, by decide⟩,⟨685369, by decide⟩,⟨685400, by decide⟩]) unmarked_context_11_22822_685401 node_context_11_22822_685401
  intro a
  fin_cases a
  · exact context_12_91288_685315
  · exact context_12_91289_685343
  · exact context_12_91290_685369
  · exact context_12_91291_685400

theorem selected_cut_27083 : selected 9 ⟨685420, by decide⟩
    (prefixPartial 12 91292) = some ⟨12, 2, 0, 685420, 91292, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_91292_685420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91292 ⟨685420, by decide⟩ :=
  accepted_of_selected 12 91292 ⟨685420, by decide⟩ ⟨12, 2, 0, 685420, 91292, 1573, 65536⟩
    (by decide) selected_cut_27083

theorem selected_cut_27084 : selected 9 ⟨685445, by decide⟩
    (prefixPartial 12 91293) = some ⟨12, 2, 0, 685445, 91293, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_91293_685445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91293 ⟨685445, by decide⟩ :=
  accepted_of_selected 12 91293 ⟨685445, by decide⟩ ⟨12, 2, 0, 685445, 91293, 1821, 65536⟩
    (by decide) selected_cut_27084

theorem selected_cut_27085 : selected 9 ⟨685463, by decide⟩
    (prefixPartial 12 91294) = some ⟨12, 2, 0, 685463, 91294, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_91294_685463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91294 ⟨685463, by decide⟩ :=
  accepted_of_selected 12 91294 ⟨685463, by decide⟩ ⟨12, 2, 0, 685463, 91294, 1873, 65536⟩
    (by decide) selected_cut_27085

theorem selected_cut_27086 : selected 9 ⟨685484, by decide⟩
    (prefixPartial 12 91295) = some ⟨12, 2, 0, 685484, 91295, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_91295_685484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91295 ⟨685484, by decide⟩ :=
  accepted_of_selected 12 91295 ⟨685484, by decide⟩ ⟨12, 2, 0, 685484, 91295, 1665, 65536⟩
    (by decide) selected_cut_27086

theorem unmarked_context_11_22823_685485 : frontier 10 ⟨685485, by decide⟩
    (prefixCache 11 22823) (prefixPartial 11 22823) = false := by
  decide +kernel

theorem node_context_11_22823_685485 : EJMOriginalGlobalDAGData.nodes 10 ⟨685485, by decide⟩ =
    .split (coordinate 11) (![⟨685420, by decide⟩,⟨685445, by decide⟩,⟨685463, by decide⟩,⟨685484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22823_685485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22823 ⟨685485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22823
    ⟨685485, by decide⟩ (by decide) (![⟨685420, by decide⟩,⟨685445, by decide⟩,⟨685463, by decide⟩,⟨685484, by decide⟩]) unmarked_context_11_22823_685485 node_context_11_22823_685485
  intro a
  fin_cases a
  · exact context_12_91292_685420
  · exact context_12_91293_685445
  · exact context_12_91294_685463
  · exact context_12_91295_685484

theorem unmarked_context_10_5705_685486 : frontier 11 ⟨685486, by decide⟩
    (prefixCache 10 5705) (prefixPartial 10 5705) = false := by
  decide +kernel

theorem node_context_10_5705_685486 : EJMOriginalGlobalDAGData.nodes 11 ⟨685486, by decide⟩ =
    .split (coordinate 10) (![⟨685155, by decide⟩,⟨685282, by decide⟩,⟨685401, by decide⟩,⟨685485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5705_685486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5705 ⟨685486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5705
    ⟨685486, by decide⟩ (by decide) (![⟨685155, by decide⟩,⟨685282, by decide⟩,⟨685401, by decide⟩,⟨685485, by decide⟩]) unmarked_context_10_5705_685486 node_context_10_5705_685486
  intro a
  fin_cases a
  · exact context_11_22820_685155
  · exact context_11_22821_685282
  · exact context_11_22822_685401
  · exact context_11_22823_685485

theorem selected_cut_27087 : selected 9 ⟨685516, by decide⟩
    (prefixPartial 12 91296) = some ⟨12, 2, 0, 685516, 91296, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_91296_685516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91296 ⟨685516, by decide⟩ :=
  accepted_of_selected 12 91296 ⟨685516, by decide⟩ ⟨12, 2, 0, 685516, 91296, 2293, 65536⟩
    (by decide) selected_cut_27087

theorem selected_cut_27088 : selected 9 ⟨685536, by decide⟩
    (prefixPartial 12 91297) = some ⟨12, 2, 0, 685536, 91297, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_91297_685536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91297 ⟨685536, by decide⟩ :=
  accepted_of_selected 12 91297 ⟨685536, by decide⟩ ⟨12, 2, 0, 685536, 91297, 1417, 65536⟩
    (by decide) selected_cut_27088

theorem selected_cut_27089 : selected 9 ⟨685551, by decide⟩
    (prefixPartial 12 91298) = some ⟨12, 2, 0, 685551, 91298, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_91298_685551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91298 ⟨685551, by decide⟩ :=
  accepted_of_selected 12 91298 ⟨685551, by decide⟩ ⟨12, 2, 0, 685551, 91298, 1385, 65536⟩
    (by decide) selected_cut_27089

theorem selected_cut_27090 : selected 9 ⟨685564, by decide⟩
    (prefixPartial 12 91299) = some ⟨12, 2, 0, 685564, 91299, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_91299_685564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91299 ⟨685564, by decide⟩ :=
  accepted_of_selected 12 91299 ⟨685564, by decide⟩ ⟨12, 2, 0, 685564, 91299, 1245, 65536⟩
    (by decide) selected_cut_27090

theorem unmarked_context_11_22824_685565 : frontier 10 ⟨685565, by decide⟩
    (prefixCache 11 22824) (prefixPartial 11 22824) = false := by
  decide +kernel

theorem node_context_11_22824_685565 : EJMOriginalGlobalDAGData.nodes 10 ⟨685565, by decide⟩ =
    .split (coordinate 11) (![⟨685516, by decide⟩,⟨685536, by decide⟩,⟨685551, by decide⟩,⟨685564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22824_685565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22824 ⟨685565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22824
    ⟨685565, by decide⟩ (by decide) (![⟨685516, by decide⟩,⟨685536, by decide⟩,⟨685551, by decide⟩,⟨685564, by decide⟩]) unmarked_context_11_22824_685565 node_context_11_22824_685565
  intro a
  fin_cases a
  · exact context_12_91296_685516
  · exact context_12_91297_685536
  · exact context_12_91298_685551
  · exact context_12_91299_685564

theorem selected_cut_27091 : selected 9 ⟨685583, by decide⟩
    (prefixPartial 12 91300) = some ⟨12, 2, 0, 685583, 91300, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_91300_685583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91300 ⟨685583, by decide⟩ :=
  accepted_of_selected 12 91300 ⟨685583, by decide⟩ ⟨12, 2, 0, 685583, 91300, 1365, 65536⟩
    (by decide) selected_cut_27091

theorem selected_cut_27092 : selected 9 ⟨685599, by decide⟩
    (prefixPartial 12 91301) = some ⟨12, 2, 0, 685599, 91301, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_91301_685599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91301 ⟨685599, by decide⟩ :=
  accepted_of_selected 12 91301 ⟨685599, by decide⟩ ⟨12, 2, 0, 685599, 91301, 1285, 65536⟩
    (by decide) selected_cut_27092

theorem selected_cut_27093 : selected 9 ⟨685615, by decide⟩
    (prefixPartial 12 91302) = some ⟨12, 2, 0, 685615, 91302, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_91302_685615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91302 ⟨685615, by decide⟩ :=
  accepted_of_selected 12 91302 ⟨685615, by decide⟩ ⟨12, 2, 0, 685615, 91302, 1361, 65536⟩
    (by decide) selected_cut_27093

theorem selected_cut_27094 : selected 9 ⟨685632, by decide⟩
    (prefixPartial 12 91303) = some ⟨12, 2, 0, 685632, 91303, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_91303_685632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91303 ⟨685632, by decide⟩ :=
  accepted_of_selected 12 91303 ⟨685632, by decide⟩ ⟨12, 2, 0, 685632, 91303, 1297, 65536⟩
    (by decide) selected_cut_27094

theorem unmarked_context_11_22825_685633 : frontier 10 ⟨685633, by decide⟩
    (prefixCache 11 22825) (prefixPartial 11 22825) = false := by
  decide +kernel

theorem node_context_11_22825_685633 : EJMOriginalGlobalDAGData.nodes 10 ⟨685633, by decide⟩ =
    .split (coordinate 11) (![⟨685583, by decide⟩,⟨685599, by decide⟩,⟨685615, by decide⟩,⟨685632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22825_685633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22825 ⟨685633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22825
    ⟨685633, by decide⟩ (by decide) (![⟨685583, by decide⟩,⟨685599, by decide⟩,⟨685615, by decide⟩,⟨685632, by decide⟩]) unmarked_context_11_22825_685633 node_context_11_22825_685633
  intro a
  fin_cases a
  · exact context_12_91300_685583
  · exact context_12_91301_685599
  · exact context_12_91302_685615
  · exact context_12_91303_685632

theorem selected_cut_27095 : selected 9 ⟨685654, by decide⟩
    (prefixPartial 12 91304) = some ⟨12, 2, 0, 685654, 91304, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_91304_685654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91304 ⟨685654, by decide⟩ :=
  accepted_of_selected 12 91304 ⟨685654, by decide⟩ ⟨12, 2, 0, 685654, 91304, 1401, 65536⟩
    (by decide) selected_cut_27095

theorem selected_cut_27096 : selected 9 ⟨685676, by decide⟩
    (prefixPartial 12 91305) = some ⟨12, 2, 0, 685676, 91305, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_91305_685676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91305 ⟨685676, by decide⟩ :=
  accepted_of_selected 12 91305 ⟨685676, by decide⟩ ⟨12, 2, 0, 685676, 91305, 1541, 65536⟩
    (by decide) selected_cut_27096

theorem selected_cut_27097 : selected 9 ⟨685695, by decide⟩
    (prefixPartial 12 91306) = some ⟨12, 2, 0, 685695, 91306, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_91306_685695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91306 ⟨685695, by decide⟩ :=
  accepted_of_selected 12 91306 ⟨685695, by decide⟩ ⟨12, 2, 0, 685695, 91306, 1397, 65536⟩
    (by decide) selected_cut_27097

theorem selected_cut_27098 : selected 9 ⟨685711, by decide⟩
    (prefixPartial 12 91307) = some ⟨12, 2, 0, 685711, 91307, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_91307_685711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91307 ⟨685711, by decide⟩ :=
  accepted_of_selected 12 91307 ⟨685711, by decide⟩ ⟨12, 2, 0, 685711, 91307, 1353, 65536⟩
    (by decide) selected_cut_27098

theorem unmarked_context_11_22826_685712 : frontier 10 ⟨685712, by decide⟩
    (prefixCache 11 22826) (prefixPartial 11 22826) = false := by
  decide +kernel

theorem node_context_11_22826_685712 : EJMOriginalGlobalDAGData.nodes 10 ⟨685712, by decide⟩ =
    .split (coordinate 11) (![⟨685654, by decide⟩,⟨685676, by decide⟩,⟨685695, by decide⟩,⟨685711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22826_685712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22826 ⟨685712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22826
    ⟨685712, by decide⟩ (by decide) (![⟨685654, by decide⟩,⟨685676, by decide⟩,⟨685695, by decide⟩,⟨685711, by decide⟩]) unmarked_context_11_22826_685712 node_context_11_22826_685712
  intro a
  fin_cases a
  · exact context_12_91304_685654
  · exact context_12_91305_685676
  · exact context_12_91306_685695
  · exact context_12_91307_685711

theorem selected_cut_27099 : selected 9 ⟨685727, by decide⟩
    (prefixPartial 12 91308) = some ⟨12, 2, 0, 685727, 91308, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_91308_685727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91308 ⟨685727, by decide⟩ :=
  accepted_of_selected 12 91308 ⟨685727, by decide⟩ ⟨12, 2, 0, 685727, 91308, 1213, 65536⟩
    (by decide) selected_cut_27099

theorem selected_cut_27100 : selected 9 ⟨685750, by decide⟩
    (prefixPartial 12 91309) = some ⟨12, 2, 0, 685750, 91309, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_91309_685750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91309 ⟨685750, by decide⟩ :=
  accepted_of_selected 12 91309 ⟨685750, by decide⟩ ⟨12, 2, 0, 685750, 91309, 1265, 65536⟩
    (by decide) selected_cut_27100

theorem selected_cut_27101 : selected 9 ⟨685763, by decide⟩
    (prefixPartial 12 91310) = some ⟨12, 2, 0, 685763, 91310, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_91310_685763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91310 ⟨685763, by decide⟩ :=
  accepted_of_selected 12 91310 ⟨685763, by decide⟩ ⟨12, 2, 0, 685763, 91310, 1301, 65536⟩
    (by decide) selected_cut_27101

theorem selected_cut_27102 : selected 9 ⟨685777, by decide⟩
    (prefixPartial 12 91311) = some ⟨12, 2, 0, 685777, 91311, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_91311_685777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91311 ⟨685777, by decide⟩ :=
  accepted_of_selected 12 91311 ⟨685777, by decide⟩ ⟨12, 2, 0, 685777, 91311, 1137, 65536⟩
    (by decide) selected_cut_27102

theorem unmarked_context_11_22827_685778 : frontier 10 ⟨685778, by decide⟩
    (prefixCache 11 22827) (prefixPartial 11 22827) = false := by
  decide +kernel

theorem node_context_11_22827_685778 : EJMOriginalGlobalDAGData.nodes 10 ⟨685778, by decide⟩ =
    .split (coordinate 11) (![⟨685727, by decide⟩,⟨685750, by decide⟩,⟨685763, by decide⟩,⟨685777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22827_685778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22827 ⟨685778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22827
    ⟨685778, by decide⟩ (by decide) (![⟨685727, by decide⟩,⟨685750, by decide⟩,⟨685763, by decide⟩,⟨685777, by decide⟩]) unmarked_context_11_22827_685778 node_context_11_22827_685778
  intro a
  fin_cases a
  · exact context_12_91308_685727
  · exact context_12_91309_685750
  · exact context_12_91310_685763
  · exact context_12_91311_685777

theorem unmarked_context_10_5706_685779 : frontier 11 ⟨685779, by decide⟩
    (prefixCache 10 5706) (prefixPartial 10 5706) = false := by
  decide +kernel

theorem node_context_10_5706_685779 : EJMOriginalGlobalDAGData.nodes 11 ⟨685779, by decide⟩ =
    .split (coordinate 10) (![⟨685565, by decide⟩,⟨685633, by decide⟩,⟨685712, by decide⟩,⟨685778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5706_685779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5706 ⟨685779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5706
    ⟨685779, by decide⟩ (by decide) (![⟨685565, by decide⟩,⟨685633, by decide⟩,⟨685712, by decide⟩,⟨685778, by decide⟩]) unmarked_context_10_5706_685779 node_context_10_5706_685779
  intro a
  fin_cases a
  · exact context_11_22824_685565
  · exact context_11_22825_685633
  · exact context_11_22826_685712
  · exact context_11_22827_685778

theorem selected_cut_27103 : selected 9 ⟨685830, by decide⟩
    (prefixPartial 12 91312) = some ⟨12, 2, 0, 685830, 91312, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_91312_685830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91312 ⟨685830, by decide⟩ :=
  accepted_of_selected 12 91312 ⟨685830, by decide⟩ ⟨12, 2, 0, 685830, 91312, 2161, 65536⟩
    (by decide) selected_cut_27103

theorem selected_cut_27104 : selected 9 ⟨685843, by decide⟩
    (prefixPartial 12 91313) = some ⟨12, 2, 0, 685843, 91313, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_91313_685843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91313 ⟨685843, by decide⟩ :=
  accepted_of_selected 12 91313 ⟨685843, by decide⟩ ⟨12, 2, 0, 685843, 91313, 1173, 65536⟩
    (by decide) selected_cut_27104

theorem selected_cut_27105 : selected 9 ⟨685860, by decide⟩
    (prefixPartial 12 91314) = some ⟨12, 2, 0, 685860, 91314, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_91314_685860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91314 ⟨685860, by decide⟩ :=
  accepted_of_selected 12 91314 ⟨685860, by decide⟩ ⟨12, 2, 0, 685860, 91314, 1261, 65536⟩
    (by decide) selected_cut_27105

theorem selected_cut_27106 : selected 9 ⟨685874, by decide⟩
    (prefixPartial 12 91315) = some ⟨12, 2, 0, 685874, 91315, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_91315_685874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91315 ⟨685874, by decide⟩ :=
  accepted_of_selected 12 91315 ⟨685874, by decide⟩ ⟨12, 2, 0, 685874, 91315, 1201, 65536⟩
    (by decide) selected_cut_27106

theorem unmarked_context_11_22828_685875 : frontier 10 ⟨685875, by decide⟩
    (prefixCache 11 22828) (prefixPartial 11 22828) = false := by
  decide +kernel

theorem node_context_11_22828_685875 : EJMOriginalGlobalDAGData.nodes 10 ⟨685875, by decide⟩ =
    .split (coordinate 11) (![⟨685830, by decide⟩,⟨685843, by decide⟩,⟨685860, by decide⟩,⟨685874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22828_685875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22828 ⟨685875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22828
    ⟨685875, by decide⟩ (by decide) (![⟨685830, by decide⟩,⟨685843, by decide⟩,⟨685860, by decide⟩,⟨685874, by decide⟩]) unmarked_context_11_22828_685875 node_context_11_22828_685875
  intro a
  fin_cases a
  · exact context_12_91312_685830
  · exact context_12_91313_685843
  · exact context_12_91314_685860
  · exact context_12_91315_685874

theorem selected_cut_27107 : selected 9 ⟨685890, by decide⟩
    (prefixPartial 12 91316) = some ⟨12, 2, 0, 685890, 91316, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_91316_685890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91316 ⟨685890, by decide⟩ :=
  accepted_of_selected 12 91316 ⟨685890, by decide⟩ ⟨12, 2, 0, 685890, 91316, 1121, 65536⟩
    (by decide) selected_cut_27107

theorem selected_cut_27108 : selected 9 ⟨685899, by decide⟩
    (prefixPartial 12 91317) = some ⟨12, 2, 0, 685899, 91317, 985, 65536⟩ := by
  decide +kernel

theorem context_12_91317_685899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91317 ⟨685899, by decide⟩ :=
  accepted_of_selected 12 91317 ⟨685899, by decide⟩ ⟨12, 2, 0, 685899, 91317, 985, 65536⟩
    (by decide) selected_cut_27108

theorem selected_cut_27109 : selected 9 ⟨685913, by decide⟩
    (prefixPartial 12 91318) = some ⟨12, 2, 0, 685913, 91318, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_91318_685913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91318 ⟨685913, by decide⟩ :=
  accepted_of_selected 12 91318 ⟨685913, by decide⟩ ⟨12, 2, 0, 685913, 91318, 1065, 65536⟩
    (by decide) selected_cut_27109

theorem selected_cut_27110 : selected 9 ⟨685927, by decide⟩
    (prefixPartial 12 91319) = some ⟨12, 2, 0, 685927, 91319, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_91319_685927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91319 ⟨685927, by decide⟩ :=
  accepted_of_selected 12 91319 ⟨685927, by decide⟩ ⟨12, 2, 0, 685927, 91319, 1105, 65536⟩
    (by decide) selected_cut_27110

theorem unmarked_context_11_22829_685928 : frontier 10 ⟨685928, by decide⟩
    (prefixCache 11 22829) (prefixPartial 11 22829) = false := by
  decide +kernel

theorem node_context_11_22829_685928 : EJMOriginalGlobalDAGData.nodes 10 ⟨685928, by decide⟩ =
    .split (coordinate 11) (![⟨685890, by decide⟩,⟨685899, by decide⟩,⟨685913, by decide⟩,⟨685927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22829_685928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22829 ⟨685928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22829
    ⟨685928, by decide⟩ (by decide) (![⟨685890, by decide⟩,⟨685899, by decide⟩,⟨685913, by decide⟩,⟨685927, by decide⟩]) unmarked_context_11_22829_685928 node_context_11_22829_685928
  intro a
  fin_cases a
  · exact context_12_91316_685890
  · exact context_12_91317_685899
  · exact context_12_91318_685913
  · exact context_12_91319_685927

theorem selected_cut_27111 : selected 9 ⟨685946, by decide⟩
    (prefixPartial 12 91320) = some ⟨12, 2, 0, 685946, 91320, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_91320_685946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91320 ⟨685946, by decide⟩ :=
  accepted_of_selected 12 91320 ⟨685946, by decide⟩ ⟨12, 2, 0, 685946, 91320, 1181, 65536⟩
    (by decide) selected_cut_27111

theorem selected_cut_27112 : selected 9 ⟨685961, by decide⟩
    (prefixPartial 12 91321) = some ⟨12, 2, 0, 685961, 91321, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_91321_685961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91321 ⟨685961, by decide⟩ :=
  accepted_of_selected 12 91321 ⟨685961, by decide⟩ ⟨12, 2, 0, 685961, 91321, 1101, 65536⟩
    (by decide) selected_cut_27112

theorem selected_cut_27113 : selected 9 ⟨685978, by decide⟩
    (prefixPartial 12 91322) = some ⟨12, 2, 0, 685978, 91322, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_91322_685978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91322 ⟨685978, by decide⟩ :=
  accepted_of_selected 12 91322 ⟨685978, by decide⟩ ⟨12, 2, 0, 685978, 91322, 1165, 65536⟩
    (by decide) selected_cut_27113

theorem selected_cut_27114 : selected 9 ⟨685999, by decide⟩
    (prefixPartial 12 91323) = some ⟨12, 2, 0, 685999, 91323, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_91323_685999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91323 ⟨685999, by decide⟩ :=
  accepted_of_selected 12 91323 ⟨685999, by decide⟩ ⟨12, 2, 0, 685999, 91323, 1189, 65536⟩
    (by decide) selected_cut_27114

theorem unmarked_context_11_22830_686000 : frontier 10 ⟨686000, by decide⟩
    (prefixCache 11 22830) (prefixPartial 11 22830) = false := by
  decide +kernel

theorem node_context_11_22830_686000 : EJMOriginalGlobalDAGData.nodes 10 ⟨686000, by decide⟩ =
    .split (coordinate 11) (![⟨685946, by decide⟩,⟨685961, by decide⟩,⟨685978, by decide⟩,⟨685999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22830_686000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22830 ⟨686000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22830
    ⟨686000, by decide⟩ (by decide) (![⟨685946, by decide⟩,⟨685961, by decide⟩,⟨685978, by decide⟩,⟨685999, by decide⟩]) unmarked_context_11_22830_686000 node_context_11_22830_686000
  intro a
  fin_cases a
  · exact context_12_91320_685946
  · exact context_12_91321_685961
  · exact context_12_91322_685978
  · exact context_12_91323_685999

theorem selected_cut_27115 : selected 10 ⟨686041, by decide⟩
    (prefixPartial 11 22831) = some ⟨11, 2, 0, 686041, 22831, 3485, 262144⟩ := by
  decide +kernel

theorem context_11_22831_686041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22831 ⟨686041, by decide⟩ :=
  accepted_of_selected 11 22831 ⟨686041, by decide⟩ ⟨11, 2, 0, 686041, 22831, 3485, 262144⟩
    (by decide) selected_cut_27115

theorem unmarked_context_10_5707_686042 : frontier 11 ⟨686042, by decide⟩
    (prefixCache 10 5707) (prefixPartial 10 5707) = false := by
  decide +kernel

theorem node_context_10_5707_686042 : EJMOriginalGlobalDAGData.nodes 11 ⟨686042, by decide⟩ =
    .split (coordinate 10) (![⟨685875, by decide⟩,⟨685928, by decide⟩,⟨686000, by decide⟩,⟨686041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5707_686042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5707 ⟨686042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5707
    ⟨686042, by decide⟩ (by decide) (![⟨685875, by decide⟩,⟨685928, by decide⟩,⟨686000, by decide⟩,⟨686041, by decide⟩]) unmarked_context_10_5707_686042 node_context_10_5707_686042
  intro a
  fin_cases a
  · exact context_11_22828_685875
  · exact context_11_22829_685928
  · exact context_11_22830_686000
  · exact context_11_22831_686041

theorem unmarked_context_9_1426_686043 : frontier 12 ⟨686043, by decide⟩
    (prefixCache 9 1426) (prefixPartial 9 1426) = false := by
  decide +kernel

theorem node_context_9_1426_686043 : EJMOriginalGlobalDAGData.nodes 12 ⟨686043, by decide⟩ =
    .split (coordinate 9) (![⟨685041, by decide⟩,⟨685486, by decide⟩,⟨685779, by decide⟩,⟨686042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1426_686043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1426 ⟨686043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1426
    ⟨686043, by decide⟩ (by decide) (![⟨685041, by decide⟩,⟨685486, by decide⟩,⟨685779, by decide⟩,⟨686042, by decide⟩]) unmarked_context_9_1426_686043 node_context_9_1426_686043
  intro a
  fin_cases a
  · exact context_10_5704_685041
  · exact context_10_5705_685486
  · exact context_10_5706_685779
  · exact context_10_5707_686042

theorem selected_cut_27116 : selected 10 ⟨686062, by decide⟩
    (prefixPartial 11 22832) = some ⟨11, 2, 0, 686062, 22832, 1957, 262144⟩ := by
  decide +kernel

theorem context_11_22832_686062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22832 ⟨686062, by decide⟩ :=
  accepted_of_selected 11 22832 ⟨686062, by decide⟩ ⟨11, 2, 0, 686062, 22832, 1957, 262144⟩
    (by decide) selected_cut_27116

theorem selected_cut_27117 : selected 10 ⟨686089, by decide⟩
    (prefixPartial 11 22833) = some ⟨11, 2, 0, 686089, 22833, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_22833_686089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22833 ⟨686089, by decide⟩ :=
  accepted_of_selected 11 22833 ⟨686089, by decide⟩ ⟨11, 2, 0, 686089, 22833, 2625, 262144⟩
    (by decide) selected_cut_27117

theorem selected_cut_27118 : selected 10 ⟨686123, by decide⟩
    (prefixPartial 11 22834) = some ⟨11, 2, 0, 686123, 22834, 2653, 262144⟩ := by
  decide +kernel

theorem context_11_22834_686123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22834 ⟨686123, by decide⟩ :=
  accepted_of_selected 11 22834 ⟨686123, by decide⟩ ⟨11, 2, 0, 686123, 22834, 2653, 262144⟩
    (by decide) selected_cut_27118

theorem selected_cut_27119 : selected 10 ⟨686158, by decide⟩
    (prefixPartial 11 22835) = some ⟨11, 2, 0, 686158, 22835, 2553, 262144⟩ := by
  decide +kernel

theorem context_11_22835_686158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22835 ⟨686158, by decide⟩ :=
  accepted_of_selected 11 22835 ⟨686158, by decide⟩ ⟨11, 2, 0, 686158, 22835, 2553, 262144⟩
    (by decide) selected_cut_27119

theorem unmarked_context_10_5708_686159 : frontier 11 ⟨686159, by decide⟩
    (prefixCache 10 5708) (prefixPartial 10 5708) = false := by
  decide +kernel

theorem node_context_10_5708_686159 : EJMOriginalGlobalDAGData.nodes 11 ⟨686159, by decide⟩ =
    .split (coordinate 10) (![⟨686062, by decide⟩,⟨686089, by decide⟩,⟨686123, by decide⟩,⟨686158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5708_686159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5708 ⟨686159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5708
    ⟨686159, by decide⟩ (by decide) (![⟨686062, by decide⟩,⟨686089, by decide⟩,⟨686123, by decide⟩,⟨686158, by decide⟩]) unmarked_context_10_5708_686159 node_context_10_5708_686159
  intro a
  fin_cases a
  · exact context_11_22832_686062
  · exact context_11_22833_686089
  · exact context_11_22834_686123
  · exact context_11_22835_686158

theorem selected_cut_27120 : selected 10 ⟨686180, by decide⟩
    (prefixPartial 11 22836) = some ⟨11, 2, 0, 686180, 22836, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_22836_686180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22836 ⟨686180, by decide⟩ :=
  accepted_of_selected 11 22836 ⟨686180, by decide⟩ ⟨11, 2, 0, 686180, 22836, 1981, 262144⟩
    (by decide) selected_cut_27120

theorem selected_cut_27121 : selected 10 ⟨686197, by decide⟩
    (prefixPartial 11 22837) = some ⟨11, 2, 0, 686197, 22837, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_22837_686197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22837 ⟨686197, by decide⟩ :=
  accepted_of_selected 11 22837 ⟨686197, by decide⟩ ⟨11, 2, 0, 686197, 22837, 1609, 262144⟩
    (by decide) selected_cut_27121

theorem selected_cut_27122 : selected 10 ⟨686220, by decide⟩
    (prefixPartial 11 22838) = some ⟨11, 2, 0, 686220, 22838, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_22838_686220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22838 ⟨686220, by decide⟩ :=
  accepted_of_selected 11 22838 ⟨686220, by decide⟩ ⟨11, 2, 0, 686220, 22838, 2193, 262144⟩
    (by decide) selected_cut_27122

theorem selected_cut_27123 : selected 10 ⟨686239, by decide⟩
    (prefixPartial 11 22839) = some ⟨11, 2, 0, 686239, 22839, 1873, 262144⟩ := by
  decide +kernel

theorem context_11_22839_686239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22839 ⟨686239, by decide⟩ :=
  accepted_of_selected 11 22839 ⟨686239, by decide⟩ ⟨11, 2, 0, 686239, 22839, 1873, 262144⟩
    (by decide) selected_cut_27123

theorem unmarked_context_10_5709_686240 : frontier 11 ⟨686240, by decide⟩
    (prefixCache 10 5709) (prefixPartial 10 5709) = false := by
  decide +kernel

theorem node_context_10_5709_686240 : EJMOriginalGlobalDAGData.nodes 11 ⟨686240, by decide⟩ =
    .split (coordinate 10) (![⟨686180, by decide⟩,⟨686197, by decide⟩,⟨686220, by decide⟩,⟨686239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5709_686240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5709 ⟨686240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5709
    ⟨686240, by decide⟩ (by decide) (![⟨686180, by decide⟩,⟨686197, by decide⟩,⟨686220, by decide⟩,⟨686239, by decide⟩]) unmarked_context_10_5709_686240 node_context_10_5709_686240
  intro a
  fin_cases a
  · exact context_11_22836_686180
  · exact context_11_22837_686197
  · exact context_11_22838_686220
  · exact context_11_22839_686239

theorem selected_cut_27124 : selected 10 ⟨686255, by decide⟩
    (prefixPartial 11 22840) = some ⟨11, 2, 0, 686255, 22840, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_22840_686255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22840 ⟨686255, by decide⟩ :=
  accepted_of_selected 11 22840 ⟨686255, by decide⟩ ⟨11, 2, 0, 686255, 22840, 1489, 262144⟩
    (by decide) selected_cut_27124

theorem selected_cut_27125 : selected 10 ⟨686268, by decide⟩
    (prefixPartial 11 22841) = some ⟨11, 2, 0, 686268, 22841, 1193, 262144⟩ := by
  decide +kernel

theorem context_11_22841_686268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22841 ⟨686268, by decide⟩ :=
  accepted_of_selected 11 22841 ⟨686268, by decide⟩ ⟨11, 2, 0, 686268, 22841, 1193, 262144⟩
    (by decide) selected_cut_27125

theorem selected_cut_27126 : selected 10 ⟨686280, by decide⟩
    (prefixPartial 11 22842) = some ⟨11, 2, 0, 686280, 22842, 1041, 262144⟩ := by
  decide +kernel

theorem context_11_22842_686280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22842 ⟨686280, by decide⟩ :=
  accepted_of_selected 11 22842 ⟨686280, by decide⟩ ⟨11, 2, 0, 686280, 22842, 1041, 262144⟩
    (by decide) selected_cut_27126

theorem selected_cut_27127 : selected 10 ⟨686292, by decide⟩
    (prefixPartial 11 22843) = some ⟨11, 2, 0, 686292, 22843, 849, 262144⟩ := by
  decide +kernel

theorem context_11_22843_686292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22843 ⟨686292, by decide⟩ :=
  accepted_of_selected 11 22843 ⟨686292, by decide⟩ ⟨11, 2, 0, 686292, 22843, 849, 262144⟩
    (by decide) selected_cut_27127

theorem unmarked_context_10_5710_686293 : frontier 11 ⟨686293, by decide⟩
    (prefixCache 10 5710) (prefixPartial 10 5710) = false := by
  decide +kernel

theorem node_context_10_5710_686293 : EJMOriginalGlobalDAGData.nodes 11 ⟨686293, by decide⟩ =
    .split (coordinate 10) (![⟨686255, by decide⟩,⟨686268, by decide⟩,⟨686280, by decide⟩,⟨686292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5710_686293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5710 ⟨686293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5710
    ⟨686293, by decide⟩ (by decide) (![⟨686255, by decide⟩,⟨686268, by decide⟩,⟨686280, by decide⟩,⟨686292, by decide⟩]) unmarked_context_10_5710_686293 node_context_10_5710_686293
  intro a
  fin_cases a
  · exact context_11_22840_686255
  · exact context_11_22841_686268
  · exact context_11_22842_686280
  · exact context_11_22843_686292

theorem selected_cut_27128 : selected 11 ⟨686314, by decide⟩
    (prefixPartial 10 5711) = some ⟨10, 2, 0, 686314, 5711, 1557, 1048576⟩ := by
  decide +kernel

theorem context_10_5711_686314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5711 ⟨686314, by decide⟩ :=
  accepted_of_selected 10 5711 ⟨686314, by decide⟩ ⟨10, 2, 0, 686314, 5711, 1557, 1048576⟩
    (by decide) selected_cut_27128

theorem unmarked_context_9_1427_686315 : frontier 12 ⟨686315, by decide⟩
    (prefixCache 9 1427) (prefixPartial 9 1427) = false := by
  decide +kernel

theorem node_context_9_1427_686315 : EJMOriginalGlobalDAGData.nodes 12 ⟨686315, by decide⟩ =
    .split (coordinate 9) (![⟨686159, by decide⟩,⟨686240, by decide⟩,⟨686293, by decide⟩,⟨686314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1427_686315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1427 ⟨686315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1427
    ⟨686315, by decide⟩ (by decide) (![⟨686159, by decide⟩,⟨686240, by decide⟩,⟨686293, by decide⟩,⟨686314, by decide⟩]) unmarked_context_9_1427_686315 node_context_9_1427_686315
  intro a
  fin_cases a
  · exact context_10_5708_686159
  · exact context_10_5709_686240
  · exact context_10_5710_686293
  · exact context_10_5711_686314

theorem unmarked_context_8_356_686316 : frontier 13 ⟨686316, by decide⟩
    (prefixCache 8 356) (prefixPartial 8 356) = false := by
  decide +kernel

theorem node_context_8_356_686316 : EJMOriginalGlobalDAGData.nodes 13 ⟨686316, by decide⟩ =
    .split (coordinate 8) (![⟨682055, by decide⟩,⟨684640, by decide⟩,⟨686043, by decide⟩,⟨686315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_356_686316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 356 ⟨686316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 356
    ⟨686316, by decide⟩ (by decide) (![⟨682055, by decide⟩,⟨684640, by decide⟩,⟨686043, by decide⟩,⟨686315, by decide⟩]) unmarked_context_8_356_686316 node_context_8_356_686316
  intro a
  fin_cases a
  · exact context_9_1424_682055
  · exact context_9_1425_684640
  · exact context_9_1426_686043
  · exact context_9_1427_686315

theorem selected_cut_27129 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 22848) = some ⟨11, 1, 0, 434745, 22848, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22848_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22848 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 22848 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 22848, 1, 262144⟩
    (by decide) selected_cut_27129

theorem selected_cut_27130 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91396) = some ⟨12, 1, 0, 448748, 91396, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91396_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91396 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91396 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91396, 1, 65536⟩
    (by decide) selected_cut_27130

theorem selected_cut_27131 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 91397) = some ⟨12, 1, 0, 34034, 91397, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91397_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91397 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 91397 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 91397, 1, 65536⟩
    (by decide) selected_cut_27131

theorem selected_cut_27132 : selected 8 ⟨686376, by decide⟩
    (prefixPartial 13 365592) = some ⟨13, 2, 0, 686376, 365592, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_365592_686376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365592 ⟨686376, by decide⟩ :=
  accepted_of_selected 13 365592 ⟨686376, by decide⟩ ⟨13, 2, 0, 686376, 365592, 2441, 16384⟩
    (by decide) selected_cut_27132

theorem selected_cut_27133 : selected 8 ⟨686430, by decide⟩
    (prefixPartial 13 365593) = some ⟨13, 2, 0, 686430, 365593, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_365593_686430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365593 ⟨686430, by decide⟩ :=
  accepted_of_selected 13 365593 ⟨686430, by decide⟩ ⟨13, 2, 0, 686430, 365593, 1269, 16384⟩
    (by decide) selected_cut_27133

theorem selected_cut_27134 : selected 8 ⟨686457, by decide⟩
    (prefixPartial 13 365594) = some ⟨13, 2, 0, 686457, 365594, 621, 16384⟩ := by
  decide +kernel

theorem context_13_365594_686457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365594 ⟨686457, by decide⟩ :=
  accepted_of_selected 13 365594 ⟨686457, by decide⟩ ⟨13, 2, 0, 686457, 365594, 621, 16384⟩
    (by decide) selected_cut_27134

theorem selected_cut_27135 : selected 8 ⟨686465, by decide⟩
    (prefixPartial 13 365595) = some ⟨13, 2, 0, 686465, 365595, 141, 16384⟩ := by
  decide +kernel

theorem context_13_365595_686465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365595 ⟨686465, by decide⟩ :=
  accepted_of_selected 13 365595 ⟨686465, by decide⟩ ⟨13, 2, 0, 686465, 365595, 141, 16384⟩
    (by decide) selected_cut_27135

theorem unmarked_context_12_91398_686466 : frontier 9 ⟨686466, by decide⟩
    (prefixCache 12 91398) (prefixPartial 12 91398) = false := by
  decide +kernel

theorem node_context_12_91398_686466 : EJMOriginalGlobalDAGData.nodes 9 ⟨686466, by decide⟩ =
    .split (coordinate 12) (![⟨686376, by decide⟩,⟨686430, by decide⟩,⟨686457, by decide⟩,⟨686465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91398_686466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91398 ⟨686466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91398
    ⟨686466, by decide⟩ (by decide) (![⟨686376, by decide⟩,⟨686430, by decide⟩,⟨686457, by decide⟩,⟨686465, by decide⟩]) unmarked_context_12_91398_686466 node_context_12_91398_686466
  intro a
  fin_cases a
  · exact context_13_365592_686376
  · exact context_13_365593_686430
  · exact context_13_365594_686457
  · exact context_13_365595_686465

theorem selected_cut_27136 : selected 8 ⟨686543, by decide⟩
    (prefixPartial 13 365596) = some ⟨13, 2, 0, 686543, 365596, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_365596_686543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365596 ⟨686543, by decide⟩ :=
  accepted_of_selected 13 365596 ⟨686543, by decide⟩ ⟨13, 2, 0, 686543, 365596, 2633, 16384⟩
    (by decide) selected_cut_27136

theorem selected_cut_27137 : selected 8 ⟨686594, by decide⟩
    (prefixPartial 13 365597) = some ⟨13, 2, 0, 686594, 365597, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_365597_686594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365597 ⟨686594, by decide⟩ :=
  accepted_of_selected 13 365597 ⟨686594, by decide⟩ ⟨13, 2, 0, 686594, 365597, 1369, 16384⟩
    (by decide) selected_cut_27137

theorem selected_cut_27138 : selected 8 ⟨686614, by decide⟩
    (prefixPartial 13 365598) = some ⟨13, 2, 0, 686614, 365598, 661, 16384⟩ := by
  decide +kernel

theorem context_13_365598_686614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365598 ⟨686614, by decide⟩ :=
  accepted_of_selected 13 365598 ⟨686614, by decide⟩ ⟨13, 2, 0, 686614, 365598, 661, 16384⟩
    (by decide) selected_cut_27138

theorem selected_cut_27139 : selected 8 ⟨686620, by decide⟩
    (prefixPartial 13 365599) = some ⟨13, 2, 0, 686620, 365599, 133, 16384⟩ := by
  decide +kernel

theorem context_13_365599_686620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365599 ⟨686620, by decide⟩ :=
  accepted_of_selected 13 365599 ⟨686620, by decide⟩ ⟨13, 2, 0, 686620, 365599, 133, 16384⟩
    (by decide) selected_cut_27139

theorem unmarked_context_12_91399_686621 : frontier 9 ⟨686621, by decide⟩
    (prefixCache 12 91399) (prefixPartial 12 91399) = false := by
  decide +kernel

theorem node_context_12_91399_686621 : EJMOriginalGlobalDAGData.nodes 9 ⟨686621, by decide⟩ =
    .split (coordinate 12) (![⟨686543, by decide⟩,⟨686594, by decide⟩,⟨686614, by decide⟩,⟨686620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91399_686621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91399 ⟨686621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91399
    ⟨686621, by decide⟩ (by decide) (![⟨686543, by decide⟩,⟨686594, by decide⟩,⟨686614, by decide⟩,⟨686620, by decide⟩]) unmarked_context_12_91399_686621 node_context_12_91399_686621
  intro a
  fin_cases a
  · exact context_13_365596_686543
  · exact context_13_365597_686594
  · exact context_13_365598_686614
  · exact context_13_365599_686620

theorem unmarked_context_11_22849_686622 : frontier 10 ⟨686622, by decide⟩
    (prefixCache 11 22849) (prefixPartial 11 22849) = false := by
  decide +kernel

theorem node_context_11_22849_686622 : EJMOriginalGlobalDAGData.nodes 10 ⟨686622, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨686466, by decide⟩,⟨686621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22849_686622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22849 ⟨686622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22849
    ⟨686622, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨686466, by decide⟩,⟨686621, by decide⟩]) unmarked_context_11_22849_686622 node_context_11_22849_686622
  intro a
  fin_cases a
  · exact context_12_91396_448748
  · exact context_12_91397_34034
  · exact context_12_91398_686466
  · exact context_12_91399_686621

theorem selected_cut_27140 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91400) = some ⟨12, 1, 0, 448748, 91400, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91400_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91400 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91400 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91400, 1, 65536⟩
    (by decide) selected_cut_27140

theorem selected_cut_27141 : selected 8 ⟨686726, by decide⟩
    (prefixPartial 13 365604) = some ⟨13, 2, 0, 686726, 365604, 4057, 16384⟩ := by
  decide +kernel

theorem context_13_365604_686726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365604 ⟨686726, by decide⟩ :=
  accepted_of_selected 13 365604 ⟨686726, by decide⟩ ⟨13, 2, 0, 686726, 365604, 4057, 16384⟩
    (by decide) selected_cut_27141

theorem selected_cut_27142 : selected 8 ⟨686790, by decide⟩
    (prefixPartial 13 365605) = some ⟨13, 2, 0, 686790, 365605, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_365605_686790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365605 ⟨686790, by decide⟩ :=
  accepted_of_selected 13 365605 ⟨686790, by decide⟩ ⟨13, 2, 0, 686790, 365605, 2433, 16384⟩
    (by decide) selected_cut_27142

theorem selected_cut_27143 : selected 8 ⟨686841, by decide⟩
    (prefixPartial 13 365606) = some ⟨13, 2, 0, 686841, 365606, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_365606_686841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365606 ⟨686841, by decide⟩ :=
  accepted_of_selected 13 365606 ⟨686841, by decide⟩ ⟨13, 2, 0, 686841, 365606, 2261, 16384⟩
    (by decide) selected_cut_27143

theorem selected_cut_27144 : selected 8 ⟨686853, by decide⟩
    (prefixPartial 13 365607) = some ⟨13, 2, 0, 686853, 365607, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_365607_686853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365607 ⟨686853, by decide⟩ :=
  accepted_of_selected 13 365607 ⟨686853, by decide⟩ ⟨13, 2, 0, 686853, 365607, 1005, 16384⟩
    (by decide) selected_cut_27144

theorem unmarked_context_12_91401_686854 : frontier 9 ⟨686854, by decide⟩
    (prefixCache 12 91401) (prefixPartial 12 91401) = false := by
  decide +kernel

theorem node_context_12_91401_686854 : EJMOriginalGlobalDAGData.nodes 9 ⟨686854, by decide⟩ =
    .split (coordinate 12) (![⟨686726, by decide⟩,⟨686790, by decide⟩,⟨686841, by decide⟩,⟨686853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91401_686854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91401 ⟨686854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91401
    ⟨686854, by decide⟩ (by decide) (![⟨686726, by decide⟩,⟨686790, by decide⟩,⟨686841, by decide⟩,⟨686853, by decide⟩]) unmarked_context_12_91401_686854 node_context_12_91401_686854
  intro a
  fin_cases a
  · exact context_13_365604_686726
  · exact context_13_365605_686790
  · exact context_13_365606_686841
  · exact context_13_365607_686853

theorem selected_cut_27145 : selected 8 ⟨686942, by decide⟩
    (prefixPartial 13 365608) = some ⟨13, 2, 0, 686942, 365608, 3509, 16384⟩ := by
  decide +kernel

theorem context_13_365608_686942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365608 ⟨686942, by decide⟩ :=
  accepted_of_selected 13 365608 ⟨686942, by decide⟩ ⟨13, 2, 0, 686942, 365608, 3509, 16384⟩
    (by decide) selected_cut_27145

theorem selected_cut_27146 : selected 8 ⟨686992, by decide⟩
    (prefixPartial 13 365609) = some ⟨13, 2, 0, 686992, 365609, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_365609_686992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365609 ⟨686992, by decide⟩ :=
  accepted_of_selected 13 365609 ⟨686992, by decide⟩ ⟨13, 2, 0, 686992, 365609, 2581, 16384⟩
    (by decide) selected_cut_27146

theorem selected_cut_27147 : selected 8 ⟨687029, by decide⟩
    (prefixPartial 13 365610) = some ⟨13, 2, 0, 687029, 365610, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_365610_687029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365610 ⟨687029, by decide⟩ :=
  accepted_of_selected 13 365610 ⟨687029, by decide⟩ ⟨13, 2, 0, 687029, 365610, 2169, 16384⟩
    (by decide) selected_cut_27147

theorem selected_cut_27148 : selected 8 ⟨687051, by decide⟩
    (prefixPartial 13 365611) = some ⟨13, 2, 0, 687051, 365611, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_365611_687051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365611 ⟨687051, by decide⟩ :=
  accepted_of_selected 13 365611 ⟨687051, by decide⟩ ⟨13, 2, 0, 687051, 365611, 1129, 16384⟩
    (by decide) selected_cut_27148

theorem unmarked_context_12_91402_687052 : frontier 9 ⟨687052, by decide⟩
    (prefixCache 12 91402) (prefixPartial 12 91402) = false := by
  decide +kernel

theorem node_context_12_91402_687052 : EJMOriginalGlobalDAGData.nodes 9 ⟨687052, by decide⟩ =
    .split (coordinate 12) (![⟨686942, by decide⟩,⟨686992, by decide⟩,⟨687029, by decide⟩,⟨687051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91402_687052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91402 ⟨687052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91402
    ⟨687052, by decide⟩ (by decide) (![⟨686942, by decide⟩,⟨686992, by decide⟩,⟨687029, by decide⟩,⟨687051, by decide⟩]) unmarked_context_12_91402_687052 node_context_12_91402_687052
  intro a
  fin_cases a
  · exact context_13_365608_686942
  · exact context_13_365609_686992
  · exact context_13_365610_687029
  · exact context_13_365611_687051

theorem selected_cut_27149 : selected 8 ⟨687129, by decide⟩
    (prefixPartial 13 365612) = some ⟨13, 2, 0, 687129, 365612, 3973, 16384⟩ := by
  decide +kernel

theorem context_13_365612_687129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365612 ⟨687129, by decide⟩ :=
  accepted_of_selected 13 365612 ⟨687129, by decide⟩ ⟨13, 2, 0, 687129, 365612, 3973, 16384⟩
    (by decide) selected_cut_27149

theorem selected_cut_27150 : selected 8 ⟨687187, by decide⟩
    (prefixPartial 13 365613) = some ⟨13, 2, 0, 687187, 365613, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_365613_687187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365613 ⟨687187, by decide⟩ :=
  accepted_of_selected 13 365613 ⟨687187, by decide⟩ ⟨13, 2, 0, 687187, 365613, 2857, 16384⟩
    (by decide) selected_cut_27150

theorem selected_cut_27151 : selected 8 ⟨687246, by decide⟩
    (prefixPartial 13 365614) = some ⟨13, 2, 0, 687246, 365614, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_365614_687246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365614 ⟨687246, by decide⟩ :=
  accepted_of_selected 13 365614 ⟨687246, by decide⟩ ⟨13, 2, 0, 687246, 365614, 2597, 16384⟩
    (by decide) selected_cut_27151

theorem selected_cut_27152 : selected 8 ⟨687258, by decide⟩
    (prefixPartial 13 365615) = some ⟨13, 2, 0, 687258, 365615, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_365615_687258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365615 ⟨687258, by decide⟩ :=
  accepted_of_selected 13 365615 ⟨687258, by decide⟩ ⟨13, 2, 0, 687258, 365615, 1121, 16384⟩
    (by decide) selected_cut_27152

theorem unmarked_context_12_91403_687259 : frontier 9 ⟨687259, by decide⟩
    (prefixCache 12 91403) (prefixPartial 12 91403) = false := by
  decide +kernel

theorem node_context_12_91403_687259 : EJMOriginalGlobalDAGData.nodes 9 ⟨687259, by decide⟩ =
    .split (coordinate 12) (![⟨687129, by decide⟩,⟨687187, by decide⟩,⟨687246, by decide⟩,⟨687258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91403_687259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91403 ⟨687259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91403
    ⟨687259, by decide⟩ (by decide) (![⟨687129, by decide⟩,⟨687187, by decide⟩,⟨687246, by decide⟩,⟨687258, by decide⟩]) unmarked_context_12_91403_687259 node_context_12_91403_687259
  intro a
  fin_cases a
  · exact context_13_365612_687129
  · exact context_13_365613_687187
  · exact context_13_365614_687246
  · exact context_13_365615_687258

theorem unmarked_context_11_22850_687260 : frontier 10 ⟨687260, by decide⟩
    (prefixCache 11 22850) (prefixPartial 11 22850) = false := by
  decide +kernel

theorem node_context_11_22850_687260 : EJMOriginalGlobalDAGData.nodes 10 ⟨687260, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨686854, by decide⟩,⟨687052, by decide⟩,⟨687259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22850_687260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22850 ⟨687260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22850
    ⟨687260, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨686854, by decide⟩,⟨687052, by decide⟩,⟨687259, by decide⟩]) unmarked_context_11_22850_687260 node_context_11_22850_687260
  intro a
  fin_cases a
  · exact context_12_91400_448748
  · exact context_12_91401_686854
  · exact context_12_91402_687052
  · exact context_12_91403_687259

theorem selected_cut_27153 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91404) = some ⟨12, 1, 0, 448748, 91404, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91404_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91404 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91404 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91404, 1, 65536⟩
    (by decide) selected_cut_27153

theorem selected_cut_27154 : selected 8 ⟨687296, by decide⟩
    (prefixPartial 13 365620) = some ⟨13, 2, 0, 687296, 365620, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_365620_687296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365620 ⟨687296, by decide⟩ :=
  accepted_of_selected 13 365620 ⟨687296, by decide⟩ ⟨13, 2, 0, 687296, 365620, 1593, 16384⟩
    (by decide) selected_cut_27154

theorem selected_cut_27155 : selected 8 ⟨687325, by decide⟩
    (prefixPartial 13 365621) = some ⟨13, 2, 0, 687325, 365621, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_365621_687325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365621 ⟨687325, by decide⟩ :=
  accepted_of_selected 13 365621 ⟨687325, by decide⟩ ⟨13, 2, 0, 687325, 365621, 1273, 16384⟩
    (by decide) selected_cut_27155

theorem selected_cut_27156 : selected 8 ⟨687361, by decide⟩
    (prefixPartial 13 365622) = some ⟨13, 2, 0, 687361, 365622, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_365622_687361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365622 ⟨687361, by decide⟩ :=
  accepted_of_selected 13 365622 ⟨687361, by decide⟩ ⟨13, 2, 0, 687361, 365622, 1669, 16384⟩
    (by decide) selected_cut_27156

theorem selected_cut_27157 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 365623) = some ⟨13, 1, 0, 265883, 365623, 1, 16384⟩ := by
  decide +kernel

theorem context_13_365623_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365623 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 365623 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 365623, 1, 16384⟩
    (by decide) selected_cut_27157

theorem unmarked_context_12_91405_687362 : frontier 9 ⟨687362, by decide⟩
    (prefixCache 12 91405) (prefixPartial 12 91405) = false := by
  decide +kernel

theorem node_context_12_91405_687362 : EJMOriginalGlobalDAGData.nodes 9 ⟨687362, by decide⟩ =
    .split (coordinate 12) (![⟨687296, by decide⟩,⟨687325, by decide⟩,⟨687361, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91405_687362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91405 ⟨687362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91405
    ⟨687362, by decide⟩ (by decide) (![⟨687296, by decide⟩,⟨687325, by decide⟩,⟨687361, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_91405_687362 node_context_12_91405_687362
  intro a
  fin_cases a
  · exact context_13_365620_687296
  · exact context_13_365621_687325
  · exact context_13_365622_687361
  · exact context_13_365623_265883

theorem selected_cut_27158 : selected 8 ⟨687421, by decide⟩
    (prefixPartial 13 365624) = some ⟨13, 2, 0, 687421, 365624, 3425, 16384⟩ := by
  decide +kernel

theorem context_13_365624_687421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365624 ⟨687421, by decide⟩ :=
  accepted_of_selected 13 365624 ⟨687421, by decide⟩ ⟨13, 2, 0, 687421, 365624, 3425, 16384⟩
    (by decide) selected_cut_27158

theorem selected_cut_27159 : selected 8 ⟨687461, by decide⟩
    (prefixPartial 13 365625) = some ⟨13, 2, 0, 687461, 365625, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_365625_687461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365625 ⟨687461, by decide⟩ :=
  accepted_of_selected 13 365625 ⟨687461, by decide⟩ ⟨13, 2, 0, 687461, 365625, 2609, 16384⟩
    (by decide) selected_cut_27159

theorem selected_cut_27160 : selected 8 ⟨687490, by decide⟩
    (prefixPartial 13 365626) = some ⟨13, 2, 0, 687490, 365626, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_365626_687490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365626 ⟨687490, by decide⟩ :=
  accepted_of_selected 13 365626 ⟨687490, by decide⟩ ⟨13, 2, 0, 687490, 365626, 2081, 16384⟩
    (by decide) selected_cut_27160

theorem selected_cut_27161 : selected 8 ⟨687521, by decide⟩
    (prefixPartial 13 365627) = some ⟨13, 2, 0, 687521, 365627, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_365627_687521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365627 ⟨687521, by decide⟩ :=
  accepted_of_selected 13 365627 ⟨687521, by decide⟩ ⟨13, 2, 0, 687521, 365627, 1245, 16384⟩
    (by decide) selected_cut_27161

theorem unmarked_context_12_91406_687522 : frontier 9 ⟨687522, by decide⟩
    (prefixCache 12 91406) (prefixPartial 12 91406) = false := by
  decide +kernel

theorem node_context_12_91406_687522 : EJMOriginalGlobalDAGData.nodes 9 ⟨687522, by decide⟩ =
    .split (coordinate 12) (![⟨687421, by decide⟩,⟨687461, by decide⟩,⟨687490, by decide⟩,⟨687521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91406_687522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91406 ⟨687522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91406
    ⟨687522, by decide⟩ (by decide) (![⟨687421, by decide⟩,⟨687461, by decide⟩,⟨687490, by decide⟩,⟨687521, by decide⟩]) unmarked_context_12_91406_687522 node_context_12_91406_687522
  intro a
  fin_cases a
  · exact context_13_365624_687421
  · exact context_13_365625_687461
  · exact context_13_365626_687490
  · exact context_13_365627_687521

theorem selected_cut_27162 : selected 8 ⟨687577, by decide⟩
    (prefixPartial 13 365628) = some ⟨13, 2, 0, 687577, 365628, 3553, 16384⟩ := by
  decide +kernel

theorem context_13_365628_687577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365628 ⟨687577, by decide⟩ :=
  accepted_of_selected 13 365628 ⟨687577, by decide⟩ ⟨13, 2, 0, 687577, 365628, 3553, 16384⟩
    (by decide) selected_cut_27162

theorem selected_cut_27163 : selected 8 ⟨687618, by decide⟩
    (prefixPartial 13 365629) = some ⟨13, 2, 0, 687618, 365629, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_365629_687618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365629 ⟨687618, by decide⟩ :=
  accepted_of_selected 13 365629 ⟨687618, by decide⟩ ⟨13, 2, 0, 687618, 365629, 2781, 16384⟩
    (by decide) selected_cut_27163

theorem selected_cut_27164 : selected 8 ⟨687659, by decide⟩
    (prefixPartial 13 365630) = some ⟨13, 2, 0, 687659, 365630, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_365630_687659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365630 ⟨687659, by decide⟩ :=
  accepted_of_selected 13 365630 ⟨687659, by decide⟩ ⟨13, 2, 0, 687659, 365630, 2369, 16384⟩
    (by decide) selected_cut_27164

theorem selected_cut_27165 : selected 8 ⟨687669, by decide⟩
    (prefixPartial 13 365631) = some ⟨13, 2, 0, 687669, 365631, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_365631_687669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365631 ⟨687669, by decide⟩ :=
  accepted_of_selected 13 365631 ⟨687669, by decide⟩ ⟨13, 2, 0, 687669, 365631, 1113, 16384⟩
    (by decide) selected_cut_27165

theorem unmarked_context_12_91407_687670 : frontier 9 ⟨687670, by decide⟩
    (prefixCache 12 91407) (prefixPartial 12 91407) = false := by
  decide +kernel

theorem node_context_12_91407_687670 : EJMOriginalGlobalDAGData.nodes 9 ⟨687670, by decide⟩ =
    .split (coordinate 12) (![⟨687577, by decide⟩,⟨687618, by decide⟩,⟨687659, by decide⟩,⟨687669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91407_687670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91407 ⟨687670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91407
    ⟨687670, by decide⟩ (by decide) (![⟨687577, by decide⟩,⟨687618, by decide⟩,⟨687659, by decide⟩,⟨687669, by decide⟩]) unmarked_context_12_91407_687670 node_context_12_91407_687670
  intro a
  fin_cases a
  · exact context_13_365628_687577
  · exact context_13_365629_687618
  · exact context_13_365630_687659
  · exact context_13_365631_687669

theorem unmarked_context_11_22851_687671 : frontier 10 ⟨687671, by decide⟩
    (prefixCache 11 22851) (prefixPartial 11 22851) = false := by
  decide +kernel

theorem node_context_11_22851_687671 : EJMOriginalGlobalDAGData.nodes 10 ⟨687671, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨687362, by decide⟩,⟨687522, by decide⟩,⟨687670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22851_687671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22851 ⟨687671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22851
    ⟨687671, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨687362, by decide⟩,⟨687522, by decide⟩,⟨687670, by decide⟩]) unmarked_context_11_22851_687671 node_context_11_22851_687671
  intro a
  fin_cases a
  · exact context_12_91404_448748
  · exact context_12_91405_687362
  · exact context_12_91406_687522
  · exact context_12_91407_687670

theorem unmarked_context_10_5712_687672 : frontier 11 ⟨687672, by decide⟩
    (prefixCache 10 5712) (prefixPartial 10 5712) = false := by
  decide +kernel

theorem node_context_10_5712_687672 : EJMOriginalGlobalDAGData.nodes 11 ⟨687672, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨686622, by decide⟩,⟨687260, by decide⟩,⟨687671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5712_687672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5712 ⟨687672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5712
    ⟨687672, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨686622, by decide⟩,⟨687260, by decide⟩,⟨687671, by decide⟩]) unmarked_context_10_5712_687672 node_context_10_5712_687672
  intro a
  fin_cases a
  · exact context_11_22848_434745
  · exact context_11_22849_686622
  · exact context_11_22850_687260
  · exact context_11_22851_687671

theorem selected_cut_27166 : selected 8 ⟨687697, by decide⟩
    (prefixPartial 13 365632) = some ⟨13, 2, 0, 687697, 365632, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_365632_687697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365632 ⟨687697, by decide⟩ :=
  accepted_of_selected 13 365632 ⟨687697, by decide⟩ ⟨13, 2, 0, 687697, 365632, 1349, 16384⟩
    (by decide) selected_cut_27166

theorem selected_cut_27167 : selected 8 ⟨687717, by decide⟩
    (prefixPartial 13 365633) = some ⟨13, 2, 0, 687717, 365633, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_365633_687717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365633 ⟨687717, by decide⟩ :=
  accepted_of_selected 13 365633 ⟨687717, by decide⟩ ⟨13, 2, 0, 687717, 365633, 1001, 16384⟩
    (by decide) selected_cut_27167

theorem selected_cut_27168 : selected 8 ⟨687737, by decide⟩
    (prefixPartial 13 365634) = some ⟨13, 2, 0, 687737, 365634, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_365634_687737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365634 ⟨687737, by decide⟩ :=
  accepted_of_selected 13 365634 ⟨687737, by decide⟩ ⟨13, 2, 0, 687737, 365634, 1321, 16384⟩
    (by decide) selected_cut_27168

theorem selected_cut_27169 : selected 8 ⟨687745, by decide⟩
    (prefixPartial 13 365635) = some ⟨13, 2, 0, 687745, 365635, 753, 16384⟩ := by
  decide +kernel

theorem context_13_365635_687745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365635 ⟨687745, by decide⟩ :=
  accepted_of_selected 13 365635 ⟨687745, by decide⟩ ⟨13, 2, 0, 687745, 365635, 753, 16384⟩
    (by decide) selected_cut_27169

theorem unmarked_context_12_91408_687746 : frontier 9 ⟨687746, by decide⟩
    (prefixCache 12 91408) (prefixPartial 12 91408) = false := by
  decide +kernel

theorem node_context_12_91408_687746 : EJMOriginalGlobalDAGData.nodes 9 ⟨687746, by decide⟩ =
    .split (coordinate 12) (![⟨687697, by decide⟩,⟨687717, by decide⟩,⟨687737, by decide⟩,⟨687745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91408_687746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91408 ⟨687746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91408
    ⟨687746, by decide⟩ (by decide) (![⟨687697, by decide⟩,⟨687717, by decide⟩,⟨687737, by decide⟩,⟨687745, by decide⟩]) unmarked_context_12_91408_687746 node_context_12_91408_687746
  intro a
  fin_cases a
  · exact context_13_365632_687697
  · exact context_13_365633_687717
  · exact context_13_365634_687737
  · exact context_13_365635_687745

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
