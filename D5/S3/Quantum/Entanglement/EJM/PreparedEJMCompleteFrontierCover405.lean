/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover404
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38883 : selected 9 ⟨417109, by decide⟩
    (prefixPartial 12 302181) = some ⟨12, 1, 0, 417109, 302181, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302181_417109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302181 ⟨417109, by decide⟩ :=
  accepted_of_selected 12 302181 ⟨417109, by decide⟩ ⟨12, 1, 0, 417109, 302181, 1, 65536⟩
    (by decide) selected_cut_38883

theorem selected_cut_38884 : selected 9 ⟨1052462, by decide⟩
    (prefixPartial 12 302182) = some ⟨12, 2, 0, 1052462, 302182, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_302182_1052462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302182 ⟨1052462, by decide⟩ :=
  accepted_of_selected 12 302182 ⟨1052462, by decide⟩ ⟨12, 2, 0, 1052462, 302182, 1865, 65536⟩
    (by decide) selected_cut_38884

theorem selected_cut_38885 : selected 9 ⟨1052485, by decide⟩
    (prefixPartial 12 302183) = some ⟨12, 2, 0, 1052485, 302183, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_302183_1052485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302183 ⟨1052485, by decide⟩ :=
  accepted_of_selected 12 302183 ⟨1052485, by decide⟩ ⟨12, 2, 0, 1052485, 302183, 1865, 65536⟩
    (by decide) selected_cut_38885

theorem unmarked_context_11_75545_1052486 : frontier 10 ⟨1052486, by decide⟩
    (prefixCache 11 75545) (prefixPartial 11 75545) = false := by
  decide +kernel

theorem node_context_11_75545_1052486 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052486, by decide⟩ =
    .split (coordinate 11) (![⟨1052439, by decide⟩,⟨417109, by decide⟩,⟨1052462, by decide⟩,⟨1052485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75545_1052486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75545 ⟨1052486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75545
    ⟨1052486, by decide⟩ (by decide) (![⟨1052439, by decide⟩,⟨417109, by decide⟩,⟨1052462, by decide⟩,⟨1052485, by decide⟩]) unmarked_context_11_75545_1052486 node_context_11_75545_1052486
  intro a
  fin_cases a
  · exact context_12_302180_1052439
  · exact context_12_302181_417109
  · exact context_12_302182_1052462
  · exact context_12_302183_1052485

theorem selected_cut_38886 : selected 9 ⟨1052513, by decide⟩
    (prefixPartial 12 302184) = some ⟨12, 2, 0, 1052513, 302184, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_302184_1052513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302184 ⟨1052513, by decide⟩ :=
  accepted_of_selected 12 302184 ⟨1052513, by decide⟩ ⟨12, 2, 0, 1052513, 302184, 1877, 65536⟩
    (by decide) selected_cut_38886

theorem selected_cut_38887 : selected 9 ⟨1052545, by decide⟩
    (prefixPartial 12 302185) = some ⟨12, 2, 0, 1052545, 302185, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_302185_1052545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302185 ⟨1052545, by decide⟩ :=
  accepted_of_selected 12 302185 ⟨1052545, by decide⟩ ⟨12, 2, 0, 1052545, 302185, 1977, 65536⟩
    (by decide) selected_cut_38887

theorem selected_cut_38888 : selected 9 ⟨1052573, by decide⟩
    (prefixPartial 12 302186) = some ⟨12, 2, 0, 1052573, 302186, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_302186_1052573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302186 ⟨1052573, by decide⟩ :=
  accepted_of_selected 12 302186 ⟨1052573, by decide⟩ ⟨12, 2, 0, 1052573, 302186, 1833, 65536⟩
    (by decide) selected_cut_38888

theorem selected_cut_38889 : selected 9 ⟨1052610, by decide⟩
    (prefixPartial 12 302187) = some ⟨12, 2, 0, 1052610, 302187, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_302187_1052610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302187 ⟨1052610, by decide⟩ :=
  accepted_of_selected 12 302187 ⟨1052610, by decide⟩ ⟨12, 2, 0, 1052610, 302187, 2061, 65536⟩
    (by decide) selected_cut_38889

theorem unmarked_context_11_75546_1052611 : frontier 10 ⟨1052611, by decide⟩
    (prefixCache 11 75546) (prefixPartial 11 75546) = false := by
  decide +kernel

theorem node_context_11_75546_1052611 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052611, by decide⟩ =
    .split (coordinate 11) (![⟨1052513, by decide⟩,⟨1052545, by decide⟩,⟨1052573, by decide⟩,⟨1052610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75546_1052611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75546 ⟨1052611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75546
    ⟨1052611, by decide⟩ (by decide) (![⟨1052513, by decide⟩,⟨1052545, by decide⟩,⟨1052573, by decide⟩,⟨1052610, by decide⟩]) unmarked_context_11_75546_1052611 node_context_11_75546_1052611
  intro a
  fin_cases a
  · exact context_12_302184_1052513
  · exact context_12_302185_1052545
  · exact context_12_302186_1052573
  · exact context_12_302187_1052610

theorem selected_cut_38890 : selected 9 ⟨1052628, by decide⟩
    (prefixPartial 12 302188) = some ⟨12, 2, 0, 1052628, 302188, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_302188_1052628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302188 ⟨1052628, by decide⟩ :=
  accepted_of_selected 12 302188 ⟨1052628, by decide⟩ ⟨12, 2, 0, 1052628, 302188, 1629, 65536⟩
    (by decide) selected_cut_38890

theorem selected_cut_38891 : selected 9 ⟨1052658, by decide⟩
    (prefixPartial 12 302189) = some ⟨12, 2, 0, 1052658, 302189, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_302189_1052658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302189 ⟨1052658, by decide⟩ :=
  accepted_of_selected 12 302189 ⟨1052658, by decide⟩ ⟨12, 2, 0, 1052658, 302189, 1817, 65536⟩
    (by decide) selected_cut_38891

theorem selected_cut_38892 : selected 9 ⟨1052685, by decide⟩
    (prefixPartial 12 302190) = some ⟨12, 2, 0, 1052685, 302190, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_302190_1052685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302190 ⟨1052685, by decide⟩ :=
  accepted_of_selected 12 302190 ⟨1052685, by decide⟩ ⟨12, 2, 0, 1052685, 302190, 1773, 65536⟩
    (by decide) selected_cut_38892

theorem selected_cut_38893 : selected 9 ⟨1052711, by decide⟩
    (prefixPartial 12 302191) = some ⟨12, 2, 0, 1052711, 302191, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_302191_1052711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302191 ⟨1052711, by decide⟩ :=
  accepted_of_selected 12 302191 ⟨1052711, by decide⟩ ⟨12, 2, 0, 1052711, 302191, 1645, 65536⟩
    (by decide) selected_cut_38893

theorem unmarked_context_11_75547_1052712 : frontier 10 ⟨1052712, by decide⟩
    (prefixCache 11 75547) (prefixPartial 11 75547) = false := by
  decide +kernel

theorem node_context_11_75547_1052712 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052712, by decide⟩ =
    .split (coordinate 11) (![⟨1052628, by decide⟩,⟨1052658, by decide⟩,⟨1052685, by decide⟩,⟨1052711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75547_1052712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75547 ⟨1052712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75547
    ⟨1052712, by decide⟩ (by decide) (![⟨1052628, by decide⟩,⟨1052658, by decide⟩,⟨1052685, by decide⟩,⟨1052711, by decide⟩]) unmarked_context_11_75547_1052712 node_context_11_75547_1052712
  intro a
  fin_cases a
  · exact context_12_302188_1052628
  · exact context_12_302189_1052658
  · exact context_12_302190_1052685
  · exact context_12_302191_1052711

theorem unmarked_context_10_18886_1052713 : frontier 11 ⟨1052713, by decide⟩
    (prefixCache 10 18886) (prefixPartial 10 18886) = false := by
  decide +kernel

theorem node_context_10_18886_1052713 : EJMOriginalGlobalDAGData.nodes 11 ⟨1052713, by decide⟩ =
    .split (coordinate 10) (![⟨1052413, by decide⟩,⟨1052486, by decide⟩,⟨1052611, by decide⟩,⟨1052712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18886_1052713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18886 ⟨1052713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18886
    ⟨1052713, by decide⟩ (by decide) (![⟨1052413, by decide⟩,⟨1052486, by decide⟩,⟨1052611, by decide⟩,⟨1052712, by decide⟩]) unmarked_context_10_18886_1052713 node_context_10_18886_1052713
  intro a
  fin_cases a
  · exact context_11_75544_1052413
  · exact context_11_75545_1052486
  · exact context_11_75546_1052611
  · exact context_11_75547_1052712

theorem selected_cut_38894 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 302192) = some ⟨12, 1, 0, 985390, 302192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302192_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302192 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 302192 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 302192, 1, 65536⟩
    (by decide) selected_cut_38894

theorem selected_cut_38895 : selected 9 ⟨1052737, by decide⟩
    (prefixPartial 12 302193) = some ⟨12, 2, 0, 1052737, 302193, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_302193_1052737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302193 ⟨1052737, by decide⟩ :=
  accepted_of_selected 12 302193 ⟨1052737, by decide⟩ ⟨12, 2, 0, 1052737, 302193, 1613, 65536⟩
    (by decide) selected_cut_38895

theorem selected_cut_38896 : selected 9 ⟨1052759, by decide⟩
    (prefixPartial 12 302194) = some ⟨12, 2, 0, 1052759, 302194, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_302194_1052759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302194 ⟨1052759, by decide⟩ :=
  accepted_of_selected 12 302194 ⟨1052759, by decide⟩ ⟨12, 2, 0, 1052759, 302194, 1325, 65536⟩
    (by decide) selected_cut_38896

theorem selected_cut_38897 : selected 9 ⟨1052779, by decide⟩
    (prefixPartial 12 302195) = some ⟨12, 2, 0, 1052779, 302195, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_302195_1052779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302195 ⟨1052779, by decide⟩ :=
  accepted_of_selected 12 302195 ⟨1052779, by decide⟩ ⟨12, 2, 0, 1052779, 302195, 1385, 65536⟩
    (by decide) selected_cut_38897

theorem unmarked_context_11_75548_1052780 : frontier 10 ⟨1052780, by decide⟩
    (prefixCache 11 75548) (prefixPartial 11 75548) = false := by
  decide +kernel

theorem node_context_11_75548_1052780 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052780, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1052737, by decide⟩,⟨1052759, by decide⟩,⟨1052779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75548_1052780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75548 ⟨1052780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75548
    ⟨1052780, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1052737, by decide⟩,⟨1052759, by decide⟩,⟨1052779, by decide⟩]) unmarked_context_11_75548_1052780 node_context_11_75548_1052780
  intro a
  fin_cases a
  · exact context_12_302192_985390
  · exact context_12_302193_1052737
  · exact context_12_302194_1052759
  · exact context_12_302195_1052779

theorem selected_cut_38898 : selected 9 ⟨1052804, by decide⟩
    (prefixPartial 12 302196) = some ⟨12, 2, 0, 1052804, 302196, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_302196_1052804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302196 ⟨1052804, by decide⟩ :=
  accepted_of_selected 12 302196 ⟨1052804, by decide⟩ ⟨12, 2, 0, 1052804, 302196, 1577, 65536⟩
    (by decide) selected_cut_38898

theorem selected_cut_38899 : selected 9 ⟨1052834, by decide⟩
    (prefixPartial 12 302197) = some ⟨12, 2, 0, 1052834, 302197, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_302197_1052834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302197 ⟨1052834, by decide⟩ :=
  accepted_of_selected 12 302197 ⟨1052834, by decide⟩ ⟨12, 2, 0, 1052834, 302197, 1677, 65536⟩
    (by decide) selected_cut_38899

theorem selected_cut_38900 : selected 9 ⟨1052856, by decide⟩
    (prefixPartial 12 302198) = some ⟨12, 2, 0, 1052856, 302198, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_302198_1052856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302198 ⟨1052856, by decide⟩ :=
  accepted_of_selected 12 302198 ⟨1052856, by decide⟩ ⟨12, 2, 0, 1052856, 302198, 1493, 65536⟩
    (by decide) selected_cut_38900

theorem selected_cut_38901 : selected 9 ⟨1052879, by decide⟩
    (prefixPartial 12 302199) = some ⟨12, 2, 0, 1052879, 302199, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_302199_1052879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302199 ⟨1052879, by decide⟩ :=
  accepted_of_selected 12 302199 ⟨1052879, by decide⟩ ⟨12, 2, 0, 1052879, 302199, 1549, 65536⟩
    (by decide) selected_cut_38901

theorem unmarked_context_11_75549_1052880 : frontier 10 ⟨1052880, by decide⟩
    (prefixCache 11 75549) (prefixPartial 11 75549) = false := by
  decide +kernel

theorem node_context_11_75549_1052880 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052880, by decide⟩ =
    .split (coordinate 11) (![⟨1052804, by decide⟩,⟨1052834, by decide⟩,⟨1052856, by decide⟩,⟨1052879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75549_1052880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75549 ⟨1052880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75549
    ⟨1052880, by decide⟩ (by decide) (![⟨1052804, by decide⟩,⟨1052834, by decide⟩,⟨1052856, by decide⟩,⟨1052879, by decide⟩]) unmarked_context_11_75549_1052880 node_context_11_75549_1052880
  intro a
  fin_cases a
  · exact context_12_302196_1052804
  · exact context_12_302197_1052834
  · exact context_12_302198_1052856
  · exact context_12_302199_1052879

theorem selected_cut_38902 : selected 9 ⟨1052899, by decide⟩
    (prefixPartial 12 302200) = some ⟨12, 2, 0, 1052899, 302200, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_302200_1052899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302200 ⟨1052899, by decide⟩ :=
  accepted_of_selected 12 302200 ⟨1052899, by decide⟩ ⟨12, 2, 0, 1052899, 302200, 1453, 65536⟩
    (by decide) selected_cut_38902

theorem selected_cut_38903 : selected 9 ⟨1052923, by decide⟩
    (prefixPartial 12 302201) = some ⟨12, 2, 0, 1052923, 302201, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_302201_1052923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302201 ⟨1052923, by decide⟩ :=
  accepted_of_selected 12 302201 ⟨1052923, by decide⟩ ⟨12, 2, 0, 1052923, 302201, 1605, 65536⟩
    (by decide) selected_cut_38903

theorem selected_cut_38904 : selected 9 ⟨1052946, by decide⟩
    (prefixPartial 12 302202) = some ⟨12, 2, 0, 1052946, 302202, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_302202_1052946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302202 ⟨1052946, by decide⟩ :=
  accepted_of_selected 12 302202 ⟨1052946, by decide⟩ ⟨12, 2, 0, 1052946, 302202, 1405, 65536⟩
    (by decide) selected_cut_38904

theorem selected_cut_38905 : selected 9 ⟨1052975, by decide⟩
    (prefixPartial 12 302203) = some ⟨12, 2, 0, 1052975, 302203, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_302203_1052975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302203 ⟨1052975, by decide⟩ :=
  accepted_of_selected 12 302203 ⟨1052975, by decide⟩ ⟨12, 2, 0, 1052975, 302203, 1609, 65536⟩
    (by decide) selected_cut_38905

theorem unmarked_context_11_75550_1052976 : frontier 10 ⟨1052976, by decide⟩
    (prefixCache 11 75550) (prefixPartial 11 75550) = false := by
  decide +kernel

theorem node_context_11_75550_1052976 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052976, by decide⟩ =
    .split (coordinate 11) (![⟨1052899, by decide⟩,⟨1052923, by decide⟩,⟨1052946, by decide⟩,⟨1052975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75550_1052976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75550 ⟨1052976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75550
    ⟨1052976, by decide⟩ (by decide) (![⟨1052899, by decide⟩,⟨1052923, by decide⟩,⟨1052946, by decide⟩,⟨1052975, by decide⟩]) unmarked_context_11_75550_1052976 node_context_11_75550_1052976
  intro a
  fin_cases a
  · exact context_12_302200_1052899
  · exact context_12_302201_1052923
  · exact context_12_302202_1052946
  · exact context_12_302203_1052975

theorem selected_cut_38906 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75551) = some ⟨11, 1, 0, 977886, 75551, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75551_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75551 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75551 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75551, 1, 262144⟩
    (by decide) selected_cut_38906

theorem unmarked_context_10_18887_1052977 : frontier 11 ⟨1052977, by decide⟩
    (prefixCache 10 18887) (prefixPartial 10 18887) = false := by
  decide +kernel

theorem node_context_10_18887_1052977 : EJMOriginalGlobalDAGData.nodes 11 ⟨1052977, by decide⟩ =
    .split (coordinate 10) (![⟨1052780, by decide⟩,⟨1052880, by decide⟩,⟨1052976, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18887_1052977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18887 ⟨1052977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18887
    ⟨1052977, by decide⟩ (by decide) (![⟨1052780, by decide⟩,⟨1052880, by decide⟩,⟨1052976, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18887_1052977 node_context_10_18887_1052977
  intro a
  fin_cases a
  · exact context_11_75548_1052780
  · exact context_11_75549_1052880
  · exact context_11_75550_1052976
  · exact context_11_75551_977886

theorem unmarked_context_9_4721_1052978 : frontier 12 ⟨1052978, by decide⟩
    (prefixCache 9 4721) (prefixPartial 9 4721) = false := by
  decide +kernel

theorem node_context_9_4721_1052978 : EJMOriginalGlobalDAGData.nodes 12 ⟨1052978, by decide⟩ =
    .split (coordinate 9) (![⟨1052329, by decide⟩,⟨893098, by decide⟩,⟨1052713, by decide⟩,⟨1052977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4721_1052978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4721 ⟨1052978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4721
    ⟨1052978, by decide⟩ (by decide) (![⟨1052329, by decide⟩,⟨893098, by decide⟩,⟨1052713, by decide⟩,⟨1052977, by decide⟩]) unmarked_context_9_4721_1052978 node_context_9_4721_1052978
  intro a
  fin_cases a
  · exact context_10_18884_1052329
  · exact context_10_18885_893098
  · exact context_10_18886_1052713
  · exact context_10_18887_1052977

theorem selected_cut_38907 : selected 10 ⟨1053033, by decide⟩
    (prefixPartial 11 75552) = some ⟨11, 2, 0, 1053033, 75552, 2781, 262144⟩ := by
  decide +kernel

theorem context_11_75552_1053033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75552 ⟨1053033, by decide⟩ :=
  accepted_of_selected 11 75552 ⟨1053033, by decide⟩ ⟨11, 2, 0, 1053033, 75552, 2781, 262144⟩
    (by decide) selected_cut_38907

theorem selected_cut_38908 : selected 9 ⟨1053068, by decide⟩
    (prefixPartial 12 302212) = some ⟨12, 2, 0, 1053068, 302212, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_302212_1053068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302212 ⟨1053068, by decide⟩ :=
  accepted_of_selected 12 302212 ⟨1053068, by decide⟩ ⟨12, 2, 0, 1053068, 302212, 1585, 65536⟩
    (by decide) selected_cut_38908

theorem selected_cut_38909 : selected 9 ⟨1053097, by decide⟩
    (prefixPartial 12 302213) = some ⟨12, 2, 0, 1053097, 302213, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_302213_1053097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302213 ⟨1053097, by decide⟩ :=
  accepted_of_selected 12 302213 ⟨1053097, by decide⟩ ⟨12, 2, 0, 1053097, 302213, 1501, 65536⟩
    (by decide) selected_cut_38909

theorem selected_cut_38910 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302214) = some ⟨12, 1, 0, 984676, 302214, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302214_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302214 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302214 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302214, 1, 65536⟩
    (by decide) selected_cut_38910

theorem selected_cut_38911 : selected 9 ⟨1053125, by decide⟩
    (prefixPartial 12 302215) = some ⟨12, 2, 0, 1053125, 302215, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_302215_1053125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302215 ⟨1053125, by decide⟩ :=
  accepted_of_selected 12 302215 ⟨1053125, by decide⟩ ⟨12, 2, 0, 1053125, 302215, 1533, 65536⟩
    (by decide) selected_cut_38911

theorem unmarked_context_11_75553_1053126 : frontier 10 ⟨1053126, by decide⟩
    (prefixCache 11 75553) (prefixPartial 11 75553) = false := by
  decide +kernel

theorem node_context_11_75553_1053126 : EJMOriginalGlobalDAGData.nodes 10 ⟨1053126, by decide⟩ =
    .split (coordinate 11) (![⟨1053068, by decide⟩,⟨1053097, by decide⟩,⟨984676, by decide⟩,⟨1053125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75553_1053126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75553 ⟨1053126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75553
    ⟨1053126, by decide⟩ (by decide) (![⟨1053068, by decide⟩,⟨1053097, by decide⟩,⟨984676, by decide⟩,⟨1053125, by decide⟩]) unmarked_context_11_75553_1053126 node_context_11_75553_1053126
  intro a
  fin_cases a
  · exact context_12_302212_1053068
  · exact context_12_302213_1053097
  · exact context_12_302214_984676
  · exact context_12_302215_1053125

theorem selected_cut_38912 : selected 9 ⟨1053157, by decide⟩
    (prefixPartial 12 302216) = some ⟨12, 2, 0, 1053157, 302216, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_302216_1053157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302216 ⟨1053157, by decide⟩ :=
  accepted_of_selected 12 302216 ⟨1053157, by decide⟩ ⟨12, 2, 0, 1053157, 302216, 1513, 65536⟩
    (by decide) selected_cut_38912

theorem selected_cut_38913 : selected 9 ⟨1053186, by decide⟩
    (prefixPartial 12 302217) = some ⟨12, 2, 0, 1053186, 302217, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_302217_1053186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302217 ⟨1053186, by decide⟩ :=
  accepted_of_selected 12 302217 ⟨1053186, by decide⟩ ⟨12, 2, 0, 1053186, 302217, 1629, 65536⟩
    (by decide) selected_cut_38913

theorem selected_cut_38914 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302218) = some ⟨12, 1, 0, 984676, 302218, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302218_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302218 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302218 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302218, 1, 65536⟩
    (by decide) selected_cut_38914

theorem selected_cut_38915 : selected 9 ⟨1053220, by decide⟩
    (prefixPartial 12 302219) = some ⟨12, 2, 0, 1053220, 302219, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_302219_1053220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302219 ⟨1053220, by decide⟩ :=
  accepted_of_selected 12 302219 ⟨1053220, by decide⟩ ⟨12, 2, 0, 1053220, 302219, 1737, 65536⟩
    (by decide) selected_cut_38915

theorem unmarked_context_11_75554_1053221 : frontier 10 ⟨1053221, by decide⟩
    (prefixCache 11 75554) (prefixPartial 11 75554) = false := by
  decide +kernel

theorem node_context_11_75554_1053221 : EJMOriginalGlobalDAGData.nodes 10 ⟨1053221, by decide⟩ =
    .split (coordinate 11) (![⟨1053157, by decide⟩,⟨1053186, by decide⟩,⟨984676, by decide⟩,⟨1053220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75554_1053221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75554 ⟨1053221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75554
    ⟨1053221, by decide⟩ (by decide) (![⟨1053157, by decide⟩,⟨1053186, by decide⟩,⟨984676, by decide⟩,⟨1053220, by decide⟩]) unmarked_context_11_75554_1053221 node_context_11_75554_1053221
  intro a
  fin_cases a
  · exact context_12_302216_1053157
  · exact context_12_302217_1053186
  · exact context_12_302218_984676
  · exact context_12_302219_1053220

theorem selected_cut_38916 : selected 9 ⟨1053242, by decide⟩
    (prefixPartial 12 302220) = some ⟨12, 2, 0, 1053242, 302220, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_302220_1053242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302220 ⟨1053242, by decide⟩ :=
  accepted_of_selected 12 302220 ⟨1053242, by decide⟩ ⟨12, 2, 0, 1053242, 302220, 1333, 65536⟩
    (by decide) selected_cut_38916

theorem selected_cut_38917 : selected 9 ⟨1053265, by decide⟩
    (prefixPartial 12 302221) = some ⟨12, 2, 0, 1053265, 302221, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_302221_1053265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302221 ⟨1053265, by decide⟩ :=
  accepted_of_selected 12 302221 ⟨1053265, by decide⟩ ⟨12, 2, 0, 1053265, 302221, 1433, 65536⟩
    (by decide) selected_cut_38917

theorem selected_cut_38918 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302222) = some ⟨12, 1, 0, 984676, 302222, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302222_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302222 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302222 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302222, 1, 65536⟩
    (by decide) selected_cut_38918

theorem selected_cut_38919 : selected 9 ⟨1053294, by decide⟩
    (prefixPartial 12 302223) = some ⟨12, 2, 0, 1053294, 302223, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_302223_1053294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302223 ⟨1053294, by decide⟩ :=
  accepted_of_selected 12 302223 ⟨1053294, by decide⟩ ⟨12, 2, 0, 1053294, 302223, 1425, 65536⟩
    (by decide) selected_cut_38919

theorem unmarked_context_11_75555_1053295 : frontier 10 ⟨1053295, by decide⟩
    (prefixCache 11 75555) (prefixPartial 11 75555) = false := by
  decide +kernel

theorem node_context_11_75555_1053295 : EJMOriginalGlobalDAGData.nodes 10 ⟨1053295, by decide⟩ =
    .split (coordinate 11) (![⟨1053242, by decide⟩,⟨1053265, by decide⟩,⟨984676, by decide⟩,⟨1053294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75555_1053295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75555 ⟨1053295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75555
    ⟨1053295, by decide⟩ (by decide) (![⟨1053242, by decide⟩,⟨1053265, by decide⟩,⟨984676, by decide⟩,⟨1053294, by decide⟩]) unmarked_context_11_75555_1053295 node_context_11_75555_1053295
  intro a
  fin_cases a
  · exact context_12_302220_1053242
  · exact context_12_302221_1053265
  · exact context_12_302222_984676
  · exact context_12_302223_1053294

theorem unmarked_context_10_18888_1053296 : frontier 11 ⟨1053296, by decide⟩
    (prefixCache 10 18888) (prefixPartial 10 18888) = false := by
  decide +kernel

theorem node_context_10_18888_1053296 : EJMOriginalGlobalDAGData.nodes 11 ⟨1053296, by decide⟩ =
    .split (coordinate 10) (![⟨1053033, by decide⟩,⟨1053126, by decide⟩,⟨1053221, by decide⟩,⟨1053295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18888_1053296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18888 ⟨1053296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18888
    ⟨1053296, by decide⟩ (by decide) (![⟨1053033, by decide⟩,⟨1053126, by decide⟩,⟨1053221, by decide⟩,⟨1053295, by decide⟩]) unmarked_context_10_18888_1053296 node_context_10_18888_1053296
  intro a
  fin_cases a
  · exact context_11_75552_1053033
  · exact context_11_75553_1053126
  · exact context_11_75554_1053221
  · exact context_11_75555_1053295

theorem selected_cut_38920 : selected 10 ⟨1053335, by decide⟩
    (prefixPartial 11 75556) = some ⟨11, 2, 0, 1053335, 75556, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_75556_1053335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75556 ⟨1053335, by decide⟩ :=
  accepted_of_selected 11 75556 ⟨1053335, by decide⟩ ⟨11, 2, 0, 1053335, 75556, 2241, 262144⟩
    (by decide) selected_cut_38920

theorem selected_cut_38921 : selected 10 ⟨1053381, by decide⟩
    (prefixPartial 11 75557) = some ⟨11, 2, 0, 1053381, 75557, 3197, 262144⟩ := by
  decide +kernel

theorem context_11_75557_1053381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75557 ⟨1053381, by decide⟩ :=
  accepted_of_selected 11 75557 ⟨1053381, by decide⟩ ⟨11, 2, 0, 1053381, 75557, 3197, 262144⟩
    (by decide) selected_cut_38921

theorem selected_cut_38922 : selected 10 ⟨1053442, by decide⟩
    (prefixPartial 11 75558) = some ⟨11, 2, 0, 1053442, 75558, 3437, 262144⟩ := by
  decide +kernel

theorem context_11_75558_1053442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75558 ⟨1053442, by decide⟩ :=
  accepted_of_selected 11 75558 ⟨1053442, by decide⟩ ⟨11, 2, 0, 1053442, 75558, 3437, 262144⟩
    (by decide) selected_cut_38922

theorem selected_cut_38923 : selected 10 ⟨1053498, by decide⟩
    (prefixPartial 11 75559) = some ⟨11, 2, 0, 1053498, 75559, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_75559_1053498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75559 ⟨1053498, by decide⟩ :=
  accepted_of_selected 11 75559 ⟨1053498, by decide⟩ ⟨11, 2, 0, 1053498, 75559, 3233, 262144⟩
    (by decide) selected_cut_38923

theorem unmarked_context_10_18889_1053499 : frontier 11 ⟨1053499, by decide⟩
    (prefixCache 10 18889) (prefixPartial 10 18889) = false := by
  decide +kernel

theorem node_context_10_18889_1053499 : EJMOriginalGlobalDAGData.nodes 11 ⟨1053499, by decide⟩ =
    .split (coordinate 10) (![⟨1053335, by decide⟩,⟨1053381, by decide⟩,⟨1053442, by decide⟩,⟨1053498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18889_1053499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18889 ⟨1053499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18889
    ⟨1053499, by decide⟩ (by decide) (![⟨1053335, by decide⟩,⟨1053381, by decide⟩,⟨1053442, by decide⟩,⟨1053498, by decide⟩]) unmarked_context_10_18889_1053499 node_context_10_18889_1053499
  intro a
  fin_cases a
  · exact context_11_75556_1053335
  · exact context_11_75557_1053381
  · exact context_11_75558_1053442
  · exact context_11_75559_1053498

theorem selected_cut_38924 : selected 10 ⟨1053536, by decide⟩
    (prefixPartial 11 75560) = some ⟨11, 2, 0, 1053536, 75560, 1989, 262144⟩ := by
  decide +kernel

theorem context_11_75560_1053536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75560 ⟨1053536, by decide⟩ :=
  accepted_of_selected 11 75560 ⟨1053536, by decide⟩ ⟨11, 2, 0, 1053536, 75560, 1989, 262144⟩
    (by decide) selected_cut_38924

theorem selected_cut_38925 : selected 10 ⟨1053580, by decide⟩
    (prefixPartial 11 75561) = some ⟨11, 2, 0, 1053580, 75561, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_75561_1053580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75561 ⟨1053580, by decide⟩ :=
  accepted_of_selected 11 75561 ⟨1053580, by decide⟩ ⟨11, 2, 0, 1053580, 75561, 2817, 262144⟩
    (by decide) selected_cut_38925

theorem selected_cut_38926 : selected 10 ⟨1053630, by decide⟩
    (prefixPartial 11 75562) = some ⟨11, 2, 0, 1053630, 75562, 1049, 262144⟩ := by
  decide +kernel

theorem context_11_75562_1053630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75562 ⟨1053630, by decide⟩ :=
  accepted_of_selected 11 75562 ⟨1053630, by decide⟩ ⟨11, 2, 0, 1053630, 75562, 1049, 262144⟩
    (by decide) selected_cut_38926

theorem selected_cut_38927 : selected 10 ⟨1053684, by decide⟩
    (prefixPartial 11 75563) = some ⟨11, 2, 0, 1053684, 75563, 2705, 262144⟩ := by
  decide +kernel

theorem context_11_75563_1053684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75563 ⟨1053684, by decide⟩ :=
  accepted_of_selected 11 75563 ⟨1053684, by decide⟩ ⟨11, 2, 0, 1053684, 75563, 2705, 262144⟩
    (by decide) selected_cut_38927

theorem unmarked_context_10_18890_1053685 : frontier 11 ⟨1053685, by decide⟩
    (prefixCache 10 18890) (prefixPartial 10 18890) = false := by
  decide +kernel

theorem node_context_10_18890_1053685 : EJMOriginalGlobalDAGData.nodes 11 ⟨1053685, by decide⟩ =
    .split (coordinate 10) (![⟨1053536, by decide⟩,⟨1053580, by decide⟩,⟨1053630, by decide⟩,⟨1053684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18890_1053685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18890 ⟨1053685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18890
    ⟨1053685, by decide⟩ (by decide) (![⟨1053536, by decide⟩,⟨1053580, by decide⟩,⟨1053630, by decide⟩,⟨1053684, by decide⟩]) unmarked_context_10_18890_1053685 node_context_10_18890_1053685
  intro a
  fin_cases a
  · exact context_11_75560_1053536
  · exact context_11_75561_1053580
  · exact context_11_75562_1053630
  · exact context_11_75563_1053684

theorem selected_cut_38928 : selected 10 ⟨1053710, by decide⟩
    (prefixPartial 11 75564) = some ⟨11, 2, 0, 1053710, 75564, 1297, 262144⟩ := by
  decide +kernel

theorem context_11_75564_1053710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75564 ⟨1053710, by decide⟩ :=
  accepted_of_selected 11 75564 ⟨1053710, by decide⟩ ⟨11, 2, 0, 1053710, 75564, 1297, 262144⟩
    (by decide) selected_cut_38928

theorem selected_cut_38929 : selected 10 ⟨1053751, by decide⟩
    (prefixPartial 11 75565) = some ⟨11, 2, 0, 1053751, 75565, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_75565_1053751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75565 ⟨1053751, by decide⟩ :=
  accepted_of_selected 11 75565 ⟨1053751, by decide⟩ ⟨11, 2, 0, 1053751, 75565, 2149, 262144⟩
    (by decide) selected_cut_38929

theorem selected_cut_38930 : selected 10 ⟨1053798, by decide⟩
    (prefixPartial 11 75566) = some ⟨11, 2, 0, 1053798, 75566, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_75566_1053798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75566 ⟨1053798, by decide⟩ :=
  accepted_of_selected 11 75566 ⟨1053798, by decide⟩ ⟨11, 2, 0, 1053798, 75566, 2133, 262144⟩
    (by decide) selected_cut_38930

theorem selected_cut_38931 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75567) = some ⟨11, 1, 0, 977886, 75567, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75567_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75567 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75567 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75567, 1, 262144⟩
    (by decide) selected_cut_38931

theorem unmarked_context_10_18891_1053799 : frontier 11 ⟨1053799, by decide⟩
    (prefixCache 10 18891) (prefixPartial 10 18891) = false := by
  decide +kernel

theorem node_context_10_18891_1053799 : EJMOriginalGlobalDAGData.nodes 11 ⟨1053799, by decide⟩ =
    .split (coordinate 10) (![⟨1053710, by decide⟩,⟨1053751, by decide⟩,⟨1053798, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18891_1053799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18891 ⟨1053799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18891
    ⟨1053799, by decide⟩ (by decide) (![⟨1053710, by decide⟩,⟨1053751, by decide⟩,⟨1053798, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18891_1053799 node_context_10_18891_1053799
  intro a
  fin_cases a
  · exact context_11_75564_1053710
  · exact context_11_75565_1053751
  · exact context_11_75566_1053798
  · exact context_11_75567_977886

theorem unmarked_context_9_4722_1053800 : frontier 12 ⟨1053800, by decide⟩
    (prefixCache 9 4722) (prefixPartial 9 4722) = false := by
  decide +kernel

theorem node_context_9_4722_1053800 : EJMOriginalGlobalDAGData.nodes 12 ⟨1053800, by decide⟩ =
    .split (coordinate 9) (![⟨1053296, by decide⟩,⟨1053499, by decide⟩,⟨1053685, by decide⟩,⟨1053799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4722_1053800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4722 ⟨1053800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4722
    ⟨1053800, by decide⟩ (by decide) (![⟨1053296, by decide⟩,⟨1053499, by decide⟩,⟨1053685, by decide⟩,⟨1053799, by decide⟩]) unmarked_context_9_4722_1053800 node_context_9_4722_1053800
  intro a
  fin_cases a
  · exact context_10_18888_1053296
  · exact context_10_18889_1053499
  · exact context_10_18890_1053685
  · exact context_10_18891_1053799

theorem selected_cut_38932 : selected 10 ⟨1053825, by decide⟩
    (prefixPartial 11 75568) = some ⟨11, 2, 0, 1053825, 75568, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_75568_1053825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75568 ⟨1053825, by decide⟩ :=
  accepted_of_selected 11 75568 ⟨1053825, by decide⟩ ⟨11, 2, 0, 1053825, 75568, 1561, 262144⟩
    (by decide) selected_cut_38932

theorem selected_cut_38933 : selected 10 ⟨1053865, by decide⟩
    (prefixPartial 11 75569) = some ⟨11, 2, 0, 1053865, 75569, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_75569_1053865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75569 ⟨1053865, by decide⟩ :=
  accepted_of_selected 11 75569 ⟨1053865, by decide⟩ ⟨11, 2, 0, 1053865, 75569, 2313, 262144⟩
    (by decide) selected_cut_38933

theorem selected_cut_38934 : selected 10 ⟨1053891, by decide⟩
    (prefixPartial 11 75570) = some ⟨11, 2, 0, 1053891, 75570, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_75570_1053891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75570 ⟨1053891, by decide⟩ :=
  accepted_of_selected 11 75570 ⟨1053891, by decide⟩ ⟨11, 2, 0, 1053891, 75570, 1889, 262144⟩
    (by decide) selected_cut_38934

theorem selected_cut_38935 : selected 10 ⟨1053917, by decide⟩
    (prefixPartial 11 75571) = some ⟨11, 2, 0, 1053917, 75571, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_75571_1053917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75571 ⟨1053917, by decide⟩ :=
  accepted_of_selected 11 75571 ⟨1053917, by decide⟩ ⟨11, 2, 0, 1053917, 75571, 1489, 262144⟩
    (by decide) selected_cut_38935

theorem unmarked_context_10_18892_1053918 : frontier 11 ⟨1053918, by decide⟩
    (prefixCache 10 18892) (prefixPartial 10 18892) = false := by
  decide +kernel

theorem node_context_10_18892_1053918 : EJMOriginalGlobalDAGData.nodes 11 ⟨1053918, by decide⟩ =
    .split (coordinate 10) (![⟨1053825, by decide⟩,⟨1053865, by decide⟩,⟨1053891, by decide⟩,⟨1053917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18892_1053918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18892 ⟨1053918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18892
    ⟨1053918, by decide⟩ (by decide) (![⟨1053825, by decide⟩,⟨1053865, by decide⟩,⟨1053891, by decide⟩,⟨1053917, by decide⟩]) unmarked_context_10_18892_1053918 node_context_10_18892_1053918
  intro a
  fin_cases a
  · exact context_11_75568_1053825
  · exact context_11_75569_1053865
  · exact context_11_75570_1053891
  · exact context_11_75571_1053917

theorem selected_cut_38936 : selected 10 ⟨1053934, by decide⟩
    (prefixPartial 11 75572) = some ⟨11, 2, 0, 1053934, 75572, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_75572_1053934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75572 ⟨1053934, by decide⟩ :=
  accepted_of_selected 11 75572 ⟨1053934, by decide⟩ ⟨11, 2, 0, 1053934, 75572, 1093, 262144⟩
    (by decide) selected_cut_38936

theorem selected_cut_38937 : selected 10 ⟨1053953, by decide⟩
    (prefixPartial 11 75573) = some ⟨11, 2, 0, 1053953, 75573, 1065, 262144⟩ := by
  decide +kernel

theorem context_11_75573_1053953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75573 ⟨1053953, by decide⟩ :=
  accepted_of_selected 11 75573 ⟨1053953, by decide⟩ ⟨11, 2, 0, 1053953, 75573, 1065, 262144⟩
    (by decide) selected_cut_38937

theorem selected_cut_38938 : selected 10 ⟨1053971, by decide⟩
    (prefixPartial 11 75574) = some ⟨11, 2, 0, 1053971, 75574, 1261, 262144⟩ := by
  decide +kernel

theorem context_11_75574_1053971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75574 ⟨1053971, by decide⟩ :=
  accepted_of_selected 11 75574 ⟨1053971, by decide⟩ ⟨11, 2, 0, 1053971, 75574, 1261, 262144⟩
    (by decide) selected_cut_38938

theorem selected_cut_38939 : selected 10 ⟨1053993, by decide⟩
    (prefixPartial 11 75575) = some ⟨11, 2, 0, 1053993, 75575, 1201, 262144⟩ := by
  decide +kernel

theorem context_11_75575_1053993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75575 ⟨1053993, by decide⟩ :=
  accepted_of_selected 11 75575 ⟨1053993, by decide⟩ ⟨11, 2, 0, 1053993, 75575, 1201, 262144⟩
    (by decide) selected_cut_38939

theorem unmarked_context_10_18893_1053994 : frontier 11 ⟨1053994, by decide⟩
    (prefixCache 10 18893) (prefixPartial 10 18893) = false := by
  decide +kernel

theorem node_context_10_18893_1053994 : EJMOriginalGlobalDAGData.nodes 11 ⟨1053994, by decide⟩ =
    .split (coordinate 10) (![⟨1053934, by decide⟩,⟨1053953, by decide⟩,⟨1053971, by decide⟩,⟨1053993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18893_1053994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18893 ⟨1053994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18893
    ⟨1053994, by decide⟩ (by decide) (![⟨1053934, by decide⟩,⟨1053953, by decide⟩,⟨1053971, by decide⟩,⟨1053993, by decide⟩]) unmarked_context_10_18893_1053994 node_context_10_18893_1053994
  intro a
  fin_cases a
  · exact context_11_75572_1053934
  · exact context_11_75573_1053953
  · exact context_11_75574_1053971
  · exact context_11_75575_1053993

theorem selected_cut_38940 : selected 11 ⟨1054051, by decide⟩
    (prefixPartial 10 18894) = some ⟨10, 2, 0, 1054051, 18894, 2529, 1048576⟩ := by
  decide +kernel

theorem context_10_18894_1054051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18894 ⟨1054051, by decide⟩ :=
  accepted_of_selected 10 18894 ⟨1054051, by decide⟩ ⟨10, 2, 0, 1054051, 18894, 2529, 1048576⟩
    (by decide) selected_cut_38940

theorem selected_cut_38941 : selected 11 ⟨1054086, by decide⟩
    (prefixPartial 10 18895) = some ⟨10, 2, 0, 1054086, 18895, 641, 1048576⟩ := by
  decide +kernel

theorem context_10_18895_1054086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18895 ⟨1054086, by decide⟩ :=
  accepted_of_selected 10 18895 ⟨1054086, by decide⟩ ⟨10, 2, 0, 1054086, 18895, 641, 1048576⟩
    (by decide) selected_cut_38941

theorem unmarked_context_9_4723_1054087 : frontier 12 ⟨1054087, by decide⟩
    (prefixCache 9 4723) (prefixPartial 9 4723) = false := by
  decide +kernel

theorem node_context_9_4723_1054087 : EJMOriginalGlobalDAGData.nodes 12 ⟨1054087, by decide⟩ =
    .split (coordinate 9) (![⟨1053918, by decide⟩,⟨1053994, by decide⟩,⟨1054051, by decide⟩,⟨1054086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4723_1054087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4723 ⟨1054087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4723
    ⟨1054087, by decide⟩ (by decide) (![⟨1053918, by decide⟩,⟨1053994, by decide⟩,⟨1054051, by decide⟩,⟨1054086, by decide⟩]) unmarked_context_9_4723_1054087 node_context_9_4723_1054087
  intro a
  fin_cases a
  · exact context_10_18892_1053918
  · exact context_10_18893_1053994
  · exact context_10_18894_1054051
  · exact context_10_18895_1054086

theorem unmarked_context_8_1180_1054088 : frontier 13 ⟨1054088, by decide⟩
    (prefixCache 8 1180) (prefixPartial 8 1180) = false := by
  decide +kernel

theorem node_context_8_1180_1054088 : EJMOriginalGlobalDAGData.nodes 13 ⟨1054088, by decide⟩ =
    .split (coordinate 8) (![⟨1051680, by decide⟩,⟨1052978, by decide⟩,⟨1053800, by decide⟩,⟨1054087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1180_1054088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1180 ⟨1054088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1180
    ⟨1054088, by decide⟩ (by decide) (![⟨1051680, by decide⟩,⟨1052978, by decide⟩,⟨1053800, by decide⟩,⟨1054087, by decide⟩]) unmarked_context_8_1180_1054088 node_context_8_1180_1054088
  intro a
  fin_cases a
  · exact context_9_4720_1051680
  · exact context_9_4721_1052978
  · exact context_9_4722_1053800
  · exact context_9_4723_1054087

theorem selected_cut_38942 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 302336) = some ⟨12, 1, 0, 34034, 302336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302336_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302336 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 302336 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 302336, 1, 65536⟩
    (by decide) selected_cut_38942

theorem selected_cut_38943 : selected 9 ⟨1054165, by decide⟩
    (prefixPartial 12 302337) = some ⟨12, 2, 0, 1054165, 302337, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_302337_1054165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302337 ⟨1054165, by decide⟩ :=
  accepted_of_selected 12 302337 ⟨1054165, by decide⟩ ⟨12, 2, 0, 1054165, 302337, 2213, 65536⟩
    (by decide) selected_cut_38943

theorem selected_cut_38944 : selected 9 ⟨1054227, by decide⟩
    (prefixPartial 12 302338) = some ⟨12, 2, 0, 1054227, 302338, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_302338_1054227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302338 ⟨1054227, by decide⟩ :=
  accepted_of_selected 12 302338 ⟨1054227, by decide⟩ ⟨12, 2, 0, 1054227, 302338, 3093, 65536⟩
    (by decide) selected_cut_38944

theorem selected_cut_38945 : selected 9 ⟨1048373, by decide⟩
    (prefixPartial 12 302339) = some ⟨12, 1, 0, 1048373, 302339, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302339_1048373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302339 ⟨1048373, by decide⟩ :=
  accepted_of_selected 12 302339 ⟨1048373, by decide⟩ ⟨12, 1, 0, 1048373, 302339, 1, 65536⟩
    (by decide) selected_cut_38945

theorem unmarked_context_11_75584_1054228 : frontier 10 ⟨1054228, by decide⟩
    (prefixCache 11 75584) (prefixPartial 11 75584) = false := by
  decide +kernel

theorem node_context_11_75584_1054228 : EJMOriginalGlobalDAGData.nodes 10 ⟨1054228, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1054165, by decide⟩,⟨1054227, by decide⟩,⟨1048373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75584_1054228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75584 ⟨1054228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75584
    ⟨1054228, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1054165, by decide⟩,⟨1054227, by decide⟩,⟨1048373, by decide⟩]) unmarked_context_11_75584_1054228 node_context_11_75584_1054228
  intro a
  fin_cases a
  · exact context_12_302336_34034
  · exact context_12_302337_1054165
  · exact context_12_302338_1054227
  · exact context_12_302339_1048373

theorem selected_cut_38946 : selected 9 ⟨1054329, by decide⟩
    (prefixPartial 12 302340) = some ⟨12, 2, 0, 1054329, 302340, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_302340_1054329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302340 ⟨1054329, by decide⟩ :=
  accepted_of_selected 12 302340 ⟨1054329, by decide⟩ ⟨12, 2, 0, 1054329, 302340, 4077, 65536⟩
    (by decide) selected_cut_38946

theorem selected_cut_38947 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 302341) = some ⟨12, 1, 0, 891951, 302341, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302341_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302341 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 302341 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 302341, 1, 65536⟩
    (by decide) selected_cut_38947

theorem selected_cut_38948 : selected 9 ⟨1054398, by decide⟩
    (prefixPartial 12 302342) = some ⟨12, 2, 0, 1054398, 302342, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_302342_1054398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302342 ⟨1054398, by decide⟩ :=
  accepted_of_selected 12 302342 ⟨1054398, by decide⟩ ⟨12, 2, 0, 1054398, 302342, 3653, 65536⟩
    (by decide) selected_cut_38948

theorem selected_cut_38949 : selected 9 ⟨1054472, by decide⟩
    (prefixPartial 12 302343) = some ⟨12, 2, 0, 1054472, 302343, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_302343_1054472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302343 ⟨1054472, by decide⟩ :=
  accepted_of_selected 12 302343 ⟨1054472, by decide⟩ ⟨12, 2, 0, 1054472, 302343, 3857, 65536⟩
    (by decide) selected_cut_38949

theorem unmarked_context_11_75585_1054473 : frontier 10 ⟨1054473, by decide⟩
    (prefixCache 11 75585) (prefixPartial 11 75585) = false := by
  decide +kernel

theorem node_context_11_75585_1054473 : EJMOriginalGlobalDAGData.nodes 10 ⟨1054473, by decide⟩ =
    .split (coordinate 11) (![⟨1054329, by decide⟩,⟨891951, by decide⟩,⟨1054398, by decide⟩,⟨1054472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75585_1054473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75585 ⟨1054473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75585
    ⟨1054473, by decide⟩ (by decide) (![⟨1054329, by decide⟩,⟨891951, by decide⟩,⟨1054398, by decide⟩,⟨1054472, by decide⟩]) unmarked_context_11_75585_1054473 node_context_11_75585_1054473
  intro a
  fin_cases a
  · exact context_12_302340_1054329
  · exact context_12_302341_891951
  · exact context_12_302342_1054398
  · exact context_12_302343_1054472

theorem selected_cut_38950 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 302344) = some ⟨12, 1, 0, 450498, 302344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302344_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302344 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 302344 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 302344, 1, 65536⟩
    (by decide) selected_cut_38950

theorem selected_cut_38951 : selected 9 ⟨1054557, by decide⟩
    (prefixPartial 12 302345) = some ⟨12, 2, 0, 1054557, 302345, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_302345_1054557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302345 ⟨1054557, by decide⟩ :=
  accepted_of_selected 12 302345 ⟨1054557, by decide⟩ ⟨12, 2, 0, 1054557, 302345, 3965, 65536⟩
    (by decide) selected_cut_38951

theorem selected_cut_38952 : selected 9 ⟨1054633, by decide⟩
    (prefixPartial 12 302346) = some ⟨12, 2, 0, 1054633, 302346, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_302346_1054633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302346 ⟨1054633, by decide⟩ :=
  accepted_of_selected 12 302346 ⟨1054633, by decide⟩ ⟨12, 2, 0, 1054633, 302346, 3761, 65536⟩
    (by decide) selected_cut_38952

theorem selected_cut_38953 : selected 9 ⟨1054697, by decide⟩
    (prefixPartial 12 302347) = some ⟨12, 2, 0, 1054697, 302347, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_302347_1054697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302347 ⟨1054697, by decide⟩ :=
  accepted_of_selected 12 302347 ⟨1054697, by decide⟩ ⟨12, 2, 0, 1054697, 302347, 3829, 65536⟩
    (by decide) selected_cut_38953

theorem unmarked_context_11_75586_1054698 : frontier 10 ⟨1054698, by decide⟩
    (prefixCache 11 75586) (prefixPartial 11 75586) = false := by
  decide +kernel

theorem node_context_11_75586_1054698 : EJMOriginalGlobalDAGData.nodes 10 ⟨1054698, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1054557, by decide⟩,⟨1054633, by decide⟩,⟨1054697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75586_1054698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75586 ⟨1054698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75586
    ⟨1054698, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1054557, by decide⟩,⟨1054633, by decide⟩,⟨1054697, by decide⟩]) unmarked_context_11_75586_1054698 node_context_11_75586_1054698
  intro a
  fin_cases a
  · exact context_12_302344_450498
  · exact context_12_302345_1054557
  · exact context_12_302346_1054633
  · exact context_12_302347_1054697

theorem selected_cut_38954 : selected 9 ⟨1054767, by decide⟩
    (prefixPartial 12 302348) = some ⟨12, 2, 0, 1054767, 302348, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_302348_1054767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302348 ⟨1054767, by decide⟩ :=
  accepted_of_selected 12 302348 ⟨1054767, by decide⟩ ⟨12, 2, 0, 1054767, 302348, 3537, 65536⟩
    (by decide) selected_cut_38954

theorem selected_cut_38955 : selected 9 ⟨1054839, by decide⟩
    (prefixPartial 12 302349) = some ⟨12, 2, 0, 1054839, 302349, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_302349_1054839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302349 ⟨1054839, by decide⟩ :=
  accepted_of_selected 12 302349 ⟨1054839, by decide⟩ ⟨12, 2, 0, 1054839, 302349, 3869, 65536⟩
    (by decide) selected_cut_38955

theorem selected_cut_38956 : selected 9 ⟨1054896, by decide⟩
    (prefixPartial 12 302350) = some ⟨12, 2, 0, 1054896, 302350, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_302350_1054896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302350 ⟨1054896, by decide⟩ :=
  accepted_of_selected 12 302350 ⟨1054896, by decide⟩ ⟨12, 2, 0, 1054896, 302350, 3473, 65536⟩
    (by decide) selected_cut_38956

theorem selected_cut_38957 : selected 9 ⟨1054970, by decide⟩
    (prefixPartial 12 302351) = some ⟨12, 2, 0, 1054970, 302351, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_302351_1054970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302351 ⟨1054970, by decide⟩ :=
  accepted_of_selected 12 302351 ⟨1054970, by decide⟩ ⟨12, 2, 0, 1054970, 302351, 3805, 65536⟩
    (by decide) selected_cut_38957

theorem unmarked_context_11_75587_1054971 : frontier 10 ⟨1054971, by decide⟩
    (prefixCache 11 75587) (prefixPartial 11 75587) = false := by
  decide +kernel

theorem node_context_11_75587_1054971 : EJMOriginalGlobalDAGData.nodes 10 ⟨1054971, by decide⟩ =
    .split (coordinate 11) (![⟨1054767, by decide⟩,⟨1054839, by decide⟩,⟨1054896, by decide⟩,⟨1054970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75587_1054971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75587 ⟨1054971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75587
    ⟨1054971, by decide⟩ (by decide) (![⟨1054767, by decide⟩,⟨1054839, by decide⟩,⟨1054896, by decide⟩,⟨1054970, by decide⟩]) unmarked_context_11_75587_1054971 node_context_11_75587_1054971
  intro a
  fin_cases a
  · exact context_12_302348_1054767
  · exact context_12_302349_1054839
  · exact context_12_302350_1054896
  · exact context_12_302351_1054970

theorem unmarked_context_10_18896_1054972 : frontier 11 ⟨1054972, by decide⟩
    (prefixCache 10 18896) (prefixPartial 10 18896) = false := by
  decide +kernel

theorem node_context_10_18896_1054972 : EJMOriginalGlobalDAGData.nodes 11 ⟨1054972, by decide⟩ =
    .split (coordinate 10) (![⟨1054228, by decide⟩,⟨1054473, by decide⟩,⟨1054698, by decide⟩,⟨1054971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18896_1054972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18896 ⟨1054972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18896
    ⟨1054972, by decide⟩ (by decide) (![⟨1054228, by decide⟩,⟨1054473, by decide⟩,⟨1054698, by decide⟩,⟨1054971, by decide⟩]) unmarked_context_10_18896_1054972 node_context_10_18896_1054972
  intro a
  fin_cases a
  · exact context_11_75584_1054228
  · exact context_11_75585_1054473
  · exact context_11_75586_1054698
  · exact context_11_75587_1054971

theorem selected_cut_38958 : selected 9 ⟨1055018, by decide⟩
    (prefixPartial 12 302352) = some ⟨12, 2, 0, 1055018, 302352, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_302352_1055018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302352 ⟨1055018, by decide⟩ :=
  accepted_of_selected 12 302352 ⟨1055018, by decide⟩ ⟨12, 2, 0, 1055018, 302352, 1741, 65536⟩
    (by decide) selected_cut_38958

theorem selected_cut_38959 : selected 9 ⟨1055072, by decide⟩
    (prefixPartial 12 302353) = some ⟨12, 2, 0, 1055072, 302353, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_302353_1055072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302353 ⟨1055072, by decide⟩ :=
  accepted_of_selected 12 302353 ⟨1055072, by decide⟩ ⟨12, 2, 0, 1055072, 302353, 2821, 65536⟩
    (by decide) selected_cut_38959

theorem selected_cut_38960 : selected 9 ⟨1055108, by decide⟩
    (prefixPartial 12 302354) = some ⟨12, 2, 0, 1055108, 302354, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_302354_1055108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302354 ⟨1055108, by decide⟩ :=
  accepted_of_selected 12 302354 ⟨1055108, by decide⟩ ⟨12, 2, 0, 1055108, 302354, 2537, 65536⟩
    (by decide) selected_cut_38960

theorem selected_cut_38961 : selected 9 ⟨1055151, by decide⟩
    (prefixPartial 12 302355) = some ⟨12, 2, 0, 1055151, 302355, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_302355_1055151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302355 ⟨1055151, by decide⟩ :=
  accepted_of_selected 12 302355 ⟨1055151, by decide⟩ ⟨12, 2, 0, 1055151, 302355, 2713, 65536⟩
    (by decide) selected_cut_38961

theorem unmarked_context_11_75588_1055152 : frontier 10 ⟨1055152, by decide⟩
    (prefixCache 11 75588) (prefixPartial 11 75588) = false := by
  decide +kernel

theorem node_context_11_75588_1055152 : EJMOriginalGlobalDAGData.nodes 10 ⟨1055152, by decide⟩ =
    .split (coordinate 11) (![⟨1055018, by decide⟩,⟨1055072, by decide⟩,⟨1055108, by decide⟩,⟨1055151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75588_1055152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75588 ⟨1055152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75588
    ⟨1055152, by decide⟩ (by decide) (![⟨1055018, by decide⟩,⟨1055072, by decide⟩,⟨1055108, by decide⟩,⟨1055151, by decide⟩]) unmarked_context_11_75588_1055152 node_context_11_75588_1055152
  intro a
  fin_cases a
  · exact context_12_302352_1055018
  · exact context_12_302353_1055072
  · exact context_12_302354_1055108
  · exact context_12_302355_1055151

theorem selected_cut_38962 : selected 9 ⟨1055201, by decide⟩
    (prefixPartial 12 302356) = some ⟨12, 2, 0, 1055201, 302356, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_302356_1055201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302356 ⟨1055201, by decide⟩ :=
  accepted_of_selected 12 302356 ⟨1055201, by decide⟩ ⟨12, 2, 0, 1055201, 302356, 2701, 65536⟩
    (by decide) selected_cut_38962

theorem selected_cut_38963 : selected 9 ⟨692794, by decide⟩
    (prefixPartial 12 302357) = some ⟨12, 1, 0, 692794, 302357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302357_692794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302357 ⟨692794, by decide⟩ :=
  accepted_of_selected 12 302357 ⟨692794, by decide⟩ ⟨12, 1, 0, 692794, 302357, 1, 65536⟩
    (by decide) selected_cut_38963

theorem selected_cut_38964 : selected 9 ⟨1055239, by decide⟩
    (prefixPartial 12 302358) = some ⟨12, 2, 0, 1055239, 302358, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_302358_1055239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302358 ⟨1055239, by decide⟩ :=
  accepted_of_selected 12 302358 ⟨1055239, by decide⟩ ⟨12, 2, 0, 1055239, 302358, 2625, 65536⟩
    (by decide) selected_cut_38964

theorem selected_cut_38965 : selected 9 ⟨1055276, by decide⟩
    (prefixPartial 12 302359) = some ⟨12, 2, 0, 1055276, 302359, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_302359_1055276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302359 ⟨1055276, by decide⟩ :=
  accepted_of_selected 12 302359 ⟨1055276, by decide⟩ ⟨12, 2, 0, 1055276, 302359, 2781, 65536⟩
    (by decide) selected_cut_38965

theorem unmarked_context_11_75589_1055277 : frontier 10 ⟨1055277, by decide⟩
    (prefixCache 11 75589) (prefixPartial 11 75589) = false := by
  decide +kernel

theorem node_context_11_75589_1055277 : EJMOriginalGlobalDAGData.nodes 10 ⟨1055277, by decide⟩ =
    .split (coordinate 11) (![⟨1055201, by decide⟩,⟨692794, by decide⟩,⟨1055239, by decide⟩,⟨1055276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75589_1055277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75589 ⟨1055277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75589
    ⟨1055277, by decide⟩ (by decide) (![⟨1055201, by decide⟩,⟨692794, by decide⟩,⟨1055239, by decide⟩,⟨1055276, by decide⟩]) unmarked_context_11_75589_1055277 node_context_11_75589_1055277
  intro a
  fin_cases a
  · exact context_12_302356_1055201
  · exact context_12_302357_692794
  · exact context_12_302358_1055239
  · exact context_12_302359_1055276

theorem selected_cut_38966 : selected 9 ⟨1055316, by decide⟩
    (prefixPartial 12 302360) = some ⟨12, 2, 0, 1055316, 302360, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_302360_1055316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302360 ⟨1055316, by decide⟩ :=
  accepted_of_selected 12 302360 ⟨1055316, by decide⟩ ⟨12, 2, 0, 1055316, 302360, 2545, 65536⟩
    (by decide) selected_cut_38966

theorem selected_cut_38967 : selected 9 ⟨1055357, by decide⟩
    (prefixPartial 12 302361) = some ⟨12, 2, 0, 1055357, 302361, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_302361_1055357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302361 ⟨1055357, by decide⟩ :=
  accepted_of_selected 12 302361 ⟨1055357, by decide⟩ ⟨12, 2, 0, 1055357, 302361, 2781, 65536⟩
    (by decide) selected_cut_38967

theorem selected_cut_38968 : selected 9 ⟨1055399, by decide⟩
    (prefixPartial 12 302362) = some ⟨12, 2, 0, 1055399, 302362, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_302362_1055399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302362 ⟨1055399, by decide⟩ :=
  accepted_of_selected 12 302362 ⟨1055399, by decide⟩ ⟨12, 2, 0, 1055399, 302362, 2617, 65536⟩
    (by decide) selected_cut_38968

theorem selected_cut_38969 : selected 9 ⟨1055443, by decide⟩
    (prefixPartial 12 302363) = some ⟨12, 2, 0, 1055443, 302363, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_302363_1055443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302363 ⟨1055443, by decide⟩ :=
  accepted_of_selected 12 302363 ⟨1055443, by decide⟩ ⟨12, 2, 0, 1055443, 302363, 2841, 65536⟩
    (by decide) selected_cut_38969

theorem unmarked_context_11_75590_1055444 : frontier 10 ⟨1055444, by decide⟩
    (prefixCache 11 75590) (prefixPartial 11 75590) = false := by
  decide +kernel

theorem node_context_11_75590_1055444 : EJMOriginalGlobalDAGData.nodes 10 ⟨1055444, by decide⟩ =
    .split (coordinate 11) (![⟨1055316, by decide⟩,⟨1055357, by decide⟩,⟨1055399, by decide⟩,⟨1055443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75590_1055444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75590 ⟨1055444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75590
    ⟨1055444, by decide⟩ (by decide) (![⟨1055316, by decide⟩,⟨1055357, by decide⟩,⟨1055399, by decide⟩,⟨1055443, by decide⟩]) unmarked_context_11_75590_1055444 node_context_11_75590_1055444
  intro a
  fin_cases a
  · exact context_12_302360_1055316
  · exact context_12_302361_1055357
  · exact context_12_302362_1055399
  · exact context_12_302363_1055443

theorem selected_cut_38970 : selected 9 ⟨1055481, by decide⟩
    (prefixPartial 12 302364) = some ⟨12, 2, 0, 1055481, 302364, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_302364_1055481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302364 ⟨1055481, by decide⟩ :=
  accepted_of_selected 12 302364 ⟨1055481, by decide⟩ ⟨12, 2, 0, 1055481, 302364, 2525, 65536⟩
    (by decide) selected_cut_38970

theorem selected_cut_38971 : selected 9 ⟨1055525, by decide⟩
    (prefixPartial 12 302365) = some ⟨12, 2, 0, 1055525, 302365, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_302365_1055525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302365 ⟨1055525, by decide⟩ :=
  accepted_of_selected 12 302365 ⟨1055525, by decide⟩ ⟨12, 2, 0, 1055525, 302365, 2721, 65536⟩
    (by decide) selected_cut_38971

theorem selected_cut_38972 : selected 9 ⟨1055555, by decide⟩
    (prefixPartial 12 302366) = some ⟨12, 2, 0, 1055555, 302366, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_302366_1055555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302366 ⟨1055555, by decide⟩ :=
  accepted_of_selected 12 302366 ⟨1055555, by decide⟩ ⟨12, 2, 0, 1055555, 302366, 2605, 65536⟩
    (by decide) selected_cut_38972

theorem selected_cut_38973 : selected 9 ⟨1055592, by decide⟩
    (prefixPartial 12 302367) = some ⟨12, 2, 0, 1055592, 302367, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_302367_1055592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302367 ⟨1055592, by decide⟩ :=
  accepted_of_selected 12 302367 ⟨1055592, by decide⟩ ⟨12, 2, 0, 1055592, 302367, 2857, 65536⟩
    (by decide) selected_cut_38973

theorem unmarked_context_11_75591_1055593 : frontier 10 ⟨1055593, by decide⟩
    (prefixCache 11 75591) (prefixPartial 11 75591) = false := by
  decide +kernel

theorem node_context_11_75591_1055593 : EJMOriginalGlobalDAGData.nodes 10 ⟨1055593, by decide⟩ =
    .split (coordinate 11) (![⟨1055481, by decide⟩,⟨1055525, by decide⟩,⟨1055555, by decide⟩,⟨1055592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75591_1055593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75591 ⟨1055593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75591
    ⟨1055593, by decide⟩ (by decide) (![⟨1055481, by decide⟩,⟨1055525, by decide⟩,⟨1055555, by decide⟩,⟨1055592, by decide⟩]) unmarked_context_11_75591_1055593 node_context_11_75591_1055593
  intro a
  fin_cases a
  · exact context_12_302364_1055481
  · exact context_12_302365_1055525
  · exact context_12_302366_1055555
  · exact context_12_302367_1055592

theorem unmarked_context_10_18897_1055594 : frontier 11 ⟨1055594, by decide⟩
    (prefixCache 10 18897) (prefixPartial 10 18897) = false := by
  decide +kernel

theorem node_context_10_18897_1055594 : EJMOriginalGlobalDAGData.nodes 11 ⟨1055594, by decide⟩ =
    .split (coordinate 10) (![⟨1055152, by decide⟩,⟨1055277, by decide⟩,⟨1055444, by decide⟩,⟨1055593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18897_1055594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18897 ⟨1055594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18897
    ⟨1055594, by decide⟩ (by decide) (![⟨1055152, by decide⟩,⟨1055277, by decide⟩,⟨1055444, by decide⟩,⟨1055593, by decide⟩]) unmarked_context_10_18897_1055594 node_context_10_18897_1055594
  intro a
  fin_cases a
  · exact context_11_75588_1055152
  · exact context_11_75589_1055277
  · exact context_11_75590_1055444
  · exact context_11_75591_1055593

theorem selected_cut_38974 : selected 9 ⟨1055595, by decide⟩
    (prefixPartial 12 302368) = some ⟨12, 1, 0, 1055595, 302368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302368_1055595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302368 ⟨1055595, by decide⟩ :=
  accepted_of_selected 12 302368 ⟨1055595, by decide⟩ ⟨12, 1, 0, 1055595, 302368, 1, 65536⟩
    (by decide) selected_cut_38974

theorem selected_cut_38975 : selected 9 ⟨1055665, by decide⟩
    (prefixPartial 12 302369) = some ⟨12, 2, 0, 1055665, 302369, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_302369_1055665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302369 ⟨1055665, by decide⟩ :=
  accepted_of_selected 12 302369 ⟨1055665, by decide⟩ ⟨12, 2, 0, 1055665, 302369, 3373, 65536⟩
    (by decide) selected_cut_38975

theorem selected_cut_38976 : selected 9 ⟨1055702, by decide⟩
    (prefixPartial 12 302370) = some ⟨12, 2, 0, 1055702, 302370, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_302370_1055702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302370 ⟨1055702, by decide⟩ :=
  accepted_of_selected 12 302370 ⟨1055702, by decide⟩ ⟨12, 2, 0, 1055702, 302370, 2689, 65536⟩
    (by decide) selected_cut_38976

theorem selected_cut_38977 : selected 9 ⟨1055745, by decide⟩
    (prefixPartial 12 302371) = some ⟨12, 2, 0, 1055745, 302371, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_302371_1055745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302371 ⟨1055745, by decide⟩ :=
  accepted_of_selected 12 302371 ⟨1055745, by decide⟩ ⟨12, 2, 0, 1055745, 302371, 2949, 65536⟩
    (by decide) selected_cut_38977

theorem unmarked_context_11_75592_1055746 : frontier 10 ⟨1055746, by decide⟩
    (prefixCache 11 75592) (prefixPartial 11 75592) = false := by
  decide +kernel

theorem node_context_11_75592_1055746 : EJMOriginalGlobalDAGData.nodes 10 ⟨1055746, by decide⟩ =
    .split (coordinate 11) (![⟨1055595, by decide⟩,⟨1055665, by decide⟩,⟨1055702, by decide⟩,⟨1055745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75592_1055746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75592 ⟨1055746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75592
    ⟨1055746, by decide⟩ (by decide) (![⟨1055595, by decide⟩,⟨1055665, by decide⟩,⟨1055702, by decide⟩,⟨1055745, by decide⟩]) unmarked_context_11_75592_1055746 node_context_11_75592_1055746
  intro a
  fin_cases a
  · exact context_12_302368_1055595
  · exact context_12_302369_1055665
  · exact context_12_302370_1055702
  · exact context_12_302371_1055745

theorem selected_cut_38978 : selected 9 ⟨1055797, by decide⟩
    (prefixPartial 12 302372) = some ⟨12, 2, 0, 1055797, 302372, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_302372_1055797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302372 ⟨1055797, by decide⟩ :=
  accepted_of_selected 12 302372 ⟨1055797, by decide⟩ ⟨12, 2, 0, 1055797, 302372, 3221, 65536⟩
    (by decide) selected_cut_38978

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
