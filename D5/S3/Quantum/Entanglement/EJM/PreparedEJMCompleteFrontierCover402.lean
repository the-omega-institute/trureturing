/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover401
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38596 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 301690) = some ⟨12, 1, 0, 893903, 301690, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301690_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301690 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 301690 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 301690, 1, 65536⟩
    (by decide) selected_cut_38596

theorem selected_cut_38597 : selected 9 ⟨1041728, by decide⟩
    (prefixPartial 12 301691) = some ⟨12, 2, 0, 1041728, 301691, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_301691_1041728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301691 ⟨1041728, by decide⟩ :=
  accepted_of_selected 12 301691 ⟨1041728, by decide⟩ ⟨12, 2, 0, 1041728, 301691, 1809, 65536⟩
    (by decide) selected_cut_38597

theorem unmarked_context_11_75422_1041729 : frontier 10 ⟨1041729, by decide⟩
    (prefixCache 11 75422) (prefixPartial 11 75422) = false := by
  decide +kernel

theorem node_context_11_75422_1041729 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041729, by decide⟩ =
    .split (coordinate 11) (![⟨1041660, by decide⟩,⟨1041696, by decide⟩,⟨893903, by decide⟩,⟨1041728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75422_1041729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75422 ⟨1041729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75422
    ⟨1041729, by decide⟩ (by decide) (![⟨1041660, by decide⟩,⟨1041696, by decide⟩,⟨893903, by decide⟩,⟨1041728, by decide⟩]) unmarked_context_11_75422_1041729 node_context_11_75422_1041729
  intro a
  fin_cases a
  · exact context_12_301688_1041660
  · exact context_12_301689_1041696
  · exact context_12_301690_893903
  · exact context_12_301691_1041728

theorem selected_cut_38598 : selected 9 ⟨1041768, by decide⟩
    (prefixPartial 12 301692) = some ⟨12, 2, 0, 1041768, 301692, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_301692_1041768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301692 ⟨1041768, by decide⟩ :=
  accepted_of_selected 12 301692 ⟨1041768, by decide⟩ ⟨12, 2, 0, 1041768, 301692, 1921, 65536⟩
    (by decide) selected_cut_38598

theorem selected_cut_38599 : selected 9 ⟨1041802, by decide⟩
    (prefixPartial 12 301693) = some ⟨12, 2, 0, 1041802, 301693, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_301693_1041802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301693 ⟨1041802, by decide⟩ :=
  accepted_of_selected 12 301693 ⟨1041802, by decide⟩ ⟨12, 2, 0, 1041802, 301693, 1893, 65536⟩
    (by decide) selected_cut_38599

theorem selected_cut_38600 : selected 9 ⟨1041828, by decide⟩
    (prefixPartial 12 301694) = some ⟨12, 2, 0, 1041828, 301694, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_301694_1041828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301694 ⟨1041828, by decide⟩ :=
  accepted_of_selected 12 301694 ⟨1041828, by decide⟩ ⟨12, 2, 0, 1041828, 301694, 1645, 65536⟩
    (by decide) selected_cut_38600

theorem selected_cut_38601 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 301695) = some ⟨12, 1, 0, 762109, 301695, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301695_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301695 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 301695 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 301695, 1, 65536⟩
    (by decide) selected_cut_38601

theorem unmarked_context_11_75423_1041829 : frontier 10 ⟨1041829, by decide⟩
    (prefixCache 11 75423) (prefixPartial 11 75423) = false := by
  decide +kernel

theorem node_context_11_75423_1041829 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041829, by decide⟩ =
    .split (coordinate 11) (![⟨1041768, by decide⟩,⟨1041802, by decide⟩,⟨1041828, by decide⟩,⟨762109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75423_1041829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75423 ⟨1041829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75423
    ⟨1041829, by decide⟩ (by decide) (![⟨1041768, by decide⟩,⟨1041802, by decide⟩,⟨1041828, by decide⟩,⟨762109, by decide⟩]) unmarked_context_11_75423_1041829 node_context_11_75423_1041829
  intro a
  fin_cases a
  · exact context_12_301692_1041768
  · exact context_12_301693_1041802
  · exact context_12_301694_1041828
  · exact context_12_301695_762109

theorem unmarked_context_10_18855_1041830 : frontier 11 ⟨1041830, by decide⟩
    (prefixCache 10 18855) (prefixPartial 10 18855) = false := by
  decide +kernel

theorem node_context_10_18855_1041830 : EJMOriginalGlobalDAGData.nodes 11 ⟨1041830, by decide⟩ =
    .split (coordinate 10) (![⟨1041554, by decide⟩,⟨1041632, by decide⟩,⟨1041729, by decide⟩,⟨1041829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18855_1041830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18855 ⟨1041830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18855
    ⟨1041830, by decide⟩ (by decide) (![⟨1041554, by decide⟩,⟨1041632, by decide⟩,⟨1041729, by decide⟩,⟨1041829, by decide⟩]) unmarked_context_10_18855_1041830 node_context_10_18855_1041830
  intro a
  fin_cases a
  · exact context_11_75420_1041554
  · exact context_11_75421_1041632
  · exact context_11_75422_1041729
  · exact context_11_75423_1041829

theorem unmarked_context_9_4713_1041831 : frontier 12 ⟨1041831, by decide⟩
    (prefixCache 9 4713) (prefixPartial 9 4713) = false := by
  decide +kernel

theorem node_context_9_4713_1041831 : EJMOriginalGlobalDAGData.nodes 12 ⟨1041831, by decide⟩ =
    .split (coordinate 9) (![⟨1041151, by decide⟩,⟨893098, by decide⟩,⟨1041439, by decide⟩,⟨1041830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4713_1041831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4713 ⟨1041831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4713
    ⟨1041831, by decide⟩ (by decide) (![⟨1041151, by decide⟩,⟨893098, by decide⟩,⟨1041439, by decide⟩,⟨1041830, by decide⟩]) unmarked_context_9_4713_1041831 node_context_9_4713_1041831
  intro a
  fin_cases a
  · exact context_10_18852_1041151
  · exact context_10_18853_893098
  · exact context_10_18854_1041439
  · exact context_10_18855_1041830

theorem selected_cut_38602 : selected 10 ⟨1041882, by decide⟩
    (prefixPartial 11 75424) = some ⟨11, 2, 0, 1041882, 75424, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_75424_1041882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75424 ⟨1041882, by decide⟩ :=
  accepted_of_selected 11 75424 ⟨1041882, by decide⟩ ⟨11, 2, 0, 1041882, 75424, 2665, 262144⟩
    (by decide) selected_cut_38602

theorem selected_cut_38603 : selected 9 ⟨1041910, by decide⟩
    (prefixPartial 12 301700) = some ⟨12, 2, 0, 1041910, 301700, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_301700_1041910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301700 ⟨1041910, by decide⟩ :=
  accepted_of_selected 12 301700 ⟨1041910, by decide⟩ ⟨12, 2, 0, 1041910, 301700, 1657, 65536⟩
    (by decide) selected_cut_38603

theorem selected_cut_38604 : selected 9 ⟨1041932, by decide⟩
    (prefixPartial 12 301701) = some ⟨12, 2, 0, 1041932, 301701, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_301701_1041932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301701 ⟨1041932, by decide⟩ :=
  accepted_of_selected 12 301701 ⟨1041932, by decide⟩ ⟨12, 2, 0, 1041932, 301701, 1445, 65536⟩
    (by decide) selected_cut_38604

theorem selected_cut_38605 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 301702) = some ⟨12, 1, 0, 984676, 301702, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301702_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301702 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 301702 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 301702, 1, 65536⟩
    (by decide) selected_cut_38605

theorem selected_cut_38606 : selected 9 ⟨1041954, by decide⟩
    (prefixPartial 12 301703) = some ⟨12, 2, 0, 1041954, 301703, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_301703_1041954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301703 ⟨1041954, by decide⟩ :=
  accepted_of_selected 12 301703 ⟨1041954, by decide⟩ ⟨12, 2, 0, 1041954, 301703, 1337, 65536⟩
    (by decide) selected_cut_38606

theorem unmarked_context_11_75425_1041955 : frontier 10 ⟨1041955, by decide⟩
    (prefixCache 11 75425) (prefixPartial 11 75425) = false := by
  decide +kernel

theorem node_context_11_75425_1041955 : EJMOriginalGlobalDAGData.nodes 10 ⟨1041955, by decide⟩ =
    .split (coordinate 11) (![⟨1041910, by decide⟩,⟨1041932, by decide⟩,⟨984676, by decide⟩,⟨1041954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75425_1041955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75425 ⟨1041955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75425
    ⟨1041955, by decide⟩ (by decide) (![⟨1041910, by decide⟩,⟨1041932, by decide⟩,⟨984676, by decide⟩,⟨1041954, by decide⟩]) unmarked_context_11_75425_1041955 node_context_11_75425_1041955
  intro a
  fin_cases a
  · exact context_12_301700_1041910
  · exact context_12_301701_1041932
  · exact context_12_301702_984676
  · exact context_12_301703_1041954

theorem selected_cut_38607 : selected 10 ⟨1042032, by decide⟩
    (prefixPartial 11 75426) = some ⟨11, 2, 0, 1042032, 75426, 4085, 262144⟩ := by
  decide +kernel

theorem context_11_75426_1042032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75426 ⟨1042032, by decide⟩ :=
  accepted_of_selected 11 75426 ⟨1042032, by decide⟩ ⟨11, 2, 0, 1042032, 75426, 4085, 262144⟩
    (by decide) selected_cut_38607

theorem selected_cut_38608 : selected 10 ⟨1042103, by decide⟩
    (prefixPartial 11 75427) = some ⟨11, 2, 0, 1042103, 75427, 4089, 262144⟩ := by
  decide +kernel

theorem context_11_75427_1042103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75427 ⟨1042103, by decide⟩ :=
  accepted_of_selected 11 75427 ⟨1042103, by decide⟩ ⟨11, 2, 0, 1042103, 75427, 4089, 262144⟩
    (by decide) selected_cut_38608

theorem unmarked_context_10_18856_1042104 : frontier 11 ⟨1042104, by decide⟩
    (prefixCache 10 18856) (prefixPartial 10 18856) = false := by
  decide +kernel

theorem node_context_10_18856_1042104 : EJMOriginalGlobalDAGData.nodes 11 ⟨1042104, by decide⟩ =
    .split (coordinate 10) (![⟨1041882, by decide⟩,⟨1041955, by decide⟩,⟨1042032, by decide⟩,⟨1042103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18856_1042104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18856 ⟨1042104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18856
    ⟨1042104, by decide⟩ (by decide) (![⟨1041882, by decide⟩,⟨1041955, by decide⟩,⟨1042032, by decide⟩,⟨1042103, by decide⟩]) unmarked_context_10_18856_1042104 node_context_10_18856_1042104
  intro a
  fin_cases a
  · exact context_11_75424_1041882
  · exact context_11_75425_1041955
  · exact context_11_75426_1042032
  · exact context_11_75427_1042103

theorem selected_cut_38609 : selected 10 ⟨1042165, by decide⟩
    (prefixPartial 11 75428) = some ⟨11, 2, 0, 1042165, 75428, 3217, 262144⟩ := by
  decide +kernel

theorem context_11_75428_1042165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75428 ⟨1042165, by decide⟩ :=
  accepted_of_selected 11 75428 ⟨1042165, by decide⟩ ⟨11, 2, 0, 1042165, 75428, 3217, 262144⟩
    (by decide) selected_cut_38609

theorem selected_cut_38610 : selected 10 ⟨1042204, by decide⟩
    (prefixPartial 11 75429) = some ⟨11, 2, 0, 1042204, 75429, 2093, 262144⟩ := by
  decide +kernel

theorem context_11_75429_1042204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75429 ⟨1042204, by decide⟩ :=
  accepted_of_selected 11 75429 ⟨1042204, by decide⟩ ⟨11, 2, 0, 1042204, 75429, 2093, 262144⟩
    (by decide) selected_cut_38610

theorem selected_cut_38611 : selected 10 ⟨1042248, by decide⟩
    (prefixPartial 11 75430) = some ⟨11, 2, 0, 1042248, 75430, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_75430_1042248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75430 ⟨1042248, by decide⟩ :=
  accepted_of_selected 11 75430 ⟨1042248, by decide⟩ ⟨11, 2, 0, 1042248, 75430, 2657, 262144⟩
    (by decide) selected_cut_38611

theorem selected_cut_38612 : selected 10 ⟨1042302, by decide⟩
    (prefixPartial 11 75431) = some ⟨11, 2, 0, 1042302, 75431, 3161, 262144⟩ := by
  decide +kernel

theorem context_11_75431_1042302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75431 ⟨1042302, by decide⟩ :=
  accepted_of_selected 11 75431 ⟨1042302, by decide⟩ ⟨11, 2, 0, 1042302, 75431, 3161, 262144⟩
    (by decide) selected_cut_38612

theorem unmarked_context_10_18857_1042303 : frontier 11 ⟨1042303, by decide⟩
    (prefixCache 10 18857) (prefixPartial 10 18857) = false := by
  decide +kernel

theorem node_context_10_18857_1042303 : EJMOriginalGlobalDAGData.nodes 11 ⟨1042303, by decide⟩ =
    .split (coordinate 10) (![⟨1042165, by decide⟩,⟨1042204, by decide⟩,⟨1042248, by decide⟩,⟨1042302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18857_1042303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18857 ⟨1042303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18857
    ⟨1042303, by decide⟩ (by decide) (![⟨1042165, by decide⟩,⟨1042204, by decide⟩,⟨1042248, by decide⟩,⟨1042302, by decide⟩]) unmarked_context_10_18857_1042303 node_context_10_18857_1042303
  intro a
  fin_cases a
  · exact context_11_75428_1042165
  · exact context_11_75429_1042204
  · exact context_11_75430_1042248
  · exact context_11_75431_1042302

theorem selected_cut_38613 : selected 10 ⟨1042331, by decide⟩
    (prefixPartial 11 75432) = some ⟨11, 2, 0, 1042331, 75432, 2261, 262144⟩ := by
  decide +kernel

theorem context_11_75432_1042331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75432 ⟨1042331, by decide⟩ :=
  accepted_of_selected 11 75432 ⟨1042331, by decide⟩ ⟨11, 2, 0, 1042331, 75432, 2261, 262144⟩
    (by decide) selected_cut_38613

theorem selected_cut_38614 : selected 10 ⟨1042368, by decide⟩
    (prefixPartial 11 75433) = some ⟨11, 2, 0, 1042368, 75433, 2337, 262144⟩ := by
  decide +kernel

theorem context_11_75433_1042368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75433 ⟨1042368, by decide⟩ :=
  accepted_of_selected 11 75433 ⟨1042368, by decide⟩ ⟨11, 2, 0, 1042368, 75433, 2337, 262144⟩
    (by decide) selected_cut_38614

theorem selected_cut_38615 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75434) = some ⟨11, 1, 0, 906566, 75434, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75434_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75434 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75434 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75434, 1, 262144⟩
    (by decide) selected_cut_38615

theorem selected_cut_38616 : selected 10 ⟨1042399, by decide⟩
    (prefixPartial 11 75435) = some ⟨11, 2, 0, 1042399, 75435, 2293, 262144⟩ := by
  decide +kernel

theorem context_11_75435_1042399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75435 ⟨1042399, by decide⟩ :=
  accepted_of_selected 11 75435 ⟨1042399, by decide⟩ ⟨11, 2, 0, 1042399, 75435, 2293, 262144⟩
    (by decide) selected_cut_38616

theorem unmarked_context_10_18858_1042400 : frontier 11 ⟨1042400, by decide⟩
    (prefixCache 10 18858) (prefixPartial 10 18858) = false := by
  decide +kernel

theorem node_context_10_18858_1042400 : EJMOriginalGlobalDAGData.nodes 11 ⟨1042400, by decide⟩ =
    .split (coordinate 10) (![⟨1042331, by decide⟩,⟨1042368, by decide⟩,⟨906566, by decide⟩,⟨1042399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18858_1042400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18858 ⟨1042400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18858
    ⟨1042400, by decide⟩ (by decide) (![⟨1042331, by decide⟩,⟨1042368, by decide⟩,⟨906566, by decide⟩,⟨1042399, by decide⟩]) unmarked_context_10_18858_1042400 node_context_10_18858_1042400
  intro a
  fin_cases a
  · exact context_11_75432_1042331
  · exact context_11_75433_1042368
  · exact context_11_75434_906566
  · exact context_11_75435_1042399

theorem selected_cut_38617 : selected 10 ⟨1042439, by decide⟩
    (prefixPartial 11 75436) = some ⟨11, 2, 0, 1042439, 75436, 2213, 262144⟩ := by
  decide +kernel

theorem context_11_75436_1042439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75436 ⟨1042439, by decide⟩ :=
  accepted_of_selected 11 75436 ⟨1042439, by decide⟩ ⟨11, 2, 0, 1042439, 75436, 2213, 262144⟩
    (by decide) selected_cut_38617

theorem selected_cut_38618 : selected 10 ⟨1042477, by decide⟩
    (prefixPartial 11 75437) = some ⟨11, 2, 0, 1042477, 75437, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_75437_1042477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75437 ⟨1042477, by decide⟩ :=
  accepted_of_selected 11 75437 ⟨1042477, by decide⟩ ⟨11, 2, 0, 1042477, 75437, 2253, 262144⟩
    (by decide) selected_cut_38618

theorem selected_cut_38619 : selected 10 ⟨1042506, by decide⟩
    (prefixPartial 11 75438) = some ⟨11, 2, 0, 1042506, 75438, 1841, 262144⟩ := by
  decide +kernel

theorem context_11_75438_1042506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75438 ⟨1042506, by decide⟩ :=
  accepted_of_selected 11 75438 ⟨1042506, by decide⟩ ⟨11, 2, 0, 1042506, 75438, 1841, 262144⟩
    (by decide) selected_cut_38619

theorem selected_cut_38620 : selected 10 ⟨1042535, by decide⟩
    (prefixPartial 11 75439) = some ⟨11, 2, 0, 1042535, 75439, 1505, 262144⟩ := by
  decide +kernel

theorem context_11_75439_1042535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75439 ⟨1042535, by decide⟩ :=
  accepted_of_selected 11 75439 ⟨1042535, by decide⟩ ⟨11, 2, 0, 1042535, 75439, 1505, 262144⟩
    (by decide) selected_cut_38620

theorem unmarked_context_10_18859_1042536 : frontier 11 ⟨1042536, by decide⟩
    (prefixCache 10 18859) (prefixPartial 10 18859) = false := by
  decide +kernel

theorem node_context_10_18859_1042536 : EJMOriginalGlobalDAGData.nodes 11 ⟨1042536, by decide⟩ =
    .split (coordinate 10) (![⟨1042439, by decide⟩,⟨1042477, by decide⟩,⟨1042506, by decide⟩,⟨1042535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18859_1042536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18859 ⟨1042536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18859
    ⟨1042536, by decide⟩ (by decide) (![⟨1042439, by decide⟩,⟨1042477, by decide⟩,⟨1042506, by decide⟩,⟨1042535, by decide⟩]) unmarked_context_10_18859_1042536 node_context_10_18859_1042536
  intro a
  fin_cases a
  · exact context_11_75436_1042439
  · exact context_11_75437_1042477
  · exact context_11_75438_1042506
  · exact context_11_75439_1042535

theorem unmarked_context_9_4714_1042537 : frontier 12 ⟨1042537, by decide⟩
    (prefixCache 9 4714) (prefixPartial 9 4714) = false := by
  decide +kernel

theorem node_context_9_4714_1042537 : EJMOriginalGlobalDAGData.nodes 12 ⟨1042537, by decide⟩ =
    .split (coordinate 9) (![⟨1042104, by decide⟩,⟨1042303, by decide⟩,⟨1042400, by decide⟩,⟨1042536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4714_1042537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4714 ⟨1042537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4714
    ⟨1042537, by decide⟩ (by decide) (![⟨1042104, by decide⟩,⟨1042303, by decide⟩,⟨1042400, by decide⟩,⟨1042536, by decide⟩]) unmarked_context_9_4714_1042537 node_context_9_4714_1042537
  intro a
  fin_cases a
  · exact context_10_18856_1042104
  · exact context_10_18857_1042303
  · exact context_10_18858_1042400
  · exact context_10_18859_1042536

theorem selected_cut_38621 : selected 10 ⟨1042572, by decide⟩
    (prefixPartial 11 75440) = some ⟨11, 2, 0, 1042572, 75440, 2017, 262144⟩ := by
  decide +kernel

theorem context_11_75440_1042572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75440 ⟨1042572, by decide⟩ :=
  accepted_of_selected 11 75440 ⟨1042572, by decide⟩ ⟨11, 2, 0, 1042572, 75440, 2017, 262144⟩
    (by decide) selected_cut_38621

theorem selected_cut_38622 : selected 10 ⟨1042640, by decide⟩
    (prefixPartial 11 75441) = some ⟨11, 2, 0, 1042640, 75441, 2773, 262144⟩ := by
  decide +kernel

theorem context_11_75441_1042640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75441 ⟨1042640, by decide⟩ :=
  accepted_of_selected 11 75441 ⟨1042640, by decide⟩ ⟨11, 2, 0, 1042640, 75441, 2773, 262144⟩
    (by decide) selected_cut_38622

theorem selected_cut_38623 : selected 10 ⟨1042674, by decide⟩
    (prefixPartial 11 75442) = some ⟨11, 2, 0, 1042674, 75442, 1829, 262144⟩ := by
  decide +kernel

theorem context_11_75442_1042674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75442 ⟨1042674, by decide⟩ :=
  accepted_of_selected 11 75442 ⟨1042674, by decide⟩ ⟨11, 2, 0, 1042674, 75442, 1829, 262144⟩
    (by decide) selected_cut_38623

theorem selected_cut_38624 : selected 10 ⟨1042736, by decide⟩
    (prefixPartial 11 75443) = some ⟨11, 2, 0, 1042736, 75443, 1833, 262144⟩ := by
  decide +kernel

theorem context_11_75443_1042736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75443 ⟨1042736, by decide⟩ :=
  accepted_of_selected 11 75443 ⟨1042736, by decide⟩ ⟨11, 2, 0, 1042736, 75443, 1833, 262144⟩
    (by decide) selected_cut_38624

theorem unmarked_context_10_18860_1042737 : frontier 11 ⟨1042737, by decide⟩
    (prefixCache 10 18860) (prefixPartial 10 18860) = false := by
  decide +kernel

theorem node_context_10_18860_1042737 : EJMOriginalGlobalDAGData.nodes 11 ⟨1042737, by decide⟩ =
    .split (coordinate 10) (![⟨1042572, by decide⟩,⟨1042640, by decide⟩,⟨1042674, by decide⟩,⟨1042736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18860_1042737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18860 ⟨1042737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18860
    ⟨1042737, by decide⟩ (by decide) (![⟨1042572, by decide⟩,⟨1042640, by decide⟩,⟨1042674, by decide⟩,⟨1042736, by decide⟩]) unmarked_context_10_18860_1042737 node_context_10_18860_1042737
  intro a
  fin_cases a
  · exact context_11_75440_1042572
  · exact context_11_75441_1042640
  · exact context_11_75442_1042674
  · exact context_11_75443_1042736

theorem selected_cut_38625 : selected 10 ⟨1042761, by decide⟩
    (prefixPartial 11 75444) = some ⟨11, 2, 0, 1042761, 75444, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_75444_1042761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75444 ⟨1042761, by decide⟩ :=
  accepted_of_selected 11 75444 ⟨1042761, by decide⟩ ⟨11, 2, 0, 1042761, 75444, 1641, 262144⟩
    (by decide) selected_cut_38625

theorem selected_cut_38626 : selected 10 ⟨1042780, by decide⟩
    (prefixPartial 11 75445) = some ⟨11, 2, 0, 1042780, 75445, 1021, 262144⟩ := by
  decide +kernel

theorem context_11_75445_1042780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75445 ⟨1042780, by decide⟩ :=
  accepted_of_selected 11 75445 ⟨1042780, by decide⟩ ⟨11, 2, 0, 1042780, 75445, 1021, 262144⟩
    (by decide) selected_cut_38626

theorem selected_cut_38627 : selected 10 ⟨1042803, by decide⟩
    (prefixPartial 11 75446) = some ⟨11, 2, 0, 1042803, 75446, 989, 262144⟩ := by
  decide +kernel

theorem context_11_75446_1042803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75446 ⟨1042803, by decide⟩ :=
  accepted_of_selected 11 75446 ⟨1042803, by decide⟩ ⟨11, 2, 0, 1042803, 75446, 989, 262144⟩
    (by decide) selected_cut_38627

theorem selected_cut_38628 : selected 10 ⟨1042827, by decide⟩
    (prefixPartial 11 75447) = some ⟨11, 2, 0, 1042827, 75447, 1001, 262144⟩ := by
  decide +kernel

theorem context_11_75447_1042827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75447 ⟨1042827, by decide⟩ :=
  accepted_of_selected 11 75447 ⟨1042827, by decide⟩ ⟨11, 2, 0, 1042827, 75447, 1001, 262144⟩
    (by decide) selected_cut_38628

theorem unmarked_context_10_18861_1042828 : frontier 11 ⟨1042828, by decide⟩
    (prefixCache 10 18861) (prefixPartial 10 18861) = false := by
  decide +kernel

theorem node_context_10_18861_1042828 : EJMOriginalGlobalDAGData.nodes 11 ⟨1042828, by decide⟩ =
    .split (coordinate 10) (![⟨1042761, by decide⟩,⟨1042780, by decide⟩,⟨1042803, by decide⟩,⟨1042827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18861_1042828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18861 ⟨1042828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18861
    ⟨1042828, by decide⟩ (by decide) (![⟨1042761, by decide⟩,⟨1042780, by decide⟩,⟨1042803, by decide⟩,⟨1042827, by decide⟩]) unmarked_context_10_18861_1042828 node_context_10_18861_1042828
  intro a
  fin_cases a
  · exact context_11_75444_1042761
  · exact context_11_75445_1042780
  · exact context_11_75446_1042803
  · exact context_11_75447_1042827

theorem selected_cut_38629 : selected 11 ⟨1042870, by decide⟩
    (prefixPartial 10 18862) = some ⟨10, 2, 0, 1042870, 18862, 2077, 1048576⟩ := by
  decide +kernel

theorem context_10_18862_1042870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18862 ⟨1042870, by decide⟩ :=
  accepted_of_selected 10 18862 ⟨1042870, by decide⟩ ⟨10, 2, 0, 1042870, 18862, 2077, 1048576⟩
    (by decide) selected_cut_38629

theorem selected_cut_38630 : selected 11 ⟨1042908, by decide⟩
    (prefixPartial 10 18863) = some ⟨10, 2, 0, 1042908, 18863, 781, 1048576⟩ := by
  decide +kernel

theorem context_10_18863_1042908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18863 ⟨1042908, by decide⟩ :=
  accepted_of_selected 10 18863 ⟨1042908, by decide⟩ ⟨10, 2, 0, 1042908, 18863, 781, 1048576⟩
    (by decide) selected_cut_38630

theorem unmarked_context_9_4715_1042909 : frontier 12 ⟨1042909, by decide⟩
    (prefixCache 9 4715) (prefixPartial 9 4715) = false := by
  decide +kernel

theorem node_context_9_4715_1042909 : EJMOriginalGlobalDAGData.nodes 12 ⟨1042909, by decide⟩ =
    .split (coordinate 9) (![⟨1042737, by decide⟩,⟨1042828, by decide⟩,⟨1042870, by decide⟩,⟨1042908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4715_1042909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4715 ⟨1042909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4715
    ⟨1042909, by decide⟩ (by decide) (![⟨1042737, by decide⟩,⟨1042828, by decide⟩,⟨1042870, by decide⟩,⟨1042908, by decide⟩]) unmarked_context_9_4715_1042909 node_context_9_4715_1042909
  intro a
  fin_cases a
  · exact context_10_18860_1042737
  · exact context_10_18861_1042828
  · exact context_10_18862_1042870
  · exact context_10_18863_1042908

theorem unmarked_context_8_1178_1042910 : frontier 13 ⟨1042910, by decide⟩
    (prefixCache 8 1178) (prefixPartial 8 1178) = false := by
  decide +kernel

theorem node_context_8_1178_1042910 : EJMOriginalGlobalDAGData.nodes 13 ⟨1042910, by decide⟩ =
    .split (coordinate 8) (![⟨1040464, by decide⟩,⟨1041831, by decide⟩,⟨1042537, by decide⟩,⟨1042909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1178_1042910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1178 ⟨1042910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1178
    ⟨1042910, by decide⟩ (by decide) (![⟨1040464, by decide⟩,⟨1041831, by decide⟩,⟨1042537, by decide⟩,⟨1042909, by decide⟩]) unmarked_context_8_1178_1042910 node_context_8_1178_1042910
  intro a
  fin_cases a
  · exact context_9_4712_1040464
  · exact context_9_4713_1041831
  · exact context_9_4714_1042537
  · exact context_9_4715_1042909

theorem selected_cut_38631 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 301824) = some ⟨12, 1, 0, 34034, 301824, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301824_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301824 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 301824 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 301824, 1, 65536⟩
    (by decide) selected_cut_38631

theorem selected_cut_38632 : selected 9 ⟨1042981, by decide⟩
    (prefixPartial 12 301825) = some ⟨12, 2, 0, 1042981, 301825, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_301825_1042981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301825 ⟨1042981, by decide⟩ :=
  accepted_of_selected 12 301825 ⟨1042981, by decide⟩ ⟨12, 2, 0, 1042981, 301825, 2265, 65536⟩
    (by decide) selected_cut_38632

theorem selected_cut_38633 : selected 9 ⟨1043033, by decide⟩
    (prefixPartial 12 301826) = some ⟨12, 2, 0, 1043033, 301826, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_301826_1043033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301826 ⟨1043033, by decide⟩ :=
  accepted_of_selected 12 301826 ⟨1043033, by decide⟩ ⟨12, 2, 0, 1043033, 301826, 3293, 65536⟩
    (by decide) selected_cut_38633

theorem selected_cut_38634 : selected 9 ⟨1043086, by decide⟩
    (prefixPartial 12 301827) = some ⟨12, 2, 0, 1043086, 301827, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_301827_1043086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301827 ⟨1043086, by decide⟩ :=
  accepted_of_selected 12 301827 ⟨1043086, by decide⟩ ⟨12, 2, 0, 1043086, 301827, 3429, 65536⟩
    (by decide) selected_cut_38634

theorem unmarked_context_11_75456_1043087 : frontier 10 ⟨1043087, by decide⟩
    (prefixCache 11 75456) (prefixPartial 11 75456) = false := by
  decide +kernel

theorem node_context_11_75456_1043087 : EJMOriginalGlobalDAGData.nodes 10 ⟨1043087, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1042981, by decide⟩,⟨1043033, by decide⟩,⟨1043086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75456_1043087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75456 ⟨1043087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75456
    ⟨1043087, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1042981, by decide⟩,⟨1043033, by decide⟩,⟨1043086, by decide⟩]) unmarked_context_11_75456_1043087 node_context_11_75456_1043087
  intro a
  fin_cases a
  · exact context_12_301824_34034
  · exact context_12_301825_1042981
  · exact context_12_301826_1043033
  · exact context_12_301827_1043086

theorem selected_cut_38635 : selected 9 ⟨1043174, by decide⟩
    (prefixPartial 12 301828) = some ⟨12, 2, 0, 1043174, 301828, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_301828_1043174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301828 ⟨1043174, by decide⟩ :=
  accepted_of_selected 12 301828 ⟨1043174, by decide⟩ ⟨12, 2, 0, 1043174, 301828, 3777, 65536⟩
    (by decide) selected_cut_38635

theorem selected_cut_38636 : selected 8 ⟨1043205, by decide⟩
    (prefixPartial 13 1207316) = some ⟨13, 2, 0, 1043205, 1207316, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_1207316_1043205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207316 ⟨1043205, by decide⟩ :=
  accepted_of_selected 13 1207316 ⟨1043205, by decide⟩ ⟨13, 2, 0, 1043205, 1207316, 1661, 16384⟩
    (by decide) selected_cut_38636

theorem selected_cut_38637 : selected 8 ⟨1043227, by decide⟩
    (prefixPartial 13 1207317) = some ⟨13, 2, 0, 1043227, 1207317, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_1207317_1043227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207317 ⟨1043227, by decide⟩ :=
  accepted_of_selected 13 1207317 ⟨1043227, by decide⟩ ⟨13, 2, 0, 1043227, 1207317, 1169, 16384⟩
    (by decide) selected_cut_38637

theorem selected_cut_38638 : selected 8 ⟨1043245, by decide⟩
    (prefixPartial 13 1207318) = some ⟨13, 2, 0, 1043245, 1207318, 913, 16384⟩ := by
  decide +kernel

theorem context_13_1207318_1043245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207318 ⟨1043245, by decide⟩ :=
  accepted_of_selected 13 1207318 ⟨1043245, by decide⟩ ⟨13, 2, 0, 1043245, 1207318, 913, 16384⟩
    (by decide) selected_cut_38638

theorem selected_cut_38639 : selected 8 ⟨1043248, by decide⟩
    (prefixPartial 13 1207319) = some ⟨13, 2, 0, 1043248, 1207319, 497, 16384⟩ := by
  decide +kernel

theorem context_13_1207319_1043248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207319 ⟨1043248, by decide⟩ :=
  accepted_of_selected 13 1207319 ⟨1043248, by decide⟩ ⟨13, 2, 0, 1043248, 1207319, 497, 16384⟩
    (by decide) selected_cut_38639

theorem unmarked_context_12_301829_1043249 : frontier 9 ⟨1043249, by decide⟩
    (prefixCache 12 301829) (prefixPartial 12 301829) = false := by
  decide +kernel

theorem node_context_12_301829_1043249 : EJMOriginalGlobalDAGData.nodes 9 ⟨1043249, by decide⟩ =
    .split (coordinate 12) (![⟨1043205, by decide⟩,⟨1043227, by decide⟩,⟨1043245, by decide⟩,⟨1043248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301829_1043249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301829 ⟨1043249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301829
    ⟨1043249, by decide⟩ (by decide) (![⟨1043205, by decide⟩,⟨1043227, by decide⟩,⟨1043245, by decide⟩,⟨1043248, by decide⟩]) unmarked_context_12_301829_1043249 node_context_12_301829_1043249
  intro a
  fin_cases a
  · exact context_13_1207316_1043205
  · exact context_13_1207317_1043227
  · exact context_13_1207318_1043245
  · exact context_13_1207319_1043248

theorem selected_cut_38640 : selected 9 ⟨1043326, by decide⟩
    (prefixPartial 12 301830) = some ⟨12, 2, 0, 1043326, 301830, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_301830_1043326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301830 ⟨1043326, by decide⟩ :=
  accepted_of_selected 12 301830 ⟨1043326, by decide⟩ ⟨12, 2, 0, 1043326, 301830, 3737, 65536⟩
    (by decide) selected_cut_38640

theorem selected_cut_38641 : selected 9 ⟨1043383, by decide⟩
    (prefixPartial 12 301831) = some ⟨12, 2, 0, 1043383, 301831, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_301831_1043383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301831 ⟨1043383, by decide⟩ :=
  accepted_of_selected 12 301831 ⟨1043383, by decide⟩ ⟨12, 2, 0, 1043383, 301831, 3777, 65536⟩
    (by decide) selected_cut_38641

theorem unmarked_context_11_75457_1043384 : frontier 10 ⟨1043384, by decide⟩
    (prefixCache 11 75457) (prefixPartial 11 75457) = false := by
  decide +kernel

theorem node_context_11_75457_1043384 : EJMOriginalGlobalDAGData.nodes 10 ⟨1043384, by decide⟩ =
    .split (coordinate 11) (![⟨1043174, by decide⟩,⟨1043249, by decide⟩,⟨1043326, by decide⟩,⟨1043383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75457_1043384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75457 ⟨1043384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75457
    ⟨1043384, by decide⟩ (by decide) (![⟨1043174, by decide⟩,⟨1043249, by decide⟩,⟨1043326, by decide⟩,⟨1043383, by decide⟩]) unmarked_context_11_75457_1043384 node_context_11_75457_1043384
  intro a
  fin_cases a
  · exact context_12_301828_1043174
  · exact context_12_301829_1043249
  · exact context_12_301830_1043326
  · exact context_12_301831_1043383

theorem selected_cut_38642 : selected 9 ⟨1043446, by decide⟩
    (prefixPartial 12 301832) = some ⟨12, 2, 0, 1043446, 301832, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_301832_1043446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301832 ⟨1043446, by decide⟩ :=
  accepted_of_selected 12 301832 ⟨1043446, by decide⟩ ⟨12, 2, 0, 1043446, 301832, 3693, 65536⟩
    (by decide) selected_cut_38642

theorem selected_cut_38643 : selected 8 ⟨1043468, by decide⟩
    (prefixPartial 13 1207332) = some ⟨13, 2, 0, 1043468, 1207332, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_1207332_1043468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207332 ⟨1043468, by decide⟩ :=
  accepted_of_selected 13 1207332 ⟨1043468, by decide⟩ ⟨13, 2, 0, 1043468, 1207332, 1385, 16384⟩
    (by decide) selected_cut_38643

theorem selected_cut_38644 : selected 8 ⟨1043488, by decide⟩
    (prefixPartial 13 1207333) = some ⟨13, 2, 0, 1043488, 1207333, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_1207333_1043488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207333 ⟨1043488, by decide⟩ :=
  accepted_of_selected 13 1207333 ⟨1043488, by decide⟩ ⟨13, 2, 0, 1043488, 1207333, 1205, 16384⟩
    (by decide) selected_cut_38644

theorem selected_cut_38645 : selected 8 ⟨1043506, by decide⟩
    (prefixPartial 13 1207334) = some ⟨13, 2, 0, 1043506, 1207334, 981, 16384⟩ := by
  decide +kernel

theorem context_13_1207334_1043506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207334 ⟨1043506, by decide⟩ :=
  accepted_of_selected 13 1207334 ⟨1043506, by decide⟩ ⟨13, 2, 0, 1043506, 1207334, 981, 16384⟩
    (by decide) selected_cut_38645

theorem selected_cut_38646 : selected 8 ⟨1043510, by decide⟩
    (prefixPartial 13 1207335) = some ⟨13, 2, 0, 1043510, 1207335, 577, 16384⟩ := by
  decide +kernel

theorem context_13_1207335_1043510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207335 ⟨1043510, by decide⟩ :=
  accepted_of_selected 13 1207335 ⟨1043510, by decide⟩ ⟨13, 2, 0, 1043510, 1207335, 577, 16384⟩
    (by decide) selected_cut_38646

theorem unmarked_context_12_301833_1043511 : frontier 9 ⟨1043511, by decide⟩
    (prefixCache 12 301833) (prefixPartial 12 301833) = false := by
  decide +kernel

theorem node_context_12_301833_1043511 : EJMOriginalGlobalDAGData.nodes 9 ⟨1043511, by decide⟩ =
    .split (coordinate 12) (![⟨1043468, by decide⟩,⟨1043488, by decide⟩,⟨1043506, by decide⟩,⟨1043510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301833_1043511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301833 ⟨1043511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301833
    ⟨1043511, by decide⟩ (by decide) (![⟨1043468, by decide⟩,⟨1043488, by decide⟩,⟨1043506, by decide⟩,⟨1043510, by decide⟩]) unmarked_context_12_301833_1043511 node_context_12_301833_1043511
  intro a
  fin_cases a
  · exact context_13_1207332_1043468
  · exact context_13_1207333_1043488
  · exact context_13_1207334_1043506
  · exact context_13_1207335_1043510

theorem selected_cut_38647 : selected 9 ⟨1043575, by decide⟩
    (prefixPartial 12 301834) = some ⟨12, 2, 0, 1043575, 301834, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_301834_1043575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301834 ⟨1043575, by decide⟩ :=
  accepted_of_selected 12 301834 ⟨1043575, by decide⟩ ⟨12, 2, 0, 1043575, 301834, 3609, 65536⟩
    (by decide) selected_cut_38647

theorem selected_cut_38648 : selected 9 ⟨1043631, by decide⟩
    (prefixPartial 12 301835) = some ⟨12, 2, 0, 1043631, 301835, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_301835_1043631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301835 ⟨1043631, by decide⟩ :=
  accepted_of_selected 12 301835 ⟨1043631, by decide⟩ ⟨12, 2, 0, 1043631, 301835, 3965, 65536⟩
    (by decide) selected_cut_38648

theorem unmarked_context_11_75458_1043632 : frontier 10 ⟨1043632, by decide⟩
    (prefixCache 11 75458) (prefixPartial 11 75458) = false := by
  decide +kernel

theorem node_context_11_75458_1043632 : EJMOriginalGlobalDAGData.nodes 10 ⟨1043632, by decide⟩ =
    .split (coordinate 11) (![⟨1043446, by decide⟩,⟨1043511, by decide⟩,⟨1043575, by decide⟩,⟨1043631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75458_1043632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75458 ⟨1043632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75458
    ⟨1043632, by decide⟩ (by decide) (![⟨1043446, by decide⟩,⟨1043511, by decide⟩,⟨1043575, by decide⟩,⟨1043631, by decide⟩]) unmarked_context_11_75458_1043632 node_context_11_75458_1043632
  intro a
  fin_cases a
  · exact context_12_301832_1043446
  · exact context_12_301833_1043511
  · exact context_12_301834_1043575
  · exact context_12_301835_1043631

theorem selected_cut_38649 : selected 9 ⟨1043689, by decide⟩
    (prefixPartial 12 301836) = some ⟨12, 2, 0, 1043689, 301836, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_301836_1043689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301836 ⟨1043689, by decide⟩ :=
  accepted_of_selected 12 301836 ⟨1043689, by decide⟩ ⟨12, 2, 0, 1043689, 301836, 3569, 65536⟩
    (by decide) selected_cut_38649

theorem selected_cut_38650 : selected 8 ⟨1043715, by decide⟩
    (prefixPartial 13 1207348) = some ⟨13, 2, 0, 1043715, 1207348, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_1207348_1043715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207348 ⟨1043715, by decide⟩ :=
  accepted_of_selected 13 1207348 ⟨1043715, by decide⟩ ⟨13, 2, 0, 1043715, 1207348, 1493, 16384⟩
    (by decide) selected_cut_38650

theorem selected_cut_38651 : selected 8 ⟨1043733, by decide⟩
    (prefixPartial 13 1207349) = some ⟨13, 2, 0, 1043733, 1207349, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_1207349_1043733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207349 ⟨1043733, by decide⟩ :=
  accepted_of_selected 13 1207349 ⟨1043733, by decide⟩ ⟨13, 2, 0, 1043733, 1207349, 1109, 16384⟩
    (by decide) selected_cut_38651

theorem selected_cut_38652 : selected 8 ⟨1043750, by decide⟩
    (prefixPartial 13 1207350) = some ⟨13, 2, 0, 1043750, 1207350, 929, 16384⟩ := by
  decide +kernel

theorem context_13_1207350_1043750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207350 ⟨1043750, by decide⟩ :=
  accepted_of_selected 13 1207350 ⟨1043750, by decide⟩ ⟨13, 2, 0, 1043750, 1207350, 929, 16384⟩
    (by decide) selected_cut_38652

theorem selected_cut_38653 : selected 8 ⟨1043755, by decide⟩
    (prefixPartial 13 1207351) = some ⟨13, 2, 0, 1043755, 1207351, 589, 16384⟩ := by
  decide +kernel

theorem context_13_1207351_1043755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1207351 ⟨1043755, by decide⟩ :=
  accepted_of_selected 13 1207351 ⟨1043755, by decide⟩ ⟨13, 2, 0, 1043755, 1207351, 589, 16384⟩
    (by decide) selected_cut_38653

theorem unmarked_context_12_301837_1043756 : frontier 9 ⟨1043756, by decide⟩
    (prefixCache 12 301837) (prefixPartial 12 301837) = false := by
  decide +kernel

theorem node_context_12_301837_1043756 : EJMOriginalGlobalDAGData.nodes 9 ⟨1043756, by decide⟩ =
    .split (coordinate 12) (![⟨1043715, by decide⟩,⟨1043733, by decide⟩,⟨1043750, by decide⟩,⟨1043755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301837_1043756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301837 ⟨1043756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301837
    ⟨1043756, by decide⟩ (by decide) (![⟨1043715, by decide⟩,⟨1043733, by decide⟩,⟨1043750, by decide⟩,⟨1043755, by decide⟩]) unmarked_context_12_301837_1043756 node_context_12_301837_1043756
  intro a
  fin_cases a
  · exact context_13_1207348_1043715
  · exact context_13_1207349_1043733
  · exact context_13_1207350_1043750
  · exact context_13_1207351_1043755

theorem selected_cut_38654 : selected 9 ⟨1043822, by decide⟩
    (prefixPartial 12 301838) = some ⟨12, 2, 0, 1043822, 301838, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_301838_1043822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301838 ⟨1043822, by decide⟩ :=
  accepted_of_selected 12 301838 ⟨1043822, by decide⟩ ⟨12, 2, 0, 1043822, 301838, 3761, 65536⟩
    (by decide) selected_cut_38654

theorem selected_cut_38655 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 301839) = some ⟨12, 1, 0, 903806, 301839, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301839_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301839 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 301839 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 301839, 1, 65536⟩
    (by decide) selected_cut_38655

theorem unmarked_context_11_75459_1043823 : frontier 10 ⟨1043823, by decide⟩
    (prefixCache 11 75459) (prefixPartial 11 75459) = false := by
  decide +kernel

theorem node_context_11_75459_1043823 : EJMOriginalGlobalDAGData.nodes 10 ⟨1043823, by decide⟩ =
    .split (coordinate 11) (![⟨1043689, by decide⟩,⟨1043756, by decide⟩,⟨1043822, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75459_1043823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75459 ⟨1043823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75459
    ⟨1043823, by decide⟩ (by decide) (![⟨1043689, by decide⟩,⟨1043756, by decide⟩,⟨1043822, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75459_1043823 node_context_11_75459_1043823
  intro a
  fin_cases a
  · exact context_12_301836_1043689
  · exact context_12_301837_1043756
  · exact context_12_301838_1043822
  · exact context_12_301839_903806

theorem unmarked_context_10_18864_1043824 : frontier 11 ⟨1043824, by decide⟩
    (prefixCache 10 18864) (prefixPartial 10 18864) = false := by
  decide +kernel

theorem node_context_10_18864_1043824 : EJMOriginalGlobalDAGData.nodes 11 ⟨1043824, by decide⟩ =
    .split (coordinate 10) (![⟨1043087, by decide⟩,⟨1043384, by decide⟩,⟨1043632, by decide⟩,⟨1043823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18864_1043824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18864 ⟨1043824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18864
    ⟨1043824, by decide⟩ (by decide) (![⟨1043087, by decide⟩,⟨1043384, by decide⟩,⟨1043632, by decide⟩,⟨1043823, by decide⟩]) unmarked_context_10_18864_1043824 node_context_10_18864_1043824
  intro a
  fin_cases a
  · exact context_11_75456_1043087
  · exact context_11_75457_1043384
  · exact context_11_75458_1043632
  · exact context_11_75459_1043823

theorem selected_cut_38656 : selected 9 ⟨1043870, by decide⟩
    (prefixPartial 12 301840) = some ⟨12, 2, 0, 1043870, 301840, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_301840_1043870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301840 ⟨1043870, by decide⟩ :=
  accepted_of_selected 12 301840 ⟨1043870, by decide⟩ ⟨12, 2, 0, 1043870, 301840, 2525, 65536⟩
    (by decide) selected_cut_38656

theorem selected_cut_38657 : selected 9 ⟨1043918, by decide⟩
    (prefixPartial 12 301841) = some ⟨12, 2, 0, 1043918, 301841, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_301841_1043918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301841 ⟨1043918, by decide⟩ :=
  accepted_of_selected 12 301841 ⟨1043918, by decide⟩ ⟨12, 2, 0, 1043918, 301841, 3109, 65536⟩
    (by decide) selected_cut_38657

theorem selected_cut_38658 : selected 9 ⟨1043960, by decide⟩
    (prefixPartial 12 301842) = some ⟨12, 2, 0, 1043960, 301842, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_301842_1043960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301842 ⟨1043960, by decide⟩ :=
  accepted_of_selected 12 301842 ⟨1043960, by decide⟩ ⟨12, 2, 0, 1043960, 301842, 2865, 65536⟩
    (by decide) selected_cut_38658

theorem selected_cut_38659 : selected 9 ⟨1044009, by decide⟩
    (prefixPartial 12 301843) = some ⟨12, 2, 0, 1044009, 301843, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_301843_1044009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301843 ⟨1044009, by decide⟩ :=
  accepted_of_selected 12 301843 ⟨1044009, by decide⟩ ⟨12, 2, 0, 1044009, 301843, 2933, 65536⟩
    (by decide) selected_cut_38659

theorem unmarked_context_11_75460_1044010 : frontier 10 ⟨1044010, by decide⟩
    (prefixCache 11 75460) (prefixPartial 11 75460) = false := by
  decide +kernel

theorem node_context_11_75460_1044010 : EJMOriginalGlobalDAGData.nodes 10 ⟨1044010, by decide⟩ =
    .split (coordinate 11) (![⟨1043870, by decide⟩,⟨1043918, by decide⟩,⟨1043960, by decide⟩,⟨1044009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75460_1044010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75460 ⟨1044010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75460
    ⟨1044010, by decide⟩ (by decide) (![⟨1043870, by decide⟩,⟨1043918, by decide⟩,⟨1043960, by decide⟩,⟨1044009, by decide⟩]) unmarked_context_11_75460_1044010 node_context_11_75460_1044010
  intro a
  fin_cases a
  · exact context_12_301840_1043870
  · exact context_12_301841_1043918
  · exact context_12_301842_1043960
  · exact context_12_301843_1044009

theorem selected_cut_38660 : selected 9 ⟨1044060, by decide⟩
    (prefixPartial 12 301844) = some ⟨12, 2, 0, 1044060, 301844, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_301844_1044060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301844 ⟨1044060, by decide⟩ :=
  accepted_of_selected 12 301844 ⟨1044060, by decide⟩ ⟨12, 2, 0, 1044060, 301844, 2881, 65536⟩
    (by decide) selected_cut_38660

theorem selected_cut_38661 : selected 9 ⟨1044111, by decide⟩
    (prefixPartial 12 301845) = some ⟨12, 2, 0, 1044111, 301845, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_301845_1044111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301845 ⟨1044111, by decide⟩ :=
  accepted_of_selected 12 301845 ⟨1044111, by decide⟩ ⟨12, 2, 0, 1044111, 301845, 3233, 65536⟩
    (by decide) selected_cut_38661

theorem selected_cut_38662 : selected 9 ⟨1044164, by decide⟩
    (prefixPartial 12 301846) = some ⟨12, 2, 0, 1044164, 301846, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_301846_1044164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301846 ⟨1044164, by decide⟩ :=
  accepted_of_selected 12 301846 ⟨1044164, by decide⟩ ⟨12, 2, 0, 1044164, 301846, 2921, 65536⟩
    (by decide) selected_cut_38662

theorem selected_cut_38663 : selected 9 ⟨1044211, by decide⟩
    (prefixPartial 12 301847) = some ⟨12, 2, 0, 1044211, 301847, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_301847_1044211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301847 ⟨1044211, by decide⟩ :=
  accepted_of_selected 12 301847 ⟨1044211, by decide⟩ ⟨12, 2, 0, 1044211, 301847, 2893, 65536⟩
    (by decide) selected_cut_38663

theorem unmarked_context_11_75461_1044212 : frontier 10 ⟨1044212, by decide⟩
    (prefixCache 11 75461) (prefixPartial 11 75461) = false := by
  decide +kernel

theorem node_context_11_75461_1044212 : EJMOriginalGlobalDAGData.nodes 10 ⟨1044212, by decide⟩ =
    .split (coordinate 11) (![⟨1044060, by decide⟩,⟨1044111, by decide⟩,⟨1044164, by decide⟩,⟨1044211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75461_1044212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75461 ⟨1044212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75461
    ⟨1044212, by decide⟩ (by decide) (![⟨1044060, by decide⟩,⟨1044111, by decide⟩,⟨1044164, by decide⟩,⟨1044211, by decide⟩]) unmarked_context_11_75461_1044212 node_context_11_75461_1044212
  intro a
  fin_cases a
  · exact context_12_301844_1044060
  · exact context_12_301845_1044111
  · exact context_12_301846_1044164
  · exact context_12_301847_1044211

theorem selected_cut_38664 : selected 9 ⟨1044258, by decide⟩
    (prefixPartial 12 301848) = some ⟨12, 2, 0, 1044258, 301848, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_301848_1044258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301848 ⟨1044258, by decide⟩ :=
  accepted_of_selected 12 301848 ⟨1044258, by decide⟩ ⟨12, 2, 0, 1044258, 301848, 2905, 65536⟩
    (by decide) selected_cut_38664

theorem selected_cut_38665 : selected 9 ⟨1044305, by decide⟩
    (prefixPartial 12 301849) = some ⟨12, 2, 0, 1044305, 301849, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_301849_1044305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301849 ⟨1044305, by decide⟩ :=
  accepted_of_selected 12 301849 ⟨1044305, by decide⟩ ⟨12, 2, 0, 1044305, 301849, 3317, 65536⟩
    (by decide) selected_cut_38665

theorem selected_cut_38666 : selected 9 ⟨1044351, by decide⟩
    (prefixPartial 12 301850) = some ⟨12, 2, 0, 1044351, 301850, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_301850_1044351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301850 ⟨1044351, by decide⟩ :=
  accepted_of_selected 12 301850 ⟨1044351, by decide⟩ ⟨12, 2, 0, 1044351, 301850, 2873, 65536⟩
    (by decide) selected_cut_38666

theorem selected_cut_38667 : selected 9 ⟨1044395, by decide⟩
    (prefixPartial 12 301851) = some ⟨12, 2, 0, 1044395, 301851, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_301851_1044395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301851 ⟨1044395, by decide⟩ :=
  accepted_of_selected 12 301851 ⟨1044395, by decide⟩ ⟨12, 2, 0, 1044395, 301851, 3221, 65536⟩
    (by decide) selected_cut_38667

theorem unmarked_context_11_75462_1044396 : frontier 10 ⟨1044396, by decide⟩
    (prefixCache 11 75462) (prefixPartial 11 75462) = false := by
  decide +kernel

theorem node_context_11_75462_1044396 : EJMOriginalGlobalDAGData.nodes 10 ⟨1044396, by decide⟩ =
    .split (coordinate 11) (![⟨1044258, by decide⟩,⟨1044305, by decide⟩,⟨1044351, by decide⟩,⟨1044395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75462_1044396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75462 ⟨1044396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75462
    ⟨1044396, by decide⟩ (by decide) (![⟨1044258, by decide⟩,⟨1044305, by decide⟩,⟨1044351, by decide⟩,⟨1044395, by decide⟩]) unmarked_context_11_75462_1044396 node_context_11_75462_1044396
  intro a
  fin_cases a
  · exact context_12_301848_1044258
  · exact context_12_301849_1044305
  · exact context_12_301850_1044351
  · exact context_12_301851_1044395

theorem selected_cut_38668 : selected 9 ⟨1044434, by decide⟩
    (prefixPartial 12 301852) = some ⟨12, 2, 0, 1044434, 301852, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_301852_1044434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301852 ⟨1044434, by decide⟩ :=
  accepted_of_selected 12 301852 ⟨1044434, by decide⟩ ⟨12, 2, 0, 1044434, 301852, 2797, 65536⟩
    (by decide) selected_cut_38668

theorem selected_cut_38669 : selected 9 ⟨1044489, by decide⟩
    (prefixPartial 12 301853) = some ⟨12, 2, 0, 1044489, 301853, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_301853_1044489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301853 ⟨1044489, by decide⟩ :=
  accepted_of_selected 12 301853 ⟨1044489, by decide⟩ ⟨12, 2, 0, 1044489, 301853, 3373, 65536⟩
    (by decide) selected_cut_38669

theorem selected_cut_38670 : selected 9 ⟨1044544, by decide⟩
    (prefixPartial 12 301854) = some ⟨12, 2, 0, 1044544, 301854, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_301854_1044544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301854 ⟨1044544, by decide⟩ :=
  accepted_of_selected 12 301854 ⟨1044544, by decide⟩ ⟨12, 2, 0, 1044544, 301854, 3157, 65536⟩
    (by decide) selected_cut_38670

theorem selected_cut_38671 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 301855) = some ⟨12, 1, 0, 903806, 301855, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301855_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301855 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 301855 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 301855, 1, 65536⟩
    (by decide) selected_cut_38671

theorem unmarked_context_11_75463_1044545 : frontier 10 ⟨1044545, by decide⟩
    (prefixCache 11 75463) (prefixPartial 11 75463) = false := by
  decide +kernel

theorem node_context_11_75463_1044545 : EJMOriginalGlobalDAGData.nodes 10 ⟨1044545, by decide⟩ =
    .split (coordinate 11) (![⟨1044434, by decide⟩,⟨1044489, by decide⟩,⟨1044544, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75463_1044545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75463 ⟨1044545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75463
    ⟨1044545, by decide⟩ (by decide) (![⟨1044434, by decide⟩,⟨1044489, by decide⟩,⟨1044544, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75463_1044545 node_context_11_75463_1044545
  intro a
  fin_cases a
  · exact context_12_301852_1044434
  · exact context_12_301853_1044489
  · exact context_12_301854_1044544
  · exact context_12_301855_903806

theorem unmarked_context_10_18865_1044546 : frontier 11 ⟨1044546, by decide⟩
    (prefixCache 10 18865) (prefixPartial 10 18865) = false := by
  decide +kernel

theorem node_context_10_18865_1044546 : EJMOriginalGlobalDAGData.nodes 11 ⟨1044546, by decide⟩ =
    .split (coordinate 10) (![⟨1044010, by decide⟩,⟨1044212, by decide⟩,⟨1044396, by decide⟩,⟨1044545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18865_1044546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18865 ⟨1044546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18865
    ⟨1044546, by decide⟩ (by decide) (![⟨1044010, by decide⟩,⟨1044212, by decide⟩,⟨1044396, by decide⟩,⟨1044545, by decide⟩]) unmarked_context_10_18865_1044546 node_context_10_18865_1044546
  intro a
  fin_cases a
  · exact context_11_75460_1044010
  · exact context_11_75461_1044212
  · exact context_11_75462_1044396
  · exact context_11_75463_1044545

theorem selected_cut_38672 : selected 9 ⟨1044590, by decide⟩
    (prefixPartial 12 301856) = some ⟨12, 2, 0, 1044590, 301856, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_301856_1044590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301856 ⟨1044590, by decide⟩ :=
  accepted_of_selected 12 301856 ⟨1044590, by decide⟩ ⟨12, 2, 0, 1044590, 301856, 2373, 65536⟩
    (by decide) selected_cut_38672

theorem selected_cut_38673 : selected 9 ⟨1044630, by decide⟩
    (prefixPartial 12 301857) = some ⟨12, 2, 0, 1044630, 301857, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_301857_1044630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301857 ⟨1044630, by decide⟩ :=
  accepted_of_selected 12 301857 ⟨1044630, by decide⟩ ⟨12, 2, 0, 1044630, 301857, 2865, 65536⟩
    (by decide) selected_cut_38673

theorem selected_cut_38674 : selected 9 ⟨1044669, by decide⟩
    (prefixPartial 12 301858) = some ⟨12, 2, 0, 1044669, 301858, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_301858_1044669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301858 ⟨1044669, by decide⟩ :=
  accepted_of_selected 12 301858 ⟨1044669, by decide⟩ ⟨12, 2, 0, 1044669, 301858, 2541, 65536⟩
    (by decide) selected_cut_38674

theorem selected_cut_38675 : selected 9 ⟨1044705, by decide⟩
    (prefixPartial 12 301859) = some ⟨12, 2, 0, 1044705, 301859, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_301859_1044705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301859 ⟨1044705, by decide⟩ :=
  accepted_of_selected 12 301859 ⟨1044705, by decide⟩ ⟨12, 2, 0, 1044705, 301859, 2533, 65536⟩
    (by decide) selected_cut_38675

theorem unmarked_context_11_75464_1044706 : frontier 10 ⟨1044706, by decide⟩
    (prefixCache 11 75464) (prefixPartial 11 75464) = false := by
  decide +kernel

theorem node_context_11_75464_1044706 : EJMOriginalGlobalDAGData.nodes 10 ⟨1044706, by decide⟩ =
    .split (coordinate 11) (![⟨1044590, by decide⟩,⟨1044630, by decide⟩,⟨1044669, by decide⟩,⟨1044705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75464_1044706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75464 ⟨1044706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75464
    ⟨1044706, by decide⟩ (by decide) (![⟨1044590, by decide⟩,⟨1044630, by decide⟩,⟨1044669, by decide⟩,⟨1044705, by decide⟩]) unmarked_context_11_75464_1044706 node_context_11_75464_1044706
  intro a
  fin_cases a
  · exact context_12_301856_1044590
  · exact context_12_301857_1044630
  · exact context_12_301858_1044669
  · exact context_12_301859_1044705

theorem selected_cut_38676 : selected 9 ⟨1044768, by decide⟩
    (prefixPartial 12 301860) = some ⟨12, 2, 0, 1044768, 301860, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_301860_1044768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301860 ⟨1044768, by decide⟩ :=
  accepted_of_selected 12 301860 ⟨1044768, by decide⟩ ⟨12, 2, 0, 1044768, 301860, 2929, 65536⟩
    (by decide) selected_cut_38676

theorem selected_cut_38677 : selected 9 ⟨1044832, by decide⟩
    (prefixPartial 12 301861) = some ⟨12, 2, 0, 1044832, 301861, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_301861_1044832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301861 ⟨1044832, by decide⟩ :=
  accepted_of_selected 12 301861 ⟨1044832, by decide⟩ ⟨12, 2, 0, 1044832, 301861, 3441, 65536⟩
    (by decide) selected_cut_38677

theorem selected_cut_38678 : selected 9 ⟨1044885, by decide⟩
    (prefixPartial 12 301862) = some ⟨12, 2, 0, 1044885, 301862, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_301862_1044885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301862 ⟨1044885, by decide⟩ :=
  accepted_of_selected 12 301862 ⟨1044885, by decide⟩ ⟨12, 2, 0, 1044885, 301862, 2697, 65536⟩
    (by decide) selected_cut_38678

theorem selected_cut_38679 : selected 9 ⟨1044924, by decide⟩
    (prefixPartial 12 301863) = some ⟨12, 2, 0, 1044924, 301863, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_301863_1044924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301863 ⟨1044924, by decide⟩ :=
  accepted_of_selected 12 301863 ⟨1044924, by decide⟩ ⟨12, 2, 0, 1044924, 301863, 2677, 65536⟩
    (by decide) selected_cut_38679

theorem unmarked_context_11_75465_1044925 : frontier 10 ⟨1044925, by decide⟩
    (prefixCache 11 75465) (prefixPartial 11 75465) = false := by
  decide +kernel

theorem node_context_11_75465_1044925 : EJMOriginalGlobalDAGData.nodes 10 ⟨1044925, by decide⟩ =
    .split (coordinate 11) (![⟨1044768, by decide⟩,⟨1044832, by decide⟩,⟨1044885, by decide⟩,⟨1044924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75465_1044925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75465 ⟨1044925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75465
    ⟨1044925, by decide⟩ (by decide) (![⟨1044768, by decide⟩,⟨1044832, by decide⟩,⟨1044885, by decide⟩,⟨1044924, by decide⟩]) unmarked_context_11_75465_1044925 node_context_11_75465_1044925
  intro a
  fin_cases a
  · exact context_12_301860_1044768
  · exact context_12_301861_1044832
  · exact context_12_301862_1044885
  · exact context_12_301863_1044924

theorem selected_cut_38680 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75466) = some ⟨11, 1, 0, 900587, 75466, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75466_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75466 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75466 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75466, 1, 262144⟩
    (by decide) selected_cut_38680

theorem selected_cut_38681 : selected 9 ⟨1044970, by decide⟩
    (prefixPartial 12 301868) = some ⟨12, 2, 0, 1044970, 301868, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_301868_1044970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301868 ⟨1044970, by decide⟩ :=
  accepted_of_selected 12 301868 ⟨1044970, by decide⟩ ⟨12, 2, 0, 1044970, 301868, 2517, 65536⟩
    (by decide) selected_cut_38681

theorem selected_cut_38682 : selected 9 ⟨1045026, by decide⟩
    (prefixPartial 12 301869) = some ⟨12, 2, 0, 1045026, 301869, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_301869_1045026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301869 ⟨1045026, by decide⟩ :=
  accepted_of_selected 12 301869 ⟨1045026, by decide⟩ ⟨12, 2, 0, 1045026, 301869, 3165, 65536⟩
    (by decide) selected_cut_38682

theorem selected_cut_38683 : selected 9 ⟨1045071, by decide⟩
    (prefixPartial 12 301870) = some ⟨12, 2, 0, 1045071, 301870, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_301870_1045071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301870 ⟨1045071, by decide⟩ :=
  accepted_of_selected 12 301870 ⟨1045071, by decide⟩ ⟨12, 2, 0, 1045071, 301870, 2745, 65536⟩
    (by decide) selected_cut_38683

theorem selected_cut_38684 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 301871) = some ⟨12, 1, 0, 903806, 301871, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301871_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301871 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 301871 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 301871, 1, 65536⟩
    (by decide) selected_cut_38684

theorem unmarked_context_11_75467_1045072 : frontier 10 ⟨1045072, by decide⟩
    (prefixCache 11 75467) (prefixPartial 11 75467) = false := by
  decide +kernel

theorem node_context_11_75467_1045072 : EJMOriginalGlobalDAGData.nodes 10 ⟨1045072, by decide⟩ =
    .split (coordinate 11) (![⟨1044970, by decide⟩,⟨1045026, by decide⟩,⟨1045071, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75467_1045072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75467 ⟨1045072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75467
    ⟨1045072, by decide⟩ (by decide) (![⟨1044970, by decide⟩,⟨1045026, by decide⟩,⟨1045071, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75467_1045072 node_context_11_75467_1045072
  intro a
  fin_cases a
  · exact context_12_301868_1044970
  · exact context_12_301869_1045026
  · exact context_12_301870_1045071
  · exact context_12_301871_903806

theorem unmarked_context_10_18866_1045073 : frontier 11 ⟨1045073, by decide⟩
    (prefixCache 10 18866) (prefixPartial 10 18866) = false := by
  decide +kernel

theorem node_context_10_18866_1045073 : EJMOriginalGlobalDAGData.nodes 11 ⟨1045073, by decide⟩ =
    .split (coordinate 10) (![⟨1044706, by decide⟩,⟨1044925, by decide⟩,⟨900587, by decide⟩,⟨1045072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18866_1045073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18866 ⟨1045073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18866
    ⟨1045073, by decide⟩ (by decide) (![⟨1044706, by decide⟩,⟨1044925, by decide⟩,⟨900587, by decide⟩,⟨1045072, by decide⟩]) unmarked_context_10_18866_1045073 node_context_10_18866_1045073
  intro a
  fin_cases a
  · exact context_11_75464_1044706
  · exact context_11_75465_1044925
  · exact context_11_75466_900587
  · exact context_11_75467_1045072

theorem selected_cut_38685 : selected 9 ⟨1045117, by decide⟩
    (prefixPartial 12 301872) = some ⟨12, 2, 0, 1045117, 301872, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_301872_1045117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301872 ⟨1045117, by decide⟩ :=
  accepted_of_selected 12 301872 ⟨1045117, by decide⟩ ⟨12, 2, 0, 1045117, 301872, 1505, 65536⟩
    (by decide) selected_cut_38685

theorem selected_cut_38686 : selected 9 ⟨1045169, by decide⟩
    (prefixPartial 12 301873) = some ⟨12, 2, 0, 1045169, 301873, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_301873_1045169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301873 ⟨1045169, by decide⟩ :=
  accepted_of_selected 12 301873 ⟨1045169, by decide⟩ ⟨12, 2, 0, 1045169, 301873, 3213, 65536⟩
    (by decide) selected_cut_38686

theorem selected_cut_38687 : selected 9 ⟨1045216, by decide⟩
    (prefixPartial 12 301874) = some ⟨12, 2, 0, 1045216, 301874, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_301874_1045216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301874 ⟨1045216, by decide⟩ :=
  accepted_of_selected 12 301874 ⟨1045216, by decide⟩ ⟨12, 2, 0, 1045216, 301874, 2841, 65536⟩
    (by decide) selected_cut_38687

theorem selected_cut_38688 : selected 9 ⟨1045261, by decide⟩
    (prefixPartial 12 301875) = some ⟨12, 2, 0, 1045261, 301875, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_301875_1045261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301875 ⟨1045261, by decide⟩ :=
  accepted_of_selected 12 301875 ⟨1045261, by decide⟩ ⟨12, 2, 0, 1045261, 301875, 2745, 65536⟩
    (by decide) selected_cut_38688

theorem unmarked_context_11_75468_1045262 : frontier 10 ⟨1045262, by decide⟩
    (prefixCache 11 75468) (prefixPartial 11 75468) = false := by
  decide +kernel

theorem node_context_11_75468_1045262 : EJMOriginalGlobalDAGData.nodes 10 ⟨1045262, by decide⟩ =
    .split (coordinate 11) (![⟨1045117, by decide⟩,⟨1045169, by decide⟩,⟨1045216, by decide⟩,⟨1045261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75468_1045262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75468 ⟨1045262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75468
    ⟨1045262, by decide⟩ (by decide) (![⟨1045117, by decide⟩,⟨1045169, by decide⟩,⟨1045216, by decide⟩,⟨1045261, by decide⟩]) unmarked_context_11_75468_1045262 node_context_11_75468_1045262
  intro a
  fin_cases a
  · exact context_12_301872_1045117
  · exact context_12_301873_1045169
  · exact context_12_301874_1045216
  · exact context_12_301875_1045261

theorem selected_cut_38689 : selected 9 ⟨1045313, by decide⟩
    (prefixPartial 12 301876) = some ⟨12, 2, 0, 1045313, 301876, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_301876_1045313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301876 ⟨1045313, by decide⟩ :=
  accepted_of_selected 12 301876 ⟨1045313, by decide⟩ ⟨12, 2, 0, 1045313, 301876, 2933, 65536⟩
    (by decide) selected_cut_38689

theorem selected_cut_38690 : selected 9 ⟨1045378, by decide⟩
    (prefixPartial 12 301877) = some ⟨12, 2, 0, 1045378, 301877, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_301877_1045378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301877 ⟨1045378, by decide⟩ :=
  accepted_of_selected 12 301877 ⟨1045378, by decide⟩ ⟨12, 2, 0, 1045378, 301877, 3505, 65536⟩
    (by decide) selected_cut_38690

theorem selected_cut_38691 : selected 9 ⟨1045436, by decide⟩
    (prefixPartial 12 301878) = some ⟨12, 2, 0, 1045436, 301878, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_301878_1045436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301878 ⟨1045436, by decide⟩ :=
  accepted_of_selected 12 301878 ⟨1045436, by decide⟩ ⟨12, 2, 0, 1045436, 301878, 2985, 65536⟩
    (by decide) selected_cut_38691

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
