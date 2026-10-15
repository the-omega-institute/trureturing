/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover039
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03842 : selected 8 ⟨123354, by decide⟩
    (prefixPartial 13 70667) = some ⟨13, 2, 0, 123354, 70667, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_70667_123354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70667 ⟨123354, by decide⟩ :=
  accepted_of_selected 13 70667 ⟨123354, by decide⟩ ⟨13, 2, 0, 123354, 70667, 1145, 16384⟩
    (by decide) selected_cut_03842

theorem unmarked_context_12_17666_123355 : frontier 9 ⟨123355, by decide⟩
    (prefixCache 12 17666) (prefixPartial 12 17666) = false := by
  decide +kernel

theorem node_context_12_17666_123355 : EJMOriginalGlobalDAGData.nodes 9 ⟨123355, by decide⟩ =
    .split (coordinate 12) (![⟨123240, by decide⟩,⟨123290, by decide⟩,⟨123332, by decide⟩,⟨123354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17666_123355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17666 ⟨123355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17666
    ⟨123355, by decide⟩ (by decide) (![⟨123240, by decide⟩,⟨123290, by decide⟩,⟨123332, by decide⟩,⟨123354, by decide⟩]) unmarked_context_12_17666_123355 node_context_12_17666_123355
  intro a
  fin_cases a
  · exact context_13_70664_123240
  · exact context_13_70665_123290
  · exact context_13_70666_123332
  · exact context_13_70667_123354

theorem selected_cut_03843 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17667) = some ⟨12, 1, 0, 893, 17667, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17667_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17667 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17667 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17667, 1, 65536⟩
    (by decide) selected_cut_03843

theorem unmarked_context_11_4416_123356 : frontier 10 ⟨123356, by decide⟩
    (prefixCache 11 4416) (prefixPartial 11 4416) = false := by
  decide +kernel

theorem node_context_11_4416_123356 : EJMOriginalGlobalDAGData.nodes 10 ⟨123356, by decide⟩ =
    .split (coordinate 11) (![⟨123043, by decide⟩,⟨123141, by decide⟩,⟨123355, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4416_123356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4416 ⟨123356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4416
    ⟨123356, by decide⟩ (by decide) (![⟨123043, by decide⟩,⟨123141, by decide⟩,⟨123355, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4416_123356 node_context_11_4416_123356
  intro a
  fin_cases a
  · exact context_12_17664_123043
  · exact context_12_17665_123141
  · exact context_12_17666_123355
  · exact context_12_17667_893

theorem selected_cut_03844 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17668) = some ⟨12, 1, 0, 895, 17668, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17668_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17668 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17668 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17668, 1, 65536⟩
    (by decide) selected_cut_03844

theorem selected_cut_03845 : selected 8 ⟨123425, by decide⟩
    (prefixPartial 13 70676) = some ⟨13, 2, 0, 123425, 70676, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_70676_123425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70676 ⟨123425, by decide⟩ :=
  accepted_of_selected 13 70676 ⟨123425, by decide⟩ ⟨13, 2, 0, 123425, 70676, 2425, 16384⟩
    (by decide) selected_cut_03845

theorem selected_cut_03846 : selected 8 ⟨123477, by decide⟩
    (prefixPartial 13 70677) = some ⟨13, 2, 0, 123477, 70677, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_70677_123477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70677 ⟨123477, by decide⟩ :=
  accepted_of_selected 13 70677 ⟨123477, by decide⟩ ⟨13, 2, 0, 123477, 70677, 1413, 16384⟩
    (by decide) selected_cut_03846

theorem selected_cut_03847 : selected 8 ⟨123491, by decide⟩
    (prefixPartial 13 70678) = some ⟨13, 2, 0, 123491, 70678, 545, 16384⟩ := by
  decide +kernel

theorem context_13_70678_123491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70678 ⟨123491, by decide⟩ :=
  accepted_of_selected 13 70678 ⟨123491, by decide⟩ ⟨13, 2, 0, 123491, 70678, 545, 16384⟩
    (by decide) selected_cut_03847

theorem selected_cut_03848 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 70679) = some ⟨13, 1, 0, 414, 70679, 1, 16384⟩ := by
  decide +kernel

theorem context_13_70679_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70679 ⟨414, by decide⟩ :=
  accepted_of_selected 13 70679 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 70679, 1, 16384⟩
    (by decide) selected_cut_03848

theorem unmarked_context_12_17669_123492 : frontier 9 ⟨123492, by decide⟩
    (prefixCache 12 17669) (prefixPartial 12 17669) = false := by
  decide +kernel

theorem node_context_12_17669_123492 : EJMOriginalGlobalDAGData.nodes 9 ⟨123492, by decide⟩ =
    .split (coordinate 12) (![⟨123425, by decide⟩,⟨123477, by decide⟩,⟨123491, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17669_123492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17669 ⟨123492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17669
    ⟨123492, by decide⟩ (by decide) (![⟨123425, by decide⟩,⟨123477, by decide⟩,⟨123491, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_17669_123492 node_context_12_17669_123492
  intro a
  fin_cases a
  · exact context_13_70676_123425
  · exact context_13_70677_123477
  · exact context_13_70678_123491
  · exact context_13_70679_414

theorem selected_cut_03849 : selected 8 ⟨123560, by decide⟩
    (prefixPartial 13 70680) = some ⟨13, 2, 0, 123560, 70680, 3897, 16384⟩ := by
  decide +kernel

theorem context_13_70680_123560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70680 ⟨123560, by decide⟩ :=
  accepted_of_selected 13 70680 ⟨123560, by decide⟩ ⟨13, 2, 0, 123560, 70680, 3897, 16384⟩
    (by decide) selected_cut_03849

theorem selected_cut_03850 : selected 8 ⟨123614, by decide⟩
    (prefixPartial 13 70681) = some ⟨13, 2, 0, 123614, 70681, 3441, 16384⟩ := by
  decide +kernel

theorem context_13_70681_123614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70681 ⟨123614, by decide⟩ :=
  accepted_of_selected 13 70681 ⟨123614, by decide⟩ ⟨13, 2, 0, 123614, 70681, 3441, 16384⟩
    (by decide) selected_cut_03850

theorem selected_cut_03851 : selected 8 ⟨123645, by decide⟩
    (prefixPartial 13 70682) = some ⟨13, 2, 0, 123645, 70682, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_70682_123645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70682 ⟨123645, by decide⟩ :=
  accepted_of_selected 13 70682 ⟨123645, by decide⟩ ⟨13, 2, 0, 123645, 70682, 2309, 16384⟩
    (by decide) selected_cut_03851

theorem selected_cut_03852 : selected 8 ⟨123658, by decide⟩
    (prefixPartial 13 70683) = some ⟨13, 2, 0, 123658, 70683, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_70683_123658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70683 ⟨123658, by decide⟩ :=
  accepted_of_selected 13 70683 ⟨123658, by decide⟩ ⟨13, 2, 0, 123658, 70683, 1157, 16384⟩
    (by decide) selected_cut_03852

theorem unmarked_context_12_17670_123659 : frontier 9 ⟨123659, by decide⟩
    (prefixCache 12 17670) (prefixPartial 12 17670) = false := by
  decide +kernel

theorem node_context_12_17670_123659 : EJMOriginalGlobalDAGData.nodes 9 ⟨123659, by decide⟩ =
    .split (coordinate 12) (![⟨123560, by decide⟩,⟨123614, by decide⟩,⟨123645, by decide⟩,⟨123658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17670_123659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17670 ⟨123659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17670
    ⟨123659, by decide⟩ (by decide) (![⟨123560, by decide⟩,⟨123614, by decide⟩,⟨123645, by decide⟩,⟨123658, by decide⟩]) unmarked_context_12_17670_123659 node_context_12_17670_123659
  intro a
  fin_cases a
  · exact context_13_70680_123560
  · exact context_13_70681_123614
  · exact context_13_70682_123645
  · exact context_13_70683_123658

theorem selected_cut_03853 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17671) = some ⟨12, 1, 0, 893, 17671, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17671_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17671 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17671 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17671, 1, 65536⟩
    (by decide) selected_cut_03853

theorem unmarked_context_11_4417_123660 : frontier 10 ⟨123660, by decide⟩
    (prefixCache 11 4417) (prefixPartial 11 4417) = false := by
  decide +kernel

theorem node_context_11_4417_123660 : EJMOriginalGlobalDAGData.nodes 10 ⟨123660, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨123492, by decide⟩,⟨123659, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4417_123660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4417 ⟨123660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4417
    ⟨123660, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨123492, by decide⟩,⟨123659, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4417_123660 node_context_11_4417_123660
  intro a
  fin_cases a
  · exact context_12_17668_895
  · exact context_12_17669_123492
  · exact context_12_17670_123659
  · exact context_12_17671_893

theorem selected_cut_03854 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17672) = some ⟨12, 1, 0, 895, 17672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17672_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17672 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17672 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17672, 1, 65536⟩
    (by decide) selected_cut_03854

theorem selected_cut_03855 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17673) = some ⟨12, 1, 0, 895, 17673, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17673_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17673 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17673 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17673, 1, 65536⟩
    (by decide) selected_cut_03855

theorem selected_cut_03856 : selected 8 ⟨123740, by decide⟩
    (prefixPartial 13 70696) = some ⟨13, 2, 0, 123740, 70696, 3473, 16384⟩ := by
  decide +kernel

theorem context_13_70696_123740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70696 ⟨123740, by decide⟩ :=
  accepted_of_selected 13 70696 ⟨123740, by decide⟩ ⟨13, 2, 0, 123740, 70696, 3473, 16384⟩
    (by decide) selected_cut_03856

theorem selected_cut_03857 : selected 8 ⟨123790, by decide⟩
    (prefixPartial 13 70697) = some ⟨13, 2, 0, 123790, 70697, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_70697_123790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70697 ⟨123790, by decide⟩ :=
  accepted_of_selected 13 70697 ⟨123790, by decide⟩ ⟨13, 2, 0, 123790, 70697, 1837, 16384⟩
    (by decide) selected_cut_03857

theorem selected_cut_03858 : selected 8 ⟨123805, by decide⟩
    (prefixPartial 13 70698) = some ⟨13, 2, 0, 123805, 70698, 625, 16384⟩ := by
  decide +kernel

theorem context_13_70698_123805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70698 ⟨123805, by decide⟩ :=
  accepted_of_selected 13 70698 ⟨123805, by decide⟩ ⟨13, 2, 0, 123805, 70698, 625, 16384⟩
    (by decide) selected_cut_03858

theorem selected_cut_03859 : selected 8 ⟨123809, by decide⟩
    (prefixPartial 13 70699) = some ⟨13, 2, 0, 123809, 70699, 113, 16384⟩ := by
  decide +kernel

theorem context_13_70699_123809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70699 ⟨123809, by decide⟩ :=
  accepted_of_selected 13 70699 ⟨123809, by decide⟩ ⟨13, 2, 0, 123809, 70699, 113, 16384⟩
    (by decide) selected_cut_03859

theorem unmarked_context_12_17674_123810 : frontier 9 ⟨123810, by decide⟩
    (prefixCache 12 17674) (prefixPartial 12 17674) = false := by
  decide +kernel

theorem node_context_12_17674_123810 : EJMOriginalGlobalDAGData.nodes 9 ⟨123810, by decide⟩ =
    .split (coordinate 12) (![⟨123740, by decide⟩,⟨123790, by decide⟩,⟨123805, by decide⟩,⟨123809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17674_123810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17674 ⟨123810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17674
    ⟨123810, by decide⟩ (by decide) (![⟨123740, by decide⟩,⟨123790, by decide⟩,⟨123805, by decide⟩,⟨123809, by decide⟩]) unmarked_context_12_17674_123810 node_context_12_17674_123810
  intro a
  fin_cases a
  · exact context_13_70696_123740
  · exact context_13_70697_123790
  · exact context_13_70698_123805
  · exact context_13_70699_123809

theorem selected_cut_03860 : selected 8 ⟨123900, by decide⟩
    (prefixPartial 13 70700) = some ⟨13, 2, 0, 123900, 70700, 3725, 16384⟩ := by
  decide +kernel

theorem context_13_70700_123900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70700 ⟨123900, by decide⟩ :=
  accepted_of_selected 13 70700 ⟨123900, by decide⟩ ⟨13, 2, 0, 123900, 70700, 3725, 16384⟩
    (by decide) selected_cut_03860

theorem selected_cut_03861 : selected 8 ⟨123965, by decide⟩
    (prefixPartial 13 70701) = some ⟨13, 2, 0, 123965, 70701, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_70701_123965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70701 ⟨123965, by decide⟩ :=
  accepted_of_selected 13 70701 ⟨123965, by decide⟩ ⟨13, 2, 0, 123965, 70701, 2033, 16384⟩
    (by decide) selected_cut_03861

theorem selected_cut_03862 : selected 8 ⟨123981, by decide⟩
    (prefixPartial 13 70702) = some ⟨13, 2, 0, 123981, 70702, 641, 16384⟩ := by
  decide +kernel

theorem context_13_70702_123981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70702 ⟨123981, by decide⟩ :=
  accepted_of_selected 13 70702 ⟨123981, by decide⟩ ⟨13, 2, 0, 123981, 70702, 641, 16384⟩
    (by decide) selected_cut_03862

theorem selected_cut_03863 : selected 8 ⟨123989, by decide⟩
    (prefixPartial 13 70703) = some ⟨13, 2, 0, 123989, 70703, 137, 16384⟩ := by
  decide +kernel

theorem context_13_70703_123989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70703 ⟨123989, by decide⟩ :=
  accepted_of_selected 13 70703 ⟨123989, by decide⟩ ⟨13, 2, 0, 123989, 70703, 137, 16384⟩
    (by decide) selected_cut_03863

theorem unmarked_context_12_17675_123990 : frontier 9 ⟨123990, by decide⟩
    (prefixCache 12 17675) (prefixPartial 12 17675) = false := by
  decide +kernel

theorem node_context_12_17675_123990 : EJMOriginalGlobalDAGData.nodes 9 ⟨123990, by decide⟩ =
    .split (coordinate 12) (![⟨123900, by decide⟩,⟨123965, by decide⟩,⟨123981, by decide⟩,⟨123989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17675_123990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17675 ⟨123990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17675
    ⟨123990, by decide⟩ (by decide) (![⟨123900, by decide⟩,⟨123965, by decide⟩,⟨123981, by decide⟩,⟨123989, by decide⟩]) unmarked_context_12_17675_123990 node_context_12_17675_123990
  intro a
  fin_cases a
  · exact context_13_70700_123900
  · exact context_13_70701_123965
  · exact context_13_70702_123981
  · exact context_13_70703_123989

theorem unmarked_context_11_4418_123991 : frontier 10 ⟨123991, by decide⟩
    (prefixCache 11 4418) (prefixPartial 11 4418) = false := by
  decide +kernel

theorem node_context_11_4418_123991 : EJMOriginalGlobalDAGData.nodes 10 ⟨123991, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨123810, by decide⟩,⟨123990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4418_123991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4418 ⟨123991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4418
    ⟨123991, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨123810, by decide⟩,⟨123990, by decide⟩]) unmarked_context_11_4418_123991 node_context_11_4418_123991
  intro a
  fin_cases a
  · exact context_12_17672_895
  · exact context_12_17673_895
  · exact context_12_17674_123810
  · exact context_12_17675_123990

theorem selected_cut_03864 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 4419) = some ⟨11, 1, 0, 1736, 4419, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4419_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4419 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 4419 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 4419, 1, 262144⟩
    (by decide) selected_cut_03864

theorem unmarked_context_10_1104_123992 : frontier 11 ⟨123992, by decide⟩
    (prefixCache 10 1104) (prefixPartial 10 1104) = false := by
  decide +kernel

theorem node_context_10_1104_123992 : EJMOriginalGlobalDAGData.nodes 11 ⟨123992, by decide⟩ =
    .split (coordinate 10) (![⟨123356, by decide⟩,⟨123660, by decide⟩,⟨123991, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1104_123992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1104 ⟨123992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1104
    ⟨123992, by decide⟩ (by decide) (![⟨123356, by decide⟩,⟨123660, by decide⟩,⟨123991, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1104_123992 node_context_10_1104_123992
  intro a
  fin_cases a
  · exact context_11_4416_123356
  · exact context_11_4417_123660
  · exact context_11_4418_123991
  · exact context_11_4419_1736

theorem selected_cut_03865 : selected 9 ⟨124065, by decide⟩
    (prefixPartial 12 17680) = some ⟨12, 2, 0, 124065, 17680, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_17680_124065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17680 ⟨124065, by decide⟩ :=
  accepted_of_selected 12 17680 ⟨124065, by decide⟩ ⟨12, 2, 0, 124065, 17680, 3553, 65536⟩
    (by decide) selected_cut_03865

theorem selected_cut_03866 : selected 9 ⟨124125, by decide⟩
    (prefixPartial 12 17681) = some ⟨12, 2, 0, 124125, 17681, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_17681_124125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17681 ⟨124125, by decide⟩ :=
  accepted_of_selected 12 17681 ⟨124125, by decide⟩ ⟨12, 2, 0, 124125, 17681, 2629, 65536⟩
    (by decide) selected_cut_03866

theorem selected_cut_03867 : selected 8 ⟨124166, by decide⟩
    (prefixPartial 13 70728) = some ⟨13, 2, 0, 124166, 70728, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_70728_124166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70728 ⟨124166, by decide⟩ :=
  accepted_of_selected 13 70728 ⟨124166, by decide⟩ ⟨13, 2, 0, 124166, 70728, 2401, 16384⟩
    (by decide) selected_cut_03867

theorem selected_cut_03868 : selected 8 ⟨124191, by decide⟩
    (prefixPartial 13 70729) = some ⟨13, 2, 0, 124191, 70729, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_70729_124191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70729 ⟨124191, by decide⟩ :=
  accepted_of_selected 13 70729 ⟨124191, by decide⟩ ⟨13, 2, 0, 124191, 70729, 1457, 16384⟩
    (by decide) selected_cut_03868

theorem selected_cut_03869 : selected 8 ⟨124208, by decide⟩
    (prefixPartial 13 70730) = some ⟨13, 2, 0, 124208, 70730, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_70730_124208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70730 ⟨124208, by decide⟩ :=
  accepted_of_selected 13 70730 ⟨124208, by decide⟩ ⟨13, 2, 0, 124208, 70730, 1533, 16384⟩
    (by decide) selected_cut_03869

theorem selected_cut_03870 : selected 8 ⟨124221, by decide⟩
    (prefixPartial 13 70731) = some ⟨13, 2, 0, 124221, 70731, 865, 16384⟩ := by
  decide +kernel

theorem context_13_70731_124221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70731 ⟨124221, by decide⟩ :=
  accepted_of_selected 13 70731 ⟨124221, by decide⟩ ⟨13, 2, 0, 124221, 70731, 865, 16384⟩
    (by decide) selected_cut_03870

theorem unmarked_context_12_17682_124222 : frontier 9 ⟨124222, by decide⟩
    (prefixCache 12 17682) (prefixPartial 12 17682) = false := by
  decide +kernel

theorem node_context_12_17682_124222 : EJMOriginalGlobalDAGData.nodes 9 ⟨124222, by decide⟩ =
    .split (coordinate 12) (![⟨124166, by decide⟩,⟨124191, by decide⟩,⟨124208, by decide⟩,⟨124221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17682_124222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17682 ⟨124222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17682
    ⟨124222, by decide⟩ (by decide) (![⟨124166, by decide⟩,⟨124191, by decide⟩,⟨124208, by decide⟩,⟨124221, by decide⟩]) unmarked_context_12_17682_124222 node_context_12_17682_124222
  intro a
  fin_cases a
  · exact context_13_70728_124166
  · exact context_13_70729_124191
  · exact context_13_70730_124208
  · exact context_13_70731_124221

theorem selected_cut_03871 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17683) = some ⟨12, 1, 0, 893, 17683, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17683_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17683 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17683 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17683, 1, 65536⟩
    (by decide) selected_cut_03871

theorem unmarked_context_11_4420_124223 : frontier 10 ⟨124223, by decide⟩
    (prefixCache 11 4420) (prefixPartial 11 4420) = false := by
  decide +kernel

theorem node_context_11_4420_124223 : EJMOriginalGlobalDAGData.nodes 10 ⟨124223, by decide⟩ =
    .split (coordinate 11) (![⟨124065, by decide⟩,⟨124125, by decide⟩,⟨124222, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4420_124223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4420 ⟨124223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4420
    ⟨124223, by decide⟩ (by decide) (![⟨124065, by decide⟩,⟨124125, by decide⟩,⟨124222, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4420_124223 node_context_11_4420_124223
  intro a
  fin_cases a
  · exact context_12_17680_124065
  · exact context_12_17681_124125
  · exact context_12_17682_124222
  · exact context_12_17683_893

theorem selected_cut_03872 : selected 8 ⟨124252, by decide⟩
    (prefixPartial 13 70736) = some ⟨13, 2, 0, 124252, 70736, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_70736_124252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70736 ⟨124252, by decide⟩ :=
  accepted_of_selected 13 70736 ⟨124252, by decide⟩ ⟨13, 2, 0, 124252, 70736, 1137, 16384⟩
    (by decide) selected_cut_03872

theorem selected_cut_03873 : selected 8 ⟨124286, by decide⟩
    (prefixPartial 13 70737) = some ⟨13, 2, 0, 124286, 70737, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_70737_124286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70737 ⟨124286, by decide⟩ :=
  accepted_of_selected 13 70737 ⟨124286, by decide⟩ ⟨13, 2, 0, 124286, 70737, 1341, 16384⟩
    (by decide) selected_cut_03873

theorem selected_cut_03874 : selected 8 ⟨124306, by decide⟩
    (prefixPartial 13 70738) = some ⟨13, 2, 0, 124306, 70738, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_70738_124306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70738 ⟨124306, by decide⟩ :=
  accepted_of_selected 13 70738 ⟨124306, by decide⟩ ⟨13, 2, 0, 124306, 70738, 1677, 16384⟩
    (by decide) selected_cut_03874

theorem selected_cut_03875 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 70739) = some ⟨13, 1, 0, 414, 70739, 1, 16384⟩ := by
  decide +kernel

theorem context_13_70739_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70739 ⟨414, by decide⟩ :=
  accepted_of_selected 13 70739 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 70739, 1, 16384⟩
    (by decide) selected_cut_03875

theorem unmarked_context_12_17684_124307 : frontier 9 ⟨124307, by decide⟩
    (prefixCache 12 17684) (prefixPartial 12 17684) = false := by
  decide +kernel

theorem node_context_12_17684_124307 : EJMOriginalGlobalDAGData.nodes 9 ⟨124307, by decide⟩ =
    .split (coordinate 12) (![⟨124252, by decide⟩,⟨124286, by decide⟩,⟨124306, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17684_124307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17684 ⟨124307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17684
    ⟨124307, by decide⟩ (by decide) (![⟨124252, by decide⟩,⟨124286, by decide⟩,⟨124306, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_17684_124307 node_context_12_17684_124307
  intro a
  fin_cases a
  · exact context_13_70736_124252
  · exact context_13_70737_124286
  · exact context_13_70738_124306
  · exact context_13_70739_414

theorem selected_cut_03876 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 17685) = some ⟨12, 1, 0, 124308, 17685, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17685_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17685 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 17685 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 17685, 1, 65536⟩
    (by decide) selected_cut_03876

theorem selected_cut_03877 : selected 8 ⟨124389, by decide⟩
    (prefixPartial 13 70744) = some ⟨13, 2, 0, 124389, 70744, 3361, 16384⟩ := by
  decide +kernel

theorem context_13_70744_124389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70744 ⟨124389, by decide⟩ :=
  accepted_of_selected 13 70744 ⟨124389, by decide⟩ ⟨13, 2, 0, 124389, 70744, 3361, 16384⟩
    (by decide) selected_cut_03877

theorem selected_cut_03878 : selected 8 ⟨124450, by decide⟩
    (prefixPartial 13 70745) = some ⟨13, 2, 0, 124450, 70745, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_70745_124450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70745 ⟨124450, by decide⟩ :=
  accepted_of_selected 13 70745 ⟨124450, by decide⟩ ⟨13, 2, 0, 124450, 70745, 2801, 16384⟩
    (by decide) selected_cut_03878

theorem selected_cut_03879 : selected 8 ⟨124475, by decide⟩
    (prefixPartial 13 70746) = some ⟨13, 2, 0, 124475, 70746, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_70746_124475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70746 ⟨124475, by decide⟩ :=
  accepted_of_selected 13 70746 ⟨124475, by decide⟩ ⟨13, 2, 0, 124475, 70746, 1793, 16384⟩
    (by decide) selected_cut_03879

theorem selected_cut_03880 : selected 8 ⟨124490, by decide⟩
    (prefixPartial 13 70747) = some ⟨13, 2, 0, 124490, 70747, 989, 16384⟩ := by
  decide +kernel

theorem context_13_70747_124490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70747 ⟨124490, by decide⟩ :=
  accepted_of_selected 13 70747 ⟨124490, by decide⟩ ⟨13, 2, 0, 124490, 70747, 989, 16384⟩
    (by decide) selected_cut_03880

theorem unmarked_context_12_17686_124491 : frontier 9 ⟨124491, by decide⟩
    (prefixCache 12 17686) (prefixPartial 12 17686) = false := by
  decide +kernel

theorem node_context_12_17686_124491 : EJMOriginalGlobalDAGData.nodes 9 ⟨124491, by decide⟩ =
    .split (coordinate 12) (![⟨124389, by decide⟩,⟨124450, by decide⟩,⟨124475, by decide⟩,⟨124490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17686_124491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17686 ⟨124491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17686
    ⟨124491, by decide⟩ (by decide) (![⟨124389, by decide⟩,⟨124450, by decide⟩,⟨124475, by decide⟩,⟨124490, by decide⟩]) unmarked_context_12_17686_124491 node_context_12_17686_124491
  intro a
  fin_cases a
  · exact context_13_70744_124389
  · exact context_13_70745_124450
  · exact context_13_70746_124475
  · exact context_13_70747_124490

theorem selected_cut_03881 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17687) = some ⟨12, 1, 0, 893, 17687, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17687_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17687 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17687 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17687, 1, 65536⟩
    (by decide) selected_cut_03881

theorem unmarked_context_11_4421_124492 : frontier 10 ⟨124492, by decide⟩
    (prefixCache 11 4421) (prefixPartial 11 4421) = false := by
  decide +kernel

theorem node_context_11_4421_124492 : EJMOriginalGlobalDAGData.nodes 10 ⟨124492, by decide⟩ =
    .split (coordinate 11) (![⟨124307, by decide⟩,⟨124308, by decide⟩,⟨124491, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4421_124492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4421 ⟨124492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4421
    ⟨124492, by decide⟩ (by decide) (![⟨124307, by decide⟩,⟨124308, by decide⟩,⟨124491, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4421_124492 node_context_11_4421_124492
  intro a
  fin_cases a
  · exact context_12_17684_124307
  · exact context_12_17685_124308
  · exact context_12_17686_124491
  · exact context_12_17687_893

theorem selected_cut_03882 : selected 8 ⟨124523, by decide⟩
    (prefixPartial 13 70752) = some ⟨13, 2, 0, 124523, 70752, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_70752_124523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70752 ⟨124523, by decide⟩ :=
  accepted_of_selected 13 70752 ⟨124523, by decide⟩ ⟨13, 2, 0, 124523, 70752, 1377, 16384⟩
    (by decide) selected_cut_03882

theorem selected_cut_03883 : selected 8 ⟨124551, by decide⟩
    (prefixPartial 13 70753) = some ⟨13, 2, 0, 124551, 70753, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_70753_124551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70753 ⟨124551, by decide⟩ :=
  accepted_of_selected 13 70753 ⟨124551, by decide⟩ ⟨13, 2, 0, 124551, 70753, 1629, 16384⟩
    (by decide) selected_cut_03883

theorem selected_cut_03884 : selected 8 ⟨124576, by decide⟩
    (prefixPartial 13 70754) = some ⟨13, 2, 0, 124576, 70754, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_70754_124576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70754 ⟨124576, by decide⟩ :=
  accepted_of_selected 13 70754 ⟨124576, by decide⟩ ⟨13, 2, 0, 124576, 70754, 1537, 16384⟩
    (by decide) selected_cut_03884

theorem selected_cut_03885 : selected 8 ⟨124586, by decide⟩
    (prefixPartial 13 70755) = some ⟨13, 2, 0, 124586, 70755, 893, 16384⟩ := by
  decide +kernel

theorem context_13_70755_124586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70755 ⟨124586, by decide⟩ :=
  accepted_of_selected 13 70755 ⟨124586, by decide⟩ ⟨13, 2, 0, 124586, 70755, 893, 16384⟩
    (by decide) selected_cut_03885

theorem unmarked_context_12_17688_124587 : frontier 9 ⟨124587, by decide⟩
    (prefixCache 12 17688) (prefixPartial 12 17688) = false := by
  decide +kernel

theorem node_context_12_17688_124587 : EJMOriginalGlobalDAGData.nodes 9 ⟨124587, by decide⟩ =
    .split (coordinate 12) (![⟨124523, by decide⟩,⟨124551, by decide⟩,⟨124576, by decide⟩,⟨124586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17688_124587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17688 ⟨124587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17688
    ⟨124587, by decide⟩ (by decide) (![⟨124523, by decide⟩,⟨124551, by decide⟩,⟨124576, by decide⟩,⟨124586, by decide⟩]) unmarked_context_12_17688_124587 node_context_12_17688_124587
  intro a
  fin_cases a
  · exact context_13_70752_124523
  · exact context_13_70753_124551
  · exact context_13_70754_124576
  · exact context_13_70755_124586

theorem selected_cut_03886 : selected 8 ⟨124626, by decide⟩
    (prefixPartial 13 70756) = some ⟨13, 2, 0, 124626, 70756, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_70756_124626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70756 ⟨124626, by decide⟩ :=
  accepted_of_selected 13 70756 ⟨124626, by decide⟩ ⟨13, 2, 0, 124626, 70756, 1745, 16384⟩
    (by decide) selected_cut_03886

theorem selected_cut_03887 : selected 8 ⟨124647, by decide⟩
    (prefixPartial 13 70757) = some ⟨13, 2, 0, 124647, 70757, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_70757_124647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70757 ⟨124647, by decide⟩ :=
  accepted_of_selected 13 70757 ⟨124647, by decide⟩ ⟨13, 2, 0, 124647, 70757, 1017, 16384⟩
    (by decide) selected_cut_03887

theorem selected_cut_03888 : selected 8 ⟨124667, by decide⟩
    (prefixPartial 13 70758) = some ⟨13, 2, 0, 124667, 70758, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_70758_124667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70758 ⟨124667, by decide⟩ :=
  accepted_of_selected 13 70758 ⟨124667, by decide⟩ ⟨13, 2, 0, 124667, 70758, 1249, 16384⟩
    (by decide) selected_cut_03888

theorem selected_cut_03889 : selected 8 ⟨124678, by decide⟩
    (prefixPartial 13 70759) = some ⟨13, 2, 0, 124678, 70759, 789, 16384⟩ := by
  decide +kernel

theorem context_13_70759_124678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70759 ⟨124678, by decide⟩ :=
  accepted_of_selected 13 70759 ⟨124678, by decide⟩ ⟨13, 2, 0, 124678, 70759, 789, 16384⟩
    (by decide) selected_cut_03889

theorem unmarked_context_12_17689_124679 : frontier 9 ⟨124679, by decide⟩
    (prefixCache 12 17689) (prefixPartial 12 17689) = false := by
  decide +kernel

theorem node_context_12_17689_124679 : EJMOriginalGlobalDAGData.nodes 9 ⟨124679, by decide⟩ =
    .split (coordinate 12) (![⟨124626, by decide⟩,⟨124647, by decide⟩,⟨124667, by decide⟩,⟨124678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17689_124679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17689 ⟨124679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17689
    ⟨124679, by decide⟩ (by decide) (![⟨124626, by decide⟩,⟨124647, by decide⟩,⟨124667, by decide⟩,⟨124678, by decide⟩]) unmarked_context_12_17689_124679 node_context_12_17689_124679
  intro a
  fin_cases a
  · exact context_13_70756_124626
  · exact context_13_70757_124647
  · exact context_13_70758_124667
  · exact context_13_70759_124678

theorem selected_cut_03890 : selected 8 ⟨124722, by decide⟩
    (prefixPartial 13 70760) = some ⟨13, 2, 0, 124722, 70760, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_70760_124722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70760 ⟨124722, by decide⟩ :=
  accepted_of_selected 13 70760 ⟨124722, by decide⟩ ⟨13, 2, 0, 124722, 70760, 1833, 16384⟩
    (by decide) selected_cut_03890

theorem selected_cut_03891 : selected 8 ⟨124748, by decide⟩
    (prefixPartial 13 70761) = some ⟨13, 2, 0, 124748, 70761, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_70761_124748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70761 ⟨124748, by decide⟩ :=
  accepted_of_selected 13 70761 ⟨124748, by decide⟩ ⟨13, 2, 0, 124748, 70761, 1337, 16384⟩
    (by decide) selected_cut_03891

theorem selected_cut_03892 : selected 8 ⟨124771, by decide⟩
    (prefixPartial 13 70762) = some ⟨13, 2, 0, 124771, 70762, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_70762_124771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70762 ⟨124771, by decide⟩ :=
  accepted_of_selected 13 70762 ⟨124771, by decide⟩ ⟨13, 2, 0, 124771, 70762, 1269, 16384⟩
    (by decide) selected_cut_03892

theorem selected_cut_03893 : selected 8 ⟨124780, by decide⟩
    (prefixPartial 13 70763) = some ⟨13, 2, 0, 124780, 70763, 745, 16384⟩ := by
  decide +kernel

theorem context_13_70763_124780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70763 ⟨124780, by decide⟩ :=
  accepted_of_selected 13 70763 ⟨124780, by decide⟩ ⟨13, 2, 0, 124780, 70763, 745, 16384⟩
    (by decide) selected_cut_03893

theorem unmarked_context_12_17690_124781 : frontier 9 ⟨124781, by decide⟩
    (prefixCache 12 17690) (prefixPartial 12 17690) = false := by
  decide +kernel

theorem node_context_12_17690_124781 : EJMOriginalGlobalDAGData.nodes 9 ⟨124781, by decide⟩ =
    .split (coordinate 12) (![⟨124722, by decide⟩,⟨124748, by decide⟩,⟨124771, by decide⟩,⟨124780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17690_124781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17690 ⟨124781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17690
    ⟨124781, by decide⟩ (by decide) (![⟨124722, by decide⟩,⟨124748, by decide⟩,⟨124771, by decide⟩,⟨124780, by decide⟩]) unmarked_context_12_17690_124781 node_context_12_17690_124781
  intro a
  fin_cases a
  · exact context_13_70760_124722
  · exact context_13_70761_124748
  · exact context_13_70762_124771
  · exact context_13_70763_124780

theorem selected_cut_03894 : selected 8 ⟨124821, by decide⟩
    (prefixPartial 13 70764) = some ⟨13, 2, 0, 124821, 70764, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_70764_124821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70764 ⟨124821, by decide⟩ :=
  accepted_of_selected 13 70764 ⟨124821, by decide⟩ ⟨13, 2, 0, 124821, 70764, 2093, 16384⟩
    (by decide) selected_cut_03894

theorem selected_cut_03895 : selected 8 ⟨124852, by decide⟩
    (prefixPartial 13 70765) = some ⟨13, 2, 0, 124852, 70765, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_70765_124852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70765 ⟨124852, by decide⟩ :=
  accepted_of_selected 13 70765 ⟨124852, by decide⟩ ⟨13, 2, 0, 124852, 70765, 1605, 16384⟩
    (by decide) selected_cut_03895

theorem selected_cut_03896 : selected 8 ⟨124874, by decide⟩
    (prefixPartial 13 70766) = some ⟨13, 2, 0, 124874, 70766, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_70766_124874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70766 ⟨124874, by decide⟩ :=
  accepted_of_selected 13 70766 ⟨124874, by decide⟩ ⟨13, 2, 0, 124874, 70766, 1425, 16384⟩
    (by decide) selected_cut_03896

theorem selected_cut_03897 : selected 8 ⟨124885, by decide⟩
    (prefixPartial 13 70767) = some ⟨13, 2, 0, 124885, 70767, 893, 16384⟩ := by
  decide +kernel

theorem context_13_70767_124885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70767 ⟨124885, by decide⟩ :=
  accepted_of_selected 13 70767 ⟨124885, by decide⟩ ⟨13, 2, 0, 124885, 70767, 893, 16384⟩
    (by decide) selected_cut_03897

theorem unmarked_context_12_17691_124886 : frontier 9 ⟨124886, by decide⟩
    (prefixCache 12 17691) (prefixPartial 12 17691) = false := by
  decide +kernel

theorem node_context_12_17691_124886 : EJMOriginalGlobalDAGData.nodes 9 ⟨124886, by decide⟩ =
    .split (coordinate 12) (![⟨124821, by decide⟩,⟨124852, by decide⟩,⟨124874, by decide⟩,⟨124885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17691_124886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17691 ⟨124886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17691
    ⟨124886, by decide⟩ (by decide) (![⟨124821, by decide⟩,⟨124852, by decide⟩,⟨124874, by decide⟩,⟨124885, by decide⟩]) unmarked_context_12_17691_124886 node_context_12_17691_124886
  intro a
  fin_cases a
  · exact context_13_70764_124821
  · exact context_13_70765_124852
  · exact context_13_70766_124874
  · exact context_13_70767_124885

theorem unmarked_context_11_4422_124887 : frontier 10 ⟨124887, by decide⟩
    (prefixCache 11 4422) (prefixPartial 11 4422) = false := by
  decide +kernel

theorem node_context_11_4422_124887 : EJMOriginalGlobalDAGData.nodes 10 ⟨124887, by decide⟩ =
    .split (coordinate 11) (![⟨124587, by decide⟩,⟨124679, by decide⟩,⟨124781, by decide⟩,⟨124886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4422_124887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4422 ⟨124887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4422
    ⟨124887, by decide⟩ (by decide) (![⟨124587, by decide⟩,⟨124679, by decide⟩,⟨124781, by decide⟩,⟨124886, by decide⟩]) unmarked_context_11_4422_124887 node_context_11_4422_124887
  intro a
  fin_cases a
  · exact context_12_17688_124587
  · exact context_12_17689_124679
  · exact context_12_17690_124781
  · exact context_12_17691_124886

theorem selected_cut_03898 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 4423) = some ⟨11, 1, 0, 1736, 4423, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4423_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4423 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 4423 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 4423, 1, 262144⟩
    (by decide) selected_cut_03898

theorem unmarked_context_10_1105_124888 : frontier 11 ⟨124888, by decide⟩
    (prefixCache 10 1105) (prefixPartial 10 1105) = false := by
  decide +kernel

theorem node_context_10_1105_124888 : EJMOriginalGlobalDAGData.nodes 11 ⟨124888, by decide⟩ =
    .split (coordinate 10) (![⟨124223, by decide⟩,⟨124492, by decide⟩,⟨124887, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1105_124888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1105 ⟨124888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1105
    ⟨124888, by decide⟩ (by decide) (![⟨124223, by decide⟩,⟨124492, by decide⟩,⟨124887, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1105_124888 node_context_10_1105_124888
  intro a
  fin_cases a
  · exact context_11_4420_124223
  · exact context_11_4421_124492
  · exact context_11_4422_124887
  · exact context_11_4423_1736

theorem selected_cut_03899 : selected 8 ⟨124929, by decide⟩
    (prefixPartial 13 70784) = some ⟨13, 2, 0, 124929, 70784, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_70784_124929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70784 ⟨124929, by decide⟩ :=
  accepted_of_selected 13 70784 ⟨124929, by decide⟩ ⟨13, 2, 0, 124929, 70784, 1857, 16384⟩
    (by decide) selected_cut_03899

theorem selected_cut_03900 : selected 8 ⟨124953, by decide⟩
    (prefixPartial 13 70785) = some ⟨13, 2, 0, 124953, 70785, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_70785_124953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70785 ⟨124953, by decide⟩ :=
  accepted_of_selected 13 70785 ⟨124953, by decide⟩ ⟨13, 2, 0, 124953, 70785, 2093, 16384⟩
    (by decide) selected_cut_03900

theorem selected_cut_03901 : selected 8 ⟨124979, by decide⟩
    (prefixPartial 13 70786) = some ⟨13, 2, 0, 124979, 70786, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_70786_124979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70786 ⟨124979, by decide⟩ :=
  accepted_of_selected 13 70786 ⟨124979, by decide⟩ ⟨13, 2, 0, 124979, 70786, 1729, 16384⟩
    (by decide) selected_cut_03901

theorem selected_cut_03902 : selected 8 ⟨124990, by decide⟩
    (prefixPartial 13 70787) = some ⟨13, 2, 0, 124990, 70787, 997, 16384⟩ := by
  decide +kernel

theorem context_13_70787_124990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70787 ⟨124990, by decide⟩ :=
  accepted_of_selected 13 70787 ⟨124990, by decide⟩ ⟨13, 2, 0, 124990, 70787, 997, 16384⟩
    (by decide) selected_cut_03902

theorem unmarked_context_12_17696_124991 : frontier 9 ⟨124991, by decide⟩
    (prefixCache 12 17696) (prefixPartial 12 17696) = false := by
  decide +kernel

theorem node_context_12_17696_124991 : EJMOriginalGlobalDAGData.nodes 9 ⟨124991, by decide⟩ =
    .split (coordinate 12) (![⟨124929, by decide⟩,⟨124953, by decide⟩,⟨124979, by decide⟩,⟨124990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17696_124991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17696 ⟨124991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17696
    ⟨124991, by decide⟩ (by decide) (![⟨124929, by decide⟩,⟨124953, by decide⟩,⟨124979, by decide⟩,⟨124990, by decide⟩]) unmarked_context_12_17696_124991 node_context_12_17696_124991
  intro a
  fin_cases a
  · exact context_13_70784_124929
  · exact context_13_70785_124953
  · exact context_13_70786_124979
  · exact context_13_70787_124990

theorem selected_cut_03903 : selected 8 ⟨125026, by decide⟩
    (prefixPartial 13 70788) = some ⟨13, 2, 0, 125026, 70788, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_70788_125026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70788 ⟨125026, by decide⟩ :=
  accepted_of_selected 13 70788 ⟨125026, by decide⟩ ⟨13, 2, 0, 125026, 70788, 1609, 16384⟩
    (by decide) selected_cut_03903

theorem selected_cut_03904 : selected 8 ⟨125050, by decide⟩
    (prefixPartial 13 70789) = some ⟨13, 2, 0, 125050, 70789, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_70789_125050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70789 ⟨125050, by decide⟩ :=
  accepted_of_selected 13 70789 ⟨125050, by decide⟩ ⟨13, 2, 0, 125050, 70789, 1585, 16384⟩
    (by decide) selected_cut_03904

theorem selected_cut_03905 : selected 8 ⟨125072, by decide⟩
    (prefixPartial 13 70790) = some ⟨13, 2, 0, 125072, 70790, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_70790_125072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70790 ⟨125072, by decide⟩ :=
  accepted_of_selected 13 70790 ⟨125072, by decide⟩ ⟨13, 2, 0, 125072, 70790, 1409, 16384⟩
    (by decide) selected_cut_03905

theorem selected_cut_03906 : selected 8 ⟨125081, by decide⟩
    (prefixPartial 13 70791) = some ⟨13, 2, 0, 125081, 70791, 865, 16384⟩ := by
  decide +kernel

theorem context_13_70791_125081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70791 ⟨125081, by decide⟩ :=
  accepted_of_selected 13 70791 ⟨125081, by decide⟩ ⟨13, 2, 0, 125081, 70791, 865, 16384⟩
    (by decide) selected_cut_03906

theorem unmarked_context_12_17697_125082 : frontier 9 ⟨125082, by decide⟩
    (prefixCache 12 17697) (prefixPartial 12 17697) = false := by
  decide +kernel

theorem node_context_12_17697_125082 : EJMOriginalGlobalDAGData.nodes 9 ⟨125082, by decide⟩ =
    .split (coordinate 12) (![⟨125026, by decide⟩,⟨125050, by decide⟩,⟨125072, by decide⟩,⟨125081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17697_125082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17697 ⟨125082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17697
    ⟨125082, by decide⟩ (by decide) (![⟨125026, by decide⟩,⟨125050, by decide⟩,⟨125072, by decide⟩,⟨125081, by decide⟩]) unmarked_context_12_17697_125082 node_context_12_17697_125082
  intro a
  fin_cases a
  · exact context_13_70788_125026
  · exact context_13_70789_125050
  · exact context_13_70790_125072
  · exact context_13_70791_125081

theorem selected_cut_03907 : selected 8 ⟨125125, by decide⟩
    (prefixPartial 13 70792) = some ⟨13, 2, 0, 125125, 70792, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_70792_125125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70792 ⟨125125, by decide⟩ :=
  accepted_of_selected 13 70792 ⟨125125, by decide⟩ ⟨13, 2, 0, 125125, 70792, 1881, 16384⟩
    (by decide) selected_cut_03907

theorem selected_cut_03908 : selected 8 ⟨125151, by decide⟩
    (prefixPartial 13 70793) = some ⟨13, 2, 0, 125151, 70793, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_70793_125151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70793 ⟨125151, by decide⟩ :=
  accepted_of_selected 13 70793 ⟨125151, by decide⟩ ⟨13, 2, 0, 125151, 70793, 1881, 16384⟩
    (by decide) selected_cut_03908

theorem selected_cut_03909 : selected 8 ⟨125180, by decide⟩
    (prefixPartial 13 70794) = some ⟨13, 2, 0, 125180, 70794, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_70794_125180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70794 ⟨125180, by decide⟩ :=
  accepted_of_selected 13 70794 ⟨125180, by decide⟩ ⟨13, 2, 0, 125180, 70794, 1573, 16384⟩
    (by decide) selected_cut_03909

theorem selected_cut_03910 : selected 8 ⟨125192, by decide⟩
    (prefixPartial 13 70795) = some ⟨13, 2, 0, 125192, 70795, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_70795_125192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70795 ⟨125192, by decide⟩ :=
  accepted_of_selected 13 70795 ⟨125192, by decide⟩ ⟨13, 2, 0, 125192, 70795, 1009, 16384⟩
    (by decide) selected_cut_03910

theorem unmarked_context_12_17698_125193 : frontier 9 ⟨125193, by decide⟩
    (prefixCache 12 17698) (prefixPartial 12 17698) = false := by
  decide +kernel

theorem node_context_12_17698_125193 : EJMOriginalGlobalDAGData.nodes 9 ⟨125193, by decide⟩ =
    .split (coordinate 12) (![⟨125125, by decide⟩,⟨125151, by decide⟩,⟨125180, by decide⟩,⟨125192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17698_125193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17698 ⟨125193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17698
    ⟨125193, by decide⟩ (by decide) (![⟨125125, by decide⟩,⟨125151, by decide⟩,⟨125180, by decide⟩,⟨125192, by decide⟩]) unmarked_context_12_17698_125193 node_context_12_17698_125193
  intro a
  fin_cases a
  · exact context_13_70792_125125
  · exact context_13_70793_125151
  · exact context_13_70794_125180
  · exact context_13_70795_125192

theorem selected_cut_03911 : selected 8 ⟨125224, by decide⟩
    (prefixPartial 13 70796) = some ⟨13, 2, 0, 125224, 70796, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_70796_125224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70796 ⟨125224, by decide⟩ :=
  accepted_of_selected 13 70796 ⟨125224, by decide⟩ ⟨13, 2, 0, 125224, 70796, 1685, 16384⟩
    (by decide) selected_cut_03911

theorem selected_cut_03912 : selected 8 ⟨125255, by decide⟩
    (prefixPartial 13 70797) = some ⟨13, 2, 0, 125255, 70797, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_70797_125255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70797 ⟨125255, by decide⟩ :=
  accepted_of_selected 13 70797 ⟨125255, by decide⟩ ⟨13, 2, 0, 125255, 70797, 1793, 16384⟩
    (by decide) selected_cut_03912

theorem selected_cut_03913 : selected 8 ⟨125290, by decide⟩
    (prefixPartial 13 70798) = some ⟨13, 2, 0, 125290, 70798, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_70798_125290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70798 ⟨125290, by decide⟩ :=
  accepted_of_selected 13 70798 ⟨125290, by decide⟩ ⟨13, 2, 0, 125290, 70798, 1609, 16384⟩
    (by decide) selected_cut_03913

theorem selected_cut_03914 : selected 8 ⟨125304, by decide⟩
    (prefixPartial 13 70799) = some ⟨13, 2, 0, 125304, 70799, 957, 16384⟩ := by
  decide +kernel

theorem context_13_70799_125304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70799 ⟨125304, by decide⟩ :=
  accepted_of_selected 13 70799 ⟨125304, by decide⟩ ⟨13, 2, 0, 125304, 70799, 957, 16384⟩
    (by decide) selected_cut_03914

theorem unmarked_context_12_17699_125305 : frontier 9 ⟨125305, by decide⟩
    (prefixCache 12 17699) (prefixPartial 12 17699) = false := by
  decide +kernel

theorem node_context_12_17699_125305 : EJMOriginalGlobalDAGData.nodes 9 ⟨125305, by decide⟩ =
    .split (coordinate 12) (![⟨125224, by decide⟩,⟨125255, by decide⟩,⟨125290, by decide⟩,⟨125304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17699_125305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17699 ⟨125305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17699
    ⟨125305, by decide⟩ (by decide) (![⟨125224, by decide⟩,⟨125255, by decide⟩,⟨125290, by decide⟩,⟨125304, by decide⟩]) unmarked_context_12_17699_125305 node_context_12_17699_125305
  intro a
  fin_cases a
  · exact context_13_70796_125224
  · exact context_13_70797_125255
  · exact context_13_70798_125290
  · exact context_13_70799_125304

theorem unmarked_context_11_4424_125306 : frontier 10 ⟨125306, by decide⟩
    (prefixCache 11 4424) (prefixPartial 11 4424) = false := by
  decide +kernel

theorem node_context_11_4424_125306 : EJMOriginalGlobalDAGData.nodes 10 ⟨125306, by decide⟩ =
    .split (coordinate 11) (![⟨124991, by decide⟩,⟨125082, by decide⟩,⟨125193, by decide⟩,⟨125305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4424_125306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4424 ⟨125306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4424
    ⟨125306, by decide⟩ (by decide) (![⟨124991, by decide⟩,⟨125082, by decide⟩,⟨125193, by decide⟩,⟨125305, by decide⟩]) unmarked_context_11_4424_125306 node_context_11_4424_125306
  intro a
  fin_cases a
  · exact context_12_17696_124991
  · exact context_12_17697_125082
  · exact context_12_17698_125193
  · exact context_12_17699_125305

theorem selected_cut_03915 : selected 8 ⟨125331, by decide⟩
    (prefixPartial 13 70800) = some ⟨13, 2, 0, 125331, 70800, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_70800_125331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70800 ⟨125331, by decide⟩ :=
  accepted_of_selected 13 70800 ⟨125331, by decide⟩ ⟨13, 2, 0, 125331, 70800, 1049, 16384⟩
    (by decide) selected_cut_03915

theorem selected_cut_03916 : selected 8 ⟨125348, by decide⟩
    (prefixPartial 13 70801) = some ⟨13, 2, 0, 125348, 70801, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_70801_125348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70801 ⟨125348, by decide⟩ :=
  accepted_of_selected 13 70801 ⟨125348, by decide⟩ ⟨13, 2, 0, 125348, 70801, 1657, 16384⟩
    (by decide) selected_cut_03916

theorem selected_cut_03917 : selected 8 ⟨125368, by decide⟩
    (prefixPartial 13 70802) = some ⟨13, 2, 0, 125368, 70802, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_70802_125368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70802 ⟨125368, by decide⟩ :=
  accepted_of_selected 13 70802 ⟨125368, by decide⟩ ⟨13, 2, 0, 125368, 70802, 1557, 16384⟩
    (by decide) selected_cut_03917

theorem selected_cut_03918 : selected 8 ⟨125379, by decide⟩
    (prefixPartial 13 70803) = some ⟨13, 2, 0, 125379, 70803, 857, 16384⟩ := by
  decide +kernel

theorem context_13_70803_125379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70803 ⟨125379, by decide⟩ :=
  accepted_of_selected 13 70803 ⟨125379, by decide⟩ ⟨13, 2, 0, 125379, 70803, 857, 16384⟩
    (by decide) selected_cut_03918

theorem unmarked_context_12_17700_125380 : frontier 9 ⟨125380, by decide⟩
    (prefixCache 12 17700) (prefixPartial 12 17700) = false := by
  decide +kernel

theorem node_context_12_17700_125380 : EJMOriginalGlobalDAGData.nodes 9 ⟨125380, by decide⟩ =
    .split (coordinate 12) (![⟨125331, by decide⟩,⟨125348, by decide⟩,⟨125368, by decide⟩,⟨125379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17700_125380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17700 ⟨125380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17700
    ⟨125380, by decide⟩ (by decide) (![⟨125331, by decide⟩,⟨125348, by decide⟩,⟨125368, by decide⟩,⟨125379, by decide⟩]) unmarked_context_12_17700_125380 node_context_12_17700_125380
  intro a
  fin_cases a
  · exact context_13_70800_125331
  · exact context_13_70801_125348
  · exact context_13_70802_125368
  · exact context_13_70803_125379

theorem selected_cut_03919 : selected 8 ⟨125408, by decide⟩
    (prefixPartial 13 70804) = some ⟨13, 2, 0, 125408, 70804, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_70804_125408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70804 ⟨125408, by decide⟩ :=
  accepted_of_selected 13 70804 ⟨125408, by decide⟩ ⟨13, 2, 0, 125408, 70804, 1509, 16384⟩
    (by decide) selected_cut_03919

theorem selected_cut_03920 : selected 8 ⟨125446, by decide⟩
    (prefixPartial 13 70805) = some ⟨13, 2, 0, 125446, 70805, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_70805_125446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70805 ⟨125446, by decide⟩ :=
  accepted_of_selected 13 70805 ⟨125446, by decide⟩ ⟨13, 2, 0, 125446, 70805, 2701, 16384⟩
    (by decide) selected_cut_03920

theorem selected_cut_03921 : selected 8 ⟨125472, by decide⟩
    (prefixPartial 13 70806) = some ⟨13, 2, 0, 125472, 70806, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_70806_125472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70806 ⟨125472, by decide⟩ :=
  accepted_of_selected 13 70806 ⟨125472, by decide⟩ ⟨13, 2, 0, 125472, 70806, 2041, 16384⟩
    (by decide) selected_cut_03921

theorem selected_cut_03922 : selected 8 ⟨125481, by decide⟩
    (prefixPartial 13 70807) = some ⟨13, 2, 0, 125481, 70807, 985, 16384⟩ := by
  decide +kernel

theorem context_13_70807_125481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70807 ⟨125481, by decide⟩ :=
  accepted_of_selected 13 70807 ⟨125481, by decide⟩ ⟨13, 2, 0, 125481, 70807, 985, 16384⟩
    (by decide) selected_cut_03922

theorem unmarked_context_12_17701_125482 : frontier 9 ⟨125482, by decide⟩
    (prefixCache 12 17701) (prefixPartial 12 17701) = false := by
  decide +kernel

theorem node_context_12_17701_125482 : EJMOriginalGlobalDAGData.nodes 9 ⟨125482, by decide⟩ =
    .split (coordinate 12) (![⟨125408, by decide⟩,⟨125446, by decide⟩,⟨125472, by decide⟩,⟨125481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17701_125482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17701 ⟨125482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17701
    ⟨125482, by decide⟩ (by decide) (![⟨125408, by decide⟩,⟨125446, by decide⟩,⟨125472, by decide⟩,⟨125481, by decide⟩]) unmarked_context_12_17701_125482 node_context_12_17701_125482
  intro a
  fin_cases a
  · exact context_13_70804_125408
  · exact context_13_70805_125446
  · exact context_13_70806_125472
  · exact context_13_70807_125481

theorem selected_cut_03923 : selected 8 ⟨125509, by decide⟩
    (prefixPartial 13 70808) = some ⟨13, 2, 0, 125509, 70808, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_70808_125509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70808 ⟨125509, by decide⟩ :=
  accepted_of_selected 13 70808 ⟨125509, by decide⟩ ⟨13, 2, 0, 125509, 70808, 1149, 16384⟩
    (by decide) selected_cut_03923

theorem selected_cut_03924 : selected 8 ⟨125536, by decide⟩
    (prefixPartial 13 70809) = some ⟨13, 2, 0, 125536, 70809, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_70809_125536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70809 ⟨125536, by decide⟩ :=
  accepted_of_selected 13 70809 ⟨125536, by decide⟩ ⟨13, 2, 0, 125536, 70809, 2109, 16384⟩
    (by decide) selected_cut_03924

theorem selected_cut_03925 : selected 8 ⟨125559, by decide⟩
    (prefixPartial 13 70810) = some ⟨13, 2, 0, 125559, 70810, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_70810_125559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70810 ⟨125559, by decide⟩ :=
  accepted_of_selected 13 70810 ⟨125559, by decide⟩ ⟨13, 2, 0, 125559, 70810, 1489, 16384⟩
    (by decide) selected_cut_03925

theorem selected_cut_03926 : selected 8 ⟨125570, by decide⟩
    (prefixPartial 13 70811) = some ⟨13, 2, 0, 125570, 70811, 821, 16384⟩ := by
  decide +kernel

theorem context_13_70811_125570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70811 ⟨125570, by decide⟩ :=
  accepted_of_selected 13 70811 ⟨125570, by decide⟩ ⟨13, 2, 0, 125570, 70811, 821, 16384⟩
    (by decide) selected_cut_03926

theorem unmarked_context_12_17702_125571 : frontier 9 ⟨125571, by decide⟩
    (prefixCache 12 17702) (prefixPartial 12 17702) = false := by
  decide +kernel

theorem node_context_12_17702_125571 : EJMOriginalGlobalDAGData.nodes 9 ⟨125571, by decide⟩ =
    .split (coordinate 12) (![⟨125509, by decide⟩,⟨125536, by decide⟩,⟨125559, by decide⟩,⟨125570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17702_125571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17702 ⟨125571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17702
    ⟨125571, by decide⟩ (by decide) (![⟨125509, by decide⟩,⟨125536, by decide⟩,⟨125559, by decide⟩,⟨125570, by decide⟩]) unmarked_context_12_17702_125571 node_context_12_17702_125571
  intro a
  fin_cases a
  · exact context_13_70808_125509
  · exact context_13_70809_125536
  · exact context_13_70810_125559
  · exact context_13_70811_125570

theorem selected_cut_03927 : selected 8 ⟨125594, by decide⟩
    (prefixPartial 13 70812) = some ⟨13, 2, 0, 125594, 70812, 977, 16384⟩ := by
  decide +kernel

theorem context_13_70812_125594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70812 ⟨125594, by decide⟩ :=
  accepted_of_selected 13 70812 ⟨125594, by decide⟩ ⟨13, 2, 0, 125594, 70812, 977, 16384⟩
    (by decide) selected_cut_03927

theorem selected_cut_03928 : selected 8 ⟨125618, by decide⟩
    (prefixPartial 13 70813) = some ⟨13, 2, 0, 125618, 70813, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_70813_125618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70813 ⟨125618, by decide⟩ :=
  accepted_of_selected 13 70813 ⟨125618, by decide⟩ ⟨13, 2, 0, 125618, 70813, 2077, 16384⟩
    (by decide) selected_cut_03928

theorem selected_cut_03929 : selected 8 ⟨125640, by decide⟩
    (prefixPartial 13 70814) = some ⟨13, 2, 0, 125640, 70814, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_70814_125640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70814 ⟨125640, by decide⟩ :=
  accepted_of_selected 13 70814 ⟨125640, by decide⟩ ⟨13, 2, 0, 125640, 70814, 1421, 16384⟩
    (by decide) selected_cut_03929

theorem selected_cut_03930 : selected 8 ⟨125650, by decide⟩
    (prefixPartial 13 70815) = some ⟨13, 2, 0, 125650, 70815, 801, 16384⟩ := by
  decide +kernel

theorem context_13_70815_125650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70815 ⟨125650, by decide⟩ :=
  accepted_of_selected 13 70815 ⟨125650, by decide⟩ ⟨13, 2, 0, 125650, 70815, 801, 16384⟩
    (by decide) selected_cut_03930

theorem unmarked_context_12_17703_125651 : frontier 9 ⟨125651, by decide⟩
    (prefixCache 12 17703) (prefixPartial 12 17703) = false := by
  decide +kernel

theorem node_context_12_17703_125651 : EJMOriginalGlobalDAGData.nodes 9 ⟨125651, by decide⟩ =
    .split (coordinate 12) (![⟨125594, by decide⟩,⟨125618, by decide⟩,⟨125640, by decide⟩,⟨125650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17703_125651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17703 ⟨125651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17703
    ⟨125651, by decide⟩ (by decide) (![⟨125594, by decide⟩,⟨125618, by decide⟩,⟨125640, by decide⟩,⟨125650, by decide⟩]) unmarked_context_12_17703_125651 node_context_12_17703_125651
  intro a
  fin_cases a
  · exact context_13_70812_125594
  · exact context_13_70813_125618
  · exact context_13_70814_125640
  · exact context_13_70815_125650

theorem unmarked_context_11_4425_125652 : frontier 10 ⟨125652, by decide⟩
    (prefixCache 11 4425) (prefixPartial 11 4425) = false := by
  decide +kernel

theorem node_context_11_4425_125652 : EJMOriginalGlobalDAGData.nodes 10 ⟨125652, by decide⟩ =
    .split (coordinate 11) (![⟨125380, by decide⟩,⟨125482, by decide⟩,⟨125571, by decide⟩,⟨125651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4425_125652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4425 ⟨125652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4425
    ⟨125652, by decide⟩ (by decide) (![⟨125380, by decide⟩,⟨125482, by decide⟩,⟨125571, by decide⟩,⟨125651, by decide⟩]) unmarked_context_11_4425_125652 node_context_11_4425_125652
  intro a
  fin_cases a
  · exact context_12_17700_125380
  · exact context_12_17701_125482
  · exact context_12_17702_125571
  · exact context_12_17703_125651

theorem selected_cut_03931 : selected 8 ⟨125665, by decide⟩
    (prefixPartial 13 70816) = some ⟨13, 2, 0, 125665, 70816, 629, 16384⟩ := by
  decide +kernel

theorem context_13_70816_125665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70816 ⟨125665, by decide⟩ :=
  accepted_of_selected 13 70816 ⟨125665, by decide⟩ ⟨13, 2, 0, 125665, 70816, 629, 16384⟩
    (by decide) selected_cut_03931

theorem selected_cut_03932 : selected 8 ⟨125685, by decide⟩
    (prefixPartial 13 70817) = some ⟨13, 2, 0, 125685, 70817, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_70817_125685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70817 ⟨125685, by decide⟩ :=
  accepted_of_selected 13 70817 ⟨125685, by decide⟩ ⟨13, 2, 0, 125685, 70817, 1853, 16384⟩
    (by decide) selected_cut_03932

theorem selected_cut_03933 : selected 8 ⟨125710, by decide⟩
    (prefixPartial 13 70818) = some ⟨13, 2, 0, 125710, 70818, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_70818_125710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70818 ⟨125710, by decide⟩ :=
  accepted_of_selected 13 70818 ⟨125710, by decide⟩ ⟨13, 2, 0, 125710, 70818, 1613, 16384⟩
    (by decide) selected_cut_03933

theorem selected_cut_03934 : selected 8 ⟨125720, by decide⟩
    (prefixPartial 13 70819) = some ⟨13, 2, 0, 125720, 70819, 845, 16384⟩ := by
  decide +kernel

theorem context_13_70819_125720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70819 ⟨125720, by decide⟩ :=
  accepted_of_selected 13 70819 ⟨125720, by decide⟩ ⟨13, 2, 0, 125720, 70819, 845, 16384⟩
    (by decide) selected_cut_03934

theorem unmarked_context_12_17704_125721 : frontier 9 ⟨125721, by decide⟩
    (prefixCache 12 17704) (prefixPartial 12 17704) = false := by
  decide +kernel

theorem node_context_12_17704_125721 : EJMOriginalGlobalDAGData.nodes 9 ⟨125721, by decide⟩ =
    .split (coordinate 12) (![⟨125665, by decide⟩,⟨125685, by decide⟩,⟨125710, by decide⟩,⟨125720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17704_125721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17704 ⟨125721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17704
    ⟨125721, by decide⟩ (by decide) (![⟨125665, by decide⟩,⟨125685, by decide⟩,⟨125710, by decide⟩,⟨125720, by decide⟩]) unmarked_context_12_17704_125721 node_context_12_17704_125721
  intro a
  fin_cases a
  · exact context_13_70816_125665
  · exact context_13_70817_125685
  · exact context_13_70818_125710
  · exact context_13_70819_125720

theorem selected_cut_03935 : selected 8 ⟨125737, by decide⟩
    (prefixPartial 13 70820) = some ⟨13, 2, 0, 125737, 70820, 713, 16384⟩ := by
  decide +kernel

theorem context_13_70820_125737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70820 ⟨125737, by decide⟩ :=
  accepted_of_selected 13 70820 ⟨125737, by decide⟩ ⟨13, 2, 0, 125737, 70820, 713, 16384⟩
    (by decide) selected_cut_03935

theorem selected_cut_03936 : selected 8 ⟨125764, by decide⟩
    (prefixPartial 13 70821) = some ⟨13, 2, 0, 125764, 70821, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_70821_125764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70821 ⟨125764, by decide⟩ :=
  accepted_of_selected 13 70821 ⟨125764, by decide⟩ ⟨13, 2, 0, 125764, 70821, 1681, 16384⟩
    (by decide) selected_cut_03936

theorem selected_cut_03937 : selected 8 ⟨125786, by decide⟩
    (prefixPartial 13 70822) = some ⟨13, 2, 0, 125786, 70822, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_70822_125786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70822 ⟨125786, by decide⟩ :=
  accepted_of_selected 13 70822 ⟨125786, by decide⟩ ⟨13, 2, 0, 125786, 70822, 1409, 16384⟩
    (by decide) selected_cut_03937

theorem selected_cut_03938 : selected 8 ⟨125797, by decide⟩
    (prefixPartial 13 70823) = some ⟨13, 2, 0, 125797, 70823, 769, 16384⟩ := by
  decide +kernel

theorem context_13_70823_125797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70823 ⟨125797, by decide⟩ :=
  accepted_of_selected 13 70823 ⟨125797, by decide⟩ ⟨13, 2, 0, 125797, 70823, 769, 16384⟩
    (by decide) selected_cut_03938

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
