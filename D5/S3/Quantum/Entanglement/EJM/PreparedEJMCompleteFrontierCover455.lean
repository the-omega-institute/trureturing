/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover454
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43683 : selected 9 ⟨1197699, by decide⟩
    (prefixPartial 12 352299) = some ⟨12, 2, 0, 1197699, 352299, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_352299_1197699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352299 ⟨1197699, by decide⟩ :=
  accepted_of_selected 12 352299 ⟨1197699, by decide⟩ ⟨12, 2, 0, 1197699, 352299, 2745, 65536⟩
    (by decide) selected_cut_43683

theorem unmarked_context_11_88074_1197700 : frontier 10 ⟨1197700, by decide⟩
    (prefixCache 11 88074) (prefixPartial 11 88074) = false := by
  decide +kernel

theorem node_context_11_88074_1197700 : EJMOriginalGlobalDAGData.nodes 10 ⟨1197700, by decide⟩ =
    .split (coordinate 11) (![⟨101803, by decide⟩,⟨1197641, by decide⟩,⟨474208, by decide⟩,⟨1197699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88074_1197700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88074 ⟨1197700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88074
    ⟨1197700, by decide⟩ (by decide) (![⟨101803, by decide⟩,⟨1197641, by decide⟩,⟨474208, by decide⟩,⟨1197699, by decide⟩]) unmarked_context_11_88074_1197700 node_context_11_88074_1197700
  intro a
  fin_cases a
  · exact context_12_352296_101803
  · exact context_12_352297_1197641
  · exact context_12_352298_474208
  · exact context_12_352299_1197699

theorem selected_cut_43684 : selected 9 ⟨1197743, by decide⟩
    (prefixPartial 12 352300) = some ⟨12, 2, 0, 1197743, 352300, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_352300_1197743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352300 ⟨1197743, by decide⟩ :=
  accepted_of_selected 12 352300 ⟨1197743, by decide⟩ ⟨12, 2, 0, 1197743, 352300, 2449, 65536⟩
    (by decide) selected_cut_43684

theorem selected_cut_43685 : selected 9 ⟨1197779, by decide⟩
    (prefixPartial 12 352301) = some ⟨12, 2, 0, 1197779, 352301, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_352301_1197779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352301 ⟨1197779, by decide⟩ :=
  accepted_of_selected 12 352301 ⟨1197779, by decide⟩ ⟨12, 2, 0, 1197779, 352301, 2193, 65536⟩
    (by decide) selected_cut_43685

theorem selected_cut_43686 : selected 9 ⟨1197819, by decide⟩
    (prefixPartial 12 352302) = some ⟨12, 2, 0, 1197819, 352302, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_352302_1197819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352302 ⟨1197819, by decide⟩ :=
  accepted_of_selected 12 352302 ⟨1197819, by decide⟩ ⟨12, 2, 0, 1197819, 352302, 2361, 65536⟩
    (by decide) selected_cut_43686

theorem selected_cut_43687 : selected 9 ⟨1197860, by decide⟩
    (prefixPartial 12 352303) = some ⟨12, 2, 0, 1197860, 352303, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_352303_1197860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352303 ⟨1197860, by decide⟩ :=
  accepted_of_selected 12 352303 ⟨1197860, by decide⟩ ⟨12, 2, 0, 1197860, 352303, 2449, 65536⟩
    (by decide) selected_cut_43687

theorem unmarked_context_11_88075_1197861 : frontier 10 ⟨1197861, by decide⟩
    (prefixCache 11 88075) (prefixPartial 11 88075) = false := by
  decide +kernel

theorem node_context_11_88075_1197861 : EJMOriginalGlobalDAGData.nodes 10 ⟨1197861, by decide⟩ =
    .split (coordinate 11) (![⟨1197743, by decide⟩,⟨1197779, by decide⟩,⟨1197819, by decide⟩,⟨1197860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88075_1197861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88075 ⟨1197861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88075
    ⟨1197861, by decide⟩ (by decide) (![⟨1197743, by decide⟩,⟨1197779, by decide⟩,⟨1197819, by decide⟩,⟨1197860, by decide⟩]) unmarked_context_11_88075_1197861 node_context_11_88075_1197861
  intro a
  fin_cases a
  · exact context_12_352300_1197743
  · exact context_12_352301_1197779
  · exact context_12_352302_1197819
  · exact context_12_352303_1197860

theorem unmarked_context_10_22018_1197862 : frontier 11 ⟨1197862, by decide⟩
    (prefixCache 10 22018) (prefixPartial 10 22018) = false := by
  decide +kernel

theorem node_context_10_22018_1197862 : EJMOriginalGlobalDAGData.nodes 11 ⟨1197862, by decide⟩ =
    .split (coordinate 10) (![⟨1197508, by decide⟩,⟨1197601, by decide⟩,⟨1197700, by decide⟩,⟨1197861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22018_1197862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22018 ⟨1197862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22018
    ⟨1197862, by decide⟩ (by decide) (![⟨1197508, by decide⟩,⟨1197601, by decide⟩,⟨1197700, by decide⟩,⟨1197861, by decide⟩]) unmarked_context_10_22018_1197862 node_context_10_22018_1197862
  intro a
  fin_cases a
  · exact context_11_88072_1197508
  · exact context_11_88073_1197601
  · exact context_11_88074_1197700
  · exact context_11_88075_1197861

theorem selected_cut_43688 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 352304) = some ⟨12, 1, 0, 985390, 352304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352304_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352304 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 352304 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 352304, 1, 65536⟩
    (by decide) selected_cut_43688

theorem selected_cut_43689 : selected 9 ⟨1197885, by decide⟩
    (prefixPartial 12 352305) = some ⟨12, 2, 0, 1197885, 352305, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_352305_1197885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352305 ⟨1197885, by decide⟩ :=
  accepted_of_selected 12 352305 ⟨1197885, by decide⟩ ⟨12, 2, 0, 1197885, 352305, 1865, 65536⟩
    (by decide) selected_cut_43689

theorem selected_cut_43690 : selected 9 ⟨1197917, by decide⟩
    (prefixPartial 12 352306) = some ⟨12, 2, 0, 1197917, 352306, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_352306_1197917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352306 ⟨1197917, by decide⟩ :=
  accepted_of_selected 12 352306 ⟨1197917, by decide⟩ ⟨12, 2, 0, 1197917, 352306, 2017, 65536⟩
    (by decide) selected_cut_43690

theorem selected_cut_43691 : selected 9 ⟨1197950, by decide⟩
    (prefixPartial 12 352307) = some ⟨12, 2, 0, 1197950, 352307, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_352307_1197950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352307 ⟨1197950, by decide⟩ :=
  accepted_of_selected 12 352307 ⟨1197950, by decide⟩ ⟨12, 2, 0, 1197950, 352307, 2073, 65536⟩
    (by decide) selected_cut_43691

theorem unmarked_context_11_88076_1197951 : frontier 10 ⟨1197951, by decide⟩
    (prefixCache 11 88076) (prefixPartial 11 88076) = false := by
  decide +kernel

theorem node_context_11_88076_1197951 : EJMOriginalGlobalDAGData.nodes 10 ⟨1197951, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1197885, by decide⟩,⟨1197917, by decide⟩,⟨1197950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88076_1197951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88076 ⟨1197951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88076
    ⟨1197951, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1197885, by decide⟩,⟨1197917, by decide⟩,⟨1197950, by decide⟩]) unmarked_context_11_88076_1197951 node_context_11_88076_1197951
  intro a
  fin_cases a
  · exact context_12_352304_985390
  · exact context_12_352305_1197885
  · exact context_12_352306_1197917
  · exact context_12_352307_1197950

theorem selected_cut_43692 : selected 9 ⟨1197509, by decide⟩
    (prefixPartial 12 352308) = some ⟨12, 1, 0, 1197509, 352308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352308_1197509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352308 ⟨1197509, by decide⟩ :=
  accepted_of_selected 12 352308 ⟨1197509, by decide⟩ ⟨12, 1, 0, 1197509, 352308, 1, 65536⟩
    (by decide) selected_cut_43692

theorem selected_cut_43693 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 352309) = some ⟨12, 1, 0, 719134, 352309, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352309_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352309 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 352309 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 352309, 1, 65536⟩
    (by decide) selected_cut_43693

theorem selected_cut_43694 : selected 9 ⟨1197993, by decide⟩
    (prefixPartial 12 352310) = some ⟨12, 2, 0, 1197993, 352310, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_352310_1197993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352310 ⟨1197993, by decide⟩ :=
  accepted_of_selected 12 352310 ⟨1197993, by decide⟩ ⟨12, 2, 0, 1197993, 352310, 2257, 65536⟩
    (by decide) selected_cut_43694

theorem selected_cut_43695 : selected 9 ⟨1198034, by decide⟩
    (prefixPartial 12 352311) = some ⟨12, 2, 0, 1198034, 352311, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_352311_1198034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352311 ⟨1198034, by decide⟩ :=
  accepted_of_selected 12 352311 ⟨1198034, by decide⟩ ⟨12, 2, 0, 1198034, 352311, 2341, 65536⟩
    (by decide) selected_cut_43695

theorem unmarked_context_11_88077_1198035 : frontier 10 ⟨1198035, by decide⟩
    (prefixCache 11 88077) (prefixPartial 11 88077) = false := by
  decide +kernel

theorem node_context_11_88077_1198035 : EJMOriginalGlobalDAGData.nodes 10 ⟨1198035, by decide⟩ =
    .split (coordinate 11) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1197993, by decide⟩,⟨1198034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88077_1198035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88077 ⟨1198035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88077
    ⟨1198035, by decide⟩ (by decide) (![⟨1197509, by decide⟩,⟨719134, by decide⟩,⟨1197993, by decide⟩,⟨1198034, by decide⟩]) unmarked_context_11_88077_1198035 node_context_11_88077_1198035
  intro a
  fin_cases a
  · exact context_12_352308_1197509
  · exact context_12_352309_719134
  · exact context_12_352310_1197993
  · exact context_12_352311_1198034

theorem selected_cut_43696 : selected 9 ⟨1198082, by decide⟩
    (prefixPartial 12 352312) = some ⟨12, 2, 0, 1198082, 352312, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_352312_1198082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352312 ⟨1198082, by decide⟩ :=
  accepted_of_selected 12 352312 ⟨1198082, by decide⟩ ⟨12, 2, 0, 1198082, 352312, 2401, 65536⟩
    (by decide) selected_cut_43696

theorem selected_cut_43697 : selected 9 ⟨1198116, by decide⟩
    (prefixPartial 12 352313) = some ⟨12, 2, 0, 1198116, 352313, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_352313_1198116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352313 ⟨1198116, by decide⟩ :=
  accepted_of_selected 12 352313 ⟨1198116, by decide⟩ ⟨12, 2, 0, 1198116, 352313, 2129, 65536⟩
    (by decide) selected_cut_43697

theorem selected_cut_43698 : selected 9 ⟨1198158, by decide⟩
    (prefixPartial 12 352314) = some ⟨12, 2, 0, 1198158, 352314, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_352314_1198158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352314 ⟨1198158, by decide⟩ :=
  accepted_of_selected 12 352314 ⟨1198158, by decide⟩ ⟨12, 2, 0, 1198158, 352314, 2341, 65536⟩
    (by decide) selected_cut_43698

theorem selected_cut_43699 : selected 9 ⟨1198207, by decide⟩
    (prefixPartial 12 352315) = some ⟨12, 2, 0, 1198207, 352315, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_352315_1198207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352315 ⟨1198207, by decide⟩ :=
  accepted_of_selected 12 352315 ⟨1198207, by decide⟩ ⟨12, 2, 0, 1198207, 352315, 2473, 65536⟩
    (by decide) selected_cut_43699

theorem unmarked_context_11_88078_1198208 : frontier 10 ⟨1198208, by decide⟩
    (prefixCache 11 88078) (prefixPartial 11 88078) = false := by
  decide +kernel

theorem node_context_11_88078_1198208 : EJMOriginalGlobalDAGData.nodes 10 ⟨1198208, by decide⟩ =
    .split (coordinate 11) (![⟨1198082, by decide⟩,⟨1198116, by decide⟩,⟨1198158, by decide⟩,⟨1198207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88078_1198208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88078 ⟨1198208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88078
    ⟨1198208, by decide⟩ (by decide) (![⟨1198082, by decide⟩,⟨1198116, by decide⟩,⟨1198158, by decide⟩,⟨1198207, by decide⟩]) unmarked_context_11_88078_1198208 node_context_11_88078_1198208
  intro a
  fin_cases a
  · exact context_12_352312_1198082
  · exact context_12_352313_1198116
  · exact context_12_352314_1198158
  · exact context_12_352315_1198207

theorem selected_cut_43700 : selected 10 ⟨1198273, by decide⟩
    (prefixPartial 11 88079) = some ⟨11, 2, 0, 1198273, 88079, 3993, 262144⟩ := by
  decide +kernel

theorem context_11_88079_1198273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88079 ⟨1198273, by decide⟩ :=
  accepted_of_selected 11 88079 ⟨1198273, by decide⟩ ⟨11, 2, 0, 1198273, 88079, 3993, 262144⟩
    (by decide) selected_cut_43700

theorem unmarked_context_10_22019_1198274 : frontier 11 ⟨1198274, by decide⟩
    (prefixCache 10 22019) (prefixPartial 10 22019) = false := by
  decide +kernel

theorem node_context_10_22019_1198274 : EJMOriginalGlobalDAGData.nodes 11 ⟨1198274, by decide⟩ =
    .split (coordinate 10) (![⟨1197951, by decide⟩,⟨1198035, by decide⟩,⟨1198208, by decide⟩,⟨1198273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22019_1198274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22019 ⟨1198274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22019
    ⟨1198274, by decide⟩ (by decide) (![⟨1197951, by decide⟩,⟨1198035, by decide⟩,⟨1198208, by decide⟩,⟨1198273, by decide⟩]) unmarked_context_10_22019_1198274 node_context_10_22019_1198274
  intro a
  fin_cases a
  · exact context_11_88076_1197951
  · exact context_11_88077_1198035
  · exact context_11_88078_1198208
  · exact context_11_88079_1198273

theorem unmarked_context_9_5504_1198275 : frontier 12 ⟨1198275, by decide⟩
    (prefixCache 9 5504) (prefixPartial 9 5504) = false := by
  decide +kernel

theorem node_context_9_5504_1198275 : EJMOriginalGlobalDAGData.nodes 12 ⟨1198275, by decide⟩ =
    .split (coordinate 9) (![⟨1196936, by decide⟩,⟨1197417, by decide⟩,⟨1197862, by decide⟩,⟨1198274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5504_1198275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5504 ⟨1198275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5504
    ⟨1198275, by decide⟩ (by decide) (![⟨1196936, by decide⟩,⟨1197417, by decide⟩,⟨1197862, by decide⟩,⟨1198274, by decide⟩]) unmarked_context_9_5504_1198275 node_context_9_5504_1198275
  intro a
  fin_cases a
  · exact context_10_22016_1196936
  · exact context_10_22017_1197417
  · exact context_10_22018_1197862
  · exact context_10_22019_1198274

theorem selected_cut_43701 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88080) = some ⟨11, 1, 0, 907917, 88080, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88080_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88080 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88080 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88080, 1, 262144⟩
    (by decide) selected_cut_43701

theorem selected_cut_43702 : selected 9 ⟨1198306, by decide⟩
    (prefixPartial 12 352324) = some ⟨12, 2, 0, 1198306, 352324, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_352324_1198306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352324 ⟨1198306, by decide⟩ :=
  accepted_of_selected 12 352324 ⟨1198306, by decide⟩ ⟨12, 2, 0, 1198306, 352324, 1565, 65536⟩
    (by decide) selected_cut_43702

theorem selected_cut_43703 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352325) = some ⟨12, 1, 0, 896706, 352325, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352325_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352325 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352325 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352325, 1, 65536⟩
    (by decide) selected_cut_43703

theorem selected_cut_43704 : selected 9 ⟨1198336, by decide⟩
    (prefixPartial 12 352326) = some ⟨12, 2, 0, 1198336, 352326, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_352326_1198336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352326 ⟨1198336, by decide⟩ :=
  accepted_of_selected 12 352326 ⟨1198336, by decide⟩ ⟨12, 2, 0, 1198336, 352326, 1789, 65536⟩
    (by decide) selected_cut_43704

theorem selected_cut_43705 : selected 9 ⟨1198369, by decide⟩
    (prefixPartial 12 352327) = some ⟨12, 2, 0, 1198369, 352327, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_352327_1198369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352327 ⟨1198369, by decide⟩ :=
  accepted_of_selected 12 352327 ⟨1198369, by decide⟩ ⟨12, 2, 0, 1198369, 352327, 1897, 65536⟩
    (by decide) selected_cut_43705

theorem unmarked_context_11_88081_1198370 : frontier 10 ⟨1198370, by decide⟩
    (prefixCache 11 88081) (prefixPartial 11 88081) = false := by
  decide +kernel

theorem node_context_11_88081_1198370 : EJMOriginalGlobalDAGData.nodes 10 ⟨1198370, by decide⟩ =
    .split (coordinate 11) (![⟨1198306, by decide⟩,⟨896706, by decide⟩,⟨1198336, by decide⟩,⟨1198369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88081_1198370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88081 ⟨1198370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88081
    ⟨1198370, by decide⟩ (by decide) (![⟨1198306, by decide⟩,⟨896706, by decide⟩,⟨1198336, by decide⟩,⟨1198369, by decide⟩]) unmarked_context_11_88081_1198370 node_context_11_88081_1198370
  intro a
  fin_cases a
  · exact context_12_352324_1198306
  · exact context_12_352325_896706
  · exact context_12_352326_1198336
  · exact context_12_352327_1198369

theorem selected_cut_43706 : selected 9 ⟨1198405, by decide⟩
    (prefixPartial 12 352328) = some ⟨12, 2, 0, 1198405, 352328, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_352328_1198405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352328 ⟨1198405, by decide⟩ :=
  accepted_of_selected 12 352328 ⟨1198405, by decide⟩ ⟨12, 2, 0, 1198405, 352328, 1769, 65536⟩
    (by decide) selected_cut_43706

theorem selected_cut_43707 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352329) = some ⟨12, 1, 0, 896706, 352329, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352329_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352329 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352329 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352329, 1, 65536⟩
    (by decide) selected_cut_43707

theorem selected_cut_43708 : selected 9 ⟨1198450, by decide⟩
    (prefixPartial 12 352330) = some ⟨12, 2, 0, 1198450, 352330, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_352330_1198450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352330 ⟨1198450, by decide⟩ :=
  accepted_of_selected 12 352330 ⟨1198450, by decide⟩ ⟨12, 2, 0, 1198450, 352330, 2045, 65536⟩
    (by decide) selected_cut_43708

theorem selected_cut_43709 : selected 9 ⟨1198508, by decide⟩
    (prefixPartial 12 352331) = some ⟨12, 2, 0, 1198508, 352331, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_352331_1198508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352331 ⟨1198508, by decide⟩ :=
  accepted_of_selected 12 352331 ⟨1198508, by decide⟩ ⟨12, 2, 0, 1198508, 352331, 2365, 65536⟩
    (by decide) selected_cut_43709

theorem unmarked_context_11_88082_1198509 : frontier 10 ⟨1198509, by decide⟩
    (prefixCache 11 88082) (prefixPartial 11 88082) = false := by
  decide +kernel

theorem node_context_11_88082_1198509 : EJMOriginalGlobalDAGData.nodes 10 ⟨1198509, by decide⟩ =
    .split (coordinate 11) (![⟨1198405, by decide⟩,⟨896706, by decide⟩,⟨1198450, by decide⟩,⟨1198508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88082_1198509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88082 ⟨1198509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88082
    ⟨1198509, by decide⟩ (by decide) (![⟨1198405, by decide⟩,⟨896706, by decide⟩,⟨1198450, by decide⟩,⟨1198508, by decide⟩]) unmarked_context_11_88082_1198509 node_context_11_88082_1198509
  intro a
  fin_cases a
  · exact context_12_352328_1198405
  · exact context_12_352329_896706
  · exact context_12_352330_1198450
  · exact context_12_352331_1198508

theorem selected_cut_43710 : selected 9 ⟨1198534, by decide⟩
    (prefixPartial 12 352332) = some ⟨12, 2, 0, 1198534, 352332, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_352332_1198534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352332 ⟨1198534, by decide⟩ :=
  accepted_of_selected 12 352332 ⟨1198534, by decide⟩ ⟨12, 2, 0, 1198534, 352332, 1537, 65536⟩
    (by decide) selected_cut_43710

theorem selected_cut_43711 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352333) = some ⟨12, 1, 0, 896706, 352333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352333_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352333 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352333 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352333, 1, 65536⟩
    (by decide) selected_cut_43711

theorem selected_cut_43712 : selected 9 ⟨1198574, by decide⟩
    (prefixPartial 12 352334) = some ⟨12, 2, 0, 1198574, 352334, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_352334_1198574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352334 ⟨1198574, by decide⟩ :=
  accepted_of_selected 12 352334 ⟨1198574, by decide⟩ ⟨12, 2, 0, 1198574, 352334, 1869, 65536⟩
    (by decide) selected_cut_43712

theorem selected_cut_43713 : selected 9 ⟨1198615, by decide⟩
    (prefixPartial 12 352335) = some ⟨12, 2, 0, 1198615, 352335, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_352335_1198615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352335 ⟨1198615, by decide⟩ :=
  accepted_of_selected 12 352335 ⟨1198615, by decide⟩ ⟨12, 2, 0, 1198615, 352335, 1945, 65536⟩
    (by decide) selected_cut_43713

theorem unmarked_context_11_88083_1198616 : frontier 10 ⟨1198616, by decide⟩
    (prefixCache 11 88083) (prefixPartial 11 88083) = false := by
  decide +kernel

theorem node_context_11_88083_1198616 : EJMOriginalGlobalDAGData.nodes 10 ⟨1198616, by decide⟩ =
    .split (coordinate 11) (![⟨1198534, by decide⟩,⟨896706, by decide⟩,⟨1198574, by decide⟩,⟨1198615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88083_1198616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88083 ⟨1198616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88083
    ⟨1198616, by decide⟩ (by decide) (![⟨1198534, by decide⟩,⟨896706, by decide⟩,⟨1198574, by decide⟩,⟨1198615, by decide⟩]) unmarked_context_11_88083_1198616 node_context_11_88083_1198616
  intro a
  fin_cases a
  · exact context_12_352332_1198534
  · exact context_12_352333_896706
  · exact context_12_352334_1198574
  · exact context_12_352335_1198615

theorem unmarked_context_10_22020_1198617 : frontier 11 ⟨1198617, by decide⟩
    (prefixCache 10 22020) (prefixPartial 10 22020) = false := by
  decide +kernel

theorem node_context_10_22020_1198617 : EJMOriginalGlobalDAGData.nodes 11 ⟨1198617, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1198370, by decide⟩,⟨1198509, by decide⟩,⟨1198616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22020_1198617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22020 ⟨1198617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22020
    ⟨1198617, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1198370, by decide⟩,⟨1198509, by decide⟩,⟨1198616, by decide⟩]) unmarked_context_10_22020_1198617 node_context_10_22020_1198617
  intro a
  fin_cases a
  · exact context_11_88080_907917
  · exact context_11_88081_1198370
  · exact context_11_88082_1198509
  · exact context_11_88083_1198616

theorem selected_cut_43714 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22021) = some ⟨10, 1, 0, 893098, 22021, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22021_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22021 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22021 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22021, 1, 1048576⟩
    (by decide) selected_cut_43714

theorem selected_cut_43715 : selected 10 ⟨1198661, by decide⟩
    (prefixPartial 11 88088) = some ⟨11, 2, 0, 1198661, 88088, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_88088_1198661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88088 ⟨1198661, by decide⟩ :=
  accepted_of_selected 11 88088 ⟨1198661, by decide⟩ ⟨11, 2, 0, 1198661, 88088, 2961, 262144⟩
    (by decide) selected_cut_43715

theorem selected_cut_43716 : selected 9 ⟨1198689, by decide⟩
    (prefixPartial 12 352356) = some ⟨12, 2, 0, 1198689, 352356, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_352356_1198689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352356 ⟨1198689, by decide⟩ :=
  accepted_of_selected 12 352356 ⟨1198689, by decide⟩ ⟨12, 2, 0, 1198689, 352356, 1517, 65536⟩
    (by decide) selected_cut_43716

theorem selected_cut_43717 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352357) = some ⟨12, 1, 0, 896706, 352357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352357_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352357 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352357 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352357, 1, 65536⟩
    (by decide) selected_cut_43717

theorem selected_cut_43718 : selected 9 ⟨1198713, by decide⟩
    (prefixPartial 12 352358) = some ⟨12, 2, 0, 1198713, 352358, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_352358_1198713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352358 ⟨1198713, by decide⟩ :=
  accepted_of_selected 12 352358 ⟨1198713, by decide⟩ ⟨12, 2, 0, 1198713, 352358, 1481, 65536⟩
    (by decide) selected_cut_43718

theorem selected_cut_43719 : selected 9 ⟨1198743, by decide⟩
    (prefixPartial 12 352359) = some ⟨12, 2, 0, 1198743, 352359, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_352359_1198743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352359 ⟨1198743, by decide⟩ :=
  accepted_of_selected 12 352359 ⟨1198743, by decide⟩ ⟨12, 2, 0, 1198743, 352359, 1641, 65536⟩
    (by decide) selected_cut_43719

theorem unmarked_context_11_88089_1198744 : frontier 10 ⟨1198744, by decide⟩
    (prefixCache 11 88089) (prefixPartial 11 88089) = false := by
  decide +kernel

theorem node_context_11_88089_1198744 : EJMOriginalGlobalDAGData.nodes 10 ⟨1198744, by decide⟩ =
    .split (coordinate 11) (![⟨1198689, by decide⟩,⟨896706, by decide⟩,⟨1198713, by decide⟩,⟨1198743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88089_1198744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88089 ⟨1198744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88089
    ⟨1198744, by decide⟩ (by decide) (![⟨1198689, by decide⟩,⟨896706, by decide⟩,⟨1198713, by decide⟩,⟨1198743, by decide⟩]) unmarked_context_11_88089_1198744 node_context_11_88089_1198744
  intro a
  fin_cases a
  · exact context_12_352356_1198689
  · exact context_12_352357_896706
  · exact context_12_352358_1198713
  · exact context_12_352359_1198743

theorem selected_cut_43720 : selected 10 ⟨1198803, by decide⟩
    (prefixPartial 11 88090) = some ⟨11, 2, 0, 1198803, 88090, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_88090_1198803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88090 ⟨1198803, by decide⟩ :=
  accepted_of_selected 11 88090 ⟨1198803, by decide⟩ ⟨11, 2, 0, 1198803, 88090, 3249, 262144⟩
    (by decide) selected_cut_43720

theorem selected_cut_43721 : selected 9 ⟨1198831, by decide⟩
    (prefixPartial 12 352364) = some ⟨12, 2, 0, 1198831, 352364, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_352364_1198831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352364 ⟨1198831, by decide⟩ :=
  accepted_of_selected 12 352364 ⟨1198831, by decide⟩ ⟨12, 2, 0, 1198831, 352364, 1605, 65536⟩
    (by decide) selected_cut_43721

theorem selected_cut_43722 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352365) = some ⟨12, 1, 0, 896706, 352365, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352365_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352365 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352365 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352365, 1, 65536⟩
    (by decide) selected_cut_43722

theorem selected_cut_43723 : selected 9 ⟨1198863, by decide⟩
    (prefixPartial 12 352366) = some ⟨12, 2, 0, 1198863, 352366, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_352366_1198863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352366 ⟨1198863, by decide⟩ :=
  accepted_of_selected 12 352366 ⟨1198863, by decide⟩ ⟨12, 2, 0, 1198863, 352366, 1697, 65536⟩
    (by decide) selected_cut_43723

theorem selected_cut_43724 : selected 9 ⟨1198896, by decide⟩
    (prefixPartial 12 352367) = some ⟨12, 2, 0, 1198896, 352367, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_352367_1198896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352367 ⟨1198896, by decide⟩ :=
  accepted_of_selected 12 352367 ⟨1198896, by decide⟩ ⟨12, 2, 0, 1198896, 352367, 1769, 65536⟩
    (by decide) selected_cut_43724

theorem unmarked_context_11_88091_1198897 : frontier 10 ⟨1198897, by decide⟩
    (prefixCache 11 88091) (prefixPartial 11 88091) = false := by
  decide +kernel

theorem node_context_11_88091_1198897 : EJMOriginalGlobalDAGData.nodes 10 ⟨1198897, by decide⟩ =
    .split (coordinate 11) (![⟨1198831, by decide⟩,⟨896706, by decide⟩,⟨1198863, by decide⟩,⟨1198896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88091_1198897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88091 ⟨1198897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88091
    ⟨1198897, by decide⟩ (by decide) (![⟨1198831, by decide⟩,⟨896706, by decide⟩,⟨1198863, by decide⟩,⟨1198896, by decide⟩]) unmarked_context_11_88091_1198897 node_context_11_88091_1198897
  intro a
  fin_cases a
  · exact context_12_352364_1198831
  · exact context_12_352365_896706
  · exact context_12_352366_1198863
  · exact context_12_352367_1198896

theorem unmarked_context_10_22022_1198898 : frontier 11 ⟨1198898, by decide⟩
    (prefixCache 10 22022) (prefixPartial 10 22022) = false := by
  decide +kernel

theorem node_context_10_22022_1198898 : EJMOriginalGlobalDAGData.nodes 11 ⟨1198898, by decide⟩ =
    .split (coordinate 10) (![⟨1198661, by decide⟩,⟨1198744, by decide⟩,⟨1198803, by decide⟩,⟨1198897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22022_1198898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22022 ⟨1198898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22022
    ⟨1198898, by decide⟩ (by decide) (![⟨1198661, by decide⟩,⟨1198744, by decide⟩,⟨1198803, by decide⟩,⟨1198897, by decide⟩]) unmarked_context_10_22022_1198898 node_context_10_22022_1198898
  intro a
  fin_cases a
  · exact context_11_88088_1198661
  · exact context_11_88089_1198744
  · exact context_11_88090_1198803
  · exact context_11_88091_1198897

theorem selected_cut_43725 : selected 10 ⟨1198946, by decide⟩
    (prefixPartial 11 88092) = some ⟨11, 2, 0, 1198946, 88092, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_88092_1198946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88092 ⟨1198946, by decide⟩ :=
  accepted_of_selected 11 88092 ⟨1198946, by decide⟩ ⟨11, 2, 0, 1198946, 88092, 2737, 262144⟩
    (by decide) selected_cut_43725

theorem selected_cut_43726 : selected 9 ⟨1198967, by decide⟩
    (prefixPartial 12 352372) = some ⟨12, 2, 0, 1198967, 352372, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_352372_1198967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352372 ⟨1198967, by decide⟩ :=
  accepted_of_selected 12 352372 ⟨1198967, by decide⟩ ⟨12, 2, 0, 1198967, 352372, 1429, 65536⟩
    (by decide) selected_cut_43726

theorem selected_cut_43727 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352373) = some ⟨12, 1, 0, 896706, 352373, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352373_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352373 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352373 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352373, 1, 65536⟩
    (by decide) selected_cut_43727

theorem selected_cut_43728 : selected 9 ⟨1198991, by decide⟩
    (prefixPartial 12 352374) = some ⟨12, 2, 0, 1198991, 352374, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_352374_1198991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352374 ⟨1198991, by decide⟩ :=
  accepted_of_selected 12 352374 ⟨1198991, by decide⟩ ⟨12, 2, 0, 1198991, 352374, 1341, 65536⟩
    (by decide) selected_cut_43728

theorem selected_cut_43729 : selected 9 ⟨1199020, by decide⟩
    (prefixPartial 12 352375) = some ⟨12, 2, 0, 1199020, 352375, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_352375_1199020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352375 ⟨1199020, by decide⟩ :=
  accepted_of_selected 12 352375 ⟨1199020, by decide⟩ ⟨12, 2, 0, 1199020, 352375, 1509, 65536⟩
    (by decide) selected_cut_43729

theorem unmarked_context_11_88093_1199021 : frontier 10 ⟨1199021, by decide⟩
    (prefixCache 11 88093) (prefixPartial 11 88093) = false := by
  decide +kernel

theorem node_context_11_88093_1199021 : EJMOriginalGlobalDAGData.nodes 10 ⟨1199021, by decide⟩ =
    .split (coordinate 11) (![⟨1198967, by decide⟩,⟨896706, by decide⟩,⟨1198991, by decide⟩,⟨1199020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88093_1199021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88093 ⟨1199021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88093
    ⟨1199021, by decide⟩ (by decide) (![⟨1198967, by decide⟩,⟨896706, by decide⟩,⟨1198991, by decide⟩,⟨1199020, by decide⟩]) unmarked_context_11_88093_1199021 node_context_11_88093_1199021
  intro a
  fin_cases a
  · exact context_12_352372_1198967
  · exact context_12_352373_896706
  · exact context_12_352374_1198991
  · exact context_12_352375_1199020

theorem selected_cut_43730 : selected 9 ⟨1199042, by decide⟩
    (prefixPartial 12 352376) = some ⟨12, 2, 0, 1199042, 352376, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_352376_1199042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352376 ⟨1199042, by decide⟩ :=
  accepted_of_selected 12 352376 ⟨1199042, by decide⟩ ⟨12, 2, 0, 1199042, 352376, 1409, 65536⟩
    (by decide) selected_cut_43730

theorem selected_cut_43731 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352377) = some ⟨12, 1, 0, 896706, 352377, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352377_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352377 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352377 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352377, 1, 65536⟩
    (by decide) selected_cut_43731

theorem selected_cut_43732 : selected 9 ⟨1199064, by decide⟩
    (prefixPartial 12 352378) = some ⟨12, 2, 0, 1199064, 352378, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_352378_1199064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352378 ⟨1199064, by decide⟩ :=
  accepted_of_selected 12 352378 ⟨1199064, by decide⟩ ⟨12, 2, 0, 1199064, 352378, 1421, 65536⟩
    (by decide) selected_cut_43732

theorem selected_cut_43733 : selected 9 ⟨1199095, by decide⟩
    (prefixPartial 12 352379) = some ⟨12, 2, 0, 1199095, 352379, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_352379_1199095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352379 ⟨1199095, by decide⟩ :=
  accepted_of_selected 12 352379 ⟨1199095, by decide⟩ ⟨12, 2, 0, 1199095, 352379, 1561, 65536⟩
    (by decide) selected_cut_43733

theorem unmarked_context_11_88094_1199096 : frontier 10 ⟨1199096, by decide⟩
    (prefixCache 11 88094) (prefixPartial 11 88094) = false := by
  decide +kernel

theorem node_context_11_88094_1199096 : EJMOriginalGlobalDAGData.nodes 10 ⟨1199096, by decide⟩ =
    .split (coordinate 11) (![⟨1199042, by decide⟩,⟨896706, by decide⟩,⟨1199064, by decide⟩,⟨1199095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88094_1199096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88094 ⟨1199096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88094
    ⟨1199096, by decide⟩ (by decide) (![⟨1199042, by decide⟩,⟨896706, by decide⟩,⟨1199064, by decide⟩,⟨1199095, by decide⟩]) unmarked_context_11_88094_1199096 node_context_11_88094_1199096
  intro a
  fin_cases a
  · exact context_12_352376_1199042
  · exact context_12_352377_896706
  · exact context_12_352378_1199064
  · exact context_12_352379_1199095

theorem selected_cut_43734 : selected 10 ⟨1199144, by decide⟩
    (prefixPartial 11 88095) = some ⟨11, 2, 0, 1199144, 88095, 2677, 262144⟩ := by
  decide +kernel

theorem context_11_88095_1199144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88095 ⟨1199144, by decide⟩ :=
  accepted_of_selected 11 88095 ⟨1199144, by decide⟩ ⟨11, 2, 0, 1199144, 88095, 2677, 262144⟩
    (by decide) selected_cut_43734

theorem unmarked_context_10_22023_1199145 : frontier 11 ⟨1199145, by decide⟩
    (prefixCache 10 22023) (prefixPartial 10 22023) = false := by
  decide +kernel

theorem node_context_10_22023_1199145 : EJMOriginalGlobalDAGData.nodes 11 ⟨1199145, by decide⟩ =
    .split (coordinate 10) (![⟨1198946, by decide⟩,⟨1199021, by decide⟩,⟨1199096, by decide⟩,⟨1199144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22023_1199145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22023 ⟨1199145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22023
    ⟨1199145, by decide⟩ (by decide) (![⟨1198946, by decide⟩,⟨1199021, by decide⟩,⟨1199096, by decide⟩,⟨1199144, by decide⟩]) unmarked_context_10_22023_1199145 node_context_10_22023_1199145
  intro a
  fin_cases a
  · exact context_11_88092_1198946
  · exact context_11_88093_1199021
  · exact context_11_88094_1199096
  · exact context_11_88095_1199144

theorem unmarked_context_9_5505_1199146 : frontier 12 ⟨1199146, by decide⟩
    (prefixCache 9 5505) (prefixPartial 9 5505) = false := by
  decide +kernel

theorem node_context_9_5505_1199146 : EJMOriginalGlobalDAGData.nodes 12 ⟨1199146, by decide⟩ =
    .split (coordinate 9) (![⟨1198617, by decide⟩,⟨893098, by decide⟩,⟨1198898, by decide⟩,⟨1199145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5505_1199146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5505 ⟨1199146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5505
    ⟨1199146, by decide⟩ (by decide) (![⟨1198617, by decide⟩,⟨893098, by decide⟩,⟨1198898, by decide⟩,⟨1199145, by decide⟩]) unmarked_context_9_5505_1199146 node_context_9_5505_1199146
  intro a
  fin_cases a
  · exact context_10_22020_1198617
  · exact context_10_22021_893098
  · exact context_10_22022_1198898
  · exact context_10_22023_1199145

theorem selected_cut_43735 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88096) = some ⟨11, 1, 0, 907917, 88096, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88096_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88096 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88096 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88096, 1, 262144⟩
    (by decide) selected_cut_43735

theorem selected_cut_43736 : selected 9 ⟨1199168, by decide⟩
    (prefixPartial 12 352388) = some ⟨12, 2, 0, 1199168, 352388, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_352388_1199168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352388 ⟨1199168, by decide⟩ :=
  accepted_of_selected 12 352388 ⟨1199168, by decide⟩ ⟨12, 2, 0, 1199168, 352388, 1261, 65536⟩
    (by decide) selected_cut_43736

theorem selected_cut_43737 : selected 9 ⟨1199195, by decide⟩
    (prefixPartial 12 352389) = some ⟨12, 2, 0, 1199195, 352389, 465, 65536⟩ := by
  decide +kernel

theorem context_12_352389_1199195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352389 ⟨1199195, by decide⟩ :=
  accepted_of_selected 12 352389 ⟨1199195, by decide⟩ ⟨12, 2, 0, 1199195, 352389, 465, 65536⟩
    (by decide) selected_cut_43737

theorem selected_cut_43738 : selected 9 ⟨1199219, by decide⟩
    (prefixPartial 12 352390) = some ⟨12, 2, 0, 1199219, 352390, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_352390_1199219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352390 ⟨1199219, by decide⟩ :=
  accepted_of_selected 12 352390 ⟨1199219, by decide⟩ ⟨12, 2, 0, 1199219, 352390, 1389, 65536⟩
    (by decide) selected_cut_43738

theorem selected_cut_43739 : selected 9 ⟨1199244, by decide⟩
    (prefixPartial 12 352391) = some ⟨12, 2, 0, 1199244, 352391, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_352391_1199244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352391 ⟨1199244, by decide⟩ :=
  accepted_of_selected 12 352391 ⟨1199244, by decide⟩ ⟨12, 2, 0, 1199244, 352391, 1329, 65536⟩
    (by decide) selected_cut_43739

theorem unmarked_context_11_88097_1199245 : frontier 10 ⟨1199245, by decide⟩
    (prefixCache 11 88097) (prefixPartial 11 88097) = false := by
  decide +kernel

theorem node_context_11_88097_1199245 : EJMOriginalGlobalDAGData.nodes 10 ⟨1199245, by decide⟩ =
    .split (coordinate 11) (![⟨1199168, by decide⟩,⟨1199195, by decide⟩,⟨1199219, by decide⟩,⟨1199244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88097_1199245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88097 ⟨1199245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88097
    ⟨1199245, by decide⟩ (by decide) (![⟨1199168, by decide⟩,⟨1199195, by decide⟩,⟨1199219, by decide⟩,⟨1199244, by decide⟩]) unmarked_context_11_88097_1199245 node_context_11_88097_1199245
  intro a
  fin_cases a
  · exact context_12_352388_1199168
  · exact context_12_352389_1199195
  · exact context_12_352390_1199219
  · exact context_12_352391_1199244

theorem selected_cut_43740 : selected 9 ⟨1199274, by decide⟩
    (prefixPartial 12 352392) = some ⟨12, 2, 0, 1199274, 352392, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_352392_1199274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352392 ⟨1199274, by decide⟩ :=
  accepted_of_selected 12 352392 ⟨1199274, by decide⟩ ⟨12, 2, 0, 1199274, 352392, 1413, 65536⟩
    (by decide) selected_cut_43740

theorem selected_cut_43741 : selected 9 ⟨1199299, by decide⟩
    (prefixPartial 12 352393) = some ⟨12, 2, 0, 1199299, 352393, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_352393_1199299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352393 ⟨1199299, by decide⟩ :=
  accepted_of_selected 12 352393 ⟨1199299, by decide⟩ ⟨12, 2, 0, 1199299, 352393, 1373, 65536⟩
    (by decide) selected_cut_43741

theorem selected_cut_43742 : selected 9 ⟨188189, by decide⟩
    (prefixPartial 12 352394) = some ⟨12, 1, 0, 188189, 352394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352394_188189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352394 ⟨188189, by decide⟩ :=
  accepted_of_selected 12 352394 ⟨188189, by decide⟩ ⟨12, 1, 0, 188189, 352394, 1, 65536⟩
    (by decide) selected_cut_43742

theorem selected_cut_43743 : selected 9 ⟨1199330, by decide⟩
    (prefixPartial 12 352395) = some ⟨12, 2, 0, 1199330, 352395, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_352395_1199330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352395 ⟨1199330, by decide⟩ :=
  accepted_of_selected 12 352395 ⟨1199330, by decide⟩ ⟨12, 2, 0, 1199330, 352395, 1597, 65536⟩
    (by decide) selected_cut_43743

theorem unmarked_context_11_88098_1199331 : frontier 10 ⟨1199331, by decide⟩
    (prefixCache 11 88098) (prefixPartial 11 88098) = false := by
  decide +kernel

theorem node_context_11_88098_1199331 : EJMOriginalGlobalDAGData.nodes 10 ⟨1199331, by decide⟩ =
    .split (coordinate 11) (![⟨1199274, by decide⟩,⟨1199299, by decide⟩,⟨188189, by decide⟩,⟨1199330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88098_1199331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88098 ⟨1199331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88098
    ⟨1199331, by decide⟩ (by decide) (![⟨1199274, by decide⟩,⟨1199299, by decide⟩,⟨188189, by decide⟩,⟨1199330, by decide⟩]) unmarked_context_11_88098_1199331 node_context_11_88098_1199331
  intro a
  fin_cases a
  · exact context_12_352392_1199274
  · exact context_12_352393_1199299
  · exact context_12_352394_188189
  · exact context_12_352395_1199330

theorem selected_cut_43744 : selected 9 ⟨1199352, by decide⟩
    (prefixPartial 12 352396) = some ⟨12, 2, 0, 1199352, 352396, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_352396_1199352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352396 ⟨1199352, by decide⟩ :=
  accepted_of_selected 12 352396 ⟨1199352, by decide⟩ ⟨12, 2, 0, 1199352, 352396, 1125, 65536⟩
    (by decide) selected_cut_43744

theorem selected_cut_43745 : selected 9 ⟨1199376, by decide⟩
    (prefixPartial 12 352397) = some ⟨12, 2, 0, 1199376, 352397, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_352397_1199376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352397 ⟨1199376, by decide⟩ :=
  accepted_of_selected 12 352397 ⟨1199376, by decide⟩ ⟨12, 2, 0, 1199376, 352397, 1165, 65536⟩
    (by decide) selected_cut_43745

theorem selected_cut_43746 : selected 9 ⟨1199400, by decide⟩
    (prefixPartial 12 352398) = some ⟨12, 2, 0, 1199400, 352398, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_352398_1199400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352398 ⟨1199400, by decide⟩ :=
  accepted_of_selected 12 352398 ⟨1199400, by decide⟩ ⟨12, 2, 0, 1199400, 352398, 1313, 65536⟩
    (by decide) selected_cut_43746

theorem selected_cut_43747 : selected 9 ⟨1199426, by decide⟩
    (prefixPartial 12 352399) = some ⟨12, 2, 0, 1199426, 352399, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_352399_1199426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352399 ⟨1199426, by decide⟩ :=
  accepted_of_selected 12 352399 ⟨1199426, by decide⟩ ⟨12, 2, 0, 1199426, 352399, 1329, 65536⟩
    (by decide) selected_cut_43747

theorem unmarked_context_11_88099_1199427 : frontier 10 ⟨1199427, by decide⟩
    (prefixCache 11 88099) (prefixPartial 11 88099) = false := by
  decide +kernel

theorem node_context_11_88099_1199427 : EJMOriginalGlobalDAGData.nodes 10 ⟨1199427, by decide⟩ =
    .split (coordinate 11) (![⟨1199352, by decide⟩,⟨1199376, by decide⟩,⟨1199400, by decide⟩,⟨1199426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88099_1199427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88099 ⟨1199427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88099
    ⟨1199427, by decide⟩ (by decide) (![⟨1199352, by decide⟩,⟨1199376, by decide⟩,⟨1199400, by decide⟩,⟨1199426, by decide⟩]) unmarked_context_11_88099_1199427 node_context_11_88099_1199427
  intro a
  fin_cases a
  · exact context_12_352396_1199352
  · exact context_12_352397_1199376
  · exact context_12_352398_1199400
  · exact context_12_352399_1199426

theorem unmarked_context_10_22024_1199428 : frontier 11 ⟨1199428, by decide⟩
    (prefixCache 10 22024) (prefixPartial 10 22024) = false := by
  decide +kernel

theorem node_context_10_22024_1199428 : EJMOriginalGlobalDAGData.nodes 11 ⟨1199428, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1199245, by decide⟩,⟨1199331, by decide⟩,⟨1199427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22024_1199428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22024 ⟨1199428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22024
    ⟨1199428, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1199245, by decide⟩,⟨1199331, by decide⟩,⟨1199427, by decide⟩]) unmarked_context_10_22024_1199428 node_context_10_22024_1199428
  intro a
  fin_cases a
  · exact context_11_88096_907917
  · exact context_11_88097_1199245
  · exact context_11_88098_1199331
  · exact context_11_88099_1199427

theorem selected_cut_43748 : selected 10 ⟨1199485, by decide⟩
    (prefixPartial 11 88100) = some ⟨11, 2, 0, 1199485, 88100, 3205, 262144⟩ := by
  decide +kernel

theorem context_11_88100_1199485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88100 ⟨1199485, by decide⟩ :=
  accepted_of_selected 11 88100 ⟨1199485, by decide⟩ ⟨11, 2, 0, 1199485, 88100, 3205, 262144⟩
    (by decide) selected_cut_43748

theorem selected_cut_43749 : selected 10 ⟨1199540, by decide⟩
    (prefixPartial 11 88101) = some ⟨11, 2, 0, 1199540, 88101, 1601, 262144⟩ := by
  decide +kernel

theorem context_11_88101_1199540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88101 ⟨1199540, by decide⟩ :=
  accepted_of_selected 11 88101 ⟨1199540, by decide⟩ ⟨11, 2, 0, 1199540, 88101, 1601, 262144⟩
    (by decide) selected_cut_43749

theorem selected_cut_43750 : selected 10 ⟨1199620, by decide⟩
    (prefixPartial 11 88102) = some ⟨11, 2, 0, 1199620, 88102, 3717, 262144⟩ := by
  decide +kernel

theorem context_11_88102_1199620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88102 ⟨1199620, by decide⟩ :=
  accepted_of_selected 11 88102 ⟨1199620, by decide⟩ ⟨11, 2, 0, 1199620, 88102, 3717, 262144⟩
    (by decide) selected_cut_43750

theorem selected_cut_43751 : selected 9 ⟨1199640, by decide⟩
    (prefixPartial 12 352412) = some ⟨12, 2, 0, 1199640, 352412, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_352412_1199640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352412 ⟨1199640, by decide⟩ :=
  accepted_of_selected 12 352412 ⟨1199640, by decide⟩ ⟨12, 2, 0, 1199640, 352412, 1081, 65536⟩
    (by decide) selected_cut_43751

theorem selected_cut_43752 : selected 9 ⟨1199656, by decide⟩
    (prefixPartial 12 352413) = some ⟨12, 2, 0, 1199656, 352413, 989, 65536⟩ := by
  decide +kernel

theorem context_12_352413_1199656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352413 ⟨1199656, by decide⟩ :=
  accepted_of_selected 12 352413 ⟨1199656, by decide⟩ ⟨12, 2, 0, 1199656, 352413, 989, 65536⟩
    (by decide) selected_cut_43752

theorem selected_cut_43753 : selected 9 ⟨1199681, by decide⟩
    (prefixPartial 12 352414) = some ⟨12, 2, 0, 1199681, 352414, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_352414_1199681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352414 ⟨1199681, by decide⟩ :=
  accepted_of_selected 12 352414 ⟨1199681, by decide⟩ ⟨12, 2, 0, 1199681, 352414, 1197, 65536⟩
    (by decide) selected_cut_43753

theorem selected_cut_43754 : selected 9 ⟨1199699, by decide⟩
    (prefixPartial 12 352415) = some ⟨12, 2, 0, 1199699, 352415, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_352415_1199699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352415 ⟨1199699, by decide⟩ :=
  accepted_of_selected 12 352415 ⟨1199699, by decide⟩ ⟨12, 2, 0, 1199699, 352415, 1145, 65536⟩
    (by decide) selected_cut_43754

theorem unmarked_context_11_88103_1199700 : frontier 10 ⟨1199700, by decide⟩
    (prefixCache 11 88103) (prefixPartial 11 88103) = false := by
  decide +kernel

theorem node_context_11_88103_1199700 : EJMOriginalGlobalDAGData.nodes 10 ⟨1199700, by decide⟩ =
    .split (coordinate 11) (![⟨1199640, by decide⟩,⟨1199656, by decide⟩,⟨1199681, by decide⟩,⟨1199699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88103_1199700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88103 ⟨1199700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88103
    ⟨1199700, by decide⟩ (by decide) (![⟨1199640, by decide⟩,⟨1199656, by decide⟩,⟨1199681, by decide⟩,⟨1199699, by decide⟩]) unmarked_context_11_88103_1199700 node_context_11_88103_1199700
  intro a
  fin_cases a
  · exact context_12_352412_1199640
  · exact context_12_352413_1199656
  · exact context_12_352414_1199681
  · exact context_12_352415_1199699

theorem unmarked_context_10_22025_1199701 : frontier 11 ⟨1199701, by decide⟩
    (prefixCache 10 22025) (prefixPartial 10 22025) = false := by
  decide +kernel

theorem node_context_10_22025_1199701 : EJMOriginalGlobalDAGData.nodes 11 ⟨1199701, by decide⟩ =
    .split (coordinate 10) (![⟨1199485, by decide⟩,⟨1199540, by decide⟩,⟨1199620, by decide⟩,⟨1199700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22025_1199701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22025 ⟨1199701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22025
    ⟨1199701, by decide⟩ (by decide) (![⟨1199485, by decide⟩,⟨1199540, by decide⟩,⟨1199620, by decide⟩,⟨1199700, by decide⟩]) unmarked_context_10_22025_1199701 node_context_10_22025_1199701
  intro a
  fin_cases a
  · exact context_11_88100_1199485
  · exact context_11_88101_1199540
  · exact context_11_88102_1199620
  · exact context_11_88103_1199700

theorem selected_cut_43755 : selected 10 ⟨1199732, by decide⟩
    (prefixPartial 11 88104) = some ⟨11, 2, 0, 1199732, 88104, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_88104_1199732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88104 ⟨1199732, by decide⟩ :=
  accepted_of_selected 11 88104 ⟨1199732, by decide⟩ ⟨11, 2, 0, 1199732, 88104, 1697, 262144⟩
    (by decide) selected_cut_43755

theorem selected_cut_43756 : selected 10 ⟨1199766, by decide⟩
    (prefixPartial 11 88105) = some ⟨11, 2, 0, 1199766, 88105, 1837, 262144⟩ := by
  decide +kernel

theorem context_11_88105_1199766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88105 ⟨1199766, by decide⟩ :=
  accepted_of_selected 11 88105 ⟨1199766, by decide⟩ ⟨11, 2, 0, 1199766, 88105, 1837, 262144⟩
    (by decide) selected_cut_43756

theorem selected_cut_43757 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 88106) = some ⟨11, 1, 0, 1109453, 88106, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88106_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88106 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 88106 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 88106, 1, 262144⟩
    (by decide) selected_cut_43757

theorem selected_cut_43758 : selected 10 ⟨1199819, by decide⟩
    (prefixPartial 11 88107) = some ⟨11, 2, 0, 1199819, 88107, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_88107_1199819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88107 ⟨1199819, by decide⟩ :=
  accepted_of_selected 11 88107 ⟨1199819, by decide⟩ ⟨11, 2, 0, 1199819, 88107, 2725, 262144⟩
    (by decide) selected_cut_43758

theorem unmarked_context_10_22026_1199820 : frontier 11 ⟨1199820, by decide⟩
    (prefixCache 10 22026) (prefixPartial 10 22026) = false := by
  decide +kernel

theorem node_context_10_22026_1199820 : EJMOriginalGlobalDAGData.nodes 11 ⟨1199820, by decide⟩ =
    .split (coordinate 10) (![⟨1199732, by decide⟩,⟨1199766, by decide⟩,⟨1109453, by decide⟩,⟨1199819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22026_1199820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22026 ⟨1199820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22026
    ⟨1199820, by decide⟩ (by decide) (![⟨1199732, by decide⟩,⟨1199766, by decide⟩,⟨1109453, by decide⟩,⟨1199819, by decide⟩]) unmarked_context_10_22026_1199820 node_context_10_22026_1199820
  intro a
  fin_cases a
  · exact context_11_88104_1199732
  · exact context_11_88105_1199766
  · exact context_11_88106_1109453
  · exact context_11_88107_1199819

theorem selected_cut_43759 : selected 10 ⟨1199861, by decide⟩
    (prefixPartial 11 88108) = some ⟨11, 2, 0, 1199861, 88108, 2185, 262144⟩ := by
  decide +kernel

theorem context_11_88108_1199861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88108 ⟨1199861, by decide⟩ :=
  accepted_of_selected 11 88108 ⟨1199861, by decide⟩ ⟨11, 2, 0, 1199861, 88108, 2185, 262144⟩
    (by decide) selected_cut_43759

theorem selected_cut_43760 : selected 10 ⟨1199911, by decide⟩
    (prefixPartial 11 88109) = some ⟨11, 2, 0, 1199911, 88109, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_88109_1199911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88109 ⟨1199911, by decide⟩ :=
  accepted_of_selected 11 88109 ⟨1199911, by decide⟩ ⟨11, 2, 0, 1199911, 88109, 2897, 262144⟩
    (by decide) selected_cut_43760

theorem selected_cut_43761 : selected 10 ⟨1199961, by decide⟩
    (prefixPartial 11 88110) = some ⟨11, 2, 0, 1199961, 88110, 2181, 262144⟩ := by
  decide +kernel

theorem context_11_88110_1199961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88110 ⟨1199961, by decide⟩ :=
  accepted_of_selected 11 88110 ⟨1199961, by decide⟩ ⟨11, 2, 0, 1199961, 88110, 2181, 262144⟩
    (by decide) selected_cut_43761

theorem selected_cut_43762 : selected 10 ⟨1199998, by decide⟩
    (prefixPartial 11 88111) = some ⟨11, 2, 0, 1199998, 88111, 1893, 262144⟩ := by
  decide +kernel

theorem context_11_88111_1199998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88111 ⟨1199998, by decide⟩ :=
  accepted_of_selected 11 88111 ⟨1199998, by decide⟩ ⟨11, 2, 0, 1199998, 88111, 1893, 262144⟩
    (by decide) selected_cut_43762

theorem unmarked_context_10_22027_1199999 : frontier 11 ⟨1199999, by decide⟩
    (prefixCache 10 22027) (prefixPartial 10 22027) = false := by
  decide +kernel

theorem node_context_10_22027_1199999 : EJMOriginalGlobalDAGData.nodes 11 ⟨1199999, by decide⟩ =
    .split (coordinate 10) (![⟨1199861, by decide⟩,⟨1199911, by decide⟩,⟨1199961, by decide⟩,⟨1199998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22027_1199999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22027 ⟨1199999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22027
    ⟨1199999, by decide⟩ (by decide) (![⟨1199861, by decide⟩,⟨1199911, by decide⟩,⟨1199961, by decide⟩,⟨1199998, by decide⟩]) unmarked_context_10_22027_1199999 node_context_10_22027_1199999
  intro a
  fin_cases a
  · exact context_11_88108_1199861
  · exact context_11_88109_1199911
  · exact context_11_88110_1199961
  · exact context_11_88111_1199998

theorem unmarked_context_9_5506_1200000 : frontier 12 ⟨1200000, by decide⟩
    (prefixCache 9 5506) (prefixPartial 9 5506) = false := by
  decide +kernel

theorem node_context_9_5506_1200000 : EJMOriginalGlobalDAGData.nodes 12 ⟨1200000, by decide⟩ =
    .split (coordinate 9) (![⟨1199428, by decide⟩,⟨1199701, by decide⟩,⟨1199820, by decide⟩,⟨1199999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5506_1200000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5506 ⟨1200000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5506
    ⟨1200000, by decide⟩ (by decide) (![⟨1199428, by decide⟩,⟨1199701, by decide⟩,⟨1199820, by decide⟩,⟨1199999, by decide⟩]) unmarked_context_9_5506_1200000 node_context_9_5506_1200000
  intro a
  fin_cases a
  · exact context_10_22024_1199428
  · exact context_10_22025_1199701
  · exact context_10_22026_1199820
  · exact context_10_22027_1199999

theorem selected_cut_43763 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88112) = some ⟨11, 1, 0, 907917, 88112, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88112_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88112 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88112 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88112, 1, 262144⟩
    (by decide) selected_cut_43763

theorem selected_cut_43764 : selected 10 ⟨1200032, by decide⟩
    (prefixPartial 11 88113) = some ⟨11, 2, 0, 1200032, 88113, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_88113_1200032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88113 ⟨1200032, by decide⟩ :=
  accepted_of_selected 11 88113 ⟨1200032, by decide⟩ ⟨11, 2, 0, 1200032, 88113, 1537, 262144⟩
    (by decide) selected_cut_43764

theorem selected_cut_43765 : selected 10 ⟨1200068, by decide⟩
    (prefixPartial 11 88114) = some ⟨11, 2, 0, 1200068, 88114, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_88114_1200068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88114 ⟨1200068, by decide⟩ :=
  accepted_of_selected 11 88114 ⟨1200068, by decide⟩ ⟨11, 2, 0, 1200068, 88114, 1825, 262144⟩
    (by decide) selected_cut_43765

theorem selected_cut_43766 : selected 10 ⟨1200091, by decide⟩
    (prefixPartial 11 88115) = some ⟨11, 2, 0, 1200091, 88115, 1241, 262144⟩ := by
  decide +kernel

theorem context_11_88115_1200091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88115 ⟨1200091, by decide⟩ :=
  accepted_of_selected 11 88115 ⟨1200091, by decide⟩ ⟨11, 2, 0, 1200091, 88115, 1241, 262144⟩
    (by decide) selected_cut_43766

theorem unmarked_context_10_22028_1200092 : frontier 11 ⟨1200092, by decide⟩
    (prefixCache 10 22028) (prefixPartial 10 22028) = false := by
  decide +kernel

theorem node_context_10_22028_1200092 : EJMOriginalGlobalDAGData.nodes 11 ⟨1200092, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1200032, by decide⟩,⟨1200068, by decide⟩,⟨1200091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22028_1200092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22028 ⟨1200092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22028
    ⟨1200092, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1200032, by decide⟩,⟨1200068, by decide⟩,⟨1200091, by decide⟩]) unmarked_context_10_22028_1200092 node_context_10_22028_1200092
  intro a
  fin_cases a
  · exact context_11_88112_907917
  · exact context_11_88113_1200032
  · exact context_11_88114_1200068
  · exact context_11_88115_1200091

theorem selected_cut_43767 : selected 11 ⟨1200155, by decide⟩
    (prefixPartial 10 22029) = some ⟨10, 2, 0, 1200155, 22029, 3509, 1048576⟩ := by
  decide +kernel

theorem context_10_22029_1200155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22029 ⟨1200155, by decide⟩ :=
  accepted_of_selected 10 22029 ⟨1200155, by decide⟩ ⟨10, 2, 0, 1200155, 22029, 3509, 1048576⟩
    (by decide) selected_cut_43767

theorem selected_cut_43768 : selected 11 ⟨1200203, by decide⟩
    (prefixPartial 10 22030) = some ⟨10, 2, 0, 1200203, 22030, 2037, 1048576⟩ := by
  decide +kernel

theorem context_10_22030_1200203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22030 ⟨1200203, by decide⟩ :=
  accepted_of_selected 10 22030 ⟨1200203, by decide⟩ ⟨10, 2, 0, 1200203, 22030, 2037, 1048576⟩
    (by decide) selected_cut_43768

theorem selected_cut_43769 : selected 11 ⟨1200218, by decide⟩
    (prefixPartial 10 22031) = some ⟨10, 2, 0, 1200218, 22031, 381, 1048576⟩ := by
  decide +kernel

theorem context_10_22031_1200218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22031 ⟨1200218, by decide⟩ :=
  accepted_of_selected 10 22031 ⟨1200218, by decide⟩ ⟨10, 2, 0, 1200218, 22031, 381, 1048576⟩
    (by decide) selected_cut_43769

theorem unmarked_context_9_5507_1200219 : frontier 12 ⟨1200219, by decide⟩
    (prefixCache 9 5507) (prefixPartial 9 5507) = false := by
  decide +kernel

theorem node_context_9_5507_1200219 : EJMOriginalGlobalDAGData.nodes 12 ⟨1200219, by decide⟩ =
    .split (coordinate 9) (![⟨1200092, by decide⟩,⟨1200155, by decide⟩,⟨1200203, by decide⟩,⟨1200218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5507_1200219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5507 ⟨1200219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5507
    ⟨1200219, by decide⟩ (by decide) (![⟨1200092, by decide⟩,⟨1200155, by decide⟩,⟨1200203, by decide⟩,⟨1200218, by decide⟩]) unmarked_context_9_5507_1200219 node_context_9_5507_1200219
  intro a
  fin_cases a
  · exact context_10_22028_1200092
  · exact context_10_22029_1200155
  · exact context_10_22030_1200203
  · exact context_10_22031_1200218

theorem unmarked_context_8_1376_1200220 : frontier 13 ⟨1200220, by decide⟩
    (prefixCache 8 1376) (prefixPartial 8 1376) = false := by
  decide +kernel

theorem node_context_8_1376_1200220 : EJMOriginalGlobalDAGData.nodes 13 ⟨1200220, by decide⟩ =
    .split (coordinate 8) (![⟨1198275, by decide⟩,⟨1199146, by decide⟩,⟨1200000, by decide⟩,⟨1200219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1376_1200220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1376 ⟨1200220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1376
    ⟨1200220, by decide⟩ (by decide) (![⟨1198275, by decide⟩,⟨1199146, by decide⟩,⟨1200000, by decide⟩,⟨1200219, by decide⟩]) unmarked_context_8_1376_1200220 node_context_8_1376_1200220
  intro a
  fin_cases a
  · exact context_9_5504_1198275
  · exact context_9_5505_1199146
  · exact context_9_5506_1200000
  · exact context_9_5507_1200219

theorem selected_cut_43770 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88128) = some ⟨11, 1, 0, 434745, 88128, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88128_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88128 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88128 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88128, 1, 262144⟩
    (by decide) selected_cut_43770

theorem selected_cut_43771 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 88129) = some ⟨11, 1, 0, 167448, 88129, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88129_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88129 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 88129 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 88129, 1, 262144⟩
    (by decide) selected_cut_43771

theorem selected_cut_43772 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 352520) = some ⟨12, 1, 0, 448748, 352520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352520_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352520 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 352520 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 352520, 1, 65536⟩
    (by decide) selected_cut_43772

theorem selected_cut_43773 : selected 9 ⟨1200284, by decide⟩
    (prefixPartial 12 352521) = some ⟨12, 2, 0, 1200284, 352521, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_352521_1200284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352521 ⟨1200284, by decide⟩ :=
  accepted_of_selected 12 352521 ⟨1200284, by decide⟩ ⟨12, 2, 0, 1200284, 352521, 3013, 65536⟩
    (by decide) selected_cut_43773

theorem selected_cut_43774 : selected 9 ⟨1200344, by decide⟩
    (prefixPartial 12 352522) = some ⟨12, 2, 0, 1200344, 352522, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_352522_1200344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352522 ⟨1200344, by decide⟩ :=
  accepted_of_selected 12 352522 ⟨1200344, by decide⟩ ⟨12, 2, 0, 1200344, 352522, 2825, 65536⟩
    (by decide) selected_cut_43774

theorem selected_cut_43775 : selected 9 ⟨1200406, by decide⟩
    (prefixPartial 12 352523) = some ⟨12, 2, 0, 1200406, 352523, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_352523_1200406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352523 ⟨1200406, by decide⟩ :=
  accepted_of_selected 12 352523 ⟨1200406, by decide⟩ ⟨12, 2, 0, 1200406, 352523, 3169, 65536⟩
    (by decide) selected_cut_43775

theorem unmarked_context_11_88130_1200407 : frontier 10 ⟨1200407, by decide⟩
    (prefixCache 11 88130) (prefixPartial 11 88130) = false := by
  decide +kernel

theorem node_context_11_88130_1200407 : EJMOriginalGlobalDAGData.nodes 10 ⟨1200407, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1200284, by decide⟩,⟨1200344, by decide⟩,⟨1200406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88130_1200407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88130 ⟨1200407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88130
    ⟨1200407, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1200284, by decide⟩,⟨1200344, by decide⟩,⟨1200406, by decide⟩]) unmarked_context_11_88130_1200407 node_context_11_88130_1200407
  intro a
  fin_cases a
  · exact context_12_352520_448748
  · exact context_12_352521_1200284
  · exact context_12_352522_1200344
  · exact context_12_352523_1200406

theorem selected_cut_43776 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 352524) = some ⟨12, 1, 0, 448748, 352524, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352524_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352524 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 352524 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 352524, 1, 65536⟩
    (by decide) selected_cut_43776

theorem selected_cut_43777 : selected 9 ⟨1200435, by decide⟩
    (prefixPartial 12 352525) = some ⟨12, 2, 0, 1200435, 352525, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_352525_1200435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352525 ⟨1200435, by decide⟩ :=
  accepted_of_selected 12 352525 ⟨1200435, by decide⟩ ⟨12, 2, 0, 1200435, 352525, 1253, 65536⟩
    (by decide) selected_cut_43777

theorem selected_cut_43778 : selected 9 ⟨1200473, by decide⟩
    (prefixPartial 12 352526) = some ⟨12, 2, 0, 1200473, 352526, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_352526_1200473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352526 ⟨1200473, by decide⟩ :=
  accepted_of_selected 12 352526 ⟨1200473, by decide⟩ ⟨12, 2, 0, 1200473, 352526, 2537, 65536⟩
    (by decide) selected_cut_43778

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
