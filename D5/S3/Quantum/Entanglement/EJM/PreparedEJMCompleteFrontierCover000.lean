/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00000 : selected 9 ⟨415, by decide⟩
    (prefixPartial 12 0) = some ⟨12, 2, 0, 415, 0, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_0_415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 0 ⟨415, by decide⟩ :=
  accepted_of_selected 12 0 ⟨415, by decide⟩ ⟨12, 2, 0, 415, 0, 2061, 65536⟩
    (by decide) selected_cut_00000

theorem selected_cut_00001 : selected 8 ⟨674, by decide⟩
    (prefixPartial 13 4) = some ⟨13, 2, 0, 674, 4, 3269, 16384⟩ := by
  decide +kernel

theorem context_13_4_674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 4 ⟨674, by decide⟩ :=
  accepted_of_selected 13 4 ⟨674, by decide⟩ ⟨13, 2, 0, 674, 4, 3269, 16384⟩
    (by decide) selected_cut_00001

theorem selected_cut_00002 : selected 8 ⟨788, by decide⟩
    (prefixPartial 13 5) = some ⟨13, 2, 0, 788, 5, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_5_788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 5 ⟨788, by decide⟩ :=
  accepted_of_selected 13 5 ⟨788, by decide⟩ ⟨13, 2, 0, 788, 5, 1649, 16384⟩
    (by decide) selected_cut_00002

theorem selected_cut_00003 : selected 8 ⟨890, by decide⟩
    (prefixPartial 13 6) = some ⟨13, 2, 0, 890, 6, 993, 16384⟩ := by
  decide +kernel

theorem context_13_6_890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 6 ⟨890, by decide⟩ :=
  accepted_of_selected 13 6 ⟨890, by decide⟩ ⟨13, 2, 0, 890, 6, 993, 16384⟩
    (by decide) selected_cut_00003

theorem selected_cut_00004 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 7) = some ⟨13, 1, 0, 414, 7, 1, 16384⟩ := by
  decide +kernel

theorem context_13_7_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 7 ⟨414, by decide⟩ :=
  accepted_of_selected 13 7 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 7, 1, 16384⟩
    (by decide) selected_cut_00004

theorem unmarked_context_12_1_891 : frontier 9 ⟨891, by decide⟩
    (prefixCache 12 1) (prefixPartial 12 1) = false := by
  decide +kernel

theorem node_context_12_1_891 : EJMOriginalGlobalDAGData.nodes 9 ⟨891, by decide⟩ =
    .split (coordinate 12) (![⟨674, by decide⟩,⟨788, by decide⟩,⟨890, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_1_891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1 ⟨891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 1
    ⟨891, by decide⟩ (by decide) (![⟨674, by decide⟩,⟨788, by decide⟩,⟨890, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_1_891 node_context_12_1_891
  intro a
  fin_cases a
  · exact context_13_4_674
  · exact context_13_5_788
  · exact context_13_6_890
  · exact context_13_7_414

theorem selected_cut_00005 : selected 9 ⟨892, by decide⟩
    (prefixPartial 12 2) = some ⟨12, 1, 0, 892, 2, 1, 65536⟩ := by
  decide +kernel

theorem context_12_2_892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 2 ⟨892, by decide⟩ :=
  accepted_of_selected 12 2 ⟨892, by decide⟩ ⟨12, 1, 0, 892, 2, 1, 65536⟩
    (by decide) selected_cut_00005

theorem selected_cut_00006 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 3) = some ⟨12, 1, 0, 893, 3, 1, 65536⟩ := by
  decide +kernel

theorem context_12_3_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 3 ⟨893, by decide⟩ :=
  accepted_of_selected 12 3 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 3, 1, 65536⟩
    (by decide) selected_cut_00006

theorem unmarked_context_11_0_894 : frontier 10 ⟨894, by decide⟩
    (prefixCache 11 0) (prefixPartial 11 0) = false := by
  decide +kernel

theorem node_context_11_0_894 : EJMOriginalGlobalDAGData.nodes 10 ⟨894, by decide⟩ =
    .split (coordinate 11) (![⟨415, by decide⟩,⟨891, by decide⟩,⟨892, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_0_894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 0 ⟨894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 0
    ⟨894, by decide⟩ (by decide) (![⟨415, by decide⟩,⟨891, by decide⟩,⟨892, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_0_894 node_context_11_0_894
  intro a
  fin_cases a
  · exact context_12_0_415
  · exact context_12_1_891
  · exact context_12_2_892
  · exact context_12_3_893

theorem selected_cut_00007 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 4) = some ⟨12, 1, 0, 895, 4, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4 ⟨895, by decide⟩ :=
  accepted_of_selected 12 4 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 4, 1, 65536⟩
    (by decide) selected_cut_00007

theorem selected_cut_00008 : selected 9 ⟨1189, by decide⟩
    (prefixPartial 12 5) = some ⟨12, 2, 0, 1189, 5, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_5_1189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5 ⟨1189, by decide⟩ :=
  accepted_of_selected 12 5 ⟨1189, by decide⟩ ⟨12, 2, 0, 1189, 5, 3705, 65536⟩
    (by decide) selected_cut_00008

theorem selected_cut_00009 : selected 8 ⟨1382, by decide⟩
    (prefixPartial 13 24) = some ⟨13, 2, 0, 1382, 24, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_24_1382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 24 ⟨1382, by decide⟩ :=
  accepted_of_selected 13 24 ⟨1382, by decide⟩ ⟨13, 2, 0, 1382, 24, 2965, 16384⟩
    (by decide) selected_cut_00009

theorem selected_cut_00010 : selected 8 ⟨1598, by decide⟩
    (prefixPartial 13 25) = some ⟨13, 2, 0, 1598, 25, 2993, 16384⟩ := by
  decide +kernel

theorem context_13_25_1598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 25 ⟨1598, by decide⟩ :=
  accepted_of_selected 13 25 ⟨1598, by decide⟩ ⟨13, 2, 0, 1598, 25, 2993, 16384⟩
    (by decide) selected_cut_00010

theorem selected_cut_00011 : selected 8 ⟨1707, by decide⟩
    (prefixPartial 13 26) = some ⟨13, 2, 0, 1707, 26, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_26_1707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26 ⟨1707, by decide⟩ :=
  accepted_of_selected 13 26 ⟨1707, by decide⟩ ⟨13, 2, 0, 1707, 26, 1113, 16384⟩
    (by decide) selected_cut_00011

theorem selected_cut_00012 : selected 8 ⟨1732, by decide⟩
    (prefixPartial 13 27) = some ⟨13, 2, 0, 1732, 27, 177, 16384⟩ := by
  decide +kernel

theorem context_13_27_1732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 27 ⟨1732, by decide⟩ :=
  accepted_of_selected 13 27 ⟨1732, by decide⟩ ⟨13, 2, 0, 1732, 27, 177, 16384⟩
    (by decide) selected_cut_00012

theorem unmarked_context_12_6_1733 : frontier 9 ⟨1733, by decide⟩
    (prefixCache 12 6) (prefixPartial 12 6) = false := by
  decide +kernel

theorem node_context_12_6_1733 : EJMOriginalGlobalDAGData.nodes 9 ⟨1733, by decide⟩ =
    .split (coordinate 12) (![⟨1382, by decide⟩,⟨1598, by decide⟩,⟨1707, by decide⟩,⟨1732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6_1733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6 ⟨1733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6
    ⟨1733, by decide⟩ (by decide) (![⟨1382, by decide⟩,⟨1598, by decide⟩,⟨1707, by decide⟩,⟨1732, by decide⟩]) unmarked_context_12_6_1733 node_context_12_6_1733
  intro a
  fin_cases a
  · exact context_13_24_1382
  · exact context_13_25_1598
  · exact context_13_26_1707
  · exact context_13_27_1732

theorem selected_cut_00013 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 7) = some ⟨12, 1, 0, 893, 7, 1, 65536⟩ := by
  decide +kernel

theorem context_12_7_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 7 ⟨893, by decide⟩ :=
  accepted_of_selected 12 7 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 7, 1, 65536⟩
    (by decide) selected_cut_00013

theorem unmarked_context_11_1_1734 : frontier 10 ⟨1734, by decide⟩
    (prefixCache 11 1) (prefixPartial 11 1) = false := by
  decide +kernel

theorem node_context_11_1_1734 : EJMOriginalGlobalDAGData.nodes 10 ⟨1734, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨1189, by decide⟩,⟨1733, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1_1734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1 ⟨1734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1
    ⟨1734, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨1189, by decide⟩,⟨1733, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1_1734 node_context_11_1_1734
  intro a
  fin_cases a
  · exact context_12_4_895
  · exact context_12_5_1189
  · exact context_12_6_1733
  · exact context_12_7_893

theorem selected_cut_00014 : selected 10 ⟨1735, by decide⟩
    (prefixPartial 11 2) = some ⟨11, 1, 0, 1735, 2, 1, 262144⟩ := by
  decide +kernel

theorem context_11_2_1735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 2 ⟨1735, by decide⟩ :=
  accepted_of_selected 11 2 ⟨1735, by decide⟩ ⟨11, 1, 0, 1735, 2, 1, 262144⟩
    (by decide) selected_cut_00014

theorem selected_cut_00015 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 3) = some ⟨11, 1, 0, 1736, 3, 1, 262144⟩ := by
  decide +kernel

theorem context_11_3_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 3 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 3 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 3, 1, 262144⟩
    (by decide) selected_cut_00015

theorem unmarked_context_10_0_1737 : frontier 11 ⟨1737, by decide⟩
    (prefixCache 10 0) (prefixPartial 10 0) = false := by
  decide +kernel

theorem node_context_10_0_1737 : EJMOriginalGlobalDAGData.nodes 11 ⟨1737, by decide⟩ =
    .split (coordinate 10) (![⟨894, by decide⟩,⟨1734, by decide⟩,⟨1735, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_0_1737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 0 ⟨1737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 0
    ⟨1737, by decide⟩ (by decide) (![⟨894, by decide⟩,⟨1734, by decide⟩,⟨1735, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_0_1737 node_context_10_0_1737
  intro a
  fin_cases a
  · exact context_11_0_894
  · exact context_11_1_1734
  · exact context_11_2_1735
  · exact context_11_3_1736

theorem selected_cut_00016 : selected 10 ⟨2006, by decide⟩
    (prefixPartial 11 4) = some ⟨11, 2, 0, 2006, 4, 3185, 262144⟩ := by
  decide +kernel

theorem context_11_4_2006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4 ⟨2006, by decide⟩ :=
  accepted_of_selected 11 4 ⟨2006, by decide⟩ ⟨11, 2, 0, 2006, 4, 3185, 262144⟩
    (by decide) selected_cut_00016

theorem selected_cut_00017 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 20) = some ⟨12, 1, 0, 1738, 20, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 20 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 20, 1, 65536⟩
    (by decide) selected_cut_00017

theorem selected_cut_00018 : selected 9 ⟨2261, by decide⟩
    (prefixPartial 12 21) = some ⟨12, 2, 0, 2261, 21, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_21_2261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21 ⟨2261, by decide⟩ :=
  accepted_of_selected 12 21 ⟨2261, by decide⟩ ⟨12, 2, 0, 2261, 21, 2953, 65536⟩
    (by decide) selected_cut_00018

theorem selected_cut_00019 : selected 8 ⟨2338, by decide⟩
    (prefixPartial 13 88) = some ⟨13, 2, 0, 2338, 88, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_88_2338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88 ⟨2338, by decide⟩ :=
  accepted_of_selected 13 88 ⟨2338, by decide⟩ ⟨13, 2, 0, 2338, 88, 1589, 16384⟩
    (by decide) selected_cut_00019

theorem selected_cut_00020 : selected 8 ⟨2450, by decide⟩
    (prefixPartial 13 89) = some ⟨13, 2, 0, 2450, 89, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_89_2450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 89 ⟨2450, by decide⟩ :=
  accepted_of_selected 13 89 ⟨2450, by decide⟩ ⟨13, 2, 0, 2450, 89, 2349, 16384⟩
    (by decide) selected_cut_00020

theorem selected_cut_00021 : selected 8 ⟨2585, by decide⟩
    (prefixPartial 13 90) = some ⟨13, 2, 0, 2585, 90, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_90_2585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 90 ⟨2585, by decide⟩ :=
  accepted_of_selected 13 90 ⟨2585, by decide⟩ ⟨13, 2, 0, 2585, 90, 1917, 16384⟩
    (by decide) selected_cut_00021

theorem selected_cut_00022 : selected 8 ⟨2701, by decide⟩
    (prefixPartial 13 91) = some ⟨13, 2, 0, 2701, 91, 977, 16384⟩ := by
  decide +kernel

theorem context_13_91_2701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91 ⟨2701, by decide⟩ :=
  accepted_of_selected 13 91 ⟨2701, by decide⟩ ⟨13, 2, 0, 2701, 91, 977, 16384⟩
    (by decide) selected_cut_00022

theorem unmarked_context_12_22_2702 : frontier 9 ⟨2702, by decide⟩
    (prefixCache 12 22) (prefixPartial 12 22) = false := by
  decide +kernel

theorem node_context_12_22_2702 : EJMOriginalGlobalDAGData.nodes 9 ⟨2702, by decide⟩ =
    .split (coordinate 12) (![⟨2338, by decide⟩,⟨2450, by decide⟩,⟨2585, by decide⟩,⟨2701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22_2702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22 ⟨2702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22
    ⟨2702, by decide⟩ (by decide) (![⟨2338, by decide⟩,⟨2450, by decide⟩,⟨2585, by decide⟩,⟨2701, by decide⟩]) unmarked_context_12_22_2702 node_context_12_22_2702
  intro a
  fin_cases a
  · exact context_13_88_2338
  · exact context_13_89_2450
  · exact context_13_90_2585
  · exact context_13_91_2701

theorem selected_cut_00023 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 23) = some ⟨12, 1, 0, 893, 23, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23 ⟨893, by decide⟩ :=
  accepted_of_selected 12 23 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 23, 1, 65536⟩
    (by decide) selected_cut_00023

theorem unmarked_context_11_5_2703 : frontier 10 ⟨2703, by decide⟩
    (prefixCache 11 5) (prefixPartial 11 5) = false := by
  decide +kernel

theorem node_context_11_5_2703 : EJMOriginalGlobalDAGData.nodes 10 ⟨2703, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨2261, by decide⟩,⟨2702, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5_2703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5 ⟨2703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5
    ⟨2703, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨2261, by decide⟩,⟨2702, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5_2703 node_context_11_5_2703
  intro a
  fin_cases a
  · exact context_12_20_1738
  · exact context_12_21_2261
  · exact context_12_22_2702
  · exact context_12_23_893

theorem selected_cut_00024 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 24) = some ⟨12, 1, 0, 1738, 24, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 24 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 24, 1, 65536⟩
    (by decide) selected_cut_00024

theorem selected_cut_00025 : selected 8 ⟨2806, by decide⟩
    (prefixPartial 13 100) = some ⟨13, 2, 0, 2806, 100, 761, 16384⟩ := by
  decide +kernel

theorem context_13_100_2806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100 ⟨2806, by decide⟩ :=
  accepted_of_selected 13 100 ⟨2806, by decide⟩ ⟨13, 2, 0, 2806, 100, 761, 16384⟩
    (by decide) selected_cut_00025

theorem selected_cut_00026 : selected 8 ⟨2959, by decide⟩
    (prefixPartial 13 101) = some ⟨13, 2, 0, 2959, 101, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_101_2959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101 ⟨2959, by decide⟩ :=
  accepted_of_selected 13 101 ⟨2959, by decide⟩ ⟨13, 2, 0, 2959, 101, 1957, 16384⟩
    (by decide) selected_cut_00026

theorem selected_cut_00027 : selected 8 ⟨3079, by decide⟩
    (prefixPartial 13 102) = some ⟨13, 2, 0, 3079, 102, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_102_3079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102 ⟨3079, by decide⟩ :=
  accepted_of_selected 13 102 ⟨3079, by decide⟩ ⟨13, 2, 0, 3079, 102, 1401, 16384⟩
    (by decide) selected_cut_00027

theorem selected_cut_00028 : selected 8 ⟨3159, by decide⟩
    (prefixPartial 13 103) = some ⟨13, 2, 0, 3159, 103, 673, 16384⟩ := by
  decide +kernel

theorem context_13_103_3159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103 ⟨3159, by decide⟩ :=
  accepted_of_selected 13 103 ⟨3159, by decide⟩ ⟨13, 2, 0, 3159, 103, 673, 16384⟩
    (by decide) selected_cut_00028

theorem unmarked_context_12_25_3160 : frontier 9 ⟨3160, by decide⟩
    (prefixCache 12 25) (prefixPartial 12 25) = false := by
  decide +kernel

theorem node_context_12_25_3160 : EJMOriginalGlobalDAGData.nodes 9 ⟨3160, by decide⟩ =
    .split (coordinate 12) (![⟨2806, by decide⟩,⟨2959, by decide⟩,⟨3079, by decide⟩,⟨3159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25_3160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25 ⟨3160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25
    ⟨3160, by decide⟩ (by decide) (![⟨2806, by decide⟩,⟨2959, by decide⟩,⟨3079, by decide⟩,⟨3159, by decide⟩]) unmarked_context_12_25_3160 node_context_12_25_3160
  intro a
  fin_cases a
  · exact context_13_100_2806
  · exact context_13_101_2959
  · exact context_13_102_3079
  · exact context_13_103_3159

theorem selected_cut_00029 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 26) = some ⟨12, 1, 0, 3161, 26, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 26 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 26, 1, 65536⟩
    (by decide) selected_cut_00029

theorem selected_cut_00030 : selected 9 ⟨3436, by decide⟩
    (prefixPartial 12 27) = some ⟨12, 2, 0, 3436, 27, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_27_3436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27 ⟨3436, by decide⟩ :=
  accepted_of_selected 12 27 ⟨3436, by decide⟩ ⟨12, 2, 0, 3436, 27, 2957, 65536⟩
    (by decide) selected_cut_00030

theorem unmarked_context_11_6_3437 : frontier 10 ⟨3437, by decide⟩
    (prefixCache 11 6) (prefixPartial 11 6) = false := by
  decide +kernel

theorem node_context_11_6_3437 : EJMOriginalGlobalDAGData.nodes 10 ⟨3437, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨3160, by decide⟩,⟨3161, by decide⟩,⟨3436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6_3437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6 ⟨3437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6
    ⟨3437, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨3160, by decide⟩,⟨3161, by decide⟩,⟨3436, by decide⟩]) unmarked_context_11_6_3437 node_context_11_6_3437
  intro a
  fin_cases a
  · exact context_12_24_1738
  · exact context_12_25_3160
  · exact context_12_26_3161
  · exact context_12_27_3436

theorem selected_cut_00031 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 7) = some ⟨11, 1, 0, 1736, 7, 1, 262144⟩ := by
  decide +kernel

theorem context_11_7_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 7 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 7, 1, 262144⟩
    (by decide) selected_cut_00031

theorem unmarked_context_10_1_3438 : frontier 11 ⟨3438, by decide⟩
    (prefixCache 10 1) (prefixPartial 10 1) = false := by
  decide +kernel

theorem node_context_10_1_3438 : EJMOriginalGlobalDAGData.nodes 11 ⟨3438, by decide⟩ =
    .split (coordinate 10) (![⟨2006, by decide⟩,⟨2703, by decide⟩,⟨3437, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1_3438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1 ⟨3438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1
    ⟨3438, by decide⟩ (by decide) (![⟨2006, by decide⟩,⟨2703, by decide⟩,⟨3437, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1_3438 node_context_10_1_3438
  intro a
  fin_cases a
  · exact context_11_4_2006
  · exact context_11_5_2703
  · exact context_11_6_3437
  · exact context_11_7_1736

theorem selected_cut_00032 : selected 11 ⟨3439, by decide⟩
    (prefixPartial 10 2) = some ⟨10, 1, 0, 3439, 2, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_2_3439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 2 ⟨3439, by decide⟩ :=
  accepted_of_selected 10 2 ⟨3439, by decide⟩ ⟨10, 1, 0, 3439, 2, 1, 1048576⟩
    (by decide) selected_cut_00032

theorem selected_cut_00033 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 3) = some ⟨10, 1, 0, 3440, 3, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_3_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 3 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 3 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 3, 1, 1048576⟩
    (by decide) selected_cut_00033

theorem unmarked_context_9_0_3441 : frontier 12 ⟨3441, by decide⟩
    (prefixCache 9 0) (prefixPartial 9 0) = false := by
  decide +kernel

theorem node_context_9_0_3441 : EJMOriginalGlobalDAGData.nodes 12 ⟨3441, by decide⟩ =
    .split (coordinate 9) (![⟨1737, by decide⟩,⟨3438, by decide⟩,⟨3439, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_0_3441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 0 ⟨3441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 0
    ⟨3441, by decide⟩ (by decide) (![⟨1737, by decide⟩,⟨3438, by decide⟩,⟨3439, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_0_3441 node_context_9_0_3441
  intro a
  fin_cases a
  · exact context_10_0_1737
  · exact context_10_1_3438
  · exact context_10_2_3439
  · exact context_10_3_3440

theorem selected_cut_00034 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4) = some ⟨10, 1, 0, 3442, 4, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4, 1, 1048576⟩
    (by decide) selected_cut_00034

theorem selected_cut_00035 : selected 10 ⟨3443, by decide⟩
    (prefixPartial 11 20) = some ⟨11, 1, 0, 3443, 20, 1, 262144⟩ := by
  decide +kernel

theorem context_11_20_3443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 20 ⟨3443, by decide⟩ :=
  accepted_of_selected 11 20 ⟨3443, by decide⟩ ⟨11, 1, 0, 3443, 20, 1, 262144⟩
    (by decide) selected_cut_00035

theorem selected_cut_00036 : selected 10 ⟨3992, by decide⟩
    (prefixPartial 11 21) = some ⟨11, 2, 0, 3992, 21, 3673, 262144⟩ := by
  decide +kernel

theorem context_11_21_3992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21 ⟨3992, by decide⟩ :=
  accepted_of_selected 11 21 ⟨3992, by decide⟩ ⟨11, 2, 0, 3992, 21, 3673, 262144⟩
    (by decide) selected_cut_00036

theorem selected_cut_00037 : selected 10 ⟨4451, by decide⟩
    (prefixPartial 11 22) = some ⟨11, 2, 0, 4451, 22, 2669, 262144⟩ := by
  decide +kernel

theorem context_11_22_4451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22 ⟨4451, by decide⟩ :=
  accepted_of_selected 11 22 ⟨4451, by decide⟩ ⟨11, 2, 0, 4451, 22, 2669, 262144⟩
    (by decide) selected_cut_00037

theorem selected_cut_00038 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 23) = some ⟨11, 1, 0, 1736, 23, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 23 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 23, 1, 262144⟩
    (by decide) selected_cut_00038

theorem unmarked_context_10_5_4452 : frontier 11 ⟨4452, by decide⟩
    (prefixCache 10 5) (prefixPartial 10 5) = false := by
  decide +kernel

theorem node_context_10_5_4452 : EJMOriginalGlobalDAGData.nodes 11 ⟨4452, by decide⟩ =
    .split (coordinate 10) (![⟨3443, by decide⟩,⟨3992, by decide⟩,⟨4451, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5_4452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5 ⟨4452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5
    ⟨4452, by decide⟩ (by decide) (![⟨3443, by decide⟩,⟨3992, by decide⟩,⟨4451, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_5_4452 node_context_10_5_4452
  intro a
  fin_cases a
  · exact context_11_20_3443
  · exact context_11_21_3992
  · exact context_11_22_4451
  · exact context_11_23_1736

theorem selected_cut_00039 : selected 11 ⟨4598, by decide⟩
    (prefixPartial 10 6) = some ⟨10, 2, 0, 4598, 6, 625, 1048576⟩ := by
  decide +kernel

theorem context_10_6_4598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6 ⟨4598, by decide⟩ :=
  accepted_of_selected 10 6 ⟨4598, by decide⟩ ⟨10, 2, 0, 4598, 6, 625, 1048576⟩
    (by decide) selected_cut_00039

theorem selected_cut_00040 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 7) = some ⟨10, 1, 0, 3440, 7, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_7_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 7 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 7, 1, 1048576⟩
    (by decide) selected_cut_00040

theorem unmarked_context_9_1_4599 : frontier 12 ⟨4599, by decide⟩
    (prefixCache 9 1) (prefixPartial 9 1) = false := by
  decide +kernel

theorem node_context_9_1_4599 : EJMOriginalGlobalDAGData.nodes 12 ⟨4599, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨4452, by decide⟩,⟨4598, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1_4599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1 ⟨4599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1
    ⟨4599, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨4452, by decide⟩,⟨4598, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1_4599 node_context_9_1_4599
  intro a
  fin_cases a
  · exact context_10_4_3442
  · exact context_10_5_4452
  · exact context_10_6_4598
  · exact context_10_7_3440

theorem selected_cut_00041 : selected 12 ⟨4600, by decide⟩
    (prefixPartial 9 2) = some ⟨9, 1, 0, 4600, 2, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_2_4600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 2 ⟨4600, by decide⟩ :=
  accepted_of_selected 9 2 ⟨4600, by decide⟩ ⟨9, 1, 0, 4600, 2, 1, 4194304⟩
    (by decide) selected_cut_00041

theorem selected_cut_00042 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 3) = some ⟨9, 1, 0, 4601, 3, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_3_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 3 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 3 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 3, 1, 4194304⟩
    (by decide) selected_cut_00042

theorem unmarked_context_8_0_4602 : frontier 13 ⟨4602, by decide⟩
    (prefixCache 8 0) (prefixPartial 8 0) = false := by
  decide +kernel

theorem node_context_8_0_4602 : EJMOriginalGlobalDAGData.nodes 13 ⟨4602, by decide⟩ =
    .split (coordinate 8) (![⟨3441, by decide⟩,⟨4599, by decide⟩,⟨4600, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_0_4602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 0 ⟨4602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 0
    ⟨4602, by decide⟩ (by decide) (![⟨3441, by decide⟩,⟨4599, by decide⟩,⟨4600, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_0_4602 node_context_8_0_4602
  intro a
  fin_cases a
  · exact context_9_0_3441
  · exact context_9_1_4599
  · exact context_9_2_4600
  · exact context_9_3_4601

theorem selected_cut_00043 : selected 7 ⟨4635, by decide⟩
    (prefixPartial 14 4096) = some ⟨14, 2, 0, 4635, 4096, 1425, 4096⟩ := by
  decide +kernel

theorem context_14_4096_4635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4096 ⟨4635, by decide⟩ :=
  accepted_of_selected 14 4096 ⟨4635, by decide⟩ ⟨14, 2, 0, 4635, 4096, 1425, 4096⟩
    (by decide) selected_cut_00043

theorem selected_cut_00044 : selected 7 ⟨4682, by decide⟩
    (prefixPartial 14 4097) = some ⟨14, 2, 0, 4682, 4097, 1641, 4096⟩ := by
  decide +kernel

theorem context_14_4097_4682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4097 ⟨4682, by decide⟩ :=
  accepted_of_selected 14 4097 ⟨4682, by decide⟩ ⟨14, 2, 0, 4682, 4097, 1641, 4096⟩
    (by decide) selected_cut_00044

theorem selected_cut_00045 : selected 7 ⟨4779, by decide⟩
    (prefixPartial 14 4098) = some ⟨14, 2, 0, 4779, 4098, 2777, 4096⟩ := by
  decide +kernel

theorem context_14_4098_4779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4098 ⟨4779, by decide⟩ :=
  accepted_of_selected 14 4098 ⟨4779, by decide⟩ ⟨14, 2, 0, 4779, 4098, 2777, 4096⟩
    (by decide) selected_cut_00045

theorem selected_cut_00046 : selected 7 ⟨291, by decide⟩
    (prefixPartial 14 4099) = some ⟨14, 1, 0, 291, 4099, 1, 4096⟩ := by
  decide +kernel

theorem context_14_4099_291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4099 ⟨291, by decide⟩ :=
  accepted_of_selected 14 4099 ⟨291, by decide⟩ ⟨14, 1, 0, 291, 4099, 1, 4096⟩
    (by decide) selected_cut_00046

theorem unmarked_context_13_1024_4780 : frontier 8 ⟨4780, by decide⟩
    (prefixCache 13 1024) (prefixPartial 13 1024) = false := by
  decide +kernel

theorem node_context_13_1024_4780 : EJMOriginalGlobalDAGData.nodes 8 ⟨4780, by decide⟩ =
    .split (coordinate 13) (![⟨4635, by decide⟩,⟨4682, by decide⟩,⟨4779, by decide⟩,⟨291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1024_4780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1024 ⟨4780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1024
    ⟨4780, by decide⟩ (by decide) (![⟨4635, by decide⟩,⟨4682, by decide⟩,⟨4779, by decide⟩,⟨291, by decide⟩]) unmarked_context_13_1024_4780 node_context_13_1024_4780
  intro a
  fin_cases a
  · exact context_14_4096_4635
  · exact context_14_4097_4682
  · exact context_14_4098_4779
  · exact context_14_4099_291

theorem selected_cut_00047 : selected 8 ⟨4891, by decide⟩
    (prefixPartial 13 1025) = some ⟨13, 2, 0, 4891, 1025, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_1025_4891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1025 ⟨4891, by decide⟩ :=
  accepted_of_selected 13 1025 ⟨4891, by decide⟩ ⟨13, 2, 0, 4891, 1025, 2293, 16384⟩
    (by decide) selected_cut_00047

theorem selected_cut_00048 : selected 8 ⟨4966, by decide⟩
    (prefixPartial 13 1026) = some ⟨13, 2, 0, 4966, 1026, 825, 16384⟩ := by
  decide +kernel

theorem context_13_1026_4966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1026 ⟨4966, by decide⟩ :=
  accepted_of_selected 13 1026 ⟨4966, by decide⟩ ⟨13, 2, 0, 4966, 1026, 825, 16384⟩
    (by decide) selected_cut_00048

theorem selected_cut_00049 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 1027) = some ⟨13, 1, 0, 414, 1027, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1027_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1027 ⟨414, by decide⟩ :=
  accepted_of_selected 13 1027 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 1027, 1, 16384⟩
    (by decide) selected_cut_00049

theorem unmarked_context_12_256_4967 : frontier 9 ⟨4967, by decide⟩
    (prefixCache 12 256) (prefixPartial 12 256) = false := by
  decide +kernel

theorem node_context_12_256_4967 : EJMOriginalGlobalDAGData.nodes 9 ⟨4967, by decide⟩ =
    .split (coordinate 12) (![⟨4780, by decide⟩,⟨4891, by decide⟩,⟨4966, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_256_4967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 256 ⟨4967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 256
    ⟨4967, by decide⟩ (by decide) (![⟨4780, by decide⟩,⟨4891, by decide⟩,⟨4966, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_256_4967 node_context_12_256_4967
  intro a
  fin_cases a
  · exact context_13_1024_4780
  · exact context_13_1025_4891
  · exact context_13_1026_4966
  · exact context_13_1027_414

theorem selected_cut_00050 : selected 7 ⟨5018, by decide⟩
    (prefixPartial 14 4112) = some ⟨14, 2, 0, 5018, 4112, 1585, 4096⟩ := by
  decide +kernel

theorem context_14_4112_5018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4112 ⟨5018, by decide⟩ :=
  accepted_of_selected 14 4112 ⟨5018, by decide⟩ ⟨14, 2, 0, 5018, 4112, 1585, 4096⟩
    (by decide) selected_cut_00050

theorem selected_cut_00051 : selected 7 ⟨5050, by decide⟩
    (prefixPartial 14 4113) = some ⟨14, 2, 0, 5050, 4113, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_4113_5050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4113 ⟨5050, by decide⟩ :=
  accepted_of_selected 14 4113 ⟨5050, by decide⟩ ⟨14, 2, 0, 5050, 4113, 1193, 4096⟩
    (by decide) selected_cut_00051

theorem selected_cut_00052 : selected 7 ⟨5101, by decide⟩
    (prefixPartial 14 4114) = some ⟨14, 2, 0, 5101, 4114, 2329, 4096⟩ := by
  decide +kernel

theorem context_14_4114_5101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4114 ⟨5101, by decide⟩ :=
  accepted_of_selected 14 4114 ⟨5101, by decide⟩ ⟨14, 2, 0, 5101, 4114, 2329, 4096⟩
    (by decide) selected_cut_00052

theorem selected_cut_00053 : selected 7 ⟨291, by decide⟩
    (prefixPartial 14 4115) = some ⟨14, 1, 0, 291, 4115, 1, 4096⟩ := by
  decide +kernel

theorem context_14_4115_291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4115 ⟨291, by decide⟩ :=
  accepted_of_selected 14 4115 ⟨291, by decide⟩ ⟨14, 1, 0, 291, 4115, 1, 4096⟩
    (by decide) selected_cut_00053

theorem unmarked_context_13_1028_5102 : frontier 8 ⟨5102, by decide⟩
    (prefixCache 13 1028) (prefixPartial 13 1028) = false := by
  decide +kernel

theorem node_context_13_1028_5102 : EJMOriginalGlobalDAGData.nodes 8 ⟨5102, by decide⟩ =
    .split (coordinate 13) (![⟨5018, by decide⟩,⟨5050, by decide⟩,⟨5101, by decide⟩,⟨291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1028_5102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1028 ⟨5102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1028
    ⟨5102, by decide⟩ (by decide) (![⟨5018, by decide⟩,⟨5050, by decide⟩,⟨5101, by decide⟩,⟨291, by decide⟩]) unmarked_context_13_1028_5102 node_context_13_1028_5102
  intro a
  fin_cases a
  · exact context_14_4112_5018
  · exact context_14_4113_5050
  · exact context_14_4114_5101
  · exact context_14_4115_291

theorem selected_cut_00054 : selected 8 ⟨5158, by decide⟩
    (prefixPartial 13 1029) = some ⟨13, 2, 0, 5158, 1029, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_1029_5158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1029 ⟨5158, by decide⟩ :=
  accepted_of_selected 13 1029 ⟨5158, by decide⟩ ⟨13, 2, 0, 5158, 1029, 2337, 16384⟩
    (by decide) selected_cut_00054

theorem selected_cut_00055 : selected 8 ⟨5300, by decide⟩
    (prefixPartial 13 1030) = some ⟨13, 2, 0, 5300, 1030, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_1030_5300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1030 ⟨5300, by decide⟩ :=
  accepted_of_selected 13 1030 ⟨5300, by decide⟩ ⟨13, 2, 0, 5300, 1030, 2917, 16384⟩
    (by decide) selected_cut_00055

theorem selected_cut_00056 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 1031) = some ⟨13, 1, 0, 414, 1031, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1031_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1031 ⟨414, by decide⟩ :=
  accepted_of_selected 13 1031 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 1031, 1, 16384⟩
    (by decide) selected_cut_00056

theorem unmarked_context_12_257_5301 : frontier 9 ⟨5301, by decide⟩
    (prefixCache 12 257) (prefixPartial 12 257) = false := by
  decide +kernel

theorem node_context_12_257_5301 : EJMOriginalGlobalDAGData.nodes 9 ⟨5301, by decide⟩ =
    .split (coordinate 12) (![⟨5102, by decide⟩,⟨5158, by decide⟩,⟨5300, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_257_5301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 257 ⟨5301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 257
    ⟨5301, by decide⟩ (by decide) (![⟨5102, by decide⟩,⟨5158, by decide⟩,⟨5300, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_257_5301 node_context_12_257_5301
  intro a
  fin_cases a
  · exact context_13_1028_5102
  · exact context_13_1029_5158
  · exact context_13_1030_5300
  · exact context_13_1031_414

theorem selected_cut_00057 : selected 7 ⟨5373, by decide⟩
    (prefixPartial 14 4128) = some ⟨14, 2, 0, 5373, 4128, 2497, 4096⟩ := by
  decide +kernel

theorem context_14_4128_5373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4128 ⟨5373, by decide⟩ :=
  accepted_of_selected 14 4128 ⟨5373, by decide⟩ ⟨14, 2, 0, 5373, 4128, 2497, 4096⟩
    (by decide) selected_cut_00057

theorem selected_cut_00058 : selected 7 ⟨5430, by decide⟩
    (prefixPartial 14 4129) = some ⟨14, 2, 0, 5430, 4129, 2821, 4096⟩ := by
  decide +kernel

theorem context_14_4129_5430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4129 ⟨5430, by decide⟩ :=
  accepted_of_selected 14 4129 ⟨5430, by decide⟩ ⟨14, 2, 0, 5430, 4129, 2821, 4096⟩
    (by decide) selected_cut_00058

theorem selected_cut_00059 : selected 7 ⟨5487, by decide⟩
    (prefixPartial 14 4130) = some ⟨14, 2, 0, 5487, 4130, 2625, 4096⟩ := by
  decide +kernel

theorem context_14_4130_5487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4130 ⟨5487, by decide⟩ :=
  accepted_of_selected 14 4130 ⟨5487, by decide⟩ ⟨14, 2, 0, 5487, 4130, 2625, 4096⟩
    (by decide) selected_cut_00059

theorem selected_cut_00060 : selected 7 ⟨5533, by decide⟩
    (prefixPartial 14 4131) = some ⟨14, 2, 0, 5533, 4131, 2577, 4096⟩ := by
  decide +kernel

theorem context_14_4131_5533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4131 ⟨5533, by decide⟩ :=
  accepted_of_selected 14 4131 ⟨5533, by decide⟩ ⟨14, 2, 0, 5533, 4131, 2577, 4096⟩
    (by decide) selected_cut_00060

theorem unmarked_context_13_1032_5534 : frontier 8 ⟨5534, by decide⟩
    (prefixCache 13 1032) (prefixPartial 13 1032) = false := by
  decide +kernel

theorem node_context_13_1032_5534 : EJMOriginalGlobalDAGData.nodes 8 ⟨5534, by decide⟩ =
    .split (coordinate 13) (![⟨5373, by decide⟩,⟨5430, by decide⟩,⟨5487, by decide⟩,⟨5533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1032_5534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1032 ⟨5534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1032
    ⟨5534, by decide⟩ (by decide) (![⟨5373, by decide⟩,⟨5430, by decide⟩,⟨5487, by decide⟩,⟨5533, by decide⟩]) unmarked_context_13_1032_5534 node_context_13_1032_5534
  intro a
  fin_cases a
  · exact context_14_4128_5373
  · exact context_14_4129_5430
  · exact context_14_4130_5487
  · exact context_14_4131_5533

theorem selected_cut_00061 : selected 7 ⟨5567, by decide⟩
    (prefixPartial 14 4132) = some ⟨14, 2, 0, 5567, 4132, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_4132_5567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4132 ⟨5567, by decide⟩ :=
  accepted_of_selected 14 4132 ⟨5567, by decide⟩ ⟨14, 2, 0, 5567, 4132, 1057, 4096⟩
    (by decide) selected_cut_00061

theorem selected_cut_00062 : selected 7 ⟨5594, by decide⟩
    (prefixPartial 14 4133) = some ⟨14, 2, 0, 5594, 4133, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_4133_5594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4133 ⟨5594, by decide⟩ :=
  accepted_of_selected 14 4133 ⟨5594, by decide⟩ ⟨14, 2, 0, 5594, 4133, 1273, 4096⟩
    (by decide) selected_cut_00062

theorem selected_cut_00063 : selected 7 ⟨5624, by decide⟩
    (prefixPartial 14 4134) = some ⟨14, 2, 0, 5624, 4134, 1449, 4096⟩ := by
  decide +kernel

theorem context_14_4134_5624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4134 ⟨5624, by decide⟩ :=
  accepted_of_selected 14 4134 ⟨5624, by decide⟩ ⟨14, 2, 0, 5624, 4134, 1449, 4096⟩
    (by decide) selected_cut_00063

theorem selected_cut_00064 : selected 7 ⟨5652, by decide⟩
    (prefixPartial 14 4135) = some ⟨14, 2, 0, 5652, 4135, 1353, 4096⟩ := by
  decide +kernel

theorem context_14_4135_5652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4135 ⟨5652, by decide⟩ :=
  accepted_of_selected 14 4135 ⟨5652, by decide⟩ ⟨14, 2, 0, 5652, 4135, 1353, 4096⟩
    (by decide) selected_cut_00064

theorem unmarked_context_13_1033_5653 : frontier 8 ⟨5653, by decide⟩
    (prefixCache 13 1033) (prefixPartial 13 1033) = false := by
  decide +kernel

theorem node_context_13_1033_5653 : EJMOriginalGlobalDAGData.nodes 8 ⟨5653, by decide⟩ =
    .split (coordinate 13) (![⟨5567, by decide⟩,⟨5594, by decide⟩,⟨5624, by decide⟩,⟨5652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1033_5653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1033 ⟨5653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1033
    ⟨5653, by decide⟩ (by decide) (![⟨5567, by decide⟩,⟨5594, by decide⟩,⟨5624, by decide⟩,⟨5652, by decide⟩]) unmarked_context_13_1033_5653 node_context_13_1033_5653
  intro a
  fin_cases a
  · exact context_14_4132_5567
  · exact context_14_4133_5594
  · exact context_14_4134_5624
  · exact context_14_4135_5652

theorem selected_cut_00065 : selected 8 ⟨5762, by decide⟩
    (prefixPartial 13 1034) = some ⟨13, 2, 0, 5762, 1034, 3613, 16384⟩ := by
  decide +kernel

theorem context_13_1034_5762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1034 ⟨5762, by decide⟩ :=
  accepted_of_selected 13 1034 ⟨5762, by decide⟩ ⟨13, 2, 0, 5762, 1034, 3613, 16384⟩
    (by decide) selected_cut_00065

theorem selected_cut_00066 : selected 8 ⟨5845, by decide⟩
    (prefixPartial 13 1035) = some ⟨13, 2, 0, 5845, 1035, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_1035_5845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1035 ⟨5845, by decide⟩ :=
  accepted_of_selected 13 1035 ⟨5845, by decide⟩ ⟨13, 2, 0, 5845, 1035, 1729, 16384⟩
    (by decide) selected_cut_00066

theorem unmarked_context_12_258_5846 : frontier 9 ⟨5846, by decide⟩
    (prefixCache 12 258) (prefixPartial 12 258) = false := by
  decide +kernel

theorem node_context_12_258_5846 : EJMOriginalGlobalDAGData.nodes 9 ⟨5846, by decide⟩ =
    .split (coordinate 12) (![⟨5534, by decide⟩,⟨5653, by decide⟩,⟨5762, by decide⟩,⟨5845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_258_5846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 258 ⟨5846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 258
    ⟨5846, by decide⟩ (by decide) (![⟨5534, by decide⟩,⟨5653, by decide⟩,⟨5762, by decide⟩,⟨5845, by decide⟩]) unmarked_context_12_258_5846 node_context_12_258_5846
  intro a
  fin_cases a
  · exact context_13_1032_5534
  · exact context_13_1033_5653
  · exact context_13_1034_5762
  · exact context_13_1035_5845

theorem selected_cut_00067 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 259) = some ⟨12, 1, 0, 893, 259, 1, 65536⟩ := by
  decide +kernel

theorem context_12_259_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 259 ⟨893, by decide⟩ :=
  accepted_of_selected 12 259 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 259, 1, 65536⟩
    (by decide) selected_cut_00067

theorem unmarked_context_11_64_5847 : frontier 10 ⟨5847, by decide⟩
    (prefixCache 11 64) (prefixPartial 11 64) = false := by
  decide +kernel

theorem node_context_11_64_5847 : EJMOriginalGlobalDAGData.nodes 10 ⟨5847, by decide⟩ =
    .split (coordinate 11) (![⟨4967, by decide⟩,⟨5301, by decide⟩,⟨5846, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_64_5847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 64 ⟨5847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 64
    ⟨5847, by decide⟩ (by decide) (![⟨4967, by decide⟩,⟨5301, by decide⟩,⟨5846, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_64_5847 node_context_11_64_5847
  intro a
  fin_cases a
  · exact context_12_256_4967
  · exact context_12_257_5301
  · exact context_12_258_5846
  · exact context_12_259_893

theorem selected_cut_00068 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 260) = some ⟨12, 1, 0, 895, 260, 1, 65536⟩ := by
  decide +kernel

theorem context_12_260_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 260 ⟨895, by decide⟩ :=
  accepted_of_selected 12 260 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 260, 1, 65536⟩
    (by decide) selected_cut_00068

theorem selected_cut_00069 : selected 8 ⟨5943, by decide⟩
    (prefixPartial 13 1044) = some ⟨13, 2, 0, 5943, 1044, 3573, 16384⟩ := by
  decide +kernel

theorem context_13_1044_5943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1044 ⟨5943, by decide⟩ :=
  accepted_of_selected 13 1044 ⟨5943, by decide⟩ ⟨13, 2, 0, 5943, 1044, 3573, 16384⟩
    (by decide) selected_cut_00069

theorem selected_cut_00070 : selected 8 ⟨6024, by decide⟩
    (prefixPartial 13 1045) = some ⟨13, 2, 0, 6024, 1045, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_1045_6024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1045 ⟨6024, by decide⟩ :=
  accepted_of_selected 13 1045 ⟨6024, by decide⟩ ⟨13, 2, 0, 6024, 1045, 2121, 16384⟩
    (by decide) selected_cut_00070

theorem selected_cut_00071 : selected 8 ⟨6061, by decide⟩
    (prefixPartial 13 1046) = some ⟨13, 2, 0, 6061, 1046, 737, 16384⟩ := by
  decide +kernel

theorem context_13_1046_6061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1046 ⟨6061, by decide⟩ :=
  accepted_of_selected 13 1046 ⟨6061, by decide⟩ ⟨13, 2, 0, 6061, 1046, 737, 16384⟩
    (by decide) selected_cut_00071

theorem selected_cut_00072 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 1047) = some ⟨13, 1, 0, 414, 1047, 1, 16384⟩ := by
  decide +kernel

theorem context_13_1047_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1047 ⟨414, by decide⟩ :=
  accepted_of_selected 13 1047 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 1047, 1, 16384⟩
    (by decide) selected_cut_00072

theorem unmarked_context_12_261_6062 : frontier 9 ⟨6062, by decide⟩
    (prefixCache 12 261) (prefixPartial 12 261) = false := by
  decide +kernel

theorem node_context_12_261_6062 : EJMOriginalGlobalDAGData.nodes 9 ⟨6062, by decide⟩ =
    .split (coordinate 12) (![⟨5943, by decide⟩,⟨6024, by decide⟩,⟨6061, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_261_6062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 261 ⟨6062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 261
    ⟨6062, by decide⟩ (by decide) (![⟨5943, by decide⟩,⟨6024, by decide⟩,⟨6061, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_261_6062 node_context_12_261_6062
  intro a
  fin_cases a
  · exact context_13_1044_5943
  · exact context_13_1045_6024
  · exact context_13_1046_6061
  · exact context_13_1047_414

theorem selected_cut_00073 : selected 7 ⟨6094, by decide⟩
    (prefixPartial 14 4192) = some ⟨14, 2, 0, 6094, 4192, 789, 4096⟩ := by
  decide +kernel

theorem context_14_4192_6094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4192 ⟨6094, by decide⟩ :=
  accepted_of_selected 14 4192 ⟨6094, by decide⟩ ⟨14, 2, 0, 6094, 4192, 789, 4096⟩
    (by decide) selected_cut_00073

theorem selected_cut_00074 : selected 7 ⟨6123, by decide⟩
    (prefixPartial 14 4193) = some ⟨14, 2, 0, 6123, 4193, 1561, 4096⟩ := by
  decide +kernel

theorem context_14_4193_6123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4193 ⟨6123, by decide⟩ :=
  accepted_of_selected 14 4193 ⟨6123, by decide⟩ ⟨14, 2, 0, 6123, 4193, 1561, 4096⟩
    (by decide) selected_cut_00074

theorem selected_cut_00075 : selected 7 ⟨6156, by decide⟩
    (prefixPartial 14 4194) = some ⟨14, 2, 0, 6156, 4194, 1461, 4096⟩ := by
  decide +kernel

theorem context_14_4194_6156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4194 ⟨6156, by decide⟩ :=
  accepted_of_selected 14 4194 ⟨6156, by decide⟩ ⟨14, 2, 0, 6156, 4194, 1461, 4096⟩
    (by decide) selected_cut_00075

theorem selected_cut_00076 : selected 7 ⟨6189, by decide⟩
    (prefixPartial 14 4195) = some ⟨14, 2, 0, 6189, 4195, 1533, 4096⟩ := by
  decide +kernel

theorem context_14_4195_6189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4195 ⟨6189, by decide⟩ :=
  accepted_of_selected 14 4195 ⟨6189, by decide⟩ ⟨14, 2, 0, 6189, 4195, 1533, 4096⟩
    (by decide) selected_cut_00076

theorem unmarked_context_13_1048_6190 : frontier 8 ⟨6190, by decide⟩
    (prefixCache 13 1048) (prefixPartial 13 1048) = false := by
  decide +kernel

theorem node_context_13_1048_6190 : EJMOriginalGlobalDAGData.nodes 8 ⟨6190, by decide⟩ =
    .split (coordinate 13) (![⟨6094, by decide⟩,⟨6123, by decide⟩,⟨6156, by decide⟩,⟨6189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1048_6190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1048 ⟨6190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1048
    ⟨6190, by decide⟩ (by decide) (![⟨6094, by decide⟩,⟨6123, by decide⟩,⟨6156, by decide⟩,⟨6189, by decide⟩]) unmarked_context_13_1048_6190 node_context_13_1048_6190
  intro a
  fin_cases a
  · exact context_14_4192_6094
  · exact context_14_4193_6123
  · exact context_14_4194_6156
  · exact context_14_4195_6189

theorem selected_cut_00077 : selected 7 ⟨6212, by decide⟩
    (prefixPartial 14 4196) = some ⟨14, 2, 0, 6212, 4196, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_4196_6212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4196 ⟨6212, by decide⟩ :=
  accepted_of_selected 14 4196 ⟨6212, by decide⟩ ⟨14, 2, 0, 6212, 4196, 1133, 4096⟩
    (by decide) selected_cut_00077

theorem selected_cut_00078 : selected 7 ⟨6238, by decide⟩
    (prefixPartial 14 4197) = some ⟨14, 2, 0, 6238, 4197, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_4197_6238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4197 ⟨6238, by decide⟩ :=
  accepted_of_selected 14 4197 ⟨6238, by decide⟩ ⟨14, 2, 0, 6238, 4197, 1189, 4096⟩
    (by decide) selected_cut_00078

theorem selected_cut_00079 : selected 7 ⟨6259, by decide⟩
    (prefixPartial 14 4198) = some ⟨14, 2, 0, 6259, 4198, 1325, 4096⟩ := by
  decide +kernel

theorem context_14_4198_6259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4198 ⟨6259, by decide⟩ :=
  accepted_of_selected 14 4198 ⟨6259, by decide⟩ ⟨14, 2, 0, 6259, 4198, 1325, 4096⟩
    (by decide) selected_cut_00079

theorem selected_cut_00080 : selected 7 ⟨6285, by decide⟩
    (prefixPartial 14 4199) = some ⟨14, 2, 0, 6285, 4199, 1309, 4096⟩ := by
  decide +kernel

theorem context_14_4199_6285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4199 ⟨6285, by decide⟩ :=
  accepted_of_selected 14 4199 ⟨6285, by decide⟩ ⟨14, 2, 0, 6285, 4199, 1309, 4096⟩
    (by decide) selected_cut_00080

theorem unmarked_context_13_1049_6286 : frontier 8 ⟨6286, by decide⟩
    (prefixCache 13 1049) (prefixPartial 13 1049) = false := by
  decide +kernel

theorem node_context_13_1049_6286 : EJMOriginalGlobalDAGData.nodes 8 ⟨6286, by decide⟩ =
    .split (coordinate 13) (![⟨6212, by decide⟩,⟨6238, by decide⟩,⟨6259, by decide⟩,⟨6285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1049_6286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1049 ⟨6286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1049
    ⟨6286, by decide⟩ (by decide) (![⟨6212, by decide⟩,⟨6238, by decide⟩,⟨6259, by decide⟩,⟨6285, by decide⟩]) unmarked_context_13_1049_6286 node_context_13_1049_6286
  intro a
  fin_cases a
  · exact context_14_4196_6212
  · exact context_14_4197_6238
  · exact context_14_4198_6259
  · exact context_14_4199_6285

theorem selected_cut_00081 : selected 8 ⟨6373, by decide⟩
    (prefixPartial 13 1050) = some ⟨13, 2, 0, 6373, 1050, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_1050_6373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1050 ⟨6373, by decide⟩ :=
  accepted_of_selected 13 1050 ⟨6373, by decide⟩ ⟨13, 2, 0, 6373, 1050, 3061, 16384⟩
    (by decide) selected_cut_00081

theorem selected_cut_00082 : selected 8 ⟨6424, by decide⟩
    (prefixPartial 13 1051) = some ⟨13, 2, 0, 6424, 1051, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_1051_6424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1051 ⟨6424, by decide⟩ :=
  accepted_of_selected 13 1051 ⟨6424, by decide⟩ ⟨13, 2, 0, 6424, 1051, 1529, 16384⟩
    (by decide) selected_cut_00082

theorem unmarked_context_12_262_6425 : frontier 9 ⟨6425, by decide⟩
    (prefixCache 12 262) (prefixPartial 12 262) = false := by
  decide +kernel

theorem node_context_12_262_6425 : EJMOriginalGlobalDAGData.nodes 9 ⟨6425, by decide⟩ =
    .split (coordinate 12) (![⟨6190, by decide⟩,⟨6286, by decide⟩,⟨6373, by decide⟩,⟨6424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_262_6425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 262 ⟨6425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 262
    ⟨6425, by decide⟩ (by decide) (![⟨6190, by decide⟩,⟨6286, by decide⟩,⟨6373, by decide⟩,⟨6424, by decide⟩]) unmarked_context_12_262_6425 node_context_12_262_6425
  intro a
  fin_cases a
  · exact context_13_1048_6190
  · exact context_13_1049_6286
  · exact context_13_1050_6373
  · exact context_13_1051_6424

theorem selected_cut_00083 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 263) = some ⟨12, 1, 0, 893, 263, 1, 65536⟩ := by
  decide +kernel

theorem context_12_263_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 263 ⟨893, by decide⟩ :=
  accepted_of_selected 12 263 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 263, 1, 65536⟩
    (by decide) selected_cut_00083

theorem unmarked_context_11_65_6426 : frontier 10 ⟨6426, by decide⟩
    (prefixCache 11 65) (prefixPartial 11 65) = false := by
  decide +kernel

theorem node_context_11_65_6426 : EJMOriginalGlobalDAGData.nodes 10 ⟨6426, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨6062, by decide⟩,⟨6425, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_65_6426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 65 ⟨6426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 65
    ⟨6426, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨6062, by decide⟩,⟨6425, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_65_6426 node_context_11_65_6426
  intro a
  fin_cases a
  · exact context_12_260_895
  · exact context_12_261_6062
  · exact context_12_262_6425
  · exact context_12_263_893

theorem selected_cut_00084 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 264) = some ⟨12, 1, 0, 895, 264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_264_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 264 ⟨895, by decide⟩ :=
  accepted_of_selected 12 264 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 264, 1, 65536⟩
    (by decide) selected_cut_00084

theorem selected_cut_00085 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 265) = some ⟨12, 1, 0, 895, 265, 1, 65536⟩ := by
  decide +kernel

theorem context_12_265_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 265 ⟨895, by decide⟩ :=
  accepted_of_selected 12 265 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 265, 1, 65536⟩
    (by decide) selected_cut_00085

theorem selected_cut_00086 : selected 7 ⟨6437, by decide⟩
    (prefixPartial 14 4256) = some ⟨14, 2, 0, 6437, 4256, 257, 4096⟩ := by
  decide +kernel

theorem context_14_4256_6437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4256 ⟨6437, by decide⟩ :=
  accepted_of_selected 14 4256 ⟨6437, by decide⟩ ⟨14, 2, 0, 6437, 4256, 257, 4096⟩
    (by decide) selected_cut_00086

theorem selected_cut_00087 : selected 7 ⟨6471, by decide⟩
    (prefixPartial 14 4257) = some ⟨14, 2, 0, 6471, 4257, 1533, 4096⟩ := by
  decide +kernel

theorem context_14_4257_6471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4257 ⟨6471, by decide⟩ :=
  accepted_of_selected 14 4257 ⟨6471, by decide⟩ ⟨14, 2, 0, 6471, 4257, 1533, 4096⟩
    (by decide) selected_cut_00087

theorem selected_cut_00088 : selected 7 ⟨6499, by decide⟩
    (prefixPartial 14 4258) = some ⟨14, 2, 0, 6499, 4258, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_4258_6499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4258 ⟨6499, by decide⟩ :=
  accepted_of_selected 14 4258 ⟨6499, by decide⟩ ⟨14, 2, 0, 6499, 4258, 1237, 4096⟩
    (by decide) selected_cut_00088

theorem selected_cut_00089 : selected 7 ⟨6531, by decide⟩
    (prefixPartial 14 4259) = some ⟨14, 2, 0, 6531, 4259, 1309, 4096⟩ := by
  decide +kernel

theorem context_14_4259_6531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4259 ⟨6531, by decide⟩ :=
  accepted_of_selected 14 4259 ⟨6531, by decide⟩ ⟨14, 2, 0, 6531, 4259, 1309, 4096⟩
    (by decide) selected_cut_00089

theorem unmarked_context_13_1064_6532 : frontier 8 ⟨6532, by decide⟩
    (prefixCache 13 1064) (prefixPartial 13 1064) = false := by
  decide +kernel

theorem node_context_13_1064_6532 : EJMOriginalGlobalDAGData.nodes 8 ⟨6532, by decide⟩ =
    .split (coordinate 13) (![⟨6437, by decide⟩,⟨6471, by decide⟩,⟨6499, by decide⟩,⟨6531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1064_6532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1064 ⟨6532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1064
    ⟨6532, by decide⟩ (by decide) (![⟨6437, by decide⟩,⟨6471, by decide⟩,⟨6499, by decide⟩,⟨6531, by decide⟩]) unmarked_context_13_1064_6532 node_context_13_1064_6532
  intro a
  fin_cases a
  · exact context_14_4256_6437
  · exact context_14_4257_6471
  · exact context_14_4258_6499
  · exact context_14_4259_6531

theorem selected_cut_00090 : selected 8 ⟨6613, by decide⟩
    (prefixPartial 13 1065) = some ⟨13, 2, 0, 6613, 1065, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_1065_6613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1065 ⟨6613, by decide⟩ :=
  accepted_of_selected 13 1065 ⟨6613, by decide⟩ ⟨13, 2, 0, 6613, 1065, 2469, 16384⟩
    (by decide) selected_cut_00090

theorem selected_cut_00091 : selected 8 ⟨6650, by decide⟩
    (prefixPartial 13 1066) = some ⟨13, 2, 0, 6650, 1066, 749, 16384⟩ := by
  decide +kernel

theorem context_13_1066_6650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1066 ⟨6650, by decide⟩ :=
  accepted_of_selected 13 1066 ⟨6650, by decide⟩ ⟨13, 2, 0, 6650, 1066, 749, 16384⟩
    (by decide) selected_cut_00091

theorem selected_cut_00092 : selected 8 ⟨6656, by decide⟩
    (prefixPartial 13 1067) = some ⟨13, 2, 0, 6656, 1067, 149, 16384⟩ := by
  decide +kernel

theorem context_13_1067_6656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1067 ⟨6656, by decide⟩ :=
  accepted_of_selected 13 1067 ⟨6656, by decide⟩ ⟨13, 2, 0, 6656, 1067, 149, 16384⟩
    (by decide) selected_cut_00092

theorem unmarked_context_12_266_6657 : frontier 9 ⟨6657, by decide⟩
    (prefixCache 12 266) (prefixPartial 12 266) = false := by
  decide +kernel

theorem node_context_12_266_6657 : EJMOriginalGlobalDAGData.nodes 9 ⟨6657, by decide⟩ =
    .split (coordinate 12) (![⟨6532, by decide⟩,⟨6613, by decide⟩,⟨6650, by decide⟩,⟨6656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_266_6657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 266 ⟨6657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 266
    ⟨6657, by decide⟩ (by decide) (![⟨6532, by decide⟩,⟨6613, by decide⟩,⟨6650, by decide⟩,⟨6656, by decide⟩]) unmarked_context_12_266_6657 node_context_12_266_6657
  intro a
  fin_cases a
  · exact context_13_1064_6532
  · exact context_13_1065_6613
  · exact context_13_1066_6650
  · exact context_13_1067_6656

theorem selected_cut_00093 : selected 7 ⟨6667, by decide⟩
    (prefixPartial 14 4272) = some ⟨14, 2, 0, 6667, 4272, 177, 4096⟩ := by
  decide +kernel

theorem context_14_4272_6667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4272 ⟨6667, by decide⟩ :=
  accepted_of_selected 14 4272 ⟨6667, by decide⟩ ⟨14, 2, 0, 6667, 4272, 177, 4096⟩
    (by decide) selected_cut_00093

theorem selected_cut_00094 : selected 7 ⟨6708, by decide⟩
    (prefixPartial 14 4273) = some ⟨14, 2, 0, 6708, 4273, 1817, 4096⟩ := by
  decide +kernel

theorem context_14_4273_6708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4273 ⟨6708, by decide⟩ :=
  accepted_of_selected 14 4273 ⟨6708, by decide⟩ ⟨14, 2, 0, 6708, 4273, 1817, 4096⟩
    (by decide) selected_cut_00094

theorem selected_cut_00095 : selected 7 ⟨6749, by decide⟩
    (prefixPartial 14 4274) = some ⟨14, 2, 0, 6749, 4274, 1553, 4096⟩ := by
  decide +kernel

theorem context_14_4274_6749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4274 ⟨6749, by decide⟩ :=
  accepted_of_selected 14 4274 ⟨6749, by decide⟩ ⟨14, 2, 0, 6749, 4274, 1553, 4096⟩
    (by decide) selected_cut_00095

theorem selected_cut_00096 : selected 7 ⟨6785, by decide⟩
    (prefixPartial 14 4275) = some ⟨14, 2, 0, 6785, 4275, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_4275_6785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 4275 ⟨6785, by decide⟩ :=
  accepted_of_selected 14 4275 ⟨6785, by decide⟩ ⟨14, 2, 0, 6785, 4275, 1301, 4096⟩
    (by decide) selected_cut_00096

theorem unmarked_context_13_1068_6786 : frontier 8 ⟨6786, by decide⟩
    (prefixCache 13 1068) (prefixPartial 13 1068) = false := by
  decide +kernel

theorem node_context_13_1068_6786 : EJMOriginalGlobalDAGData.nodes 8 ⟨6786, by decide⟩ =
    .split (coordinate 13) (![⟨6667, by decide⟩,⟨6708, by decide⟩,⟨6749, by decide⟩,⟨6785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_1068_6786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1068 ⟨6786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 1068
    ⟨6786, by decide⟩ (by decide) (![⟨6667, by decide⟩,⟨6708, by decide⟩,⟨6749, by decide⟩,⟨6785, by decide⟩]) unmarked_context_13_1068_6786 node_context_13_1068_6786
  intro a
  fin_cases a
  · exact context_14_4272_6667
  · exact context_14_4273_6708
  · exact context_14_4274_6749
  · exact context_14_4275_6785

theorem selected_cut_00097 : selected 8 ⟨6889, by decide⟩
    (prefixPartial 13 1069) = some ⟨13, 2, 0, 6889, 1069, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_1069_6889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1069 ⟨6889, by decide⟩ :=
  accepted_of_selected 13 1069 ⟨6889, by decide⟩ ⟨13, 2, 0, 6889, 1069, 2673, 16384⟩
    (by decide) selected_cut_00097

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
