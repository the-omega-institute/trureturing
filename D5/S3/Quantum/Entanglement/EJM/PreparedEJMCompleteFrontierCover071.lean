/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover070
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_22019_201820 : frontier 9 ⟨201820, by decide⟩
    (prefixCache 12 22019) (prefixPartial 12 22019) = false := by
  decide +kernel

theorem node_context_12_22019_201820 : EJMOriginalGlobalDAGData.nodes 9 ⟨201820, by decide⟩ =
    .split (coordinate 12) (![⟨201720, by decide⟩,⟨201783, by decide⟩,⟨201810, by decide⟩,⟨201819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22019_201820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22019 ⟨201820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22019
    ⟨201820, by decide⟩ (by decide) (![⟨201720, by decide⟩,⟨201783, by decide⟩,⟨201810, by decide⟩,⟨201819, by decide⟩]) unmarked_context_12_22019_201820 node_context_12_22019_201820
  intro a
  fin_cases a
  · exact context_13_88076_201720
  · exact context_13_88077_201783
  · exact context_13_88078_201810
  · exact context_13_88079_201819

theorem unmarked_context_11_5504_201821 : frontier 10 ⟨201821, by decide⟩
    (prefixCache 11 5504) (prefixPartial 11 5504) = false := by
  decide +kernel

theorem node_context_11_5504_201821 : EJMOriginalGlobalDAGData.nodes 10 ⟨201821, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨201526, by decide⟩,⟨201661, by decide⟩,⟨201820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5504_201821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5504 ⟨201821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5504
    ⟨201821, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨201526, by decide⟩,⟨201661, by decide⟩,⟨201820, by decide⟩]) unmarked_context_11_5504_201821 node_context_11_5504_201821
  intro a
  fin_cases a
  · exact context_12_22016_34034
  · exact context_12_22017_201526
  · exact context_12_22018_201661
  · exact context_12_22019_201820

theorem selected_cut_06819 : selected 8 ⟨201874, by decide⟩
    (prefixPartial 13 88080) = some ⟨13, 2, 0, 201874, 88080, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_88080_201874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88080 ⟨201874, by decide⟩ :=
  accepted_of_selected 13 88080 ⟨201874, by decide⟩ ⟨13, 2, 0, 201874, 88080, 2905, 16384⟩
    (by decide) selected_cut_06819

theorem selected_cut_06820 : selected 7 ⟨201904, by decide⟩
    (prefixPartial 14 352324) = some ⟨14, 2, 0, 201904, 352324, 1441, 4096⟩ := by
  decide +kernel

theorem context_14_352324_201904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352324 ⟨201904, by decide⟩ :=
  accepted_of_selected 14 352324 ⟨201904, by decide⟩ ⟨14, 2, 0, 201904, 352324, 1441, 4096⟩
    (by decide) selected_cut_06820

theorem selected_cut_06821 : selected 7 ⟨201929, by decide⟩
    (prefixPartial 14 352325) = some ⟨14, 2, 0, 201929, 352325, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_352325_201929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352325 ⟨201929, by decide⟩ :=
  accepted_of_selected 14 352325 ⟨201929, by decide⟩ ⟨14, 2, 0, 201929, 352325, 1201, 4096⟩
    (by decide) selected_cut_06821

theorem selected_cut_06822 : selected 7 ⟨201949, by decide⟩
    (prefixPartial 14 352326) = some ⟨14, 2, 0, 201949, 352326, 861, 4096⟩ := by
  decide +kernel

theorem context_14_352326_201949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352326 ⟨201949, by decide⟩ :=
  accepted_of_selected 14 352326 ⟨201949, by decide⟩ ⟨14, 2, 0, 201949, 352326, 861, 4096⟩
    (by decide) selected_cut_06822

theorem selected_cut_06823 : selected 7 ⟨201968, by decide⟩
    (prefixPartial 14 352327) = some ⟨14, 2, 0, 201968, 352327, 857, 4096⟩ := by
  decide +kernel

theorem context_14_352327_201968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352327 ⟨201968, by decide⟩ :=
  accepted_of_selected 14 352327 ⟨201968, by decide⟩ ⟨14, 2, 0, 201968, 352327, 857, 4096⟩
    (by decide) selected_cut_06823

theorem unmarked_context_13_88081_201969 : frontier 8 ⟨201969, by decide⟩
    (prefixCache 13 88081) (prefixPartial 13 88081) = false := by
  decide +kernel

theorem node_context_13_88081_201969 : EJMOriginalGlobalDAGData.nodes 8 ⟨201969, by decide⟩ =
    .split (coordinate 13) (![⟨201904, by decide⟩,⟨201929, by decide⟩,⟨201949, by decide⟩,⟨201968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88081_201969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88081 ⟨201969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88081
    ⟨201969, by decide⟩ (by decide) (![⟨201904, by decide⟩,⟨201929, by decide⟩,⟨201949, by decide⟩,⟨201968, by decide⟩]) unmarked_context_13_88081_201969 node_context_13_88081_201969
  intro a
  fin_cases a
  · exact context_14_352324_201904
  · exact context_14_352325_201929
  · exact context_14_352326_201949
  · exact context_14_352327_201968

theorem selected_cut_06824 : selected 8 ⟨202015, by decide⟩
    (prefixPartial 13 88082) = some ⟨13, 2, 0, 202015, 88082, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_88082_202015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88082 ⟨202015, by decide⟩ :=
  accepted_of_selected 13 88082 ⟨202015, by decide⟩ ⟨13, 2, 0, 202015, 88082, 2289, 16384⟩
    (by decide) selected_cut_06824

theorem selected_cut_06825 : selected 8 ⟨202043, by decide⟩
    (prefixPartial 13 88083) = some ⟨13, 2, 0, 202043, 88083, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_88083_202043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88083 ⟨202043, by decide⟩ :=
  accepted_of_selected 13 88083 ⟨202043, by decide⟩ ⟨13, 2, 0, 202043, 88083, 1285, 16384⟩
    (by decide) selected_cut_06825

theorem unmarked_context_12_22020_202044 : frontier 9 ⟨202044, by decide⟩
    (prefixCache 12 22020) (prefixPartial 12 22020) = false := by
  decide +kernel

theorem node_context_12_22020_202044 : EJMOriginalGlobalDAGData.nodes 9 ⟨202044, by decide⟩ =
    .split (coordinate 12) (![⟨201874, by decide⟩,⟨201969, by decide⟩,⟨202015, by decide⟩,⟨202043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22020_202044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22020 ⟨202044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22020
    ⟨202044, by decide⟩ (by decide) (![⟨201874, by decide⟩,⟨201969, by decide⟩,⟨202015, by decide⟩,⟨202043, by decide⟩]) unmarked_context_12_22020_202044 node_context_12_22020_202044
  intro a
  fin_cases a
  · exact context_13_88080_201874
  · exact context_13_88081_201969
  · exact context_13_88082_202015
  · exact context_13_88083_202043

theorem selected_cut_06826 : selected 8 ⟨202089, by decide⟩
    (prefixPartial 13 88084) = some ⟨13, 2, 0, 202089, 88084, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_88084_202089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88084 ⟨202089, by decide⟩ :=
  accepted_of_selected 13 88084 ⟨202089, by decide⟩ ⟨13, 2, 0, 202089, 88084, 3025, 16384⟩
    (by decide) selected_cut_06826

theorem selected_cut_06827 : selected 8 ⟨202152, by decide⟩
    (prefixPartial 13 88085) = some ⟨13, 2, 0, 202152, 88085, 3645, 16384⟩ := by
  decide +kernel

theorem context_13_88085_202152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88085 ⟨202152, by decide⟩ :=
  accepted_of_selected 13 88085 ⟨202152, by decide⟩ ⟨13, 2, 0, 202152, 88085, 3645, 16384⟩
    (by decide) selected_cut_06827

theorem selected_cut_06828 : selected 8 ⟨202181, by decide⟩
    (prefixPartial 13 88086) = some ⟨13, 2, 0, 202181, 88086, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_88086_202181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88086 ⟨202181, by decide⟩ :=
  accepted_of_selected 13 88086 ⟨202181, by decide⟩ ⟨13, 2, 0, 202181, 88086, 2045, 16384⟩
    (by decide) selected_cut_06828

theorem selected_cut_06829 : selected 8 ⟨202192, by decide⟩
    (prefixPartial 13 88087) = some ⟨13, 2, 0, 202192, 88087, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_88087_202192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88087 ⟨202192, by decide⟩ :=
  accepted_of_selected 13 88087 ⟨202192, by decide⟩ ⟨13, 2, 0, 202192, 88087, 1281, 16384⟩
    (by decide) selected_cut_06829

theorem unmarked_context_12_22021_202193 : frontier 9 ⟨202193, by decide⟩
    (prefixCache 12 22021) (prefixPartial 12 22021) = false := by
  decide +kernel

theorem node_context_12_22021_202193 : EJMOriginalGlobalDAGData.nodes 9 ⟨202193, by decide⟩ =
    .split (coordinate 12) (![⟨202089, by decide⟩,⟨202152, by decide⟩,⟨202181, by decide⟩,⟨202192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22021_202193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22021 ⟨202193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22021
    ⟨202193, by decide⟩ (by decide) (![⟨202089, by decide⟩,⟨202152, by decide⟩,⟨202181, by decide⟩,⟨202192, by decide⟩]) unmarked_context_12_22021_202193 node_context_12_22021_202193
  intro a
  fin_cases a
  · exact context_13_88084_202089
  · exact context_13_88085_202152
  · exact context_13_88086_202181
  · exact context_13_88087_202192

theorem selected_cut_06830 : selected 8 ⟨202242, by decide⟩
    (prefixPartial 13 88088) = some ⟨13, 2, 0, 202242, 88088, 3301, 16384⟩ := by
  decide +kernel

theorem context_13_88088_202242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88088 ⟨202242, by decide⟩ :=
  accepted_of_selected 13 88088 ⟨202242, by decide⟩ ⟨13, 2, 0, 202242, 88088, 3301, 16384⟩
    (by decide) selected_cut_06830

theorem selected_cut_06831 : selected 8 ⟨202317, by decide⟩
    (prefixPartial 13 88089) = some ⟨13, 2, 0, 202317, 88089, 4005, 16384⟩ := by
  decide +kernel

theorem context_13_88089_202317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88089 ⟨202317, by decide⟩ :=
  accepted_of_selected 13 88089 ⟨202317, by decide⟩ ⟨13, 2, 0, 202317, 88089, 4005, 16384⟩
    (by decide) selected_cut_06831

theorem selected_cut_06832 : selected 8 ⟨202341, by decide⟩
    (prefixPartial 13 88090) = some ⟨13, 2, 0, 202341, 88090, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_88090_202341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88090 ⟨202341, by decide⟩ :=
  accepted_of_selected 13 88090 ⟨202341, by decide⟩ ⟨13, 2, 0, 202341, 88090, 1885, 16384⟩
    (by decide) selected_cut_06832

theorem selected_cut_06833 : selected 8 ⟨202364, by decide⟩
    (prefixPartial 13 88091) = some ⟨13, 2, 0, 202364, 88091, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_88091_202364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88091 ⟨202364, by decide⟩ :=
  accepted_of_selected 13 88091 ⟨202364, by decide⟩ ⟨13, 2, 0, 202364, 88091, 1417, 16384⟩
    (by decide) selected_cut_06833

theorem unmarked_context_12_22022_202365 : frontier 9 ⟨202365, by decide⟩
    (prefixCache 12 22022) (prefixPartial 12 22022) = false := by
  decide +kernel

theorem node_context_12_22022_202365 : EJMOriginalGlobalDAGData.nodes 9 ⟨202365, by decide⟩ =
    .split (coordinate 12) (![⟨202242, by decide⟩,⟨202317, by decide⟩,⟨202341, by decide⟩,⟨202364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22022_202365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22022 ⟨202365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22022
    ⟨202365, by decide⟩ (by decide) (![⟨202242, by decide⟩,⟨202317, by decide⟩,⟨202341, by decide⟩,⟨202364, by decide⟩]) unmarked_context_12_22022_202365 node_context_12_22022_202365
  intro a
  fin_cases a
  · exact context_13_88088_202242
  · exact context_13_88089_202317
  · exact context_13_88090_202341
  · exact context_13_88091_202364

theorem selected_cut_06834 : selected 8 ⟨202424, by decide⟩
    (prefixPartial 13 88092) = some ⟨13, 2, 0, 202424, 88092, 3777, 16384⟩ := by
  decide +kernel

theorem context_13_88092_202424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88092 ⟨202424, by decide⟩ :=
  accepted_of_selected 13 88092 ⟨202424, by decide⟩ ⟨13, 2, 0, 202424, 88092, 3777, 16384⟩
    (by decide) selected_cut_06834

theorem selected_cut_06835 : selected 7 ⟨202449, by decide⟩
    (prefixPartial 14 352372) = some ⟨14, 2, 0, 202449, 352372, 1361, 4096⟩ := by
  decide +kernel

theorem context_14_352372_202449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352372 ⟨202449, by decide⟩ :=
  accepted_of_selected 14 352372 ⟨202449, by decide⟩ ⟨14, 2, 0, 202449, 352372, 1361, 4096⟩
    (by decide) selected_cut_06835

theorem selected_cut_06836 : selected 7 ⟨202476, by decide⟩
    (prefixPartial 14 352373) = some ⟨14, 2, 0, 202476, 352373, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_352373_202476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352373 ⟨202476, by decide⟩ :=
  accepted_of_selected 14 352373 ⟨202476, by decide⟩ ⟨14, 2, 0, 202476, 352373, 1245, 4096⟩
    (by decide) selected_cut_06836

theorem selected_cut_06837 : selected 7 ⟨202491, by decide⟩
    (prefixPartial 14 352374) = some ⟨14, 2, 0, 202491, 352374, 917, 4096⟩ := by
  decide +kernel

theorem context_14_352374_202491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352374 ⟨202491, by decide⟩ :=
  accepted_of_selected 14 352374 ⟨202491, by decide⟩ ⟨14, 2, 0, 202491, 352374, 917, 4096⟩
    (by decide) selected_cut_06837

theorem selected_cut_06838 : selected 7 ⟨202506, by decide⟩
    (prefixPartial 14 352375) = some ⟨14, 2, 0, 202506, 352375, 953, 4096⟩ := by
  decide +kernel

theorem context_14_352375_202506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352375 ⟨202506, by decide⟩ :=
  accepted_of_selected 14 352375 ⟨202506, by decide⟩ ⟨14, 2, 0, 202506, 352375, 953, 4096⟩
    (by decide) selected_cut_06838

theorem unmarked_context_13_88093_202507 : frontier 8 ⟨202507, by decide⟩
    (prefixCache 13 88093) (prefixPartial 13 88093) = false := by
  decide +kernel

theorem node_context_13_88093_202507 : EJMOriginalGlobalDAGData.nodes 8 ⟨202507, by decide⟩ =
    .split (coordinate 13) (![⟨202449, by decide⟩,⟨202476, by decide⟩,⟨202491, by decide⟩,⟨202506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88093_202507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88093 ⟨202507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88093
    ⟨202507, by decide⟩ (by decide) (![⟨202449, by decide⟩,⟨202476, by decide⟩,⟨202491, by decide⟩,⟨202506, by decide⟩]) unmarked_context_13_88093_202507 node_context_13_88093_202507
  intro a
  fin_cases a
  · exact context_14_352372_202449
  · exact context_14_352373_202476
  · exact context_14_352374_202491
  · exact context_14_352375_202506

theorem selected_cut_06839 : selected 8 ⟨202540, by decide⟩
    (prefixPartial 13 88094) = some ⟨13, 2, 0, 202540, 88094, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_88094_202540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88094 ⟨202540, by decide⟩ :=
  accepted_of_selected 13 88094 ⟨202540, by decide⟩ ⟨13, 2, 0, 202540, 88094, 2269, 16384⟩
    (by decide) selected_cut_06839

theorem selected_cut_06840 : selected 8 ⟨202550, by decide⟩
    (prefixPartial 13 88095) = some ⟨13, 2, 0, 202550, 88095, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_88095_202550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88095 ⟨202550, by decide⟩ :=
  accepted_of_selected 13 88095 ⟨202550, by decide⟩ ⟨13, 2, 0, 202550, 88095, 1117, 16384⟩
    (by decide) selected_cut_06840

theorem unmarked_context_12_22023_202551 : frontier 9 ⟨202551, by decide⟩
    (prefixCache 12 22023) (prefixPartial 12 22023) = false := by
  decide +kernel

theorem node_context_12_22023_202551 : EJMOriginalGlobalDAGData.nodes 9 ⟨202551, by decide⟩ =
    .split (coordinate 12) (![⟨202424, by decide⟩,⟨202507, by decide⟩,⟨202540, by decide⟩,⟨202550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22023_202551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22023 ⟨202551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22023
    ⟨202551, by decide⟩ (by decide) (![⟨202424, by decide⟩,⟨202507, by decide⟩,⟨202540, by decide⟩,⟨202550, by decide⟩]) unmarked_context_12_22023_202551 node_context_12_22023_202551
  intro a
  fin_cases a
  · exact context_13_88092_202424
  · exact context_13_88093_202507
  · exact context_13_88094_202540
  · exact context_13_88095_202550

theorem unmarked_context_11_5505_202552 : frontier 10 ⟨202552, by decide⟩
    (prefixCache 11 5505) (prefixPartial 11 5505) = false := by
  decide +kernel

theorem node_context_11_5505_202552 : EJMOriginalGlobalDAGData.nodes 10 ⟨202552, by decide⟩ =
    .split (coordinate 11) (![⟨202044, by decide⟩,⟨202193, by decide⟩,⟨202365, by decide⟩,⟨202551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5505_202552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5505 ⟨202552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5505
    ⟨202552, by decide⟩ (by decide) (![⟨202044, by decide⟩,⟨202193, by decide⟩,⟨202365, by decide⟩,⟨202551, by decide⟩]) unmarked_context_11_5505_202552 node_context_11_5505_202552
  intro a
  fin_cases a
  · exact context_12_22020_202044
  · exact context_12_22021_202193
  · exact context_12_22022_202365
  · exact context_12_22023_202551

theorem selected_cut_06841 : selected 8 ⟨202581, by decide⟩
    (prefixPartial 13 88096) = some ⟨13, 2, 0, 202581, 88096, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_88096_202581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88096 ⟨202581, by decide⟩ :=
  accepted_of_selected 13 88096 ⟨202581, by decide⟩ ⟨13, 2, 0, 202581, 88096, 2257, 16384⟩
    (by decide) selected_cut_06841

theorem selected_cut_06842 : selected 8 ⟨202636, by decide⟩
    (prefixPartial 13 88097) = some ⟨13, 2, 0, 202636, 88097, 3469, 16384⟩ := by
  decide +kernel

theorem context_13_88097_202636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88097 ⟨202636, by decide⟩ :=
  accepted_of_selected 13 88097 ⟨202636, by decide⟩ ⟨13, 2, 0, 202636, 88097, 3469, 16384⟩
    (by decide) selected_cut_06842

theorem selected_cut_06843 : selected 8 ⟨202664, by decide⟩
    (prefixPartial 13 88098) = some ⟨13, 2, 0, 202664, 88098, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_88098_202664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88098 ⟨202664, by decide⟩ :=
  accepted_of_selected 13 88098 ⟨202664, by decide⟩ ⟨13, 2, 0, 202664, 88098, 1941, 16384⟩
    (by decide) selected_cut_06843

theorem selected_cut_06844 : selected 8 ⟨202676, by decide⟩
    (prefixPartial 13 88099) = some ⟨13, 2, 0, 202676, 88099, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_88099_202676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88099 ⟨202676, by decide⟩ :=
  accepted_of_selected 13 88099 ⟨202676, by decide⟩ ⟨13, 2, 0, 202676, 88099, 1137, 16384⟩
    (by decide) selected_cut_06844

theorem unmarked_context_12_22024_202677 : frontier 9 ⟨202677, by decide⟩
    (prefixCache 12 22024) (prefixPartial 12 22024) = false := by
  decide +kernel

theorem node_context_12_22024_202677 : EJMOriginalGlobalDAGData.nodes 9 ⟨202677, by decide⟩ =
    .split (coordinate 12) (![⟨202581, by decide⟩,⟨202636, by decide⟩,⟨202664, by decide⟩,⟨202676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22024_202677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22024 ⟨202677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22024
    ⟨202677, by decide⟩ (by decide) (![⟨202581, by decide⟩,⟨202636, by decide⟩,⟨202664, by decide⟩,⟨202676, by decide⟩]) unmarked_context_12_22024_202677 node_context_12_22024_202677
  intro a
  fin_cases a
  · exact context_13_88096_202581
  · exact context_13_88097_202636
  · exact context_13_88098_202664
  · exact context_13_88099_202676

theorem selected_cut_06845 : selected 8 ⟨202716, by decide⟩
    (prefixPartial 13 88100) = some ⟨13, 2, 0, 202716, 88100, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_88100_202716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88100 ⟨202716, by decide⟩ :=
  accepted_of_selected 13 88100 ⟨202716, by decide⟩ ⟨13, 2, 0, 202716, 88100, 2801, 16384⟩
    (by decide) selected_cut_06845

theorem selected_cut_06846 : selected 8 ⟨202764, by decide⟩
    (prefixPartial 13 88101) = some ⟨13, 2, 0, 202764, 88101, 2985, 16384⟩ := by
  decide +kernel

theorem context_13_88101_202764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88101 ⟨202764, by decide⟩ :=
  accepted_of_selected 13 88101 ⟨202764, by decide⟩ ⟨13, 2, 0, 202764, 88101, 2985, 16384⟩
    (by decide) selected_cut_06846

theorem selected_cut_06847 : selected 8 ⟨202791, by decide⟩
    (prefixPartial 13 88102) = some ⟨13, 2, 0, 202791, 88102, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_88102_202791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88102 ⟨202791, by decide⟩ :=
  accepted_of_selected 13 88102 ⟨202791, by decide⟩ ⟨13, 2, 0, 202791, 88102, 1793, 16384⟩
    (by decide) selected_cut_06847

theorem selected_cut_06848 : selected 8 ⟨202799, by decide⟩
    (prefixPartial 13 88103) = some ⟨13, 2, 0, 202799, 88103, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_88103_202799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88103 ⟨202799, by decide⟩ :=
  accepted_of_selected 13 88103 ⟨202799, by decide⟩ ⟨13, 2, 0, 202799, 88103, 1213, 16384⟩
    (by decide) selected_cut_06848

theorem unmarked_context_12_22025_202800 : frontier 9 ⟨202800, by decide⟩
    (prefixCache 12 22025) (prefixPartial 12 22025) = false := by
  decide +kernel

theorem node_context_12_22025_202800 : EJMOriginalGlobalDAGData.nodes 9 ⟨202800, by decide⟩ =
    .split (coordinate 12) (![⟨202716, by decide⟩,⟨202764, by decide⟩,⟨202791, by decide⟩,⟨202799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22025_202800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22025 ⟨202800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22025
    ⟨202800, by decide⟩ (by decide) (![⟨202716, by decide⟩,⟨202764, by decide⟩,⟨202791, by decide⟩,⟨202799, by decide⟩]) unmarked_context_12_22025_202800 node_context_12_22025_202800
  intro a
  fin_cases a
  · exact context_13_88100_202716
  · exact context_13_88101_202764
  · exact context_13_88102_202791
  · exact context_13_88103_202799

theorem selected_cut_06849 : selected 7 ⟨202816, by decide⟩
    (prefixPartial 14 352416) = some ⟨14, 2, 0, 202816, 352416, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_352416_202816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352416 ⟨202816, by decide⟩ :=
  accepted_of_selected 14 352416 ⟨202816, by decide⟩ ⟨14, 2, 0, 202816, 352416, 1105, 4096⟩
    (by decide) selected_cut_06849

theorem selected_cut_06850 : selected 7 ⟨202836, by decide⟩
    (prefixPartial 14 352417) = some ⟨14, 2, 0, 202836, 352417, 1393, 4096⟩ := by
  decide +kernel

theorem context_14_352417_202836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352417 ⟨202836, by decide⟩ :=
  accepted_of_selected 14 352417 ⟨202836, by decide⟩ ⟨14, 2, 0, 202836, 352417, 1393, 4096⟩
    (by decide) selected_cut_06850

theorem selected_cut_06851 : selected 7 ⟨202856, by decide⟩
    (prefixPartial 14 352418) = some ⟨14, 2, 0, 202856, 352418, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_352418_202856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352418 ⟨202856, by decide⟩ :=
  accepted_of_selected 14 352418 ⟨202856, by decide⟩ ⟨14, 2, 0, 202856, 352418, 1249, 4096⟩
    (by decide) selected_cut_06851

theorem selected_cut_06852 : selected 7 ⟨202879, by decide⟩
    (prefixPartial 14 352419) = some ⟨14, 2, 0, 202879, 352419, 1389, 4096⟩ := by
  decide +kernel

theorem context_14_352419_202879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352419 ⟨202879, by decide⟩ :=
  accepted_of_selected 14 352419 ⟨202879, by decide⟩ ⟨14, 2, 0, 202879, 352419, 1389, 4096⟩
    (by decide) selected_cut_06852

theorem unmarked_context_13_88104_202880 : frontier 8 ⟨202880, by decide⟩
    (prefixCache 13 88104) (prefixPartial 13 88104) = false := by
  decide +kernel

theorem node_context_13_88104_202880 : EJMOriginalGlobalDAGData.nodes 8 ⟨202880, by decide⟩ =
    .split (coordinate 13) (![⟨202816, by decide⟩,⟨202836, by decide⟩,⟨202856, by decide⟩,⟨202879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88104_202880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88104 ⟨202880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88104
    ⟨202880, by decide⟩ (by decide) (![⟨202816, by decide⟩,⟨202836, by decide⟩,⟨202856, by decide⟩,⟨202879, by decide⟩]) unmarked_context_13_88104_202880 node_context_13_88104_202880
  intro a
  fin_cases a
  · exact context_14_352416_202816
  · exact context_14_352417_202836
  · exact context_14_352418_202856
  · exact context_14_352419_202879

theorem selected_cut_06853 : selected 7 ⟨202920, by decide⟩
    (prefixPartial 14 352420) = some ⟨14, 2, 0, 202920, 352420, 1761, 4096⟩ := by
  decide +kernel

theorem context_14_352420_202920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352420 ⟨202920, by decide⟩ :=
  accepted_of_selected 14 352420 ⟨202920, by decide⟩ ⟨14, 2, 0, 202920, 352420, 1761, 4096⟩
    (by decide) selected_cut_06853

theorem selected_cut_06854 : selected 7 ⟨202961, by decide⟩
    (prefixPartial 14 352421) = some ⟨14, 2, 0, 202961, 352421, 1797, 4096⟩ := by
  decide +kernel

theorem context_14_352421_202961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352421 ⟨202961, by decide⟩ :=
  accepted_of_selected 14 352421 ⟨202961, by decide⟩ ⟨14, 2, 0, 202961, 352421, 1797, 4096⟩
    (by decide) selected_cut_06854

theorem selected_cut_06855 : selected 7 ⟨202992, by decide⟩
    (prefixPartial 14 352422) = some ⟨14, 2, 0, 202992, 352422, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_352422_202992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352422 ⟨202992, by decide⟩ :=
  accepted_of_selected 14 352422 ⟨202992, by decide⟩ ⟨14, 2, 0, 202992, 352422, 1417, 4096⟩
    (by decide) selected_cut_06855

theorem selected_cut_06856 : selected 7 ⟨203011, by decide⟩
    (prefixPartial 14 352423) = some ⟨14, 2, 0, 203011, 352423, 1197, 4096⟩ := by
  decide +kernel

theorem context_14_352423_203011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352423 ⟨203011, by decide⟩ :=
  accepted_of_selected 14 352423 ⟨203011, by decide⟩ ⟨14, 2, 0, 203011, 352423, 1197, 4096⟩
    (by decide) selected_cut_06856

theorem unmarked_context_13_88105_203012 : frontier 8 ⟨203012, by decide⟩
    (prefixCache 13 88105) (prefixPartial 13 88105) = false := by
  decide +kernel

theorem node_context_13_88105_203012 : EJMOriginalGlobalDAGData.nodes 8 ⟨203012, by decide⟩ =
    .split (coordinate 13) (![⟨202920, by decide⟩,⟨202961, by decide⟩,⟨202992, by decide⟩,⟨203011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88105_203012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88105 ⟨203012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88105
    ⟨203012, by decide⟩ (by decide) (![⟨202920, by decide⟩,⟨202961, by decide⟩,⟨202992, by decide⟩,⟨203011, by decide⟩]) unmarked_context_13_88105_203012 node_context_13_88105_203012
  intro a
  fin_cases a
  · exact context_14_352420_202920
  · exact context_14_352421_202961
  · exact context_14_352422_202992
  · exact context_14_352423_203011

theorem selected_cut_06857 : selected 8 ⟨203075, by decide⟩
    (prefixPartial 13 88106) = some ⟨13, 2, 0, 203075, 88106, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_88106_203075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88106 ⟨203075, by decide⟩ :=
  accepted_of_selected 13 88106 ⟨203075, by decide⟩ ⟨13, 2, 0, 203075, 88106, 2901, 16384⟩
    (by decide) selected_cut_06857

theorem selected_cut_06858 : selected 8 ⟨203106, by decide⟩
    (prefixPartial 13 88107) = some ⟨13, 2, 0, 203106, 88107, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_88107_203106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88107 ⟨203106, by decide⟩ :=
  accepted_of_selected 13 88107 ⟨203106, by decide⟩ ⟨13, 2, 0, 203106, 88107, 1809, 16384⟩
    (by decide) selected_cut_06858

theorem unmarked_context_12_22026_203107 : frontier 9 ⟨203107, by decide⟩
    (prefixCache 12 22026) (prefixPartial 12 22026) = false := by
  decide +kernel

theorem node_context_12_22026_203107 : EJMOriginalGlobalDAGData.nodes 9 ⟨203107, by decide⟩ =
    .split (coordinate 12) (![⟨202880, by decide⟩,⟨203012, by decide⟩,⟨203075, by decide⟩,⟨203106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22026_203107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22026 ⟨203107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22026
    ⟨203107, by decide⟩ (by decide) (![⟨202880, by decide⟩,⟨203012, by decide⟩,⟨203075, by decide⟩,⟨203106, by decide⟩]) unmarked_context_12_22026_203107 node_context_12_22026_203107
  intro a
  fin_cases a
  · exact context_13_88104_202880
  · exact context_13_88105_203012
  · exact context_13_88106_203075
  · exact context_13_88107_203106

theorem selected_cut_06859 : selected 8 ⟨203151, by decide⟩
    (prefixPartial 13 88108) = some ⟨13, 2, 0, 203151, 88108, 3201, 16384⟩ := by
  decide +kernel

theorem context_13_88108_203151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88108 ⟨203151, by decide⟩ :=
  accepted_of_selected 13 88108 ⟨203151, by decide⟩ ⟨13, 2, 0, 203151, 88108, 3201, 16384⟩
    (by decide) selected_cut_06859

theorem selected_cut_06860 : selected 7 ⟨203176, by decide⟩
    (prefixPartial 14 352436) = some ⟨14, 2, 0, 203176, 352436, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_352436_203176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352436 ⟨203176, by decide⟩ :=
  accepted_of_selected 14 352436 ⟨203176, by decide⟩ ⟨14, 2, 0, 203176, 352436, 1221, 4096⟩
    (by decide) selected_cut_06860

theorem selected_cut_06861 : selected 7 ⟨203199, by decide⟩
    (prefixPartial 14 352437) = some ⟨14, 2, 0, 203199, 352437, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_352437_203199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352437 ⟨203199, by decide⟩ :=
  accepted_of_selected 14 352437 ⟨203199, by decide⟩ ⟨14, 2, 0, 203199, 352437, 1193, 4096⟩
    (by decide) selected_cut_06861

theorem selected_cut_06862 : selected 7 ⟨203214, by decide⟩
    (prefixPartial 14 352438) = some ⟨14, 2, 0, 203214, 352438, 937, 4096⟩ := by
  decide +kernel

theorem context_14_352438_203214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352438 ⟨203214, by decide⟩ :=
  accepted_of_selected 14 352438 ⟨203214, by decide⟩ ⟨14, 2, 0, 203214, 352438, 937, 4096⟩
    (by decide) selected_cut_06862

theorem selected_cut_06863 : selected 7 ⟨203228, by decide⟩
    (prefixPartial 14 352439) = some ⟨14, 2, 0, 203228, 352439, 877, 4096⟩ := by
  decide +kernel

theorem context_14_352439_203228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352439 ⟨203228, by decide⟩ :=
  accepted_of_selected 14 352439 ⟨203228, by decide⟩ ⟨14, 2, 0, 203228, 352439, 877, 4096⟩
    (by decide) selected_cut_06863

theorem unmarked_context_13_88109_203229 : frontier 8 ⟨203229, by decide⟩
    (prefixCache 13 88109) (prefixPartial 13 88109) = false := by
  decide +kernel

theorem node_context_13_88109_203229 : EJMOriginalGlobalDAGData.nodes 8 ⟨203229, by decide⟩ =
    .split (coordinate 13) (![⟨203176, by decide⟩,⟨203199, by decide⟩,⟨203214, by decide⟩,⟨203228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88109_203229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88109 ⟨203229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88109
    ⟨203229, by decide⟩ (by decide) (![⟨203176, by decide⟩,⟨203199, by decide⟩,⟨203214, by decide⟩,⟨203228, by decide⟩]) unmarked_context_13_88109_203229 node_context_13_88109_203229
  intro a
  fin_cases a
  · exact context_14_352436_203176
  · exact context_14_352437_203199
  · exact context_14_352438_203214
  · exact context_14_352439_203228

theorem selected_cut_06864 : selected 8 ⟨203260, by decide⟩
    (prefixPartial 13 88110) = some ⟨13, 2, 0, 203260, 88110, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_88110_203260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88110 ⟨203260, by decide⟩ :=
  accepted_of_selected 13 88110 ⟨203260, by decide⟩ ⟨13, 2, 0, 203260, 88110, 1941, 16384⟩
    (by decide) selected_cut_06864

theorem selected_cut_06865 : selected 8 ⟨203269, by decide⟩
    (prefixPartial 13 88111) = some ⟨13, 2, 0, 203269, 88111, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_88111_203269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88111 ⟨203269, by decide⟩ :=
  accepted_of_selected 13 88111 ⟨203269, by decide⟩ ⟨13, 2, 0, 203269, 88111, 1053, 16384⟩
    (by decide) selected_cut_06865

theorem unmarked_context_12_22027_203270 : frontier 9 ⟨203270, by decide⟩
    (prefixCache 12 22027) (prefixPartial 12 22027) = false := by
  decide +kernel

theorem node_context_12_22027_203270 : EJMOriginalGlobalDAGData.nodes 9 ⟨203270, by decide⟩ =
    .split (coordinate 12) (![⟨203151, by decide⟩,⟨203229, by decide⟩,⟨203260, by decide⟩,⟨203269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22027_203270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22027 ⟨203270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22027
    ⟨203270, by decide⟩ (by decide) (![⟨203151, by decide⟩,⟨203229, by decide⟩,⟨203260, by decide⟩,⟨203269, by decide⟩]) unmarked_context_12_22027_203270 node_context_12_22027_203270
  intro a
  fin_cases a
  · exact context_13_88108_203151
  · exact context_13_88109_203229
  · exact context_13_88110_203260
  · exact context_13_88111_203269

theorem unmarked_context_11_5506_203271 : frontier 10 ⟨203271, by decide⟩
    (prefixCache 11 5506) (prefixPartial 11 5506) = false := by
  decide +kernel

theorem node_context_11_5506_203271 : EJMOriginalGlobalDAGData.nodes 10 ⟨203271, by decide⟩ =
    .split (coordinate 11) (![⟨202677, by decide⟩,⟨202800, by decide⟩,⟨203107, by decide⟩,⟨203270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5506_203271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5506 ⟨203271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5506
    ⟨203271, by decide⟩ (by decide) (![⟨202677, by decide⟩,⟨202800, by decide⟩,⟨203107, by decide⟩,⟨203270, by decide⟩]) unmarked_context_11_5506_203271 node_context_11_5506_203271
  intro a
  fin_cases a
  · exact context_12_22024_202677
  · exact context_12_22025_202800
  · exact context_12_22026_203107
  · exact context_12_22027_203270

theorem selected_cut_06866 : selected 8 ⟨203301, by decide⟩
    (prefixPartial 13 88112) = some ⟨13, 2, 0, 203301, 88112, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_88112_203301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88112 ⟨203301, by decide⟩ :=
  accepted_of_selected 13 88112 ⟨203301, by decide⟩ ⟨13, 2, 0, 203301, 88112, 2073, 16384⟩
    (by decide) selected_cut_06866

theorem selected_cut_06867 : selected 8 ⟨203357, by decide⟩
    (prefixPartial 13 88113) = some ⟨13, 2, 0, 203357, 88113, 4001, 16384⟩ := by
  decide +kernel

theorem context_13_88113_203357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88113 ⟨203357, by decide⟩ :=
  accepted_of_selected 13 88113 ⟨203357, by decide⟩ ⟨13, 2, 0, 203357, 88113, 4001, 16384⟩
    (by decide) selected_cut_06867

theorem selected_cut_06868 : selected 8 ⟨203387, by decide⟩
    (prefixPartial 13 88114) = some ⟨13, 2, 0, 203387, 88114, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_88114_203387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88114 ⟨203387, by decide⟩ :=
  accepted_of_selected 13 88114 ⟨203387, by decide⟩ ⟨13, 2, 0, 203387, 88114, 2341, 16384⟩
    (by decide) selected_cut_06868

theorem selected_cut_06869 : selected 8 ⟨203406, by decide⟩
    (prefixPartial 13 88115) = some ⟨13, 2, 0, 203406, 88115, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_88115_203406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88115 ⟨203406, by decide⟩ :=
  accepted_of_selected 13 88115 ⟨203406, by decide⟩ ⟨13, 2, 0, 203406, 88115, 1233, 16384⟩
    (by decide) selected_cut_06869

theorem unmarked_context_12_22028_203407 : frontier 9 ⟨203407, by decide⟩
    (prefixCache 12 22028) (prefixPartial 12 22028) = false := by
  decide +kernel

theorem node_context_12_22028_203407 : EJMOriginalGlobalDAGData.nodes 9 ⟨203407, by decide⟩ =
    .split (coordinate 12) (![⟨203301, by decide⟩,⟨203357, by decide⟩,⟨203387, by decide⟩,⟨203406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22028_203407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22028 ⟨203407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22028
    ⟨203407, by decide⟩ (by decide) (![⟨203301, by decide⟩,⟨203357, by decide⟩,⟨203387, by decide⟩,⟨203406, by decide⟩]) unmarked_context_12_22028_203407 node_context_12_22028_203407
  intro a
  fin_cases a
  · exact context_13_88112_203301
  · exact context_13_88113_203357
  · exact context_13_88114_203387
  · exact context_13_88115_203406

theorem selected_cut_06870 : selected 8 ⟨203441, by decide⟩
    (prefixPartial 13 88116) = some ⟨13, 2, 0, 203441, 88116, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_88116_203441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88116 ⟨203441, by decide⟩ :=
  accepted_of_selected 13 88116 ⟨203441, by decide⟩ ⟨13, 2, 0, 203441, 88116, 2545, 16384⟩
    (by decide) selected_cut_06870

theorem selected_cut_06871 : selected 8 ⟨203497, by decide⟩
    (prefixPartial 13 88117) = some ⟨13, 2, 0, 203497, 88117, 3453, 16384⟩ := by
  decide +kernel

theorem context_13_88117_203497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88117 ⟨203497, by decide⟩ :=
  accepted_of_selected 13 88117 ⟨203497, by decide⟩ ⟨13, 2, 0, 203497, 88117, 3453, 16384⟩
    (by decide) selected_cut_06871

theorem selected_cut_06872 : selected 8 ⟨203526, by decide⟩
    (prefixPartial 13 88118) = some ⟨13, 2, 0, 203526, 88118, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_88118_203526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88118 ⟨203526, by decide⟩ :=
  accepted_of_selected 13 88118 ⟨203526, by decide⟩ ⟨13, 2, 0, 203526, 88118, 2185, 16384⟩
    (by decide) selected_cut_06872

theorem selected_cut_06873 : selected 8 ⟨203534, by decide⟩
    (prefixPartial 13 88119) = some ⟨13, 2, 0, 203534, 88119, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_88119_203534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88119 ⟨203534, by decide⟩ :=
  accepted_of_selected 13 88119 ⟨203534, by decide⟩ ⟨13, 2, 0, 203534, 88119, 1129, 16384⟩
    (by decide) selected_cut_06873

theorem unmarked_context_12_22029_203535 : frontier 9 ⟨203535, by decide⟩
    (prefixCache 12 22029) (prefixPartial 12 22029) = false := by
  decide +kernel

theorem node_context_12_22029_203535 : EJMOriginalGlobalDAGData.nodes 9 ⟨203535, by decide⟩ =
    .split (coordinate 12) (![⟨203441, by decide⟩,⟨203497, by decide⟩,⟨203526, by decide⟩,⟨203534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22029_203535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22029 ⟨203535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22029
    ⟨203535, by decide⟩ (by decide) (![⟨203441, by decide⟩,⟨203497, by decide⟩,⟨203526, by decide⟩,⟨203534, by decide⟩]) unmarked_context_12_22029_203535 node_context_12_22029_203535
  intro a
  fin_cases a
  · exact context_13_88116_203441
  · exact context_13_88117_203497
  · exact context_13_88118_203526
  · exact context_13_88119_203534

theorem selected_cut_06874 : selected 8 ⟨203574, by decide⟩
    (prefixPartial 13 88120) = some ⟨13, 2, 0, 203574, 88120, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_88120_203574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88120 ⟨203574, by decide⟩ :=
  accepted_of_selected 13 88120 ⟨203574, by decide⟩ ⟨13, 2, 0, 203574, 88120, 2717, 16384⟩
    (by decide) selected_cut_06874

theorem selected_cut_06875 : selected 7 ⟨203597, by decide⟩
    (prefixPartial 14 352484) = some ⟨14, 2, 0, 203597, 352484, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_352484_203597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352484 ⟨203597, by decide⟩ :=
  accepted_of_selected 14 352484 ⟨203597, by decide⟩ ⟨14, 2, 0, 203597, 352484, 1245, 4096⟩
    (by decide) selected_cut_06875

theorem selected_cut_06876 : selected 7 ⟨203616, by decide⟩
    (prefixPartial 14 352485) = some ⟨14, 2, 0, 203616, 352485, 1209, 4096⟩ := by
  decide +kernel

theorem context_14_352485_203616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352485 ⟨203616, by decide⟩ :=
  accepted_of_selected 14 352485 ⟨203616, by decide⟩ ⟨14, 2, 0, 203616, 352485, 1209, 4096⟩
    (by decide) selected_cut_06876

theorem selected_cut_06877 : selected 7 ⟨203630, by decide⟩
    (prefixPartial 14 352486) = some ⟨14, 2, 0, 203630, 352486, 905, 4096⟩ := by
  decide +kernel

theorem context_14_352486_203630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352486 ⟨203630, by decide⟩ :=
  accepted_of_selected 14 352486 ⟨203630, by decide⟩ ⟨14, 2, 0, 203630, 352486, 905, 4096⟩
    (by decide) selected_cut_06877

theorem selected_cut_06878 : selected 7 ⟨203640, by decide⟩
    (prefixPartial 14 352487) = some ⟨14, 2, 0, 203640, 352487, 797, 4096⟩ := by
  decide +kernel

theorem context_14_352487_203640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352487 ⟨203640, by decide⟩ :=
  accepted_of_selected 14 352487 ⟨203640, by decide⟩ ⟨14, 2, 0, 203640, 352487, 797, 4096⟩
    (by decide) selected_cut_06878

theorem unmarked_context_13_88121_203641 : frontier 8 ⟨203641, by decide⟩
    (prefixCache 13 88121) (prefixPartial 13 88121) = false := by
  decide +kernel

theorem node_context_13_88121_203641 : EJMOriginalGlobalDAGData.nodes 8 ⟨203641, by decide⟩ =
    .split (coordinate 13) (![⟨203597, by decide⟩,⟨203616, by decide⟩,⟨203630, by decide⟩,⟨203640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88121_203641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88121 ⟨203641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88121
    ⟨203641, by decide⟩ (by decide) (![⟨203597, by decide⟩,⟨203616, by decide⟩,⟨203630, by decide⟩,⟨203640, by decide⟩]) unmarked_context_13_88121_203641 node_context_13_88121_203641
  intro a
  fin_cases a
  · exact context_14_352484_203597
  · exact context_14_352485_203616
  · exact context_14_352486_203630
  · exact context_14_352487_203640

theorem selected_cut_06879 : selected 8 ⟨203665, by decide⟩
    (prefixPartial 13 88122) = some ⟨13, 2, 0, 203665, 88122, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_88122_203665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88122 ⟨203665, by decide⟩ :=
  accepted_of_selected 13 88122 ⟨203665, by decide⟩ ⟨13, 2, 0, 203665, 88122, 1849, 16384⟩
    (by decide) selected_cut_06879

theorem selected_cut_06880 : selected 8 ⟨203677, by decide⟩
    (prefixPartial 13 88123) = some ⟨13, 2, 0, 203677, 88123, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_88123_203677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88123 ⟨203677, by decide⟩ :=
  accepted_of_selected 13 88123 ⟨203677, by decide⟩ ⟨13, 2, 0, 203677, 88123, 1205, 16384⟩
    (by decide) selected_cut_06880

theorem unmarked_context_12_22030_203678 : frontier 9 ⟨203678, by decide⟩
    (prefixCache 12 22030) (prefixPartial 12 22030) = false := by
  decide +kernel

theorem node_context_12_22030_203678 : EJMOriginalGlobalDAGData.nodes 9 ⟨203678, by decide⟩ =
    .split (coordinate 12) (![⟨203574, by decide⟩,⟨203641, by decide⟩,⟨203665, by decide⟩,⟨203677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22030_203678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22030 ⟨203678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22030
    ⟨203678, by decide⟩ (by decide) (![⟨203574, by decide⟩,⟨203641, by decide⟩,⟨203665, by decide⟩,⟨203677, by decide⟩]) unmarked_context_12_22030_203678 node_context_12_22030_203678
  intro a
  fin_cases a
  · exact context_13_88120_203574
  · exact context_13_88121_203641
  · exact context_13_88122_203665
  · exact context_13_88123_203677

theorem selected_cut_06881 : selected 8 ⟨203722, by decide⟩
    (prefixPartial 13 88124) = some ⟨13, 2, 0, 203722, 88124, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_88124_203722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88124 ⟨203722, by decide⟩ :=
  accepted_of_selected 13 88124 ⟨203722, by decide⟩ ⟨13, 2, 0, 203722, 88124, 2873, 16384⟩
    (by decide) selected_cut_06881

theorem selected_cut_06882 : selected 7 ⟨203749, by decide⟩
    (prefixPartial 14 352500) = some ⟨14, 2, 0, 203749, 352500, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_352500_203749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352500 ⟨203749, by decide⟩ :=
  accepted_of_selected 14 352500 ⟨203749, by decide⟩ ⟨14, 2, 0, 203749, 352500, 1437, 4096⟩
    (by decide) selected_cut_06882

theorem selected_cut_06883 : selected 7 ⟨203770, by decide⟩
    (prefixPartial 14 352501) = some ⟨14, 2, 0, 203770, 352501, 1153, 4096⟩ := by
  decide +kernel

theorem context_14_352501_203770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352501 ⟨203770, by decide⟩ :=
  accepted_of_selected 14 352501 ⟨203770, by decide⟩ ⟨14, 2, 0, 203770, 352501, 1153, 4096⟩
    (by decide) selected_cut_06883

theorem selected_cut_06884 : selected 7 ⟨203787, by decide⟩
    (prefixPartial 14 352502) = some ⟨14, 2, 0, 203787, 352502, 901, 4096⟩ := by
  decide +kernel

theorem context_14_352502_203787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352502 ⟨203787, by decide⟩ :=
  accepted_of_selected 14 352502 ⟨203787, by decide⟩ ⟨14, 2, 0, 203787, 352502, 901, 4096⟩
    (by decide) selected_cut_06884

theorem selected_cut_06885 : selected 7 ⟨203801, by decide⟩
    (prefixPartial 14 352503) = some ⟨14, 2, 0, 203801, 352503, 853, 4096⟩ := by
  decide +kernel

theorem context_14_352503_203801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352503 ⟨203801, by decide⟩ :=
  accepted_of_selected 14 352503 ⟨203801, by decide⟩ ⟨14, 2, 0, 203801, 352503, 853, 4096⟩
    (by decide) selected_cut_06885

theorem unmarked_context_13_88125_203802 : frontier 8 ⟨203802, by decide⟩
    (prefixCache 13 88125) (prefixPartial 13 88125) = false := by
  decide +kernel

theorem node_context_13_88125_203802 : EJMOriginalGlobalDAGData.nodes 8 ⟨203802, by decide⟩ =
    .split (coordinate 13) (![⟨203749, by decide⟩,⟨203770, by decide⟩,⟨203787, by decide⟩,⟨203801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88125_203802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88125 ⟨203802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88125
    ⟨203802, by decide⟩ (by decide) (![⟨203749, by decide⟩,⟨203770, by decide⟩,⟨203787, by decide⟩,⟨203801, by decide⟩]) unmarked_context_13_88125_203802 node_context_13_88125_203802
  intro a
  fin_cases a
  · exact context_14_352500_203749
  · exact context_14_352501_203770
  · exact context_14_352502_203787
  · exact context_14_352503_203801

theorem selected_cut_06886 : selected 8 ⟨203829, by decide⟩
    (prefixPartial 13 88126) = some ⟨13, 2, 0, 203829, 88126, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_88126_203829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88126 ⟨203829, by decide⟩ :=
  accepted_of_selected 13 88126 ⟨203829, by decide⟩ ⟨13, 2, 0, 203829, 88126, 2105, 16384⟩
    (by decide) selected_cut_06886

theorem selected_cut_06887 : selected 8 ⟨203840, by decide⟩
    (prefixPartial 13 88127) = some ⟨13, 2, 0, 203840, 88127, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_88127_203840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88127 ⟨203840, by decide⟩ :=
  accepted_of_selected 13 88127 ⟨203840, by decide⟩ ⟨13, 2, 0, 203840, 88127, 1053, 16384⟩
    (by decide) selected_cut_06887

theorem unmarked_context_12_22031_203841 : frontier 9 ⟨203841, by decide⟩
    (prefixCache 12 22031) (prefixPartial 12 22031) = false := by
  decide +kernel

theorem node_context_12_22031_203841 : EJMOriginalGlobalDAGData.nodes 9 ⟨203841, by decide⟩ =
    .split (coordinate 12) (![⟨203722, by decide⟩,⟨203802, by decide⟩,⟨203829, by decide⟩,⟨203840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22031_203841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22031 ⟨203841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22031
    ⟨203841, by decide⟩ (by decide) (![⟨203722, by decide⟩,⟨203802, by decide⟩,⟨203829, by decide⟩,⟨203840, by decide⟩]) unmarked_context_12_22031_203841 node_context_12_22031_203841
  intro a
  fin_cases a
  · exact context_13_88124_203722
  · exact context_13_88125_203802
  · exact context_13_88126_203829
  · exact context_13_88127_203840

theorem unmarked_context_11_5507_203842 : frontier 10 ⟨203842, by decide⟩
    (prefixCache 11 5507) (prefixPartial 11 5507) = false := by
  decide +kernel

theorem node_context_11_5507_203842 : EJMOriginalGlobalDAGData.nodes 10 ⟨203842, by decide⟩ =
    .split (coordinate 11) (![⟨203407, by decide⟩,⟨203535, by decide⟩,⟨203678, by decide⟩,⟨203841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5507_203842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5507 ⟨203842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5507
    ⟨203842, by decide⟩ (by decide) (![⟨203407, by decide⟩,⟨203535, by decide⟩,⟨203678, by decide⟩,⟨203841, by decide⟩]) unmarked_context_11_5507_203842 node_context_11_5507_203842
  intro a
  fin_cases a
  · exact context_12_22028_203407
  · exact context_12_22029_203535
  · exact context_12_22030_203678
  · exact context_12_22031_203841

theorem unmarked_context_10_1376_203843 : frontier 11 ⟨203843, by decide⟩
    (prefixCache 10 1376) (prefixPartial 10 1376) = false := by
  decide +kernel

theorem node_context_10_1376_203843 : EJMOriginalGlobalDAGData.nodes 11 ⟨203843, by decide⟩ =
    .split (coordinate 10) (![⟨201821, by decide⟩,⟨202552, by decide⟩,⟨203271, by decide⟩,⟨203842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1376_203843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1376 ⟨203843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1376
    ⟨203843, by decide⟩ (by decide) (![⟨201821, by decide⟩,⟨202552, by decide⟩,⟨203271, by decide⟩,⟨203842, by decide⟩]) unmarked_context_10_1376_203843 node_context_10_1376_203843
  intro a
  fin_cases a
  · exact context_11_5504_201821
  · exact context_11_5505_202552
  · exact context_11_5506_203271
  · exact context_11_5507_203842

theorem selected_cut_06888 : selected 8 ⟨203859, by decide⟩
    (prefixPartial 13 88128) = some ⟨13, 2, 0, 203859, 88128, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_88128_203859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88128 ⟨203859, by decide⟩ :=
  accepted_of_selected 13 88128 ⟨203859, by decide⟩ ⟨13, 2, 0, 203859, 88128, 1333, 16384⟩
    (by decide) selected_cut_06888

theorem selected_cut_06889 : selected 8 ⟨203884, by decide⟩
    (prefixPartial 13 88129) = some ⟨13, 2, 0, 203884, 88129, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_88129_203884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88129 ⟨203884, by decide⟩ :=
  accepted_of_selected 13 88129 ⟨203884, by decide⟩ ⟨13, 2, 0, 203884, 88129, 1701, 16384⟩
    (by decide) selected_cut_06889

theorem selected_cut_06890 : selected 8 ⟨203901, by decide⟩
    (prefixPartial 13 88130) = some ⟨13, 2, 0, 203901, 88130, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_88130_203901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88130 ⟨203901, by decide⟩ :=
  accepted_of_selected 13 88130 ⟨203901, by decide⟩ ⟨13, 2, 0, 203901, 88130, 1513, 16384⟩
    (by decide) selected_cut_06890

theorem selected_cut_06891 : selected 8 ⟨203910, by decide⟩
    (prefixPartial 13 88131) = some ⟨13, 2, 0, 203910, 88131, 805, 16384⟩ := by
  decide +kernel

theorem context_13_88131_203910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88131 ⟨203910, by decide⟩ :=
  accepted_of_selected 13 88131 ⟨203910, by decide⟩ ⟨13, 2, 0, 203910, 88131, 805, 16384⟩
    (by decide) selected_cut_06891

theorem unmarked_context_12_22032_203911 : frontier 9 ⟨203911, by decide⟩
    (prefixCache 12 22032) (prefixPartial 12 22032) = false := by
  decide +kernel

theorem node_context_12_22032_203911 : EJMOriginalGlobalDAGData.nodes 9 ⟨203911, by decide⟩ =
    .split (coordinate 12) (![⟨203859, by decide⟩,⟨203884, by decide⟩,⟨203901, by decide⟩,⟨203910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22032_203911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22032 ⟨203911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22032
    ⟨203911, by decide⟩ (by decide) (![⟨203859, by decide⟩,⟨203884, by decide⟩,⟨203901, by decide⟩,⟨203910, by decide⟩]) unmarked_context_12_22032_203911 node_context_12_22032_203911
  intro a
  fin_cases a
  · exact context_13_88128_203859
  · exact context_13_88129_203884
  · exact context_13_88130_203901
  · exact context_13_88131_203910

theorem selected_cut_06892 : selected 8 ⟨203932, by decide⟩
    (prefixPartial 13 88132) = some ⟨13, 2, 0, 203932, 88132, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_88132_203932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88132 ⟨203932, by decide⟩ :=
  accepted_of_selected 13 88132 ⟨203932, by decide⟩ ⟨13, 2, 0, 203932, 88132, 1629, 16384⟩
    (by decide) selected_cut_06892

theorem selected_cut_06893 : selected 8 ⟨203955, by decide⟩
    (prefixPartial 13 88133) = some ⟨13, 2, 0, 203955, 88133, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_88133_203955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88133 ⟨203955, by decide⟩ :=
  accepted_of_selected 13 88133 ⟨203955, by decide⟩ ⟨13, 2, 0, 203955, 88133, 1477, 16384⟩
    (by decide) selected_cut_06893

theorem selected_cut_06894 : selected 8 ⟨203973, by decide⟩
    (prefixPartial 13 88134) = some ⟨13, 2, 0, 203973, 88134, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_88134_203973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88134 ⟨203973, by decide⟩ :=
  accepted_of_selected 13 88134 ⟨203973, by decide⟩ ⟨13, 2, 0, 203973, 88134, 1285, 16384⟩
    (by decide) selected_cut_06894

theorem selected_cut_06895 : selected 8 ⟨203982, by decide⟩
    (prefixPartial 13 88135) = some ⟨13, 2, 0, 203982, 88135, 829, 16384⟩ := by
  decide +kernel

theorem context_13_88135_203982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88135 ⟨203982, by decide⟩ :=
  accepted_of_selected 13 88135 ⟨203982, by decide⟩ ⟨13, 2, 0, 203982, 88135, 829, 16384⟩
    (by decide) selected_cut_06895

theorem unmarked_context_12_22033_203983 : frontier 9 ⟨203983, by decide⟩
    (prefixCache 12 22033) (prefixPartial 12 22033) = false := by
  decide +kernel

theorem node_context_12_22033_203983 : EJMOriginalGlobalDAGData.nodes 9 ⟨203983, by decide⟩ =
    .split (coordinate 12) (![⟨203932, by decide⟩,⟨203955, by decide⟩,⟨203973, by decide⟩,⟨203982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22033_203983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22033 ⟨203983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22033
    ⟨203983, by decide⟩ (by decide) (![⟨203932, by decide⟩,⟨203955, by decide⟩,⟨203973, by decide⟩,⟨203982, by decide⟩]) unmarked_context_12_22033_203983 node_context_12_22033_203983
  intro a
  fin_cases a
  · exact context_13_88132_203932
  · exact context_13_88133_203955
  · exact context_13_88134_203973
  · exact context_13_88135_203982

theorem selected_cut_06896 : selected 8 ⟨204006, by decide⟩
    (prefixPartial 13 88136) = some ⟨13, 2, 0, 204006, 88136, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_88136_204006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88136 ⟨204006, by decide⟩ :=
  accepted_of_selected 13 88136 ⟨204006, by decide⟩ ⟨13, 2, 0, 204006, 88136, 1689, 16384⟩
    (by decide) selected_cut_06896

theorem selected_cut_06897 : selected 8 ⟨204034, by decide⟩
    (prefixPartial 13 88137) = some ⟨13, 2, 0, 204034, 88137, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_88137_204034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88137 ⟨204034, by decide⟩ :=
  accepted_of_selected 13 88137 ⟨204034, by decide⟩ ⟨13, 2, 0, 204034, 88137, 2029, 16384⟩
    (by decide) selected_cut_06897

theorem selected_cut_06898 : selected 8 ⟨204053, by decide⟩
    (prefixPartial 13 88138) = some ⟨13, 2, 0, 204053, 88138, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_88138_204053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88138 ⟨204053, by decide⟩ :=
  accepted_of_selected 13 88138 ⟨204053, by decide⟩ ⟨13, 2, 0, 204053, 88138, 1321, 16384⟩
    (by decide) selected_cut_06898

theorem selected_cut_06899 : selected 8 ⟨204061, by decide⟩
    (prefixPartial 13 88139) = some ⟨13, 2, 0, 204061, 88139, 937, 16384⟩ := by
  decide +kernel

theorem context_13_88139_204061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88139 ⟨204061, by decide⟩ :=
  accepted_of_selected 13 88139 ⟨204061, by decide⟩ ⟨13, 2, 0, 204061, 88139, 937, 16384⟩
    (by decide) selected_cut_06899

theorem unmarked_context_12_22034_204062 : frontier 9 ⟨204062, by decide⟩
    (prefixCache 12 22034) (prefixPartial 12 22034) = false := by
  decide +kernel

theorem node_context_12_22034_204062 : EJMOriginalGlobalDAGData.nodes 9 ⟨204062, by decide⟩ =
    .split (coordinate 12) (![⟨204006, by decide⟩,⟨204034, by decide⟩,⟨204053, by decide⟩,⟨204061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22034_204062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22034 ⟨204062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22034
    ⟨204062, by decide⟩ (by decide) (![⟨204006, by decide⟩,⟨204034, by decide⟩,⟨204053, by decide⟩,⟨204061, by decide⟩]) unmarked_context_12_22034_204062 node_context_12_22034_204062
  intro a
  fin_cases a
  · exact context_13_88136_204006
  · exact context_13_88137_204034
  · exact context_13_88138_204053
  · exact context_13_88139_204061

theorem selected_cut_06900 : selected 8 ⟨204084, by decide⟩
    (prefixPartial 13 88140) = some ⟨13, 2, 0, 204084, 88140, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_88140_204084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88140 ⟨204084, by decide⟩ :=
  accepted_of_selected 13 88140 ⟨204084, by decide⟩ ⟨13, 2, 0, 204084, 88140, 1965, 16384⟩
    (by decide) selected_cut_06900

theorem selected_cut_06901 : selected 8 ⟨204112, by decide⟩
    (prefixPartial 13 88141) = some ⟨13, 2, 0, 204112, 88141, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_88141_204112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88141 ⟨204112, by decide⟩ :=
  accepted_of_selected 13 88141 ⟨204112, by decide⟩ ⟨13, 2, 0, 204112, 88141, 2273, 16384⟩
    (by decide) selected_cut_06901

theorem selected_cut_06902 : selected 8 ⟨204128, by decide⟩
    (prefixPartial 13 88142) = some ⟨13, 2, 0, 204128, 88142, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_88142_204128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88142 ⟨204128, by decide⟩ :=
  accepted_of_selected 13 88142 ⟨204128, by decide⟩ ⟨13, 2, 0, 204128, 88142, 1573, 16384⟩
    (by decide) selected_cut_06902

theorem selected_cut_06903 : selected 8 ⟨204134, by decide⟩
    (prefixPartial 13 88143) = some ⟨13, 2, 0, 204134, 88143, 853, 16384⟩ := by
  decide +kernel

theorem context_13_88143_204134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88143 ⟨204134, by decide⟩ :=
  accepted_of_selected 13 88143 ⟨204134, by decide⟩ ⟨13, 2, 0, 204134, 88143, 853, 16384⟩
    (by decide) selected_cut_06903

theorem unmarked_context_12_22035_204135 : frontier 9 ⟨204135, by decide⟩
    (prefixCache 12 22035) (prefixPartial 12 22035) = false := by
  decide +kernel

theorem node_context_12_22035_204135 : EJMOriginalGlobalDAGData.nodes 9 ⟨204135, by decide⟩ =
    .split (coordinate 12) (![⟨204084, by decide⟩,⟨204112, by decide⟩,⟨204128, by decide⟩,⟨204134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22035_204135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22035 ⟨204135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22035
    ⟨204135, by decide⟩ (by decide) (![⟨204084, by decide⟩,⟨204112, by decide⟩,⟨204128, by decide⟩,⟨204134, by decide⟩]) unmarked_context_12_22035_204135 node_context_12_22035_204135
  intro a
  fin_cases a
  · exact context_13_88140_204084
  · exact context_13_88141_204112
  · exact context_13_88142_204128
  · exact context_13_88143_204134

theorem unmarked_context_11_5508_204136 : frontier 10 ⟨204136, by decide⟩
    (prefixCache 11 5508) (prefixPartial 11 5508) = false := by
  decide +kernel

theorem node_context_11_5508_204136 : EJMOriginalGlobalDAGData.nodes 10 ⟨204136, by decide⟩ =
    .split (coordinate 11) (![⟨203911, by decide⟩,⟨203983, by decide⟩,⟨204062, by decide⟩,⟨204135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5508_204136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5508 ⟨204136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5508
    ⟨204136, by decide⟩ (by decide) (![⟨203911, by decide⟩,⟨203983, by decide⟩,⟨204062, by decide⟩,⟨204135, by decide⟩]) unmarked_context_11_5508_204136 node_context_11_5508_204136
  intro a
  fin_cases a
  · exact context_12_22032_203911
  · exact context_12_22033_203983
  · exact context_12_22034_204062
  · exact context_12_22035_204135

theorem selected_cut_06904 : selected 8 ⟨204160, by decide⟩
    (prefixPartial 13 88144) = some ⟨13, 2, 0, 204160, 88144, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_88144_204160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88144 ⟨204160, by decide⟩ :=
  accepted_of_selected 13 88144 ⟨204160, by decide⟩ ⟨13, 2, 0, 204160, 88144, 1785, 16384⟩
    (by decide) selected_cut_06904

theorem selected_cut_06905 : selected 8 ⟨204207, by decide⟩
    (prefixPartial 13 88145) = some ⟨13, 2, 0, 204207, 88145, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_88145_204207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88145 ⟨204207, by decide⟩ :=
  accepted_of_selected 13 88145 ⟨204207, by decide⟩ ⟨13, 2, 0, 204207, 88145, 3421, 16384⟩
    (by decide) selected_cut_06905

theorem selected_cut_06906 : selected 8 ⟨204243, by decide⟩
    (prefixPartial 13 88146) = some ⟨13, 2, 0, 204243, 88146, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_88146_204243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88146 ⟨204243, by decide⟩ :=
  accepted_of_selected 13 88146 ⟨204243, by decide⟩ ⟨13, 2, 0, 204243, 88146, 1857, 16384⟩
    (by decide) selected_cut_06906

theorem selected_cut_06907 : selected 8 ⟨204254, by decide⟩
    (prefixPartial 13 88147) = some ⟨13, 2, 0, 204254, 88147, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_88147_204254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88147 ⟨204254, by decide⟩ :=
  accepted_of_selected 13 88147 ⟨204254, by decide⟩ ⟨13, 2, 0, 204254, 88147, 1045, 16384⟩
    (by decide) selected_cut_06907

theorem unmarked_context_12_22036_204255 : frontier 9 ⟨204255, by decide⟩
    (prefixCache 12 22036) (prefixPartial 12 22036) = false := by
  decide +kernel

theorem node_context_12_22036_204255 : EJMOriginalGlobalDAGData.nodes 9 ⟨204255, by decide⟩ =
    .split (coordinate 12) (![⟨204160, by decide⟩,⟨204207, by decide⟩,⟨204243, by decide⟩,⟨204254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22036_204255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22036 ⟨204255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22036
    ⟨204255, by decide⟩ (by decide) (![⟨204160, by decide⟩,⟨204207, by decide⟩,⟨204243, by decide⟩,⟨204254, by decide⟩]) unmarked_context_12_22036_204255 node_context_12_22036_204255
  intro a
  fin_cases a
  · exact context_13_88144_204160
  · exact context_13_88145_204207
  · exact context_13_88146_204243
  · exact context_13_88147_204254

theorem selected_cut_06908 : selected 8 ⟨204276, by decide⟩
    (prefixPartial 13 88148) = some ⟨13, 2, 0, 204276, 88148, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_88148_204276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88148 ⟨204276, by decide⟩ :=
  accepted_of_selected 13 88148 ⟨204276, by decide⟩ ⟨13, 2, 0, 204276, 88148, 1889, 16384⟩
    (by decide) selected_cut_06908

theorem selected_cut_06909 : selected 8 ⟨204325, by decide⟩
    (prefixPartial 13 88149) = some ⟨13, 2, 0, 204325, 88149, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_88149_204325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88149 ⟨204325, by decide⟩ :=
  accepted_of_selected 13 88149 ⟨204325, by decide⟩ ⟨13, 2, 0, 204325, 88149, 2705, 16384⟩
    (by decide) selected_cut_06909

theorem selected_cut_06910 : selected 8 ⟨204349, by decide⟩
    (prefixPartial 13 88150) = some ⟨13, 2, 0, 204349, 88150, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_88150_204349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88150 ⟨204349, by decide⟩ :=
  accepted_of_selected 13 88150 ⟨204349, by decide⟩ ⟨13, 2, 0, 204349, 88150, 1725, 16384⟩
    (by decide) selected_cut_06910

theorem selected_cut_06911 : selected 8 ⟨204356, by decide⟩
    (prefixPartial 13 88151) = some ⟨13, 2, 0, 204356, 88151, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_88151_204356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88151 ⟨204356, by decide⟩ :=
  accepted_of_selected 13 88151 ⟨204356, by decide⟩ ⟨13, 2, 0, 204356, 88151, 1017, 16384⟩
    (by decide) selected_cut_06911

theorem unmarked_context_12_22037_204357 : frontier 9 ⟨204357, by decide⟩
    (prefixCache 12 22037) (prefixPartial 12 22037) = false := by
  decide +kernel

theorem node_context_12_22037_204357 : EJMOriginalGlobalDAGData.nodes 9 ⟨204357, by decide⟩ =
    .split (coordinate 12) (![⟨204276, by decide⟩,⟨204325, by decide⟩,⟨204349, by decide⟩,⟨204356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22037_204357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22037 ⟨204357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22037
    ⟨204357, by decide⟩ (by decide) (![⟨204276, by decide⟩,⟨204325, by decide⟩,⟨204349, by decide⟩,⟨204356, by decide⟩]) unmarked_context_12_22037_204357 node_context_12_22037_204357
  intro a
  fin_cases a
  · exact context_13_88148_204276
  · exact context_13_88149_204325
  · exact context_13_88150_204349
  · exact context_13_88151_204356

theorem selected_cut_06912 : selected 8 ⟨204380, by decide⟩
    (prefixPartial 13 88152) = some ⟨13, 2, 0, 204380, 88152, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_88152_204380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88152 ⟨204380, by decide⟩ :=
  accepted_of_selected 13 88152 ⟨204380, by decide⟩ ⟨13, 2, 0, 204380, 88152, 1997, 16384⟩
    (by decide) selected_cut_06912

theorem selected_cut_06913 : selected 8 ⟨204428, by decide⟩
    (prefixPartial 13 88153) = some ⟨13, 2, 0, 204428, 88153, 3577, 16384⟩ := by
  decide +kernel

theorem context_13_88153_204428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88153 ⟨204428, by decide⟩ :=
  accepted_of_selected 13 88153 ⟨204428, by decide⟩ ⟨13, 2, 0, 204428, 88153, 3577, 16384⟩
    (by decide) selected_cut_06913

theorem selected_cut_06914 : selected 8 ⟨204448, by decide⟩
    (prefixPartial 13 88154) = some ⟨13, 2, 0, 204448, 88154, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_88154_204448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88154 ⟨204448, by decide⟩ :=
  accepted_of_selected 13 88154 ⟨204448, by decide⟩ ⟨13, 2, 0, 204448, 88154, 1641, 16384⟩
    (by decide) selected_cut_06914

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
