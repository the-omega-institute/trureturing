/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover244
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_23523 : selected 10 ⟨595511, by decide⟩
    (prefixPartial 11 19122) = some ⟨11, 2, 0, 595511, 19122, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_19122_595511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19122 ⟨595511, by decide⟩ :=
  accepted_of_selected 11 19122 ⟨595511, by decide⟩ ⟨11, 2, 0, 595511, 19122, 2429, 262144⟩
    (by decide) selected_cut_23523

theorem selected_cut_23524 : selected 10 ⟨595548, by decide⟩
    (prefixPartial 11 19123) = some ⟨11, 2, 0, 595548, 19123, 3385, 262144⟩ := by
  decide +kernel

theorem context_11_19123_595548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19123 ⟨595548, by decide⟩ :=
  accepted_of_selected 11 19123 ⟨595548, by decide⟩ ⟨11, 2, 0, 595548, 19123, 3385, 262144⟩
    (by decide) selected_cut_23524

theorem unmarked_context_10_4780_595549 : frontier 11 ⟨595549, by decide⟩
    (prefixCache 10 4780) (prefixPartial 10 4780) = false := by
  decide +kernel

theorem node_context_10_4780_595549 : EJMOriginalGlobalDAGData.nodes 11 ⟨595549, by decide⟩ =
    .split (coordinate 10) (![⟨595454, by decide⟩,⟨595490, by decide⟩,⟨595511, by decide⟩,⟨595548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4780_595549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4780 ⟨595549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4780
    ⟨595549, by decide⟩ (by decide) (![⟨595454, by decide⟩,⟨595490, by decide⟩,⟨595511, by decide⟩,⟨595548, by decide⟩]) unmarked_context_10_4780_595549 node_context_10_4780_595549
  intro a
  fin_cases a
  · exact context_11_19120_595454
  · exact context_11_19121_595490
  · exact context_11_19122_595511
  · exact context_11_19123_595548

theorem selected_cut_23525 : selected 10 ⟨595582, by decide⟩
    (prefixPartial 11 19124) = some ⟨11, 2, 0, 595582, 19124, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_19124_595582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19124 ⟨595582, by decide⟩ :=
  accepted_of_selected 11 19124 ⟨595582, by decide⟩ ⟨11, 2, 0, 595582, 19124, 2873, 262144⟩
    (by decide) selected_cut_23525

theorem selected_cut_23526 : selected 10 ⟨595611, by decide⟩
    (prefixPartial 11 19125) = some ⟨11, 2, 0, 595611, 19125, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_19125_595611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19125 ⟨595611, by decide⟩ :=
  accepted_of_selected 11 19125 ⟨595611, by decide⟩ ⟨11, 2, 0, 595611, 19125, 2657, 262144⟩
    (by decide) selected_cut_23526

theorem selected_cut_23527 : selected 10 ⟨595649, by decide⟩
    (prefixPartial 11 19126) = some ⟨11, 2, 0, 595649, 19126, 2365, 262144⟩ := by
  decide +kernel

theorem context_11_19126_595649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19126 ⟨595649, by decide⟩ :=
  accepted_of_selected 11 19126 ⟨595649, by decide⟩ ⟨11, 2, 0, 595649, 19126, 2365, 262144⟩
    (by decide) selected_cut_23527

theorem selected_cut_23528 : selected 10 ⟨595680, by decide⟩
    (prefixPartial 11 19127) = some ⟨11, 2, 0, 595680, 19127, 2005, 262144⟩ := by
  decide +kernel

theorem context_11_19127_595680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19127 ⟨595680, by decide⟩ :=
  accepted_of_selected 11 19127 ⟨595680, by decide⟩ ⟨11, 2, 0, 595680, 19127, 2005, 262144⟩
    (by decide) selected_cut_23528

theorem unmarked_context_10_4781_595681 : frontier 11 ⟨595681, by decide⟩
    (prefixCache 10 4781) (prefixPartial 10 4781) = false := by
  decide +kernel

theorem node_context_10_4781_595681 : EJMOriginalGlobalDAGData.nodes 11 ⟨595681, by decide⟩ =
    .split (coordinate 10) (![⟨595582, by decide⟩,⟨595611, by decide⟩,⟨595649, by decide⟩,⟨595680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4781_595681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4781 ⟨595681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4781
    ⟨595681, by decide⟩ (by decide) (![⟨595582, by decide⟩,⟨595611, by decide⟩,⟨595649, by decide⟩,⟨595680, by decide⟩]) unmarked_context_10_4781_595681 node_context_10_4781_595681
  intro a
  fin_cases a
  · exact context_11_19124_595582
  · exact context_11_19125_595611
  · exact context_11_19126_595649
  · exact context_11_19127_595680

theorem selected_cut_23529 : selected 11 ⟨595737, by decide⟩
    (prefixPartial 10 4782) = some ⟨10, 2, 0, 595737, 4782, 4081, 1048576⟩ := by
  decide +kernel

theorem context_10_4782_595737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4782 ⟨595737, by decide⟩ :=
  accepted_of_selected 10 4782 ⟨595737, by decide⟩ ⟨10, 2, 0, 595737, 4782, 4081, 1048576⟩
    (by decide) selected_cut_23529

theorem selected_cut_23530 : selected 11 ⟨595778, by decide⟩
    (prefixPartial 10 4783) = some ⟨10, 2, 0, 595778, 4783, 1641, 1048576⟩ := by
  decide +kernel

theorem context_10_4783_595778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4783 ⟨595778, by decide⟩ :=
  accepted_of_selected 10 4783 ⟨595778, by decide⟩ ⟨10, 2, 0, 595778, 4783, 1641, 1048576⟩
    (by decide) selected_cut_23530

theorem unmarked_context_9_1195_595779 : frontier 12 ⟨595779, by decide⟩
    (prefixCache 9 1195) (prefixPartial 9 1195) = false := by
  decide +kernel

theorem node_context_9_1195_595779 : EJMOriginalGlobalDAGData.nodes 12 ⟨595779, by decide⟩ =
    .split (coordinate 9) (![⟨595549, by decide⟩,⟨595681, by decide⟩,⟨595737, by decide⟩,⟨595778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1195_595779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1195 ⟨595779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1195
    ⟨595779, by decide⟩ (by decide) (![⟨595549, by decide⟩,⟨595681, by decide⟩,⟨595737, by decide⟩,⟨595778, by decide⟩]) unmarked_context_9_1195_595779 node_context_9_1195_595779
  intro a
  fin_cases a
  · exact context_10_4780_595549
  · exact context_10_4781_595681
  · exact context_10_4782_595737
  · exact context_10_4783_595778

theorem unmarked_context_8_298_595780 : frontier 13 ⟨595780, by decide⟩
    (prefixCache 8 298) (prefixPartial 8 298) = false := by
  decide +kernel

theorem node_context_8_298_595780 : EJMOriginalGlobalDAGData.nodes 13 ⟨595780, by decide⟩ =
    .split (coordinate 8) (![⟨591713, by decide⟩,⟨594368, by decide⟩,⟨595415, by decide⟩,⟨595779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_298_595780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 298 ⟨595780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 298
    ⟨595780, by decide⟩ (by decide) (![⟨591713, by decide⟩,⟨594368, by decide⟩,⟨595415, by decide⟩,⟨595779, by decide⟩]) unmarked_context_8_298_595780 node_context_8_298_595780
  intro a
  fin_cases a
  · exact context_9_1192_591713
  · exact context_9_1193_594368
  · exact context_9_1194_595415
  · exact context_9_1195_595779

theorem selected_cut_23531 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 19136) = some ⟨11, 1, 0, 434745, 19136, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19136_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19136 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 19136 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 19136, 1, 262144⟩
    (by decide) selected_cut_23531

theorem selected_cut_23532 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76548) = some ⟨12, 1, 0, 448748, 76548, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76548_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76548 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76548 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76548, 1, 65536⟩
    (by decide) selected_cut_23532

theorem selected_cut_23533 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 76549) = some ⟨12, 1, 0, 34034, 76549, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76549_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76549 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 76549 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 76549, 1, 65536⟩
    (by decide) selected_cut_23533

theorem selected_cut_23534 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 76550) = some ⟨12, 1, 0, 88909, 76550, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76550_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76550 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 76550 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 76550, 1, 65536⟩
    (by decide) selected_cut_23534

theorem selected_cut_23535 : selected 8 ⟨595844, by decide⟩
    (prefixPartial 13 306204) = some ⟨13, 2, 0, 595844, 306204, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_306204_595844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306204 ⟨595844, by decide⟩ :=
  accepted_of_selected 13 306204 ⟨595844, by decide⟩ ⟨13, 2, 0, 595844, 306204, 2357, 16384⟩
    (by decide) selected_cut_23535

theorem selected_cut_23536 : selected 8 ⟨595875, by decide⟩
    (prefixPartial 13 306205) = some ⟨13, 2, 0, 595875, 306205, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_306205_595875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306205 ⟨595875, by decide⟩ :=
  accepted_of_selected 13 306205 ⟨595875, by decide⟩ ⟨13, 2, 0, 595875, 306205, 2893, 16384⟩
    (by decide) selected_cut_23536

theorem selected_cut_23537 : selected 8 ⟨595897, by decide⟩
    (prefixPartial 13 306206) = some ⟨13, 2, 0, 595897, 306206, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_306206_595897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306206 ⟨595897, by decide⟩ :=
  accepted_of_selected 13 306206 ⟨595897, by decide⟩ ⟨13, 2, 0, 595897, 306206, 1949, 16384⟩
    (by decide) selected_cut_23537

theorem selected_cut_23538 : selected 8 ⟨595901, by decide⟩
    (prefixPartial 13 306207) = some ⟨13, 2, 0, 595901, 306207, 817, 16384⟩ := by
  decide +kernel

theorem context_13_306207_595901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306207 ⟨595901, by decide⟩ :=
  accepted_of_selected 13 306207 ⟨595901, by decide⟩ ⟨13, 2, 0, 595901, 306207, 817, 16384⟩
    (by decide) selected_cut_23538

theorem unmarked_context_12_76551_595902 : frontier 9 ⟨595902, by decide⟩
    (prefixCache 12 76551) (prefixPartial 12 76551) = false := by
  decide +kernel

theorem node_context_12_76551_595902 : EJMOriginalGlobalDAGData.nodes 9 ⟨595902, by decide⟩ =
    .split (coordinate 12) (![⟨595844, by decide⟩,⟨595875, by decide⟩,⟨595897, by decide⟩,⟨595901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76551_595902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76551 ⟨595902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76551
    ⟨595902, by decide⟩ (by decide) (![⟨595844, by decide⟩,⟨595875, by decide⟩,⟨595897, by decide⟩,⟨595901, by decide⟩]) unmarked_context_12_76551_595902 node_context_12_76551_595902
  intro a
  fin_cases a
  · exact context_13_306204_595844
  · exact context_13_306205_595875
  · exact context_13_306206_595897
  · exact context_13_306207_595901

theorem unmarked_context_11_19137_595903 : frontier 10 ⟨595903, by decide⟩
    (prefixCache 11 19137) (prefixPartial 11 19137) = false := by
  decide +kernel

theorem node_context_11_19137_595903 : EJMOriginalGlobalDAGData.nodes 10 ⟨595903, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨88909, by decide⟩,⟨595902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19137_595903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19137 ⟨595903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19137
    ⟨595903, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨88909, by decide⟩,⟨595902, by decide⟩]) unmarked_context_11_19137_595903 node_context_11_19137_595903
  intro a
  fin_cases a
  · exact context_12_76548_448748
  · exact context_12_76549_34034
  · exact context_12_76550_88909
  · exact context_12_76551_595902

theorem selected_cut_23539 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76552) = some ⟨12, 1, 0, 448748, 76552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76552_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76552 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76552 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76552, 1, 65536⟩
    (by decide) selected_cut_23539

theorem selected_cut_23540 : selected 8 ⟨595986, by decide⟩
    (prefixPartial 13 306212) = some ⟨13, 2, 0, 595986, 306212, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_306212_595986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306212 ⟨595986, by decide⟩ :=
  accepted_of_selected 13 306212 ⟨595986, by decide⟩ ⟨13, 2, 0, 595986, 306212, 3233, 16384⟩
    (by decide) selected_cut_23540

theorem selected_cut_23541 : selected 8 ⟨596037, by decide⟩
    (prefixPartial 13 306213) = some ⟨13, 2, 0, 596037, 306213, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_306213_596037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306213 ⟨596037, by decide⟩ :=
  accepted_of_selected 13 306213 ⟨596037, by decide⟩ ⟨13, 2, 0, 596037, 306213, 2877, 16384⟩
    (by decide) selected_cut_23541

theorem selected_cut_23542 : selected 8 ⟨596058, by decide⟩
    (prefixPartial 13 306214) = some ⟨13, 2, 0, 596058, 306214, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_306214_596058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306214 ⟨596058, by decide⟩ :=
  accepted_of_selected 13 306214 ⟨596058, by decide⟩ ⟨13, 2, 0, 596058, 306214, 1685, 16384⟩
    (by decide) selected_cut_23542

theorem selected_cut_23543 : selected 8 ⟨596066, by decide⟩
    (prefixPartial 13 306215) = some ⟨13, 2, 0, 596066, 306215, 929, 16384⟩ := by
  decide +kernel

theorem context_13_306215_596066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306215 ⟨596066, by decide⟩ :=
  accepted_of_selected 13 306215 ⟨596066, by decide⟩ ⟨13, 2, 0, 596066, 306215, 929, 16384⟩
    (by decide) selected_cut_23543

theorem unmarked_context_12_76553_596067 : frontier 9 ⟨596067, by decide⟩
    (prefixCache 12 76553) (prefixPartial 12 76553) = false := by
  decide +kernel

theorem node_context_12_76553_596067 : EJMOriginalGlobalDAGData.nodes 9 ⟨596067, by decide⟩ =
    .split (coordinate 12) (![⟨595986, by decide⟩,⟨596037, by decide⟩,⟨596058, by decide⟩,⟨596066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76553_596067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76553 ⟨596067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76553
    ⟨596067, by decide⟩ (by decide) (![⟨595986, by decide⟩,⟨596037, by decide⟩,⟨596058, by decide⟩,⟨596066, by decide⟩]) unmarked_context_12_76553_596067 node_context_12_76553_596067
  intro a
  fin_cases a
  · exact context_13_306212_595986
  · exact context_13_306213_596037
  · exact context_13_306214_596058
  · exact context_13_306215_596066

theorem selected_cut_23544 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 76554) = some ⟨12, 1, 0, 524302, 76554, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76554_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76554 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 76554 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 76554, 1, 65536⟩
    (by decide) selected_cut_23544

theorem selected_cut_23545 : selected 9 ⟨508415, by decide⟩
    (prefixPartial 12 76555) = some ⟨12, 1, 0, 508415, 76555, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76555_508415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76555 ⟨508415, by decide⟩ :=
  accepted_of_selected 12 76555 ⟨508415, by decide⟩ ⟨12, 1, 0, 508415, 76555, 1, 65536⟩
    (by decide) selected_cut_23545

theorem unmarked_context_11_19138_596068 : frontier 10 ⟨596068, by decide⟩
    (prefixCache 11 19138) (prefixPartial 11 19138) = false := by
  decide +kernel

theorem node_context_11_19138_596068 : EJMOriginalGlobalDAGData.nodes 10 ⟨596068, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨596067, by decide⟩,⟨524302, by decide⟩,⟨508415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19138_596068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19138 ⟨596068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19138
    ⟨596068, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨596067, by decide⟩,⟨524302, by decide⟩,⟨508415, by decide⟩]) unmarked_context_11_19138_596068 node_context_11_19138_596068
  intro a
  fin_cases a
  · exact context_12_76552_448748
  · exact context_12_76553_596067
  · exact context_12_76554_524302
  · exact context_12_76555_508415

theorem selected_cut_23546 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76556) = some ⟨12, 1, 0, 448748, 76556, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76556_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76556 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76556 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76556, 1, 65536⟩
    (by decide) selected_cut_23546

theorem selected_cut_23547 : selected 8 ⟨596142, by decide⟩
    (prefixPartial 13 306228) = some ⟨13, 2, 0, 596142, 306228, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_306228_596142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306228 ⟨596142, by decide⟩ :=
  accepted_of_selected 13 306228 ⟨596142, by decide⟩ ⟨13, 2, 0, 596142, 306228, 3049, 16384⟩
    (by decide) selected_cut_23547

theorem selected_cut_23548 : selected 8 ⟨596184, by decide⟩
    (prefixPartial 13 306229) = some ⟨13, 2, 0, 596184, 306229, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_306229_596184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306229 ⟨596184, by decide⟩ :=
  accepted_of_selected 13 306229 ⟨596184, by decide⟩ ⟨13, 2, 0, 596184, 306229, 3005, 16384⟩
    (by decide) selected_cut_23548

theorem selected_cut_23549 : selected 8 ⟨596210, by decide⟩
    (prefixPartial 13 306230) = some ⟨13, 2, 0, 596210, 306230, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_306230_596210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306230 ⟨596210, by decide⟩ :=
  accepted_of_selected 13 306230 ⟨596210, by decide⟩ ⟨13, 2, 0, 596210, 306230, 2069, 16384⟩
    (by decide) selected_cut_23549

theorem selected_cut_23550 : selected 8 ⟨596218, by decide⟩
    (prefixPartial 13 306231) = some ⟨13, 2, 0, 596218, 306231, 905, 16384⟩ := by
  decide +kernel

theorem context_13_306231_596218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306231 ⟨596218, by decide⟩ :=
  accepted_of_selected 13 306231 ⟨596218, by decide⟩ ⟨13, 2, 0, 596218, 306231, 905, 16384⟩
    (by decide) selected_cut_23550

theorem unmarked_context_12_76557_596219 : frontier 9 ⟨596219, by decide⟩
    (prefixCache 12 76557) (prefixPartial 12 76557) = false := by
  decide +kernel

theorem node_context_12_76557_596219 : EJMOriginalGlobalDAGData.nodes 9 ⟨596219, by decide⟩ =
    .split (coordinate 12) (![⟨596142, by decide⟩,⟨596184, by decide⟩,⟨596210, by decide⟩,⟨596218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76557_596219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76557 ⟨596219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76557
    ⟨596219, by decide⟩ (by decide) (![⟨596142, by decide⟩,⟨596184, by decide⟩,⟨596210, by decide⟩,⟨596218, by decide⟩]) unmarked_context_12_76557_596219 node_context_12_76557_596219
  intro a
  fin_cases a
  · exact context_13_306228_596142
  · exact context_13_306229_596184
  · exact context_13_306230_596210
  · exact context_13_306231_596218

theorem selected_cut_23551 : selected 9 ⟨573823, by decide⟩
    (prefixPartial 12 76558) = some ⟨12, 1, 0, 573823, 76558, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76558_573823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76558 ⟨573823, by decide⟩ :=
  accepted_of_selected 12 76558 ⟨573823, by decide⟩ ⟨12, 1, 0, 573823, 76558, 1, 65536⟩
    (by decide) selected_cut_23551

theorem selected_cut_23552 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 76559) = some ⟨12, 1, 0, 518278, 76559, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76559_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76559 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 76559 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 76559, 1, 65536⟩
    (by decide) selected_cut_23552

theorem unmarked_context_11_19139_596220 : frontier 10 ⟨596220, by decide⟩
    (prefixCache 11 19139) (prefixPartial 11 19139) = false := by
  decide +kernel

theorem node_context_11_19139_596220 : EJMOriginalGlobalDAGData.nodes 10 ⟨596220, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨596219, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19139_596220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19139 ⟨596220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19139
    ⟨596220, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨596219, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_19139_596220 node_context_11_19139_596220
  intro a
  fin_cases a
  · exact context_12_76556_448748
  · exact context_12_76557_596219
  · exact context_12_76558_573823
  · exact context_12_76559_518278

theorem unmarked_context_10_4784_596221 : frontier 11 ⟨596221, by decide⟩
    (prefixCache 10 4784) (prefixPartial 10 4784) = false := by
  decide +kernel

theorem node_context_10_4784_596221 : EJMOriginalGlobalDAGData.nodes 11 ⟨596221, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨595903, by decide⟩,⟨596068, by decide⟩,⟨596220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4784_596221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4784 ⟨596221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4784
    ⟨596221, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨595903, by decide⟩,⟨596068, by decide⟩,⟨596220, by decide⟩]) unmarked_context_10_4784_596221 node_context_10_4784_596221
  intro a
  fin_cases a
  · exact context_11_19136_434745
  · exact context_11_19137_595903
  · exact context_11_19138_596068
  · exact context_11_19139_596220

theorem selected_cut_23553 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76560) = some ⟨12, 1, 0, 435160, 76560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76560_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76560 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76560 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76560, 1, 65536⟩
    (by decide) selected_cut_23553

theorem selected_cut_23554 : selected 8 ⟨596268, by decide⟩
    (prefixPartial 13 306244) = some ⟨13, 2, 0, 596268, 306244, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_306244_596268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306244 ⟨596268, by decide⟩ :=
  accepted_of_selected 13 306244 ⟨596268, by decide⟩ ⟨13, 2, 0, 596268, 306244, 2405, 16384⟩
    (by decide) selected_cut_23554

theorem selected_cut_23555 : selected 8 ⟨596297, by decide⟩
    (prefixPartial 13 306245) = some ⟨13, 2, 0, 596297, 306245, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_306245_596297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306245 ⟨596297, by decide⟩ :=
  accepted_of_selected 13 306245 ⟨596297, by decide⟩ ⟨13, 2, 0, 596297, 306245, 2265, 16384⟩
    (by decide) selected_cut_23555

theorem selected_cut_23556 : selected 8 ⟨596326, by decide⟩
    (prefixPartial 13 306246) = some ⟨13, 2, 0, 596326, 306246, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_306246_596326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306246 ⟨596326, by decide⟩ :=
  accepted_of_selected 13 306246 ⟨596326, by decide⟩ ⟨13, 2, 0, 596326, 306246, 2009, 16384⟩
    (by decide) selected_cut_23556

theorem selected_cut_23557 : selected 8 ⟨596331, by decide⟩
    (prefixPartial 13 306247) = some ⟨13, 2, 0, 596331, 306247, 717, 16384⟩ := by
  decide +kernel

theorem context_13_306247_596331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306247 ⟨596331, by decide⟩ :=
  accepted_of_selected 13 306247 ⟨596331, by decide⟩ ⟨13, 2, 0, 596331, 306247, 717, 16384⟩
    (by decide) selected_cut_23557

theorem unmarked_context_12_76561_596332 : frontier 9 ⟨596332, by decide⟩
    (prefixCache 12 76561) (prefixPartial 12 76561) = false := by
  decide +kernel

theorem node_context_12_76561_596332 : EJMOriginalGlobalDAGData.nodes 9 ⟨596332, by decide⟩ =
    .split (coordinate 12) (![⟨596268, by decide⟩,⟨596297, by decide⟩,⟨596326, by decide⟩,⟨596331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76561_596332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76561 ⟨596332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76561
    ⟨596332, by decide⟩ (by decide) (![⟨596268, by decide⟩,⟨596297, by decide⟩,⟨596326, by decide⟩,⟨596331, by decide⟩]) unmarked_context_12_76561_596332 node_context_12_76561_596332
  intro a
  fin_cases a
  · exact context_13_306244_596268
  · exact context_13_306245_596297
  · exact context_13_306246_596326
  · exact context_13_306247_596331

theorem selected_cut_23558 : selected 8 ⟨596366, by decide⟩
    (prefixPartial 13 306248) = some ⟨13, 2, 0, 596366, 306248, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_306248_596366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306248 ⟨596366, by decide⟩ :=
  accepted_of_selected 13 306248 ⟨596366, by decide⟩ ⟨13, 2, 0, 596366, 306248, 2001, 16384⟩
    (by decide) selected_cut_23558

theorem selected_cut_23559 : selected 8 ⟨596398, by decide⟩
    (prefixPartial 13 306249) = some ⟨13, 2, 0, 596398, 306249, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_306249_596398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306249 ⟨596398, by decide⟩ :=
  accepted_of_selected 13 306249 ⟨596398, by decide⟩ ⟨13, 2, 0, 596398, 306249, 2461, 16384⟩
    (by decide) selected_cut_23559

theorem selected_cut_23560 : selected 8 ⟨596423, by decide⟩
    (prefixPartial 13 306250) = some ⟨13, 2, 0, 596423, 306250, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_306250_596423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306250 ⟨596423, by decide⟩ :=
  accepted_of_selected 13 306250 ⟨596423, by decide⟩ ⟨13, 2, 0, 596423, 306250, 2001, 16384⟩
    (by decide) selected_cut_23560

theorem selected_cut_23561 : selected 8 ⟨596430, by decide⟩
    (prefixPartial 13 306251) = some ⟨13, 2, 0, 596430, 306251, 745, 16384⟩ := by
  decide +kernel

theorem context_13_306251_596430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306251 ⟨596430, by decide⟩ :=
  accepted_of_selected 13 306251 ⟨596430, by decide⟩ ⟨13, 2, 0, 596430, 306251, 745, 16384⟩
    (by decide) selected_cut_23561

theorem unmarked_context_12_76562_596431 : frontier 9 ⟨596431, by decide⟩
    (prefixCache 12 76562) (prefixPartial 12 76562) = false := by
  decide +kernel

theorem node_context_12_76562_596431 : EJMOriginalGlobalDAGData.nodes 9 ⟨596431, by decide⟩ =
    .split (coordinate 12) (![⟨596366, by decide⟩,⟨596398, by decide⟩,⟨596423, by decide⟩,⟨596430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76562_596431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76562 ⟨596431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76562
    ⟨596431, by decide⟩ (by decide) (![⟨596366, by decide⟩,⟨596398, by decide⟩,⟨596423, by decide⟩,⟨596430, by decide⟩]) unmarked_context_12_76562_596431 node_context_12_76562_596431
  intro a
  fin_cases a
  · exact context_13_306248_596366
  · exact context_13_306249_596398
  · exact context_13_306250_596423
  · exact context_13_306251_596430

theorem selected_cut_23562 : selected 8 ⟨596465, by decide⟩
    (prefixPartial 13 306252) = some ⟨13, 2, 0, 596465, 306252, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_306252_596465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306252 ⟨596465, by decide⟩ :=
  accepted_of_selected 13 306252 ⟨596465, by decide⟩ ⟨13, 2, 0, 596465, 306252, 1749, 16384⟩
    (by decide) selected_cut_23562

theorem selected_cut_23563 : selected 8 ⟨596494, by decide⟩
    (prefixPartial 13 306253) = some ⟨13, 2, 0, 596494, 306253, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_306253_596494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306253 ⟨596494, by decide⟩ :=
  accepted_of_selected 13 306253 ⟨596494, by decide⟩ ⟨13, 2, 0, 596494, 306253, 2357, 16384⟩
    (by decide) selected_cut_23563

theorem selected_cut_23564 : selected 8 ⟨596515, by decide⟩
    (prefixPartial 13 306254) = some ⟨13, 2, 0, 596515, 306254, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_306254_596515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306254 ⟨596515, by decide⟩ :=
  accepted_of_selected 13 306254 ⟨596515, by decide⟩ ⟨13, 2, 0, 596515, 306254, 1745, 16384⟩
    (by decide) selected_cut_23564

theorem selected_cut_23565 : selected 8 ⟨596518, by decide⟩
    (prefixPartial 13 306255) = some ⟨13, 2, 0, 596518, 306255, 577, 16384⟩ := by
  decide +kernel

theorem context_13_306255_596518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306255 ⟨596518, by decide⟩ :=
  accepted_of_selected 13 306255 ⟨596518, by decide⟩ ⟨13, 2, 0, 596518, 306255, 577, 16384⟩
    (by decide) selected_cut_23565

theorem unmarked_context_12_76563_596519 : frontier 9 ⟨596519, by decide⟩
    (prefixCache 12 76563) (prefixPartial 12 76563) = false := by
  decide +kernel

theorem node_context_12_76563_596519 : EJMOriginalGlobalDAGData.nodes 9 ⟨596519, by decide⟩ =
    .split (coordinate 12) (![⟨596465, by decide⟩,⟨596494, by decide⟩,⟨596515, by decide⟩,⟨596518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76563_596519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76563 ⟨596519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76563
    ⟨596519, by decide⟩ (by decide) (![⟨596465, by decide⟩,⟨596494, by decide⟩,⟨596515, by decide⟩,⟨596518, by decide⟩]) unmarked_context_12_76563_596519 node_context_12_76563_596519
  intro a
  fin_cases a
  · exact context_13_306252_596465
  · exact context_13_306253_596494
  · exact context_13_306254_596515
  · exact context_13_306255_596518

theorem unmarked_context_11_19140_596520 : frontier 10 ⟨596520, by decide⟩
    (prefixCache 11 19140) (prefixPartial 11 19140) = false := by
  decide +kernel

theorem node_context_11_19140_596520 : EJMOriginalGlobalDAGData.nodes 10 ⟨596520, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨596332, by decide⟩,⟨596431, by decide⟩,⟨596519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19140_596520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19140 ⟨596520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19140
    ⟨596520, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨596332, by decide⟩,⟨596431, by decide⟩,⟨596519, by decide⟩]) unmarked_context_11_19140_596520 node_context_11_19140_596520
  intro a
  fin_cases a
  · exact context_12_76560_435160
  · exact context_12_76561_596332
  · exact context_12_76562_596431
  · exact context_12_76563_596519

theorem selected_cut_23566 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76564) = some ⟨12, 1, 0, 435160, 76564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76564_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76564 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76564 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76564, 1, 65536⟩
    (by decide) selected_cut_23566

theorem selected_cut_23567 : selected 8 ⟨596565, by decide⟩
    (prefixPartial 13 306260) = some ⟨13, 2, 0, 596565, 306260, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_306260_596565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306260 ⟨596565, by decide⟩ :=
  accepted_of_selected 13 306260 ⟨596565, by decide⟩ ⟨13, 2, 0, 596565, 306260, 2209, 16384⟩
    (by decide) selected_cut_23567

theorem selected_cut_23568 : selected 8 ⟨596591, by decide⟩
    (prefixPartial 13 306261) = some ⟨13, 2, 0, 596591, 306261, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_306261_596591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306261 ⟨596591, by decide⟩ :=
  accepted_of_selected 13 306261 ⟨596591, by decide⟩ ⟨13, 2, 0, 596591, 306261, 2077, 16384⟩
    (by decide) selected_cut_23568

theorem selected_cut_23569 : selected 8 ⟨596611, by decide⟩
    (prefixPartial 13 306262) = some ⟨13, 2, 0, 596611, 306262, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_306262_596611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306262 ⟨596611, by decide⟩ :=
  accepted_of_selected 13 306262 ⟨596611, by decide⟩ ⟨13, 2, 0, 596611, 306262, 1921, 16384⟩
    (by decide) selected_cut_23569

theorem selected_cut_23570 : selected 8 ⟨596618, by decide⟩
    (prefixPartial 13 306263) = some ⟨13, 2, 0, 596618, 306263, 841, 16384⟩ := by
  decide +kernel

theorem context_13_306263_596618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306263 ⟨596618, by decide⟩ :=
  accepted_of_selected 13 306263 ⟨596618, by decide⟩ ⟨13, 2, 0, 596618, 306263, 841, 16384⟩
    (by decide) selected_cut_23570

theorem unmarked_context_12_76565_596619 : frontier 9 ⟨596619, by decide⟩
    (prefixCache 12 76565) (prefixPartial 12 76565) = false := by
  decide +kernel

theorem node_context_12_76565_596619 : EJMOriginalGlobalDAGData.nodes 9 ⟨596619, by decide⟩ =
    .split (coordinate 12) (![⟨596565, by decide⟩,⟨596591, by decide⟩,⟨596611, by decide⟩,⟨596618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76565_596619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76565 ⟨596619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76565
    ⟨596619, by decide⟩ (by decide) (![⟨596565, by decide⟩,⟨596591, by decide⟩,⟨596611, by decide⟩,⟨596618, by decide⟩]) unmarked_context_12_76565_596619 node_context_12_76565_596619
  intro a
  fin_cases a
  · exact context_13_306260_596565
  · exact context_13_306261_596591
  · exact context_13_306262_596611
  · exact context_13_306263_596618

theorem selected_cut_23571 : selected 8 ⟨596654, by decide⟩
    (prefixPartial 13 306264) = some ⟨13, 2, 0, 596654, 306264, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_306264_596654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306264 ⟨596654, by decide⟩ :=
  accepted_of_selected 13 306264 ⟨596654, by decide⟩ ⟨13, 2, 0, 596654, 306264, 2029, 16384⟩
    (by decide) selected_cut_23571

theorem selected_cut_23572 : selected 8 ⟨596684, by decide⟩
    (prefixPartial 13 306265) = some ⟨13, 2, 0, 596684, 306265, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_306265_596684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306265 ⟨596684, by decide⟩ :=
  accepted_of_selected 13 306265 ⟨596684, by decide⟩ ⟨13, 2, 0, 596684, 306265, 2493, 16384⟩
    (by decide) selected_cut_23572

theorem selected_cut_23573 : selected 8 ⟨596705, by decide⟩
    (prefixPartial 13 306266) = some ⟨13, 2, 0, 596705, 306266, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_306266_596705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306266 ⟨596705, by decide⟩ :=
  accepted_of_selected 13 306266 ⟨596705, by decide⟩ ⟨13, 2, 0, 596705, 306266, 1925, 16384⟩
    (by decide) selected_cut_23573

theorem selected_cut_23574 : selected 8 ⟨596714, by decide⟩
    (prefixPartial 13 306267) = some ⟨13, 2, 0, 596714, 306267, 929, 16384⟩ := by
  decide +kernel

theorem context_13_306267_596714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306267 ⟨596714, by decide⟩ :=
  accepted_of_selected 13 306267 ⟨596714, by decide⟩ ⟨13, 2, 0, 596714, 306267, 929, 16384⟩
    (by decide) selected_cut_23574

theorem unmarked_context_12_76566_596715 : frontier 9 ⟨596715, by decide⟩
    (prefixCache 12 76566) (prefixPartial 12 76566) = false := by
  decide +kernel

theorem node_context_12_76566_596715 : EJMOriginalGlobalDAGData.nodes 9 ⟨596715, by decide⟩ =
    .split (coordinate 12) (![⟨596654, by decide⟩,⟨596684, by decide⟩,⟨596705, by decide⟩,⟨596714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76566_596715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76566 ⟨596715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76566
    ⟨596715, by decide⟩ (by decide) (![⟨596654, by decide⟩,⟨596684, by decide⟩,⟨596705, by decide⟩,⟨596714, by decide⟩]) unmarked_context_12_76566_596715 node_context_12_76566_596715
  intro a
  fin_cases a
  · exact context_13_306264_596654
  · exact context_13_306265_596684
  · exact context_13_306266_596705
  · exact context_13_306267_596714

theorem selected_cut_23575 : selected 8 ⟨596755, by decide⟩
    (prefixPartial 13 306268) = some ⟨13, 2, 0, 596755, 306268, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_306268_596755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306268 ⟨596755, by decide⟩ :=
  accepted_of_selected 13 306268 ⟨596755, by decide⟩ ⟨13, 2, 0, 596755, 306268, 1745, 16384⟩
    (by decide) selected_cut_23575

theorem selected_cut_23576 : selected 8 ⟨596780, by decide⟩
    (prefixPartial 13 306269) = some ⟨13, 2, 0, 596780, 306269, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_306269_596780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306269 ⟨596780, by decide⟩ :=
  accepted_of_selected 13 306269 ⟨596780, by decide⟩ ⟨13, 2, 0, 596780, 306269, 2305, 16384⟩
    (by decide) selected_cut_23576

theorem selected_cut_23577 : selected 8 ⟨596797, by decide⟩
    (prefixPartial 13 306270) = some ⟨13, 2, 0, 596797, 306270, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_306270_596797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306270 ⟨596797, by decide⟩ :=
  accepted_of_selected 13 306270 ⟨596797, by decide⟩ ⟨13, 2, 0, 596797, 306270, 1805, 16384⟩
    (by decide) selected_cut_23577

theorem selected_cut_23578 : selected 8 ⟨596801, by decide⟩
    (prefixPartial 13 306271) = some ⟨13, 2, 0, 596801, 306271, 669, 16384⟩ := by
  decide +kernel

theorem context_13_306271_596801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306271 ⟨596801, by decide⟩ :=
  accepted_of_selected 13 306271 ⟨596801, by decide⟩ ⟨13, 2, 0, 596801, 306271, 669, 16384⟩
    (by decide) selected_cut_23578

theorem unmarked_context_12_76567_596802 : frontier 9 ⟨596802, by decide⟩
    (prefixCache 12 76567) (prefixPartial 12 76567) = false := by
  decide +kernel

theorem node_context_12_76567_596802 : EJMOriginalGlobalDAGData.nodes 9 ⟨596802, by decide⟩ =
    .split (coordinate 12) (![⟨596755, by decide⟩,⟨596780, by decide⟩,⟨596797, by decide⟩,⟨596801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76567_596802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76567 ⟨596802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76567
    ⟨596802, by decide⟩ (by decide) (![⟨596755, by decide⟩,⟨596780, by decide⟩,⟨596797, by decide⟩,⟨596801, by decide⟩]) unmarked_context_12_76567_596802 node_context_12_76567_596802
  intro a
  fin_cases a
  · exact context_13_306268_596755
  · exact context_13_306269_596780
  · exact context_13_306270_596797
  · exact context_13_306271_596801

theorem unmarked_context_11_19141_596803 : frontier 10 ⟨596803, by decide⟩
    (prefixCache 11 19141) (prefixPartial 11 19141) = false := by
  decide +kernel

theorem node_context_11_19141_596803 : EJMOriginalGlobalDAGData.nodes 10 ⟨596803, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨596619, by decide⟩,⟨596715, by decide⟩,⟨596802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19141_596803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19141 ⟨596803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19141
    ⟨596803, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨596619, by decide⟩,⟨596715, by decide⟩,⟨596802, by decide⟩]) unmarked_context_11_19141_596803 node_context_11_19141_596803
  intro a
  fin_cases a
  · exact context_12_76564_435160
  · exact context_12_76565_596619
  · exact context_12_76566_596715
  · exact context_12_76567_596802

theorem selected_cut_23579 : selected 8 ⟨596853, by decide⟩
    (prefixPartial 13 306272) = some ⟨13, 2, 0, 596853, 306272, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_306272_596853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306272 ⟨596853, by decide⟩ :=
  accepted_of_selected 13 306272 ⟨596853, by decide⟩ ⟨13, 2, 0, 596853, 306272, 1993, 16384⟩
    (by decide) selected_cut_23579

theorem selected_cut_23580 : selected 8 ⟨596893, by decide⟩
    (prefixPartial 13 306273) = some ⟨13, 2, 0, 596893, 306273, 3053, 16384⟩ := by
  decide +kernel

theorem context_13_306273_596893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306273 ⟨596893, by decide⟩ :=
  accepted_of_selected 13 306273 ⟨596893, by decide⟩ ⟨13, 2, 0, 596893, 306273, 3053, 16384⟩
    (by decide) selected_cut_23580

theorem selected_cut_23581 : selected 8 ⟨596915, by decide⟩
    (prefixPartial 13 306274) = some ⟨13, 2, 0, 596915, 306274, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_306274_596915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306274 ⟨596915, by decide⟩ :=
  accepted_of_selected 13 306274 ⟨596915, by decide⟩ ⟨13, 2, 0, 596915, 306274, 2065, 16384⟩
    (by decide) selected_cut_23581

theorem selected_cut_23582 : selected 8 ⟨596931, by decide⟩
    (prefixPartial 13 306275) = some ⟨13, 2, 0, 596931, 306275, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_306275_596931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306275 ⟨596931, by decide⟩ :=
  accepted_of_selected 13 306275 ⟨596931, by decide⟩ ⟨13, 2, 0, 596931, 306275, 1085, 16384⟩
    (by decide) selected_cut_23582

theorem unmarked_context_12_76568_596932 : frontier 9 ⟨596932, by decide⟩
    (prefixCache 12 76568) (prefixPartial 12 76568) = false := by
  decide +kernel

theorem node_context_12_76568_596932 : EJMOriginalGlobalDAGData.nodes 9 ⟨596932, by decide⟩ =
    .split (coordinate 12) (![⟨596853, by decide⟩,⟨596893, by decide⟩,⟨596915, by decide⟩,⟨596931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76568_596932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76568 ⟨596932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76568
    ⟨596932, by decide⟩ (by decide) (![⟨596853, by decide⟩,⟨596893, by decide⟩,⟨596915, by decide⟩,⟨596931, by decide⟩]) unmarked_context_12_76568_596932 node_context_12_76568_596932
  intro a
  fin_cases a
  · exact context_13_306272_596853
  · exact context_13_306273_596893
  · exact context_13_306274_596915
  · exact context_13_306275_596931

theorem selected_cut_23583 : selected 8 ⟨596965, by decide⟩
    (prefixPartial 13 306276) = some ⟨13, 2, 0, 596965, 306276, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_306276_596965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306276 ⟨596965, by decide⟩ :=
  accepted_of_selected 13 306276 ⟨596965, by decide⟩ ⟨13, 2, 0, 596965, 306276, 1769, 16384⟩
    (by decide) selected_cut_23583

theorem selected_cut_23584 : selected 8 ⟨596996, by decide⟩
    (prefixPartial 13 306277) = some ⟨13, 2, 0, 596996, 306277, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_306277_596996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306277 ⟨596996, by decide⟩ :=
  accepted_of_selected 13 306277 ⟨596996, by decide⟩ ⟨13, 2, 0, 596996, 306277, 1949, 16384⟩
    (by decide) selected_cut_23584

theorem selected_cut_23585 : selected 8 ⟨597015, by decide⟩
    (prefixPartial 13 306278) = some ⟨13, 2, 0, 597015, 306278, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_306278_597015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306278 ⟨597015, by decide⟩ :=
  accepted_of_selected 13 306278 ⟨597015, by decide⟩ ⟨13, 2, 0, 597015, 306278, 1689, 16384⟩
    (by decide) selected_cut_23585

theorem selected_cut_23586 : selected 8 ⟨597023, by decide⟩
    (prefixPartial 13 306279) = some ⟨13, 2, 0, 597023, 306279, 901, 16384⟩ := by
  decide +kernel

theorem context_13_306279_597023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306279 ⟨597023, by decide⟩ :=
  accepted_of_selected 13 306279 ⟨597023, by decide⟩ ⟨13, 2, 0, 597023, 306279, 901, 16384⟩
    (by decide) selected_cut_23586

theorem unmarked_context_12_76569_597024 : frontier 9 ⟨597024, by decide⟩
    (prefixCache 12 76569) (prefixPartial 12 76569) = false := by
  decide +kernel

theorem node_context_12_76569_597024 : EJMOriginalGlobalDAGData.nodes 9 ⟨597024, by decide⟩ =
    .split (coordinate 12) (![⟨596965, by decide⟩,⟨596996, by decide⟩,⟨597015, by decide⟩,⟨597023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76569_597024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76569 ⟨597024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76569
    ⟨597024, by decide⟩ (by decide) (![⟨596965, by decide⟩,⟨596996, by decide⟩,⟨597015, by decide⟩,⟨597023, by decide⟩]) unmarked_context_12_76569_597024 node_context_12_76569_597024
  intro a
  fin_cases a
  · exact context_13_306276_596965
  · exact context_13_306277_596996
  · exact context_13_306278_597015
  · exact context_13_306279_597023

theorem selected_cut_23587 : selected 8 ⟨597049, by decide⟩
    (prefixPartial 13 306280) = some ⟨13, 2, 0, 597049, 306280, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_306280_597049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306280 ⟨597049, by decide⟩ :=
  accepted_of_selected 13 306280 ⟨597049, by decide⟩ ⟨13, 2, 0, 597049, 306280, 1389, 16384⟩
    (by decide) selected_cut_23587

theorem selected_cut_23588 : selected 8 ⟨597081, by decide⟩
    (prefixPartial 13 306281) = some ⟨13, 2, 0, 597081, 306281, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_306281_597081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306281 ⟨597081, by decide⟩ :=
  accepted_of_selected 13 306281 ⟨597081, by decide⟩ ⟨13, 2, 0, 597081, 306281, 2293, 16384⟩
    (by decide) selected_cut_23588

theorem selected_cut_23589 : selected 8 ⟨597102, by decide⟩
    (prefixPartial 13 306282) = some ⟨13, 2, 0, 597102, 306282, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_306282_597102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306282 ⟨597102, by decide⟩ :=
  accepted_of_selected 13 306282 ⟨597102, by decide⟩ ⟨13, 2, 0, 597102, 306282, 1609, 16384⟩
    (by decide) selected_cut_23589

theorem selected_cut_23590 : selected 8 ⟨597111, by decide⟩
    (prefixPartial 13 306283) = some ⟨13, 2, 0, 597111, 306283, 833, 16384⟩ := by
  decide +kernel

theorem context_13_306283_597111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306283 ⟨597111, by decide⟩ :=
  accepted_of_selected 13 306283 ⟨597111, by decide⟩ ⟨13, 2, 0, 597111, 306283, 833, 16384⟩
    (by decide) selected_cut_23590

theorem unmarked_context_12_76570_597112 : frontier 9 ⟨597112, by decide⟩
    (prefixCache 12 76570) (prefixPartial 12 76570) = false := by
  decide +kernel

theorem node_context_12_76570_597112 : EJMOriginalGlobalDAGData.nodes 9 ⟨597112, by decide⟩ =
    .split (coordinate 12) (![⟨597049, by decide⟩,⟨597081, by decide⟩,⟨597102, by decide⟩,⟨597111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76570_597112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76570 ⟨597112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76570
    ⟨597112, by decide⟩ (by decide) (![⟨597049, by decide⟩,⟨597081, by decide⟩,⟨597102, by decide⟩,⟨597111, by decide⟩]) unmarked_context_12_76570_597112 node_context_12_76570_597112
  intro a
  fin_cases a
  · exact context_13_306280_597049
  · exact context_13_306281_597081
  · exact context_13_306282_597102
  · exact context_13_306283_597111

theorem selected_cut_23591 : selected 8 ⟨597137, by decide⟩
    (prefixPartial 13 306284) = some ⟨13, 2, 0, 597137, 306284, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_306284_597137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306284 ⟨597137, by decide⟩ :=
  accepted_of_selected 13 306284 ⟨597137, by decide⟩ ⟨13, 2, 0, 597137, 306284, 1261, 16384⟩
    (by decide) selected_cut_23591

theorem selected_cut_23592 : selected 8 ⟨597167, by decide⟩
    (prefixPartial 13 306285) = some ⟨13, 2, 0, 597167, 306285, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_306285_597167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306285 ⟨597167, by decide⟩ :=
  accepted_of_selected 13 306285 ⟨597167, by decide⟩ ⟨13, 2, 0, 597167, 306285, 2297, 16384⟩
    (by decide) selected_cut_23592

theorem selected_cut_23593 : selected 8 ⟨597185, by decide⟩
    (prefixPartial 13 306286) = some ⟨13, 2, 0, 597185, 306286, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_306286_597185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306286 ⟨597185, by decide⟩ :=
  accepted_of_selected 13 306286 ⟨597185, by decide⟩ ⟨13, 2, 0, 597185, 306286, 1449, 16384⟩
    (by decide) selected_cut_23593

theorem selected_cut_23594 : selected 8 ⟨597191, by decide⟩
    (prefixPartial 13 306287) = some ⟨13, 2, 0, 597191, 306287, 641, 16384⟩ := by
  decide +kernel

theorem context_13_306287_597191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306287 ⟨597191, by decide⟩ :=
  accepted_of_selected 13 306287 ⟨597191, by decide⟩ ⟨13, 2, 0, 597191, 306287, 641, 16384⟩
    (by decide) selected_cut_23594

theorem unmarked_context_12_76571_597192 : frontier 9 ⟨597192, by decide⟩
    (prefixCache 12 76571) (prefixPartial 12 76571) = false := by
  decide +kernel

theorem node_context_12_76571_597192 : EJMOriginalGlobalDAGData.nodes 9 ⟨597192, by decide⟩ =
    .split (coordinate 12) (![⟨597137, by decide⟩,⟨597167, by decide⟩,⟨597185, by decide⟩,⟨597191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76571_597192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76571 ⟨597192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76571
    ⟨597192, by decide⟩ (by decide) (![⟨597137, by decide⟩,⟨597167, by decide⟩,⟨597185, by decide⟩,⟨597191, by decide⟩]) unmarked_context_12_76571_597192 node_context_12_76571_597192
  intro a
  fin_cases a
  · exact context_13_306284_597137
  · exact context_13_306285_597167
  · exact context_13_306286_597185
  · exact context_13_306287_597191

theorem unmarked_context_11_19142_597193 : frontier 10 ⟨597193, by decide⟩
    (prefixCache 11 19142) (prefixPartial 11 19142) = false := by
  decide +kernel

theorem node_context_11_19142_597193 : EJMOriginalGlobalDAGData.nodes 10 ⟨597193, by decide⟩ =
    .split (coordinate 11) (![⟨596932, by decide⟩,⟨597024, by decide⟩,⟨597112, by decide⟩,⟨597192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19142_597193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19142 ⟨597193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19142
    ⟨597193, by decide⟩ (by decide) (![⟨596932, by decide⟩,⟨597024, by decide⟩,⟨597112, by decide⟩,⟨597192, by decide⟩]) unmarked_context_11_19142_597193 node_context_11_19142_597193
  intro a
  fin_cases a
  · exact context_12_76568_596932
  · exact context_12_76569_597024
  · exact context_12_76570_597112
  · exact context_12_76571_597192

theorem selected_cut_23595 : selected 8 ⟨597219, by decide⟩
    (prefixPartial 13 306288) = some ⟨13, 2, 0, 597219, 306288, 669, 16384⟩ := by
  decide +kernel

theorem context_13_306288_597219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306288 ⟨597219, by decide⟩ :=
  accepted_of_selected 13 306288 ⟨597219, by decide⟩ ⟨13, 2, 0, 597219, 306288, 669, 16384⟩
    (by decide) selected_cut_23595

theorem selected_cut_23596 : selected 8 ⟨597257, by decide⟩
    (prefixPartial 13 306289) = some ⟨13, 2, 0, 597257, 306289, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_306289_597257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306289 ⟨597257, by decide⟩ :=
  accepted_of_selected 13 306289 ⟨597257, by decide⟩ ⟨13, 2, 0, 597257, 306289, 1785, 16384⟩
    (by decide) selected_cut_23596

theorem selected_cut_23597 : selected 8 ⟨597315, by decide⟩
    (prefixPartial 13 306290) = some ⟨13, 2, 0, 597315, 306290, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_306290_597315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306290 ⟨597315, by decide⟩ :=
  accepted_of_selected 13 306290 ⟨597315, by decide⟩ ⟨13, 2, 0, 597315, 306290, 2309, 16384⟩
    (by decide) selected_cut_23597

theorem selected_cut_23598 : selected 8 ⟨508985, by decide⟩
    (prefixPartial 13 306291) = some ⟨13, 1, 0, 508985, 306291, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306291_508985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306291 ⟨508985, by decide⟩ :=
  accepted_of_selected 13 306291 ⟨508985, by decide⟩ ⟨13, 1, 0, 508985, 306291, 1, 16384⟩
    (by decide) selected_cut_23598

theorem unmarked_context_12_76572_597316 : frontier 9 ⟨597316, by decide⟩
    (prefixCache 12 76572) (prefixPartial 12 76572) = false := by
  decide +kernel

theorem node_context_12_76572_597316 : EJMOriginalGlobalDAGData.nodes 9 ⟨597316, by decide⟩ =
    .split (coordinate 12) (![⟨597219, by decide⟩,⟨597257, by decide⟩,⟨597315, by decide⟩,⟨508985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76572_597316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76572 ⟨597316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76572
    ⟨597316, by decide⟩ (by decide) (![⟨597219, by decide⟩,⟨597257, by decide⟩,⟨597315, by decide⟩,⟨508985, by decide⟩]) unmarked_context_12_76572_597316 node_context_12_76572_597316
  intro a
  fin_cases a
  · exact context_13_306288_597219
  · exact context_13_306289_597257
  · exact context_13_306290_597315
  · exact context_13_306291_508985

theorem selected_cut_23599 : selected 8 ⟨597345, by decide⟩
    (prefixPartial 13 306292) = some ⟨13, 2, 0, 597345, 306292, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_306292_597345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306292 ⟨597345, by decide⟩ :=
  accepted_of_selected 13 306292 ⟨597345, by decide⟩ ⟨13, 2, 0, 597345, 306292, 1469, 16384⟩
    (by decide) selected_cut_23599

theorem selected_cut_23600 : selected 8 ⟨597375, by decide⟩
    (prefixPartial 13 306293) = some ⟨13, 2, 0, 597375, 306293, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_306293_597375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306293 ⟨597375, by decide⟩ :=
  accepted_of_selected 13 306293 ⟨597375, by decide⟩ ⟨13, 2, 0, 597375, 306293, 2145, 16384⟩
    (by decide) selected_cut_23600

theorem selected_cut_23601 : selected 8 ⟨597397, by decide⟩
    (prefixPartial 13 306294) = some ⟨13, 2, 0, 597397, 306294, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_306294_597397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306294 ⟨597397, by decide⟩ :=
  accepted_of_selected 13 306294 ⟨597397, by decide⟩ ⟨13, 2, 0, 597397, 306294, 2013, 16384⟩
    (by decide) selected_cut_23601

theorem selected_cut_23602 : selected 8 ⟨597404, by decide⟩
    (prefixPartial 13 306295) = some ⟨13, 2, 0, 597404, 306295, 781, 16384⟩ := by
  decide +kernel

theorem context_13_306295_597404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306295 ⟨597404, by decide⟩ :=
  accepted_of_selected 13 306295 ⟨597404, by decide⟩ ⟨13, 2, 0, 597404, 306295, 781, 16384⟩
    (by decide) selected_cut_23602

theorem unmarked_context_12_76573_597405 : frontier 9 ⟨597405, by decide⟩
    (prefixCache 12 76573) (prefixPartial 12 76573) = false := by
  decide +kernel

theorem node_context_12_76573_597405 : EJMOriginalGlobalDAGData.nodes 9 ⟨597405, by decide⟩ =
    .split (coordinate 12) (![⟨597345, by decide⟩,⟨597375, by decide⟩,⟨597397, by decide⟩,⟨597404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76573_597405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76573 ⟨597405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76573
    ⟨597405, by decide⟩ (by decide) (![⟨597345, by decide⟩,⟨597375, by decide⟩,⟨597397, by decide⟩,⟨597404, by decide⟩]) unmarked_context_12_76573_597405 node_context_12_76573_597405
  intro a
  fin_cases a
  · exact context_13_306292_597345
  · exact context_13_306293_597375
  · exact context_13_306294_597397
  · exact context_13_306295_597404

theorem selected_cut_23603 : selected 8 ⟨597425, by decide⟩
    (prefixPartial 13 306296) = some ⟨13, 2, 0, 597425, 306296, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_306296_597425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306296 ⟨597425, by decide⟩ :=
  accepted_of_selected 13 306296 ⟨597425, by decide⟩ ⟨13, 2, 0, 597425, 306296, 1229, 16384⟩
    (by decide) selected_cut_23603

theorem selected_cut_23604 : selected 8 ⟨597464, by decide⟩
    (prefixPartial 13 306297) = some ⟨13, 2, 0, 597464, 306297, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_306297_597464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306297 ⟨597464, by decide⟩ :=
  accepted_of_selected 13 306297 ⟨597464, by decide⟩ ⟨13, 2, 0, 597464, 306297, 2677, 16384⟩
    (by decide) selected_cut_23604

theorem selected_cut_23605 : selected 8 ⟨597487, by decide⟩
    (prefixPartial 13 306298) = some ⟨13, 2, 0, 597487, 306298, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_306298_597487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306298 ⟨597487, by decide⟩ :=
  accepted_of_selected 13 306298 ⟨597487, by decide⟩ ⟨13, 2, 0, 597487, 306298, 1773, 16384⟩
    (by decide) selected_cut_23605

theorem selected_cut_23606 : selected 8 ⟨597496, by decide⟩
    (prefixPartial 13 306299) = some ⟨13, 2, 0, 597496, 306299, 797, 16384⟩ := by
  decide +kernel

theorem context_13_306299_597496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306299 ⟨597496, by decide⟩ :=
  accepted_of_selected 13 306299 ⟨597496, by decide⟩ ⟨13, 2, 0, 597496, 306299, 797, 16384⟩
    (by decide) selected_cut_23606

theorem unmarked_context_12_76574_597497 : frontier 9 ⟨597497, by decide⟩
    (prefixCache 12 76574) (prefixPartial 12 76574) = false := by
  decide +kernel

theorem node_context_12_76574_597497 : EJMOriginalGlobalDAGData.nodes 9 ⟨597497, by decide⟩ =
    .split (coordinate 12) (![⟨597425, by decide⟩,⟨597464, by decide⟩,⟨597487, by decide⟩,⟨597496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76574_597497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76574 ⟨597497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76574
    ⟨597497, by decide⟩ (by decide) (![⟨597425, by decide⟩,⟨597464, by decide⟩,⟨597487, by decide⟩,⟨597496, by decide⟩]) unmarked_context_12_76574_597497 node_context_12_76574_597497
  intro a
  fin_cases a
  · exact context_13_306296_597425
  · exact context_13_306297_597464
  · exact context_13_306298_597487
  · exact context_13_306299_597496

theorem selected_cut_23607 : selected 8 ⟨597523, by decide⟩
    (prefixPartial 13 306300) = some ⟨13, 2, 0, 597523, 306300, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_306300_597523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306300 ⟨597523, by decide⟩ :=
  accepted_of_selected 13 306300 ⟨597523, by decide⟩ ⟨13, 2, 0, 597523, 306300, 1845, 16384⟩
    (by decide) selected_cut_23607

theorem selected_cut_23608 : selected 8 ⟨597568, by decide⟩
    (prefixPartial 13 306301) = some ⟨13, 2, 0, 597568, 306301, 3781, 16384⟩ := by
  decide +kernel

theorem context_13_306301_597568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306301 ⟨597568, by decide⟩ :=
  accepted_of_selected 13 306301 ⟨597568, by decide⟩ ⟨13, 2, 0, 597568, 306301, 3781, 16384⟩
    (by decide) selected_cut_23608

theorem selected_cut_23609 : selected 8 ⟨597620, by decide⟩
    (prefixPartial 13 306302) = some ⟨13, 2, 0, 597620, 306302, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_306302_597620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306302 ⟨597620, by decide⟩ :=
  accepted_of_selected 13 306302 ⟨597620, by decide⟩ ⟨13, 2, 0, 597620, 306302, 2693, 16384⟩
    (by decide) selected_cut_23609

theorem selected_cut_23610 : selected 8 ⟨597627, by decide⟩
    (prefixPartial 13 306303) = some ⟨13, 2, 0, 597627, 306303, 953, 16384⟩ := by
  decide +kernel

theorem context_13_306303_597627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306303 ⟨597627, by decide⟩ :=
  accepted_of_selected 13 306303 ⟨597627, by decide⟩ ⟨13, 2, 0, 597627, 306303, 953, 16384⟩
    (by decide) selected_cut_23610

theorem unmarked_context_12_76575_597628 : frontier 9 ⟨597628, by decide⟩
    (prefixCache 12 76575) (prefixPartial 12 76575) = false := by
  decide +kernel

theorem node_context_12_76575_597628 : EJMOriginalGlobalDAGData.nodes 9 ⟨597628, by decide⟩ =
    .split (coordinate 12) (![⟨597523, by decide⟩,⟨597568, by decide⟩,⟨597620, by decide⟩,⟨597627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76575_597628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76575 ⟨597628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76575
    ⟨597628, by decide⟩ (by decide) (![⟨597523, by decide⟩,⟨597568, by decide⟩,⟨597620, by decide⟩,⟨597627, by decide⟩]) unmarked_context_12_76575_597628 node_context_12_76575_597628
  intro a
  fin_cases a
  · exact context_13_306300_597523
  · exact context_13_306301_597568
  · exact context_13_306302_597620
  · exact context_13_306303_597627

theorem unmarked_context_11_19143_597629 : frontier 10 ⟨597629, by decide⟩
    (prefixCache 11 19143) (prefixPartial 11 19143) = false := by
  decide +kernel

theorem node_context_11_19143_597629 : EJMOriginalGlobalDAGData.nodes 10 ⟨597629, by decide⟩ =
    .split (coordinate 11) (![⟨597316, by decide⟩,⟨597405, by decide⟩,⟨597497, by decide⟩,⟨597628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19143_597629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19143 ⟨597629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19143
    ⟨597629, by decide⟩ (by decide) (![⟨597316, by decide⟩,⟨597405, by decide⟩,⟨597497, by decide⟩,⟨597628, by decide⟩]) unmarked_context_11_19143_597629 node_context_11_19143_597629
  intro a
  fin_cases a
  · exact context_12_76572_597316
  · exact context_12_76573_597405
  · exact context_12_76574_597497
  · exact context_12_76575_597628

theorem unmarked_context_10_4785_597630 : frontier 11 ⟨597630, by decide⟩
    (prefixCache 10 4785) (prefixPartial 10 4785) = false := by
  decide +kernel

theorem node_context_10_4785_597630 : EJMOriginalGlobalDAGData.nodes 11 ⟨597630, by decide⟩ =
    .split (coordinate 10) (![⟨596520, by decide⟩,⟨596803, by decide⟩,⟨597193, by decide⟩,⟨597629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4785_597630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4785 ⟨597630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4785
    ⟨597630, by decide⟩ (by decide) (![⟨596520, by decide⟩,⟨596803, by decide⟩,⟨597193, by decide⟩,⟨597629, by decide⟩]) unmarked_context_10_4785_597630 node_context_10_4785_597630
  intro a
  fin_cases a
  · exact context_11_19140_596520
  · exact context_11_19141_596803
  · exact context_11_19142_597193
  · exact context_11_19143_597629

theorem selected_cut_23611 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76576) = some ⟨12, 1, 0, 435790, 76576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76576_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76576 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76576 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76576, 1, 65536⟩
    (by decide) selected_cut_23611

theorem selected_cut_23612 : selected 8 ⟨597649, by decide⟩
    (prefixPartial 13 306308) = some ⟨13, 2, 0, 597649, 306308, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_306308_597649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306308 ⟨597649, by decide⟩ :=
  accepted_of_selected 13 306308 ⟨597649, by decide⟩ ⟨13, 2, 0, 597649, 306308, 1109, 16384⟩
    (by decide) selected_cut_23612

theorem selected_cut_23613 : selected 8 ⟨597674, by decide⟩
    (prefixPartial 13 306309) = some ⟨13, 2, 0, 597674, 306309, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_306309_597674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306309 ⟨597674, by decide⟩ :=
  accepted_of_selected 13 306309 ⟨597674, by decide⟩ ⟨13, 2, 0, 597674, 306309, 1813, 16384⟩
    (by decide) selected_cut_23613

theorem selected_cut_23614 : selected 8 ⟨597693, by decide⟩
    (prefixPartial 13 306310) = some ⟨13, 2, 0, 597693, 306310, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_306310_597693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306310 ⟨597693, by decide⟩ :=
  accepted_of_selected 13 306310 ⟨597693, by decide⟩ ⟨13, 2, 0, 597693, 306310, 1409, 16384⟩
    (by decide) selected_cut_23614

theorem selected_cut_23615 : selected 8 ⟨597698, by decide⟩
    (prefixPartial 13 306311) = some ⟨13, 2, 0, 597698, 306311, 613, 16384⟩ := by
  decide +kernel

theorem context_13_306311_597698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306311 ⟨597698, by decide⟩ :=
  accepted_of_selected 13 306311 ⟨597698, by decide⟩ ⟨13, 2, 0, 597698, 306311, 613, 16384⟩
    (by decide) selected_cut_23615

theorem unmarked_context_12_76577_597699 : frontier 9 ⟨597699, by decide⟩
    (prefixCache 12 76577) (prefixPartial 12 76577) = false := by
  decide +kernel

theorem node_context_12_76577_597699 : EJMOriginalGlobalDAGData.nodes 9 ⟨597699, by decide⟩ =
    .split (coordinate 12) (![⟨597649, by decide⟩,⟨597674, by decide⟩,⟨597693, by decide⟩,⟨597698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76577_597699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76577 ⟨597699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76577
    ⟨597699, by decide⟩ (by decide) (![⟨597649, by decide⟩,⟨597674, by decide⟩,⟨597693, by decide⟩,⟨597698, by decide⟩]) unmarked_context_12_76577_597699 node_context_12_76577_597699
  intro a
  fin_cases a
  · exact context_13_306308_597649
  · exact context_13_306309_597674
  · exact context_13_306310_597693
  · exact context_13_306311_597698

theorem selected_cut_23616 : selected 8 ⟨597714, by decide⟩
    (prefixPartial 13 306312) = some ⟨13, 2, 0, 597714, 306312, 989, 16384⟩ := by
  decide +kernel

theorem context_13_306312_597714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306312 ⟨597714, by decide⟩ :=
  accepted_of_selected 13 306312 ⟨597714, by decide⟩ ⟨13, 2, 0, 597714, 306312, 989, 16384⟩
    (by decide) selected_cut_23616

theorem selected_cut_23617 : selected 8 ⟨597740, by decide⟩
    (prefixPartial 13 306313) = some ⟨13, 2, 0, 597740, 306313, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_306313_597740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306313 ⟨597740, by decide⟩ :=
  accepted_of_selected 13 306313 ⟨597740, by decide⟩ ⟨13, 2, 0, 597740, 306313, 1953, 16384⟩
    (by decide) selected_cut_23617

theorem selected_cut_23618 : selected 8 ⟨597758, by decide⟩
    (prefixPartial 13 306314) = some ⟨13, 2, 0, 597758, 306314, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_306314_597758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306314 ⟨597758, by decide⟩ :=
  accepted_of_selected 13 306314 ⟨597758, by decide⟩ ⟨13, 2, 0, 597758, 306314, 1417, 16384⟩
    (by decide) selected_cut_23618

theorem selected_cut_23619 : selected 8 ⟨597762, by decide⟩
    (prefixPartial 13 306315) = some ⟨13, 2, 0, 597762, 306315, 601, 16384⟩ := by
  decide +kernel

theorem context_13_306315_597762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306315 ⟨597762, by decide⟩ :=
  accepted_of_selected 13 306315 ⟨597762, by decide⟩ ⟨13, 2, 0, 597762, 306315, 601, 16384⟩
    (by decide) selected_cut_23619

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
