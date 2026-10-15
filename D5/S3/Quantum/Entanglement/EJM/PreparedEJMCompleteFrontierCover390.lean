/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover389
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_37443 : selected 8 ⟨1000692, by decide⟩
    (prefixPartial 13 1199202) = some ⟨13, 2, 0, 1000692, 1199202, 849, 16384⟩ := by
  decide +kernel

theorem context_13_1199202_1000692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199202 ⟨1000692, by decide⟩ :=
  accepted_of_selected 13 1199202 ⟨1000692, by decide⟩ ⟨13, 2, 0, 1000692, 1199202, 849, 16384⟩
    (by decide) selected_cut_37443

theorem selected_cut_37444 : selected 8 ⟨1000696, by decide⟩
    (prefixPartial 13 1199203) = some ⟨13, 2, 0, 1000696, 1199203, 545, 16384⟩ := by
  decide +kernel

theorem context_13_1199203_1000696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199203 ⟨1000696, by decide⟩ :=
  accepted_of_selected 13 1199203 ⟨1000696, by decide⟩ ⟨13, 2, 0, 1000696, 1199203, 545, 16384⟩
    (by decide) selected_cut_37444

theorem unmarked_context_12_299800_1000697 : frontier 9 ⟨1000697, by decide⟩
    (prefixCache 12 299800) (prefixPartial 12 299800) = false := by
  decide +kernel

theorem node_context_12_299800_1000697 : EJMOriginalGlobalDAGData.nodes 9 ⟨1000697, by decide⟩ =
    .split (coordinate 12) (![⟨1000655, by decide⟩,⟨1000673, by decide⟩,⟨1000692, by decide⟩,⟨1000696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299800_1000697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299800 ⟨1000697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299800
    ⟨1000697, by decide⟩ (by decide) (![⟨1000655, by decide⟩,⟨1000673, by decide⟩,⟨1000692, by decide⟩,⟨1000696, by decide⟩]) unmarked_context_12_299800_1000697 node_context_12_299800_1000697
  intro a
  fin_cases a
  · exact context_13_1199200_1000655
  · exact context_13_1199201_1000673
  · exact context_13_1199202_1000692
  · exact context_13_1199203_1000696

theorem selected_cut_37445 : selected 9 ⟨1000756, by decide⟩
    (prefixPartial 12 299801) = some ⟨12, 2, 0, 1000756, 299801, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_299801_1000756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299801 ⟨1000756, by decide⟩ :=
  accepted_of_selected 12 299801 ⟨1000756, by decide⟩ ⟨12, 2, 0, 1000756, 299801, 3913, 65536⟩
    (by decide) selected_cut_37445

theorem selected_cut_37446 : selected 9 ⟨1000812, by decide⟩
    (prefixPartial 12 299802) = some ⟨12, 2, 0, 1000812, 299802, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_299802_1000812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299802 ⟨1000812, by decide⟩ :=
  accepted_of_selected 12 299802 ⟨1000812, by decide⟩ ⟨12, 2, 0, 1000812, 299802, 3517, 65536⟩
    (by decide) selected_cut_37446

theorem selected_cut_37447 : selected 9 ⟨1000868, by decide⟩
    (prefixPartial 12 299803) = some ⟨12, 2, 0, 1000868, 299803, 3865, 65536⟩ := by
  decide +kernel

theorem context_12_299803_1000868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299803 ⟨1000868, by decide⟩ :=
  accepted_of_selected 12 299803 ⟨1000868, by decide⟩ ⟨12, 2, 0, 1000868, 299803, 3865, 65536⟩
    (by decide) selected_cut_37447

theorem unmarked_context_11_74950_1000869 : frontier 10 ⟨1000869, by decide⟩
    (prefixCache 11 74950) (prefixPartial 11 74950) = false := by
  decide +kernel

theorem node_context_11_74950_1000869 : EJMOriginalGlobalDAGData.nodes 10 ⟨1000869, by decide⟩ =
    .split (coordinate 11) (![⟨1000697, by decide⟩,⟨1000756, by decide⟩,⟨1000812, by decide⟩,⟨1000868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74950_1000869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74950 ⟨1000869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74950
    ⟨1000869, by decide⟩ (by decide) (![⟨1000697, by decide⟩,⟨1000756, by decide⟩,⟨1000812, by decide⟩,⟨1000868, by decide⟩]) unmarked_context_11_74950_1000869 node_context_11_74950_1000869
  intro a
  fin_cases a
  · exact context_12_299800_1000697
  · exact context_12_299801_1000756
  · exact context_12_299802_1000812
  · exact context_12_299803_1000868

theorem selected_cut_37448 : selected 8 ⟨1000901, by decide⟩
    (prefixPartial 13 1199216) = some ⟨13, 2, 0, 1000901, 1199216, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_1199216_1000901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199216 ⟨1000901, by decide⟩ :=
  accepted_of_selected 13 1199216 ⟨1000901, by decide⟩ ⟨13, 2, 0, 1000901, 1199216, 1661, 16384⟩
    (by decide) selected_cut_37448

theorem selected_cut_37449 : selected 8 ⟨1000917, by decide⟩
    (prefixPartial 13 1199217) = some ⟨13, 2, 0, 1000917, 1199217, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_1199217_1000917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199217 ⟨1000917, by decide⟩ :=
  accepted_of_selected 13 1199217 ⟨1000917, by decide⟩ ⟨13, 2, 0, 1000917, 1199217, 1177, 16384⟩
    (by decide) selected_cut_37449

theorem selected_cut_37450 : selected 8 ⟨1000930, by decide⟩
    (prefixPartial 13 1199218) = some ⟨13, 2, 0, 1000930, 1199218, 805, 16384⟩ := by
  decide +kernel

theorem context_13_1199218_1000930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199218 ⟨1000930, by decide⟩ :=
  accepted_of_selected 13 1199218 ⟨1000930, by decide⟩ ⟨13, 2, 0, 1000930, 1199218, 805, 16384⟩
    (by decide) selected_cut_37450

theorem selected_cut_37451 : selected 8 ⟨1000935, by decide⟩
    (prefixPartial 13 1199219) = some ⟨13, 2, 0, 1000935, 1199219, 617, 16384⟩ := by
  decide +kernel

theorem context_13_1199219_1000935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199219 ⟨1000935, by decide⟩ :=
  accepted_of_selected 13 1199219 ⟨1000935, by decide⟩ ⟨13, 2, 0, 1000935, 1199219, 617, 16384⟩
    (by decide) selected_cut_37451

theorem unmarked_context_12_299804_1000936 : frontier 9 ⟨1000936, by decide⟩
    (prefixCache 12 299804) (prefixPartial 12 299804) = false := by
  decide +kernel

theorem node_context_12_299804_1000936 : EJMOriginalGlobalDAGData.nodes 9 ⟨1000936, by decide⟩ =
    .split (coordinate 12) (![⟨1000901, by decide⟩,⟨1000917, by decide⟩,⟨1000930, by decide⟩,⟨1000935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299804_1000936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299804 ⟨1000936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299804
    ⟨1000936, by decide⟩ (by decide) (![⟨1000901, by decide⟩,⟨1000917, by decide⟩,⟨1000930, by decide⟩,⟨1000935, by decide⟩]) unmarked_context_12_299804_1000936 node_context_12_299804_1000936
  intro a
  fin_cases a
  · exact context_13_1199216_1000901
  · exact context_13_1199217_1000917
  · exact context_13_1199218_1000930
  · exact context_13_1199219_1000935

theorem selected_cut_37452 : selected 8 ⟨1000961, by decide⟩
    (prefixPartial 13 1199220) = some ⟨13, 2, 0, 1000961, 1199220, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_1199220_1000961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199220 ⟨1000961, by decide⟩ :=
  accepted_of_selected 13 1199220 ⟨1000961, by decide⟩ ⟨13, 2, 0, 1000961, 1199220, 1357, 16384⟩
    (by decide) selected_cut_37452

theorem selected_cut_37453 : selected 8 ⟨1000976, by decide⟩
    (prefixPartial 13 1199221) = some ⟨13, 2, 0, 1000976, 1199221, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_1199221_1000976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199221 ⟨1000976, by decide⟩ :=
  accepted_of_selected 13 1199221 ⟨1000976, by decide⟩ ⟨13, 2, 0, 1000976, 1199221, 1329, 16384⟩
    (by decide) selected_cut_37453

theorem selected_cut_37454 : selected 8 ⟨1000994, by decide⟩
    (prefixPartial 13 1199222) = some ⟨13, 2, 0, 1000994, 1199222, 957, 16384⟩ := by
  decide +kernel

theorem context_13_1199222_1000994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199222 ⟨1000994, by decide⟩ :=
  accepted_of_selected 13 1199222 ⟨1000994, by decide⟩ ⟨13, 2, 0, 1000994, 1199222, 957, 16384⟩
    (by decide) selected_cut_37454

theorem selected_cut_37455 : selected 8 ⟨1001001, by decide⟩
    (prefixPartial 13 1199223) = some ⟨13, 2, 0, 1001001, 1199223, 597, 16384⟩ := by
  decide +kernel

theorem context_13_1199223_1001001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199223 ⟨1001001, by decide⟩ :=
  accepted_of_selected 13 1199223 ⟨1001001, by decide⟩ ⟨13, 2, 0, 1001001, 1199223, 597, 16384⟩
    (by decide) selected_cut_37455

theorem unmarked_context_12_299805_1001002 : frontier 9 ⟨1001002, by decide⟩
    (prefixCache 12 299805) (prefixPartial 12 299805) = false := by
  decide +kernel

theorem node_context_12_299805_1001002 : EJMOriginalGlobalDAGData.nodes 9 ⟨1001002, by decide⟩ =
    .split (coordinate 12) (![⟨1000961, by decide⟩,⟨1000976, by decide⟩,⟨1000994, by decide⟩,⟨1001001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299805_1001002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299805 ⟨1001002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299805
    ⟨1001002, by decide⟩ (by decide) (![⟨1000961, by decide⟩,⟨1000976, by decide⟩,⟨1000994, by decide⟩,⟨1001001, by decide⟩]) unmarked_context_12_299805_1001002 node_context_12_299805_1001002
  intro a
  fin_cases a
  · exact context_13_1199220_1000961
  · exact context_13_1199221_1000976
  · exact context_13_1199222_1000994
  · exact context_13_1199223_1001001

theorem selected_cut_37456 : selected 9 ⟨1001065, by decide⟩
    (prefixPartial 12 299806) = some ⟨12, 2, 0, 1001065, 299806, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_299806_1001065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299806 ⟨1001065, by decide⟩ :=
  accepted_of_selected 12 299806 ⟨1001065, by decide⟩ ⟨12, 2, 0, 1001065, 299806, 3973, 65536⟩
    (by decide) selected_cut_37456

theorem selected_cut_37457 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 299807) = some ⟨12, 1, 0, 903806, 299807, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299807_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299807 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 299807 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 299807, 1, 65536⟩
    (by decide) selected_cut_37457

theorem unmarked_context_11_74951_1001066 : frontier 10 ⟨1001066, by decide⟩
    (prefixCache 11 74951) (prefixPartial 11 74951) = false := by
  decide +kernel

theorem node_context_11_74951_1001066 : EJMOriginalGlobalDAGData.nodes 10 ⟨1001066, by decide⟩ =
    .split (coordinate 11) (![⟨1000936, by decide⟩,⟨1001002, by decide⟩,⟨1001065, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74951_1001066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74951 ⟨1001066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74951
    ⟨1001066, by decide⟩ (by decide) (![⟨1000936, by decide⟩,⟨1001002, by decide⟩,⟨1001065, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_74951_1001066 node_context_11_74951_1001066
  intro a
  fin_cases a
  · exact context_12_299804_1000936
  · exact context_12_299805_1001002
  · exact context_12_299806_1001065
  · exact context_12_299807_903806

theorem unmarked_context_10_18737_1001067 : frontier 11 ⟨1001067, by decide⟩
    (prefixCache 10 18737) (prefixPartial 10 18737) = false := by
  decide +kernel

theorem node_context_10_18737_1001067 : EJMOriginalGlobalDAGData.nodes 11 ⟨1001067, by decide⟩ =
    .split (coordinate 10) (![⟨1000283, by decide⟩,⟨1000623, by decide⟩,⟨1000869, by decide⟩,⟨1001066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18737_1001067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18737 ⟨1001067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18737
    ⟨1001067, by decide⟩ (by decide) (![⟨1000283, by decide⟩,⟨1000623, by decide⟩,⟨1000869, by decide⟩,⟨1001066, by decide⟩]) unmarked_context_10_18737_1001067 node_context_10_18737_1001067
  intro a
  fin_cases a
  · exact context_11_74948_1000283
  · exact context_11_74949_1000623
  · exact context_11_74950_1000869
  · exact context_11_74951_1001066

theorem selected_cut_37458 : selected 9 ⟨1001122, by decide⟩
    (prefixPartial 12 299808) = some ⟨12, 2, 0, 1001122, 299808, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_299808_1001122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299808 ⟨1001122, by decide⟩ :=
  accepted_of_selected 12 299808 ⟨1001122, by decide⟩ ⟨12, 2, 0, 1001122, 299808, 3177, 65536⟩
    (by decide) selected_cut_37458

theorem selected_cut_37459 : selected 9 ⟨1001168, by decide⟩
    (prefixPartial 12 299809) = some ⟨12, 2, 0, 1001168, 299809, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_299809_1001168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299809 ⟨1001168, by decide⟩ :=
  accepted_of_selected 12 299809 ⟨1001168, by decide⟩ ⟨12, 2, 0, 1001168, 299809, 3121, 65536⟩
    (by decide) selected_cut_37459

theorem selected_cut_37460 : selected 9 ⟨1001211, by decide⟩
    (prefixPartial 12 299810) = some ⟨12, 2, 0, 1001211, 299810, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_299810_1001211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299810 ⟨1001211, by decide⟩ :=
  accepted_of_selected 12 299810 ⟨1001211, by decide⟩ ⟨12, 2, 0, 1001211, 299810, 3017, 65536⟩
    (by decide) selected_cut_37460

theorem selected_cut_37461 : selected 9 ⟨1001254, by decide⟩
    (prefixPartial 12 299811) = some ⟨12, 2, 0, 1001254, 299811, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_299811_1001254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299811 ⟨1001254, by decide⟩ :=
  accepted_of_selected 12 299811 ⟨1001254, by decide⟩ ⟨12, 2, 0, 1001254, 299811, 2957, 65536⟩
    (by decide) selected_cut_37461

theorem unmarked_context_11_74952_1001255 : frontier 10 ⟨1001255, by decide⟩
    (prefixCache 11 74952) (prefixPartial 11 74952) = false := by
  decide +kernel

theorem node_context_11_74952_1001255 : EJMOriginalGlobalDAGData.nodes 10 ⟨1001255, by decide⟩ =
    .split (coordinate 11) (![⟨1001122, by decide⟩,⟨1001168, by decide⟩,⟨1001211, by decide⟩,⟨1001254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74952_1001255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74952 ⟨1001255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74952
    ⟨1001255, by decide⟩ (by decide) (![⟨1001122, by decide⟩,⟨1001168, by decide⟩,⟨1001211, by decide⟩,⟨1001254, by decide⟩]) unmarked_context_11_74952_1001255 node_context_11_74952_1001255
  intro a
  fin_cases a
  · exact context_12_299808_1001122
  · exact context_12_299809_1001168
  · exact context_12_299810_1001211
  · exact context_12_299811_1001254

theorem selected_cut_37462 : selected 8 ⟨1001293, by decide⟩
    (prefixPartial 13 1199248) = some ⟨13, 2, 0, 1001293, 1199248, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_1199248_1001293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199248 ⟨1001293, by decide⟩ :=
  accepted_of_selected 13 1199248 ⟨1001293, by decide⟩ ⟨13, 2, 0, 1001293, 1199248, 1601, 16384⟩
    (by decide) selected_cut_37462

theorem selected_cut_37463 : selected 8 ⟨1001317, by decide⟩
    (prefixPartial 13 1199249) = some ⟨13, 2, 0, 1001317, 1199249, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_1199249_1001317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199249 ⟨1001317, by decide⟩ :=
  accepted_of_selected 13 1199249 ⟨1001317, by decide⟩ ⟨13, 2, 0, 1001317, 1199249, 1245, 16384⟩
    (by decide) selected_cut_37463

theorem selected_cut_37464 : selected 8 ⟨1001332, by decide⟩
    (prefixPartial 13 1199250) = some ⟨13, 2, 0, 1001332, 1199250, 853, 16384⟩ := by
  decide +kernel

theorem context_13_1199250_1001332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199250 ⟨1001332, by decide⟩ :=
  accepted_of_selected 13 1199250 ⟨1001332, by decide⟩ ⟨13, 2, 0, 1001332, 1199250, 853, 16384⟩
    (by decide) selected_cut_37464

theorem selected_cut_37465 : selected 8 ⟨1001335, by decide⟩
    (prefixPartial 13 1199251) = some ⟨13, 2, 0, 1001335, 1199251, 505, 16384⟩ := by
  decide +kernel

theorem context_13_1199251_1001335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199251 ⟨1001335, by decide⟩ :=
  accepted_of_selected 13 1199251 ⟨1001335, by decide⟩ ⟨13, 2, 0, 1001335, 1199251, 505, 16384⟩
    (by decide) selected_cut_37465

theorem unmarked_context_12_299812_1001336 : frontier 9 ⟨1001336, by decide⟩
    (prefixCache 12 299812) (prefixPartial 12 299812) = false := by
  decide +kernel

theorem node_context_12_299812_1001336 : EJMOriginalGlobalDAGData.nodes 9 ⟨1001336, by decide⟩ =
    .split (coordinate 12) (![⟨1001293, by decide⟩,⟨1001317, by decide⟩,⟨1001332, by decide⟩,⟨1001335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299812_1001336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299812 ⟨1001336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299812
    ⟨1001336, by decide⟩ (by decide) (![⟨1001293, by decide⟩,⟨1001317, by decide⟩,⟨1001332, by decide⟩,⟨1001335, by decide⟩]) unmarked_context_12_299812_1001336 node_context_12_299812_1001336
  intro a
  fin_cases a
  · exact context_13_1199248_1001293
  · exact context_13_1199249_1001317
  · exact context_13_1199250_1001332
  · exact context_13_1199251_1001335

theorem selected_cut_37466 : selected 9 ⟨1001400, by decide⟩
    (prefixPartial 12 299813) = some ⟨12, 2, 0, 1001400, 299813, 4005, 65536⟩ := by
  decide +kernel

theorem context_12_299813_1001400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299813 ⟨1001400, by decide⟩ :=
  accepted_of_selected 12 299813 ⟨1001400, by decide⟩ ⟨12, 2, 0, 1001400, 299813, 4005, 65536⟩
    (by decide) selected_cut_37466

theorem selected_cut_37467 : selected 9 ⟨1001452, by decide⟩
    (prefixPartial 12 299814) = some ⟨12, 2, 0, 1001452, 299814, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_299814_1001452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299814 ⟨1001452, by decide⟩ :=
  accepted_of_selected 12 299814 ⟨1001452, by decide⟩ ⟨12, 2, 0, 1001452, 299814, 3473, 65536⟩
    (by decide) selected_cut_37467

theorem selected_cut_37468 : selected 9 ⟨1001501, by decide⟩
    (prefixPartial 12 299815) = some ⟨12, 2, 0, 1001501, 299815, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_299815_1001501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299815 ⟨1001501, by decide⟩ :=
  accepted_of_selected 12 299815 ⟨1001501, by decide⟩ ⟨12, 2, 0, 1001501, 299815, 3461, 65536⟩
    (by decide) selected_cut_37468

theorem unmarked_context_11_74953_1001502 : frontier 10 ⟨1001502, by decide⟩
    (prefixCache 11 74953) (prefixPartial 11 74953) = false := by
  decide +kernel

theorem node_context_11_74953_1001502 : EJMOriginalGlobalDAGData.nodes 10 ⟨1001502, by decide⟩ =
    .split (coordinate 11) (![⟨1001336, by decide⟩,⟨1001400, by decide⟩,⟨1001452, by decide⟩,⟨1001501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74953_1001502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74953 ⟨1001502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74953
    ⟨1001502, by decide⟩ (by decide) (![⟨1001336, by decide⟩,⟨1001400, by decide⟩,⟨1001452, by decide⟩,⟨1001501, by decide⟩]) unmarked_context_11_74953_1001502 node_context_11_74953_1001502
  intro a
  fin_cases a
  · exact context_12_299812_1001336
  · exact context_12_299813_1001400
  · exact context_12_299814_1001452
  · exact context_12_299815_1001501

theorem selected_cut_37469 : selected 9 ⟨1001571, by decide⟩
    (prefixPartial 12 299816) = some ⟨12, 2, 0, 1001571, 299816, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_299816_1001571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299816 ⟨1001571, by decide⟩ :=
  accepted_of_selected 12 299816 ⟨1001571, by decide⟩ ⟨12, 2, 0, 1001571, 299816, 4069, 65536⟩
    (by decide) selected_cut_37469

theorem selected_cut_37470 : selected 9 ⟨1001640, by decide⟩
    (prefixPartial 12 299817) = some ⟨12, 2, 0, 1001640, 299817, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_299817_1001640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299817 ⟨1001640, by decide⟩ :=
  accepted_of_selected 12 299817 ⟨1001640, by decide⟩ ⟨12, 2, 0, 1001640, 299817, 3913, 65536⟩
    (by decide) selected_cut_37470

theorem selected_cut_37471 : selected 9 ⟨1001687, by decide⟩
    (prefixPartial 12 299818) = some ⟨12, 2, 0, 1001687, 299818, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_299818_1001687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299818 ⟨1001687, by decide⟩ :=
  accepted_of_selected 12 299818 ⟨1001687, by decide⟩ ⟨12, 2, 0, 1001687, 299818, 3285, 65536⟩
    (by decide) selected_cut_37471

theorem selected_cut_37472 : selected 9 ⟨1001734, by decide⟩
    (prefixPartial 12 299819) = some ⟨12, 2, 0, 1001734, 299819, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_299819_1001734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299819 ⟨1001734, by decide⟩ :=
  accepted_of_selected 12 299819 ⟨1001734, by decide⟩ ⟨12, 2, 0, 1001734, 299819, 3509, 65536⟩
    (by decide) selected_cut_37472

theorem unmarked_context_11_74954_1001735 : frontier 10 ⟨1001735, by decide⟩
    (prefixCache 11 74954) (prefixPartial 11 74954) = false := by
  decide +kernel

theorem node_context_11_74954_1001735 : EJMOriginalGlobalDAGData.nodes 10 ⟨1001735, by decide⟩ =
    .split (coordinate 11) (![⟨1001571, by decide⟩,⟨1001640, by decide⟩,⟨1001687, by decide⟩,⟨1001734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74954_1001735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74954 ⟨1001735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74954
    ⟨1001735, by decide⟩ (by decide) (![⟨1001571, by decide⟩,⟨1001640, by decide⟩,⟨1001687, by decide⟩,⟨1001734, by decide⟩]) unmarked_context_11_74954_1001735 node_context_11_74954_1001735
  intro a
  fin_cases a
  · exact context_12_299816_1001571
  · exact context_12_299817_1001640
  · exact context_12_299818_1001687
  · exact context_12_299819_1001734

theorem selected_cut_37473 : selected 9 ⟨1001796, by decide⟩
    (prefixPartial 12 299820) = some ⟨12, 2, 0, 1001796, 299820, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_299820_1001796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299820 ⟨1001796, by decide⟩ :=
  accepted_of_selected 12 299820 ⟨1001796, by decide⟩ ⟨12, 2, 0, 1001796, 299820, 3441, 65536⟩
    (by decide) selected_cut_37473

theorem selected_cut_37474 : selected 9 ⟨1001866, by decide⟩
    (prefixPartial 12 299821) = some ⟨12, 2, 0, 1001866, 299821, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_299821_1001866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299821 ⟨1001866, by decide⟩ :=
  accepted_of_selected 12 299821 ⟨1001866, by decide⟩ ⟨12, 2, 0, 1001866, 299821, 3849, 65536⟩
    (by decide) selected_cut_37474

theorem selected_cut_37475 : selected 9 ⟨1001926, by decide⟩
    (prefixPartial 12 299822) = some ⟨12, 2, 0, 1001926, 299822, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_299822_1001926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299822 ⟨1001926, by decide⟩ :=
  accepted_of_selected 12 299822 ⟨1001926, by decide⟩ ⟨12, 2, 0, 1001926, 299822, 3457, 65536⟩
    (by decide) selected_cut_37475

theorem selected_cut_37476 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 299823) = some ⟨12, 1, 0, 903806, 299823, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299823_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299823 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 299823 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 299823, 1, 65536⟩
    (by decide) selected_cut_37476

theorem unmarked_context_11_74955_1001927 : frontier 10 ⟨1001927, by decide⟩
    (prefixCache 11 74955) (prefixPartial 11 74955) = false := by
  decide +kernel

theorem node_context_11_74955_1001927 : EJMOriginalGlobalDAGData.nodes 10 ⟨1001927, by decide⟩ =
    .split (coordinate 11) (![⟨1001796, by decide⟩,⟨1001866, by decide⟩,⟨1001926, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74955_1001927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74955 ⟨1001927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74955
    ⟨1001927, by decide⟩ (by decide) (![⟨1001796, by decide⟩,⟨1001866, by decide⟩,⟨1001926, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_74955_1001927 node_context_11_74955_1001927
  intro a
  fin_cases a
  · exact context_12_299820_1001796
  · exact context_12_299821_1001866
  · exact context_12_299822_1001926
  · exact context_12_299823_903806

theorem unmarked_context_10_18738_1001928 : frontier 11 ⟨1001928, by decide⟩
    (prefixCache 10 18738) (prefixPartial 10 18738) = false := by
  decide +kernel

theorem node_context_10_18738_1001928 : EJMOriginalGlobalDAGData.nodes 11 ⟨1001928, by decide⟩ =
    .split (coordinate 10) (![⟨1001255, by decide⟩,⟨1001502, by decide⟩,⟨1001735, by decide⟩,⟨1001927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18738_1001928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18738 ⟨1001928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18738
    ⟨1001928, by decide⟩ (by decide) (![⟨1001255, by decide⟩,⟨1001502, by decide⟩,⟨1001735, by decide⟩,⟨1001927, by decide⟩]) unmarked_context_10_18738_1001928 node_context_10_18738_1001928
  intro a
  fin_cases a
  · exact context_11_74952_1001255
  · exact context_11_74953_1001502
  · exact context_11_74954_1001735
  · exact context_11_74955_1001927

theorem selected_cut_37477 : selected 9 ⟨1001995, by decide⟩
    (prefixPartial 12 299824) = some ⟨12, 2, 0, 1001995, 299824, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_299824_1001995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299824 ⟨1001995, by decide⟩ :=
  accepted_of_selected 12 299824 ⟨1001995, by decide⟩ ⟨12, 2, 0, 1001995, 299824, 1777, 65536⟩
    (by decide) selected_cut_37477

theorem selected_cut_37478 : selected 9 ⟨1002041, by decide⟩
    (prefixPartial 12 299825) = some ⟨12, 2, 0, 1002041, 299825, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_299825_1002041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299825 ⟨1002041, by decide⟩ :=
  accepted_of_selected 12 299825 ⟨1002041, by decide⟩ ⟨12, 2, 0, 1002041, 299825, 3109, 65536⟩
    (by decide) selected_cut_37478

theorem selected_cut_37479 : selected 9 ⟨1002081, by decide⟩
    (prefixPartial 12 299826) = some ⟨12, 2, 0, 1002081, 299826, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_299826_1002081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299826 ⟨1002081, by decide⟩ :=
  accepted_of_selected 12 299826 ⟨1002081, by decide⟩ ⟨12, 2, 0, 1002081, 299826, 2833, 65536⟩
    (by decide) selected_cut_37479

theorem selected_cut_37480 : selected 9 ⟨1002121, by decide⟩
    (prefixPartial 12 299827) = some ⟨12, 2, 0, 1002121, 299827, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_299827_1002121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299827 ⟨1002121, by decide⟩ :=
  accepted_of_selected 12 299827 ⟨1002121, by decide⟩ ⟨12, 2, 0, 1002121, 299827, 2705, 65536⟩
    (by decide) selected_cut_37480

theorem unmarked_context_11_74956_1002122 : frontier 10 ⟨1002122, by decide⟩
    (prefixCache 11 74956) (prefixPartial 11 74956) = false := by
  decide +kernel

theorem node_context_11_74956_1002122 : EJMOriginalGlobalDAGData.nodes 10 ⟨1002122, by decide⟩ =
    .split (coordinate 11) (![⟨1001995, by decide⟩,⟨1002041, by decide⟩,⟨1002081, by decide⟩,⟨1002121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74956_1002122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74956 ⟨1002122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74956
    ⟨1002122, by decide⟩ (by decide) (![⟨1001995, by decide⟩,⟨1002041, by decide⟩,⟨1002081, by decide⟩,⟨1002121, by decide⟩]) unmarked_context_11_74956_1002122 node_context_11_74956_1002122
  intro a
  fin_cases a
  · exact context_12_299824_1001995
  · exact context_12_299825_1002041
  · exact context_12_299826_1002081
  · exact context_12_299827_1002121

theorem selected_cut_37481 : selected 9 ⟨1002190, by decide⟩
    (prefixPartial 12 299828) = some ⟨12, 2, 0, 1002190, 299828, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_299828_1002190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299828 ⟨1002190, by decide⟩ :=
  accepted_of_selected 12 299828 ⟨1002190, by decide⟩ ⟨12, 2, 0, 1002190, 299828, 3825, 65536⟩
    (by decide) selected_cut_37481

theorem selected_cut_37482 : selected 9 ⟨1002250, by decide⟩
    (prefixPartial 12 299829) = some ⟨12, 2, 0, 1002250, 299829, 3793, 65536⟩ := by
  decide +kernel

theorem context_12_299829_1002250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299829 ⟨1002250, by decide⟩ :=
  accepted_of_selected 12 299829 ⟨1002250, by decide⟩ ⟨12, 2, 0, 1002250, 299829, 3793, 65536⟩
    (by decide) selected_cut_37482

theorem selected_cut_37483 : selected 9 ⟨1002301, by decide⟩
    (prefixPartial 12 299830) = some ⟨12, 2, 0, 1002301, 299830, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_299830_1002301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299830 ⟨1002301, by decide⟩ :=
  accepted_of_selected 12 299830 ⟨1002301, by decide⟩ ⟨12, 2, 0, 1002301, 299830, 3337, 65536⟩
    (by decide) selected_cut_37483

theorem selected_cut_37484 : selected 9 ⟨1002346, by decide⟩
    (prefixPartial 12 299831) = some ⟨12, 2, 0, 1002346, 299831, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_299831_1002346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299831 ⟨1002346, by decide⟩ :=
  accepted_of_selected 12 299831 ⟨1002346, by decide⟩ ⟨12, 2, 0, 1002346, 299831, 3185, 65536⟩
    (by decide) selected_cut_37484

theorem unmarked_context_11_74957_1002347 : frontier 10 ⟨1002347, by decide⟩
    (prefixCache 11 74957) (prefixPartial 11 74957) = false := by
  decide +kernel

theorem node_context_11_74957_1002347 : EJMOriginalGlobalDAGData.nodes 10 ⟨1002347, by decide⟩ =
    .split (coordinate 11) (![⟨1002190, by decide⟩,⟨1002250, by decide⟩,⟨1002301, by decide⟩,⟨1002346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74957_1002347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74957 ⟨1002347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74957
    ⟨1002347, by decide⟩ (by decide) (![⟨1002190, by decide⟩,⟨1002250, by decide⟩,⟨1002301, by decide⟩,⟨1002346, by decide⟩]) unmarked_context_11_74957_1002347 node_context_11_74957_1002347
  intro a
  fin_cases a
  · exact context_12_299828_1002190
  · exact context_12_299829_1002250
  · exact context_12_299830_1002301
  · exact context_12_299831_1002346

theorem selected_cut_37485 : selected 9 ⟨1002409, by decide⟩
    (prefixPartial 12 299832) = some ⟨12, 2, 0, 1002409, 299832, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_299832_1002409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299832 ⟨1002409, by decide⟩ :=
  accepted_of_selected 12 299832 ⟨1002409, by decide⟩ ⟨12, 2, 0, 1002409, 299832, 3541, 65536⟩
    (by decide) selected_cut_37485

theorem selected_cut_37486 : selected 9 ⟨1002467, by decide⟩
    (prefixPartial 12 299833) = some ⟨12, 2, 0, 1002467, 299833, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_299833_1002467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299833 ⟨1002467, by decide⟩ :=
  accepted_of_selected 12 299833 ⟨1002467, by decide⟩ ⟨12, 2, 0, 1002467, 299833, 3585, 65536⟩
    (by decide) selected_cut_37486

theorem selected_cut_37487 : selected 9 ⟨1002512, by decide⟩
    (prefixPartial 12 299834) = some ⟨12, 2, 0, 1002512, 299834, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_299834_1002512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299834 ⟨1002512, by decide⟩ :=
  accepted_of_selected 12 299834 ⟨1002512, by decide⟩ ⟨12, 2, 0, 1002512, 299834, 3137, 65536⟩
    (by decide) selected_cut_37487

theorem selected_cut_37488 : selected 9 ⟨1002558, by decide⟩
    (prefixPartial 12 299835) = some ⟨12, 2, 0, 1002558, 299835, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_299835_1002558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299835 ⟨1002558, by decide⟩ :=
  accepted_of_selected 12 299835 ⟨1002558, by decide⟩ ⟨12, 2, 0, 1002558, 299835, 3041, 65536⟩
    (by decide) selected_cut_37488

theorem unmarked_context_11_74958_1002559 : frontier 10 ⟨1002559, by decide⟩
    (prefixCache 11 74958) (prefixPartial 11 74958) = false := by
  decide +kernel

theorem node_context_11_74958_1002559 : EJMOriginalGlobalDAGData.nodes 10 ⟨1002559, by decide⟩ =
    .split (coordinate 11) (![⟨1002409, by decide⟩,⟨1002467, by decide⟩,⟨1002512, by decide⟩,⟨1002558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74958_1002559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74958 ⟨1002559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74958
    ⟨1002559, by decide⟩ (by decide) (![⟨1002409, by decide⟩,⟨1002467, by decide⟩,⟨1002512, by decide⟩,⟨1002558, by decide⟩]) unmarked_context_11_74958_1002559 node_context_11_74958_1002559
  intro a
  fin_cases a
  · exact context_12_299832_1002409
  · exact context_12_299833_1002467
  · exact context_12_299834_1002512
  · exact context_12_299835_1002558

theorem selected_cut_37489 : selected 9 ⟨1002615, by decide⟩
    (prefixPartial 12 299836) = some ⟨12, 2, 0, 1002615, 299836, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_299836_1002615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299836 ⟨1002615, by decide⟩ :=
  accepted_of_selected 12 299836 ⟨1002615, by decide⟩ ⟨12, 2, 0, 1002615, 299836, 3245, 65536⟩
    (by decide) selected_cut_37489

theorem selected_cut_37490 : selected 9 ⟨1002671, by decide⟩
    (prefixPartial 12 299837) = some ⟨12, 2, 0, 1002671, 299837, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_299837_1002671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299837 ⟨1002671, by decide⟩ :=
  accepted_of_selected 12 299837 ⟨1002671, by decide⟩ ⟨12, 2, 0, 1002671, 299837, 3397, 65536⟩
    (by decide) selected_cut_37490

theorem selected_cut_37491 : selected 9 ⟨1002724, by decide⟩
    (prefixPartial 12 299838) = some ⟨12, 2, 0, 1002724, 299838, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_299838_1002724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299838 ⟨1002724, by decide⟩ :=
  accepted_of_selected 12 299838 ⟨1002724, by decide⟩ ⟨12, 2, 0, 1002724, 299838, 3189, 65536⟩
    (by decide) selected_cut_37491

theorem selected_cut_37492 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 299839) = some ⟨12, 1, 0, 429285, 299839, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299839_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299839 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 299839 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 299839, 1, 65536⟩
    (by decide) selected_cut_37492

theorem unmarked_context_11_74959_1002725 : frontier 10 ⟨1002725, by decide⟩
    (prefixCache 11 74959) (prefixPartial 11 74959) = false := by
  decide +kernel

theorem node_context_11_74959_1002725 : EJMOriginalGlobalDAGData.nodes 10 ⟨1002725, by decide⟩ =
    .split (coordinate 11) (![⟨1002615, by decide⟩,⟨1002671, by decide⟩,⟨1002724, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74959_1002725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74959 ⟨1002725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74959
    ⟨1002725, by decide⟩ (by decide) (![⟨1002615, by decide⟩,⟨1002671, by decide⟩,⟨1002724, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_74959_1002725 node_context_11_74959_1002725
  intro a
  fin_cases a
  · exact context_12_299836_1002615
  · exact context_12_299837_1002671
  · exact context_12_299838_1002724
  · exact context_12_299839_429285

theorem unmarked_context_10_18739_1002726 : frontier 11 ⟨1002726, by decide⟩
    (prefixCache 10 18739) (prefixPartial 10 18739) = false := by
  decide +kernel

theorem node_context_10_18739_1002726 : EJMOriginalGlobalDAGData.nodes 11 ⟨1002726, by decide⟩ =
    .split (coordinate 10) (![⟨1002122, by decide⟩,⟨1002347, by decide⟩,⟨1002559, by decide⟩,⟨1002725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18739_1002726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18739 ⟨1002726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18739
    ⟨1002726, by decide⟩ (by decide) (![⟨1002122, by decide⟩,⟨1002347, by decide⟩,⟨1002559, by decide⟩,⟨1002725, by decide⟩]) unmarked_context_10_18739_1002726 node_context_10_18739_1002726
  intro a
  fin_cases a
  · exact context_11_74956_1002122
  · exact context_11_74957_1002347
  · exact context_11_74958_1002559
  · exact context_11_74959_1002725

theorem unmarked_context_9_4684_1002727 : frontier 12 ⟨1002727, by decide⟩
    (prefixCache 9 4684) (prefixPartial 9 4684) = false := by
  decide +kernel

theorem node_context_9_4684_1002727 : EJMOriginalGlobalDAGData.nodes 12 ⟨1002727, by decide⟩ =
    .split (coordinate 9) (![⟨1000088, by decide⟩,⟨1001067, by decide⟩,⟨1001928, by decide⟩,⟨1002726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4684_1002727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4684 ⟨1002727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4684
    ⟨1002727, by decide⟩ (by decide) (![⟨1000088, by decide⟩,⟨1001067, by decide⟩,⟨1001928, by decide⟩,⟨1002726, by decide⟩]) unmarked_context_9_4684_1002727 node_context_9_4684_1002727
  intro a
  fin_cases a
  · exact context_10_18736_1000088
  · exact context_10_18737_1001067
  · exact context_10_18738_1001928
  · exact context_10_18739_1002726

theorem selected_cut_37493 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74960) = some ⟨11, 1, 0, 907917, 74960, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74960_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74960 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74960 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74960, 1, 262144⟩
    (by decide) selected_cut_37493

theorem selected_cut_37494 : selected 9 ⟨1002775, by decide⟩
    (prefixPartial 12 299844) = some ⟨12, 2, 0, 1002775, 299844, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_299844_1002775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299844 ⟨1002775, by decide⟩ :=
  accepted_of_selected 12 299844 ⟨1002775, by decide⟩ ⟨12, 2, 0, 1002775, 299844, 2805, 65536⟩
    (by decide) selected_cut_37494

theorem selected_cut_37495 : selected 9 ⟨1002819, by decide⟩
    (prefixPartial 12 299845) = some ⟨12, 2, 0, 1002819, 299845, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_299845_1002819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299845 ⟨1002819, by decide⟩ :=
  accepted_of_selected 12 299845 ⟨1002819, by decide⟩ ⟨12, 2, 0, 1002819, 299845, 2753, 65536⟩
    (by decide) selected_cut_37495

theorem selected_cut_37496 : selected 9 ⟨1002853, by decide⟩
    (prefixPartial 12 299846) = some ⟨12, 2, 0, 1002853, 299846, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_299846_1002853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299846 ⟨1002853, by decide⟩ :=
  accepted_of_selected 12 299846 ⟨1002853, by decide⟩ ⟨12, 2, 0, 1002853, 299846, 2429, 65536⟩
    (by decide) selected_cut_37496

theorem selected_cut_37497 : selected 9 ⟨1002894, by decide⟩
    (prefixPartial 12 299847) = some ⟨12, 2, 0, 1002894, 299847, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_299847_1002894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299847 ⟨1002894, by decide⟩ :=
  accepted_of_selected 12 299847 ⟨1002894, by decide⟩ ⟨12, 2, 0, 1002894, 299847, 2549, 65536⟩
    (by decide) selected_cut_37497

theorem unmarked_context_11_74961_1002895 : frontier 10 ⟨1002895, by decide⟩
    (prefixCache 11 74961) (prefixPartial 11 74961) = false := by
  decide +kernel

theorem node_context_11_74961_1002895 : EJMOriginalGlobalDAGData.nodes 10 ⟨1002895, by decide⟩ =
    .split (coordinate 11) (![⟨1002775, by decide⟩,⟨1002819, by decide⟩,⟨1002853, by decide⟩,⟨1002894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74961_1002895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74961 ⟨1002895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74961
    ⟨1002895, by decide⟩ (by decide) (![⟨1002775, by decide⟩,⟨1002819, by decide⟩,⟨1002853, by decide⟩,⟨1002894, by decide⟩]) unmarked_context_11_74961_1002895 node_context_11_74961_1002895
  intro a
  fin_cases a
  · exact context_12_299844_1002775
  · exact context_12_299845_1002819
  · exact context_12_299846_1002853
  · exact context_12_299847_1002894

theorem selected_cut_37498 : selected 9 ⟨1002938, by decide⟩
    (prefixPartial 12 299848) = some ⟨12, 2, 0, 1002938, 299848, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_299848_1002938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299848 ⟨1002938, by decide⟩ :=
  accepted_of_selected 12 299848 ⟨1002938, by decide⟩ ⟨12, 2, 0, 1002938, 299848, 2797, 65536⟩
    (by decide) selected_cut_37498

theorem selected_cut_37499 : selected 9 ⟨1002979, by decide⟩
    (prefixPartial 12 299849) = some ⟨12, 2, 0, 1002979, 299849, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_299849_1002979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299849 ⟨1002979, by decide⟩ :=
  accepted_of_selected 12 299849 ⟨1002979, by decide⟩ ⟨12, 2, 0, 1002979, 299849, 2733, 65536⟩
    (by decide) selected_cut_37499

theorem selected_cut_37500 : selected 9 ⟨1003016, by decide⟩
    (prefixPartial 12 299850) = some ⟨12, 2, 0, 1003016, 299850, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_299850_1003016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299850 ⟨1003016, by decide⟩ :=
  accepted_of_selected 12 299850 ⟨1003016, by decide⟩ ⟨12, 2, 0, 1003016, 299850, 2353, 65536⟩
    (by decide) selected_cut_37500

theorem selected_cut_37501 : selected 9 ⟨1003055, by decide⟩
    (prefixPartial 12 299851) = some ⟨12, 2, 0, 1003055, 299851, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_299851_1003055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299851 ⟨1003055, by decide⟩ :=
  accepted_of_selected 12 299851 ⟨1003055, by decide⟩ ⟨12, 2, 0, 1003055, 299851, 2609, 65536⟩
    (by decide) selected_cut_37501

theorem unmarked_context_11_74962_1003056 : frontier 10 ⟨1003056, by decide⟩
    (prefixCache 11 74962) (prefixPartial 11 74962) = false := by
  decide +kernel

theorem node_context_11_74962_1003056 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003056, by decide⟩ =
    .split (coordinate 11) (![⟨1002938, by decide⟩,⟨1002979, by decide⟩,⟨1003016, by decide⟩,⟨1003055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74962_1003056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74962 ⟨1003056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74962
    ⟨1003056, by decide⟩ (by decide) (![⟨1002938, by decide⟩,⟨1002979, by decide⟩,⟨1003016, by decide⟩,⟨1003055, by decide⟩]) unmarked_context_11_74962_1003056 node_context_11_74962_1003056
  intro a
  fin_cases a
  · exact context_12_299848_1002938
  · exact context_12_299849_1002979
  · exact context_12_299850_1003016
  · exact context_12_299851_1003055

theorem selected_cut_37502 : selected 9 ⟨1003094, by decide⟩
    (prefixPartial 12 299852) = some ⟨12, 2, 0, 1003094, 299852, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_299852_1003094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299852 ⟨1003094, by decide⟩ :=
  accepted_of_selected 12 299852 ⟨1003094, by decide⟩ ⟨12, 2, 0, 1003094, 299852, 2541, 65536⟩
    (by decide) selected_cut_37502

theorem selected_cut_37503 : selected 9 ⟨1003134, by decide⟩
    (prefixPartial 12 299853) = some ⟨12, 2, 0, 1003134, 299853, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_299853_1003134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299853 ⟨1003134, by decide⟩ :=
  accepted_of_selected 12 299853 ⟨1003134, by decide⟩ ⟨12, 2, 0, 1003134, 299853, 2513, 65536⟩
    (by decide) selected_cut_37503

theorem selected_cut_37504 : selected 9 ⟨1003180, by decide⟩
    (prefixPartial 12 299854) = some ⟨12, 2, 0, 1003180, 299854, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_299854_1003180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299854 ⟨1003180, by decide⟩ :=
  accepted_of_selected 12 299854 ⟨1003180, by decide⟩ ⟨12, 2, 0, 1003180, 299854, 2417, 65536⟩
    (by decide) selected_cut_37504

theorem selected_cut_37505 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 299855) = some ⟨12, 1, 0, 903806, 299855, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299855_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299855 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 299855 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 299855, 1, 65536⟩
    (by decide) selected_cut_37505

theorem unmarked_context_11_74963_1003181 : frontier 10 ⟨1003181, by decide⟩
    (prefixCache 11 74963) (prefixPartial 11 74963) = false := by
  decide +kernel

theorem node_context_11_74963_1003181 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003181, by decide⟩ =
    .split (coordinate 11) (![⟨1003094, by decide⟩,⟨1003134, by decide⟩,⟨1003180, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74963_1003181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74963 ⟨1003181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74963
    ⟨1003181, by decide⟩ (by decide) (![⟨1003094, by decide⟩,⟨1003134, by decide⟩,⟨1003180, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_74963_1003181 node_context_11_74963_1003181
  intro a
  fin_cases a
  · exact context_12_299852_1003094
  · exact context_12_299853_1003134
  · exact context_12_299854_1003180
  · exact context_12_299855_903806

theorem unmarked_context_10_18740_1003182 : frontier 11 ⟨1003182, by decide⟩
    (prefixCache 10 18740) (prefixPartial 10 18740) = false := by
  decide +kernel

theorem node_context_10_18740_1003182 : EJMOriginalGlobalDAGData.nodes 11 ⟨1003182, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1002895, by decide⟩,⟨1003056, by decide⟩,⟨1003181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18740_1003182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18740 ⟨1003182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18740
    ⟨1003182, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1002895, by decide⟩,⟨1003056, by decide⟩,⟨1003181, by decide⟩]) unmarked_context_10_18740_1003182 node_context_10_18740_1003182
  intro a
  fin_cases a
  · exact context_11_74960_907917
  · exact context_11_74961_1002895
  · exact context_11_74962_1003056
  · exact context_11_74963_1003181

theorem selected_cut_37506 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18741) = some ⟨10, 1, 0, 893098, 18741, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18741_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18741 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18741 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18741, 1, 1048576⟩
    (by decide) selected_cut_37506

theorem selected_cut_37507 : selected 9 ⟨1003209, by decide⟩
    (prefixPartial 12 299872) = some ⟨12, 2, 0, 1003209, 299872, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_299872_1003209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299872 ⟨1003209, by decide⟩ :=
  accepted_of_selected 12 299872 ⟨1003209, by decide⟩ ⟨12, 2, 0, 1003209, 299872, 1981, 65536⟩
    (by decide) selected_cut_37507

theorem selected_cut_37508 : selected 9 ⟨1003238, by decide⟩
    (prefixPartial 12 299873) = some ⟨12, 2, 0, 1003238, 299873, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_299873_1003238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299873 ⟨1003238, by decide⟩ :=
  accepted_of_selected 12 299873 ⟨1003238, by decide⟩ ⟨12, 2, 0, 1003238, 299873, 2117, 65536⟩
    (by decide) selected_cut_37508

theorem selected_cut_37509 : selected 9 ⟨1003263, by decide⟩
    (prefixPartial 12 299874) = some ⟨12, 2, 0, 1003263, 299874, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_299874_1003263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299874 ⟨1003263, by decide⟩ :=
  accepted_of_selected 12 299874 ⟨1003263, by decide⟩ ⟨12, 2, 0, 1003263, 299874, 1957, 65536⟩
    (by decide) selected_cut_37509

theorem selected_cut_37510 : selected 9 ⟨1003289, by decide⟩
    (prefixPartial 12 299875) = some ⟨12, 2, 0, 1003289, 299875, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_299875_1003289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299875 ⟨1003289, by decide⟩ :=
  accepted_of_selected 12 299875 ⟨1003289, by decide⟩ ⟨12, 2, 0, 1003289, 299875, 1913, 65536⟩
    (by decide) selected_cut_37510

theorem unmarked_context_11_74968_1003290 : frontier 10 ⟨1003290, by decide⟩
    (prefixCache 11 74968) (prefixPartial 11 74968) = false := by
  decide +kernel

theorem node_context_11_74968_1003290 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003290, by decide⟩ =
    .split (coordinate 11) (![⟨1003209, by decide⟩,⟨1003238, by decide⟩,⟨1003263, by decide⟩,⟨1003289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74968_1003290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74968 ⟨1003290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74968
    ⟨1003290, by decide⟩ (by decide) (![⟨1003209, by decide⟩,⟨1003238, by decide⟩,⟨1003263, by decide⟩,⟨1003289, by decide⟩]) unmarked_context_11_74968_1003290 node_context_11_74968_1003290
  intro a
  fin_cases a
  · exact context_12_299872_1003209
  · exact context_12_299873_1003238
  · exact context_12_299874_1003263
  · exact context_12_299875_1003289

theorem selected_cut_37511 : selected 9 ⟨1003317, by decide⟩
    (prefixPartial 12 299876) = some ⟨12, 2, 0, 1003317, 299876, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_299876_1003317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299876 ⟨1003317, by decide⟩ :=
  accepted_of_selected 12 299876 ⟨1003317, by decide⟩ ⟨12, 2, 0, 1003317, 299876, 1869, 65536⟩
    (by decide) selected_cut_37511

theorem selected_cut_37512 : selected 9 ⟨1003371, by decide⟩
    (prefixPartial 12 299877) = some ⟨12, 2, 0, 1003371, 299877, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_299877_1003371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299877 ⟨1003371, by decide⟩ :=
  accepted_of_selected 12 299877 ⟨1003371, by decide⟩ ⟨12, 2, 0, 1003371, 299877, 1273, 65536⟩
    (by decide) selected_cut_37512

theorem selected_cut_37513 : selected 9 ⟨1003392, by decide⟩
    (prefixPartial 12 299878) = some ⟨12, 2, 0, 1003392, 299878, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_299878_1003392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299878 ⟨1003392, by decide⟩ :=
  accepted_of_selected 12 299878 ⟨1003392, by decide⟩ ⟨12, 2, 0, 1003392, 299878, 1801, 65536⟩
    (by decide) selected_cut_37513

theorem selected_cut_37514 : selected 9 ⟨1003416, by decide⟩
    (prefixPartial 12 299879) = some ⟨12, 2, 0, 1003416, 299879, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_299879_1003416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299879 ⟨1003416, by decide⟩ :=
  accepted_of_selected 12 299879 ⟨1003416, by decide⟩ ⟨12, 2, 0, 1003416, 299879, 1913, 65536⟩
    (by decide) selected_cut_37514

theorem unmarked_context_11_74969_1003417 : frontier 10 ⟨1003417, by decide⟩
    (prefixCache 11 74969) (prefixPartial 11 74969) = false := by
  decide +kernel

theorem node_context_11_74969_1003417 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003417, by decide⟩ =
    .split (coordinate 11) (![⟨1003317, by decide⟩,⟨1003371, by decide⟩,⟨1003392, by decide⟩,⟨1003416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74969_1003417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74969 ⟨1003417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74969
    ⟨1003417, by decide⟩ (by decide) (![⟨1003317, by decide⟩,⟨1003371, by decide⟩,⟨1003392, by decide⟩,⟨1003416, by decide⟩]) unmarked_context_11_74969_1003417 node_context_11_74969_1003417
  intro a
  fin_cases a
  · exact context_12_299876_1003317
  · exact context_12_299877_1003371
  · exact context_12_299878_1003392
  · exact context_12_299879_1003416

theorem selected_cut_37515 : selected 9 ⟨1003448, by decide⟩
    (prefixPartial 12 299880) = some ⟨12, 2, 0, 1003448, 299880, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_299880_1003448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299880 ⟨1003448, by decide⟩ :=
  accepted_of_selected 12 299880 ⟨1003448, by decide⟩ ⟨12, 2, 0, 1003448, 299880, 2069, 65536⟩
    (by decide) selected_cut_37515

theorem selected_cut_37516 : selected 9 ⟨1003483, by decide⟩
    (prefixPartial 12 299881) = some ⟨12, 2, 0, 1003483, 299881, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_299881_1003483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299881 ⟨1003483, by decide⟩ :=
  accepted_of_selected 12 299881 ⟨1003483, by decide⟩ ⟨12, 2, 0, 1003483, 299881, 2269, 65536⟩
    (by decide) selected_cut_37516

theorem selected_cut_37517 : selected 9 ⟨1003512, by decide⟩
    (prefixPartial 12 299882) = some ⟨12, 2, 0, 1003512, 299882, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_299882_1003512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299882 ⟨1003512, by decide⟩ :=
  accepted_of_selected 12 299882 ⟨1003512, by decide⟩ ⟨12, 2, 0, 1003512, 299882, 1877, 65536⟩
    (by decide) selected_cut_37517

theorem selected_cut_37518 : selected 9 ⟨1003547, by decide⟩
    (prefixPartial 12 299883) = some ⟨12, 2, 0, 1003547, 299883, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_299883_1003547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299883 ⟨1003547, by decide⟩ :=
  accepted_of_selected 12 299883 ⟨1003547, by decide⟩ ⟨12, 2, 0, 1003547, 299883, 2125, 65536⟩
    (by decide) selected_cut_37518

theorem unmarked_context_11_74970_1003548 : frontier 10 ⟨1003548, by decide⟩
    (prefixCache 11 74970) (prefixPartial 11 74970) = false := by
  decide +kernel

theorem node_context_11_74970_1003548 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003548, by decide⟩ =
    .split (coordinate 11) (![⟨1003448, by decide⟩,⟨1003483, by decide⟩,⟨1003512, by decide⟩,⟨1003547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74970_1003548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74970 ⟨1003548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74970
    ⟨1003548, by decide⟩ (by decide) (![⟨1003448, by decide⟩,⟨1003483, by decide⟩,⟨1003512, by decide⟩,⟨1003547, by decide⟩]) unmarked_context_11_74970_1003548 node_context_11_74970_1003548
  intro a
  fin_cases a
  · exact context_12_299880_1003448
  · exact context_12_299881_1003483
  · exact context_12_299882_1003512
  · exact context_12_299883_1003547

theorem selected_cut_37519 : selected 9 ⟨1003581, by decide⟩
    (prefixPartial 12 299884) = some ⟨12, 2, 0, 1003581, 299884, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_299884_1003581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299884 ⟨1003581, by decide⟩ :=
  accepted_of_selected 12 299884 ⟨1003581, by decide⟩ ⟨12, 2, 0, 1003581, 299884, 1813, 65536⟩
    (by decide) selected_cut_37519

theorem selected_cut_37520 : selected 9 ⟨1003617, by decide⟩
    (prefixPartial 12 299885) = some ⟨12, 2, 0, 1003617, 299885, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_299885_1003617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299885 ⟨1003617, by decide⟩ :=
  accepted_of_selected 12 299885 ⟨1003617, by decide⟩ ⟨12, 2, 0, 1003617, 299885, 2089, 65536⟩
    (by decide) selected_cut_37520

theorem selected_cut_37521 : selected 9 ⟨1003651, by decide⟩
    (prefixPartial 12 299886) = some ⟨12, 2, 0, 1003651, 299886, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_299886_1003651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299886 ⟨1003651, by decide⟩ :=
  accepted_of_selected 12 299886 ⟨1003651, by decide⟩ ⟨12, 2, 0, 1003651, 299886, 1901, 65536⟩
    (by decide) selected_cut_37521

theorem selected_cut_37522 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 299887) = some ⟨12, 1, 0, 903806, 299887, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299887_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299887 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 299887 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 299887, 1, 65536⟩
    (by decide) selected_cut_37522

theorem unmarked_context_11_74971_1003652 : frontier 10 ⟨1003652, by decide⟩
    (prefixCache 11 74971) (prefixPartial 11 74971) = false := by
  decide +kernel

theorem node_context_11_74971_1003652 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003652, by decide⟩ =
    .split (coordinate 11) (![⟨1003581, by decide⟩,⟨1003617, by decide⟩,⟨1003651, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74971_1003652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74971 ⟨1003652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74971
    ⟨1003652, by decide⟩ (by decide) (![⟨1003581, by decide⟩,⟨1003617, by decide⟩,⟨1003651, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_74971_1003652 node_context_11_74971_1003652
  intro a
  fin_cases a
  · exact context_12_299884_1003581
  · exact context_12_299885_1003617
  · exact context_12_299886_1003651
  · exact context_12_299887_903806

theorem unmarked_context_10_18742_1003653 : frontier 11 ⟨1003653, by decide⟩
    (prefixCache 10 18742) (prefixPartial 10 18742) = false := by
  decide +kernel

theorem node_context_10_18742_1003653 : EJMOriginalGlobalDAGData.nodes 11 ⟨1003653, by decide⟩ =
    .split (coordinate 10) (![⟨1003290, by decide⟩,⟨1003417, by decide⟩,⟨1003548, by decide⟩,⟨1003652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18742_1003653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18742 ⟨1003653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18742
    ⟨1003653, by decide⟩ (by decide) (![⟨1003290, by decide⟩,⟨1003417, by decide⟩,⟨1003548, by decide⟩,⟨1003652, by decide⟩]) unmarked_context_10_18742_1003653 node_context_10_18742_1003653
  intro a
  fin_cases a
  · exact context_11_74968_1003290
  · exact context_11_74969_1003417
  · exact context_11_74970_1003548
  · exact context_11_74971_1003652

theorem selected_cut_37523 : selected 9 ⟨1003681, by decide⟩
    (prefixPartial 12 299888) = some ⟨12, 2, 0, 1003681, 299888, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_299888_1003681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299888 ⟨1003681, by decide⟩ :=
  accepted_of_selected 12 299888 ⟨1003681, by decide⟩ ⟨12, 2, 0, 1003681, 299888, 1713, 65536⟩
    (by decide) selected_cut_37523

theorem selected_cut_37524 : selected 9 ⟨1003709, by decide⟩
    (prefixPartial 12 299889) = some ⟨12, 2, 0, 1003709, 299889, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_299889_1003709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299889 ⟨1003709, by decide⟩ :=
  accepted_of_selected 12 299889 ⟨1003709, by decide⟩ ⟨12, 2, 0, 1003709, 299889, 1941, 65536⟩
    (by decide) selected_cut_37524

theorem selected_cut_37525 : selected 9 ⟨1003726, by decide⟩
    (prefixPartial 12 299890) = some ⟨12, 2, 0, 1003726, 299890, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_299890_1003726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299890 ⟨1003726, by decide⟩ :=
  accepted_of_selected 12 299890 ⟨1003726, by decide⟩ ⟨12, 2, 0, 1003726, 299890, 1589, 65536⟩
    (by decide) selected_cut_37525

theorem selected_cut_37526 : selected 9 ⟨1003746, by decide⟩
    (prefixPartial 12 299891) = some ⟨12, 2, 0, 1003746, 299891, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_299891_1003746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299891 ⟨1003746, by decide⟩ :=
  accepted_of_selected 12 299891 ⟨1003746, by decide⟩ ⟨12, 2, 0, 1003746, 299891, 1577, 65536⟩
    (by decide) selected_cut_37526

theorem unmarked_context_11_74972_1003747 : frontier 10 ⟨1003747, by decide⟩
    (prefixCache 11 74972) (prefixPartial 11 74972) = false := by
  decide +kernel

theorem node_context_11_74972_1003747 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003747, by decide⟩ =
    .split (coordinate 11) (![⟨1003681, by decide⟩,⟨1003709, by decide⟩,⟨1003726, by decide⟩,⟨1003746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74972_1003747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74972 ⟨1003747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74972
    ⟨1003747, by decide⟩ (by decide) (![⟨1003681, by decide⟩,⟨1003709, by decide⟩,⟨1003726, by decide⟩,⟨1003746, by decide⟩]) unmarked_context_11_74972_1003747 node_context_11_74972_1003747
  intro a
  fin_cases a
  · exact context_12_299888_1003681
  · exact context_12_299889_1003709
  · exact context_12_299890_1003726
  · exact context_12_299891_1003746

theorem selected_cut_37527 : selected 9 ⟨1003776, by decide⟩
    (prefixPartial 12 299892) = some ⟨12, 2, 0, 1003776, 299892, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_299892_1003776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299892 ⟨1003776, by decide⟩ :=
  accepted_of_selected 12 299892 ⟨1003776, by decide⟩ ⟨12, 2, 0, 1003776, 299892, 1741, 65536⟩
    (by decide) selected_cut_37527

theorem selected_cut_37528 : selected 9 ⟨1003803, by decide⟩
    (prefixPartial 12 299893) = some ⟨12, 2, 0, 1003803, 299893, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_299893_1003803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299893 ⟨1003803, by decide⟩ :=
  accepted_of_selected 12 299893 ⟨1003803, by decide⟩ ⟨12, 2, 0, 1003803, 299893, 1905, 65536⟩
    (by decide) selected_cut_37528

theorem selected_cut_37529 : selected 9 ⟨1003825, by decide⟩
    (prefixPartial 12 299894) = some ⟨12, 2, 0, 1003825, 299894, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_299894_1003825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299894 ⟨1003825, by decide⟩ :=
  accepted_of_selected 12 299894 ⟨1003825, by decide⟩ ⟨12, 2, 0, 1003825, 299894, 1577, 65536⟩
    (by decide) selected_cut_37529

theorem selected_cut_37530 : selected 9 ⟨1003849, by decide⟩
    (prefixPartial 12 299895) = some ⟨12, 2, 0, 1003849, 299895, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_299895_1003849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299895 ⟨1003849, by decide⟩ :=
  accepted_of_selected 12 299895 ⟨1003849, by decide⟩ ⟨12, 2, 0, 1003849, 299895, 1617, 65536⟩
    (by decide) selected_cut_37530

theorem unmarked_context_11_74973_1003850 : frontier 10 ⟨1003850, by decide⟩
    (prefixCache 11 74973) (prefixPartial 11 74973) = false := by
  decide +kernel

theorem node_context_11_74973_1003850 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003850, by decide⟩ =
    .split (coordinate 11) (![⟨1003776, by decide⟩,⟨1003803, by decide⟩,⟨1003825, by decide⟩,⟨1003849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74973_1003850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74973 ⟨1003850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74973
    ⟨1003850, by decide⟩ (by decide) (![⟨1003776, by decide⟩,⟨1003803, by decide⟩,⟨1003825, by decide⟩,⟨1003849, by decide⟩]) unmarked_context_11_74973_1003850 node_context_11_74973_1003850
  intro a
  fin_cases a
  · exact context_12_299892_1003776
  · exact context_12_299893_1003803
  · exact context_12_299894_1003825
  · exact context_12_299895_1003849

theorem selected_cut_37531 : selected 9 ⟨1003879, by decide⟩
    (prefixPartial 12 299896) = some ⟨12, 2, 0, 1003879, 299896, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_299896_1003879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299896 ⟨1003879, by decide⟩ :=
  accepted_of_selected 12 299896 ⟨1003879, by decide⟩ ⟨12, 2, 0, 1003879, 299896, 1853, 65536⟩
    (by decide) selected_cut_37531

theorem selected_cut_37532 : selected 9 ⟨1003909, by decide⟩
    (prefixPartial 12 299897) = some ⟨12, 2, 0, 1003909, 299897, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_299897_1003909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299897 ⟨1003909, by decide⟩ :=
  accepted_of_selected 12 299897 ⟨1003909, by decide⟩ ⟨12, 2, 0, 1003909, 299897, 2025, 65536⟩
    (by decide) selected_cut_37532

theorem selected_cut_37533 : selected 9 ⟨1003937, by decide⟩
    (prefixPartial 12 299898) = some ⟨12, 2, 0, 1003937, 299898, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_299898_1003937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299898 ⟨1003937, by decide⟩ :=
  accepted_of_selected 12 299898 ⟨1003937, by decide⟩ ⟨12, 2, 0, 1003937, 299898, 1613, 65536⟩
    (by decide) selected_cut_37533

theorem selected_cut_37534 : selected 9 ⟨1003963, by decide⟩
    (prefixPartial 12 299899) = some ⟨12, 2, 0, 1003963, 299899, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_299899_1003963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299899 ⟨1003963, by decide⟩ :=
  accepted_of_selected 12 299899 ⟨1003963, by decide⟩ ⟨12, 2, 0, 1003963, 299899, 1725, 65536⟩
    (by decide) selected_cut_37534

theorem unmarked_context_11_74974_1003964 : frontier 10 ⟨1003964, by decide⟩
    (prefixCache 11 74974) (prefixPartial 11 74974) = false := by
  decide +kernel

theorem node_context_11_74974_1003964 : EJMOriginalGlobalDAGData.nodes 10 ⟨1003964, by decide⟩ =
    .split (coordinate 11) (![⟨1003879, by decide⟩,⟨1003909, by decide⟩,⟨1003937, by decide⟩,⟨1003963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74974_1003964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74974 ⟨1003964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74974
    ⟨1003964, by decide⟩ (by decide) (![⟨1003879, by decide⟩,⟨1003909, by decide⟩,⟨1003937, by decide⟩,⟨1003963, by decide⟩]) unmarked_context_11_74974_1003964 node_context_11_74974_1003964
  intro a
  fin_cases a
  · exact context_12_299896_1003879
  · exact context_12_299897_1003909
  · exact context_12_299898_1003937
  · exact context_12_299899_1003963

theorem selected_cut_37535 : selected 9 ⟨1003994, by decide⟩
    (prefixPartial 12 299900) = some ⟨12, 2, 0, 1003994, 299900, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_299900_1003994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299900 ⟨1003994, by decide⟩ :=
  accepted_of_selected 12 299900 ⟨1003994, by decide⟩ ⟨12, 2, 0, 1003994, 299900, 1693, 65536⟩
    (by decide) selected_cut_37535

theorem selected_cut_37536 : selected 9 ⟨1004043, by decide⟩
    (prefixPartial 12 299901) = some ⟨12, 2, 0, 1004043, 299901, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_299901_1004043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299901 ⟨1004043, by decide⟩ :=
  accepted_of_selected 12 299901 ⟨1004043, by decide⟩ ⟨12, 2, 0, 1004043, 299901, 1945, 65536⟩
    (by decide) selected_cut_37536

theorem selected_cut_37537 : selected 9 ⟨1004069, by decide⟩
    (prefixPartial 12 299902) = some ⟨12, 2, 0, 1004069, 299902, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_299902_1004069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299902 ⟨1004069, by decide⟩ :=
  accepted_of_selected 12 299902 ⟨1004069, by decide⟩ ⟨12, 2, 0, 1004069, 299902, 1629, 65536⟩
    (by decide) selected_cut_37537

theorem selected_cut_37538 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 299903) = some ⟨12, 1, 0, 429285, 299903, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299903_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299903 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 299903 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 299903, 1, 65536⟩
    (by decide) selected_cut_37538

theorem unmarked_context_11_74975_1004070 : frontier 10 ⟨1004070, by decide⟩
    (prefixCache 11 74975) (prefixPartial 11 74975) = false := by
  decide +kernel

theorem node_context_11_74975_1004070 : EJMOriginalGlobalDAGData.nodes 10 ⟨1004070, by decide⟩ =
    .split (coordinate 11) (![⟨1003994, by decide⟩,⟨1004043, by decide⟩,⟨1004069, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74975_1004070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74975 ⟨1004070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74975
    ⟨1004070, by decide⟩ (by decide) (![⟨1003994, by decide⟩,⟨1004043, by decide⟩,⟨1004069, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_74975_1004070 node_context_11_74975_1004070
  intro a
  fin_cases a
  · exact context_12_299900_1003994
  · exact context_12_299901_1004043
  · exact context_12_299902_1004069
  · exact context_12_299903_429285

theorem unmarked_context_10_18743_1004071 : frontier 11 ⟨1004071, by decide⟩
    (prefixCache 10 18743) (prefixPartial 10 18743) = false := by
  decide +kernel

theorem node_context_10_18743_1004071 : EJMOriginalGlobalDAGData.nodes 11 ⟨1004071, by decide⟩ =
    .split (coordinate 10) (![⟨1003747, by decide⟩,⟨1003850, by decide⟩,⟨1003964, by decide⟩,⟨1004070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18743_1004071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18743 ⟨1004071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18743
    ⟨1004071, by decide⟩ (by decide) (![⟨1003747, by decide⟩,⟨1003850, by decide⟩,⟨1003964, by decide⟩,⟨1004070, by decide⟩]) unmarked_context_10_18743_1004071 node_context_10_18743_1004071
  intro a
  fin_cases a
  · exact context_11_74972_1003747
  · exact context_11_74973_1003850
  · exact context_11_74974_1003964
  · exact context_11_74975_1004070

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
