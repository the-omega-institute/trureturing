/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover295
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28420 : selected 8 ⟨717896, by decide⟩
    (prefixPartial 13 369787) = some ⟨13, 2, 0, 717896, 369787, 901, 16384⟩ := by
  decide +kernel

theorem context_13_369787_717896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369787 ⟨717896, by decide⟩ :=
  accepted_of_selected 13 369787 ⟨717896, by decide⟩ ⟨13, 2, 0, 717896, 369787, 901, 16384⟩
    (by decide) selected_cut_28420

theorem unmarked_context_12_92446_717897 : frontier 9 ⟨717897, by decide⟩
    (prefixCache 12 92446) (prefixPartial 12 92446) = false := by
  decide +kernel

theorem node_context_12_92446_717897 : EJMOriginalGlobalDAGData.nodes 9 ⟨717897, by decide⟩ =
    .split (coordinate 12) (![⟨717848, by decide⟩,⟨717868, by decide⟩,⟨717888, by decide⟩,⟨717896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92446_717897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92446 ⟨717897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92446
    ⟨717897, by decide⟩ (by decide) (![⟨717848, by decide⟩,⟨717868, by decide⟩,⟨717888, by decide⟩,⟨717896, by decide⟩]) unmarked_context_12_92446_717897 node_context_12_92446_717897
  intro a
  fin_cases a
  · exact context_13_369784_717848
  · exact context_13_369785_717868
  · exact context_13_369786_717888
  · exact context_13_369787_717896

theorem selected_cut_28421 : selected 8 ⟨717922, by decide⟩
    (prefixPartial 13 369788) = some ⟨13, 2, 0, 717922, 369788, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_369788_717922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369788 ⟨717922, by decide⟩ :=
  accepted_of_selected 13 369788 ⟨717922, by decide⟩ ⟨13, 2, 0, 717922, 369788, 1441, 16384⟩
    (by decide) selected_cut_28421

theorem selected_cut_28422 : selected 8 ⟨717945, by decide⟩
    (prefixPartial 13 369789) = some ⟨13, 2, 0, 717945, 369789, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_369789_717945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369789 ⟨717945, by decide⟩ :=
  accepted_of_selected 13 369789 ⟨717945, by decide⟩ ⟨13, 2, 0, 717945, 369789, 1833, 16384⟩
    (by decide) selected_cut_28422

theorem selected_cut_28423 : selected 8 ⟨717964, by decide⟩
    (prefixPartial 13 369790) = some ⟨13, 2, 0, 717964, 369790, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_369790_717964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369790 ⟨717964, by decide⟩ :=
  accepted_of_selected 13 369790 ⟨717964, by decide⟩ ⟨13, 2, 0, 717964, 369790, 1409, 16384⟩
    (by decide) selected_cut_28423

theorem selected_cut_28424 : selected 8 ⟨717968, by decide⟩
    (prefixPartial 13 369791) = some ⟨13, 2, 0, 717968, 369791, 861, 16384⟩ := by
  decide +kernel

theorem context_13_369791_717968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369791 ⟨717968, by decide⟩ :=
  accepted_of_selected 13 369791 ⟨717968, by decide⟩ ⟨13, 2, 0, 717968, 369791, 861, 16384⟩
    (by decide) selected_cut_28424

theorem unmarked_context_12_92447_717969 : frontier 9 ⟨717969, by decide⟩
    (prefixCache 12 92447) (prefixPartial 12 92447) = false := by
  decide +kernel

theorem node_context_12_92447_717969 : EJMOriginalGlobalDAGData.nodes 9 ⟨717969, by decide⟩ =
    .split (coordinate 12) (![⟨717922, by decide⟩,⟨717945, by decide⟩,⟨717964, by decide⟩,⟨717968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92447_717969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92447 ⟨717969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92447
    ⟨717969, by decide⟩ (by decide) (![⟨717922, by decide⟩,⟨717945, by decide⟩,⟨717964, by decide⟩,⟨717968, by decide⟩]) unmarked_context_12_92447_717969 node_context_12_92447_717969
  intro a
  fin_cases a
  · exact context_13_369788_717922
  · exact context_13_369789_717945
  · exact context_13_369790_717964
  · exact context_13_369791_717968

theorem unmarked_context_11_23111_717970 : frontier 10 ⟨717970, by decide⟩
    (prefixCache 11 23111) (prefixPartial 11 23111) = false := by
  decide +kernel

theorem node_context_11_23111_717970 : EJMOriginalGlobalDAGData.nodes 10 ⟨717970, by decide⟩ =
    .split (coordinate 11) (![⟨717769, by decide⟩,⟨717832, by decide⟩,⟨717897, by decide⟩,⟨717969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23111_717970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23111 ⟨717970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23111
    ⟨717970, by decide⟩ (by decide) (![⟨717769, by decide⟩,⟨717832, by decide⟩,⟨717897, by decide⟩,⟨717969, by decide⟩]) unmarked_context_11_23111_717970 node_context_11_23111_717970
  intro a
  fin_cases a
  · exact context_12_92444_717769
  · exact context_12_92445_717832
  · exact context_12_92446_717897
  · exact context_12_92447_717969

theorem unmarked_context_10_5777_717971 : frontier 11 ⟨717971, by decide⟩
    (prefixCache 10 5777) (prefixPartial 10 5777) = false := by
  decide +kernel

theorem node_context_10_5777_717971 : EJMOriginalGlobalDAGData.nodes 11 ⟨717971, by decide⟩ =
    .split (coordinate 10) (![⟨717265, by decide⟩,⟨717453, by decide⟩,⟨717706, by decide⟩,⟨717970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5777_717971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5777 ⟨717971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5777
    ⟨717971, by decide⟩ (by decide) (![⟨717265, by decide⟩,⟨717453, by decide⟩,⟨717706, by decide⟩,⟨717970, by decide⟩]) unmarked_context_10_5777_717971 node_context_10_5777_717971
  intro a
  fin_cases a
  · exact context_11_23108_717265
  · exact context_11_23109_717453
  · exact context_11_23110_717706
  · exact context_11_23111_717970

theorem selected_cut_28425 : selected 8 ⟨717987, by decide⟩
    (prefixPartial 13 369792) = some ⟨13, 2, 0, 717987, 369792, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_369792_717987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369792 ⟨717987, by decide⟩ :=
  accepted_of_selected 13 369792 ⟨717987, by decide⟩ ⟨13, 2, 0, 717987, 369792, 1369, 16384⟩
    (by decide) selected_cut_28425

theorem selected_cut_28426 : selected 8 ⟨718008, by decide⟩
    (prefixPartial 13 369793) = some ⟨13, 2, 0, 718008, 369793, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_369793_718008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369793 ⟨718008, by decide⟩ :=
  accepted_of_selected 13 369793 ⟨718008, by decide⟩ ⟨13, 2, 0, 718008, 369793, 1493, 16384⟩
    (by decide) selected_cut_28426

theorem selected_cut_28427 : selected 8 ⟨718024, by decide⟩
    (prefixPartial 13 369794) = some ⟨13, 2, 0, 718024, 369794, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_369794_718024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369794 ⟨718024, by decide⟩ :=
  accepted_of_selected 13 369794 ⟨718024, by decide⟩ ⟨13, 2, 0, 718024, 369794, 1209, 16384⟩
    (by decide) selected_cut_28427

theorem selected_cut_28428 : selected 8 ⟨718034, by decide⟩
    (prefixPartial 13 369795) = some ⟨13, 2, 0, 718034, 369795, 825, 16384⟩ := by
  decide +kernel

theorem context_13_369795_718034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369795 ⟨718034, by decide⟩ :=
  accepted_of_selected 13 369795 ⟨718034, by decide⟩ ⟨13, 2, 0, 718034, 369795, 825, 16384⟩
    (by decide) selected_cut_28428

theorem unmarked_context_12_92448_718035 : frontier 9 ⟨718035, by decide⟩
    (prefixCache 12 92448) (prefixPartial 12 92448) = false := by
  decide +kernel

theorem node_context_12_92448_718035 : EJMOriginalGlobalDAGData.nodes 9 ⟨718035, by decide⟩ =
    .split (coordinate 12) (![⟨717987, by decide⟩,⟨718008, by decide⟩,⟨718024, by decide⟩,⟨718034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92448_718035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92448 ⟨718035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92448
    ⟨718035, by decide⟩ (by decide) (![⟨717987, by decide⟩,⟨718008, by decide⟩,⟨718024, by decide⟩,⟨718034, by decide⟩]) unmarked_context_12_92448_718035 node_context_12_92448_718035
  intro a
  fin_cases a
  · exact context_13_369792_717987
  · exact context_13_369793_718008
  · exact context_13_369794_718024
  · exact context_13_369795_718034

theorem selected_cut_28429 : selected 8 ⟨718050, by decide⟩
    (prefixPartial 13 369796) = some ⟨13, 2, 0, 718050, 369796, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_369796_718050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369796 ⟨718050, by decide⟩ :=
  accepted_of_selected 13 369796 ⟨718050, by decide⟩ ⟨13, 2, 0, 718050, 369796, 1165, 16384⟩
    (by decide) selected_cut_28429

theorem selected_cut_28430 : selected 8 ⟨718071, by decide⟩
    (prefixPartial 13 369797) = some ⟨13, 2, 0, 718071, 369797, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_369797_718071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369797 ⟨718071, by decide⟩ :=
  accepted_of_selected 13 369797 ⟨718071, by decide⟩ ⟨13, 2, 0, 718071, 369797, 1269, 16384⟩
    (by decide) selected_cut_28430

theorem selected_cut_28431 : selected 8 ⟨718089, by decide⟩
    (prefixPartial 13 369798) = some ⟨13, 2, 0, 718089, 369798, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_369798_718089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369798 ⟨718089, by decide⟩ :=
  accepted_of_selected 13 369798 ⟨718089, by decide⟩ ⟨13, 2, 0, 718089, 369798, 1181, 16384⟩
    (by decide) selected_cut_28431

theorem selected_cut_28432 : selected 8 ⟨718096, by decide⟩
    (prefixPartial 13 369799) = some ⟨13, 2, 0, 718096, 369799, 745, 16384⟩ := by
  decide +kernel

theorem context_13_369799_718096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369799 ⟨718096, by decide⟩ :=
  accepted_of_selected 13 369799 ⟨718096, by decide⟩ ⟨13, 2, 0, 718096, 369799, 745, 16384⟩
    (by decide) selected_cut_28432

theorem unmarked_context_12_92449_718097 : frontier 9 ⟨718097, by decide⟩
    (prefixCache 12 92449) (prefixPartial 12 92449) = false := by
  decide +kernel

theorem node_context_12_92449_718097 : EJMOriginalGlobalDAGData.nodes 9 ⟨718097, by decide⟩ =
    .split (coordinate 12) (![⟨718050, by decide⟩,⟨718071, by decide⟩,⟨718089, by decide⟩,⟨718096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92449_718097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92449 ⟨718097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92449
    ⟨718097, by decide⟩ (by decide) (![⟨718050, by decide⟩,⟨718071, by decide⟩,⟨718089, by decide⟩,⟨718096, by decide⟩]) unmarked_context_12_92449_718097 node_context_12_92449_718097
  intro a
  fin_cases a
  · exact context_13_369796_718050
  · exact context_13_369797_718071
  · exact context_13_369798_718089
  · exact context_13_369799_718096

theorem selected_cut_28433 : selected 8 ⟨718112, by decide⟩
    (prefixPartial 13 369800) = some ⟨13, 2, 0, 718112, 369800, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_369800_718112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369800 ⟨718112, by decide⟩ :=
  accepted_of_selected 13 369800 ⟨718112, by decide⟩ ⟨13, 2, 0, 718112, 369800, 1185, 16384⟩
    (by decide) selected_cut_28433

theorem selected_cut_28434 : selected 8 ⟨718133, by decide⟩
    (prefixPartial 13 369801) = some ⟨13, 2, 0, 718133, 369801, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_369801_718133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369801 ⟨718133, by decide⟩ :=
  accepted_of_selected 13 369801 ⟨718133, by decide⟩ ⟨13, 2, 0, 718133, 369801, 1593, 16384⟩
    (by decide) selected_cut_28434

theorem selected_cut_28435 : selected 8 ⟨718148, by decide⟩
    (prefixPartial 13 369802) = some ⟨13, 2, 0, 718148, 369802, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_369802_718148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369802 ⟨718148, by decide⟩ :=
  accepted_of_selected 13 369802 ⟨718148, by decide⟩ ⟨13, 2, 0, 718148, 369802, 1169, 16384⟩
    (by decide) selected_cut_28435

theorem selected_cut_28436 : selected 8 ⟨718163, by decide⟩
    (prefixPartial 13 369803) = some ⟨13, 2, 0, 718163, 369803, 889, 16384⟩ := by
  decide +kernel

theorem context_13_369803_718163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369803 ⟨718163, by decide⟩ :=
  accepted_of_selected 13 369803 ⟨718163, by decide⟩ ⟨13, 2, 0, 718163, 369803, 889, 16384⟩
    (by decide) selected_cut_28436

theorem unmarked_context_12_92450_718164 : frontier 9 ⟨718164, by decide⟩
    (prefixCache 12 92450) (prefixPartial 12 92450) = false := by
  decide +kernel

theorem node_context_12_92450_718164 : EJMOriginalGlobalDAGData.nodes 9 ⟨718164, by decide⟩ =
    .split (coordinate 12) (![⟨718112, by decide⟩,⟨718133, by decide⟩,⟨718148, by decide⟩,⟨718163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92450_718164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92450 ⟨718164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92450
    ⟨718164, by decide⟩ (by decide) (![⟨718112, by decide⟩,⟨718133, by decide⟩,⟨718148, by decide⟩,⟨718163, by decide⟩]) unmarked_context_12_92450_718164 node_context_12_92450_718164
  intro a
  fin_cases a
  · exact context_13_369800_718112
  · exact context_13_369801_718133
  · exact context_13_369802_718148
  · exact context_13_369803_718163

theorem selected_cut_28437 : selected 8 ⟨718181, by decide⟩
    (prefixPartial 13 369804) = some ⟨13, 2, 0, 718181, 369804, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_369804_718181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369804 ⟨718181, by decide⟩ :=
  accepted_of_selected 13 369804 ⟨718181, by decide⟩ ⟨13, 2, 0, 718181, 369804, 1245, 16384⟩
    (by decide) selected_cut_28437

theorem selected_cut_28438 : selected 8 ⟨718206, by decide⟩
    (prefixPartial 13 369805) = some ⟨13, 2, 0, 718206, 369805, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_369805_718206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369805 ⟨718206, by decide⟩ :=
  accepted_of_selected 13 369805 ⟨718206, by decide⟩ ⟨13, 2, 0, 718206, 369805, 1633, 16384⟩
    (by decide) selected_cut_28438

theorem selected_cut_28439 : selected 8 ⟨718222, by decide⟩
    (prefixPartial 13 369806) = some ⟨13, 2, 0, 718222, 369806, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_369806_718222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369806 ⟨718222, by decide⟩ :=
  accepted_of_selected 13 369806 ⟨718222, by decide⟩ ⟨13, 2, 0, 718222, 369806, 1233, 16384⟩
    (by decide) selected_cut_28439

theorem selected_cut_28440 : selected 8 ⟨718230, by decide⟩
    (prefixPartial 13 369807) = some ⟨13, 2, 0, 718230, 369807, 837, 16384⟩ := by
  decide +kernel

theorem context_13_369807_718230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369807 ⟨718230, by decide⟩ :=
  accepted_of_selected 13 369807 ⟨718230, by decide⟩ ⟨13, 2, 0, 718230, 369807, 837, 16384⟩
    (by decide) selected_cut_28440

theorem unmarked_context_12_92451_718231 : frontier 9 ⟨718231, by decide⟩
    (prefixCache 12 92451) (prefixPartial 12 92451) = false := by
  decide +kernel

theorem node_context_12_92451_718231 : EJMOriginalGlobalDAGData.nodes 9 ⟨718231, by decide⟩ =
    .split (coordinate 12) (![⟨718181, by decide⟩,⟨718206, by decide⟩,⟨718222, by decide⟩,⟨718230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92451_718231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92451 ⟨718231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92451
    ⟨718231, by decide⟩ (by decide) (![⟨718181, by decide⟩,⟨718206, by decide⟩,⟨718222, by decide⟩,⟨718230, by decide⟩]) unmarked_context_12_92451_718231 node_context_12_92451_718231
  intro a
  fin_cases a
  · exact context_13_369804_718181
  · exact context_13_369805_718206
  · exact context_13_369806_718222
  · exact context_13_369807_718230

theorem unmarked_context_11_23112_718232 : frontier 10 ⟨718232, by decide⟩
    (prefixCache 11 23112) (prefixPartial 11 23112) = false := by
  decide +kernel

theorem node_context_11_23112_718232 : EJMOriginalGlobalDAGData.nodes 10 ⟨718232, by decide⟩ =
    .split (coordinate 11) (![⟨718035, by decide⟩,⟨718097, by decide⟩,⟨718164, by decide⟩,⟨718231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23112_718232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23112 ⟨718232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23112
    ⟨718232, by decide⟩ (by decide) (![⟨718035, by decide⟩,⟨718097, by decide⟩,⟨718164, by decide⟩,⟨718231, by decide⟩]) unmarked_context_11_23112_718232 node_context_11_23112_718232
  intro a
  fin_cases a
  · exact context_12_92448_718035
  · exact context_12_92449_718097
  · exact context_12_92450_718164
  · exact context_12_92451_718231

theorem selected_cut_28441 : selected 8 ⟨718249, by decide⟩
    (prefixPartial 13 369808) = some ⟨13, 2, 0, 718249, 369808, 981, 16384⟩ := by
  decide +kernel

theorem context_13_369808_718249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369808 ⟨718249, by decide⟩ :=
  accepted_of_selected 13 369808 ⟨718249, by decide⟩ ⟨13, 2, 0, 718249, 369808, 981, 16384⟩
    (by decide) selected_cut_28441

theorem selected_cut_28442 : selected 8 ⟨718269, by decide⟩
    (prefixPartial 13 369809) = some ⟨13, 2, 0, 718269, 369809, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_369809_718269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369809 ⟨718269, by decide⟩ :=
  accepted_of_selected 13 369809 ⟨718269, by decide⟩ ⟨13, 2, 0, 718269, 369809, 1389, 16384⟩
    (by decide) selected_cut_28442

theorem selected_cut_28443 : selected 8 ⟨718283, by decide⟩
    (prefixPartial 13 369810) = some ⟨13, 2, 0, 718283, 369810, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_369810_718283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369810 ⟨718283, by decide⟩ :=
  accepted_of_selected 13 369810 ⟨718283, by decide⟩ ⟨13, 2, 0, 718283, 369810, 1101, 16384⟩
    (by decide) selected_cut_28443

theorem selected_cut_28444 : selected 8 ⟨718290, by decide⟩
    (prefixPartial 13 369811) = some ⟨13, 2, 0, 718290, 369811, 837, 16384⟩ := by
  decide +kernel

theorem context_13_369811_718290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369811 ⟨718290, by decide⟩ :=
  accepted_of_selected 13 369811 ⟨718290, by decide⟩ ⟨13, 2, 0, 718290, 369811, 837, 16384⟩
    (by decide) selected_cut_28444

theorem unmarked_context_12_92452_718291 : frontier 9 ⟨718291, by decide⟩
    (prefixCache 12 92452) (prefixPartial 12 92452) = false := by
  decide +kernel

theorem node_context_12_92452_718291 : EJMOriginalGlobalDAGData.nodes 9 ⟨718291, by decide⟩ =
    .split (coordinate 12) (![⟨718249, by decide⟩,⟨718269, by decide⟩,⟨718283, by decide⟩,⟨718290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92452_718291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92452 ⟨718291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92452
    ⟨718291, by decide⟩ (by decide) (![⟨718249, by decide⟩,⟨718269, by decide⟩,⟨718283, by decide⟩,⟨718290, by decide⟩]) unmarked_context_12_92452_718291 node_context_12_92452_718291
  intro a
  fin_cases a
  · exact context_13_369808_718249
  · exact context_13_369809_718269
  · exact context_13_369810_718283
  · exact context_13_369811_718290

theorem selected_cut_28445 : selected 9 ⟨234650, by decide⟩
    (prefixPartial 12 92453) = some ⟨12, 1, 0, 234650, 92453, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92453_234650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92453 ⟨234650, by decide⟩ :=
  accepted_of_selected 12 92453 ⟨234650, by decide⟩ ⟨12, 1, 0, 234650, 92453, 1, 65536⟩
    (by decide) selected_cut_28445

theorem selected_cut_28446 : selected 8 ⟨718306, by decide⟩
    (prefixPartial 13 369816) = some ⟨13, 2, 0, 718306, 369816, 941, 16384⟩ := by
  decide +kernel

theorem context_13_369816_718306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369816 ⟨718306, by decide⟩ :=
  accepted_of_selected 13 369816 ⟨718306, by decide⟩ ⟨13, 2, 0, 718306, 369816, 941, 16384⟩
    (by decide) selected_cut_28446

theorem selected_cut_28447 : selected 8 ⟨718326, by decide⟩
    (prefixPartial 13 369817) = some ⟨13, 2, 0, 718326, 369817, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_369817_718326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369817 ⟨718326, by decide⟩ :=
  accepted_of_selected 13 369817 ⟨718326, by decide⟩ ⟨13, 2, 0, 718326, 369817, 1349, 16384⟩
    (by decide) selected_cut_28447

theorem selected_cut_28448 : selected 8 ⟨718339, by decide⟩
    (prefixPartial 13 369818) = some ⟨13, 2, 0, 718339, 369818, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_369818_718339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369818 ⟨718339, by decide⟩ :=
  accepted_of_selected 13 369818 ⟨718339, by decide⟩ ⟨13, 2, 0, 718339, 369818, 1085, 16384⟩
    (by decide) selected_cut_28448

theorem selected_cut_28449 : selected 8 ⟨718344, by decide⟩
    (prefixPartial 13 369819) = some ⟨13, 2, 0, 718344, 369819, 917, 16384⟩ := by
  decide +kernel

theorem context_13_369819_718344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369819 ⟨718344, by decide⟩ :=
  accepted_of_selected 13 369819 ⟨718344, by decide⟩ ⟨13, 2, 0, 718344, 369819, 917, 16384⟩
    (by decide) selected_cut_28449

theorem unmarked_context_12_92454_718345 : frontier 9 ⟨718345, by decide⟩
    (prefixCache 12 92454) (prefixPartial 12 92454) = false := by
  decide +kernel

theorem node_context_12_92454_718345 : EJMOriginalGlobalDAGData.nodes 9 ⟨718345, by decide⟩ =
    .split (coordinate 12) (![⟨718306, by decide⟩,⟨718326, by decide⟩,⟨718339, by decide⟩,⟨718344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92454_718345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92454 ⟨718345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92454
    ⟨718345, by decide⟩ (by decide) (![⟨718306, by decide⟩,⟨718326, by decide⟩,⟨718339, by decide⟩,⟨718344, by decide⟩]) unmarked_context_12_92454_718345 node_context_12_92454_718345
  intro a
  fin_cases a
  · exact context_13_369816_718306
  · exact context_13_369817_718326
  · exact context_13_369818_718339
  · exact context_13_369819_718344

theorem selected_cut_28450 : selected 8 ⟨718358, by decide⟩
    (prefixPartial 13 369820) = some ⟨13, 2, 0, 718358, 369820, 941, 16384⟩ := by
  decide +kernel

theorem context_13_369820_718358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369820 ⟨718358, by decide⟩ :=
  accepted_of_selected 13 369820 ⟨718358, by decide⟩ ⟨13, 2, 0, 718358, 369820, 941, 16384⟩
    (by decide) selected_cut_28450

theorem selected_cut_28451 : selected 8 ⟨718378, by decide⟩
    (prefixPartial 13 369821) = some ⟨13, 2, 0, 718378, 369821, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_369821_718378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369821 ⟨718378, by decide⟩ :=
  accepted_of_selected 13 369821 ⟨718378, by decide⟩ ⟨13, 2, 0, 718378, 369821, 1433, 16384⟩
    (by decide) selected_cut_28451

theorem selected_cut_28452 : selected 8 ⟨718397, by decide⟩
    (prefixPartial 13 369822) = some ⟨13, 2, 0, 718397, 369822, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_369822_718397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369822 ⟨718397, by decide⟩ :=
  accepted_of_selected 13 369822 ⟨718397, by decide⟩ ⟨13, 2, 0, 718397, 369822, 1229, 16384⟩
    (by decide) selected_cut_28452

theorem selected_cut_28453 : selected 8 ⟨718403, by decide⟩
    (prefixPartial 13 369823) = some ⟨13, 2, 0, 718403, 369823, 781, 16384⟩ := by
  decide +kernel

theorem context_13_369823_718403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369823 ⟨718403, by decide⟩ :=
  accepted_of_selected 13 369823 ⟨718403, by decide⟩ ⟨13, 2, 0, 718403, 369823, 781, 16384⟩
    (by decide) selected_cut_28453

theorem unmarked_context_12_92455_718404 : frontier 9 ⟨718404, by decide⟩
    (prefixCache 12 92455) (prefixPartial 12 92455) = false := by
  decide +kernel

theorem node_context_12_92455_718404 : EJMOriginalGlobalDAGData.nodes 9 ⟨718404, by decide⟩ =
    .split (coordinate 12) (![⟨718358, by decide⟩,⟨718378, by decide⟩,⟨718397, by decide⟩,⟨718403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92455_718404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92455 ⟨718404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92455
    ⟨718404, by decide⟩ (by decide) (![⟨718358, by decide⟩,⟨718378, by decide⟩,⟨718397, by decide⟩,⟨718403, by decide⟩]) unmarked_context_12_92455_718404 node_context_12_92455_718404
  intro a
  fin_cases a
  · exact context_13_369820_718358
  · exact context_13_369821_718378
  · exact context_13_369822_718397
  · exact context_13_369823_718403

theorem unmarked_context_11_23113_718405 : frontier 10 ⟨718405, by decide⟩
    (prefixCache 11 23113) (prefixPartial 11 23113) = false := by
  decide +kernel

theorem node_context_11_23113_718405 : EJMOriginalGlobalDAGData.nodes 10 ⟨718405, by decide⟩ =
    .split (coordinate 11) (![⟨718291, by decide⟩,⟨234650, by decide⟩,⟨718345, by decide⟩,⟨718404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23113_718405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23113 ⟨718405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23113
    ⟨718405, by decide⟩ (by decide) (![⟨718291, by decide⟩,⟨234650, by decide⟩,⟨718345, by decide⟩,⟨718404, by decide⟩]) unmarked_context_11_23113_718405 node_context_11_23113_718405
  intro a
  fin_cases a
  · exact context_12_92452_718291
  · exact context_12_92453_234650
  · exact context_12_92454_718345
  · exact context_12_92455_718404

theorem selected_cut_28454 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 92456) = some ⟨12, 1, 0, 224365, 92456, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92456_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92456 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 92456 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 92456, 1, 65536⟩
    (by decide) selected_cut_28454

theorem selected_cut_28455 : selected 9 ⟨718521, by decide⟩
    (prefixPartial 12 92457) = some ⟨12, 2, 0, 718521, 92457, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_92457_718521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92457 ⟨718521, by decide⟩ :=
  accepted_of_selected 12 92457 ⟨718521, by decide⟩ ⟨12, 2, 0, 718521, 92457, 3413, 65536⟩
    (by decide) selected_cut_28455

theorem selected_cut_28456 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 92458) = some ⟨12, 1, 0, 224365, 92458, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92458_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92458 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 92458 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 92458, 1, 65536⟩
    (by decide) selected_cut_28456

theorem selected_cut_28457 : selected 8 ⟨718541, by decide⟩
    (prefixPartial 13 369836) = some ⟨13, 2, 0, 718541, 369836, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_369836_718541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369836 ⟨718541, by decide⟩ :=
  accepted_of_selected 13 369836 ⟨718541, by decide⟩ ⟨13, 2, 0, 718541, 369836, 1289, 16384⟩
    (by decide) selected_cut_28457

theorem selected_cut_28458 : selected 8 ⟨718564, by decide⟩
    (prefixPartial 13 369837) = some ⟨13, 2, 0, 718564, 369837, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_369837_718564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369837 ⟨718564, by decide⟩ :=
  accepted_of_selected 13 369837 ⟨718564, by decide⟩ ⟨13, 2, 0, 718564, 369837, 2241, 16384⟩
    (by decide) selected_cut_28458

theorem selected_cut_28459 : selected 8 ⟨718584, by decide⟩
    (prefixPartial 13 369838) = some ⟨13, 2, 0, 718584, 369838, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_369838_718584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369838 ⟨718584, by decide⟩ :=
  accepted_of_selected 13 369838 ⟨718584, by decide⟩ ⟨13, 2, 0, 718584, 369838, 1725, 16384⟩
    (by decide) selected_cut_28459

theorem selected_cut_28460 : selected 8 ⟨718591, by decide⟩
    (prefixPartial 13 369839) = some ⟨13, 2, 0, 718591, 369839, 993, 16384⟩ := by
  decide +kernel

theorem context_13_369839_718591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369839 ⟨718591, by decide⟩ :=
  accepted_of_selected 13 369839 ⟨718591, by decide⟩ ⟨13, 2, 0, 718591, 369839, 993, 16384⟩
    (by decide) selected_cut_28460

theorem unmarked_context_12_92459_718592 : frontier 9 ⟨718592, by decide⟩
    (prefixCache 12 92459) (prefixPartial 12 92459) = false := by
  decide +kernel

theorem node_context_12_92459_718592 : EJMOriginalGlobalDAGData.nodes 9 ⟨718592, by decide⟩ =
    .split (coordinate 12) (![⟨718541, by decide⟩,⟨718564, by decide⟩,⟨718584, by decide⟩,⟨718591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92459_718592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92459 ⟨718592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92459
    ⟨718592, by decide⟩ (by decide) (![⟨718541, by decide⟩,⟨718564, by decide⟩,⟨718584, by decide⟩,⟨718591, by decide⟩]) unmarked_context_12_92459_718592 node_context_12_92459_718592
  intro a
  fin_cases a
  · exact context_13_369836_718541
  · exact context_13_369837_718564
  · exact context_13_369838_718584
  · exact context_13_369839_718591

theorem unmarked_context_11_23114_718593 : frontier 10 ⟨718593, by decide⟩
    (prefixCache 11 23114) (prefixPartial 11 23114) = false := by
  decide +kernel

theorem node_context_11_23114_718593 : EJMOriginalGlobalDAGData.nodes 10 ⟨718593, by decide⟩ =
    .split (coordinate 11) (![⟨224365, by decide⟩,⟨718521, by decide⟩,⟨224365, by decide⟩,⟨718592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23114_718593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23114 ⟨718593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23114
    ⟨718593, by decide⟩ (by decide) (![⟨224365, by decide⟩,⟨718521, by decide⟩,⟨224365, by decide⟩,⟨718592, by decide⟩]) unmarked_context_11_23114_718593 node_context_11_23114_718593
  intro a
  fin_cases a
  · exact context_12_92456_224365
  · exact context_12_92457_718521
  · exact context_12_92458_224365
  · exact context_12_92459_718592

theorem selected_cut_28461 : selected 8 ⟨718604, by decide⟩
    (prefixPartial 13 369840) = some ⟨13, 2, 0, 718604, 369840, 837, 16384⟩ := by
  decide +kernel

theorem context_13_369840_718604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369840 ⟨718604, by decide⟩ :=
  accepted_of_selected 13 369840 ⟨718604, by decide⟩ ⟨13, 2, 0, 718604, 369840, 837, 16384⟩
    (by decide) selected_cut_28461

theorem selected_cut_28462 : selected 8 ⟨718626, by decide⟩
    (prefixPartial 13 369841) = some ⟨13, 2, 0, 718626, 369841, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_369841_718626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369841 ⟨718626, by decide⟩ :=
  accepted_of_selected 13 369841 ⟨718626, by decide⟩ ⟨13, 2, 0, 718626, 369841, 1737, 16384⟩
    (by decide) selected_cut_28462

theorem selected_cut_28463 : selected 8 ⟨718645, by decide⟩
    (prefixPartial 13 369842) = some ⟨13, 2, 0, 718645, 369842, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_369842_718645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369842 ⟨718645, by decide⟩ :=
  accepted_of_selected 13 369842 ⟨718645, by decide⟩ ⟨13, 2, 0, 718645, 369842, 1329, 16384⟩
    (by decide) selected_cut_28463

theorem selected_cut_28464 : selected 8 ⟨718655, by decide⟩
    (prefixPartial 13 369843) = some ⟨13, 2, 0, 718655, 369843, 957, 16384⟩ := by
  decide +kernel

theorem context_13_369843_718655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369843 ⟨718655, by decide⟩ :=
  accepted_of_selected 13 369843 ⟨718655, by decide⟩ ⟨13, 2, 0, 718655, 369843, 957, 16384⟩
    (by decide) selected_cut_28464

theorem unmarked_context_12_92460_718656 : frontier 9 ⟨718656, by decide⟩
    (prefixCache 12 92460) (prefixPartial 12 92460) = false := by
  decide +kernel

theorem node_context_12_92460_718656 : EJMOriginalGlobalDAGData.nodes 9 ⟨718656, by decide⟩ =
    .split (coordinate 12) (![⟨718604, by decide⟩,⟨718626, by decide⟩,⟨718645, by decide⟩,⟨718655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92460_718656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92460 ⟨718656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92460
    ⟨718656, by decide⟩ (by decide) (![⟨718604, by decide⟩,⟨718626, by decide⟩,⟨718645, by decide⟩,⟨718655, by decide⟩]) unmarked_context_12_92460_718656 node_context_12_92460_718656
  intro a
  fin_cases a
  · exact context_13_369840_718604
  · exact context_13_369841_718626
  · exact context_13_369842_718645
  · exact context_13_369843_718655

theorem selected_cut_28465 : selected 8 ⟨718666, by decide⟩
    (prefixPartial 13 369844) = some ⟨13, 2, 0, 718666, 369844, 749, 16384⟩ := by
  decide +kernel

theorem context_13_369844_718666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369844 ⟨718666, by decide⟩ :=
  accepted_of_selected 13 369844 ⟨718666, by decide⟩ ⟨13, 2, 0, 718666, 369844, 749, 16384⟩
    (by decide) selected_cut_28465

theorem selected_cut_28466 : selected 8 ⟨718685, by decide⟩
    (prefixPartial 13 369845) = some ⟨13, 2, 0, 718685, 369845, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_369845_718685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369845 ⟨718685, by decide⟩ :=
  accepted_of_selected 13 369845 ⟨718685, by decide⟩ ⟨13, 2, 0, 718685, 369845, 1289, 16384⟩
    (by decide) selected_cut_28466

theorem selected_cut_28467 : selected 8 ⟨718703, by decide⟩
    (prefixPartial 13 369846) = some ⟨13, 2, 0, 718703, 369846, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_369846_718703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369846 ⟨718703, by decide⟩ :=
  accepted_of_selected 13 369846 ⟨718703, by decide⟩ ⟨13, 2, 0, 718703, 369846, 1297, 16384⟩
    (by decide) selected_cut_28467

theorem selected_cut_28468 : selected 8 ⟨718709, by decide⟩
    (prefixPartial 13 369847) = some ⟨13, 2, 0, 718709, 369847, 817, 16384⟩ := by
  decide +kernel

theorem context_13_369847_718709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369847 ⟨718709, by decide⟩ :=
  accepted_of_selected 13 369847 ⟨718709, by decide⟩ ⟨13, 2, 0, 718709, 369847, 817, 16384⟩
    (by decide) selected_cut_28468

theorem unmarked_context_12_92461_718710 : frontier 9 ⟨718710, by decide⟩
    (prefixCache 12 92461) (prefixPartial 12 92461) = false := by
  decide +kernel

theorem node_context_12_92461_718710 : EJMOriginalGlobalDAGData.nodes 9 ⟨718710, by decide⟩ =
    .split (coordinate 12) (![⟨718666, by decide⟩,⟨718685, by decide⟩,⟨718703, by decide⟩,⟨718709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92461_718710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92461 ⟨718710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92461
    ⟨718710, by decide⟩ (by decide) (![⟨718666, by decide⟩,⟨718685, by decide⟩,⟨718703, by decide⟩,⟨718709, by decide⟩]) unmarked_context_12_92461_718710 node_context_12_92461_718710
  intro a
  fin_cases a
  · exact context_13_369844_718666
  · exact context_13_369845_718685
  · exact context_13_369846_718703
  · exact context_13_369847_718709

theorem selected_cut_28469 : selected 8 ⟨718724, by decide⟩
    (prefixPartial 13 369848) = some ⟨13, 2, 0, 718724, 369848, 833, 16384⟩ := by
  decide +kernel

theorem context_13_369848_718724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369848 ⟨718724, by decide⟩ :=
  accepted_of_selected 13 369848 ⟨718724, by decide⟩ ⟨13, 2, 0, 718724, 369848, 833, 16384⟩
    (by decide) selected_cut_28469

theorem selected_cut_28470 : selected 8 ⟨718744, by decide⟩
    (prefixPartial 13 369849) = some ⟨13, 2, 0, 718744, 369849, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_369849_718744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369849 ⟨718744, by decide⟩ :=
  accepted_of_selected 13 369849 ⟨718744, by decide⟩ ⟨13, 2, 0, 718744, 369849, 1653, 16384⟩
    (by decide) selected_cut_28470

theorem selected_cut_28471 : selected 8 ⟨718760, by decide⟩
    (prefixPartial 13 369850) = some ⟨13, 2, 0, 718760, 369850, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_369850_718760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369850 ⟨718760, by decide⟩ :=
  accepted_of_selected 13 369850 ⟨718760, by decide⟩ ⟨13, 2, 0, 718760, 369850, 1325, 16384⟩
    (by decide) selected_cut_28471

theorem selected_cut_28472 : selected 8 ⟨718767, by decide⟩
    (prefixPartial 13 369851) = some ⟨13, 2, 0, 718767, 369851, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_369851_718767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369851 ⟨718767, by decide⟩ :=
  accepted_of_selected 13 369851 ⟨718767, by decide⟩ ⟨13, 2, 0, 718767, 369851, 1061, 16384⟩
    (by decide) selected_cut_28472

theorem unmarked_context_12_92462_718768 : frontier 9 ⟨718768, by decide⟩
    (prefixCache 12 92462) (prefixPartial 12 92462) = false := by
  decide +kernel

theorem node_context_12_92462_718768 : EJMOriginalGlobalDAGData.nodes 9 ⟨718768, by decide⟩ =
    .split (coordinate 12) (![⟨718724, by decide⟩,⟨718744, by decide⟩,⟨718760, by decide⟩,⟨718767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92462_718768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92462 ⟨718768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92462
    ⟨718768, by decide⟩ (by decide) (![⟨718724, by decide⟩,⟨718744, by decide⟩,⟨718760, by decide⟩,⟨718767, by decide⟩]) unmarked_context_12_92462_718768 node_context_12_92462_718768
  intro a
  fin_cases a
  · exact context_13_369848_718724
  · exact context_13_369849_718744
  · exact context_13_369850_718760
  · exact context_13_369851_718767

theorem selected_cut_28473 : selected 8 ⟨718777, by decide⟩
    (prefixPartial 13 369852) = some ⟨13, 2, 0, 718777, 369852, 761, 16384⟩ := by
  decide +kernel

theorem context_13_369852_718777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369852 ⟨718777, by decide⟩ :=
  accepted_of_selected 13 369852 ⟨718777, by decide⟩ ⟨13, 2, 0, 718777, 369852, 761, 16384⟩
    (by decide) selected_cut_28473

theorem selected_cut_28474 : selected 8 ⟨718797, by decide⟩
    (prefixPartial 13 369853) = some ⟨13, 2, 0, 718797, 369853, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_369853_718797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369853 ⟨718797, by decide⟩ :=
  accepted_of_selected 13 369853 ⟨718797, by decide⟩ ⟨13, 2, 0, 718797, 369853, 1769, 16384⟩
    (by decide) selected_cut_28474

theorem selected_cut_28475 : selected 8 ⟨718816, by decide⟩
    (prefixPartial 13 369854) = some ⟨13, 2, 0, 718816, 369854, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_369854_718816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369854 ⟨718816, by decide⟩ :=
  accepted_of_selected 13 369854 ⟨718816, by decide⟩ ⟨13, 2, 0, 718816, 369854, 1401, 16384⟩
    (by decide) selected_cut_28475

theorem selected_cut_28476 : selected 8 ⟨718824, by decide⟩
    (prefixPartial 13 369855) = some ⟨13, 2, 0, 718824, 369855, 957, 16384⟩ := by
  decide +kernel

theorem context_13_369855_718824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369855 ⟨718824, by decide⟩ :=
  accepted_of_selected 13 369855 ⟨718824, by decide⟩ ⟨13, 2, 0, 718824, 369855, 957, 16384⟩
    (by decide) selected_cut_28476

theorem unmarked_context_12_92463_718825 : frontier 9 ⟨718825, by decide⟩
    (prefixCache 12 92463) (prefixPartial 12 92463) = false := by
  decide +kernel

theorem node_context_12_92463_718825 : EJMOriginalGlobalDAGData.nodes 9 ⟨718825, by decide⟩ =
    .split (coordinate 12) (![⟨718777, by decide⟩,⟨718797, by decide⟩,⟨718816, by decide⟩,⟨718824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92463_718825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92463 ⟨718825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92463
    ⟨718825, by decide⟩ (by decide) (![⟨718777, by decide⟩,⟨718797, by decide⟩,⟨718816, by decide⟩,⟨718824, by decide⟩]) unmarked_context_12_92463_718825 node_context_12_92463_718825
  intro a
  fin_cases a
  · exact context_13_369852_718777
  · exact context_13_369853_718797
  · exact context_13_369854_718816
  · exact context_13_369855_718824

theorem unmarked_context_11_23115_718826 : frontier 10 ⟨718826, by decide⟩
    (prefixCache 11 23115) (prefixPartial 11 23115) = false := by
  decide +kernel

theorem node_context_11_23115_718826 : EJMOriginalGlobalDAGData.nodes 10 ⟨718826, by decide⟩ =
    .split (coordinate 11) (![⟨718656, by decide⟩,⟨718710, by decide⟩,⟨718768, by decide⟩,⟨718825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23115_718826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23115 ⟨718826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23115
    ⟨718826, by decide⟩ (by decide) (![⟨718656, by decide⟩,⟨718710, by decide⟩,⟨718768, by decide⟩,⟨718825, by decide⟩]) unmarked_context_11_23115_718826 node_context_11_23115_718826
  intro a
  fin_cases a
  · exact context_12_92460_718656
  · exact context_12_92461_718710
  · exact context_12_92462_718768
  · exact context_12_92463_718825

theorem unmarked_context_10_5778_718827 : frontier 11 ⟨718827, by decide⟩
    (prefixCache 10 5778) (prefixPartial 10 5778) = false := by
  decide +kernel

theorem node_context_10_5778_718827 : EJMOriginalGlobalDAGData.nodes 11 ⟨718827, by decide⟩ =
    .split (coordinate 10) (![⟨718232, by decide⟩,⟨718405, by decide⟩,⟨718593, by decide⟩,⟨718826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5778_718827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5778 ⟨718827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5778
    ⟨718827, by decide⟩ (by decide) (![⟨718232, by decide⟩,⟨718405, by decide⟩,⟨718593, by decide⟩,⟨718826, by decide⟩]) unmarked_context_10_5778_718827 node_context_10_5778_718827
  intro a
  fin_cases a
  · exact context_11_23112_718232
  · exact context_11_23113_718405
  · exact context_11_23114_718593
  · exact context_11_23115_718826

theorem selected_cut_28477 : selected 8 ⟨718839, by decide⟩
    (prefixPartial 13 369856) = some ⟨13, 2, 0, 718839, 369856, 861, 16384⟩ := by
  decide +kernel

theorem context_13_369856_718839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369856 ⟨718839, by decide⟩ :=
  accepted_of_selected 13 369856 ⟨718839, by decide⟩ ⟨13, 2, 0, 718839, 369856, 861, 16384⟩
    (by decide) selected_cut_28477

theorem selected_cut_28478 : selected 8 ⟨718862, by decide⟩
    (prefixPartial 13 369857) = some ⟨13, 2, 0, 718862, 369857, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_369857_718862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369857 ⟨718862, by decide⟩ :=
  accepted_of_selected 13 369857 ⟨718862, by decide⟩ ⟨13, 2, 0, 718862, 369857, 1813, 16384⟩
    (by decide) selected_cut_28478

theorem selected_cut_28479 : selected 8 ⟨718882, by decide⟩
    (prefixPartial 13 369858) = some ⟨13, 2, 0, 718882, 369858, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_369858_718882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369858 ⟨718882, by decide⟩ :=
  accepted_of_selected 13 369858 ⟨718882, by decide⟩ ⟨13, 2, 0, 718882, 369858, 1585, 16384⟩
    (by decide) selected_cut_28479

theorem selected_cut_28480 : selected 8 ⟨718888, by decide⟩
    (prefixPartial 13 369859) = some ⟨13, 2, 0, 718888, 369859, 837, 16384⟩ := by
  decide +kernel

theorem context_13_369859_718888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369859 ⟨718888, by decide⟩ :=
  accepted_of_selected 13 369859 ⟨718888, by decide⟩ ⟨13, 2, 0, 718888, 369859, 837, 16384⟩
    (by decide) selected_cut_28480

theorem unmarked_context_12_92464_718889 : frontier 9 ⟨718889, by decide⟩
    (prefixCache 12 92464) (prefixPartial 12 92464) = false := by
  decide +kernel

theorem node_context_12_92464_718889 : EJMOriginalGlobalDAGData.nodes 9 ⟨718889, by decide⟩ =
    .split (coordinate 12) (![⟨718839, by decide⟩,⟨718862, by decide⟩,⟨718882, by decide⟩,⟨718888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92464_718889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92464 ⟨718889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92464
    ⟨718889, by decide⟩ (by decide) (![⟨718839, by decide⟩,⟨718862, by decide⟩,⟨718882, by decide⟩,⟨718888, by decide⟩]) unmarked_context_12_92464_718889 node_context_12_92464_718889
  intro a
  fin_cases a
  · exact context_13_369856_718839
  · exact context_13_369857_718862
  · exact context_13_369858_718882
  · exact context_13_369859_718888

theorem selected_cut_28481 : selected 8 ⟨718898, by decide⟩
    (prefixPartial 13 369860) = some ⟨13, 2, 0, 718898, 369860, 729, 16384⟩ := by
  decide +kernel

theorem context_13_369860_718898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369860 ⟨718898, by decide⟩ :=
  accepted_of_selected 13 369860 ⟨718898, by decide⟩ ⟨13, 2, 0, 718898, 369860, 729, 16384⟩
    (by decide) selected_cut_28481

theorem selected_cut_28482 : selected 8 ⟨718919, by decide⟩
    (prefixPartial 13 369861) = some ⟨13, 2, 0, 718919, 369861, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_369861_718919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369861 ⟨718919, by decide⟩ :=
  accepted_of_selected 13 369861 ⟨718919, by decide⟩ ⟨13, 2, 0, 718919, 369861, 1581, 16384⟩
    (by decide) selected_cut_28482

theorem selected_cut_28483 : selected 8 ⟨718934, by decide⟩
    (prefixPartial 13 369862) = some ⟨13, 2, 0, 718934, 369862, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_369862_718934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369862 ⟨718934, by decide⟩ :=
  accepted_of_selected 13 369862 ⟨718934, by decide⟩ ⟨13, 2, 0, 718934, 369862, 1461, 16384⟩
    (by decide) selected_cut_28483

theorem selected_cut_28484 : selected 8 ⟨718940, by decide⟩
    (prefixPartial 13 369863) = some ⟨13, 2, 0, 718940, 369863, 813, 16384⟩ := by
  decide +kernel

theorem context_13_369863_718940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369863 ⟨718940, by decide⟩ :=
  accepted_of_selected 13 369863 ⟨718940, by decide⟩ ⟨13, 2, 0, 718940, 369863, 813, 16384⟩
    (by decide) selected_cut_28484

theorem unmarked_context_12_92465_718941 : frontier 9 ⟨718941, by decide⟩
    (prefixCache 12 92465) (prefixPartial 12 92465) = false := by
  decide +kernel

theorem node_context_12_92465_718941 : EJMOriginalGlobalDAGData.nodes 9 ⟨718941, by decide⟩ =
    .split (coordinate 12) (![⟨718898, by decide⟩,⟨718919, by decide⟩,⟨718934, by decide⟩,⟨718940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92465_718941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92465 ⟨718941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92465
    ⟨718941, by decide⟩ (by decide) (![⟨718898, by decide⟩,⟨718919, by decide⟩,⟨718934, by decide⟩,⟨718940, by decide⟩]) unmarked_context_12_92465_718941 node_context_12_92465_718941
  intro a
  fin_cases a
  · exact context_13_369860_718898
  · exact context_13_369861_718919
  · exact context_13_369862_718934
  · exact context_13_369863_718940

theorem selected_cut_28485 : selected 8 ⟨718948, by decide⟩
    (prefixPartial 13 369864) = some ⟨13, 2, 0, 718948, 369864, 753, 16384⟩ := by
  decide +kernel

theorem context_13_369864_718948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369864 ⟨718948, by decide⟩ :=
  accepted_of_selected 13 369864 ⟨718948, by decide⟩ ⟨13, 2, 0, 718948, 369864, 753, 16384⟩
    (by decide) selected_cut_28485

theorem selected_cut_28486 : selected 8 ⟨718973, by decide⟩
    (prefixPartial 13 369865) = some ⟨13, 2, 0, 718973, 369865, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_369865_718973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369865 ⟨718973, by decide⟩ :=
  accepted_of_selected 13 369865 ⟨718973, by decide⟩ ⟨13, 2, 0, 718973, 369865, 1817, 16384⟩
    (by decide) selected_cut_28486

theorem selected_cut_28487 : selected 8 ⟨718990, by decide⟩
    (prefixPartial 13 369866) = some ⟨13, 2, 0, 718990, 369866, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_369866_718990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369866 ⟨718990, by decide⟩ :=
  accepted_of_selected 13 369866 ⟨718990, by decide⟩ ⟨13, 2, 0, 718990, 369866, 1581, 16384⟩
    (by decide) selected_cut_28487

theorem selected_cut_28488 : selected 8 ⟨718998, by decide⟩
    (prefixPartial 13 369867) = some ⟨13, 2, 0, 718998, 369867, 905, 16384⟩ := by
  decide +kernel

theorem context_13_369867_718998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369867 ⟨718998, by decide⟩ :=
  accepted_of_selected 13 369867 ⟨718998, by decide⟩ ⟨13, 2, 0, 718998, 369867, 905, 16384⟩
    (by decide) selected_cut_28488

theorem unmarked_context_12_92466_718999 : frontier 9 ⟨718999, by decide⟩
    (prefixCache 12 92466) (prefixPartial 12 92466) = false := by
  decide +kernel

theorem node_context_12_92466_718999 : EJMOriginalGlobalDAGData.nodes 9 ⟨718999, by decide⟩ =
    .split (coordinate 12) (![⟨718948, by decide⟩,⟨718973, by decide⟩,⟨718990, by decide⟩,⟨718998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92466_718999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92466 ⟨718999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92466
    ⟨718999, by decide⟩ (by decide) (![⟨718948, by decide⟩,⟨718973, by decide⟩,⟨718990, by decide⟩,⟨718998, by decide⟩]) unmarked_context_12_92466_718999 node_context_12_92466_718999
  intro a
  fin_cases a
  · exact context_13_369864_718948
  · exact context_13_369865_718973
  · exact context_13_369866_718990
  · exact context_13_369867_718998

theorem selected_cut_28489 : selected 8 ⟨719019, by decide⟩
    (prefixPartial 13 369868) = some ⟨13, 2, 0, 719019, 369868, 853, 16384⟩ := by
  decide +kernel

theorem context_13_369868_719019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369868 ⟨719019, by decide⟩ :=
  accepted_of_selected 13 369868 ⟨719019, by decide⟩ ⟨13, 2, 0, 719019, 369868, 853, 16384⟩
    (by decide) selected_cut_28489

theorem selected_cut_28490 : selected 8 ⟨719051, by decide⟩
    (prefixPartial 13 369869) = some ⟨13, 2, 0, 719051, 369869, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_369869_719051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369869 ⟨719051, by decide⟩ :=
  accepted_of_selected 13 369869 ⟨719051, by decide⟩ ⟨13, 2, 0, 719051, 369869, 2165, 16384⟩
    (by decide) selected_cut_28490

theorem selected_cut_28491 : selected 8 ⟨719070, by decide⟩
    (prefixPartial 13 369870) = some ⟨13, 2, 0, 719070, 369870, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_369870_719070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369870 ⟨719070, by decide⟩ :=
  accepted_of_selected 13 369870 ⟨719070, by decide⟩ ⟨13, 2, 0, 719070, 369870, 1617, 16384⟩
    (by decide) selected_cut_28491

theorem selected_cut_28492 : selected 8 ⟨719079, by decide⟩
    (prefixPartial 13 369871) = some ⟨13, 2, 0, 719079, 369871, 893, 16384⟩ := by
  decide +kernel

theorem context_13_369871_719079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369871 ⟨719079, by decide⟩ :=
  accepted_of_selected 13 369871 ⟨719079, by decide⟩ ⟨13, 2, 0, 719079, 369871, 893, 16384⟩
    (by decide) selected_cut_28492

theorem unmarked_context_12_92467_719080 : frontier 9 ⟨719080, by decide⟩
    (prefixCache 12 92467) (prefixPartial 12 92467) = false := by
  decide +kernel

theorem node_context_12_92467_719080 : EJMOriginalGlobalDAGData.nodes 9 ⟨719080, by decide⟩ =
    .split (coordinate 12) (![⟨719019, by decide⟩,⟨719051, by decide⟩,⟨719070, by decide⟩,⟨719079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92467_719080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92467 ⟨719080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92467
    ⟨719080, by decide⟩ (by decide) (![⟨719019, by decide⟩,⟨719051, by decide⟩,⟨719070, by decide⟩,⟨719079, by decide⟩]) unmarked_context_12_92467_719080 node_context_12_92467_719080
  intro a
  fin_cases a
  · exact context_13_369868_719019
  · exact context_13_369869_719051
  · exact context_13_369870_719070
  · exact context_13_369871_719079

theorem unmarked_context_11_23116_719081 : frontier 10 ⟨719081, by decide⟩
    (prefixCache 11 23116) (prefixPartial 11 23116) = false := by
  decide +kernel

theorem node_context_11_23116_719081 : EJMOriginalGlobalDAGData.nodes 10 ⟨719081, by decide⟩ =
    .split (coordinate 11) (![⟨718889, by decide⟩,⟨718941, by decide⟩,⟨718999, by decide⟩,⟨719080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23116_719081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23116 ⟨719081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23116
    ⟨719081, by decide⟩ (by decide) (![⟨718889, by decide⟩,⟨718941, by decide⟩,⟨718999, by decide⟩,⟨719080, by decide⟩]) unmarked_context_11_23116_719081 node_context_11_23116_719081
  intro a
  fin_cases a
  · exact context_12_92464_718889
  · exact context_12_92465_718941
  · exact context_12_92466_718999
  · exact context_12_92467_719080

theorem selected_cut_28493 : selected 8 ⟨719089, by decide⟩
    (prefixPartial 13 369872) = some ⟨13, 2, 0, 719089, 369872, 661, 16384⟩ := by
  decide +kernel

theorem context_13_369872_719089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369872 ⟨719089, by decide⟩ :=
  accepted_of_selected 13 369872 ⟨719089, by decide⟩ ⟨13, 2, 0, 719089, 369872, 661, 16384⟩
    (by decide) selected_cut_28493

theorem selected_cut_28494 : selected 8 ⟨719109, by decide⟩
    (prefixPartial 13 369873) = some ⟨13, 2, 0, 719109, 369873, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_369873_719109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369873 ⟨719109, by decide⟩ :=
  accepted_of_selected 13 369873 ⟨719109, by decide⟩ ⟨13, 2, 0, 719109, 369873, 1745, 16384⟩
    (by decide) selected_cut_28494

theorem selected_cut_28495 : selected 8 ⟨719127, by decide⟩
    (prefixPartial 13 369874) = some ⟨13, 2, 0, 719127, 369874, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_369874_719127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369874 ⟨719127, by decide⟩ :=
  accepted_of_selected 13 369874 ⟨719127, by decide⟩ ⟨13, 2, 0, 719127, 369874, 1449, 16384⟩
    (by decide) selected_cut_28495

theorem selected_cut_28496 : selected 8 ⟨719132, by decide⟩
    (prefixPartial 13 369875) = some ⟨13, 2, 0, 719132, 369875, 797, 16384⟩ := by
  decide +kernel

theorem context_13_369875_719132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369875 ⟨719132, by decide⟩ :=
  accepted_of_selected 13 369875 ⟨719132, by decide⟩ ⟨13, 2, 0, 719132, 369875, 797, 16384⟩
    (by decide) selected_cut_28496

theorem unmarked_context_12_92468_719133 : frontier 9 ⟨719133, by decide⟩
    (prefixCache 12 92468) (prefixPartial 12 92468) = false := by
  decide +kernel

theorem node_context_12_92468_719133 : EJMOriginalGlobalDAGData.nodes 9 ⟨719133, by decide⟩ =
    .split (coordinate 12) (![⟨719089, by decide⟩,⟨719109, by decide⟩,⟨719127, by decide⟩,⟨719132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92468_719133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92468 ⟨719133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92468
    ⟨719133, by decide⟩ (by decide) (![⟨719089, by decide⟩,⟨719109, by decide⟩,⟨719127, by decide⟩,⟨719132, by decide⟩]) unmarked_context_12_92468_719133 node_context_12_92468_719133
  intro a
  fin_cases a
  · exact context_13_369872_719089
  · exact context_13_369873_719109
  · exact context_13_369874_719127
  · exact context_13_369875_719132

theorem selected_cut_28497 : selected 9 ⟨719134, by decide⟩
    (prefixPartial 12 92469) = some ⟨12, 1, 0, 719134, 92469, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92469_719134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92469 ⟨719134, by decide⟩ :=
  accepted_of_selected 12 92469 ⟨719134, by decide⟩ ⟨12, 1, 0, 719134, 92469, 1, 65536⟩
    (by decide) selected_cut_28497

theorem selected_cut_28498 : selected 8 ⟨719144, by decide⟩
    (prefixPartial 13 369880) = some ⟨13, 2, 0, 719144, 369880, 641, 16384⟩ := by
  decide +kernel

theorem context_13_369880_719144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369880 ⟨719144, by decide⟩ :=
  accepted_of_selected 13 369880 ⟨719144, by decide⟩ ⟨13, 2, 0, 719144, 369880, 641, 16384⟩
    (by decide) selected_cut_28498

theorem selected_cut_28499 : selected 8 ⟨719164, by decide⟩
    (prefixPartial 13 369881) = some ⟨13, 2, 0, 719164, 369881, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_369881_719164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369881 ⟨719164, by decide⟩ :=
  accepted_of_selected 13 369881 ⟨719164, by decide⟩ ⟨13, 2, 0, 719164, 369881, 1625, 16384⟩
    (by decide) selected_cut_28499

theorem selected_cut_28500 : selected 8 ⟨719182, by decide⟩
    (prefixPartial 13 369882) = some ⟨13, 2, 0, 719182, 369882, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_369882_719182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369882 ⟨719182, by decide⟩ :=
  accepted_of_selected 13 369882 ⟨719182, by decide⟩ ⟨13, 2, 0, 719182, 369882, 1417, 16384⟩
    (by decide) selected_cut_28500

theorem selected_cut_28501 : selected 8 ⟨719188, by decide⟩
    (prefixPartial 13 369883) = some ⟨13, 2, 0, 719188, 369883, 857, 16384⟩ := by
  decide +kernel

theorem context_13_369883_719188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369883 ⟨719188, by decide⟩ :=
  accepted_of_selected 13 369883 ⟨719188, by decide⟩ ⟨13, 2, 0, 719188, 369883, 857, 16384⟩
    (by decide) selected_cut_28501

theorem unmarked_context_12_92470_719189 : frontier 9 ⟨719189, by decide⟩
    (prefixCache 12 92470) (prefixPartial 12 92470) = false := by
  decide +kernel

theorem node_context_12_92470_719189 : EJMOriginalGlobalDAGData.nodes 9 ⟨719189, by decide⟩ =
    .split (coordinate 12) (![⟨719144, by decide⟩,⟨719164, by decide⟩,⟨719182, by decide⟩,⟨719188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92470_719189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92470 ⟨719189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92470
    ⟨719189, by decide⟩ (by decide) (![⟨719144, by decide⟩,⟨719164, by decide⟩,⟨719182, by decide⟩,⟨719188, by decide⟩]) unmarked_context_12_92470_719189 node_context_12_92470_719189
  intro a
  fin_cases a
  · exact context_13_369880_719144
  · exact context_13_369881_719164
  · exact context_13_369882_719182
  · exact context_13_369883_719188

theorem selected_cut_28502 : selected 8 ⟨719203, by decide⟩
    (prefixPartial 13 369884) = some ⟨13, 2, 0, 719203, 369884, 593, 16384⟩ := by
  decide +kernel

theorem context_13_369884_719203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369884 ⟨719203, by decide⟩ :=
  accepted_of_selected 13 369884 ⟨719203, by decide⟩ ⟨13, 2, 0, 719203, 369884, 593, 16384⟩
    (by decide) selected_cut_28502

theorem selected_cut_28503 : selected 8 ⟨719228, by decide⟩
    (prefixPartial 13 369885) = some ⟨13, 2, 0, 719228, 369885, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_369885_719228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369885 ⟨719228, by decide⟩ :=
  accepted_of_selected 13 369885 ⟨719228, by decide⟩ ⟨13, 2, 0, 719228, 369885, 2049, 16384⟩
    (by decide) selected_cut_28503

theorem selected_cut_28504 : selected 8 ⟨719247, by decide⟩
    (prefixPartial 13 369886) = some ⟨13, 2, 0, 719247, 369886, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_369886_719247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369886 ⟨719247, by decide⟩ :=
  accepted_of_selected 13 369886 ⟨719247, by decide⟩ ⟨13, 2, 0, 719247, 369886, 1613, 16384⟩
    (by decide) selected_cut_28504

theorem selected_cut_28505 : selected 8 ⟨719253, by decide⟩
    (prefixPartial 13 369887) = some ⟨13, 2, 0, 719253, 369887, 793, 16384⟩ := by
  decide +kernel

theorem context_13_369887_719253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369887 ⟨719253, by decide⟩ :=
  accepted_of_selected 13 369887 ⟨719253, by decide⟩ ⟨13, 2, 0, 719253, 369887, 793, 16384⟩
    (by decide) selected_cut_28505

theorem unmarked_context_12_92471_719254 : frontier 9 ⟨719254, by decide⟩
    (prefixCache 12 92471) (prefixPartial 12 92471) = false := by
  decide +kernel

theorem node_context_12_92471_719254 : EJMOriginalGlobalDAGData.nodes 9 ⟨719254, by decide⟩ =
    .split (coordinate 12) (![⟨719203, by decide⟩,⟨719228, by decide⟩,⟨719247, by decide⟩,⟨719253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92471_719254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92471 ⟨719254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92471
    ⟨719254, by decide⟩ (by decide) (![⟨719203, by decide⟩,⟨719228, by decide⟩,⟨719247, by decide⟩,⟨719253, by decide⟩]) unmarked_context_12_92471_719254 node_context_12_92471_719254
  intro a
  fin_cases a
  · exact context_13_369884_719203
  · exact context_13_369885_719228
  · exact context_13_369886_719247
  · exact context_13_369887_719253

theorem unmarked_context_11_23117_719255 : frontier 10 ⟨719255, by decide⟩
    (prefixCache 11 23117) (prefixPartial 11 23117) = false := by
  decide +kernel

theorem node_context_11_23117_719255 : EJMOriginalGlobalDAGData.nodes 10 ⟨719255, by decide⟩ =
    .split (coordinate 11) (![⟨719133, by decide⟩,⟨719134, by decide⟩,⟨719189, by decide⟩,⟨719254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23117_719255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23117 ⟨719255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23117
    ⟨719255, by decide⟩ (by decide) (![⟨719133, by decide⟩,⟨719134, by decide⟩,⟨719189, by decide⟩,⟨719254, by decide⟩]) unmarked_context_11_23117_719255 node_context_11_23117_719255
  intro a
  fin_cases a
  · exact context_12_92468_719133
  · exact context_12_92469_719134
  · exact context_12_92470_719189
  · exact context_12_92471_719254

theorem selected_cut_28506 : selected 8 ⟨719262, by decide⟩
    (prefixPartial 13 369888) = some ⟨13, 2, 0, 719262, 369888, 477, 16384⟩ := by
  decide +kernel

theorem context_13_369888_719262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369888 ⟨719262, by decide⟩ :=
  accepted_of_selected 13 369888 ⟨719262, by decide⟩ ⟨13, 2, 0, 719262, 369888, 477, 16384⟩
    (by decide) selected_cut_28506

theorem selected_cut_28507 : selected 8 ⟨719284, by decide⟩
    (prefixPartial 13 369889) = some ⟨13, 2, 0, 719284, 369889, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_369889_719284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369889 ⟨719284, by decide⟩ :=
  accepted_of_selected 13 369889 ⟨719284, by decide⟩ ⟨13, 2, 0, 719284, 369889, 1805, 16384⟩
    (by decide) selected_cut_28507

theorem selected_cut_28508 : selected 8 ⟨719301, by decide⟩
    (prefixPartial 13 369890) = some ⟨13, 2, 0, 719301, 369890, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_369890_719301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369890 ⟨719301, by decide⟩ :=
  accepted_of_selected 13 369890 ⟨719301, by decide⟩ ⟨13, 2, 0, 719301, 369890, 1645, 16384⟩
    (by decide) selected_cut_28508

theorem selected_cut_28509 : selected 8 ⟨719308, by decide⟩
    (prefixPartial 13 369891) = some ⟨13, 2, 0, 719308, 369891, 857, 16384⟩ := by
  decide +kernel

theorem context_13_369891_719308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369891 ⟨719308, by decide⟩ :=
  accepted_of_selected 13 369891 ⟨719308, by decide⟩ ⟨13, 2, 0, 719308, 369891, 857, 16384⟩
    (by decide) selected_cut_28509

theorem unmarked_context_12_92472_719309 : frontier 9 ⟨719309, by decide⟩
    (prefixCache 12 92472) (prefixPartial 12 92472) = false := by
  decide +kernel

theorem node_context_12_92472_719309 : EJMOriginalGlobalDAGData.nodes 9 ⟨719309, by decide⟩ =
    .split (coordinate 12) (![⟨719262, by decide⟩,⟨719284, by decide⟩,⟨719301, by decide⟩,⟨719308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92472_719309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92472 ⟨719309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92472
    ⟨719309, by decide⟩ (by decide) (![⟨719262, by decide⟩,⟨719284, by decide⟩,⟨719301, by decide⟩,⟨719308, by decide⟩]) unmarked_context_12_92472_719309 node_context_12_92472_719309
  intro a
  fin_cases a
  · exact context_13_369888_719262
  · exact context_13_369889_719284
  · exact context_13_369890_719301
  · exact context_13_369891_719308

theorem selected_cut_28510 : selected 8 ⟨719316, by decide⟩
    (prefixPartial 13 369892) = some ⟨13, 2, 0, 719316, 369892, 437, 16384⟩ := by
  decide +kernel

theorem context_13_369892_719316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369892 ⟨719316, by decide⟩ :=
  accepted_of_selected 13 369892 ⟨719316, by decide⟩ ⟨13, 2, 0, 719316, 369892, 437, 16384⟩
    (by decide) selected_cut_28510

theorem selected_cut_28511 : selected 8 ⟨719338, by decide⟩
    (prefixPartial 13 369893) = some ⟨13, 2, 0, 719338, 369893, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_369893_719338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369893 ⟨719338, by decide⟩ :=
  accepted_of_selected 13 369893 ⟨719338, by decide⟩ ⟨13, 2, 0, 719338, 369893, 1465, 16384⟩
    (by decide) selected_cut_28511

theorem selected_cut_28512 : selected 8 ⟨719355, by decide⟩
    (prefixPartial 13 369894) = some ⟨13, 2, 0, 719355, 369894, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_369894_719355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369894 ⟨719355, by decide⟩ :=
  accepted_of_selected 13 369894 ⟨719355, by decide⟩ ⟨13, 2, 0, 719355, 369894, 1525, 16384⟩
    (by decide) selected_cut_28512

theorem selected_cut_28513 : selected 8 ⟨719363, by decide⟩
    (prefixPartial 13 369895) = some ⟨13, 2, 0, 719363, 369895, 805, 16384⟩ := by
  decide +kernel

theorem context_13_369895_719363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369895 ⟨719363, by decide⟩ :=
  accepted_of_selected 13 369895 ⟨719363, by decide⟩ ⟨13, 2, 0, 719363, 369895, 805, 16384⟩
    (by decide) selected_cut_28513

theorem unmarked_context_12_92473_719364 : frontier 9 ⟨719364, by decide⟩
    (prefixCache 12 92473) (prefixPartial 12 92473) = false := by
  decide +kernel

theorem node_context_12_92473_719364 : EJMOriginalGlobalDAGData.nodes 9 ⟨719364, by decide⟩ =
    .split (coordinate 12) (![⟨719316, by decide⟩,⟨719338, by decide⟩,⟨719355, by decide⟩,⟨719363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92473_719364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92473 ⟨719364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92473
    ⟨719364, by decide⟩ (by decide) (![⟨719316, by decide⟩,⟨719338, by decide⟩,⟨719355, by decide⟩,⟨719363, by decide⟩]) unmarked_context_12_92473_719364 node_context_12_92473_719364
  intro a
  fin_cases a
  · exact context_13_369892_719316
  · exact context_13_369893_719338
  · exact context_13_369894_719355
  · exact context_13_369895_719363

theorem selected_cut_28514 : selected 8 ⟨719370, by decide⟩
    (prefixPartial 13 369896) = some ⟨13, 2, 0, 719370, 369896, 369, 16384⟩ := by
  decide +kernel

theorem context_13_369896_719370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369896 ⟨719370, by decide⟩ :=
  accepted_of_selected 13 369896 ⟨719370, by decide⟩ ⟨13, 2, 0, 719370, 369896, 369, 16384⟩
    (by decide) selected_cut_28514

theorem selected_cut_28515 : selected 8 ⟨719391, by decide⟩
    (prefixPartial 13 369897) = some ⟨13, 2, 0, 719391, 369897, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_369897_719391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 369897 ⟨719391, by decide⟩ :=
  accepted_of_selected 13 369897 ⟨719391, by decide⟩ ⟨13, 2, 0, 719391, 369897, 1613, 16384⟩
    (by decide) selected_cut_28515

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
