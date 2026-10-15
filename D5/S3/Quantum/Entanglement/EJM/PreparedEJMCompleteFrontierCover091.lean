/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover090
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_08740 : selected 8 ⟨243953, by decide⟩
    (prefixPartial 13 92413) = some ⟨13, 2, 0, 243953, 92413, 2945, 16384⟩ := by
  decide +kernel

theorem context_13_92413_243953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92413 ⟨243953, by decide⟩ :=
  accepted_of_selected 13 92413 ⟨243953, by decide⟩ ⟨13, 2, 0, 243953, 92413, 2945, 16384⟩
    (by decide) selected_cut_08740

theorem selected_cut_08741 : selected 8 ⟨243978, by decide⟩
    (prefixPartial 13 92414) = some ⟨13, 2, 0, 243978, 92414, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_92414_243978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92414 ⟨243978, by decide⟩ :=
  accepted_of_selected 13 92414 ⟨243978, by decide⟩ ⟨13, 2, 0, 243978, 92414, 1533, 16384⟩
    (by decide) selected_cut_08741

theorem selected_cut_08742 : selected 8 ⟨243985, by decide⟩
    (prefixPartial 13 92415) = some ⟨13, 2, 0, 243985, 92415, 929, 16384⟩ := by
  decide +kernel

theorem context_13_92415_243985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92415 ⟨243985, by decide⟩ :=
  accepted_of_selected 13 92415 ⟨243985, by decide⟩ ⟨13, 2, 0, 243985, 92415, 929, 16384⟩
    (by decide) selected_cut_08742

theorem unmarked_context_12_23103_243986 : frontier 9 ⟨243986, by decide⟩
    (prefixCache 12 23103) (prefixPartial 12 23103) = false := by
  decide +kernel

theorem node_context_12_23103_243986 : EJMOriginalGlobalDAGData.nodes 9 ⟨243986, by decide⟩ =
    .split (coordinate 12) (![⟨243912, by decide⟩,⟨243953, by decide⟩,⟨243978, by decide⟩,⟨243985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23103_243986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23103 ⟨243986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23103
    ⟨243986, by decide⟩ (by decide) (![⟨243912, by decide⟩,⟨243953, by decide⟩,⟨243978, by decide⟩,⟨243985, by decide⟩]) unmarked_context_12_23103_243986 node_context_12_23103_243986
  intro a
  fin_cases a
  · exact context_13_92412_243912
  · exact context_13_92413_243953
  · exact context_13_92414_243978
  · exact context_13_92415_243985

theorem unmarked_context_11_5775_243987 : frontier 10 ⟨243987, by decide⟩
    (prefixCache 11 5775) (prefixPartial 11 5775) = false := by
  decide +kernel

theorem node_context_11_5775_243987 : EJMOriginalGlobalDAGData.nodes 10 ⟨243987, by decide⟩ =
    .split (coordinate 11) (![⟨243753, by decide⟩,⟨243824, by decide⟩,⟨243907, by decide⟩,⟨243986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5775_243987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5775 ⟨243987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5775
    ⟨243987, by decide⟩ (by decide) (![⟨243753, by decide⟩,⟨243824, by decide⟩,⟨243907, by decide⟩,⟨243986, by decide⟩]) unmarked_context_11_5775_243987 node_context_11_5775_243987
  intro a
  fin_cases a
  · exact context_12_23100_243753
  · exact context_12_23101_243824
  · exact context_12_23102_243907
  · exact context_12_23103_243986

theorem unmarked_context_10_1443_243988 : frontier 11 ⟨243988, by decide⟩
    (prefixCache 10 1443) (prefixPartial 10 1443) = false := by
  decide +kernel

theorem node_context_10_1443_243988 : EJMOriginalGlobalDAGData.nodes 11 ⟨243988, by decide⟩ =
    .split (coordinate 10) (![⟨242935, by decide⟩,⟨243279, by decide⟩,⟨243681, by decide⟩,⟨243987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1443_243988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1443 ⟨243988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1443
    ⟨243988, by decide⟩ (by decide) (![⟨242935, by decide⟩,⟨243279, by decide⟩,⟨243681, by decide⟩,⟨243987, by decide⟩]) unmarked_context_10_1443_243988 node_context_10_1443_243988
  intro a
  fin_cases a
  · exact context_11_5772_242935
  · exact context_11_5773_243279
  · exact context_11_5774_243681
  · exact context_11_5775_243987

theorem unmarked_context_9_360_243989 : frontier 12 ⟨243989, by decide⟩
    (prefixCache 9 360) (prefixPartial 9 360) = false := by
  decide +kernel

theorem node_context_9_360_243989 : EJMOriginalGlobalDAGData.nodes 12 ⟨243989, by decide⟩ =
    .split (coordinate 9) (![⟨239355, by decide⟩,⟨241254, by decide⟩,⟨242611, by decide⟩,⟨243988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_360_243989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 360 ⟨243989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 360
    ⟨243989, by decide⟩ (by decide) (![⟨239355, by decide⟩,⟨241254, by decide⟩,⟨242611, by decide⟩,⟨243988, by decide⟩]) unmarked_context_9_360_243989 node_context_9_360_243989
  intro a
  fin_cases a
  · exact context_10_1440_239355
  · exact context_10_1441_241254
  · exact context_10_1442_242611
  · exact context_10_1443_243988

theorem selected_cut_08743 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92416) = some ⟨13, 1, 0, 3444, 92416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92416, 1, 16384⟩
    (by decide) selected_cut_08743

theorem selected_cut_08744 : selected 8 ⟨244044, by decide⟩
    (prefixPartial 13 92417) = some ⟨13, 2, 0, 244044, 92417, 3553, 16384⟩ := by
  decide +kernel

theorem context_13_92417_244044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92417 ⟨244044, by decide⟩ :=
  accepted_of_selected 13 92417 ⟨244044, by decide⟩ ⟨13, 2, 0, 244044, 92417, 3553, 16384⟩
    (by decide) selected_cut_08744

theorem selected_cut_08745 : selected 8 ⟨244065, by decide⟩
    (prefixPartial 13 92418) = some ⟨13, 2, 0, 244065, 92418, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_92418_244065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92418 ⟨244065, by decide⟩ :=
  accepted_of_selected 13 92418 ⟨244065, by decide⟩ ⟨13, 2, 0, 244065, 92418, 1701, 16384⟩
    (by decide) selected_cut_08745

theorem selected_cut_08746 : selected 8 ⟨244072, by decide⟩
    (prefixPartial 13 92419) = some ⟨13, 2, 0, 244072, 92419, 953, 16384⟩ := by
  decide +kernel

theorem context_13_92419_244072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92419 ⟨244072, by decide⟩ :=
  accepted_of_selected 13 92419 ⟨244072, by decide⟩ ⟨13, 2, 0, 244072, 92419, 953, 16384⟩
    (by decide) selected_cut_08746

theorem unmarked_context_12_23104_244073 : frontier 9 ⟨244073, by decide⟩
    (prefixCache 12 23104) (prefixPartial 12 23104) = false := by
  decide +kernel

theorem node_context_12_23104_244073 : EJMOriginalGlobalDAGData.nodes 9 ⟨244073, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244044, by decide⟩,⟨244065, by decide⟩,⟨244072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23104_244073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23104 ⟨244073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23104
    ⟨244073, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244044, by decide⟩,⟨244065, by decide⟩,⟨244072, by decide⟩]) unmarked_context_12_23104_244073 node_context_12_23104_244073
  intro a
  fin_cases a
  · exact context_13_92416_3444
  · exact context_13_92417_244044
  · exact context_13_92418_244065
  · exact context_13_92419_244072

theorem selected_cut_08747 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92420) = some ⟨13, 1, 0, 3444, 92420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92420, 1, 16384⟩
    (by decide) selected_cut_08747

theorem selected_cut_08748 : selected 7 ⟨244107, by decide⟩
    (prefixPartial 14 369684) = some ⟨14, 2, 0, 244107, 369684, 1553, 4096⟩ := by
  decide +kernel

theorem context_14_369684_244107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369684 ⟨244107, by decide⟩ :=
  accepted_of_selected 14 369684 ⟨244107, by decide⟩ ⟨14, 2, 0, 244107, 369684, 1553, 4096⟩
    (by decide) selected_cut_08748

theorem selected_cut_08749 : selected 7 ⟨244132, by decide⟩
    (prefixPartial 14 369685) = some ⟨14, 2, 0, 244132, 369685, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_369685_244132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369685 ⟨244132, by decide⟩ :=
  accepted_of_selected 14 369685 ⟨244132, by decide⟩ ⟨14, 2, 0, 244132, 369685, 1297, 4096⟩
    (by decide) selected_cut_08749

theorem selected_cut_08750 : selected 7 ⟨244164, by decide⟩
    (prefixPartial 14 369686) = some ⟨14, 2, 0, 244164, 369686, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_369686_244164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369686 ⟨244164, by decide⟩ :=
  accepted_of_selected 14 369686 ⟨244164, by decide⟩ ⟨14, 2, 0, 244164, 369686, 1321, 4096⟩
    (by decide) selected_cut_08750

theorem selected_cut_08751 : selected 7 ⟨244184, by decide⟩
    (prefixPartial 14 369687) = some ⟨14, 2, 0, 244184, 369687, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_369687_244184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369687 ⟨244184, by decide⟩ :=
  accepted_of_selected 14 369687 ⟨244184, by decide⟩ ⟨14, 2, 0, 244184, 369687, 1181, 4096⟩
    (by decide) selected_cut_08751

theorem unmarked_context_13_92421_244185 : frontier 8 ⟨244185, by decide⟩
    (prefixCache 13 92421) (prefixPartial 13 92421) = false := by
  decide +kernel

theorem node_context_13_92421_244185 : EJMOriginalGlobalDAGData.nodes 8 ⟨244185, by decide⟩ =
    .split (coordinate 13) (![⟨244107, by decide⟩,⟨244132, by decide⟩,⟨244164, by decide⟩,⟨244184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92421_244185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92421 ⟨244185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92421
    ⟨244185, by decide⟩ (by decide) (![⟨244107, by decide⟩,⟨244132, by decide⟩,⟨244164, by decide⟩,⟨244184, by decide⟩]) unmarked_context_13_92421_244185 node_context_13_92421_244185
  intro a
  fin_cases a
  · exact context_14_369684_244107
  · exact context_14_369685_244132
  · exact context_14_369686_244164
  · exact context_14_369687_244184

theorem selected_cut_08752 : selected 8 ⟨244207, by decide⟩
    (prefixPartial 13 92422) = some ⟨13, 2, 0, 244207, 92422, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_92422_244207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92422 ⟨244207, by decide⟩ :=
  accepted_of_selected 13 92422 ⟨244207, by decide⟩ ⟨13, 2, 0, 244207, 92422, 1825, 16384⟩
    (by decide) selected_cut_08752

theorem selected_cut_08753 : selected 8 ⟨244230, by decide⟩
    (prefixPartial 13 92423) = some ⟨13, 2, 0, 244230, 92423, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_92423_244230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92423 ⟨244230, by decide⟩ :=
  accepted_of_selected 13 92423 ⟨244230, by decide⟩ ⟨13, 2, 0, 244230, 92423, 1317, 16384⟩
    (by decide) selected_cut_08753

theorem unmarked_context_12_23105_244231 : frontier 9 ⟨244231, by decide⟩
    (prefixCache 12 23105) (prefixPartial 12 23105) = false := by
  decide +kernel

theorem node_context_12_23105_244231 : EJMOriginalGlobalDAGData.nodes 9 ⟨244231, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244185, by decide⟩,⟨244207, by decide⟩,⟨244230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23105_244231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23105 ⟨244231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23105
    ⟨244231, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244185, by decide⟩,⟨244207, by decide⟩,⟨244230, by decide⟩]) unmarked_context_12_23105_244231 node_context_12_23105_244231
  intro a
  fin_cases a
  · exact context_13_92420_3444
  · exact context_13_92421_244185
  · exact context_13_92422_244207
  · exact context_13_92423_244230

theorem selected_cut_08754 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92424) = some ⟨13, 1, 0, 3444, 92424, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92424_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92424 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92424 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92424, 1, 16384⟩
    (by decide) selected_cut_08754

theorem selected_cut_08755 : selected 8 ⟨244281, by decide⟩
    (prefixPartial 13 92425) = some ⟨13, 2, 0, 244281, 92425, 3669, 16384⟩ := by
  decide +kernel

theorem context_13_92425_244281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92425 ⟨244281, by decide⟩ :=
  accepted_of_selected 13 92425 ⟨244281, by decide⟩ ⟨13, 2, 0, 244281, 92425, 3669, 16384⟩
    (by decide) selected_cut_08755

theorem selected_cut_08756 : selected 8 ⟨244300, by decide⟩
    (prefixPartial 13 92426) = some ⟨13, 2, 0, 244300, 92426, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_92426_244300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92426 ⟨244300, by decide⟩ :=
  accepted_of_selected 13 92426 ⟨244300, by decide⟩ ⟨13, 2, 0, 244300, 92426, 1601, 16384⟩
    (by decide) selected_cut_08756

theorem selected_cut_08757 : selected 8 ⟨244311, by decide⟩
    (prefixPartial 13 92427) = some ⟨13, 2, 0, 244311, 92427, 985, 16384⟩ := by
  decide +kernel

theorem context_13_92427_244311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92427 ⟨244311, by decide⟩ :=
  accepted_of_selected 13 92427 ⟨244311, by decide⟩ ⟨13, 2, 0, 244311, 92427, 985, 16384⟩
    (by decide) selected_cut_08757

theorem unmarked_context_12_23106_244312 : frontier 9 ⟨244312, by decide⟩
    (prefixCache 12 23106) (prefixPartial 12 23106) = false := by
  decide +kernel

theorem node_context_12_23106_244312 : EJMOriginalGlobalDAGData.nodes 9 ⟨244312, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244281, by decide⟩,⟨244300, by decide⟩,⟨244311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23106_244312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23106 ⟨244312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23106
    ⟨244312, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244281, by decide⟩,⟨244300, by decide⟩,⟨244311, by decide⟩]) unmarked_context_12_23106_244312 node_context_12_23106_244312
  intro a
  fin_cases a
  · exact context_13_92424_3444
  · exact context_13_92425_244281
  · exact context_13_92426_244300
  · exact context_13_92427_244311

theorem selected_cut_08758 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92428) = some ⟨13, 1, 0, 3444, 92428, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92428_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92428 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92428 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92428, 1, 16384⟩
    (by decide) selected_cut_08758

theorem selected_cut_08759 : selected 8 ⟨244375, by decide⟩
    (prefixPartial 13 92429) = some ⟨13, 2, 0, 244375, 92429, 3753, 16384⟩ := by
  decide +kernel

theorem context_13_92429_244375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92429 ⟨244375, by decide⟩ :=
  accepted_of_selected 13 92429 ⟨244375, by decide⟩ ⟨13, 2, 0, 244375, 92429, 3753, 16384⟩
    (by decide) selected_cut_08759

theorem selected_cut_08760 : selected 8 ⟨244395, by decide⟩
    (prefixPartial 13 92430) = some ⟨13, 2, 0, 244395, 92430, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_92430_244395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92430 ⟨244395, by decide⟩ :=
  accepted_of_selected 13 92430 ⟨244395, by decide⟩ ⟨13, 2, 0, 244395, 92430, 1721, 16384⟩
    (by decide) selected_cut_08760

theorem selected_cut_08761 : selected 8 ⟨244407, by decide⟩
    (prefixPartial 13 92431) = some ⟨13, 2, 0, 244407, 92431, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_92431_244407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92431 ⟨244407, by decide⟩ :=
  accepted_of_selected 13 92431 ⟨244407, by decide⟩ ⟨13, 2, 0, 244407, 92431, 1057, 16384⟩
    (by decide) selected_cut_08761

theorem unmarked_context_12_23107_244408 : frontier 9 ⟨244408, by decide⟩
    (prefixCache 12 23107) (prefixPartial 12 23107) = false := by
  decide +kernel

theorem node_context_12_23107_244408 : EJMOriginalGlobalDAGData.nodes 9 ⟨244408, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244375, by decide⟩,⟨244395, by decide⟩,⟨244407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23107_244408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23107 ⟨244408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23107
    ⟨244408, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244375, by decide⟩,⟨244395, by decide⟩,⟨244407, by decide⟩]) unmarked_context_12_23107_244408 node_context_12_23107_244408
  intro a
  fin_cases a
  · exact context_13_92428_3444
  · exact context_13_92429_244375
  · exact context_13_92430_244395
  · exact context_13_92431_244407

theorem unmarked_context_11_5776_244409 : frontier 10 ⟨244409, by decide⟩
    (prefixCache 11 5776) (prefixPartial 11 5776) = false := by
  decide +kernel

theorem node_context_11_5776_244409 : EJMOriginalGlobalDAGData.nodes 10 ⟨244409, by decide⟩ =
    .split (coordinate 11) (![⟨244073, by decide⟩,⟨244231, by decide⟩,⟨244312, by decide⟩,⟨244408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5776_244409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5776 ⟨244409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5776
    ⟨244409, by decide⟩ (by decide) (![⟨244073, by decide⟩,⟨244231, by decide⟩,⟨244312, by decide⟩,⟨244408, by decide⟩]) unmarked_context_11_5776_244409 node_context_11_5776_244409
  intro a
  fin_cases a
  · exact context_12_23104_244073
  · exact context_12_23105_244231
  · exact context_12_23106_244312
  · exact context_12_23107_244408

theorem selected_cut_08762 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92432) = some ⟨13, 1, 0, 3444, 92432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92432, 1, 16384⟩
    (by decide) selected_cut_08762

theorem selected_cut_08763 : selected 8 ⟨244467, by decide⟩
    (prefixPartial 13 92433) = some ⟨13, 2, 0, 244467, 92433, 3513, 16384⟩ := by
  decide +kernel

theorem context_13_92433_244467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92433 ⟨244467, by decide⟩ :=
  accepted_of_selected 13 92433 ⟨244467, by decide⟩ ⟨13, 2, 0, 244467, 92433, 3513, 16384⟩
    (by decide) selected_cut_08763

theorem selected_cut_08764 : selected 8 ⟨244488, by decide⟩
    (prefixPartial 13 92434) = some ⟨13, 2, 0, 244488, 92434, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_92434_244488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92434 ⟨244488, by decide⟩ :=
  accepted_of_selected 13 92434 ⟨244488, by decide⟩ ⟨13, 2, 0, 244488, 92434, 1701, 16384⟩
    (by decide) selected_cut_08764

theorem selected_cut_08765 : selected 8 ⟨244499, by decide⟩
    (prefixPartial 13 92435) = some ⟨13, 2, 0, 244499, 92435, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_92435_244499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92435 ⟨244499, by decide⟩ :=
  accepted_of_selected 13 92435 ⟨244499, by decide⟩ ⟨13, 2, 0, 244499, 92435, 1069, 16384⟩
    (by decide) selected_cut_08765

theorem unmarked_context_12_23108_244500 : frontier 9 ⟨244500, by decide⟩
    (prefixCache 12 23108) (prefixPartial 12 23108) = false := by
  decide +kernel

theorem node_context_12_23108_244500 : EJMOriginalGlobalDAGData.nodes 9 ⟨244500, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244467, by decide⟩,⟨244488, by decide⟩,⟨244499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23108_244500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23108 ⟨244500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23108
    ⟨244500, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244467, by decide⟩,⟨244488, by decide⟩,⟨244499, by decide⟩]) unmarked_context_12_23108_244500 node_context_12_23108_244500
  intro a
  fin_cases a
  · exact context_13_92432_3444
  · exact context_13_92433_244467
  · exact context_13_92434_244488
  · exact context_13_92435_244499

theorem selected_cut_08766 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92436) = some ⟨13, 1, 0, 3444, 92436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92436, 1, 16384⟩
    (by decide) selected_cut_08766

theorem selected_cut_08767 : selected 7 ⟨244528, by decide⟩
    (prefixPartial 14 369748) = some ⟨14, 2, 0, 244528, 369748, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_369748_244528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369748 ⟨244528, by decide⟩ :=
  accepted_of_selected 14 369748 ⟨244528, by decide⟩ ⟨14, 2, 0, 244528, 369748, 1321, 4096⟩
    (by decide) selected_cut_08767

theorem selected_cut_08768 : selected 7 ⟨244553, by decide⟩
    (prefixPartial 14 369749) = some ⟨14, 2, 0, 244553, 369749, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_369749_244553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369749 ⟨244553, by decide⟩ :=
  accepted_of_selected 14 369749 ⟨244553, by decide⟩ ⟨14, 2, 0, 244553, 369749, 1205, 4096⟩
    (by decide) selected_cut_08768

theorem selected_cut_08769 : selected 7 ⟨244574, by decide⟩
    (prefixPartial 14 369750) = some ⟨14, 2, 0, 244574, 369750, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_369750_244574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369750 ⟨244574, by decide⟩ :=
  accepted_of_selected 14 369750 ⟨244574, by decide⟩ ⟨14, 2, 0, 244574, 369750, 1205, 4096⟩
    (by decide) selected_cut_08769

theorem selected_cut_08770 : selected 7 ⟨244586, by decide⟩
    (prefixPartial 14 369751) = some ⟨14, 2, 0, 244586, 369751, 1033, 4096⟩ := by
  decide +kernel

theorem context_14_369751_244586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369751 ⟨244586, by decide⟩ :=
  accepted_of_selected 14 369751 ⟨244586, by decide⟩ ⟨14, 2, 0, 244586, 369751, 1033, 4096⟩
    (by decide) selected_cut_08770

theorem unmarked_context_13_92437_244587 : frontier 8 ⟨244587, by decide⟩
    (prefixCache 13 92437) (prefixPartial 13 92437) = false := by
  decide +kernel

theorem node_context_13_92437_244587 : EJMOriginalGlobalDAGData.nodes 8 ⟨244587, by decide⟩ =
    .split (coordinate 13) (![⟨244528, by decide⟩,⟨244553, by decide⟩,⟨244574, by decide⟩,⟨244586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92437_244587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92437 ⟨244587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92437
    ⟨244587, by decide⟩ (by decide) (![⟨244528, by decide⟩,⟨244553, by decide⟩,⟨244574, by decide⟩,⟨244586, by decide⟩]) unmarked_context_13_92437_244587 node_context_13_92437_244587
  intro a
  fin_cases a
  · exact context_14_369748_244528
  · exact context_14_369749_244553
  · exact context_14_369750_244574
  · exact context_14_369751_244586

theorem selected_cut_08771 : selected 8 ⟨244606, by decide⟩
    (prefixPartial 13 92438) = some ⟨13, 2, 0, 244606, 92438, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_92438_244606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92438 ⟨244606, by decide⟩ :=
  accepted_of_selected 13 92438 ⟨244606, by decide⟩ ⟨13, 2, 0, 244606, 92438, 1881, 16384⟩
    (by decide) selected_cut_08771

theorem selected_cut_08772 : selected 8 ⟨244628, by decide⟩
    (prefixPartial 13 92439) = some ⟨13, 2, 0, 244628, 92439, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_92439_244628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92439 ⟨244628, by decide⟩ :=
  accepted_of_selected 13 92439 ⟨244628, by decide⟩ ⟨13, 2, 0, 244628, 92439, 1329, 16384⟩
    (by decide) selected_cut_08772

theorem unmarked_context_12_23109_244629 : frontier 9 ⟨244629, by decide⟩
    (prefixCache 12 23109) (prefixPartial 12 23109) = false := by
  decide +kernel

theorem node_context_12_23109_244629 : EJMOriginalGlobalDAGData.nodes 9 ⟨244629, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244587, by decide⟩,⟨244606, by decide⟩,⟨244628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23109_244629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23109 ⟨244629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23109
    ⟨244629, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244587, by decide⟩,⟨244606, by decide⟩,⟨244628, by decide⟩]) unmarked_context_12_23109_244629 node_context_12_23109_244629
  intro a
  fin_cases a
  · exact context_13_92436_3444
  · exact context_13_92437_244587
  · exact context_13_92438_244606
  · exact context_13_92439_244628

theorem selected_cut_08773 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92440) = some ⟨13, 1, 0, 3444, 92440, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92440_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92440 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92440 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92440, 1, 16384⟩
    (by decide) selected_cut_08773

theorem selected_cut_08774 : selected 8 ⟨244669, by decide⟩
    (prefixPartial 13 92441) = some ⟨13, 2, 0, 244669, 92441, 3057, 16384⟩ := by
  decide +kernel

theorem context_13_92441_244669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92441 ⟨244669, by decide⟩ :=
  accepted_of_selected 13 92441 ⟨244669, by decide⟩ ⟨13, 2, 0, 244669, 92441, 3057, 16384⟩
    (by decide) selected_cut_08774

theorem selected_cut_08775 : selected 8 ⟨244691, by decide⟩
    (prefixPartial 13 92442) = some ⟨13, 2, 0, 244691, 92442, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_92442_244691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92442 ⟨244691, by decide⟩ :=
  accepted_of_selected 13 92442 ⟨244691, by decide⟩ ⟨13, 2, 0, 244691, 92442, 1677, 16384⟩
    (by decide) selected_cut_08775

theorem selected_cut_08776 : selected 8 ⟨244707, by decide⟩
    (prefixPartial 13 92443) = some ⟨13, 2, 0, 244707, 92443, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_92443_244707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92443 ⟨244707, by decide⟩ :=
  accepted_of_selected 13 92443 ⟨244707, by decide⟩ ⟨13, 2, 0, 244707, 92443, 1057, 16384⟩
    (by decide) selected_cut_08776

theorem unmarked_context_12_23110_244708 : frontier 9 ⟨244708, by decide⟩
    (prefixCache 12 23110) (prefixPartial 12 23110) = false := by
  decide +kernel

theorem node_context_12_23110_244708 : EJMOriginalGlobalDAGData.nodes 9 ⟨244708, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244669, by decide⟩,⟨244691, by decide⟩,⟨244707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23110_244708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23110 ⟨244708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23110
    ⟨244708, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244669, by decide⟩,⟨244691, by decide⟩,⟨244707, by decide⟩]) unmarked_context_12_23110_244708 node_context_12_23110_244708
  intro a
  fin_cases a
  · exact context_13_92440_3444
  · exact context_13_92441_244669
  · exact context_13_92442_244691
  · exact context_13_92443_244707

theorem selected_cut_08777 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92444) = some ⟨13, 1, 0, 3444, 92444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92444, 1, 16384⟩
    (by decide) selected_cut_08777

theorem selected_cut_08778 : selected 8 ⟨244751, by decide⟩
    (prefixPartial 13 92445) = some ⟨13, 2, 0, 244751, 92445, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_92445_244751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92445 ⟨244751, by decide⟩ :=
  accepted_of_selected 13 92445 ⟨244751, by decide⟩ ⟨13, 2, 0, 244751, 92445, 3089, 16384⟩
    (by decide) selected_cut_08778

theorem selected_cut_08779 : selected 8 ⟨244776, by decide⟩
    (prefixPartial 13 92446) = some ⟨13, 2, 0, 244776, 92446, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_92446_244776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92446 ⟨244776, by decide⟩ :=
  accepted_of_selected 13 92446 ⟨244776, by decide⟩ ⟨13, 2, 0, 244776, 92446, 1929, 16384⟩
    (by decide) selected_cut_08779

theorem selected_cut_08780 : selected 8 ⟨244792, by decide⟩
    (prefixPartial 13 92447) = some ⟨13, 2, 0, 244792, 92447, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_92447_244792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92447 ⟨244792, by decide⟩ :=
  accepted_of_selected 13 92447 ⟨244792, by decide⟩ ⟨13, 2, 0, 244792, 92447, 1105, 16384⟩
    (by decide) selected_cut_08780

theorem unmarked_context_12_23111_244793 : frontier 9 ⟨244793, by decide⟩
    (prefixCache 12 23111) (prefixPartial 12 23111) = false := by
  decide +kernel

theorem node_context_12_23111_244793 : EJMOriginalGlobalDAGData.nodes 9 ⟨244793, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244751, by decide⟩,⟨244776, by decide⟩,⟨244792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23111_244793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23111 ⟨244793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23111
    ⟨244793, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244751, by decide⟩,⟨244776, by decide⟩,⟨244792, by decide⟩]) unmarked_context_12_23111_244793 node_context_12_23111_244793
  intro a
  fin_cases a
  · exact context_13_92444_3444
  · exact context_13_92445_244751
  · exact context_13_92446_244776
  · exact context_13_92447_244792

theorem unmarked_context_11_5777_244794 : frontier 10 ⟨244794, by decide⟩
    (prefixCache 11 5777) (prefixPartial 11 5777) = false := by
  decide +kernel

theorem node_context_11_5777_244794 : EJMOriginalGlobalDAGData.nodes 10 ⟨244794, by decide⟩ =
    .split (coordinate 11) (![⟨244500, by decide⟩,⟨244629, by decide⟩,⟨244708, by decide⟩,⟨244793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5777_244794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5777 ⟨244794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5777
    ⟨244794, by decide⟩ (by decide) (![⟨244500, by decide⟩,⟨244629, by decide⟩,⟨244708, by decide⟩,⟨244793, by decide⟩]) unmarked_context_11_5777_244794 node_context_11_5777_244794
  intro a
  fin_cases a
  · exact context_12_23108_244500
  · exact context_12_23109_244629
  · exact context_12_23110_244708
  · exact context_12_23111_244793

theorem selected_cut_08781 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92448) = some ⟨13, 1, 0, 3444, 92448, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92448_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92448 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92448 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92448, 1, 16384⟩
    (by decide) selected_cut_08781

theorem selected_cut_08782 : selected 8 ⟨244832, by decide⟩
    (prefixPartial 13 92449) = some ⟨13, 2, 0, 244832, 92449, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_92449_244832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92449 ⟨244832, by decide⟩ :=
  accepted_of_selected 13 92449 ⟨244832, by decide⟩ ⟨13, 2, 0, 244832, 92449, 2473, 16384⟩
    (by decide) selected_cut_08782

theorem selected_cut_08783 : selected 8 ⟨244853, by decide⟩
    (prefixPartial 13 92450) = some ⟨13, 2, 0, 244853, 92450, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_92450_244853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92450 ⟨244853, by decide⟩ :=
  accepted_of_selected 13 92450 ⟨244853, by decide⟩ ⟨13, 2, 0, 244853, 92450, 1721, 16384⟩
    (by decide) selected_cut_08783

theorem selected_cut_08784 : selected 8 ⟨244863, by decide⟩
    (prefixPartial 13 92451) = some ⟨13, 2, 0, 244863, 92451, 921, 16384⟩ := by
  decide +kernel

theorem context_13_92451_244863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92451 ⟨244863, by decide⟩ :=
  accepted_of_selected 13 92451 ⟨244863, by decide⟩ ⟨13, 2, 0, 244863, 92451, 921, 16384⟩
    (by decide) selected_cut_08784

theorem unmarked_context_12_23112_244864 : frontier 9 ⟨244864, by decide⟩
    (prefixCache 12 23112) (prefixPartial 12 23112) = false := by
  decide +kernel

theorem node_context_12_23112_244864 : EJMOriginalGlobalDAGData.nodes 9 ⟨244864, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244832, by decide⟩,⟨244853, by decide⟩,⟨244863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23112_244864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23112 ⟨244864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23112
    ⟨244864, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244832, by decide⟩,⟨244853, by decide⟩,⟨244863, by decide⟩]) unmarked_context_12_23112_244864 node_context_12_23112_244864
  intro a
  fin_cases a
  · exact context_13_92448_3444
  · exact context_13_92449_244832
  · exact context_13_92450_244853
  · exact context_13_92451_244863

theorem selected_cut_08785 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92452) = some ⟨13, 1, 0, 3444, 92452, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92452_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92452 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92452 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92452, 1, 16384⟩
    (by decide) selected_cut_08785

theorem selected_cut_08786 : selected 8 ⟨244918, by decide⟩
    (prefixPartial 13 92453) = some ⟨13, 2, 0, 244918, 92453, 3633, 16384⟩ := by
  decide +kernel

theorem context_13_92453_244918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92453 ⟨244918, by decide⟩ :=
  accepted_of_selected 13 92453 ⟨244918, by decide⟩ ⟨13, 2, 0, 244918, 92453, 3633, 16384⟩
    (by decide) selected_cut_08786

theorem selected_cut_08787 : selected 8 ⟨244943, by decide⟩
    (prefixPartial 13 92454) = some ⟨13, 2, 0, 244943, 92454, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_92454_244943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92454 ⟨244943, by decide⟩ :=
  accepted_of_selected 13 92454 ⟨244943, by decide⟩ ⟨13, 2, 0, 244943, 92454, 2073, 16384⟩
    (by decide) selected_cut_08787

theorem selected_cut_08788 : selected 8 ⟨244956, by decide⟩
    (prefixPartial 13 92455) = some ⟨13, 2, 0, 244956, 92455, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_92455_244956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92455 ⟨244956, by decide⟩ :=
  accepted_of_selected 13 92455 ⟨244956, by decide⟩ ⟨13, 2, 0, 244956, 92455, 1205, 16384⟩
    (by decide) selected_cut_08788

theorem unmarked_context_12_23113_244957 : frontier 9 ⟨244957, by decide⟩
    (prefixCache 12 23113) (prefixPartial 12 23113) = false := by
  decide +kernel

theorem node_context_12_23113_244957 : EJMOriginalGlobalDAGData.nodes 9 ⟨244957, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨244918, by decide⟩,⟨244943, by decide⟩,⟨244956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23113_244957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23113 ⟨244957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23113
    ⟨244957, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨244918, by decide⟩,⟨244943, by decide⟩,⟨244956, by decide⟩]) unmarked_context_12_23113_244957 node_context_12_23113_244957
  intro a
  fin_cases a
  · exact context_13_92452_3444
  · exact context_13_92453_244918
  · exact context_13_92454_244943
  · exact context_13_92455_244956

theorem selected_cut_08789 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92456) = some ⟨13, 1, 0, 3444, 92456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92456, 1, 16384⟩
    (by decide) selected_cut_08789

theorem selected_cut_08790 : selected 8 ⟨245020, by decide⟩
    (prefixPartial 13 92457) = some ⟨13, 2, 0, 245020, 92457, 3929, 16384⟩ := by
  decide +kernel

theorem context_13_92457_245020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92457 ⟨245020, by decide⟩ :=
  accepted_of_selected 13 92457 ⟨245020, by decide⟩ ⟨13, 2, 0, 245020, 92457, 3929, 16384⟩
    (by decide) selected_cut_08790

theorem selected_cut_08791 : selected 8 ⟨245093, by decide⟩
    (prefixPartial 13 92458) = some ⟨13, 2, 0, 245093, 92458, 3209, 16384⟩ := by
  decide +kernel

theorem context_13_92458_245093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92458 ⟨245093, by decide⟩ :=
  accepted_of_selected 13 92458 ⟨245093, by decide⟩ ⟨13, 2, 0, 245093, 92458, 3209, 16384⟩
    (by decide) selected_cut_08791

theorem selected_cut_08792 : selected 8 ⟨245107, by decide⟩
    (prefixPartial 13 92459) = some ⟨13, 2, 0, 245107, 92459, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_92459_245107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92459 ⟨245107, by decide⟩ :=
  accepted_of_selected 13 92459 ⟨245107, by decide⟩ ⟨13, 2, 0, 245107, 92459, 1297, 16384⟩
    (by decide) selected_cut_08792

theorem unmarked_context_12_23114_245108 : frontier 9 ⟨245108, by decide⟩
    (prefixCache 12 23114) (prefixPartial 12 23114) = false := by
  decide +kernel

theorem node_context_12_23114_245108 : EJMOriginalGlobalDAGData.nodes 9 ⟨245108, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245020, by decide⟩,⟨245093, by decide⟩,⟨245107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23114_245108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23114 ⟨245108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23114
    ⟨245108, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245020, by decide⟩,⟨245093, by decide⟩,⟨245107, by decide⟩]) unmarked_context_12_23114_245108 node_context_12_23114_245108
  intro a
  fin_cases a
  · exact context_13_92456_3444
  · exact context_13_92457_245020
  · exact context_13_92458_245093
  · exact context_13_92459_245107

theorem selected_cut_08793 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92460) = some ⟨13, 1, 0, 3444, 92460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92460, 1, 16384⟩
    (by decide) selected_cut_08793

theorem selected_cut_08794 : selected 8 ⟨245141, by decide⟩
    (prefixPartial 13 92461) = some ⟨13, 2, 0, 245141, 92461, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_92461_245141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92461 ⟨245141, by decide⟩ :=
  accepted_of_selected 13 92461 ⟨245141, by decide⟩ ⟨13, 2, 0, 245141, 92461, 2609, 16384⟩
    (by decide) selected_cut_08794

theorem selected_cut_08795 : selected 8 ⟨245159, by decide⟩
    (prefixPartial 13 92462) = some ⟨13, 2, 0, 245159, 92462, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_92462_245159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92462 ⟨245159, by decide⟩ :=
  accepted_of_selected 13 92462 ⟨245159, by decide⟩ ⟨13, 2, 0, 245159, 92462, 1905, 16384⟩
    (by decide) selected_cut_08795

theorem selected_cut_08796 : selected 8 ⟨245172, by decide⟩
    (prefixPartial 13 92463) = some ⟨13, 2, 0, 245172, 92463, 965, 16384⟩ := by
  decide +kernel

theorem context_13_92463_245172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92463 ⟨245172, by decide⟩ :=
  accepted_of_selected 13 92463 ⟨245172, by decide⟩ ⟨13, 2, 0, 245172, 92463, 965, 16384⟩
    (by decide) selected_cut_08796

theorem unmarked_context_12_23115_245173 : frontier 9 ⟨245173, by decide⟩
    (prefixCache 12 23115) (prefixPartial 12 23115) = false := by
  decide +kernel

theorem node_context_12_23115_245173 : EJMOriginalGlobalDAGData.nodes 9 ⟨245173, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245141, by decide⟩,⟨245159, by decide⟩,⟨245172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23115_245173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23115 ⟨245173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23115
    ⟨245173, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245141, by decide⟩,⟨245159, by decide⟩,⟨245172, by decide⟩]) unmarked_context_12_23115_245173 node_context_12_23115_245173
  intro a
  fin_cases a
  · exact context_13_92460_3444
  · exact context_13_92461_245141
  · exact context_13_92462_245159
  · exact context_13_92463_245172

theorem unmarked_context_11_5778_245174 : frontier 10 ⟨245174, by decide⟩
    (prefixCache 11 5778) (prefixPartial 11 5778) = false := by
  decide +kernel

theorem node_context_11_5778_245174 : EJMOriginalGlobalDAGData.nodes 10 ⟨245174, by decide⟩ =
    .split (coordinate 11) (![⟨244864, by decide⟩,⟨244957, by decide⟩,⟨245108, by decide⟩,⟨245173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5778_245174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5778 ⟨245174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5778
    ⟨245174, by decide⟩ (by decide) (![⟨244864, by decide⟩,⟨244957, by decide⟩,⟨245108, by decide⟩,⟨245173, by decide⟩]) unmarked_context_11_5778_245174 node_context_11_5778_245174
  intro a
  fin_cases a
  · exact context_12_23112_244864
  · exact context_12_23113_244957
  · exact context_12_23114_245108
  · exact context_12_23115_245173

theorem selected_cut_08797 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92464) = some ⟨13, 1, 0, 3444, 92464, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92464_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92464 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92464 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92464, 1, 16384⟩
    (by decide) selected_cut_08797

theorem selected_cut_08798 : selected 8 ⟨245213, by decide⟩
    (prefixPartial 13 92465) = some ⟨13, 2, 0, 245213, 92465, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_92465_245213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92465 ⟨245213, by decide⟩ :=
  accepted_of_selected 13 92465 ⟨245213, by decide⟩ ⟨13, 2, 0, 245213, 92465, 2769, 16384⟩
    (by decide) selected_cut_08798

theorem selected_cut_08799 : selected 8 ⟨245236, by decide⟩
    (prefixPartial 13 92466) = some ⟨13, 2, 0, 245236, 92466, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_92466_245236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92466 ⟨245236, by decide⟩ :=
  accepted_of_selected 13 92466 ⟨245236, by decide⟩ ⟨13, 2, 0, 245236, 92466, 2045, 16384⟩
    (by decide) selected_cut_08799

theorem selected_cut_08800 : selected 8 ⟨245249, by decide⟩
    (prefixPartial 13 92467) = some ⟨13, 2, 0, 245249, 92467, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_92467_245249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92467 ⟨245249, by decide⟩ :=
  accepted_of_selected 13 92467 ⟨245249, by decide⟩ ⟨13, 2, 0, 245249, 92467, 1205, 16384⟩
    (by decide) selected_cut_08800

theorem unmarked_context_12_23116_245250 : frontier 9 ⟨245250, by decide⟩
    (prefixCache 12 23116) (prefixPartial 12 23116) = false := by
  decide +kernel

theorem node_context_12_23116_245250 : EJMOriginalGlobalDAGData.nodes 9 ⟨245250, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245213, by decide⟩,⟨245236, by decide⟩,⟨245249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23116_245250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23116 ⟨245250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23116
    ⟨245250, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245213, by decide⟩,⟨245236, by decide⟩,⟨245249, by decide⟩]) unmarked_context_12_23116_245250 node_context_12_23116_245250
  intro a
  fin_cases a
  · exact context_13_92464_3444
  · exact context_13_92465_245213
  · exact context_13_92466_245236
  · exact context_13_92467_245249

theorem selected_cut_08801 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92468) = some ⟨13, 1, 0, 3444, 92468, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92468_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92468 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92468 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92468, 1, 16384⟩
    (by decide) selected_cut_08801

theorem selected_cut_08802 : selected 8 ⟨245315, by decide⟩
    (prefixPartial 13 92469) = some ⟨13, 2, 0, 245315, 92469, 3869, 16384⟩ := by
  decide +kernel

theorem context_13_92469_245315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92469 ⟨245315, by decide⟩ :=
  accepted_of_selected 13 92469 ⟨245315, by decide⟩ ⟨13, 2, 0, 245315, 92469, 3869, 16384⟩
    (by decide) selected_cut_08802

theorem selected_cut_08803 : selected 8 ⟨245350, by decide⟩
    (prefixPartial 13 92470) = some ⟨13, 2, 0, 245350, 92470, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_92470_245350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92470 ⟨245350, by decide⟩ :=
  accepted_of_selected 13 92470 ⟨245350, by decide⟩ ⟨13, 2, 0, 245350, 92470, 2381, 16384⟩
    (by decide) selected_cut_08803

theorem selected_cut_08804 : selected 8 ⟨245381, by decide⟩
    (prefixPartial 13 92471) = some ⟨13, 2, 0, 245381, 92471, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_92471_245381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92471 ⟨245381, by decide⟩ :=
  accepted_of_selected 13 92471 ⟨245381, by decide⟩ ⟨13, 2, 0, 245381, 92471, 1429, 16384⟩
    (by decide) selected_cut_08804

theorem unmarked_context_12_23117_245382 : frontier 9 ⟨245382, by decide⟩
    (prefixCache 12 23117) (prefixPartial 12 23117) = false := by
  decide +kernel

theorem node_context_12_23117_245382 : EJMOriginalGlobalDAGData.nodes 9 ⟨245382, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245315, by decide⟩,⟨245350, by decide⟩,⟨245381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23117_245382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23117 ⟨245382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23117
    ⟨245382, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245315, by decide⟩,⟨245350, by decide⟩,⟨245381, by decide⟩]) unmarked_context_12_23117_245382 node_context_12_23117_245382
  intro a
  fin_cases a
  · exact context_13_92468_3444
  · exact context_13_92469_245315
  · exact context_13_92470_245350
  · exact context_13_92471_245381

theorem selected_cut_08805 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92472) = some ⟨13, 1, 0, 3444, 92472, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92472_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92472 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92472 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92472, 1, 16384⟩
    (by decide) selected_cut_08805

theorem selected_cut_08806 : selected 8 ⟨245414, by decide⟩
    (prefixPartial 13 92473) = some ⟨13, 2, 0, 245414, 92473, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_92473_245414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92473 ⟨245414, by decide⟩ :=
  accepted_of_selected 13 92473 ⟨245414, by decide⟩ ⟨13, 2, 0, 245414, 92473, 2753, 16384⟩
    (by decide) selected_cut_08806

theorem selected_cut_08807 : selected 8 ⟨245440, by decide⟩
    (prefixPartial 13 92474) = some ⟨13, 2, 0, 245440, 92474, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_92474_245440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92474 ⟨245440, by decide⟩ :=
  accepted_of_selected 13 92474 ⟨245440, by decide⟩ ⟨13, 2, 0, 245440, 92474, 2005, 16384⟩
    (by decide) selected_cut_08807

theorem selected_cut_08808 : selected 8 ⟨245453, by decide⟩
    (prefixPartial 13 92475) = some ⟨13, 2, 0, 245453, 92475, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_92475_245453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92475 ⟨245453, by decide⟩ :=
  accepted_of_selected 13 92475 ⟨245453, by decide⟩ ⟨13, 2, 0, 245453, 92475, 1101, 16384⟩
    (by decide) selected_cut_08808

theorem unmarked_context_12_23118_245454 : frontier 9 ⟨245454, by decide⟩
    (prefixCache 12 23118) (prefixPartial 12 23118) = false := by
  decide +kernel

theorem node_context_12_23118_245454 : EJMOriginalGlobalDAGData.nodes 9 ⟨245454, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245414, by decide⟩,⟨245440, by decide⟩,⟨245453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23118_245454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23118 ⟨245454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23118
    ⟨245454, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245414, by decide⟩,⟨245440, by decide⟩,⟨245453, by decide⟩]) unmarked_context_12_23118_245454 node_context_12_23118_245454
  intro a
  fin_cases a
  · exact context_13_92472_3444
  · exact context_13_92473_245414
  · exact context_13_92474_245440
  · exact context_13_92475_245453

theorem selected_cut_08809 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92476) = some ⟨13, 1, 0, 3444, 92476, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92476_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92476 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92476 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92476, 1, 16384⟩
    (by decide) selected_cut_08809

theorem selected_cut_08810 : selected 8 ⟨245480, by decide⟩
    (prefixPartial 13 92477) = some ⟨13, 2, 0, 245480, 92477, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_92477_245480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92477 ⟨245480, by decide⟩ :=
  accepted_of_selected 13 92477 ⟨245480, by decide⟩ ⟨13, 2, 0, 245480, 92477, 2517, 16384⟩
    (by decide) selected_cut_08810

theorem selected_cut_08811 : selected 8 ⟨245499, by decide⟩
    (prefixPartial 13 92478) = some ⟨13, 2, 0, 245499, 92478, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_92478_245499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92478 ⟨245499, by decide⟩ :=
  accepted_of_selected 13 92478 ⟨245499, by decide⟩ ⟨13, 2, 0, 245499, 92478, 2061, 16384⟩
    (by decide) selected_cut_08811

theorem selected_cut_08812 : selected 8 ⟨245511, by decide⟩
    (prefixPartial 13 92479) = some ⟨13, 2, 0, 245511, 92479, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_92479_245511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92479 ⟨245511, by decide⟩ :=
  accepted_of_selected 13 92479 ⟨245511, by decide⟩ ⟨13, 2, 0, 245511, 92479, 1241, 16384⟩
    (by decide) selected_cut_08812

theorem unmarked_context_12_23119_245512 : frontier 9 ⟨245512, by decide⟩
    (prefixCache 12 23119) (prefixPartial 12 23119) = false := by
  decide +kernel

theorem node_context_12_23119_245512 : EJMOriginalGlobalDAGData.nodes 9 ⟨245512, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245480, by decide⟩,⟨245499, by decide⟩,⟨245511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23119_245512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23119 ⟨245512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23119
    ⟨245512, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245480, by decide⟩,⟨245499, by decide⟩,⟨245511, by decide⟩]) unmarked_context_12_23119_245512 node_context_12_23119_245512
  intro a
  fin_cases a
  · exact context_13_92476_3444
  · exact context_13_92477_245480
  · exact context_13_92478_245499
  · exact context_13_92479_245511

theorem unmarked_context_11_5779_245513 : frontier 10 ⟨245513, by decide⟩
    (prefixCache 11 5779) (prefixPartial 11 5779) = false := by
  decide +kernel

theorem node_context_11_5779_245513 : EJMOriginalGlobalDAGData.nodes 10 ⟨245513, by decide⟩ =
    .split (coordinate 11) (![⟨245250, by decide⟩,⟨245382, by decide⟩,⟨245454, by decide⟩,⟨245512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5779_245513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5779 ⟨245513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5779
    ⟨245513, by decide⟩ (by decide) (![⟨245250, by decide⟩,⟨245382, by decide⟩,⟨245454, by decide⟩,⟨245512, by decide⟩]) unmarked_context_11_5779_245513 node_context_11_5779_245513
  intro a
  fin_cases a
  · exact context_12_23116_245250
  · exact context_12_23117_245382
  · exact context_12_23118_245454
  · exact context_12_23119_245512

theorem unmarked_context_10_1444_245514 : frontier 11 ⟨245514, by decide⟩
    (prefixCache 10 1444) (prefixPartial 10 1444) = false := by
  decide +kernel

theorem node_context_10_1444_245514 : EJMOriginalGlobalDAGData.nodes 11 ⟨245514, by decide⟩ =
    .split (coordinate 10) (![⟨244409, by decide⟩,⟨244794, by decide⟩,⟨245174, by decide⟩,⟨245513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1444_245514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1444 ⟨245514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1444
    ⟨245514, by decide⟩ (by decide) (![⟨244409, by decide⟩,⟨244794, by decide⟩,⟨245174, by decide⟩,⟨245513, by decide⟩]) unmarked_context_10_1444_245514 node_context_10_1444_245514
  intro a
  fin_cases a
  · exact context_11_5776_244409
  · exact context_11_5777_244794
  · exact context_11_5778_245174
  · exact context_11_5779_245513

theorem selected_cut_08813 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92480) = some ⟨13, 1, 0, 3444, 92480, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92480_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92480 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92480 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92480, 1, 16384⟩
    (by decide) selected_cut_08813

theorem selected_cut_08814 : selected 8 ⟨245536, by decide⟩
    (prefixPartial 13 92481) = some ⟨13, 2, 0, 245536, 92481, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_92481_245536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92481 ⟨245536, by decide⟩ :=
  accepted_of_selected 13 92481 ⟨245536, by decide⟩ ⟨13, 2, 0, 245536, 92481, 2033, 16384⟩
    (by decide) selected_cut_08814

theorem selected_cut_08815 : selected 8 ⟨245556, by decide⟩
    (prefixPartial 13 92482) = some ⟨13, 2, 0, 245556, 92482, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_92482_245556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92482 ⟨245556, by decide⟩ :=
  accepted_of_selected 13 92482 ⟨245556, by decide⟩ ⟨13, 2, 0, 245556, 92482, 1381, 16384⟩
    (by decide) selected_cut_08815

theorem selected_cut_08816 : selected 8 ⟨245567, by decide⟩
    (prefixPartial 13 92483) = some ⟨13, 2, 0, 245567, 92483, 949, 16384⟩ := by
  decide +kernel

theorem context_13_92483_245567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92483 ⟨245567, by decide⟩ :=
  accepted_of_selected 13 92483 ⟨245567, by decide⟩ ⟨13, 2, 0, 245567, 92483, 949, 16384⟩
    (by decide) selected_cut_08816

theorem unmarked_context_12_23120_245568 : frontier 9 ⟨245568, by decide⟩
    (prefixCache 12 23120) (prefixPartial 12 23120) = false := by
  decide +kernel

theorem node_context_12_23120_245568 : EJMOriginalGlobalDAGData.nodes 9 ⟨245568, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245536, by decide⟩,⟨245556, by decide⟩,⟨245567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23120_245568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23120 ⟨245568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23120
    ⟨245568, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245536, by decide⟩,⟨245556, by decide⟩,⟨245567, by decide⟩]) unmarked_context_12_23120_245568 node_context_12_23120_245568
  intro a
  fin_cases a
  · exact context_13_92480_3444
  · exact context_13_92481_245536
  · exact context_13_92482_245556
  · exact context_13_92483_245567

theorem selected_cut_08817 : selected 9 ⟨245678, by decide⟩
    (prefixPartial 12 23121) = some ⟨12, 2, 0, 245678, 23121, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_23121_245678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23121 ⟨245678, by decide⟩ :=
  accepted_of_selected 12 23121 ⟨245678, by decide⟩ ⟨12, 2, 0, 245678, 23121, 2013, 65536⟩
    (by decide) selected_cut_08817

theorem selected_cut_08818 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92488) = some ⟨13, 1, 0, 3444, 92488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92488, 1, 16384⟩
    (by decide) selected_cut_08818

theorem selected_cut_08819 : selected 8 ⟨245705, by decide⟩
    (prefixPartial 13 92489) = some ⟨13, 2, 0, 245705, 92489, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_92489_245705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92489 ⟨245705, by decide⟩ :=
  accepted_of_selected 13 92489 ⟨245705, by decide⟩ ⟨13, 2, 0, 245705, 92489, 2325, 16384⟩
    (by decide) selected_cut_08819

theorem selected_cut_08820 : selected 8 ⟨245724, by decide⟩
    (prefixPartial 13 92490) = some ⟨13, 2, 0, 245724, 92490, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_92490_245724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92490 ⟨245724, by decide⟩ :=
  accepted_of_selected 13 92490 ⟨245724, by decide⟩ ⟨13, 2, 0, 245724, 92490, 1649, 16384⟩
    (by decide) selected_cut_08820

theorem selected_cut_08821 : selected 8 ⟨245734, by decide⟩
    (prefixPartial 13 92491) = some ⟨13, 2, 0, 245734, 92491, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_92491_245734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92491 ⟨245734, by decide⟩ :=
  accepted_of_selected 13 92491 ⟨245734, by decide⟩ ⟨13, 2, 0, 245734, 92491, 1029, 16384⟩
    (by decide) selected_cut_08821

theorem unmarked_context_12_23122_245735 : frontier 9 ⟨245735, by decide⟩
    (prefixCache 12 23122) (prefixPartial 12 23122) = false := by
  decide +kernel

theorem node_context_12_23122_245735 : EJMOriginalGlobalDAGData.nodes 9 ⟨245735, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245705, by decide⟩,⟨245724, by decide⟩,⟨245734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23122_245735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23122 ⟨245735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23122
    ⟨245735, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245705, by decide⟩,⟨245724, by decide⟩,⟨245734, by decide⟩]) unmarked_context_12_23122_245735 node_context_12_23122_245735
  intro a
  fin_cases a
  · exact context_13_92488_3444
  · exact context_13_92489_245705
  · exact context_13_92490_245724
  · exact context_13_92491_245734

theorem selected_cut_08822 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92492) = some ⟨13, 1, 0, 3444, 92492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92492, 1, 16384⟩
    (by decide) selected_cut_08822

theorem selected_cut_08823 : selected 8 ⟨245769, by decide⟩
    (prefixPartial 13 92493) = some ⟨13, 2, 0, 245769, 92493, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_92493_245769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92493 ⟨245769, by decide⟩ :=
  accepted_of_selected 13 92493 ⟨245769, by decide⟩ ⟨13, 2, 0, 245769, 92493, 2601, 16384⟩
    (by decide) selected_cut_08823

theorem selected_cut_08824 : selected 8 ⟨245791, by decide⟩
    (prefixPartial 13 92494) = some ⟨13, 2, 0, 245791, 92494, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_92494_245791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92494 ⟨245791, by decide⟩ :=
  accepted_of_selected 13 92494 ⟨245791, by decide⟩ ⟨13, 2, 0, 245791, 92494, 1813, 16384⟩
    (by decide) selected_cut_08824

theorem selected_cut_08825 : selected 8 ⟨245807, by decide⟩
    (prefixPartial 13 92495) = some ⟨13, 2, 0, 245807, 92495, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_92495_245807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92495 ⟨245807, by decide⟩ :=
  accepted_of_selected 13 92495 ⟨245807, by decide⟩ ⟨13, 2, 0, 245807, 92495, 1077, 16384⟩
    (by decide) selected_cut_08825

theorem unmarked_context_12_23123_245808 : frontier 9 ⟨245808, by decide⟩
    (prefixCache 12 23123) (prefixPartial 12 23123) = false := by
  decide +kernel

theorem node_context_12_23123_245808 : EJMOriginalGlobalDAGData.nodes 9 ⟨245808, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245769, by decide⟩,⟨245791, by decide⟩,⟨245807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23123_245808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23123 ⟨245808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23123
    ⟨245808, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245769, by decide⟩,⟨245791, by decide⟩,⟨245807, by decide⟩]) unmarked_context_12_23123_245808 node_context_12_23123_245808
  intro a
  fin_cases a
  · exact context_13_92492_3444
  · exact context_13_92493_245769
  · exact context_13_92494_245791
  · exact context_13_92495_245807

theorem unmarked_context_11_5780_245809 : frontier 10 ⟨245809, by decide⟩
    (prefixCache 11 5780) (prefixPartial 11 5780) = false := by
  decide +kernel

theorem node_context_11_5780_245809 : EJMOriginalGlobalDAGData.nodes 10 ⟨245809, by decide⟩ =
    .split (coordinate 11) (![⟨245568, by decide⟩,⟨245678, by decide⟩,⟨245735, by decide⟩,⟨245808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5780_245809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5780 ⟨245809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5780
    ⟨245809, by decide⟩ (by decide) (![⟨245568, by decide⟩,⟨245678, by decide⟩,⟨245735, by decide⟩,⟨245808, by decide⟩]) unmarked_context_11_5780_245809 node_context_11_5780_245809
  intro a
  fin_cases a
  · exact context_12_23120_245568
  · exact context_12_23121_245678
  · exact context_12_23122_245735
  · exact context_12_23123_245808

theorem selected_cut_08826 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92496) = some ⟨13, 1, 0, 3444, 92496, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92496_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92496 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92496 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92496, 1, 16384⟩
    (by decide) selected_cut_08826

theorem selected_cut_08827 : selected 8 ⟨245830, by decide⟩
    (prefixPartial 13 92497) = some ⟨13, 2, 0, 245830, 92497, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_92497_245830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92497 ⟨245830, by decide⟩ :=
  accepted_of_selected 13 92497 ⟨245830, by decide⟩ ⟨13, 2, 0, 245830, 92497, 1841, 16384⟩
    (by decide) selected_cut_08827

theorem selected_cut_08828 : selected 8 ⟨245852, by decide⟩
    (prefixPartial 13 92498) = some ⟨13, 2, 0, 245852, 92498, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_92498_245852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92498 ⟨245852, by decide⟩ :=
  accepted_of_selected 13 92498 ⟨245852, by decide⟩ ⟨13, 2, 0, 245852, 92498, 1353, 16384⟩
    (by decide) selected_cut_08828

theorem selected_cut_08829 : selected 8 ⟨245863, by decide⟩
    (prefixPartial 13 92499) = some ⟨13, 2, 0, 245863, 92499, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_92499_245863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92499 ⟨245863, by decide⟩ :=
  accepted_of_selected 13 92499 ⟨245863, by decide⟩ ⟨13, 2, 0, 245863, 92499, 1073, 16384⟩
    (by decide) selected_cut_08829

theorem unmarked_context_12_23124_245864 : frontier 9 ⟨245864, by decide⟩
    (prefixCache 12 23124) (prefixPartial 12 23124) = false := by
  decide +kernel

theorem node_context_12_23124_245864 : EJMOriginalGlobalDAGData.nodes 9 ⟨245864, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245830, by decide⟩,⟨245852, by decide⟩,⟨245863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23124_245864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23124 ⟨245864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23124
    ⟨245864, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245830, by decide⟩,⟨245852, by decide⟩,⟨245863, by decide⟩]) unmarked_context_12_23124_245864 node_context_12_23124_245864
  intro a
  fin_cases a
  · exact context_13_92496_3444
  · exact context_13_92497_245830
  · exact context_13_92498_245852
  · exact context_13_92499_245863

theorem selected_cut_08830 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 23125) = some ⟨12, 1, 0, 170504, 23125, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23125_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23125 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 23125 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 23125, 1, 65536⟩
    (by decide) selected_cut_08830

theorem selected_cut_08831 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92504) = some ⟨13, 1, 0, 3444, 92504, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92504_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92504 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92504 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92504, 1, 16384⟩
    (by decide) selected_cut_08831

theorem selected_cut_08832 : selected 8 ⟨245884, by decide⟩
    (prefixPartial 13 92505) = some ⟨13, 2, 0, 245884, 92505, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_92505_245884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92505 ⟨245884, by decide⟩ :=
  accepted_of_selected 13 92505 ⟨245884, by decide⟩ ⟨13, 2, 0, 245884, 92505, 1881, 16384⟩
    (by decide) selected_cut_08832

theorem selected_cut_08833 : selected 8 ⟨245901, by decide⟩
    (prefixPartial 13 92506) = some ⟨13, 2, 0, 245901, 92506, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_92506_245901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92506 ⟨245901, by decide⟩ :=
  accepted_of_selected 13 92506 ⟨245901, by decide⟩ ⟨13, 2, 0, 245901, 92506, 1545, 16384⟩
    (by decide) selected_cut_08833

theorem selected_cut_08834 : selected 8 ⟨245915, by decide⟩
    (prefixPartial 13 92507) = some ⟨13, 2, 0, 245915, 92507, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_92507_245915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92507 ⟨245915, by decide⟩ :=
  accepted_of_selected 13 92507 ⟨245915, by decide⟩ ⟨13, 2, 0, 245915, 92507, 1121, 16384⟩
    (by decide) selected_cut_08834

theorem unmarked_context_12_23126_245916 : frontier 9 ⟨245916, by decide⟩
    (prefixCache 12 23126) (prefixPartial 12 23126) = false := by
  decide +kernel

theorem node_context_12_23126_245916 : EJMOriginalGlobalDAGData.nodes 9 ⟨245916, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245884, by decide⟩,⟨245901, by decide⟩,⟨245915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23126_245916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23126 ⟨245916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23126
    ⟨245916, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245884, by decide⟩,⟨245901, by decide⟩,⟨245915, by decide⟩]) unmarked_context_12_23126_245916 node_context_12_23126_245916
  intro a
  fin_cases a
  · exact context_13_92504_3444
  · exact context_13_92505_245884
  · exact context_13_92506_245901
  · exact context_13_92507_245915

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
