/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover198
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19107 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288060) = some ⟨13, 1, 0, 3444, 288060, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288060_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288060 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288060 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288060, 1, 16384⟩
    (by decide) selected_cut_19107

theorem selected_cut_19108 : selected 8 ⟨489369, by decide⟩
    (prefixPartial 13 288061) = some ⟨13, 2, 0, 489369, 288061, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_288061_489369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288061 ⟨489369, by decide⟩ :=
  accepted_of_selected 13 288061 ⟨489369, by decide⟩ ⟨13, 2, 0, 489369, 288061, 2393, 16384⟩
    (by decide) selected_cut_19108

theorem selected_cut_19109 : selected 8 ⟨489396, by decide⟩
    (prefixPartial 13 288062) = some ⟨13, 2, 0, 489396, 288062, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_288062_489396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288062 ⟨489396, by decide⟩ :=
  accepted_of_selected 13 288062 ⟨489396, by decide⟩ ⟨13, 2, 0, 489396, 288062, 2325, 16384⟩
    (by decide) selected_cut_19109

theorem selected_cut_19110 : selected 8 ⟨489402, by decide⟩
    (prefixPartial 13 288063) = some ⟨13, 2, 0, 489402, 288063, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_288063_489402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288063 ⟨489402, by decide⟩ :=
  accepted_of_selected 13 288063 ⟨489402, by decide⟩ ⟨13, 2, 0, 489402, 288063, 1205, 16384⟩
    (by decide) selected_cut_19110

theorem unmarked_context_12_72015_489403 : frontier 9 ⟨489403, by decide⟩
    (prefixCache 12 72015) (prefixPartial 12 72015) = false := by
  decide +kernel

theorem node_context_12_72015_489403 : EJMOriginalGlobalDAGData.nodes 9 ⟨489403, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489369, by decide⟩,⟨489396, by decide⟩,⟨489402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72015_489403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72015 ⟨489403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72015
    ⟨489403, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489369, by decide⟩,⟨489396, by decide⟩,⟨489402, by decide⟩]) unmarked_context_12_72015_489403 node_context_12_72015_489403
  intro a
  fin_cases a
  · exact context_13_288060_3444
  · exact context_13_288061_489369
  · exact context_13_288062_489396
  · exact context_13_288063_489402

theorem unmarked_context_11_18003_489404 : frontier 10 ⟨489404, by decide⟩
    (prefixCache 11 18003) (prefixPartial 11 18003) = false := by
  decide +kernel

theorem node_context_11_18003_489404 : EJMOriginalGlobalDAGData.nodes 10 ⟨489404, by decide⟩ =
    .split (coordinate 11) (![⟨489205, by decide⟩,⟨489265, by decide⟩,⟨489345, by decide⟩,⟨489403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18003_489404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18003 ⟨489404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18003
    ⟨489404, by decide⟩ (by decide) (![⟨489205, by decide⟩,⟨489265, by decide⟩,⟨489345, by decide⟩,⟨489403, by decide⟩]) unmarked_context_11_18003_489404 node_context_11_18003_489404
  intro a
  fin_cases a
  · exact context_12_72012_489205
  · exact context_12_72013_489265
  · exact context_12_72014_489345
  · exact context_12_72015_489403

theorem unmarked_context_10_4500_489405 : frontier 11 ⟨489405, by decide⟩
    (prefixCache 10 4500) (prefixPartial 10 4500) = false := by
  decide +kernel

theorem node_context_10_4500_489405 : EJMOriginalGlobalDAGData.nodes 11 ⟨489405, by decide⟩ =
    .split (coordinate 10) (![⟨488698, by decide⟩,⟨488933, by decide⟩,⟨489153, by decide⟩,⟨489404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4500_489405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4500 ⟨489405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4500
    ⟨489405, by decide⟩ (by decide) (![⟨488698, by decide⟩,⟨488933, by decide⟩,⟨489153, by decide⟩,⟨489404, by decide⟩]) unmarked_context_10_4500_489405 node_context_10_4500_489405
  intro a
  fin_cases a
  · exact context_11_18000_488698
  · exact context_11_18001_488933
  · exact context_11_18002_489153
  · exact context_11_18003_489404

theorem selected_cut_19111 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288064) = some ⟨13, 1, 0, 3444, 288064, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288064_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288064 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288064 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288064, 1, 16384⟩
    (by decide) selected_cut_19111

theorem selected_cut_19112 : selected 8 ⟨489430, by decide⟩
    (prefixPartial 13 288065) = some ⟨13, 2, 0, 489430, 288065, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_288065_489430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288065 ⟨489430, by decide⟩ :=
  accepted_of_selected 13 288065 ⟨489430, by decide⟩ ⟨13, 2, 0, 489430, 288065, 1689, 16384⟩
    (by decide) selected_cut_19112

theorem selected_cut_19113 : selected 8 ⟨489455, by decide⟩
    (prefixPartial 13 288066) = some ⟨13, 2, 0, 489455, 288066, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_288066_489455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288066 ⟨489455, by decide⟩ :=
  accepted_of_selected 13 288066 ⟨489455, by decide⟩ ⟨13, 2, 0, 489455, 288066, 1785, 16384⟩
    (by decide) selected_cut_19113

theorem selected_cut_19114 : selected 8 ⟨489463, by decide⟩
    (prefixPartial 13 288067) = some ⟨13, 2, 0, 489463, 288067, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_288067_489463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288067 ⟨489463, by decide⟩ :=
  accepted_of_selected 13 288067 ⟨489463, by decide⟩ ⟨13, 2, 0, 489463, 288067, 1077, 16384⟩
    (by decide) selected_cut_19114

theorem unmarked_context_12_72016_489464 : frontier 9 ⟨489464, by decide⟩
    (prefixCache 12 72016) (prefixPartial 12 72016) = false := by
  decide +kernel

theorem node_context_12_72016_489464 : EJMOriginalGlobalDAGData.nodes 9 ⟨489464, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489430, by decide⟩,⟨489455, by decide⟩,⟨489463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72016_489464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72016 ⟨489464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72016
    ⟨489464, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489430, by decide⟩,⟨489455, by decide⟩,⟨489463, by decide⟩]) unmarked_context_12_72016_489464 node_context_12_72016_489464
  intro a
  fin_cases a
  · exact context_13_288064_3444
  · exact context_13_288065_489430
  · exact context_13_288066_489455
  · exact context_13_288067_489463

theorem selected_cut_19115 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288068) = some ⟨13, 1, 0, 3444, 288068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288068, 1, 16384⟩
    (by decide) selected_cut_19115

theorem selected_cut_19116 : selected 8 ⟨489488, by decide⟩
    (prefixPartial 13 288069) = some ⟨13, 2, 0, 489488, 288069, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_288069_489488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288069 ⟨489488, by decide⟩ :=
  accepted_of_selected 13 288069 ⟨489488, by decide⟩ ⟨13, 2, 0, 489488, 288069, 1661, 16384⟩
    (by decide) selected_cut_19116

theorem selected_cut_19117 : selected 8 ⟨489510, by decide⟩
    (prefixPartial 13 288070) = some ⟨13, 2, 0, 489510, 288070, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_288070_489510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288070 ⟨489510, by decide⟩ :=
  accepted_of_selected 13 288070 ⟨489510, by decide⟩ ⟨13, 2, 0, 489510, 288070, 1881, 16384⟩
    (by decide) selected_cut_19117

theorem selected_cut_19118 : selected 8 ⟨489519, by decide⟩
    (prefixPartial 13 288071) = some ⟨13, 2, 0, 489519, 288071, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_288071_489519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288071 ⟨489519, by decide⟩ :=
  accepted_of_selected 13 288071 ⟨489519, by decide⟩ ⟨13, 2, 0, 489519, 288071, 1157, 16384⟩
    (by decide) selected_cut_19118

theorem unmarked_context_12_72017_489520 : frontier 9 ⟨489520, by decide⟩
    (prefixCache 12 72017) (prefixPartial 12 72017) = false := by
  decide +kernel

theorem node_context_12_72017_489520 : EJMOriginalGlobalDAGData.nodes 9 ⟨489520, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489488, by decide⟩,⟨489510, by decide⟩,⟨489519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72017_489520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72017 ⟨489520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72017
    ⟨489520, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489488, by decide⟩,⟨489510, by decide⟩,⟨489519, by decide⟩]) unmarked_context_12_72017_489520 node_context_12_72017_489520
  intro a
  fin_cases a
  · exact context_13_288068_3444
  · exact context_13_288069_489488
  · exact context_13_288070_489510
  · exact context_13_288071_489519

theorem selected_cut_19119 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288072) = some ⟨13, 1, 0, 3444, 288072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288072, 1, 16384⟩
    (by decide) selected_cut_19119

theorem selected_cut_19120 : selected 8 ⟨489563, by decide⟩
    (prefixPartial 13 288073) = some ⟨13, 2, 0, 489563, 288073, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_288073_489563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288073 ⟨489563, by decide⟩ :=
  accepted_of_selected 13 288073 ⟨489563, by decide⟩ ⟨13, 2, 0, 489563, 288073, 2277, 16384⟩
    (by decide) selected_cut_19120

theorem selected_cut_19121 : selected 8 ⟨489597, by decide⟩
    (prefixPartial 13 288074) = some ⟨13, 2, 0, 489597, 288074, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_288074_489597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288074 ⟨489597, by decide⟩ :=
  accepted_of_selected 13 288074 ⟨489597, by decide⟩ ⟨13, 2, 0, 489597, 288074, 2417, 16384⟩
    (by decide) selected_cut_19121

theorem selected_cut_19122 : selected 8 ⟨489611, by decide⟩
    (prefixPartial 13 288075) = some ⟨13, 2, 0, 489611, 288075, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_288075_489611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288075 ⟨489611, by decide⟩ :=
  accepted_of_selected 13 288075 ⟨489611, by decide⟩ ⟨13, 2, 0, 489611, 288075, 1261, 16384⟩
    (by decide) selected_cut_19122

theorem unmarked_context_12_72018_489612 : frontier 9 ⟨489612, by decide⟩
    (prefixCache 12 72018) (prefixPartial 12 72018) = false := by
  decide +kernel

theorem node_context_12_72018_489612 : EJMOriginalGlobalDAGData.nodes 9 ⟨489612, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489563, by decide⟩,⟨489597, by decide⟩,⟨489611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72018_489612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72018 ⟨489612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72018
    ⟨489612, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489563, by decide⟩,⟨489597, by decide⟩,⟨489611, by decide⟩]) unmarked_context_12_72018_489612 node_context_12_72018_489612
  intro a
  fin_cases a
  · exact context_13_288072_3444
  · exact context_13_288073_489563
  · exact context_13_288074_489597
  · exact context_13_288075_489611

theorem selected_cut_19123 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288076) = some ⟨13, 1, 0, 3444, 288076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288076, 1, 16384⟩
    (by decide) selected_cut_19123

theorem selected_cut_19124 : selected 8 ⟨489642, by decide⟩
    (prefixPartial 13 288077) = some ⟨13, 2, 0, 489642, 288077, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_288077_489642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288077 ⟨489642, by decide⟩ :=
  accepted_of_selected 13 288077 ⟨489642, by decide⟩ ⟨13, 2, 0, 489642, 288077, 2177, 16384⟩
    (by decide) selected_cut_19124

theorem selected_cut_19125 : selected 8 ⟨489682, by decide⟩
    (prefixPartial 13 288078) = some ⟨13, 2, 0, 489682, 288078, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_288078_489682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288078 ⟨489682, by decide⟩ :=
  accepted_of_selected 13 288078 ⟨489682, by decide⟩ ⟨13, 2, 0, 489682, 288078, 2545, 16384⟩
    (by decide) selected_cut_19125

theorem selected_cut_19126 : selected 8 ⟨489694, by decide⟩
    (prefixPartial 13 288079) = some ⟨13, 2, 0, 489694, 288079, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_288079_489694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288079 ⟨489694, by decide⟩ :=
  accepted_of_selected 13 288079 ⟨489694, by decide⟩ ⟨13, 2, 0, 489694, 288079, 1153, 16384⟩
    (by decide) selected_cut_19126

theorem unmarked_context_12_72019_489695 : frontier 9 ⟨489695, by decide⟩
    (prefixCache 12 72019) (prefixPartial 12 72019) = false := by
  decide +kernel

theorem node_context_12_72019_489695 : EJMOriginalGlobalDAGData.nodes 9 ⟨489695, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489642, by decide⟩,⟨489682, by decide⟩,⟨489694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72019_489695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72019 ⟨489695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72019
    ⟨489695, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489642, by decide⟩,⟨489682, by decide⟩,⟨489694, by decide⟩]) unmarked_context_12_72019_489695 node_context_12_72019_489695
  intro a
  fin_cases a
  · exact context_13_288076_3444
  · exact context_13_288077_489642
  · exact context_13_288078_489682
  · exact context_13_288079_489694

theorem unmarked_context_11_18004_489696 : frontier 10 ⟨489696, by decide⟩
    (prefixCache 11 18004) (prefixPartial 11 18004) = false := by
  decide +kernel

theorem node_context_11_18004_489696 : EJMOriginalGlobalDAGData.nodes 10 ⟨489696, by decide⟩ =
    .split (coordinate 11) (![⟨489464, by decide⟩,⟨489520, by decide⟩,⟨489612, by decide⟩,⟨489695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18004_489696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18004 ⟨489696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18004
    ⟨489696, by decide⟩ (by decide) (![⟨489464, by decide⟩,⟨489520, by decide⟩,⟨489612, by decide⟩,⟨489695, by decide⟩]) unmarked_context_11_18004_489696 node_context_11_18004_489696
  intro a
  fin_cases a
  · exact context_12_72016_489464
  · exact context_12_72017_489520
  · exact context_12_72018_489612
  · exact context_12_72019_489695

theorem selected_cut_19127 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288080) = some ⟨13, 1, 0, 3444, 288080, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288080_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288080 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288080 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288080, 1, 16384⟩
    (by decide) selected_cut_19127

theorem selected_cut_19128 : selected 8 ⟨489716, by decide⟩
    (prefixPartial 13 288081) = some ⟨13, 2, 0, 489716, 288081, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_288081_489716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288081 ⟨489716, by decide⟩ :=
  accepted_of_selected 13 288081 ⟨489716, by decide⟩ ⟨13, 2, 0, 489716, 288081, 1685, 16384⟩
    (by decide) selected_cut_19128

theorem selected_cut_19129 : selected 8 ⟨489734, by decide⟩
    (prefixPartial 13 288082) = some ⟨13, 2, 0, 489734, 288082, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_288082_489734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288082 ⟨489734, by decide⟩ :=
  accepted_of_selected 13 288082 ⟨489734, by decide⟩ ⟨13, 2, 0, 489734, 288082, 1985, 16384⟩
    (by decide) selected_cut_19129

theorem selected_cut_19130 : selected 8 ⟨489739, by decide⟩
    (prefixPartial 13 288083) = some ⟨13, 2, 0, 489739, 288083, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_288083_489739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288083 ⟨489739, by decide⟩ :=
  accepted_of_selected 13 288083 ⟨489739, by decide⟩ ⟨13, 2, 0, 489739, 288083, 1117, 16384⟩
    (by decide) selected_cut_19130

theorem unmarked_context_12_72020_489740 : frontier 9 ⟨489740, by decide⟩
    (prefixCache 12 72020) (prefixPartial 12 72020) = false := by
  decide +kernel

theorem node_context_12_72020_489740 : EJMOriginalGlobalDAGData.nodes 9 ⟨489740, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489716, by decide⟩,⟨489734, by decide⟩,⟨489739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72020_489740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72020 ⟨489740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72020
    ⟨489740, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489716, by decide⟩,⟨489734, by decide⟩,⟨489739, by decide⟩]) unmarked_context_12_72020_489740 node_context_12_72020_489740
  intro a
  fin_cases a
  · exact context_13_288080_3444
  · exact context_13_288081_489716
  · exact context_13_288082_489734
  · exact context_13_288083_489739

theorem selected_cut_19131 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 72021) = some ⟨12, 1, 0, 439069, 72021, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72021_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72021 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 72021 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 72021, 1, 65536⟩
    (by decide) selected_cut_19131

theorem selected_cut_19132 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288088) = some ⟨13, 1, 0, 3444, 288088, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288088_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288088 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288088 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288088, 1, 16384⟩
    (by decide) selected_cut_19132

theorem selected_cut_19133 : selected 8 ⟨489768, by decide⟩
    (prefixPartial 13 288089) = some ⟨13, 2, 0, 489768, 288089, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_288089_489768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288089 ⟨489768, by decide⟩ :=
  accepted_of_selected 13 288089 ⟨489768, by decide⟩ ⟨13, 2, 0, 489768, 288089, 2081, 16384⟩
    (by decide) selected_cut_19133

theorem selected_cut_19134 : selected 8 ⟨489810, by decide⟩
    (prefixPartial 13 288090) = some ⟨13, 2, 0, 489810, 288090, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_288090_489810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288090 ⟨489810, by decide⟩ :=
  accepted_of_selected 13 288090 ⟨489810, by decide⟩ ⟨13, 2, 0, 489810, 288090, 2377, 16384⟩
    (by decide) selected_cut_19134

theorem selected_cut_19135 : selected 8 ⟨489829, by decide⟩
    (prefixPartial 13 288091) = some ⟨13, 2, 0, 489829, 288091, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_288091_489829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288091 ⟨489829, by decide⟩ :=
  accepted_of_selected 13 288091 ⟨489829, by decide⟩ ⟨13, 2, 0, 489829, 288091, 1317, 16384⟩
    (by decide) selected_cut_19135

theorem unmarked_context_12_72022_489830 : frontier 9 ⟨489830, by decide⟩
    (prefixCache 12 72022) (prefixPartial 12 72022) = false := by
  decide +kernel

theorem node_context_12_72022_489830 : EJMOriginalGlobalDAGData.nodes 9 ⟨489830, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489768, by decide⟩,⟨489810, by decide⟩,⟨489829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72022_489830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72022 ⟨489830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72022
    ⟨489830, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489768, by decide⟩,⟨489810, by decide⟩,⟨489829, by decide⟩]) unmarked_context_12_72022_489830 node_context_12_72022_489830
  intro a
  fin_cases a
  · exact context_13_288088_3444
  · exact context_13_288089_489768
  · exact context_13_288090_489810
  · exact context_13_288091_489829

theorem selected_cut_19136 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288092) = some ⟨13, 1, 0, 3444, 288092, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288092_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288092 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288092 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288092, 1, 16384⟩
    (by decide) selected_cut_19136

theorem selected_cut_19137 : selected 8 ⟨489851, by decide⟩
    (prefixPartial 13 288093) = some ⟨13, 2, 0, 489851, 288093, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_288093_489851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288093 ⟨489851, by decide⟩ :=
  accepted_of_selected 13 288093 ⟨489851, by decide⟩ ⟨13, 2, 0, 489851, 288093, 2013, 16384⟩
    (by decide) selected_cut_19137

theorem selected_cut_19138 : selected 8 ⟨489892, by decide⟩
    (prefixPartial 13 288094) = some ⟨13, 2, 0, 489892, 288094, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_288094_489892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288094 ⟨489892, by decide⟩ :=
  accepted_of_selected 13 288094 ⟨489892, by decide⟩ ⟨13, 2, 0, 489892, 288094, 2537, 16384⟩
    (by decide) selected_cut_19138

theorem selected_cut_19139 : selected 8 ⟨489897, by decide⟩
    (prefixPartial 13 288095) = some ⟨13, 2, 0, 489897, 288095, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_288095_489897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288095 ⟨489897, by decide⟩ :=
  accepted_of_selected 13 288095 ⟨489897, by decide⟩ ⟨13, 2, 0, 489897, 288095, 1049, 16384⟩
    (by decide) selected_cut_19139

theorem unmarked_context_12_72023_489898 : frontier 9 ⟨489898, by decide⟩
    (prefixCache 12 72023) (prefixPartial 12 72023) = false := by
  decide +kernel

theorem node_context_12_72023_489898 : EJMOriginalGlobalDAGData.nodes 9 ⟨489898, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489851, by decide⟩,⟨489892, by decide⟩,⟨489897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72023_489898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72023 ⟨489898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72023
    ⟨489898, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489851, by decide⟩,⟨489892, by decide⟩,⟨489897, by decide⟩]) unmarked_context_12_72023_489898 node_context_12_72023_489898
  intro a
  fin_cases a
  · exact context_13_288092_3444
  · exact context_13_288093_489851
  · exact context_13_288094_489892
  · exact context_13_288095_489897

theorem unmarked_context_11_18005_489899 : frontier 10 ⟨489899, by decide⟩
    (prefixCache 11 18005) (prefixPartial 11 18005) = false := by
  decide +kernel

theorem node_context_11_18005_489899 : EJMOriginalGlobalDAGData.nodes 10 ⟨489899, by decide⟩ =
    .split (coordinate 11) (![⟨489740, by decide⟩,⟨439069, by decide⟩,⟨489830, by decide⟩,⟨489898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18005_489899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18005 ⟨489899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18005
    ⟨489899, by decide⟩ (by decide) (![⟨489740, by decide⟩,⟨439069, by decide⟩,⟨489830, by decide⟩,⟨489898, by decide⟩]) unmarked_context_11_18005_489899 node_context_11_18005_489899
  intro a
  fin_cases a
  · exact context_12_72020_489740
  · exact context_12_72021_439069
  · exact context_12_72022_489830
  · exact context_12_72023_489898

theorem selected_cut_19140 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288096) = some ⟨13, 1, 0, 3444, 288096, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288096_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288096 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288096 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288096, 1, 16384⟩
    (by decide) selected_cut_19140

theorem selected_cut_19141 : selected 8 ⟨489920, by decide⟩
    (prefixPartial 13 288097) = some ⟨13, 2, 0, 489920, 288097, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_288097_489920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288097 ⟨489920, by decide⟩ :=
  accepted_of_selected 13 288097 ⟨489920, by decide⟩ ⟨13, 2, 0, 489920, 288097, 1853, 16384⟩
    (by decide) selected_cut_19141

theorem selected_cut_19142 : selected 8 ⟨489941, by decide⟩
    (prefixPartial 13 288098) = some ⟨13, 2, 0, 489941, 288098, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_288098_489941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288098 ⟨489941, by decide⟩ :=
  accepted_of_selected 13 288098 ⟨489941, by decide⟩ ⟨13, 2, 0, 489941, 288098, 2105, 16384⟩
    (by decide) selected_cut_19142

theorem selected_cut_19143 : selected 8 ⟨489954, by decide⟩
    (prefixPartial 13 288099) = some ⟨13, 2, 0, 489954, 288099, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_288099_489954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288099 ⟨489954, by decide⟩ :=
  accepted_of_selected 13 288099 ⟨489954, by decide⟩ ⟨13, 2, 0, 489954, 288099, 1237, 16384⟩
    (by decide) selected_cut_19143

theorem unmarked_context_12_72024_489955 : frontier 9 ⟨489955, by decide⟩
    (prefixCache 12 72024) (prefixPartial 12 72024) = false := by
  decide +kernel

theorem node_context_12_72024_489955 : EJMOriginalGlobalDAGData.nodes 9 ⟨489955, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489920, by decide⟩,⟨489941, by decide⟩,⟨489954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72024_489955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72024 ⟨489955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72024
    ⟨489955, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489920, by decide⟩,⟨489941, by decide⟩,⟨489954, by decide⟩]) unmarked_context_12_72024_489955 node_context_12_72024_489955
  intro a
  fin_cases a
  · exact context_13_288096_3444
  · exact context_13_288097_489920
  · exact context_13_288098_489941
  · exact context_13_288099_489954

theorem selected_cut_19144 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288100) = some ⟨13, 1, 0, 3444, 288100, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288100_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288100 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288100 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288100, 1, 16384⟩
    (by decide) selected_cut_19144

theorem selected_cut_19145 : selected 8 ⟨489975, by decide⟩
    (prefixPartial 13 288101) = some ⟨13, 2, 0, 489975, 288101, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_288101_489975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288101 ⟨489975, by decide⟩ :=
  accepted_of_selected 13 288101 ⟨489975, by decide⟩ ⟨13, 2, 0, 489975, 288101, 1597, 16384⟩
    (by decide) selected_cut_19145

theorem selected_cut_19146 : selected 8 ⟨489991, by decide⟩
    (prefixPartial 13 288102) = some ⟨13, 2, 0, 489991, 288102, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_288102_489991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288102 ⟨489991, by decide⟩ :=
  accepted_of_selected 13 288102 ⟨489991, by decide⟩ ⟨13, 2, 0, 489991, 288102, 2097, 16384⟩
    (by decide) selected_cut_19146

theorem selected_cut_19147 : selected 8 ⟨489998, by decide⟩
    (prefixPartial 13 288103) = some ⟨13, 2, 0, 489998, 288103, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_288103_489998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288103 ⟨489998, by decide⟩ :=
  accepted_of_selected 13 288103 ⟨489998, by decide⟩ ⟨13, 2, 0, 489998, 288103, 1197, 16384⟩
    (by decide) selected_cut_19147

theorem unmarked_context_12_72025_489999 : frontier 9 ⟨489999, by decide⟩
    (prefixCache 12 72025) (prefixPartial 12 72025) = false := by
  decide +kernel

theorem node_context_12_72025_489999 : EJMOriginalGlobalDAGData.nodes 9 ⟨489999, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨489975, by decide⟩,⟨489991, by decide⟩,⟨489998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72025_489999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72025 ⟨489999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72025
    ⟨489999, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨489975, by decide⟩,⟨489991, by decide⟩,⟨489998, by decide⟩]) unmarked_context_12_72025_489999 node_context_12_72025_489999
  intro a
  fin_cases a
  · exact context_13_288100_3444
  · exact context_13_288101_489975
  · exact context_13_288102_489991
  · exact context_13_288103_489998

theorem selected_cut_19148 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288104) = some ⟨13, 1, 0, 3444, 288104, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288104_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288104 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288104 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288104, 1, 16384⟩
    (by decide) selected_cut_19148

theorem selected_cut_19149 : selected 8 ⟨490029, by decide⟩
    (prefixPartial 13 288105) = some ⟨13, 2, 0, 490029, 288105, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_288105_490029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288105 ⟨490029, by decide⟩ :=
  accepted_of_selected 13 288105 ⟨490029, by decide⟩ ⟨13, 2, 0, 490029, 288105, 2009, 16384⟩
    (by decide) selected_cut_19149

theorem selected_cut_19150 : selected 8 ⟨490061, by decide⟩
    (prefixPartial 13 288106) = some ⟨13, 2, 0, 490061, 288106, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_288106_490061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288106 ⟨490061, by decide⟩ :=
  accepted_of_selected 13 288106 ⟨490061, by decide⟩ ⟨13, 2, 0, 490061, 288106, 2409, 16384⟩
    (by decide) selected_cut_19150

theorem selected_cut_19151 : selected 8 ⟨490074, by decide⟩
    (prefixPartial 13 288107) = some ⟨13, 2, 0, 490074, 288107, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_288107_490074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288107 ⟨490074, by decide⟩ :=
  accepted_of_selected 13 288107 ⟨490074, by decide⟩ ⟨13, 2, 0, 490074, 288107, 1293, 16384⟩
    (by decide) selected_cut_19151

theorem unmarked_context_12_72026_490075 : frontier 9 ⟨490075, by decide⟩
    (prefixCache 12 72026) (prefixPartial 12 72026) = false := by
  decide +kernel

theorem node_context_12_72026_490075 : EJMOriginalGlobalDAGData.nodes 9 ⟨490075, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490029, by decide⟩,⟨490061, by decide⟩,⟨490074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72026_490075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72026 ⟨490075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72026
    ⟨490075, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490029, by decide⟩,⟨490061, by decide⟩,⟨490074, by decide⟩]) unmarked_context_12_72026_490075 node_context_12_72026_490075
  intro a
  fin_cases a
  · exact context_13_288104_3444
  · exact context_13_288105_490029
  · exact context_13_288106_490061
  · exact context_13_288107_490074

theorem selected_cut_19152 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288108) = some ⟨13, 1, 0, 3444, 288108, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288108_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288108 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288108 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288108, 1, 16384⟩
    (by decide) selected_cut_19152

theorem selected_cut_19153 : selected 8 ⟨490095, by decide⟩
    (prefixPartial 13 288109) = some ⟨13, 2, 0, 490095, 288109, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_288109_490095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288109 ⟨490095, by decide⟩ :=
  accepted_of_selected 13 288109 ⟨490095, by decide⟩ ⟨13, 2, 0, 490095, 288109, 1965, 16384⟩
    (by decide) selected_cut_19153

theorem selected_cut_19154 : selected 8 ⟨490126, by decide⟩
    (prefixPartial 13 288110) = some ⟨13, 2, 0, 490126, 288110, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_288110_490126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288110 ⟨490126, by decide⟩ :=
  accepted_of_selected 13 288110 ⟨490126, by decide⟩ ⟨13, 2, 0, 490126, 288110, 2517, 16384⟩
    (by decide) selected_cut_19154

theorem selected_cut_19155 : selected 8 ⟨490139, by decide⟩
    (prefixPartial 13 288111) = some ⟨13, 2, 0, 490139, 288111, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_288111_490139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288111 ⟨490139, by decide⟩ :=
  accepted_of_selected 13 288111 ⟨490139, by decide⟩ ⟨13, 2, 0, 490139, 288111, 1173, 16384⟩
    (by decide) selected_cut_19155

theorem unmarked_context_12_72027_490140 : frontier 9 ⟨490140, by decide⟩
    (prefixCache 12 72027) (prefixPartial 12 72027) = false := by
  decide +kernel

theorem node_context_12_72027_490140 : EJMOriginalGlobalDAGData.nodes 9 ⟨490140, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490095, by decide⟩,⟨490126, by decide⟩,⟨490139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72027_490140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72027 ⟨490140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72027
    ⟨490140, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490095, by decide⟩,⟨490126, by decide⟩,⟨490139, by decide⟩]) unmarked_context_12_72027_490140 node_context_12_72027_490140
  intro a
  fin_cases a
  · exact context_13_288108_3444
  · exact context_13_288109_490095
  · exact context_13_288110_490126
  · exact context_13_288111_490139

theorem unmarked_context_11_18006_490141 : frontier 10 ⟨490141, by decide⟩
    (prefixCache 11 18006) (prefixPartial 11 18006) = false := by
  decide +kernel

theorem node_context_11_18006_490141 : EJMOriginalGlobalDAGData.nodes 10 ⟨490141, by decide⟩ =
    .split (coordinate 11) (![⟨489955, by decide⟩,⟨489999, by decide⟩,⟨490075, by decide⟩,⟨490140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18006_490141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18006 ⟨490141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18006
    ⟨490141, by decide⟩ (by decide) (![⟨489955, by decide⟩,⟨489999, by decide⟩,⟨490075, by decide⟩,⟨490140, by decide⟩]) unmarked_context_11_18006_490141 node_context_11_18006_490141
  intro a
  fin_cases a
  · exact context_12_72024_489955
  · exact context_12_72025_489999
  · exact context_12_72026_490075
  · exact context_12_72027_490140

theorem selected_cut_19156 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288112) = some ⟨13, 1, 0, 3444, 288112, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288112_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288112 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288112 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288112, 1, 16384⟩
    (by decide) selected_cut_19156

theorem selected_cut_19157 : selected 8 ⟨490167, by decide⟩
    (prefixPartial 13 288113) = some ⟨13, 2, 0, 490167, 288113, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_288113_490167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288113 ⟨490167, by decide⟩ :=
  accepted_of_selected 13 288113 ⟨490167, by decide⟩ ⟨13, 2, 0, 490167, 288113, 1765, 16384⟩
    (by decide) selected_cut_19157

theorem selected_cut_19158 : selected 8 ⟨490198, by decide⟩
    (prefixPartial 13 288114) = some ⟨13, 2, 0, 490198, 288114, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_288114_490198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288114 ⟨490198, by decide⟩ :=
  accepted_of_selected 13 288114 ⟨490198, by decide⟩ ⟨13, 2, 0, 490198, 288114, 2361, 16384⟩
    (by decide) selected_cut_19158

theorem selected_cut_19159 : selected 8 ⟨490217, by decide⟩
    (prefixPartial 13 288115) = some ⟨13, 2, 0, 490217, 288115, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_288115_490217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288115 ⟨490217, by decide⟩ :=
  accepted_of_selected 13 288115 ⟨490217, by decide⟩ ⟨13, 2, 0, 490217, 288115, 1325, 16384⟩
    (by decide) selected_cut_19159

theorem unmarked_context_12_72028_490218 : frontier 9 ⟨490218, by decide⟩
    (prefixCache 12 72028) (prefixPartial 12 72028) = false := by
  decide +kernel

theorem node_context_12_72028_490218 : EJMOriginalGlobalDAGData.nodes 9 ⟨490218, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490167, by decide⟩,⟨490198, by decide⟩,⟨490217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72028_490218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72028 ⟨490218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72028
    ⟨490218, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490167, by decide⟩,⟨490198, by decide⟩,⟨490217, by decide⟩]) unmarked_context_12_72028_490218 node_context_12_72028_490218
  intro a
  fin_cases a
  · exact context_13_288112_3444
  · exact context_13_288113_490167
  · exact context_13_288114_490198
  · exact context_13_288115_490217

theorem selected_cut_19160 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288116) = some ⟨13, 1, 0, 3444, 288116, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288116_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288116 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288116 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288116, 1, 16384⟩
    (by decide) selected_cut_19160

theorem selected_cut_19161 : selected 8 ⟨490232, by decide⟩
    (prefixPartial 13 288117) = some ⟨13, 2, 0, 490232, 288117, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_288117_490232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288117 ⟨490232, by decide⟩ :=
  accepted_of_selected 13 288117 ⟨490232, by decide⟩ ⟨13, 2, 0, 490232, 288117, 1477, 16384⟩
    (by decide) selected_cut_19161

theorem selected_cut_19162 : selected 8 ⟨490255, by decide⟩
    (prefixPartial 13 288118) = some ⟨13, 2, 0, 490255, 288118, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_288118_490255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288118 ⟨490255, by decide⟩ :=
  accepted_of_selected 13 288118 ⟨490255, by decide⟩ ⟨13, 2, 0, 490255, 288118, 2213, 16384⟩
    (by decide) selected_cut_19162

theorem selected_cut_19163 : selected 8 ⟨490268, by decide⟩
    (prefixPartial 13 288119) = some ⟨13, 2, 0, 490268, 288119, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_288119_490268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288119 ⟨490268, by decide⟩ :=
  accepted_of_selected 13 288119 ⟨490268, by decide⟩ ⟨13, 2, 0, 490268, 288119, 1273, 16384⟩
    (by decide) selected_cut_19163

theorem unmarked_context_12_72029_490269 : frontier 9 ⟨490269, by decide⟩
    (prefixCache 12 72029) (prefixPartial 12 72029) = false := by
  decide +kernel

theorem node_context_12_72029_490269 : EJMOriginalGlobalDAGData.nodes 9 ⟨490269, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490232, by decide⟩,⟨490255, by decide⟩,⟨490268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72029_490269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72029 ⟨490269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72029
    ⟨490269, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490232, by decide⟩,⟨490255, by decide⟩,⟨490268, by decide⟩]) unmarked_context_12_72029_490269 node_context_12_72029_490269
  intro a
  fin_cases a
  · exact context_13_288116_3444
  · exact context_13_288117_490232
  · exact context_13_288118_490255
  · exact context_13_288119_490268

theorem selected_cut_19164 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288120) = some ⟨13, 1, 0, 3444, 288120, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288120_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288120 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288120 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288120, 1, 16384⟩
    (by decide) selected_cut_19164

theorem selected_cut_19165 : selected 8 ⟨490297, by decide⟩
    (prefixPartial 13 288121) = some ⟨13, 2, 0, 490297, 288121, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_288121_490297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288121 ⟨490297, by decide⟩ :=
  accepted_of_selected 13 288121 ⟨490297, by decide⟩ ⟨13, 2, 0, 490297, 288121, 1941, 16384⟩
    (by decide) selected_cut_19165

theorem selected_cut_19166 : selected 8 ⟨490341, by decide⟩
    (prefixPartial 13 288122) = some ⟨13, 2, 0, 490341, 288122, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_288122_490341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288122 ⟨490341, by decide⟩ :=
  accepted_of_selected 13 288122 ⟨490341, by decide⟩ ⟨13, 2, 0, 490341, 288122, 2749, 16384⟩
    (by decide) selected_cut_19166

theorem selected_cut_19167 : selected 8 ⟨490367, by decide⟩
    (prefixPartial 13 288123) = some ⟨13, 2, 0, 490367, 288123, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_288123_490367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288123 ⟨490367, by decide⟩ :=
  accepted_of_selected 13 288123 ⟨490367, by decide⟩ ⟨13, 2, 0, 490367, 288123, 1389, 16384⟩
    (by decide) selected_cut_19167

theorem unmarked_context_12_72030_490368 : frontier 9 ⟨490368, by decide⟩
    (prefixCache 12 72030) (prefixPartial 12 72030) = false := by
  decide +kernel

theorem node_context_12_72030_490368 : EJMOriginalGlobalDAGData.nodes 9 ⟨490368, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490297, by decide⟩,⟨490341, by decide⟩,⟨490367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72030_490368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72030 ⟨490368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72030
    ⟨490368, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490297, by decide⟩,⟨490341, by decide⟩,⟨490367, by decide⟩]) unmarked_context_12_72030_490368 node_context_12_72030_490368
  intro a
  fin_cases a
  · exact context_13_288120_3444
  · exact context_13_288121_490297
  · exact context_13_288122_490341
  · exact context_13_288123_490367

theorem selected_cut_19168 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288124) = some ⟨13, 1, 0, 3444, 288124, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288124_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288124 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288124 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288124, 1, 16384⟩
    (by decide) selected_cut_19168

theorem selected_cut_19169 : selected 8 ⟨490386, by decide⟩
    (prefixPartial 13 288125) = some ⟨13, 2, 0, 490386, 288125, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_288125_490386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288125 ⟨490386, by decide⟩ :=
  accepted_of_selected 13 288125 ⟨490386, by decide⟩ ⟨13, 2, 0, 490386, 288125, 1677, 16384⟩
    (by decide) selected_cut_19169

theorem selected_cut_19170 : selected 8 ⟨490414, by decide⟩
    (prefixPartial 13 288126) = some ⟨13, 2, 0, 490414, 288126, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_288126_490414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288126 ⟨490414, by decide⟩ :=
  accepted_of_selected 13 288126 ⟨490414, by decide⟩ ⟨13, 2, 0, 490414, 288126, 2785, 16384⟩
    (by decide) selected_cut_19170

theorem selected_cut_19171 : selected 8 ⟨490426, by decide⟩
    (prefixPartial 13 288127) = some ⟨13, 2, 0, 490426, 288127, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_288127_490426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288127 ⟨490426, by decide⟩ :=
  accepted_of_selected 13 288127 ⟨490426, by decide⟩ ⟨13, 2, 0, 490426, 288127, 1261, 16384⟩
    (by decide) selected_cut_19171

theorem unmarked_context_12_72031_490427 : frontier 9 ⟨490427, by decide⟩
    (prefixCache 12 72031) (prefixPartial 12 72031) = false := by
  decide +kernel

theorem node_context_12_72031_490427 : EJMOriginalGlobalDAGData.nodes 9 ⟨490427, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490386, by decide⟩,⟨490414, by decide⟩,⟨490426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72031_490427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72031 ⟨490427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72031
    ⟨490427, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490386, by decide⟩,⟨490414, by decide⟩,⟨490426, by decide⟩]) unmarked_context_12_72031_490427 node_context_12_72031_490427
  intro a
  fin_cases a
  · exact context_13_288124_3444
  · exact context_13_288125_490386
  · exact context_13_288126_490414
  · exact context_13_288127_490426

theorem unmarked_context_11_18007_490428 : frontier 10 ⟨490428, by decide⟩
    (prefixCache 11 18007) (prefixPartial 11 18007) = false := by
  decide +kernel

theorem node_context_11_18007_490428 : EJMOriginalGlobalDAGData.nodes 10 ⟨490428, by decide⟩ =
    .split (coordinate 11) (![⟨490218, by decide⟩,⟨490269, by decide⟩,⟨490368, by decide⟩,⟨490427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18007_490428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18007 ⟨490428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18007
    ⟨490428, by decide⟩ (by decide) (![⟨490218, by decide⟩,⟨490269, by decide⟩,⟨490368, by decide⟩,⟨490427, by decide⟩]) unmarked_context_11_18007_490428 node_context_11_18007_490428
  intro a
  fin_cases a
  · exact context_12_72028_490218
  · exact context_12_72029_490269
  · exact context_12_72030_490368
  · exact context_12_72031_490427

theorem unmarked_context_10_4501_490429 : frontier 11 ⟨490429, by decide⟩
    (prefixCache 10 4501) (prefixPartial 10 4501) = false := by
  decide +kernel

theorem node_context_10_4501_490429 : EJMOriginalGlobalDAGData.nodes 11 ⟨490429, by decide⟩ =
    .split (coordinate 10) (![⟨489696, by decide⟩,⟨489899, by decide⟩,⟨490141, by decide⟩,⟨490428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4501_490429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4501 ⟨490429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4501
    ⟨490429, by decide⟩ (by decide) (![⟨489696, by decide⟩,⟨489899, by decide⟩,⟨490141, by decide⟩,⟨490428, by decide⟩]) unmarked_context_10_4501_490429 node_context_10_4501_490429
  intro a
  fin_cases a
  · exact context_11_18004_489696
  · exact context_11_18005_489899
  · exact context_11_18006_490141
  · exact context_11_18007_490428

theorem selected_cut_19172 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288128) = some ⟨13, 1, 0, 3444, 288128, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288128_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288128 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288128 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288128, 1, 16384⟩
    (by decide) selected_cut_19172

theorem selected_cut_19173 : selected 8 ⟨490450, by decide⟩
    (prefixPartial 13 288129) = some ⟨13, 2, 0, 490450, 288129, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_288129_490450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288129 ⟨490450, by decide⟩ :=
  accepted_of_selected 13 288129 ⟨490450, by decide⟩ ⟨13, 2, 0, 490450, 288129, 1421, 16384⟩
    (by decide) selected_cut_19173

theorem selected_cut_19174 : selected 8 ⟨490475, by decide⟩
    (prefixPartial 13 288130) = some ⟨13, 2, 0, 490475, 288130, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_288130_490475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288130 ⟨490475, by decide⟩ :=
  accepted_of_selected 13 288130 ⟨490475, by decide⟩ ⟨13, 2, 0, 490475, 288130, 1785, 16384⟩
    (by decide) selected_cut_19174

theorem selected_cut_19175 : selected 8 ⟨490486, by decide⟩
    (prefixPartial 13 288131) = some ⟨13, 2, 0, 490486, 288131, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_288131_490486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288131 ⟨490486, by decide⟩ :=
  accepted_of_selected 13 288131 ⟨490486, by decide⟩ ⟨13, 2, 0, 490486, 288131, 1145, 16384⟩
    (by decide) selected_cut_19175

theorem unmarked_context_12_72032_490487 : frontier 9 ⟨490487, by decide⟩
    (prefixCache 12 72032) (prefixPartial 12 72032) = false := by
  decide +kernel

theorem node_context_12_72032_490487 : EJMOriginalGlobalDAGData.nodes 9 ⟨490487, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490450, by decide⟩,⟨490475, by decide⟩,⟨490486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72032_490487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72032 ⟨490487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72032
    ⟨490487, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490450, by decide⟩,⟨490475, by decide⟩,⟨490486, by decide⟩]) unmarked_context_12_72032_490487 node_context_12_72032_490487
  intro a
  fin_cases a
  · exact context_13_288128_3444
  · exact context_13_288129_490450
  · exact context_13_288130_490475
  · exact context_13_288131_490486

theorem selected_cut_19176 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288132) = some ⟨13, 1, 0, 3444, 288132, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288132_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288132 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288132 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288132, 1, 16384⟩
    (by decide) selected_cut_19176

theorem selected_cut_19177 : selected 8 ⟨490505, by decide⟩
    (prefixPartial 13 288133) = some ⟨13, 2, 0, 490505, 288133, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_288133_490505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288133 ⟨490505, by decide⟩ :=
  accepted_of_selected 13 288133 ⟨490505, by decide⟩ ⟨13, 2, 0, 490505, 288133, 1365, 16384⟩
    (by decide) selected_cut_19177

theorem selected_cut_19178 : selected 8 ⟨490524, by decide⟩
    (prefixPartial 13 288134) = some ⟨13, 2, 0, 490524, 288134, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_288134_490524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288134 ⟨490524, by decide⟩ :=
  accepted_of_selected 13 288134 ⟨490524, by decide⟩ ⟨13, 2, 0, 490524, 288134, 1957, 16384⟩
    (by decide) selected_cut_19178

theorem selected_cut_19179 : selected 8 ⟨490536, by decide⟩
    (prefixPartial 13 288135) = some ⟨13, 2, 0, 490536, 288135, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_288135_490536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288135 ⟨490536, by decide⟩ :=
  accepted_of_selected 13 288135 ⟨490536, by decide⟩ ⟨13, 2, 0, 490536, 288135, 1261, 16384⟩
    (by decide) selected_cut_19179

theorem unmarked_context_12_72033_490537 : frontier 9 ⟨490537, by decide⟩
    (prefixCache 12 72033) (prefixPartial 12 72033) = false := by
  decide +kernel

theorem node_context_12_72033_490537 : EJMOriginalGlobalDAGData.nodes 9 ⟨490537, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490505, by decide⟩,⟨490524, by decide⟩,⟨490536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72033_490537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72033 ⟨490537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72033
    ⟨490537, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490505, by decide⟩,⟨490524, by decide⟩,⟨490536, by decide⟩]) unmarked_context_12_72033_490537 node_context_12_72033_490537
  intro a
  fin_cases a
  · exact context_13_288132_3444
  · exact context_13_288133_490505
  · exact context_13_288134_490524
  · exact context_13_288135_490536

theorem selected_cut_19180 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288136) = some ⟨13, 1, 0, 3444, 288136, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288136_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288136 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288136 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288136, 1, 16384⟩
    (by decide) selected_cut_19180

theorem selected_cut_19181 : selected 8 ⟨490570, by decide⟩
    (prefixPartial 13 288137) = some ⟨13, 2, 0, 490570, 288137, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_288137_490570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288137 ⟨490570, by decide⟩ :=
  accepted_of_selected 13 288137 ⟨490570, by decide⟩ ⟨13, 2, 0, 490570, 288137, 1817, 16384⟩
    (by decide) selected_cut_19181

theorem selected_cut_19182 : selected 8 ⟨490605, by decide⟩
    (prefixPartial 13 288138) = some ⟨13, 2, 0, 490605, 288138, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_288138_490605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288138 ⟨490605, by decide⟩ :=
  accepted_of_selected 13 288138 ⟨490605, by decide⟩ ⟨13, 2, 0, 490605, 288138, 2365, 16384⟩
    (by decide) selected_cut_19182

theorem selected_cut_19183 : selected 8 ⟨490620, by decide⟩
    (prefixPartial 13 288139) = some ⟨13, 2, 0, 490620, 288139, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_288139_490620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288139 ⟨490620, by decide⟩ :=
  accepted_of_selected 13 288139 ⟨490620, by decide⟩ ⟨13, 2, 0, 490620, 288139, 1377, 16384⟩
    (by decide) selected_cut_19183

theorem unmarked_context_12_72034_490621 : frontier 9 ⟨490621, by decide⟩
    (prefixCache 12 72034) (prefixPartial 12 72034) = false := by
  decide +kernel

theorem node_context_12_72034_490621 : EJMOriginalGlobalDAGData.nodes 9 ⟨490621, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490570, by decide⟩,⟨490605, by decide⟩,⟨490620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72034_490621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72034 ⟨490621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72034
    ⟨490621, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490570, by decide⟩,⟨490605, by decide⟩,⟨490620, by decide⟩]) unmarked_context_12_72034_490621 node_context_12_72034_490621
  intro a
  fin_cases a
  · exact context_13_288136_3444
  · exact context_13_288137_490570
  · exact context_13_288138_490605
  · exact context_13_288139_490620

theorem selected_cut_19184 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288140) = some ⟨13, 1, 0, 3444, 288140, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288140_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288140 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288140 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288140, 1, 16384⟩
    (by decide) selected_cut_19184

theorem selected_cut_19185 : selected 8 ⟨490648, by decide⟩
    (prefixPartial 13 288141) = some ⟨13, 2, 0, 490648, 288141, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_288141_490648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288141 ⟨490648, by decide⟩ :=
  accepted_of_selected 13 288141 ⟨490648, by decide⟩ ⟨13, 2, 0, 490648, 288141, 1685, 16384⟩
    (by decide) selected_cut_19185

theorem selected_cut_19186 : selected 8 ⟨490681, by decide⟩
    (prefixPartial 13 288142) = some ⟨13, 2, 0, 490681, 288142, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_288142_490681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288142 ⟨490681, by decide⟩ :=
  accepted_of_selected 13 288142 ⟨490681, by decide⟩ ⟨13, 2, 0, 490681, 288142, 2553, 16384⟩
    (by decide) selected_cut_19186

theorem selected_cut_19187 : selected 8 ⟨490689, by decide⟩
    (prefixPartial 13 288143) = some ⟨13, 2, 0, 490689, 288143, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_288143_490689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288143 ⟨490689, by decide⟩ :=
  accepted_of_selected 13 288143 ⟨490689, by decide⟩ ⟨13, 2, 0, 490689, 288143, 1209, 16384⟩
    (by decide) selected_cut_19187

theorem unmarked_context_12_72035_490690 : frontier 9 ⟨490690, by decide⟩
    (prefixCache 12 72035) (prefixPartial 12 72035) = false := by
  decide +kernel

theorem node_context_12_72035_490690 : EJMOriginalGlobalDAGData.nodes 9 ⟨490690, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490648, by decide⟩,⟨490681, by decide⟩,⟨490689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72035_490690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72035 ⟨490690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72035
    ⟨490690, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490648, by decide⟩,⟨490681, by decide⟩,⟨490689, by decide⟩]) unmarked_context_12_72035_490690 node_context_12_72035_490690
  intro a
  fin_cases a
  · exact context_13_288140_3444
  · exact context_13_288141_490648
  · exact context_13_288142_490681
  · exact context_13_288143_490689

theorem unmarked_context_11_18008_490691 : frontier 10 ⟨490691, by decide⟩
    (prefixCache 11 18008) (prefixPartial 11 18008) = false := by
  decide +kernel

theorem node_context_11_18008_490691 : EJMOriginalGlobalDAGData.nodes 10 ⟨490691, by decide⟩ =
    .split (coordinate 11) (![⟨490487, by decide⟩,⟨490537, by decide⟩,⟨490621, by decide⟩,⟨490690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18008_490691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18008 ⟨490691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18008
    ⟨490691, by decide⟩ (by decide) (![⟨490487, by decide⟩,⟨490537, by decide⟩,⟨490621, by decide⟩,⟨490690, by decide⟩]) unmarked_context_11_18008_490691 node_context_11_18008_490691
  intro a
  fin_cases a
  · exact context_12_72032_490487
  · exact context_12_72033_490537
  · exact context_12_72034_490621
  · exact context_12_72035_490690

theorem selected_cut_19188 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288144) = some ⟨13, 1, 0, 3444, 288144, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288144_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288144 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288144 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288144, 1, 16384⟩
    (by decide) selected_cut_19188

theorem selected_cut_19189 : selected 8 ⟨490706, by decide⟩
    (prefixPartial 13 288145) = some ⟨13, 2, 0, 490706, 288145, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_288145_490706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288145 ⟨490706, by decide⟩ :=
  accepted_of_selected 13 288145 ⟨490706, by decide⟩ ⟨13, 2, 0, 490706, 288145, 1173, 16384⟩
    (by decide) selected_cut_19189

theorem selected_cut_19190 : selected 8 ⟨490730, by decide⟩
    (prefixPartial 13 288146) = some ⟨13, 2, 0, 490730, 288146, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_288146_490730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288146 ⟨490730, by decide⟩ :=
  accepted_of_selected 13 288146 ⟨490730, by decide⟩ ⟨13, 2, 0, 490730, 288146, 1845, 16384⟩
    (by decide) selected_cut_19190

theorem selected_cut_19191 : selected 8 ⟨490746, by decide⟩
    (prefixPartial 13 288147) = some ⟨13, 2, 0, 490746, 288147, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_288147_490746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288147 ⟨490746, by decide⟩ :=
  accepted_of_selected 13 288147 ⟨490746, by decide⟩ ⟨13, 2, 0, 490746, 288147, 1289, 16384⟩
    (by decide) selected_cut_19191

theorem unmarked_context_12_72036_490747 : frontier 9 ⟨490747, by decide⟩
    (prefixCache 12 72036) (prefixPartial 12 72036) = false := by
  decide +kernel

theorem node_context_12_72036_490747 : EJMOriginalGlobalDAGData.nodes 9 ⟨490747, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490706, by decide⟩,⟨490730, by decide⟩,⟨490746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72036_490747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72036 ⟨490747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72036
    ⟨490747, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490706, by decide⟩,⟨490730, by decide⟩,⟨490746, by decide⟩]) unmarked_context_12_72036_490747 node_context_12_72036_490747
  intro a
  fin_cases a
  · exact context_13_288144_3444
  · exact context_13_288145_490706
  · exact context_13_288146_490730
  · exact context_13_288147_490746

theorem selected_cut_19192 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 72037) = some ⟨12, 1, 0, 441672, 72037, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72037_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72037 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 72037 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 72037, 1, 65536⟩
    (by decide) selected_cut_19192

theorem selected_cut_19193 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288152) = some ⟨13, 1, 0, 3444, 288152, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288152_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288152 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288152 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288152, 1, 16384⟩
    (by decide) selected_cut_19193

theorem selected_cut_19194 : selected 8 ⟨490771, by decide⟩
    (prefixPartial 13 288153) = some ⟨13, 2, 0, 490771, 288153, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_288153_490771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288153 ⟨490771, by decide⟩ :=
  accepted_of_selected 13 288153 ⟨490771, by decide⟩ ⟨13, 2, 0, 490771, 288153, 1421, 16384⟩
    (by decide) selected_cut_19194

theorem selected_cut_19195 : selected 8 ⟨490801, by decide⟩
    (prefixPartial 13 288154) = some ⟨13, 2, 0, 490801, 288154, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_288154_490801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288154 ⟨490801, by decide⟩ :=
  accepted_of_selected 13 288154 ⟨490801, by decide⟩ ⟨13, 2, 0, 490801, 288154, 2073, 16384⟩
    (by decide) selected_cut_19195

theorem selected_cut_19196 : selected 8 ⟨490822, by decide⟩
    (prefixPartial 13 288155) = some ⟨13, 2, 0, 490822, 288155, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_288155_490822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288155 ⟨490822, by decide⟩ :=
  accepted_of_selected 13 288155 ⟨490822, by decide⟩ ⟨13, 2, 0, 490822, 288155, 1425, 16384⟩
    (by decide) selected_cut_19196

theorem unmarked_context_12_72038_490823 : frontier 9 ⟨490823, by decide⟩
    (prefixCache 12 72038) (prefixPartial 12 72038) = false := by
  decide +kernel

theorem node_context_12_72038_490823 : EJMOriginalGlobalDAGData.nodes 9 ⟨490823, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490771, by decide⟩,⟨490801, by decide⟩,⟨490822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72038_490823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72038 ⟨490823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72038
    ⟨490823, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490771, by decide⟩,⟨490801, by decide⟩,⟨490822, by decide⟩]) unmarked_context_12_72038_490823 node_context_12_72038_490823
  intro a
  fin_cases a
  · exact context_13_288152_3444
  · exact context_13_288153_490771
  · exact context_13_288154_490801
  · exact context_13_288155_490822

theorem selected_cut_19197 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288156) = some ⟨13, 1, 0, 3444, 288156, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288156_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288156 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288156 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288156, 1, 16384⟩
    (by decide) selected_cut_19197

theorem selected_cut_19198 : selected 8 ⟨490838, by decide⟩
    (prefixPartial 13 288157) = some ⟨13, 2, 0, 490838, 288157, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_288157_490838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288157 ⟨490838, by decide⟩ :=
  accepted_of_selected 13 288157 ⟨490838, by decide⟩ ⟨13, 2, 0, 490838, 288157, 1301, 16384⟩
    (by decide) selected_cut_19198

theorem selected_cut_19199 : selected 8 ⟨490875, by decide⟩
    (prefixPartial 13 288158) = some ⟨13, 2, 0, 490875, 288158, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_288158_490875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288158 ⟨490875, by decide⟩ :=
  accepted_of_selected 13 288158 ⟨490875, by decide⟩ ⟨13, 2, 0, 490875, 288158, 2389, 16384⟩
    (by decide) selected_cut_19199

theorem selected_cut_19200 : selected 8 ⟨490886, by decide⟩
    (prefixPartial 13 288159) = some ⟨13, 2, 0, 490886, 288159, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_288159_490886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288159 ⟨490886, by decide⟩ :=
  accepted_of_selected 13 288159 ⟨490886, by decide⟩ ⟨13, 2, 0, 490886, 288159, 1225, 16384⟩
    (by decide) selected_cut_19200

theorem unmarked_context_12_72039_490887 : frontier 9 ⟨490887, by decide⟩
    (prefixCache 12 72039) (prefixPartial 12 72039) = false := by
  decide +kernel

theorem node_context_12_72039_490887 : EJMOriginalGlobalDAGData.nodes 9 ⟨490887, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨490838, by decide⟩,⟨490875, by decide⟩,⟨490886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72039_490887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72039 ⟨490887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72039
    ⟨490887, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨490838, by decide⟩,⟨490875, by decide⟩,⟨490886, by decide⟩]) unmarked_context_12_72039_490887 node_context_12_72039_490887
  intro a
  fin_cases a
  · exact context_13_288156_3444
  · exact context_13_288157_490838
  · exact context_13_288158_490875
  · exact context_13_288159_490886

theorem unmarked_context_11_18009_490888 : frontier 10 ⟨490888, by decide⟩
    (prefixCache 11 18009) (prefixPartial 11 18009) = false := by
  decide +kernel

theorem node_context_11_18009_490888 : EJMOriginalGlobalDAGData.nodes 10 ⟨490888, by decide⟩ =
    .split (coordinate 11) (![⟨490747, by decide⟩,⟨441672, by decide⟩,⟨490823, by decide⟩,⟨490887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18009_490888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18009 ⟨490888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18009
    ⟨490888, by decide⟩ (by decide) (![⟨490747, by decide⟩,⟨441672, by decide⟩,⟨490823, by decide⟩,⟨490887, by decide⟩]) unmarked_context_11_18009_490888 node_context_11_18009_490888
  intro a
  fin_cases a
  · exact context_12_72036_490747
  · exact context_12_72037_441672
  · exact context_12_72038_490823
  · exact context_12_72039_490887

theorem selected_cut_19201 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 288160) = some ⟨13, 1, 0, 3444, 288160, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288160_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288160 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 288160 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 288160, 1, 16384⟩
    (by decide) selected_cut_19201

theorem selected_cut_19202 : selected 8 ⟨490920, by decide⟩
    (prefixPartial 13 288161) = some ⟨13, 2, 0, 490920, 288161, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_288161_490920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288161 ⟨490920, by decide⟩ :=
  accepted_of_selected 13 288161 ⟨490920, by decide⟩ ⟨13, 2, 0, 490920, 288161, 1753, 16384⟩
    (by decide) selected_cut_19202

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
