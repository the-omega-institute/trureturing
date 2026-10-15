/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover008
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_00866 : selected 8 ⟨35106, by decide⟩
    (prefixPartial 13 16427) = some ⟨13, 2, 0, 35106, 16427, 901, 16384⟩ := by
  decide +kernel

theorem context_13_16427_35106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16427 ⟨35106, by decide⟩ :=
  accepted_of_selected 13 16427 ⟨35106, by decide⟩ ⟨13, 2, 0, 35106, 16427, 901, 16384⟩
    (by decide) selected_cut_00866

theorem unmarked_context_12_4106_35107 : frontier 9 ⟨35107, by decide⟩
    (prefixCache 12 4106) (prefixPartial 12 4106) = false := by
  decide +kernel

theorem node_context_12_4106_35107 : EJMOriginalGlobalDAGData.nodes 9 ⟨35107, by decide⟩ =
    .split (coordinate 12) (![⟨35019, by decide⟩,⟨35064, by decide⟩,⟨35093, by decide⟩,⟨35106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4106_35107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4106 ⟨35107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4106
    ⟨35107, by decide⟩ (by decide) (![⟨35019, by decide⟩,⟨35064, by decide⟩,⟨35093, by decide⟩,⟨35106, by decide⟩]) unmarked_context_12_4106_35107 node_context_12_4106_35107
  intro a
  fin_cases a
  · exact context_13_16424_35019
  · exact context_13_16425_35064
  · exact context_13_16426_35093
  · exact context_13_16427_35106

theorem selected_cut_00867 : selected 8 ⟨35132, by decide⟩
    (prefixPartial 13 16428) = some ⟨13, 2, 0, 35132, 16428, 945, 16384⟩ := by
  decide +kernel

theorem context_13_16428_35132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16428 ⟨35132, by decide⟩ :=
  accepted_of_selected 13 16428 ⟨35132, by decide⟩ ⟨13, 2, 0, 35132, 16428, 945, 16384⟩
    (by decide) selected_cut_00867

theorem selected_cut_00868 : selected 8 ⟨35171, by decide⟩
    (prefixPartial 13 16429) = some ⟨13, 2, 0, 35171, 16429, 2929, 16384⟩ := by
  decide +kernel

theorem context_13_16429_35171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16429 ⟨35171, by decide⟩ :=
  accepted_of_selected 13 16429 ⟨35171, by decide⟩ ⟨13, 2, 0, 35171, 16429, 2929, 16384⟩
    (by decide) selected_cut_00868

theorem selected_cut_00869 : selected 8 ⟨35203, by decide⟩
    (prefixPartial 13 16430) = some ⟨13, 2, 0, 35203, 16430, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_16430_35203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16430 ⟨35203, by decide⟩ :=
  accepted_of_selected 13 16430 ⟨35203, by decide⟩ ⟨13, 2, 0, 35203, 16430, 1909, 16384⟩
    (by decide) selected_cut_00869

theorem selected_cut_00870 : selected 8 ⟨35216, by decide⟩
    (prefixPartial 13 16431) = some ⟨13, 2, 0, 35216, 16431, 969, 16384⟩ := by
  decide +kernel

theorem context_13_16431_35216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16431 ⟨35216, by decide⟩ :=
  accepted_of_selected 13 16431 ⟨35216, by decide⟩ ⟨13, 2, 0, 35216, 16431, 969, 16384⟩
    (by decide) selected_cut_00870

theorem unmarked_context_12_4107_35217 : frontier 9 ⟨35217, by decide⟩
    (prefixCache 12 4107) (prefixPartial 12 4107) = false := by
  decide +kernel

theorem node_context_12_4107_35217 : EJMOriginalGlobalDAGData.nodes 9 ⟨35217, by decide⟩ =
    .split (coordinate 12) (![⟨35132, by decide⟩,⟨35171, by decide⟩,⟨35203, by decide⟩,⟨35216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4107_35217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4107 ⟨35217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4107
    ⟨35217, by decide⟩ (by decide) (![⟨35132, by decide⟩,⟨35171, by decide⟩,⟨35203, by decide⟩,⟨35216, by decide⟩]) unmarked_context_12_4107_35217 node_context_12_4107_35217
  intro a
  fin_cases a
  · exact context_13_16428_35132
  · exact context_13_16429_35171
  · exact context_13_16430_35203
  · exact context_13_16431_35216

theorem unmarked_context_11_1026_35218 : frontier 10 ⟨35218, by decide⟩
    (prefixCache 11 1026) (prefixPartial 11 1026) = false := by
  decide +kernel

theorem node_context_11_1026_35218 : EJMOriginalGlobalDAGData.nodes 10 ⟨35218, by decide⟩ =
    .split (coordinate 11) (![⟨34858, by decide⟩,⟨34986, by decide⟩,⟨35107, by decide⟩,⟨35217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1026_35218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1026 ⟨35218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1026
    ⟨35218, by decide⟩ (by decide) (![⟨34858, by decide⟩,⟨34986, by decide⟩,⟨35107, by decide⟩,⟨35217, by decide⟩]) unmarked_context_11_1026_35218 node_context_11_1026_35218
  intro a
  fin_cases a
  · exact context_12_4104_34858
  · exact context_12_4105_34986
  · exact context_12_4106_35107
  · exact context_12_4107_35217

theorem selected_cut_00871 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1027) = some ⟨11, 1, 0, 1736, 1027, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1027_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1027 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1027 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1027, 1, 262144⟩
    (by decide) selected_cut_00871

theorem unmarked_context_10_256_35219 : frontier 11 ⟨35219, by decide⟩
    (prefixCache 10 256) (prefixPartial 10 256) = false := by
  decide +kernel

theorem node_context_10_256_35219 : EJMOriginalGlobalDAGData.nodes 11 ⟨35219, by decide⟩ =
    .split (coordinate 10) (![⟨34338, by decide⟩,⟨34716, by decide⟩,⟨35218, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_256_35219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 256 ⟨35219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 256
    ⟨35219, by decide⟩ (by decide) (![⟨34338, by decide⟩,⟨34716, by decide⟩,⟨35218, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_256_35219 node_context_10_256_35219
  intro a
  fin_cases a
  · exact context_11_1024_34338
  · exact context_11_1025_34716
  · exact context_11_1026_35218
  · exact context_11_1027_1736

theorem selected_cut_00872 : selected 10 ⟨35335, by decide⟩
    (prefixPartial 11 1028) = some ⟨11, 2, 0, 35335, 1028, 3789, 262144⟩ := by
  decide +kernel

theorem context_11_1028_35335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1028 ⟨35335, by decide⟩ :=
  accepted_of_selected 11 1028 ⟨35335, by decide⟩ ⟨11, 2, 0, 35335, 1028, 3789, 262144⟩
    (by decide) selected_cut_00872

theorem selected_cut_00873 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4116) = some ⟨12, 1, 0, 1738, 4116, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4116_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4116 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4116 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4116, 1, 65536⟩
    (by decide) selected_cut_00873

theorem selected_cut_00874 : selected 9 ⟨35400, by decide⟩
    (prefixPartial 12 4117) = some ⟨12, 2, 0, 35400, 4117, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_4117_35400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4117 ⟨35400, by decide⟩ :=
  accepted_of_selected 12 4117 ⟨35400, by decide⟩ ⟨12, 2, 0, 35400, 4117, 1713, 65536⟩
    (by decide) selected_cut_00874

theorem selected_cut_00875 : selected 8 ⟨35420, by decide⟩
    (prefixPartial 13 16472) = some ⟨13, 2, 0, 35420, 16472, 685, 16384⟩ := by
  decide +kernel

theorem context_13_16472_35420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16472 ⟨35420, by decide⟩ :=
  accepted_of_selected 13 16472 ⟨35420, by decide⟩ ⟨13, 2, 0, 35420, 16472, 685, 16384⟩
    (by decide) selected_cut_00875

theorem selected_cut_00876 : selected 8 ⟨35457, by decide⟩
    (prefixPartial 13 16473) = some ⟨13, 2, 0, 35457, 16473, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_16473_35457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16473 ⟨35457, by decide⟩ :=
  accepted_of_selected 13 16473 ⟨35457, by decide⟩ ⟨13, 2, 0, 35457, 16473, 1557, 16384⟩
    (by decide) selected_cut_00876

theorem selected_cut_00877 : selected 8 ⟨35484, by decide⟩
    (prefixPartial 13 16474) = some ⟨13, 2, 0, 35484, 16474, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_16474_35484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16474 ⟨35484, by decide⟩ :=
  accepted_of_selected 13 16474 ⟨35484, by decide⟩ ⟨13, 2, 0, 35484, 16474, 1413, 16384⟩
    (by decide) selected_cut_00877

theorem selected_cut_00878 : selected 8 ⟨35501, by decide⟩
    (prefixPartial 13 16475) = some ⟨13, 2, 0, 35501, 16475, 761, 16384⟩ := by
  decide +kernel

theorem context_13_16475_35501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16475 ⟨35501, by decide⟩ :=
  accepted_of_selected 13 16475 ⟨35501, by decide⟩ ⟨13, 2, 0, 35501, 16475, 761, 16384⟩
    (by decide) selected_cut_00878

theorem unmarked_context_12_4118_35502 : frontier 9 ⟨35502, by decide⟩
    (prefixCache 12 4118) (prefixPartial 12 4118) = false := by
  decide +kernel

theorem node_context_12_4118_35502 : EJMOriginalGlobalDAGData.nodes 9 ⟨35502, by decide⟩ =
    .split (coordinate 12) (![⟨35420, by decide⟩,⟨35457, by decide⟩,⟨35484, by decide⟩,⟨35501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4118_35502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4118 ⟨35502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4118
    ⟨35502, by decide⟩ (by decide) (![⟨35420, by decide⟩,⟨35457, by decide⟩,⟨35484, by decide⟩,⟨35501, by decide⟩]) unmarked_context_12_4118_35502 node_context_12_4118_35502
  intro a
  fin_cases a
  · exact context_13_16472_35420
  · exact context_13_16473_35457
  · exact context_13_16474_35484
  · exact context_13_16475_35501

theorem selected_cut_00879 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4119) = some ⟨12, 1, 0, 893, 4119, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4119_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4119 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4119 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4119, 1, 65536⟩
    (by decide) selected_cut_00879

theorem unmarked_context_11_1029_35503 : frontier 10 ⟨35503, by decide⟩
    (prefixCache 11 1029) (prefixPartial 11 1029) = false := by
  decide +kernel

theorem node_context_11_1029_35503 : EJMOriginalGlobalDAGData.nodes 10 ⟨35503, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨35400, by decide⟩,⟨35502, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1029_35503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1029 ⟨35503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1029
    ⟨35503, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨35400, by decide⟩,⟨35502, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1029_35503 node_context_11_1029_35503
  intro a
  fin_cases a
  · exact context_12_4116_1738
  · exact context_12_4117_35400
  · exact context_12_4118_35502
  · exact context_12_4119_893

theorem selected_cut_00880 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4120) = some ⟨12, 1, 0, 1738, 4120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4120_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4120 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4120 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4120, 1, 65536⟩
    (by decide) selected_cut_00880

theorem selected_cut_00881 : selected 9 ⟨35592, by decide⟩
    (prefixPartial 12 4121) = some ⟨12, 2, 0, 35592, 4121, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_4121_35592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4121 ⟨35592, by decide⟩ :=
  accepted_of_selected 12 4121 ⟨35592, by decide⟩ ⟨12, 2, 0, 35592, 4121, 3329, 65536⟩
    (by decide) selected_cut_00881

theorem selected_cut_00882 : selected 8 ⟨35613, by decide⟩
    (prefixPartial 13 16488) = some ⟨13, 2, 0, 35613, 16488, 613, 16384⟩ := by
  decide +kernel

theorem context_13_16488_35613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16488 ⟨35613, by decide⟩ :=
  accepted_of_selected 13 16488 ⟨35613, by decide⟩ ⟨13, 2, 0, 35613, 16488, 613, 16384⟩
    (by decide) selected_cut_00882

theorem selected_cut_00883 : selected 8 ⟨35659, by decide⟩
    (prefixPartial 13 16489) = some ⟨13, 2, 0, 35659, 16489, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_16489_35659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16489 ⟨35659, by decide⟩ :=
  accepted_of_selected 13 16489 ⟨35659, by decide⟩ ⟨13, 2, 0, 35659, 16489, 1825, 16384⟩
    (by decide) selected_cut_00883

theorem selected_cut_00884 : selected 8 ⟨35683, by decide⟩
    (prefixPartial 13 16490) = some ⟨13, 2, 0, 35683, 16490, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_16490_35683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16490 ⟨35683, by decide⟩ :=
  accepted_of_selected 13 16490 ⟨35683, by decide⟩ ⟨13, 2, 0, 35683, 16490, 1305, 16384⟩
    (by decide) selected_cut_00884

theorem selected_cut_00885 : selected 8 ⟨35697, by decide⟩
    (prefixPartial 13 16491) = some ⟨13, 2, 0, 35697, 16491, 805, 16384⟩ := by
  decide +kernel

theorem context_13_16491_35697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16491 ⟨35697, by decide⟩ :=
  accepted_of_selected 13 16491 ⟨35697, by decide⟩ ⟨13, 2, 0, 35697, 16491, 805, 16384⟩
    (by decide) selected_cut_00885

theorem unmarked_context_12_4122_35698 : frontier 9 ⟨35698, by decide⟩
    (prefixCache 12 4122) (prefixPartial 12 4122) = false := by
  decide +kernel

theorem node_context_12_4122_35698 : EJMOriginalGlobalDAGData.nodes 9 ⟨35698, by decide⟩ =
    .split (coordinate 12) (![⟨35613, by decide⟩,⟨35659, by decide⟩,⟨35683, by decide⟩,⟨35697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4122_35698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4122 ⟨35698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4122
    ⟨35698, by decide⟩ (by decide) (![⟨35613, by decide⟩,⟨35659, by decide⟩,⟨35683, by decide⟩,⟨35697, by decide⟩]) unmarked_context_12_4122_35698 node_context_12_4122_35698
  intro a
  fin_cases a
  · exact context_13_16488_35613
  · exact context_13_16489_35659
  · exact context_13_16490_35683
  · exact context_13_16491_35697

theorem selected_cut_00886 : selected 8 ⟨35714, by decide⟩
    (prefixPartial 13 16492) = some ⟨13, 2, 0, 35714, 16492, 553, 16384⟩ := by
  decide +kernel

theorem context_13_16492_35714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16492 ⟨35714, by decide⟩ :=
  accepted_of_selected 13 16492 ⟨35714, by decide⟩ ⟨13, 2, 0, 35714, 16492, 553, 16384⟩
    (by decide) selected_cut_00886

theorem selected_cut_00887 : selected 8 ⟨35748, by decide⟩
    (prefixPartial 13 16493) = some ⟨13, 2, 0, 35748, 16493, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_16493_35748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16493 ⟨35748, by decide⟩ :=
  accepted_of_selected 13 16493 ⟨35748, by decide⟩ ⟨13, 2, 0, 35748, 16493, 1901, 16384⟩
    (by decide) selected_cut_00887

theorem selected_cut_00888 : selected 8 ⟨35779, by decide⟩
    (prefixPartial 13 16494) = some ⟨13, 2, 0, 35779, 16494, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_16494_35779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16494 ⟨35779, by decide⟩ :=
  accepted_of_selected 13 16494 ⟨35779, by decide⟩ ⟨13, 2, 0, 35779, 16494, 1473, 16384⟩
    (by decide) selected_cut_00888

theorem selected_cut_00889 : selected 8 ⟨35795, by decide⟩
    (prefixPartial 13 16495) = some ⟨13, 2, 0, 35795, 16495, 841, 16384⟩ := by
  decide +kernel

theorem context_13_16495_35795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16495 ⟨35795, by decide⟩ :=
  accepted_of_selected 13 16495 ⟨35795, by decide⟩ ⟨13, 2, 0, 35795, 16495, 841, 16384⟩
    (by decide) selected_cut_00889

theorem unmarked_context_12_4123_35796 : frontier 9 ⟨35796, by decide⟩
    (prefixCache 12 4123) (prefixPartial 12 4123) = false := by
  decide +kernel

theorem node_context_12_4123_35796 : EJMOriginalGlobalDAGData.nodes 9 ⟨35796, by decide⟩ =
    .split (coordinate 12) (![⟨35714, by decide⟩,⟨35748, by decide⟩,⟨35779, by decide⟩,⟨35795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4123_35796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4123 ⟨35796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4123
    ⟨35796, by decide⟩ (by decide) (![⟨35714, by decide⟩,⟨35748, by decide⟩,⟨35779, by decide⟩,⟨35795, by decide⟩]) unmarked_context_12_4123_35796 node_context_12_4123_35796
  intro a
  fin_cases a
  · exact context_13_16492_35714
  · exact context_13_16493_35748
  · exact context_13_16494_35779
  · exact context_13_16495_35795

theorem unmarked_context_11_1030_35797 : frontier 10 ⟨35797, by decide⟩
    (prefixCache 11 1030) (prefixPartial 11 1030) = false := by
  decide +kernel

theorem node_context_11_1030_35797 : EJMOriginalGlobalDAGData.nodes 10 ⟨35797, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨35592, by decide⟩,⟨35698, by decide⟩,⟨35796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1030_35797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1030 ⟨35797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1030
    ⟨35797, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨35592, by decide⟩,⟨35698, by decide⟩,⟨35796, by decide⟩]) unmarked_context_11_1030_35797 node_context_11_1030_35797
  intro a
  fin_cases a
  · exact context_12_4120_1738
  · exact context_12_4121_35592
  · exact context_12_4122_35698
  · exact context_12_4123_35796

theorem selected_cut_00890 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1031) = some ⟨11, 1, 0, 1736, 1031, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1031_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1031 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1031 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1031, 1, 262144⟩
    (by decide) selected_cut_00890

theorem unmarked_context_10_257_35798 : frontier 11 ⟨35798, by decide⟩
    (prefixCache 10 257) (prefixPartial 10 257) = false := by
  decide +kernel

theorem node_context_10_257_35798 : EJMOriginalGlobalDAGData.nodes 11 ⟨35798, by decide⟩ =
    .split (coordinate 10) (![⟨35335, by decide⟩,⟨35503, by decide⟩,⟨35797, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_257_35798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 257 ⟨35798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 257
    ⟨35798, by decide⟩ (by decide) (![⟨35335, by decide⟩,⟨35503, by decide⟩,⟨35797, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_257_35798 node_context_10_257_35798
  intro a
  fin_cases a
  · exact context_11_1028_35335
  · exact context_11_1029_35503
  · exact context_11_1030_35797
  · exact context_11_1031_1736

theorem selected_cut_00891 : selected 10 ⟨35899, by decide⟩
    (prefixPartial 11 1032) = some ⟨11, 2, 0, 35899, 1032, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_1032_35899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1032 ⟨35899, by decide⟩ :=
  accepted_of_selected 11 1032 ⟨35899, by decide⟩ ⟨11, 2, 0, 35899, 1032, 3545, 262144⟩
    (by decide) selected_cut_00891

theorem selected_cut_00892 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4132) = some ⟨12, 1, 0, 1738, 4132, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4132_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4132 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4132 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4132, 1, 65536⟩
    (by decide) selected_cut_00892

theorem selected_cut_00893 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4133) = some ⟨12, 1, 0, 1738, 4133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4133_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4133 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4133 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4133, 1, 65536⟩
    (by decide) selected_cut_00893

theorem selected_cut_00894 : selected 9 ⟨35986, by decide⟩
    (prefixPartial 12 4134) = some ⟨12, 2, 0, 35986, 4134, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_4134_35986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4134 ⟨35986, by decide⟩ :=
  accepted_of_selected 12 4134 ⟨35986, by decide⟩ ⟨12, 2, 0, 35986, 4134, 3265, 65536⟩
    (by decide) selected_cut_00894

theorem selected_cut_00895 : selected 9 ⟨36059, by decide⟩
    (prefixPartial 12 4135) = some ⟨12, 2, 0, 36059, 4135, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_4135_36059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4135 ⟨36059, by decide⟩ :=
  accepted_of_selected 12 4135 ⟨36059, by decide⟩ ⟨12, 2, 0, 36059, 4135, 2669, 65536⟩
    (by decide) selected_cut_00895

theorem unmarked_context_11_1033_36060 : frontier 10 ⟨36060, by decide⟩
    (prefixCache 11 1033) (prefixPartial 11 1033) = false := by
  decide +kernel

theorem node_context_11_1033_36060 : EJMOriginalGlobalDAGData.nodes 10 ⟨36060, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨35986, by decide⟩,⟨36059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1033_36060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1033 ⟨36060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1033
    ⟨36060, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨35986, by decide⟩,⟨36059, by decide⟩]) unmarked_context_11_1033_36060 node_context_11_1033_36060
  intro a
  fin_cases a
  · exact context_12_4132_1738
  · exact context_12_4133_1738
  · exact context_12_4134_35986
  · exact context_12_4135_36059

theorem selected_cut_00896 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4136) = some ⟨12, 1, 0, 1738, 4136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4136_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4136 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4136 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4136, 1, 65536⟩
    (by decide) selected_cut_00896

theorem selected_cut_00897 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4137) = some ⟨12, 1, 0, 1738, 4137, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4137_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4137 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4137 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4137, 1, 65536⟩
    (by decide) selected_cut_00897

theorem selected_cut_00898 : selected 9 ⟨36146, by decide⟩
    (prefixPartial 12 4138) = some ⟨12, 2, 0, 36146, 4138, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_4138_36146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4138 ⟨36146, by decide⟩ :=
  accepted_of_selected 12 4138 ⟨36146, by decide⟩ ⟨12, 2, 0, 36146, 4138, 3205, 65536⟩
    (by decide) selected_cut_00898

theorem selected_cut_00899 : selected 8 ⟨36156, by decide⟩
    (prefixPartial 13 16556) = some ⟨13, 2, 0, 36156, 16556, 217, 16384⟩ := by
  decide +kernel

theorem context_13_16556_36156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16556 ⟨36156, by decide⟩ :=
  accepted_of_selected 13 16556 ⟨36156, by decide⟩ ⟨13, 2, 0, 36156, 16556, 217, 16384⟩
    (by decide) selected_cut_00899

theorem selected_cut_00900 : selected 8 ⟨36201, by decide⟩
    (prefixPartial 13 16557) = some ⟨13, 2, 0, 36201, 16557, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_16557_36201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16557 ⟨36201, by decide⟩ :=
  accepted_of_selected 13 16557 ⟨36201, by decide⟩ ⟨13, 2, 0, 36201, 16557, 2325, 16384⟩
    (by decide) selected_cut_00900

theorem selected_cut_00901 : selected 8 ⟨36225, by decide⟩
    (prefixPartial 13 16558) = some ⟨13, 2, 0, 36225, 16558, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_16558_36225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16558 ⟨36225, by decide⟩ :=
  accepted_of_selected 13 16558 ⟨36225, by decide⟩ ⟨13, 2, 0, 36225, 16558, 1161, 16384⟩
    (by decide) selected_cut_00901

theorem selected_cut_00902 : selected 8 ⟨36240, by decide⟩
    (prefixPartial 13 16559) = some ⟨13, 2, 0, 36240, 16559, 853, 16384⟩ := by
  decide +kernel

theorem context_13_16559_36240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16559 ⟨36240, by decide⟩ :=
  accepted_of_selected 13 16559 ⟨36240, by decide⟩ ⟨13, 2, 0, 36240, 16559, 853, 16384⟩
    (by decide) selected_cut_00902

theorem unmarked_context_12_4139_36241 : frontier 9 ⟨36241, by decide⟩
    (prefixCache 12 4139) (prefixPartial 12 4139) = false := by
  decide +kernel

theorem node_context_12_4139_36241 : EJMOriginalGlobalDAGData.nodes 9 ⟨36241, by decide⟩ =
    .split (coordinate 12) (![⟨36156, by decide⟩,⟨36201, by decide⟩,⟨36225, by decide⟩,⟨36240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4139_36241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4139 ⟨36241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4139
    ⟨36241, by decide⟩ (by decide) (![⟨36156, by decide⟩,⟨36201, by decide⟩,⟨36225, by decide⟩,⟨36240, by decide⟩]) unmarked_context_12_4139_36241 node_context_12_4139_36241
  intro a
  fin_cases a
  · exact context_13_16556_36156
  · exact context_13_16557_36201
  · exact context_13_16558_36225
  · exact context_13_16559_36240

theorem unmarked_context_11_1034_36242 : frontier 10 ⟨36242, by decide⟩
    (prefixCache 11 1034) (prefixPartial 11 1034) = false := by
  decide +kernel

theorem node_context_11_1034_36242 : EJMOriginalGlobalDAGData.nodes 10 ⟨36242, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨36146, by decide⟩,⟨36241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1034_36242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1034 ⟨36242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1034
    ⟨36242, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨36146, by decide⟩,⟨36241, by decide⟩]) unmarked_context_11_1034_36242 node_context_11_1034_36242
  intro a
  fin_cases a
  · exact context_12_4136_1738
  · exact context_12_4137_1738
  · exact context_12_4138_36146
  · exact context_12_4139_36241

theorem selected_cut_00903 : selected 10 ⟨36315, by decide⟩
    (prefixPartial 11 1035) = some ⟨11, 2, 0, 36315, 1035, 3325, 262144⟩ := by
  decide +kernel

theorem context_11_1035_36315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1035 ⟨36315, by decide⟩ :=
  accepted_of_selected 11 1035 ⟨36315, by decide⟩ ⟨11, 2, 0, 36315, 1035, 3325, 262144⟩
    (by decide) selected_cut_00903

theorem unmarked_context_10_258_36316 : frontier 11 ⟨36316, by decide⟩
    (prefixCache 10 258) (prefixPartial 10 258) = false := by
  decide +kernel

theorem node_context_10_258_36316 : EJMOriginalGlobalDAGData.nodes 11 ⟨36316, by decide⟩ =
    .split (coordinate 10) (![⟨35899, by decide⟩,⟨36060, by decide⟩,⟨36242, by decide⟩,⟨36315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_258_36316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 258 ⟨36316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 258
    ⟨36316, by decide⟩ (by decide) (![⟨35899, by decide⟩,⟨36060, by decide⟩,⟨36242, by decide⟩,⟨36315, by decide⟩]) unmarked_context_10_258_36316 node_context_10_258_36316
  intro a
  fin_cases a
  · exact context_11_1032_35899
  · exact context_11_1033_36060
  · exact context_11_1034_36242
  · exact context_11_1035_36315

theorem selected_cut_00904 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 259) = some ⟨10, 1, 0, 3440, 259, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_259_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 259 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 259 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 259, 1, 1048576⟩
    (by decide) selected_cut_00904

theorem unmarked_context_9_64_36317 : frontier 12 ⟨36317, by decide⟩
    (prefixCache 9 64) (prefixPartial 9 64) = false := by
  decide +kernel

theorem node_context_9_64_36317 : EJMOriginalGlobalDAGData.nodes 12 ⟨36317, by decide⟩ =
    .split (coordinate 9) (![⟨35219, by decide⟩,⟨35798, by decide⟩,⟨36316, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_64_36317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 64 ⟨36317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 64
    ⟨36317, by decide⟩ (by decide) (![⟨35219, by decide⟩,⟨35798, by decide⟩,⟨36316, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_64_36317 node_context_9_64_36317
  intro a
  fin_cases a
  · exact context_10_256_35219
  · exact context_10_257_35798
  · exact context_10_258_36316
  · exact context_10_259_3440

theorem selected_cut_00905 : selected 9 ⟨36483, by decide⟩
    (prefixPartial 12 4160) = some ⟨12, 2, 0, 36483, 4160, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_4160_36483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4160 ⟨36483, by decide⟩ :=
  accepted_of_selected 12 4160 ⟨36483, by decide⟩ ⟨12, 2, 0, 36483, 4160, 1733, 65536⟩
    (by decide) selected_cut_00905

theorem selected_cut_00906 : selected 9 ⟨36553, by decide⟩
    (prefixPartial 12 4161) = some ⟨12, 2, 0, 36553, 4161, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_4161_36553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4161 ⟨36553, by decide⟩ :=
  accepted_of_selected 12 4161 ⟨36553, by decide⟩ ⟨12, 2, 0, 36553, 4161, 3373, 65536⟩
    (by decide) selected_cut_00906

theorem selected_cut_00907 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16648) = some ⟨13, 1, 0, 3444, 16648, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16648_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16648 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16648 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16648, 1, 16384⟩
    (by decide) selected_cut_00907

theorem selected_cut_00908 : selected 8 ⟨36609, by decide⟩
    (prefixPartial 13 16649) = some ⟨13, 2, 0, 36609, 16649, 3109, 16384⟩ := by
  decide +kernel

theorem context_13_16649_36609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16649 ⟨36609, by decide⟩ :=
  accepted_of_selected 13 16649 ⟨36609, by decide⟩ ⟨13, 2, 0, 36609, 16649, 3109, 16384⟩
    (by decide) selected_cut_00908

theorem selected_cut_00909 : selected 8 ⟨36666, by decide⟩
    (prefixPartial 13 16650) = some ⟨13, 2, 0, 36666, 16650, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_16650_36666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16650 ⟨36666, by decide⟩ :=
  accepted_of_selected 13 16650 ⟨36666, by decide⟩ ⟨13, 2, 0, 36666, 16650, 2297, 16384⟩
    (by decide) selected_cut_00909

theorem selected_cut_00910 : selected 8 ⟨36685, by decide⟩
    (prefixPartial 13 16651) = some ⟨13, 2, 0, 36685, 16651, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_16651_36685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16651 ⟨36685, by decide⟩ :=
  accepted_of_selected 13 16651 ⟨36685, by decide⟩ ⟨13, 2, 0, 36685, 16651, 1073, 16384⟩
    (by decide) selected_cut_00910

theorem unmarked_context_12_4162_36686 : frontier 9 ⟨36686, by decide⟩
    (prefixCache 12 4162) (prefixPartial 12 4162) = false := by
  decide +kernel

theorem node_context_12_4162_36686 : EJMOriginalGlobalDAGData.nodes 9 ⟨36686, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨36609, by decide⟩,⟨36666, by decide⟩,⟨36685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4162_36686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4162 ⟨36686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4162
    ⟨36686, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨36609, by decide⟩,⟨36666, by decide⟩,⟨36685, by decide⟩]) unmarked_context_12_4162_36686 node_context_12_4162_36686
  intro a
  fin_cases a
  · exact context_13_16648_3444
  · exact context_13_16649_36609
  · exact context_13_16650_36666
  · exact context_13_16651_36685

theorem selected_cut_00911 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4163) = some ⟨12, 1, 0, 893, 4163, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4163_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4163 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4163 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4163, 1, 65536⟩
    (by decide) selected_cut_00911

theorem unmarked_context_11_1040_36687 : frontier 10 ⟨36687, by decide⟩
    (prefixCache 11 1040) (prefixPartial 11 1040) = false := by
  decide +kernel

theorem node_context_11_1040_36687 : EJMOriginalGlobalDAGData.nodes 10 ⟨36687, by decide⟩ =
    .split (coordinate 11) (![⟨36483, by decide⟩,⟨36553, by decide⟩,⟨36686, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1040_36687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1040 ⟨36687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1040
    ⟨36687, by decide⟩ (by decide) (![⟨36483, by decide⟩,⟨36553, by decide⟩,⟨36686, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1040_36687 node_context_11_1040_36687
  intro a
  fin_cases a
  · exact context_12_4160_36483
  · exact context_12_4161_36553
  · exact context_12_4162_36686
  · exact context_12_4163_893

theorem selected_cut_00912 : selected 9 ⟨36738, by decide⟩
    (prefixPartial 12 4164) = some ⟨12, 2, 0, 36738, 4164, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_4164_36738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4164 ⟨36738, by decide⟩ :=
  accepted_of_selected 12 4164 ⟨36738, by decide⟩ ⟨12, 2, 0, 36738, 4164, 1541, 65536⟩
    (by decide) selected_cut_00912

theorem selected_cut_00913 : selected 9 ⟨36798, by decide⟩
    (prefixPartial 12 4165) = some ⟨12, 2, 0, 36798, 4165, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_4165_36798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4165 ⟨36798, by decide⟩ :=
  accepted_of_selected 12 4165 ⟨36798, by decide⟩ ⟨12, 2, 0, 36798, 4165, 2789, 65536⟩
    (by decide) selected_cut_00913

theorem selected_cut_00914 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16664) = some ⟨13, 1, 0, 3444, 16664, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16664_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16664 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16664 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16664, 1, 16384⟩
    (by decide) selected_cut_00914

theorem selected_cut_00915 : selected 8 ⟨36850, by decide⟩
    (prefixPartial 13 16665) = some ⟨13, 2, 0, 36850, 16665, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_16665_36850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16665 ⟨36850, by decide⟩ :=
  accepted_of_selected 13 16665 ⟨36850, by decide⟩ ⟨13, 2, 0, 36850, 16665, 2553, 16384⟩
    (by decide) selected_cut_00915

theorem selected_cut_00916 : selected 8 ⟨36886, by decide⟩
    (prefixPartial 13 16666) = some ⟨13, 2, 0, 36886, 16666, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_16666_36886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16666 ⟨36886, by decide⟩ :=
  accepted_of_selected 13 16666 ⟨36886, by decide⟩ ⟨13, 2, 0, 36886, 16666, 2037, 16384⟩
    (by decide) selected_cut_00916

theorem selected_cut_00917 : selected 8 ⟨36903, by decide⟩
    (prefixPartial 13 16667) = some ⟨13, 2, 0, 36903, 16667, 969, 16384⟩ := by
  decide +kernel

theorem context_13_16667_36903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16667 ⟨36903, by decide⟩ :=
  accepted_of_selected 13 16667 ⟨36903, by decide⟩ ⟨13, 2, 0, 36903, 16667, 969, 16384⟩
    (by decide) selected_cut_00917

theorem unmarked_context_12_4166_36904 : frontier 9 ⟨36904, by decide⟩
    (prefixCache 12 4166) (prefixPartial 12 4166) = false := by
  decide +kernel

theorem node_context_12_4166_36904 : EJMOriginalGlobalDAGData.nodes 9 ⟨36904, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨36850, by decide⟩,⟨36886, by decide⟩,⟨36903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4166_36904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4166 ⟨36904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4166
    ⟨36904, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨36850, by decide⟩,⟨36886, by decide⟩,⟨36903, by decide⟩]) unmarked_context_12_4166_36904 node_context_12_4166_36904
  intro a
  fin_cases a
  · exact context_13_16664_3444
  · exact context_13_16665_36850
  · exact context_13_16666_36886
  · exact context_13_16667_36903

theorem selected_cut_00918 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4167) = some ⟨12, 1, 0, 893, 4167, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4167_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4167 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4167 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4167, 1, 65536⟩
    (by decide) selected_cut_00918

theorem unmarked_context_11_1041_36905 : frontier 10 ⟨36905, by decide⟩
    (prefixCache 11 1041) (prefixPartial 11 1041) = false := by
  decide +kernel

theorem node_context_11_1041_36905 : EJMOriginalGlobalDAGData.nodes 10 ⟨36905, by decide⟩ =
    .split (coordinate 11) (![⟨36738, by decide⟩,⟨36798, by decide⟩,⟨36904, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1041_36905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1041 ⟨36905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1041
    ⟨36905, by decide⟩ (by decide) (![⟨36738, by decide⟩,⟨36798, by decide⟩,⟨36904, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1041_36905 node_context_11_1041_36905
  intro a
  fin_cases a
  · exact context_12_4164_36738
  · exact context_12_4165_36798
  · exact context_12_4166_36904
  · exact context_12_4167_893

theorem selected_cut_00919 : selected 9 ⟨36957, by decide⟩
    (prefixPartial 12 4168) = some ⟨12, 2, 0, 36957, 4168, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_4168_36957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4168 ⟨36957, by decide⟩ :=
  accepted_of_selected 12 4168 ⟨36957, by decide⟩ ⟨12, 2, 0, 36957, 4168, 2013, 65536⟩
    (by decide) selected_cut_00919

theorem selected_cut_00920 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16676) = some ⟨13, 1, 0, 3444, 16676, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16676_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16676 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16676 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16676, 1, 16384⟩
    (by decide) selected_cut_00920

theorem selected_cut_00921 : selected 8 ⟨36987, by decide⟩
    (prefixPartial 13 16677) = some ⟨13, 2, 0, 36987, 16677, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_16677_36987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16677 ⟨36987, by decide⟩ :=
  accepted_of_selected 13 16677 ⟨36987, by decide⟩ ⟨13, 2, 0, 36987, 16677, 1745, 16384⟩
    (by decide) selected_cut_00921

theorem selected_cut_00922 : selected 8 ⟨37023, by decide⟩
    (prefixPartial 13 16678) = some ⟨13, 2, 0, 37023, 16678, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_16678_37023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16678 ⟨37023, by decide⟩ :=
  accepted_of_selected 13 16678 ⟨37023, by decide⟩ ⟨13, 2, 0, 37023, 16678, 2005, 16384⟩
    (by decide) selected_cut_00922

theorem selected_cut_00923 : selected 8 ⟨37035, by decide⟩
    (prefixPartial 13 16679) = some ⟨13, 2, 0, 37035, 16679, 941, 16384⟩ := by
  decide +kernel

theorem context_13_16679_37035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16679 ⟨37035, by decide⟩ :=
  accepted_of_selected 13 16679 ⟨37035, by decide⟩ ⟨13, 2, 0, 37035, 16679, 941, 16384⟩
    (by decide) selected_cut_00923

theorem unmarked_context_12_4169_37036 : frontier 9 ⟨37036, by decide⟩
    (prefixCache 12 4169) (prefixPartial 12 4169) = false := by
  decide +kernel

theorem node_context_12_4169_37036 : EJMOriginalGlobalDAGData.nodes 9 ⟨37036, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨36987, by decide⟩,⟨37023, by decide⟩,⟨37035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4169_37036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4169 ⟨37036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4169
    ⟨37036, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨36987, by decide⟩,⟨37023, by decide⟩,⟨37035, by decide⟩]) unmarked_context_12_4169_37036 node_context_12_4169_37036
  intro a
  fin_cases a
  · exact context_13_16676_3444
  · exact context_13_16677_36987
  · exact context_13_16678_37023
  · exact context_13_16679_37035

theorem selected_cut_00924 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16680) = some ⟨13, 1, 0, 3444, 16680, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16680_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16680 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16680 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16680, 1, 16384⟩
    (by decide) selected_cut_00924

theorem selected_cut_00925 : selected 8 ⟨37066, by decide⟩
    (prefixPartial 13 16681) = some ⟨13, 2, 0, 37066, 16681, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_16681_37066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16681 ⟨37066, by decide⟩ :=
  accepted_of_selected 13 16681 ⟨37066, by decide⟩ ⟨13, 2, 0, 37066, 16681, 1701, 16384⟩
    (by decide) selected_cut_00925

theorem selected_cut_00926 : selected 8 ⟨37098, by decide⟩
    (prefixPartial 13 16682) = some ⟨13, 2, 0, 37098, 16682, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_16682_37098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16682 ⟨37098, by decide⟩ :=
  accepted_of_selected 13 16682 ⟨37098, by decide⟩ ⟨13, 2, 0, 37098, 16682, 1889, 16384⟩
    (by decide) selected_cut_00926

theorem selected_cut_00927 : selected 8 ⟨37110, by decide⟩
    (prefixPartial 13 16683) = some ⟨13, 2, 0, 37110, 16683, 929, 16384⟩ := by
  decide +kernel

theorem context_13_16683_37110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16683 ⟨37110, by decide⟩ :=
  accepted_of_selected 13 16683 ⟨37110, by decide⟩ ⟨13, 2, 0, 37110, 16683, 929, 16384⟩
    (by decide) selected_cut_00927

theorem unmarked_context_12_4170_37111 : frontier 9 ⟨37111, by decide⟩
    (prefixCache 12 4170) (prefixPartial 12 4170) = false := by
  decide +kernel

theorem node_context_12_4170_37111 : EJMOriginalGlobalDAGData.nodes 9 ⟨37111, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨37066, by decide⟩,⟨37098, by decide⟩,⟨37110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4170_37111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4170 ⟨37111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4170
    ⟨37111, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨37066, by decide⟩,⟨37098, by decide⟩,⟨37110, by decide⟩]) unmarked_context_12_4170_37111 node_context_12_4170_37111
  intro a
  fin_cases a
  · exact context_13_16680_3444
  · exact context_13_16681_37066
  · exact context_13_16682_37098
  · exact context_13_16683_37110

theorem selected_cut_00928 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16684) = some ⟨13, 1, 0, 3444, 16684, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16684_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16684 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16684 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16684, 1, 16384⟩
    (by decide) selected_cut_00928

theorem selected_cut_00929 : selected 8 ⟨37139, by decide⟩
    (prefixPartial 13 16685) = some ⟨13, 2, 0, 37139, 16685, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_16685_37139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16685 ⟨37139, by decide⟩ :=
  accepted_of_selected 13 16685 ⟨37139, by decide⟩ ⟨13, 2, 0, 37139, 16685, 1545, 16384⟩
    (by decide) selected_cut_00929

theorem selected_cut_00930 : selected 8 ⟨37169, by decide⟩
    (prefixPartial 13 16686) = some ⟨13, 2, 0, 37169, 16686, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_16686_37169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16686 ⟨37169, by decide⟩ :=
  accepted_of_selected 13 16686 ⟨37169, by decide⟩ ⟨13, 2, 0, 37169, 16686, 2049, 16384⟩
    (by decide) selected_cut_00930

theorem selected_cut_00931 : selected 8 ⟨37186, by decide⟩
    (prefixPartial 13 16687) = some ⟨13, 2, 0, 37186, 16687, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_16687_37186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16687 ⟨37186, by decide⟩ :=
  accepted_of_selected 13 16687 ⟨37186, by decide⟩ ⟨13, 2, 0, 37186, 16687, 1089, 16384⟩
    (by decide) selected_cut_00931

theorem unmarked_context_12_4171_37187 : frontier 9 ⟨37187, by decide⟩
    (prefixCache 12 4171) (prefixPartial 12 4171) = false := by
  decide +kernel

theorem node_context_12_4171_37187 : EJMOriginalGlobalDAGData.nodes 9 ⟨37187, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨37139, by decide⟩,⟨37169, by decide⟩,⟨37186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4171_37187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4171 ⟨37187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4171
    ⟨37187, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨37139, by decide⟩,⟨37169, by decide⟩,⟨37186, by decide⟩]) unmarked_context_12_4171_37187 node_context_12_4171_37187
  intro a
  fin_cases a
  · exact context_13_16684_3444
  · exact context_13_16685_37139
  · exact context_13_16686_37169
  · exact context_13_16687_37186

theorem unmarked_context_11_1042_37188 : frontier 10 ⟨37188, by decide⟩
    (prefixCache 11 1042) (prefixPartial 11 1042) = false := by
  decide +kernel

theorem node_context_11_1042_37188 : EJMOriginalGlobalDAGData.nodes 10 ⟨37188, by decide⟩ =
    .split (coordinate 11) (![⟨36957, by decide⟩,⟨37036, by decide⟩,⟨37111, by decide⟩,⟨37187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1042_37188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1042 ⟨37188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1042
    ⟨37188, by decide⟩ (by decide) (![⟨36957, by decide⟩,⟨37036, by decide⟩,⟨37111, by decide⟩,⟨37187, by decide⟩]) unmarked_context_11_1042_37188 node_context_11_1042_37188
  intro a
  fin_cases a
  · exact context_12_4168_36957
  · exact context_12_4169_37036
  · exact context_12_4170_37111
  · exact context_12_4171_37187

theorem selected_cut_00932 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1043) = some ⟨11, 1, 0, 1736, 1043, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1043_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1043 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1043 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1043, 1, 262144⟩
    (by decide) selected_cut_00932

theorem unmarked_context_10_260_37189 : frontier 11 ⟨37189, by decide⟩
    (prefixCache 10 260) (prefixPartial 10 260) = false := by
  decide +kernel

theorem node_context_10_260_37189 : EJMOriginalGlobalDAGData.nodes 11 ⟨37189, by decide⟩ =
    .split (coordinate 10) (![⟨36687, by decide⟩,⟨36905, by decide⟩,⟨37188, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_260_37189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 260 ⟨37189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 260
    ⟨37189, by decide⟩ (by decide) (![⟨36687, by decide⟩,⟨36905, by decide⟩,⟨37188, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_260_37189 node_context_10_260_37189
  intro a
  fin_cases a
  · exact context_11_1040_36687
  · exact context_11_1041_36905
  · exact context_11_1042_37188
  · exact context_11_1043_1736

theorem selected_cut_00933 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4176) = some ⟨12, 1, 0, 1738, 4176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4176_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4176 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4176 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4176, 1, 65536⟩
    (by decide) selected_cut_00933

theorem selected_cut_00934 : selected 9 ⟨37230, by decide⟩
    (prefixPartial 12 4177) = some ⟨12, 2, 0, 37230, 4177, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_4177_37230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4177 ⟨37230, by decide⟩ :=
  accepted_of_selected 12 4177 ⟨37230, by decide⟩ ⟨12, 2, 0, 37230, 4177, 1629, 65536⟩
    (by decide) selected_cut_00934

theorem selected_cut_00935 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16712) = some ⟨13, 1, 0, 3444, 16712, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16712_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16712 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16712 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16712, 1, 16384⟩
    (by decide) selected_cut_00935

theorem selected_cut_00936 : selected 8 ⟨37261, by decide⟩
    (prefixPartial 13 16713) = some ⟨13, 2, 0, 37261, 16713, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_16713_37261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16713 ⟨37261, by decide⟩ :=
  accepted_of_selected 13 16713 ⟨37261, by decide⟩ ⟨13, 2, 0, 37261, 16713, 1525, 16384⟩
    (by decide) selected_cut_00936

theorem selected_cut_00937 : selected 8 ⟨37292, by decide⟩
    (prefixPartial 13 16714) = some ⟨13, 2, 0, 37292, 16714, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_16714_37292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16714 ⟨37292, by decide⟩ :=
  accepted_of_selected 13 16714 ⟨37292, by decide⟩ ⟨13, 2, 0, 37292, 16714, 1721, 16384⟩
    (by decide) selected_cut_00937

theorem selected_cut_00938 : selected 8 ⟨37308, by decide⟩
    (prefixPartial 13 16715) = some ⟨13, 2, 0, 37308, 16715, 865, 16384⟩ := by
  decide +kernel

theorem context_13_16715_37308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16715 ⟨37308, by decide⟩ :=
  accepted_of_selected 13 16715 ⟨37308, by decide⟩ ⟨13, 2, 0, 37308, 16715, 865, 16384⟩
    (by decide) selected_cut_00938

theorem unmarked_context_12_4178_37309 : frontier 9 ⟨37309, by decide⟩
    (prefixCache 12 4178) (prefixPartial 12 4178) = false := by
  decide +kernel

theorem node_context_12_4178_37309 : EJMOriginalGlobalDAGData.nodes 9 ⟨37309, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨37261, by decide⟩,⟨37292, by decide⟩,⟨37308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4178_37309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4178 ⟨37309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4178
    ⟨37309, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨37261, by decide⟩,⟨37292, by decide⟩,⟨37308, by decide⟩]) unmarked_context_12_4178_37309 node_context_12_4178_37309
  intro a
  fin_cases a
  · exact context_13_16712_3444
  · exact context_13_16713_37261
  · exact context_13_16714_37292
  · exact context_13_16715_37308

theorem selected_cut_00939 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4179) = some ⟨12, 1, 0, 893, 4179, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4179_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4179 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4179 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4179, 1, 65536⟩
    (by decide) selected_cut_00939

theorem unmarked_context_11_1044_37310 : frontier 10 ⟨37310, by decide⟩
    (prefixCache 11 1044) (prefixPartial 11 1044) = false := by
  decide +kernel

theorem node_context_11_1044_37310 : EJMOriginalGlobalDAGData.nodes 10 ⟨37310, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨37230, by decide⟩,⟨37309, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1044_37310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1044 ⟨37310, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1044
    ⟨37310, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨37230, by decide⟩,⟨37309, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1044_37310 node_context_11_1044_37310
  intro a
  fin_cases a
  · exact context_12_4176_1738
  · exact context_12_4177_37230
  · exact context_12_4178_37309
  · exact context_12_4179_893

theorem selected_cut_00940 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4180) = some ⟨12, 1, 0, 1738, 4180, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4180_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4180 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4180 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4180, 1, 65536⟩
    (by decide) selected_cut_00940

theorem selected_cut_00941 : selected 9 ⟨37364, by decide⟩
    (prefixPartial 12 4181) = some ⟨12, 2, 0, 37364, 4181, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_4181_37364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4181 ⟨37364, by decide⟩ :=
  accepted_of_selected 12 4181 ⟨37364, by decide⟩ ⟨12, 2, 0, 37364, 4181, 2097, 65536⟩
    (by decide) selected_cut_00941

theorem selected_cut_00942 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16728) = some ⟨13, 1, 0, 3444, 16728, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16728_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16728 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16728 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16728, 1, 16384⟩
    (by decide) selected_cut_00942

theorem selected_cut_00943 : selected 8 ⟨37401, by decide⟩
    (prefixPartial 13 16729) = some ⟨13, 2, 0, 37401, 16729, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_16729_37401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16729 ⟨37401, by decide⟩ :=
  accepted_of_selected 13 16729 ⟨37401, by decide⟩ ⟨13, 2, 0, 37401, 16729, 1777, 16384⟩
    (by decide) selected_cut_00943

theorem selected_cut_00944 : selected 8 ⟨37457, by decide⟩
    (prefixPartial 13 16730) = some ⟨13, 2, 0, 37457, 16730, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_16730_37457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16730 ⟨37457, by decide⟩ :=
  accepted_of_selected 13 16730 ⟨37457, by decide⟩ ⟨13, 2, 0, 37457, 16730, 2589, 16384⟩
    (by decide) selected_cut_00944

theorem selected_cut_00945 : selected 8 ⟨37480, by decide⟩
    (prefixPartial 13 16731) = some ⟨13, 2, 0, 37480, 16731, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_16731_37480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16731 ⟨37480, by decide⟩ :=
  accepted_of_selected 13 16731 ⟨37480, by decide⟩ ⟨13, 2, 0, 37480, 16731, 1205, 16384⟩
    (by decide) selected_cut_00945

theorem unmarked_context_12_4182_37481 : frontier 9 ⟨37481, by decide⟩
    (prefixCache 12 4182) (prefixPartial 12 4182) = false := by
  decide +kernel

theorem node_context_12_4182_37481 : EJMOriginalGlobalDAGData.nodes 9 ⟨37481, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨37401, by decide⟩,⟨37457, by decide⟩,⟨37480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4182_37481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4182 ⟨37481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4182
    ⟨37481, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨37401, by decide⟩,⟨37457, by decide⟩,⟨37480, by decide⟩]) unmarked_context_12_4182_37481 node_context_12_4182_37481
  intro a
  fin_cases a
  · exact context_13_16728_3444
  · exact context_13_16729_37401
  · exact context_13_16730_37457
  · exact context_13_16731_37480

theorem selected_cut_00946 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4183) = some ⟨12, 1, 0, 893, 4183, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4183_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4183 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4183 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4183, 1, 65536⟩
    (by decide) selected_cut_00946

theorem unmarked_context_11_1045_37482 : frontier 10 ⟨37482, by decide⟩
    (prefixCache 11 1045) (prefixPartial 11 1045) = false := by
  decide +kernel

theorem node_context_11_1045_37482 : EJMOriginalGlobalDAGData.nodes 10 ⟨37482, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨37364, by decide⟩,⟨37481, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1045_37482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1045 ⟨37482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1045
    ⟨37482, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨37364, by decide⟩,⟨37481, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1045_37482 node_context_11_1045_37482
  intro a
  fin_cases a
  · exact context_12_4180_1738
  · exact context_12_4181_37364
  · exact context_12_4182_37481
  · exact context_12_4183_893

theorem selected_cut_00947 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4184) = some ⟨12, 1, 0, 1738, 4184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4184_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4184 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4184 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4184, 1, 65536⟩
    (by decide) selected_cut_00947

theorem selected_cut_00948 : selected 9 ⟨37598, by decide⟩
    (prefixPartial 12 4185) = some ⟨12, 2, 0, 37598, 4185, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_4185_37598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4185 ⟨37598, by decide⟩ :=
  accepted_of_selected 12 4185 ⟨37598, by decide⟩ ⟨12, 2, 0, 37598, 4185, 3821, 65536⟩
    (by decide) selected_cut_00948

theorem selected_cut_00949 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16744) = some ⟨13, 1, 0, 3444, 16744, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16744_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16744 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16744 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16744, 1, 16384⟩
    (by decide) selected_cut_00949

theorem selected_cut_00950 : selected 8 ⟨37634, by decide⟩
    (prefixPartial 13 16745) = some ⟨13, 2, 0, 37634, 16745, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_16745_37634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16745 ⟨37634, by decide⟩ :=
  accepted_of_selected 13 16745 ⟨37634, by decide⟩ ⟨13, 2, 0, 37634, 16745, 1425, 16384⟩
    (by decide) selected_cut_00950

theorem selected_cut_00951 : selected 8 ⟨37681, by decide⟩
    (prefixPartial 13 16746) = some ⟨13, 2, 0, 37681, 16746, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_16746_37681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16746 ⟨37681, by decide⟩ :=
  accepted_of_selected 13 16746 ⟨37681, by decide⟩ ⟨13, 2, 0, 37681, 16746, 2405, 16384⟩
    (by decide) selected_cut_00951

theorem selected_cut_00952 : selected 8 ⟨37698, by decide⟩
    (prefixPartial 13 16747) = some ⟨13, 2, 0, 37698, 16747, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_16747_37698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16747 ⟨37698, by decide⟩ :=
  accepted_of_selected 13 16747 ⟨37698, by decide⟩ ⟨13, 2, 0, 37698, 16747, 1221, 16384⟩
    (by decide) selected_cut_00952

theorem unmarked_context_12_4186_37699 : frontier 9 ⟨37699, by decide⟩
    (prefixCache 12 4186) (prefixPartial 12 4186) = false := by
  decide +kernel

theorem node_context_12_4186_37699 : EJMOriginalGlobalDAGData.nodes 9 ⟨37699, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨37634, by decide⟩,⟨37681, by decide⟩,⟨37698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4186_37699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4186 ⟨37699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4186
    ⟨37699, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨37634, by decide⟩,⟨37681, by decide⟩,⟨37698, by decide⟩]) unmarked_context_12_4186_37699 node_context_12_4186_37699
  intro a
  fin_cases a
  · exact context_13_16744_3444
  · exact context_13_16745_37634
  · exact context_13_16746_37681
  · exact context_13_16747_37698

theorem selected_cut_00953 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 16748) = some ⟨13, 1, 0, 3444, 16748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_16748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 16748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 16748, 1, 16384⟩
    (by decide) selected_cut_00953

theorem selected_cut_00954 : selected 8 ⟨37731, by decide⟩
    (prefixPartial 13 16749) = some ⟨13, 2, 0, 37731, 16749, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_16749_37731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16749 ⟨37731, by decide⟩ :=
  accepted_of_selected 13 16749 ⟨37731, by decide⟩ ⟨13, 2, 0, 37731, 16749, 1221, 16384⟩
    (by decide) selected_cut_00954

theorem selected_cut_00955 : selected 8 ⟨37794, by decide⟩
    (prefixPartial 13 16750) = some ⟨13, 2, 0, 37794, 16750, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_16750_37794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16750 ⟨37794, by decide⟩ :=
  accepted_of_selected 13 16750 ⟨37794, by decide⟩ ⟨13, 2, 0, 37794, 16750, 2657, 16384⟩
    (by decide) selected_cut_00955

theorem selected_cut_00956 : selected 8 ⟨37814, by decide⟩
    (prefixPartial 13 16751) = some ⟨13, 2, 0, 37814, 16751, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_16751_37814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 16751 ⟨37814, by decide⟩ :=
  accepted_of_selected 13 16751 ⟨37814, by decide⟩ ⟨13, 2, 0, 37814, 16751, 1281, 16384⟩
    (by decide) selected_cut_00956

theorem unmarked_context_12_4187_37815 : frontier 9 ⟨37815, by decide⟩
    (prefixCache 12 4187) (prefixPartial 12 4187) = false := by
  decide +kernel

theorem node_context_12_4187_37815 : EJMOriginalGlobalDAGData.nodes 9 ⟨37815, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨37731, by decide⟩,⟨37794, by decide⟩,⟨37814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4187_37815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4187 ⟨37815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4187
    ⟨37815, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨37731, by decide⟩,⟨37794, by decide⟩,⟨37814, by decide⟩]) unmarked_context_12_4187_37815 node_context_12_4187_37815
  intro a
  fin_cases a
  · exact context_13_16748_3444
  · exact context_13_16749_37731
  · exact context_13_16750_37794
  · exact context_13_16751_37814

theorem unmarked_context_11_1046_37816 : frontier 10 ⟨37816, by decide⟩
    (prefixCache 11 1046) (prefixPartial 11 1046) = false := by
  decide +kernel

theorem node_context_11_1046_37816 : EJMOriginalGlobalDAGData.nodes 10 ⟨37816, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨37598, by decide⟩,⟨37699, by decide⟩,⟨37815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1046_37816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1046 ⟨37816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1046
    ⟨37816, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨37598, by decide⟩,⟨37699, by decide⟩,⟨37815, by decide⟩]) unmarked_context_11_1046_37816 node_context_11_1046_37816
  intro a
  fin_cases a
  · exact context_12_4184_1738
  · exact context_12_4185_37598
  · exact context_12_4186_37699
  · exact context_12_4187_37815

theorem selected_cut_00957 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1047) = some ⟨11, 1, 0, 1736, 1047, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1047_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1047 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1047 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1047, 1, 262144⟩
    (by decide) selected_cut_00957

theorem unmarked_context_10_261_37817 : frontier 11 ⟨37817, by decide⟩
    (prefixCache 10 261) (prefixPartial 10 261) = false := by
  decide +kernel

theorem node_context_10_261_37817 : EJMOriginalGlobalDAGData.nodes 11 ⟨37817, by decide⟩ =
    .split (coordinate 10) (![⟨37310, by decide⟩,⟨37482, by decide⟩,⟨37816, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_261_37817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 261 ⟨37817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 261
    ⟨37817, by decide⟩ (by decide) (![⟨37310, by decide⟩,⟨37482, by decide⟩,⟨37816, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_261_37817 node_context_10_261_37817
  intro a
  fin_cases a
  · exact context_11_1044_37310
  · exact context_11_1045_37482
  · exact context_11_1046_37816
  · exact context_11_1047_1736

theorem selected_cut_00958 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4192) = some ⟨12, 1, 0, 1738, 4192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4192_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4192 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4192 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4192, 1, 65536⟩
    (by decide) selected_cut_00958

theorem selected_cut_00959 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4193) = some ⟨12, 1, 0, 1738, 4193, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4193_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4193 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4193 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4193, 1, 65536⟩
    (by decide) selected_cut_00959

theorem selected_cut_00960 : selected 9 ⟨37881, by decide⟩
    (prefixPartial 12 4194) = some ⟨12, 2, 0, 37881, 4194, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_4194_37881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4194 ⟨37881, by decide⟩ :=
  accepted_of_selected 12 4194 ⟨37881, by decide⟩ ⟨12, 2, 0, 37881, 4194, 2545, 65536⟩
    (by decide) selected_cut_00960

theorem selected_cut_00961 : selected 9 ⟨37926, by decide⟩
    (prefixPartial 12 4195) = some ⟨12, 2, 0, 37926, 4195, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_4195_37926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4195 ⟨37926, by decide⟩ :=
  accepted_of_selected 12 4195 ⟨37926, by decide⟩ ⟨12, 2, 0, 37926, 4195, 2117, 65536⟩
    (by decide) selected_cut_00961

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
