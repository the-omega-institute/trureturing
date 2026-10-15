/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover082
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_5699_227428 : frontier 10 ⟨227428, by decide⟩
    (prefixCache 11 5699) (prefixPartial 11 5699) = false := by
  decide +kernel

theorem node_context_11_5699_227428 : EJMOriginalGlobalDAGData.nodes 10 ⟨227428, by decide⟩ =
    .split (coordinate 11) (![⟨227042, by decide⟩,⟨227128, by decide⟩,⟨227286, by decide⟩,⟨227427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5699_227428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5699 ⟨227428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5699
    ⟨227428, by decide⟩ (by decide) (![⟨227042, by decide⟩,⟨227128, by decide⟩,⟨227286, by decide⟩,⟨227427, by decide⟩]) unmarked_context_11_5699_227428 node_context_11_5699_227428
  intro a
  fin_cases a
  · exact context_12_22796_227042
  · exact context_12_22797_227128
  · exact context_12_22798_227286
  · exact context_12_22799_227427

theorem unmarked_context_10_1424_227429 : frontier 11 ⟨227429, by decide⟩
    (prefixCache 10 1424) (prefixPartial 10 1424) = false := by
  decide +kernel

theorem node_context_10_1424_227429 : EJMOriginalGlobalDAGData.nodes 11 ⟨227429, by decide⟩ =
    .split (coordinate 10) (![⟨225641, by decide⟩,⟨226368, by decide⟩,⟨226924, by decide⟩,⟨227428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1424_227429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1424 ⟨227429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1424
    ⟨227429, by decide⟩ (by decide) (![⟨225641, by decide⟩,⟨226368, by decide⟩,⟨226924, by decide⟩,⟨227428, by decide⟩]) unmarked_context_10_1424_227429 node_context_10_1424_227429
  intro a
  fin_cases a
  · exact context_11_5696_225641
  · exact context_11_5697_226368
  · exact context_11_5698_226924
  · exact context_11_5699_227428

theorem selected_cut_07971 : selected 8 ⟨227446, by decide⟩
    (prefixPartial 13 91200) = some ⟨13, 2, 0, 227446, 91200, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_91200_227446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91200 ⟨227446, by decide⟩ :=
  accepted_of_selected 13 91200 ⟨227446, by decide⟩ ⟨13, 2, 0, 227446, 91200, 1773, 16384⟩
    (by decide) selected_cut_07971

theorem selected_cut_07972 : selected 8 ⟨227475, by decide⟩
    (prefixPartial 13 91201) = some ⟨13, 2, 0, 227475, 91201, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_91201_227475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91201 ⟨227475, by decide⟩ :=
  accepted_of_selected 13 91201 ⟨227475, by decide⟩ ⟨13, 2, 0, 227475, 91201, 2033, 16384⟩
    (by decide) selected_cut_07972

theorem selected_cut_07973 : selected 8 ⟨227495, by decide⟩
    (prefixPartial 13 91202) = some ⟨13, 2, 0, 227495, 91202, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_91202_227495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91202 ⟨227495, by decide⟩ :=
  accepted_of_selected 13 91202 ⟨227495, by decide⟩ ⟨13, 2, 0, 227495, 91202, 1277, 16384⟩
    (by decide) selected_cut_07973

theorem selected_cut_07974 : selected 8 ⟨227502, by decide⟩
    (prefixPartial 13 91203) = some ⟨13, 2, 0, 227502, 91203, 849, 16384⟩ := by
  decide +kernel

theorem context_13_91203_227502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91203 ⟨227502, by decide⟩ :=
  accepted_of_selected 13 91203 ⟨227502, by decide⟩ ⟨13, 2, 0, 227502, 91203, 849, 16384⟩
    (by decide) selected_cut_07974

theorem unmarked_context_12_22800_227503 : frontier 9 ⟨227503, by decide⟩
    (prefixCache 12 22800) (prefixPartial 12 22800) = false := by
  decide +kernel

theorem node_context_12_22800_227503 : EJMOriginalGlobalDAGData.nodes 9 ⟨227503, by decide⟩ =
    .split (coordinate 12) (![⟨227446, by decide⟩,⟨227475, by decide⟩,⟨227495, by decide⟩,⟨227502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22800_227503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22800 ⟨227503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22800
    ⟨227503, by decide⟩ (by decide) (![⟨227446, by decide⟩,⟨227475, by decide⟩,⟨227495, by decide⟩,⟨227502, by decide⟩]) unmarked_context_12_22800_227503 node_context_12_22800_227503
  intro a
  fin_cases a
  · exact context_13_91200_227446
  · exact context_13_91201_227475
  · exact context_13_91202_227495
  · exact context_13_91203_227502

theorem selected_cut_07975 : selected 8 ⟨227523, by decide⟩
    (prefixPartial 13 91204) = some ⟨13, 2, 0, 227523, 91204, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_91204_227523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91204 ⟨227523, by decide⟩ :=
  accepted_of_selected 13 91204 ⟨227523, by decide⟩ ⟨13, 2, 0, 227523, 91204, 1641, 16384⟩
    (by decide) selected_cut_07975

theorem selected_cut_07976 : selected 8 ⟨227546, by decide⟩
    (prefixPartial 13 91205) = some ⟨13, 2, 0, 227546, 91205, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_91205_227546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91205 ⟨227546, by decide⟩ :=
  accepted_of_selected 13 91205 ⟨227546, by decide⟩ ⟨13, 2, 0, 227546, 91205, 1593, 16384⟩
    (by decide) selected_cut_07976

theorem selected_cut_07977 : selected 8 ⟨227563, by decide⟩
    (prefixPartial 13 91206) = some ⟨13, 2, 0, 227563, 91206, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_91206_227563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91206 ⟨227563, by decide⟩ :=
  accepted_of_selected 13 91206 ⟨227563, by decide⟩ ⟨13, 2, 0, 227563, 91206, 1309, 16384⟩
    (by decide) selected_cut_07977

theorem selected_cut_07978 : selected 8 ⟨227569, by decide⟩
    (prefixPartial 13 91207) = some ⟨13, 2, 0, 227569, 91207, 825, 16384⟩ := by
  decide +kernel

theorem context_13_91207_227569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91207 ⟨227569, by decide⟩ :=
  accepted_of_selected 13 91207 ⟨227569, by decide⟩ ⟨13, 2, 0, 227569, 91207, 825, 16384⟩
    (by decide) selected_cut_07978

theorem unmarked_context_12_22801_227570 : frontier 9 ⟨227570, by decide⟩
    (prefixCache 12 22801) (prefixPartial 12 22801) = false := by
  decide +kernel

theorem node_context_12_22801_227570 : EJMOriginalGlobalDAGData.nodes 9 ⟨227570, by decide⟩ =
    .split (coordinate 12) (![⟨227523, by decide⟩,⟨227546, by decide⟩,⟨227563, by decide⟩,⟨227569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22801_227570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22801 ⟨227570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22801
    ⟨227570, by decide⟩ (by decide) (![⟨227523, by decide⟩,⟨227546, by decide⟩,⟨227563, by decide⟩,⟨227569, by decide⟩]) unmarked_context_12_22801_227570 node_context_12_22801_227570
  intro a
  fin_cases a
  · exact context_13_91204_227523
  · exact context_13_91205_227546
  · exact context_13_91206_227563
  · exact context_13_91207_227569

theorem selected_cut_07979 : selected 8 ⟨227606, by decide⟩
    (prefixPartial 13 91208) = some ⟨13, 2, 0, 227606, 91208, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_91208_227606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91208 ⟨227606, by decide⟩ :=
  accepted_of_selected 13 91208 ⟨227606, by decide⟩ ⟨13, 2, 0, 227606, 91208, 2437, 16384⟩
    (by decide) selected_cut_07979

theorem selected_cut_07980 : selected 8 ⟨227645, by decide⟩
    (prefixPartial 13 91209) = some ⟨13, 2, 0, 227645, 91209, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_91209_227645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91209 ⟨227645, by decide⟩ :=
  accepted_of_selected 13 91209 ⟨227645, by decide⟩ ⟨13, 2, 0, 227645, 91209, 2881, 16384⟩
    (by decide) selected_cut_07980

theorem selected_cut_07981 : selected 8 ⟨227666, by decide⟩
    (prefixPartial 13 91210) = some ⟨13, 2, 0, 227666, 91210, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_91210_227666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91210 ⟨227666, by decide⟩ :=
  accepted_of_selected 13 91210 ⟨227666, by decide⟩ ⟨13, 2, 0, 227666, 91210, 1845, 16384⟩
    (by decide) selected_cut_07981

theorem selected_cut_07982 : selected 8 ⟨227673, by decide⟩
    (prefixPartial 13 91211) = some ⟨13, 2, 0, 227673, 91211, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_91211_227673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91211 ⟨227673, by decide⟩ :=
  accepted_of_selected 13 91211 ⟨227673, by decide⟩ ⟨13, 2, 0, 227673, 91211, 1029, 16384⟩
    (by decide) selected_cut_07982

theorem unmarked_context_12_22802_227674 : frontier 9 ⟨227674, by decide⟩
    (prefixCache 12 22802) (prefixPartial 12 22802) = false := by
  decide +kernel

theorem node_context_12_22802_227674 : EJMOriginalGlobalDAGData.nodes 9 ⟨227674, by decide⟩ =
    .split (coordinate 12) (![⟨227606, by decide⟩,⟨227645, by decide⟩,⟨227666, by decide⟩,⟨227673, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22802_227674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22802 ⟨227674, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22802
    ⟨227674, by decide⟩ (by decide) (![⟨227606, by decide⟩,⟨227645, by decide⟩,⟨227666, by decide⟩,⟨227673, by decide⟩]) unmarked_context_12_22802_227674 node_context_12_22802_227674
  intro a
  fin_cases a
  · exact context_13_91208_227606
  · exact context_13_91209_227645
  · exact context_13_91210_227666
  · exact context_13_91211_227673

theorem selected_cut_07983 : selected 8 ⟨227708, by decide⟩
    (prefixPartial 13 91212) = some ⟨13, 2, 0, 227708, 91212, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_91212_227708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91212 ⟨227708, by decide⟩ :=
  accepted_of_selected 13 91212 ⟨227708, by decide⟩ ⟨13, 2, 0, 227708, 91212, 2337, 16384⟩
    (by decide) selected_cut_07983

theorem selected_cut_07984 : selected 8 ⟨227755, by decide⟩
    (prefixPartial 13 91213) = some ⟨13, 2, 0, 227755, 91213, 2941, 16384⟩ := by
  decide +kernel

theorem context_13_91213_227755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91213 ⟨227755, by decide⟩ :=
  accepted_of_selected 13 91213 ⟨227755, by decide⟩ ⟨13, 2, 0, 227755, 91213, 2941, 16384⟩
    (by decide) selected_cut_07984

theorem selected_cut_07985 : selected 8 ⟨227776, by decide⟩
    (prefixPartial 13 91214) = some ⟨13, 2, 0, 227776, 91214, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_91214_227776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91214 ⟨227776, by decide⟩ :=
  accepted_of_selected 13 91214 ⟨227776, by decide⟩ ⟨13, 2, 0, 227776, 91214, 1721, 16384⟩
    (by decide) selected_cut_07985

theorem selected_cut_07986 : selected 8 ⟨227781, by decide⟩
    (prefixPartial 13 91215) = some ⟨13, 2, 0, 227781, 91215, 969, 16384⟩ := by
  decide +kernel

theorem context_13_91215_227781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91215 ⟨227781, by decide⟩ :=
  accepted_of_selected 13 91215 ⟨227781, by decide⟩ ⟨13, 2, 0, 227781, 91215, 969, 16384⟩
    (by decide) selected_cut_07986

theorem unmarked_context_12_22803_227782 : frontier 9 ⟨227782, by decide⟩
    (prefixCache 12 22803) (prefixPartial 12 22803) = false := by
  decide +kernel

theorem node_context_12_22803_227782 : EJMOriginalGlobalDAGData.nodes 9 ⟨227782, by decide⟩ =
    .split (coordinate 12) (![⟨227708, by decide⟩,⟨227755, by decide⟩,⟨227776, by decide⟩,⟨227781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22803_227782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22803 ⟨227782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22803
    ⟨227782, by decide⟩ (by decide) (![⟨227708, by decide⟩,⟨227755, by decide⟩,⟨227776, by decide⟩,⟨227781, by decide⟩]) unmarked_context_12_22803_227782 node_context_12_22803_227782
  intro a
  fin_cases a
  · exact context_13_91212_227708
  · exact context_13_91213_227755
  · exact context_13_91214_227776
  · exact context_13_91215_227781

theorem unmarked_context_11_5700_227783 : frontier 10 ⟨227783, by decide⟩
    (prefixCache 11 5700) (prefixPartial 11 5700) = false := by
  decide +kernel

theorem node_context_11_5700_227783 : EJMOriginalGlobalDAGData.nodes 10 ⟨227783, by decide⟩ =
    .split (coordinate 11) (![⟨227503, by decide⟩,⟨227570, by decide⟩,⟨227674, by decide⟩,⟨227782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5700_227783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5700 ⟨227783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5700
    ⟨227783, by decide⟩ (by decide) (![⟨227503, by decide⟩,⟨227570, by decide⟩,⟨227674, by decide⟩,⟨227782, by decide⟩]) unmarked_context_11_5700_227783 node_context_11_5700_227783
  intro a
  fin_cases a
  · exact context_12_22800_227503
  · exact context_12_22801_227570
  · exact context_12_22802_227674
  · exact context_12_22803_227782

theorem selected_cut_07987 : selected 8 ⟨227802, by decide⟩
    (prefixPartial 13 91216) = some ⟨13, 2, 0, 227802, 91216, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_91216_227802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91216 ⟨227802, by decide⟩ :=
  accepted_of_selected 13 91216 ⟨227802, by decide⟩ ⟨13, 2, 0, 227802, 91216, 1341, 16384⟩
    (by decide) selected_cut_07987

theorem selected_cut_07988 : selected 8 ⟨227833, by decide⟩
    (prefixPartial 13 91217) = some ⟨13, 2, 0, 227833, 91217, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_91217_227833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91217 ⟨227833, by decide⟩ :=
  accepted_of_selected 13 91217 ⟨227833, by decide⟩ ⟨13, 2, 0, 227833, 91217, 1781, 16384⟩
    (by decide) selected_cut_07988

theorem selected_cut_07989 : selected 8 ⟨227851, by decide⟩
    (prefixPartial 13 91218) = some ⟨13, 2, 0, 227851, 91218, 997, 16384⟩ := by
  decide +kernel

theorem context_13_91218_227851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91218 ⟨227851, by decide⟩ :=
  accepted_of_selected 13 91218 ⟨227851, by decide⟩ ⟨13, 2, 0, 227851, 91218, 997, 16384⟩
    (by decide) selected_cut_07989

theorem selected_cut_07990 : selected 8 ⟨227857, by decide⟩
    (prefixPartial 13 91219) = some ⟨13, 2, 0, 227857, 91219, 837, 16384⟩ := by
  decide +kernel

theorem context_13_91219_227857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91219 ⟨227857, by decide⟩ :=
  accepted_of_selected 13 91219 ⟨227857, by decide⟩ ⟨13, 2, 0, 227857, 91219, 837, 16384⟩
    (by decide) selected_cut_07990

theorem unmarked_context_12_22804_227858 : frontier 9 ⟨227858, by decide⟩
    (prefixCache 12 22804) (prefixPartial 12 22804) = false := by
  decide +kernel

theorem node_context_12_22804_227858 : EJMOriginalGlobalDAGData.nodes 9 ⟨227858, by decide⟩ =
    .split (coordinate 12) (![⟨227802, by decide⟩,⟨227833, by decide⟩,⟨227851, by decide⟩,⟨227857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22804_227858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22804 ⟨227858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22804
    ⟨227858, by decide⟩ (by decide) (![⟨227802, by decide⟩,⟨227833, by decide⟩,⟨227851, by decide⟩,⟨227857, by decide⟩]) unmarked_context_12_22804_227858 node_context_12_22804_227858
  intro a
  fin_cases a
  · exact context_13_91216_227802
  · exact context_13_91217_227833
  · exact context_13_91218_227851
  · exact context_13_91219_227857

theorem selected_cut_07991 : selected 8 ⟨227886, by decide⟩
    (prefixPartial 13 91220) = some ⟨13, 2, 0, 227886, 91220, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_91220_227886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91220 ⟨227886, by decide⟩ :=
  accepted_of_selected 13 91220 ⟨227886, by decide⟩ ⟨13, 2, 0, 227886, 91220, 2029, 16384⟩
    (by decide) selected_cut_07991

theorem selected_cut_07992 : selected 8 ⟨227917, by decide⟩
    (prefixPartial 13 91221) = some ⟨13, 2, 0, 227917, 91221, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_91221_227917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91221 ⟨227917, by decide⟩ :=
  accepted_of_selected 13 91221 ⟨227917, by decide⟩ ⟨13, 2, 0, 227917, 91221, 2629, 16384⟩
    (by decide) selected_cut_07992

theorem selected_cut_07993 : selected 8 ⟨227937, by decide⟩
    (prefixPartial 13 91222) = some ⟨13, 2, 0, 227937, 91222, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_91222_227937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91222 ⟨227937, by decide⟩ :=
  accepted_of_selected 13 91222 ⟨227937, by decide⟩ ⟨13, 2, 0, 227937, 91222, 1529, 16384⟩
    (by decide) selected_cut_07993

theorem selected_cut_07994 : selected 8 ⟨227943, by decide⟩
    (prefixPartial 13 91223) = some ⟨13, 2, 0, 227943, 91223, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_91223_227943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91223 ⟨227943, by decide⟩ :=
  accepted_of_selected 13 91223 ⟨227943, by decide⟩ ⟨13, 2, 0, 227943, 91223, 1105, 16384⟩
    (by decide) selected_cut_07994

theorem unmarked_context_12_22805_227944 : frontier 9 ⟨227944, by decide⟩
    (prefixCache 12 22805) (prefixPartial 12 22805) = false := by
  decide +kernel

theorem node_context_12_22805_227944 : EJMOriginalGlobalDAGData.nodes 9 ⟨227944, by decide⟩ =
    .split (coordinate 12) (![⟨227886, by decide⟩,⟨227917, by decide⟩,⟨227937, by decide⟩,⟨227943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22805_227944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22805 ⟨227944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22805
    ⟨227944, by decide⟩ (by decide) (![⟨227886, by decide⟩,⟨227917, by decide⟩,⟨227937, by decide⟩,⟨227943, by decide⟩]) unmarked_context_12_22805_227944 node_context_12_22805_227944
  intro a
  fin_cases a
  · exact context_13_91220_227886
  · exact context_13_91221_227917
  · exact context_13_91222_227937
  · exact context_13_91223_227943

theorem selected_cut_07995 : selected 8 ⟨227968, by decide⟩
    (prefixPartial 13 91224) = some ⟨13, 2, 0, 227968, 91224, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_91224_227968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91224 ⟨227968, by decide⟩ :=
  accepted_of_selected 13 91224 ⟨227968, by decide⟩ ⟨13, 2, 0, 227968, 91224, 1837, 16384⟩
    (by decide) selected_cut_07995

theorem selected_cut_07996 : selected 8 ⟨227999, by decide⟩
    (prefixPartial 13 91225) = some ⟨13, 2, 0, 227999, 91225, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_91225_227999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91225 ⟨227999, by decide⟩ :=
  accepted_of_selected 13 91225 ⟨227999, by decide⟩ ⟨13, 2, 0, 227999, 91225, 2301, 16384⟩
    (by decide) selected_cut_07996

theorem selected_cut_07997 : selected 8 ⟨228016, by decide⟩
    (prefixPartial 13 91226) = some ⟨13, 2, 0, 228016, 91226, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_91226_228016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91226 ⟨228016, by decide⟩ :=
  accepted_of_selected 13 91226 ⟨228016, by decide⟩ ⟨13, 2, 0, 228016, 91226, 1425, 16384⟩
    (by decide) selected_cut_07997

theorem selected_cut_07998 : selected 8 ⟨228024, by decide⟩
    (prefixPartial 13 91227) = some ⟨13, 2, 0, 228024, 91227, 969, 16384⟩ := by
  decide +kernel

theorem context_13_91227_228024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91227 ⟨228024, by decide⟩ :=
  accepted_of_selected 13 91227 ⟨228024, by decide⟩ ⟨13, 2, 0, 228024, 91227, 969, 16384⟩
    (by decide) selected_cut_07998

theorem unmarked_context_12_22806_228025 : frontier 9 ⟨228025, by decide⟩
    (prefixCache 12 22806) (prefixPartial 12 22806) = false := by
  decide +kernel

theorem node_context_12_22806_228025 : EJMOriginalGlobalDAGData.nodes 9 ⟨228025, by decide⟩ =
    .split (coordinate 12) (![⟨227968, by decide⟩,⟨227999, by decide⟩,⟨228016, by decide⟩,⟨228024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22806_228025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22806 ⟨228025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22806
    ⟨228025, by decide⟩ (by decide) (![⟨227968, by decide⟩,⟨227999, by decide⟩,⟨228016, by decide⟩,⟨228024, by decide⟩]) unmarked_context_12_22806_228025 node_context_12_22806_228025
  intro a
  fin_cases a
  · exact context_13_91224_227968
  · exact context_13_91225_227999
  · exact context_13_91226_228016
  · exact context_13_91227_228024

theorem selected_cut_07999 : selected 8 ⟨228047, by decide⟩
    (prefixPartial 13 91228) = some ⟨13, 2, 0, 228047, 91228, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_91228_228047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91228 ⟨228047, by decide⟩ :=
  accepted_of_selected 13 91228 ⟨228047, by decide⟩ ⟨13, 2, 0, 228047, 91228, 1709, 16384⟩
    (by decide) selected_cut_07999

theorem selected_cut_08000 : selected 8 ⟨228078, by decide⟩
    (prefixPartial 13 91229) = some ⟨13, 2, 0, 228078, 91229, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_91229_228078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91229 ⟨228078, by decide⟩ :=
  accepted_of_selected 13 91229 ⟨228078, by decide⟩ ⟨13, 2, 0, 228078, 91229, 2341, 16384⟩
    (by decide) selected_cut_08000

theorem selected_cut_08001 : selected 8 ⟨228098, by decide⟩
    (prefixPartial 13 91230) = some ⟨13, 2, 0, 228098, 91230, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_91230_228098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91230 ⟨228098, by decide⟩ :=
  accepted_of_selected 13 91230 ⟨228098, by decide⟩ ⟨13, 2, 0, 228098, 91230, 1245, 16384⟩
    (by decide) selected_cut_08001

theorem selected_cut_08002 : selected 8 ⟨228107, by decide⟩
    (prefixPartial 13 91231) = some ⟨13, 2, 0, 228107, 91231, 901, 16384⟩ := by
  decide +kernel

theorem context_13_91231_228107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91231 ⟨228107, by decide⟩ :=
  accepted_of_selected 13 91231 ⟨228107, by decide⟩ ⟨13, 2, 0, 228107, 91231, 901, 16384⟩
    (by decide) selected_cut_08002

theorem unmarked_context_12_22807_228108 : frontier 9 ⟨228108, by decide⟩
    (prefixCache 12 22807) (prefixPartial 12 22807) = false := by
  decide +kernel

theorem node_context_12_22807_228108 : EJMOriginalGlobalDAGData.nodes 9 ⟨228108, by decide⟩ =
    .split (coordinate 12) (![⟨228047, by decide⟩,⟨228078, by decide⟩,⟨228098, by decide⟩,⟨228107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22807_228108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22807 ⟨228108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22807
    ⟨228108, by decide⟩ (by decide) (![⟨228047, by decide⟩,⟨228078, by decide⟩,⟨228098, by decide⟩,⟨228107, by decide⟩]) unmarked_context_12_22807_228108 node_context_12_22807_228108
  intro a
  fin_cases a
  · exact context_13_91228_228047
  · exact context_13_91229_228078
  · exact context_13_91230_228098
  · exact context_13_91231_228107

theorem unmarked_context_11_5701_228109 : frontier 10 ⟨228109, by decide⟩
    (prefixCache 11 5701) (prefixPartial 11 5701) = false := by
  decide +kernel

theorem node_context_11_5701_228109 : EJMOriginalGlobalDAGData.nodes 10 ⟨228109, by decide⟩ =
    .split (coordinate 11) (![⟨227858, by decide⟩,⟨227944, by decide⟩,⟨228025, by decide⟩,⟨228108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5701_228109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5701 ⟨228109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5701
    ⟨228109, by decide⟩ (by decide) (![⟨227858, by decide⟩,⟨227944, by decide⟩,⟨228025, by decide⟩,⟨228108, by decide⟩]) unmarked_context_11_5701_228109 node_context_11_5701_228109
  intro a
  fin_cases a
  · exact context_12_22804_227858
  · exact context_12_22805_227944
  · exact context_12_22806_228025
  · exact context_12_22807_228108

theorem selected_cut_08003 : selected 8 ⟨228125, by decide⟩
    (prefixPartial 13 91232) = some ⟨13, 2, 0, 228125, 91232, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_91232_228125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91232 ⟨228125, by decide⟩ :=
  accepted_of_selected 13 91232 ⟨228125, by decide⟩ ⟨13, 2, 0, 228125, 91232, 1373, 16384⟩
    (by decide) selected_cut_08003

theorem selected_cut_08004 : selected 8 ⟨228152, by decide⟩
    (prefixPartial 13 91233) = some ⟨13, 2, 0, 228152, 91233, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_91233_228152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91233 ⟨228152, by decide⟩ :=
  accepted_of_selected 13 91233 ⟨228152, by decide⟩ ⟨13, 2, 0, 228152, 91233, 2181, 16384⟩
    (by decide) selected_cut_08004

theorem selected_cut_08005 : selected 8 ⟨228171, by decide⟩
    (prefixPartial 13 91234) = some ⟨13, 2, 0, 228171, 91234, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_91234_228171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91234 ⟨228171, by decide⟩ :=
  accepted_of_selected 13 91234 ⟨228171, by decide⟩ ⟨13, 2, 0, 228171, 91234, 1473, 16384⟩
    (by decide) selected_cut_08005

theorem selected_cut_08006 : selected 8 ⟨228177, by decide⟩
    (prefixPartial 13 91235) = some ⟨13, 2, 0, 228177, 91235, 797, 16384⟩ := by
  decide +kernel

theorem context_13_91235_228177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91235 ⟨228177, by decide⟩ :=
  accepted_of_selected 13 91235 ⟨228177, by decide⟩ ⟨13, 2, 0, 228177, 91235, 797, 16384⟩
    (by decide) selected_cut_08006

theorem unmarked_context_12_22808_228178 : frontier 9 ⟨228178, by decide⟩
    (prefixCache 12 22808) (prefixPartial 12 22808) = false := by
  decide +kernel

theorem node_context_12_22808_228178 : EJMOriginalGlobalDAGData.nodes 9 ⟨228178, by decide⟩ =
    .split (coordinate 12) (![⟨228125, by decide⟩,⟨228152, by decide⟩,⟨228171, by decide⟩,⟨228177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22808_228178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22808 ⟨228178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22808
    ⟨228178, by decide⟩ (by decide) (![⟨228125, by decide⟩,⟨228152, by decide⟩,⟨228171, by decide⟩,⟨228177, by decide⟩]) unmarked_context_12_22808_228178 node_context_12_22808_228178
  intro a
  fin_cases a
  · exact context_13_91232_228125
  · exact context_13_91233_228152
  · exact context_13_91234_228171
  · exact context_13_91235_228177

theorem selected_cut_08007 : selected 8 ⟨228196, by decide⟩
    (prefixPartial 13 91236) = some ⟨13, 2, 0, 228196, 91236, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_91236_228196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91236 ⟨228196, by decide⟩ :=
  accepted_of_selected 13 91236 ⟨228196, by decide⟩ ⟨13, 2, 0, 228196, 91236, 1217, 16384⟩
    (by decide) selected_cut_08007

theorem selected_cut_08008 : selected 8 ⟨228220, by decide⟩
    (prefixPartial 13 91237) = some ⟨13, 2, 0, 228220, 91237, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_91237_228220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91237 ⟨228220, by decide⟩ :=
  accepted_of_selected 13 91237 ⟨228220, by decide⟩ ⟨13, 2, 0, 228220, 91237, 1513, 16384⟩
    (by decide) selected_cut_08008

theorem selected_cut_08009 : selected 8 ⟨228239, by decide⟩
    (prefixPartial 13 91238) = some ⟨13, 2, 0, 228239, 91238, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_91238_228239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91238 ⟨228239, by decide⟩ :=
  accepted_of_selected 13 91238 ⟨228239, by decide⟩ ⟨13, 2, 0, 228239, 91238, 1385, 16384⟩
    (by decide) selected_cut_08009

theorem selected_cut_08010 : selected 8 ⟨228245, by decide⟩
    (prefixPartial 13 91239) = some ⟨13, 2, 0, 228245, 91239, 757, 16384⟩ := by
  decide +kernel

theorem context_13_91239_228245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91239 ⟨228245, by decide⟩ :=
  accepted_of_selected 13 91239 ⟨228245, by decide⟩ ⟨13, 2, 0, 228245, 91239, 757, 16384⟩
    (by decide) selected_cut_08010

theorem unmarked_context_12_22809_228246 : frontier 9 ⟨228246, by decide⟩
    (prefixCache 12 22809) (prefixPartial 12 22809) = false := by
  decide +kernel

theorem node_context_12_22809_228246 : EJMOriginalGlobalDAGData.nodes 9 ⟨228246, by decide⟩ =
    .split (coordinate 12) (![⟨228196, by decide⟩,⟨228220, by decide⟩,⟨228239, by decide⟩,⟨228245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22809_228246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22809 ⟨228246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22809
    ⟨228246, by decide⟩ (by decide) (![⟨228196, by decide⟩,⟨228220, by decide⟩,⟨228239, by decide⟩,⟨228245, by decide⟩]) unmarked_context_12_22809_228246 node_context_12_22809_228246
  intro a
  fin_cases a
  · exact context_13_91236_228196
  · exact context_13_91237_228220
  · exact context_13_91238_228239
  · exact context_13_91239_228245

theorem selected_cut_08011 : selected 8 ⟨228272, by decide⟩
    (prefixPartial 13 91240) = some ⟨13, 2, 0, 228272, 91240, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_91240_228272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91240 ⟨228272, by decide⟩ :=
  accepted_of_selected 13 91240 ⟨228272, by decide⟩ ⟨13, 2, 0, 228272, 91240, 1937, 16384⟩
    (by decide) selected_cut_08011

theorem selected_cut_08012 : selected 8 ⟨228299, by decide⟩
    (prefixPartial 13 91241) = some ⟨13, 2, 0, 228299, 91241, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_91241_228299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91241 ⟨228299, by decide⟩ :=
  accepted_of_selected 13 91241 ⟨228299, by decide⟩ ⟨13, 2, 0, 228299, 91241, 2621, 16384⟩
    (by decide) selected_cut_08012

theorem selected_cut_08013 : selected 8 ⟨228329, by decide⟩
    (prefixPartial 13 91242) = some ⟨13, 2, 0, 228329, 91242, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_91242_228329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91242 ⟨228329, by decide⟩ :=
  accepted_of_selected 13 91242 ⟨228329, by decide⟩ ⟨13, 2, 0, 228329, 91242, 1985, 16384⟩
    (by decide) selected_cut_08013

theorem selected_cut_08014 : selected 8 ⟨228338, by decide⟩
    (prefixPartial 13 91243) = some ⟨13, 2, 0, 228338, 91243, 917, 16384⟩ := by
  decide +kernel

theorem context_13_91243_228338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91243 ⟨228338, by decide⟩ :=
  accepted_of_selected 13 91243 ⟨228338, by decide⟩ ⟨13, 2, 0, 228338, 91243, 917, 16384⟩
    (by decide) selected_cut_08014

theorem unmarked_context_12_22810_228339 : frontier 9 ⟨228339, by decide⟩
    (prefixCache 12 22810) (prefixPartial 12 22810) = false := by
  decide +kernel

theorem node_context_12_22810_228339 : EJMOriginalGlobalDAGData.nodes 9 ⟨228339, by decide⟩ =
    .split (coordinate 12) (![⟨228272, by decide⟩,⟨228299, by decide⟩,⟨228329, by decide⟩,⟨228338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22810_228339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22810 ⟨228339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22810
    ⟨228339, by decide⟩ (by decide) (![⟨228272, by decide⟩,⟨228299, by decide⟩,⟨228329, by decide⟩,⟨228338, by decide⟩]) unmarked_context_12_22810_228339 node_context_12_22810_228339
  intro a
  fin_cases a
  · exact context_13_91240_228272
  · exact context_13_91241_228299
  · exact context_13_91242_228329
  · exact context_13_91243_228338

theorem selected_cut_08015 : selected 8 ⟨228362, by decide⟩
    (prefixPartial 13 91244) = some ⟨13, 2, 0, 228362, 91244, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_91244_228362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91244 ⟨228362, by decide⟩ :=
  accepted_of_selected 13 91244 ⟨228362, by decide⟩ ⟨13, 2, 0, 228362, 91244, 1901, 16384⟩
    (by decide) selected_cut_08015

theorem selected_cut_08016 : selected 8 ⟨228402, by decide⟩
    (prefixPartial 13 91245) = some ⟨13, 2, 0, 228402, 91245, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_91245_228402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91245 ⟨228402, by decide⟩ :=
  accepted_of_selected 13 91245 ⟨228402, by decide⟩ ⟨13, 2, 0, 228402, 91245, 2817, 16384⟩
    (by decide) selected_cut_08016

theorem selected_cut_08017 : selected 8 ⟨228426, by decide⟩
    (prefixPartial 13 91246) = some ⟨13, 2, 0, 228426, 91246, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_91246_228426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91246 ⟨228426, by decide⟩ :=
  accepted_of_selected 13 91246 ⟨228426, by decide⟩ ⟨13, 2, 0, 228426, 91246, 1865, 16384⟩
    (by decide) selected_cut_08017

theorem selected_cut_08018 : selected 8 ⟨228433, by decide⟩
    (prefixPartial 13 91247) = some ⟨13, 2, 0, 228433, 91247, 893, 16384⟩ := by
  decide +kernel

theorem context_13_91247_228433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91247 ⟨228433, by decide⟩ :=
  accepted_of_selected 13 91247 ⟨228433, by decide⟩ ⟨13, 2, 0, 228433, 91247, 893, 16384⟩
    (by decide) selected_cut_08018

theorem unmarked_context_12_22811_228434 : frontier 9 ⟨228434, by decide⟩
    (prefixCache 12 22811) (prefixPartial 12 22811) = false := by
  decide +kernel

theorem node_context_12_22811_228434 : EJMOriginalGlobalDAGData.nodes 9 ⟨228434, by decide⟩ =
    .split (coordinate 12) (![⟨228362, by decide⟩,⟨228402, by decide⟩,⟨228426, by decide⟩,⟨228433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22811_228434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22811 ⟨228434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22811
    ⟨228434, by decide⟩ (by decide) (![⟨228362, by decide⟩,⟨228402, by decide⟩,⟨228426, by decide⟩,⟨228433, by decide⟩]) unmarked_context_12_22811_228434 node_context_12_22811_228434
  intro a
  fin_cases a
  · exact context_13_91244_228362
  · exact context_13_91245_228402
  · exact context_13_91246_228426
  · exact context_13_91247_228433

theorem unmarked_context_11_5702_228435 : frontier 10 ⟨228435, by decide⟩
    (prefixCache 11 5702) (prefixPartial 11 5702) = false := by
  decide +kernel

theorem node_context_11_5702_228435 : EJMOriginalGlobalDAGData.nodes 10 ⟨228435, by decide⟩ =
    .split (coordinate 11) (![⟨228178, by decide⟩,⟨228246, by decide⟩,⟨228339, by decide⟩,⟨228434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5702_228435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5702 ⟨228435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5702
    ⟨228435, by decide⟩ (by decide) (![⟨228178, by decide⟩,⟨228246, by decide⟩,⟨228339, by decide⟩,⟨228434, by decide⟩]) unmarked_context_11_5702_228435 node_context_11_5702_228435
  intro a
  fin_cases a
  · exact context_12_22808_228178
  · exact context_12_22809_228246
  · exact context_12_22810_228339
  · exact context_12_22811_228434

theorem selected_cut_08019 : selected 8 ⟨228455, by decide⟩
    (prefixPartial 13 91248) = some ⟨13, 2, 0, 228455, 91248, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_91248_228455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91248 ⟨228455, by decide⟩ :=
  accepted_of_selected 13 91248 ⟨228455, by decide⟩ ⟨13, 2, 0, 228455, 91248, 1373, 16384⟩
    (by decide) selected_cut_08019

theorem selected_cut_08020 : selected 8 ⟨228483, by decide⟩
    (prefixPartial 13 91249) = some ⟨13, 2, 0, 228483, 91249, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_91249_228483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91249 ⟨228483, by decide⟩ :=
  accepted_of_selected 13 91249 ⟨228483, by decide⟩ ⟨13, 2, 0, 228483, 91249, 2181, 16384⟩
    (by decide) selected_cut_08020

theorem selected_cut_08021 : selected 8 ⟨228500, by decide⟩
    (prefixPartial 13 91250) = some ⟨13, 2, 0, 228500, 91250, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_91250_228500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91250 ⟨228500, by decide⟩ :=
  accepted_of_selected 13 91250 ⟨228500, by decide⟩ ⟨13, 2, 0, 228500, 91250, 1257, 16384⟩
    (by decide) selected_cut_08021

theorem selected_cut_08022 : selected 8 ⟨228508, by decide⟩
    (prefixPartial 13 91251) = some ⟨13, 2, 0, 228508, 91251, 857, 16384⟩ := by
  decide +kernel

theorem context_13_91251_228508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91251 ⟨228508, by decide⟩ :=
  accepted_of_selected 13 91251 ⟨228508, by decide⟩ ⟨13, 2, 0, 228508, 91251, 857, 16384⟩
    (by decide) selected_cut_08022

theorem unmarked_context_12_22812_228509 : frontier 9 ⟨228509, by decide⟩
    (prefixCache 12 22812) (prefixPartial 12 22812) = false := by
  decide +kernel

theorem node_context_12_22812_228509 : EJMOriginalGlobalDAGData.nodes 9 ⟨228509, by decide⟩ =
    .split (coordinate 12) (![⟨228455, by decide⟩,⟨228483, by decide⟩,⟨228500, by decide⟩,⟨228508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22812_228509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22812 ⟨228509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22812
    ⟨228509, by decide⟩ (by decide) (![⟨228455, by decide⟩,⟨228483, by decide⟩,⟨228500, by decide⟩,⟨228508, by decide⟩]) unmarked_context_12_22812_228509 node_context_12_22812_228509
  intro a
  fin_cases a
  · exact context_13_91248_228455
  · exact context_13_91249_228483
  · exact context_13_91250_228500
  · exact context_13_91251_228508

theorem selected_cut_08023 : selected 8 ⟨228533, by decide⟩
    (prefixPartial 13 91252) = some ⟨13, 2, 0, 228533, 91252, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_91252_228533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91252 ⟨228533, by decide⟩ :=
  accepted_of_selected 13 91252 ⟨228533, by decide⟩ ⟨13, 2, 0, 228533, 91252, 1305, 16384⟩
    (by decide) selected_cut_08023

theorem selected_cut_08024 : selected 8 ⟨228559, by decide⟩
    (prefixPartial 13 91253) = some ⟨13, 2, 0, 228559, 91253, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_91253_228559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91253 ⟨228559, by decide⟩ :=
  accepted_of_selected 13 91253 ⟨228559, by decide⟩ ⟨13, 2, 0, 228559, 91253, 1601, 16384⟩
    (by decide) selected_cut_08024

theorem selected_cut_08025 : selected 8 ⟨228575, by decide⟩
    (prefixPartial 13 91254) = some ⟨13, 2, 0, 228575, 91254, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_91254_228575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91254 ⟨228575, by decide⟩ :=
  accepted_of_selected 13 91254 ⟨228575, by decide⟩ ⟨13, 2, 0, 228575, 91254, 1153, 16384⟩
    (by decide) selected_cut_08025

theorem selected_cut_08026 : selected 8 ⟨228580, by decide⟩
    (prefixPartial 13 91255) = some ⟨13, 2, 0, 228580, 91255, 713, 16384⟩ := by
  decide +kernel

theorem context_13_91255_228580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91255 ⟨228580, by decide⟩ :=
  accepted_of_selected 13 91255 ⟨228580, by decide⟩ ⟨13, 2, 0, 228580, 91255, 713, 16384⟩
    (by decide) selected_cut_08026

theorem unmarked_context_12_22813_228581 : frontier 9 ⟨228581, by decide⟩
    (prefixCache 12 22813) (prefixPartial 12 22813) = false := by
  decide +kernel

theorem node_context_12_22813_228581 : EJMOriginalGlobalDAGData.nodes 9 ⟨228581, by decide⟩ =
    .split (coordinate 12) (![⟨228533, by decide⟩,⟨228559, by decide⟩,⟨228575, by decide⟩,⟨228580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22813_228581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22813 ⟨228581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22813
    ⟨228581, by decide⟩ (by decide) (![⟨228533, by decide⟩,⟨228559, by decide⟩,⟨228575, by decide⟩,⟨228580, by decide⟩]) unmarked_context_12_22813_228581 node_context_12_22813_228581
  intro a
  fin_cases a
  · exact context_13_91252_228533
  · exact context_13_91253_228559
  · exact context_13_91254_228575
  · exact context_13_91255_228580

theorem selected_cut_08027 : selected 8 ⟨228612, by decide⟩
    (prefixPartial 13 91256) = some ⟨13, 2, 0, 228612, 91256, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_91256_228612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91256 ⟨228612, by decide⟩ :=
  accepted_of_selected 13 91256 ⟨228612, by decide⟩ ⟨13, 2, 0, 228612, 91256, 1909, 16384⟩
    (by decide) selected_cut_08027

theorem selected_cut_08028 : selected 8 ⟨228651, by decide⟩
    (prefixPartial 13 91257) = some ⟨13, 2, 0, 228651, 91257, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_91257_228651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91257 ⟨228651, by decide⟩ :=
  accepted_of_selected 13 91257 ⟨228651, by decide⟩ ⟨13, 2, 0, 228651, 91257, 2737, 16384⟩
    (by decide) selected_cut_08028

theorem selected_cut_08029 : selected 8 ⟨228672, by decide⟩
    (prefixPartial 13 91258) = some ⟨13, 2, 0, 228672, 91258, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_91258_228672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91258 ⟨228672, by decide⟩ :=
  accepted_of_selected 13 91258 ⟨228672, by decide⟩ ⟨13, 2, 0, 228672, 91258, 1761, 16384⟩
    (by decide) selected_cut_08029

theorem selected_cut_08030 : selected 8 ⟨228679, by decide⟩
    (prefixPartial 13 91259) = some ⟨13, 2, 0, 228679, 91259, 885, 16384⟩ := by
  decide +kernel

theorem context_13_91259_228679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91259 ⟨228679, by decide⟩ :=
  accepted_of_selected 13 91259 ⟨228679, by decide⟩ ⟨13, 2, 0, 228679, 91259, 885, 16384⟩
    (by decide) selected_cut_08030

theorem unmarked_context_12_22814_228680 : frontier 9 ⟨228680, by decide⟩
    (prefixCache 12 22814) (prefixPartial 12 22814) = false := by
  decide +kernel

theorem node_context_12_22814_228680 : EJMOriginalGlobalDAGData.nodes 9 ⟨228680, by decide⟩ =
    .split (coordinate 12) (![⟨228612, by decide⟩,⟨228651, by decide⟩,⟨228672, by decide⟩,⟨228679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22814_228680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22814 ⟨228680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22814
    ⟨228680, by decide⟩ (by decide) (![⟨228612, by decide⟩,⟨228651, by decide⟩,⟨228672, by decide⟩,⟨228679, by decide⟩]) unmarked_context_12_22814_228680 node_context_12_22814_228680
  intro a
  fin_cases a
  · exact context_13_91256_228612
  · exact context_13_91257_228651
  · exact context_13_91258_228672
  · exact context_13_91259_228679

theorem selected_cut_08031 : selected 8 ⟨228711, by decide⟩
    (prefixPartial 13 91260) = some ⟨13, 2, 0, 228711, 91260, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_91260_228711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91260 ⟨228711, by decide⟩ :=
  accepted_of_selected 13 91260 ⟨228711, by decide⟩ ⟨13, 2, 0, 228711, 91260, 1817, 16384⟩
    (by decide) selected_cut_08031

theorem selected_cut_08032 : selected 8 ⟨228752, by decide⟩
    (prefixPartial 13 91261) = some ⟨13, 2, 0, 228752, 91261, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_91261_228752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91261 ⟨228752, by decide⟩ :=
  accepted_of_selected 13 91261 ⟨228752, by decide⟩ ⟨13, 2, 0, 228752, 91261, 2769, 16384⟩
    (by decide) selected_cut_08032

theorem selected_cut_08033 : selected 8 ⟨228772, by decide⟩
    (prefixPartial 13 91262) = some ⟨13, 2, 0, 228772, 91262, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_91262_228772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91262 ⟨228772, by decide⟩ :=
  accepted_of_selected 13 91262 ⟨228772, by decide⟩ ⟨13, 2, 0, 228772, 91262, 1429, 16384⟩
    (by decide) selected_cut_08033

theorem selected_cut_08034 : selected 8 ⟨228782, by decide⟩
    (prefixPartial 13 91263) = some ⟨13, 2, 0, 228782, 91263, 849, 16384⟩ := by
  decide +kernel

theorem context_13_91263_228782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91263 ⟨228782, by decide⟩ :=
  accepted_of_selected 13 91263 ⟨228782, by decide⟩ ⟨13, 2, 0, 228782, 91263, 849, 16384⟩
    (by decide) selected_cut_08034

theorem unmarked_context_12_22815_228783 : frontier 9 ⟨228783, by decide⟩
    (prefixCache 12 22815) (prefixPartial 12 22815) = false := by
  decide +kernel

theorem node_context_12_22815_228783 : EJMOriginalGlobalDAGData.nodes 9 ⟨228783, by decide⟩ =
    .split (coordinate 12) (![⟨228711, by decide⟩,⟨228752, by decide⟩,⟨228772, by decide⟩,⟨228782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22815_228783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22815 ⟨228783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22815
    ⟨228783, by decide⟩ (by decide) (![⟨228711, by decide⟩,⟨228752, by decide⟩,⟨228772, by decide⟩,⟨228782, by decide⟩]) unmarked_context_12_22815_228783 node_context_12_22815_228783
  intro a
  fin_cases a
  · exact context_13_91260_228711
  · exact context_13_91261_228752
  · exact context_13_91262_228772
  · exact context_13_91263_228782

theorem unmarked_context_11_5703_228784 : frontier 10 ⟨228784, by decide⟩
    (prefixCache 11 5703) (prefixPartial 11 5703) = false := by
  decide +kernel

theorem node_context_11_5703_228784 : EJMOriginalGlobalDAGData.nodes 10 ⟨228784, by decide⟩ =
    .split (coordinate 11) (![⟨228509, by decide⟩,⟨228581, by decide⟩,⟨228680, by decide⟩,⟨228783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5703_228784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5703 ⟨228784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5703
    ⟨228784, by decide⟩ (by decide) (![⟨228509, by decide⟩,⟨228581, by decide⟩,⟨228680, by decide⟩,⟨228783, by decide⟩]) unmarked_context_11_5703_228784 node_context_11_5703_228784
  intro a
  fin_cases a
  · exact context_12_22812_228509
  · exact context_12_22813_228581
  · exact context_12_22814_228680
  · exact context_12_22815_228783

theorem unmarked_context_10_1425_228785 : frontier 11 ⟨228785, by decide⟩
    (prefixCache 10 1425) (prefixPartial 10 1425) = false := by
  decide +kernel

theorem node_context_10_1425_228785 : EJMOriginalGlobalDAGData.nodes 11 ⟨228785, by decide⟩ =
    .split (coordinate 10) (![⟨227783, by decide⟩,⟨228109, by decide⟩,⟨228435, by decide⟩,⟨228784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1425_228785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1425 ⟨228785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1425
    ⟨228785, by decide⟩ (by decide) (![⟨227783, by decide⟩,⟨228109, by decide⟩,⟨228435, by decide⟩,⟨228784, by decide⟩]) unmarked_context_10_1425_228785 node_context_10_1425_228785
  intro a
  fin_cases a
  · exact context_11_5700_227783
  · exact context_11_5701_228109
  · exact context_11_5702_228435
  · exact context_11_5703_228784

theorem selected_cut_08035 : selected 8 ⟨228801, by decide⟩
    (prefixPartial 13 91264) = some ⟨13, 2, 0, 228801, 91264, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_91264_228801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91264 ⟨228801, by decide⟩ :=
  accepted_of_selected 13 91264 ⟨228801, by decide⟩ ⟨13, 2, 0, 228801, 91264, 1461, 16384⟩
    (by decide) selected_cut_08035

theorem selected_cut_08036 : selected 8 ⟨228823, by decide⟩
    (prefixPartial 13 91265) = some ⟨13, 2, 0, 228823, 91265, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_91265_228823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91265 ⟨228823, by decide⟩ :=
  accepted_of_selected 13 91265 ⟨228823, by decide⟩ ⟨13, 2, 0, 228823, 91265, 2221, 16384⟩
    (by decide) selected_cut_08036

theorem selected_cut_08037 : selected 8 ⟨228843, by decide⟩
    (prefixPartial 13 91266) = some ⟨13, 2, 0, 228843, 91266, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_91266_228843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91266 ⟨228843, by decide⟩ :=
  accepted_of_selected 13 91266 ⟨228843, by decide⟩ ⟨13, 2, 0, 228843, 91266, 1357, 16384⟩
    (by decide) selected_cut_08037

theorem selected_cut_08038 : selected 8 ⟨228850, by decide⟩
    (prefixPartial 13 91267) = some ⟨13, 2, 0, 228850, 91267, 965, 16384⟩ := by
  decide +kernel

theorem context_13_91267_228850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91267 ⟨228850, by decide⟩ :=
  accepted_of_selected 13 91267 ⟨228850, by decide⟩ ⟨13, 2, 0, 228850, 91267, 965, 16384⟩
    (by decide) selected_cut_08038

theorem unmarked_context_12_22816_228851 : frontier 9 ⟨228851, by decide⟩
    (prefixCache 12 22816) (prefixPartial 12 22816) = false := by
  decide +kernel

theorem node_context_12_22816_228851 : EJMOriginalGlobalDAGData.nodes 9 ⟨228851, by decide⟩ =
    .split (coordinate 12) (![⟨228801, by decide⟩,⟨228823, by decide⟩,⟨228843, by decide⟩,⟨228850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22816_228851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22816 ⟨228851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22816
    ⟨228851, by decide⟩ (by decide) (![⟨228801, by decide⟩,⟨228823, by decide⟩,⟨228843, by decide⟩,⟨228850, by decide⟩]) unmarked_context_12_22816_228851 node_context_12_22816_228851
  intro a
  fin_cases a
  · exact context_13_91264_228801
  · exact context_13_91265_228823
  · exact context_13_91266_228843
  · exact context_13_91267_228850

theorem selected_cut_08039 : selected 8 ⟨228863, by decide⟩
    (prefixPartial 13 91268) = some ⟨13, 2, 0, 228863, 91268, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_91268_228863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91268 ⟨228863, by decide⟩ :=
  accepted_of_selected 13 91268 ⟨228863, by decide⟩ ⟨13, 2, 0, 228863, 91268, 1273, 16384⟩
    (by decide) selected_cut_08039

theorem selected_cut_08040 : selected 8 ⟨228892, by decide⟩
    (prefixPartial 13 91269) = some ⟨13, 2, 0, 228892, 91269, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_91269_228892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91269 ⟨228892, by decide⟩ :=
  accepted_of_selected 13 91269 ⟨228892, by decide⟩ ⟨13, 2, 0, 228892, 91269, 1777, 16384⟩
    (by decide) selected_cut_08040

theorem selected_cut_08041 : selected 8 ⟨228911, by decide⟩
    (prefixPartial 13 91270) = some ⟨13, 2, 0, 228911, 91270, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_91270_228911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91270 ⟨228911, by decide⟩ :=
  accepted_of_selected 13 91270 ⟨228911, by decide⟩ ⟨13, 2, 0, 228911, 91270, 1453, 16384⟩
    (by decide) selected_cut_08041

theorem selected_cut_08042 : selected 8 ⟨228917, by decide⟩
    (prefixPartial 13 91271) = some ⟨13, 2, 0, 228917, 91271, 961, 16384⟩ := by
  decide +kernel

theorem context_13_91271_228917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91271 ⟨228917, by decide⟩ :=
  accepted_of_selected 13 91271 ⟨228917, by decide⟩ ⟨13, 2, 0, 228917, 91271, 961, 16384⟩
    (by decide) selected_cut_08042

theorem unmarked_context_12_22817_228918 : frontier 9 ⟨228918, by decide⟩
    (prefixCache 12 22817) (prefixPartial 12 22817) = false := by
  decide +kernel

theorem node_context_12_22817_228918 : EJMOriginalGlobalDAGData.nodes 9 ⟨228918, by decide⟩ =
    .split (coordinate 12) (![⟨228863, by decide⟩,⟨228892, by decide⟩,⟨228911, by decide⟩,⟨228917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22817_228918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22817 ⟨228918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22817
    ⟨228918, by decide⟩ (by decide) (![⟨228863, by decide⟩,⟨228892, by decide⟩,⟨228911, by decide⟩,⟨228917, by decide⟩]) unmarked_context_12_22817_228918 node_context_12_22817_228918
  intro a
  fin_cases a
  · exact context_13_91268_228863
  · exact context_13_91269_228892
  · exact context_13_91270_228911
  · exact context_13_91271_228917

theorem selected_cut_08043 : selected 8 ⟨228941, by decide⟩
    (prefixPartial 13 91272) = some ⟨13, 2, 0, 228941, 91272, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_91272_228941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91272 ⟨228941, by decide⟩ :=
  accepted_of_selected 13 91272 ⟨228941, by decide⟩ ⟨13, 2, 0, 228941, 91272, 1901, 16384⟩
    (by decide) selected_cut_08043

theorem selected_cut_08044 : selected 8 ⟨228973, by decide⟩
    (prefixPartial 13 91273) = some ⟨13, 2, 0, 228973, 91273, 2737, 16384⟩ := by
  decide +kernel

theorem context_13_91273_228973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91273 ⟨228973, by decide⟩ :=
  accepted_of_selected 13 91273 ⟨228973, by decide⟩ ⟨13, 2, 0, 228973, 91273, 2737, 16384⟩
    (by decide) selected_cut_08044

theorem selected_cut_08045 : selected 8 ⟨228994, by decide⟩
    (prefixPartial 13 91274) = some ⟨13, 2, 0, 228994, 91274, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_91274_228994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91274 ⟨228994, by decide⟩ :=
  accepted_of_selected 13 91274 ⟨228994, by decide⟩ ⟨13, 2, 0, 228994, 91274, 1777, 16384⟩
    (by decide) selected_cut_08045

theorem selected_cut_08046 : selected 8 ⟨229005, by decide⟩
    (prefixPartial 13 91275) = some ⟨13, 2, 0, 229005, 91275, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_91275_229005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91275 ⟨229005, by decide⟩ :=
  accepted_of_selected 13 91275 ⟨229005, by decide⟩ ⟨13, 2, 0, 229005, 91275, 1085, 16384⟩
    (by decide) selected_cut_08046

theorem unmarked_context_12_22818_229006 : frontier 9 ⟨229006, by decide⟩
    (prefixCache 12 22818) (prefixPartial 12 22818) = false := by
  decide +kernel

theorem node_context_12_22818_229006 : EJMOriginalGlobalDAGData.nodes 9 ⟨229006, by decide⟩ =
    .split (coordinate 12) (![⟨228941, by decide⟩,⟨228973, by decide⟩,⟨228994, by decide⟩,⟨229005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22818_229006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22818 ⟨229006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22818
    ⟨229006, by decide⟩ (by decide) (![⟨228941, by decide⟩,⟨228973, by decide⟩,⟨228994, by decide⟩,⟨229005, by decide⟩]) unmarked_context_12_22818_229006 node_context_12_22818_229006
  intro a
  fin_cases a
  · exact context_13_91272_228941
  · exact context_13_91273_228973
  · exact context_13_91274_228994
  · exact context_13_91275_229005

theorem selected_cut_08047 : selected 8 ⟨229031, by decide⟩
    (prefixPartial 13 91276) = some ⟨13, 2, 0, 229031, 91276, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_91276_229031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91276 ⟨229031, by decide⟩ :=
  accepted_of_selected 13 91276 ⟨229031, by decide⟩ ⟨13, 2, 0, 229031, 91276, 1881, 16384⟩
    (by decide) selected_cut_08047

theorem selected_cut_08048 : selected 8 ⟨229072, by decide⟩
    (prefixPartial 13 91277) = some ⟨13, 2, 0, 229072, 91277, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_91277_229072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91277 ⟨229072, by decide⟩ :=
  accepted_of_selected 13 91277 ⟨229072, by decide⟩ ⟨13, 2, 0, 229072, 91277, 2901, 16384⟩
    (by decide) selected_cut_08048

theorem selected_cut_08049 : selected 8 ⟨229092, by decide⟩
    (prefixPartial 13 91278) = some ⟨13, 2, 0, 229092, 91278, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_91278_229092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91278 ⟨229092, by decide⟩ :=
  accepted_of_selected 13 91278 ⟨229092, by decide⟩ ⟨13, 2, 0, 229092, 91278, 1785, 16384⟩
    (by decide) selected_cut_08049

theorem selected_cut_08050 : selected 8 ⟨229102, by decide⟩
    (prefixPartial 13 91279) = some ⟨13, 2, 0, 229102, 91279, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_91279_229102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91279 ⟨229102, by decide⟩ :=
  accepted_of_selected 13 91279 ⟨229102, by decide⟩ ⟨13, 2, 0, 229102, 91279, 1093, 16384⟩
    (by decide) selected_cut_08050

theorem unmarked_context_12_22819_229103 : frontier 9 ⟨229103, by decide⟩
    (prefixCache 12 22819) (prefixPartial 12 22819) = false := by
  decide +kernel

theorem node_context_12_22819_229103 : EJMOriginalGlobalDAGData.nodes 9 ⟨229103, by decide⟩ =
    .split (coordinate 12) (![⟨229031, by decide⟩,⟨229072, by decide⟩,⟨229092, by decide⟩,⟨229102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22819_229103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22819 ⟨229103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22819
    ⟨229103, by decide⟩ (by decide) (![⟨229031, by decide⟩,⟨229072, by decide⟩,⟨229092, by decide⟩,⟨229102, by decide⟩]) unmarked_context_12_22819_229103 node_context_12_22819_229103
  intro a
  fin_cases a
  · exact context_13_91276_229031
  · exact context_13_91277_229072
  · exact context_13_91278_229092
  · exact context_13_91279_229102

theorem unmarked_context_11_5704_229104 : frontier 10 ⟨229104, by decide⟩
    (prefixCache 11 5704) (prefixPartial 11 5704) = false := by
  decide +kernel

theorem node_context_11_5704_229104 : EJMOriginalGlobalDAGData.nodes 10 ⟨229104, by decide⟩ =
    .split (coordinate 11) (![⟨228851, by decide⟩,⟨228918, by decide⟩,⟨229006, by decide⟩,⟨229103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5704_229104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5704 ⟨229104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5704
    ⟨229104, by decide⟩ (by decide) (![⟨228851, by decide⟩,⟨228918, by decide⟩,⟨229006, by decide⟩,⟨229103, by decide⟩]) unmarked_context_11_5704_229104 node_context_11_5704_229104
  intro a
  fin_cases a
  · exact context_12_22816_228851
  · exact context_12_22817_228918
  · exact context_12_22818_229006
  · exact context_12_22819_229103

theorem selected_cut_08051 : selected 8 ⟨229118, by decide⟩
    (prefixPartial 13 91280) = some ⟨13, 2, 0, 229118, 91280, 921, 16384⟩ := by
  decide +kernel

theorem context_13_91280_229118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91280 ⟨229118, by decide⟩ :=
  accepted_of_selected 13 91280 ⟨229118, by decide⟩ ⟨13, 2, 0, 229118, 91280, 921, 16384⟩
    (by decide) selected_cut_08051

theorem selected_cut_08052 : selected 8 ⟨229143, by decide⟩
    (prefixPartial 13 91281) = some ⟨13, 2, 0, 229143, 91281, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_91281_229143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91281 ⟨229143, by decide⟩ :=
  accepted_of_selected 13 91281 ⟨229143, by decide⟩ ⟨13, 2, 0, 229143, 91281, 2013, 16384⟩
    (by decide) selected_cut_08052

theorem selected_cut_08053 : selected 8 ⟨229161, by decide⟩
    (prefixPartial 13 91282) = some ⟨13, 2, 0, 229161, 91282, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_91282_229161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91282 ⟨229161, by decide⟩ :=
  accepted_of_selected 13 91282 ⟨229161, by decide⟩ ⟨13, 2, 0, 229161, 91282, 1089, 16384⟩
    (by decide) selected_cut_08053

theorem selected_cut_08054 : selected 8 ⟨229166, by decide⟩
    (prefixPartial 13 91283) = some ⟨13, 2, 0, 229166, 91283, 909, 16384⟩ := by
  decide +kernel

theorem context_13_91283_229166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91283 ⟨229166, by decide⟩ :=
  accepted_of_selected 13 91283 ⟨229166, by decide⟩ ⟨13, 2, 0, 229166, 91283, 909, 16384⟩
    (by decide) selected_cut_08054

theorem unmarked_context_12_22820_229167 : frontier 9 ⟨229167, by decide⟩
    (prefixCache 12 22820) (prefixPartial 12 22820) = false := by
  decide +kernel

theorem node_context_12_22820_229167 : EJMOriginalGlobalDAGData.nodes 9 ⟨229167, by decide⟩ =
    .split (coordinate 12) (![⟨229118, by decide⟩,⟨229143, by decide⟩,⟨229161, by decide⟩,⟨229166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22820_229167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22820 ⟨229167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22820
    ⟨229167, by decide⟩ (by decide) (![⟨229118, by decide⟩,⟨229143, by decide⟩,⟨229161, by decide⟩,⟨229166, by decide⟩]) unmarked_context_12_22820_229167 node_context_12_22820_229167
  intro a
  fin_cases a
  · exact context_13_91280_229118
  · exact context_13_91281_229143
  · exact context_13_91282_229161
  · exact context_13_91283_229166

theorem selected_cut_08055 : selected 8 ⟨229184, by decide⟩
    (prefixPartial 13 91284) = some ⟨13, 2, 0, 229184, 91284, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_91284_229184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91284 ⟨229184, by decide⟩ :=
  accepted_of_selected 13 91284 ⟨229184, by decide⟩ ⟨13, 2, 0, 229184, 91284, 1421, 16384⟩
    (by decide) selected_cut_08055

theorem selected_cut_08056 : selected 8 ⟨229209, by decide⟩
    (prefixPartial 13 91285) = some ⟨13, 2, 0, 229209, 91285, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_91285_229209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91285 ⟨229209, by decide⟩ :=
  accepted_of_selected 13 91285 ⟨229209, by decide⟩ ⟨13, 2, 0, 229209, 91285, 2849, 16384⟩
    (by decide) selected_cut_08056

theorem selected_cut_08057 : selected 8 ⟨229229, by decide⟩
    (prefixPartial 13 91286) = some ⟨13, 2, 0, 229229, 91286, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_91286_229229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91286 ⟨229229, by decide⟩ :=
  accepted_of_selected 13 91286 ⟨229229, by decide⟩ ⟨13, 2, 0, 229229, 91286, 1889, 16384⟩
    (by decide) selected_cut_08057

theorem selected_cut_08058 : selected 8 ⟨229235, by decide⟩
    (prefixPartial 13 91287) = some ⟨13, 2, 0, 229235, 91287, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_91287_229235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91287 ⟨229235, by decide⟩ :=
  accepted_of_selected 13 91287 ⟨229235, by decide⟩ ⟨13, 2, 0, 229235, 91287, 1161, 16384⟩
    (by decide) selected_cut_08058

theorem unmarked_context_12_22821_229236 : frontier 9 ⟨229236, by decide⟩
    (prefixCache 12 22821) (prefixPartial 12 22821) = false := by
  decide +kernel

theorem node_context_12_22821_229236 : EJMOriginalGlobalDAGData.nodes 9 ⟨229236, by decide⟩ =
    .split (coordinate 12) (![⟨229184, by decide⟩,⟨229209, by decide⟩,⟨229229, by decide⟩,⟨229235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22821_229236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22821 ⟨229236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22821
    ⟨229236, by decide⟩ (by decide) (![⟨229184, by decide⟩,⟨229209, by decide⟩,⟨229229, by decide⟩,⟨229235, by decide⟩]) unmarked_context_12_22821_229236 node_context_12_22821_229236
  intro a
  fin_cases a
  · exact context_13_91284_229184
  · exact context_13_91285_229209
  · exact context_13_91286_229229
  · exact context_13_91287_229235

theorem selected_cut_08059 : selected 8 ⟨229253, by decide⟩
    (prefixPartial 13 91288) = some ⟨13, 2, 0, 229253, 91288, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_91288_229253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91288 ⟨229253, by decide⟩ :=
  accepted_of_selected 13 91288 ⟨229253, by decide⟩ ⟨13, 2, 0, 229253, 91288, 1225, 16384⟩
    (by decide) selected_cut_08059

theorem selected_cut_08060 : selected 8 ⟨229278, by decide⟩
    (prefixPartial 13 91289) = some ⟨13, 2, 0, 229278, 91289, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_91289_229278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91289 ⟨229278, by decide⟩ :=
  accepted_of_selected 13 91289 ⟨229278, by decide⟩ ⟨13, 2, 0, 229278, 91289, 2305, 16384⟩
    (by decide) selected_cut_08060

theorem selected_cut_08061 : selected 8 ⟨229297, by decide⟩
    (prefixPartial 13 91290) = some ⟨13, 2, 0, 229297, 91290, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_91290_229297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91290 ⟨229297, by decide⟩ :=
  accepted_of_selected 13 91290 ⟨229297, by decide⟩ ⟨13, 2, 0, 229297, 91290, 1373, 16384⟩
    (by decide) selected_cut_08061

theorem selected_cut_08062 : selected 8 ⟨229304, by decide⟩
    (prefixPartial 13 91291) = some ⟨13, 2, 0, 229304, 91291, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_91291_229304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91291 ⟨229304, by decide⟩ :=
  accepted_of_selected 13 91291 ⟨229304, by decide⟩ ⟨13, 2, 0, 229304, 91291, 1013, 16384⟩
    (by decide) selected_cut_08062

theorem unmarked_context_12_22822_229305 : frontier 9 ⟨229305, by decide⟩
    (prefixCache 12 22822) (prefixPartial 12 22822) = false := by
  decide +kernel

theorem node_context_12_22822_229305 : EJMOriginalGlobalDAGData.nodes 9 ⟨229305, by decide⟩ =
    .split (coordinate 12) (![⟨229253, by decide⟩,⟨229278, by decide⟩,⟨229297, by decide⟩,⟨229304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22822_229305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22822 ⟨229305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22822
    ⟨229305, by decide⟩ (by decide) (![⟨229253, by decide⟩,⟨229278, by decide⟩,⟨229297, by decide⟩,⟨229304, by decide⟩]) unmarked_context_12_22822_229305 node_context_12_22822_229305
  intro a
  fin_cases a
  · exact context_13_91288_229253
  · exact context_13_91289_229278
  · exact context_13_91290_229297
  · exact context_13_91291_229304

theorem selected_cut_08063 : selected 8 ⟨229324, by decide⟩
    (prefixPartial 13 91292) = some ⟨13, 2, 0, 229324, 91292, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_91292_229324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91292 ⟨229324, by decide⟩ :=
  accepted_of_selected 13 91292 ⟨229324, by decide⟩ ⟨13, 2, 0, 229324, 91292, 1125, 16384⟩
    (by decide) selected_cut_08063

theorem selected_cut_08064 : selected 8 ⟨229352, by decide⟩
    (prefixPartial 13 91293) = some ⟨13, 2, 0, 229352, 91293, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_91293_229352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91293 ⟨229352, by decide⟩ :=
  accepted_of_selected 13 91293 ⟨229352, by decide⟩ ⟨13, 2, 0, 229352, 91293, 2345, 16384⟩
    (by decide) selected_cut_08064

theorem selected_cut_08065 : selected 8 ⟨229373, by decide⟩
    (prefixPartial 13 91294) = some ⟨13, 2, 0, 229373, 91294, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_91294_229373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91294 ⟨229373, by decide⟩ :=
  accepted_of_selected 13 91294 ⟨229373, by decide⟩ ⟨13, 2, 0, 229373, 91294, 1269, 16384⟩
    (by decide) selected_cut_08065

theorem selected_cut_08066 : selected 8 ⟨229383, by decide⟩
    (prefixPartial 13 91295) = some ⟨13, 2, 0, 229383, 91295, 937, 16384⟩ := by
  decide +kernel

theorem context_13_91295_229383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91295 ⟨229383, by decide⟩ :=
  accepted_of_selected 13 91295 ⟨229383, by decide⟩ ⟨13, 2, 0, 229383, 91295, 937, 16384⟩
    (by decide) selected_cut_08066

theorem unmarked_context_12_22823_229384 : frontier 9 ⟨229384, by decide⟩
    (prefixCache 12 22823) (prefixPartial 12 22823) = false := by
  decide +kernel

theorem node_context_12_22823_229384 : EJMOriginalGlobalDAGData.nodes 9 ⟨229384, by decide⟩ =
    .split (coordinate 12) (![⟨229324, by decide⟩,⟨229352, by decide⟩,⟨229373, by decide⟩,⟨229383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22823_229384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22823 ⟨229384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22823
    ⟨229384, by decide⟩ (by decide) (![⟨229324, by decide⟩,⟨229352, by decide⟩,⟨229373, by decide⟩,⟨229383, by decide⟩]) unmarked_context_12_22823_229384 node_context_12_22823_229384
  intro a
  fin_cases a
  · exact context_13_91292_229324
  · exact context_13_91293_229352
  · exact context_13_91294_229373
  · exact context_13_91295_229383

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
