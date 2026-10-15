/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover280
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26980 : selected 8 ⟨681972, by decide⟩
    (prefixPartial 13 364795) = some ⟨13, 2, 0, 681972, 364795, 797, 16384⟩ := by
  decide +kernel

theorem context_13_364795_681972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364795 ⟨681972, by decide⟩ :=
  accepted_of_selected 13 364795 ⟨681972, by decide⟩ ⟨13, 2, 0, 681972, 364795, 797, 16384⟩
    (by decide) selected_cut_26980

theorem unmarked_context_12_91198_681973 : frontier 9 ⟨681973, by decide⟩
    (prefixCache 12 91198) (prefixPartial 12 91198) = false := by
  decide +kernel

theorem node_context_12_91198_681973 : EJMOriginalGlobalDAGData.nodes 9 ⟨681973, by decide⟩ =
    .split (coordinate 12) (![⟨681915, by decide⟩,⟨681947, by decide⟩,⟨681964, by decide⟩,⟨681972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91198_681973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91198 ⟨681973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91198
    ⟨681973, by decide⟩ (by decide) (![⟨681915, by decide⟩,⟨681947, by decide⟩,⟨681964, by decide⟩,⟨681972, by decide⟩]) unmarked_context_12_91198_681973 node_context_12_91198_681973
  intro a
  fin_cases a
  · exact context_13_364792_681915
  · exact context_13_364793_681947
  · exact context_13_364794_681964
  · exact context_13_364795_681972

theorem selected_cut_26981 : selected 8 ⟨681976, by decide⟩
    (prefixPartial 13 364796) = some ⟨13, 2, 0, 681976, 364796, 53, 16384⟩ := by
  decide +kernel

theorem context_13_364796_681976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364796 ⟨681976, by decide⟩ :=
  accepted_of_selected 13 364796 ⟨681976, by decide⟩ ⟨13, 2, 0, 681976, 364796, 53, 16384⟩
    (by decide) selected_cut_26981

theorem selected_cut_26982 : selected 8 ⟨682026, by decide⟩
    (prefixPartial 13 364797) = some ⟨13, 2, 0, 682026, 364797, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_364797_682026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364797 ⟨682026, by decide⟩ :=
  accepted_of_selected 13 364797 ⟨682026, by decide⟩ ⟨13, 2, 0, 682026, 364797, 2469, 16384⟩
    (by decide) selected_cut_26982

theorem selected_cut_26983 : selected 8 ⟨682046, by decide⟩
    (prefixPartial 13 364798) = some ⟨13, 2, 0, 682046, 364798, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_364798_682046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364798 ⟨682046, by decide⟩ :=
  accepted_of_selected 13 364798 ⟨682046, by decide⟩ ⟨13, 2, 0, 682046, 364798, 1465, 16384⟩
    (by decide) selected_cut_26983

theorem selected_cut_26984 : selected 8 ⟨682051, by decide⟩
    (prefixPartial 13 364799) = some ⟨13, 2, 0, 682051, 364799, 693, 16384⟩ := by
  decide +kernel

theorem context_13_364799_682051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364799 ⟨682051, by decide⟩ :=
  accepted_of_selected 13 364799 ⟨682051, by decide⟩ ⟨13, 2, 0, 682051, 364799, 693, 16384⟩
    (by decide) selected_cut_26984

theorem unmarked_context_12_91199_682052 : frontier 9 ⟨682052, by decide⟩
    (prefixCache 12 91199) (prefixPartial 12 91199) = false := by
  decide +kernel

theorem node_context_12_91199_682052 : EJMOriginalGlobalDAGData.nodes 9 ⟨682052, by decide⟩ =
    .split (coordinate 12) (![⟨681976, by decide⟩,⟨682026, by decide⟩,⟨682046, by decide⟩,⟨682051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91199_682052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91199 ⟨682052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91199
    ⟨682052, by decide⟩ (by decide) (![⟨681976, by decide⟩,⟨682026, by decide⟩,⟨682046, by decide⟩,⟨682051, by decide⟩]) unmarked_context_12_91199_682052 node_context_12_91199_682052
  intro a
  fin_cases a
  · exact context_13_364796_681976
  · exact context_13_364797_682026
  · exact context_13_364798_682046
  · exact context_13_364799_682051

theorem unmarked_context_11_22799_682053 : frontier 10 ⟨682053, by decide⟩
    (prefixCache 11 22799) (prefixPartial 11 22799) = false := by
  decide +kernel

theorem node_context_11_22799_682053 : EJMOriginalGlobalDAGData.nodes 10 ⟨682053, by decide⟩ =
    .split (coordinate 11) (![⟨681827, by decide⟩,⟨681912, by decide⟩,⟨681973, by decide⟩,⟨682052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22799_682053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22799 ⟨682053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22799
    ⟨682053, by decide⟩ (by decide) (![⟨681827, by decide⟩,⟨681912, by decide⟩,⟨681973, by decide⟩,⟨682052, by decide⟩]) unmarked_context_11_22799_682053 node_context_11_22799_682053
  intro a
  fin_cases a
  · exact context_12_91196_681827
  · exact context_12_91197_681912
  · exact context_12_91198_681973
  · exact context_12_91199_682052

theorem unmarked_context_10_5699_682054 : frontier 11 ⟨682054, by decide⟩
    (prefixCache 10 5699) (prefixPartial 10 5699) = false := by
  decide +kernel

theorem node_context_10_5699_682054 : EJMOriginalGlobalDAGData.nodes 11 ⟨682054, by decide⟩ =
    .split (coordinate 10) (![⟨681086, by decide⟩,⟨681373, by decide⟩,⟨681762, by decide⟩,⟨682053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5699_682054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5699 ⟨682054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5699
    ⟨682054, by decide⟩ (by decide) (![⟨681086, by decide⟩,⟨681373, by decide⟩,⟨681762, by decide⟩,⟨682053, by decide⟩]) unmarked_context_10_5699_682054 node_context_10_5699_682054
  intro a
  fin_cases a
  · exact context_11_22796_681086
  · exact context_11_22797_681373
  · exact context_11_22798_681762
  · exact context_11_22799_682053

theorem unmarked_context_9_1424_682055 : frontier 12 ⟨682055, by decide⟩
    (prefixCache 9 1424) (prefixPartial 9 1424) = false := by
  decide +kernel

theorem node_context_9_1424_682055 : EJMOriginalGlobalDAGData.nodes 12 ⟨682055, by decide⟩ =
    .split (coordinate 9) (![⟨678237, by decide⟩,⟨679730, by decide⟩,⟨680877, by decide⟩,⟨682054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1424_682055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1424 ⟨682055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1424
    ⟨682055, by decide⟩ (by decide) (![⟨678237, by decide⟩,⟨679730, by decide⟩,⟨680877, by decide⟩,⟨682054, by decide⟩]) unmarked_context_9_1424_682055 node_context_9_1424_682055
  intro a
  fin_cases a
  · exact context_10_5696_678237
  · exact context_10_5697_679730
  · exact context_10_5698_680877
  · exact context_10_5699_682054

theorem selected_cut_26985 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 91200) = some ⟨12, 1, 0, 450982, 91200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91200_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91200 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 91200 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 91200, 1, 65536⟩
    (by decide) selected_cut_26985

theorem selected_cut_26986 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91201) = some ⟨12, 1, 0, 170504, 91201, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91201_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91201 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91201 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91201, 1, 65536⟩
    (by decide) selected_cut_26986

theorem selected_cut_26987 : selected 9 ⟨682117, by decide⟩
    (prefixPartial 12 91202) = some ⟨12, 2, 0, 682117, 91202, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_91202_682117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91202 ⟨682117, by decide⟩ :=
  accepted_of_selected 12 91202 ⟨682117, by decide⟩ ⟨12, 2, 0, 682117, 91202, 3405, 65536⟩
    (by decide) selected_cut_26987

theorem selected_cut_26988 : selected 9 ⟨682185, by decide⟩
    (prefixPartial 12 91203) = some ⟨12, 2, 0, 682185, 91203, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_91203_682185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91203 ⟨682185, by decide⟩ :=
  accepted_of_selected 12 91203 ⟨682185, by decide⟩ ⟨12, 2, 0, 682185, 91203, 3617, 65536⟩
    (by decide) selected_cut_26988

theorem unmarked_context_11_22800_682186 : frontier 10 ⟨682186, by decide⟩
    (prefixCache 11 22800) (prefixPartial 11 22800) = false := by
  decide +kernel

theorem node_context_11_22800_682186 : EJMOriginalGlobalDAGData.nodes 10 ⟨682186, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨170504, by decide⟩,⟨682117, by decide⟩,⟨682185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22800_682186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22800 ⟨682186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22800
    ⟨682186, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨170504, by decide⟩,⟨682117, by decide⟩,⟨682185, by decide⟩]) unmarked_context_11_22800_682186 node_context_11_22800_682186
  intro a
  fin_cases a
  · exact context_12_91200_450982
  · exact context_12_91201_170504
  · exact context_12_91202_682117
  · exact context_12_91203_682185

theorem selected_cut_26989 : selected 9 ⟨682240, by decide⟩
    (prefixPartial 12 91204) = some ⟨12, 2, 0, 682240, 91204, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_91204_682240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91204 ⟨682240, by decide⟩ :=
  accepted_of_selected 12 91204 ⟨682240, by decide⟩ ⟨12, 2, 0, 682240, 91204, 2921, 65536⟩
    (by decide) selected_cut_26989

theorem selected_cut_26990 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 91205) = some ⟨12, 1, 0, 170504, 91205, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91205_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91205 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 91205 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 91205, 1, 65536⟩
    (by decide) selected_cut_26990

theorem selected_cut_26991 : selected 9 ⟨682294, by decide⟩
    (prefixPartial 12 91206) = some ⟨12, 2, 0, 682294, 91206, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_91206_682294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91206 ⟨682294, by decide⟩ :=
  accepted_of_selected 12 91206 ⟨682294, by decide⟩ ⟨12, 2, 0, 682294, 91206, 3457, 65536⟩
    (by decide) selected_cut_26991

theorem selected_cut_26992 : selected 9 ⟨682353, by decide⟩
    (prefixPartial 12 91207) = some ⟨12, 2, 0, 682353, 91207, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_91207_682353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91207 ⟨682353, by decide⟩ :=
  accepted_of_selected 12 91207 ⟨682353, by decide⟩ ⟨12, 2, 0, 682353, 91207, 3617, 65536⟩
    (by decide) selected_cut_26992

theorem unmarked_context_11_22801_682354 : frontier 10 ⟨682354, by decide⟩
    (prefixCache 11 22801) (prefixPartial 11 22801) = false := by
  decide +kernel

theorem node_context_11_22801_682354 : EJMOriginalGlobalDAGData.nodes 10 ⟨682354, by decide⟩ =
    .split (coordinate 11) (![⟨682240, by decide⟩,⟨170504, by decide⟩,⟨682294, by decide⟩,⟨682353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22801_682354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22801 ⟨682354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22801
    ⟨682354, by decide⟩ (by decide) (![⟨682240, by decide⟩,⟨170504, by decide⟩,⟨682294, by decide⟩,⟨682353, by decide⟩]) unmarked_context_11_22801_682354 node_context_11_22801_682354
  intro a
  fin_cases a
  · exact context_12_91204_682240
  · exact context_12_91205_170504
  · exact context_12_91206_682294
  · exact context_12_91207_682353

theorem selected_cut_26993 : selected 9 ⟨682420, by decide⟩
    (prefixPartial 12 91208) = some ⟨12, 2, 0, 682420, 91208, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_91208_682420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91208 ⟨682420, by decide⟩ :=
  accepted_of_selected 12 91208 ⟨682420, by decide⟩ ⟨12, 2, 0, 682420, 91208, 3377, 65536⟩
    (by decide) selected_cut_26993

theorem selected_cut_26994 : selected 9 ⟨682494, by decide⟩
    (prefixPartial 12 91209) = some ⟨12, 2, 0, 682494, 91209, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_91209_682494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91209 ⟨682494, by decide⟩ :=
  accepted_of_selected 12 91209 ⟨682494, by decide⟩ ⟨12, 2, 0, 682494, 91209, 2025, 65536⟩
    (by decide) selected_cut_26994

theorem selected_cut_26995 : selected 9 ⟨682559, by decide⟩
    (prefixPartial 12 91210) = some ⟨12, 2, 0, 682559, 91210, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_91210_682559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91210 ⟨682559, by decide⟩ :=
  accepted_of_selected 12 91210 ⟨682559, by decide⟩ ⟨12, 2, 0, 682559, 91210, 3589, 65536⟩
    (by decide) selected_cut_26995

theorem selected_cut_26996 : selected 9 ⟨682627, by decide⟩
    (prefixPartial 12 91211) = some ⟨12, 2, 0, 682627, 91211, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_91211_682627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91211 ⟨682627, by decide⟩ :=
  accepted_of_selected 12 91211 ⟨682627, by decide⟩ ⟨12, 2, 0, 682627, 91211, 3965, 65536⟩
    (by decide) selected_cut_26996

theorem unmarked_context_11_22802_682628 : frontier 10 ⟨682628, by decide⟩
    (prefixCache 11 22802) (prefixPartial 11 22802) = false := by
  decide +kernel

theorem node_context_11_22802_682628 : EJMOriginalGlobalDAGData.nodes 10 ⟨682628, by decide⟩ =
    .split (coordinate 11) (![⟨682420, by decide⟩,⟨682494, by decide⟩,⟨682559, by decide⟩,⟨682627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22802_682628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22802 ⟨682628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22802
    ⟨682628, by decide⟩ (by decide) (![⟨682420, by decide⟩,⟨682494, by decide⟩,⟨682559, by decide⟩,⟨682627, by decide⟩]) unmarked_context_11_22802_682628 node_context_11_22802_682628
  intro a
  fin_cases a
  · exact context_12_91208_682420
  · exact context_12_91209_682494
  · exact context_12_91210_682559
  · exact context_12_91211_682627

theorem selected_cut_26997 : selected 9 ⟨682682, by decide⟩
    (prefixPartial 12 91212) = some ⟨12, 2, 0, 682682, 91212, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_91212_682682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91212 ⟨682682, by decide⟩ :=
  accepted_of_selected 12 91212 ⟨682682, by decide⟩ ⟨12, 2, 0, 682682, 91212, 3133, 65536⟩
    (by decide) selected_cut_26997

theorem selected_cut_26998 : selected 9 ⟨682734, by decide⟩
    (prefixPartial 12 91213) = some ⟨12, 2, 0, 682734, 91213, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_91213_682734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91213 ⟨682734, by decide⟩ :=
  accepted_of_selected 12 91213 ⟨682734, by decide⟩ ⟨12, 2, 0, 682734, 91213, 2117, 65536⟩
    (by decide) selected_cut_26998

theorem selected_cut_26999 : selected 9 ⟨682788, by decide⟩
    (prefixPartial 12 91214) = some ⟨12, 2, 0, 682788, 91214, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_91214_682788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91214 ⟨682788, by decide⟩ :=
  accepted_of_selected 12 91214 ⟨682788, by decide⟩ ⟨12, 2, 0, 682788, 91214, 3729, 65536⟩
    (by decide) selected_cut_26999

theorem selected_cut_27000 : selected 9 ⟨682840, by decide⟩
    (prefixPartial 12 91215) = some ⟨12, 2, 0, 682840, 91215, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_91215_682840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91215 ⟨682840, by decide⟩ :=
  accepted_of_selected 12 91215 ⟨682840, by decide⟩ ⟨12, 2, 0, 682840, 91215, 3557, 65536⟩
    (by decide) selected_cut_27000

theorem unmarked_context_11_22803_682841 : frontier 10 ⟨682841, by decide⟩
    (prefixCache 11 22803) (prefixPartial 11 22803) = false := by
  decide +kernel

theorem node_context_11_22803_682841 : EJMOriginalGlobalDAGData.nodes 10 ⟨682841, by decide⟩ =
    .split (coordinate 11) (![⟨682682, by decide⟩,⟨682734, by decide⟩,⟨682788, by decide⟩,⟨682840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22803_682841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22803 ⟨682841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22803
    ⟨682841, by decide⟩ (by decide) (![⟨682682, by decide⟩,⟨682734, by decide⟩,⟨682788, by decide⟩,⟨682840, by decide⟩]) unmarked_context_11_22803_682841 node_context_11_22803_682841
  intro a
  fin_cases a
  · exact context_12_91212_682682
  · exact context_12_91213_682734
  · exact context_12_91214_682788
  · exact context_12_91215_682840

theorem unmarked_context_10_5700_682842 : frontier 11 ⟨682842, by decide⟩
    (prefixCache 10 5700) (prefixPartial 10 5700) = false := by
  decide +kernel

theorem node_context_10_5700_682842 : EJMOriginalGlobalDAGData.nodes 11 ⟨682842, by decide⟩ =
    .split (coordinate 10) (![⟨682186, by decide⟩,⟨682354, by decide⟩,⟨682628, by decide⟩,⟨682841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5700_682842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5700 ⟨682842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5700
    ⟨682842, by decide⟩ (by decide) (![⟨682186, by decide⟩,⟨682354, by decide⟩,⟨682628, by decide⟩,⟨682841, by decide⟩]) unmarked_context_10_5700_682842 node_context_10_5700_682842
  intro a
  fin_cases a
  · exact context_11_22800_682186
  · exact context_11_22801_682354
  · exact context_11_22802_682628
  · exact context_11_22803_682841

theorem selected_cut_27001 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 91216) = some ⟨12, 1, 0, 307381, 91216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91216_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91216 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 91216 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 91216, 1, 65536⟩
    (by decide) selected_cut_27001

theorem selected_cut_27002 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91217) = some ⟨12, 1, 0, 642341, 91217, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91217_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91217 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91217 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91217, 1, 65536⟩
    (by decide) selected_cut_27002

theorem selected_cut_27003 : selected 9 ⟨682879, by decide⟩
    (prefixPartial 12 91218) = some ⟨12, 2, 0, 682879, 91218, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_91218_682879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91218 ⟨682879, by decide⟩ :=
  accepted_of_selected 12 91218 ⟨682879, by decide⟩ ⟨12, 2, 0, 682879, 91218, 3161, 65536⟩
    (by decide) selected_cut_27003

theorem selected_cut_27004 : selected 9 ⟨682924, by decide⟩
    (prefixPartial 12 91219) = some ⟨12, 2, 0, 682924, 91219, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_91219_682924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91219 ⟨682924, by decide⟩ :=
  accepted_of_selected 12 91219 ⟨682924, by decide⟩ ⟨12, 2, 0, 682924, 91219, 3449, 65536⟩
    (by decide) selected_cut_27004

theorem unmarked_context_11_22804_682925 : frontier 10 ⟨682925, by decide⟩
    (prefixCache 11 22804) (prefixPartial 11 22804) = false := by
  decide +kernel

theorem node_context_11_22804_682925 : EJMOriginalGlobalDAGData.nodes 10 ⟨682925, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨642341, by decide⟩,⟨682879, by decide⟩,⟨682924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22804_682925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22804 ⟨682925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22804
    ⟨682925, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨642341, by decide⟩,⟨682879, by decide⟩,⟨682924, by decide⟩]) unmarked_context_11_22804_682925 node_context_11_22804_682925
  intro a
  fin_cases a
  · exact context_12_91216_307381
  · exact context_12_91217_642341
  · exact context_12_91218_682879
  · exact context_12_91219_682924

theorem selected_cut_27005 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 22805) = some ⟨11, 1, 0, 451541, 22805, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22805_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22805 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 22805 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 22805, 1, 262144⟩
    (by decide) selected_cut_27005

theorem selected_cut_27006 : selected 9 ⟨682968, by decide⟩
    (prefixPartial 12 91224) = some ⟨12, 2, 0, 682968, 91224, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_91224_682968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91224 ⟨682968, by decide⟩ :=
  accepted_of_selected 12 91224 ⟨682968, by decide⟩ ⟨12, 2, 0, 682968, 91224, 3169, 65536⟩
    (by decide) selected_cut_27006

theorem selected_cut_27007 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91225) = some ⟨12, 1, 0, 642341, 91225, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91225_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91225 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91225 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91225, 1, 65536⟩
    (by decide) selected_cut_27007

theorem selected_cut_27008 : selected 9 ⟨683013, by decide⟩
    (prefixPartial 12 91226) = some ⟨12, 2, 0, 683013, 91226, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_91226_683013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91226 ⟨683013, by decide⟩ :=
  accepted_of_selected 12 91226 ⟨683013, by decide⟩ ⟨12, 2, 0, 683013, 91226, 3329, 65536⟩
    (by decide) selected_cut_27008

theorem selected_cut_27009 : selected 9 ⟨683063, by decide⟩
    (prefixPartial 12 91227) = some ⟨12, 2, 0, 683063, 91227, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_91227_683063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91227 ⟨683063, by decide⟩ :=
  accepted_of_selected 12 91227 ⟨683063, by decide⟩ ⟨12, 2, 0, 683063, 91227, 3809, 65536⟩
    (by decide) selected_cut_27009

theorem unmarked_context_11_22806_683064 : frontier 10 ⟨683064, by decide⟩
    (prefixCache 11 22806) (prefixPartial 11 22806) = false := by
  decide +kernel

theorem node_context_11_22806_683064 : EJMOriginalGlobalDAGData.nodes 10 ⟨683064, by decide⟩ =
    .split (coordinate 11) (![⟨682968, by decide⟩,⟨642341, by decide⟩,⟨683013, by decide⟩,⟨683063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22806_683064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22806 ⟨683064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22806
    ⟨683064, by decide⟩ (by decide) (![⟨682968, by decide⟩,⟨642341, by decide⟩,⟨683013, by decide⟩,⟨683063, by decide⟩]) unmarked_context_11_22806_683064 node_context_11_22806_683064
  intro a
  fin_cases a
  · exact context_12_91224_682968
  · exact context_12_91225_642341
  · exact context_12_91226_683013
  · exact context_12_91227_683063

theorem selected_cut_27010 : selected 9 ⟨683105, by decide⟩
    (prefixPartial 12 91228) = some ⟨12, 2, 0, 683105, 91228, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_91228_683105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91228 ⟨683105, by decide⟩ :=
  accepted_of_selected 12 91228 ⟨683105, by decide⟩ ⟨12, 2, 0, 683105, 91228, 2953, 65536⟩
    (by decide) selected_cut_27010

theorem selected_cut_27011 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 91229) = some ⟨12, 1, 0, 642341, 91229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91229_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91229 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 91229 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 91229, 1, 65536⟩
    (by decide) selected_cut_27011

theorem selected_cut_27012 : selected 9 ⟨683148, by decide⟩
    (prefixPartial 12 91230) = some ⟨12, 2, 0, 683148, 91230, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_91230_683148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91230 ⟨683148, by decide⟩ :=
  accepted_of_selected 12 91230 ⟨683148, by decide⟩ ⟨12, 2, 0, 683148, 91230, 3677, 65536⟩
    (by decide) selected_cut_27012

theorem selected_cut_27013 : selected 9 ⟨683191, by decide⟩
    (prefixPartial 12 91231) = some ⟨12, 2, 0, 683191, 91231, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_91231_683191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91231 ⟨683191, by decide⟩ :=
  accepted_of_selected 12 91231 ⟨683191, by decide⟩ ⟨12, 2, 0, 683191, 91231, 3513, 65536⟩
    (by decide) selected_cut_27013

theorem unmarked_context_11_22807_683192 : frontier 10 ⟨683192, by decide⟩
    (prefixCache 11 22807) (prefixPartial 11 22807) = false := by
  decide +kernel

theorem node_context_11_22807_683192 : EJMOriginalGlobalDAGData.nodes 10 ⟨683192, by decide⟩ =
    .split (coordinate 11) (![⟨683105, by decide⟩,⟨642341, by decide⟩,⟨683148, by decide⟩,⟨683191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22807_683192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22807 ⟨683192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22807
    ⟨683192, by decide⟩ (by decide) (![⟨683105, by decide⟩,⟨642341, by decide⟩,⟨683148, by decide⟩,⟨683191, by decide⟩]) unmarked_context_11_22807_683192 node_context_11_22807_683192
  intro a
  fin_cases a
  · exact context_12_91228_683105
  · exact context_12_91229_642341
  · exact context_12_91230_683148
  · exact context_12_91231_683191

theorem unmarked_context_10_5701_683193 : frontier 11 ⟨683193, by decide⟩
    (prefixCache 10 5701) (prefixPartial 10 5701) = false := by
  decide +kernel

theorem node_context_10_5701_683193 : EJMOriginalGlobalDAGData.nodes 11 ⟨683193, by decide⟩ =
    .split (coordinate 10) (![⟨682925, by decide⟩,⟨451541, by decide⟩,⟨683064, by decide⟩,⟨683192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5701_683193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5701 ⟨683193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5701
    ⟨683193, by decide⟩ (by decide) (![⟨682925, by decide⟩,⟨451541, by decide⟩,⟨683064, by decide⟩,⟨683192, by decide⟩]) unmarked_context_10_5701_683193 node_context_10_5701_683193
  intro a
  fin_cases a
  · exact context_11_22804_682925
  · exact context_11_22805_451541
  · exact context_11_22806_683064
  · exact context_11_22807_683192

theorem selected_cut_27014 : selected 9 ⟨683295, by decide⟩
    (prefixPartial 12 91232) = some ⟨12, 2, 0, 683295, 91232, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_91232_683295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91232 ⟨683295, by decide⟩ :=
  accepted_of_selected 12 91232 ⟨683295, by decide⟩ ⟨12, 2, 0, 683295, 91232, 2769, 65536⟩
    (by decide) selected_cut_27014

theorem selected_cut_27015 : selected 9 ⟨683296, by decide⟩
    (prefixPartial 12 91233) = some ⟨12, 1, 0, 683296, 91233, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91233_683296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91233 ⟨683296, by decide⟩ :=
  accepted_of_selected 12 91233 ⟨683296, by decide⟩ ⟨12, 1, 0, 683296, 91233, 1, 65536⟩
    (by decide) selected_cut_27015

theorem selected_cut_27016 : selected 9 ⟨683336, by decide⟩
    (prefixPartial 12 91234) = some ⟨12, 2, 0, 683336, 91234, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_91234_683336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91234 ⟨683336, by decide⟩ :=
  accepted_of_selected 12 91234 ⟨683336, by decide⟩ ⟨12, 2, 0, 683336, 91234, 3093, 65536⟩
    (by decide) selected_cut_27016

theorem selected_cut_27017 : selected 9 ⟨683380, by decide⟩
    (prefixPartial 12 91235) = some ⟨12, 2, 0, 683380, 91235, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_91235_683380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91235 ⟨683380, by decide⟩ :=
  accepted_of_selected 12 91235 ⟨683380, by decide⟩ ⟨12, 2, 0, 683380, 91235, 3105, 65536⟩
    (by decide) selected_cut_27017

theorem unmarked_context_11_22808_683381 : frontier 10 ⟨683381, by decide⟩
    (prefixCache 11 22808) (prefixPartial 11 22808) = false := by
  decide +kernel

theorem node_context_11_22808_683381 : EJMOriginalGlobalDAGData.nodes 10 ⟨683381, by decide⟩ =
    .split (coordinate 11) (![⟨683295, by decide⟩,⟨683296, by decide⟩,⟨683336, by decide⟩,⟨683380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22808_683381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22808 ⟨683381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22808
    ⟨683381, by decide⟩ (by decide) (![⟨683295, by decide⟩,⟨683296, by decide⟩,⟨683336, by decide⟩,⟨683380, by decide⟩]) unmarked_context_11_22808_683381 node_context_11_22808_683381
  intro a
  fin_cases a
  · exact context_12_91232_683295
  · exact context_12_91233_683296
  · exact context_12_91234_683336
  · exact context_12_91235_683380

theorem selected_cut_27018 : selected 9 ⟨683425, by decide⟩
    (prefixPartial 12 91236) = some ⟨12, 2, 0, 683425, 91236, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_91236_683425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91236 ⟨683425, by decide⟩ :=
  accepted_of_selected 12 91236 ⟨683425, by decide⟩ ⟨12, 2, 0, 683425, 91236, 2761, 65536⟩
    (by decide) selected_cut_27018

theorem selected_cut_27019 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 91237) = some ⟨12, 1, 0, 642794, 91237, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91237_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91237 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 91237 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 91237, 1, 65536⟩
    (by decide) selected_cut_27019

theorem selected_cut_27020 : selected 9 ⟨683467, by decide⟩
    (prefixPartial 12 91238) = some ⟨12, 2, 0, 683467, 91238, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_91238_683467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91238 ⟨683467, by decide⟩ :=
  accepted_of_selected 12 91238 ⟨683467, by decide⟩ ⟨12, 2, 0, 683467, 91238, 3009, 65536⟩
    (by decide) selected_cut_27020

theorem selected_cut_27021 : selected 9 ⟨683511, by decide⟩
    (prefixPartial 12 91239) = some ⟨12, 2, 0, 683511, 91239, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_91239_683511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91239 ⟨683511, by decide⟩ :=
  accepted_of_selected 12 91239 ⟨683511, by decide⟩ ⟨12, 2, 0, 683511, 91239, 3149, 65536⟩
    (by decide) selected_cut_27021

theorem unmarked_context_11_22809_683512 : frontier 10 ⟨683512, by decide⟩
    (prefixCache 11 22809) (prefixPartial 11 22809) = false := by
  decide +kernel

theorem node_context_11_22809_683512 : EJMOriginalGlobalDAGData.nodes 10 ⟨683512, by decide⟩ =
    .split (coordinate 11) (![⟨683425, by decide⟩,⟨642794, by decide⟩,⟨683467, by decide⟩,⟨683511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22809_683512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22809 ⟨683512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22809
    ⟨683512, by decide⟩ (by decide) (![⟨683425, by decide⟩,⟨642794, by decide⟩,⟨683467, by decide⟩,⟨683511, by decide⟩]) unmarked_context_11_22809_683512 node_context_11_22809_683512
  intro a
  fin_cases a
  · exact context_12_91236_683425
  · exact context_12_91237_642794
  · exact context_12_91238_683467
  · exact context_12_91239_683511

theorem selected_cut_27022 : selected 9 ⟨683552, by decide⟩
    (prefixPartial 12 91240) = some ⟨12, 2, 0, 683552, 91240, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_91240_683552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91240 ⟨683552, by decide⟩ :=
  accepted_of_selected 12 91240 ⟨683552, by decide⟩ ⟨12, 2, 0, 683552, 91240, 2965, 65536⟩
    (by decide) selected_cut_27022

theorem selected_cut_27023 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 364964) = some ⟨13, 1, 0, 3444, 364964, 1, 16384⟩ := by
  decide +kernel

theorem context_13_364964_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364964 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 364964 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 364964, 1, 16384⟩
    (by decide) selected_cut_27023

theorem selected_cut_27024 : selected 8 ⟨683573, by decide⟩
    (prefixPartial 13 364965) = some ⟨13, 2, 0, 683573, 364965, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_364965_683573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364965 ⟨683573, by decide⟩ :=
  accepted_of_selected 13 364965 ⟨683573, by decide⟩ ⟨13, 2, 0, 683573, 364965, 1133, 16384⟩
    (by decide) selected_cut_27024

theorem selected_cut_27025 : selected 8 ⟨683609, by decide⟩
    (prefixPartial 13 364966) = some ⟨13, 2, 0, 683609, 364966, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_364966_683609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364966 ⟨683609, by decide⟩ :=
  accepted_of_selected 13 364966 ⟨683609, by decide⟩ ⟨13, 2, 0, 683609, 364966, 2133, 16384⟩
    (by decide) selected_cut_27025

theorem selected_cut_27026 : selected 8 ⟨683643, by decide⟩
    (prefixPartial 13 364967) = some ⟨13, 2, 0, 683643, 364967, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_364967_683643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364967 ⟨683643, by decide⟩ :=
  accepted_of_selected 13 364967 ⟨683643, by decide⟩ ⟨13, 2, 0, 683643, 364967, 1305, 16384⟩
    (by decide) selected_cut_27026

theorem unmarked_context_12_91241_683644 : frontier 9 ⟨683644, by decide⟩
    (prefixCache 12 91241) (prefixPartial 12 91241) = false := by
  decide +kernel

theorem node_context_12_91241_683644 : EJMOriginalGlobalDAGData.nodes 9 ⟨683644, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨683573, by decide⟩,⟨683609, by decide⟩,⟨683643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91241_683644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91241 ⟨683644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91241
    ⟨683644, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨683573, by decide⟩,⟨683609, by decide⟩,⟨683643, by decide⟩]) unmarked_context_12_91241_683644 node_context_12_91241_683644
  intro a
  fin_cases a
  · exact context_13_364964_3444
  · exact context_13_364965_683573
  · exact context_13_364966_683609
  · exact context_13_364967_683643

theorem selected_cut_27027 : selected 9 ⟨683684, by decide⟩
    (prefixPartial 12 91242) = some ⟨12, 2, 0, 683684, 91242, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_91242_683684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91242 ⟨683684, by decide⟩ :=
  accepted_of_selected 12 91242 ⟨683684, by decide⟩ ⟨12, 2, 0, 683684, 91242, 2993, 65536⟩
    (by decide) selected_cut_27027

theorem selected_cut_27028 : selected 9 ⟨683729, by decide⟩
    (prefixPartial 12 91243) = some ⟨12, 2, 0, 683729, 91243, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_91243_683729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91243 ⟨683729, by decide⟩ :=
  accepted_of_selected 12 91243 ⟨683729, by decide⟩ ⟨12, 2, 0, 683729, 91243, 3053, 65536⟩
    (by decide) selected_cut_27028

theorem unmarked_context_11_22810_683730 : frontier 10 ⟨683730, by decide⟩
    (prefixCache 11 22810) (prefixPartial 11 22810) = false := by
  decide +kernel

theorem node_context_11_22810_683730 : EJMOriginalGlobalDAGData.nodes 10 ⟨683730, by decide⟩ =
    .split (coordinate 11) (![⟨683552, by decide⟩,⟨683644, by decide⟩,⟨683684, by decide⟩,⟨683729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22810_683730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22810 ⟨683730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22810
    ⟨683730, by decide⟩ (by decide) (![⟨683552, by decide⟩,⟨683644, by decide⟩,⟨683684, by decide⟩,⟨683729, by decide⟩]) unmarked_context_11_22810_683730 node_context_11_22810_683730
  intro a
  fin_cases a
  · exact context_12_91240_683552
  · exact context_12_91241_683644
  · exact context_12_91242_683684
  · exact context_12_91243_683729

theorem selected_cut_27029 : selected 9 ⟨683768, by decide⟩
    (prefixPartial 12 91244) = some ⟨12, 2, 0, 683768, 91244, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_91244_683768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91244 ⟨683768, by decide⟩ :=
  accepted_of_selected 12 91244 ⟨683768, by decide⟩ ⟨12, 2, 0, 683768, 91244, 3013, 65536⟩
    (by decide) selected_cut_27029

theorem selected_cut_27030 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 364980) = some ⟨13, 1, 0, 3444, 364980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_364980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 364980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 364980, 1, 16384⟩
    (by decide) selected_cut_27030

theorem selected_cut_27031 : selected 8 ⟨683797, by decide⟩
    (prefixPartial 13 364981) = some ⟨13, 2, 0, 683797, 364981, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_364981_683797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364981 ⟨683797, by decide⟩ :=
  accepted_of_selected 13 364981 ⟨683797, by decide⟩ ⟨13, 2, 0, 683797, 364981, 1121, 16384⟩
    (by decide) selected_cut_27031

theorem selected_cut_27032 : selected 8 ⟨683839, by decide⟩
    (prefixPartial 13 364982) = some ⟨13, 2, 0, 683839, 364982, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_364982_683839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364982 ⟨683839, by decide⟩ :=
  accepted_of_selected 13 364982 ⟨683839, by decide⟩ ⟨13, 2, 0, 683839, 364982, 2229, 16384⟩
    (by decide) selected_cut_27032

theorem selected_cut_27033 : selected 8 ⟨683859, by decide⟩
    (prefixPartial 13 364983) = some ⟨13, 2, 0, 683859, 364983, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_364983_683859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364983 ⟨683859, by decide⟩ :=
  accepted_of_selected 13 364983 ⟨683859, by decide⟩ ⟨13, 2, 0, 683859, 364983, 1241, 16384⟩
    (by decide) selected_cut_27033

theorem unmarked_context_12_91245_683860 : frontier 9 ⟨683860, by decide⟩
    (prefixCache 12 91245) (prefixPartial 12 91245) = false := by
  decide +kernel

theorem node_context_12_91245_683860 : EJMOriginalGlobalDAGData.nodes 9 ⟨683860, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨683797, by decide⟩,⟨683839, by decide⟩,⟨683859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91245_683860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91245 ⟨683860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91245
    ⟨683860, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨683797, by decide⟩,⟨683839, by decide⟩,⟨683859, by decide⟩]) unmarked_context_12_91245_683860 node_context_12_91245_683860
  intro a
  fin_cases a
  · exact context_13_364980_3444
  · exact context_13_364981_683797
  · exact context_13_364982_683839
  · exact context_13_364983_683859

theorem selected_cut_27034 : selected 9 ⟨683901, by decide⟩
    (prefixPartial 12 91246) = some ⟨12, 2, 0, 683901, 91246, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_91246_683901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91246 ⟨683901, by decide⟩ :=
  accepted_of_selected 12 91246 ⟨683901, by decide⟩ ⟨12, 2, 0, 683901, 91246, 3285, 65536⟩
    (by decide) selected_cut_27034

theorem selected_cut_27035 : selected 9 ⟨683944, by decide⟩
    (prefixPartial 12 91247) = some ⟨12, 2, 0, 683944, 91247, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_91247_683944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91247 ⟨683944, by decide⟩ :=
  accepted_of_selected 12 91247 ⟨683944, by decide⟩ ⟨12, 2, 0, 683944, 91247, 2853, 65536⟩
    (by decide) selected_cut_27035

theorem unmarked_context_11_22811_683945 : frontier 10 ⟨683945, by decide⟩
    (prefixCache 11 22811) (prefixPartial 11 22811) = false := by
  decide +kernel

theorem node_context_11_22811_683945 : EJMOriginalGlobalDAGData.nodes 10 ⟨683945, by decide⟩ =
    .split (coordinate 11) (![⟨683768, by decide⟩,⟨683860, by decide⟩,⟨683901, by decide⟩,⟨683944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22811_683945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22811 ⟨683945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22811
    ⟨683945, by decide⟩ (by decide) (![⟨683768, by decide⟩,⟨683860, by decide⟩,⟨683901, by decide⟩,⟨683944, by decide⟩]) unmarked_context_11_22811_683945 node_context_11_22811_683945
  intro a
  fin_cases a
  · exact context_12_91244_683768
  · exact context_12_91245_683860
  · exact context_12_91246_683901
  · exact context_12_91247_683944

theorem unmarked_context_10_5702_683946 : frontier 11 ⟨683946, by decide⟩
    (prefixCache 10 5702) (prefixPartial 10 5702) = false := by
  decide +kernel

theorem node_context_10_5702_683946 : EJMOriginalGlobalDAGData.nodes 11 ⟨683946, by decide⟩ =
    .split (coordinate 10) (![⟨683381, by decide⟩,⟨683512, by decide⟩,⟨683730, by decide⟩,⟨683945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5702_683946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5702 ⟨683946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5702
    ⟨683946, by decide⟩ (by decide) (![⟨683381, by decide⟩,⟨683512, by decide⟩,⟨683730, by decide⟩,⟨683945, by decide⟩]) unmarked_context_10_5702_683946 node_context_10_5702_683946
  intro a
  fin_cases a
  · exact context_11_22808_683381
  · exact context_11_22809_683512
  · exact context_11_22810_683730
  · exact context_11_22811_683945

theorem selected_cut_27036 : selected 9 ⟨684084, by decide⟩
    (prefixPartial 12 91248) = some ⟨12, 2, 0, 684084, 91248, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_91248_684084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91248 ⟨684084, by decide⟩ :=
  accepted_of_selected 12 91248 ⟨684084, by decide⟩ ⟨12, 2, 0, 684084, 91248, 2497, 65536⟩
    (by decide) selected_cut_27036

theorem selected_cut_27037 : selected 9 ⟨684085, by decide⟩
    (prefixPartial 12 91249) = some ⟨12, 1, 0, 684085, 91249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91249_684085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91249 ⟨684085, by decide⟩ :=
  accepted_of_selected 12 91249 ⟨684085, by decide⟩ ⟨12, 1, 0, 684085, 91249, 1, 65536⟩
    (by decide) selected_cut_27037

theorem selected_cut_27038 : selected 9 ⟨684116, by decide⟩
    (prefixPartial 12 91250) = some ⟨12, 2, 0, 684116, 91250, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_91250_684116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91250 ⟨684116, by decide⟩ :=
  accepted_of_selected 12 91250 ⟨684116, by decide⟩ ⟨12, 2, 0, 684116, 91250, 2837, 65536⟩
    (by decide) selected_cut_27038

theorem selected_cut_27039 : selected 9 ⟨684166, by decide⟩
    (prefixPartial 12 91251) = some ⟨12, 2, 0, 684166, 91251, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_91251_684166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91251 ⟨684166, by decide⟩ :=
  accepted_of_selected 12 91251 ⟨684166, by decide⟩ ⟨12, 2, 0, 684166, 91251, 3169, 65536⟩
    (by decide) selected_cut_27039

theorem unmarked_context_11_22812_684167 : frontier 10 ⟨684167, by decide⟩
    (prefixCache 11 22812) (prefixPartial 11 22812) = false := by
  decide +kernel

theorem node_context_11_22812_684167 : EJMOriginalGlobalDAGData.nodes 10 ⟨684167, by decide⟩ =
    .split (coordinate 11) (![⟨684084, by decide⟩,⟨684085, by decide⟩,⟨684116, by decide⟩,⟨684166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22812_684167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22812 ⟨684167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22812
    ⟨684167, by decide⟩ (by decide) (![⟨684084, by decide⟩,⟨684085, by decide⟩,⟨684116, by decide⟩,⟨684166, by decide⟩]) unmarked_context_11_22812_684167 node_context_11_22812_684167
  intro a
  fin_cases a
  · exact context_12_91248_684084
  · exact context_12_91249_684085
  · exact context_12_91250_684116
  · exact context_12_91251_684166

theorem selected_cut_27040 : selected 9 ⟨684202, by decide⟩
    (prefixPartial 12 91252) = some ⟨12, 2, 0, 684202, 91252, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_91252_684202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91252 ⟨684202, by decide⟩ :=
  accepted_of_selected 12 91252 ⟨684202, by decide⟩ ⟨12, 2, 0, 684202, 91252, 2585, 65536⟩
    (by decide) selected_cut_27040

theorem selected_cut_27041 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 91253) = some ⟨12, 1, 0, 642794, 91253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91253_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91253 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 91253 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 91253, 1, 65536⟩
    (by decide) selected_cut_27041

theorem selected_cut_27042 : selected 9 ⟨684242, by decide⟩
    (prefixPartial 12 91254) = some ⟨12, 2, 0, 684242, 91254, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_91254_684242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91254 ⟨684242, by decide⟩ :=
  accepted_of_selected 12 91254 ⟨684242, by decide⟩ ⟨12, 2, 0, 684242, 91254, 2741, 65536⟩
    (by decide) selected_cut_27042

theorem selected_cut_27043 : selected 9 ⟨684280, by decide⟩
    (prefixPartial 12 91255) = some ⟨12, 2, 0, 684280, 91255, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_91255_684280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91255 ⟨684280, by decide⟩ :=
  accepted_of_selected 12 91255 ⟨684280, by decide⟩ ⟨12, 2, 0, 684280, 91255, 3085, 65536⟩
    (by decide) selected_cut_27043

theorem unmarked_context_11_22813_684281 : frontier 10 ⟨684281, by decide⟩
    (prefixCache 11 22813) (prefixPartial 11 22813) = false := by
  decide +kernel

theorem node_context_11_22813_684281 : EJMOriginalGlobalDAGData.nodes 10 ⟨684281, by decide⟩ =
    .split (coordinate 11) (![⟨684202, by decide⟩,⟨642794, by decide⟩,⟨684242, by decide⟩,⟨684280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22813_684281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22813 ⟨684281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22813
    ⟨684281, by decide⟩ (by decide) (![⟨684202, by decide⟩,⟨642794, by decide⟩,⟨684242, by decide⟩,⟨684280, by decide⟩]) unmarked_context_11_22813_684281 node_context_11_22813_684281
  intro a
  fin_cases a
  · exact context_12_91252_684202
  · exact context_12_91253_642794
  · exact context_12_91254_684242
  · exact context_12_91255_684280

theorem selected_cut_27044 : selected 9 ⟨684314, by decide⟩
    (prefixPartial 12 91256) = some ⟨12, 2, 0, 684314, 91256, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_91256_684314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91256 ⟨684314, by decide⟩ :=
  accepted_of_selected 12 91256 ⟨684314, by decide⟩ ⟨12, 2, 0, 684314, 91256, 2925, 65536⟩
    (by decide) selected_cut_27044

theorem selected_cut_27045 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 365028) = some ⟨13, 1, 0, 3444, 365028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_365028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 365028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 365028, 1, 16384⟩
    (by decide) selected_cut_27045

theorem selected_cut_27046 : selected 8 ⟨684326, by decide⟩
    (prefixPartial 13 365029) = some ⟨13, 2, 0, 684326, 365029, 577, 16384⟩ := by
  decide +kernel

theorem context_13_365029_684326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365029 ⟨684326, by decide⟩ :=
  accepted_of_selected 13 365029 ⟨684326, by decide⟩ ⟨13, 2, 0, 684326, 365029, 577, 16384⟩
    (by decide) selected_cut_27046

theorem selected_cut_27047 : selected 8 ⟨684378, by decide⟩
    (prefixPartial 13 365030) = some ⟨13, 2, 0, 684378, 365030, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_365030_684378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365030 ⟨684378, by decide⟩ :=
  accepted_of_selected 13 365030 ⟨684378, by decide⟩ ⟨13, 2, 0, 684378, 365030, 2645, 16384⟩
    (by decide) selected_cut_27047

theorem selected_cut_27048 : selected 8 ⟨684405, by decide⟩
    (prefixPartial 13 365031) = some ⟨13, 2, 0, 684405, 365031, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_365031_684405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 365031 ⟨684405, by decide⟩ :=
  accepted_of_selected 13 365031 ⟨684405, by decide⟩ ⟨13, 2, 0, 684405, 365031, 1181, 16384⟩
    (by decide) selected_cut_27048

theorem unmarked_context_12_91257_684406 : frontier 9 ⟨684406, by decide⟩
    (prefixCache 12 91257) (prefixPartial 12 91257) = false := by
  decide +kernel

theorem node_context_12_91257_684406 : EJMOriginalGlobalDAGData.nodes 9 ⟨684406, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨684326, by decide⟩,⟨684378, by decide⟩,⟨684405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91257_684406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91257 ⟨684406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91257
    ⟨684406, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨684326, by decide⟩,⟨684378, by decide⟩,⟨684405, by decide⟩]) unmarked_context_12_91257_684406 node_context_12_91257_684406
  intro a
  fin_cases a
  · exact context_13_365028_3444
  · exact context_13_365029_684326
  · exact context_13_365030_684378
  · exact context_13_365031_684405

theorem selected_cut_27049 : selected 9 ⟨684447, by decide⟩
    (prefixPartial 12 91258) = some ⟨12, 2, 0, 684447, 91258, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_91258_684447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91258 ⟨684447, by decide⟩ :=
  accepted_of_selected 12 91258 ⟨684447, by decide⟩ ⟨12, 2, 0, 684447, 91258, 2697, 65536⟩
    (by decide) selected_cut_27049

theorem selected_cut_27050 : selected 9 ⟨684491, by decide⟩
    (prefixPartial 12 91259) = some ⟨12, 2, 0, 684491, 91259, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_91259_684491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91259 ⟨684491, by decide⟩ :=
  accepted_of_selected 12 91259 ⟨684491, by decide⟩ ⟨12, 2, 0, 684491, 91259, 3089, 65536⟩
    (by decide) selected_cut_27050

theorem unmarked_context_11_22814_684492 : frontier 10 ⟨684492, by decide⟩
    (prefixCache 11 22814) (prefixPartial 11 22814) = false := by
  decide +kernel

theorem node_context_11_22814_684492 : EJMOriginalGlobalDAGData.nodes 10 ⟨684492, by decide⟩ =
    .split (coordinate 11) (![⟨684314, by decide⟩,⟨684406, by decide⟩,⟨684447, by decide⟩,⟨684491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22814_684492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22814 ⟨684492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22814
    ⟨684492, by decide⟩ (by decide) (![⟨684314, by decide⟩,⟨684406, by decide⟩,⟨684447, by decide⟩,⟨684491, by decide⟩]) unmarked_context_11_22814_684492 node_context_11_22814_684492
  intro a
  fin_cases a
  · exact context_12_91256_684314
  · exact context_12_91257_684406
  · exact context_12_91258_684447
  · exact context_12_91259_684491

theorem selected_cut_27051 : selected 9 ⟨684525, by decide⟩
    (prefixPartial 12 91260) = some ⟨12, 2, 0, 684525, 91260, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_91260_684525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91260 ⟨684525, by decide⟩ :=
  accepted_of_selected 12 91260 ⟨684525, by decide⟩ ⟨12, 2, 0, 684525, 91260, 2497, 65536⟩
    (by decide) selected_cut_27051

theorem selected_cut_27052 : selected 9 ⟨684578, by decide⟩
    (prefixPartial 12 91261) = some ⟨12, 2, 0, 684578, 91261, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_91261_684578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91261 ⟨684578, by decide⟩ :=
  accepted_of_selected 12 91261 ⟨684578, by decide⟩ ⟨12, 2, 0, 684578, 91261, 3741, 65536⟩
    (by decide) selected_cut_27052

theorem selected_cut_27053 : selected 9 ⟨684613, by decide⟩
    (prefixPartial 12 91262) = some ⟨12, 2, 0, 684613, 91262, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_91262_684613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91262 ⟨684613, by decide⟩ :=
  accepted_of_selected 12 91262 ⟨684613, by decide⟩ ⟨12, 2, 0, 684613, 91262, 2605, 65536⟩
    (by decide) selected_cut_27053

theorem selected_cut_27054 : selected 9 ⟨684637, by decide⟩
    (prefixPartial 12 91263) = some ⟨12, 2, 0, 684637, 91263, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_91263_684637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91263 ⟨684637, by decide⟩ :=
  accepted_of_selected 12 91263 ⟨684637, by decide⟩ ⟨12, 2, 0, 684637, 91263, 2545, 65536⟩
    (by decide) selected_cut_27054

theorem unmarked_context_11_22815_684638 : frontier 10 ⟨684638, by decide⟩
    (prefixCache 11 22815) (prefixPartial 11 22815) = false := by
  decide +kernel

theorem node_context_11_22815_684638 : EJMOriginalGlobalDAGData.nodes 10 ⟨684638, by decide⟩ =
    .split (coordinate 11) (![⟨684525, by decide⟩,⟨684578, by decide⟩,⟨684613, by decide⟩,⟨684637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22815_684638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22815 ⟨684638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22815
    ⟨684638, by decide⟩ (by decide) (![⟨684525, by decide⟩,⟨684578, by decide⟩,⟨684613, by decide⟩,⟨684637, by decide⟩]) unmarked_context_11_22815_684638 node_context_11_22815_684638
  intro a
  fin_cases a
  · exact context_12_91260_684525
  · exact context_12_91261_684578
  · exact context_12_91262_684613
  · exact context_12_91263_684637

theorem unmarked_context_10_5703_684639 : frontier 11 ⟨684639, by decide⟩
    (prefixCache 10 5703) (prefixPartial 10 5703) = false := by
  decide +kernel

theorem node_context_10_5703_684639 : EJMOriginalGlobalDAGData.nodes 11 ⟨684639, by decide⟩ =
    .split (coordinate 10) (![⟨684167, by decide⟩,⟨684281, by decide⟩,⟨684492, by decide⟩,⟨684638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5703_684639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5703 ⟨684639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5703
    ⟨684639, by decide⟩ (by decide) (![⟨684167, by decide⟩,⟨684281, by decide⟩,⟨684492, by decide⟩,⟨684638, by decide⟩]) unmarked_context_10_5703_684639 node_context_10_5703_684639
  intro a
  fin_cases a
  · exact context_11_22812_684167
  · exact context_11_22813_684281
  · exact context_11_22814_684492
  · exact context_11_22815_684638

theorem unmarked_context_9_1425_684640 : frontier 12 ⟨684640, by decide⟩
    (prefixCache 9 1425) (prefixPartial 9 1425) = false := by
  decide +kernel

theorem node_context_9_1425_684640 : EJMOriginalGlobalDAGData.nodes 12 ⟨684640, by decide⟩ =
    .split (coordinate 9) (![⟨682842, by decide⟩,⟨683193, by decide⟩,⟨683946, by decide⟩,⟨684639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1425_684640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1425 ⟨684640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1425
    ⟨684640, by decide⟩ (by decide) (![⟨682842, by decide⟩,⟨683193, by decide⟩,⟨683946, by decide⟩,⟨684639, by decide⟩]) unmarked_context_9_1425_684640 node_context_9_1425_684640
  intro a
  fin_cases a
  · exact context_10_5700_682842
  · exact context_10_5701_683193
  · exact context_10_5702_683946
  · exact context_10_5703_684639

theorem selected_cut_27055 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 91264) = some ⟨12, 1, 0, 450982, 91264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91264_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91264 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 91264 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 91264, 1, 65536⟩
    (by decide) selected_cut_27055

theorem selected_cut_27056 : selected 9 ⟨684664, by decide⟩
    (prefixPartial 12 91265) = some ⟨12, 2, 0, 684664, 91265, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_91265_684664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91265 ⟨684664, by decide⟩ :=
  accepted_of_selected 12 91265 ⟨684664, by decide⟩ ⟨12, 2, 0, 684664, 91265, 1797, 65536⟩
    (by decide) selected_cut_27056

theorem selected_cut_27057 : selected 9 ⟨684682, by decide⟩
    (prefixPartial 12 91266) = some ⟨12, 2, 0, 684682, 91266, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_91266_684682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91266 ⟨684682, by decide⟩ :=
  accepted_of_selected 12 91266 ⟨684682, by decide⟩ ⟨12, 2, 0, 684682, 91266, 1677, 65536⟩
    (by decide) selected_cut_27057

theorem selected_cut_27058 : selected 9 ⟨684702, by decide⟩
    (prefixPartial 12 91267) = some ⟨12, 2, 0, 684702, 91267, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_91267_684702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91267 ⟨684702, by decide⟩ :=
  accepted_of_selected 12 91267 ⟨684702, by decide⟩ ⟨12, 2, 0, 684702, 91267, 1797, 65536⟩
    (by decide) selected_cut_27058

theorem unmarked_context_11_22816_684703 : frontier 10 ⟨684703, by decide⟩
    (prefixCache 11 22816) (prefixPartial 11 22816) = false := by
  decide +kernel

theorem node_context_11_22816_684703 : EJMOriginalGlobalDAGData.nodes 10 ⟨684703, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨684664, by decide⟩,⟨684682, by decide⟩,⟨684702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22816_684703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22816 ⟨684703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22816
    ⟨684703, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨684664, by decide⟩,⟨684682, by decide⟩,⟨684702, by decide⟩]) unmarked_context_11_22816_684703 node_context_11_22816_684703
  intro a
  fin_cases a
  · exact context_12_91264_450982
  · exact context_12_91265_684664
  · exact context_12_91266_684682
  · exact context_12_91267_684702

theorem selected_cut_27059 : selected 9 ⟨684724, by decide⟩
    (prefixPartial 12 91268) = some ⟨12, 2, 0, 684724, 91268, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_91268_684724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91268 ⟨684724, by decide⟩ :=
  accepted_of_selected 12 91268 ⟨684724, by decide⟩ ⟨12, 2, 0, 684724, 91268, 1669, 65536⟩
    (by decide) selected_cut_27059

theorem selected_cut_27060 : selected 9 ⟨684749, by decide⟩
    (prefixPartial 12 91269) = some ⟨12, 2, 0, 684749, 91269, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_91269_684749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91269 ⟨684749, by decide⟩ :=
  accepted_of_selected 12 91269 ⟨684749, by decide⟩ ⟨12, 2, 0, 684749, 91269, 1849, 65536⟩
    (by decide) selected_cut_27060

theorem selected_cut_27061 : selected 9 ⟨684777, by decide⟩
    (prefixPartial 12 91270) = some ⟨12, 2, 0, 684777, 91270, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_91270_684777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91270 ⟨684777, by decide⟩ :=
  accepted_of_selected 12 91270 ⟨684777, by decide⟩ ⟨12, 2, 0, 684777, 91270, 1813, 65536⟩
    (by decide) selected_cut_27061

theorem selected_cut_27062 : selected 9 ⟨684798, by decide⟩
    (prefixPartial 12 91271) = some ⟨12, 2, 0, 684798, 91271, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_91271_684798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91271 ⟨684798, by decide⟩ :=
  accepted_of_selected 12 91271 ⟨684798, by decide⟩ ⟨12, 2, 0, 684798, 91271, 1941, 65536⟩
    (by decide) selected_cut_27062

theorem unmarked_context_11_22817_684799 : frontier 10 ⟨684799, by decide⟩
    (prefixCache 11 22817) (prefixPartial 11 22817) = false := by
  decide +kernel

theorem node_context_11_22817_684799 : EJMOriginalGlobalDAGData.nodes 10 ⟨684799, by decide⟩ =
    .split (coordinate 11) (![⟨684724, by decide⟩,⟨684749, by decide⟩,⟨684777, by decide⟩,⟨684798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22817_684799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22817 ⟨684799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22817
    ⟨684799, by decide⟩ (by decide) (![⟨684724, by decide⟩,⟨684749, by decide⟩,⟨684777, by decide⟩,⟨684798, by decide⟩]) unmarked_context_11_22817_684799 node_context_11_22817_684799
  intro a
  fin_cases a
  · exact context_12_91268_684724
  · exact context_12_91269_684749
  · exact context_12_91270_684777
  · exact context_12_91271_684798

theorem selected_cut_27063 : selected 9 ⟨684834, by decide⟩
    (prefixPartial 12 91272) = some ⟨12, 2, 0, 684834, 91272, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_91272_684834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91272 ⟨684834, by decide⟩ :=
  accepted_of_selected 12 91272 ⟨684834, by decide⟩ ⟨12, 2, 0, 684834, 91272, 1981, 65536⟩
    (by decide) selected_cut_27063

theorem selected_cut_27064 : selected 9 ⟨684876, by decide⟩
    (prefixPartial 12 91273) = some ⟨12, 2, 0, 684876, 91273, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_91273_684876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91273 ⟨684876, by decide⟩ :=
  accepted_of_selected 12 91273 ⟨684876, by decide⟩ ⟨12, 2, 0, 684876, 91273, 2357, 65536⟩
    (by decide) selected_cut_27064

theorem selected_cut_27065 : selected 9 ⟨684907, by decide⟩
    (prefixPartial 12 91274) = some ⟨12, 2, 0, 684907, 91274, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_91274_684907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91274 ⟨684907, by decide⟩ :=
  accepted_of_selected 12 91274 ⟨684907, by decide⟩ ⟨12, 2, 0, 684907, 91274, 2013, 65536⟩
    (by decide) selected_cut_27065

theorem selected_cut_27066 : selected 9 ⟨684934, by decide⟩
    (prefixPartial 12 91275) = some ⟨12, 2, 0, 684934, 91275, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_91275_684934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91275 ⟨684934, by decide⟩ :=
  accepted_of_selected 12 91275 ⟨684934, by decide⟩ ⟨12, 2, 0, 684934, 91275, 2149, 65536⟩
    (by decide) selected_cut_27066

theorem unmarked_context_11_22818_684935 : frontier 10 ⟨684935, by decide⟩
    (prefixCache 11 22818) (prefixPartial 11 22818) = false := by
  decide +kernel

theorem node_context_11_22818_684935 : EJMOriginalGlobalDAGData.nodes 10 ⟨684935, by decide⟩ =
    .split (coordinate 11) (![⟨684834, by decide⟩,⟨684876, by decide⟩,⟨684907, by decide⟩,⟨684934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22818_684935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22818 ⟨684935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22818
    ⟨684935, by decide⟩ (by decide) (![⟨684834, by decide⟩,⟨684876, by decide⟩,⟨684907, by decide⟩,⟨684934, by decide⟩]) unmarked_context_11_22818_684935 node_context_11_22818_684935
  intro a
  fin_cases a
  · exact context_12_91272_684834
  · exact context_12_91273_684876
  · exact context_12_91274_684907
  · exact context_12_91275_684934

theorem selected_cut_27067 : selected 9 ⟨684961, by decide⟩
    (prefixPartial 12 91276) = some ⟨12, 2, 0, 684961, 91276, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_91276_684961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91276 ⟨684961, by decide⟩ :=
  accepted_of_selected 12 91276 ⟨684961, by decide⟩ ⟨12, 2, 0, 684961, 91276, 1593, 65536⟩
    (by decide) selected_cut_27067

theorem selected_cut_27068 : selected 9 ⟨684992, by decide⟩
    (prefixPartial 12 91277) = some ⟨12, 2, 0, 684992, 91277, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_91277_684992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91277 ⟨684992, by decide⟩ :=
  accepted_of_selected 12 91277 ⟨684992, by decide⟩ ⟨12, 2, 0, 684992, 91277, 1845, 65536⟩
    (by decide) selected_cut_27068

theorem selected_cut_27069 : selected 9 ⟨685018, by decide⟩
    (prefixPartial 12 91278) = some ⟨12, 2, 0, 685018, 91278, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_91278_685018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91278 ⟨685018, by decide⟩ :=
  accepted_of_selected 12 91278 ⟨685018, by decide⟩ ⟨12, 2, 0, 685018, 91278, 1841, 65536⟩
    (by decide) selected_cut_27069

theorem selected_cut_27070 : selected 9 ⟨685039, by decide⟩
    (prefixPartial 12 91279) = some ⟨12, 2, 0, 685039, 91279, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_91279_685039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91279 ⟨685039, by decide⟩ :=
  accepted_of_selected 12 91279 ⟨685039, by decide⟩ ⟨12, 2, 0, 685039, 91279, 1717, 65536⟩
    (by decide) selected_cut_27070

theorem unmarked_context_11_22819_685040 : frontier 10 ⟨685040, by decide⟩
    (prefixCache 11 22819) (prefixPartial 11 22819) = false := by
  decide +kernel

theorem node_context_11_22819_685040 : EJMOriginalGlobalDAGData.nodes 10 ⟨685040, by decide⟩ =
    .split (coordinate 11) (![⟨684961, by decide⟩,⟨684992, by decide⟩,⟨685018, by decide⟩,⟨685039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22819_685040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22819 ⟨685040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22819
    ⟨685040, by decide⟩ (by decide) (![⟨684961, by decide⟩,⟨684992, by decide⟩,⟨685018, by decide⟩,⟨685039, by decide⟩]) unmarked_context_11_22819_685040 node_context_11_22819_685040
  intro a
  fin_cases a
  · exact context_12_91276_684961
  · exact context_12_91277_684992
  · exact context_12_91278_685018
  · exact context_12_91279_685039

theorem unmarked_context_10_5704_685041 : frontier 11 ⟨685041, by decide⟩
    (prefixCache 10 5704) (prefixPartial 10 5704) = false := by
  decide +kernel

theorem node_context_10_5704_685041 : EJMOriginalGlobalDAGData.nodes 11 ⟨685041, by decide⟩ =
    .split (coordinate 10) (![⟨684703, by decide⟩,⟨684799, by decide⟩,⟨684935, by decide⟩,⟨685040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5704_685041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5704 ⟨685041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5704
    ⟨685041, by decide⟩ (by decide) (![⟨684703, by decide⟩,⟨684799, by decide⟩,⟨684935, by decide⟩,⟨685040, by decide⟩]) unmarked_context_10_5704_685041 node_context_10_5704_685041
  intro a
  fin_cases a
  · exact context_11_22816_684703
  · exact context_11_22817_684799
  · exact context_11_22818_684935
  · exact context_11_22819_685040

theorem selected_cut_27071 : selected 9 ⟨685077, by decide⟩
    (prefixPartial 12 91280) = some ⟨12, 2, 0, 685077, 91280, 929, 65536⟩ := by
  decide +kernel

theorem context_12_91280_685077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91280 ⟨685077, by decide⟩ :=
  accepted_of_selected 12 91280 ⟨685077, by decide⟩ ⟨12, 2, 0, 685077, 91280, 929, 65536⟩
    (by decide) selected_cut_27071

theorem selected_cut_27072 : selected 9 ⟨685103, by decide⟩
    (prefixPartial 12 91281) = some ⟨12, 2, 0, 685103, 91281, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_91281_685103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91281 ⟨685103, by decide⟩ :=
  accepted_of_selected 12 91281 ⟨685103, by decide⟩ ⟨12, 2, 0, 685103, 91281, 2097, 65536⟩
    (by decide) selected_cut_27072

theorem selected_cut_27073 : selected 9 ⟨685131, by decide⟩
    (prefixPartial 12 91282) = some ⟨12, 2, 0, 685131, 91282, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_91282_685131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91282 ⟨685131, by decide⟩ :=
  accepted_of_selected 12 91282 ⟨685131, by decide⟩ ⟨12, 2, 0, 685131, 91282, 2125, 65536⟩
    (by decide) selected_cut_27073

theorem selected_cut_27074 : selected 9 ⟨685154, by decide⟩
    (prefixPartial 12 91283) = some ⟨12, 2, 0, 685154, 91283, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_91283_685154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91283 ⟨685154, by decide⟩ :=
  accepted_of_selected 12 91283 ⟨685154, by decide⟩ ⟨12, 2, 0, 685154, 91283, 2077, 65536⟩
    (by decide) selected_cut_27074

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
