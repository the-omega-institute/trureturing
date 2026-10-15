/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover342
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32932 : selected 8 ⟨848031, by decide⟩
    (prefixPartial 13 439462) = some ⟨13, 2, 0, 848031, 439462, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_439462_848031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439462 ⟨848031, by decide⟩ :=
  accepted_of_selected 13 439462 ⟨848031, by decide⟩ ⟨13, 2, 0, 848031, 439462, 1545, 16384⟩
    (by decide) selected_cut_32932

theorem selected_cut_32933 : selected 8 ⟨848040, by decide⟩
    (prefixPartial 13 439463) = some ⟨13, 2, 0, 848040, 439463, 741, 16384⟩ := by
  decide +kernel

theorem context_13_439463_848040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439463 ⟨848040, by decide⟩ :=
  accepted_of_selected 13 439463 ⟨848040, by decide⟩ ⟨13, 2, 0, 848040, 439463, 741, 16384⟩
    (by decide) selected_cut_32933

theorem unmarked_context_12_109865_848041 : frontier 9 ⟨848041, by decide⟩
    (prefixCache 12 109865) (prefixPartial 12 109865) = false := by
  decide +kernel

theorem node_context_12_109865_848041 : EJMOriginalGlobalDAGData.nodes 9 ⟨848041, by decide⟩ =
    .split (coordinate 12) (![⟨847980, by decide⟩,⟨848004, by decide⟩,⟨848031, by decide⟩,⟨848040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109865_848041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109865 ⟨848041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109865
    ⟨848041, by decide⟩ (by decide) (![⟨847980, by decide⟩,⟨848004, by decide⟩,⟨848031, by decide⟩,⟨848040, by decide⟩]) unmarked_context_12_109865_848041 node_context_12_109865_848041
  intro a
  fin_cases a
  · exact context_13_439460_847980
  · exact context_13_439461_848004
  · exact context_13_439462_848031
  · exact context_13_439463_848040

theorem selected_cut_32934 : selected 8 ⟨848056, by decide⟩
    (prefixPartial 13 439464) = some ⟨13, 2, 0, 848056, 439464, 945, 16384⟩ := by
  decide +kernel

theorem context_13_439464_848056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439464 ⟨848056, by decide⟩ :=
  accepted_of_selected 13 439464 ⟨848056, by decide⟩ ⟨13, 2, 0, 848056, 439464, 945, 16384⟩
    (by decide) selected_cut_32934

theorem selected_cut_32935 : selected 8 ⟨848080, by decide⟩
    (prefixPartial 13 439465) = some ⟨13, 2, 0, 848080, 439465, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_439465_848080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439465 ⟨848080, by decide⟩ :=
  accepted_of_selected 13 439465 ⟨848080, by decide⟩ ⟨13, 2, 0, 848080, 439465, 2325, 16384⟩
    (by decide) selected_cut_32935

theorem selected_cut_32936 : selected 8 ⟨848100, by decide⟩
    (prefixPartial 13 439466) = some ⟨13, 2, 0, 848100, 439466, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_439466_848100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439466 ⟨848100, by decide⟩ :=
  accepted_of_selected 13 439466 ⟨848100, by decide⟩ ⟨13, 2, 0, 848100, 439466, 1189, 16384⟩
    (by decide) selected_cut_32936

theorem selected_cut_32937 : selected 8 ⟨848107, by decide⟩
    (prefixPartial 13 439467) = some ⟨13, 2, 0, 848107, 439467, 769, 16384⟩ := by
  decide +kernel

theorem context_13_439467_848107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439467 ⟨848107, by decide⟩ :=
  accepted_of_selected 13 439467 ⟨848107, by decide⟩ ⟨13, 2, 0, 848107, 439467, 769, 16384⟩
    (by decide) selected_cut_32937

theorem unmarked_context_12_109866_848108 : frontier 9 ⟨848108, by decide⟩
    (prefixCache 12 109866) (prefixPartial 12 109866) = false := by
  decide +kernel

theorem node_context_12_109866_848108 : EJMOriginalGlobalDAGData.nodes 9 ⟨848108, by decide⟩ =
    .split (coordinate 12) (![⟨848056, by decide⟩,⟨848080, by decide⟩,⟨848100, by decide⟩,⟨848107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109866_848108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109866 ⟨848108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109866
    ⟨848108, by decide⟩ (by decide) (![⟨848056, by decide⟩,⟨848080, by decide⟩,⟨848100, by decide⟩,⟨848107, by decide⟩]) unmarked_context_12_109866_848108 node_context_12_109866_848108
  intro a
  fin_cases a
  · exact context_13_439464_848056
  · exact context_13_439465_848080
  · exact context_13_439466_848100
  · exact context_13_439467_848107

theorem selected_cut_32938 : selected 8 ⟨848128, by decide⟩
    (prefixPartial 13 439468) = some ⟨13, 2, 0, 848128, 439468, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_439468_848128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439468 ⟨848128, by decide⟩ :=
  accepted_of_selected 13 439468 ⟨848128, by decide⟩ ⟨13, 2, 0, 848128, 439468, 1033, 16384⟩
    (by decide) selected_cut_32938

theorem selected_cut_32939 : selected 8 ⟨848156, by decide⟩
    (prefixPartial 13 439469) = some ⟨13, 2, 0, 848156, 439469, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_439469_848156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439469 ⟨848156, by decide⟩ :=
  accepted_of_selected 13 439469 ⟨848156, by decide⟩ ⟨13, 2, 0, 848156, 439469, 2657, 16384⟩
    (by decide) selected_cut_32939

theorem selected_cut_32940 : selected 8 ⟨848186, by decide⟩
    (prefixPartial 13 439470) = some ⟨13, 2, 0, 848186, 439470, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_439470_848186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439470 ⟨848186, by decide⟩ :=
  accepted_of_selected 13 439470 ⟨848186, by decide⟩ ⟨13, 2, 0, 848186, 439470, 1629, 16384⟩
    (by decide) selected_cut_32940

theorem selected_cut_32941 : selected 8 ⟨848196, by decide⟩
    (prefixPartial 13 439471) = some ⟨13, 2, 0, 848196, 439471, 753, 16384⟩ := by
  decide +kernel

theorem context_13_439471_848196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439471 ⟨848196, by decide⟩ :=
  accepted_of_selected 13 439471 ⟨848196, by decide⟩ ⟨13, 2, 0, 848196, 439471, 753, 16384⟩
    (by decide) selected_cut_32941

theorem unmarked_context_12_109867_848197 : frontier 9 ⟨848197, by decide⟩
    (prefixCache 12 109867) (prefixPartial 12 109867) = false := by
  decide +kernel

theorem node_context_12_109867_848197 : EJMOriginalGlobalDAGData.nodes 9 ⟨848197, by decide⟩ =
    .split (coordinate 12) (![⟨848128, by decide⟩,⟨848156, by decide⟩,⟨848186, by decide⟩,⟨848196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109867_848197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109867 ⟨848197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109867
    ⟨848197, by decide⟩ (by decide) (![⟨848128, by decide⟩,⟨848156, by decide⟩,⟨848186, by decide⟩,⟨848196, by decide⟩]) unmarked_context_12_109867_848197 node_context_12_109867_848197
  intro a
  fin_cases a
  · exact context_13_439468_848128
  · exact context_13_439469_848156
  · exact context_13_439470_848186
  · exact context_13_439471_848196

theorem unmarked_context_11_27466_848198 : frontier 10 ⟨848198, by decide⟩
    (prefixCache 11 27466) (prefixPartial 11 27466) = false := by
  decide +kernel

theorem node_context_11_27466_848198 : EJMOriginalGlobalDAGData.nodes 10 ⟨848198, by decide⟩ =
    .split (coordinate 11) (![⟨847967, by decide⟩,⟨848041, by decide⟩,⟨848108, by decide⟩,⟨848197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27466_848198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27466 ⟨848198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27466
    ⟨848198, by decide⟩ (by decide) (![⟨847967, by decide⟩,⟨848041, by decide⟩,⟨848108, by decide⟩,⟨848197, by decide⟩]) unmarked_context_11_27466_848198 node_context_11_27466_848198
  intro a
  fin_cases a
  · exact context_12_109864_847967
  · exact context_12_109865_848041
  · exact context_12_109866_848108
  · exact context_12_109867_848197

theorem selected_cut_32942 : selected 8 ⟨848208, by decide⟩
    (prefixPartial 13 439472) = some ⟨13, 2, 0, 848208, 439472, 673, 16384⟩ := by
  decide +kernel

theorem context_13_439472_848208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439472 ⟨848208, by decide⟩ :=
  accepted_of_selected 13 439472 ⟨848208, by decide⟩ ⟨13, 2, 0, 848208, 439472, 673, 16384⟩
    (by decide) selected_cut_32942

theorem selected_cut_32943 : selected 8 ⟨848240, by decide⟩
    (prefixPartial 13 439473) = some ⟨13, 2, 0, 848240, 439473, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_439473_848240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439473 ⟨848240, by decide⟩ :=
  accepted_of_selected 13 439473 ⟨848240, by decide⟩ ⟨13, 2, 0, 848240, 439473, 2557, 16384⟩
    (by decide) selected_cut_32943

theorem selected_cut_32944 : selected 8 ⟨848265, by decide⟩
    (prefixPartial 13 439474) = some ⟨13, 2, 0, 848265, 439474, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_439474_848265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439474 ⟨848265, by decide⟩ :=
  accepted_of_selected 13 439474 ⟨848265, by decide⟩ ⟨13, 2, 0, 848265, 439474, 1405, 16384⟩
    (by decide) selected_cut_32944

theorem selected_cut_32945 : selected 8 ⟨848279, by decide⟩
    (prefixPartial 13 439475) = some ⟨13, 2, 0, 848279, 439475, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_439475_848279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439475 ⟨848279, by decide⟩ :=
  accepted_of_selected 13 439475 ⟨848279, by decide⟩ ⟨13, 2, 0, 848279, 439475, 1021, 16384⟩
    (by decide) selected_cut_32945

theorem unmarked_context_12_109868_848280 : frontier 9 ⟨848280, by decide⟩
    (prefixCache 12 109868) (prefixPartial 12 109868) = false := by
  decide +kernel

theorem node_context_12_109868_848280 : EJMOriginalGlobalDAGData.nodes 9 ⟨848280, by decide⟩ =
    .split (coordinate 12) (![⟨848208, by decide⟩,⟨848240, by decide⟩,⟨848265, by decide⟩,⟨848279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109868_848280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109868 ⟨848280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109868
    ⟨848280, by decide⟩ (by decide) (![⟨848208, by decide⟩,⟨848240, by decide⟩,⟨848265, by decide⟩,⟨848279, by decide⟩]) unmarked_context_12_109868_848280 node_context_12_109868_848280
  intro a
  fin_cases a
  · exact context_13_439472_848208
  · exact context_13_439473_848240
  · exact context_13_439474_848265
  · exact context_13_439475_848279

theorem selected_cut_32946 : selected 8 ⟨848292, by decide⟩
    (prefixPartial 13 439476) = some ⟨13, 2, 0, 848292, 439476, 725, 16384⟩ := by
  decide +kernel

theorem context_13_439476_848292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439476 ⟨848292, by decide⟩ :=
  accepted_of_selected 13 439476 ⟨848292, by decide⟩ ⟨13, 2, 0, 848292, 439476, 725, 16384⟩
    (by decide) selected_cut_32946

theorem selected_cut_32947 : selected 8 ⟨848322, by decide⟩
    (prefixPartial 13 439477) = some ⟨13, 2, 0, 848322, 439477, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_439477_848322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439477 ⟨848322, by decide⟩ :=
  accepted_of_selected 13 439477 ⟨848322, by decide⟩ ⟨13, 2, 0, 848322, 439477, 2625, 16384⟩
    (by decide) selected_cut_32947

theorem selected_cut_32948 : selected 8 ⟨848346, by decide⟩
    (prefixPartial 13 439478) = some ⟨13, 2, 0, 848346, 439478, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_439478_848346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439478 ⟨848346, by decide⟩ :=
  accepted_of_selected 13 439478 ⟨848346, by decide⟩ ⟨13, 2, 0, 848346, 439478, 1533, 16384⟩
    (by decide) selected_cut_32948

theorem selected_cut_32949 : selected 8 ⟨848355, by decide⟩
    (prefixPartial 13 439479) = some ⟨13, 2, 0, 848355, 439479, 953, 16384⟩ := by
  decide +kernel

theorem context_13_439479_848355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439479 ⟨848355, by decide⟩ :=
  accepted_of_selected 13 439479 ⟨848355, by decide⟩ ⟨13, 2, 0, 848355, 439479, 953, 16384⟩
    (by decide) selected_cut_32949

theorem unmarked_context_12_109869_848356 : frontier 9 ⟨848356, by decide⟩
    (prefixCache 12 109869) (prefixPartial 12 109869) = false := by
  decide +kernel

theorem node_context_12_109869_848356 : EJMOriginalGlobalDAGData.nodes 9 ⟨848356, by decide⟩ =
    .split (coordinate 12) (![⟨848292, by decide⟩,⟨848322, by decide⟩,⟨848346, by decide⟩,⟨848355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109869_848356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109869 ⟨848356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109869
    ⟨848356, by decide⟩ (by decide) (![⟨848292, by decide⟩,⟨848322, by decide⟩,⟨848346, by decide⟩,⟨848355, by decide⟩]) unmarked_context_12_109869_848356 node_context_12_109869_848356
  intro a
  fin_cases a
  · exact context_13_439476_848292
  · exact context_13_439477_848322
  · exact context_13_439478_848346
  · exact context_13_439479_848355

theorem selected_cut_32950 : selected 8 ⟨848373, by decide⟩
    (prefixPartial 13 439480) = some ⟨13, 2, 0, 848373, 439480, 621, 16384⟩ := by
  decide +kernel

theorem context_13_439480_848373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439480 ⟨848373, by decide⟩ :=
  accepted_of_selected 13 439480 ⟨848373, by decide⟩ ⟨13, 2, 0, 848373, 439480, 621, 16384⟩
    (by decide) selected_cut_32950

theorem selected_cut_32951 : selected 8 ⟨848404, by decide⟩
    (prefixPartial 13 439481) = some ⟨13, 2, 0, 848404, 439481, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_439481_848404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439481 ⟨848404, by decide⟩ :=
  accepted_of_selected 13 439481 ⟨848404, by decide⟩ ⟨13, 2, 0, 848404, 439481, 2469, 16384⟩
    (by decide) selected_cut_32951

theorem selected_cut_32952 : selected 8 ⟨848421, by decide⟩
    (prefixPartial 13 439482) = some ⟨13, 2, 0, 848421, 439482, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_439482_848421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439482 ⟨848421, by decide⟩ :=
  accepted_of_selected 13 439482 ⟨848421, by decide⟩ ⟨13, 2, 0, 848421, 439482, 1197, 16384⟩
    (by decide) selected_cut_32952

theorem selected_cut_32953 : selected 8 ⟨848428, by decide⟩
    (prefixPartial 13 439483) = some ⟨13, 2, 0, 848428, 439483, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_439483_848428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439483 ⟨848428, by decide⟩ :=
  accepted_of_selected 13 439483 ⟨848428, by decide⟩ ⟨13, 2, 0, 848428, 439483, 1013, 16384⟩
    (by decide) selected_cut_32953

theorem unmarked_context_12_109870_848429 : frontier 9 ⟨848429, by decide⟩
    (prefixCache 12 109870) (prefixPartial 12 109870) = false := by
  decide +kernel

theorem node_context_12_109870_848429 : EJMOriginalGlobalDAGData.nodes 9 ⟨848429, by decide⟩ =
    .split (coordinate 12) (![⟨848373, by decide⟩,⟨848404, by decide⟩,⟨848421, by decide⟩,⟨848428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109870_848429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109870 ⟨848429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109870
    ⟨848429, by decide⟩ (by decide) (![⟨848373, by decide⟩,⟨848404, by decide⟩,⟨848421, by decide⟩,⟨848428, by decide⟩]) unmarked_context_12_109870_848429 node_context_12_109870_848429
  intro a
  fin_cases a
  · exact context_13_439480_848373
  · exact context_13_439481_848404
  · exact context_13_439482_848421
  · exact context_13_439483_848428

theorem selected_cut_32954 : selected 8 ⟨848442, by decide⟩
    (prefixPartial 13 439484) = some ⟨13, 2, 0, 848442, 439484, 693, 16384⟩ := by
  decide +kernel

theorem context_13_439484_848442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439484 ⟨848442, by decide⟩ :=
  accepted_of_selected 13 439484 ⟨848442, by decide⟩ ⟨13, 2, 0, 848442, 439484, 693, 16384⟩
    (by decide) selected_cut_32954

theorem selected_cut_32955 : selected 8 ⟨848481, by decide⟩
    (prefixPartial 13 439485) = some ⟨13, 2, 0, 848481, 439485, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_439485_848481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439485 ⟨848481, by decide⟩ :=
  accepted_of_selected 13 439485 ⟨848481, by decide⟩ ⟨13, 2, 0, 848481, 439485, 2785, 16384⟩
    (by decide) selected_cut_32955

theorem selected_cut_32956 : selected 8 ⟨848510, by decide⟩
    (prefixPartial 13 439486) = some ⟨13, 2, 0, 848510, 439486, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_439486_848510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439486 ⟨848510, by decide⟩ :=
  accepted_of_selected 13 439486 ⟨848510, by decide⟩ ⟨13, 2, 0, 848510, 439486, 1677, 16384⟩
    (by decide) selected_cut_32956

theorem selected_cut_32957 : selected 8 ⟨848517, by decide⟩
    (prefixPartial 13 439487) = some ⟨13, 2, 0, 848517, 439487, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_439487_848517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439487 ⟨848517, by decide⟩ :=
  accepted_of_selected 13 439487 ⟨848517, by decide⟩ ⟨13, 2, 0, 848517, 439487, 1053, 16384⟩
    (by decide) selected_cut_32957

theorem unmarked_context_12_109871_848518 : frontier 9 ⟨848518, by decide⟩
    (prefixCache 12 109871) (prefixPartial 12 109871) = false := by
  decide +kernel

theorem node_context_12_109871_848518 : EJMOriginalGlobalDAGData.nodes 9 ⟨848518, by decide⟩ =
    .split (coordinate 12) (![⟨848442, by decide⟩,⟨848481, by decide⟩,⟨848510, by decide⟩,⟨848517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109871_848518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109871 ⟨848518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109871
    ⟨848518, by decide⟩ (by decide) (![⟨848442, by decide⟩,⟨848481, by decide⟩,⟨848510, by decide⟩,⟨848517, by decide⟩]) unmarked_context_12_109871_848518 node_context_12_109871_848518
  intro a
  fin_cases a
  · exact context_13_439484_848442
  · exact context_13_439485_848481
  · exact context_13_439486_848510
  · exact context_13_439487_848517

theorem unmarked_context_11_27467_848519 : frontier 10 ⟨848519, by decide⟩
    (prefixCache 11 27467) (prefixPartial 11 27467) = false := by
  decide +kernel

theorem node_context_11_27467_848519 : EJMOriginalGlobalDAGData.nodes 10 ⟨848519, by decide⟩ =
    .split (coordinate 11) (![⟨848280, by decide⟩,⟨848356, by decide⟩,⟨848429, by decide⟩,⟨848518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27467_848519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27467 ⟨848519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27467
    ⟨848519, by decide⟩ (by decide) (![⟨848280, by decide⟩,⟨848356, by decide⟩,⟨848429, by decide⟩,⟨848518, by decide⟩]) unmarked_context_11_27467_848519 node_context_11_27467_848519
  intro a
  fin_cases a
  · exact context_12_109868_848280
  · exact context_12_109869_848356
  · exact context_12_109870_848429
  · exact context_12_109871_848518

theorem unmarked_context_10_6866_848520 : frontier 11 ⟨848520, by decide⟩
    (prefixCache 10 6866) (prefixPartial 10 6866) = false := by
  decide +kernel

theorem node_context_10_6866_848520 : EJMOriginalGlobalDAGData.nodes 11 ⟨848520, by decide⟩ =
    .split (coordinate 10) (![⟨847312, by decide⟩,⟨847887, by decide⟩,⟨848198, by decide⟩,⟨848519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6866_848520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6866 ⟨848520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6866
    ⟨848520, by decide⟩ (by decide) (![⟨847312, by decide⟩,⟨847887, by decide⟩,⟨848198, by decide⟩,⟨848519, by decide⟩]) unmarked_context_10_6866_848520 node_context_10_6866_848520
  intro a
  fin_cases a
  · exact context_11_27464_847312
  · exact context_11_27465_847887
  · exact context_11_27466_848198
  · exact context_11_27467_848519

theorem selected_cut_32958 : selected 8 ⟨848530, by decide⟩
    (prefixPartial 13 439488) = some ⟨13, 2, 0, 848530, 439488, 641, 16384⟩ := by
  decide +kernel

theorem context_13_439488_848530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439488 ⟨848530, by decide⟩ :=
  accepted_of_selected 13 439488 ⟨848530, by decide⟩ ⟨13, 2, 0, 848530, 439488, 641, 16384⟩
    (by decide) selected_cut_32958

theorem selected_cut_32959 : selected 8 ⟨848560, by decide⟩
    (prefixPartial 13 439489) = some ⟨13, 2, 0, 848560, 439489, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_439489_848560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439489 ⟨848560, by decide⟩ :=
  accepted_of_selected 13 439489 ⟨848560, by decide⟩ ⟨13, 2, 0, 848560, 439489, 2329, 16384⟩
    (by decide) selected_cut_32959

theorem selected_cut_32960 : selected 8 ⟨848578, by decide⟩
    (prefixPartial 13 439490) = some ⟨13, 2, 0, 848578, 439490, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_439490_848578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439490 ⟨848578, by decide⟩ :=
  accepted_of_selected 13 439490 ⟨848578, by decide⟩ ⟨13, 2, 0, 848578, 439490, 1129, 16384⟩
    (by decide) selected_cut_32960

theorem selected_cut_32961 : selected 8 ⟨848585, by decide⟩
    (prefixPartial 13 439491) = some ⟨13, 2, 0, 848585, 439491, 653, 16384⟩ := by
  decide +kernel

theorem context_13_439491_848585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439491 ⟨848585, by decide⟩ :=
  accepted_of_selected 13 439491 ⟨848585, by decide⟩ ⟨13, 2, 0, 848585, 439491, 653, 16384⟩
    (by decide) selected_cut_32961

theorem unmarked_context_12_109872_848586 : frontier 9 ⟨848586, by decide⟩
    (prefixCache 12 109872) (prefixPartial 12 109872) = false := by
  decide +kernel

theorem node_context_12_109872_848586 : EJMOriginalGlobalDAGData.nodes 9 ⟨848586, by decide⟩ =
    .split (coordinate 12) (![⟨848530, by decide⟩,⟨848560, by decide⟩,⟨848578, by decide⟩,⟨848585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109872_848586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109872 ⟨848586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109872
    ⟨848586, by decide⟩ (by decide) (![⟨848530, by decide⟩,⟨848560, by decide⟩,⟨848578, by decide⟩,⟨848585, by decide⟩]) unmarked_context_12_109872_848586 node_context_12_109872_848586
  intro a
  fin_cases a
  · exact context_13_439488_848530
  · exact context_13_439489_848560
  · exact context_13_439490_848578
  · exact context_13_439491_848585

theorem selected_cut_32962 : selected 8 ⟨848594, by decide⟩
    (prefixPartial 13 439492) = some ⟨13, 2, 0, 848594, 439492, 533, 16384⟩ := by
  decide +kernel

theorem context_13_439492_848594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439492 ⟨848594, by decide⟩ :=
  accepted_of_selected 13 439492 ⟨848594, by decide⟩ ⟨13, 2, 0, 848594, 439492, 533, 16384⟩
    (by decide) selected_cut_32962

theorem selected_cut_32963 : selected 8 ⟨848617, by decide⟩
    (prefixPartial 13 439493) = some ⟨13, 2, 0, 848617, 439493, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_439493_848617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439493 ⟨848617, by decide⟩ :=
  accepted_of_selected 13 439493 ⟨848617, by decide⟩ ⟨13, 2, 0, 848617, 439493, 2273, 16384⟩
    (by decide) selected_cut_32963

theorem selected_cut_32964 : selected 8 ⟨848639, by decide⟩
    (prefixPartial 13 439494) = some ⟨13, 2, 0, 848639, 439494, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_439494_848639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439494 ⟨848639, by decide⟩ :=
  accepted_of_selected 13 439494 ⟨848639, by decide⟩ ⟨13, 2, 0, 848639, 439494, 1141, 16384⟩
    (by decide) selected_cut_32964

theorem selected_cut_32965 : selected 8 ⟨848644, by decide⟩
    (prefixPartial 13 439495) = some ⟨13, 2, 0, 848644, 439495, 653, 16384⟩ := by
  decide +kernel

theorem context_13_439495_848644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439495 ⟨848644, by decide⟩ :=
  accepted_of_selected 13 439495 ⟨848644, by decide⟩ ⟨13, 2, 0, 848644, 439495, 653, 16384⟩
    (by decide) selected_cut_32965

theorem unmarked_context_12_109873_848645 : frontier 9 ⟨848645, by decide⟩
    (prefixCache 12 109873) (prefixPartial 12 109873) = false := by
  decide +kernel

theorem node_context_12_109873_848645 : EJMOriginalGlobalDAGData.nodes 9 ⟨848645, by decide⟩ =
    .split (coordinate 12) (![⟨848594, by decide⟩,⟨848617, by decide⟩,⟨848639, by decide⟩,⟨848644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109873_848645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109873 ⟨848645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109873
    ⟨848645, by decide⟩ (by decide) (![⟨848594, by decide⟩,⟨848617, by decide⟩,⟨848639, by decide⟩,⟨848644, by decide⟩]) unmarked_context_12_109873_848645 node_context_12_109873_848645
  intro a
  fin_cases a
  · exact context_13_439492_848594
  · exact context_13_439493_848617
  · exact context_13_439494_848639
  · exact context_13_439495_848644

theorem selected_cut_32966 : selected 8 ⟨848651, by decide⟩
    (prefixPartial 13 439496) = some ⟨13, 2, 0, 848651, 439496, 409, 16384⟩ := by
  decide +kernel

theorem context_13_439496_848651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439496 ⟨848651, by decide⟩ :=
  accepted_of_selected 13 439496 ⟨848651, by decide⟩ ⟨13, 2, 0, 848651, 439496, 409, 16384⟩
    (by decide) selected_cut_32966

theorem selected_cut_32967 : selected 8 ⟨848680, by decide⟩
    (prefixPartial 13 439497) = some ⟨13, 2, 0, 848680, 439497, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_439497_848680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439497 ⟨848680, by decide⟩ :=
  accepted_of_selected 13 439497 ⟨848680, by decide⟩ ⟨13, 2, 0, 848680, 439497, 2277, 16384⟩
    (by decide) selected_cut_32967

theorem selected_cut_32968 : selected 8 ⟨848697, by decide⟩
    (prefixPartial 13 439498) = some ⟨13, 2, 0, 848697, 439498, 953, 16384⟩ := by
  decide +kernel

theorem context_13_439498_848697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439498 ⟨848697, by decide⟩ :=
  accepted_of_selected 13 439498 ⟨848697, by decide⟩ ⟨13, 2, 0, 848697, 439498, 953, 16384⟩
    (by decide) selected_cut_32968

theorem selected_cut_32969 : selected 8 ⟨848704, by decide⟩
    (prefixPartial 13 439499) = some ⟨13, 2, 0, 848704, 439499, 721, 16384⟩ := by
  decide +kernel

theorem context_13_439499_848704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439499 ⟨848704, by decide⟩ :=
  accepted_of_selected 13 439499 ⟨848704, by decide⟩ ⟨13, 2, 0, 848704, 439499, 721, 16384⟩
    (by decide) selected_cut_32969

theorem unmarked_context_12_109874_848705 : frontier 9 ⟨848705, by decide⟩
    (prefixCache 12 109874) (prefixPartial 12 109874) = false := by
  decide +kernel

theorem node_context_12_109874_848705 : EJMOriginalGlobalDAGData.nodes 9 ⟨848705, by decide⟩ =
    .split (coordinate 12) (![⟨848651, by decide⟩,⟨848680, by decide⟩,⟨848697, by decide⟩,⟨848704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109874_848705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109874 ⟨848705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109874
    ⟨848705, by decide⟩ (by decide) (![⟨848651, by decide⟩,⟨848680, by decide⟩,⟨848697, by decide⟩,⟨848704, by decide⟩]) unmarked_context_12_109874_848705 node_context_12_109874_848705
  intro a
  fin_cases a
  · exact context_13_439496_848651
  · exact context_13_439497_848680
  · exact context_13_439498_848697
  · exact context_13_439499_848704

theorem selected_cut_32970 : selected 8 ⟨848717, by decide⟩
    (prefixPartial 13 439500) = some ⟨13, 2, 0, 848717, 439500, 557, 16384⟩ := by
  decide +kernel

theorem context_13_439500_848717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439500 ⟨848717, by decide⟩ :=
  accepted_of_selected 13 439500 ⟨848717, by decide⟩ ⟨13, 2, 0, 848717, 439500, 557, 16384⟩
    (by decide) selected_cut_32970

theorem selected_cut_32971 : selected 8 ⟨848760, by decide⟩
    (prefixPartial 13 439501) = some ⟨13, 2, 0, 848760, 439501, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_439501_848760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439501 ⟨848760, by decide⟩ :=
  accepted_of_selected 13 439501 ⟨848760, by decide⟩ ⟨13, 2, 0, 848760, 439501, 2809, 16384⟩
    (by decide) selected_cut_32971

theorem selected_cut_32972 : selected 8 ⟨848782, by decide⟩
    (prefixPartial 13 439502) = some ⟨13, 2, 0, 848782, 439502, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_439502_848782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439502 ⟨848782, by decide⟩ :=
  accepted_of_selected 13 439502 ⟨848782, by decide⟩ ⟨13, 2, 0, 848782, 439502, 1237, 16384⟩
    (by decide) selected_cut_32972

theorem selected_cut_32973 : selected 8 ⟨848787, by decide⟩
    (prefixPartial 13 439503) = some ⟨13, 2, 0, 848787, 439503, 749, 16384⟩ := by
  decide +kernel

theorem context_13_439503_848787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439503 ⟨848787, by decide⟩ :=
  accepted_of_selected 13 439503 ⟨848787, by decide⟩ ⟨13, 2, 0, 848787, 439503, 749, 16384⟩
    (by decide) selected_cut_32973

theorem unmarked_context_12_109875_848788 : frontier 9 ⟨848788, by decide⟩
    (prefixCache 12 109875) (prefixPartial 12 109875) = false := by
  decide +kernel

theorem node_context_12_109875_848788 : EJMOriginalGlobalDAGData.nodes 9 ⟨848788, by decide⟩ =
    .split (coordinate 12) (![⟨848717, by decide⟩,⟨848760, by decide⟩,⟨848782, by decide⟩,⟨848787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109875_848788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109875 ⟨848788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109875
    ⟨848788, by decide⟩ (by decide) (![⟨848717, by decide⟩,⟨848760, by decide⟩,⟨848782, by decide⟩,⟨848787, by decide⟩]) unmarked_context_12_109875_848788 node_context_12_109875_848788
  intro a
  fin_cases a
  · exact context_13_439500_848717
  · exact context_13_439501_848760
  · exact context_13_439502_848782
  · exact context_13_439503_848787

theorem unmarked_context_11_27468_848789 : frontier 10 ⟨848789, by decide⟩
    (prefixCache 11 27468) (prefixPartial 11 27468) = false := by
  decide +kernel

theorem node_context_11_27468_848789 : EJMOriginalGlobalDAGData.nodes 10 ⟨848789, by decide⟩ =
    .split (coordinate 11) (![⟨848586, by decide⟩,⟨848645, by decide⟩,⟨848705, by decide⟩,⟨848788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27468_848789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27468 ⟨848789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27468
    ⟨848789, by decide⟩ (by decide) (![⟨848586, by decide⟩,⟨848645, by decide⟩,⟨848705, by decide⟩,⟨848788, by decide⟩]) unmarked_context_11_27468_848789 node_context_11_27468_848789
  intro a
  fin_cases a
  · exact context_12_109872_848586
  · exact context_12_109873_848645
  · exact context_12_109874_848705
  · exact context_12_109875_848788

theorem selected_cut_32974 : selected 8 ⟨848798, by decide⟩
    (prefixPartial 13 439504) = some ⟨13, 2, 0, 848798, 439504, 369, 16384⟩ := by
  decide +kernel

theorem context_13_439504_848798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439504 ⟨848798, by decide⟩ :=
  accepted_of_selected 13 439504 ⟨848798, by decide⟩ ⟨13, 2, 0, 848798, 439504, 369, 16384⟩
    (by decide) selected_cut_32974

theorem selected_cut_32975 : selected 8 ⟨848825, by decide⟩
    (prefixPartial 13 439505) = some ⟨13, 2, 0, 848825, 439505, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_439505_848825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439505 ⟨848825, by decide⟩ :=
  accepted_of_selected 13 439505 ⟨848825, by decide⟩ ⟨13, 2, 0, 848825, 439505, 2117, 16384⟩
    (by decide) selected_cut_32975

theorem selected_cut_32976 : selected 8 ⟨848844, by decide⟩
    (prefixPartial 13 439506) = some ⟨13, 2, 0, 848844, 439506, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_439506_848844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439506 ⟨848844, by decide⟩ :=
  accepted_of_selected 13 439506 ⟨848844, by decide⟩ ⟨13, 2, 0, 848844, 439506, 1141, 16384⟩
    (by decide) selected_cut_32976

theorem selected_cut_32977 : selected 8 ⟨848850, by decide⟩
    (prefixPartial 13 439507) = some ⟨13, 2, 0, 848850, 439507, 601, 16384⟩ := by
  decide +kernel

theorem context_13_439507_848850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439507 ⟨848850, by decide⟩ :=
  accepted_of_selected 13 439507 ⟨848850, by decide⟩ ⟨13, 2, 0, 848850, 439507, 601, 16384⟩
    (by decide) selected_cut_32977

theorem unmarked_context_12_109876_848851 : frontier 9 ⟨848851, by decide⟩
    (prefixCache 12 109876) (prefixPartial 12 109876) = false := by
  decide +kernel

theorem node_context_12_109876_848851 : EJMOriginalGlobalDAGData.nodes 9 ⟨848851, by decide⟩ =
    .split (coordinate 12) (![⟨848798, by decide⟩,⟨848825, by decide⟩,⟨848844, by decide⟩,⟨848850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109876_848851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109876 ⟨848851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109876
    ⟨848851, by decide⟩ (by decide) (![⟨848798, by decide⟩,⟨848825, by decide⟩,⟨848844, by decide⟩,⟨848850, by decide⟩]) unmarked_context_12_109876_848851 node_context_12_109876_848851
  intro a
  fin_cases a
  · exact context_13_439504_848798
  · exact context_13_439505_848825
  · exact context_13_439506_848844
  · exact context_13_439507_848850

theorem selected_cut_32978 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 109877) = some ⟨12, 1, 0, 689956, 109877, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109877_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109877 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 109877 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 109877, 1, 65536⟩
    (by decide) selected_cut_32978

theorem selected_cut_32979 : selected 9 ⟨848900, by decide⟩
    (prefixPartial 12 109878) = some ⟨12, 2, 0, 848900, 109878, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_109878_848900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109878 ⟨848900, by decide⟩ :=
  accepted_of_selected 12 109878 ⟨848900, by decide⟩ ⟨12, 2, 0, 848900, 109878, 3725, 65536⟩
    (by decide) selected_cut_32979

theorem selected_cut_32980 : selected 8 ⟨848909, by decide⟩
    (prefixPartial 13 439516) = some ⟨13, 2, 0, 848909, 439516, 313, 16384⟩ := by
  decide +kernel

theorem context_13_439516_848909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439516 ⟨848909, by decide⟩ :=
  accepted_of_selected 13 439516 ⟨848909, by decide⟩ ⟨13, 2, 0, 848909, 439516, 313, 16384⟩
    (by decide) selected_cut_32980

theorem selected_cut_32981 : selected 8 ⟨848957, by decide⟩
    (prefixPartial 13 439517) = some ⟨13, 2, 0, 848957, 439517, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_439517_848957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439517 ⟨848957, by decide⟩ :=
  accepted_of_selected 13 439517 ⟨848957, by decide⟩ ⟨13, 2, 0, 848957, 439517, 2589, 16384⟩
    (by decide) selected_cut_32981

theorem selected_cut_32982 : selected 8 ⟨848990, by decide⟩
    (prefixPartial 13 439518) = some ⟨13, 2, 0, 848990, 439518, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_439518_848990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439518 ⟨848990, by decide⟩ :=
  accepted_of_selected 13 439518 ⟨848990, by decide⟩ ⟨13, 2, 0, 848990, 439518, 1341, 16384⟩
    (by decide) selected_cut_32982

theorem selected_cut_32983 : selected 8 ⟨848997, by decide⟩
    (prefixPartial 13 439519) = some ⟨13, 2, 0, 848997, 439519, 617, 16384⟩ := by
  decide +kernel

theorem context_13_439519_848997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439519 ⟨848997, by decide⟩ :=
  accepted_of_selected 13 439519 ⟨848997, by decide⟩ ⟨13, 2, 0, 848997, 439519, 617, 16384⟩
    (by decide) selected_cut_32983

theorem unmarked_context_12_109879_848998 : frontier 9 ⟨848998, by decide⟩
    (prefixCache 12 109879) (prefixPartial 12 109879) = false := by
  decide +kernel

theorem node_context_12_109879_848998 : EJMOriginalGlobalDAGData.nodes 9 ⟨848998, by decide⟩ =
    .split (coordinate 12) (![⟨848909, by decide⟩,⟨848957, by decide⟩,⟨848990, by decide⟩,⟨848997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109879_848998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109879 ⟨848998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109879
    ⟨848998, by decide⟩ (by decide) (![⟨848909, by decide⟩,⟨848957, by decide⟩,⟨848990, by decide⟩,⟨848997, by decide⟩]) unmarked_context_12_109879_848998 node_context_12_109879_848998
  intro a
  fin_cases a
  · exact context_13_439516_848909
  · exact context_13_439517_848957
  · exact context_13_439518_848990
  · exact context_13_439519_848997

theorem unmarked_context_11_27469_848999 : frontier 10 ⟨848999, by decide⟩
    (prefixCache 11 27469) (prefixPartial 11 27469) = false := by
  decide +kernel

theorem node_context_11_27469_848999 : EJMOriginalGlobalDAGData.nodes 10 ⟨848999, by decide⟩ =
    .split (coordinate 11) (![⟨848851, by decide⟩,⟨689956, by decide⟩,⟨848900, by decide⟩,⟨848998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27469_848999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27469 ⟨848999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27469
    ⟨848999, by decide⟩ (by decide) (![⟨848851, by decide⟩,⟨689956, by decide⟩,⟨848900, by decide⟩,⟨848998, by decide⟩]) unmarked_context_11_27469_848999 node_context_11_27469_848999
  intro a
  fin_cases a
  · exact context_12_109876_848851
  · exact context_12_109877_689956
  · exact context_12_109878_848900
  · exact context_12_109879_848998

theorem selected_cut_32984 : selected 8 ⟨849004, by decide⟩
    (prefixPartial 13 439520) = some ⟨13, 2, 0, 849004, 439520, 205, 16384⟩ := by
  decide +kernel

theorem context_13_439520_849004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439520 ⟨849004, by decide⟩ :=
  accepted_of_selected 13 439520 ⟨849004, by decide⟩ ⟨13, 2, 0, 849004, 439520, 205, 16384⟩
    (by decide) selected_cut_32984

theorem selected_cut_32985 : selected 8 ⟨849033, by decide⟩
    (prefixPartial 13 439521) = some ⟨13, 2, 0, 849033, 439521, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_439521_849033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439521 ⟨849033, by decide⟩ :=
  accepted_of_selected 13 439521 ⟨849033, by decide⟩ ⟨13, 2, 0, 849033, 439521, 2273, 16384⟩
    (by decide) selected_cut_32985

theorem selected_cut_32986 : selected 8 ⟨849068, by decide⟩
    (prefixPartial 13 439522) = some ⟨13, 2, 0, 849068, 439522, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_439522_849068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439522 ⟨849068, by decide⟩ :=
  accepted_of_selected 13 439522 ⟨849068, by decide⟩ ⟨13, 2, 0, 849068, 439522, 1421, 16384⟩
    (by decide) selected_cut_32986

theorem selected_cut_32987 : selected 8 ⟨849074, by decide⟩
    (prefixPartial 13 439523) = some ⟨13, 2, 0, 849074, 439523, 649, 16384⟩ := by
  decide +kernel

theorem context_13_439523_849074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439523 ⟨849074, by decide⟩ :=
  accepted_of_selected 13 439523 ⟨849074, by decide⟩ ⟨13, 2, 0, 849074, 439523, 649, 16384⟩
    (by decide) selected_cut_32987

theorem unmarked_context_12_109880_849075 : frontier 9 ⟨849075, by decide⟩
    (prefixCache 12 109880) (prefixPartial 12 109880) = false := by
  decide +kernel

theorem node_context_12_109880_849075 : EJMOriginalGlobalDAGData.nodes 9 ⟨849075, by decide⟩ =
    .split (coordinate 12) (![⟨849004, by decide⟩,⟨849033, by decide⟩,⟨849068, by decide⟩,⟨849074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109880_849075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109880 ⟨849075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109880
    ⟨849075, by decide⟩ (by decide) (![⟨849004, by decide⟩,⟨849033, by decide⟩,⟨849068, by decide⟩,⟨849074, by decide⟩]) unmarked_context_12_109880_849075 node_context_12_109880_849075
  intro a
  fin_cases a
  · exact context_13_439520_849004
  · exact context_13_439521_849033
  · exact context_13_439522_849068
  · exact context_13_439523_849074

theorem selected_cut_32988 : selected 8 ⟨849079, by decide⟩
    (prefixPartial 13 439524) = some ⟨13, 2, 0, 849079, 439524, 173, 16384⟩ := by
  decide +kernel

theorem context_13_439524_849079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439524 ⟨849079, by decide⟩ :=
  accepted_of_selected 13 439524 ⟨849079, by decide⟩ ⟨13, 2, 0, 849079, 439524, 173, 16384⟩
    (by decide) selected_cut_32988

theorem selected_cut_32989 : selected 8 ⟨849100, by decide⟩
    (prefixPartial 13 439525) = some ⟨13, 2, 0, 849100, 439525, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_439525_849100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439525 ⟨849100, by decide⟩ :=
  accepted_of_selected 13 439525 ⟨849100, by decide⟩ ⟨13, 2, 0, 849100, 439525, 1953, 16384⟩
    (by decide) selected_cut_32989

theorem selected_cut_32990 : selected 8 ⟨849123, by decide⟩
    (prefixPartial 13 439526) = some ⟨13, 2, 0, 849123, 439526, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_439526_849123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439526 ⟨849123, by decide⟩ :=
  accepted_of_selected 13 439526 ⟨849123, by decide⟩ ⟨13, 2, 0, 849123, 439526, 1505, 16384⟩
    (by decide) selected_cut_32990

theorem selected_cut_32991 : selected 8 ⟨849129, by decide⟩
    (prefixPartial 13 439527) = some ⟨13, 2, 0, 849129, 439527, 637, 16384⟩ := by
  decide +kernel

theorem context_13_439527_849129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439527 ⟨849129, by decide⟩ :=
  accepted_of_selected 13 439527 ⟨849129, by decide⟩ ⟨13, 2, 0, 849129, 439527, 637, 16384⟩
    (by decide) selected_cut_32991

theorem unmarked_context_12_109881_849130 : frontier 9 ⟨849130, by decide⟩
    (prefixCache 12 109881) (prefixPartial 12 109881) = false := by
  decide +kernel

theorem node_context_12_109881_849130 : EJMOriginalGlobalDAGData.nodes 9 ⟨849130, by decide⟩ =
    .split (coordinate 12) (![⟨849079, by decide⟩,⟨849100, by decide⟩,⟨849123, by decide⟩,⟨849129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109881_849130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109881 ⟨849130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109881
    ⟨849130, by decide⟩ (by decide) (![⟨849079, by decide⟩,⟨849100, by decide⟩,⟨849123, by decide⟩,⟨849129, by decide⟩]) unmarked_context_12_109881_849130 node_context_12_109881_849130
  intro a
  fin_cases a
  · exact context_13_439524_849079
  · exact context_13_439525_849100
  · exact context_13_439526_849123
  · exact context_13_439527_849129

theorem selected_cut_32992 : selected 9 ⟨849183, by decide⟩
    (prefixPartial 12 109882) = some ⟨12, 2, 0, 849183, 109882, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_109882_849183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109882 ⟨849183, by decide⟩ :=
  accepted_of_selected 12 109882 ⟨849183, by decide⟩ ⟨12, 2, 0, 849183, 109882, 3713, 65536⟩
    (by decide) selected_cut_32992

theorem selected_cut_32993 : selected 8 ⟨849186, by decide⟩
    (prefixPartial 13 439532) = some ⟨13, 2, 0, 849186, 439532, 85, 16384⟩ := by
  decide +kernel

theorem context_13_439532_849186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439532 ⟨849186, by decide⟩ :=
  accepted_of_selected 13 439532 ⟨849186, by decide⟩ ⟨13, 2, 0, 849186, 439532, 85, 16384⟩
    (by decide) selected_cut_32993

theorem selected_cut_32994 : selected 8 ⟨849230, by decide⟩
    (prefixPartial 13 439533) = some ⟨13, 2, 0, 849230, 439533, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_439533_849230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439533 ⟨849230, by decide⟩ :=
  accepted_of_selected 13 439533 ⟨849230, by decide⟩ ⟨13, 2, 0, 849230, 439533, 2625, 16384⟩
    (by decide) selected_cut_32994

theorem selected_cut_32995 : selected 8 ⟨849263, by decide⟩
    (prefixPartial 13 439534) = some ⟨13, 2, 0, 849263, 439534, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_439534_849263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439534 ⟨849263, by decide⟩ :=
  accepted_of_selected 13 439534 ⟨849263, by decide⟩ ⟨13, 2, 0, 849263, 439534, 1561, 16384⟩
    (by decide) selected_cut_32995

theorem selected_cut_32996 : selected 8 ⟨849269, by decide⟩
    (prefixPartial 13 439535) = some ⟨13, 2, 0, 849269, 439535, 633, 16384⟩ := by
  decide +kernel

theorem context_13_439535_849269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439535 ⟨849269, by decide⟩ :=
  accepted_of_selected 13 439535 ⟨849269, by decide⟩ ⟨13, 2, 0, 849269, 439535, 633, 16384⟩
    (by decide) selected_cut_32996

theorem unmarked_context_12_109883_849270 : frontier 9 ⟨849270, by decide⟩
    (prefixCache 12 109883) (prefixPartial 12 109883) = false := by
  decide +kernel

theorem node_context_12_109883_849270 : EJMOriginalGlobalDAGData.nodes 9 ⟨849270, by decide⟩ =
    .split (coordinate 12) (![⟨849186, by decide⟩,⟨849230, by decide⟩,⟨849263, by decide⟩,⟨849269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109883_849270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109883 ⟨849270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109883
    ⟨849270, by decide⟩ (by decide) (![⟨849186, by decide⟩,⟨849230, by decide⟩,⟨849263, by decide⟩,⟨849269, by decide⟩]) unmarked_context_12_109883_849270 node_context_12_109883_849270
  intro a
  fin_cases a
  · exact context_13_439532_849186
  · exact context_13_439533_849230
  · exact context_13_439534_849263
  · exact context_13_439535_849269

theorem unmarked_context_11_27470_849271 : frontier 10 ⟨849271, by decide⟩
    (prefixCache 11 27470) (prefixPartial 11 27470) = false := by
  decide +kernel

theorem node_context_11_27470_849271 : EJMOriginalGlobalDAGData.nodes 10 ⟨849271, by decide⟩ =
    .split (coordinate 11) (![⟨849075, by decide⟩,⟨849130, by decide⟩,⟨849183, by decide⟩,⟨849270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27470_849271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27470 ⟨849271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27470
    ⟨849271, by decide⟩ (by decide) (![⟨849075, by decide⟩,⟨849130, by decide⟩,⟨849183, by decide⟩,⟨849270, by decide⟩]) unmarked_context_11_27470_849271 node_context_11_27470_849271
  intro a
  fin_cases a
  · exact context_12_109880_849075
  · exact context_12_109881_849130
  · exact context_12_109882_849183
  · exact context_12_109883_849270

theorem selected_cut_32997 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 27471) = some ⟨11, 1, 0, 793294, 27471, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27471_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27471 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 27471 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 27471, 1, 262144⟩
    (by decide) selected_cut_32997

theorem unmarked_context_10_6867_849272 : frontier 11 ⟨849272, by decide⟩
    (prefixCache 10 6867) (prefixPartial 10 6867) = false := by
  decide +kernel

theorem node_context_10_6867_849272 : EJMOriginalGlobalDAGData.nodes 11 ⟨849272, by decide⟩ =
    .split (coordinate 10) (![⟨848789, by decide⟩,⟨848999, by decide⟩,⟨849271, by decide⟩,⟨793294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6867_849272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6867 ⟨849272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6867
    ⟨849272, by decide⟩ (by decide) (![⟨848789, by decide⟩,⟨848999, by decide⟩,⟨849271, by decide⟩,⟨793294, by decide⟩]) unmarked_context_10_6867_849272 node_context_10_6867_849272
  intro a
  fin_cases a
  · exact context_11_27468_848789
  · exact context_11_27469_848999
  · exact context_11_27470_849271
  · exact context_11_27471_793294

theorem unmarked_context_9_1716_849273 : frontier 12 ⟨849273, by decide⟩
    (prefixCache 9 1716) (prefixPartial 9 1716) = false := by
  decide +kernel

theorem node_context_9_1716_849273 : EJMOriginalGlobalDAGData.nodes 12 ⟨849273, by decide⟩ =
    .split (coordinate 9) (![⟨845481, by decide⟩,⟨846976, by decide⟩,⟨848520, by decide⟩,⟨849272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1716_849273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1716 ⟨849273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1716
    ⟨849273, by decide⟩ (by decide) (![⟨845481, by decide⟩,⟨846976, by decide⟩,⟨848520, by decide⟩,⟨849272, by decide⟩]) unmarked_context_9_1716_849273 node_context_9_1716_849273
  intro a
  fin_cases a
  · exact context_10_6864_845481
  · exact context_10_6865_846976
  · exact context_10_6866_848520
  · exact context_10_6867_849272

theorem selected_cut_32998 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 439552) = some ⟨13, 1, 0, 3444, 439552, 1, 16384⟩ := by
  decide +kernel

theorem context_13_439552_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439552 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 439552 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 439552, 1, 16384⟩
    (by decide) selected_cut_32998

theorem selected_cut_32999 : selected 8 ⟨849303, by decide⟩
    (prefixPartial 13 439553) = some ⟨13, 2, 0, 849303, 439553, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_439553_849303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439553 ⟨849303, by decide⟩ :=
  accepted_of_selected 13 439553 ⟨849303, by decide⟩ ⟨13, 2, 0, 849303, 439553, 2209, 16384⟩
    (by decide) selected_cut_32999

theorem selected_cut_33000 : selected 8 ⟨849323, by decide⟩
    (prefixPartial 13 439554) = some ⟨13, 2, 0, 849323, 439554, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_439554_849323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439554 ⟨849323, by decide⟩ :=
  accepted_of_selected 13 439554 ⟨849323, by decide⟩ ⟨13, 2, 0, 849323, 439554, 1249, 16384⟩
    (by decide) selected_cut_33000

theorem selected_cut_33001 : selected 8 ⟨849333, by decide⟩
    (prefixPartial 13 439555) = some ⟨13, 2, 0, 849333, 439555, 749, 16384⟩ := by
  decide +kernel

theorem context_13_439555_849333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439555 ⟨849333, by decide⟩ :=
  accepted_of_selected 13 439555 ⟨849333, by decide⟩ ⟨13, 2, 0, 849333, 439555, 749, 16384⟩
    (by decide) selected_cut_33001

theorem unmarked_context_12_109888_849334 : frontier 9 ⟨849334, by decide⟩
    (prefixCache 12 109888) (prefixPartial 12 109888) = false := by
  decide +kernel

theorem node_context_12_109888_849334 : EJMOriginalGlobalDAGData.nodes 9 ⟨849334, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨849303, by decide⟩,⟨849323, by decide⟩,⟨849333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109888_849334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109888 ⟨849334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109888
    ⟨849334, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨849303, by decide⟩,⟨849323, by decide⟩,⟨849333, by decide⟩]) unmarked_context_12_109888_849334 node_context_12_109888_849334
  intro a
  fin_cases a
  · exact context_13_439552_3444
  · exact context_13_439553_849303
  · exact context_13_439554_849323
  · exact context_13_439555_849333

theorem selected_cut_33002 : selected 9 ⟨849382, by decide⟩
    (prefixPartial 12 109889) = some ⟨12, 2, 0, 849382, 109889, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_109889_849382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109889 ⟨849382, by decide⟩ :=
  accepted_of_selected 12 109889 ⟨849382, by decide⟩ ⟨12, 2, 0, 849382, 109889, 3641, 65536⟩
    (by decide) selected_cut_33002

theorem selected_cut_33003 : selected 9 ⟨849437, by decide⟩
    (prefixPartial 12 109890) = some ⟨12, 2, 0, 849437, 109890, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_109890_849437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109890 ⟨849437, by decide⟩ :=
  accepted_of_selected 12 109890 ⟨849437, by decide⟩ ⟨12, 2, 0, 849437, 109890, 3989, 65536⟩
    (by decide) selected_cut_33003

theorem selected_cut_33004 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 439564) = some ⟨13, 1, 0, 3444, 439564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_439564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 439564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 439564, 1, 16384⟩
    (by decide) selected_cut_33004

theorem selected_cut_33005 : selected 8 ⟨849460, by decide⟩
    (prefixPartial 13 439565) = some ⟨13, 2, 0, 849460, 439565, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_439565_849460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439565 ⟨849460, by decide⟩ :=
  accepted_of_selected 13 439565 ⟨849460, by decide⟩ ⟨13, 2, 0, 849460, 439565, 2081, 16384⟩
    (by decide) selected_cut_33005

theorem selected_cut_33006 : selected 8 ⟨849495, by decide⟩
    (prefixPartial 13 439566) = some ⟨13, 2, 0, 849495, 439566, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_439566_849495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439566 ⟨849495, by decide⟩ :=
  accepted_of_selected 13 439566 ⟨849495, by decide⟩ ⟨13, 2, 0, 849495, 439566, 1337, 16384⟩
    (by decide) selected_cut_33006

theorem selected_cut_33007 : selected 8 ⟨849501, by decide⟩
    (prefixPartial 13 439567) = some ⟨13, 2, 0, 849501, 439567, 893, 16384⟩ := by
  decide +kernel

theorem context_13_439567_849501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439567 ⟨849501, by decide⟩ :=
  accepted_of_selected 13 439567 ⟨849501, by decide⟩ ⟨13, 2, 0, 849501, 439567, 893, 16384⟩
    (by decide) selected_cut_33007

theorem unmarked_context_12_109891_849502 : frontier 9 ⟨849502, by decide⟩
    (prefixCache 12 109891) (prefixPartial 12 109891) = false := by
  decide +kernel

theorem node_context_12_109891_849502 : EJMOriginalGlobalDAGData.nodes 9 ⟨849502, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨849460, by decide⟩,⟨849495, by decide⟩,⟨849501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109891_849502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109891 ⟨849502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109891
    ⟨849502, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨849460, by decide⟩,⟨849495, by decide⟩,⟨849501, by decide⟩]) unmarked_context_12_109891_849502 node_context_12_109891_849502
  intro a
  fin_cases a
  · exact context_13_439564_3444
  · exact context_13_439565_849460
  · exact context_13_439566_849495
  · exact context_13_439567_849501

theorem unmarked_context_11_27472_849503 : frontier 10 ⟨849503, by decide⟩
    (prefixCache 11 27472) (prefixPartial 11 27472) = false := by
  decide +kernel

theorem node_context_11_27472_849503 : EJMOriginalGlobalDAGData.nodes 10 ⟨849503, by decide⟩ =
    .split (coordinate 11) (![⟨849334, by decide⟩,⟨849382, by decide⟩,⟨849437, by decide⟩,⟨849502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27472_849503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27472 ⟨849503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27472
    ⟨849503, by decide⟩ (by decide) (![⟨849334, by decide⟩,⟨849382, by decide⟩,⟨849437, by decide⟩,⟨849502, by decide⟩]) unmarked_context_11_27472_849503 node_context_11_27472_849503
  intro a
  fin_cases a
  · exact context_12_109888_849334
  · exact context_12_109889_849382
  · exact context_12_109890_849437
  · exact context_12_109891_849502

theorem selected_cut_33008 : selected 9 ⟨849559, by decide⟩
    (prefixPartial 12 109892) = some ⟨12, 2, 0, 849559, 109892, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_109892_849559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109892 ⟨849559, by decide⟩ :=
  accepted_of_selected 12 109892 ⟨849559, by decide⟩ ⟨12, 2, 0, 849559, 109892, 3897, 65536⟩
    (by decide) selected_cut_33008

theorem selected_cut_33009 : selected 9 ⟨849560, by decide⟩
    (prefixPartial 12 109893) = some ⟨12, 1, 0, 849560, 109893, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109893_849560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109893 ⟨849560, by decide⟩ :=
  accepted_of_selected 12 109893 ⟨849560, by decide⟩ ⟨12, 1, 0, 849560, 109893, 1, 65536⟩
    (by decide) selected_cut_33009

theorem selected_cut_33010 : selected 9 ⟨849614, by decide⟩
    (prefixPartial 12 109894) = some ⟨12, 2, 0, 849614, 109894, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_109894_849614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109894 ⟨849614, by decide⟩ :=
  accepted_of_selected 12 109894 ⟨849614, by decide⟩ ⟨12, 2, 0, 849614, 109894, 3585, 65536⟩
    (by decide) selected_cut_33010

theorem selected_cut_33011 : selected 9 ⟨849686, by decide⟩
    (prefixPartial 12 109895) = some ⟨12, 2, 0, 849686, 109895, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_109895_849686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109895 ⟨849686, by decide⟩ :=
  accepted_of_selected 12 109895 ⟨849686, by decide⟩ ⟨12, 2, 0, 849686, 109895, 4045, 65536⟩
    (by decide) selected_cut_33011

theorem unmarked_context_11_27473_849687 : frontier 10 ⟨849687, by decide⟩
    (prefixCache 11 27473) (prefixPartial 11 27473) = false := by
  decide +kernel

theorem node_context_11_27473_849687 : EJMOriginalGlobalDAGData.nodes 10 ⟨849687, by decide⟩ =
    .split (coordinate 11) (![⟨849559, by decide⟩,⟨849560, by decide⟩,⟨849614, by decide⟩,⟨849686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27473_849687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27473 ⟨849687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27473
    ⟨849687, by decide⟩ (by decide) (![⟨849559, by decide⟩,⟨849560, by decide⟩,⟨849614, by decide⟩,⟨849686, by decide⟩]) unmarked_context_11_27473_849687 node_context_11_27473_849687
  intro a
  fin_cases a
  · exact context_12_109892_849559
  · exact context_12_109893_849560
  · exact context_12_109894_849614
  · exact context_12_109895_849686

theorem selected_cut_33012 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 439584) = some ⟨13, 1, 0, 3444, 439584, 1, 16384⟩ := by
  decide +kernel

theorem context_13_439584_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439584 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 439584 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 439584, 1, 16384⟩
    (by decide) selected_cut_33012

theorem selected_cut_33013 : selected 8 ⟨849720, by decide⟩
    (prefixPartial 13 439585) = some ⟨13, 2, 0, 849720, 439585, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_439585_849720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439585 ⟨849720, by decide⟩ :=
  accepted_of_selected 13 439585 ⟨849720, by decide⟩ ⟨13, 2, 0, 849720, 439585, 2061, 16384⟩
    (by decide) selected_cut_33013

theorem selected_cut_33014 : selected 8 ⟨849747, by decide⟩
    (prefixPartial 13 439586) = some ⟨13, 2, 0, 849747, 439586, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_439586_849747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439586 ⟨849747, by decide⟩ :=
  accepted_of_selected 13 439586 ⟨849747, by decide⟩ ⟨13, 2, 0, 849747, 439586, 1445, 16384⟩
    (by decide) selected_cut_33014

theorem selected_cut_33015 : selected 8 ⟨849754, by decide⟩
    (prefixPartial 13 439587) = some ⟨13, 2, 0, 849754, 439587, 629, 16384⟩ := by
  decide +kernel

theorem context_13_439587_849754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439587 ⟨849754, by decide⟩ :=
  accepted_of_selected 13 439587 ⟨849754, by decide⟩ ⟨13, 2, 0, 849754, 439587, 629, 16384⟩
    (by decide) selected_cut_33015

theorem unmarked_context_12_109896_849755 : frontier 9 ⟨849755, by decide⟩
    (prefixCache 12 109896) (prefixPartial 12 109896) = false := by
  decide +kernel

theorem node_context_12_109896_849755 : EJMOriginalGlobalDAGData.nodes 9 ⟨849755, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨849720, by decide⟩,⟨849747, by decide⟩,⟨849754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109896_849755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109896 ⟨849755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109896
    ⟨849755, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨849720, by decide⟩,⟨849747, by decide⟩,⟨849754, by decide⟩]) unmarked_context_12_109896_849755 node_context_12_109896_849755
  intro a
  fin_cases a
  · exact context_13_439584_3444
  · exact context_13_439585_849720
  · exact context_13_439586_849747
  · exact context_13_439587_849754

theorem selected_cut_33016 : selected 9 ⟨849811, by decide⟩
    (prefixPartial 12 109897) = some ⟨12, 2, 0, 849811, 109897, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_109897_849811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109897 ⟨849811, by decide⟩ :=
  accepted_of_selected 12 109897 ⟨849811, by decide⟩ ⟨12, 2, 0, 849811, 109897, 3469, 65536⟩
    (by decide) selected_cut_33016

theorem selected_cut_33017 : selected 9 ⟨849858, by decide⟩
    (prefixPartial 12 109898) = some ⟨12, 2, 0, 849858, 109898, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_109898_849858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109898 ⟨849858, by decide⟩ :=
  accepted_of_selected 12 109898 ⟨849858, by decide⟩ ⟨12, 2, 0, 849858, 109898, 3417, 65536⟩
    (by decide) selected_cut_33017

theorem selected_cut_33018 : selected 9 ⟨849927, by decide⟩
    (prefixPartial 12 109899) = some ⟨12, 2, 0, 849927, 109899, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_109899_849927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109899 ⟨849927, by decide⟩ :=
  accepted_of_selected 12 109899 ⟨849927, by decide⟩ ⟨12, 2, 0, 849927, 109899, 3957, 65536⟩
    (by decide) selected_cut_33018

theorem unmarked_context_11_27474_849928 : frontier 10 ⟨849928, by decide⟩
    (prefixCache 11 27474) (prefixPartial 11 27474) = false := by
  decide +kernel

theorem node_context_11_27474_849928 : EJMOriginalGlobalDAGData.nodes 10 ⟨849928, by decide⟩ =
    .split (coordinate 11) (![⟨849755, by decide⟩,⟨849811, by decide⟩,⟨849858, by decide⟩,⟨849927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27474_849928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27474 ⟨849928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27474
    ⟨849928, by decide⟩ (by decide) (![⟨849755, by decide⟩,⟨849811, by decide⟩,⟨849858, by decide⟩,⟨849927, by decide⟩]) unmarked_context_11_27474_849928 node_context_11_27474_849928
  intro a
  fin_cases a
  · exact context_12_109896_849755
  · exact context_12_109897_849811
  · exact context_12_109898_849858
  · exact context_12_109899_849927

theorem selected_cut_33019 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 439600) = some ⟨13, 1, 0, 3444, 439600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_439600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 439600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 439600, 1, 16384⟩
    (by decide) selected_cut_33019

theorem selected_cut_33020 : selected 8 ⟨849949, by decide⟩
    (prefixPartial 13 439601) = some ⟨13, 2, 0, 849949, 439601, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_439601_849949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439601 ⟨849949, by decide⟩ :=
  accepted_of_selected 13 439601 ⟨849949, by decide⟩ ⟨13, 2, 0, 849949, 439601, 2057, 16384⟩
    (by decide) selected_cut_33020

theorem selected_cut_33021 : selected 8 ⟨849980, by decide⟩
    (prefixPartial 13 439602) = some ⟨13, 2, 0, 849980, 439602, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_439602_849980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439602 ⟨849980, by decide⟩ :=
  accepted_of_selected 13 439602 ⟨849980, by decide⟩ ⟨13, 2, 0, 849980, 439602, 1381, 16384⟩
    (by decide) selected_cut_33021

theorem selected_cut_33022 : selected 8 ⟨849990, by decide⟩
    (prefixPartial 13 439603) = some ⟨13, 2, 0, 849990, 439603, 889, 16384⟩ := by
  decide +kernel

theorem context_13_439603_849990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439603 ⟨849990, by decide⟩ :=
  accepted_of_selected 13 439603 ⟨849990, by decide⟩ ⟨13, 2, 0, 849990, 439603, 889, 16384⟩
    (by decide) selected_cut_33022

theorem unmarked_context_12_109900_849991 : frontier 9 ⟨849991, by decide⟩
    (prefixCache 12 109900) (prefixPartial 12 109900) = false := by
  decide +kernel

theorem node_context_12_109900_849991 : EJMOriginalGlobalDAGData.nodes 9 ⟨849991, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨849949, by decide⟩,⟨849980, by decide⟩,⟨849990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109900_849991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109900 ⟨849991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109900
    ⟨849991, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨849949, by decide⟩,⟨849980, by decide⟩,⟨849990, by decide⟩]) unmarked_context_12_109900_849991 node_context_12_109900_849991
  intro a
  fin_cases a
  · exact context_13_439600_3444
  · exact context_13_439601_849949
  · exact context_13_439602_849980
  · exact context_13_439603_849990

theorem selected_cut_33023 : selected 9 ⟨850036, by decide⟩
    (prefixPartial 12 109901) = some ⟨12, 2, 0, 850036, 109901, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_109901_850036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109901 ⟨850036, by decide⟩ :=
  accepted_of_selected 12 109901 ⟨850036, by decide⟩ ⟨12, 2, 0, 850036, 109901, 3497, 65536⟩
    (by decide) selected_cut_33023

theorem selected_cut_33024 : selected 9 ⟨850079, by decide⟩
    (prefixPartial 12 109902) = some ⟨12, 2, 0, 850079, 109902, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_109902_850079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109902 ⟨850079, by decide⟩ :=
  accepted_of_selected 12 109902 ⟨850079, by decide⟩ ⟨12, 2, 0, 850079, 109902, 3693, 65536⟩
    (by decide) selected_cut_33024

theorem selected_cut_33025 : selected 9 ⟨850136, by decide⟩
    (prefixPartial 12 109903) = some ⟨12, 2, 0, 850136, 109903, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_109903_850136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109903 ⟨850136, by decide⟩ :=
  accepted_of_selected 12 109903 ⟨850136, by decide⟩ ⟨12, 2, 0, 850136, 109903, 4057, 65536⟩
    (by decide) selected_cut_33025

theorem unmarked_context_11_27475_850137 : frontier 10 ⟨850137, by decide⟩
    (prefixCache 11 27475) (prefixPartial 11 27475) = false := by
  decide +kernel

theorem node_context_11_27475_850137 : EJMOriginalGlobalDAGData.nodes 10 ⟨850137, by decide⟩ =
    .split (coordinate 11) (![⟨849991, by decide⟩,⟨850036, by decide⟩,⟨850079, by decide⟩,⟨850136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27475_850137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27475 ⟨850137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27475
    ⟨850137, by decide⟩ (by decide) (![⟨849991, by decide⟩,⟨850036, by decide⟩,⟨850079, by decide⟩,⟨850136, by decide⟩]) unmarked_context_11_27475_850137 node_context_11_27475_850137
  intro a
  fin_cases a
  · exact context_12_109900_849991
  · exact context_12_109901_850036
  · exact context_12_109902_850079
  · exact context_12_109903_850136

theorem unmarked_context_10_6868_850138 : frontier 11 ⟨850138, by decide⟩
    (prefixCache 10 6868) (prefixPartial 10 6868) = false := by
  decide +kernel

theorem node_context_10_6868_850138 : EJMOriginalGlobalDAGData.nodes 11 ⟨850138, by decide⟩ =
    .split (coordinate 10) (![⟨849503, by decide⟩,⟨849687, by decide⟩,⟨849928, by decide⟩,⟨850137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6868_850138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6868 ⟨850138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6868
    ⟨850138, by decide⟩ (by decide) (![⟨849503, by decide⟩,⟨849687, by decide⟩,⟨849928, by decide⟩,⟨850137, by decide⟩]) unmarked_context_10_6868_850138 node_context_10_6868_850138
  intro a
  fin_cases a
  · exact context_11_27472_849503
  · exact context_11_27473_849687
  · exact context_11_27474_849928
  · exact context_11_27475_850137

theorem selected_cut_33026 : selected 9 ⟨850189, by decide⟩
    (prefixPartial 12 109904) = some ⟨12, 2, 0, 850189, 109904, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_109904_850189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109904 ⟨850189, by decide⟩ :=
  accepted_of_selected 12 109904 ⟨850189, by decide⟩ ⟨12, 2, 0, 850189, 109904, 3837, 65536⟩
    (by decide) selected_cut_33026

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
