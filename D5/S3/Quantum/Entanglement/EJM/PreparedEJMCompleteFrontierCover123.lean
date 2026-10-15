/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover122
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_11810 : selected 8 ⟨316047, by decide⟩
    (prefixPartial 13 103496) = some ⟨13, 2, 0, 316047, 103496, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_103496_316047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103496 ⟨316047, by decide⟩ :=
  accepted_of_selected 13 103496 ⟨316047, by decide⟩ ⟨13, 2, 0, 316047, 103496, 2129, 16384⟩
    (by decide) selected_cut_11810

theorem selected_cut_11811 : selected 8 ⟨316072, by decide⟩
    (prefixPartial 13 103497) = some ⟨13, 2, 0, 316072, 103497, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_103497_316072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103497 ⟨316072, by decide⟩ :=
  accepted_of_selected 13 103497 ⟨316072, by decide⟩ ⟨13, 2, 0, 316072, 103497, 1717, 16384⟩
    (by decide) selected_cut_11811

theorem selected_cut_11812 : selected 8 ⟨316091, by decide⟩
    (prefixPartial 13 103498) = some ⟨13, 2, 0, 316091, 103498, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_103498_316091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103498 ⟨316091, by decide⟩ :=
  accepted_of_selected 13 103498 ⟨316091, by decide⟩ ⟨13, 2, 0, 316091, 103498, 1569, 16384⟩
    (by decide) selected_cut_11812

theorem selected_cut_11813 : selected 8 ⟨316099, by decide⟩
    (prefixPartial 13 103499) = some ⟨13, 2, 0, 316099, 103499, 865, 16384⟩ := by
  decide +kernel

theorem context_13_103499_316099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103499 ⟨316099, by decide⟩ :=
  accepted_of_selected 13 103499 ⟨316099, by decide⟩ ⟨13, 2, 0, 316099, 103499, 865, 16384⟩
    (by decide) selected_cut_11813

theorem unmarked_context_12_25874_316100 : frontier 9 ⟨316100, by decide⟩
    (prefixCache 12 25874) (prefixPartial 12 25874) = false := by
  decide +kernel

theorem node_context_12_25874_316100 : EJMOriginalGlobalDAGData.nodes 9 ⟨316100, by decide⟩ =
    .split (coordinate 12) (![⟨316047, by decide⟩,⟨316072, by decide⟩,⟨316091, by decide⟩,⟨316099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25874_316100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25874 ⟨316100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25874
    ⟨316100, by decide⟩ (by decide) (![⟨316047, by decide⟩,⟨316072, by decide⟩,⟨316091, by decide⟩,⟨316099, by decide⟩]) unmarked_context_12_25874_316100 node_context_12_25874_316100
  intro a
  fin_cases a
  · exact context_13_103496_316047
  · exact context_13_103497_316072
  · exact context_13_103498_316091
  · exact context_13_103499_316099

theorem selected_cut_11814 : selected 8 ⟨316129, by decide⟩
    (prefixPartial 13 103500) = some ⟨13, 2, 0, 316129, 103500, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_103500_316129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103500 ⟨316129, by decide⟩ :=
  accepted_of_selected 13 103500 ⟨316129, by decide⟩ ⟨13, 2, 0, 316129, 103500, 2213, 16384⟩
    (by decide) selected_cut_11814

theorem selected_cut_11815 : selected 8 ⟨316149, by decide⟩
    (prefixPartial 13 103501) = some ⟨13, 2, 0, 316149, 103501, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_103501_316149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103501 ⟨316149, by decide⟩ :=
  accepted_of_selected 13 103501 ⟨316149, by decide⟩ ⟨13, 2, 0, 316149, 103501, 1965, 16384⟩
    (by decide) selected_cut_11815

theorem selected_cut_11816 : selected 8 ⟨316170, by decide⟩
    (prefixPartial 13 103502) = some ⟨13, 2, 0, 316170, 103502, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_103502_316170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103502 ⟨316170, by decide⟩ :=
  accepted_of_selected 13 103502 ⟨316170, by decide⟩ ⟨13, 2, 0, 316170, 103502, 1697, 16384⟩
    (by decide) selected_cut_11816

theorem selected_cut_11817 : selected 8 ⟨316176, by decide⟩
    (prefixPartial 13 103503) = some ⟨13, 2, 0, 316176, 103503, 901, 16384⟩ := by
  decide +kernel

theorem context_13_103503_316176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103503 ⟨316176, by decide⟩ :=
  accepted_of_selected 13 103503 ⟨316176, by decide⟩ ⟨13, 2, 0, 316176, 103503, 901, 16384⟩
    (by decide) selected_cut_11817

theorem unmarked_context_12_25875_316177 : frontier 9 ⟨316177, by decide⟩
    (prefixCache 12 25875) (prefixPartial 12 25875) = false := by
  decide +kernel

theorem node_context_12_25875_316177 : EJMOriginalGlobalDAGData.nodes 9 ⟨316177, by decide⟩ =
    .split (coordinate 12) (![⟨316129, by decide⟩,⟨316149, by decide⟩,⟨316170, by decide⟩,⟨316176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25875_316177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25875 ⟨316177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25875
    ⟨316177, by decide⟩ (by decide) (![⟨316129, by decide⟩,⟨316149, by decide⟩,⟨316170, by decide⟩,⟨316176, by decide⟩]) unmarked_context_12_25875_316177 node_context_12_25875_316177
  intro a
  fin_cases a
  · exact context_13_103500_316129
  · exact context_13_103501_316149
  · exact context_13_103502_316170
  · exact context_13_103503_316176

theorem unmarked_context_11_6468_316178 : frontier 10 ⟨316178, by decide⟩
    (prefixCache 11 6468) (prefixPartial 11 6468) = false := by
  decide +kernel

theorem node_context_11_6468_316178 : EJMOriginalGlobalDAGData.nodes 10 ⟨316178, by decide⟩ =
    .split (coordinate 11) (![⟨315944, by decide⟩,⟨316015, by decide⟩,⟨316100, by decide⟩,⟨316177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6468_316178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6468 ⟨316178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6468
    ⟨316178, by decide⟩ (by decide) (![⟨315944, by decide⟩,⟨316015, by decide⟩,⟨316100, by decide⟩,⟨316177, by decide⟩]) unmarked_context_11_6468_316178 node_context_11_6468_316178
  intro a
  fin_cases a
  · exact context_12_25872_315944
  · exact context_12_25873_316015
  · exact context_12_25874_316100
  · exact context_12_25875_316177

theorem selected_cut_11818 : selected 8 ⟨316207, by decide⟩
    (prefixPartial 13 103504) = some ⟨13, 2, 0, 316207, 103504, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_103504_316207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103504 ⟨316207, by decide⟩ :=
  accepted_of_selected 13 103504 ⟨316207, by decide⟩ ⟨13, 2, 0, 316207, 103504, 1853, 16384⟩
    (by decide) selected_cut_11818

theorem selected_cut_11819 : selected 8 ⟨316248, by decide⟩
    (prefixPartial 13 103505) = some ⟨13, 2, 0, 316248, 103505, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_103505_316248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103505 ⟨316248, by decide⟩ :=
  accepted_of_selected 13 103505 ⟨316248, by decide⟩ ⟨13, 2, 0, 316248, 103505, 2537, 16384⟩
    (by decide) selected_cut_11819

theorem selected_cut_11820 : selected 8 ⟨316272, by decide⟩
    (prefixPartial 13 103506) = some ⟨13, 2, 0, 316272, 103506, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_103506_316272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103506 ⟨316272, by decide⟩ :=
  accepted_of_selected 13 103506 ⟨316272, by decide⟩ ⟨13, 2, 0, 316272, 103506, 1653, 16384⟩
    (by decide) selected_cut_11820

theorem selected_cut_11821 : selected 8 ⟨316283, by decide⟩
    (prefixPartial 13 103507) = some ⟨13, 2, 0, 316283, 103507, 981, 16384⟩ := by
  decide +kernel

theorem context_13_103507_316283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103507 ⟨316283, by decide⟩ :=
  accepted_of_selected 13 103507 ⟨316283, by decide⟩ ⟨13, 2, 0, 316283, 103507, 981, 16384⟩
    (by decide) selected_cut_11821

theorem unmarked_context_12_25876_316284 : frontier 9 ⟨316284, by decide⟩
    (prefixCache 12 25876) (prefixPartial 12 25876) = false := by
  decide +kernel

theorem node_context_12_25876_316284 : EJMOriginalGlobalDAGData.nodes 9 ⟨316284, by decide⟩ =
    .split (coordinate 12) (![⟨316207, by decide⟩,⟨316248, by decide⟩,⟨316272, by decide⟩,⟨316283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25876_316284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25876 ⟨316284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25876
    ⟨316284, by decide⟩ (by decide) (![⟨316207, by decide⟩,⟨316248, by decide⟩,⟨316272, by decide⟩,⟨316283, by decide⟩]) unmarked_context_12_25876_316284 node_context_12_25876_316284
  intro a
  fin_cases a
  · exact context_13_103504_316207
  · exact context_13_103505_316248
  · exact context_13_103506_316272
  · exact context_13_103507_316283

theorem selected_cut_11822 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 25877) = some ⟨12, 1, 0, 124308, 25877, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25877_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25877 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 25877 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 25877, 1, 65536⟩
    (by decide) selected_cut_11822

theorem selected_cut_11823 : selected 8 ⟨316333, by decide⟩
    (prefixPartial 13 103512) = some ⟨13, 2, 0, 316333, 103512, 2885, 16384⟩ := by
  decide +kernel

theorem context_13_103512_316333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103512 ⟨316333, by decide⟩ :=
  accepted_of_selected 13 103512 ⟨316333, by decide⟩ ⟨13, 2, 0, 316333, 103512, 2885, 16384⟩
    (by decide) selected_cut_11823

theorem selected_cut_11824 : selected 8 ⟨316383, by decide⟩
    (prefixPartial 13 103513) = some ⟨13, 2, 0, 316383, 103513, 2869, 16384⟩ := by
  decide +kernel

theorem context_13_103513_316383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103513 ⟨316383, by decide⟩ :=
  accepted_of_selected 13 103513 ⟨316383, by decide⟩ ⟨13, 2, 0, 316383, 103513, 2869, 16384⟩
    (by decide) selected_cut_11824

theorem selected_cut_11825 : selected 8 ⟨316406, by decide⟩
    (prefixPartial 13 103514) = some ⟨13, 2, 0, 316406, 103514, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_103514_316406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103514 ⟨316406, by decide⟩ :=
  accepted_of_selected 13 103514 ⟨316406, by decide⟩ ⟨13, 2, 0, 316406, 103514, 1953, 16384⟩
    (by decide) selected_cut_11825

theorem selected_cut_11826 : selected 8 ⟨316412, by decide⟩
    (prefixPartial 13 103515) = some ⟨13, 2, 0, 316412, 103515, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_103515_316412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103515 ⟨316412, by decide⟩ :=
  accepted_of_selected 13 103515 ⟨316412, by decide⟩ ⟨13, 2, 0, 316412, 103515, 1101, 16384⟩
    (by decide) selected_cut_11826

theorem unmarked_context_12_25878_316413 : frontier 9 ⟨316413, by decide⟩
    (prefixCache 12 25878) (prefixPartial 12 25878) = false := by
  decide +kernel

theorem node_context_12_25878_316413 : EJMOriginalGlobalDAGData.nodes 9 ⟨316413, by decide⟩ =
    .split (coordinate 12) (![⟨316333, by decide⟩,⟨316383, by decide⟩,⟨316406, by decide⟩,⟨316412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25878_316413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25878 ⟨316413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25878
    ⟨316413, by decide⟩ (by decide) (![⟨316333, by decide⟩,⟨316383, by decide⟩,⟨316406, by decide⟩,⟨316412, by decide⟩]) unmarked_context_12_25878_316413 node_context_12_25878_316413
  intro a
  fin_cases a
  · exact context_13_103512_316333
  · exact context_13_103513_316383
  · exact context_13_103514_316406
  · exact context_13_103515_316412

theorem selected_cut_11827 : selected 8 ⟨316460, by decide⟩
    (prefixPartial 13 103516) = some ⟨13, 2, 0, 316460, 103516, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_103516_316460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103516 ⟨316460, by decide⟩ :=
  accepted_of_selected 13 103516 ⟨316460, by decide⟩ ⟨13, 2, 0, 316460, 103516, 2925, 16384⟩
    (by decide) selected_cut_11827

theorem selected_cut_11828 : selected 8 ⟨316515, by decide⟩
    (prefixPartial 13 103517) = some ⟨13, 2, 0, 316515, 103517, 3369, 16384⟩ := by
  decide +kernel

theorem context_13_103517_316515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103517 ⟨316515, by decide⟩ :=
  accepted_of_selected 13 103517 ⟨316515, by decide⟩ ⟨13, 2, 0, 316515, 103517, 3369, 16384⟩
    (by decide) selected_cut_11828

theorem selected_cut_11829 : selected 8 ⟨316536, by decide⟩
    (prefixPartial 13 103518) = some ⟨13, 2, 0, 316536, 103518, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_103518_316536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103518 ⟨316536, by decide⟩ :=
  accepted_of_selected 13 103518 ⟨316536, by decide⟩ ⟨13, 2, 0, 316536, 103518, 2037, 16384⟩
    (by decide) selected_cut_11829

theorem selected_cut_11830 : selected 8 ⟨316549, by decide⟩
    (prefixPartial 13 103519) = some ⟨13, 2, 0, 316549, 103519, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_103519_316549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103519 ⟨316549, by decide⟩ :=
  accepted_of_selected 13 103519 ⟨316549, by decide⟩ ⟨13, 2, 0, 316549, 103519, 1165, 16384⟩
    (by decide) selected_cut_11830

theorem unmarked_context_12_25879_316550 : frontier 9 ⟨316550, by decide⟩
    (prefixCache 12 25879) (prefixPartial 12 25879) = false := by
  decide +kernel

theorem node_context_12_25879_316550 : EJMOriginalGlobalDAGData.nodes 9 ⟨316550, by decide⟩ =
    .split (coordinate 12) (![⟨316460, by decide⟩,⟨316515, by decide⟩,⟨316536, by decide⟩,⟨316549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25879_316550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25879 ⟨316550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25879
    ⟨316550, by decide⟩ (by decide) (![⟨316460, by decide⟩,⟨316515, by decide⟩,⟨316536, by decide⟩,⟨316549, by decide⟩]) unmarked_context_12_25879_316550 node_context_12_25879_316550
  intro a
  fin_cases a
  · exact context_13_103516_316460
  · exact context_13_103517_316515
  · exact context_13_103518_316536
  · exact context_13_103519_316549

theorem unmarked_context_11_6469_316551 : frontier 10 ⟨316551, by decide⟩
    (prefixCache 11 6469) (prefixPartial 11 6469) = false := by
  decide +kernel

theorem node_context_11_6469_316551 : EJMOriginalGlobalDAGData.nodes 10 ⟨316551, by decide⟩ =
    .split (coordinate 11) (![⟨316284, by decide⟩,⟨124308, by decide⟩,⟨316413, by decide⟩,⟨316550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6469_316551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6469 ⟨316551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6469
    ⟨316551, by decide⟩ (by decide) (![⟨316284, by decide⟩,⟨124308, by decide⟩,⟨316413, by decide⟩,⟨316550, by decide⟩]) unmarked_context_11_6469_316551 node_context_11_6469_316551
  intro a
  fin_cases a
  · exact context_12_25876_316284
  · exact context_12_25877_124308
  · exact context_12_25878_316413
  · exact context_12_25879_316550

theorem selected_cut_11831 : selected 8 ⟨316566, by decide⟩
    (prefixPartial 13 103520) = some ⟨13, 2, 0, 316566, 103520, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_103520_316566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103520 ⟨316566, by decide⟩ :=
  accepted_of_selected 13 103520 ⟨316566, by decide⟩ ⟨13, 2, 0, 316566, 103520, 1201, 16384⟩
    (by decide) selected_cut_11831

theorem selected_cut_11832 : selected 8 ⟨316589, by decide⟩
    (prefixPartial 13 103521) = some ⟨13, 2, 0, 316589, 103521, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_103521_316589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103521 ⟨316589, by decide⟩ :=
  accepted_of_selected 13 103521 ⟨316589, by decide⟩ ⟨13, 2, 0, 316589, 103521, 1661, 16384⟩
    (by decide) selected_cut_11832

theorem selected_cut_11833 : selected 8 ⟨316611, by decide⟩
    (prefixPartial 13 103522) = some ⟨13, 2, 0, 316611, 103522, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_103522_316611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103522 ⟨316611, by decide⟩ :=
  accepted_of_selected 13 103522 ⟨316611, by decide⟩ ⟨13, 2, 0, 316611, 103522, 1493, 16384⟩
    (by decide) selected_cut_11833

theorem selected_cut_11834 : selected 8 ⟨316619, by decide⟩
    (prefixPartial 13 103523) = some ⟨13, 2, 0, 316619, 103523, 849, 16384⟩ := by
  decide +kernel

theorem context_13_103523_316619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103523 ⟨316619, by decide⟩ :=
  accepted_of_selected 13 103523 ⟨316619, by decide⟩ ⟨13, 2, 0, 316619, 103523, 849, 16384⟩
    (by decide) selected_cut_11834

theorem unmarked_context_12_25880_316620 : frontier 9 ⟨316620, by decide⟩
    (prefixCache 12 25880) (prefixPartial 12 25880) = false := by
  decide +kernel

theorem node_context_12_25880_316620 : EJMOriginalGlobalDAGData.nodes 9 ⟨316620, by decide⟩ =
    .split (coordinate 12) (![⟨316566, by decide⟩,⟨316589, by decide⟩,⟨316611, by decide⟩,⟨316619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25880_316620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25880 ⟨316620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25880
    ⟨316620, by decide⟩ (by decide) (![⟨316566, by decide⟩,⟨316589, by decide⟩,⟨316611, by decide⟩,⟨316619, by decide⟩]) unmarked_context_12_25880_316620 node_context_12_25880_316620
  intro a
  fin_cases a
  · exact context_13_103520_316566
  · exact context_13_103521_316589
  · exact context_13_103522_316611
  · exact context_13_103523_316619

theorem selected_cut_11835 : selected 8 ⟨316640, by decide⟩
    (prefixPartial 13 103524) = some ⟨13, 2, 0, 316640, 103524, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_103524_316640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103524 ⟨316640, by decide⟩ :=
  accepted_of_selected 13 103524 ⟨316640, by decide⟩ ⟨13, 2, 0, 316640, 103524, 1429, 16384⟩
    (by decide) selected_cut_11835

theorem selected_cut_11836 : selected 8 ⟨316664, by decide⟩
    (prefixPartial 13 103525) = some ⟨13, 2, 0, 316664, 103525, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_103525_316664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103525 ⟨316664, by decide⟩ :=
  accepted_of_selected 13 103525 ⟨316664, by decide⟩ ⟨13, 2, 0, 316664, 103525, 1093, 16384⟩
    (by decide) selected_cut_11836

theorem selected_cut_11837 : selected 8 ⟨316686, by decide⟩
    (prefixPartial 13 103526) = some ⟨13, 2, 0, 316686, 103526, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_103526_316686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103526 ⟨316686, by decide⟩ :=
  accepted_of_selected 13 103526 ⟨316686, by decide⟩ ⟨13, 2, 0, 316686, 103526, 1325, 16384⟩
    (by decide) selected_cut_11837

theorem selected_cut_11838 : selected 8 ⟨316693, by decide⟩
    (prefixPartial 13 103527) = some ⟨13, 2, 0, 316693, 103527, 789, 16384⟩ := by
  decide +kernel

theorem context_13_103527_316693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103527 ⟨316693, by decide⟩ :=
  accepted_of_selected 13 103527 ⟨316693, by decide⟩ ⟨13, 2, 0, 316693, 103527, 789, 16384⟩
    (by decide) selected_cut_11838

theorem unmarked_context_12_25881_316694 : frontier 9 ⟨316694, by decide⟩
    (prefixCache 12 25881) (prefixPartial 12 25881) = false := by
  decide +kernel

theorem node_context_12_25881_316694 : EJMOriginalGlobalDAGData.nodes 9 ⟨316694, by decide⟩ =
    .split (coordinate 12) (![⟨316640, by decide⟩,⟨316664, by decide⟩,⟨316686, by decide⟩,⟨316693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25881_316694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25881 ⟨316694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25881
    ⟨316694, by decide⟩ (by decide) (![⟨316640, by decide⟩,⟨316664, by decide⟩,⟨316686, by decide⟩,⟨316693, by decide⟩]) unmarked_context_12_25881_316694 node_context_12_25881_316694
  intro a
  fin_cases a
  · exact context_13_103524_316640
  · exact context_13_103525_316664
  · exact context_13_103526_316686
  · exact context_13_103527_316693

theorem selected_cut_11839 : selected 8 ⟨316724, by decide⟩
    (prefixPartial 13 103528) = some ⟨13, 2, 0, 316724, 103528, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_103528_316724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103528 ⟨316724, by decide⟩ :=
  accepted_of_selected 13 103528 ⟨316724, by decide⟩ ⟨13, 2, 0, 316724, 103528, 1693, 16384⟩
    (by decide) selected_cut_11839

theorem selected_cut_11840 : selected 8 ⟨316746, by decide⟩
    (prefixPartial 13 103529) = some ⟨13, 2, 0, 316746, 103529, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_103529_316746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103529 ⟨316746, by decide⟩ :=
  accepted_of_selected 13 103529 ⟨316746, by decide⟩ ⟨13, 2, 0, 316746, 103529, 1621, 16384⟩
    (by decide) selected_cut_11840

theorem selected_cut_11841 : selected 8 ⟨316766, by decide⟩
    (prefixPartial 13 103530) = some ⟨13, 2, 0, 316766, 103530, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_103530_316766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103530 ⟨316766, by decide⟩ :=
  accepted_of_selected 13 103530 ⟨316766, by decide⟩ ⟨13, 2, 0, 316766, 103530, 1513, 16384⟩
    (by decide) selected_cut_11841

theorem selected_cut_11842 : selected 8 ⟨316770, by decide⟩
    (prefixPartial 13 103531) = some ⟨13, 2, 0, 316770, 103531, 897, 16384⟩ := by
  decide +kernel

theorem context_13_103531_316770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103531 ⟨316770, by decide⟩ :=
  accepted_of_selected 13 103531 ⟨316770, by decide⟩ ⟨13, 2, 0, 316770, 103531, 897, 16384⟩
    (by decide) selected_cut_11842

theorem unmarked_context_12_25882_316771 : frontier 9 ⟨316771, by decide⟩
    (prefixCache 12 25882) (prefixPartial 12 25882) = false := by
  decide +kernel

theorem node_context_12_25882_316771 : EJMOriginalGlobalDAGData.nodes 9 ⟨316771, by decide⟩ =
    .split (coordinate 12) (![⟨316724, by decide⟩,⟨316746, by decide⟩,⟨316766, by decide⟩,⟨316770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25882_316771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25882 ⟨316771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25882
    ⟨316771, by decide⟩ (by decide) (![⟨316724, by decide⟩,⟨316746, by decide⟩,⟨316766, by decide⟩,⟨316770, by decide⟩]) unmarked_context_12_25882_316771 node_context_12_25882_316771
  intro a
  fin_cases a
  · exact context_13_103528_316724
  · exact context_13_103529_316746
  · exact context_13_103530_316766
  · exact context_13_103531_316770

theorem selected_cut_11843 : selected 8 ⟨316793, by decide⟩
    (prefixPartial 13 103532) = some ⟨13, 2, 0, 316793, 103532, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_103532_316793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103532 ⟨316793, by decide⟩ :=
  accepted_of_selected 13 103532 ⟨316793, by decide⟩ ⟨13, 2, 0, 316793, 103532, 1845, 16384⟩
    (by decide) selected_cut_11843

theorem selected_cut_11844 : selected 8 ⟨316826, by decide⟩
    (prefixPartial 13 103533) = some ⟨13, 2, 0, 316826, 103533, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_103533_316826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103533 ⟨316826, by decide⟩ :=
  accepted_of_selected 13 103533 ⟨316826, by decide⟩ ⟨13, 2, 0, 316826, 103533, 2165, 16384⟩
    (by decide) selected_cut_11844

theorem selected_cut_11845 : selected 8 ⟨316847, by decide⟩
    (prefixPartial 13 103534) = some ⟨13, 2, 0, 316847, 103534, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_103534_316847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103534 ⟨316847, by decide⟩ :=
  accepted_of_selected 13 103534 ⟨316847, by decide⟩ ⟨13, 2, 0, 316847, 103534, 1569, 16384⟩
    (by decide) selected_cut_11845

theorem selected_cut_11846 : selected 8 ⟨316855, by decide⟩
    (prefixPartial 13 103535) = some ⟨13, 2, 0, 316855, 103535, 989, 16384⟩ := by
  decide +kernel

theorem context_13_103535_316855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103535 ⟨316855, by decide⟩ :=
  accepted_of_selected 13 103535 ⟨316855, by decide⟩ ⟨13, 2, 0, 316855, 103535, 989, 16384⟩
    (by decide) selected_cut_11846

theorem unmarked_context_12_25883_316856 : frontier 9 ⟨316856, by decide⟩
    (prefixCache 12 25883) (prefixPartial 12 25883) = false := by
  decide +kernel

theorem node_context_12_25883_316856 : EJMOriginalGlobalDAGData.nodes 9 ⟨316856, by decide⟩ =
    .split (coordinate 12) (![⟨316793, by decide⟩,⟨316826, by decide⟩,⟨316847, by decide⟩,⟨316855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25883_316856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25883 ⟨316856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25883
    ⟨316856, by decide⟩ (by decide) (![⟨316793, by decide⟩,⟨316826, by decide⟩,⟨316847, by decide⟩,⟨316855, by decide⟩]) unmarked_context_12_25883_316856 node_context_12_25883_316856
  intro a
  fin_cases a
  · exact context_13_103532_316793
  · exact context_13_103533_316826
  · exact context_13_103534_316847
  · exact context_13_103535_316855

theorem unmarked_context_11_6470_316857 : frontier 10 ⟨316857, by decide⟩
    (prefixCache 11 6470) (prefixPartial 11 6470) = false := by
  decide +kernel

theorem node_context_11_6470_316857 : EJMOriginalGlobalDAGData.nodes 10 ⟨316857, by decide⟩ =
    .split (coordinate 11) (![⟨316620, by decide⟩,⟨316694, by decide⟩,⟨316771, by decide⟩,⟨316856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6470_316857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6470 ⟨316857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6470
    ⟨316857, by decide⟩ (by decide) (![⟨316620, by decide⟩,⟨316694, by decide⟩,⟨316771, by decide⟩,⟨316856, by decide⟩]) unmarked_context_11_6470_316857 node_context_11_6470_316857
  intro a
  fin_cases a
  · exact context_12_25880_316620
  · exact context_12_25881_316694
  · exact context_12_25882_316771
  · exact context_12_25883_316856

theorem selected_cut_11847 : selected 8 ⟨316869, by decide⟩
    (prefixPartial 13 103536) = some ⟨13, 2, 0, 316869, 103536, 981, 16384⟩ := by
  decide +kernel

theorem context_13_103536_316869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103536 ⟨316869, by decide⟩ :=
  accepted_of_selected 13 103536 ⟨316869, by decide⟩ ⟨13, 2, 0, 316869, 103536, 981, 16384⟩
    (by decide) selected_cut_11847

theorem selected_cut_11848 : selected 8 ⟨316894, by decide⟩
    (prefixPartial 13 103537) = some ⟨13, 2, 0, 316894, 103537, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_103537_316894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103537 ⟨316894, by decide⟩ :=
  accepted_of_selected 13 103537 ⟨316894, by decide⟩ ⟨13, 2, 0, 316894, 103537, 1717, 16384⟩
    (by decide) selected_cut_11848

theorem selected_cut_11849 : selected 8 ⟨316912, by decide⟩
    (prefixPartial 13 103538) = some ⟨13, 2, 0, 316912, 103538, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_103538_316912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103538 ⟨316912, by decide⟩ :=
  accepted_of_selected 13 103538 ⟨316912, by decide⟩ ⟨13, 2, 0, 316912, 103538, 1353, 16384⟩
    (by decide) selected_cut_11849

theorem selected_cut_11850 : selected 8 ⟨316919, by decide⟩
    (prefixPartial 13 103539) = some ⟨13, 2, 0, 316919, 103539, 821, 16384⟩ := by
  decide +kernel

theorem context_13_103539_316919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103539 ⟨316919, by decide⟩ :=
  accepted_of_selected 13 103539 ⟨316919, by decide⟩ ⟨13, 2, 0, 316919, 103539, 821, 16384⟩
    (by decide) selected_cut_11850

theorem unmarked_context_12_25884_316920 : frontier 9 ⟨316920, by decide⟩
    (prefixCache 12 25884) (prefixPartial 12 25884) = false := by
  decide +kernel

theorem node_context_12_25884_316920 : EJMOriginalGlobalDAGData.nodes 9 ⟨316920, by decide⟩ =
    .split (coordinate 12) (![⟨316869, by decide⟩,⟨316894, by decide⟩,⟨316912, by decide⟩,⟨316919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25884_316920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25884 ⟨316920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25884
    ⟨316920, by decide⟩ (by decide) (![⟨316869, by decide⟩,⟨316894, by decide⟩,⟨316912, by decide⟩,⟨316919, by decide⟩]) unmarked_context_12_25884_316920 node_context_12_25884_316920
  intro a
  fin_cases a
  · exact context_13_103536_316869
  · exact context_13_103537_316894
  · exact context_13_103538_316912
  · exact context_13_103539_316919

theorem selected_cut_11851 : selected 8 ⟨316941, by decide⟩
    (prefixPartial 13 103540) = some ⟨13, 2, 0, 316941, 103540, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_103540_316941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103540 ⟨316941, by decide⟩ :=
  accepted_of_selected 13 103540 ⟨316941, by decide⟩ ⟨13, 2, 0, 316941, 103540, 1305, 16384⟩
    (by decide) selected_cut_11851

theorem selected_cut_11852 : selected 8 ⟨316963, by decide⟩
    (prefixPartial 13 103541) = some ⟨13, 2, 0, 316963, 103541, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_103541_316963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103541 ⟨316963, by decide⟩ :=
  accepted_of_selected 13 103541 ⟨316963, by decide⟩ ⟨13, 2, 0, 316963, 103541, 1225, 16384⟩
    (by decide) selected_cut_11852

theorem selected_cut_11853 : selected 8 ⟨316982, by decide⟩
    (prefixPartial 13 103542) = some ⟨13, 2, 0, 316982, 103542, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_103542_316982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103542 ⟨316982, by decide⟩ :=
  accepted_of_selected 13 103542 ⟨316982, by decide⟩ ⟨13, 2, 0, 316982, 103542, 1393, 16384⟩
    (by decide) selected_cut_11853

theorem selected_cut_11854 : selected 8 ⟨316988, by decide⟩
    (prefixPartial 13 103543) = some ⟨13, 2, 0, 316988, 103543, 681, 16384⟩ := by
  decide +kernel

theorem context_13_103543_316988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103543 ⟨316988, by decide⟩ :=
  accepted_of_selected 13 103543 ⟨316988, by decide⟩ ⟨13, 2, 0, 316988, 103543, 681, 16384⟩
    (by decide) selected_cut_11854

theorem unmarked_context_12_25885_316989 : frontier 9 ⟨316989, by decide⟩
    (prefixCache 12 25885) (prefixPartial 12 25885) = false := by
  decide +kernel

theorem node_context_12_25885_316989 : EJMOriginalGlobalDAGData.nodes 9 ⟨316989, by decide⟩ =
    .split (coordinate 12) (![⟨316941, by decide⟩,⟨316963, by decide⟩,⟨316982, by decide⟩,⟨316988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25885_316989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25885 ⟨316989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25885
    ⟨316989, by decide⟩ (by decide) (![⟨316941, by decide⟩,⟨316963, by decide⟩,⟨316982, by decide⟩,⟨316988, by decide⟩]) unmarked_context_12_25885_316989 node_context_12_25885_316989
  intro a
  fin_cases a
  · exact context_13_103540_316941
  · exact context_13_103541_316963
  · exact context_13_103542_316982
  · exact context_13_103543_316988

theorem selected_cut_11855 : selected 8 ⟨317019, by decide⟩
    (prefixPartial 13 103544) = some ⟨13, 2, 0, 317019, 103544, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_103544_317019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103544 ⟨317019, by decide⟩ :=
  accepted_of_selected 13 103544 ⟨317019, by decide⟩ ⟨13, 2, 0, 317019, 103544, 1513, 16384⟩
    (by decide) selected_cut_11855

theorem selected_cut_11856 : selected 8 ⟨317043, by decide⟩
    (prefixPartial 13 103545) = some ⟨13, 2, 0, 317043, 103545, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_103545_317043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103545 ⟨317043, by decide⟩ :=
  accepted_of_selected 13 103545 ⟨317043, by decide⟩ ⟨13, 2, 0, 317043, 103545, 1853, 16384⟩
    (by decide) selected_cut_11856

theorem selected_cut_11857 : selected 8 ⟨317064, by decide⟩
    (prefixPartial 13 103546) = some ⟨13, 2, 0, 317064, 103546, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_103546_317064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103546 ⟨317064, by decide⟩ :=
  accepted_of_selected 13 103546 ⟨317064, by decide⟩ ⟨13, 2, 0, 317064, 103546, 1417, 16384⟩
    (by decide) selected_cut_11857

theorem selected_cut_11858 : selected 8 ⟨317071, by decide⟩
    (prefixPartial 13 103547) = some ⟨13, 2, 0, 317071, 103547, 821, 16384⟩ := by
  decide +kernel

theorem context_13_103547_317071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103547 ⟨317071, by decide⟩ :=
  accepted_of_selected 13 103547 ⟨317071, by decide⟩ ⟨13, 2, 0, 317071, 103547, 821, 16384⟩
    (by decide) selected_cut_11858

theorem unmarked_context_12_25886_317072 : frontier 9 ⟨317072, by decide⟩
    (prefixCache 12 25886) (prefixPartial 12 25886) = false := by
  decide +kernel

theorem node_context_12_25886_317072 : EJMOriginalGlobalDAGData.nodes 9 ⟨317072, by decide⟩ =
    .split (coordinate 12) (![⟨317019, by decide⟩,⟨317043, by decide⟩,⟨317064, by decide⟩,⟨317071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25886_317072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25886 ⟨317072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25886
    ⟨317072, by decide⟩ (by decide) (![⟨317019, by decide⟩,⟨317043, by decide⟩,⟨317064, by decide⟩,⟨317071, by decide⟩]) unmarked_context_12_25886_317072 node_context_12_25886_317072
  intro a
  fin_cases a
  · exact context_13_103544_317019
  · exact context_13_103545_317043
  · exact context_13_103546_317064
  · exact context_13_103547_317071

theorem selected_cut_11859 : selected 8 ⟨317100, by decide⟩
    (prefixPartial 13 103548) = some ⟨13, 2, 0, 317100, 103548, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_103548_317100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103548 ⟨317100, by decide⟩ :=
  accepted_of_selected 13 103548 ⟨317100, by decide⟩ ⟨13, 2, 0, 317100, 103548, 1653, 16384⟩
    (by decide) selected_cut_11859

theorem selected_cut_11860 : selected 8 ⟨317124, by decide⟩
    (prefixPartial 13 103549) = some ⟨13, 2, 0, 317124, 103549, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_103549_317124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103549 ⟨317124, by decide⟩ :=
  accepted_of_selected 13 103549 ⟨317124, by decide⟩ ⟨13, 2, 0, 317124, 103549, 1909, 16384⟩
    (by decide) selected_cut_11860

theorem selected_cut_11861 : selected 8 ⟨317146, by decide⟩
    (prefixPartial 13 103550) = some ⟨13, 2, 0, 317146, 103550, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_103550_317146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103550 ⟨317146, by decide⟩ :=
  accepted_of_selected 13 103550 ⟨317146, by decide⟩ ⟨13, 2, 0, 317146, 103550, 1565, 16384⟩
    (by decide) selected_cut_11861

theorem selected_cut_11862 : selected 8 ⟨317153, by decide⟩
    (prefixPartial 13 103551) = some ⟨13, 2, 0, 317153, 103551, 941, 16384⟩ := by
  decide +kernel

theorem context_13_103551_317153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103551 ⟨317153, by decide⟩ :=
  accepted_of_selected 13 103551 ⟨317153, by decide⟩ ⟨13, 2, 0, 317153, 103551, 941, 16384⟩
    (by decide) selected_cut_11862

theorem unmarked_context_12_25887_317154 : frontier 9 ⟨317154, by decide⟩
    (prefixCache 12 25887) (prefixPartial 12 25887) = false := by
  decide +kernel

theorem node_context_12_25887_317154 : EJMOriginalGlobalDAGData.nodes 9 ⟨317154, by decide⟩ =
    .split (coordinate 12) (![⟨317100, by decide⟩,⟨317124, by decide⟩,⟨317146, by decide⟩,⟨317153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25887_317154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25887 ⟨317154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25887
    ⟨317154, by decide⟩ (by decide) (![⟨317100, by decide⟩,⟨317124, by decide⟩,⟨317146, by decide⟩,⟨317153, by decide⟩]) unmarked_context_12_25887_317154 node_context_12_25887_317154
  intro a
  fin_cases a
  · exact context_13_103548_317100
  · exact context_13_103549_317124
  · exact context_13_103550_317146
  · exact context_13_103551_317153

theorem unmarked_context_11_6471_317155 : frontier 10 ⟨317155, by decide⟩
    (prefixCache 11 6471) (prefixPartial 11 6471) = false := by
  decide +kernel

theorem node_context_11_6471_317155 : EJMOriginalGlobalDAGData.nodes 10 ⟨317155, by decide⟩ =
    .split (coordinate 11) (![⟨316920, by decide⟩,⟨316989, by decide⟩,⟨317072, by decide⟩,⟨317154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6471_317155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6471 ⟨317155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6471
    ⟨317155, by decide⟩ (by decide) (![⟨316920, by decide⟩,⟨316989, by decide⟩,⟨317072, by decide⟩,⟨317154, by decide⟩]) unmarked_context_11_6471_317155 node_context_11_6471_317155
  intro a
  fin_cases a
  · exact context_12_25884_316920
  · exact context_12_25885_316989
  · exact context_12_25886_317072
  · exact context_12_25887_317154

theorem unmarked_context_10_1617_317156 : frontier 11 ⟨317156, by decide⟩
    (prefixCache 10 1617) (prefixPartial 10 1617) = false := by
  decide +kernel

theorem node_context_10_1617_317156 : EJMOriginalGlobalDAGData.nodes 11 ⟨317156, by decide⟩ =
    .split (coordinate 10) (![⟨316178, by decide⟩,⟨316551, by decide⟩,⟨316857, by decide⟩,⟨317155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1617_317156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1617 ⟨317156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1617
    ⟨317156, by decide⟩ (by decide) (![⟨316178, by decide⟩,⟨316551, by decide⟩,⟨316857, by decide⟩,⟨317155, by decide⟩]) unmarked_context_10_1617_317156 node_context_10_1617_317156
  intro a
  fin_cases a
  · exact context_11_6468_316178
  · exact context_11_6469_316551
  · exact context_11_6470_316857
  · exact context_11_6471_317155

theorem selected_cut_11863 : selected 8 ⟨317168, by decide⟩
    (prefixPartial 13 103552) = some ⟨13, 2, 0, 317168, 103552, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_103552_317168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103552 ⟨317168, by decide⟩ :=
  accepted_of_selected 13 103552 ⟨317168, by decide⟩ ⟨13, 2, 0, 317168, 103552, 1121, 16384⟩
    (by decide) selected_cut_11863

theorem selected_cut_11864 : selected 8 ⟨317199, by decide⟩
    (prefixPartial 13 103553) = some ⟨13, 2, 0, 317199, 103553, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_103553_317199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103553 ⟨317199, by decide⟩ :=
  accepted_of_selected 13 103553 ⟨317199, by decide⟩ ⟨13, 2, 0, 317199, 103553, 1905, 16384⟩
    (by decide) selected_cut_11864

theorem selected_cut_11865 : selected 8 ⟨317216, by decide⟩
    (prefixPartial 13 103554) = some ⟨13, 2, 0, 317216, 103554, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_103554_317216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103554 ⟨317216, by decide⟩ :=
  accepted_of_selected 13 103554 ⟨317216, by decide⟩ ⟨13, 2, 0, 317216, 103554, 1169, 16384⟩
    (by decide) selected_cut_11865

theorem selected_cut_11866 : selected 8 ⟨317223, by decide⟩
    (prefixPartial 13 103555) = some ⟨13, 2, 0, 317223, 103555, 877, 16384⟩ := by
  decide +kernel

theorem context_13_103555_317223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103555 ⟨317223, by decide⟩ :=
  accepted_of_selected 13 103555 ⟨317223, by decide⟩ ⟨13, 2, 0, 317223, 103555, 877, 16384⟩
    (by decide) selected_cut_11866

theorem unmarked_context_12_25888_317224 : frontier 9 ⟨317224, by decide⟩
    (prefixCache 12 25888) (prefixPartial 12 25888) = false := by
  decide +kernel

theorem node_context_12_25888_317224 : EJMOriginalGlobalDAGData.nodes 9 ⟨317224, by decide⟩ =
    .split (coordinate 12) (![⟨317168, by decide⟩,⟨317199, by decide⟩,⟨317216, by decide⟩,⟨317223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25888_317224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25888 ⟨317224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25888
    ⟨317224, by decide⟩ (by decide) (![⟨317168, by decide⟩,⟨317199, by decide⟩,⟨317216, by decide⟩,⟨317223, by decide⟩]) unmarked_context_12_25888_317224 node_context_12_25888_317224
  intro a
  fin_cases a
  · exact context_13_103552_317168
  · exact context_13_103553_317199
  · exact context_13_103554_317216
  · exact context_13_103555_317223

theorem selected_cut_11867 : selected 8 ⟨317251, by decide⟩
    (prefixPartial 13 103556) = some ⟨13, 2, 0, 317251, 103556, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_103556_317251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103556 ⟨317251, by decide⟩ :=
  accepted_of_selected 13 103556 ⟨317251, by decide⟩ ⟨13, 2, 0, 317251, 103556, 1493, 16384⟩
    (by decide) selected_cut_11867

theorem selected_cut_11868 : selected 8 ⟨317276, by decide⟩
    (prefixPartial 13 103557) = some ⟨13, 2, 0, 317276, 103557, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_103557_317276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103557 ⟨317276, by decide⟩ :=
  accepted_of_selected 13 103557 ⟨317276, by decide⟩ ⟨13, 2, 0, 317276, 103557, 2145, 16384⟩
    (by decide) selected_cut_11868

theorem selected_cut_11869 : selected 8 ⟨317295, by decide⟩
    (prefixPartial 13 103558) = some ⟨13, 2, 0, 317295, 103558, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_103558_317295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103558 ⟨317295, by decide⟩ :=
  accepted_of_selected 13 103558 ⟨317295, by decide⟩ ⟨13, 2, 0, 317295, 103558, 1565, 16384⟩
    (by decide) selected_cut_11869

theorem selected_cut_11870 : selected 8 ⟨317303, by decide⟩
    (prefixPartial 13 103559) = some ⟨13, 2, 0, 317303, 103559, 989, 16384⟩ := by
  decide +kernel

theorem context_13_103559_317303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103559 ⟨317303, by decide⟩ :=
  accepted_of_selected 13 103559 ⟨317303, by decide⟩ ⟨13, 2, 0, 317303, 103559, 989, 16384⟩
    (by decide) selected_cut_11870

theorem unmarked_context_12_25889_317304 : frontier 9 ⟨317304, by decide⟩
    (prefixCache 12 25889) (prefixPartial 12 25889) = false := by
  decide +kernel

theorem node_context_12_25889_317304 : EJMOriginalGlobalDAGData.nodes 9 ⟨317304, by decide⟩ =
    .split (coordinate 12) (![⟨317251, by decide⟩,⟨317276, by decide⟩,⟨317295, by decide⟩,⟨317303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25889_317304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25889 ⟨317304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25889
    ⟨317304, by decide⟩ (by decide) (![⟨317251, by decide⟩,⟨317276, by decide⟩,⟨317295, by decide⟩,⟨317303, by decide⟩]) unmarked_context_12_25889_317304 node_context_12_25889_317304
  intro a
  fin_cases a
  · exact context_13_103556_317251
  · exact context_13_103557_317276
  · exact context_13_103558_317295
  · exact context_13_103559_317303

theorem selected_cut_11871 : selected 8 ⟨317336, by decide⟩
    (prefixPartial 13 103560) = some ⟨13, 2, 0, 317336, 103560, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_103560_317336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103560 ⟨317336, by decide⟩ :=
  accepted_of_selected 13 103560 ⟨317336, by decide⟩ ⟨13, 2, 0, 317336, 103560, 1657, 16384⟩
    (by decide) selected_cut_11871

theorem selected_cut_11872 : selected 8 ⟨317374, by decide⟩
    (prefixPartial 13 103561) = some ⟨13, 2, 0, 317374, 103561, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_103561_317374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103561 ⟨317374, by decide⟩ :=
  accepted_of_selected 13 103561 ⟨317374, by decide⟩ ⟨13, 2, 0, 317374, 103561, 2293, 16384⟩
    (by decide) selected_cut_11872

theorem selected_cut_11873 : selected 8 ⟨317396, by decide⟩
    (prefixPartial 13 103562) = some ⟨13, 2, 0, 317396, 103562, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_103562_317396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103562 ⟨317396, by decide⟩ :=
  accepted_of_selected 13 103562 ⟨317396, by decide⟩ ⟨13, 2, 0, 317396, 103562, 1505, 16384⟩
    (by decide) selected_cut_11873

theorem selected_cut_11874 : selected 8 ⟨317406, by decide⟩
    (prefixPartial 13 103563) = some ⟨13, 2, 0, 317406, 103563, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_103563_317406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103563 ⟨317406, by decide⟩ :=
  accepted_of_selected 13 103563 ⟨317406, by decide⟩ ⟨13, 2, 0, 317406, 103563, 1065, 16384⟩
    (by decide) selected_cut_11874

theorem unmarked_context_12_25890_317407 : frontier 9 ⟨317407, by decide⟩
    (prefixCache 12 25890) (prefixPartial 12 25890) = false := by
  decide +kernel

theorem node_context_12_25890_317407 : EJMOriginalGlobalDAGData.nodes 9 ⟨317407, by decide⟩ =
    .split (coordinate 12) (![⟨317336, by decide⟩,⟨317374, by decide⟩,⟨317396, by decide⟩,⟨317406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25890_317407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25890 ⟨317407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25890
    ⟨317407, by decide⟩ (by decide) (![⟨317336, by decide⟩,⟨317374, by decide⟩,⟨317396, by decide⟩,⟨317406, by decide⟩]) unmarked_context_12_25890_317407 node_context_12_25890_317407
  intro a
  fin_cases a
  · exact context_13_103560_317336
  · exact context_13_103561_317374
  · exact context_13_103562_317396
  · exact context_13_103563_317406

theorem selected_cut_11875 : selected 8 ⟨317435, by decide⟩
    (prefixPartial 13 103564) = some ⟨13, 2, 0, 317435, 103564, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_103564_317435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103564 ⟨317435, by decide⟩ :=
  accepted_of_selected 13 103564 ⟨317435, by decide⟩ ⟨13, 2, 0, 317435, 103564, 1717, 16384⟩
    (by decide) selected_cut_11875

theorem selected_cut_11876 : selected 8 ⟨317470, by decide⟩
    (prefixPartial 13 103565) = some ⟨13, 2, 0, 317470, 103565, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_103565_317470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103565 ⟨317470, by decide⟩ :=
  accepted_of_selected 13 103565 ⟨317470, by decide⟩ ⟨13, 2, 0, 317470, 103565, 2561, 16384⟩
    (by decide) selected_cut_11876

theorem selected_cut_11877 : selected 8 ⟨317498, by decide⟩
    (prefixPartial 13 103566) = some ⟨13, 2, 0, 317498, 103566, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_103566_317498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103566 ⟨317498, by decide⟩ :=
  accepted_of_selected 13 103566 ⟨317498, by decide⟩ ⟨13, 2, 0, 317498, 103566, 1705, 16384⟩
    (by decide) selected_cut_11877

theorem selected_cut_11878 : selected 8 ⟨317509, by decide⟩
    (prefixPartial 13 103567) = some ⟨13, 2, 0, 317509, 103567, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_103567_317509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103567 ⟨317509, by decide⟩ :=
  accepted_of_selected 13 103567 ⟨317509, by decide⟩ ⟨13, 2, 0, 317509, 103567, 1089, 16384⟩
    (by decide) selected_cut_11878

theorem unmarked_context_12_25891_317510 : frontier 9 ⟨317510, by decide⟩
    (prefixCache 12 25891) (prefixPartial 12 25891) = false := by
  decide +kernel

theorem node_context_12_25891_317510 : EJMOriginalGlobalDAGData.nodes 9 ⟨317510, by decide⟩ =
    .split (coordinate 12) (![⟨317435, by decide⟩,⟨317470, by decide⟩,⟨317498, by decide⟩,⟨317509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25891_317510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25891 ⟨317510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25891
    ⟨317510, by decide⟩ (by decide) (![⟨317435, by decide⟩,⟨317470, by decide⟩,⟨317498, by decide⟩,⟨317509, by decide⟩]) unmarked_context_12_25891_317510 node_context_12_25891_317510
  intro a
  fin_cases a
  · exact context_13_103564_317435
  · exact context_13_103565_317470
  · exact context_13_103566_317498
  · exact context_13_103567_317509

theorem unmarked_context_11_6472_317511 : frontier 10 ⟨317511, by decide⟩
    (prefixCache 11 6472) (prefixPartial 11 6472) = false := by
  decide +kernel

theorem node_context_11_6472_317511 : EJMOriginalGlobalDAGData.nodes 10 ⟨317511, by decide⟩ =
    .split (coordinate 11) (![⟨317224, by decide⟩,⟨317304, by decide⟩,⟨317407, by decide⟩,⟨317510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6472_317511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6472 ⟨317511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6472
    ⟨317511, by decide⟩ (by decide) (![⟨317224, by decide⟩,⟨317304, by decide⟩,⟨317407, by decide⟩,⟨317510, by decide⟩]) unmarked_context_11_6472_317511 node_context_11_6472_317511
  intro a
  fin_cases a
  · exact context_12_25888_317224
  · exact context_12_25889_317304
  · exact context_12_25890_317407
  · exact context_12_25891_317510

theorem selected_cut_11879 : selected 8 ⟨317521, by decide⟩
    (prefixPartial 13 103568) = some ⟨13, 2, 0, 317521, 103568, 833, 16384⟩ := by
  decide +kernel

theorem context_13_103568_317521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103568 ⟨317521, by decide⟩ :=
  accepted_of_selected 13 103568 ⟨317521, by decide⟩ ⟨13, 2, 0, 317521, 103568, 833, 16384⟩
    (by decide) selected_cut_11879

theorem selected_cut_11880 : selected 8 ⟨317543, by decide⟩
    (prefixPartial 13 103569) = some ⟨13, 2, 0, 317543, 103569, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_103569_317543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103569 ⟨317543, by decide⟩ :=
  accepted_of_selected 13 103569 ⟨317543, by decide⟩ ⟨13, 2, 0, 317543, 103569, 1625, 16384⟩
    (by decide) selected_cut_11880

theorem selected_cut_11881 : selected 8 ⟨317558, by decide⟩
    (prefixPartial 13 103570) = some ⟨13, 2, 0, 317558, 103570, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_103570_317558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103570 ⟨317558, by decide⟩ :=
  accepted_of_selected 13 103570 ⟨317558, by decide⟩ ⟨13, 2, 0, 317558, 103570, 1213, 16384⟩
    (by decide) selected_cut_11881

theorem selected_cut_11882 : selected 8 ⟨317566, by decide⟩
    (prefixPartial 13 103571) = some ⟨13, 2, 0, 317566, 103571, 805, 16384⟩ := by
  decide +kernel

theorem context_13_103571_317566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103571 ⟨317566, by decide⟩ :=
  accepted_of_selected 13 103571 ⟨317566, by decide⟩ ⟨13, 2, 0, 317566, 103571, 805, 16384⟩
    (by decide) selected_cut_11882

theorem unmarked_context_12_25892_317567 : frontier 9 ⟨317567, by decide⟩
    (prefixCache 12 25892) (prefixPartial 12 25892) = false := by
  decide +kernel

theorem node_context_12_25892_317567 : EJMOriginalGlobalDAGData.nodes 9 ⟨317567, by decide⟩ =
    .split (coordinate 12) (![⟨317521, by decide⟩,⟨317543, by decide⟩,⟨317558, by decide⟩,⟨317566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25892_317567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25892 ⟨317567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25892
    ⟨317567, by decide⟩ (by decide) (![⟨317521, by decide⟩,⟨317543, by decide⟩,⟨317558, by decide⟩,⟨317566, by decide⟩]) unmarked_context_12_25892_317567 node_context_12_25892_317567
  intro a
  fin_cases a
  · exact context_13_103568_317521
  · exact context_13_103569_317543
  · exact context_13_103570_317558
  · exact context_13_103571_317566

theorem selected_cut_11883 : selected 8 ⟨317594, by decide⟩
    (prefixPartial 13 103572) = some ⟨13, 2, 0, 317594, 103572, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_103572_317594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103572 ⟨317594, by decide⟩ :=
  accepted_of_selected 13 103572 ⟨317594, by decide⟩ ⟨13, 2, 0, 317594, 103572, 1749, 16384⟩
    (by decide) selected_cut_11883

theorem selected_cut_11884 : selected 8 ⟨317630, by decide⟩
    (prefixPartial 13 103573) = some ⟨13, 2, 0, 317630, 103573, 3237, 16384⟩ := by
  decide +kernel

theorem context_13_103573_317630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103573 ⟨317630, by decide⟩ :=
  accepted_of_selected 13 103573 ⟨317630, by decide⟩ ⟨13, 2, 0, 317630, 103573, 3237, 16384⟩
    (by decide) selected_cut_11884

theorem selected_cut_11885 : selected 8 ⟨317646, by decide⟩
    (prefixPartial 13 103574) = some ⟨13, 2, 0, 317646, 103574, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_103574_317646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103574 ⟨317646, by decide⟩ :=
  accepted_of_selected 13 103574 ⟨317646, by decide⟩ ⟨13, 2, 0, 317646, 103574, 2193, 16384⟩
    (by decide) selected_cut_11885

theorem selected_cut_11886 : selected 8 ⟨317654, by decide⟩
    (prefixPartial 13 103575) = some ⟨13, 2, 0, 317654, 103575, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_103575_317654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103575 ⟨317654, by decide⟩ :=
  accepted_of_selected 13 103575 ⟨317654, by decide⟩ ⟨13, 2, 0, 317654, 103575, 1161, 16384⟩
    (by decide) selected_cut_11886

theorem unmarked_context_12_25893_317655 : frontier 9 ⟨317655, by decide⟩
    (prefixCache 12 25893) (prefixPartial 12 25893) = false := by
  decide +kernel

theorem node_context_12_25893_317655 : EJMOriginalGlobalDAGData.nodes 9 ⟨317655, by decide⟩ =
    .split (coordinate 12) (![⟨317594, by decide⟩,⟨317630, by decide⟩,⟨317646, by decide⟩,⟨317654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25893_317655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25893 ⟨317655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25893
    ⟨317655, by decide⟩ (by decide) (![⟨317594, by decide⟩,⟨317630, by decide⟩,⟨317646, by decide⟩,⟨317654, by decide⟩]) unmarked_context_12_25893_317655 node_context_12_25893_317655
  intro a
  fin_cases a
  · exact context_13_103572_317594
  · exact context_13_103573_317630
  · exact context_13_103574_317646
  · exact context_13_103575_317654

theorem selected_cut_11887 : selected 8 ⟨317677, by decide⟩
    (prefixPartial 13 103576) = some ⟨13, 2, 0, 317677, 103576, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_103576_317677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103576 ⟨317677, by decide⟩ :=
  accepted_of_selected 13 103576 ⟨317677, by decide⟩ ⟨13, 2, 0, 317677, 103576, 1181, 16384⟩
    (by decide) selected_cut_11887

theorem selected_cut_11888 : selected 8 ⟨317707, by decide⟩
    (prefixPartial 13 103577) = some ⟨13, 2, 0, 317707, 103577, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_103577_317707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103577 ⟨317707, by decide⟩ :=
  accepted_of_selected 13 103577 ⟨317707, by decide⟩ ⟨13, 2, 0, 317707, 103577, 1925, 16384⟩
    (by decide) selected_cut_11888

theorem selected_cut_11889 : selected 8 ⟨317724, by decide⟩
    (prefixPartial 13 103578) = some ⟨13, 2, 0, 317724, 103578, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_103578_317724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103578 ⟨317724, by decide⟩ :=
  accepted_of_selected 13 103578 ⟨317724, by decide⟩ ⟨13, 2, 0, 317724, 103578, 1253, 16384⟩
    (by decide) selected_cut_11889

theorem selected_cut_11890 : selected 8 ⟨317732, by decide⟩
    (prefixPartial 13 103579) = some ⟨13, 2, 0, 317732, 103579, 941, 16384⟩ := by
  decide +kernel

theorem context_13_103579_317732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103579 ⟨317732, by decide⟩ :=
  accepted_of_selected 13 103579 ⟨317732, by decide⟩ ⟨13, 2, 0, 317732, 103579, 941, 16384⟩
    (by decide) selected_cut_11890

theorem unmarked_context_12_25894_317733 : frontier 9 ⟨317733, by decide⟩
    (prefixCache 12 25894) (prefixPartial 12 25894) = false := by
  decide +kernel

theorem node_context_12_25894_317733 : EJMOriginalGlobalDAGData.nodes 9 ⟨317733, by decide⟩ =
    .split (coordinate 12) (![⟨317677, by decide⟩,⟨317707, by decide⟩,⟨317724, by decide⟩,⟨317732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25894_317733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25894 ⟨317733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25894
    ⟨317733, by decide⟩ (by decide) (![⟨317677, by decide⟩,⟨317707, by decide⟩,⟨317724, by decide⟩,⟨317732, by decide⟩]) unmarked_context_12_25894_317733 node_context_12_25894_317733
  intro a
  fin_cases a
  · exact context_13_103576_317677
  · exact context_13_103577_317707
  · exact context_13_103578_317724
  · exact context_13_103579_317732

theorem selected_cut_11891 : selected 8 ⟨317748, by decide⟩
    (prefixPartial 13 103580) = some ⟨13, 2, 0, 317748, 103580, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_103580_317748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103580 ⟨317748, by decide⟩ :=
  accepted_of_selected 13 103580 ⟨317748, by decide⟩ ⟨13, 2, 0, 317748, 103580, 1141, 16384⟩
    (by decide) selected_cut_11891

theorem selected_cut_11892 : selected 8 ⟨317778, by decide⟩
    (prefixPartial 13 103581) = some ⟨13, 2, 0, 317778, 103581, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_103581_317778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103581 ⟨317778, by decide⟩ :=
  accepted_of_selected 13 103581 ⟨317778, by decide⟩ ⟨13, 2, 0, 317778, 103581, 2281, 16384⟩
    (by decide) selected_cut_11892

theorem selected_cut_11893 : selected 8 ⟨317797, by decide⟩
    (prefixPartial 13 103582) = some ⟨13, 2, 0, 317797, 103582, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_103582_317797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103582 ⟨317797, by decide⟩ :=
  accepted_of_selected 13 103582 ⟨317797, by decide⟩ ⟨13, 2, 0, 317797, 103582, 1449, 16384⟩
    (by decide) selected_cut_11893

theorem selected_cut_11894 : selected 8 ⟨317802, by decide⟩
    (prefixPartial 13 103583) = some ⟨13, 2, 0, 317802, 103583, 905, 16384⟩ := by
  decide +kernel

theorem context_13_103583_317802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103583 ⟨317802, by decide⟩ :=
  accepted_of_selected 13 103583 ⟨317802, by decide⟩ ⟨13, 2, 0, 317802, 103583, 905, 16384⟩
    (by decide) selected_cut_11894

theorem unmarked_context_12_25895_317803 : frontier 9 ⟨317803, by decide⟩
    (prefixCache 12 25895) (prefixPartial 12 25895) = false := by
  decide +kernel

theorem node_context_12_25895_317803 : EJMOriginalGlobalDAGData.nodes 9 ⟨317803, by decide⟩ =
    .split (coordinate 12) (![⟨317748, by decide⟩,⟨317778, by decide⟩,⟨317797, by decide⟩,⟨317802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25895_317803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25895 ⟨317803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25895
    ⟨317803, by decide⟩ (by decide) (![⟨317748, by decide⟩,⟨317778, by decide⟩,⟨317797, by decide⟩,⟨317802, by decide⟩]) unmarked_context_12_25895_317803 node_context_12_25895_317803
  intro a
  fin_cases a
  · exact context_13_103580_317748
  · exact context_13_103581_317778
  · exact context_13_103582_317797
  · exact context_13_103583_317802

theorem unmarked_context_11_6473_317804 : frontier 10 ⟨317804, by decide⟩
    (prefixCache 11 6473) (prefixPartial 11 6473) = false := by
  decide +kernel

theorem node_context_11_6473_317804 : EJMOriginalGlobalDAGData.nodes 10 ⟨317804, by decide⟩ =
    .split (coordinate 11) (![⟨317567, by decide⟩,⟨317655, by decide⟩,⟨317733, by decide⟩,⟨317803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6473_317804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6473 ⟨317804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6473
    ⟨317804, by decide⟩ (by decide) (![⟨317567, by decide⟩,⟨317655, by decide⟩,⟨317733, by decide⟩,⟨317803, by decide⟩]) unmarked_context_11_6473_317804 node_context_11_6473_317804
  intro a
  fin_cases a
  · exact context_12_25892_317567
  · exact context_12_25893_317655
  · exact context_12_25894_317733
  · exact context_12_25895_317803

theorem selected_cut_11895 : selected 8 ⟨317814, by decide⟩
    (prefixPartial 13 103584) = some ⟨13, 2, 0, 317814, 103584, 845, 16384⟩ := by
  decide +kernel

theorem context_13_103584_317814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103584 ⟨317814, by decide⟩ :=
  accepted_of_selected 13 103584 ⟨317814, by decide⟩ ⟨13, 2, 0, 317814, 103584, 845, 16384⟩
    (by decide) selected_cut_11895

theorem selected_cut_11896 : selected 8 ⟨317842, by decide⟩
    (prefixPartial 13 103585) = some ⟨13, 2, 0, 317842, 103585, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_103585_317842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103585 ⟨317842, by decide⟩ :=
  accepted_of_selected 13 103585 ⟨317842, by decide⟩ ⟨13, 2, 0, 317842, 103585, 1857, 16384⟩
    (by decide) selected_cut_11896

theorem selected_cut_11897 : selected 8 ⟨317860, by decide⟩
    (prefixPartial 13 103586) = some ⟨13, 2, 0, 317860, 103586, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_103586_317860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103586 ⟨317860, by decide⟩ :=
  accepted_of_selected 13 103586 ⟨317860, by decide⟩ ⟨13, 2, 0, 317860, 103586, 1621, 16384⟩
    (by decide) selected_cut_11897

theorem selected_cut_11898 : selected 8 ⟨317869, by decide⟩
    (prefixPartial 13 103587) = some ⟨13, 2, 0, 317869, 103587, 945, 16384⟩ := by
  decide +kernel

theorem context_13_103587_317869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103587 ⟨317869, by decide⟩ :=
  accepted_of_selected 13 103587 ⟨317869, by decide⟩ ⟨13, 2, 0, 317869, 103587, 945, 16384⟩
    (by decide) selected_cut_11898

theorem unmarked_context_12_25896_317870 : frontier 9 ⟨317870, by decide⟩
    (prefixCache 12 25896) (prefixPartial 12 25896) = false := by
  decide +kernel

theorem node_context_12_25896_317870 : EJMOriginalGlobalDAGData.nodes 9 ⟨317870, by decide⟩ =
    .split (coordinate 12) (![⟨317814, by decide⟩,⟨317842, by decide⟩,⟨317860, by decide⟩,⟨317869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25896_317870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25896 ⟨317870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25896
    ⟨317870, by decide⟩ (by decide) (![⟨317814, by decide⟩,⟨317842, by decide⟩,⟨317860, by decide⟩,⟨317869, by decide⟩]) unmarked_context_12_25896_317870 node_context_12_25896_317870
  intro a
  fin_cases a
  · exact context_13_103584_317814
  · exact context_13_103585_317842
  · exact context_13_103586_317860
  · exact context_13_103587_317869

theorem selected_cut_11899 : selected 8 ⟨317886, by decide⟩
    (prefixPartial 13 103588) = some ⟨13, 2, 0, 317886, 103588, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_103588_317886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103588 ⟨317886, by decide⟩ :=
  accepted_of_selected 13 103588 ⟨317886, by decide⟩ ⟨13, 2, 0, 317886, 103588, 1065, 16384⟩
    (by decide) selected_cut_11899

theorem selected_cut_11900 : selected 8 ⟨317916, by decide⟩
    (prefixPartial 13 103589) = some ⟨13, 2, 0, 317916, 103589, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_103589_317916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103589 ⟨317916, by decide⟩ :=
  accepted_of_selected 13 103589 ⟨317916, by decide⟩ ⟨13, 2, 0, 317916, 103589, 1909, 16384⟩
    (by decide) selected_cut_11900

theorem selected_cut_11901 : selected 8 ⟨317938, by decide⟩
    (prefixPartial 13 103590) = some ⟨13, 2, 0, 317938, 103590, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_103590_317938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103590 ⟨317938, by decide⟩ :=
  accepted_of_selected 13 103590 ⟨317938, by decide⟩ ⟨13, 2, 0, 317938, 103590, 1605, 16384⟩
    (by decide) selected_cut_11901

theorem selected_cut_11902 : selected 8 ⟨317947, by decide⟩
    (prefixPartial 13 103591) = some ⟨13, 2, 0, 317947, 103591, 965, 16384⟩ := by
  decide +kernel

theorem context_13_103591_317947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103591 ⟨317947, by decide⟩ :=
  accepted_of_selected 13 103591 ⟨317947, by decide⟩ ⟨13, 2, 0, 317947, 103591, 965, 16384⟩
    (by decide) selected_cut_11902

theorem unmarked_context_12_25897_317948 : frontier 9 ⟨317948, by decide⟩
    (prefixCache 12 25897) (prefixPartial 12 25897) = false := by
  decide +kernel

theorem node_context_12_25897_317948 : EJMOriginalGlobalDAGData.nodes 9 ⟨317948, by decide⟩ =
    .split (coordinate 12) (![⟨317886, by decide⟩,⟨317916, by decide⟩,⟨317938, by decide⟩,⟨317947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25897_317948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25897 ⟨317948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25897
    ⟨317948, by decide⟩ (by decide) (![⟨317886, by decide⟩,⟨317916, by decide⟩,⟨317938, by decide⟩,⟨317947, by decide⟩]) unmarked_context_12_25897_317948 node_context_12_25897_317948
  intro a
  fin_cases a
  · exact context_13_103588_317886
  · exact context_13_103589_317916
  · exact context_13_103590_317938
  · exact context_13_103591_317947

theorem selected_cut_11903 : selected 8 ⟨317969, by decide⟩
    (prefixPartial 13 103592) = some ⟨13, 2, 0, 317969, 103592, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_103592_317969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103592 ⟨317969, by decide⟩ :=
  accepted_of_selected 13 103592 ⟨317969, by decide⟩ ⟨13, 2, 0, 317969, 103592, 1081, 16384⟩
    (by decide) selected_cut_11903

theorem selected_cut_11904 : selected 8 ⟨317997, by decide⟩
    (prefixPartial 13 103593) = some ⟨13, 2, 0, 317997, 103593, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_103593_317997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103593 ⟨317997, by decide⟩ :=
  accepted_of_selected 13 103593 ⟨317997, by decide⟩ ⟨13, 2, 0, 317997, 103593, 2085, 16384⟩
    (by decide) selected_cut_11904

theorem selected_cut_11905 : selected 8 ⟨318016, by decide⟩
    (prefixPartial 13 103594) = some ⟨13, 2, 0, 318016, 103594, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_103594_318016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103594 ⟨318016, by decide⟩ :=
  accepted_of_selected 13 103594 ⟨318016, by decide⟩ ⟨13, 2, 0, 318016, 103594, 1569, 16384⟩
    (by decide) selected_cut_11905

theorem selected_cut_11906 : selected 8 ⟨318027, by decide⟩
    (prefixPartial 13 103595) = some ⟨13, 2, 0, 318027, 103595, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_103595_318027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103595 ⟨318027, by decide⟩ :=
  accepted_of_selected 13 103595 ⟨318027, by decide⟩ ⟨13, 2, 0, 318027, 103595, 1021, 16384⟩
    (by decide) selected_cut_11906

theorem unmarked_context_12_25898_318028 : frontier 9 ⟨318028, by decide⟩
    (prefixCache 12 25898) (prefixPartial 12 25898) = false := by
  decide +kernel

theorem node_context_12_25898_318028 : EJMOriginalGlobalDAGData.nodes 9 ⟨318028, by decide⟩ =
    .split (coordinate 12) (![⟨317969, by decide⟩,⟨317997, by decide⟩,⟨318016, by decide⟩,⟨318027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25898_318028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25898 ⟨318028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25898
    ⟨318028, by decide⟩ (by decide) (![⟨317969, by decide⟩,⟨317997, by decide⟩,⟨318016, by decide⟩,⟨318027, by decide⟩]) unmarked_context_12_25898_318028 node_context_12_25898_318028
  intro a
  fin_cases a
  · exact context_13_103592_317969
  · exact context_13_103593_317997
  · exact context_13_103594_318016
  · exact context_13_103595_318027

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
