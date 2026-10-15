/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover159
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_15362 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110852) = some ⟨13, 1, 0, 3444, 110852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110852, 1, 16384⟩
    (by decide) selected_cut_15362

theorem selected_cut_15363 : selected 8 ⟨394239, by decide⟩
    (prefixPartial 13 110853) = some ⟨13, 2, 0, 394239, 110853, 3313, 16384⟩ := by
  decide +kernel

theorem context_13_110853_394239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110853 ⟨394239, by decide⟩ :=
  accepted_of_selected 13 110853 ⟨394239, by decide⟩ ⟨13, 2, 0, 394239, 110853, 3313, 16384⟩
    (by decide) selected_cut_15363

theorem selected_cut_15364 : selected 8 ⟨394268, by decide⟩
    (prefixPartial 13 110854) = some ⟨13, 2, 0, 394268, 110854, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_110854_394268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110854 ⟨394268, by decide⟩ :=
  accepted_of_selected 13 110854 ⟨394268, by decide⟩ ⟨13, 2, 0, 394268, 110854, 2129, 16384⟩
    (by decide) selected_cut_15364

theorem selected_cut_15365 : selected 8 ⟨394282, by decide⟩
    (prefixPartial 13 110855) = some ⟨13, 2, 0, 394282, 110855, 945, 16384⟩ := by
  decide +kernel

theorem context_13_110855_394282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110855 ⟨394282, by decide⟩ :=
  accepted_of_selected 13 110855 ⟨394282, by decide⟩ ⟨13, 2, 0, 394282, 110855, 945, 16384⟩
    (by decide) selected_cut_15365

theorem unmarked_context_12_27713_394283 : frontier 9 ⟨394283, by decide⟩
    (prefixCache 12 27713) (prefixPartial 12 27713) = false := by
  decide +kernel

theorem node_context_12_27713_394283 : EJMOriginalGlobalDAGData.nodes 9 ⟨394283, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394239, by decide⟩,⟨394268, by decide⟩,⟨394282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27713_394283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27713 ⟨394283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27713
    ⟨394283, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394239, by decide⟩,⟨394268, by decide⟩,⟨394282, by decide⟩]) unmarked_context_12_27713_394283 node_context_12_27713_394283
  intro a
  fin_cases a
  · exact context_13_110852_3444
  · exact context_13_110853_394239
  · exact context_13_110854_394268
  · exact context_13_110855_394282

theorem selected_cut_15366 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110856) = some ⟨13, 1, 0, 3444, 110856, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110856_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110856 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110856 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110856, 1, 16384⟩
    (by decide) selected_cut_15366

theorem selected_cut_15367 : selected 8 ⟨394313, by decide⟩
    (prefixPartial 13 110857) = some ⟨13, 2, 0, 394313, 110857, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_110857_394313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110857 ⟨394313, by decide⟩ :=
  accepted_of_selected 13 110857 ⟨394313, by decide⟩ ⟨13, 2, 0, 394313, 110857, 2681, 16384⟩
    (by decide) selected_cut_15367

theorem selected_cut_15368 : selected 8 ⟨394332, by decide⟩
    (prefixPartial 13 110858) = some ⟨13, 2, 0, 394332, 110858, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_110858_394332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110858 ⟨394332, by decide⟩ :=
  accepted_of_selected 13 110858 ⟨394332, by decide⟩ ⟨13, 2, 0, 394332, 110858, 1429, 16384⟩
    (by decide) selected_cut_15368

theorem selected_cut_15369 : selected 8 ⟨394338, by decide⟩
    (prefixPartial 13 110859) = some ⟨13, 2, 0, 394338, 110859, 713, 16384⟩ := by
  decide +kernel

theorem context_13_110859_394338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110859 ⟨394338, by decide⟩ :=
  accepted_of_selected 13 110859 ⟨394338, by decide⟩ ⟨13, 2, 0, 394338, 110859, 713, 16384⟩
    (by decide) selected_cut_15369

theorem unmarked_context_12_27714_394339 : frontier 9 ⟨394339, by decide⟩
    (prefixCache 12 27714) (prefixPartial 12 27714) = false := by
  decide +kernel

theorem node_context_12_27714_394339 : EJMOriginalGlobalDAGData.nodes 9 ⟨394339, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394313, by decide⟩,⟨394332, by decide⟩,⟨394338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27714_394339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27714 ⟨394339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27714
    ⟨394339, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394313, by decide⟩,⟨394332, by decide⟩,⟨394338, by decide⟩]) unmarked_context_12_27714_394339 node_context_12_27714_394339
  intro a
  fin_cases a
  · exact context_13_110856_3444
  · exact context_13_110857_394313
  · exact context_13_110858_394332
  · exact context_13_110859_394338

theorem selected_cut_15370 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110860) = some ⟨13, 1, 0, 3444, 110860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110860, 1, 16384⟩
    (by decide) selected_cut_15370

theorem selected_cut_15371 : selected 8 ⟨394378, by decide⟩
    (prefixPartial 13 110861) = some ⟨13, 2, 0, 394378, 110861, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_110861_394378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110861 ⟨394378, by decide⟩ :=
  accepted_of_selected 13 110861 ⟨394378, by decide⟩ ⟨13, 2, 0, 394378, 110861, 2805, 16384⟩
    (by decide) selected_cut_15371

theorem selected_cut_15372 : selected 8 ⟨394399, by decide⟩
    (prefixPartial 13 110862) = some ⟨13, 2, 0, 394399, 110862, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_110862_394399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110862 ⟨394399, by decide⟩ :=
  accepted_of_selected 13 110862 ⟨394399, by decide⟩ ⟨13, 2, 0, 394399, 110862, 1569, 16384⟩
    (by decide) selected_cut_15372

theorem selected_cut_15373 : selected 8 ⟨394407, by decide⟩
    (prefixPartial 13 110863) = some ⟨13, 2, 0, 394407, 110863, 813, 16384⟩ := by
  decide +kernel

theorem context_13_110863_394407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110863 ⟨394407, by decide⟩ :=
  accepted_of_selected 13 110863 ⟨394407, by decide⟩ ⟨13, 2, 0, 394407, 110863, 813, 16384⟩
    (by decide) selected_cut_15373

theorem unmarked_context_12_27715_394408 : frontier 9 ⟨394408, by decide⟩
    (prefixCache 12 27715) (prefixPartial 12 27715) = false := by
  decide +kernel

theorem node_context_12_27715_394408 : EJMOriginalGlobalDAGData.nodes 9 ⟨394408, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394378, by decide⟩,⟨394399, by decide⟩,⟨394407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27715_394408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27715 ⟨394408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27715
    ⟨394408, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394378, by decide⟩,⟨394399, by decide⟩,⟨394407, by decide⟩]) unmarked_context_12_27715_394408 node_context_12_27715_394408
  intro a
  fin_cases a
  · exact context_13_110860_3444
  · exact context_13_110861_394378
  · exact context_13_110862_394399
  · exact context_13_110863_394407

theorem unmarked_context_11_6928_394409 : frontier 10 ⟨394409, by decide⟩
    (prefixCache 11 6928) (prefixPartial 11 6928) = false := by
  decide +kernel

theorem node_context_11_6928_394409 : EJMOriginalGlobalDAGData.nodes 10 ⟨394409, by decide⟩ =
    .split (coordinate 11) (![⟨394179, by decide⟩,⟨394283, by decide⟩,⟨394339, by decide⟩,⟨394408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6928_394409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6928 ⟨394409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6928
    ⟨394409, by decide⟩ (by decide) (![⟨394179, by decide⟩,⟨394283, by decide⟩,⟨394339, by decide⟩,⟨394408, by decide⟩]) unmarked_context_11_6928_394409 node_context_11_6928_394409
  intro a
  fin_cases a
  · exact context_12_27712_394179
  · exact context_12_27713_394283
  · exact context_12_27714_394339
  · exact context_12_27715_394408

theorem selected_cut_15374 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110864) = some ⟨13, 1, 0, 3444, 110864, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110864_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110864 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110864 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110864, 1, 16384⟩
    (by decide) selected_cut_15374

theorem selected_cut_15375 : selected 8 ⟨394460, by decide⟩
    (prefixPartial 13 110865) = some ⟨13, 2, 0, 394460, 110865, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_110865_394460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110865 ⟨394460, by decide⟩ :=
  accepted_of_selected 13 110865 ⟨394460, by decide⟩ ⟨13, 2, 0, 394460, 110865, 2817, 16384⟩
    (by decide) selected_cut_15375

theorem selected_cut_15376 : selected 8 ⟨394487, by decide⟩
    (prefixPartial 13 110866) = some ⟨13, 2, 0, 394487, 110866, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_110866_394487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110866 ⟨394487, by decide⟩ :=
  accepted_of_selected 13 110866 ⟨394487, by decide⟩ ⟨13, 2, 0, 394487, 110866, 1833, 16384⟩
    (by decide) selected_cut_15376

theorem selected_cut_15377 : selected 8 ⟨394492, by decide⟩
    (prefixPartial 13 110867) = some ⟨13, 2, 0, 394492, 110867, 641, 16384⟩ := by
  decide +kernel

theorem context_13_110867_394492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110867 ⟨394492, by decide⟩ :=
  accepted_of_selected 13 110867 ⟨394492, by decide⟩ ⟨13, 2, 0, 394492, 110867, 641, 16384⟩
    (by decide) selected_cut_15377

theorem unmarked_context_12_27716_394493 : frontier 9 ⟨394493, by decide⟩
    (prefixCache 12 27716) (prefixPartial 12 27716) = false := by
  decide +kernel

theorem node_context_12_27716_394493 : EJMOriginalGlobalDAGData.nodes 9 ⟨394493, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394460, by decide⟩,⟨394487, by decide⟩,⟨394492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27716_394493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27716 ⟨394493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27716
    ⟨394493, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394460, by decide⟩,⟨394487, by decide⟩,⟨394492, by decide⟩]) unmarked_context_12_27716_394493 node_context_12_27716_394493
  intro a
  fin_cases a
  · exact context_13_110864_3444
  · exact context_13_110865_394460
  · exact context_13_110866_394487
  · exact context_13_110867_394492

theorem selected_cut_15378 : selected 9 ⟨268917, by decide⟩
    (prefixPartial 12 27717) = some ⟨12, 1, 0, 268917, 27717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27717_268917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27717 ⟨268917, by decide⟩ :=
  accepted_of_selected 12 27717 ⟨268917, by decide⟩ ⟨12, 1, 0, 268917, 27717, 1, 65536⟩
    (by decide) selected_cut_15378

theorem selected_cut_15379 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110872) = some ⟨13, 1, 0, 3444, 110872, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110872_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110872 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110872 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110872, 1, 16384⟩
    (by decide) selected_cut_15379

theorem selected_cut_15380 : selected 8 ⟨394541, by decide⟩
    (prefixPartial 13 110873) = some ⟨13, 2, 0, 394541, 110873, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_110873_394541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110873 ⟨394541, by decide⟩ :=
  accepted_of_selected 13 110873 ⟨394541, by decide⟩ ⟨13, 2, 0, 394541, 110873, 2785, 16384⟩
    (by decide) selected_cut_15380

theorem selected_cut_15381 : selected 8 ⟨394566, by decide⟩
    (prefixPartial 13 110874) = some ⟨13, 2, 0, 394566, 110874, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_110874_394566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110874 ⟨394566, by decide⟩ :=
  accepted_of_selected 13 110874 ⟨394566, by decide⟩ ⟨13, 2, 0, 394566, 110874, 1861, 16384⟩
    (by decide) selected_cut_15381

theorem selected_cut_15382 : selected 8 ⟨394574, by decide⟩
    (prefixPartial 13 110875) = some ⟨13, 2, 0, 394574, 110875, 789, 16384⟩ := by
  decide +kernel

theorem context_13_110875_394574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110875 ⟨394574, by decide⟩ :=
  accepted_of_selected 13 110875 ⟨394574, by decide⟩ ⟨13, 2, 0, 394574, 110875, 789, 16384⟩
    (by decide) selected_cut_15382

theorem unmarked_context_12_27718_394575 : frontier 9 ⟨394575, by decide⟩
    (prefixCache 12 27718) (prefixPartial 12 27718) = false := by
  decide +kernel

theorem node_context_12_27718_394575 : EJMOriginalGlobalDAGData.nodes 9 ⟨394575, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394541, by decide⟩,⟨394566, by decide⟩,⟨394574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27718_394575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27718 ⟨394575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27718
    ⟨394575, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394541, by decide⟩,⟨394566, by decide⟩,⟨394574, by decide⟩]) unmarked_context_12_27718_394575 node_context_12_27718_394575
  intro a
  fin_cases a
  · exact context_13_110872_3444
  · exact context_13_110873_394541
  · exact context_13_110874_394566
  · exact context_13_110875_394574

theorem selected_cut_15383 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110876) = some ⟨13, 1, 0, 3444, 110876, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110876_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110876 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110876 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110876, 1, 16384⟩
    (by decide) selected_cut_15383

theorem selected_cut_15384 : selected 8 ⟨394625, by decide⟩
    (prefixPartial 13 110877) = some ⟨13, 2, 0, 394625, 110877, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_110877_394625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110877 ⟨394625, by decide⟩ :=
  accepted_of_selected 13 110877 ⟨394625, by decide⟩ ⟨13, 2, 0, 394625, 110877, 2793, 16384⟩
    (by decide) selected_cut_15384

theorem selected_cut_15385 : selected 8 ⟨394650, by decide⟩
    (prefixPartial 13 110878) = some ⟨13, 2, 0, 394650, 110878, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_110878_394650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110878 ⟨394650, by decide⟩ :=
  accepted_of_selected 13 110878 ⟨394650, by decide⟩ ⟨13, 2, 0, 394650, 110878, 1929, 16384⟩
    (by decide) selected_cut_15385

theorem selected_cut_15386 : selected 8 ⟨394662, by decide⟩
    (prefixPartial 13 110879) = some ⟨13, 2, 0, 394662, 110879, 925, 16384⟩ := by
  decide +kernel

theorem context_13_110879_394662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110879 ⟨394662, by decide⟩ :=
  accepted_of_selected 13 110879 ⟨394662, by decide⟩ ⟨13, 2, 0, 394662, 110879, 925, 16384⟩
    (by decide) selected_cut_15386

theorem unmarked_context_12_27719_394663 : frontier 9 ⟨394663, by decide⟩
    (prefixCache 12 27719) (prefixPartial 12 27719) = false := by
  decide +kernel

theorem node_context_12_27719_394663 : EJMOriginalGlobalDAGData.nodes 9 ⟨394663, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394625, by decide⟩,⟨394650, by decide⟩,⟨394662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27719_394663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27719 ⟨394663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27719
    ⟨394663, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394625, by decide⟩,⟨394650, by decide⟩,⟨394662, by decide⟩]) unmarked_context_12_27719_394663 node_context_12_27719_394663
  intro a
  fin_cases a
  · exact context_13_110876_3444
  · exact context_13_110877_394625
  · exact context_13_110878_394650
  · exact context_13_110879_394662

theorem unmarked_context_11_6929_394664 : frontier 10 ⟨394664, by decide⟩
    (prefixCache 11 6929) (prefixPartial 11 6929) = false := by
  decide +kernel

theorem node_context_11_6929_394664 : EJMOriginalGlobalDAGData.nodes 10 ⟨394664, by decide⟩ =
    .split (coordinate 11) (![⟨394493, by decide⟩,⟨268917, by decide⟩,⟨394575, by decide⟩,⟨394663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6929_394664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6929 ⟨394664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6929
    ⟨394664, by decide⟩ (by decide) (![⟨394493, by decide⟩,⟨268917, by decide⟩,⟨394575, by decide⟩,⟨394663, by decide⟩]) unmarked_context_11_6929_394664 node_context_11_6929_394664
  intro a
  fin_cases a
  · exact context_12_27716_394493
  · exact context_12_27717_268917
  · exact context_12_27718_394575
  · exact context_12_27719_394663

theorem selected_cut_15387 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110880) = some ⟨13, 1, 0, 3444, 110880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110880, 1, 16384⟩
    (by decide) selected_cut_15387

theorem selected_cut_15388 : selected 8 ⟨394699, by decide⟩
    (prefixPartial 13 110881) = some ⟨13, 2, 0, 394699, 110881, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_110881_394699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110881 ⟨394699, by decide⟩ :=
  accepted_of_selected 13 110881 ⟨394699, by decide⟩ ⟨13, 2, 0, 394699, 110881, 2549, 16384⟩
    (by decide) selected_cut_15388

theorem selected_cut_15389 : selected 8 ⟨394725, by decide⟩
    (prefixPartial 13 110882) = some ⟨13, 2, 0, 394725, 110882, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_110882_394725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110882 ⟨394725, by decide⟩ :=
  accepted_of_selected 13 110882 ⟨394725, by decide⟩ ⟨13, 2, 0, 394725, 110882, 1921, 16384⟩
    (by decide) selected_cut_15389

theorem selected_cut_15390 : selected 8 ⟨394734, by decide⟩
    (prefixPartial 13 110883) = some ⟨13, 2, 0, 394734, 110883, 833, 16384⟩ := by
  decide +kernel

theorem context_13_110883_394734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110883 ⟨394734, by decide⟩ :=
  accepted_of_selected 13 110883 ⟨394734, by decide⟩ ⟨13, 2, 0, 394734, 110883, 833, 16384⟩
    (by decide) selected_cut_15390

theorem unmarked_context_12_27720_394735 : frontier 9 ⟨394735, by decide⟩
    (prefixCache 12 27720) (prefixPartial 12 27720) = false := by
  decide +kernel

theorem node_context_12_27720_394735 : EJMOriginalGlobalDAGData.nodes 9 ⟨394735, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394699, by decide⟩,⟨394725, by decide⟩,⟨394734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27720_394735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27720 ⟨394735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27720
    ⟨394735, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394699, by decide⟩,⟨394725, by decide⟩,⟨394734, by decide⟩]) unmarked_context_12_27720_394735 node_context_12_27720_394735
  intro a
  fin_cases a
  · exact context_13_110880_3444
  · exact context_13_110881_394699
  · exact context_13_110882_394725
  · exact context_13_110883_394734

theorem selected_cut_15391 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110884) = some ⟨13, 1, 0, 3444, 110884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110884, 1, 16384⟩
    (by decide) selected_cut_15391

theorem selected_cut_15392 : selected 8 ⟨394802, by decide⟩
    (prefixPartial 13 110885) = some ⟨13, 2, 0, 394802, 110885, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_110885_394802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110885 ⟨394802, by decide⟩ :=
  accepted_of_selected 13 110885 ⟨394802, by decide⟩ ⟨13, 2, 0, 394802, 110885, 3233, 16384⟩
    (by decide) selected_cut_15392

theorem selected_cut_15393 : selected 8 ⟨394850, by decide⟩
    (prefixPartial 13 110886) = some ⟨13, 2, 0, 394850, 110886, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_110886_394850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110886 ⟨394850, by decide⟩ :=
  accepted_of_selected 13 110886 ⟨394850, by decide⟩ ⟨13, 2, 0, 394850, 110886, 2445, 16384⟩
    (by decide) selected_cut_15393

theorem selected_cut_15394 : selected 8 ⟨394870, by decide⟩
    (prefixPartial 13 110887) = some ⟨13, 2, 0, 394870, 110887, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_110887_394870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110887 ⟨394870, by decide⟩ :=
  accepted_of_selected 13 110887 ⟨394870, by decide⟩ ⟨13, 2, 0, 394870, 110887, 1101, 16384⟩
    (by decide) selected_cut_15394

theorem unmarked_context_12_27721_394871 : frontier 9 ⟨394871, by decide⟩
    (prefixCache 12 27721) (prefixPartial 12 27721) = false := by
  decide +kernel

theorem node_context_12_27721_394871 : EJMOriginalGlobalDAGData.nodes 9 ⟨394871, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394802, by decide⟩,⟨394850, by decide⟩,⟨394870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27721_394871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27721 ⟨394871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27721
    ⟨394871, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394802, by decide⟩,⟨394850, by decide⟩,⟨394870, by decide⟩]) unmarked_context_12_27721_394871 node_context_12_27721_394871
  intro a
  fin_cases a
  · exact context_13_110884_3444
  · exact context_13_110885_394802
  · exact context_13_110886_394850
  · exact context_13_110887_394870

theorem selected_cut_15395 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110888) = some ⟨13, 1, 0, 3444, 110888, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110888_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110888 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110888 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110888, 1, 16384⟩
    (by decide) selected_cut_15395

theorem selected_cut_15396 : selected 8 ⟨394900, by decide⟩
    (prefixPartial 13 110889) = some ⟨13, 2, 0, 394900, 110889, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_110889_394900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110889 ⟨394900, by decide⟩ :=
  accepted_of_selected 13 110889 ⟨394900, by decide⟩ ⟨13, 2, 0, 394900, 110889, 2217, 16384⟩
    (by decide) selected_cut_15396

theorem selected_cut_15397 : selected 8 ⟨394922, by decide⟩
    (prefixPartial 13 110890) = some ⟨13, 2, 0, 394922, 110890, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_110890_394922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110890 ⟨394922, by decide⟩ :=
  accepted_of_selected 13 110890 ⟨394922, by decide⟩ ⟨13, 2, 0, 394922, 110890, 1581, 16384⟩
    (by decide) selected_cut_15397

theorem selected_cut_15398 : selected 8 ⟨394932, by decide⟩
    (prefixPartial 13 110891) = some ⟨13, 2, 0, 394932, 110891, 897, 16384⟩ := by
  decide +kernel

theorem context_13_110891_394932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110891 ⟨394932, by decide⟩ :=
  accepted_of_selected 13 110891 ⟨394932, by decide⟩ ⟨13, 2, 0, 394932, 110891, 897, 16384⟩
    (by decide) selected_cut_15398

theorem unmarked_context_12_27722_394933 : frontier 9 ⟨394933, by decide⟩
    (prefixCache 12 27722) (prefixPartial 12 27722) = false := by
  decide +kernel

theorem node_context_12_27722_394933 : EJMOriginalGlobalDAGData.nodes 9 ⟨394933, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394900, by decide⟩,⟨394922, by decide⟩,⟨394932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27722_394933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27722 ⟨394933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27722
    ⟨394933, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394900, by decide⟩,⟨394922, by decide⟩,⟨394932, by decide⟩]) unmarked_context_12_27722_394933 node_context_12_27722_394933
  intro a
  fin_cases a
  · exact context_13_110888_3444
  · exact context_13_110889_394900
  · exact context_13_110890_394922
  · exact context_13_110891_394932

theorem selected_cut_15399 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110892) = some ⟨13, 1, 0, 3444, 110892, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110892_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110892 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110892 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110892, 1, 16384⟩
    (by decide) selected_cut_15399

theorem selected_cut_15400 : selected 8 ⟨394963, by decide⟩
    (prefixPartial 13 110893) = some ⟨13, 2, 0, 394963, 110893, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_110893_394963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110893 ⟨394963, by decide⟩ :=
  accepted_of_selected 13 110893 ⟨394963, by decide⟩ ⟨13, 2, 0, 394963, 110893, 2353, 16384⟩
    (by decide) selected_cut_15400

theorem selected_cut_15401 : selected 8 ⟨394986, by decide⟩
    (prefixPartial 13 110894) = some ⟨13, 2, 0, 394986, 110894, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_110894_394986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110894 ⟨394986, by decide⟩ :=
  accepted_of_selected 13 110894 ⟨394986, by decide⟩ ⟨13, 2, 0, 394986, 110894, 1825, 16384⟩
    (by decide) selected_cut_15401

theorem selected_cut_15402 : selected 8 ⟨394994, by decide⟩
    (prefixPartial 13 110895) = some ⟨13, 2, 0, 394994, 110895, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_110895_394994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110895 ⟨394994, by decide⟩ :=
  accepted_of_selected 13 110895 ⟨394994, by decide⟩ ⟨13, 2, 0, 394994, 110895, 1089, 16384⟩
    (by decide) selected_cut_15402

theorem unmarked_context_12_27723_394995 : frontier 9 ⟨394995, by decide⟩
    (prefixCache 12 27723) (prefixPartial 12 27723) = false := by
  decide +kernel

theorem node_context_12_27723_394995 : EJMOriginalGlobalDAGData.nodes 9 ⟨394995, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨394963, by decide⟩,⟨394986, by decide⟩,⟨394994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27723_394995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27723 ⟨394995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27723
    ⟨394995, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨394963, by decide⟩,⟨394986, by decide⟩,⟨394994, by decide⟩]) unmarked_context_12_27723_394995 node_context_12_27723_394995
  intro a
  fin_cases a
  · exact context_13_110892_3444
  · exact context_13_110893_394963
  · exact context_13_110894_394986
  · exact context_13_110895_394994

theorem unmarked_context_11_6930_394996 : frontier 10 ⟨394996, by decide⟩
    (prefixCache 11 6930) (prefixPartial 11 6930) = false := by
  decide +kernel

theorem node_context_11_6930_394996 : EJMOriginalGlobalDAGData.nodes 10 ⟨394996, by decide⟩ =
    .split (coordinate 11) (![⟨394735, by decide⟩,⟨394871, by decide⟩,⟨394933, by decide⟩,⟨394995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6930_394996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6930 ⟨394996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6930
    ⟨394996, by decide⟩ (by decide) (![⟨394735, by decide⟩,⟨394871, by decide⟩,⟨394933, by decide⟩,⟨394995, by decide⟩]) unmarked_context_11_6930_394996 node_context_11_6930_394996
  intro a
  fin_cases a
  · exact context_12_27720_394735
  · exact context_12_27721_394871
  · exact context_12_27722_394933
  · exact context_12_27723_394995

theorem selected_cut_15403 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110896) = some ⟨13, 1, 0, 3444, 110896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110896, 1, 16384⟩
    (by decide) selected_cut_15403

theorem selected_cut_15404 : selected 8 ⟨395020, by decide⟩
    (prefixPartial 13 110897) = some ⟨13, 2, 0, 395020, 110897, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_110897_395020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110897 ⟨395020, by decide⟩ :=
  accepted_of_selected 13 110897 ⟨395020, by decide⟩ ⟨13, 2, 0, 395020, 110897, 2025, 16384⟩
    (by decide) selected_cut_15404

theorem selected_cut_15405 : selected 8 ⟨395040, by decide⟩
    (prefixPartial 13 110898) = some ⟨13, 2, 0, 395040, 110898, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_110898_395040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110898 ⟨395040, by decide⟩ :=
  accepted_of_selected 13 110898 ⟨395040, by decide⟩ ⟨13, 2, 0, 395040, 110898, 1545, 16384⟩
    (by decide) selected_cut_15405

theorem selected_cut_15406 : selected 8 ⟨395047, by decide⟩
    (prefixPartial 13 110899) = some ⟨13, 2, 0, 395047, 110899, 789, 16384⟩ := by
  decide +kernel

theorem context_13_110899_395047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110899 ⟨395047, by decide⟩ :=
  accepted_of_selected 13 110899 ⟨395047, by decide⟩ ⟨13, 2, 0, 395047, 110899, 789, 16384⟩
    (by decide) selected_cut_15406

theorem unmarked_context_12_27724_395048 : frontier 9 ⟨395048, by decide⟩
    (prefixCache 12 27724) (prefixPartial 12 27724) = false := by
  decide +kernel

theorem node_context_12_27724_395048 : EJMOriginalGlobalDAGData.nodes 9 ⟨395048, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395020, by decide⟩,⟨395040, by decide⟩,⟨395047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27724_395048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27724 ⟨395048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27724
    ⟨395048, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395020, by decide⟩,⟨395040, by decide⟩,⟨395047, by decide⟩]) unmarked_context_12_27724_395048 node_context_12_27724_395048
  intro a
  fin_cases a
  · exact context_13_110896_3444
  · exact context_13_110897_395020
  · exact context_13_110898_395040
  · exact context_13_110899_395047

theorem selected_cut_15407 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110900) = some ⟨13, 1, 0, 3444, 110900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110900, 1, 16384⟩
    (by decide) selected_cut_15407

theorem selected_cut_15408 : selected 8 ⟨395086, by decide⟩
    (prefixPartial 13 110901) = some ⟨13, 2, 0, 395086, 110901, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_110901_395086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110901 ⟨395086, by decide⟩ :=
  accepted_of_selected 13 110901 ⟨395086, by decide⟩ ⟨13, 2, 0, 395086, 110901, 2661, 16384⟩
    (by decide) selected_cut_15408

theorem selected_cut_15409 : selected 8 ⟨395108, by decide⟩
    (prefixPartial 13 110902) = some ⟨13, 2, 0, 395108, 110902, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_110902_395108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110902 ⟨395108, by decide⟩ :=
  accepted_of_selected 13 110902 ⟨395108, by decide⟩ ⟨13, 2, 0, 395108, 110902, 2245, 16384⟩
    (by decide) selected_cut_15409

theorem selected_cut_15410 : selected 8 ⟨395113, by decide⟩
    (prefixPartial 13 110903) = some ⟨13, 2, 0, 395113, 110903, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_110903_395113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110903 ⟨395113, by decide⟩ :=
  accepted_of_selected 13 110903 ⟨395113, by decide⟩ ⟨13, 2, 0, 395113, 110903, 1025, 16384⟩
    (by decide) selected_cut_15410

theorem unmarked_context_12_27725_395114 : frontier 9 ⟨395114, by decide⟩
    (prefixCache 12 27725) (prefixPartial 12 27725) = false := by
  decide +kernel

theorem node_context_12_27725_395114 : EJMOriginalGlobalDAGData.nodes 9 ⟨395114, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395086, by decide⟩,⟨395108, by decide⟩,⟨395113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27725_395114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27725 ⟨395114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27725
    ⟨395114, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395086, by decide⟩,⟨395108, by decide⟩,⟨395113, by decide⟩]) unmarked_context_12_27725_395114 node_context_12_27725_395114
  intro a
  fin_cases a
  · exact context_13_110900_3444
  · exact context_13_110901_395086
  · exact context_13_110902_395108
  · exact context_13_110903_395113

theorem selected_cut_15411 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110904) = some ⟨13, 1, 0, 3444, 110904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110904, 1, 16384⟩
    (by decide) selected_cut_15411

theorem selected_cut_15412 : selected 8 ⟨395135, by decide⟩
    (prefixPartial 13 110905) = some ⟨13, 2, 0, 395135, 110905, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_110905_395135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110905 ⟨395135, by decide⟩ :=
  accepted_of_selected 13 110905 ⟨395135, by decide⟩ ⟨13, 2, 0, 395135, 110905, 1921, 16384⟩
    (by decide) selected_cut_15412

theorem selected_cut_15413 : selected 8 ⟨395155, by decide⟩
    (prefixPartial 13 110906) = some ⟨13, 2, 0, 395155, 110906, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_110906_395155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110906 ⟨395155, by decide⟩ :=
  accepted_of_selected 13 110906 ⟨395155, by decide⟩ ⟨13, 2, 0, 395155, 110906, 1649, 16384⟩
    (by decide) selected_cut_15413

theorem selected_cut_15414 : selected 8 ⟨395165, by decide⟩
    (prefixPartial 13 110907) = some ⟨13, 2, 0, 395165, 110907, 841, 16384⟩ := by
  decide +kernel

theorem context_13_110907_395165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110907 ⟨395165, by decide⟩ :=
  accepted_of_selected 13 110907 ⟨395165, by decide⟩ ⟨13, 2, 0, 395165, 110907, 841, 16384⟩
    (by decide) selected_cut_15414

theorem unmarked_context_12_27726_395166 : frontier 9 ⟨395166, by decide⟩
    (prefixCache 12 27726) (prefixPartial 12 27726) = false := by
  decide +kernel

theorem node_context_12_27726_395166 : EJMOriginalGlobalDAGData.nodes 9 ⟨395166, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395135, by decide⟩,⟨395155, by decide⟩,⟨395165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27726_395166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27726 ⟨395166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27726
    ⟨395166, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395135, by decide⟩,⟨395155, by decide⟩,⟨395165, by decide⟩]) unmarked_context_12_27726_395166 node_context_12_27726_395166
  intro a
  fin_cases a
  · exact context_13_110904_3444
  · exact context_13_110905_395135
  · exact context_13_110906_395155
  · exact context_13_110907_395165

theorem selected_cut_15415 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110908) = some ⟨13, 1, 0, 3444, 110908, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110908_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110908 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110908 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110908, 1, 16384⟩
    (by decide) selected_cut_15415

theorem selected_cut_15416 : selected 8 ⟨395191, by decide⟩
    (prefixPartial 13 110909) = some ⟨13, 2, 0, 395191, 110909, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_110909_395191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110909 ⟨395191, by decide⟩ :=
  accepted_of_selected 13 110909 ⟨395191, by decide⟩ ⟨13, 2, 0, 395191, 110909, 1997, 16384⟩
    (by decide) selected_cut_15416

theorem selected_cut_15417 : selected 8 ⟨395212, by decide⟩
    (prefixPartial 13 110910) = some ⟨13, 2, 0, 395212, 110910, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_110910_395212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110910 ⟨395212, by decide⟩ :=
  accepted_of_selected 13 110910 ⟨395212, by decide⟩ ⟨13, 2, 0, 395212, 110910, 1645, 16384⟩
    (by decide) selected_cut_15417

theorem selected_cut_15418 : selected 8 ⟨395220, by decide⟩
    (prefixPartial 13 110911) = some ⟨13, 2, 0, 395220, 110911, 957, 16384⟩ := by
  decide +kernel

theorem context_13_110911_395220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110911 ⟨395220, by decide⟩ :=
  accepted_of_selected 13 110911 ⟨395220, by decide⟩ ⟨13, 2, 0, 395220, 110911, 957, 16384⟩
    (by decide) selected_cut_15418

theorem unmarked_context_12_27727_395221 : frontier 9 ⟨395221, by decide⟩
    (prefixCache 12 27727) (prefixPartial 12 27727) = false := by
  decide +kernel

theorem node_context_12_27727_395221 : EJMOriginalGlobalDAGData.nodes 9 ⟨395221, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395191, by decide⟩,⟨395212, by decide⟩,⟨395220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27727_395221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27727 ⟨395221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27727
    ⟨395221, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395191, by decide⟩,⟨395212, by decide⟩,⟨395220, by decide⟩]) unmarked_context_12_27727_395221 node_context_12_27727_395221
  intro a
  fin_cases a
  · exact context_13_110908_3444
  · exact context_13_110909_395191
  · exact context_13_110910_395212
  · exact context_13_110911_395220

theorem unmarked_context_11_6931_395222 : frontier 10 ⟨395222, by decide⟩
    (prefixCache 11 6931) (prefixPartial 11 6931) = false := by
  decide +kernel

theorem node_context_11_6931_395222 : EJMOriginalGlobalDAGData.nodes 10 ⟨395222, by decide⟩ =
    .split (coordinate 11) (![⟨395048, by decide⟩,⟨395114, by decide⟩,⟨395166, by decide⟩,⟨395221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6931_395222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6931 ⟨395222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6931
    ⟨395222, by decide⟩ (by decide) (![⟨395048, by decide⟩,⟨395114, by decide⟩,⟨395166, by decide⟩,⟨395221, by decide⟩]) unmarked_context_11_6931_395222 node_context_11_6931_395222
  intro a
  fin_cases a
  · exact context_12_27724_395048
  · exact context_12_27725_395114
  · exact context_12_27726_395166
  · exact context_12_27727_395221

theorem unmarked_context_10_1732_395223 : frontier 11 ⟨395223, by decide⟩
    (prefixCache 10 1732) (prefixPartial 10 1732) = false := by
  decide +kernel

theorem node_context_10_1732_395223 : EJMOriginalGlobalDAGData.nodes 11 ⟨395223, by decide⟩ =
    .split (coordinate 10) (![⟨394409, by decide⟩,⟨394664, by decide⟩,⟨394996, by decide⟩,⟨395222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1732_395223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1732 ⟨395223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1732
    ⟨395223, by decide⟩ (by decide) (![⟨394409, by decide⟩,⟨394664, by decide⟩,⟨394996, by decide⟩,⟨395222, by decide⟩]) unmarked_context_10_1732_395223 node_context_10_1732_395223
  intro a
  fin_cases a
  · exact context_11_6928_394409
  · exact context_11_6929_394664
  · exact context_11_6930_394996
  · exact context_11_6931_395222

theorem selected_cut_15419 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110912) = some ⟨13, 1, 0, 3444, 110912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110912, 1, 16384⟩
    (by decide) selected_cut_15419

theorem selected_cut_15420 : selected 8 ⟨395294, by decide⟩
    (prefixPartial 13 110913) = some ⟨13, 2, 0, 395294, 110913, 3237, 16384⟩ := by
  decide +kernel

theorem context_13_110913_395294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110913 ⟨395294, by decide⟩ :=
  accepted_of_selected 13 110913 ⟨395294, by decide⟩ ⟨13, 2, 0, 395294, 110913, 3237, 16384⟩
    (by decide) selected_cut_15420

theorem selected_cut_15421 : selected 8 ⟨395368, by decide⟩
    (prefixPartial 13 110914) = some ⟨13, 2, 0, 395368, 110914, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_110914_395368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110914 ⟨395368, by decide⟩ :=
  accepted_of_selected 13 110914 ⟨395368, by decide⟩ ⟨13, 2, 0, 395368, 110914, 2753, 16384⟩
    (by decide) selected_cut_15421

theorem selected_cut_15422 : selected 8 ⟨395384, by decide⟩
    (prefixPartial 13 110915) = some ⟨13, 2, 0, 395384, 110915, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_110915_395384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110915 ⟨395384, by decide⟩ :=
  accepted_of_selected 13 110915 ⟨395384, by decide⟩ ⟨13, 2, 0, 395384, 110915, 1213, 16384⟩
    (by decide) selected_cut_15422

theorem unmarked_context_12_27728_395385 : frontier 9 ⟨395385, by decide⟩
    (prefixCache 12 27728) (prefixPartial 12 27728) = false := by
  decide +kernel

theorem node_context_12_27728_395385 : EJMOriginalGlobalDAGData.nodes 9 ⟨395385, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395294, by decide⟩,⟨395368, by decide⟩,⟨395384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27728_395385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27728 ⟨395385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27728
    ⟨395385, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395294, by decide⟩,⟨395368, by decide⟩,⟨395384, by decide⟩]) unmarked_context_12_27728_395385 node_context_12_27728_395385
  intro a
  fin_cases a
  · exact context_13_110912_3444
  · exact context_13_110913_395294
  · exact context_13_110914_395368
  · exact context_13_110915_395384

theorem selected_cut_15423 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27729) = some ⟨12, 1, 0, 170504, 27729, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27729_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27729 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27729 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27729, 1, 65536⟩
    (by decide) selected_cut_15423

theorem selected_cut_15424 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110920) = some ⟨13, 1, 0, 3444, 110920, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110920_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110920 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110920 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110920, 1, 16384⟩
    (by decide) selected_cut_15424

theorem selected_cut_15425 : selected 8 ⟨395407, by decide⟩
    (prefixPartial 13 110921) = some ⟨13, 2, 0, 395407, 110921, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_110921_395407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110921 ⟨395407, by decide⟩ :=
  accepted_of_selected 13 110921 ⟨395407, by decide⟩ ⟨13, 2, 0, 395407, 110921, 1881, 16384⟩
    (by decide) selected_cut_15425

theorem selected_cut_15426 : selected 8 ⟨395433, by decide⟩
    (prefixPartial 13 110922) = some ⟨13, 2, 0, 395433, 110922, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_110922_395433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110922 ⟨395433, by decide⟩ :=
  accepted_of_selected 13 110922 ⟨395433, by decide⟩ ⟨13, 2, 0, 395433, 110922, 1781, 16384⟩
    (by decide) selected_cut_15426

theorem selected_cut_15427 : selected 8 ⟨395440, by decide⟩
    (prefixPartial 13 110923) = some ⟨13, 2, 0, 395440, 110923, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_110923_395440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110923 ⟨395440, by decide⟩ :=
  accepted_of_selected 13 110923 ⟨395440, by decide⟩ ⟨13, 2, 0, 395440, 110923, 1049, 16384⟩
    (by decide) selected_cut_15427

theorem unmarked_context_12_27730_395441 : frontier 9 ⟨395441, by decide⟩
    (prefixCache 12 27730) (prefixPartial 12 27730) = false := by
  decide +kernel

theorem node_context_12_27730_395441 : EJMOriginalGlobalDAGData.nodes 9 ⟨395441, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395407, by decide⟩,⟨395433, by decide⟩,⟨395440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27730_395441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27730 ⟨395441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27730
    ⟨395441, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395407, by decide⟩,⟨395433, by decide⟩,⟨395440, by decide⟩]) unmarked_context_12_27730_395441 node_context_12_27730_395441
  intro a
  fin_cases a
  · exact context_13_110920_3444
  · exact context_13_110921_395407
  · exact context_13_110922_395433
  · exact context_13_110923_395440

theorem selected_cut_15428 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110924) = some ⟨13, 1, 0, 3444, 110924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110924, 1, 16384⟩
    (by decide) selected_cut_15428

theorem selected_cut_15429 : selected 8 ⟨395466, by decide⟩
    (prefixPartial 13 110925) = some ⟨13, 2, 0, 395466, 110925, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_110925_395466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110925 ⟨395466, by decide⟩ :=
  accepted_of_selected 13 110925 ⟨395466, by decide⟩ ⟨13, 2, 0, 395466, 110925, 1925, 16384⟩
    (by decide) selected_cut_15429

theorem selected_cut_15430 : selected 8 ⟨395485, by decide⟩
    (prefixPartial 13 110926) = some ⟨13, 2, 0, 395485, 110926, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_110926_395485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110926 ⟨395485, by decide⟩ :=
  accepted_of_selected 13 110926 ⟨395485, by decide⟩ ⟨13, 2, 0, 395485, 110926, 2045, 16384⟩
    (by decide) selected_cut_15430

theorem selected_cut_15431 : selected 8 ⟨395491, by decide⟩
    (prefixPartial 13 110927) = some ⟨13, 2, 0, 395491, 110927, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_110927_395491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110927 ⟨395491, by decide⟩ :=
  accepted_of_selected 13 110927 ⟨395491, by decide⟩ ⟨13, 2, 0, 395491, 110927, 1025, 16384⟩
    (by decide) selected_cut_15431

theorem unmarked_context_12_27731_395492 : frontier 9 ⟨395492, by decide⟩
    (prefixCache 12 27731) (prefixPartial 12 27731) = false := by
  decide +kernel

theorem node_context_12_27731_395492 : EJMOriginalGlobalDAGData.nodes 9 ⟨395492, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395466, by decide⟩,⟨395485, by decide⟩,⟨395491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27731_395492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27731 ⟨395492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27731
    ⟨395492, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395466, by decide⟩,⟨395485, by decide⟩,⟨395491, by decide⟩]) unmarked_context_12_27731_395492 node_context_12_27731_395492
  intro a
  fin_cases a
  · exact context_13_110924_3444
  · exact context_13_110925_395466
  · exact context_13_110926_395485
  · exact context_13_110927_395491

theorem unmarked_context_11_6932_395493 : frontier 10 ⟨395493, by decide⟩
    (prefixCache 11 6932) (prefixPartial 11 6932) = false := by
  decide +kernel

theorem node_context_11_6932_395493 : EJMOriginalGlobalDAGData.nodes 10 ⟨395493, by decide⟩ =
    .split (coordinate 11) (![⟨395385, by decide⟩,⟨170504, by decide⟩,⟨395441, by decide⟩,⟨395492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6932_395493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6932 ⟨395493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6932
    ⟨395493, by decide⟩ (by decide) (![⟨395385, by decide⟩,⟨170504, by decide⟩,⟨395441, by decide⟩,⟨395492, by decide⟩]) unmarked_context_11_6932_395493 node_context_11_6932_395493
  intro a
  fin_cases a
  · exact context_12_27728_395385
  · exact context_12_27729_170504
  · exact context_12_27730_395441
  · exact context_12_27731_395492

theorem selected_cut_15432 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110928) = some ⟨13, 1, 0, 3444, 110928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110928, 1, 16384⟩
    (by decide) selected_cut_15432

theorem selected_cut_15433 : selected 8 ⟨395513, by decide⟩
    (prefixPartial 13 110929) = some ⟨13, 2, 0, 395513, 110929, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_110929_395513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110929 ⟨395513, by decide⟩ :=
  accepted_of_selected 13 110929 ⟨395513, by decide⟩ ⟨13, 2, 0, 395513, 110929, 1733, 16384⟩
    (by decide) selected_cut_15433

theorem selected_cut_15434 : selected 8 ⟨395536, by decide⟩
    (prefixPartial 13 110930) = some ⟨13, 2, 0, 395536, 110930, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_110930_395536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110930 ⟨395536, by decide⟩ :=
  accepted_of_selected 13 110930 ⟨395536, by decide⟩ ⟨13, 2, 0, 395536, 110930, 1841, 16384⟩
    (by decide) selected_cut_15434

theorem selected_cut_15435 : selected 8 ⟨395544, by decide⟩
    (prefixPartial 13 110931) = some ⟨13, 2, 0, 395544, 110931, 717, 16384⟩ := by
  decide +kernel

theorem context_13_110931_395544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110931 ⟨395544, by decide⟩ :=
  accepted_of_selected 13 110931 ⟨395544, by decide⟩ ⟨13, 2, 0, 395544, 110931, 717, 16384⟩
    (by decide) selected_cut_15435

theorem unmarked_context_12_27732_395545 : frontier 9 ⟨395545, by decide⟩
    (prefixCache 12 27732) (prefixPartial 12 27732) = false := by
  decide +kernel

theorem node_context_12_27732_395545 : EJMOriginalGlobalDAGData.nodes 9 ⟨395545, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395513, by decide⟩,⟨395536, by decide⟩,⟨395544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27732_395545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27732 ⟨395545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27732
    ⟨395545, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395513, by decide⟩,⟨395536, by decide⟩,⟨395544, by decide⟩]) unmarked_context_12_27732_395545 node_context_12_27732_395545
  intro a
  fin_cases a
  · exact context_13_110928_3444
  · exact context_13_110929_395513
  · exact context_13_110930_395536
  · exact context_13_110931_395544

theorem selected_cut_15436 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27733) = some ⟨12, 1, 0, 170504, 27733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27733_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27733 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27733 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27733, 1, 65536⟩
    (by decide) selected_cut_15436

theorem selected_cut_15437 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110936) = some ⟨13, 1, 0, 3444, 110936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110936, 1, 16384⟩
    (by decide) selected_cut_15437

theorem selected_cut_15438 : selected 8 ⟨395568, by decide⟩
    (prefixPartial 13 110937) = some ⟨13, 2, 0, 395568, 110937, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_110937_395568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110937 ⟨395568, by decide⟩ :=
  accepted_of_selected 13 110937 ⟨395568, by decide⟩ ⟨13, 2, 0, 395568, 110937, 1805, 16384⟩
    (by decide) selected_cut_15438

theorem selected_cut_15439 : selected 8 ⟨395602, by decide⟩
    (prefixPartial 13 110938) = some ⟨13, 2, 0, 395602, 110938, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_110938_395602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110938 ⟨395602, by decide⟩ :=
  accepted_of_selected 13 110938 ⟨395602, by decide⟩ ⟨13, 2, 0, 395602, 110938, 2173, 16384⟩
    (by decide) selected_cut_15439

theorem selected_cut_15440 : selected 8 ⟨395608, by decide⟩
    (prefixPartial 13 110939) = some ⟨13, 2, 0, 395608, 110939, 929, 16384⟩ := by
  decide +kernel

theorem context_13_110939_395608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110939 ⟨395608, by decide⟩ :=
  accepted_of_selected 13 110939 ⟨395608, by decide⟩ ⟨13, 2, 0, 395608, 110939, 929, 16384⟩
    (by decide) selected_cut_15440

theorem unmarked_context_12_27734_395609 : frontier 9 ⟨395609, by decide⟩
    (prefixCache 12 27734) (prefixPartial 12 27734) = false := by
  decide +kernel

theorem node_context_12_27734_395609 : EJMOriginalGlobalDAGData.nodes 9 ⟨395609, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395568, by decide⟩,⟨395602, by decide⟩,⟨395608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27734_395609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27734 ⟨395609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27734
    ⟨395609, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395568, by decide⟩,⟨395602, by decide⟩,⟨395608, by decide⟩]) unmarked_context_12_27734_395609 node_context_12_27734_395609
  intro a
  fin_cases a
  · exact context_13_110936_3444
  · exact context_13_110937_395568
  · exact context_13_110938_395602
  · exact context_13_110939_395608

theorem selected_cut_15441 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110940) = some ⟨13, 1, 0, 3444, 110940, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110940_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110940 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110940 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110940, 1, 16384⟩
    (by decide) selected_cut_15441

theorem selected_cut_15442 : selected 8 ⟨395631, by decide⟩
    (prefixPartial 13 110941) = some ⟨13, 2, 0, 395631, 110941, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_110941_395631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110941 ⟨395631, by decide⟩ :=
  accepted_of_selected 13 110941 ⟨395631, by decide⟩ ⟨13, 2, 0, 395631, 110941, 1801, 16384⟩
    (by decide) selected_cut_15442

theorem selected_cut_15443 : selected 8 ⟨395658, by decide⟩
    (prefixPartial 13 110942) = some ⟨13, 2, 0, 395658, 110942, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_110942_395658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110942 ⟨395658, by decide⟩ :=
  accepted_of_selected 13 110942 ⟨395658, by decide⟩ ⟨13, 2, 0, 395658, 110942, 2429, 16384⟩
    (by decide) selected_cut_15443

theorem selected_cut_15444 : selected 8 ⟨395670, by decide⟩
    (prefixPartial 13 110943) = some ⟨13, 2, 0, 395670, 110943, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_110943_395670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110943 ⟨395670, by decide⟩ :=
  accepted_of_selected 13 110943 ⟨395670, by decide⟩ ⟨13, 2, 0, 395670, 110943, 1057, 16384⟩
    (by decide) selected_cut_15444

theorem unmarked_context_12_27735_395671 : frontier 9 ⟨395671, by decide⟩
    (prefixCache 12 27735) (prefixPartial 12 27735) = false := by
  decide +kernel

theorem node_context_12_27735_395671 : EJMOriginalGlobalDAGData.nodes 9 ⟨395671, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395631, by decide⟩,⟨395658, by decide⟩,⟨395670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27735_395671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27735 ⟨395671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27735
    ⟨395671, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395631, by decide⟩,⟨395658, by decide⟩,⟨395670, by decide⟩]) unmarked_context_12_27735_395671 node_context_12_27735_395671
  intro a
  fin_cases a
  · exact context_13_110940_3444
  · exact context_13_110941_395631
  · exact context_13_110942_395658
  · exact context_13_110943_395670

theorem unmarked_context_11_6933_395672 : frontier 10 ⟨395672, by decide⟩
    (prefixCache 11 6933) (prefixPartial 11 6933) = false := by
  decide +kernel

theorem node_context_11_6933_395672 : EJMOriginalGlobalDAGData.nodes 10 ⟨395672, by decide⟩ =
    .split (coordinate 11) (![⟨395545, by decide⟩,⟨170504, by decide⟩,⟨395609, by decide⟩,⟨395671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6933_395672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6933 ⟨395672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6933
    ⟨395672, by decide⟩ (by decide) (![⟨395545, by decide⟩,⟨170504, by decide⟩,⟨395609, by decide⟩,⟨395671, by decide⟩]) unmarked_context_11_6933_395672 node_context_11_6933_395672
  intro a
  fin_cases a
  · exact context_12_27732_395545
  · exact context_12_27733_170504
  · exact context_12_27734_395609
  · exact context_12_27735_395671

theorem selected_cut_15445 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110944) = some ⟨13, 1, 0, 3444, 110944, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110944_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110944 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110944 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110944, 1, 16384⟩
    (by decide) selected_cut_15445

theorem selected_cut_15446 : selected 8 ⟨395692, by decide⟩
    (prefixPartial 13 110945) = some ⟨13, 2, 0, 395692, 110945, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_110945_395692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110945 ⟨395692, by decide⟩ :=
  accepted_of_selected 13 110945 ⟨395692, by decide⟩ ⟨13, 2, 0, 395692, 110945, 1557, 16384⟩
    (by decide) selected_cut_15446

theorem selected_cut_15447 : selected 8 ⟨395720, by decide⟩
    (prefixPartial 13 110946) = some ⟨13, 2, 0, 395720, 110946, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_110946_395720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110946 ⟨395720, by decide⟩ :=
  accepted_of_selected 13 110946 ⟨395720, by decide⟩ ⟨13, 2, 0, 395720, 110946, 1777, 16384⟩
    (by decide) selected_cut_15447

theorem selected_cut_15448 : selected 8 ⟨395733, by decide⟩
    (prefixPartial 13 110947) = some ⟨13, 2, 0, 395733, 110947, 849, 16384⟩ := by
  decide +kernel

theorem context_13_110947_395733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110947 ⟨395733, by decide⟩ :=
  accepted_of_selected 13 110947 ⟨395733, by decide⟩ ⟨13, 2, 0, 395733, 110947, 849, 16384⟩
    (by decide) selected_cut_15448

theorem unmarked_context_12_27736_395734 : frontier 9 ⟨395734, by decide⟩
    (prefixCache 12 27736) (prefixPartial 12 27736) = false := by
  decide +kernel

theorem node_context_12_27736_395734 : EJMOriginalGlobalDAGData.nodes 9 ⟨395734, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395692, by decide⟩,⟨395720, by decide⟩,⟨395733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27736_395734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27736 ⟨395734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27736
    ⟨395734, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395692, by decide⟩,⟨395720, by decide⟩,⟨395733, by decide⟩]) unmarked_context_12_27736_395734 node_context_12_27736_395734
  intro a
  fin_cases a
  · exact context_13_110944_3444
  · exact context_13_110945_395692
  · exact context_13_110946_395720
  · exact context_13_110947_395733

theorem selected_cut_15449 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 27737) = some ⟨12, 1, 0, 126371, 27737, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27737_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27737 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 27737 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 27737, 1, 65536⟩
    (by decide) selected_cut_15449

theorem selected_cut_15450 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110952) = some ⟨13, 1, 0, 3444, 110952, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110952_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110952 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110952 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110952, 1, 16384⟩
    (by decide) selected_cut_15450

theorem selected_cut_15451 : selected 8 ⟨395755, by decide⟩
    (prefixPartial 13 110953) = some ⟨13, 2, 0, 395755, 110953, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_110953_395755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110953 ⟨395755, by decide⟩ :=
  accepted_of_selected 13 110953 ⟨395755, by decide⟩ ⟨13, 2, 0, 395755, 110953, 1449, 16384⟩
    (by decide) selected_cut_15451

theorem selected_cut_15452 : selected 8 ⟨395782, by decide⟩
    (prefixPartial 13 110954) = some ⟨13, 2, 0, 395782, 110954, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_110954_395782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110954 ⟨395782, by decide⟩ :=
  accepted_of_selected 13 110954 ⟨395782, by decide⟩ ⟨13, 2, 0, 395782, 110954, 1721, 16384⟩
    (by decide) selected_cut_15452

theorem selected_cut_15453 : selected 8 ⟨395791, by decide⟩
    (prefixPartial 13 110955) = some ⟨13, 2, 0, 395791, 110955, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_110955_395791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110955 ⟨395791, by decide⟩ :=
  accepted_of_selected 13 110955 ⟨395791, by decide⟩ ⟨13, 2, 0, 395791, 110955, 1005, 16384⟩
    (by decide) selected_cut_15453

theorem unmarked_context_12_27738_395792 : frontier 9 ⟨395792, by decide⟩
    (prefixCache 12 27738) (prefixPartial 12 27738) = false := by
  decide +kernel

theorem node_context_12_27738_395792 : EJMOriginalGlobalDAGData.nodes 9 ⟨395792, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395755, by decide⟩,⟨395782, by decide⟩,⟨395791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27738_395792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27738 ⟨395792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27738
    ⟨395792, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395755, by decide⟩,⟨395782, by decide⟩,⟨395791, by decide⟩]) unmarked_context_12_27738_395792 node_context_12_27738_395792
  intro a
  fin_cases a
  · exact context_13_110952_3444
  · exact context_13_110953_395755
  · exact context_13_110954_395782
  · exact context_13_110955_395791

theorem selected_cut_15454 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 110956) = some ⟨13, 1, 0, 3444, 110956, 1, 16384⟩ := by
  decide +kernel

theorem context_13_110956_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110956 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 110956 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 110956, 1, 16384⟩
    (by decide) selected_cut_15454

theorem selected_cut_15455 : selected 8 ⟨395812, by decide⟩
    (prefixPartial 13 110957) = some ⟨13, 2, 0, 395812, 110957, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_110957_395812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110957 ⟨395812, by decide⟩ :=
  accepted_of_selected 13 110957 ⟨395812, by decide⟩ ⟨13, 2, 0, 395812, 110957, 1489, 16384⟩
    (by decide) selected_cut_15455

theorem selected_cut_15456 : selected 8 ⟨395836, by decide⟩
    (prefixPartial 13 110958) = some ⟨13, 2, 0, 395836, 110958, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_110958_395836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110958 ⟨395836, by decide⟩ :=
  accepted_of_selected 13 110958 ⟨395836, by decide⟩ ⟨13, 2, 0, 395836, 110958, 2013, 16384⟩
    (by decide) selected_cut_15456

theorem selected_cut_15457 : selected 8 ⟨395848, by decide⟩
    (prefixPartial 13 110959) = some ⟨13, 2, 0, 395848, 110959, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_110959_395848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110959 ⟨395848, by decide⟩ :=
  accepted_of_selected 13 110959 ⟨395848, by decide⟩ ⟨13, 2, 0, 395848, 110959, 1125, 16384⟩
    (by decide) selected_cut_15457

theorem unmarked_context_12_27739_395849 : frontier 9 ⟨395849, by decide⟩
    (prefixCache 12 27739) (prefixPartial 12 27739) = false := by
  decide +kernel

theorem node_context_12_27739_395849 : EJMOriginalGlobalDAGData.nodes 9 ⟨395849, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨395812, by decide⟩,⟨395836, by decide⟩,⟨395848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27739_395849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27739 ⟨395849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27739
    ⟨395849, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨395812, by decide⟩,⟨395836, by decide⟩,⟨395848, by decide⟩]) unmarked_context_12_27739_395849 node_context_12_27739_395849
  intro a
  fin_cases a
  · exact context_13_110956_3444
  · exact context_13_110957_395812
  · exact context_13_110958_395836
  · exact context_13_110959_395848

theorem unmarked_context_11_6934_395850 : frontier 10 ⟨395850, by decide⟩
    (prefixCache 11 6934) (prefixPartial 11 6934) = false := by
  decide +kernel

theorem node_context_11_6934_395850 : EJMOriginalGlobalDAGData.nodes 10 ⟨395850, by decide⟩ =
    .split (coordinate 11) (![⟨395734, by decide⟩,⟨126371, by decide⟩,⟨395792, by decide⟩,⟨395849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6934_395850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6934 ⟨395850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6934
    ⟨395850, by decide⟩ (by decide) (![⟨395734, by decide⟩,⟨126371, by decide⟩,⟨395792, by decide⟩,⟨395849, by decide⟩]) unmarked_context_11_6934_395850 node_context_11_6934_395850
  intro a
  fin_cases a
  · exact context_12_27736_395734
  · exact context_12_27737_126371
  · exact context_12_27738_395792
  · exact context_12_27739_395849

theorem selected_cut_15458 : selected 9 ⟨395893, by decide⟩
    (prefixPartial 12 27740) = some ⟨12, 2, 0, 395893, 27740, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_27740_395893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27740 ⟨395893, by decide⟩ :=
  accepted_of_selected 12 27740 ⟨395893, by decide⟩ ⟨12, 2, 0, 395893, 27740, 3649, 65536⟩
    (by decide) selected_cut_15458

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
