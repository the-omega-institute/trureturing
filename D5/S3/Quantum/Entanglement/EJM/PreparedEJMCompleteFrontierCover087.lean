/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover086
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_5729_234316 : frontier 10 ⟨234316, by decide⟩
    (prefixCache 11 5729) (prefixPartial 11 5729) = false := by
  decide +kernel

theorem node_context_11_5729_234316 : EJMOriginalGlobalDAGData.nodes 10 ⟨234316, by decide⟩ =
    .split (coordinate 11) (![⟨234234, by decide⟩,⟨234263, by decide⟩,⟨234288, by decide⟩,⟨234315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5729_234316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5729 ⟨234316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5729
    ⟨234316, by decide⟩ (by decide) (![⟨234234, by decide⟩,⟨234263, by decide⟩,⟨234288, by decide⟩,⟨234315, by decide⟩]) unmarked_context_11_5729_234316 node_context_11_5729_234316
  intro a
  fin_cases a
  · exact context_12_22916_234234
  · exact context_12_22917_234263
  · exact context_12_22918_234288
  · exact context_12_22919_234315

theorem selected_cut_08355 : selected 9 ⟨234343, by decide⟩
    (prefixPartial 12 22920) = some ⟨12, 2, 0, 234343, 22920, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_22920_234343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22920 ⟨234343, by decide⟩ :=
  accepted_of_selected 12 22920 ⟨234343, by decide⟩ ⟨12, 2, 0, 234343, 22920, 2413, 65536⟩
    (by decide) selected_cut_08355

theorem selected_cut_08356 : selected 9 ⟨234377, by decide⟩
    (prefixPartial 12 22921) = some ⟨12, 2, 0, 234377, 22921, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_22921_234377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22921 ⟨234377, by decide⟩ :=
  accepted_of_selected 12 22921 ⟨234377, by decide⟩ ⟨12, 2, 0, 234377, 22921, 2289, 65536⟩
    (by decide) selected_cut_08356

theorem selected_cut_08357 : selected 9 ⟨234407, by decide⟩
    (prefixPartial 12 22922) = some ⟨12, 2, 0, 234407, 22922, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_22922_234407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22922 ⟨234407, by decide⟩ :=
  accepted_of_selected 12 22922 ⟨234407, by decide⟩ ⟨12, 2, 0, 234407, 22922, 2401, 65536⟩
    (by decide) selected_cut_08357

theorem selected_cut_08358 : selected 9 ⟨234437, by decide⟩
    (prefixPartial 12 22923) = some ⟨12, 2, 0, 234437, 22923, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_22923_234437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22923 ⟨234437, by decide⟩ :=
  accepted_of_selected 12 22923 ⟨234437, by decide⟩ ⟨12, 2, 0, 234437, 22923, 2397, 65536⟩
    (by decide) selected_cut_08358

theorem unmarked_context_11_5730_234438 : frontier 10 ⟨234438, by decide⟩
    (prefixCache 11 5730) (prefixPartial 11 5730) = false := by
  decide +kernel

theorem node_context_11_5730_234438 : EJMOriginalGlobalDAGData.nodes 10 ⟨234438, by decide⟩ =
    .split (coordinate 11) (![⟨234343, by decide⟩,⟨234377, by decide⟩,⟨234407, by decide⟩,⟨234437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5730_234438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5730 ⟨234438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5730
    ⟨234438, by decide⟩ (by decide) (![⟨234343, by decide⟩,⟨234377, by decide⟩,⟨234407, by decide⟩,⟨234437, by decide⟩]) unmarked_context_11_5730_234438 node_context_11_5730_234438
  intro a
  fin_cases a
  · exact context_12_22920_234343
  · exact context_12_22921_234377
  · exact context_12_22922_234407
  · exact context_12_22923_234437

theorem selected_cut_08359 : selected 9 ⟨234460, by decide⟩
    (prefixPartial 12 22924) = some ⟨12, 2, 0, 234460, 22924, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_22924_234460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22924 ⟨234460, by decide⟩ :=
  accepted_of_selected 12 22924 ⟨234460, by decide⟩ ⟨12, 2, 0, 234460, 22924, 2325, 65536⟩
    (by decide) selected_cut_08359

theorem selected_cut_08360 : selected 9 ⟨234486, by decide⟩
    (prefixPartial 12 22925) = some ⟨12, 2, 0, 234486, 22925, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_22925_234486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22925 ⟨234486, by decide⟩ :=
  accepted_of_selected 12 22925 ⟨234486, by decide⟩ ⟨12, 2, 0, 234486, 22925, 2249, 65536⟩
    (by decide) selected_cut_08360

theorem selected_cut_08361 : selected 9 ⟨234513, by decide⟩
    (prefixPartial 12 22926) = some ⟨12, 2, 0, 234513, 22926, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_22926_234513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22926 ⟨234513, by decide⟩ :=
  accepted_of_selected 12 22926 ⟨234513, by decide⟩ ⟨12, 2, 0, 234513, 22926, 2481, 65536⟩
    (by decide) selected_cut_08361

theorem selected_cut_08362 : selected 9 ⟨234538, by decide⟩
    (prefixPartial 12 22927) = some ⟨12, 2, 0, 234538, 22927, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_22927_234538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22927 ⟨234538, by decide⟩ :=
  accepted_of_selected 12 22927 ⟨234538, by decide⟩ ⟨12, 2, 0, 234538, 22927, 2245, 65536⟩
    (by decide) selected_cut_08362

theorem unmarked_context_11_5731_234539 : frontier 10 ⟨234539, by decide⟩
    (prefixCache 11 5731) (prefixPartial 11 5731) = false := by
  decide +kernel

theorem node_context_11_5731_234539 : EJMOriginalGlobalDAGData.nodes 10 ⟨234539, by decide⟩ =
    .split (coordinate 11) (![⟨234460, by decide⟩,⟨234486, by decide⟩,⟨234513, by decide⟩,⟨234538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5731_234539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5731 ⟨234539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5731
    ⟨234539, by decide⟩ (by decide) (![⟨234460, by decide⟩,⟨234486, by decide⟩,⟨234513, by decide⟩,⟨234538, by decide⟩]) unmarked_context_11_5731_234539 node_context_11_5731_234539
  intro a
  fin_cases a
  · exact context_12_22924_234460
  · exact context_12_22925_234486
  · exact context_12_22926_234513
  · exact context_12_22927_234538

theorem unmarked_context_10_1432_234540 : frontier 11 ⟨234540, by decide⟩
    (prefixCache 10 1432) (prefixPartial 10 1432) = false := by
  decide +kernel

theorem node_context_10_1432_234540 : EJMOriginalGlobalDAGData.nodes 11 ⟨234540, by decide⟩ =
    .split (coordinate 10) (![⟨234207, by decide⟩,⟨234316, by decide⟩,⟨234438, by decide⟩,⟨234539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1432_234540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1432 ⟨234540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1432
    ⟨234540, by decide⟩ (by decide) (![⟨234207, by decide⟩,⟨234316, by decide⟩,⟨234438, by decide⟩,⟨234539, by decide⟩]) unmarked_context_10_1432_234540 node_context_10_1432_234540
  intro a
  fin_cases a
  · exact context_11_5728_234207
  · exact context_11_5729_234316
  · exact context_11_5730_234438
  · exact context_11_5731_234539

theorem selected_cut_08363 : selected 9 ⟨234561, by decide⟩
    (prefixPartial 12 22928) = some ⟨12, 2, 0, 234561, 22928, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_22928_234561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22928 ⟨234561, by decide⟩ :=
  accepted_of_selected 12 22928 ⟨234561, by decide⟩ ⟨12, 2, 0, 234561, 22928, 2013, 65536⟩
    (by decide) selected_cut_08363

theorem selected_cut_08364 : selected 9 ⟨234583, by decide⟩
    (prefixPartial 12 22929) = some ⟨12, 2, 0, 234583, 22929, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_22929_234583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22929 ⟨234583, by decide⟩ :=
  accepted_of_selected 12 22929 ⟨234583, by decide⟩ ⟨12, 2, 0, 234583, 22929, 2037, 65536⟩
    (by decide) selected_cut_08364

theorem selected_cut_08365 : selected 9 ⟨234610, by decide⟩
    (prefixPartial 12 22930) = some ⟨12, 2, 0, 234610, 22930, 2409, 65536⟩ := by
  decide +kernel

theorem context_12_22930_234610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22930 ⟨234610, by decide⟩ :=
  accepted_of_selected 12 22930 ⟨234610, by decide⟩ ⟨12, 2, 0, 234610, 22930, 2409, 65536⟩
    (by decide) selected_cut_08365

theorem selected_cut_08366 : selected 9 ⟨234628, by decide⟩
    (prefixPartial 12 22931) = some ⟨12, 2, 0, 234628, 22931, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_22931_234628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22931 ⟨234628, by decide⟩ :=
  accepted_of_selected 12 22931 ⟨234628, by decide⟩ ⟨12, 2, 0, 234628, 22931, 2293, 65536⟩
    (by decide) selected_cut_08366

theorem unmarked_context_11_5732_234629 : frontier 10 ⟨234629, by decide⟩
    (prefixCache 11 5732) (prefixPartial 11 5732) = false := by
  decide +kernel

theorem node_context_11_5732_234629 : EJMOriginalGlobalDAGData.nodes 10 ⟨234629, by decide⟩ =
    .split (coordinate 11) (![⟨234561, by decide⟩,⟨234583, by decide⟩,⟨234610, by decide⟩,⟨234628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5732_234629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5732 ⟨234629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5732
    ⟨234629, by decide⟩ (by decide) (![⟨234561, by decide⟩,⟨234583, by decide⟩,⟨234610, by decide⟩,⟨234628, by decide⟩]) unmarked_context_11_5732_234629 node_context_11_5732_234629
  intro a
  fin_cases a
  · exact context_12_22928_234561
  · exact context_12_22929_234583
  · exact context_12_22930_234610
  · exact context_12_22931_234628

theorem selected_cut_08367 : selected 9 ⟨234649, by decide⟩
    (prefixPartial 12 22932) = some ⟨12, 2, 0, 234649, 22932, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_22932_234649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22932 ⟨234649, by decide⟩ :=
  accepted_of_selected 12 22932 ⟨234649, by decide⟩ ⟨12, 2, 0, 234649, 22932, 1597, 65536⟩
    (by decide) selected_cut_08367

theorem selected_cut_08368 : selected 9 ⟨234650, by decide⟩
    (prefixPartial 12 22933) = some ⟨12, 1, 0, 234650, 22933, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22933_234650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22933 ⟨234650, by decide⟩ :=
  accepted_of_selected 12 22933 ⟨234650, by decide⟩ ⟨12, 1, 0, 234650, 22933, 1, 65536⟩
    (by decide) selected_cut_08368

theorem selected_cut_08369 : selected 9 ⟨234674, by decide⟩
    (prefixPartial 12 22934) = some ⟨12, 2, 0, 234674, 22934, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_22934_234674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22934 ⟨234674, by decide⟩ :=
  accepted_of_selected 12 22934 ⟨234674, by decide⟩ ⟨12, 2, 0, 234674, 22934, 1877, 65536⟩
    (by decide) selected_cut_08369

theorem selected_cut_08370 : selected 9 ⟨234693, by decide⟩
    (prefixPartial 12 22935) = some ⟨12, 2, 0, 234693, 22935, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_22935_234693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22935 ⟨234693, by decide⟩ :=
  accepted_of_selected 12 22935 ⟨234693, by decide⟩ ⟨12, 2, 0, 234693, 22935, 1777, 65536⟩
    (by decide) selected_cut_08370

theorem unmarked_context_11_5733_234694 : frontier 10 ⟨234694, by decide⟩
    (prefixCache 11 5733) (prefixPartial 11 5733) = false := by
  decide +kernel

theorem node_context_11_5733_234694 : EJMOriginalGlobalDAGData.nodes 10 ⟨234694, by decide⟩ =
    .split (coordinate 11) (![⟨234649, by decide⟩,⟨234650, by decide⟩,⟨234674, by decide⟩,⟨234693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5733_234694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5733 ⟨234694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5733
    ⟨234694, by decide⟩ (by decide) (![⟨234649, by decide⟩,⟨234650, by decide⟩,⟨234674, by decide⟩,⟨234693, by decide⟩]) unmarked_context_11_5733_234694 node_context_11_5733_234694
  intro a
  fin_cases a
  · exact context_12_22932_234649
  · exact context_12_22933_234650
  · exact context_12_22934_234674
  · exact context_12_22935_234693

theorem selected_cut_08371 : selected 9 ⟨234712, by decide⟩
    (prefixPartial 12 22936) = some ⟨12, 2, 0, 234712, 22936, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_22936_234712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22936 ⟨234712, by decide⟩ :=
  accepted_of_selected 12 22936 ⟨234712, by decide⟩ ⟨12, 2, 0, 234712, 22936, 1705, 65536⟩
    (by decide) selected_cut_08371

theorem selected_cut_08372 : selected 9 ⟨234731, by decide⟩
    (prefixPartial 12 22937) = some ⟨12, 2, 0, 234731, 22937, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_22937_234731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22937 ⟨234731, by decide⟩ :=
  accepted_of_selected 12 22937 ⟨234731, by decide⟩ ⟨12, 2, 0, 234731, 22937, 1661, 65536⟩
    (by decide) selected_cut_08372

theorem selected_cut_08373 : selected 9 ⟨234757, by decide⟩
    (prefixPartial 12 22938) = some ⟨12, 2, 0, 234757, 22938, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_22938_234757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22938 ⟨234757, by decide⟩ :=
  accepted_of_selected 12 22938 ⟨234757, by decide⟩ ⟨12, 2, 0, 234757, 22938, 1869, 65536⟩
    (by decide) selected_cut_08373

theorem selected_cut_08374 : selected 9 ⟨234781, by decide⟩
    (prefixPartial 12 22939) = some ⟨12, 2, 0, 234781, 22939, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_22939_234781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22939 ⟨234781, by decide⟩ :=
  accepted_of_selected 12 22939 ⟨234781, by decide⟩ ⟨12, 2, 0, 234781, 22939, 1877, 65536⟩
    (by decide) selected_cut_08374

theorem unmarked_context_11_5734_234782 : frontier 10 ⟨234782, by decide⟩
    (prefixCache 11 5734) (prefixPartial 11 5734) = false := by
  decide +kernel

theorem node_context_11_5734_234782 : EJMOriginalGlobalDAGData.nodes 10 ⟨234782, by decide⟩ =
    .split (coordinate 11) (![⟨234712, by decide⟩,⟨234731, by decide⟩,⟨234757, by decide⟩,⟨234781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5734_234782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5734 ⟨234782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5734
    ⟨234782, by decide⟩ (by decide) (![⟨234712, by decide⟩,⟨234731, by decide⟩,⟨234757, by decide⟩,⟨234781, by decide⟩]) unmarked_context_11_5734_234782 node_context_11_5734_234782
  intro a
  fin_cases a
  · exact context_12_22936_234712
  · exact context_12_22937_234731
  · exact context_12_22938_234757
  · exact context_12_22939_234781

theorem selected_cut_08375 : selected 9 ⟨234802, by decide⟩
    (prefixPartial 12 22940) = some ⟨12, 2, 0, 234802, 22940, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_22940_234802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22940 ⟨234802, by decide⟩ :=
  accepted_of_selected 12 22940 ⟨234802, by decide⟩ ⟨12, 2, 0, 234802, 22940, 1705, 65536⟩
    (by decide) selected_cut_08375

theorem selected_cut_08376 : selected 9 ⟨234821, by decide⟩
    (prefixPartial 12 22941) = some ⟨12, 2, 0, 234821, 22941, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_22941_234821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22941 ⟨234821, by decide⟩ :=
  accepted_of_selected 12 22941 ⟨234821, by decide⟩ ⟨12, 2, 0, 234821, 22941, 1485, 65536⟩
    (by decide) selected_cut_08376

theorem selected_cut_08377 : selected 9 ⟨234843, by decide⟩
    (prefixPartial 12 22942) = some ⟨12, 2, 0, 234843, 22942, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_22942_234843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22942 ⟨234843, by decide⟩ :=
  accepted_of_selected 12 22942 ⟨234843, by decide⟩ ⟨12, 2, 0, 234843, 22942, 1869, 65536⟩
    (by decide) selected_cut_08377

theorem selected_cut_08378 : selected 9 ⟨234864, by decide⟩
    (prefixPartial 12 22943) = some ⟨12, 2, 0, 234864, 22943, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_22943_234864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22943 ⟨234864, by decide⟩ :=
  accepted_of_selected 12 22943 ⟨234864, by decide⟩ ⟨12, 2, 0, 234864, 22943, 1661, 65536⟩
    (by decide) selected_cut_08378

theorem unmarked_context_11_5735_234865 : frontier 10 ⟨234865, by decide⟩
    (prefixCache 11 5735) (prefixPartial 11 5735) = false := by
  decide +kernel

theorem node_context_11_5735_234865 : EJMOriginalGlobalDAGData.nodes 10 ⟨234865, by decide⟩ =
    .split (coordinate 11) (![⟨234802, by decide⟩,⟨234821, by decide⟩,⟨234843, by decide⟩,⟨234864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5735_234865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5735 ⟨234865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5735
    ⟨234865, by decide⟩ (by decide) (![⟨234802, by decide⟩,⟨234821, by decide⟩,⟨234843, by decide⟩,⟨234864, by decide⟩]) unmarked_context_11_5735_234865 node_context_11_5735_234865
  intro a
  fin_cases a
  · exact context_12_22940_234802
  · exact context_12_22941_234821
  · exact context_12_22942_234843
  · exact context_12_22943_234864

theorem unmarked_context_10_1433_234866 : frontier 11 ⟨234866, by decide⟩
    (prefixCache 10 1433) (prefixPartial 10 1433) = false := by
  decide +kernel

theorem node_context_10_1433_234866 : EJMOriginalGlobalDAGData.nodes 11 ⟨234866, by decide⟩ =
    .split (coordinate 10) (![⟨234629, by decide⟩,⟨234694, by decide⟩,⟨234782, by decide⟩,⟨234865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1433_234866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1433 ⟨234866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1433
    ⟨234866, by decide⟩ (by decide) (![⟨234629, by decide⟩,⟨234694, by decide⟩,⟨234782, by decide⟩,⟨234865, by decide⟩]) unmarked_context_10_1433_234866 node_context_10_1433_234866
  intro a
  fin_cases a
  · exact context_11_5732_234629
  · exact context_11_5733_234694
  · exact context_11_5734_234782
  · exact context_11_5735_234865

theorem selected_cut_08379 : selected 9 ⟨234888, by decide⟩
    (prefixPartial 12 22944) = some ⟨12, 2, 0, 234888, 22944, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_22944_234888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22944 ⟨234888, by decide⟩ :=
  accepted_of_selected 12 22944 ⟨234888, by decide⟩ ⟨12, 2, 0, 234888, 22944, 1673, 65536⟩
    (by decide) selected_cut_08379

theorem selected_cut_08380 : selected 9 ⟨234906, by decide⟩
    (prefixPartial 12 22945) = some ⟨12, 2, 0, 234906, 22945, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_22945_234906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22945 ⟨234906, by decide⟩ :=
  accepted_of_selected 12 22945 ⟨234906, by decide⟩ ⟨12, 2, 0, 234906, 22945, 1701, 65536⟩
    (by decide) selected_cut_08380

theorem selected_cut_08381 : selected 9 ⟨234923, by decide⟩
    (prefixPartial 12 22946) = some ⟨12, 2, 0, 234923, 22946, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_22946_234923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22946 ⟨234923, by decide⟩ :=
  accepted_of_selected 12 22946 ⟨234923, by decide⟩ ⟨12, 2, 0, 234923, 22946, 1829, 65536⟩
    (by decide) selected_cut_08381

theorem selected_cut_08382 : selected 9 ⟨234939, by decide⟩
    (prefixPartial 12 22947) = some ⟨12, 2, 0, 234939, 22947, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_22947_234939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22947 ⟨234939, by decide⟩ :=
  accepted_of_selected 12 22947 ⟨234939, by decide⟩ ⟨12, 2, 0, 234939, 22947, 1781, 65536⟩
    (by decide) selected_cut_08382

theorem unmarked_context_11_5736_234940 : frontier 10 ⟨234940, by decide⟩
    (prefixCache 11 5736) (prefixPartial 11 5736) = false := by
  decide +kernel

theorem node_context_11_5736_234940 : EJMOriginalGlobalDAGData.nodes 10 ⟨234940, by decide⟩ =
    .split (coordinate 11) (![⟨234888, by decide⟩,⟨234906, by decide⟩,⟨234923, by decide⟩,⟨234939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5736_234940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5736 ⟨234940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5736
    ⟨234940, by decide⟩ (by decide) (![⟨234888, by decide⟩,⟨234906, by decide⟩,⟨234923, by decide⟩,⟨234939, by decide⟩]) unmarked_context_11_5736_234940 node_context_11_5736_234940
  intro a
  fin_cases a
  · exact context_12_22944_234888
  · exact context_12_22945_234906
  · exact context_12_22946_234923
  · exact context_12_22947_234939

theorem selected_cut_08383 : selected 9 ⟨234955, by decide⟩
    (prefixPartial 12 22948) = some ⟨12, 2, 0, 234955, 22948, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_22948_234955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22948 ⟨234955, by decide⟩ :=
  accepted_of_selected 12 22948 ⟨234955, by decide⟩ ⟨12, 2, 0, 234955, 22948, 1353, 65536⟩
    (by decide) selected_cut_08383

theorem selected_cut_08384 : selected 9 ⟨234974, by decide⟩
    (prefixPartial 12 22949) = some ⟨12, 2, 0, 234974, 22949, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_22949_234974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22949 ⟨234974, by decide⟩ :=
  accepted_of_selected 12 22949 ⟨234974, by decide⟩ ⟨12, 2, 0, 234974, 22949, 1977, 65536⟩
    (by decide) selected_cut_08384

theorem selected_cut_08385 : selected 9 ⟨234990, by decide⟩
    (prefixPartial 12 22950) = some ⟨12, 2, 0, 234990, 22950, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_22950_234990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22950 ⟨234990, by decide⟩ :=
  accepted_of_selected 12 22950 ⟨234990, by decide⟩ ⟨12, 2, 0, 234990, 22950, 1449, 65536⟩
    (by decide) selected_cut_08385

theorem selected_cut_08386 : selected 9 ⟨235009, by decide⟩
    (prefixPartial 12 22951) = some ⟨12, 2, 0, 235009, 22951, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_22951_235009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22951 ⟨235009, by decide⟩ :=
  accepted_of_selected 12 22951 ⟨235009, by decide⟩ ⟨12, 2, 0, 235009, 22951, 1349, 65536⟩
    (by decide) selected_cut_08386

theorem unmarked_context_11_5737_235010 : frontier 10 ⟨235010, by decide⟩
    (prefixCache 11 5737) (prefixPartial 11 5737) = false := by
  decide +kernel

theorem node_context_11_5737_235010 : EJMOriginalGlobalDAGData.nodes 10 ⟨235010, by decide⟩ =
    .split (coordinate 11) (![⟨234955, by decide⟩,⟨234974, by decide⟩,⟨234990, by decide⟩,⟨235009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5737_235010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5737 ⟨235010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5737
    ⟨235010, by decide⟩ (by decide) (![⟨234955, by decide⟩,⟨234974, by decide⟩,⟨234990, by decide⟩,⟨235009, by decide⟩]) unmarked_context_11_5737_235010 node_context_11_5737_235010
  intro a
  fin_cases a
  · exact context_12_22948_234955
  · exact context_12_22949_234974
  · exact context_12_22950_234990
  · exact context_12_22951_235009

theorem selected_cut_08387 : selected 9 ⟨235027, by decide⟩
    (prefixPartial 12 22952) = some ⟨12, 2, 0, 235027, 22952, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_22952_235027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22952 ⟨235027, by decide⟩ :=
  accepted_of_selected 12 22952 ⟨235027, by decide⟩ ⟨12, 2, 0, 235027, 22952, 1745, 65536⟩
    (by decide) selected_cut_08387

theorem selected_cut_08388 : selected 9 ⟨235041, by decide⟩
    (prefixPartial 12 22953) = some ⟨12, 2, 0, 235041, 22953, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_22953_235041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22953 ⟨235041, by decide⟩ :=
  accepted_of_selected 12 22953 ⟨235041, by decide⟩ ⟨12, 2, 0, 235041, 22953, 1777, 65536⟩
    (by decide) selected_cut_08388

theorem selected_cut_08389 : selected 9 ⟨224365, by decide⟩
    (prefixPartial 12 22954) = some ⟨12, 1, 0, 224365, 22954, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22954_224365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22954 ⟨224365, by decide⟩ :=
  accepted_of_selected 12 22954 ⟨224365, by decide⟩ ⟨12, 1, 0, 224365, 22954, 1, 65536⟩
    (by decide) selected_cut_08389

theorem selected_cut_08390 : selected 9 ⟨235063, by decide⟩
    (prefixPartial 12 22955) = some ⟨12, 2, 0, 235063, 22955, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_22955_235063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22955 ⟨235063, by decide⟩ :=
  accepted_of_selected 12 22955 ⟨235063, by decide⟩ ⟨12, 2, 0, 235063, 22955, 1797, 65536⟩
    (by decide) selected_cut_08390

theorem unmarked_context_11_5738_235064 : frontier 10 ⟨235064, by decide⟩
    (prefixCache 11 5738) (prefixPartial 11 5738) = false := by
  decide +kernel

theorem node_context_11_5738_235064 : EJMOriginalGlobalDAGData.nodes 10 ⟨235064, by decide⟩ =
    .split (coordinate 11) (![⟨235027, by decide⟩,⟨235041, by decide⟩,⟨224365, by decide⟩,⟨235063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5738_235064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5738 ⟨235064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5738
    ⟨235064, by decide⟩ (by decide) (![⟨235027, by decide⟩,⟨235041, by decide⟩,⟨224365, by decide⟩,⟨235063, by decide⟩]) unmarked_context_11_5738_235064 node_context_11_5738_235064
  intro a
  fin_cases a
  · exact context_12_22952_235027
  · exact context_12_22953_235041
  · exact context_12_22954_224365
  · exact context_12_22955_235063

theorem selected_cut_08391 : selected 9 ⟨235081, by decide⟩
    (prefixPartial 12 22956) = some ⟨12, 2, 0, 235081, 22956, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_22956_235081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22956 ⟨235081, by decide⟩ :=
  accepted_of_selected 12 22956 ⟨235081, by decide⟩ ⟨12, 2, 0, 235081, 22956, 1453, 65536⟩
    (by decide) selected_cut_08391

theorem selected_cut_08392 : selected 9 ⟨235100, by decide⟩
    (prefixPartial 12 22957) = some ⟨12, 2, 0, 235100, 22957, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_22957_235100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22957 ⟨235100, by decide⟩ :=
  accepted_of_selected 12 22957 ⟨235100, by decide⟩ ⟨12, 2, 0, 235100, 22957, 1321, 65536⟩
    (by decide) selected_cut_08392

theorem selected_cut_08393 : selected 9 ⟨235116, by decide⟩
    (prefixPartial 12 22958) = some ⟨12, 2, 0, 235116, 22958, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_22958_235116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22958 ⟨235116, by decide⟩ :=
  accepted_of_selected 12 22958 ⟨235116, by decide⟩ ⟨12, 2, 0, 235116, 22958, 1413, 65536⟩
    (by decide) selected_cut_08393

theorem selected_cut_08394 : selected 9 ⟨235130, by decide⟩
    (prefixPartial 12 22959) = some ⟨12, 2, 0, 235130, 22959, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_22959_235130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22959 ⟨235130, by decide⟩ :=
  accepted_of_selected 12 22959 ⟨235130, by decide⟩ ⟨12, 2, 0, 235130, 22959, 1341, 65536⟩
    (by decide) selected_cut_08394

theorem unmarked_context_11_5739_235131 : frontier 10 ⟨235131, by decide⟩
    (prefixCache 11 5739) (prefixPartial 11 5739) = false := by
  decide +kernel

theorem node_context_11_5739_235131 : EJMOriginalGlobalDAGData.nodes 10 ⟨235131, by decide⟩ =
    .split (coordinate 11) (![⟨235081, by decide⟩,⟨235100, by decide⟩,⟨235116, by decide⟩,⟨235130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5739_235131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5739 ⟨235131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5739
    ⟨235131, by decide⟩ (by decide) (![⟨235081, by decide⟩,⟨235100, by decide⟩,⟨235116, by decide⟩,⟨235130, by decide⟩]) unmarked_context_11_5739_235131 node_context_11_5739_235131
  intro a
  fin_cases a
  · exact context_12_22956_235081
  · exact context_12_22957_235100
  · exact context_12_22958_235116
  · exact context_12_22959_235130

theorem unmarked_context_10_1434_235132 : frontier 11 ⟨235132, by decide⟩
    (prefixCache 10 1434) (prefixPartial 10 1434) = false := by
  decide +kernel

theorem node_context_10_1434_235132 : EJMOriginalGlobalDAGData.nodes 11 ⟨235132, by decide⟩ =
    .split (coordinate 10) (![⟨234940, by decide⟩,⟨235010, by decide⟩,⟨235064, by decide⟩,⟨235131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1434_235132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1434 ⟨235132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1434
    ⟨235132, by decide⟩ (by decide) (![⟨234940, by decide⟩,⟨235010, by decide⟩,⟨235064, by decide⟩,⟨235131, by decide⟩]) unmarked_context_10_1434_235132 node_context_10_1434_235132
  intro a
  fin_cases a
  · exact context_11_5736_234940
  · exact context_11_5737_235010
  · exact context_11_5738_235064
  · exact context_11_5739_235131

theorem selected_cut_08395 : selected 9 ⟨235143, by decide⟩
    (prefixPartial 12 22960) = some ⟨12, 2, 0, 235143, 22960, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_22960_235143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22960 ⟨235143, by decide⟩ :=
  accepted_of_selected 12 22960 ⟨235143, by decide⟩ ⟨12, 2, 0, 235143, 22960, 1397, 65536⟩
    (by decide) selected_cut_08395

theorem selected_cut_08396 : selected 9 ⟨235157, by decide⟩
    (prefixPartial 12 22961) = some ⟨12, 2, 0, 235157, 22961, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_22961_235157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22961 ⟨235157, by decide⟩ :=
  accepted_of_selected 12 22961 ⟨235157, by decide⟩ ⟨12, 2, 0, 235157, 22961, 1401, 65536⟩
    (by decide) selected_cut_08396

theorem selected_cut_08397 : selected 9 ⟨235170, by decide⟩
    (prefixPartial 12 22962) = some ⟨12, 2, 0, 235170, 22962, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_22962_235170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22962 ⟨235170, by decide⟩ :=
  accepted_of_selected 12 22962 ⟨235170, by decide⟩ ⟨12, 2, 0, 235170, 22962, 1489, 65536⟩
    (by decide) selected_cut_08397

theorem selected_cut_08398 : selected 9 ⟨235186, by decide⟩
    (prefixPartial 12 22963) = some ⟨12, 2, 0, 235186, 22963, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_22963_235186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22963 ⟨235186, by decide⟩ :=
  accepted_of_selected 12 22963 ⟨235186, by decide⟩ ⟨12, 2, 0, 235186, 22963, 1425, 65536⟩
    (by decide) selected_cut_08398

theorem unmarked_context_11_5740_235187 : frontier 10 ⟨235187, by decide⟩
    (prefixCache 11 5740) (prefixPartial 11 5740) = false := by
  decide +kernel

theorem node_context_11_5740_235187 : EJMOriginalGlobalDAGData.nodes 10 ⟨235187, by decide⟩ =
    .split (coordinate 11) (![⟨235143, by decide⟩,⟨235157, by decide⟩,⟨235170, by decide⟩,⟨235186, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5740_235187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5740 ⟨235187, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5740
    ⟨235187, by decide⟩ (by decide) (![⟨235143, by decide⟩,⟨235157, by decide⟩,⟨235170, by decide⟩,⟨235186, by decide⟩]) unmarked_context_11_5740_235187 node_context_11_5740_235187
  intro a
  fin_cases a
  · exact context_12_22960_235143
  · exact context_12_22961_235157
  · exact context_12_22962_235170
  · exact context_12_22963_235186

theorem selected_cut_08399 : selected 9 ⟨235198, by decide⟩
    (prefixPartial 12 22964) = some ⟨12, 2, 0, 235198, 22964, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_22964_235198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22964 ⟨235198, by decide⟩ :=
  accepted_of_selected 12 22964 ⟨235198, by decide⟩ ⟨12, 2, 0, 235198, 22964, 1121, 65536⟩
    (by decide) selected_cut_08399

theorem selected_cut_08400 : selected 9 ⟨235213, by decide⟩
    (prefixPartial 12 22965) = some ⟨12, 2, 0, 235213, 22965, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_22965_235213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22965 ⟨235213, by decide⟩ :=
  accepted_of_selected 12 22965 ⟨235213, by decide⟩ ⟨12, 2, 0, 235213, 22965, 1597, 65536⟩
    (by decide) selected_cut_08400

theorem selected_cut_08401 : selected 9 ⟨235224, by decide⟩
    (prefixPartial 12 22966) = some ⟨12, 2, 0, 235224, 22966, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_22966_235224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22966 ⟨235224, by decide⟩ :=
  accepted_of_selected 12 22966 ⟨235224, by decide⟩ ⟨12, 2, 0, 235224, 22966, 1149, 65536⟩
    (by decide) selected_cut_08401

theorem selected_cut_08402 : selected 9 ⟨235236, by decide⟩
    (prefixPartial 12 22967) = some ⟨12, 2, 0, 235236, 22967, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_22967_235236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22967 ⟨235236, by decide⟩ :=
  accepted_of_selected 12 22967 ⟨235236, by decide⟩ ⟨12, 2, 0, 235236, 22967, 1121, 65536⟩
    (by decide) selected_cut_08402

theorem unmarked_context_11_5741_235237 : frontier 10 ⟨235237, by decide⟩
    (prefixCache 11 5741) (prefixPartial 11 5741) = false := by
  decide +kernel

theorem node_context_11_5741_235237 : EJMOriginalGlobalDAGData.nodes 10 ⟨235237, by decide⟩ =
    .split (coordinate 11) (![⟨235198, by decide⟩,⟨235213, by decide⟩,⟨235224, by decide⟩,⟨235236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5741_235237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5741 ⟨235237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5741
    ⟨235237, by decide⟩ (by decide) (![⟨235198, by decide⟩,⟨235213, by decide⟩,⟨235224, by decide⟩,⟨235236, by decide⟩]) unmarked_context_11_5741_235237 node_context_11_5741_235237
  intro a
  fin_cases a
  · exact context_12_22964_235198
  · exact context_12_22965_235213
  · exact context_12_22966_235224
  · exact context_12_22967_235236

theorem selected_cut_08403 : selected 9 ⟨235248, by decide⟩
    (prefixPartial 12 22968) = some ⟨12, 2, 0, 235248, 22968, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_22968_235248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22968 ⟨235248, by decide⟩ :=
  accepted_of_selected 12 22968 ⟨235248, by decide⟩ ⟨12, 2, 0, 235248, 22968, 1145, 65536⟩
    (by decide) selected_cut_08403

theorem selected_cut_08404 : selected 9 ⟨235260, by decide⟩
    (prefixPartial 12 22969) = some ⟨12, 2, 0, 235260, 22969, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_22969_235260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22969 ⟨235260, by decide⟩ :=
  accepted_of_selected 12 22969 ⟨235260, by decide⟩ ⟨12, 2, 0, 235260, 22969, 1173, 65536⟩
    (by decide) selected_cut_08404

theorem selected_cut_08405 : selected 9 ⟨235274, by decide⟩
    (prefixPartial 12 22970) = some ⟨12, 2, 0, 235274, 22970, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_22970_235274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22970 ⟨235274, by decide⟩ :=
  accepted_of_selected 12 22970 ⟨235274, by decide⟩ ⟨12, 2, 0, 235274, 22970, 1117, 65536⟩
    (by decide) selected_cut_08405

theorem selected_cut_08406 : selected 9 ⟨235288, by decide⟩
    (prefixPartial 12 22971) = some ⟨12, 2, 0, 235288, 22971, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_22971_235288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22971 ⟨235288, by decide⟩ :=
  accepted_of_selected 12 22971 ⟨235288, by decide⟩ ⟨12, 2, 0, 235288, 22971, 1149, 65536⟩
    (by decide) selected_cut_08406

theorem unmarked_context_11_5742_235289 : frontier 10 ⟨235289, by decide⟩
    (prefixCache 11 5742) (prefixPartial 11 5742) = false := by
  decide +kernel

theorem node_context_11_5742_235289 : EJMOriginalGlobalDAGData.nodes 10 ⟨235289, by decide⟩ =
    .split (coordinate 11) (![⟨235248, by decide⟩,⟨235260, by decide⟩,⟨235274, by decide⟩,⟨235288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5742_235289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5742 ⟨235289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5742
    ⟨235289, by decide⟩ (by decide) (![⟨235248, by decide⟩,⟨235260, by decide⟩,⟨235274, by decide⟩,⟨235288, by decide⟩]) unmarked_context_11_5742_235289 node_context_11_5742_235289
  intro a
  fin_cases a
  · exact context_12_22968_235248
  · exact context_12_22969_235260
  · exact context_12_22970_235274
  · exact context_12_22971_235288

theorem selected_cut_08407 : selected 10 ⟨235331, by decide⟩
    (prefixPartial 11 5743) = some ⟨11, 2, 0, 235331, 5743, 3989, 262144⟩ := by
  decide +kernel

theorem context_11_5743_235331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5743 ⟨235331, by decide⟩ :=
  accepted_of_selected 11 5743 ⟨235331, by decide⟩ ⟨11, 2, 0, 235331, 5743, 3989, 262144⟩
    (by decide) selected_cut_08407

theorem unmarked_context_10_1435_235332 : frontier 11 ⟨235332, by decide⟩
    (prefixCache 10 1435) (prefixPartial 10 1435) = false := by
  decide +kernel

theorem node_context_10_1435_235332 : EJMOriginalGlobalDAGData.nodes 11 ⟨235332, by decide⟩ =
    .split (coordinate 10) (![⟨235187, by decide⟩,⟨235237, by decide⟩,⟨235289, by decide⟩,⟨235331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1435_235332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1435 ⟨235332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1435
    ⟨235332, by decide⟩ (by decide) (![⟨235187, by decide⟩,⟨235237, by decide⟩,⟨235289, by decide⟩,⟨235331, by decide⟩]) unmarked_context_10_1435_235332 node_context_10_1435_235332
  intro a
  fin_cases a
  · exact context_11_5740_235187
  · exact context_11_5741_235237
  · exact context_11_5742_235289
  · exact context_11_5743_235331

theorem unmarked_context_9_358_235333 : frontier 12 ⟨235333, by decide⟩
    (prefixCache 9 358) (prefixPartial 9 358) = false := by
  decide +kernel

theorem node_context_9_358_235333 : EJMOriginalGlobalDAGData.nodes 12 ⟨235333, by decide⟩ =
    .split (coordinate 9) (![⟨234540, by decide⟩,⟨234866, by decide⟩,⟨235132, by decide⟩,⟨235332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_358_235333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 358 ⟨235333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 358
    ⟨235333, by decide⟩ (by decide) (![⟨234540, by decide⟩,⟨234866, by decide⟩,⟨235132, by decide⟩,⟨235332, by decide⟩]) unmarked_context_9_358_235333 node_context_9_358_235333
  intro a
  fin_cases a
  · exact context_10_1432_234540
  · exact context_10_1433_234866
  · exact context_10_1434_235132
  · exact context_10_1435_235332

theorem selected_cut_08408 : selected 9 ⟨235340, by decide⟩
    (prefixPartial 12 22976) = some ⟨12, 2, 0, 235340, 22976, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_22976_235340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22976 ⟨235340, by decide⟩ :=
  accepted_of_selected 12 22976 ⟨235340, by decide⟩ ⟨12, 2, 0, 235340, 22976, 1201, 65536⟩
    (by decide) selected_cut_08408

theorem selected_cut_08409 : selected 9 ⟨235346, by decide⟩
    (prefixPartial 12 22977) = some ⟨12, 2, 0, 235346, 22977, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_22977_235346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22977 ⟨235346, by decide⟩ :=
  accepted_of_selected 12 22977 ⟨235346, by decide⟩ ⟨12, 2, 0, 235346, 22977, 1117, 65536⟩
    (by decide) selected_cut_08409

theorem selected_cut_08410 : selected 9 ⟨235360, by decide⟩
    (prefixPartial 12 22978) = some ⟨12, 2, 0, 235360, 22978, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_22978_235360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22978 ⟨235360, by decide⟩ :=
  accepted_of_selected 12 22978 ⟨235360, by decide⟩ ⟨12, 2, 0, 235360, 22978, 1221, 65536⟩
    (by decide) selected_cut_08410

theorem selected_cut_08411 : selected 9 ⟨235368, by decide⟩
    (prefixPartial 12 22979) = some ⟨12, 2, 0, 235368, 22979, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_22979_235368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22979 ⟨235368, by decide⟩ :=
  accepted_of_selected 12 22979 ⟨235368, by decide⟩ ⟨12, 2, 0, 235368, 22979, 1157, 65536⟩
    (by decide) selected_cut_08411

theorem unmarked_context_11_5744_235369 : frontier 10 ⟨235369, by decide⟩
    (prefixCache 11 5744) (prefixPartial 11 5744) = false := by
  decide +kernel

theorem node_context_11_5744_235369 : EJMOriginalGlobalDAGData.nodes 10 ⟨235369, by decide⟩ =
    .split (coordinate 11) (![⟨235340, by decide⟩,⟨235346, by decide⟩,⟨235360, by decide⟩,⟨235368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5744_235369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5744 ⟨235369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5744
    ⟨235369, by decide⟩ (by decide) (![⟨235340, by decide⟩,⟨235346, by decide⟩,⟨235360, by decide⟩,⟨235368, by decide⟩]) unmarked_context_11_5744_235369 node_context_11_5744_235369
  intro a
  fin_cases a
  · exact context_12_22976_235340
  · exact context_12_22977_235346
  · exact context_12_22978_235360
  · exact context_12_22979_235368

theorem selected_cut_08412 : selected 10 ⟨235408, by decide⟩
    (prefixPartial 11 5745) = some ⟨11, 2, 0, 235408, 5745, 4037, 262144⟩ := by
  decide +kernel

theorem context_11_5745_235408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5745 ⟨235408, by decide⟩ :=
  accepted_of_selected 11 5745 ⟨235408, by decide⟩ ⟨11, 2, 0, 235408, 5745, 4037, 262144⟩
    (by decide) selected_cut_08412

theorem selected_cut_08413 : selected 10 ⟨235436, by decide⟩
    (prefixPartial 11 5746) = some ⟨11, 2, 0, 235436, 5746, 3557, 262144⟩ := by
  decide +kernel

theorem context_11_5746_235436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5746 ⟨235436, by decide⟩ :=
  accepted_of_selected 11 5746 ⟨235436, by decide⟩ ⟨11, 2, 0, 235436, 5746, 3557, 262144⟩
    (by decide) selected_cut_08413

theorem selected_cut_08414 : selected 10 ⟨235467, by decide⟩
    (prefixPartial 11 5747) = some ⟨11, 2, 0, 235467, 5747, 3521, 262144⟩ := by
  decide +kernel

theorem context_11_5747_235467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5747 ⟨235467, by decide⟩ :=
  accepted_of_selected 11 5747 ⟨235467, by decide⟩ ⟨11, 2, 0, 235467, 5747, 3521, 262144⟩
    (by decide) selected_cut_08414

theorem unmarked_context_10_1436_235468 : frontier 11 ⟨235468, by decide⟩
    (prefixCache 10 1436) (prefixPartial 10 1436) = false := by
  decide +kernel

theorem node_context_10_1436_235468 : EJMOriginalGlobalDAGData.nodes 11 ⟨235468, by decide⟩ =
    .split (coordinate 10) (![⟨235369, by decide⟩,⟨235408, by decide⟩,⟨235436, by decide⟩,⟨235467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1436_235468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1436 ⟨235468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1436
    ⟨235468, by decide⟩ (by decide) (![⟨235369, by decide⟩,⟨235408, by decide⟩,⟨235436, by decide⟩,⟨235467, by decide⟩]) unmarked_context_10_1436_235468 node_context_10_1436_235468
  intro a
  fin_cases a
  · exact context_11_5744_235369
  · exact context_11_5745_235408
  · exact context_11_5746_235436
  · exact context_11_5747_235467

theorem selected_cut_08415 : selected 10 ⟨235499, by decide⟩
    (prefixPartial 11 5748) = some ⟨11, 2, 0, 235499, 5748, 2993, 262144⟩ := by
  decide +kernel

theorem context_11_5748_235499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5748 ⟨235499, by decide⟩ :=
  accepted_of_selected 11 5748 ⟨235499, by decide⟩ ⟨11, 2, 0, 235499, 5748, 2993, 262144⟩
    (by decide) selected_cut_08415

theorem selected_cut_08416 : selected 10 ⟨235523, by decide⟩
    (prefixPartial 11 5749) = some ⟨11, 2, 0, 235523, 5749, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_5749_235523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5749 ⟨235523, by decide⟩ :=
  accepted_of_selected 11 5749 ⟨235523, by decide⟩ ⟨11, 2, 0, 235523, 5749, 2393, 262144⟩
    (by decide) selected_cut_08416

theorem selected_cut_08417 : selected 10 ⟨235544, by decide⟩
    (prefixPartial 11 5750) = some ⟨11, 2, 0, 235544, 5750, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_5750_235544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5750 ⟨235544, by decide⟩ :=
  accepted_of_selected 11 5750 ⟨235544, by decide⟩ ⟨11, 2, 0, 235544, 5750, 2101, 262144⟩
    (by decide) selected_cut_08417

theorem selected_cut_08418 : selected 10 ⟨235561, by decide⟩
    (prefixPartial 11 5751) = some ⟨11, 2, 0, 235561, 5751, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_5751_235561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5751 ⟨235561, by decide⟩ :=
  accepted_of_selected 11 5751 ⟨235561, by decide⟩ ⟨11, 2, 0, 235561, 5751, 1861, 262144⟩
    (by decide) selected_cut_08418

theorem unmarked_context_10_1437_235562 : frontier 11 ⟨235562, by decide⟩
    (prefixCache 10 1437) (prefixPartial 10 1437) = false := by
  decide +kernel

theorem node_context_10_1437_235562 : EJMOriginalGlobalDAGData.nodes 11 ⟨235562, by decide⟩ =
    .split (coordinate 10) (![⟨235499, by decide⟩,⟨235523, by decide⟩,⟨235544, by decide⟩,⟨235561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1437_235562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1437 ⟨235562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1437
    ⟨235562, by decide⟩ (by decide) (![⟨235499, by decide⟩,⟨235523, by decide⟩,⟨235544, by decide⟩,⟨235561, by decide⟩]) unmarked_context_10_1437_235562 node_context_10_1437_235562
  intro a
  fin_cases a
  · exact context_11_5748_235499
  · exact context_11_5749_235523
  · exact context_11_5750_235544
  · exact context_11_5751_235561

theorem selected_cut_08419 : selected 10 ⟨235582, by decide⟩
    (prefixPartial 11 5752) = some ⟨11, 2, 0, 235582, 5752, 1921, 262144⟩ := by
  decide +kernel

theorem context_11_5752_235582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5752 ⟨235582, by decide⟩ :=
  accepted_of_selected 11 5752 ⟨235582, by decide⟩ ⟨11, 2, 0, 235582, 5752, 1921, 262144⟩
    (by decide) selected_cut_08419

theorem selected_cut_08420 : selected 10 ⟨235598, by decide⟩
    (prefixPartial 11 5753) = some ⟨11, 2, 0, 235598, 5753, 1473, 262144⟩ := by
  decide +kernel

theorem context_11_5753_235598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5753 ⟨235598, by decide⟩ :=
  accepted_of_selected 11 5753 ⟨235598, by decide⟩ ⟨11, 2, 0, 235598, 5753, 1473, 262144⟩
    (by decide) selected_cut_08420

theorem selected_cut_08421 : selected 10 ⟨235621, by decide⟩
    (prefixPartial 11 5754) = some ⟨11, 2, 0, 235621, 5754, 1389, 262144⟩ := by
  decide +kernel

theorem context_11_5754_235621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5754 ⟨235621, by decide⟩ :=
  accepted_of_selected 11 5754 ⟨235621, by decide⟩ ⟨11, 2, 0, 235621, 5754, 1389, 262144⟩
    (by decide) selected_cut_08421

theorem selected_cut_08422 : selected 10 ⟨235634, by decide⟩
    (prefixPartial 11 5755) = some ⟨11, 2, 0, 235634, 5755, 961, 262144⟩ := by
  decide +kernel

theorem context_11_5755_235634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5755 ⟨235634, by decide⟩ :=
  accepted_of_selected 11 5755 ⟨235634, by decide⟩ ⟨11, 2, 0, 235634, 5755, 961, 262144⟩
    (by decide) selected_cut_08422

theorem unmarked_context_10_1438_235635 : frontier 11 ⟨235635, by decide⟩
    (prefixCache 10 1438) (prefixPartial 10 1438) = false := by
  decide +kernel

theorem node_context_10_1438_235635 : EJMOriginalGlobalDAGData.nodes 11 ⟨235635, by decide⟩ =
    .split (coordinate 10) (![⟨235582, by decide⟩,⟨235598, by decide⟩,⟨235621, by decide⟩,⟨235634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1438_235635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1438 ⟨235635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1438
    ⟨235635, by decide⟩ (by decide) (![⟨235582, by decide⟩,⟨235598, by decide⟩,⟨235621, by decide⟩,⟨235634, by decide⟩]) unmarked_context_10_1438_235635 node_context_10_1438_235635
  intro a
  fin_cases a
  · exact context_11_5752_235582
  · exact context_11_5753_235598
  · exact context_11_5754_235621
  · exact context_11_5755_235634

theorem selected_cut_08423 : selected 11 ⟨235679, by decide⟩
    (prefixPartial 10 1439) = some ⟨10, 2, 0, 235679, 1439, 1889, 1048576⟩ := by
  decide +kernel

theorem context_10_1439_235679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1439 ⟨235679, by decide⟩ :=
  accepted_of_selected 10 1439 ⟨235679, by decide⟩ ⟨10, 2, 0, 235679, 1439, 1889, 1048576⟩
    (by decide) selected_cut_08423

theorem unmarked_context_9_359_235680 : frontier 12 ⟨235680, by decide⟩
    (prefixCache 9 359) (prefixPartial 9 359) = false := by
  decide +kernel

theorem node_context_9_359_235680 : EJMOriginalGlobalDAGData.nodes 12 ⟨235680, by decide⟩ =
    .split (coordinate 9) (![⟨235468, by decide⟩,⟨235562, by decide⟩,⟨235635, by decide⟩,⟨235679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_359_235680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 359 ⟨235680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 359
    ⟨235680, by decide⟩ (by decide) (![⟨235468, by decide⟩,⟨235562, by decide⟩,⟨235635, by decide⟩,⟨235679, by decide⟩]) unmarked_context_9_359_235680 node_context_9_359_235680
  intro a
  fin_cases a
  · exact context_10_1436_235468
  · exact context_10_1437_235562
  · exact context_10_1438_235635
  · exact context_10_1439_235679

theorem unmarked_context_8_89_235681 : frontier 13 ⟨235681, by decide⟩
    (prefixCache 8 89) (prefixPartial 8 89) = false := by
  decide +kernel

theorem node_context_8_89_235681 : EJMOriginalGlobalDAGData.nodes 13 ⟨235681, by decide⟩ =
    .split (coordinate 8) (![⟨231107, by decide⟩,⟨234099, by decide⟩,⟨235333, by decide⟩,⟨235680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_89_235681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 89 ⟨235681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 89
    ⟨235681, by decide⟩ (by decide) (![⟨231107, by decide⟩,⟨234099, by decide⟩,⟨235333, by decide⟩,⟨235680, by decide⟩]) unmarked_context_8_89_235681 node_context_8_89_235681
  intro a
  fin_cases a
  · exact context_9_356_231107
  · exact context_9_357_234099
  · exact context_9_358_235333
  · exact context_9_359_235680

theorem selected_cut_08424 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 23040) = some ⟨12, 1, 0, 34034, 23040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23040_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23040 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 23040 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 23040, 1, 65536⟩
    (by decide) selected_cut_08424

theorem selected_cut_08425 : selected 7 ⟨235727, by decide⟩
    (prefixPartial 14 368656) = some ⟨14, 2, 0, 235727, 368656, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_368656_235727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368656 ⟨235727, by decide⟩ :=
  accepted_of_selected 14 368656 ⟨235727, by decide⟩ ⟨14, 2, 0, 235727, 368656, 1357, 4096⟩
    (by decide) selected_cut_08425

theorem selected_cut_08426 : selected 7 ⟨235750, by decide⟩
    (prefixPartial 14 368657) = some ⟨14, 2, 0, 235750, 368657, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_368657_235750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368657 ⟨235750, by decide⟩ :=
  accepted_of_selected 14 368657 ⟨235750, by decide⟩ ⟨14, 2, 0, 235750, 368657, 1221, 4096⟩
    (by decide) selected_cut_08426

theorem selected_cut_08427 : selected 7 ⟨235767, by decide⟩
    (prefixPartial 14 368658) = some ⟨14, 2, 0, 235767, 368658, 969, 4096⟩ := by
  decide +kernel

theorem context_14_368658_235767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368658 ⟨235767, by decide⟩ :=
  accepted_of_selected 14 368658 ⟨235767, by decide⟩ ⟨14, 2, 0, 235767, 368658, 969, 4096⟩
    (by decide) selected_cut_08427

theorem selected_cut_08428 : selected 7 ⟨235787, by decide⟩
    (prefixPartial 14 368659) = some ⟨14, 2, 0, 235787, 368659, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_368659_235787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368659 ⟨235787, by decide⟩ :=
  accepted_of_selected 14 368659 ⟨235787, by decide⟩ ⟨14, 2, 0, 235787, 368659, 1097, 4096⟩
    (by decide) selected_cut_08428

theorem unmarked_context_13_92164_235788 : frontier 8 ⟨235788, by decide⟩
    (prefixCache 13 92164) (prefixPartial 13 92164) = false := by
  decide +kernel

theorem node_context_13_92164_235788 : EJMOriginalGlobalDAGData.nodes 8 ⟨235788, by decide⟩ =
    .split (coordinate 13) (![⟨235727, by decide⟩,⟨235750, by decide⟩,⟨235767, by decide⟩,⟨235787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92164_235788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92164 ⟨235788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92164
    ⟨235788, by decide⟩ (by decide) (![⟨235727, by decide⟩,⟨235750, by decide⟩,⟨235767, by decide⟩,⟨235787, by decide⟩]) unmarked_context_13_92164_235788 node_context_13_92164_235788
  intro a
  fin_cases a
  · exact context_14_368656_235727
  · exact context_14_368657_235750
  · exact context_14_368658_235767
  · exact context_14_368659_235787

theorem selected_cut_08429 : selected 8 ⟨235887, by decide⟩
    (prefixPartial 13 92165) = some ⟨13, 2, 0, 235887, 92165, 4033, 16384⟩ := by
  decide +kernel

theorem context_13_92165_235887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92165 ⟨235887, by decide⟩ :=
  accepted_of_selected 13 92165 ⟨235887, by decide⟩ ⟨13, 2, 0, 235887, 92165, 4033, 16384⟩
    (by decide) selected_cut_08429

theorem selected_cut_08430 : selected 8 ⟨235932, by decide⟩
    (prefixPartial 13 92166) = some ⟨13, 2, 0, 235932, 92166, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_92166_235932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92166 ⟨235932, by decide⟩ :=
  accepted_of_selected 13 92166 ⟨235932, by decide⟩ ⟨13, 2, 0, 235932, 92166, 2017, 16384⟩
    (by decide) selected_cut_08430

theorem selected_cut_08431 : selected 8 ⟨235967, by decide⟩
    (prefixPartial 13 92167) = some ⟨13, 2, 0, 235967, 92167, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_92167_235967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92167 ⟨235967, by decide⟩ :=
  accepted_of_selected 13 92167 ⟨235967, by decide⟩ ⟨13, 2, 0, 235967, 92167, 1337, 16384⟩
    (by decide) selected_cut_08431

theorem unmarked_context_12_23041_235968 : frontier 9 ⟨235968, by decide⟩
    (prefixCache 12 23041) (prefixPartial 12 23041) = false := by
  decide +kernel

theorem node_context_12_23041_235968 : EJMOriginalGlobalDAGData.nodes 9 ⟨235968, by decide⟩ =
    .split (coordinate 12) (![⟨235788, by decide⟩,⟨235887, by decide⟩,⟨235932, by decide⟩,⟨235967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23041_235968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23041 ⟨235968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23041
    ⟨235968, by decide⟩ (by decide) (![⟨235788, by decide⟩,⟨235887, by decide⟩,⟨235932, by decide⟩,⟨235967, by decide⟩]) unmarked_context_12_23041_235968 node_context_12_23041_235968
  intro a
  fin_cases a
  · exact context_13_92164_235788
  · exact context_13_92165_235887
  · exact context_13_92166_235932
  · exact context_13_92167_235967

theorem selected_cut_08432 : selected 9 ⟨48867, by decide⟩
    (prefixPartial 12 23042) = some ⟨12, 1, 0, 48867, 23042, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23042_48867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23042 ⟨48867, by decide⟩ :=
  accepted_of_selected 12 23042 ⟨48867, by decide⟩ ⟨12, 1, 0, 48867, 23042, 1, 65536⟩
    (by decide) selected_cut_08432

theorem selected_cut_08433 : selected 7 ⟨236009, by decide⟩
    (prefixPartial 14 368688) = some ⟨14, 2, 0, 236009, 368688, 1825, 4096⟩ := by
  decide +kernel

theorem context_14_368688_236009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368688 ⟨236009, by decide⟩ :=
  accepted_of_selected 14 368688 ⟨236009, by decide⟩ ⟨14, 2, 0, 236009, 368688, 1825, 4096⟩
    (by decide) selected_cut_08433

theorem selected_cut_08434 : selected 7 ⟨236033, by decide⟩
    (prefixPartial 14 368689) = some ⟨14, 2, 0, 236033, 368689, 1373, 4096⟩ := by
  decide +kernel

theorem context_14_368689_236033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368689 ⟨236033, by decide⟩ :=
  accepted_of_selected 14 368689 ⟨236033, by decide⟩ ⟨14, 2, 0, 236033, 368689, 1373, 4096⟩
    (by decide) selected_cut_08434

theorem selected_cut_08435 : selected 7 ⟨236053, by decide⟩
    (prefixPartial 14 368690) = some ⟨14, 2, 0, 236053, 368690, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_368690_236053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368690 ⟨236053, by decide⟩ :=
  accepted_of_selected 14 368690 ⟨236053, by decide⟩ ⟨14, 2, 0, 236053, 368690, 1205, 4096⟩
    (by decide) selected_cut_08435

theorem selected_cut_08436 : selected 7 ⟨236084, by decide⟩
    (prefixPartial 14 368691) = some ⟨14, 2, 0, 236084, 368691, 1421, 4096⟩ := by
  decide +kernel

theorem context_14_368691_236084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368691 ⟨236084, by decide⟩ :=
  accepted_of_selected 14 368691 ⟨236084, by decide⟩ ⟨14, 2, 0, 236084, 368691, 1421, 4096⟩
    (by decide) selected_cut_08436

theorem unmarked_context_13_92172_236085 : frontier 8 ⟨236085, by decide⟩
    (prefixCache 13 92172) (prefixPartial 13 92172) = false := by
  decide +kernel

theorem node_context_13_92172_236085 : EJMOriginalGlobalDAGData.nodes 8 ⟨236085, by decide⟩ =
    .split (coordinate 13) (![⟨236009, by decide⟩,⟨236033, by decide⟩,⟨236053, by decide⟩,⟨236084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92172_236085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92172 ⟨236085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92172
    ⟨236085, by decide⟩ (by decide) (![⟨236009, by decide⟩,⟨236033, by decide⟩,⟨236053, by decide⟩,⟨236084, by decide⟩]) unmarked_context_13_92172_236085 node_context_13_92172_236085
  intro a
  fin_cases a
  · exact context_14_368688_236009
  · exact context_14_368689_236033
  · exact context_14_368690_236053
  · exact context_14_368691_236084

theorem selected_cut_08437 : selected 7 ⟨236114, by decide⟩
    (prefixPartial 14 368692) = some ⟨14, 2, 0, 236114, 368692, 1309, 4096⟩ := by
  decide +kernel

theorem context_14_368692_236114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368692 ⟨236114, by decide⟩ :=
  accepted_of_selected 14 368692 ⟨236114, by decide⟩ ⟨14, 2, 0, 236114, 368692, 1309, 4096⟩
    (by decide) selected_cut_08437

theorem selected_cut_08438 : selected 7 ⟨236157, by decide⟩
    (prefixPartial 14 368693) = some ⟨14, 2, 0, 236157, 368693, 1485, 4096⟩ := by
  decide +kernel

theorem context_14_368693_236157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368693 ⟨236157, by decide⟩ :=
  accepted_of_selected 14 368693 ⟨236157, by decide⟩ ⟨14, 2, 0, 236157, 368693, 1485, 4096⟩
    (by decide) selected_cut_08438

theorem selected_cut_08439 : selected 7 ⟨236186, by decide⟩
    (prefixPartial 14 368694) = some ⟨14, 2, 0, 236186, 368694, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_368694_236186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368694 ⟨236186, by decide⟩ :=
  accepted_of_selected 14 368694 ⟨236186, by decide⟩ ⟨14, 2, 0, 236186, 368694, 1189, 4096⟩
    (by decide) selected_cut_08439

theorem selected_cut_08440 : selected 7 ⟨236210, by decide⟩
    (prefixPartial 14 368695) = some ⟨14, 2, 0, 236210, 368695, 1141, 4096⟩ := by
  decide +kernel

theorem context_14_368695_236210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368695 ⟨236210, by decide⟩ :=
  accepted_of_selected 14 368695 ⟨236210, by decide⟩ ⟨14, 2, 0, 236210, 368695, 1141, 4096⟩
    (by decide) selected_cut_08440

theorem unmarked_context_13_92173_236211 : frontier 8 ⟨236211, by decide⟩
    (prefixCache 13 92173) (prefixPartial 13 92173) = false := by
  decide +kernel

theorem node_context_13_92173_236211 : EJMOriginalGlobalDAGData.nodes 8 ⟨236211, by decide⟩ =
    .split (coordinate 13) (![⟨236114, by decide⟩,⟨236157, by decide⟩,⟨236186, by decide⟩,⟨236210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92173_236211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92173 ⟨236211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92173
    ⟨236211, by decide⟩ (by decide) (![⟨236114, by decide⟩,⟨236157, by decide⟩,⟨236186, by decide⟩,⟨236210, by decide⟩]) unmarked_context_13_92173_236211 node_context_13_92173_236211
  intro a
  fin_cases a
  · exact context_14_368692_236114
  · exact context_14_368693_236157
  · exact context_14_368694_236186
  · exact context_14_368695_236210

theorem selected_cut_08441 : selected 8 ⟨236255, by decide⟩
    (prefixPartial 13 92174) = some ⟨13, 2, 0, 236255, 92174, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_92174_236255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92174 ⟨236255, by decide⟩ :=
  accepted_of_selected 13 92174 ⟨236255, by decide⟩ ⟨13, 2, 0, 236255, 92174, 2285, 16384⟩
    (by decide) selected_cut_08441

theorem selected_cut_08442 : selected 8 ⟨236287, by decide⟩
    (prefixPartial 13 92175) = some ⟨13, 2, 0, 236287, 92175, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_92175_236287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92175 ⟨236287, by decide⟩ :=
  accepted_of_selected 13 92175 ⟨236287, by decide⟩ ⟨13, 2, 0, 236287, 92175, 1349, 16384⟩
    (by decide) selected_cut_08442

theorem unmarked_context_12_23043_236288 : frontier 9 ⟨236288, by decide⟩
    (prefixCache 12 23043) (prefixPartial 12 23043) = false := by
  decide +kernel

theorem node_context_12_23043_236288 : EJMOriginalGlobalDAGData.nodes 9 ⟨236288, by decide⟩ =
    .split (coordinate 12) (![⟨236085, by decide⟩,⟨236211, by decide⟩,⟨236255, by decide⟩,⟨236287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23043_236288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23043 ⟨236288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23043
    ⟨236288, by decide⟩ (by decide) (![⟨236085, by decide⟩,⟨236211, by decide⟩,⟨236255, by decide⟩,⟨236287, by decide⟩]) unmarked_context_12_23043_236288 node_context_12_23043_236288
  intro a
  fin_cases a
  · exact context_13_92172_236085
  · exact context_13_92173_236211
  · exact context_13_92174_236255
  · exact context_13_92175_236287

theorem unmarked_context_11_5760_236289 : frontier 10 ⟨236289, by decide⟩
    (prefixCache 11 5760) (prefixPartial 11 5760) = false := by
  decide +kernel

theorem node_context_11_5760_236289 : EJMOriginalGlobalDAGData.nodes 10 ⟨236289, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨235968, by decide⟩,⟨48867, by decide⟩,⟨236288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5760_236289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5760 ⟨236289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5760
    ⟨236289, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨235968, by decide⟩,⟨48867, by decide⟩,⟨236288, by decide⟩]) unmarked_context_11_5760_236289 node_context_11_5760_236289
  intro a
  fin_cases a
  · exact context_12_23040_34034
  · exact context_12_23041_235968
  · exact context_12_23042_48867
  · exact context_12_23043_236288

theorem selected_cut_08443 : selected 8 ⟨236384, by decide⟩
    (prefixPartial 13 92176) = some ⟨13, 2, 0, 236384, 92176, 3989, 16384⟩ := by
  decide +kernel

theorem context_13_92176_236384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92176 ⟨236384, by decide⟩ :=
  accepted_of_selected 13 92176 ⟨236384, by decide⟩ ⟨13, 2, 0, 236384, 92176, 3989, 16384⟩
    (by decide) selected_cut_08443

theorem selected_cut_08444 : selected 7 ⟨236423, by decide⟩
    (prefixPartial 14 368708) = some ⟨14, 2, 0, 236423, 368708, 1597, 4096⟩ := by
  decide +kernel

theorem context_14_368708_236423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368708 ⟨236423, by decide⟩ :=
  accepted_of_selected 14 368708 ⟨236423, by decide⟩ ⟨14, 2, 0, 236423, 368708, 1597, 4096⟩
    (by decide) selected_cut_08444

theorem selected_cut_08445 : selected 7 ⟨236473, by decide⟩
    (prefixPartial 14 368709) = some ⟨14, 2, 0, 236473, 368709, 1633, 4096⟩ := by
  decide +kernel

theorem context_14_368709_236473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368709 ⟨236473, by decide⟩ :=
  accepted_of_selected 14 368709 ⟨236473, by decide⟩ ⟨14, 2, 0, 236473, 368709, 1633, 4096⟩
    (by decide) selected_cut_08445

theorem selected_cut_08446 : selected 7 ⟨236496, by decide⟩
    (prefixPartial 14 368710) = some ⟨14, 2, 0, 236496, 368710, 997, 4096⟩ := by
  decide +kernel

theorem context_14_368710_236496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368710 ⟨236496, by decide⟩ :=
  accepted_of_selected 14 368710 ⟨236496, by decide⟩ ⟨14, 2, 0, 236496, 368710, 997, 4096⟩
    (by decide) selected_cut_08446

theorem selected_cut_08447 : selected 7 ⟨236522, by decide⟩
    (prefixPartial 14 368711) = some ⟨14, 2, 0, 236522, 368711, 1129, 4096⟩ := by
  decide +kernel

theorem context_14_368711_236522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 368711 ⟨236522, by decide⟩ :=
  accepted_of_selected 14 368711 ⟨236522, by decide⟩ ⟨14, 2, 0, 236522, 368711, 1129, 4096⟩
    (by decide) selected_cut_08447

theorem unmarked_context_13_92177_236523 : frontier 8 ⟨236523, by decide⟩
    (prefixCache 13 92177) (prefixPartial 13 92177) = false := by
  decide +kernel

theorem node_context_13_92177_236523 : EJMOriginalGlobalDAGData.nodes 8 ⟨236523, by decide⟩ =
    .split (coordinate 13) (![⟨236423, by decide⟩,⟨236473, by decide⟩,⟨236496, by decide⟩,⟨236522, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92177_236523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92177 ⟨236523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92177
    ⟨236523, by decide⟩ (by decide) (![⟨236423, by decide⟩,⟨236473, by decide⟩,⟨236496, by decide⟩,⟨236522, by decide⟩]) unmarked_context_13_92177_236523 node_context_13_92177_236523
  intro a
  fin_cases a
  · exact context_14_368708_236423
  · exact context_14_368709_236473
  · exact context_14_368710_236496
  · exact context_14_368711_236522

theorem selected_cut_08448 : selected 8 ⟨236579, by decide⟩
    (prefixPartial 13 92178) = some ⟨13, 2, 0, 236579, 92178, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_92178_236579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92178 ⟨236579, by decide⟩ :=
  accepted_of_selected 13 92178 ⟨236579, by decide⟩ ⟨13, 2, 0, 236579, 92178, 2209, 16384⟩
    (by decide) selected_cut_08448

theorem selected_cut_08449 : selected 8 ⟨236624, by decide⟩
    (prefixPartial 13 92179) = some ⟨13, 2, 0, 236624, 92179, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_92179_236624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92179 ⟨236624, by decide⟩ :=
  accepted_of_selected 13 92179 ⟨236624, by decide⟩ ⟨13, 2, 0, 236624, 92179, 1461, 16384⟩
    (by decide) selected_cut_08449

theorem unmarked_context_12_23044_236625 : frontier 9 ⟨236625, by decide⟩
    (prefixCache 12 23044) (prefixPartial 12 23044) = false := by
  decide +kernel

theorem node_context_12_23044_236625 : EJMOriginalGlobalDAGData.nodes 9 ⟨236625, by decide⟩ =
    .split (coordinate 12) (![⟨236384, by decide⟩,⟨236523, by decide⟩,⟨236579, by decide⟩,⟨236624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23044_236625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23044 ⟨236625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23044
    ⟨236625, by decide⟩ (by decide) (![⟨236384, by decide⟩,⟨236523, by decide⟩,⟨236579, by decide⟩,⟨236624, by decide⟩]) unmarked_context_12_23044_236625 node_context_12_23044_236625
  intro a
  fin_cases a
  · exact context_13_92176_236384
  · exact context_13_92177_236523
  · exact context_13_92178_236579
  · exact context_13_92179_236624

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
