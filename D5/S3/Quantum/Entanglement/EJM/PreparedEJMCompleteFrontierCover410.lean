/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover409
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_39363 : selected 9 ⟨1068034, by decide⟩
    (prefixPartial 12 302913) = some ⟨12, 2, 0, 1068034, 302913, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_302913_1068034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302913 ⟨1068034, by decide⟩ :=
  accepted_of_selected 12 302913 ⟨1068034, by decide⟩ ⟨12, 2, 0, 1068034, 302913, 2841, 65536⟩
    (by decide) selected_cut_39363

theorem selected_cut_39364 : selected 9 ⟨1068072, by decide⟩
    (prefixPartial 12 302914) = some ⟨12, 2, 0, 1068072, 302914, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_302914_1068072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302914 ⟨1068072, by decide⟩ :=
  accepted_of_selected 12 302914 ⟨1068072, by decide⟩ ⟨12, 2, 0, 1068072, 302914, 2721, 65536⟩
    (by decide) selected_cut_39364

theorem selected_cut_39365 : selected 9 ⟨1068109, by decide⟩
    (prefixPartial 12 302915) = some ⟨12, 2, 0, 1068109, 302915, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_302915_1068109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302915 ⟨1068109, by decide⟩ :=
  accepted_of_selected 12 302915 ⟨1068109, by decide⟩ ⟨12, 2, 0, 1068109, 302915, 2625, 65536⟩
    (by decide) selected_cut_39365

theorem unmarked_context_11_75728_1068110 : frontier 10 ⟨1068110, by decide⟩
    (prefixCache 11 75728) (prefixPartial 11 75728) = false := by
  decide +kernel

theorem node_context_11_75728_1068110 : EJMOriginalGlobalDAGData.nodes 10 ⟨1068110, by decide⟩ =
    .split (coordinate 11) (![⟨1051681, by decide⟩,⟨1068034, by decide⟩,⟨1068072, by decide⟩,⟨1068109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75728_1068110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75728 ⟨1068110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75728
    ⟨1068110, by decide⟩ (by decide) (![⟨1051681, by decide⟩,⟨1068034, by decide⟩,⟨1068072, by decide⟩,⟨1068109, by decide⟩]) unmarked_context_11_75728_1068110 node_context_11_75728_1068110
  intro a
  fin_cases a
  · exact context_12_302912_1051681
  · exact context_12_302913_1068034
  · exact context_12_302914_1068072
  · exact context_12_302915_1068109

theorem selected_cut_39366 : selected 9 ⟨1068166, by decide⟩
    (prefixPartial 12 302916) = some ⟨12, 2, 0, 1068166, 302916, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_302916_1068166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302916 ⟨1068166, by decide⟩ :=
  accepted_of_selected 12 302916 ⟨1068166, by decide⟩ ⟨12, 2, 0, 1068166, 302916, 3101, 65536⟩
    (by decide) selected_cut_39366

theorem selected_cut_39367 : selected 9 ⟨1068219, by decide⟩
    (prefixPartial 12 302917) = some ⟨12, 2, 0, 1068219, 302917, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_302917_1068219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302917 ⟨1068219, by decide⟩ :=
  accepted_of_selected 12 302917 ⟨1068219, by decide⟩ ⟨12, 2, 0, 1068219, 302917, 2977, 65536⟩
    (by decide) selected_cut_39367

theorem selected_cut_39368 : selected 9 ⟨1068262, by decide⟩
    (prefixPartial 12 302918) = some ⟨12, 2, 0, 1068262, 302918, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_302918_1068262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302918 ⟨1068262, by decide⟩ :=
  accepted_of_selected 12 302918 ⟨1068262, by decide⟩ ⟨12, 2, 0, 1068262, 302918, 2637, 65536⟩
    (by decide) selected_cut_39368

theorem selected_cut_39369 : selected 9 ⟨1068304, by decide⟩
    (prefixPartial 12 302919) = some ⟨12, 2, 0, 1068304, 302919, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_302919_1068304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302919 ⟨1068304, by decide⟩ :=
  accepted_of_selected 12 302919 ⟨1068304, by decide⟩ ⟨12, 2, 0, 1068304, 302919, 2645, 65536⟩
    (by decide) selected_cut_39369

theorem unmarked_context_11_75729_1068305 : frontier 10 ⟨1068305, by decide⟩
    (prefixCache 11 75729) (prefixPartial 11 75729) = false := by
  decide +kernel

theorem node_context_11_75729_1068305 : EJMOriginalGlobalDAGData.nodes 10 ⟨1068305, by decide⟩ =
    .split (coordinate 11) (![⟨1068166, by decide⟩,⟨1068219, by decide⟩,⟨1068262, by decide⟩,⟨1068304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75729_1068305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75729 ⟨1068305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75729
    ⟨1068305, by decide⟩ (by decide) (![⟨1068166, by decide⟩,⟨1068219, by decide⟩,⟨1068262, by decide⟩,⟨1068304, by decide⟩]) unmarked_context_11_75729_1068305 node_context_11_75729_1068305
  intro a
  fin_cases a
  · exact context_12_302916_1068166
  · exact context_12_302917_1068219
  · exact context_12_302918_1068262
  · exact context_12_302919_1068304

theorem selected_cut_39370 : selected 9 ⟨1068361, by decide⟩
    (prefixPartial 12 302920) = some ⟨12, 2, 0, 1068361, 302920, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_302920_1068361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302920 ⟨1068361, by decide⟩ :=
  accepted_of_selected 12 302920 ⟨1068361, by decide⟩ ⟨12, 2, 0, 1068361, 302920, 3245, 65536⟩
    (by decide) selected_cut_39370

theorem selected_cut_39371 : selected 9 ⟨1068402, by decide⟩
    (prefixPartial 12 302921) = some ⟨12, 2, 0, 1068402, 302921, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_302921_1068402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302921 ⟨1068402, by decide⟩ :=
  accepted_of_selected 12 302921 ⟨1068402, by decide⟩ ⟨12, 2, 0, 1068402, 302921, 3021, 65536⟩
    (by decide) selected_cut_39371

theorem selected_cut_39372 : selected 9 ⟨1068445, by decide⟩
    (prefixPartial 12 302922) = some ⟨12, 2, 0, 1068445, 302922, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_302922_1068445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302922 ⟨1068445, by decide⟩ :=
  accepted_of_selected 12 302922 ⟨1068445, by decide⟩ ⟨12, 2, 0, 1068445, 302922, 2893, 65536⟩
    (by decide) selected_cut_39372

theorem selected_cut_39373 : selected 9 ⟨1068487, by decide⟩
    (prefixPartial 12 302923) = some ⟨12, 2, 0, 1068487, 302923, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_302923_1068487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302923 ⟨1068487, by decide⟩ :=
  accepted_of_selected 12 302923 ⟨1068487, by decide⟩ ⟨12, 2, 0, 1068487, 302923, 2877, 65536⟩
    (by decide) selected_cut_39373

theorem unmarked_context_11_75730_1068488 : frontier 10 ⟨1068488, by decide⟩
    (prefixCache 11 75730) (prefixPartial 11 75730) = false := by
  decide +kernel

theorem node_context_11_75730_1068488 : EJMOriginalGlobalDAGData.nodes 10 ⟨1068488, by decide⟩ =
    .split (coordinate 11) (![⟨1068361, by decide⟩,⟨1068402, by decide⟩,⟨1068445, by decide⟩,⟨1068487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75730_1068488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75730 ⟨1068488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75730
    ⟨1068488, by decide⟩ (by decide) (![⟨1068361, by decide⟩,⟨1068402, by decide⟩,⟨1068445, by decide⟩,⟨1068487, by decide⟩]) unmarked_context_11_75730_1068488 node_context_11_75730_1068488
  intro a
  fin_cases a
  · exact context_12_302920_1068361
  · exact context_12_302921_1068402
  · exact context_12_302922_1068445
  · exact context_12_302923_1068487

theorem selected_cut_39374 : selected 9 ⟨1068538, by decide⟩
    (prefixPartial 12 302924) = some ⟨12, 2, 0, 1068538, 302924, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_302924_1068538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302924 ⟨1068538, by decide⟩ :=
  accepted_of_selected 12 302924 ⟨1068538, by decide⟩ ⟨12, 2, 0, 1068538, 302924, 2849, 65536⟩
    (by decide) selected_cut_39374

theorem selected_cut_39375 : selected 9 ⟨1068587, by decide⟩
    (prefixPartial 12 302925) = some ⟨12, 2, 0, 1068587, 302925, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_302925_1068587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302925 ⟨1068587, by decide⟩ :=
  accepted_of_selected 12 302925 ⟨1068587, by decide⟩ ⟨12, 2, 0, 1068587, 302925, 2701, 65536⟩
    (by decide) selected_cut_39375

theorem selected_cut_39376 : selected 9 ⟨1068630, by decide⟩
    (prefixPartial 12 302926) = some ⟨12, 2, 0, 1068630, 302926, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_302926_1068630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302926 ⟨1068630, by decide⟩ :=
  accepted_of_selected 12 302926 ⟨1068630, by decide⟩ ⟨12, 2, 0, 1068630, 302926, 2633, 65536⟩
    (by decide) selected_cut_39376

theorem selected_cut_39377 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 302927) = some ⟨12, 1, 0, 903806, 302927, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302927_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302927 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 302927 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 302927, 1, 65536⟩
    (by decide) selected_cut_39377

theorem unmarked_context_11_75731_1068631 : frontier 10 ⟨1068631, by decide⟩
    (prefixCache 11 75731) (prefixPartial 11 75731) = false := by
  decide +kernel

theorem node_context_11_75731_1068631 : EJMOriginalGlobalDAGData.nodes 10 ⟨1068631, by decide⟩ =
    .split (coordinate 11) (![⟨1068538, by decide⟩,⟨1068587, by decide⟩,⟨1068630, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75731_1068631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75731 ⟨1068631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75731
    ⟨1068631, by decide⟩ (by decide) (![⟨1068538, by decide⟩,⟨1068587, by decide⟩,⟨1068630, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75731_1068631 node_context_11_75731_1068631
  intro a
  fin_cases a
  · exact context_12_302924_1068538
  · exact context_12_302925_1068587
  · exact context_12_302926_1068630
  · exact context_12_302927_903806

theorem unmarked_context_10_18932_1068632 : frontier 11 ⟨1068632, by decide⟩
    (prefixCache 10 18932) (prefixPartial 10 18932) = false := by
  decide +kernel

theorem node_context_10_18932_1068632 : EJMOriginalGlobalDAGData.nodes 11 ⟨1068632, by decide⟩ =
    .split (coordinate 10) (![⟨1068110, by decide⟩,⟨1068305, by decide⟩,⟨1068488, by decide⟩,⟨1068631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18932_1068632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18932 ⟨1068632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18932
    ⟨1068632, by decide⟩ (by decide) (![⟨1068110, by decide⟩,⟨1068305, by decide⟩,⟨1068488, by decide⟩,⟨1068631, by decide⟩]) unmarked_context_10_18932_1068632 node_context_10_18932_1068632
  intro a
  fin_cases a
  · exact context_11_75728_1068110
  · exact context_11_75729_1068305
  · exact context_11_75730_1068488
  · exact context_11_75731_1068631

theorem selected_cut_39378 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18933) = some ⟨10, 1, 0, 893098, 18933, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18933_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18933 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18933 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18933, 1, 1048576⟩
    (by decide) selected_cut_39378

theorem selected_cut_39379 : selected 9 ⟨1068657, by decide⟩
    (prefixPartial 12 302944) = some ⟨12, 2, 0, 1068657, 302944, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_302944_1068657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302944 ⟨1068657, by decide⟩ :=
  accepted_of_selected 12 302944 ⟨1068657, by decide⟩ ⟨12, 2, 0, 1068657, 302944, 2197, 65536⟩
    (by decide) selected_cut_39379

theorem selected_cut_39380 : selected 9 ⟨1068692, by decide⟩
    (prefixPartial 12 302945) = some ⟨12, 2, 0, 1068692, 302945, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_302945_1068692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302945 ⟨1068692, by decide⟩ :=
  accepted_of_selected 12 302945 ⟨1068692, by decide⟩ ⟨12, 2, 0, 1068692, 302945, 2353, 65536⟩
    (by decide) selected_cut_39380

theorem selected_cut_39381 : selected 9 ⟨1068720, by decide⟩
    (prefixPartial 12 302946) = some ⟨12, 2, 0, 1068720, 302946, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_302946_1068720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302946 ⟨1068720, by decide⟩ :=
  accepted_of_selected 12 302946 ⟨1068720, by decide⟩ ⟨12, 2, 0, 1068720, 302946, 2177, 65536⟩
    (by decide) selected_cut_39381

theorem selected_cut_39382 : selected 9 ⟨1068745, by decide⟩
    (prefixPartial 12 302947) = some ⟨12, 2, 0, 1068745, 302947, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_302947_1068745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302947 ⟨1068745, by decide⟩ :=
  accepted_of_selected 12 302947 ⟨1068745, by decide⟩ ⟨12, 2, 0, 1068745, 302947, 2041, 65536⟩
    (by decide) selected_cut_39382

theorem unmarked_context_11_75736_1068746 : frontier 10 ⟨1068746, by decide⟩
    (prefixCache 11 75736) (prefixPartial 11 75736) = false := by
  decide +kernel

theorem node_context_11_75736_1068746 : EJMOriginalGlobalDAGData.nodes 10 ⟨1068746, by decide⟩ =
    .split (coordinate 11) (![⟨1068657, by decide⟩,⟨1068692, by decide⟩,⟨1068720, by decide⟩,⟨1068745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75736_1068746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75736 ⟨1068746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75736
    ⟨1068746, by decide⟩ (by decide) (![⟨1068657, by decide⟩,⟨1068692, by decide⟩,⟨1068720, by decide⟩,⟨1068745, by decide⟩]) unmarked_context_11_75736_1068746 node_context_11_75736_1068746
  intro a
  fin_cases a
  · exact context_12_302944_1068657
  · exact context_12_302945_1068692
  · exact context_12_302946_1068720
  · exact context_12_302947_1068745

theorem selected_cut_39383 : selected 9 ⟨1068774, by decide⟩
    (prefixPartial 12 302948) = some ⟨12, 2, 0, 1068774, 302948, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_302948_1068774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302948 ⟨1068774, by decide⟩ :=
  accepted_of_selected 12 302948 ⟨1068774, by decide⟩ ⟨12, 2, 0, 1068774, 302948, 2021, 65536⟩
    (by decide) selected_cut_39383

theorem selected_cut_39384 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 302949) = some ⟨12, 1, 0, 1025817, 302949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302949_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302949 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 302949 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 302949, 1, 65536⟩
    (by decide) selected_cut_39384

theorem selected_cut_39385 : selected 9 ⟨1068806, by decide⟩
    (prefixPartial 12 302950) = some ⟨12, 2, 0, 1068806, 302950, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_302950_1068806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302950 ⟨1068806, by decide⟩ :=
  accepted_of_selected 12 302950 ⟨1068806, by decide⟩ ⟨12, 2, 0, 1068806, 302950, 1981, 65536⟩
    (by decide) selected_cut_39385

theorem selected_cut_39386 : selected 9 ⟨1068830, by decide⟩
    (prefixPartial 12 302951) = some ⟨12, 2, 0, 1068830, 302951, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_302951_1068830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302951 ⟨1068830, by decide⟩ :=
  accepted_of_selected 12 302951 ⟨1068830, by decide⟩ ⟨12, 2, 0, 1068830, 302951, 2021, 65536⟩
    (by decide) selected_cut_39386

theorem unmarked_context_11_75737_1068831 : frontier 10 ⟨1068831, by decide⟩
    (prefixCache 11 75737) (prefixPartial 11 75737) = false := by
  decide +kernel

theorem node_context_11_75737_1068831 : EJMOriginalGlobalDAGData.nodes 10 ⟨1068831, by decide⟩ =
    .split (coordinate 11) (![⟨1068774, by decide⟩,⟨1025817, by decide⟩,⟨1068806, by decide⟩,⟨1068830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75737_1068831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75737 ⟨1068831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75737
    ⟨1068831, by decide⟩ (by decide) (![⟨1068774, by decide⟩,⟨1025817, by decide⟩,⟨1068806, by decide⟩,⟨1068830, by decide⟩]) unmarked_context_11_75737_1068831 node_context_11_75737_1068831
  intro a
  fin_cases a
  · exact context_12_302948_1068774
  · exact context_12_302949_1025817
  · exact context_12_302950_1068806
  · exact context_12_302951_1068830

theorem selected_cut_39387 : selected 9 ⟨1068860, by decide⟩
    (prefixPartial 12 302952) = some ⟨12, 2, 0, 1068860, 302952, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_302952_1068860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302952 ⟨1068860, by decide⟩ :=
  accepted_of_selected 12 302952 ⟨1068860, by decide⟩ ⟨12, 2, 0, 1068860, 302952, 2269, 65536⟩
    (by decide) selected_cut_39387

theorem selected_cut_39388 : selected 9 ⟨1068897, by decide⟩
    (prefixPartial 12 302953) = some ⟨12, 2, 0, 1068897, 302953, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_302953_1068897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302953 ⟨1068897, by decide⟩ :=
  accepted_of_selected 12 302953 ⟨1068897, by decide⟩ ⟨12, 2, 0, 1068897, 302953, 2457, 65536⟩
    (by decide) selected_cut_39388

theorem selected_cut_39389 : selected 9 ⟨661672, by decide⟩
    (prefixPartial 12 302954) = some ⟨12, 1, 0, 661672, 302954, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302954_661672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302954 ⟨661672, by decide⟩ :=
  accepted_of_selected 12 302954 ⟨661672, by decide⟩ ⟨12, 1, 0, 661672, 302954, 1, 65536⟩
    (by decide) selected_cut_39389

theorem selected_cut_39390 : selected 9 ⟨1068934, by decide⟩
    (prefixPartial 12 302955) = some ⟨12, 2, 0, 1068934, 302955, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_302955_1068934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302955 ⟨1068934, by decide⟩ :=
  accepted_of_selected 12 302955 ⟨1068934, by decide⟩ ⟨12, 2, 0, 1068934, 302955, 2261, 65536⟩
    (by decide) selected_cut_39390

theorem unmarked_context_11_75738_1068935 : frontier 10 ⟨1068935, by decide⟩
    (prefixCache 11 75738) (prefixPartial 11 75738) = false := by
  decide +kernel

theorem node_context_11_75738_1068935 : EJMOriginalGlobalDAGData.nodes 10 ⟨1068935, by decide⟩ =
    .split (coordinate 11) (![⟨1068860, by decide⟩,⟨1068897, by decide⟩,⟨661672, by decide⟩,⟨1068934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75738_1068935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75738 ⟨1068935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75738
    ⟨1068935, by decide⟩ (by decide) (![⟨1068860, by decide⟩,⟨1068897, by decide⟩,⟨661672, by decide⟩,⟨1068934, by decide⟩]) unmarked_context_11_75738_1068935 node_context_11_75738_1068935
  intro a
  fin_cases a
  · exact context_12_302952_1068860
  · exact context_12_302953_1068897
  · exact context_12_302954_661672
  · exact context_12_302955_1068934

theorem selected_cut_39391 : selected 9 ⟨1068964, by decide⟩
    (prefixPartial 12 302956) = some ⟨12, 2, 0, 1068964, 302956, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_302956_1068964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302956 ⟨1068964, by decide⟩ :=
  accepted_of_selected 12 302956 ⟨1068964, by decide⟩ ⟨12, 2, 0, 1068964, 302956, 1773, 65536⟩
    (by decide) selected_cut_39391

theorem selected_cut_39392 : selected 9 ⟨1069000, by decide⟩
    (prefixPartial 12 302957) = some ⟨12, 2, 0, 1069000, 302957, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_302957_1069000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302957 ⟨1069000, by decide⟩ :=
  accepted_of_selected 12 302957 ⟨1069000, by decide⟩ ⟨12, 2, 0, 1069000, 302957, 2117, 65536⟩
    (by decide) selected_cut_39392

theorem selected_cut_39393 : selected 9 ⟨1069033, by decide⟩
    (prefixPartial 12 302958) = some ⟨12, 2, 0, 1069033, 302958, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_302958_1069033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302958 ⟨1069033, by decide⟩ :=
  accepted_of_selected 12 302958 ⟨1069033, by decide⟩ ⟨12, 2, 0, 1069033, 302958, 1941, 65536⟩
    (by decide) selected_cut_39393

theorem selected_cut_39394 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 302959) = some ⟨12, 1, 0, 903806, 302959, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302959_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302959 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 302959 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 302959, 1, 65536⟩
    (by decide) selected_cut_39394

theorem unmarked_context_11_75739_1069034 : frontier 10 ⟨1069034, by decide⟩
    (prefixCache 11 75739) (prefixPartial 11 75739) = false := by
  decide +kernel

theorem node_context_11_75739_1069034 : EJMOriginalGlobalDAGData.nodes 10 ⟨1069034, by decide⟩ =
    .split (coordinate 11) (![⟨1068964, by decide⟩,⟨1069000, by decide⟩,⟨1069033, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75739_1069034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75739 ⟨1069034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75739
    ⟨1069034, by decide⟩ (by decide) (![⟨1068964, by decide⟩,⟨1069000, by decide⟩,⟨1069033, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_75739_1069034 node_context_11_75739_1069034
  intro a
  fin_cases a
  · exact context_12_302956_1068964
  · exact context_12_302957_1069000
  · exact context_12_302958_1069033
  · exact context_12_302959_903806

theorem unmarked_context_10_18934_1069035 : frontier 11 ⟨1069035, by decide⟩
    (prefixCache 10 18934) (prefixPartial 10 18934) = false := by
  decide +kernel

theorem node_context_10_18934_1069035 : EJMOriginalGlobalDAGData.nodes 11 ⟨1069035, by decide⟩ =
    .split (coordinate 10) (![⟨1068746, by decide⟩,⟨1068831, by decide⟩,⟨1068935, by decide⟩,⟨1069034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18934_1069035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18934 ⟨1069035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18934
    ⟨1069035, by decide⟩ (by decide) (![⟨1068746, by decide⟩,⟨1068831, by decide⟩,⟨1068935, by decide⟩,⟨1069034, by decide⟩]) unmarked_context_10_18934_1069035 node_context_10_18934_1069035
  intro a
  fin_cases a
  · exact context_11_75736_1068746
  · exact context_11_75737_1068831
  · exact context_11_75738_1068935
  · exact context_11_75739_1069034

theorem selected_cut_39395 : selected 9 ⟨1069058, by decide⟩
    (prefixPartial 12 302960) = some ⟨12, 2, 0, 1069058, 302960, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_302960_1069058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302960 ⟨1069058, by decide⟩ :=
  accepted_of_selected 12 302960 ⟨1069058, by decide⟩ ⟨12, 2, 0, 1069058, 302960, 1677, 65536⟩
    (by decide) selected_cut_39395

theorem selected_cut_39396 : selected 9 ⟨1069086, by decide⟩
    (prefixPartial 12 302961) = some ⟨12, 2, 0, 1069086, 302961, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_302961_1069086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302961 ⟨1069086, by decide⟩ :=
  accepted_of_selected 12 302961 ⟨1069086, by decide⟩ ⟨12, 2, 0, 1069086, 302961, 1801, 65536⟩
    (by decide) selected_cut_39396

theorem selected_cut_39397 : selected 9 ⟨1069106, by decide⟩
    (prefixPartial 12 302962) = some ⟨12, 2, 0, 1069106, 302962, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_302962_1069106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302962 ⟨1069106, by decide⟩ :=
  accepted_of_selected 12 302962 ⟨1069106, by decide⟩ ⟨12, 2, 0, 1069106, 302962, 1693, 65536⟩
    (by decide) selected_cut_39397

theorem selected_cut_39398 : selected 9 ⟨1069122, by decide⟩
    (prefixPartial 12 302963) = some ⟨12, 2, 0, 1069122, 302963, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_302963_1069122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302963 ⟨1069122, by decide⟩ :=
  accepted_of_selected 12 302963 ⟨1069122, by decide⟩ ⟨12, 2, 0, 1069122, 302963, 1465, 65536⟩
    (by decide) selected_cut_39398

theorem unmarked_context_11_75740_1069123 : frontier 10 ⟨1069123, by decide⟩
    (prefixCache 11 75740) (prefixPartial 11 75740) = false := by
  decide +kernel

theorem node_context_11_75740_1069123 : EJMOriginalGlobalDAGData.nodes 10 ⟨1069123, by decide⟩ =
    .split (coordinate 11) (![⟨1069058, by decide⟩,⟨1069086, by decide⟩,⟨1069106, by decide⟩,⟨1069122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75740_1069123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75740 ⟨1069123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75740
    ⟨1069123, by decide⟩ (by decide) (![⟨1069058, by decide⟩,⟨1069086, by decide⟩,⟨1069106, by decide⟩,⟨1069122, by decide⟩]) unmarked_context_11_75740_1069123 node_context_11_75740_1069123
  intro a
  fin_cases a
  · exact context_12_302960_1069058
  · exact context_12_302961_1069086
  · exact context_12_302962_1069106
  · exact context_12_302963_1069122

theorem selected_cut_39399 : selected 9 ⟨1069148, by decide⟩
    (prefixPartial 12 302964) = some ⟨12, 2, 0, 1069148, 302964, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_302964_1069148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302964 ⟨1069148, by decide⟩ :=
  accepted_of_selected 12 302964 ⟨1069148, by decide⟩ ⟨12, 2, 0, 1069148, 302964, 1757, 65536⟩
    (by decide) selected_cut_39399

theorem selected_cut_39400 : selected 9 ⟨1026250, by decide⟩
    (prefixPartial 12 302965) = some ⟨12, 1, 0, 1026250, 302965, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302965_1026250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302965 ⟨1026250, by decide⟩ :=
  accepted_of_selected 12 302965 ⟨1026250, by decide⟩ ⟨12, 1, 0, 1026250, 302965, 1, 65536⟩
    (by decide) selected_cut_39400

theorem selected_cut_39401 : selected 9 ⟨1069173, by decide⟩
    (prefixPartial 12 302966) = some ⟨12, 2, 0, 1069173, 302966, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_302966_1069173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302966 ⟨1069173, by decide⟩ :=
  accepted_of_selected 12 302966 ⟨1069173, by decide⟩ ⟨12, 2, 0, 1069173, 302966, 1589, 65536⟩
    (by decide) selected_cut_39401

theorem selected_cut_39402 : selected 9 ⟨1069204, by decide⟩
    (prefixPartial 12 302967) = some ⟨12, 2, 0, 1069204, 302967, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_302967_1069204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302967 ⟨1069204, by decide⟩ :=
  accepted_of_selected 12 302967 ⟨1069204, by decide⟩ ⟨12, 2, 0, 1069204, 302967, 1509, 65536⟩
    (by decide) selected_cut_39402

theorem unmarked_context_11_75741_1069205 : frontier 10 ⟨1069205, by decide⟩
    (prefixCache 11 75741) (prefixPartial 11 75741) = false := by
  decide +kernel

theorem node_context_11_75741_1069205 : EJMOriginalGlobalDAGData.nodes 10 ⟨1069205, by decide⟩ =
    .split (coordinate 11) (![⟨1069148, by decide⟩,⟨1026250, by decide⟩,⟨1069173, by decide⟩,⟨1069204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75741_1069205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75741 ⟨1069205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75741
    ⟨1069205, by decide⟩ (by decide) (![⟨1069148, by decide⟩,⟨1026250, by decide⟩,⟨1069173, by decide⟩,⟨1069204, by decide⟩]) unmarked_context_11_75741_1069205 node_context_11_75741_1069205
  intro a
  fin_cases a
  · exact context_12_302964_1069148
  · exact context_12_302965_1026250
  · exact context_12_302966_1069173
  · exact context_12_302967_1069204

theorem selected_cut_39403 : selected 9 ⟨1069240, by decide⟩
    (prefixPartial 12 302968) = some ⟨12, 2, 0, 1069240, 302968, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_302968_1069240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302968 ⟨1069240, by decide⟩ :=
  accepted_of_selected 12 302968 ⟨1069240, by decide⟩ ⟨12, 2, 0, 1069240, 302968, 1849, 65536⟩
    (by decide) selected_cut_39403

theorem selected_cut_39404 : selected 9 ⟨1069271, by decide⟩
    (prefixPartial 12 302969) = some ⟨12, 2, 0, 1069271, 302969, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_302969_1069271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302969 ⟨1069271, by decide⟩ :=
  accepted_of_selected 12 302969 ⟨1069271, by decide⟩ ⟨12, 2, 0, 1069271, 302969, 1757, 65536⟩
    (by decide) selected_cut_39404

theorem selected_cut_39405 : selected 9 ⟨1069298, by decide⟩
    (prefixPartial 12 302970) = some ⟨12, 2, 0, 1069298, 302970, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_302970_1069298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302970 ⟨1069298, by decide⟩ :=
  accepted_of_selected 12 302970 ⟨1069298, by decide⟩ ⟨12, 2, 0, 1069298, 302970, 1605, 65536⟩
    (by decide) selected_cut_39405

theorem selected_cut_39406 : selected 9 ⟨1069327, by decide⟩
    (prefixPartial 12 302971) = some ⟨12, 2, 0, 1069327, 302971, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_302971_1069327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302971 ⟨1069327, by decide⟩ :=
  accepted_of_selected 12 302971 ⟨1069327, by decide⟩ ⟨12, 2, 0, 1069327, 302971, 1465, 65536⟩
    (by decide) selected_cut_39406

theorem unmarked_context_11_75742_1069328 : frontier 10 ⟨1069328, by decide⟩
    (prefixCache 11 75742) (prefixPartial 11 75742) = false := by
  decide +kernel

theorem node_context_11_75742_1069328 : EJMOriginalGlobalDAGData.nodes 10 ⟨1069328, by decide⟩ =
    .split (coordinate 11) (![⟨1069240, by decide⟩,⟨1069271, by decide⟩,⟨1069298, by decide⟩,⟨1069327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75742_1069328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75742 ⟨1069328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75742
    ⟨1069328, by decide⟩ (by decide) (![⟨1069240, by decide⟩,⟨1069271, by decide⟩,⟨1069298, by decide⟩,⟨1069327, by decide⟩]) unmarked_context_11_75742_1069328 node_context_11_75742_1069328
  intro a
  fin_cases a
  · exact context_12_302968_1069240
  · exact context_12_302969_1069271
  · exact context_12_302970_1069298
  · exact context_12_302971_1069327

theorem selected_cut_39407 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75743) = some ⟨11, 1, 0, 977886, 75743, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75743_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75743 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75743 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75743, 1, 262144⟩
    (by decide) selected_cut_39407

theorem unmarked_context_10_18935_1069329 : frontier 11 ⟨1069329, by decide⟩
    (prefixCache 10 18935) (prefixPartial 10 18935) = false := by
  decide +kernel

theorem node_context_10_18935_1069329 : EJMOriginalGlobalDAGData.nodes 11 ⟨1069329, by decide⟩ =
    .split (coordinate 10) (![⟨1069123, by decide⟩,⟨1069205, by decide⟩,⟨1069328, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18935_1069329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18935 ⟨1069329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18935
    ⟨1069329, by decide⟩ (by decide) (![⟨1069123, by decide⟩,⟨1069205, by decide⟩,⟨1069328, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18935_1069329 node_context_10_18935_1069329
  intro a
  fin_cases a
  · exact context_11_75740_1069123
  · exact context_11_75741_1069205
  · exact context_11_75742_1069328
  · exact context_11_75743_977886

theorem unmarked_context_9_4733_1069330 : frontier 12 ⟨1069330, by decide⟩
    (prefixCache 9 4733) (prefixPartial 9 4733) = false := by
  decide +kernel

theorem node_context_9_4733_1069330 : EJMOriginalGlobalDAGData.nodes 12 ⟨1069330, by decide⟩ =
    .split (coordinate 9) (![⟨1068632, by decide⟩,⟨893098, by decide⟩,⟨1069035, by decide⟩,⟨1069329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4733_1069330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4733 ⟨1069330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4733
    ⟨1069330, by decide⟩ (by decide) (![⟨1068632, by decide⟩,⟨893098, by decide⟩,⟨1069035, by decide⟩,⟨1069329, by decide⟩]) unmarked_context_9_4733_1069330 node_context_9_4733_1069330
  intro a
  fin_cases a
  · exact context_10_18932_1068632
  · exact context_10_18933_893098
  · exact context_10_18934_1069035
  · exact context_10_18935_1069329

theorem selected_cut_39408 : selected 10 ⟨1069374, by decide⟩
    (prefixPartial 11 75744) = some ⟨11, 2, 0, 1069374, 75744, 2753, 262144⟩ := by
  decide +kernel

theorem context_11_75744_1069374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75744 ⟨1069374, by decide⟩ :=
  accepted_of_selected 11 75744 ⟨1069374, by decide⟩ ⟨11, 2, 0, 1069374, 75744, 2753, 262144⟩
    (by decide) selected_cut_39408

theorem selected_cut_39409 : selected 9 ⟨1069405, by decide⟩
    (prefixPartial 12 302980) = some ⟨12, 2, 0, 1069405, 302980, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_302980_1069405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302980 ⟨1069405, by decide⟩ :=
  accepted_of_selected 12 302980 ⟨1069405, by decide⟩ ⟨12, 2, 0, 1069405, 302980, 1485, 65536⟩
    (by decide) selected_cut_39409

theorem selected_cut_39410 : selected 9 ⟨1069428, by decide⟩
    (prefixPartial 12 302981) = some ⟨12, 2, 0, 1069428, 302981, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_302981_1069428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302981 ⟨1069428, by decide⟩ :=
  accepted_of_selected 12 302981 ⟨1069428, by decide⟩ ⟨12, 2, 0, 1069428, 302981, 1369, 65536⟩
    (by decide) selected_cut_39410

theorem selected_cut_39411 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302982) = some ⟨12, 1, 0, 984676, 302982, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302982_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302982 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302982 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302982, 1, 65536⟩
    (by decide) selected_cut_39411

theorem selected_cut_39412 : selected 9 ⟨1069446, by decide⟩
    (prefixPartial 12 302983) = some ⟨12, 2, 0, 1069446, 302983, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_302983_1069446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302983 ⟨1069446, by decide⟩ :=
  accepted_of_selected 12 302983 ⟨1069446, by decide⟩ ⟨12, 2, 0, 1069446, 302983, 1325, 65536⟩
    (by decide) selected_cut_39412

theorem unmarked_context_11_75745_1069447 : frontier 10 ⟨1069447, by decide⟩
    (prefixCache 11 75745) (prefixPartial 11 75745) = false := by
  decide +kernel

theorem node_context_11_75745_1069447 : EJMOriginalGlobalDAGData.nodes 10 ⟨1069447, by decide⟩ =
    .split (coordinate 11) (![⟨1069405, by decide⟩,⟨1069428, by decide⟩,⟨984676, by decide⟩,⟨1069446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75745_1069447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75745 ⟨1069447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75745
    ⟨1069447, by decide⟩ (by decide) (![⟨1069405, by decide⟩,⟨1069428, by decide⟩,⟨984676, by decide⟩,⟨1069446, by decide⟩]) unmarked_context_11_75745_1069447 node_context_11_75745_1069447
  intro a
  fin_cases a
  · exact context_12_302980_1069405
  · exact context_12_302981_1069428
  · exact context_12_302982_984676
  · exact context_12_302983_1069446

theorem selected_cut_39413 : selected 9 ⟨1069493, by decide⟩
    (prefixPartial 12 302984) = some ⟨12, 2, 0, 1069493, 302984, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_302984_1069493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302984 ⟨1069493, by decide⟩ :=
  accepted_of_selected 12 302984 ⟨1069493, by decide⟩ ⟨12, 2, 0, 1069493, 302984, 1665, 65536⟩
    (by decide) selected_cut_39413

theorem selected_cut_39414 : selected 9 ⟨1069528, by decide⟩
    (prefixPartial 12 302985) = some ⟨12, 2, 0, 1069528, 302985, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_302985_1069528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302985 ⟨1069528, by decide⟩ :=
  accepted_of_selected 12 302985 ⟨1069528, by decide⟩ ⟨12, 2, 0, 1069528, 302985, 1433, 65536⟩
    (by decide) selected_cut_39414

theorem selected_cut_39415 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302986) = some ⟨12, 1, 0, 984676, 302986, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302986_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302986 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302986 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302986, 1, 65536⟩
    (by decide) selected_cut_39415

theorem selected_cut_39416 : selected 9 ⟨1069551, by decide⟩
    (prefixPartial 12 302987) = some ⟨12, 2, 0, 1069551, 302987, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_302987_1069551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302987 ⟨1069551, by decide⟩ :=
  accepted_of_selected 12 302987 ⟨1069551, by decide⟩ ⟨12, 2, 0, 1069551, 302987, 1469, 65536⟩
    (by decide) selected_cut_39416

theorem unmarked_context_11_75746_1069552 : frontier 10 ⟨1069552, by decide⟩
    (prefixCache 11 75746) (prefixPartial 11 75746) = false := by
  decide +kernel

theorem node_context_11_75746_1069552 : EJMOriginalGlobalDAGData.nodes 10 ⟨1069552, by decide⟩ =
    .split (coordinate 11) (![⟨1069493, by decide⟩,⟨1069528, by decide⟩,⟨984676, by decide⟩,⟨1069551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75746_1069552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75746 ⟨1069552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75746
    ⟨1069552, by decide⟩ (by decide) (![⟨1069493, by decide⟩,⟨1069528, by decide⟩,⟨984676, by decide⟩,⟨1069551, by decide⟩]) unmarked_context_11_75746_1069552 node_context_11_75746_1069552
  intro a
  fin_cases a
  · exact context_12_302984_1069493
  · exact context_12_302985_1069528
  · exact context_12_302986_984676
  · exact context_12_302987_1069551

theorem selected_cut_39417 : selected 10 ⟨1069593, by decide⟩
    (prefixPartial 11 75747) = some ⟨11, 2, 0, 1069593, 75747, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_75747_1069593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75747 ⟨1069593, by decide⟩ :=
  accepted_of_selected 11 75747 ⟨1069593, by decide⟩ ⟨11, 2, 0, 1069593, 75747, 2613, 262144⟩
    (by decide) selected_cut_39417

theorem unmarked_context_10_18936_1069594 : frontier 11 ⟨1069594, by decide⟩
    (prefixCache 10 18936) (prefixPartial 10 18936) = false := by
  decide +kernel

theorem node_context_10_18936_1069594 : EJMOriginalGlobalDAGData.nodes 11 ⟨1069594, by decide⟩ =
    .split (coordinate 10) (![⟨1069374, by decide⟩,⟨1069447, by decide⟩,⟨1069552, by decide⟩,⟨1069593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18936_1069594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18936 ⟨1069594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18936
    ⟨1069594, by decide⟩ (by decide) (![⟨1069374, by decide⟩,⟨1069447, by decide⟩,⟨1069552, by decide⟩,⟨1069593, by decide⟩]) unmarked_context_10_18936_1069594 node_context_10_18936_1069594
  intro a
  fin_cases a
  · exact context_11_75744_1069374
  · exact context_11_75745_1069447
  · exact context_11_75746_1069552
  · exact context_11_75747_1069593

theorem selected_cut_39418 : selected 10 ⟨1069638, by decide⟩
    (prefixPartial 11 75748) = some ⟨11, 2, 0, 1069638, 75748, 3121, 262144⟩ := by
  decide +kernel

theorem context_11_75748_1069638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75748 ⟨1069638, by decide⟩ :=
  accepted_of_selected 11 75748 ⟨1069638, by decide⟩ ⟨11, 2, 0, 1069638, 75748, 3121, 262144⟩
    (by decide) selected_cut_39418

theorem selected_cut_39419 : selected 10 ⟨1069663, by decide⟩
    (prefixPartial 11 75749) = some ⟨11, 2, 0, 1069663, 75749, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_75749_1069663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75749 ⟨1069663, by decide⟩ :=
  accepted_of_selected 11 75749 ⟨1069663, by decide⟩ ⟨11, 2, 0, 1069663, 75749, 1773, 262144⟩
    (by decide) selected_cut_39419

theorem selected_cut_39420 : selected 10 ⟨1069703, by decide⟩
    (prefixPartial 11 75750) = some ⟨11, 2, 0, 1069703, 75750, 3029, 262144⟩ := by
  decide +kernel

theorem context_11_75750_1069703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75750 ⟨1069703, by decide⟩ :=
  accepted_of_selected 11 75750 ⟨1069703, by decide⟩ ⟨11, 2, 0, 1069703, 75750, 3029, 262144⟩
    (by decide) selected_cut_39420

theorem selected_cut_39421 : selected 10 ⟨1069728, by decide⟩
    (prefixPartial 11 75751) = some ⟨11, 2, 0, 1069728, 75751, 1913, 262144⟩ := by
  decide +kernel

theorem context_11_75751_1069728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75751 ⟨1069728, by decide⟩ :=
  accepted_of_selected 11 75751 ⟨1069728, by decide⟩ ⟨11, 2, 0, 1069728, 75751, 1913, 262144⟩
    (by decide) selected_cut_39421

theorem unmarked_context_10_18937_1069729 : frontier 11 ⟨1069729, by decide⟩
    (prefixCache 10 18937) (prefixPartial 10 18937) = false := by
  decide +kernel

theorem node_context_10_18937_1069729 : EJMOriginalGlobalDAGData.nodes 11 ⟨1069729, by decide⟩ =
    .split (coordinate 10) (![⟨1069638, by decide⟩,⟨1069663, by decide⟩,⟨1069703, by decide⟩,⟨1069728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18937_1069729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18937 ⟨1069729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18937
    ⟨1069729, by decide⟩ (by decide) (![⟨1069638, by decide⟩,⟨1069663, by decide⟩,⟨1069703, by decide⟩,⟨1069728, by decide⟩]) unmarked_context_10_18937_1069729 node_context_10_18937_1069729
  intro a
  fin_cases a
  · exact context_11_75748_1069638
  · exact context_11_75749_1069663
  · exact context_11_75750_1069703
  · exact context_11_75751_1069728

theorem selected_cut_39422 : selected 10 ⟨1069759, by decide⟩
    (prefixPartial 11 75752) = some ⟨11, 2, 0, 1069759, 75752, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_75752_1069759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75752 ⟨1069759, by decide⟩ :=
  accepted_of_selected 11 75752 ⟨1069759, by decide⟩ ⟨11, 2, 0, 1069759, 75752, 2425, 262144⟩
    (by decide) selected_cut_39422

theorem selected_cut_39423 : selected 10 ⟨1069787, by decide⟩
    (prefixPartial 11 75753) = some ⟨11, 2, 0, 1069787, 75753, 2169, 262144⟩ := by
  decide +kernel

theorem context_11_75753_1069787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75753 ⟨1069787, by decide⟩ :=
  accepted_of_selected 11 75753 ⟨1069787, by decide⟩ ⟨11, 2, 0, 1069787, 75753, 2169, 262144⟩
    (by decide) selected_cut_39423

theorem selected_cut_39424 : selected 10 ⟨1069794, by decide⟩
    (prefixPartial 11 75754) = some ⟨11, 2, 0, 1069794, 75754, 733, 262144⟩ := by
  decide +kernel

theorem context_11_75754_1069794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75754 ⟨1069794, by decide⟩ :=
  accepted_of_selected 11 75754 ⟨1069794, by decide⟩ ⟨11, 2, 0, 1069794, 75754, 733, 262144⟩
    (by decide) selected_cut_39424

theorem selected_cut_39425 : selected 10 ⟨1069814, by decide⟩
    (prefixPartial 11 75755) = some ⟨11, 2, 0, 1069814, 75755, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_75755_1069814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75755 ⟨1069814, by decide⟩ :=
  accepted_of_selected 11 75755 ⟨1069814, by decide⟩ ⟨11, 2, 0, 1069814, 75755, 1461, 262144⟩
    (by decide) selected_cut_39425

theorem unmarked_context_10_18938_1069815 : frontier 11 ⟨1069815, by decide⟩
    (prefixCache 10 18938) (prefixPartial 10 18938) = false := by
  decide +kernel

theorem node_context_10_18938_1069815 : EJMOriginalGlobalDAGData.nodes 11 ⟨1069815, by decide⟩ =
    .split (coordinate 10) (![⟨1069759, by decide⟩,⟨1069787, by decide⟩,⟨1069794, by decide⟩,⟨1069814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18938_1069815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18938 ⟨1069815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18938
    ⟨1069815, by decide⟩ (by decide) (![⟨1069759, by decide⟩,⟨1069787, by decide⟩,⟨1069794, by decide⟩,⟨1069814, by decide⟩]) unmarked_context_10_18938_1069815 node_context_10_18938_1069815
  intro a
  fin_cases a
  · exact context_11_75752_1069759
  · exact context_11_75753_1069787
  · exact context_11_75754_1069794
  · exact context_11_75755_1069814

theorem selected_cut_39426 : selected 10 ⟨1069845, by decide⟩
    (prefixPartial 11 75756) = some ⟨11, 2, 0, 1069845, 75756, 1893, 262144⟩ := by
  decide +kernel

theorem context_11_75756_1069845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75756 ⟨1069845, by decide⟩ :=
  accepted_of_selected 11 75756 ⟨1069845, by decide⟩ ⟨11, 2, 0, 1069845, 75756, 1893, 262144⟩
    (by decide) selected_cut_39426

theorem selected_cut_39427 : selected 10 ⟨1069865, by decide⟩
    (prefixPartial 11 75757) = some ⟨11, 2, 0, 1069865, 75757, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_75757_1069865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75757 ⟨1069865, by decide⟩ :=
  accepted_of_selected 11 75757 ⟨1069865, by decide⟩ ⟨11, 2, 0, 1069865, 75757, 1753, 262144⟩
    (by decide) selected_cut_39427

theorem selected_cut_39428 : selected 10 ⟨1069888, by decide⟩
    (prefixPartial 11 75758) = some ⟨11, 2, 0, 1069888, 75758, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_75758_1069888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75758 ⟨1069888, by decide⟩ :=
  accepted_of_selected 11 75758 ⟨1069888, by decide⟩ ⟨11, 2, 0, 1069888, 75758, 1753, 262144⟩
    (by decide) selected_cut_39428

theorem selected_cut_39429 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75759) = some ⟨11, 1, 0, 977886, 75759, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75759_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75759 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75759 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75759, 1, 262144⟩
    (by decide) selected_cut_39429

theorem unmarked_context_10_18939_1069889 : frontier 11 ⟨1069889, by decide⟩
    (prefixCache 10 18939) (prefixPartial 10 18939) = false := by
  decide +kernel

theorem node_context_10_18939_1069889 : EJMOriginalGlobalDAGData.nodes 11 ⟨1069889, by decide⟩ =
    .split (coordinate 10) (![⟨1069845, by decide⟩,⟨1069865, by decide⟩,⟨1069888, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18939_1069889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18939 ⟨1069889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18939
    ⟨1069889, by decide⟩ (by decide) (![⟨1069845, by decide⟩,⟨1069865, by decide⟩,⟨1069888, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18939_1069889 node_context_10_18939_1069889
  intro a
  fin_cases a
  · exact context_11_75756_1069845
  · exact context_11_75757_1069865
  · exact context_11_75758_1069888
  · exact context_11_75759_977886

theorem unmarked_context_9_4734_1069890 : frontier 12 ⟨1069890, by decide⟩
    (prefixCache 9 4734) (prefixPartial 9 4734) = false := by
  decide +kernel

theorem node_context_9_4734_1069890 : EJMOriginalGlobalDAGData.nodes 12 ⟨1069890, by decide⟩ =
    .split (coordinate 9) (![⟨1069594, by decide⟩,⟨1069729, by decide⟩,⟨1069815, by decide⟩,⟨1069889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4734_1069890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4734 ⟨1069890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4734
    ⟨1069890, by decide⟩ (by decide) (![⟨1069594, by decide⟩,⟨1069729, by decide⟩,⟨1069815, by decide⟩,⟨1069889, by decide⟩]) unmarked_context_9_4734_1069890 node_context_9_4734_1069890
  intro a
  fin_cases a
  · exact context_10_18936_1069594
  · exact context_10_18937_1069729
  · exact context_10_18938_1069815
  · exact context_10_18939_1069889

theorem selected_cut_39430 : selected 10 ⟨1069907, by decide⟩
    (prefixPartial 11 75760) = some ⟨11, 2, 0, 1069907, 75760, 1329, 262144⟩ := by
  decide +kernel

theorem context_11_75760_1069907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75760 ⟨1069907, by decide⟩ :=
  accepted_of_selected 11 75760 ⟨1069907, by decide⟩ ⟨11, 2, 0, 1069907, 75760, 1329, 262144⟩
    (by decide) selected_cut_39430

theorem selected_cut_39431 : selected 10 ⟨1069933, by decide⟩
    (prefixPartial 11 75761) = some ⟨11, 2, 0, 1069933, 75761, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_75761_1069933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75761 ⟨1069933, by decide⟩ :=
  accepted_of_selected 11 75761 ⟨1069933, by decide⟩ ⟨11, 2, 0, 1069933, 75761, 1941, 262144⟩
    (by decide) selected_cut_39431

theorem selected_cut_39432 : selected 10 ⟨1069958, by decide⟩
    (prefixPartial 11 75762) = some ⟨11, 2, 0, 1069958, 75762, 1809, 262144⟩ := by
  decide +kernel

theorem context_11_75762_1069958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75762 ⟨1069958, by decide⟩ :=
  accepted_of_selected 11 75762 ⟨1069958, by decide⟩ ⟨11, 2, 0, 1069958, 75762, 1809, 262144⟩
    (by decide) selected_cut_39432

theorem selected_cut_39433 : selected 10 ⟨1069978, by decide⟩
    (prefixPartial 11 75763) = some ⟨11, 2, 0, 1069978, 75763, 1389, 262144⟩ := by
  decide +kernel

theorem context_11_75763_1069978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75763 ⟨1069978, by decide⟩ :=
  accepted_of_selected 11 75763 ⟨1069978, by decide⟩ ⟨11, 2, 0, 1069978, 75763, 1389, 262144⟩
    (by decide) selected_cut_39433

theorem unmarked_context_10_18940_1069979 : frontier 11 ⟨1069979, by decide⟩
    (prefixCache 10 18940) (prefixPartial 10 18940) = false := by
  decide +kernel

theorem node_context_10_18940_1069979 : EJMOriginalGlobalDAGData.nodes 11 ⟨1069979, by decide⟩ =
    .split (coordinate 10) (![⟨1069907, by decide⟩,⟨1069933, by decide⟩,⟨1069958, by decide⟩,⟨1069978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18940_1069979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18940 ⟨1069979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18940
    ⟨1069979, by decide⟩ (by decide) (![⟨1069907, by decide⟩,⟨1069933, by decide⟩,⟨1069958, by decide⟩,⟨1069978, by decide⟩]) unmarked_context_10_18940_1069979 node_context_10_18940_1069979
  intro a
  fin_cases a
  · exact context_11_75760_1069907
  · exact context_11_75761_1069933
  · exact context_11_75762_1069958
  · exact context_11_75763_1069978

theorem selected_cut_39434 : selected 10 ⟨1069995, by decide⟩
    (prefixPartial 11 75764) = some ⟨11, 2, 0, 1069995, 75764, 1357, 262144⟩ := by
  decide +kernel

theorem context_11_75764_1069995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75764 ⟨1069995, by decide⟩ :=
  accepted_of_selected 11 75764 ⟨1069995, by decide⟩ ⟨11, 2, 0, 1069995, 75764, 1357, 262144⟩
    (by decide) selected_cut_39434

theorem selected_cut_39435 : selected 10 ⟨1070010, by decide⟩
    (prefixPartial 11 75765) = some ⟨11, 2, 0, 1070010, 75765, 913, 262144⟩ := by
  decide +kernel

theorem context_11_75765_1070010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75765 ⟨1070010, by decide⟩ :=
  accepted_of_selected 11 75765 ⟨1070010, by decide⟩ ⟨11, 2, 0, 1070010, 75765, 913, 262144⟩
    (by decide) selected_cut_39435

theorem selected_cut_39436 : selected 10 ⟨1070022, by decide⟩
    (prefixPartial 11 75766) = some ⟨11, 2, 0, 1070022, 75766, 1181, 262144⟩ := by
  decide +kernel

theorem context_11_75766_1070022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75766 ⟨1070022, by decide⟩ :=
  accepted_of_selected 11 75766 ⟨1070022, by decide⟩ ⟨11, 2, 0, 1070022, 75766, 1181, 262144⟩
    (by decide) selected_cut_39436

theorem selected_cut_39437 : selected 10 ⟨1070033, by decide⟩
    (prefixPartial 11 75767) = some ⟨11, 2, 0, 1070033, 75767, 809, 262144⟩ := by
  decide +kernel

theorem context_11_75767_1070033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75767 ⟨1070033, by decide⟩ :=
  accepted_of_selected 11 75767 ⟨1070033, by decide⟩ ⟨11, 2, 0, 1070033, 75767, 809, 262144⟩
    (by decide) selected_cut_39437

theorem unmarked_context_10_18941_1070034 : frontier 11 ⟨1070034, by decide⟩
    (prefixCache 10 18941) (prefixPartial 10 18941) = false := by
  decide +kernel

theorem node_context_10_18941_1070034 : EJMOriginalGlobalDAGData.nodes 11 ⟨1070034, by decide⟩ =
    .split (coordinate 10) (![⟨1069995, by decide⟩,⟨1070010, by decide⟩,⟨1070022, by decide⟩,⟨1070033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18941_1070034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18941 ⟨1070034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18941
    ⟨1070034, by decide⟩ (by decide) (![⟨1069995, by decide⟩,⟨1070010, by decide⟩,⟨1070022, by decide⟩,⟨1070033, by decide⟩]) unmarked_context_10_18941_1070034 node_context_10_18941_1070034
  intro a
  fin_cases a
  · exact context_11_75764_1069995
  · exact context_11_75765_1070010
  · exact context_11_75766_1070022
  · exact context_11_75767_1070033

theorem selected_cut_39438 : selected 11 ⟨1070086, by decide⟩
    (prefixPartial 10 18942) = some ⟨10, 2, 0, 1070086, 18942, 2565, 1048576⟩ := by
  decide +kernel

theorem context_10_18942_1070086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18942 ⟨1070086, by decide⟩ :=
  accepted_of_selected 10 18942 ⟨1070086, by decide⟩ ⟨10, 2, 0, 1070086, 18942, 2565, 1048576⟩
    (by decide) selected_cut_39438

theorem selected_cut_39439 : selected 11 ⟨1070113, by decide⟩
    (prefixPartial 10 18943) = some ⟨10, 2, 0, 1070113, 18943, 721, 1048576⟩ := by
  decide +kernel

theorem context_10_18943_1070113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18943 ⟨1070113, by decide⟩ :=
  accepted_of_selected 10 18943 ⟨1070113, by decide⟩ ⟨10, 2, 0, 1070113, 18943, 721, 1048576⟩
    (by decide) selected_cut_39439

theorem unmarked_context_9_4735_1070114 : frontier 12 ⟨1070114, by decide⟩
    (prefixCache 9 4735) (prefixPartial 9 4735) = false := by
  decide +kernel

theorem node_context_9_4735_1070114 : EJMOriginalGlobalDAGData.nodes 12 ⟨1070114, by decide⟩ =
    .split (coordinate 9) (![⟨1069979, by decide⟩,⟨1070034, by decide⟩,⟨1070086, by decide⟩,⟨1070113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4735_1070114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4735 ⟨1070114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4735
    ⟨1070114, by decide⟩ (by decide) (![⟨1069979, by decide⟩,⟨1070034, by decide⟩,⟨1070086, by decide⟩,⟨1070113, by decide⟩]) unmarked_context_9_4735_1070114 node_context_9_4735_1070114
  intro a
  fin_cases a
  · exact context_10_18940_1069979
  · exact context_10_18941_1070034
  · exact context_10_18942_1070086
  · exact context_10_18943_1070113

theorem unmarked_context_8_1183_1070115 : frontier 13 ⟨1070115, by decide⟩
    (prefixCache 8 1183) (prefixPartial 8 1183) = false := by
  decide +kernel

theorem node_context_8_1183_1070115 : EJMOriginalGlobalDAGData.nodes 13 ⟨1070115, by decide⟩ =
    .split (coordinate 8) (![⟨1067994, by decide⟩,⟨1069330, by decide⟩,⟨1069890, by decide⟩,⟨1070114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1183_1070115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1183 ⟨1070115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1183
    ⟨1070115, by decide⟩ (by decide) (![⟨1067994, by decide⟩,⟨1069330, by decide⟩,⟨1069890, by decide⟩,⟨1070114, by decide⟩]) unmarked_context_8_1183_1070115 node_context_8_1183_1070115
  intro a
  fin_cases a
  · exact context_9_4732_1067994
  · exact context_9_4733_1069330
  · exact context_9_4734_1069890
  · exact context_9_4735_1070114

theorem unmarked_context_7_295_1070116 : frontier 14 ⟨1070116, by decide⟩
    (prefixCache 7 295) (prefixPartial 7 295) = false := by
  decide +kernel

theorem node_context_7_295_1070116 : EJMOriginalGlobalDAGData.nodes 14 ⟨1070116, by decide⟩ =
    .split (coordinate 7) (![⟨1054088, by decide⟩,⟨1058905, by decide⟩,⟨1064724, by decide⟩,⟨1070115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_295_1070116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 295 ⟨1070116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 295
    ⟨1070116, by decide⟩ (by decide) (![⟨1054088, by decide⟩,⟨1058905, by decide⟩,⟨1064724, by decide⟩,⟨1070115, by decide⟩]) unmarked_context_7_295_1070116 node_context_7_295_1070116
  intro a
  fin_cases a
  · exact context_8_1180_1054088
  · exact context_8_1181_1058905
  · exact context_8_1182_1064724
  · exact context_8_1183_1070115

theorem unmarked_context_6_73_1070117 : frontier 15 ⟨1070117, by decide⟩
    (prefixCache 6 73) (prefixPartial 6 73) = false := by
  decide +kernel

theorem node_context_6_73_1070117 : EJMOriginalGlobalDAGData.nodes 15 ⟨1070117, by decide⟩ =
    .split (coordinate 6) (![⟨1004909, by decide⟩,⟨1027416, by decide⟩,⟨1048193, by decide⟩,⟨1070116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_73_1070117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 73 ⟨1070117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 73
    ⟨1070117, by decide⟩ (by decide) (![⟨1004909, by decide⟩,⟨1027416, by decide⟩,⟨1048193, by decide⟩,⟨1070116, by decide⟩]) unmarked_context_6_73_1070117 node_context_6_73_1070117
  intro a
  fin_cases a
  · exact context_7_292_1004909
  · exact context_7_293_1027416
  · exact context_7_294_1048193
  · exact context_7_295_1070116

theorem selected_cut_39440 : selected 15 ⟨1070118, by decide⟩
    (prefixPartial 6 74) = some ⟨6, 1, 0, 1070118, 74, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_74_1070118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 74 ⟨1070118, by decide⟩ :=
  accepted_of_selected 6 74 ⟨1070118, by decide⟩ ⟨6, 1, 0, 1070118, 74, 1, 268435456⟩
    (by decide) selected_cut_39440

theorem selected_cut_39441 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 76800) = some ⟨11, 1, 0, 167448, 76800, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76800_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76800 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 76800 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 76800, 1, 262144⟩
    (by decide) selected_cut_39441

theorem selected_cut_39442 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 307204) = some ⟨12, 1, 0, 34034, 307204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307204_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307204 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 307204 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 307204, 1, 65536⟩
    (by decide) selected_cut_39442

theorem selected_cut_39443 : selected 9 ⟨1070165, by decide⟩
    (prefixPartial 12 307205) = some ⟨12, 2, 0, 1070165, 307205, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_307205_1070165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307205 ⟨1070165, by decide⟩ :=
  accepted_of_selected 12 307205 ⟨1070165, by decide⟩ ⟨12, 2, 0, 1070165, 307205, 2841, 65536⟩
    (by decide) selected_cut_39443

theorem selected_cut_39444 : selected 9 ⟨1070215, by decide⟩
    (prefixPartial 12 307206) = some ⟨12, 2, 0, 1070215, 307206, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_307206_1070215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307206 ⟨1070215, by decide⟩ :=
  accepted_of_selected 12 307206 ⟨1070215, by decide⟩ ⟨12, 2, 0, 1070215, 307206, 2909, 65536⟩
    (by decide) selected_cut_39444

theorem selected_cut_39445 : selected 9 ⟨1070266, by decide⟩
    (prefixPartial 12 307207) = some ⟨12, 2, 0, 1070266, 307207, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_307207_1070266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307207 ⟨1070266, by decide⟩ :=
  accepted_of_selected 12 307207 ⟨1070266, by decide⟩ ⟨12, 2, 0, 1070266, 307207, 2813, 65536⟩
    (by decide) selected_cut_39445

theorem unmarked_context_11_76801_1070267 : frontier 10 ⟨1070267, by decide⟩
    (prefixCache 11 76801) (prefixPartial 11 76801) = false := by
  decide +kernel

theorem node_context_11_76801_1070267 : EJMOriginalGlobalDAGData.nodes 10 ⟨1070267, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1070165, by decide⟩,⟨1070215, by decide⟩,⟨1070266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76801_1070267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76801 ⟨1070267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76801
    ⟨1070267, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1070165, by decide⟩,⟨1070215, by decide⟩,⟨1070266, by decide⟩]) unmarked_context_11_76801_1070267 node_context_11_76801_1070267
  intro a
  fin_cases a
  · exact context_12_307204_34034
  · exact context_12_307205_1070165
  · exact context_12_307206_1070215
  · exact context_12_307207_1070266

theorem selected_cut_39446 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 307208) = some ⟨12, 1, 0, 3161, 307208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307208_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307208 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 307208 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 307208, 1, 65536⟩
    (by decide) selected_cut_39446

theorem selected_cut_39447 : selected 9 ⟨1070306, by decide⟩
    (prefixPartial 12 307209) = some ⟨12, 2, 0, 1070306, 307209, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_307209_1070306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307209 ⟨1070306, by decide⟩ :=
  accepted_of_selected 12 307209 ⟨1070306, by decide⟩ ⟨12, 2, 0, 1070306, 307209, 2801, 65536⟩
    (by decide) selected_cut_39447

theorem selected_cut_39448 : selected 9 ⟨1070354, by decide⟩
    (prefixPartial 12 307210) = some ⟨12, 2, 0, 1070354, 307210, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_307210_1070354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307210 ⟨1070354, by decide⟩ :=
  accepted_of_selected 12 307210 ⟨1070354, by decide⟩ ⟨12, 2, 0, 1070354, 307210, 2773, 65536⟩
    (by decide) selected_cut_39448

theorem selected_cut_39449 : selected 9 ⟨1070401, by decide⟩
    (prefixPartial 12 307211) = some ⟨12, 2, 0, 1070401, 307211, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_307211_1070401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307211 ⟨1070401, by decide⟩ :=
  accepted_of_selected 12 307211 ⟨1070401, by decide⟩ ⟨12, 2, 0, 1070401, 307211, 2785, 65536⟩
    (by decide) selected_cut_39449

theorem unmarked_context_11_76802_1070402 : frontier 10 ⟨1070402, by decide⟩
    (prefixCache 11 76802) (prefixPartial 11 76802) = false := by
  decide +kernel

theorem node_context_11_76802_1070402 : EJMOriginalGlobalDAGData.nodes 10 ⟨1070402, by decide⟩ =
    .split (coordinate 11) (![⟨3161, by decide⟩,⟨1070306, by decide⟩,⟨1070354, by decide⟩,⟨1070401, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76802_1070402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76802 ⟨1070402, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76802
    ⟨1070402, by decide⟩ (by decide) (![⟨3161, by decide⟩,⟨1070306, by decide⟩,⟨1070354, by decide⟩,⟨1070401, by decide⟩]) unmarked_context_11_76802_1070402 node_context_11_76802_1070402
  intro a
  fin_cases a
  · exact context_12_307208_3161
  · exact context_12_307209_1070306
  · exact context_12_307210_1070354
  · exact context_12_307211_1070401

theorem selected_cut_39450 : selected 9 ⟨1070464, by decide⟩
    (prefixPartial 12 307212) = some ⟨12, 2, 0, 1070464, 307212, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_307212_1070464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307212 ⟨1070464, by decide⟩ :=
  accepted_of_selected 12 307212 ⟨1070464, by decide⟩ ⟨12, 2, 0, 1070464, 307212, 1965, 65536⟩
    (by decide) selected_cut_39450

theorem selected_cut_39451 : selected 9 ⟨1070513, by decide⟩
    (prefixPartial 12 307213) = some ⟨12, 2, 0, 1070513, 307213, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_307213_1070513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307213 ⟨1070513, by decide⟩ :=
  accepted_of_selected 12 307213 ⟨1070513, by decide⟩ ⟨12, 2, 0, 1070513, 307213, 2877, 65536⟩
    (by decide) selected_cut_39451

theorem selected_cut_39452 : selected 9 ⟨1070564, by decide⟩
    (prefixPartial 12 307214) = some ⟨12, 2, 0, 1070564, 307214, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_307214_1070564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307214 ⟨1070564, by decide⟩ :=
  accepted_of_selected 12 307214 ⟨1070564, by decide⟩ ⟨12, 2, 0, 1070564, 307214, 3117, 65536⟩
    (by decide) selected_cut_39452

theorem selected_cut_39453 : selected 9 ⟨1070602, by decide⟩
    (prefixPartial 12 307215) = some ⟨12, 2, 0, 1070602, 307215, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_307215_1070602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307215 ⟨1070602, by decide⟩ :=
  accepted_of_selected 12 307215 ⟨1070602, by decide⟩ ⟨12, 2, 0, 1070602, 307215, 2717, 65536⟩
    (by decide) selected_cut_39453

theorem unmarked_context_11_76803_1070603 : frontier 10 ⟨1070603, by decide⟩
    (prefixCache 11 76803) (prefixPartial 11 76803) = false := by
  decide +kernel

theorem node_context_11_76803_1070603 : EJMOriginalGlobalDAGData.nodes 10 ⟨1070603, by decide⟩ =
    .split (coordinate 11) (![⟨1070464, by decide⟩,⟨1070513, by decide⟩,⟨1070564, by decide⟩,⟨1070602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76803_1070603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76803 ⟨1070603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76803
    ⟨1070603, by decide⟩ (by decide) (![⟨1070464, by decide⟩,⟨1070513, by decide⟩,⟨1070564, by decide⟩,⟨1070602, by decide⟩]) unmarked_context_11_76803_1070603 node_context_11_76803_1070603
  intro a
  fin_cases a
  · exact context_12_307212_1070464
  · exact context_12_307213_1070513
  · exact context_12_307214_1070564
  · exact context_12_307215_1070602

theorem unmarked_context_10_19200_1070604 : frontier 11 ⟨1070604, by decide⟩
    (prefixCache 10 19200) (prefixPartial 10 19200) = false := by
  decide +kernel

theorem node_context_10_19200_1070604 : EJMOriginalGlobalDAGData.nodes 11 ⟨1070604, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1070267, by decide⟩,⟨1070402, by decide⟩,⟨1070603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19200_1070604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19200 ⟨1070604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19200
    ⟨1070604, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1070267, by decide⟩,⟨1070402, by decide⟩,⟨1070603, by decide⟩]) unmarked_context_10_19200_1070604 node_context_10_19200_1070604
  intro a
  fin_cases a
  · exact context_11_76800_167448
  · exact context_11_76801_1070267
  · exact context_11_76802_1070402
  · exact context_11_76803_1070603

theorem selected_cut_39454 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 307216) = some ⟨12, 1, 0, 26677, 307216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307216_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307216 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 307216 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 307216, 1, 65536⟩
    (by decide) selected_cut_39454

theorem selected_cut_39455 : selected 9 ⟨1070636, by decide⟩
    (prefixPartial 12 307217) = some ⟨12, 2, 0, 1070636, 307217, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_307217_1070636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307217 ⟨1070636, by decide⟩ :=
  accepted_of_selected 12 307217 ⟨1070636, by decide⟩ ⟨12, 2, 0, 1070636, 307217, 2041, 65536⟩
    (by decide) selected_cut_39455

theorem selected_cut_39456 : selected 9 ⟨1070664, by decide⟩
    (prefixPartial 12 307218) = some ⟨12, 2, 0, 1070664, 307218, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_307218_1070664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307218 ⟨1070664, by decide⟩ :=
  accepted_of_selected 12 307218 ⟨1070664, by decide⟩ ⟨12, 2, 0, 1070664, 307218, 1133, 65536⟩
    (by decide) selected_cut_39456

theorem selected_cut_39457 : selected 9 ⟨1070699, by decide⟩
    (prefixPartial 12 307219) = some ⟨12, 2, 0, 1070699, 307219, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_307219_1070699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307219 ⟨1070699, by decide⟩ :=
  accepted_of_selected 12 307219 ⟨1070699, by decide⟩ ⟨12, 2, 0, 1070699, 307219, 1937, 65536⟩
    (by decide) selected_cut_39457

theorem unmarked_context_11_76804_1070700 : frontier 10 ⟨1070700, by decide⟩
    (prefixCache 11 76804) (prefixPartial 11 76804) = false := by
  decide +kernel

theorem node_context_11_76804_1070700 : EJMOriginalGlobalDAGData.nodes 10 ⟨1070700, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1070636, by decide⟩,⟨1070664, by decide⟩,⟨1070699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76804_1070700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76804 ⟨1070700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76804
    ⟨1070700, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1070636, by decide⟩,⟨1070664, by decide⟩,⟨1070699, by decide⟩]) unmarked_context_11_76804_1070700 node_context_11_76804_1070700
  intro a
  fin_cases a
  · exact context_12_307216_26677
  · exact context_12_307217_1070636
  · exact context_12_307218_1070664
  · exact context_12_307219_1070699

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
