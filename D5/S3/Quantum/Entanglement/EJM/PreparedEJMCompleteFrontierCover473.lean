/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover472
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_22962_1259000 : frontier 11 ⟨1259000, by decide⟩
    (prefixCache 10 22962) (prefixPartial 10 22962) = false := by
  decide +kernel

theorem node_context_10_22962_1259000 : EJMOriginalGlobalDAGData.nodes 11 ⟨1259000, by decide⟩ =
    .split (coordinate 10) (![⟨1258653, by decide⟩,⟨1258880, by decide⟩,⟨900587, by decide⟩,⟨1258999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22962_1259000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22962 ⟨1259000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22962
    ⟨1259000, by decide⟩ (by decide) (![⟨1258653, by decide⟩,⟨1258880, by decide⟩,⟨900587, by decide⟩,⟨1258999, by decide⟩]) unmarked_context_10_22962_1259000 node_context_10_22962_1259000
  intro a
  fin_cases a
  · exact context_11_91848_1258653
  · exact context_11_91849_1258880
  · exact context_11_91850_900587
  · exact context_11_91851_1258999

theorem selected_cut_45412 : selected 9 ⟨766630, by decide⟩
    (prefixPartial 12 367408) = some ⟨12, 1, 0, 766630, 367408, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367408_766630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367408 ⟨766630, by decide⟩ :=
  accepted_of_selected 12 367408 ⟨766630, by decide⟩ ⟨12, 1, 0, 766630, 367408, 1, 65536⟩
    (by decide) selected_cut_45412

theorem selected_cut_45413 : selected 9 ⟨1259044, by decide⟩
    (prefixPartial 12 367409) = some ⟨12, 2, 0, 1259044, 367409, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_367409_1259044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367409 ⟨1259044, by decide⟩ :=
  accepted_of_selected 12 367409 ⟨1259044, by decide⟩ ⟨12, 2, 0, 1259044, 367409, 2037, 65536⟩
    (by decide) selected_cut_45413

theorem selected_cut_45414 : selected 9 ⟨1259086, by decide⟩
    (prefixPartial 12 367410) = some ⟨12, 2, 0, 1259086, 367410, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_367410_1259086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367410 ⟨1259086, by decide⟩ :=
  accepted_of_selected 12 367410 ⟨1259086, by decide⟩ ⟨12, 2, 0, 1259086, 367410, 2001, 65536⟩
    (by decide) selected_cut_45414

theorem selected_cut_45415 : selected 9 ⟨1259125, by decide⟩
    (prefixPartial 12 367411) = some ⟨12, 2, 0, 1259125, 367411, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_367411_1259125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367411 ⟨1259125, by decide⟩ :=
  accepted_of_selected 12 367411 ⟨1259125, by decide⟩ ⟨12, 2, 0, 1259125, 367411, 1829, 65536⟩
    (by decide) selected_cut_45415

theorem unmarked_context_11_91852_1259126 : frontier 10 ⟨1259126, by decide⟩
    (prefixCache 11 91852) (prefixPartial 11 91852) = false := by
  decide +kernel

theorem node_context_11_91852_1259126 : EJMOriginalGlobalDAGData.nodes 10 ⟨1259126, by decide⟩ =
    .split (coordinate 11) (![⟨766630, by decide⟩,⟨1259044, by decide⟩,⟨1259086, by decide⟩,⟨1259125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91852_1259126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91852 ⟨1259126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91852
    ⟨1259126, by decide⟩ (by decide) (![⟨766630, by decide⟩,⟨1259044, by decide⟩,⟨1259086, by decide⟩,⟨1259125, by decide⟩]) unmarked_context_11_91852_1259126 node_context_11_91852_1259126
  intro a
  fin_cases a
  · exact context_12_367408_766630
  · exact context_12_367409_1259044
  · exact context_12_367410_1259086
  · exact context_12_367411_1259125

theorem selected_cut_45416 : selected 9 ⟨1259164, by decide⟩
    (prefixPartial 12 367412) = some ⟨12, 2, 0, 1259164, 367412, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_367412_1259164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367412 ⟨1259164, by decide⟩ :=
  accepted_of_selected 12 367412 ⟨1259164, by decide⟩ ⟨12, 2, 0, 1259164, 367412, 1649, 65536⟩
    (by decide) selected_cut_45416

theorem selected_cut_45417 : selected 9 ⟨1259216, by decide⟩
    (prefixPartial 12 367413) = some ⟨12, 2, 0, 1259216, 367413, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_367413_1259216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367413 ⟨1259216, by decide⟩ :=
  accepted_of_selected 12 367413 ⟨1259216, by decide⟩ ⟨12, 2, 0, 1259216, 367413, 2145, 65536⟩
    (by decide) selected_cut_45417

theorem selected_cut_45418 : selected 9 ⟨1259250, by decide⟩
    (prefixPartial 12 367414) = some ⟨12, 2, 0, 1259250, 367414, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_367414_1259250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367414 ⟨1259250, by decide⟩ :=
  accepted_of_selected 12 367414 ⟨1259250, by decide⟩ ⟨12, 2, 0, 1259250, 367414, 1661, 65536⟩
    (by decide) selected_cut_45418

theorem selected_cut_45419 : selected 9 ⟨1259282, by decide⟩
    (prefixPartial 12 367415) = some ⟨12, 2, 0, 1259282, 367415, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_367415_1259282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367415 ⟨1259282, by decide⟩ :=
  accepted_of_selected 12 367415 ⟨1259282, by decide⟩ ⟨12, 2, 0, 1259282, 367415, 1553, 65536⟩
    (by decide) selected_cut_45419

theorem unmarked_context_11_91853_1259283 : frontier 10 ⟨1259283, by decide⟩
    (prefixCache 11 91853) (prefixPartial 11 91853) = false := by
  decide +kernel

theorem node_context_11_91853_1259283 : EJMOriginalGlobalDAGData.nodes 10 ⟨1259283, by decide⟩ =
    .split (coordinate 11) (![⟨1259164, by decide⟩,⟨1259216, by decide⟩,⟨1259250, by decide⟩,⟨1259282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91853_1259283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91853 ⟨1259283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91853
    ⟨1259283, by decide⟩ (by decide) (![⟨1259164, by decide⟩,⟨1259216, by decide⟩,⟨1259250, by decide⟩,⟨1259282, by decide⟩]) unmarked_context_11_91853_1259283 node_context_11_91853_1259283
  intro a
  fin_cases a
  · exact context_12_367412_1259164
  · exact context_12_367413_1259216
  · exact context_12_367414_1259250
  · exact context_12_367415_1259282

theorem selected_cut_45420 : selected 9 ⟨1259311, by decide⟩
    (prefixPartial 12 367416) = some ⟨12, 2, 0, 1259311, 367416, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_367416_1259311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367416 ⟨1259311, by decide⟩ :=
  accepted_of_selected 12 367416 ⟨1259311, by decide⟩ ⟨12, 2, 0, 1259311, 367416, 1481, 65536⟩
    (by decide) selected_cut_45420

theorem selected_cut_45421 : selected 9 ⟨1259334, by decide⟩
    (prefixPartial 12 367417) = some ⟨12, 2, 0, 1259334, 367417, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_367417_1259334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367417 ⟨1259334, by decide⟩ :=
  accepted_of_selected 12 367417 ⟨1259334, by decide⟩ ⟨12, 2, 0, 1259334, 367417, 1601, 65536⟩
    (by decide) selected_cut_45421

theorem selected_cut_45422 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 367418) = some ⟨12, 1, 0, 662655, 367418, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367418_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367418 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 367418 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 367418, 1, 65536⟩
    (by decide) selected_cut_45422

theorem selected_cut_45423 : selected 9 ⟨1259364, by decide⟩
    (prefixPartial 12 367419) = some ⟨12, 2, 0, 1259364, 367419, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_367419_1259364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367419 ⟨1259364, by decide⟩ :=
  accepted_of_selected 12 367419 ⟨1259364, by decide⟩ ⟨12, 2, 0, 1259364, 367419, 1565, 65536⟩
    (by decide) selected_cut_45423

theorem unmarked_context_11_91854_1259365 : frontier 10 ⟨1259365, by decide⟩
    (prefixCache 11 91854) (prefixPartial 11 91854) = false := by
  decide +kernel

theorem node_context_11_91854_1259365 : EJMOriginalGlobalDAGData.nodes 10 ⟨1259365, by decide⟩ =
    .split (coordinate 11) (![⟨1259311, by decide⟩,⟨1259334, by decide⟩,⟨662655, by decide⟩,⟨1259364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91854_1259365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91854 ⟨1259365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91854
    ⟨1259365, by decide⟩ (by decide) (![⟨1259311, by decide⟩,⟨1259334, by decide⟩,⟨662655, by decide⟩,⟨1259364, by decide⟩]) unmarked_context_11_91854_1259365 node_context_11_91854_1259365
  intro a
  fin_cases a
  · exact context_12_367416_1259311
  · exact context_12_367417_1259334
  · exact context_12_367418_662655
  · exact context_12_367419_1259364

theorem selected_cut_45424 : selected 10 ⟨1259420, by decide⟩
    (prefixPartial 11 91855) = some ⟨11, 2, 0, 1259420, 91855, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_91855_1259420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91855 ⟨1259420, by decide⟩ :=
  accepted_of_selected 11 91855 ⟨1259420, by decide⟩ ⟨11, 2, 0, 1259420, 91855, 2725, 262144⟩
    (by decide) selected_cut_45424

theorem unmarked_context_10_22963_1259421 : frontier 11 ⟨1259421, by decide⟩
    (prefixCache 10 22963) (prefixPartial 10 22963) = false := by
  decide +kernel

theorem node_context_10_22963_1259421 : EJMOriginalGlobalDAGData.nodes 11 ⟨1259421, by decide⟩ =
    .split (coordinate 10) (![⟨1259126, by decide⟩,⟨1259283, by decide⟩,⟨1259365, by decide⟩,⟨1259420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22963_1259421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22963 ⟨1259421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22963
    ⟨1259421, by decide⟩ (by decide) (![⟨1259126, by decide⟩,⟨1259283, by decide⟩,⟨1259365, by decide⟩,⟨1259420, by decide⟩]) unmarked_context_10_22963_1259421 node_context_10_22963_1259421
  intro a
  fin_cases a
  · exact context_11_91852_1259126
  · exact context_11_91853_1259283
  · exact context_11_91854_1259365
  · exact context_11_91855_1259420

theorem unmarked_context_9_5740_1259422 : frontier 12 ⟨1259422, by decide⟩
    (prefixCache 9 5740) (prefixPartial 9 5740) = false := by
  decide +kernel

theorem node_context_9_5740_1259422 : EJMOriginalGlobalDAGData.nodes 12 ⟨1259422, by decide⟩ =
    .split (coordinate 9) (![⟨1257792, by decide⟩,⟨1258509, by decide⟩,⟨1259000, by decide⟩,⟨1259421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5740_1259422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5740 ⟨1259422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5740
    ⟨1259422, by decide⟩ (by decide) (![⟨1257792, by decide⟩,⟨1258509, by decide⟩,⟨1259000, by decide⟩,⟨1259421, by decide⟩]) unmarked_context_9_5740_1259422 node_context_9_5740_1259422
  intro a
  fin_cases a
  · exact context_10_22960_1257792
  · exact context_10_22961_1258509
  · exact context_10_22962_1259000
  · exact context_10_22963_1259421

theorem selected_cut_45425 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 22964) = some ⟨10, 1, 0, 3442, 22964, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22964_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22964 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 22964 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 22964, 1, 1048576⟩
    (by decide) selected_cut_45425

theorem selected_cut_45426 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22965) = some ⟨10, 1, 0, 893098, 22965, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22965_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22965 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22965 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22965, 1, 1048576⟩
    (by decide) selected_cut_45426

theorem selected_cut_45427 : selected 10 ⟨1259498, by decide⟩
    (prefixPartial 11 91864) = some ⟨11, 2, 0, 1259498, 91864, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_91864_1259498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91864 ⟨1259498, by decide⟩ :=
  accepted_of_selected 11 91864 ⟨1259498, by decide⟩ ⟨11, 2, 0, 1259498, 91864, 2893, 262144⟩
    (by decide) selected_cut_45427

theorem selected_cut_45428 : selected 10 ⟨1259566, by decide⟩
    (prefixPartial 11 91865) = some ⟨11, 2, 0, 1259566, 91865, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_91865_1259566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91865 ⟨1259566, by decide⟩ :=
  accepted_of_selected 11 91865 ⟨1259566, by decide⟩ ⟨11, 2, 0, 1259566, 91865, 2837, 262144⟩
    (by decide) selected_cut_45428

theorem selected_cut_45429 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 91866) = some ⟨11, 1, 0, 900587, 91866, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91866_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91866 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 91866 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 91866, 1, 262144⟩
    (by decide) selected_cut_45429

theorem selected_cut_45430 : selected 10 ⟨1259610, by decide⟩
    (prefixPartial 11 91867) = some ⟨11, 2, 0, 1259610, 91867, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_91867_1259610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91867 ⟨1259610, by decide⟩ :=
  accepted_of_selected 11 91867 ⟨1259610, by decide⟩ ⟨11, 2, 0, 1259610, 91867, 1733, 262144⟩
    (by decide) selected_cut_45430

theorem unmarked_context_10_22966_1259611 : frontier 11 ⟨1259611, by decide⟩
    (prefixCache 10 22966) (prefixPartial 10 22966) = false := by
  decide +kernel

theorem node_context_10_22966_1259611 : EJMOriginalGlobalDAGData.nodes 11 ⟨1259611, by decide⟩ =
    .split (coordinate 10) (![⟨1259498, by decide⟩,⟨1259566, by decide⟩,⟨900587, by decide⟩,⟨1259610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22966_1259611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22966 ⟨1259611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22966
    ⟨1259611, by decide⟩ (by decide) (![⟨1259498, by decide⟩,⟨1259566, by decide⟩,⟨900587, by decide⟩,⟨1259610, by decide⟩]) unmarked_context_10_22966_1259611 node_context_10_22966_1259611
  intro a
  fin_cases a
  · exact context_11_91864_1259498
  · exact context_11_91865_1259566
  · exact context_11_91866_900587
  · exact context_11_91867_1259610

theorem selected_cut_45431 : selected 10 ⟨1259684, by decide⟩
    (prefixPartial 11 91868) = some ⟨11, 2, 0, 1259684, 91868, 3317, 262144⟩ := by
  decide +kernel

theorem context_11_91868_1259684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91868 ⟨1259684, by decide⟩ :=
  accepted_of_selected 11 91868 ⟨1259684, by decide⟩ ⟨11, 2, 0, 1259684, 91868, 3317, 262144⟩
    (by decide) selected_cut_45431

theorem selected_cut_45432 : selected 10 ⟨1259727, by decide⟩
    (prefixPartial 11 91869) = some ⟨11, 2, 0, 1259727, 91869, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_91869_1259727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91869 ⟨1259727, by decide⟩ :=
  accepted_of_selected 11 91869 ⟨1259727, by decide⟩ ⟨11, 2, 0, 1259727, 91869, 2061, 262144⟩
    (by decide) selected_cut_45432

theorem selected_cut_45433 : selected 10 ⟨1259769, by decide⟩
    (prefixPartial 11 91870) = some ⟨11, 2, 0, 1259769, 91870, 1853, 262144⟩ := by
  decide +kernel

theorem context_11_91870_1259769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91870 ⟨1259769, by decide⟩ :=
  accepted_of_selected 11 91870 ⟨1259769, by decide⟩ ⟨11, 2, 0, 1259769, 91870, 1853, 262144⟩
    (by decide) selected_cut_45433

theorem selected_cut_45434 : selected 10 ⟨1259785, by decide⟩
    (prefixPartial 11 91871) = some ⟨11, 2, 0, 1259785, 91871, 945, 262144⟩ := by
  decide +kernel

theorem context_11_91871_1259785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91871 ⟨1259785, by decide⟩ :=
  accepted_of_selected 11 91871 ⟨1259785, by decide⟩ ⟨11, 2, 0, 1259785, 91871, 945, 262144⟩
    (by decide) selected_cut_45434

theorem unmarked_context_10_22967_1259786 : frontier 11 ⟨1259786, by decide⟩
    (prefixCache 10 22967) (prefixPartial 10 22967) = false := by
  decide +kernel

theorem node_context_10_22967_1259786 : EJMOriginalGlobalDAGData.nodes 11 ⟨1259786, by decide⟩ =
    .split (coordinate 10) (![⟨1259684, by decide⟩,⟨1259727, by decide⟩,⟨1259769, by decide⟩,⟨1259785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22967_1259786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22967 ⟨1259786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22967
    ⟨1259786, by decide⟩ (by decide) (![⟨1259684, by decide⟩,⟨1259727, by decide⟩,⟨1259769, by decide⟩,⟨1259785, by decide⟩]) unmarked_context_10_22967_1259786 node_context_10_22967_1259786
  intro a
  fin_cases a
  · exact context_11_91868_1259684
  · exact context_11_91869_1259727
  · exact context_11_91870_1259769
  · exact context_11_91871_1259785

theorem unmarked_context_9_5741_1259787 : frontier 12 ⟨1259787, by decide⟩
    (prefixCache 9 5741) (prefixPartial 9 5741) = false := by
  decide +kernel

theorem node_context_9_5741_1259787 : EJMOriginalGlobalDAGData.nodes 12 ⟨1259787, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1259611, by decide⟩,⟨1259786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5741_1259787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5741 ⟨1259787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5741
    ⟨1259787, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨1259611, by decide⟩,⟨1259786, by decide⟩]) unmarked_context_9_5741_1259787 node_context_9_5741_1259787
  intro a
  fin_cases a
  · exact context_10_22964_3442
  · exact context_10_22965_893098
  · exact context_10_22966_1259611
  · exact context_10_22967_1259786

theorem selected_cut_45435 : selected 12 ⟨1259889, by decide⟩
    (prefixPartial 9 5742) = some ⟨9, 2, 0, 1259889, 5742, 3261, 4194304⟩ := by
  decide +kernel

theorem context_9_5742_1259889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5742 ⟨1259889, by decide⟩ :=
  accepted_of_selected 9 5742 ⟨1259889, by decide⟩ ⟨9, 2, 0, 1259889, 5742, 3261, 4194304⟩
    (by decide) selected_cut_45435

theorem selected_cut_45436 : selected 12 ⟨1259909, by decide⟩
    (prefixPartial 9 5743) = some ⟨9, 2, 0, 1259909, 5743, 213, 4194304⟩ := by
  decide +kernel

theorem context_9_5743_1259909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5743 ⟨1259909, by decide⟩ :=
  accepted_of_selected 9 5743 ⟨1259909, by decide⟩ ⟨9, 2, 0, 1259909, 5743, 213, 4194304⟩
    (by decide) selected_cut_45436

theorem unmarked_context_8_1435_1259910 : frontier 13 ⟨1259910, by decide⟩
    (prefixCache 8 1435) (prefixPartial 8 1435) = false := by
  decide +kernel

theorem node_context_8_1435_1259910 : EJMOriginalGlobalDAGData.nodes 13 ⟨1259910, by decide⟩ =
    .split (coordinate 8) (![⟨1259422, by decide⟩,⟨1259787, by decide⟩,⟨1259889, by decide⟩,⟨1259909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1435_1259910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1435 ⟨1259910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1435
    ⟨1259910, by decide⟩ (by decide) (![⟨1259422, by decide⟩,⟨1259787, by decide⟩,⟨1259889, by decide⟩,⟨1259909, by decide⟩]) unmarked_context_8_1435_1259910 node_context_8_1435_1259910
  intro a
  fin_cases a
  · exact context_9_5740_1259422
  · exact context_9_5741_1259787
  · exact context_9_5742_1259889
  · exact context_9_5743_1259909

theorem unmarked_context_7_358_1259911 : frontier 14 ⟨1259911, by decide⟩
    (prefixCache 7 358) (prefixPartial 7 358) = false := by
  decide +kernel

theorem node_context_7_358_1259911 : EJMOriginalGlobalDAGData.nodes 14 ⟨1259911, by decide⟩ =
    .split (coordinate 7) (![⟨1254454, by decide⟩,⟨1109534, by decide⟩,⟨1257325, by decide⟩,⟨1259910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_358_1259911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 358 ⟨1259911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 358
    ⟨1259911, by decide⟩ (by decide) (![⟨1254454, by decide⟩,⟨1109534, by decide⟩,⟨1257325, by decide⟩,⟨1259910, by decide⟩]) unmarked_context_7_358_1259911 node_context_7_358_1259911
  intro a
  fin_cases a
  · exact context_8_1432_1254454
  · exact context_8_1433_1109534
  · exact context_8_1434_1257325
  · exact context_8_1435_1259910

theorem selected_cut_45437 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 91904) = some ⟨11, 1, 0, 434745, 91904, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91904_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91904 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 91904 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 91904, 1, 262144⟩
    (by decide) selected_cut_45437

theorem selected_cut_45438 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 367620) = some ⟨12, 1, 0, 14169, 367620, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367620_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367620 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 367620 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 367620, 1, 65536⟩
    (by decide) selected_cut_45438

theorem selected_cut_45439 : selected 9 ⟨1260031, by decide⟩
    (prefixPartial 12 367621) = some ⟨12, 2, 0, 1260031, 367621, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_367621_1260031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367621 ⟨1260031, by decide⟩ :=
  accepted_of_selected 12 367621 ⟨1260031, by decide⟩ ⟨12, 2, 0, 1260031, 367621, 1893, 65536⟩
    (by decide) selected_cut_45439

theorem selected_cut_45440 : selected 9 ⟨1260127, by decide⟩
    (prefixPartial 12 367622) = some ⟨12, 2, 0, 1260127, 367622, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_367622_1260127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367622 ⟨1260127, by decide⟩ :=
  accepted_of_selected 12 367622 ⟨1260127, by decide⟩ ⟨12, 2, 0, 1260127, 367622, 3929, 65536⟩
    (by decide) selected_cut_45440

theorem selected_cut_45441 : selected 9 ⟨1260215, by decide⟩
    (prefixPartial 12 367623) = some ⟨12, 2, 0, 1260215, 367623, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_367623_1260215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367623 ⟨1260215, by decide⟩ :=
  accepted_of_selected 12 367623 ⟨1260215, by decide⟩ ⟨12, 2, 0, 1260215, 367623, 3925, 65536⟩
    (by decide) selected_cut_45441

theorem unmarked_context_11_91905_1260216 : frontier 10 ⟨1260216, by decide⟩
    (prefixCache 11 91905) (prefixPartial 11 91905) = false := by
  decide +kernel

theorem node_context_11_91905_1260216 : EJMOriginalGlobalDAGData.nodes 10 ⟨1260216, by decide⟩ =
    .split (coordinate 11) (![⟨14169, by decide⟩,⟨1260031, by decide⟩,⟨1260127, by decide⟩,⟨1260215, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91905_1260216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91905 ⟨1260216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91905
    ⟨1260216, by decide⟩ (by decide) (![⟨14169, by decide⟩,⟨1260031, by decide⟩,⟨1260127, by decide⟩,⟨1260215, by decide⟩]) unmarked_context_11_91905_1260216 node_context_11_91905_1260216
  intro a
  fin_cases a
  · exact context_12_367620_14169
  · exact context_12_367621_1260031
  · exact context_12_367622_1260127
  · exact context_12_367623_1260215

theorem selected_cut_45442 : selected 10 ⟨1260317, by decide⟩
    (prefixPartial 11 91906) = some ⟨11, 2, 0, 1260317, 91906, 2477, 262144⟩ := by
  decide +kernel

theorem context_11_91906_1260317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91906 ⟨1260317, by decide⟩ :=
  accepted_of_selected 11 91906 ⟨1260317, by decide⟩ ⟨11, 2, 0, 1260317, 91906, 2477, 262144⟩
    (by decide) selected_cut_45442

theorem selected_cut_45443 : selected 10 ⟨1260385, by decide⟩
    (prefixPartial 11 91907) = some ⟨11, 2, 0, 1260385, 91907, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_91907_1260385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91907 ⟨1260385, by decide⟩ :=
  accepted_of_selected 11 91907 ⟨1260385, by decide⟩ ⟨11, 2, 0, 1260385, 91907, 2193, 262144⟩
    (by decide) selected_cut_45443

theorem unmarked_context_10_22976_1260386 : frontier 11 ⟨1260386, by decide⟩
    (prefixCache 10 22976) (prefixPartial 10 22976) = false := by
  decide +kernel

theorem node_context_10_22976_1260386 : EJMOriginalGlobalDAGData.nodes 11 ⟨1260386, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1260216, by decide⟩,⟨1260317, by decide⟩,⟨1260385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22976_1260386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22976 ⟨1260386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22976
    ⟨1260386, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1260216, by decide⟩,⟨1260317, by decide⟩,⟨1260385, by decide⟩]) unmarked_context_10_22976_1260386 node_context_10_22976_1260386
  intro a
  fin_cases a
  · exact context_11_91904_434745
  · exact context_11_91905_1260216
  · exact context_11_91906_1260317
  · exact context_11_91907_1260385

theorem selected_cut_45444 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 367632) = some ⟨12, 1, 0, 985390, 367632, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367632_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367632 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 367632 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 367632, 1, 65536⟩
    (by decide) selected_cut_45444

theorem selected_cut_45445 : selected 9 ⟨1260455, by decide⟩
    (prefixPartial 12 367633) = some ⟨12, 2, 0, 1260455, 367633, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_367633_1260455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367633 ⟨1260455, by decide⟩ :=
  accepted_of_selected 12 367633 ⟨1260455, by decide⟩ ⟨12, 2, 0, 1260455, 367633, 2161, 65536⟩
    (by decide) selected_cut_45445

theorem selected_cut_45446 : selected 9 ⟨1260523, by decide⟩
    (prefixPartial 12 367634) = some ⟨12, 2, 0, 1260523, 367634, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_367634_1260523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367634 ⟨1260523, by decide⟩ :=
  accepted_of_selected 12 367634 ⟨1260523, by decide⟩ ⟨12, 2, 0, 1260523, 367634, 3005, 65536⟩
    (by decide) selected_cut_45446

theorem selected_cut_45447 : selected 9 ⟨1260588, by decide⟩
    (prefixPartial 12 367635) = some ⟨12, 2, 0, 1260588, 367635, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_367635_1260588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367635 ⟨1260588, by decide⟩ :=
  accepted_of_selected 12 367635 ⟨1260588, by decide⟩ ⟨12, 2, 0, 1260588, 367635, 3017, 65536⟩
    (by decide) selected_cut_45447

theorem unmarked_context_11_91908_1260589 : frontier 10 ⟨1260589, by decide⟩
    (prefixCache 11 91908) (prefixPartial 11 91908) = false := by
  decide +kernel

theorem node_context_11_91908_1260589 : EJMOriginalGlobalDAGData.nodes 10 ⟨1260589, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1260455, by decide⟩,⟨1260523, by decide⟩,⟨1260588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91908_1260589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91908 ⟨1260589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91908
    ⟨1260589, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1260455, by decide⟩,⟨1260523, by decide⟩,⟨1260588, by decide⟩]) unmarked_context_11_91908_1260589 node_context_11_91908_1260589
  intro a
  fin_cases a
  · exact context_12_367632_985390
  · exact context_12_367633_1260455
  · exact context_12_367634_1260523
  · exact context_12_367635_1260588

theorem selected_cut_45448 : selected 9 ⟨1260689, by decide⟩
    (prefixPartial 12 367636) = some ⟨12, 2, 0, 1260689, 367636, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_367636_1260689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367636 ⟨1260689, by decide⟩ :=
  accepted_of_selected 12 367636 ⟨1260689, by decide⟩ ⟨12, 2, 0, 1260689, 367636, 1793, 65536⟩
    (by decide) selected_cut_45448

theorem selected_cut_45449 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 367637) = some ⟨12, 1, 0, 772506, 367637, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367637_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367637 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 367637 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 367637, 1, 65536⟩
    (by decide) selected_cut_45449

theorem selected_cut_45450 : selected 9 ⟨1260754, by decide⟩
    (prefixPartial 12 367638) = some ⟨12, 2, 0, 1260754, 367638, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_367638_1260754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367638 ⟨1260754, by decide⟩ :=
  accepted_of_selected 12 367638 ⟨1260754, by decide⟩ ⟨12, 2, 0, 1260754, 367638, 2989, 65536⟩
    (by decide) selected_cut_45450

theorem selected_cut_45451 : selected 9 ⟨1260821, by decide⟩
    (prefixPartial 12 367639) = some ⟨12, 2, 0, 1260821, 367639, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_367639_1260821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367639 ⟨1260821, by decide⟩ :=
  accepted_of_selected 12 367639 ⟨1260821, by decide⟩ ⟨12, 2, 0, 1260821, 367639, 3069, 65536⟩
    (by decide) selected_cut_45451

theorem unmarked_context_11_91909_1260822 : frontier 10 ⟨1260822, by decide⟩
    (prefixCache 11 91909) (prefixPartial 11 91909) = false := by
  decide +kernel

theorem node_context_11_91909_1260822 : EJMOriginalGlobalDAGData.nodes 10 ⟨1260822, by decide⟩ =
    .split (coordinate 11) (![⟨1260689, by decide⟩,⟨772506, by decide⟩,⟨1260754, by decide⟩,⟨1260821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91909_1260822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91909 ⟨1260822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91909
    ⟨1260822, by decide⟩ (by decide) (![⟨1260689, by decide⟩,⟨772506, by decide⟩,⟨1260754, by decide⟩,⟨1260821, by decide⟩]) unmarked_context_11_91909_1260822 node_context_11_91909_1260822
  intro a
  fin_cases a
  · exact context_12_367636_1260689
  · exact context_12_367637_772506
  · exact context_12_367638_1260754
  · exact context_12_367639_1260821

theorem selected_cut_45452 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 367640) = some ⟨12, 1, 0, 994572, 367640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367640_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367640 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 367640 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 367640, 1, 65536⟩
    (by decide) selected_cut_45452

theorem selected_cut_45453 : selected 9 ⟨1260887, by decide⟩
    (prefixPartial 12 367641) = some ⟨12, 2, 0, 1260887, 367641, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_367641_1260887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367641 ⟨1260887, by decide⟩ :=
  accepted_of_selected 12 367641 ⟨1260887, by decide⟩ ⟨12, 2, 0, 1260887, 367641, 2893, 65536⟩
    (by decide) selected_cut_45453

theorem selected_cut_45454 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 367642) = some ⟨12, 1, 0, 806997, 367642, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367642_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367642 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 367642 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 367642, 1, 65536⟩
    (by decide) selected_cut_45454

theorem selected_cut_45455 : selected 9 ⟨1260961, by decide⟩
    (prefixPartial 12 367643) = some ⟨12, 2, 0, 1260961, 367643, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_367643_1260961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367643 ⟨1260961, by decide⟩ :=
  accepted_of_selected 12 367643 ⟨1260961, by decide⟩ ⟨12, 2, 0, 1260961, 367643, 3125, 65536⟩
    (by decide) selected_cut_45455

theorem unmarked_context_11_91910_1260962 : frontier 10 ⟨1260962, by decide⟩
    (prefixCache 11 91910) (prefixPartial 11 91910) = false := by
  decide +kernel

theorem node_context_11_91910_1260962 : EJMOriginalGlobalDAGData.nodes 10 ⟨1260962, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1260887, by decide⟩,⟨806997, by decide⟩,⟨1260961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91910_1260962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91910 ⟨1260962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91910
    ⟨1260962, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1260887, by decide⟩,⟨806997, by decide⟩,⟨1260961, by decide⟩]) unmarked_context_11_91910_1260962 node_context_11_91910_1260962
  intro a
  fin_cases a
  · exact context_12_367640_994572
  · exact context_12_367641_1260887
  · exact context_12_367642_806997
  · exact context_12_367643_1260961

theorem selected_cut_45456 : selected 9 ⟨1261016, by decide⟩
    (prefixPartial 12 367644) = some ⟨12, 2, 0, 1261016, 367644, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_367644_1261016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367644 ⟨1261016, by decide⟩ :=
  accepted_of_selected 12 367644 ⟨1261016, by decide⟩ ⟨12, 2, 0, 1261016, 367644, 2185, 65536⟩
    (by decide) selected_cut_45456

theorem selected_cut_45457 : selected 9 ⟨1261074, by decide⟩
    (prefixPartial 12 367645) = some ⟨12, 2, 0, 1261074, 367645, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_367645_1261074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367645 ⟨1261074, by decide⟩ :=
  accepted_of_selected 12 367645 ⟨1261074, by decide⟩ ⟨12, 2, 0, 1261074, 367645, 2505, 65536⟩
    (by decide) selected_cut_45457

theorem selected_cut_45458 : selected 9 ⟨1261147, by decide⟩
    (prefixPartial 12 367646) = some ⟨12, 2, 0, 1261147, 367646, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_367646_1261147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367646 ⟨1261147, by decide⟩ :=
  accepted_of_selected 12 367646 ⟨1261147, by decide⟩ ⟨12, 2, 0, 1261147, 367646, 2629, 65536⟩
    (by decide) selected_cut_45458

theorem selected_cut_45459 : selected 9 ⟨1261198, by decide⟩
    (prefixPartial 12 367647) = some ⟨12, 2, 0, 1261198, 367647, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_367647_1261198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367647 ⟨1261198, by decide⟩ :=
  accepted_of_selected 12 367647 ⟨1261198, by decide⟩ ⟨12, 2, 0, 1261198, 367647, 2245, 65536⟩
    (by decide) selected_cut_45459

theorem unmarked_context_11_91911_1261199 : frontier 10 ⟨1261199, by decide⟩
    (prefixCache 11 91911) (prefixPartial 11 91911) = false := by
  decide +kernel

theorem node_context_11_91911_1261199 : EJMOriginalGlobalDAGData.nodes 10 ⟨1261199, by decide⟩ =
    .split (coordinate 11) (![⟨1261016, by decide⟩,⟨1261074, by decide⟩,⟨1261147, by decide⟩,⟨1261198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91911_1261199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91911 ⟨1261199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91911
    ⟨1261199, by decide⟩ (by decide) (![⟨1261016, by decide⟩,⟨1261074, by decide⟩,⟨1261147, by decide⟩,⟨1261198, by decide⟩]) unmarked_context_11_91911_1261199 node_context_11_91911_1261199
  intro a
  fin_cases a
  · exact context_12_367644_1261016
  · exact context_12_367645_1261074
  · exact context_12_367646_1261147
  · exact context_12_367647_1261198

theorem unmarked_context_10_22977_1261200 : frontier 11 ⟨1261200, by decide⟩
    (prefixCache 10 22977) (prefixPartial 10 22977) = false := by
  decide +kernel

theorem node_context_10_22977_1261200 : EJMOriginalGlobalDAGData.nodes 11 ⟨1261200, by decide⟩ =
    .split (coordinate 10) (![⟨1260589, by decide⟩,⟨1260822, by decide⟩,⟨1260962, by decide⟩,⟨1261199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22977_1261200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22977 ⟨1261200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22977
    ⟨1261200, by decide⟩ (by decide) (![⟨1260589, by decide⟩,⟨1260822, by decide⟩,⟨1260962, by decide⟩,⟨1261199, by decide⟩]) unmarked_context_10_22977_1261200 node_context_10_22977_1261200
  intro a
  fin_cases a
  · exact context_11_91908_1260589
  · exact context_11_91909_1260822
  · exact context_11_91910_1260962
  · exact context_11_91911_1261199

theorem selected_cut_45460 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 367648) = some ⟨12, 1, 0, 435790, 367648, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367648_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367648 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 367648 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 367648, 1, 65536⟩
    (by decide) selected_cut_45460

theorem selected_cut_45461 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 367649) = some ⟨12, 1, 0, 772506, 367649, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367649_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367649 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 367649 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 367649, 1, 65536⟩
    (by decide) selected_cut_45461

theorem selected_cut_45462 : selected 9 ⟨1261275, by decide⟩
    (prefixPartial 12 367650) = some ⟨12, 2, 0, 1261275, 367650, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_367650_1261275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367650 ⟨1261275, by decide⟩ :=
  accepted_of_selected 12 367650 ⟨1261275, by decide⟩ ⟨12, 2, 0, 1261275, 367650, 2249, 65536⟩
    (by decide) selected_cut_45462

theorem selected_cut_45463 : selected 9 ⟨1261337, by decide⟩
    (prefixPartial 12 367651) = some ⟨12, 2, 0, 1261337, 367651, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_367651_1261337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367651 ⟨1261337, by decide⟩ :=
  accepted_of_selected 12 367651 ⟨1261337, by decide⟩ ⟨12, 2, 0, 1261337, 367651, 2161, 65536⟩
    (by decide) selected_cut_45463

theorem unmarked_context_11_91912_1261338 : frontier 10 ⟨1261338, by decide⟩
    (prefixCache 11 91912) (prefixPartial 11 91912) = false := by
  decide +kernel

theorem node_context_11_91912_1261338 : EJMOriginalGlobalDAGData.nodes 10 ⟨1261338, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨772506, by decide⟩,⟨1261275, by decide⟩,⟨1261337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91912_1261338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91912 ⟨1261338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91912
    ⟨1261338, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨772506, by decide⟩,⟨1261275, by decide⟩,⟨1261337, by decide⟩]) unmarked_context_11_91912_1261338 node_context_11_91912_1261338
  intro a
  fin_cases a
  · exact context_12_367648_435790
  · exact context_12_367649_772506
  · exact context_12_367650_1261275
  · exact context_12_367651_1261337

theorem selected_cut_45464 : selected 10 ⟨1261478, by decide⟩
    (prefixPartial 11 91913) = some ⟨11, 2, 0, 1261478, 91913, 3673, 262144⟩ := by
  decide +kernel

theorem context_11_91913_1261478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91913 ⟨1261478, by decide⟩ :=
  accepted_of_selected 11 91913 ⟨1261478, by decide⟩ ⟨11, 2, 0, 1261478, 91913, 3673, 262144⟩
    (by decide) selected_cut_45464

theorem selected_cut_45465 : selected 10 ⟨1261586, by decide⟩
    (prefixPartial 11 91914) = some ⟨11, 2, 0, 1261586, 91914, 3517, 262144⟩ := by
  decide +kernel

theorem context_11_91914_1261586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91914 ⟨1261586, by decide⟩ :=
  accepted_of_selected 11 91914 ⟨1261586, by decide⟩ ⟨11, 2, 0, 1261586, 91914, 3517, 262144⟩
    (by decide) selected_cut_45465

theorem selected_cut_45466 : selected 9 ⟨1261633, by decide⟩
    (prefixPartial 12 367660) = some ⟨12, 2, 0, 1261633, 367660, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_367660_1261633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367660 ⟨1261633, by decide⟩ :=
  accepted_of_selected 12 367660 ⟨1261633, by decide⟩ ⟨12, 2, 0, 1261633, 367660, 1617, 65536⟩
    (by decide) selected_cut_45466

theorem selected_cut_45467 : selected 9 ⟨1261681, by decide⟩
    (prefixPartial 12 367661) = some ⟨12, 2, 0, 1261681, 367661, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_367661_1261681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367661 ⟨1261681, by decide⟩ :=
  accepted_of_selected 12 367661 ⟨1261681, by decide⟩ ⟨12, 2, 0, 1261681, 367661, 1713, 65536⟩
    (by decide) selected_cut_45467

theorem selected_cut_45468 : selected 9 ⟨1261725, by decide⟩
    (prefixPartial 12 367662) = some ⟨12, 2, 0, 1261725, 367662, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_367662_1261725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367662 ⟨1261725, by decide⟩ :=
  accepted_of_selected 12 367662 ⟨1261725, by decide⟩ ⟨12, 2, 0, 1261725, 367662, 1673, 65536⟩
    (by decide) selected_cut_45468

theorem selected_cut_45469 : selected 9 ⟨1261763, by decide⟩
    (prefixPartial 12 367663) = some ⟨12, 2, 0, 1261763, 367663, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_367663_1261763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367663 ⟨1261763, by decide⟩ :=
  accepted_of_selected 12 367663 ⟨1261763, by decide⟩ ⟨12, 2, 0, 1261763, 367663, 1437, 65536⟩
    (by decide) selected_cut_45469

theorem unmarked_context_11_91915_1261764 : frontier 10 ⟨1261764, by decide⟩
    (prefixCache 11 91915) (prefixPartial 11 91915) = false := by
  decide +kernel

theorem node_context_11_91915_1261764 : EJMOriginalGlobalDAGData.nodes 10 ⟨1261764, by decide⟩ =
    .split (coordinate 11) (![⟨1261633, by decide⟩,⟨1261681, by decide⟩,⟨1261725, by decide⟩,⟨1261763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91915_1261764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91915 ⟨1261764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91915
    ⟨1261764, by decide⟩ (by decide) (![⟨1261633, by decide⟩,⟨1261681, by decide⟩,⟨1261725, by decide⟩,⟨1261763, by decide⟩]) unmarked_context_11_91915_1261764 node_context_11_91915_1261764
  intro a
  fin_cases a
  · exact context_12_367660_1261633
  · exact context_12_367661_1261681
  · exact context_12_367662_1261725
  · exact context_12_367663_1261763

theorem unmarked_context_10_22978_1261765 : frontier 11 ⟨1261765, by decide⟩
    (prefixCache 10 22978) (prefixPartial 10 22978) = false := by
  decide +kernel

theorem node_context_10_22978_1261765 : EJMOriginalGlobalDAGData.nodes 11 ⟨1261765, by decide⟩ =
    .split (coordinate 10) (![⟨1261338, by decide⟩,⟨1261478, by decide⟩,⟨1261586, by decide⟩,⟨1261764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22978_1261765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22978 ⟨1261765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22978
    ⟨1261765, by decide⟩ (by decide) (![⟨1261338, by decide⟩,⟨1261478, by decide⟩,⟨1261586, by decide⟩,⟨1261764, by decide⟩]) unmarked_context_10_22978_1261765 node_context_10_22978_1261765
  intro a
  fin_cases a
  · exact context_11_91912_1261338
  · exact context_11_91913_1261478
  · exact context_11_91914_1261586
  · exact context_11_91915_1261764

theorem selected_cut_45470 : selected 10 ⟨1261903, by decide⟩
    (prefixPartial 11 91916) = some ⟨11, 2, 0, 1261903, 91916, 2549, 262144⟩ := by
  decide +kernel

theorem context_11_91916_1261903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91916 ⟨1261903, by decide⟩ :=
  accepted_of_selected 11 91916 ⟨1261903, by decide⟩ ⟨11, 2, 0, 1261903, 91916, 2549, 262144⟩
    (by decide) selected_cut_45470

theorem selected_cut_45471 : selected 10 ⟨1261961, by decide⟩
    (prefixPartial 11 91917) = some ⟨11, 2, 0, 1261961, 91917, 777, 262144⟩ := by
  decide +kernel

theorem context_11_91917_1261961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91917 ⟨1261961, by decide⟩ :=
  accepted_of_selected 11 91917 ⟨1261961, by decide⟩ ⟨11, 2, 0, 1261961, 91917, 777, 262144⟩
    (by decide) selected_cut_45471

theorem selected_cut_45472 : selected 10 ⟨1262002, by decide⟩
    (prefixPartial 11 91918) = some ⟨11, 2, 0, 1262002, 91918, 1109, 262144⟩ := by
  decide +kernel

theorem context_11_91918_1262002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91918 ⟨1262002, by decide⟩ :=
  accepted_of_selected 11 91918 ⟨1262002, by decide⟩ ⟨11, 2, 0, 1262002, 91918, 1109, 262144⟩
    (by decide) selected_cut_45472

theorem selected_cut_45473 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 91919) = some ⟨11, 1, 0, 977886, 91919, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91919_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91919 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 91919 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 91919, 1, 262144⟩
    (by decide) selected_cut_45473

theorem unmarked_context_10_22979_1262003 : frontier 11 ⟨1262003, by decide⟩
    (prefixCache 10 22979) (prefixPartial 10 22979) = false := by
  decide +kernel

theorem node_context_10_22979_1262003 : EJMOriginalGlobalDAGData.nodes 11 ⟨1262003, by decide⟩ =
    .split (coordinate 10) (![⟨1261903, by decide⟩,⟨1261961, by decide⟩,⟨1262002, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22979_1262003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22979 ⟨1262003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22979
    ⟨1262003, by decide⟩ (by decide) (![⟨1261903, by decide⟩,⟨1261961, by decide⟩,⟨1262002, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22979_1262003 node_context_10_22979_1262003
  intro a
  fin_cases a
  · exact context_11_91916_1261903
  · exact context_11_91917_1261961
  · exact context_11_91918_1262002
  · exact context_11_91919_977886

theorem unmarked_context_9_5744_1262004 : frontier 12 ⟨1262004, by decide⟩
    (prefixCache 9 5744) (prefixPartial 9 5744) = false := by
  decide +kernel

theorem node_context_9_5744_1262004 : EJMOriginalGlobalDAGData.nodes 12 ⟨1262004, by decide⟩ =
    .split (coordinate 9) (![⟨1260386, by decide⟩,⟨1261200, by decide⟩,⟨1261765, by decide⟩,⟨1262003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5744_1262004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5744 ⟨1262004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5744
    ⟨1262004, by decide⟩ (by decide) (![⟨1260386, by decide⟩,⟨1261200, by decide⟩,⟨1261765, by decide⟩,⟨1262003, by decide⟩]) unmarked_context_9_5744_1262004 node_context_9_5744_1262004
  intro a
  fin_cases a
  · exact context_10_22976_1260386
  · exact context_10_22977_1261200
  · exact context_10_22978_1261765
  · exact context_10_22979_1262003

theorem selected_cut_45474 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 22980) = some ⟨10, 1, 0, 793297, 22980, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22980_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22980 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 22980 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 22980, 1, 1048576⟩
    (by decide) selected_cut_45474

theorem selected_cut_45475 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22981) = some ⟨10, 1, 0, 893098, 22981, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22981_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22981 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22981 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22981, 1, 1048576⟩
    (by decide) selected_cut_45475

theorem selected_cut_45476 : selected 11 ⟨1262267, by decide⟩
    (prefixPartial 10 22982) = some ⟨10, 2, 0, 1262267, 22982, 3829, 1048576⟩ := by
  decide +kernel

theorem context_10_22982_1262267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22982 ⟨1262267, by decide⟩ :=
  accepted_of_selected 10 22982 ⟨1262267, by decide⟩ ⟨10, 2, 0, 1262267, 22982, 3829, 1048576⟩
    (by decide) selected_cut_45476

theorem selected_cut_45477 : selected 11 ⟨1262348, by decide⟩
    (prefixPartial 10 22983) = some ⟨10, 2, 0, 1262348, 22983, 729, 1048576⟩ := by
  decide +kernel

theorem context_10_22983_1262348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22983 ⟨1262348, by decide⟩ :=
  accepted_of_selected 10 22983 ⟨1262348, by decide⟩ ⟨10, 2, 0, 1262348, 22983, 729, 1048576⟩
    (by decide) selected_cut_45477

theorem unmarked_context_9_5745_1262349 : frontier 12 ⟨1262349, by decide⟩
    (prefixCache 9 5745) (prefixPartial 9 5745) = false := by
  decide +kernel

theorem node_context_9_5745_1262349 : EJMOriginalGlobalDAGData.nodes 12 ⟨1262349, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1262267, by decide⟩,⟨1262348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5745_1262349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5745 ⟨1262349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5745
    ⟨1262349, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1262267, by decide⟩,⟨1262348, by decide⟩]) unmarked_context_9_5745_1262349 node_context_9_5745_1262349
  intro a
  fin_cases a
  · exact context_10_22980_793297
  · exact context_10_22981_893098
  · exact context_10_22982_1262267
  · exact context_10_22983_1262348

theorem selected_cut_45478 : selected 12 ⟨1262376, by decide⟩
    (prefixPartial 9 5746) = some ⟨9, 2, 0, 1262376, 5746, 169, 4194304⟩ := by
  decide +kernel

theorem context_9_5746_1262376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5746 ⟨1262376, by decide⟩ :=
  accepted_of_selected 9 5746 ⟨1262376, by decide⟩ ⟨9, 2, 0, 1262376, 5746, 169, 4194304⟩
    (by decide) selected_cut_45478

theorem selected_cut_45479 : selected 12 ⟨1262379, by decide⟩
    (prefixPartial 9 5747) = some ⟨9, 2, 0, 1262379, 5747, 17, 4194304⟩ := by
  decide +kernel

theorem context_9_5747_1262379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5747 ⟨1262379, by decide⟩ :=
  accepted_of_selected 9 5747 ⟨1262379, by decide⟩ ⟨9, 2, 0, 1262379, 5747, 17, 4194304⟩
    (by decide) selected_cut_45479

theorem unmarked_context_8_1436_1262380 : frontier 13 ⟨1262380, by decide⟩
    (prefixCache 8 1436) (prefixPartial 8 1436) = false := by
  decide +kernel

theorem node_context_8_1436_1262380 : EJMOriginalGlobalDAGData.nodes 13 ⟨1262380, by decide⟩ =
    .split (coordinate 8) (![⟨1262004, by decide⟩,⟨1262349, by decide⟩,⟨1262376, by decide⟩,⟨1262379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1436_1262380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1436 ⟨1262380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1436
    ⟨1262380, by decide⟩ (by decide) (![⟨1262004, by decide⟩,⟨1262349, by decide⟩,⟨1262376, by decide⟩,⟨1262379, by decide⟩]) unmarked_context_8_1436_1262380 node_context_8_1436_1262380
  intro a
  fin_cases a
  · exact context_9_5744_1262004
  · exact context_9_5745_1262349
  · exact context_9_5746_1262376
  · exact context_9_5747_1262379

theorem selected_cut_45480 : selected 13 ⟨1109534, by decide⟩
    (prefixPartial 8 1437) = some ⟨8, 1, 0, 1109534, 1437, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1437_1109534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1437 ⟨1109534, by decide⟩ :=
  accepted_of_selected 8 1437 ⟨1109534, by decide⟩ ⟨8, 1, 0, 1109534, 1437, 1, 16777216⟩
    (by decide) selected_cut_45480

theorem selected_cut_45481 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92032) = some ⟨11, 1, 0, 434745, 92032, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92032_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92032 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92032 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92032, 1, 262144⟩
    (by decide) selected_cut_45481

theorem selected_cut_45482 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 368132) = some ⟨12, 1, 0, 448748, 368132, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368132_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368132 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 368132 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 368132, 1, 65536⟩
    (by decide) selected_cut_45482

theorem selected_cut_45483 : selected 8 ⟨1262452, by decide⟩
    (prefixPartial 13 1472532) = some ⟨13, 2, 0, 1262452, 1472532, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_1472532_1262452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472532 ⟨1262452, by decide⟩ :=
  accepted_of_selected 13 1472532 ⟨1262452, by decide⟩ ⟨13, 2, 0, 1262452, 1472532, 2409, 16384⟩
    (by decide) selected_cut_45483

theorem selected_cut_45484 : selected 8 ⟨1262487, by decide⟩
    (prefixPartial 13 1472533) = some ⟨13, 2, 0, 1262487, 1472533, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_1472533_1262487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472533 ⟨1262487, by decide⟩ :=
  accepted_of_selected 13 1472533 ⟨1262487, by decide⟩ ⟨13, 2, 0, 1262487, 1472533, 1321, 16384⟩
    (by decide) selected_cut_45484

theorem selected_cut_45485 : selected 8 ⟨1262507, by decide⟩
    (prefixPartial 13 1472534) = some ⟨13, 2, 0, 1262507, 1472534, 937, 16384⟩ := by
  decide +kernel

theorem context_13_1472534_1262507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472534 ⟨1262507, by decide⟩ :=
  accepted_of_selected 13 1472534 ⟨1262507, by decide⟩ ⟨13, 2, 0, 1262507, 1472534, 937, 16384⟩
    (by decide) selected_cut_45485

theorem selected_cut_45486 : selected 8 ⟨1262528, by decide⟩
    (prefixPartial 13 1472535) = some ⟨13, 2, 0, 1262528, 1472535, 665, 16384⟩ := by
  decide +kernel

theorem context_13_1472535_1262528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472535 ⟨1262528, by decide⟩ :=
  accepted_of_selected 13 1472535 ⟨1262528, by decide⟩ ⟨13, 2, 0, 1262528, 1472535, 665, 16384⟩
    (by decide) selected_cut_45486

theorem unmarked_context_12_368133_1262529 : frontier 9 ⟨1262529, by decide⟩
    (prefixCache 12 368133) (prefixPartial 12 368133) = false := by
  decide +kernel

theorem node_context_12_368133_1262529 : EJMOriginalGlobalDAGData.nodes 9 ⟨1262529, by decide⟩ =
    .split (coordinate 12) (![⟨1262452, by decide⟩,⟨1262487, by decide⟩,⟨1262507, by decide⟩,⟨1262528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_368133_1262529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368133 ⟨1262529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 368133
    ⟨1262529, by decide⟩ (by decide) (![⟨1262452, by decide⟩,⟨1262487, by decide⟩,⟨1262507, by decide⟩,⟨1262528, by decide⟩]) unmarked_context_12_368133_1262529 node_context_12_368133_1262529
  intro a
  fin_cases a
  · exact context_13_1472532_1262452
  · exact context_13_1472533_1262487
  · exact context_13_1472534_1262507
  · exact context_13_1472535_1262528

theorem selected_cut_45487 : selected 8 ⟨1262576, by decide⟩
    (prefixPartial 13 1472536) = some ⟨13, 2, 0, 1262576, 1472536, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_1472536_1262576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472536 ⟨1262576, by decide⟩ :=
  accepted_of_selected 13 1472536 ⟨1262576, by decide⟩ ⟨13, 2, 0, 1262576, 1472536, 1729, 16384⟩
    (by decide) selected_cut_45487

theorem selected_cut_45488 : selected 8 ⟨1262596, by decide⟩
    (prefixPartial 13 1472537) = some ⟨13, 2, 0, 1262596, 1472537, 961, 16384⟩ := by
  decide +kernel

theorem context_13_1472537_1262596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472537 ⟨1262596, by decide⟩ :=
  accepted_of_selected 13 1472537 ⟨1262596, by decide⟩ ⟨13, 2, 0, 1262596, 1472537, 961, 16384⟩
    (by decide) selected_cut_45488

theorem selected_cut_45489 : selected 8 ⟨1262615, by decide⟩
    (prefixPartial 13 1472538) = some ⟨13, 2, 0, 1262615, 1472538, 761, 16384⟩ := by
  decide +kernel

theorem context_13_1472538_1262615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472538 ⟨1262615, by decide⟩ :=
  accepted_of_selected 13 1472538 ⟨1262615, by decide⟩ ⟨13, 2, 0, 1262615, 1472538, 761, 16384⟩
    (by decide) selected_cut_45489

theorem selected_cut_45490 : selected 8 ⟨1262627, by decide⟩
    (prefixPartial 13 1472539) = some ⟨13, 2, 0, 1262627, 1472539, 657, 16384⟩ := by
  decide +kernel

theorem context_13_1472539_1262627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472539 ⟨1262627, by decide⟩ :=
  accepted_of_selected 13 1472539 ⟨1262627, by decide⟩ ⟨13, 2, 0, 1262627, 1472539, 657, 16384⟩
    (by decide) selected_cut_45490

theorem unmarked_context_12_368134_1262628 : frontier 9 ⟨1262628, by decide⟩
    (prefixCache 12 368134) (prefixPartial 12 368134) = false := by
  decide +kernel

theorem node_context_12_368134_1262628 : EJMOriginalGlobalDAGData.nodes 9 ⟨1262628, by decide⟩ =
    .split (coordinate 12) (![⟨1262576, by decide⟩,⟨1262596, by decide⟩,⟨1262615, by decide⟩,⟨1262627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_368134_1262628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368134 ⟨1262628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 368134
    ⟨1262628, by decide⟩ (by decide) (![⟨1262576, by decide⟩,⟨1262596, by decide⟩,⟨1262615, by decide⟩,⟨1262627, by decide⟩]) unmarked_context_12_368134_1262628 node_context_12_368134_1262628
  intro a
  fin_cases a
  · exact context_13_1472536_1262576
  · exact context_13_1472537_1262596
  · exact context_13_1472538_1262615
  · exact context_13_1472539_1262627

theorem selected_cut_45491 : selected 8 ⟨1262674, by decide⟩
    (prefixPartial 13 1472540) = some ⟨13, 2, 0, 1262674, 1472540, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_1472540_1262674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472540 ⟨1262674, by decide⟩ :=
  accepted_of_selected 13 1472540 ⟨1262674, by decide⟩ ⟨13, 2, 0, 1262674, 1472540, 2009, 16384⟩
    (by decide) selected_cut_45491

theorem selected_cut_45492 : selected 8 ⟨1262696, by decide⟩
    (prefixPartial 13 1472541) = some ⟨13, 2, 0, 1262696, 1472541, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_1472541_1262696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472541 ⟨1262696, by decide⟩ :=
  accepted_of_selected 13 1472541 ⟨1262696, by decide⟩ ⟨13, 2, 0, 1262696, 1472541, 1065, 16384⟩
    (by decide) selected_cut_45492

theorem selected_cut_45493 : selected 8 ⟨1262714, by decide⟩
    (prefixPartial 13 1472542) = some ⟨13, 2, 0, 1262714, 1472542, 793, 16384⟩ := by
  decide +kernel

theorem context_13_1472542_1262714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472542 ⟨1262714, by decide⟩ :=
  accepted_of_selected 13 1472542 ⟨1262714, by decide⟩ ⟨13, 2, 0, 1262714, 1472542, 793, 16384⟩
    (by decide) selected_cut_45493

theorem selected_cut_45494 : selected 8 ⟨1262724, by decide⟩
    (prefixPartial 13 1472543) = some ⟨13, 2, 0, 1262724, 1472543, 685, 16384⟩ := by
  decide +kernel

theorem context_13_1472543_1262724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472543 ⟨1262724, by decide⟩ :=
  accepted_of_selected 13 1472543 ⟨1262724, by decide⟩ ⟨13, 2, 0, 1262724, 1472543, 685, 16384⟩
    (by decide) selected_cut_45494

theorem unmarked_context_12_368135_1262725 : frontier 9 ⟨1262725, by decide⟩
    (prefixCache 12 368135) (prefixPartial 12 368135) = false := by
  decide +kernel

theorem node_context_12_368135_1262725 : EJMOriginalGlobalDAGData.nodes 9 ⟨1262725, by decide⟩ =
    .split (coordinate 12) (![⟨1262674, by decide⟩,⟨1262696, by decide⟩,⟨1262714, by decide⟩,⟨1262724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_368135_1262725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368135 ⟨1262725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 368135
    ⟨1262725, by decide⟩ (by decide) (![⟨1262674, by decide⟩,⟨1262696, by decide⟩,⟨1262714, by decide⟩,⟨1262724, by decide⟩]) unmarked_context_12_368135_1262725 node_context_12_368135_1262725
  intro a
  fin_cases a
  · exact context_13_1472540_1262674
  · exact context_13_1472541_1262696
  · exact context_13_1472542_1262714
  · exact context_13_1472543_1262724

theorem unmarked_context_11_92033_1262726 : frontier 10 ⟨1262726, by decide⟩
    (prefixCache 11 92033) (prefixPartial 11 92033) = false := by
  decide +kernel

theorem node_context_11_92033_1262726 : EJMOriginalGlobalDAGData.nodes 10 ⟨1262726, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1262529, by decide⟩,⟨1262628, by decide⟩,⟨1262725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92033_1262726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92033 ⟨1262726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92033
    ⟨1262726, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1262529, by decide⟩,⟨1262628, by decide⟩,⟨1262725, by decide⟩]) unmarked_context_11_92033_1262726 node_context_11_92033_1262726
  intro a
  fin_cases a
  · exact context_12_368132_448748
  · exact context_12_368133_1262529
  · exact context_12_368134_1262628
  · exact context_12_368135_1262725

theorem selected_cut_45495 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 368136) = some ⟨12, 1, 0, 448748, 368136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368136_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368136 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 368136 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 368136, 1, 65536⟩
    (by decide) selected_cut_45495

theorem selected_cut_45496 : selected 8 ⟨1262761, by decide⟩
    (prefixPartial 13 1472548) = some ⟨13, 2, 0, 1262761, 1472548, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_1472548_1262761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472548 ⟨1262761, by decide⟩ :=
  accepted_of_selected 13 1472548 ⟨1262761, by decide⟩ ⟨13, 2, 0, 1262761, 1472548, 1841, 16384⟩
    (by decide) selected_cut_45496

theorem selected_cut_45497 : selected 8 ⟨1262785, by decide⟩
    (prefixPartial 13 1472549) = some ⟨13, 2, 0, 1262785, 1472549, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1472549_1262785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472549 ⟨1262785, by decide⟩ :=
  accepted_of_selected 13 1472549 ⟨1262785, by decide⟩ ⟨13, 2, 0, 1262785, 1472549, 1113, 16384⟩
    (by decide) selected_cut_45497

theorem selected_cut_45498 : selected 8 ⟨1262799, by decide⟩
    (prefixPartial 13 1472550) = some ⟨13, 2, 0, 1262799, 1472550, 713, 16384⟩ := by
  decide +kernel

theorem context_13_1472550_1262799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472550 ⟨1262799, by decide⟩ :=
  accepted_of_selected 13 1472550 ⟨1262799, by decide⟩ ⟨13, 2, 0, 1262799, 1472550, 713, 16384⟩
    (by decide) selected_cut_45498

theorem selected_cut_45499 : selected 8 ⟨1262808, by decide⟩
    (prefixPartial 13 1472551) = some ⟨13, 2, 0, 1262808, 1472551, 533, 16384⟩ := by
  decide +kernel

theorem context_13_1472551_1262808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472551 ⟨1262808, by decide⟩ :=
  accepted_of_selected 13 1472551 ⟨1262808, by decide⟩ ⟨13, 2, 0, 1262808, 1472551, 533, 16384⟩
    (by decide) selected_cut_45499

theorem unmarked_context_12_368137_1262809 : frontier 9 ⟨1262809, by decide⟩
    (prefixCache 12 368137) (prefixPartial 12 368137) = false := by
  decide +kernel

theorem node_context_12_368137_1262809 : EJMOriginalGlobalDAGData.nodes 9 ⟨1262809, by decide⟩ =
    .split (coordinate 12) (![⟨1262761, by decide⟩,⟨1262785, by decide⟩,⟨1262799, by decide⟩,⟨1262808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_368137_1262809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368137 ⟨1262809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 368137
    ⟨1262809, by decide⟩ (by decide) (![⟨1262761, by decide⟩,⟨1262785, by decide⟩,⟨1262799, by decide⟩,⟨1262808, by decide⟩]) unmarked_context_12_368137_1262809 node_context_12_368137_1262809
  intro a
  fin_cases a
  · exact context_13_1472548_1262761
  · exact context_13_1472549_1262785
  · exact context_13_1472550_1262799
  · exact context_13_1472551_1262808

theorem selected_cut_45500 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 368138) = some ⟨12, 1, 0, 893903, 368138, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368138_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368138 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 368138 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 368138, 1, 65536⟩
    (by decide) selected_cut_45500

theorem selected_cut_45501 : selected 8 ⟨1262844, by decide⟩
    (prefixPartial 13 1472556) = some ⟨13, 2, 0, 1262844, 1472556, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_1472556_1262844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472556 ⟨1262844, by decide⟩ :=
  accepted_of_selected 13 1472556 ⟨1262844, by decide⟩ ⟨13, 2, 0, 1262844, 1472556, 1849, 16384⟩
    (by decide) selected_cut_45501

theorem selected_cut_45502 : selected 8 ⟨1262871, by decide⟩
    (prefixPartial 13 1472557) = some ⟨13, 2, 0, 1262871, 1472557, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_1472557_1262871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472557 ⟨1262871, by decide⟩ :=
  accepted_of_selected 13 1472557 ⟨1262871, by decide⟩ ⟨13, 2, 0, 1262871, 1472557, 1237, 16384⟩
    (by decide) selected_cut_45502

theorem selected_cut_45503 : selected 8 ⟨1262886, by decide⟩
    (prefixPartial 13 1472558) = some ⟨13, 2, 0, 1262886, 1472558, 861, 16384⟩ := by
  decide +kernel

theorem context_13_1472558_1262886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472558 ⟨1262886, by decide⟩ :=
  accepted_of_selected 13 1472558 ⟨1262886, by decide⟩ ⟨13, 2, 0, 1262886, 1472558, 861, 16384⟩
    (by decide) selected_cut_45503

theorem selected_cut_45504 : selected 8 ⟨1262896, by decide⟩
    (prefixPartial 13 1472559) = some ⟨13, 2, 0, 1262896, 1472559, 649, 16384⟩ := by
  decide +kernel

theorem context_13_1472559_1262896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472559 ⟨1262896, by decide⟩ :=
  accepted_of_selected 13 1472559 ⟨1262896, by decide⟩ ⟨13, 2, 0, 1262896, 1472559, 649, 16384⟩
    (by decide) selected_cut_45504

theorem unmarked_context_12_368139_1262897 : frontier 9 ⟨1262897, by decide⟩
    (prefixCache 12 368139) (prefixPartial 12 368139) = false := by
  decide +kernel

theorem node_context_12_368139_1262897 : EJMOriginalGlobalDAGData.nodes 9 ⟨1262897, by decide⟩ =
    .split (coordinate 12) (![⟨1262844, by decide⟩,⟨1262871, by decide⟩,⟨1262886, by decide⟩,⟨1262896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_368139_1262897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368139 ⟨1262897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 368139
    ⟨1262897, by decide⟩ (by decide) (![⟨1262844, by decide⟩,⟨1262871, by decide⟩,⟨1262886, by decide⟩,⟨1262896, by decide⟩]) unmarked_context_12_368139_1262897 node_context_12_368139_1262897
  intro a
  fin_cases a
  · exact context_13_1472556_1262844
  · exact context_13_1472557_1262871
  · exact context_13_1472558_1262886
  · exact context_13_1472559_1262896

theorem unmarked_context_11_92034_1262898 : frontier 10 ⟨1262898, by decide⟩
    (prefixCache 11 92034) (prefixPartial 11 92034) = false := by
  decide +kernel

theorem node_context_11_92034_1262898 : EJMOriginalGlobalDAGData.nodes 10 ⟨1262898, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1262809, by decide⟩,⟨893903, by decide⟩,⟨1262897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92034_1262898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92034 ⟨1262898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92034
    ⟨1262898, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1262809, by decide⟩,⟨893903, by decide⟩,⟨1262897, by decide⟩]) unmarked_context_11_92034_1262898 node_context_11_92034_1262898
  intro a
  fin_cases a
  · exact context_12_368136_448748
  · exact context_12_368137_1262809
  · exact context_12_368138_893903
  · exact context_12_368139_1262897

theorem selected_cut_45505 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 368140) = some ⟨12, 1, 0, 448748, 368140, 1, 65536⟩ := by
  decide +kernel

theorem context_12_368140_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 368140 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 368140 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 368140, 1, 65536⟩
    (by decide) selected_cut_45505

theorem selected_cut_45506 : selected 8 ⟨1262933, by decide⟩
    (prefixPartial 13 1472564) = some ⟨13, 2, 0, 1262933, 1472564, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_1472564_1262933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472564 ⟨1262933, by decide⟩ :=
  accepted_of_selected 13 1472564 ⟨1262933, by decide⟩ ⟨13, 2, 0, 1262933, 1472564, 1709, 16384⟩
    (by decide) selected_cut_45506

theorem selected_cut_45507 : selected 8 ⟨1262955, by decide⟩
    (prefixPartial 13 1472565) = some ⟨13, 2, 0, 1262955, 1472565, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_1472565_1262955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1472565 ⟨1262955, by decide⟩ :=
  accepted_of_selected 13 1472565 ⟨1262955, by decide⟩ ⟨13, 2, 0, 1262955, 1472565, 1017, 16384⟩
    (by decide) selected_cut_45507

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
