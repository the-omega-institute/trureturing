/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover390
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_9_4685_1004072 : frontier 12 ⟨1004072, by decide⟩
    (prefixCache 9 4685) (prefixPartial 9 4685) = false := by
  decide +kernel

theorem node_context_9_4685_1004072 : EJMOriginalGlobalDAGData.nodes 12 ⟨1004072, by decide⟩ =
    .split (coordinate 9) (![⟨1003182, by decide⟩,⟨893098, by decide⟩,⟨1003653, by decide⟩,⟨1004071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4685_1004072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4685 ⟨1004072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4685
    ⟨1004072, by decide⟩ (by decide) (![⟨1003182, by decide⟩,⟨893098, by decide⟩,⟨1003653, by decide⟩,⟨1004071, by decide⟩]) unmarked_context_9_4685_1004072 node_context_9_4685_1004072
  intro a
  fin_cases a
  · exact context_10_18740_1003182
  · exact context_10_18741_893098
  · exact context_10_18742_1003653
  · exact context_10_18743_1004071

theorem selected_cut_37539 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74976) = some ⟨11, 1, 0, 907917, 74976, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74976_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74976 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74976 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74976, 1, 262144⟩
    (by decide) selected_cut_37539

theorem selected_cut_37540 : selected 10 ⟨1004148, by decide⟩
    (prefixPartial 11 74977) = some ⟨11, 2, 0, 1004148, 74977, 3829, 262144⟩ := by
  decide +kernel

theorem context_11_74977_1004148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74977 ⟨1004148, by decide⟩ :=
  accepted_of_selected 11 74977 ⟨1004148, by decide⟩ ⟨11, 2, 0, 1004148, 74977, 3829, 262144⟩
    (by decide) selected_cut_37540

theorem selected_cut_37541 : selected 10 ⟨1004211, by decide⟩
    (prefixPartial 11 74978) = some ⟨11, 2, 0, 1004211, 74978, 3929, 262144⟩ := by
  decide +kernel

theorem context_11_74978_1004211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74978 ⟨1004211, by decide⟩ :=
  accepted_of_selected 11 74978 ⟨1004211, by decide⟩ ⟨11, 2, 0, 1004211, 74978, 3929, 262144⟩
    (by decide) selected_cut_37541

theorem selected_cut_37542 : selected 10 ⟨1004244, by decide⟩
    (prefixPartial 11 74979) = some ⟨11, 2, 0, 1004244, 74979, 2297, 262144⟩ := by
  decide +kernel

theorem context_11_74979_1004244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74979 ⟨1004244, by decide⟩ :=
  accepted_of_selected 11 74979 ⟨1004244, by decide⟩ ⟨11, 2, 0, 1004244, 74979, 2297, 262144⟩
    (by decide) selected_cut_37542

theorem unmarked_context_10_18744_1004245 : frontier 11 ⟨1004245, by decide⟩
    (prefixCache 10 18744) (prefixPartial 10 18744) = false := by
  decide +kernel

theorem node_context_10_18744_1004245 : EJMOriginalGlobalDAGData.nodes 11 ⟨1004245, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1004148, by decide⟩,⟨1004211, by decide⟩,⟨1004244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18744_1004245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18744 ⟨1004245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18744
    ⟨1004245, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1004148, by decide⟩,⟨1004211, by decide⟩,⟨1004244, by decide⟩]) unmarked_context_10_18744_1004245 node_context_10_18744_1004245
  intro a
  fin_cases a
  · exact context_11_74976_907917
  · exact context_11_74977_1004148
  · exact context_11_74978_1004211
  · exact context_11_74979_1004244

theorem selected_cut_37543 : selected 10 ⟨1004289, by decide⟩
    (prefixPartial 11 74980) = some ⟨11, 2, 0, 1004289, 74980, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_74980_1004289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74980 ⟨1004289, by decide⟩ :=
  accepted_of_selected 11 74980 ⟨1004289, by decide⟩ ⟨11, 2, 0, 1004289, 74980, 2917, 262144⟩
    (by decide) selected_cut_37543

theorem selected_cut_37544 : selected 10 ⟨1004336, by decide⟩
    (prefixPartial 11 74981) = some ⟨11, 2, 0, 1004336, 74981, 2745, 262144⟩ := by
  decide +kernel

theorem context_11_74981_1004336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74981 ⟨1004336, by decide⟩ :=
  accepted_of_selected 11 74981 ⟨1004336, by decide⟩ ⟨11, 2, 0, 1004336, 74981, 2745, 262144⟩
    (by decide) selected_cut_37544

theorem selected_cut_37545 : selected 10 ⟨1004375, by decide⟩
    (prefixPartial 11 74982) = some ⟨11, 2, 0, 1004375, 74982, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_74982_1004375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74982 ⟨1004375, by decide⟩ :=
  accepted_of_selected 11 74982 ⟨1004375, by decide⟩ ⟨11, 2, 0, 1004375, 74982, 3025, 262144⟩
    (by decide) selected_cut_37545

theorem selected_cut_37546 : selected 10 ⟨1004407, by decide⟩
    (prefixPartial 11 74983) = some ⟨11, 2, 0, 1004407, 74983, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_74983_1004407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74983 ⟨1004407, by decide⟩ :=
  accepted_of_selected 11 74983 ⟨1004407, by decide⟩ ⟨11, 2, 0, 1004407, 74983, 1981, 262144⟩
    (by decide) selected_cut_37546

theorem unmarked_context_10_18745_1004408 : frontier 11 ⟨1004408, by decide⟩
    (prefixCache 10 18745) (prefixPartial 10 18745) = false := by
  decide +kernel

theorem node_context_10_18745_1004408 : EJMOriginalGlobalDAGData.nodes 11 ⟨1004408, by decide⟩ =
    .split (coordinate 10) (![⟨1004289, by decide⟩,⟨1004336, by decide⟩,⟨1004375, by decide⟩,⟨1004407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18745_1004408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18745 ⟨1004408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18745
    ⟨1004408, by decide⟩ (by decide) (![⟨1004289, by decide⟩,⟨1004336, by decide⟩,⟨1004375, by decide⟩,⟨1004407, by decide⟩]) unmarked_context_10_18745_1004408 node_context_10_18745_1004408
  intro a
  fin_cases a
  · exact context_11_74980_1004289
  · exact context_11_74981_1004336
  · exact context_11_74982_1004375
  · exact context_11_74983_1004407

theorem selected_cut_37547 : selected 10 ⟨1004440, by decide⟩
    (prefixPartial 11 74984) = some ⟨11, 2, 0, 1004440, 74984, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_74984_1004440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74984 ⟨1004440, by decide⟩ :=
  accepted_of_selected 11 74984 ⟨1004440, by decide⟩ ⟨11, 2, 0, 1004440, 74984, 2361, 262144⟩
    (by decide) selected_cut_37547

theorem selected_cut_37548 : selected 10 ⟨1004470, by decide⟩
    (prefixPartial 11 74985) = some ⟨11, 2, 0, 1004470, 74985, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_74985_1004470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74985 ⟨1004470, by decide⟩ :=
  accepted_of_selected 11 74985 ⟨1004470, by decide⟩ ⟨11, 2, 0, 1004470, 74985, 2253, 262144⟩
    (by decide) selected_cut_37548

theorem selected_cut_37549 : selected 10 ⟨1004497, by decide⟩
    (prefixPartial 11 74986) = some ⟨11, 2, 0, 1004497, 74986, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_74986_1004497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74986 ⟨1004497, by decide⟩ :=
  accepted_of_selected 11 74986 ⟨1004497, by decide⟩ ⟨11, 2, 0, 1004497, 74986, 1857, 262144⟩
    (by decide) selected_cut_37549

theorem selected_cut_37550 : selected 10 ⟨1004520, by decide⟩
    (prefixPartial 11 74987) = some ⟨11, 2, 0, 1004520, 74987, 1553, 262144⟩ := by
  decide +kernel

theorem context_11_74987_1004520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74987 ⟨1004520, by decide⟩ :=
  accepted_of_selected 11 74987 ⟨1004520, by decide⟩ ⟨11, 2, 0, 1004520, 74987, 1553, 262144⟩
    (by decide) selected_cut_37550

theorem unmarked_context_10_18746_1004521 : frontier 11 ⟨1004521, by decide⟩
    (prefixCache 10 18746) (prefixPartial 10 18746) = false := by
  decide +kernel

theorem node_context_10_18746_1004521 : EJMOriginalGlobalDAGData.nodes 11 ⟨1004521, by decide⟩ =
    .split (coordinate 10) (![⟨1004440, by decide⟩,⟨1004470, by decide⟩,⟨1004497, by decide⟩,⟨1004520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18746_1004521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18746 ⟨1004521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18746
    ⟨1004521, by decide⟩ (by decide) (![⟨1004440, by decide⟩,⟨1004470, by decide⟩,⟨1004497, by decide⟩,⟨1004520, by decide⟩]) unmarked_context_10_18746_1004521 node_context_10_18746_1004521
  intro a
  fin_cases a
  · exact context_11_74984_1004440
  · exact context_11_74985_1004470
  · exact context_11_74986_1004497
  · exact context_11_74987_1004520

theorem selected_cut_37551 : selected 10 ⟨1004555, by decide⟩
    (prefixPartial 11 74988) = some ⟨11, 2, 0, 1004555, 74988, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_74988_1004555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74988 ⟨1004555, by decide⟩ :=
  accepted_of_selected 11 74988 ⟨1004555, by decide⟩ ⟨11, 2, 0, 1004555, 74988, 2125, 262144⟩
    (by decide) selected_cut_37551

theorem selected_cut_37552 : selected 10 ⟨1004584, by decide⟩
    (prefixPartial 11 74989) = some ⟨11, 2, 0, 1004584, 74989, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_74989_1004584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74989 ⟨1004584, by decide⟩ :=
  accepted_of_selected 11 74989 ⟨1004584, by decide⟩ ⟨11, 2, 0, 1004584, 74989, 2073, 262144⟩
    (by decide) selected_cut_37552

theorem selected_cut_37553 : selected 10 ⟨1004617, by decide⟩
    (prefixPartial 11 74990) = some ⟨11, 2, 0, 1004617, 74990, 2097, 262144⟩ := by
  decide +kernel

theorem context_11_74990_1004617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74990 ⟨1004617, by decide⟩ :=
  accepted_of_selected 11 74990 ⟨1004617, by decide⟩ ⟨11, 2, 0, 1004617, 74990, 2097, 262144⟩
    (by decide) selected_cut_37553

theorem selected_cut_37554 : selected 10 ⟨1004638, by decide⟩
    (prefixPartial 11 74991) = some ⟨11, 2, 0, 1004638, 74991, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_74991_1004638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74991 ⟨1004638, by decide⟩ :=
  accepted_of_selected 11 74991 ⟨1004638, by decide⟩ ⟨11, 2, 0, 1004638, 74991, 1309, 262144⟩
    (by decide) selected_cut_37554

theorem unmarked_context_10_18747_1004639 : frontier 11 ⟨1004639, by decide⟩
    (prefixCache 10 18747) (prefixPartial 10 18747) = false := by
  decide +kernel

theorem node_context_10_18747_1004639 : EJMOriginalGlobalDAGData.nodes 11 ⟨1004639, by decide⟩ =
    .split (coordinate 10) (![⟨1004555, by decide⟩,⟨1004584, by decide⟩,⟨1004617, by decide⟩,⟨1004638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18747_1004639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18747 ⟨1004639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18747
    ⟨1004639, by decide⟩ (by decide) (![⟨1004555, by decide⟩,⟨1004584, by decide⟩,⟨1004617, by decide⟩,⟨1004638, by decide⟩]) unmarked_context_10_18747_1004639 node_context_10_18747_1004639
  intro a
  fin_cases a
  · exact context_11_74988_1004555
  · exact context_11_74989_1004584
  · exact context_11_74990_1004617
  · exact context_11_74991_1004638

theorem unmarked_context_9_4686_1004640 : frontier 12 ⟨1004640, by decide⟩
    (prefixCache 9 4686) (prefixPartial 9 4686) = false := by
  decide +kernel

theorem node_context_9_4686_1004640 : EJMOriginalGlobalDAGData.nodes 12 ⟨1004640, by decide⟩ =
    .split (coordinate 9) (![⟨1004245, by decide⟩,⟨1004408, by decide⟩,⟨1004521, by decide⟩,⟨1004639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4686_1004640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4686 ⟨1004640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4686
    ⟨1004640, by decide⟩ (by decide) (![⟨1004245, by decide⟩,⟨1004408, by decide⟩,⟨1004521, by decide⟩,⟨1004639, by decide⟩]) unmarked_context_9_4686_1004640 node_context_9_4686_1004640
  intro a
  fin_cases a
  · exact context_10_18744_1004245
  · exact context_10_18745_1004408
  · exact context_10_18746_1004521
  · exact context_10_18747_1004639

theorem selected_cut_37555 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74992) = some ⟨11, 1, 0, 907917, 74992, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74992_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74992 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74992 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74992, 1, 262144⟩
    (by decide) selected_cut_37555

theorem selected_cut_37556 : selected 10 ⟨1004667, by decide⟩
    (prefixPartial 11 74993) = some ⟨11, 2, 0, 1004667, 74993, 1961, 262144⟩ := by
  decide +kernel

theorem context_11_74993_1004667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74993 ⟨1004667, by decide⟩ :=
  accepted_of_selected 11 74993 ⟨1004667, by decide⟩ ⟨11, 2, 0, 1004667, 74993, 1961, 262144⟩
    (by decide) selected_cut_37556

theorem selected_cut_37557 : selected 10 ⟨1004693, by decide⟩
    (prefixPartial 11 74994) = some ⟨11, 2, 0, 1004693, 74994, 1937, 262144⟩ := by
  decide +kernel

theorem context_11_74994_1004693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74994 ⟨1004693, by decide⟩ :=
  accepted_of_selected 11 74994 ⟨1004693, by decide⟩ ⟨11, 2, 0, 1004693, 74994, 1937, 262144⟩
    (by decide) selected_cut_37557

theorem selected_cut_37558 : selected 10 ⟨1004718, by decide⟩
    (prefixPartial 11 74995) = some ⟨11, 2, 0, 1004718, 74995, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_74995_1004718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74995 ⟨1004718, by decide⟩ :=
  accepted_of_selected 11 74995 ⟨1004718, by decide⟩ ⟨11, 2, 0, 1004718, 74995, 1481, 262144⟩
    (by decide) selected_cut_37558

theorem unmarked_context_10_18748_1004719 : frontier 11 ⟨1004719, by decide⟩
    (prefixCache 10 18748) (prefixPartial 10 18748) = false := by
  decide +kernel

theorem node_context_10_18748_1004719 : EJMOriginalGlobalDAGData.nodes 11 ⟨1004719, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1004667, by decide⟩,⟨1004693, by decide⟩,⟨1004718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18748_1004719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18748 ⟨1004719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18748
    ⟨1004719, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1004667, by decide⟩,⟨1004693, by decide⟩,⟨1004718, by decide⟩]) unmarked_context_10_18748_1004719 node_context_10_18748_1004719
  intro a
  fin_cases a
  · exact context_11_74992_907917
  · exact context_11_74993_1004667
  · exact context_11_74994_1004693
  · exact context_11_74995_1004718

theorem selected_cut_37559 : selected 10 ⟨1004739, by decide⟩
    (prefixPartial 11 74996) = some ⟨11, 2, 0, 1004739, 74996, 1441, 262144⟩ := by
  decide +kernel

theorem context_11_74996_1004739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74996 ⟨1004739, by decide⟩ :=
  accepted_of_selected 11 74996 ⟨1004739, by decide⟩ ⟨11, 2, 0, 1004739, 74996, 1441, 262144⟩
    (by decide) selected_cut_37559

theorem selected_cut_37560 : selected 10 ⟨1004756, by decide⟩
    (prefixPartial 11 74997) = some ⟨11, 2, 0, 1004756, 74997, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_74997_1004756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74997 ⟨1004756, by decide⟩ :=
  accepted_of_selected 11 74997 ⟨1004756, by decide⟩ ⟨11, 2, 0, 1004756, 74997, 1397, 262144⟩
    (by decide) selected_cut_37560

theorem selected_cut_37561 : selected 10 ⟨1004770, by decide⟩
    (prefixPartial 11 74998) = some ⟨11, 2, 0, 1004770, 74998, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_74998_1004770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74998 ⟨1004770, by decide⟩ :=
  accepted_of_selected 11 74998 ⟨1004770, by decide⟩ ⟨11, 2, 0, 1004770, 74998, 1309, 262144⟩
    (by decide) selected_cut_37561

theorem selected_cut_37562 : selected 10 ⟨1004792, by decide⟩
    (prefixPartial 11 74999) = some ⟨11, 2, 0, 1004792, 74999, 997, 262144⟩ := by
  decide +kernel

theorem context_11_74999_1004792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74999 ⟨1004792, by decide⟩ :=
  accepted_of_selected 11 74999 ⟨1004792, by decide⟩ ⟨11, 2, 0, 1004792, 74999, 997, 262144⟩
    (by decide) selected_cut_37562

theorem unmarked_context_10_18749_1004793 : frontier 11 ⟨1004793, by decide⟩
    (prefixCache 10 18749) (prefixPartial 10 18749) = false := by
  decide +kernel

theorem node_context_10_18749_1004793 : EJMOriginalGlobalDAGData.nodes 11 ⟨1004793, by decide⟩ =
    .split (coordinate 10) (![⟨1004739, by decide⟩,⟨1004756, by decide⟩,⟨1004770, by decide⟩,⟨1004792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18749_1004793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18749 ⟨1004793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18749
    ⟨1004793, by decide⟩ (by decide) (![⟨1004739, by decide⟩,⟨1004756, by decide⟩,⟨1004770, by decide⟩,⟨1004792, by decide⟩]) unmarked_context_10_18749_1004793 node_context_10_18749_1004793
  intro a
  fin_cases a
  · exact context_11_74996_1004739
  · exact context_11_74997_1004756
  · exact context_11_74998_1004770
  · exact context_11_74999_1004792

theorem selected_cut_37563 : selected 11 ⟨1004861, by decide⟩
    (prefixPartial 10 18750) = some ⟨10, 2, 0, 1004861, 18750, 3117, 1048576⟩ := by
  decide +kernel

theorem context_10_18750_1004861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18750 ⟨1004861, by decide⟩ :=
  accepted_of_selected 10 18750 ⟨1004861, by decide⟩ ⟨10, 2, 0, 1004861, 18750, 3117, 1048576⟩
    (by decide) selected_cut_37563

theorem selected_cut_37564 : selected 11 ⟨1004906, by decide⟩
    (prefixPartial 10 18751) = some ⟨10, 2, 0, 1004906, 18751, 1149, 1048576⟩ := by
  decide +kernel

theorem context_10_18751_1004906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18751 ⟨1004906, by decide⟩ :=
  accepted_of_selected 10 18751 ⟨1004906, by decide⟩ ⟨10, 2, 0, 1004906, 18751, 1149, 1048576⟩
    (by decide) selected_cut_37564

theorem unmarked_context_9_4687_1004907 : frontier 12 ⟨1004907, by decide⟩
    (prefixCache 9 4687) (prefixPartial 9 4687) = false := by
  decide +kernel

theorem node_context_9_4687_1004907 : EJMOriginalGlobalDAGData.nodes 12 ⟨1004907, by decide⟩ =
    .split (coordinate 9) (![⟨1004719, by decide⟩,⟨1004793, by decide⟩,⟨1004861, by decide⟩,⟨1004906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4687_1004907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4687 ⟨1004907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4687
    ⟨1004907, by decide⟩ (by decide) (![⟨1004719, by decide⟩,⟨1004793, by decide⟩,⟨1004861, by decide⟩,⟨1004906, by decide⟩]) unmarked_context_9_4687_1004907 node_context_9_4687_1004907
  intro a
  fin_cases a
  · exact context_10_18748_1004719
  · exact context_10_18749_1004793
  · exact context_10_18750_1004861
  · exact context_10_18751_1004906

theorem unmarked_context_8_1171_1004908 : frontier 13 ⟨1004908, by decide⟩
    (prefixCache 8 1171) (prefixPartial 8 1171) = false := by
  decide +kernel

theorem node_context_8_1171_1004908 : EJMOriginalGlobalDAGData.nodes 13 ⟨1004908, by decide⟩ =
    .split (coordinate 8) (![⟨1002727, by decide⟩,⟨1004072, by decide⟩,⟨1004640, by decide⟩,⟨1004907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1171_1004908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1171 ⟨1004908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1171
    ⟨1004908, by decide⟩ (by decide) (![⟨1002727, by decide⟩,⟨1004072, by decide⟩,⟨1004640, by decide⟩,⟨1004907, by decide⟩]) unmarked_context_8_1171_1004908 node_context_8_1171_1004908
  intro a
  fin_cases a
  · exact context_9_4684_1002727
  · exact context_9_4685_1004072
  · exact context_9_4686_1004640
  · exact context_9_4687_1004907

theorem unmarked_context_7_292_1004909 : frontier 14 ⟨1004909, by decide⟩
    (prefixCache 7 292) (prefixPartial 7 292) = false := by
  decide +kernel

theorem node_context_7_292_1004909 : EJMOriginalGlobalDAGData.nodes 14 ⟨1004909, by decide⟩ =
    .split (coordinate 7) (![⟨989027, by decide⟩,⟨993569, by decide⟩,⟨999177, by decide⟩,⟨1004908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_292_1004909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 292 ⟨1004909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 292
    ⟨1004909, by decide⟩ (by decide) (![⟨989027, by decide⟩,⟨993569, by decide⟩,⟨999177, by decide⟩,⟨1004908, by decide⟩]) unmarked_context_7_292_1004909 node_context_7_292_1004909
  intro a
  fin_cases a
  · exact context_8_1168_989027
  · exact context_8_1169_993569
  · exact context_8_1170_999177
  · exact context_8_1171_1004908

theorem selected_cut_37565 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 75008) = some ⟨11, 1, 0, 167448, 75008, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75008_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75008 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 75008 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 75008, 1, 262144⟩
    (by decide) selected_cut_37565

theorem selected_cut_37566 : selected 9 ⟨1005024, by decide⟩
    (prefixPartial 12 300036) = some ⟨12, 2, 0, 1005024, 300036, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_300036_1005024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300036 ⟨1005024, by decide⟩ :=
  accepted_of_selected 12 300036 ⟨1005024, by decide⟩ ⟨12, 2, 0, 1005024, 300036, 4053, 65536⟩
    (by decide) selected_cut_37566

theorem selected_cut_37567 : selected 9 ⟨1005093, by decide⟩
    (prefixPartial 12 300037) = some ⟨12, 2, 0, 1005093, 300037, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_300037_1005093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300037 ⟨1005093, by decide⟩ :=
  accepted_of_selected 12 300037 ⟨1005093, by decide⟩ ⟨12, 2, 0, 1005093, 300037, 3257, 65536⟩
    (by decide) selected_cut_37567

theorem selected_cut_37568 : selected 9 ⟨1005166, by decide⟩
    (prefixPartial 12 300038) = some ⟨12, 2, 0, 1005166, 300038, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_300038_1005166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300038 ⟨1005166, by decide⟩ :=
  accepted_of_selected 12 300038 ⟨1005166, by decide⟩ ⟨12, 2, 0, 1005166, 300038, 3681, 65536⟩
    (by decide) selected_cut_37568

theorem selected_cut_37569 : selected 9 ⟨1005236, by decide⟩
    (prefixPartial 12 300039) = some ⟨12, 2, 0, 1005236, 300039, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_300039_1005236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300039 ⟨1005236, by decide⟩ :=
  accepted_of_selected 12 300039 ⟨1005236, by decide⟩ ⟨12, 2, 0, 1005236, 300039, 3861, 65536⟩
    (by decide) selected_cut_37569

theorem unmarked_context_11_75009_1005237 : frontier 10 ⟨1005237, by decide⟩
    (prefixCache 11 75009) (prefixPartial 11 75009) = false := by
  decide +kernel

theorem node_context_11_75009_1005237 : EJMOriginalGlobalDAGData.nodes 10 ⟨1005237, by decide⟩ =
    .split (coordinate 11) (![⟨1005024, by decide⟩,⟨1005093, by decide⟩,⟨1005166, by decide⟩,⟨1005236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75009_1005237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75009 ⟨1005237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75009
    ⟨1005237, by decide⟩ (by decide) (![⟨1005024, by decide⟩,⟨1005093, by decide⟩,⟨1005166, by decide⟩,⟨1005236, by decide⟩]) unmarked_context_11_75009_1005237 node_context_11_75009_1005237
  intro a
  fin_cases a
  · exact context_12_300036_1005024
  · exact context_12_300037_1005093
  · exact context_12_300038_1005166
  · exact context_12_300039_1005236

theorem selected_cut_37570 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 300040) = some ⟨12, 1, 0, 450498, 300040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300040_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300040 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 300040 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 300040, 1, 65536⟩
    (by decide) selected_cut_37570

theorem selected_cut_37571 : selected 9 ⟨1005323, by decide⟩
    (prefixPartial 12 300041) = some ⟨12, 2, 0, 1005323, 300041, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_300041_1005323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300041 ⟨1005323, by decide⟩ :=
  accepted_of_selected 12 300041 ⟨1005323, by decide⟩ ⟨12, 2, 0, 1005323, 300041, 3977, 65536⟩
    (by decide) selected_cut_37571

theorem selected_cut_37572 : selected 8 ⟨1005354, by decide⟩
    (prefixPartial 13 1200168) = some ⟨13, 2, 0, 1005354, 1200168, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_1200168_1005354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200168 ⟨1005354, by decide⟩ :=
  accepted_of_selected 13 1200168 ⟨1005354, by decide⟩ ⟨13, 2, 0, 1005354, 1200168, 1569, 16384⟩
    (by decide) selected_cut_37572

theorem selected_cut_37573 : selected 8 ⟨1005388, by decide⟩
    (prefixPartial 13 1200169) = some ⟨13, 2, 0, 1005388, 1200169, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_1200169_1005388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200169 ⟨1005388, by decide⟩ :=
  accepted_of_selected 13 1200169 ⟨1005388, by decide⟩ ⟨13, 2, 0, 1005388, 1200169, 1245, 16384⟩
    (by decide) selected_cut_37573

theorem selected_cut_37574 : selected 8 ⟨1005409, by decide⟩
    (prefixPartial 13 1200170) = some ⟨13, 2, 0, 1005409, 1200170, 825, 16384⟩ := by
  decide +kernel

theorem context_13_1200170_1005409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200170 ⟨1005409, by decide⟩ :=
  accepted_of_selected 13 1200170 ⟨1005409, by decide⟩ ⟨13, 2, 0, 1005409, 1200170, 825, 16384⟩
    (by decide) selected_cut_37574

theorem selected_cut_37575 : selected 8 ⟨1005413, by decide⟩
    (prefixPartial 13 1200171) = some ⟨13, 2, 0, 1005413, 1200171, 505, 16384⟩ := by
  decide +kernel

theorem context_13_1200171_1005413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200171 ⟨1005413, by decide⟩ :=
  accepted_of_selected 13 1200171 ⟨1005413, by decide⟩ ⟨13, 2, 0, 1005413, 1200171, 505, 16384⟩
    (by decide) selected_cut_37575

theorem unmarked_context_12_300042_1005414 : frontier 9 ⟨1005414, by decide⟩
    (prefixCache 12 300042) (prefixPartial 12 300042) = false := by
  decide +kernel

theorem node_context_12_300042_1005414 : EJMOriginalGlobalDAGData.nodes 9 ⟨1005414, by decide⟩ =
    .split (coordinate 12) (![⟨1005354, by decide⟩,⟨1005388, by decide⟩,⟨1005409, by decide⟩,⟨1005413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300042_1005414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300042 ⟨1005414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300042
    ⟨1005414, by decide⟩ (by decide) (![⟨1005354, by decide⟩,⟨1005388, by decide⟩,⟨1005409, by decide⟩,⟨1005413, by decide⟩]) unmarked_context_12_300042_1005414 node_context_12_300042_1005414
  intro a
  fin_cases a
  · exact context_13_1200168_1005354
  · exact context_13_1200169_1005388
  · exact context_13_1200170_1005409
  · exact context_13_1200171_1005413

theorem selected_cut_37576 : selected 8 ⟨1005450, by decide⟩
    (prefixPartial 13 1200172) = some ⟨13, 2, 0, 1005450, 1200172, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_1200172_1005450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200172 ⟨1005450, by decide⟩ :=
  accepted_of_selected 13 1200172 ⟨1005450, by decide⟩ ⟨13, 2, 0, 1005450, 1200172, 1617, 16384⟩
    (by decide) selected_cut_37576

theorem selected_cut_37577 : selected 8 ⟨1005480, by decide⟩
    (prefixPartial 13 1200173) = some ⟨13, 2, 0, 1005480, 1200173, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_1200173_1005480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200173 ⟨1005480, by decide⟩ :=
  accepted_of_selected 13 1200173 ⟨1005480, by decide⟩ ⟨13, 2, 0, 1005480, 1200173, 1401, 16384⟩
    (by decide) selected_cut_37577

theorem selected_cut_37578 : selected 8 ⟨1005509, by decide⟩
    (prefixPartial 13 1200174) = some ⟨13, 2, 0, 1005509, 1200174, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_1200174_1005509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200174 ⟨1005509, by decide⟩ :=
  accepted_of_selected 13 1200174 ⟨1005509, by decide⟩ ⟨13, 2, 0, 1005509, 1200174, 1013, 16384⟩
    (by decide) selected_cut_37578

theorem selected_cut_37579 : selected 8 ⟨1005519, by decide⟩
    (prefixPartial 13 1200175) = some ⟨13, 2, 0, 1005519, 1200175, 581, 16384⟩ := by
  decide +kernel

theorem context_13_1200175_1005519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200175 ⟨1005519, by decide⟩ :=
  accepted_of_selected 13 1200175 ⟨1005519, by decide⟩ ⟨13, 2, 0, 1005519, 1200175, 581, 16384⟩
    (by decide) selected_cut_37579

theorem unmarked_context_12_300043_1005520 : frontier 9 ⟨1005520, by decide⟩
    (prefixCache 12 300043) (prefixPartial 12 300043) = false := by
  decide +kernel

theorem node_context_12_300043_1005520 : EJMOriginalGlobalDAGData.nodes 9 ⟨1005520, by decide⟩ =
    .split (coordinate 12) (![⟨1005450, by decide⟩,⟨1005480, by decide⟩,⟨1005509, by decide⟩,⟨1005519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300043_1005520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300043 ⟨1005520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300043
    ⟨1005520, by decide⟩ (by decide) (![⟨1005450, by decide⟩,⟨1005480, by decide⟩,⟨1005509, by decide⟩,⟨1005519, by decide⟩]) unmarked_context_12_300043_1005520 node_context_12_300043_1005520
  intro a
  fin_cases a
  · exact context_13_1200172_1005450
  · exact context_13_1200173_1005480
  · exact context_13_1200174_1005509
  · exact context_13_1200175_1005519

theorem unmarked_context_11_75010_1005521 : frontier 10 ⟨1005521, by decide⟩
    (prefixCache 11 75010) (prefixPartial 11 75010) = false := by
  decide +kernel

theorem node_context_11_75010_1005521 : EJMOriginalGlobalDAGData.nodes 10 ⟨1005521, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1005323, by decide⟩,⟨1005414, by decide⟩,⟨1005520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75010_1005521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75010 ⟨1005521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75010
    ⟨1005521, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1005323, by decide⟩,⟨1005414, by decide⟩,⟨1005520, by decide⟩]) unmarked_context_11_75010_1005521 node_context_11_75010_1005521
  intro a
  fin_cases a
  · exact context_12_300040_450498
  · exact context_12_300041_1005323
  · exact context_12_300042_1005414
  · exact context_12_300043_1005520

theorem selected_cut_37580 : selected 8 ⟨1005547, by decide⟩
    (prefixPartial 13 1200176) = some ⟨13, 2, 0, 1005547, 1200176, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_1200176_1005547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200176 ⟨1005547, by decide⟩ :=
  accepted_of_selected 13 1200176 ⟨1005547, by decide⟩ ⟨13, 2, 0, 1005547, 1200176, 1357, 16384⟩
    (by decide) selected_cut_37580

theorem selected_cut_37581 : selected 8 ⟨1005572, by decide⟩
    (prefixPartial 13 1200177) = some ⟨13, 2, 0, 1005572, 1200177, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_1200177_1005572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200177 ⟨1005572, by decide⟩ :=
  accepted_of_selected 13 1200177 ⟨1005572, by decide⟩ ⟨13, 2, 0, 1005572, 1200177, 1389, 16384⟩
    (by decide) selected_cut_37581

theorem selected_cut_37582 : selected 8 ⟨1005598, by decide⟩
    (prefixPartial 13 1200178) = some ⟨13, 2, 0, 1005598, 1200178, 937, 16384⟩ := by
  decide +kernel

theorem context_13_1200178_1005598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200178 ⟨1005598, by decide⟩ :=
  accepted_of_selected 13 1200178 ⟨1005598, by decide⟩ ⟨13, 2, 0, 1005598, 1200178, 937, 16384⟩
    (by decide) selected_cut_37582

theorem selected_cut_37583 : selected 8 ⟨1005606, by decide⟩
    (prefixPartial 13 1200179) = some ⟨13, 2, 0, 1005606, 1200179, 609, 16384⟩ := by
  decide +kernel

theorem context_13_1200179_1005606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200179 ⟨1005606, by decide⟩ :=
  accepted_of_selected 13 1200179 ⟨1005606, by decide⟩ ⟨13, 2, 0, 1005606, 1200179, 609, 16384⟩
    (by decide) selected_cut_37583

theorem unmarked_context_12_300044_1005607 : frontier 9 ⟨1005607, by decide⟩
    (prefixCache 12 300044) (prefixPartial 12 300044) = false := by
  decide +kernel

theorem node_context_12_300044_1005607 : EJMOriginalGlobalDAGData.nodes 9 ⟨1005607, by decide⟩ =
    .split (coordinate 12) (![⟨1005547, by decide⟩,⟨1005572, by decide⟩,⟨1005598, by decide⟩,⟨1005606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300044_1005607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300044 ⟨1005607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300044
    ⟨1005607, by decide⟩ (by decide) (![⟨1005547, by decide⟩,⟨1005572, by decide⟩,⟨1005598, by decide⟩,⟨1005606, by decide⟩]) unmarked_context_12_300044_1005607 node_context_12_300044_1005607
  intro a
  fin_cases a
  · exact context_13_1200176_1005547
  · exact context_13_1200177_1005572
  · exact context_13_1200178_1005598
  · exact context_13_1200179_1005606

theorem selected_cut_37584 : selected 9 ⟨1005685, by decide⟩
    (prefixPartial 12 300045) = some ⟨12, 2, 0, 1005685, 300045, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_300045_1005685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300045 ⟨1005685, by decide⟩ :=
  accepted_of_selected 12 300045 ⟨1005685, by decide⟩ ⟨12, 2, 0, 1005685, 300045, 4009, 65536⟩
    (by decide) selected_cut_37584

theorem selected_cut_37585 : selected 8 ⟨1005717, by decide⟩
    (prefixPartial 13 1200184) = some ⟨13, 2, 0, 1005717, 1200184, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_1200184_1005717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200184 ⟨1005717, by decide⟩ :=
  accepted_of_selected 13 1200184 ⟨1005717, by decide⟩ ⟨13, 2, 0, 1005717, 1200184, 1585, 16384⟩
    (by decide) selected_cut_37585

theorem selected_cut_37586 : selected 8 ⟨1005744, by decide⟩
    (prefixPartial 13 1200185) = some ⟨13, 2, 0, 1005744, 1200185, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_1200185_1005744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200185 ⟨1005744, by decide⟩ :=
  accepted_of_selected 13 1200185 ⟨1005744, by decide⟩ ⟨13, 2, 0, 1005744, 1200185, 1401, 16384⟩
    (by decide) selected_cut_37586

theorem selected_cut_37587 : selected 8 ⟨1005766, by decide⟩
    (prefixPartial 13 1200186) = some ⟨13, 2, 0, 1005766, 1200186, 945, 16384⟩ := by
  decide +kernel

theorem context_13_1200186_1005766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200186 ⟨1005766, by decide⟩ :=
  accepted_of_selected 13 1200186 ⟨1005766, by decide⟩ ⟨13, 2, 0, 1005766, 1200186, 945, 16384⟩
    (by decide) selected_cut_37587

theorem selected_cut_37588 : selected 8 ⟨1005774, by decide⟩
    (prefixPartial 13 1200187) = some ⟨13, 2, 0, 1005774, 1200187, 593, 16384⟩ := by
  decide +kernel

theorem context_13_1200187_1005774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200187 ⟨1005774, by decide⟩ :=
  accepted_of_selected 13 1200187 ⟨1005774, by decide⟩ ⟨13, 2, 0, 1005774, 1200187, 593, 16384⟩
    (by decide) selected_cut_37588

theorem unmarked_context_12_300046_1005775 : frontier 9 ⟨1005775, by decide⟩
    (prefixCache 12 300046) (prefixPartial 12 300046) = false := by
  decide +kernel

theorem node_context_12_300046_1005775 : EJMOriginalGlobalDAGData.nodes 9 ⟨1005775, by decide⟩ =
    .split (coordinate 12) (![⟨1005717, by decide⟩,⟨1005744, by decide⟩,⟨1005766, by decide⟩,⟨1005774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300046_1005775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300046 ⟨1005775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300046
    ⟨1005775, by decide⟩ (by decide) (![⟨1005717, by decide⟩,⟨1005744, by decide⟩,⟨1005766, by decide⟩,⟨1005774, by decide⟩]) unmarked_context_12_300046_1005775 node_context_12_300046_1005775
  intro a
  fin_cases a
  · exact context_13_1200184_1005717
  · exact context_13_1200185_1005744
  · exact context_13_1200186_1005766
  · exact context_13_1200187_1005774

theorem selected_cut_37589 : selected 8 ⟨1005805, by decide⟩
    (prefixPartial 13 1200188) = some ⟨13, 2, 0, 1005805, 1200188, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_1200188_1005805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200188 ⟨1005805, by decide⟩ :=
  accepted_of_selected 13 1200188 ⟨1005805, by decide⟩ ⟨13, 2, 0, 1005805, 1200188, 1393, 16384⟩
    (by decide) selected_cut_37589

theorem selected_cut_37590 : selected 8 ⟨1005825, by decide⟩
    (prefixPartial 13 1200189) = some ⟨13, 2, 0, 1005825, 1200189, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_1200189_1005825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200189 ⟨1005825, by decide⟩ :=
  accepted_of_selected 13 1200189 ⟨1005825, by decide⟩ ⟨13, 2, 0, 1005825, 1200189, 1321, 16384⟩
    (by decide) selected_cut_37590

theorem selected_cut_37591 : selected 8 ⟨1005842, by decide⟩
    (prefixPartial 13 1200190) = some ⟨13, 2, 0, 1005842, 1200190, 821, 16384⟩ := by
  decide +kernel

theorem context_13_1200190_1005842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200190 ⟨1005842, by decide⟩ :=
  accepted_of_selected 13 1200190 ⟨1005842, by decide⟩ ⟨13, 2, 0, 1005842, 1200190, 821, 16384⟩
    (by decide) selected_cut_37591

theorem selected_cut_37592 : selected 8 ⟨1005848, by decide⟩
    (prefixPartial 13 1200191) = some ⟨13, 2, 0, 1005848, 1200191, 589, 16384⟩ := by
  decide +kernel

theorem context_13_1200191_1005848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1200191 ⟨1005848, by decide⟩ :=
  accepted_of_selected 13 1200191 ⟨1005848, by decide⟩ ⟨13, 2, 0, 1005848, 1200191, 589, 16384⟩
    (by decide) selected_cut_37592

theorem unmarked_context_12_300047_1005849 : frontier 9 ⟨1005849, by decide⟩
    (prefixCache 12 300047) (prefixPartial 12 300047) = false := by
  decide +kernel

theorem node_context_12_300047_1005849 : EJMOriginalGlobalDAGData.nodes 9 ⟨1005849, by decide⟩ =
    .split (coordinate 12) (![⟨1005805, by decide⟩,⟨1005825, by decide⟩,⟨1005842, by decide⟩,⟨1005848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_300047_1005849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300047 ⟨1005849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 300047
    ⟨1005849, by decide⟩ (by decide) (![⟨1005805, by decide⟩,⟨1005825, by decide⟩,⟨1005842, by decide⟩,⟨1005848, by decide⟩]) unmarked_context_12_300047_1005849 node_context_12_300047_1005849
  intro a
  fin_cases a
  · exact context_13_1200188_1005805
  · exact context_13_1200189_1005825
  · exact context_13_1200190_1005842
  · exact context_13_1200191_1005848

theorem unmarked_context_11_75011_1005850 : frontier 10 ⟨1005850, by decide⟩
    (prefixCache 11 75011) (prefixPartial 11 75011) = false := by
  decide +kernel

theorem node_context_11_75011_1005850 : EJMOriginalGlobalDAGData.nodes 10 ⟨1005850, by decide⟩ =
    .split (coordinate 11) (![⟨1005607, by decide⟩,⟨1005685, by decide⟩,⟨1005775, by decide⟩,⟨1005849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75011_1005850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75011 ⟨1005850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75011
    ⟨1005850, by decide⟩ (by decide) (![⟨1005607, by decide⟩,⟨1005685, by decide⟩,⟨1005775, by decide⟩,⟨1005849, by decide⟩]) unmarked_context_11_75011_1005850 node_context_11_75011_1005850
  intro a
  fin_cases a
  · exact context_12_300044_1005607
  · exact context_12_300045_1005685
  · exact context_12_300046_1005775
  · exact context_12_300047_1005849

theorem unmarked_context_10_18752_1005851 : frontier 11 ⟨1005851, by decide⟩
    (prefixCache 10 18752) (prefixPartial 10 18752) = false := by
  decide +kernel

theorem node_context_10_18752_1005851 : EJMOriginalGlobalDAGData.nodes 11 ⟨1005851, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1005237, by decide⟩,⟨1005521, by decide⟩,⟨1005850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18752_1005851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18752 ⟨1005851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18752
    ⟨1005851, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1005237, by decide⟩,⟨1005521, by decide⟩,⟨1005850, by decide⟩]) unmarked_context_10_18752_1005851 node_context_10_18752_1005851
  intro a
  fin_cases a
  · exact context_11_75008_167448
  · exact context_11_75009_1005237
  · exact context_11_75010_1005521
  · exact context_11_75011_1005850

theorem selected_cut_37593 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 300048) = some ⟨12, 1, 0, 985390, 300048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300048_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300048 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 300048 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 300048, 1, 65536⟩
    (by decide) selected_cut_37593

theorem selected_cut_37594 : selected 9 ⟨1005893, by decide⟩
    (prefixPartial 12 300049) = some ⟨12, 2, 0, 1005893, 300049, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_300049_1005893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300049 ⟨1005893, by decide⟩ :=
  accepted_of_selected 12 300049 ⟨1005893, by decide⟩ ⟨12, 2, 0, 1005893, 300049, 2501, 65536⟩
    (by decide) selected_cut_37594

theorem selected_cut_37595 : selected 9 ⟨1005935, by decide⟩
    (prefixPartial 12 300050) = some ⟨12, 2, 0, 1005935, 300050, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_300050_1005935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300050 ⟨1005935, by decide⟩ :=
  accepted_of_selected 12 300050 ⟨1005935, by decide⟩ ⟨12, 2, 0, 1005935, 300050, 2693, 65536⟩
    (by decide) selected_cut_37595

theorem selected_cut_37596 : selected 9 ⟨1005980, by decide⟩
    (prefixPartial 12 300051) = some ⟨12, 2, 0, 1005980, 300051, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_300051_1005980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300051 ⟨1005980, by decide⟩ :=
  accepted_of_selected 12 300051 ⟨1005980, by decide⟩ ⟨12, 2, 0, 1005980, 300051, 2789, 65536⟩
    (by decide) selected_cut_37596

theorem unmarked_context_11_75012_1005981 : frontier 10 ⟨1005981, by decide⟩
    (prefixCache 11 75012) (prefixPartial 11 75012) = false := by
  decide +kernel

theorem node_context_11_75012_1005981 : EJMOriginalGlobalDAGData.nodes 10 ⟨1005981, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1005893, by decide⟩,⟨1005935, by decide⟩,⟨1005980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75012_1005981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75012 ⟨1005981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75012
    ⟨1005981, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1005893, by decide⟩,⟨1005935, by decide⟩,⟨1005980, by decide⟩]) unmarked_context_11_75012_1005981 node_context_11_75012_1005981
  intro a
  fin_cases a
  · exact context_12_300048_985390
  · exact context_12_300049_1005893
  · exact context_12_300050_1005935
  · exact context_12_300051_1005980

theorem selected_cut_37597 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 75013) = some ⟨11, 1, 0, 892405, 75013, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75013_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75013 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 75013 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 75013, 1, 262144⟩
    (by decide) selected_cut_37597

theorem selected_cut_37598 : selected 9 ⟨1006035, by decide⟩
    (prefixPartial 12 300056) = some ⟨12, 2, 0, 1006035, 300056, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_300056_1006035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300056 ⟨1006035, by decide⟩ :=
  accepted_of_selected 12 300056 ⟨1006035, by decide⟩ ⟨12, 2, 0, 1006035, 300056, 3129, 65536⟩
    (by decide) selected_cut_37598

theorem selected_cut_37599 : selected 9 ⟨1006099, by decide⟩
    (prefixPartial 12 300057) = some ⟨12, 2, 0, 1006099, 300057, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_300057_1006099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300057 ⟨1006099, by decide⟩ :=
  accepted_of_selected 12 300057 ⟨1006099, by decide⟩ ⟨12, 2, 0, 1006099, 300057, 2921, 65536⟩
    (by decide) selected_cut_37599

theorem selected_cut_37600 : selected 9 ⟨1006156, by decide⟩
    (prefixPartial 12 300058) = some ⟨12, 2, 0, 1006156, 300058, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_300058_1006156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300058 ⟨1006156, by decide⟩ :=
  accepted_of_selected 12 300058 ⟨1006156, by decide⟩ ⟨12, 2, 0, 1006156, 300058, 3161, 65536⟩
    (by decide) selected_cut_37600

theorem selected_cut_37601 : selected 9 ⟨1006230, by decide⟩
    (prefixPartial 12 300059) = some ⟨12, 2, 0, 1006230, 300059, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_300059_1006230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300059 ⟨1006230, by decide⟩ :=
  accepted_of_selected 12 300059 ⟨1006230, by decide⟩ ⟨12, 2, 0, 1006230, 300059, 3577, 65536⟩
    (by decide) selected_cut_37601

theorem unmarked_context_11_75014_1006231 : frontier 10 ⟨1006231, by decide⟩
    (prefixCache 11 75014) (prefixPartial 11 75014) = false := by
  decide +kernel

theorem node_context_11_75014_1006231 : EJMOriginalGlobalDAGData.nodes 10 ⟨1006231, by decide⟩ =
    .split (coordinate 11) (![⟨1006035, by decide⟩,⟨1006099, by decide⟩,⟨1006156, by decide⟩,⟨1006230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75014_1006231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75014 ⟨1006231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75014
    ⟨1006231, by decide⟩ (by decide) (![⟨1006035, by decide⟩,⟨1006099, by decide⟩,⟨1006156, by decide⟩,⟨1006230, by decide⟩]) unmarked_context_11_75014_1006231 node_context_11_75014_1006231
  intro a
  fin_cases a
  · exact context_12_300056_1006035
  · exact context_12_300057_1006099
  · exact context_12_300058_1006156
  · exact context_12_300059_1006230

theorem selected_cut_37602 : selected 9 ⟨1006289, by decide⟩
    (prefixPartial 12 300060) = some ⟨12, 2, 0, 1006289, 300060, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_300060_1006289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300060 ⟨1006289, by decide⟩ :=
  accepted_of_selected 12 300060 ⟨1006289, by decide⟩ ⟨12, 2, 0, 1006289, 300060, 3317, 65536⟩
    (by decide) selected_cut_37602

theorem selected_cut_37603 : selected 9 ⟨1006346, by decide⟩
    (prefixPartial 12 300061) = some ⟨12, 2, 0, 1006346, 300061, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_300061_1006346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300061 ⟨1006346, by decide⟩ :=
  accepted_of_selected 12 300061 ⟨1006346, by decide⟩ ⟨12, 2, 0, 1006346, 300061, 3049, 65536⟩
    (by decide) selected_cut_37603

theorem selected_cut_37604 : selected 9 ⟨1006419, by decide⟩
    (prefixPartial 12 300062) = some ⟨12, 2, 0, 1006419, 300062, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_300062_1006419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300062 ⟨1006419, by decide⟩ :=
  accepted_of_selected 12 300062 ⟨1006419, by decide⟩ ⟨12, 2, 0, 1006419, 300062, 3501, 65536⟩
    (by decide) selected_cut_37604

theorem selected_cut_37605 : selected 9 ⟨1006485, by decide⟩
    (prefixPartial 12 300063) = some ⟨12, 2, 0, 1006485, 300063, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_300063_1006485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300063 ⟨1006485, by decide⟩ :=
  accepted_of_selected 12 300063 ⟨1006485, by decide⟩ ⟨12, 2, 0, 1006485, 300063, 3361, 65536⟩
    (by decide) selected_cut_37605

theorem unmarked_context_11_75015_1006486 : frontier 10 ⟨1006486, by decide⟩
    (prefixCache 11 75015) (prefixPartial 11 75015) = false := by
  decide +kernel

theorem node_context_11_75015_1006486 : EJMOriginalGlobalDAGData.nodes 10 ⟨1006486, by decide⟩ =
    .split (coordinate 11) (![⟨1006289, by decide⟩,⟨1006346, by decide⟩,⟨1006419, by decide⟩,⟨1006485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75015_1006486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75015 ⟨1006486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75015
    ⟨1006486, by decide⟩ (by decide) (![⟨1006289, by decide⟩,⟨1006346, by decide⟩,⟨1006419, by decide⟩,⟨1006485, by decide⟩]) unmarked_context_11_75015_1006486 node_context_11_75015_1006486
  intro a
  fin_cases a
  · exact context_12_300060_1006289
  · exact context_12_300061_1006346
  · exact context_12_300062_1006419
  · exact context_12_300063_1006485

theorem unmarked_context_10_18753_1006487 : frontier 11 ⟨1006487, by decide⟩
    (prefixCache 10 18753) (prefixPartial 10 18753) = false := by
  decide +kernel

theorem node_context_10_18753_1006487 : EJMOriginalGlobalDAGData.nodes 11 ⟨1006487, by decide⟩ =
    .split (coordinate 10) (![⟨1005981, by decide⟩,⟨892405, by decide⟩,⟨1006231, by decide⟩,⟨1006486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18753_1006487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18753 ⟨1006487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18753
    ⟨1006487, by decide⟩ (by decide) (![⟨1005981, by decide⟩,⟨892405, by decide⟩,⟨1006231, by decide⟩,⟨1006486, by decide⟩]) unmarked_context_10_18753_1006487 node_context_10_18753_1006487
  intro a
  fin_cases a
  · exact context_11_75012_1005981
  · exact context_11_75013_892405
  · exact context_11_75014_1006231
  · exact context_11_75015_1006486

theorem selected_cut_37606 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 300064) = some ⟨12, 1, 0, 985390, 300064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300064_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300064 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 300064 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 300064, 1, 65536⟩
    (by decide) selected_cut_37606

theorem selected_cut_37607 : selected 9 ⟨1006537, by decide⟩
    (prefixPartial 12 300065) = some ⟨12, 2, 0, 1006537, 300065, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_300065_1006537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300065 ⟨1006537, by decide⟩ :=
  accepted_of_selected 12 300065 ⟨1006537, by decide⟩ ⟨12, 2, 0, 1006537, 300065, 2977, 65536⟩
    (by decide) selected_cut_37607

theorem selected_cut_37608 : selected 9 ⟨1006581, by decide⟩
    (prefixPartial 12 300066) = some ⟨12, 2, 0, 1006581, 300066, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_300066_1006581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300066 ⟨1006581, by decide⟩ :=
  accepted_of_selected 12 300066 ⟨1006581, by decide⟩ ⟨12, 2, 0, 1006581, 300066, 2949, 65536⟩
    (by decide) selected_cut_37608

theorem selected_cut_37609 : selected 9 ⟨1006637, by decide⟩
    (prefixPartial 12 300067) = some ⟨12, 2, 0, 1006637, 300067, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_300067_1006637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300067 ⟨1006637, by decide⟩ :=
  accepted_of_selected 12 300067 ⟨1006637, by decide⟩ ⟨12, 2, 0, 1006637, 300067, 3137, 65536⟩
    (by decide) selected_cut_37609

theorem unmarked_context_11_75016_1006638 : frontier 10 ⟨1006638, by decide⟩
    (prefixCache 11 75016) (prefixPartial 11 75016) = false := by
  decide +kernel

theorem node_context_11_75016_1006638 : EJMOriginalGlobalDAGData.nodes 10 ⟨1006638, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1006537, by decide⟩,⟨1006581, by decide⟩,⟨1006637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75016_1006638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75016 ⟨1006638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75016
    ⟨1006638, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1006537, by decide⟩,⟨1006581, by decide⟩,⟨1006637, by decide⟩]) unmarked_context_11_75016_1006638 node_context_11_75016_1006638
  intro a
  fin_cases a
  · exact context_12_300064_985390
  · exact context_12_300065_1006537
  · exact context_12_300066_1006581
  · exact context_12_300067_1006637

theorem selected_cut_37610 : selected 9 ⟨1006690, by decide⟩
    (prefixPartial 12 300068) = some ⟨12, 2, 0, 1006690, 300068, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_300068_1006690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300068 ⟨1006690, by decide⟩ :=
  accepted_of_selected 12 300068 ⟨1006690, by decide⟩ ⟨12, 2, 0, 1006690, 300068, 3145, 65536⟩
    (by decide) selected_cut_37610

theorem selected_cut_37611 : selected 9 ⟨1006739, by decide⟩
    (prefixPartial 12 300069) = some ⟨12, 2, 0, 1006739, 300069, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_300069_1006739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300069 ⟨1006739, by decide⟩ :=
  accepted_of_selected 12 300069 ⟨1006739, by decide⟩ ⟨12, 2, 0, 1006739, 300069, 2885, 65536⟩
    (by decide) selected_cut_37611

theorem selected_cut_37612 : selected 9 ⟨1006784, by decide⟩
    (prefixPartial 12 300070) = some ⟨12, 2, 0, 1006784, 300070, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_300070_1006784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300070 ⟨1006784, by decide⟩ :=
  accepted_of_selected 12 300070 ⟨1006784, by decide⟩ ⟨12, 2, 0, 1006784, 300070, 3037, 65536⟩
    (by decide) selected_cut_37612

theorem selected_cut_37613 : selected 9 ⟨1006837, by decide⟩
    (prefixPartial 12 300071) = some ⟨12, 2, 0, 1006837, 300071, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_300071_1006837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300071 ⟨1006837, by decide⟩ :=
  accepted_of_selected 12 300071 ⟨1006837, by decide⟩ ⟨12, 2, 0, 1006837, 300071, 3289, 65536⟩
    (by decide) selected_cut_37613

theorem unmarked_context_11_75017_1006838 : frontier 10 ⟨1006838, by decide⟩
    (prefixCache 11 75017) (prefixPartial 11 75017) = false := by
  decide +kernel

theorem node_context_11_75017_1006838 : EJMOriginalGlobalDAGData.nodes 10 ⟨1006838, by decide⟩ =
    .split (coordinate 11) (![⟨1006690, by decide⟩,⟨1006739, by decide⟩,⟨1006784, by decide⟩,⟨1006837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75017_1006838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75017 ⟨1006838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75017
    ⟨1006838, by decide⟩ (by decide) (![⟨1006690, by decide⟩,⟨1006739, by decide⟩,⟨1006784, by decide⟩,⟨1006837, by decide⟩]) unmarked_context_11_75017_1006838 node_context_11_75017_1006838
  intro a
  fin_cases a
  · exact context_12_300068_1006690
  · exact context_12_300069_1006739
  · exact context_12_300070_1006784
  · exact context_12_300071_1006837

theorem selected_cut_37614 : selected 9 ⟨1006905, by decide⟩
    (prefixPartial 12 300072) = some ⟨12, 2, 0, 1006905, 300072, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_300072_1006905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300072 ⟨1006905, by decide⟩ :=
  accepted_of_selected 12 300072 ⟨1006905, by decide⟩ ⟨12, 2, 0, 1006905, 300072, 3413, 65536⟩
    (by decide) selected_cut_37614

theorem selected_cut_37615 : selected 9 ⟨1006975, by decide⟩
    (prefixPartial 12 300073) = some ⟨12, 2, 0, 1006975, 300073, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_300073_1006975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300073 ⟨1006975, by decide⟩ :=
  accepted_of_selected 12 300073 ⟨1006975, by decide⟩ ⟨12, 2, 0, 1006975, 300073, 3357, 65536⟩
    (by decide) selected_cut_37615

theorem selected_cut_37616 : selected 9 ⟨592223, by decide⟩
    (prefixPartial 12 300074) = some ⟨12, 1, 0, 592223, 300074, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300074_592223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300074 ⟨592223, by decide⟩ :=
  accepted_of_selected 12 300074 ⟨592223, by decide⟩ ⟨12, 1, 0, 592223, 300074, 1, 65536⟩
    (by decide) selected_cut_37616

theorem selected_cut_37617 : selected 9 ⟨1007058, by decide⟩
    (prefixPartial 12 300075) = some ⟨12, 2, 0, 1007058, 300075, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_300075_1007058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300075 ⟨1007058, by decide⟩ :=
  accepted_of_selected 12 300075 ⟨1007058, by decide⟩ ⟨12, 2, 0, 1007058, 300075, 4017, 65536⟩
    (by decide) selected_cut_37617

theorem unmarked_context_11_75018_1007059 : frontier 10 ⟨1007059, by decide⟩
    (prefixCache 11 75018) (prefixPartial 11 75018) = false := by
  decide +kernel

theorem node_context_11_75018_1007059 : EJMOriginalGlobalDAGData.nodes 10 ⟨1007059, by decide⟩ =
    .split (coordinate 11) (![⟨1006905, by decide⟩,⟨1006975, by decide⟩,⟨592223, by decide⟩,⟨1007058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75018_1007059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75018 ⟨1007059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75018
    ⟨1007059, by decide⟩ (by decide) (![⟨1006905, by decide⟩,⟨1006975, by decide⟩,⟨592223, by decide⟩,⟨1007058, by decide⟩]) unmarked_context_11_75018_1007059 node_context_11_75018_1007059
  intro a
  fin_cases a
  · exact context_12_300072_1006905
  · exact context_12_300073_1006975
  · exact context_12_300074_592223
  · exact context_12_300075_1007058

theorem selected_cut_37618 : selected 9 ⟨1007115, by decide⟩
    (prefixPartial 12 300076) = some ⟨12, 2, 0, 1007115, 300076, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_300076_1007115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300076 ⟨1007115, by decide⟩ :=
  accepted_of_selected 12 300076 ⟨1007115, by decide⟩ ⟨12, 2, 0, 1007115, 300076, 3197, 65536⟩
    (by decide) selected_cut_37618

theorem selected_cut_37619 : selected 9 ⟨1007173, by decide⟩
    (prefixPartial 12 300077) = some ⟨12, 2, 0, 1007173, 300077, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_300077_1007173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300077 ⟨1007173, by decide⟩ :=
  accepted_of_selected 12 300077 ⟨1007173, by decide⟩ ⟨12, 2, 0, 1007173, 300077, 3301, 65536⟩
    (by decide) selected_cut_37619

theorem selected_cut_37620 : selected 9 ⟨1007240, by decide⟩
    (prefixPartial 12 300078) = some ⟨12, 2, 0, 1007240, 300078, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_300078_1007240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300078 ⟨1007240, by decide⟩ :=
  accepted_of_selected 12 300078 ⟨1007240, by decide⟩ ⟨12, 2, 0, 1007240, 300078, 3533, 65536⟩
    (by decide) selected_cut_37620

theorem selected_cut_37621 : selected 9 ⟨1007301, by decide⟩
    (prefixPartial 12 300079) = some ⟨12, 2, 0, 1007301, 300079, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_300079_1007301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300079 ⟨1007301, by decide⟩ :=
  accepted_of_selected 12 300079 ⟨1007301, by decide⟩ ⟨12, 2, 0, 1007301, 300079, 3437, 65536⟩
    (by decide) selected_cut_37621

theorem unmarked_context_11_75019_1007302 : frontier 10 ⟨1007302, by decide⟩
    (prefixCache 11 75019) (prefixPartial 11 75019) = false := by
  decide +kernel

theorem node_context_11_75019_1007302 : EJMOriginalGlobalDAGData.nodes 10 ⟨1007302, by decide⟩ =
    .split (coordinate 11) (![⟨1007115, by decide⟩,⟨1007173, by decide⟩,⟨1007240, by decide⟩,⟨1007301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75019_1007302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75019 ⟨1007302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75019
    ⟨1007302, by decide⟩ (by decide) (![⟨1007115, by decide⟩,⟨1007173, by decide⟩,⟨1007240, by decide⟩,⟨1007301, by decide⟩]) unmarked_context_11_75019_1007302 node_context_11_75019_1007302
  intro a
  fin_cases a
  · exact context_12_300076_1007115
  · exact context_12_300077_1007173
  · exact context_12_300078_1007240
  · exact context_12_300079_1007301

theorem unmarked_context_10_18754_1007303 : frontier 11 ⟨1007303, by decide⟩
    (prefixCache 10 18754) (prefixPartial 10 18754) = false := by
  decide +kernel

theorem node_context_10_18754_1007303 : EJMOriginalGlobalDAGData.nodes 11 ⟨1007303, by decide⟩ =
    .split (coordinate 10) (![⟨1006638, by decide⟩,⟨1006838, by decide⟩,⟨1007059, by decide⟩,⟨1007302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18754_1007303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18754 ⟨1007303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18754
    ⟨1007303, by decide⟩ (by decide) (![⟨1006638, by decide⟩,⟨1006838, by decide⟩,⟨1007059, by decide⟩,⟨1007302, by decide⟩]) unmarked_context_10_18754_1007303 node_context_10_18754_1007303
  intro a
  fin_cases a
  · exact context_11_75016_1006638
  · exact context_11_75017_1006838
  · exact context_11_75018_1007059
  · exact context_11_75019_1007302

theorem selected_cut_37622 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 300080) = some ⟨12, 1, 0, 985390, 300080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_300080_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300080 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 300080 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 300080, 1, 65536⟩
    (by decide) selected_cut_37622

theorem selected_cut_37623 : selected 9 ⟨1007344, by decide⟩
    (prefixPartial 12 300081) = some ⟨12, 2, 0, 1007344, 300081, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_300081_1007344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300081 ⟨1007344, by decide⟩ :=
  accepted_of_selected 12 300081 ⟨1007344, by decide⟩ ⟨12, 2, 0, 1007344, 300081, 2757, 65536⟩
    (by decide) selected_cut_37623

theorem selected_cut_37624 : selected 9 ⟨1007379, by decide⟩
    (prefixPartial 12 300082) = some ⟨12, 2, 0, 1007379, 300082, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_300082_1007379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300082 ⟨1007379, by decide⟩ :=
  accepted_of_selected 12 300082 ⟨1007379, by decide⟩ ⟨12, 2, 0, 1007379, 300082, 2621, 65536⟩
    (by decide) selected_cut_37624

theorem selected_cut_37625 : selected 9 ⟨1007430, by decide⟩
    (prefixPartial 12 300083) = some ⟨12, 2, 0, 1007430, 300083, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_300083_1007430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300083 ⟨1007430, by decide⟩ :=
  accepted_of_selected 12 300083 ⟨1007430, by decide⟩ ⟨12, 2, 0, 1007430, 300083, 2929, 65536⟩
    (by decide) selected_cut_37625

theorem unmarked_context_11_75020_1007431 : frontier 10 ⟨1007431, by decide⟩
    (prefixCache 11 75020) (prefixPartial 11 75020) = false := by
  decide +kernel

theorem node_context_11_75020_1007431 : EJMOriginalGlobalDAGData.nodes 10 ⟨1007431, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1007344, by decide⟩,⟨1007379, by decide⟩,⟨1007430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75020_1007431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75020 ⟨1007431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75020
    ⟨1007431, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1007344, by decide⟩,⟨1007379, by decide⟩,⟨1007430, by decide⟩]) unmarked_context_11_75020_1007431 node_context_11_75020_1007431
  intro a
  fin_cases a
  · exact context_12_300080_985390
  · exact context_12_300081_1007344
  · exact context_12_300082_1007379
  · exact context_12_300083_1007430

theorem selected_cut_37626 : selected 9 ⟨1007484, by decide⟩
    (prefixPartial 12 300084) = some ⟨12, 2, 0, 1007484, 300084, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_300084_1007484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300084 ⟨1007484, by decide⟩ :=
  accepted_of_selected 12 300084 ⟨1007484, by decide⟩ ⟨12, 2, 0, 1007484, 300084, 2985, 65536⟩
    (by decide) selected_cut_37626

theorem selected_cut_37627 : selected 9 ⟨1007533, by decide⟩
    (prefixPartial 12 300085) = some ⟨12, 2, 0, 1007533, 300085, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_300085_1007533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300085 ⟨1007533, by decide⟩ :=
  accepted_of_selected 12 300085 ⟨1007533, by decide⟩ ⟨12, 2, 0, 1007533, 300085, 2829, 65536⟩
    (by decide) selected_cut_37627

theorem selected_cut_37628 : selected 9 ⟨1007581, by decide⟩
    (prefixPartial 12 300086) = some ⟨12, 2, 0, 1007581, 300086, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_300086_1007581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300086 ⟨1007581, by decide⟩ :=
  accepted_of_selected 12 300086 ⟨1007581, by decide⟩ ⟨12, 2, 0, 1007581, 300086, 2937, 65536⟩
    (by decide) selected_cut_37628

theorem selected_cut_37629 : selected 9 ⟨1007635, by decide⟩
    (prefixPartial 12 300087) = some ⟨12, 2, 0, 1007635, 300087, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_300087_1007635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300087 ⟨1007635, by decide⟩ :=
  accepted_of_selected 12 300087 ⟨1007635, by decide⟩ ⟨12, 2, 0, 1007635, 300087, 3217, 65536⟩
    (by decide) selected_cut_37629

theorem unmarked_context_11_75021_1007636 : frontier 10 ⟨1007636, by decide⟩
    (prefixCache 11 75021) (prefixPartial 11 75021) = false := by
  decide +kernel

theorem node_context_11_75021_1007636 : EJMOriginalGlobalDAGData.nodes 10 ⟨1007636, by decide⟩ =
    .split (coordinate 11) (![⟨1007484, by decide⟩,⟨1007533, by decide⟩,⟨1007581, by decide⟩,⟨1007635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75021_1007636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75021 ⟨1007636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75021
    ⟨1007636, by decide⟩ (by decide) (![⟨1007484, by decide⟩,⟨1007533, by decide⟩,⟨1007581, by decide⟩,⟨1007635, by decide⟩]) unmarked_context_11_75021_1007636 node_context_11_75021_1007636
  intro a
  fin_cases a
  · exact context_12_300084_1007484
  · exact context_12_300085_1007533
  · exact context_12_300086_1007581
  · exact context_12_300087_1007635

theorem selected_cut_37630 : selected 9 ⟨1007684, by decide⟩
    (prefixPartial 12 300088) = some ⟨12, 2, 0, 1007684, 300088, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_300088_1007684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300088 ⟨1007684, by decide⟩ :=
  accepted_of_selected 12 300088 ⟨1007684, by decide⟩ ⟨12, 2, 0, 1007684, 300088, 3009, 65536⟩
    (by decide) selected_cut_37630

theorem selected_cut_37631 : selected 9 ⟨1007736, by decide⟩
    (prefixPartial 12 300089) = some ⟨12, 2, 0, 1007736, 300089, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_300089_1007736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300089 ⟨1007736, by decide⟩ :=
  accepted_of_selected 12 300089 ⟨1007736, by decide⟩ ⟨12, 2, 0, 1007736, 300089, 2957, 65536⟩
    (by decide) selected_cut_37631

theorem selected_cut_37632 : selected 9 ⟨1007793, by decide⟩
    (prefixPartial 12 300090) = some ⟨12, 2, 0, 1007793, 300090, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_300090_1007793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300090 ⟨1007793, by decide⟩ :=
  accepted_of_selected 12 300090 ⟨1007793, by decide⟩ ⟨12, 2, 0, 1007793, 300090, 2957, 65536⟩
    (by decide) selected_cut_37632

theorem selected_cut_37633 : selected 9 ⟨1007866, by decide⟩
    (prefixPartial 12 300091) = some ⟨12, 2, 0, 1007866, 300091, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_300091_1007866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300091 ⟨1007866, by decide⟩ :=
  accepted_of_selected 12 300091 ⟨1007866, by decide⟩ ⟨12, 2, 0, 1007866, 300091, 3469, 65536⟩
    (by decide) selected_cut_37633

theorem unmarked_context_11_75022_1007867 : frontier 10 ⟨1007867, by decide⟩
    (prefixCache 11 75022) (prefixPartial 11 75022) = false := by
  decide +kernel

theorem node_context_11_75022_1007867 : EJMOriginalGlobalDAGData.nodes 10 ⟨1007867, by decide⟩ =
    .split (coordinate 11) (![⟨1007684, by decide⟩,⟨1007736, by decide⟩,⟨1007793, by decide⟩,⟨1007866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75022_1007867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75022 ⟨1007867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75022
    ⟨1007867, by decide⟩ (by decide) (![⟨1007684, by decide⟩,⟨1007736, by decide⟩,⟨1007793, by decide⟩,⟨1007866, by decide⟩]) unmarked_context_11_75022_1007867 node_context_11_75022_1007867
  intro a
  fin_cases a
  · exact context_12_300088_1007684
  · exact context_12_300089_1007736
  · exact context_12_300090_1007793
  · exact context_12_300091_1007866

theorem selected_cut_37634 : selected 9 ⟨1007910, by decide⟩
    (prefixPartial 12 300092) = some ⟨12, 2, 0, 1007910, 300092, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_300092_1007910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 300092 ⟨1007910, by decide⟩ :=
  accepted_of_selected 12 300092 ⟨1007910, by decide⟩ ⟨12, 2, 0, 1007910, 300092, 2745, 65536⟩
    (by decide) selected_cut_37634

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
