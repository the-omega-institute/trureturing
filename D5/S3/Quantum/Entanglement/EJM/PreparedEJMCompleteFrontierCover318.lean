/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover317
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30532 : selected 8 ⟨773633, by decide⟩
    (prefixPartial 13 418939) = some ⟨13, 2, 0, 773633, 418939, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_418939_773633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418939 ⟨773633, by decide⟩ :=
  accepted_of_selected 13 418939 ⟨773633, by decide⟩ ⟨13, 2, 0, 773633, 418939, 1049, 16384⟩
    (by decide) selected_cut_30532

theorem unmarked_context_12_104734_773634 : frontier 9 ⟨773634, by decide⟩
    (prefixCache 12 104734) (prefixPartial 12 104734) = false := by
  decide +kernel

theorem node_context_12_104734_773634 : EJMOriginalGlobalDAGData.nodes 9 ⟨773634, by decide⟩ =
    .split (coordinate 12) (![⟨773519, by decide⟩,⟨773565, by decide⟩,⟨773602, by decide⟩,⟨773633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104734_773634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104734 ⟨773634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104734
    ⟨773634, by decide⟩ (by decide) (![⟨773519, by decide⟩,⟨773565, by decide⟩,⟨773602, by decide⟩,⟨773633, by decide⟩]) unmarked_context_12_104734_773634 node_context_12_104734_773634
  intro a
  fin_cases a
  · exact context_13_418936_773519
  · exact context_13_418937_773565
  · exact context_13_418938_773602
  · exact context_13_418939_773633

theorem selected_cut_30533 : selected 8 ⟨773663, by decide⟩
    (prefixPartial 13 418940) = some ⟨13, 2, 0, 773663, 418940, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_418940_773663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418940 ⟨773663, by decide⟩ :=
  accepted_of_selected 13 418940 ⟨773663, by decide⟩ ⟨13, 2, 0, 773663, 418940, 1585, 16384⟩
    (by decide) selected_cut_30533

theorem selected_cut_30534 : selected 8 ⟨773701, by decide⟩
    (prefixPartial 13 418941) = some ⟨13, 2, 0, 773701, 418941, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_418941_773701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418941 ⟨773701, by decide⟩ :=
  accepted_of_selected 13 418941 ⟨773701, by decide⟩ ⟨13, 2, 0, 773701, 418941, 2189, 16384⟩
    (by decide) selected_cut_30534

theorem selected_cut_30535 : selected 8 ⟨773750, by decide⟩
    (prefixPartial 13 418942) = some ⟨13, 2, 0, 773750, 418942, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_418942_773750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418942 ⟨773750, by decide⟩ :=
  accepted_of_selected 13 418942 ⟨773750, by decide⟩ ⟨13, 2, 0, 773750, 418942, 1601, 16384⟩
    (by decide) selected_cut_30535

theorem selected_cut_30536 : selected 8 ⟨773778, by decide⟩
    (prefixPartial 13 418943) = some ⟨13, 2, 0, 773778, 418943, 953, 16384⟩ := by
  decide +kernel

theorem context_13_418943_773778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418943 ⟨773778, by decide⟩ :=
  accepted_of_selected 13 418943 ⟨773778, by decide⟩ ⟨13, 2, 0, 773778, 418943, 953, 16384⟩
    (by decide) selected_cut_30536

theorem unmarked_context_12_104735_773779 : frontier 9 ⟨773779, by decide⟩
    (prefixCache 12 104735) (prefixPartial 12 104735) = false := by
  decide +kernel

theorem node_context_12_104735_773779 : EJMOriginalGlobalDAGData.nodes 9 ⟨773779, by decide⟩ =
    .split (coordinate 12) (![⟨773663, by decide⟩,⟨773701, by decide⟩,⟨773750, by decide⟩,⟨773778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104735_773779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104735 ⟨773779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104735
    ⟨773779, by decide⟩ (by decide) (![⟨773663, by decide⟩,⟨773701, by decide⟩,⟨773750, by decide⟩,⟨773778, by decide⟩]) unmarked_context_12_104735_773779 node_context_12_104735_773779
  intro a
  fin_cases a
  · exact context_13_418940_773663
  · exact context_13_418941_773701
  · exact context_13_418942_773750
  · exact context_13_418943_773778

theorem unmarked_context_11_26183_773780 : frontier 10 ⟨773780, by decide⟩
    (prefixCache 11 26183) (prefixPartial 11 26183) = false := by
  decide +kernel

theorem node_context_11_26183_773780 : EJMOriginalGlobalDAGData.nodes 10 ⟨773780, by decide⟩ =
    .split (coordinate 11) (![⟨773370, by decide⟩,⟨773489, by decide⟩,⟨773634, by decide⟩,⟨773779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26183_773780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26183 ⟨773780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26183
    ⟨773780, by decide⟩ (by decide) (![⟨773370, by decide⟩,⟨773489, by decide⟩,⟨773634, by decide⟩,⟨773779, by decide⟩]) unmarked_context_11_26183_773780 node_context_11_26183_773780
  intro a
  fin_cases a
  · exact context_12_104732_773370
  · exact context_12_104733_773489
  · exact context_12_104734_773634
  · exact context_12_104735_773779

theorem unmarked_context_10_6545_773781 : frontier 11 ⟨773781, by decide⟩
    (prefixCache 10 6545) (prefixPartial 10 6545) = false := by
  decide +kernel

theorem node_context_10_6545_773781 : EJMOriginalGlobalDAGData.nodes 11 ⟨773781, by decide⟩ =
    .split (coordinate 10) (![⟨772344, by decide⟩,⟨772757, by decide⟩,⟨773230, by decide⟩,⟨773780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6545_773781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6545 ⟨773781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6545
    ⟨773781, by decide⟩ (by decide) (![⟨772344, by decide⟩,⟨772757, by decide⟩,⟨773230, by decide⟩,⟨773780, by decide⟩]) unmarked_context_10_6545_773781 node_context_10_6545_773781
  intro a
  fin_cases a
  · exact context_11_26180_772344
  · exact context_11_26181_772757
  · exact context_11_26182_773230
  · exact context_11_26183_773780

theorem selected_cut_30537 : selected 8 ⟨773811, by decide⟩
    (prefixPartial 13 418944) = some ⟨13, 2, 0, 773811, 418944, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_418944_773811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418944 ⟨773811, by decide⟩ :=
  accepted_of_selected 13 418944 ⟨773811, by decide⟩ ⟨13, 2, 0, 773811, 418944, 1149, 16384⟩
    (by decide) selected_cut_30537

theorem selected_cut_30538 : selected 8 ⟨773845, by decide⟩
    (prefixPartial 13 418945) = some ⟨13, 2, 0, 773845, 418945, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_418945_773845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418945 ⟨773845, by decide⟩ :=
  accepted_of_selected 13 418945 ⟨773845, by decide⟩ ⟨13, 2, 0, 773845, 418945, 1469, 16384⟩
    (by decide) selected_cut_30538

theorem selected_cut_30539 : selected 8 ⟨773866, by decide⟩
    (prefixPartial 13 418946) = some ⟨13, 2, 0, 773866, 418946, 845, 16384⟩ := by
  decide +kernel

theorem context_13_418946_773866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418946 ⟨773866, by decide⟩ :=
  accepted_of_selected 13 418946 ⟨773866, by decide⟩ ⟨13, 2, 0, 773866, 418946, 845, 16384⟩
    (by decide) selected_cut_30539

theorem selected_cut_30540 : selected 8 ⟨773880, by decide⟩
    (prefixPartial 13 418947) = some ⟨13, 2, 0, 773880, 418947, 801, 16384⟩ := by
  decide +kernel

theorem context_13_418947_773880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418947 ⟨773880, by decide⟩ :=
  accepted_of_selected 13 418947 ⟨773880, by decide⟩ ⟨13, 2, 0, 773880, 418947, 801, 16384⟩
    (by decide) selected_cut_30540

theorem unmarked_context_12_104736_773881 : frontier 9 ⟨773881, by decide⟩
    (prefixCache 12 104736) (prefixPartial 12 104736) = false := by
  decide +kernel

theorem node_context_12_104736_773881 : EJMOriginalGlobalDAGData.nodes 9 ⟨773881, by decide⟩ =
    .split (coordinate 12) (![⟨773811, by decide⟩,⟨773845, by decide⟩,⟨773866, by decide⟩,⟨773880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104736_773881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104736 ⟨773881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104736
    ⟨773881, by decide⟩ (by decide) (![⟨773811, by decide⟩,⟨773845, by decide⟩,⟨773866, by decide⟩,⟨773880, by decide⟩]) unmarked_context_12_104736_773881 node_context_12_104736_773881
  intro a
  fin_cases a
  · exact context_13_418944_773811
  · exact context_13_418945_773845
  · exact context_13_418946_773866
  · exact context_13_418947_773880

theorem selected_cut_30541 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 104737) = some ⟨12, 1, 0, 772506, 104737, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104737_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104737 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 104737 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 104737, 1, 65536⟩
    (by decide) selected_cut_30541

theorem selected_cut_30542 : selected 8 ⟨773908, by decide⟩
    (prefixPartial 13 418952) = some ⟨13, 2, 0, 773908, 418952, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_418952_773908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418952 ⟨773908, by decide⟩ :=
  accepted_of_selected 13 418952 ⟨773908, by decide⟩ ⟨13, 2, 0, 773908, 418952, 1309, 16384⟩
    (by decide) selected_cut_30542

theorem selected_cut_30543 : selected 8 ⟨773947, by decide⟩
    (prefixPartial 13 418953) = some ⟨13, 2, 0, 773947, 418953, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_418953_773947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418953 ⟨773947, by decide⟩ :=
  accepted_of_selected 13 418953 ⟨773947, by decide⟩ ⟨13, 2, 0, 773947, 418953, 1737, 16384⟩
    (by decide) selected_cut_30543

theorem selected_cut_30544 : selected 8 ⟨773976, by decide⟩
    (prefixPartial 13 418954) = some ⟨13, 2, 0, 773976, 418954, 993, 16384⟩ := by
  decide +kernel

theorem context_13_418954_773976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418954 ⟨773976, by decide⟩ :=
  accepted_of_selected 13 418954 ⟨773976, by decide⟩ ⟨13, 2, 0, 773976, 418954, 993, 16384⟩
    (by decide) selected_cut_30544

theorem selected_cut_30545 : selected 8 ⟨773989, by decide⟩
    (prefixPartial 13 418955) = some ⟨13, 2, 0, 773989, 418955, 857, 16384⟩ := by
  decide +kernel

theorem context_13_418955_773989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418955 ⟨773989, by decide⟩ :=
  accepted_of_selected 13 418955 ⟨773989, by decide⟩ ⟨13, 2, 0, 773989, 418955, 857, 16384⟩
    (by decide) selected_cut_30545

theorem unmarked_context_12_104738_773990 : frontier 9 ⟨773990, by decide⟩
    (prefixCache 12 104738) (prefixPartial 12 104738) = false := by
  decide +kernel

theorem node_context_12_104738_773990 : EJMOriginalGlobalDAGData.nodes 9 ⟨773990, by decide⟩ =
    .split (coordinate 12) (![⟨773908, by decide⟩,⟨773947, by decide⟩,⟨773976, by decide⟩,⟨773989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104738_773990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104738 ⟨773990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104738
    ⟨773990, by decide⟩ (by decide) (![⟨773908, by decide⟩,⟨773947, by decide⟩,⟨773976, by decide⟩,⟨773989, by decide⟩]) unmarked_context_12_104738_773990 node_context_12_104738_773990
  intro a
  fin_cases a
  · exact context_13_418952_773908
  · exact context_13_418953_773947
  · exact context_13_418954_773976
  · exact context_13_418955_773989

theorem selected_cut_30546 : selected 8 ⟨774019, by decide⟩
    (prefixPartial 13 418956) = some ⟨13, 2, 0, 774019, 418956, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_418956_774019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418956 ⟨774019, by decide⟩ :=
  accepted_of_selected 13 418956 ⟨774019, by decide⟩ ⟨13, 2, 0, 774019, 418956, 1273, 16384⟩
    (by decide) selected_cut_30546

theorem selected_cut_30547 : selected 8 ⟨774047, by decide⟩
    (prefixPartial 13 418957) = some ⟨13, 2, 0, 774047, 418957, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_418957_774047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418957 ⟨774047, by decide⟩ :=
  accepted_of_selected 13 418957 ⟨774047, by decide⟩ ⟨13, 2, 0, 774047, 418957, 1785, 16384⟩
    (by decide) selected_cut_30547

theorem selected_cut_30548 : selected 8 ⟨774074, by decide⟩
    (prefixPartial 13 418958) = some ⟨13, 2, 0, 774074, 418958, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_418958_774074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418958 ⟨774074, by decide⟩ :=
  accepted_of_selected 13 418958 ⟨774074, by decide⟩ ⟨13, 2, 0, 774074, 418958, 1129, 16384⟩
    (by decide) selected_cut_30548

theorem selected_cut_30549 : selected 8 ⟨774087, by decide⟩
    (prefixPartial 13 418959) = some ⟨13, 2, 0, 774087, 418959, 845, 16384⟩ := by
  decide +kernel

theorem context_13_418959_774087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418959 ⟨774087, by decide⟩ :=
  accepted_of_selected 13 418959 ⟨774087, by decide⟩ ⟨13, 2, 0, 774087, 418959, 845, 16384⟩
    (by decide) selected_cut_30549

theorem unmarked_context_12_104739_774088 : frontier 9 ⟨774088, by decide⟩
    (prefixCache 12 104739) (prefixPartial 12 104739) = false := by
  decide +kernel

theorem node_context_12_104739_774088 : EJMOriginalGlobalDAGData.nodes 9 ⟨774088, by decide⟩ =
    .split (coordinate 12) (![⟨774019, by decide⟩,⟨774047, by decide⟩,⟨774074, by decide⟩,⟨774087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104739_774088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104739 ⟨774088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104739
    ⟨774088, by decide⟩ (by decide) (![⟨774019, by decide⟩,⟨774047, by decide⟩,⟨774074, by decide⟩,⟨774087, by decide⟩]) unmarked_context_12_104739_774088 node_context_12_104739_774088
  intro a
  fin_cases a
  · exact context_13_418956_774019
  · exact context_13_418957_774047
  · exact context_13_418958_774074
  · exact context_13_418959_774087

theorem unmarked_context_11_26184_774089 : frontier 10 ⟨774089, by decide⟩
    (prefixCache 11 26184) (prefixPartial 11 26184) = false := by
  decide +kernel

theorem node_context_11_26184_774089 : EJMOriginalGlobalDAGData.nodes 10 ⟨774089, by decide⟩ =
    .split (coordinate 11) (![⟨773881, by decide⟩,⟨772506, by decide⟩,⟨773990, by decide⟩,⟨774088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26184_774089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26184 ⟨774089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26184
    ⟨774089, by decide⟩ (by decide) (![⟨773881, by decide⟩,⟨772506, by decide⟩,⟨773990, by decide⟩,⟨774088, by decide⟩]) unmarked_context_11_26184_774089 node_context_11_26184_774089
  intro a
  fin_cases a
  · exact context_12_104736_773881
  · exact context_12_104737_772506
  · exact context_12_104738_773990
  · exact context_12_104739_774088

theorem selected_cut_30550 : selected 9 ⟨455939, by decide⟩
    (prefixPartial 12 104740) = some ⟨12, 1, 0, 455939, 104740, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104740_455939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104740 ⟨455939, by decide⟩ :=
  accepted_of_selected 12 104740 ⟨455939, by decide⟩ ⟨12, 1, 0, 455939, 104740, 1, 65536⟩
    (by decide) selected_cut_30550

theorem selected_cut_30551 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 104741) = some ⟨12, 1, 0, 772506, 104741, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104741_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104741 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 104741 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 104741, 1, 65536⟩
    (by decide) selected_cut_30551

theorem selected_cut_30552 : selected 9 ⟨774191, by decide⟩
    (prefixPartial 12 104742) = some ⟨12, 2, 0, 774191, 104742, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_104742_774191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104742 ⟨774191, by decide⟩ :=
  accepted_of_selected 12 104742 ⟨774191, by decide⟩ ⟨12, 2, 0, 774191, 104742, 3257, 65536⟩
    (by decide) selected_cut_30552

theorem selected_cut_30553 : selected 8 ⟨774227, by decide⟩
    (prefixPartial 13 418972) = some ⟨13, 2, 0, 774227, 418972, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_418972_774227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418972 ⟨774227, by decide⟩ :=
  accepted_of_selected 13 418972 ⟨774227, by decide⟩ ⟨13, 2, 0, 774227, 418972, 1157, 16384⟩
    (by decide) selected_cut_30553

theorem selected_cut_30554 : selected 8 ⟨774269, by decide⟩
    (prefixPartial 13 418973) = some ⟨13, 2, 0, 774269, 418973, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_418973_774269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418973 ⟨774269, by decide⟩ :=
  accepted_of_selected 13 418973 ⟨774269, by decide⟩ ⟨13, 2, 0, 774269, 418973, 1921, 16384⟩
    (by decide) selected_cut_30554

theorem selected_cut_30555 : selected 8 ⟨774297, by decide⟩
    (prefixPartial 13 418974) = some ⟨13, 2, 0, 774297, 418974, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_418974_774297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418974 ⟨774297, by decide⟩ :=
  accepted_of_selected 13 418974 ⟨774297, by decide⟩ ⟨13, 2, 0, 774297, 418974, 1041, 16384⟩
    (by decide) selected_cut_30555

theorem selected_cut_30556 : selected 8 ⟨774310, by decide⟩
    (prefixPartial 13 418975) = some ⟨13, 2, 0, 774310, 418975, 809, 16384⟩ := by
  decide +kernel

theorem context_13_418975_774310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418975 ⟨774310, by decide⟩ :=
  accepted_of_selected 13 418975 ⟨774310, by decide⟩ ⟨13, 2, 0, 774310, 418975, 809, 16384⟩
    (by decide) selected_cut_30556

theorem unmarked_context_12_104743_774311 : frontier 9 ⟨774311, by decide⟩
    (prefixCache 12 104743) (prefixPartial 12 104743) = false := by
  decide +kernel

theorem node_context_12_104743_774311 : EJMOriginalGlobalDAGData.nodes 9 ⟨774311, by decide⟩ =
    .split (coordinate 12) (![⟨774227, by decide⟩,⟨774269, by decide⟩,⟨774297, by decide⟩,⟨774310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104743_774311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104743 ⟨774311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104743
    ⟨774311, by decide⟩ (by decide) (![⟨774227, by decide⟩,⟨774269, by decide⟩,⟨774297, by decide⟩,⟨774310, by decide⟩]) unmarked_context_12_104743_774311 node_context_12_104743_774311
  intro a
  fin_cases a
  · exact context_13_418972_774227
  · exact context_13_418973_774269
  · exact context_13_418974_774297
  · exact context_13_418975_774310

theorem unmarked_context_11_26185_774312 : frontier 10 ⟨774312, by decide⟩
    (prefixCache 11 26185) (prefixPartial 11 26185) = false := by
  decide +kernel

theorem node_context_11_26185_774312 : EJMOriginalGlobalDAGData.nodes 10 ⟨774312, by decide⟩ =
    .split (coordinate 11) (![⟨455939, by decide⟩,⟨772506, by decide⟩,⟨774191, by decide⟩,⟨774311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26185_774312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26185 ⟨774312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26185
    ⟨774312, by decide⟩ (by decide) (![⟨455939, by decide⟩,⟨772506, by decide⟩,⟨774191, by decide⟩,⟨774311, by decide⟩]) unmarked_context_11_26185_774312 node_context_11_26185_774312
  intro a
  fin_cases a
  · exact context_12_104740_455939
  · exact context_12_104741_772506
  · exact context_12_104742_774191
  · exact context_12_104743_774311

theorem selected_cut_30557 : selected 10 ⟨766338, by decide⟩
    (prefixPartial 11 26186) = some ⟨11, 1, 0, 766338, 26186, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26186_766338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26186 ⟨766338, by decide⟩ :=
  accepted_of_selected 11 26186 ⟨766338, by decide⟩ ⟨11, 1, 0, 766338, 26186, 1, 262144⟩
    (by decide) selected_cut_30557

theorem selected_cut_30558 : selected 8 ⟨774336, by decide⟩
    (prefixPartial 13 418992) = some ⟨13, 2, 0, 774336, 418992, 857, 16384⟩ := by
  decide +kernel

theorem context_13_418992_774336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418992 ⟨774336, by decide⟩ :=
  accepted_of_selected 13 418992 ⟨774336, by decide⟩ ⟨13, 2, 0, 774336, 418992, 857, 16384⟩
    (by decide) selected_cut_30558

theorem selected_cut_30559 : selected 8 ⟨774370, by decide⟩
    (prefixPartial 13 418993) = some ⟨13, 2, 0, 774370, 418993, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_418993_774370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418993 ⟨774370, by decide⟩ :=
  accepted_of_selected 13 418993 ⟨774370, by decide⟩ ⟨13, 2, 0, 774370, 418993, 1609, 16384⟩
    (by decide) selected_cut_30559

theorem selected_cut_30560 : selected 8 ⟨774400, by decide⟩
    (prefixPartial 13 418994) = some ⟨13, 2, 0, 774400, 418994, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_418994_774400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418994 ⟨774400, by decide⟩ :=
  accepted_of_selected 13 418994 ⟨774400, by decide⟩ ⟨13, 2, 0, 774400, 418994, 1029, 16384⟩
    (by decide) selected_cut_30560

theorem selected_cut_30561 : selected 8 ⟨774424, by decide⟩
    (prefixPartial 13 418995) = some ⟨13, 2, 0, 774424, 418995, 937, 16384⟩ := by
  decide +kernel

theorem context_13_418995_774424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418995 ⟨774424, by decide⟩ :=
  accepted_of_selected 13 418995 ⟨774424, by decide⟩ ⟨13, 2, 0, 774424, 418995, 937, 16384⟩
    (by decide) selected_cut_30561

theorem unmarked_context_12_104748_774425 : frontier 9 ⟨774425, by decide⟩
    (prefixCache 12 104748) (prefixPartial 12 104748) = false := by
  decide +kernel

theorem node_context_12_104748_774425 : EJMOriginalGlobalDAGData.nodes 9 ⟨774425, by decide⟩ =
    .split (coordinate 12) (![⟨774336, by decide⟩,⟨774370, by decide⟩,⟨774400, by decide⟩,⟨774424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104748_774425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104748 ⟨774425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104748
    ⟨774425, by decide⟩ (by decide) (![⟨774336, by decide⟩,⟨774370, by decide⟩,⟨774400, by decide⟩,⟨774424, by decide⟩]) unmarked_context_12_104748_774425 node_context_12_104748_774425
  intro a
  fin_cases a
  · exact context_13_418992_774336
  · exact context_13_418993_774370
  · exact context_13_418994_774400
  · exact context_13_418995_774424

theorem selected_cut_30562 : selected 8 ⟨774451, by decide⟩
    (prefixPartial 13 418996) = some ⟨13, 2, 0, 774451, 418996, 825, 16384⟩ := by
  decide +kernel

theorem context_13_418996_774451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418996 ⟨774451, by decide⟩ :=
  accepted_of_selected 13 418996 ⟨774451, by decide⟩ ⟨13, 2, 0, 774451, 418996, 825, 16384⟩
    (by decide) selected_cut_30562

theorem selected_cut_30563 : selected 8 ⟨774480, by decide⟩
    (prefixPartial 13 418997) = some ⟨13, 2, 0, 774480, 418997, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_418997_774480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418997 ⟨774480, by decide⟩ :=
  accepted_of_selected 13 418997 ⟨774480, by decide⟩ ⟨13, 2, 0, 774480, 418997, 1661, 16384⟩
    (by decide) selected_cut_30563

theorem selected_cut_30564 : selected 8 ⟨774506, by decide⟩
    (prefixPartial 13 418998) = some ⟨13, 2, 0, 774506, 418998, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_418998_774506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418998 ⟨774506, by decide⟩ :=
  accepted_of_selected 13 418998 ⟨774506, by decide⟩ ⟨13, 2, 0, 774506, 418998, 1037, 16384⟩
    (by decide) selected_cut_30564

theorem selected_cut_30565 : selected 8 ⟨774524, by decide⟩
    (prefixPartial 13 418999) = some ⟨13, 2, 0, 774524, 418999, 913, 16384⟩ := by
  decide +kernel

theorem context_13_418999_774524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418999 ⟨774524, by decide⟩ :=
  accepted_of_selected 13 418999 ⟨774524, by decide⟩ ⟨13, 2, 0, 774524, 418999, 913, 16384⟩
    (by decide) selected_cut_30565

theorem unmarked_context_12_104749_774525 : frontier 9 ⟨774525, by decide⟩
    (prefixCache 12 104749) (prefixPartial 12 104749) = false := by
  decide +kernel

theorem node_context_12_104749_774525 : EJMOriginalGlobalDAGData.nodes 9 ⟨774525, by decide⟩ =
    .split (coordinate 12) (![⟨774451, by decide⟩,⟨774480, by decide⟩,⟨774506, by decide⟩,⟨774524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104749_774525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104749 ⟨774525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104749
    ⟨774525, by decide⟩ (by decide) (![⟨774451, by decide⟩,⟨774480, by decide⟩,⟨774506, by decide⟩,⟨774524, by decide⟩]) unmarked_context_12_104749_774525 node_context_12_104749_774525
  intro a
  fin_cases a
  · exact context_13_418996_774451
  · exact context_13_418997_774480
  · exact context_13_418998_774506
  · exact context_13_418999_774524

theorem selected_cut_30566 : selected 8 ⟨774542, by decide⟩
    (prefixPartial 13 419000) = some ⟨13, 2, 0, 774542, 419000, 777, 16384⟩ := by
  decide +kernel

theorem context_13_419000_774542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419000 ⟨774542, by decide⟩ :=
  accepted_of_selected 13 419000 ⟨774542, by decide⟩ ⟨13, 2, 0, 774542, 419000, 777, 16384⟩
    (by decide) selected_cut_30566

theorem selected_cut_30567 : selected 8 ⟨774586, by decide⟩
    (prefixPartial 13 419001) = some ⟨13, 2, 0, 774586, 419001, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_419001_774586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419001 ⟨774586, by decide⟩ :=
  accepted_of_selected 13 419001 ⟨774586, by decide⟩ ⟨13, 2, 0, 774586, 419001, 1697, 16384⟩
    (by decide) selected_cut_30567

theorem selected_cut_30568 : selected 8 ⟨774615, by decide⟩
    (prefixPartial 13 419002) = some ⟨13, 2, 0, 774615, 419002, 961, 16384⟩ := by
  decide +kernel

theorem context_13_419002_774615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419002 ⟨774615, by decide⟩ :=
  accepted_of_selected 13 419002 ⟨774615, by decide⟩ ⟨13, 2, 0, 774615, 419002, 961, 16384⟩
    (by decide) selected_cut_30568

theorem selected_cut_30569 : selected 8 ⟨774640, by decide⟩
    (prefixPartial 13 419003) = some ⟨13, 2, 0, 774640, 419003, 861, 16384⟩ := by
  decide +kernel

theorem context_13_419003_774640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419003 ⟨774640, by decide⟩ :=
  accepted_of_selected 13 419003 ⟨774640, by decide⟩ ⟨13, 2, 0, 774640, 419003, 861, 16384⟩
    (by decide) selected_cut_30569

theorem unmarked_context_12_104750_774641 : frontier 9 ⟨774641, by decide⟩
    (prefixCache 12 104750) (prefixPartial 12 104750) = false := by
  decide +kernel

theorem node_context_12_104750_774641 : EJMOriginalGlobalDAGData.nodes 9 ⟨774641, by decide⟩ =
    .split (coordinate 12) (![⟨774542, by decide⟩,⟨774586, by decide⟩,⟨774615, by decide⟩,⟨774640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104750_774641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104750 ⟨774641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104750
    ⟨774641, by decide⟩ (by decide) (![⟨774542, by decide⟩,⟨774586, by decide⟩,⟨774615, by decide⟩,⟨774640, by decide⟩]) unmarked_context_12_104750_774641 node_context_12_104750_774641
  intro a
  fin_cases a
  · exact context_13_419000_774542
  · exact context_13_419001_774586
  · exact context_13_419002_774615
  · exact context_13_419003_774640

theorem selected_cut_30570 : selected 8 ⟨774659, by decide⟩
    (prefixPartial 13 419004) = some ⟨13, 2, 0, 774659, 419004, 757, 16384⟩ := by
  decide +kernel

theorem context_13_419004_774659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419004 ⟨774659, by decide⟩ :=
  accepted_of_selected 13 419004 ⟨774659, by decide⟩ ⟨13, 2, 0, 774659, 419004, 757, 16384⟩
    (by decide) selected_cut_30570

theorem selected_cut_30571 : selected 8 ⟨774693, by decide⟩
    (prefixPartial 13 419005) = some ⟨13, 2, 0, 774693, 419005, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_419005_774693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419005 ⟨774693, by decide⟩ :=
  accepted_of_selected 13 419005 ⟨774693, by decide⟩ ⟨13, 2, 0, 774693, 419005, 1797, 16384⟩
    (by decide) selected_cut_30571

theorem selected_cut_30572 : selected 8 ⟨774716, by decide⟩
    (prefixPartial 13 419006) = some ⟨13, 2, 0, 774716, 419006, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_419006_774716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419006 ⟨774716, by decide⟩ :=
  accepted_of_selected 13 419006 ⟨774716, by decide⟩ ⟨13, 2, 0, 774716, 419006, 1017, 16384⟩
    (by decide) selected_cut_30572

theorem selected_cut_30573 : selected 8 ⟨774728, by decide⟩
    (prefixPartial 13 419007) = some ⟨13, 2, 0, 774728, 419007, 825, 16384⟩ := by
  decide +kernel

theorem context_13_419007_774728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419007 ⟨774728, by decide⟩ :=
  accepted_of_selected 13 419007 ⟨774728, by decide⟩ ⟨13, 2, 0, 774728, 419007, 825, 16384⟩
    (by decide) selected_cut_30573

theorem unmarked_context_12_104751_774729 : frontier 9 ⟨774729, by decide⟩
    (prefixCache 12 104751) (prefixPartial 12 104751) = false := by
  decide +kernel

theorem node_context_12_104751_774729 : EJMOriginalGlobalDAGData.nodes 9 ⟨774729, by decide⟩ =
    .split (coordinate 12) (![⟨774659, by decide⟩,⟨774693, by decide⟩,⟨774716, by decide⟩,⟨774728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104751_774729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104751 ⟨774729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104751
    ⟨774729, by decide⟩ (by decide) (![⟨774659, by decide⟩,⟨774693, by decide⟩,⟨774716, by decide⟩,⟨774728, by decide⟩]) unmarked_context_12_104751_774729 node_context_12_104751_774729
  intro a
  fin_cases a
  · exact context_13_419004_774659
  · exact context_13_419005_774693
  · exact context_13_419006_774716
  · exact context_13_419007_774728

theorem unmarked_context_11_26187_774730 : frontier 10 ⟨774730, by decide⟩
    (prefixCache 11 26187) (prefixPartial 11 26187) = false := by
  decide +kernel

theorem node_context_11_26187_774730 : EJMOriginalGlobalDAGData.nodes 10 ⟨774730, by decide⟩ =
    .split (coordinate 11) (![⟨774425, by decide⟩,⟨774525, by decide⟩,⟨774641, by decide⟩,⟨774729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26187_774730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26187 ⟨774730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26187
    ⟨774730, by decide⟩ (by decide) (![⟨774425, by decide⟩,⟨774525, by decide⟩,⟨774641, by decide⟩,⟨774729, by decide⟩]) unmarked_context_11_26187_774730 node_context_11_26187_774730
  intro a
  fin_cases a
  · exact context_12_104748_774425
  · exact context_12_104749_774525
  · exact context_12_104750_774641
  · exact context_12_104751_774729

theorem unmarked_context_10_6546_774731 : frontier 11 ⟨774731, by decide⟩
    (prefixCache 10 6546) (prefixPartial 10 6546) = false := by
  decide +kernel

theorem node_context_10_6546_774731 : EJMOriginalGlobalDAGData.nodes 11 ⟨774731, by decide⟩ =
    .split (coordinate 10) (![⟨774089, by decide⟩,⟨774312, by decide⟩,⟨766338, by decide⟩,⟨774730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6546_774731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6546 ⟨774731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6546
    ⟨774731, by decide⟩ (by decide) (![⟨774089, by decide⟩,⟨774312, by decide⟩,⟨766338, by decide⟩,⟨774730, by decide⟩]) unmarked_context_10_6546_774731 node_context_10_6546_774731
  intro a
  fin_cases a
  · exact context_11_26184_774089
  · exact context_11_26185_774312
  · exact context_11_26186_766338
  · exact context_11_26187_774730

theorem selected_cut_30574 : selected 9 ⟨774846, by decide⟩
    (prefixPartial 12 104752) = some ⟨12, 2, 0, 774846, 104752, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_104752_774846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104752 ⟨774846, by decide⟩ :=
  accepted_of_selected 12 104752 ⟨774846, by decide⟩ ⟨12, 2, 0, 774846, 104752, 3625, 65536⟩
    (by decide) selected_cut_30574

theorem selected_cut_30575 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 104753) = some ⟨12, 1, 0, 772506, 104753, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104753_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104753 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 104753 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 104753, 1, 65536⟩
    (by decide) selected_cut_30575

theorem selected_cut_30576 : selected 9 ⟨774967, by decide⟩
    (prefixPartial 12 104754) = some ⟨12, 2, 0, 774967, 104754, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_104754_774967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104754 ⟨774967, by decide⟩ :=
  accepted_of_selected 12 104754 ⟨774967, by decide⟩ ⟨12, 2, 0, 774967, 104754, 3965, 65536⟩
    (by decide) selected_cut_30576

theorem selected_cut_30577 : selected 8 ⟨775002, by decide⟩
    (prefixPartial 13 419020) = some ⟨13, 2, 0, 775002, 419020, 841, 16384⟩ := by
  decide +kernel

theorem context_13_419020_775002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419020 ⟨775002, by decide⟩ :=
  accepted_of_selected 13 419020 ⟨775002, by decide⟩ ⟨13, 2, 0, 775002, 419020, 841, 16384⟩
    (by decide) selected_cut_30577

theorem selected_cut_30578 : selected 8 ⟨775056, by decide⟩
    (prefixPartial 13 419021) = some ⟨13, 2, 0, 775056, 419021, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_419021_775056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419021 ⟨775056, by decide⟩ :=
  accepted_of_selected 13 419021 ⟨775056, by decide⟩ ⟨13, 2, 0, 775056, 419021, 1781, 16384⟩
    (by decide) selected_cut_30578

theorem selected_cut_30579 : selected 8 ⟨775103, by decide⟩
    (prefixPartial 13 419022) = some ⟨13, 2, 0, 775103, 419022, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_419022_775103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419022 ⟨775103, by decide⟩ :=
  accepted_of_selected 13 419022 ⟨775103, by decide⟩ ⟨13, 2, 0, 775103, 419022, 1105, 16384⟩
    (by decide) selected_cut_30579

theorem selected_cut_30580 : selected 8 ⟨775119, by decide⟩
    (prefixPartial 13 419023) = some ⟨13, 2, 0, 775119, 419023, 697, 16384⟩ := by
  decide +kernel

theorem context_13_419023_775119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419023 ⟨775119, by decide⟩ :=
  accepted_of_selected 13 419023 ⟨775119, by decide⟩ ⟨13, 2, 0, 775119, 419023, 697, 16384⟩
    (by decide) selected_cut_30580

theorem unmarked_context_12_104755_775120 : frontier 9 ⟨775120, by decide⟩
    (prefixCache 12 104755) (prefixPartial 12 104755) = false := by
  decide +kernel

theorem node_context_12_104755_775120 : EJMOriginalGlobalDAGData.nodes 9 ⟨775120, by decide⟩ =
    .split (coordinate 12) (![⟨775002, by decide⟩,⟨775056, by decide⟩,⟨775103, by decide⟩,⟨775119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104755_775120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104755 ⟨775120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104755
    ⟨775120, by decide⟩ (by decide) (![⟨775002, by decide⟩,⟨775056, by decide⟩,⟨775103, by decide⟩,⟨775119, by decide⟩]) unmarked_context_12_104755_775120 node_context_12_104755_775120
  intro a
  fin_cases a
  · exact context_13_419020_775002
  · exact context_13_419021_775056
  · exact context_13_419022_775103
  · exact context_13_419023_775119

theorem unmarked_context_11_26188_775121 : frontier 10 ⟨775121, by decide⟩
    (prefixCache 11 26188) (prefixPartial 11 26188) = false := by
  decide +kernel

theorem node_context_11_26188_775121 : EJMOriginalGlobalDAGData.nodes 10 ⟨775121, by decide⟩ =
    .split (coordinate 11) (![⟨774846, by decide⟩,⟨772506, by decide⟩,⟨774967, by decide⟩,⟨775120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26188_775121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26188 ⟨775121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26188
    ⟨775121, by decide⟩ (by decide) (![⟨774846, by decide⟩,⟨772506, by decide⟩,⟨774967, by decide⟩,⟨775120, by decide⟩]) unmarked_context_11_26188_775121 node_context_11_26188_775121
  intro a
  fin_cases a
  · exact context_12_104752_774846
  · exact context_12_104753_772506
  · exact context_12_104754_774967
  · exact context_12_104755_775120

theorem selected_cut_30581 : selected 10 ⟨775270, by decide⟩
    (prefixPartial 11 26189) = some ⟨11, 2, 0, 775270, 26189, 2549, 262144⟩ := by
  decide +kernel

theorem context_11_26189_775270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26189 ⟨775270, by decide⟩ :=
  accepted_of_selected 11 26189 ⟨775270, by decide⟩ ⟨11, 2, 0, 775270, 26189, 2549, 262144⟩
    (by decide) selected_cut_30581

theorem selected_cut_30582 : selected 9 ⟨775379, by decide⟩
    (prefixPartial 12 104760) = some ⟨12, 2, 0, 775379, 104760, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_104760_775379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104760 ⟨775379, by decide⟩ :=
  accepted_of_selected 12 104760 ⟨775379, by decide⟩ ⟨12, 2, 0, 775379, 104760, 3361, 65536⟩
    (by decide) selected_cut_30582

theorem selected_cut_30583 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 104761) = some ⟨12, 1, 0, 772506, 104761, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104761_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104761 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 104761 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 104761, 1, 65536⟩
    (by decide) selected_cut_30583

theorem selected_cut_30584 : selected 9 ⟨775457, by decide⟩
    (prefixPartial 12 104762) = some ⟨12, 2, 0, 775457, 104762, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_104762_775457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104762 ⟨775457, by decide⟩ :=
  accepted_of_selected 12 104762 ⟨775457, by decide⟩ ⟨12, 2, 0, 775457, 104762, 3189, 65536⟩
    (by decide) selected_cut_30584

theorem selected_cut_30585 : selected 9 ⟨775570, by decide⟩
    (prefixPartial 12 104763) = some ⟨12, 2, 0, 775570, 104763, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_104763_775570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104763 ⟨775570, by decide⟩ :=
  accepted_of_selected 12 104763 ⟨775570, by decide⟩ ⟨12, 2, 0, 775570, 104763, 3557, 65536⟩
    (by decide) selected_cut_30585

theorem unmarked_context_11_26190_775571 : frontier 10 ⟨775571, by decide⟩
    (prefixCache 11 26190) (prefixPartial 11 26190) = false := by
  decide +kernel

theorem node_context_11_26190_775571 : EJMOriginalGlobalDAGData.nodes 10 ⟨775571, by decide⟩ =
    .split (coordinate 11) (![⟨775379, by decide⟩,⟨772506, by decide⟩,⟨775457, by decide⟩,⟨775570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26190_775571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26190 ⟨775571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26190
    ⟨775571, by decide⟩ (by decide) (![⟨775379, by decide⟩,⟨772506, by decide⟩,⟨775457, by decide⟩,⟨775570, by decide⟩]) unmarked_context_11_26190_775571 node_context_11_26190_775571
  intro a
  fin_cases a
  · exact context_12_104760_775379
  · exact context_12_104761_772506
  · exact context_12_104762_775457
  · exact context_12_104763_775570

theorem selected_cut_30586 : selected 9 ⟨775646, by decide⟩
    (prefixPartial 12 104764) = some ⟨12, 2, 0, 775646, 104764, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_104764_775646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104764 ⟨775646, by decide⟩ :=
  accepted_of_selected 12 104764 ⟨775646, by decide⟩ ⟨12, 2, 0, 775646, 104764, 2985, 65536⟩
    (by decide) selected_cut_30586

theorem selected_cut_30587 : selected 9 ⟨775723, by decide⟩
    (prefixPartial 12 104765) = some ⟨12, 2, 0, 775723, 104765, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_104765_775723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104765 ⟨775723, by decide⟩ :=
  accepted_of_selected 12 104765 ⟨775723, by decide⟩ ⟨12, 2, 0, 775723, 104765, 2105, 65536⟩
    (by decide) selected_cut_30587

theorem selected_cut_30588 : selected 9 ⟨775797, by decide⟩
    (prefixPartial 12 104766) = some ⟨12, 2, 0, 775797, 104766, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_104766_775797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104766 ⟨775797, by decide⟩ :=
  accepted_of_selected 12 104766 ⟨775797, by decide⟩ ⟨12, 2, 0, 775797, 104766, 2905, 65536⟩
    (by decide) selected_cut_30588

theorem selected_cut_30589 : selected 9 ⟨775884, by decide⟩
    (prefixPartial 12 104767) = some ⟨12, 2, 0, 775884, 104767, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_104767_775884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104767 ⟨775884, by decide⟩ :=
  accepted_of_selected 12 104767 ⟨775884, by decide⟩ ⟨12, 2, 0, 775884, 104767, 3033, 65536⟩
    (by decide) selected_cut_30589

theorem unmarked_context_11_26191_775885 : frontier 10 ⟨775885, by decide⟩
    (prefixCache 11 26191) (prefixPartial 11 26191) = false := by
  decide +kernel

theorem node_context_11_26191_775885 : EJMOriginalGlobalDAGData.nodes 10 ⟨775885, by decide⟩ =
    .split (coordinate 11) (![⟨775646, by decide⟩,⟨775723, by decide⟩,⟨775797, by decide⟩,⟨775884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26191_775885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26191 ⟨775885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26191
    ⟨775885, by decide⟩ (by decide) (![⟨775646, by decide⟩,⟨775723, by decide⟩,⟨775797, by decide⟩,⟨775884, by decide⟩]) unmarked_context_11_26191_775885 node_context_11_26191_775885
  intro a
  fin_cases a
  · exact context_12_104764_775646
  · exact context_12_104765_775723
  · exact context_12_104766_775797
  · exact context_12_104767_775884

theorem unmarked_context_10_6547_775886 : frontier 11 ⟨775886, by decide⟩
    (prefixCache 10 6547) (prefixPartial 10 6547) = false := by
  decide +kernel

theorem node_context_10_6547_775886 : EJMOriginalGlobalDAGData.nodes 11 ⟨775886, by decide⟩ =
    .split (coordinate 10) (![⟨775121, by decide⟩,⟨775270, by decide⟩,⟨775571, by decide⟩,⟨775885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6547_775886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6547 ⟨775886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6547
    ⟨775886, by decide⟩ (by decide) (![⟨775121, by decide⟩,⟨775270, by decide⟩,⟨775571, by decide⟩,⟨775885, by decide⟩]) unmarked_context_10_6547_775886 node_context_10_6547_775886
  intro a
  fin_cases a
  · exact context_11_26188_775121
  · exact context_11_26189_775270
  · exact context_11_26190_775571
  · exact context_11_26191_775885

theorem unmarked_context_9_1636_775887 : frontier 12 ⟨775887, by decide⟩
    (prefixCache 9 1636) (prefixPartial 9 1636) = false := by
  decide +kernel

theorem node_context_9_1636_775887 : EJMOriginalGlobalDAGData.nodes 12 ⟨775887, by decide⟩ =
    .split (coordinate 9) (![⟨771700, by decide⟩,⟨773781, by decide⟩,⟨774731, by decide⟩,⟨775886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1636_775887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1636 ⟨775887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1636
    ⟨775887, by decide⟩ (by decide) (![⟨771700, by decide⟩,⟨773781, by decide⟩,⟨774731, by decide⟩,⟨775886, by decide⟩]) unmarked_context_9_1636_775887 node_context_9_1636_775887
  intro a
  fin_cases a
  · exact context_10_6544_771700
  · exact context_10_6545_773781
  · exact context_10_6546_774731
  · exact context_10_6547_775886

theorem selected_cut_30590 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6548) = some ⟨10, 1, 0, 3442, 6548, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6548_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6548 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6548 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6548, 1, 1048576⟩
    (by decide) selected_cut_30590

theorem selected_cut_30591 : selected 9 ⟨775936, by decide⟩
    (prefixPartial 12 104784) = some ⟨12, 2, 0, 775936, 104784, 849, 65536⟩ := by
  decide +kernel

theorem context_12_104784_775936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104784 ⟨775936, by decide⟩ :=
  accepted_of_selected 12 104784 ⟨775936, by decide⟩ ⟨12, 2, 0, 775936, 104784, 849, 65536⟩
    (by decide) selected_cut_30591

theorem selected_cut_30592 : selected 9 ⟨775937, by decide⟩
    (prefixPartial 12 104785) = some ⟨12, 1, 0, 775937, 104785, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104785_775937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104785 ⟨775937, by decide⟩ :=
  accepted_of_selected 12 104785 ⟨775937, by decide⟩ ⟨12, 1, 0, 775937, 104785, 1, 65536⟩
    (by decide) selected_cut_30592

theorem selected_cut_30593 : selected 9 ⟨776045, by decide⟩
    (prefixPartial 12 104786) = some ⟨12, 2, 0, 776045, 104786, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_104786_776045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104786 ⟨776045, by decide⟩ :=
  accepted_of_selected 12 104786 ⟨776045, by decide⟩ ⟨12, 2, 0, 776045, 104786, 2161, 65536⟩
    (by decide) selected_cut_30593

theorem selected_cut_30594 : selected 9 ⟨776104, by decide⟩
    (prefixPartial 12 104787) = some ⟨12, 2, 0, 776104, 104787, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_104787_776104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104787 ⟨776104, by decide⟩ :=
  accepted_of_selected 12 104787 ⟨776104, by decide⟩ ⟨12, 2, 0, 776104, 104787, 2061, 65536⟩
    (by decide) selected_cut_30594

theorem unmarked_context_11_26196_776105 : frontier 10 ⟨776105, by decide⟩
    (prefixCache 11 26196) (prefixPartial 11 26196) = false := by
  decide +kernel

theorem node_context_11_26196_776105 : EJMOriginalGlobalDAGData.nodes 10 ⟨776105, by decide⟩ =
    .split (coordinate 11) (![⟨775936, by decide⟩,⟨775937, by decide⟩,⟨776045, by decide⟩,⟨776104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26196_776105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26196 ⟨776105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26196
    ⟨776105, by decide⟩ (by decide) (![⟨775936, by decide⟩,⟨775937, by decide⟩,⟨776045, by decide⟩,⟨776104, by decide⟩]) unmarked_context_11_26196_776105 node_context_11_26196_776105
  intro a
  fin_cases a
  · exact context_12_104784_775936
  · exact context_12_104785_775937
  · exact context_12_104786_776045
  · exact context_12_104787_776104

theorem selected_cut_30595 : selected 10 ⟨459416, by decide⟩
    (prefixPartial 11 26197) = some ⟨11, 1, 0, 459416, 26197, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26197_459416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26197 ⟨459416, by decide⟩ :=
  accepted_of_selected 11 26197 ⟨459416, by decide⟩ ⟨11, 1, 0, 459416, 26197, 1, 262144⟩
    (by decide) selected_cut_30595

theorem selected_cut_30596 : selected 10 ⟨776216, by decide⟩
    (prefixPartial 11 26198) = some ⟨11, 2, 0, 776216, 26198, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_26198_776216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26198 ⟨776216, by decide⟩ :=
  accepted_of_selected 11 26198 ⟨776216, by decide⟩ ⟨11, 2, 0, 776216, 26198, 3097, 262144⟩
    (by decide) selected_cut_30596

theorem selected_cut_30597 : selected 10 ⟨776256, by decide⟩
    (prefixPartial 11 26199) = some ⟨11, 2, 0, 776256, 26199, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_26199_776256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26199 ⟨776256, by decide⟩ :=
  accepted_of_selected 11 26199 ⟨776256, by decide⟩ ⟨11, 2, 0, 776256, 26199, 1101, 262144⟩
    (by decide) selected_cut_30597

theorem unmarked_context_10_6549_776257 : frontier 11 ⟨776257, by decide⟩
    (prefixCache 10 6549) (prefixPartial 10 6549) = false := by
  decide +kernel

theorem node_context_10_6549_776257 : EJMOriginalGlobalDAGData.nodes 11 ⟨776257, by decide⟩ =
    .split (coordinate 10) (![⟨776105, by decide⟩,⟨459416, by decide⟩,⟨776216, by decide⟩,⟨776256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6549_776257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6549 ⟨776257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6549
    ⟨776257, by decide⟩ (by decide) (![⟨776105, by decide⟩,⟨459416, by decide⟩,⟨776216, by decide⟩,⟨776256, by decide⟩]) unmarked_context_10_6549_776257 node_context_10_6549_776257
  intro a
  fin_cases a
  · exact context_11_26196_776105
  · exact context_11_26197_459416
  · exact context_11_26198_776216
  · exact context_11_26199_776256

theorem selected_cut_30598 : selected 10 ⟨776388, by decide⟩
    (prefixPartial 11 26200) = some ⟨11, 2, 0, 776388, 26200, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_26200_776388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26200 ⟨776388, by decide⟩ :=
  accepted_of_selected 11 26200 ⟨776388, by decide⟩ ⟨11, 2, 0, 776388, 26200, 2893, 262144⟩
    (by decide) selected_cut_30598

theorem selected_cut_30599 : selected 10 ⟨459416, by decide⟩
    (prefixPartial 11 26201) = some ⟨11, 1, 0, 459416, 26201, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26201_459416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26201 ⟨459416, by decide⟩ :=
  accepted_of_selected 11 26201 ⟨459416, by decide⟩ ⟨11, 1, 0, 459416, 26201, 1, 262144⟩
    (by decide) selected_cut_30599

theorem selected_cut_30600 : selected 10 ⟨776668, by decide⟩
    (prefixPartial 11 26202) = some ⟨11, 2, 0, 776668, 26202, 3745, 262144⟩ := by
  decide +kernel

theorem context_11_26202_776668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26202 ⟨776668, by decide⟩ :=
  accepted_of_selected 11 26202 ⟨776668, by decide⟩ ⟨11, 2, 0, 776668, 26202, 3745, 262144⟩
    (by decide) selected_cut_30600

theorem selected_cut_30601 : selected 10 ⟨776805, by decide⟩
    (prefixPartial 11 26203) = some ⟨11, 2, 0, 776805, 26203, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_26203_776805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26203 ⟨776805, by decide⟩ :=
  accepted_of_selected 11 26203 ⟨776805, by decide⟩ ⟨11, 2, 0, 776805, 26203, 3545, 262144⟩
    (by decide) selected_cut_30601

theorem unmarked_context_10_6550_776806 : frontier 11 ⟨776806, by decide⟩
    (prefixCache 10 6550) (prefixPartial 10 6550) = false := by
  decide +kernel

theorem node_context_10_6550_776806 : EJMOriginalGlobalDAGData.nodes 11 ⟨776806, by decide⟩ =
    .split (coordinate 10) (![⟨776388, by decide⟩,⟨459416, by decide⟩,⟨776668, by decide⟩,⟨776805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6550_776806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6550 ⟨776806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6550
    ⟨776806, by decide⟩ (by decide) (![⟨776388, by decide⟩,⟨459416, by decide⟩,⟨776668, by decide⟩,⟨776805, by decide⟩]) unmarked_context_10_6550_776806 node_context_10_6550_776806
  intro a
  fin_cases a
  · exact context_11_26200_776388
  · exact context_11_26201_459416
  · exact context_11_26202_776668
  · exact context_11_26203_776805

theorem selected_cut_30602 : selected 11 ⟨777004, by decide⟩
    (prefixPartial 10 6551) = some ⟨10, 2, 0, 777004, 6551, 3541, 1048576⟩ := by
  decide +kernel

theorem context_10_6551_777004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6551 ⟨777004, by decide⟩ :=
  accepted_of_selected 10 6551 ⟨777004, by decide⟩ ⟨10, 2, 0, 777004, 6551, 3541, 1048576⟩
    (by decide) selected_cut_30602

theorem unmarked_context_9_1637_777005 : frontier 12 ⟨777005, by decide⟩
    (prefixCache 9 1637) (prefixPartial 9 1637) = false := by
  decide +kernel

theorem node_context_9_1637_777005 : EJMOriginalGlobalDAGData.nodes 12 ⟨777005, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨776257, by decide⟩,⟨776806, by decide⟩,⟨777004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1637_777005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1637 ⟨777005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1637
    ⟨777005, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨776257, by decide⟩,⟨776806, by decide⟩,⟨777004, by decide⟩]) unmarked_context_9_1637_777005 node_context_9_1637_777005
  intro a
  fin_cases a
  · exact context_10_6548_3442
  · exact context_10_6549_776257
  · exact context_10_6550_776806
  · exact context_10_6551_777004

theorem selected_cut_30603 : selected 12 ⟨777082, by decide⟩
    (prefixPartial 9 1638) = some ⟨9, 2, 0, 777082, 1638, 629, 4194304⟩ := by
  decide +kernel

theorem context_9_1638_777082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1638 ⟨777082, by decide⟩ :=
  accepted_of_selected 9 1638 ⟨777082, by decide⟩ ⟨9, 2, 0, 777082, 1638, 629, 4194304⟩
    (by decide) selected_cut_30603

theorem selected_cut_30604 : selected 12 ⟨777084, by decide⟩
    (prefixPartial 9 1639) = some ⟨9, 2, 0, 777084, 1639, 41, 4194304⟩ := by
  decide +kernel

theorem context_9_1639_777084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1639 ⟨777084, by decide⟩ :=
  accepted_of_selected 9 1639 ⟨777084, by decide⟩ ⟨9, 2, 0, 777084, 1639, 41, 4194304⟩
    (by decide) selected_cut_30604

theorem unmarked_context_8_409_777085 : frontier 13 ⟨777085, by decide⟩
    (prefixCache 8 409) (prefixPartial 8 409) = false := by
  decide +kernel

theorem node_context_8_409_777085 : EJMOriginalGlobalDAGData.nodes 13 ⟨777085, by decide⟩ =
    .split (coordinate 8) (![⟨775887, by decide⟩,⟨777005, by decide⟩,⟨777082, by decide⟩,⟨777084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_409_777085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 409 ⟨777085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 409
    ⟨777085, by decide⟩ (by decide) (![⟨775887, by decide⟩,⟨777005, by decide⟩,⟨777082, by decide⟩,⟨777084, by decide⟩]) unmarked_context_8_409_777085 node_context_8_409_777085
  intro a
  fin_cases a
  · exact context_9_1636_775887
  · exact context_9_1637_777005
  · exact context_9_1638_777082
  · exact context_9_1639_777084

theorem selected_cut_30605 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26240) = some ⟨11, 1, 0, 434745, 26240, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26240_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26240 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26240 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26240, 1, 262144⟩
    (by decide) selected_cut_30605

theorem selected_cut_30606 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104964) = some ⟨12, 1, 0, 895, 104964, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104964_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104964 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104964 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104964, 1, 65536⟩
    (by decide) selected_cut_30606

theorem selected_cut_30607 : selected 8 ⟨777213, by decide⟩
    (prefixPartial 13 419860) = some ⟨13, 2, 0, 777213, 419860, 3473, 16384⟩ := by
  decide +kernel

theorem context_13_419860_777213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419860 ⟨777213, by decide⟩ :=
  accepted_of_selected 13 419860 ⟨777213, by decide⟩ ⟨13, 2, 0, 777213, 419860, 3473, 16384⟩
    (by decide) selected_cut_30607

theorem selected_cut_30608 : selected 8 ⟨777301, by decide⟩
    (prefixPartial 13 419861) = some ⟨13, 2, 0, 777301, 419861, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_419861_777301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419861 ⟨777301, by decide⟩ :=
  accepted_of_selected 13 419861 ⟨777301, by decide⟩ ⟨13, 2, 0, 777301, 419861, 1901, 16384⟩
    (by decide) selected_cut_30608

theorem selected_cut_30609 : selected 8 ⟨777329, by decide⟩
    (prefixPartial 13 419862) = some ⟨13, 2, 0, 777329, 419862, 469, 16384⟩ := by
  decide +kernel

theorem context_13_419862_777329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419862 ⟨777329, by decide⟩ :=
  accepted_of_selected 13 419862 ⟨777329, by decide⟩ ⟨13, 2, 0, 777329, 419862, 469, 16384⟩
    (by decide) selected_cut_30609

theorem selected_cut_30610 : selected 8 ⟨777342, by decide⟩
    (prefixPartial 13 419863) = some ⟨13, 2, 0, 777342, 419863, 145, 16384⟩ := by
  decide +kernel

theorem context_13_419863_777342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419863 ⟨777342, by decide⟩ :=
  accepted_of_selected 13 419863 ⟨777342, by decide⟩ ⟨13, 2, 0, 777342, 419863, 145, 16384⟩
    (by decide) selected_cut_30610

theorem unmarked_context_12_104965_777343 : frontier 9 ⟨777343, by decide⟩
    (prefixCache 12 104965) (prefixPartial 12 104965) = false := by
  decide +kernel

theorem node_context_12_104965_777343 : EJMOriginalGlobalDAGData.nodes 9 ⟨777343, by decide⟩ =
    .split (coordinate 12) (![⟨777213, by decide⟩,⟨777301, by decide⟩,⟨777329, by decide⟩,⟨777342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104965_777343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104965 ⟨777343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104965
    ⟨777343, by decide⟩ (by decide) (![⟨777213, by decide⟩,⟨777301, by decide⟩,⟨777329, by decide⟩,⟨777342, by decide⟩]) unmarked_context_12_104965_777343 node_context_12_104965_777343
  intro a
  fin_cases a
  · exact context_13_419860_777213
  · exact context_13_419861_777301
  · exact context_13_419862_777329
  · exact context_13_419863_777342

theorem selected_cut_30611 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 104966) = some ⟨12, 1, 0, 763842, 104966, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104966_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104966 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 104966 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 104966, 1, 65536⟩
    (by decide) selected_cut_30611

theorem selected_cut_30612 : selected 8 ⟨777445, by decide⟩
    (prefixPartial 13 419868) = some ⟨13, 2, 0, 777445, 419868, 3757, 16384⟩ := by
  decide +kernel

theorem context_13_419868_777445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419868 ⟨777445, by decide⟩ :=
  accepted_of_selected 13 419868 ⟨777445, by decide⟩ ⟨13, 2, 0, 777445, 419868, 3757, 16384⟩
    (by decide) selected_cut_30612

theorem selected_cut_30613 : selected 7 ⟨777476, by decide⟩
    (prefixPartial 14 1679476) = some ⟨14, 2, 0, 777476, 1679476, 1285, 4096⟩ := by
  decide +kernel

theorem context_14_1679476_777476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1679476 ⟨777476, by decide⟩ :=
  accepted_of_selected 14 1679476 ⟨777476, by decide⟩ ⟨14, 2, 0, 777476, 1679476, 1285, 4096⟩
    (by decide) selected_cut_30613

theorem selected_cut_30614 : selected 7 ⟨777507, by decide⟩
    (prefixPartial 14 1679477) = some ⟨14, 2, 0, 777507, 1679477, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_1679477_777507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1679477 ⟨777507, by decide⟩ :=
  accepted_of_selected 14 1679477 ⟨777507, by decide⟩ ⟨14, 2, 0, 777507, 1679477, 1101, 4096⟩
    (by decide) selected_cut_30614

theorem selected_cut_30615 : selected 7 ⟨777526, by decide⟩
    (prefixPartial 14 1679478) = some ⟨14, 2, 0, 777526, 1679478, 829, 4096⟩ := by
  decide +kernel

theorem context_14_1679478_777526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1679478 ⟨777526, by decide⟩ :=
  accepted_of_selected 14 1679478 ⟨777526, by decide⟩ ⟨14, 2, 0, 777526, 1679478, 829, 4096⟩
    (by decide) selected_cut_30615

theorem selected_cut_30616 : selected 7 ⟨777556, by decide⟩
    (prefixPartial 14 1679479) = some ⟨14, 2, 0, 777556, 1679479, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_1679479_777556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1679479 ⟨777556, by decide⟩ :=
  accepted_of_selected 14 1679479 ⟨777556, by decide⟩ ⟨14, 2, 0, 777556, 1679479, 1105, 4096⟩
    (by decide) selected_cut_30616

theorem unmarked_context_13_419869_777557 : frontier 8 ⟨777557, by decide⟩
    (prefixCache 13 419869) (prefixPartial 13 419869) = false := by
  decide +kernel

theorem node_context_13_419869_777557 : EJMOriginalGlobalDAGData.nodes 8 ⟨777557, by decide⟩ =
    .split (coordinate 13) (![⟨777476, by decide⟩,⟨777507, by decide⟩,⟨777526, by decide⟩,⟨777556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_419869_777557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419869 ⟨777557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 419869
    ⟨777557, by decide⟩ (by decide) (![⟨777476, by decide⟩,⟨777507, by decide⟩,⟨777526, by decide⟩,⟨777556, by decide⟩]) unmarked_context_13_419869_777557 node_context_13_419869_777557
  intro a
  fin_cases a
  · exact context_14_1679476_777476
  · exact context_14_1679477_777507
  · exact context_14_1679478_777526
  · exact context_14_1679479_777556

theorem selected_cut_30617 : selected 8 ⟨777620, by decide⟩
    (prefixPartial 13 419870) = some ⟨13, 2, 0, 777620, 419870, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_419870_777620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419870 ⟨777620, by decide⟩ :=
  accepted_of_selected 13 419870 ⟨777620, by decide⟩ ⟨13, 2, 0, 777620, 419870, 2029, 16384⟩
    (by decide) selected_cut_30617

theorem selected_cut_30618 : selected 8 ⟨777664, by decide⟩
    (prefixPartial 13 419871) = some ⟨13, 2, 0, 777664, 419871, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_419871_777664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419871 ⟨777664, by decide⟩ :=
  accepted_of_selected 13 419871 ⟨777664, by decide⟩ ⟨13, 2, 0, 777664, 419871, 1325, 16384⟩
    (by decide) selected_cut_30618

theorem unmarked_context_12_104967_777665 : frontier 9 ⟨777665, by decide⟩
    (prefixCache 12 104967) (prefixPartial 12 104967) = false := by
  decide +kernel

theorem node_context_12_104967_777665 : EJMOriginalGlobalDAGData.nodes 9 ⟨777665, by decide⟩ =
    .split (coordinate 12) (![⟨777445, by decide⟩,⟨777557, by decide⟩,⟨777620, by decide⟩,⟨777664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104967_777665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104967 ⟨777665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104967
    ⟨777665, by decide⟩ (by decide) (![⟨777445, by decide⟩,⟨777557, by decide⟩,⟨777620, by decide⟩,⟨777664, by decide⟩]) unmarked_context_12_104967_777665 node_context_12_104967_777665
  intro a
  fin_cases a
  · exact context_13_419868_777445
  · exact context_13_419869_777557
  · exact context_13_419870_777620
  · exact context_13_419871_777664

theorem unmarked_context_11_26241_777666 : frontier 10 ⟨777666, by decide⟩
    (prefixCache 11 26241) (prefixPartial 11 26241) = false := by
  decide +kernel

theorem node_context_11_26241_777666 : EJMOriginalGlobalDAGData.nodes 10 ⟨777666, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨777343, by decide⟩,⟨763842, by decide⟩,⟨777665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26241_777666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26241 ⟨777666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26241
    ⟨777666, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨777343, by decide⟩,⟨763842, by decide⟩,⟨777665, by decide⟩]) unmarked_context_11_26241_777666 node_context_11_26241_777666
  intro a
  fin_cases a
  · exact context_12_104964_895
  · exact context_12_104965_777343
  · exact context_12_104966_763842
  · exact context_12_104967_777665

theorem selected_cut_30619 : selected 10 ⟨764169, by decide⟩
    (prefixPartial 11 26242) = some ⟨11, 1, 0, 764169, 26242, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26242_764169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26242 ⟨764169, by decide⟩ :=
  accepted_of_selected 11 26242 ⟨764169, by decide⟩ ⟨11, 1, 0, 764169, 26242, 1, 262144⟩
    (by decide) selected_cut_30619

theorem selected_cut_30620 : selected 10 ⟨777809, by decide⟩
    (prefixPartial 11 26243) = some ⟨11, 2, 0, 777809, 26243, 3497, 262144⟩ := by
  decide +kernel

theorem context_11_26243_777809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26243 ⟨777809, by decide⟩ :=
  accepted_of_selected 11 26243 ⟨777809, by decide⟩ ⟨11, 2, 0, 777809, 26243, 3497, 262144⟩
    (by decide) selected_cut_30620

theorem unmarked_context_10_6560_777810 : frontier 11 ⟨777810, by decide⟩
    (prefixCache 10 6560) (prefixPartial 10 6560) = false := by
  decide +kernel

theorem node_context_10_6560_777810 : EJMOriginalGlobalDAGData.nodes 11 ⟨777810, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨777666, by decide⟩,⟨764169, by decide⟩,⟨777809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6560_777810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6560 ⟨777810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6560
    ⟨777810, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨777666, by decide⟩,⟨764169, by decide⟩,⟨777809, by decide⟩]) unmarked_context_10_6560_777810 node_context_10_6560_777810
  intro a
  fin_cases a
  · exact context_11_26240_434745
  · exact context_11_26241_777666
  · exact context_11_26242_764169
  · exact context_11_26243_777809

theorem selected_cut_30621 : selected 8 ⟨777850, by decide⟩
    (prefixPartial 13 419904) = some ⟨13, 2, 0, 777850, 419904, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_419904_777850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419904 ⟨777850, by decide⟩ :=
  accepted_of_selected 13 419904 ⟨777850, by decide⟩ ⟨13, 2, 0, 777850, 419904, 1981, 16384⟩
    (by decide) selected_cut_30621

theorem selected_cut_30622 : selected 8 ⟨777869, by decide⟩
    (prefixPartial 13 419905) = some ⟨13, 2, 0, 777869, 419905, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_419905_777869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419905 ⟨777869, by decide⟩ :=
  accepted_of_selected 13 419905 ⟨777869, by decide⟩ ⟨13, 2, 0, 777869, 419905, 1889, 16384⟩
    (by decide) selected_cut_30622

theorem selected_cut_30623 : selected 8 ⟨777888, by decide⟩
    (prefixPartial 13 419906) = some ⟨13, 2, 0, 777888, 419906, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_419906_777888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419906 ⟨777888, by decide⟩ :=
  accepted_of_selected 13 419906 ⟨777888, by decide⟩ ⟨13, 2, 0, 777888, 419906, 1133, 16384⟩
    (by decide) selected_cut_30623

theorem selected_cut_30624 : selected 8 ⟨777900, by decide⟩
    (prefixPartial 13 419907) = some ⟨13, 2, 0, 777900, 419907, 921, 16384⟩ := by
  decide +kernel

theorem context_13_419907_777900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419907 ⟨777900, by decide⟩ :=
  accepted_of_selected 13 419907 ⟨777900, by decide⟩ ⟨13, 2, 0, 777900, 419907, 921, 16384⟩
    (by decide) selected_cut_30624

theorem unmarked_context_12_104976_777901 : frontier 9 ⟨777901, by decide⟩
    (prefixCache 12 104976) (prefixPartial 12 104976) = false := by
  decide +kernel

theorem node_context_12_104976_777901 : EJMOriginalGlobalDAGData.nodes 9 ⟨777901, by decide⟩ =
    .split (coordinate 12) (![⟨777850, by decide⟩,⟨777869, by decide⟩,⟨777888, by decide⟩,⟨777900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104976_777901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104976 ⟨777901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104976
    ⟨777901, by decide⟩ (by decide) (![⟨777850, by decide⟩,⟨777869, by decide⟩,⟨777888, by decide⟩,⟨777900, by decide⟩]) unmarked_context_12_104976_777901 node_context_12_104976_777901
  intro a
  fin_cases a
  · exact context_13_419904_777850
  · exact context_13_419905_777869
  · exact context_13_419906_777888
  · exact context_13_419907_777900

theorem selected_cut_30625 : selected 8 ⟨777957, by decide⟩
    (prefixPartial 13 419908) = some ⟨13, 2, 0, 777957, 419908, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_419908_777957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419908 ⟨777957, by decide⟩ :=
  accepted_of_selected 13 419908 ⟨777957, by decide⟩ ⟨13, 2, 0, 777957, 419908, 2537, 16384⟩
    (by decide) selected_cut_30625

theorem selected_cut_30626 : selected 8 ⟨777996, by decide⟩
    (prefixPartial 13 419909) = some ⟨13, 2, 0, 777996, 419909, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_419909_777996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 419909 ⟨777996, by decide⟩ :=
  accepted_of_selected 13 419909 ⟨777996, by decide⟩ ⟨13, 2, 0, 777996, 419909, 2313, 16384⟩
    (by decide) selected_cut_30626

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
