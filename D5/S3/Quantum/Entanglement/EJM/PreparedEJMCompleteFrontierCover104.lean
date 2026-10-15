/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover103
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09987 : selected 8 ⟨274566, by decide⟩
    (prefixPartial 13 99387) = some ⟨13, 2, 0, 274566, 99387, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_99387_274566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99387 ⟨274566, by decide⟩ :=
  accepted_of_selected 13 99387 ⟨274566, by decide⟩ ⟨13, 2, 0, 274566, 99387, 1137, 16384⟩
    (by decide) selected_cut_09987

theorem unmarked_context_12_24846_274567 : frontier 9 ⟨274567, by decide⟩
    (prefixCache 12 24846) (prefixPartial 12 24846) = false := by
  decide +kernel

theorem node_context_12_24846_274567 : EJMOriginalGlobalDAGData.nodes 9 ⟨274567, by decide⟩ =
    .split (coordinate 12) (![⟨274484, by decide⟩,⟨274529, by decide⟩,⟨274555, by decide⟩,⟨274566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24846_274567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24846 ⟨274567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24846
    ⟨274567, by decide⟩ (by decide) (![⟨274484, by decide⟩,⟨274529, by decide⟩,⟨274555, by decide⟩,⟨274566, by decide⟩]) unmarked_context_12_24846_274567 node_context_12_24846_274567
  intro a
  fin_cases a
  · exact context_13_99384_274484
  · exact context_13_99385_274529
  · exact context_13_99386_274555
  · exact context_13_99387_274566

theorem selected_cut_09988 : selected 8 ⟨274602, by decide⟩
    (prefixPartial 13 99388) = some ⟨13, 2, 0, 274602, 99388, 3385, 16384⟩ := by
  decide +kernel

theorem context_13_99388_274602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99388 ⟨274602, by decide⟩ :=
  accepted_of_selected 13 99388 ⟨274602, by decide⟩ ⟨13, 2, 0, 274602, 99388, 3385, 16384⟩
    (by decide) selected_cut_09988

theorem selected_cut_09989 : selected 8 ⟨274641, by decide⟩
    (prefixPartial 13 99389) = some ⟨13, 2, 0, 274641, 99389, 3569, 16384⟩ := by
  decide +kernel

theorem context_13_99389_274641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99389 ⟨274641, by decide⟩ :=
  accepted_of_selected 13 99389 ⟨274641, by decide⟩ ⟨13, 2, 0, 274641, 99389, 3569, 16384⟩
    (by decide) selected_cut_09989

theorem selected_cut_09990 : selected 8 ⟨274667, by decide⟩
    (prefixPartial 13 99390) = some ⟨13, 2, 0, 274667, 99390, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_99390_274667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99390 ⟨274667, by decide⟩ :=
  accepted_of_selected 13 99390 ⟨274667, by decide⟩ ⟨13, 2, 0, 274667, 99390, 2385, 16384⟩
    (by decide) selected_cut_09990

theorem selected_cut_09991 : selected 8 ⟨274674, by decide⟩
    (prefixPartial 13 99391) = some ⟨13, 2, 0, 274674, 99391, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_99391_274674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99391 ⟨274674, by decide⟩ :=
  accepted_of_selected 13 99391 ⟨274674, by decide⟩ ⟨13, 2, 0, 274674, 99391, 1245, 16384⟩
    (by decide) selected_cut_09991

theorem unmarked_context_12_24847_274675 : frontier 9 ⟨274675, by decide⟩
    (prefixCache 12 24847) (prefixPartial 12 24847) = false := by
  decide +kernel

theorem node_context_12_24847_274675 : EJMOriginalGlobalDAGData.nodes 9 ⟨274675, by decide⟩ =
    .split (coordinate 12) (![⟨274602, by decide⟩,⟨274641, by decide⟩,⟨274667, by decide⟩,⟨274674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24847_274675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24847 ⟨274675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24847
    ⟨274675, by decide⟩ (by decide) (![⟨274602, by decide⟩,⟨274641, by decide⟩,⟨274667, by decide⟩,⟨274674, by decide⟩]) unmarked_context_12_24847_274675 node_context_12_24847_274675
  intro a
  fin_cases a
  · exact context_13_99388_274602
  · exact context_13_99389_274641
  · exact context_13_99390_274667
  · exact context_13_99391_274674

theorem unmarked_context_11_6211_274676 : frontier 10 ⟨274676, by decide⟩
    (prefixCache 11 6211) (prefixPartial 11 6211) = false := by
  decide +kernel

theorem node_context_11_6211_274676 : EJMOriginalGlobalDAGData.nodes 10 ⟨274676, by decide⟩ =
    .split (coordinate 11) (![⟨274323, by decide⟩,⟨274443, by decide⟩,⟨274567, by decide⟩,⟨274675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6211_274676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6211 ⟨274676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6211
    ⟨274676, by decide⟩ (by decide) (![⟨274323, by decide⟩,⟨274443, by decide⟩,⟨274567, by decide⟩,⟨274675, by decide⟩]) unmarked_context_11_6211_274676 node_context_11_6211_274676
  intro a
  fin_cases a
  · exact context_12_24844_274323
  · exact context_12_24845_274443
  · exact context_12_24846_274567
  · exact context_12_24847_274675

theorem unmarked_context_10_1552_274677 : frontier 11 ⟨274677, by decide⟩
    (prefixCache 10 1552) (prefixPartial 10 1552) = false := by
  decide +kernel

theorem node_context_10_1552_274677 : EJMOriginalGlobalDAGData.nodes 11 ⟨274677, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨273677, by decide⟩,⟨274202, by decide⟩,⟨274676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1552_274677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1552 ⟨274677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1552
    ⟨274677, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨273677, by decide⟩,⟨274202, by decide⟩,⟨274676, by decide⟩]) unmarked_context_10_1552_274677 node_context_10_1552_274677
  intro a
  fin_cases a
  · exact context_11_6208_167448
  · exact context_11_6209_273677
  · exact context_11_6210_274202
  · exact context_11_6211_274676

theorem selected_cut_09992 : selected 8 ⟨274703, by decide⟩
    (prefixPartial 13 99392) = some ⟨13, 2, 0, 274703, 99392, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_99392_274703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99392 ⟨274703, by decide⟩ :=
  accepted_of_selected 13 99392 ⟨274703, by decide⟩ ⟨13, 2, 0, 274703, 99392, 1225, 16384⟩
    (by decide) selected_cut_09992

theorem selected_cut_09993 : selected 8 ⟨274725, by decide⟩
    (prefixPartial 13 99393) = some ⟨13, 2, 0, 274725, 99393, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_99393_274725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99393 ⟨274725, by decide⟩ :=
  accepted_of_selected 13 99393 ⟨274725, by decide⟩ ⟨13, 2, 0, 274725, 99393, 1493, 16384⟩
    (by decide) selected_cut_09993

theorem selected_cut_09994 : selected 8 ⟨274739, by decide⟩
    (prefixPartial 13 99394) = some ⟨13, 2, 0, 274739, 99394, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_99394_274739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99394 ⟨274739, by decide⟩ :=
  accepted_of_selected 13 99394 ⟨274739, by decide⟩ ⟨13, 2, 0, 274739, 99394, 1001, 16384⟩
    (by decide) selected_cut_09994

theorem selected_cut_09995 : selected 8 ⟨274744, by decide⟩
    (prefixPartial 13 99395) = some ⟨13, 2, 0, 274744, 99395, 617, 16384⟩ := by
  decide +kernel

theorem context_13_99395_274744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99395 ⟨274744, by decide⟩ :=
  accepted_of_selected 13 99395 ⟨274744, by decide⟩ ⟨13, 2, 0, 274744, 99395, 617, 16384⟩
    (by decide) selected_cut_09995

theorem unmarked_context_12_24848_274745 : frontier 9 ⟨274745, by decide⟩
    (prefixCache 12 24848) (prefixPartial 12 24848) = false := by
  decide +kernel

theorem node_context_12_24848_274745 : EJMOriginalGlobalDAGData.nodes 9 ⟨274745, by decide⟩ =
    .split (coordinate 12) (![⟨274703, by decide⟩,⟨274725, by decide⟩,⟨274739, by decide⟩,⟨274744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24848_274745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24848 ⟨274745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24848
    ⟨274745, by decide⟩ (by decide) (![⟨274703, by decide⟩,⟨274725, by decide⟩,⟨274739, by decide⟩,⟨274744, by decide⟩]) unmarked_context_12_24848_274745 node_context_12_24848_274745
  intro a
  fin_cases a
  · exact context_13_99392_274703
  · exact context_13_99393_274725
  · exact context_13_99394_274739
  · exact context_13_99395_274744

theorem selected_cut_09996 : selected 8 ⟨274762, by decide⟩
    (prefixPartial 13 99396) = some ⟨13, 2, 0, 274762, 99396, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_99396_274762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99396 ⟨274762, by decide⟩ :=
  accepted_of_selected 13 99396 ⟨274762, by decide⟩ ⟨13, 2, 0, 274762, 99396, 1133, 16384⟩
    (by decide) selected_cut_09996

theorem selected_cut_09997 : selected 8 ⟨274786, by decide⟩
    (prefixPartial 13 99397) = some ⟨13, 2, 0, 274786, 99397, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_99397_274786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99397 ⟨274786, by decide⟩ :=
  accepted_of_selected 13 99397 ⟨274786, by decide⟩ ⟨13, 2, 0, 274786, 99397, 1413, 16384⟩
    (by decide) selected_cut_09997

theorem selected_cut_09998 : selected 8 ⟨274803, by decide⟩
    (prefixPartial 13 99398) = some ⟨13, 2, 0, 274803, 99398, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_99398_274803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99398 ⟨274803, by decide⟩ :=
  accepted_of_selected 13 99398 ⟨274803, by decide⟩ ⟨13, 2, 0, 274803, 99398, 1245, 16384⟩
    (by decide) selected_cut_09998

theorem selected_cut_09999 : selected 8 ⟨274812, by decide⟩
    (prefixPartial 13 99399) = some ⟨13, 2, 0, 274812, 99399, 673, 16384⟩ := by
  decide +kernel

theorem context_13_99399_274812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99399 ⟨274812, by decide⟩ :=
  accepted_of_selected 13 99399 ⟨274812, by decide⟩ ⟨13, 2, 0, 274812, 99399, 673, 16384⟩
    (by decide) selected_cut_09999

theorem unmarked_context_12_24849_274813 : frontier 9 ⟨274813, by decide⟩
    (prefixCache 12 24849) (prefixPartial 12 24849) = false := by
  decide +kernel

theorem node_context_12_24849_274813 : EJMOriginalGlobalDAGData.nodes 9 ⟨274813, by decide⟩ =
    .split (coordinate 12) (![⟨274762, by decide⟩,⟨274786, by decide⟩,⟨274803, by decide⟩,⟨274812, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24849_274813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24849 ⟨274813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24849
    ⟨274813, by decide⟩ (by decide) (![⟨274762, by decide⟩,⟨274786, by decide⟩,⟨274803, by decide⟩,⟨274812, by decide⟩]) unmarked_context_12_24849_274813 node_context_12_24849_274813
  intro a
  fin_cases a
  · exact context_13_99396_274762
  · exact context_13_99397_274786
  · exact context_13_99398_274803
  · exact context_13_99399_274812

theorem selected_cut_10000 : selected 8 ⟨274829, by decide⟩
    (prefixPartial 13 99400) = some ⟨13, 2, 0, 274829, 99400, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_99400_274829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99400 ⟨274829, by decide⟩ :=
  accepted_of_selected 13 99400 ⟨274829, by decide⟩ ⟨13, 2, 0, 274829, 99400, 1389, 16384⟩
    (by decide) selected_cut_10000

theorem selected_cut_10001 : selected 8 ⟨274850, by decide⟩
    (prefixPartial 13 99401) = some ⟨13, 2, 0, 274850, 99401, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_99401_274850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99401 ⟨274850, by decide⟩ :=
  accepted_of_selected 13 99401 ⟨274850, by decide⟩ ⟨13, 2, 0, 274850, 99401, 1721, 16384⟩
    (by decide) selected_cut_10001

theorem selected_cut_10002 : selected 8 ⟨274867, by decide⟩
    (prefixPartial 13 99402) = some ⟨13, 2, 0, 274867, 99402, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_99402_274867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99402 ⟨274867, by decide⟩ :=
  accepted_of_selected 13 99402 ⟨274867, by decide⟩ ⟨13, 2, 0, 274867, 99402, 1229, 16384⟩
    (by decide) selected_cut_10002

theorem selected_cut_10003 : selected 8 ⟨274874, by decide⟩
    (prefixPartial 13 99403) = some ⟨13, 2, 0, 274874, 99403, 741, 16384⟩ := by
  decide +kernel

theorem context_13_99403_274874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99403 ⟨274874, by decide⟩ :=
  accepted_of_selected 13 99403 ⟨274874, by decide⟩ ⟨13, 2, 0, 274874, 99403, 741, 16384⟩
    (by decide) selected_cut_10003

theorem unmarked_context_12_24850_274875 : frontier 9 ⟨274875, by decide⟩
    (prefixCache 12 24850) (prefixPartial 12 24850) = false := by
  decide +kernel

theorem node_context_12_24850_274875 : EJMOriginalGlobalDAGData.nodes 9 ⟨274875, by decide⟩ =
    .split (coordinate 12) (![⟨274829, by decide⟩,⟨274850, by decide⟩,⟨274867, by decide⟩,⟨274874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24850_274875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24850 ⟨274875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24850
    ⟨274875, by decide⟩ (by decide) (![⟨274829, by decide⟩,⟨274850, by decide⟩,⟨274867, by decide⟩,⟨274874, by decide⟩]) unmarked_context_12_24850_274875 node_context_12_24850_274875
  intro a
  fin_cases a
  · exact context_13_99400_274829
  · exact context_13_99401_274850
  · exact context_13_99402_274867
  · exact context_13_99403_274874

theorem selected_cut_10004 : selected 8 ⟨274899, by decide⟩
    (prefixPartial 13 99404) = some ⟨13, 2, 0, 274899, 99404, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_99404_274899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99404 ⟨274899, by decide⟩ :=
  accepted_of_selected 13 99404 ⟨274899, by decide⟩ ⟨13, 2, 0, 274899, 99404, 1621, 16384⟩
    (by decide) selected_cut_10004

theorem selected_cut_10005 : selected 8 ⟨274920, by decide⟩
    (prefixPartial 13 99405) = some ⟨13, 2, 0, 274920, 99405, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_99405_274920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99405 ⟨274920, by decide⟩ :=
  accepted_of_selected 13 99405 ⟨274920, by decide⟩ ⟨13, 2, 0, 274920, 99405, 1921, 16384⟩
    (by decide) selected_cut_10005

theorem selected_cut_10006 : selected 8 ⟨274938, by decide⟩
    (prefixPartial 13 99406) = some ⟨13, 2, 0, 274938, 99406, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_99406_274938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99406 ⟨274938, by decide⟩ :=
  accepted_of_selected 13 99406 ⟨274938, by decide⟩ ⟨13, 2, 0, 274938, 99406, 1417, 16384⟩
    (by decide) selected_cut_10006

theorem selected_cut_10007 : selected 8 ⟨274945, by decide⟩
    (prefixPartial 13 99407) = some ⟨13, 2, 0, 274945, 99407, 693, 16384⟩ := by
  decide +kernel

theorem context_13_99407_274945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99407 ⟨274945, by decide⟩ :=
  accepted_of_selected 13 99407 ⟨274945, by decide⟩ ⟨13, 2, 0, 274945, 99407, 693, 16384⟩
    (by decide) selected_cut_10007

theorem unmarked_context_12_24851_274946 : frontier 9 ⟨274946, by decide⟩
    (prefixCache 12 24851) (prefixPartial 12 24851) = false := by
  decide +kernel

theorem node_context_12_24851_274946 : EJMOriginalGlobalDAGData.nodes 9 ⟨274946, by decide⟩ =
    .split (coordinate 12) (![⟨274899, by decide⟩,⟨274920, by decide⟩,⟨274938, by decide⟩,⟨274945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24851_274946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24851 ⟨274946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24851
    ⟨274946, by decide⟩ (by decide) (![⟨274899, by decide⟩,⟨274920, by decide⟩,⟨274938, by decide⟩,⟨274945, by decide⟩]) unmarked_context_12_24851_274946 node_context_12_24851_274946
  intro a
  fin_cases a
  · exact context_13_99404_274899
  · exact context_13_99405_274920
  · exact context_13_99406_274938
  · exact context_13_99407_274945

theorem unmarked_context_11_6212_274947 : frontier 10 ⟨274947, by decide⟩
    (prefixCache 11 6212) (prefixPartial 11 6212) = false := by
  decide +kernel

theorem node_context_11_6212_274947 : EJMOriginalGlobalDAGData.nodes 10 ⟨274947, by decide⟩ =
    .split (coordinate 11) (![⟨274745, by decide⟩,⟨274813, by decide⟩,⟨274875, by decide⟩,⟨274946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6212_274947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6212 ⟨274947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6212
    ⟨274947, by decide⟩ (by decide) (![⟨274745, by decide⟩,⟨274813, by decide⟩,⟨274875, by decide⟩,⟨274946, by decide⟩]) unmarked_context_11_6212_274947 node_context_11_6212_274947
  intro a
  fin_cases a
  · exact context_12_24848_274745
  · exact context_12_24849_274813
  · exact context_12_24850_274875
  · exact context_12_24851_274946

theorem selected_cut_10008 : selected 8 ⟨274965, by decide⟩
    (prefixPartial 13 99408) = some ⟨13, 2, 0, 274965, 99408, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_99408_274965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99408 ⟨274965, by decide⟩ :=
  accepted_of_selected 13 99408 ⟨274965, by decide⟩ ⟨13, 2, 0, 274965, 99408, 1213, 16384⟩
    (by decide) selected_cut_10008

theorem selected_cut_10009 : selected 8 ⟨274989, by decide⟩
    (prefixPartial 13 99409) = some ⟨13, 2, 0, 274989, 99409, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_99409_274989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99409 ⟨274989, by decide⟩ :=
  accepted_of_selected 13 99409 ⟨274989, by decide⟩ ⟨13, 2, 0, 274989, 99409, 1573, 16384⟩
    (by decide) selected_cut_10009

theorem selected_cut_10010 : selected 8 ⟨275004, by decide⟩
    (prefixPartial 13 99410) = some ⟨13, 2, 0, 275004, 99410, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_99410_275004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99410 ⟨275004, by decide⟩ :=
  accepted_of_selected 13 99410 ⟨275004, by decide⟩ ⟨13, 2, 0, 275004, 99410, 1141, 16384⟩
    (by decide) selected_cut_10010

theorem selected_cut_10011 : selected 8 ⟨275011, by decide⟩
    (prefixPartial 13 99411) = some ⟨13, 2, 0, 275011, 99411, 697, 16384⟩ := by
  decide +kernel

theorem context_13_99411_275011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99411 ⟨275011, by decide⟩ :=
  accepted_of_selected 13 99411 ⟨275011, by decide⟩ ⟨13, 2, 0, 275011, 99411, 697, 16384⟩
    (by decide) selected_cut_10011

theorem unmarked_context_12_24852_275012 : frontier 9 ⟨275012, by decide⟩
    (prefixCache 12 24852) (prefixPartial 12 24852) = false := by
  decide +kernel

theorem node_context_12_24852_275012 : EJMOriginalGlobalDAGData.nodes 9 ⟨275012, by decide⟩ =
    .split (coordinate 12) (![⟨274965, by decide⟩,⟨274989, by decide⟩,⟨275004, by decide⟩,⟨275011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24852_275012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24852 ⟨275012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24852
    ⟨275012, by decide⟩ (by decide) (![⟨274965, by decide⟩,⟨274989, by decide⟩,⟨275004, by decide⟩,⟨275011, by decide⟩]) unmarked_context_12_24852_275012 node_context_12_24852_275012
  intro a
  fin_cases a
  · exact context_13_99408_274965
  · exact context_13_99409_274989
  · exact context_13_99410_275004
  · exact context_13_99411_275011

theorem selected_cut_10012 : selected 9 ⟨275013, by decide⟩
    (prefixPartial 12 24853) = some ⟨12, 1, 0, 275013, 24853, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24853_275013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24853 ⟨275013, by decide⟩ :=
  accepted_of_selected 12 24853 ⟨275013, by decide⟩ ⟨12, 1, 0, 275013, 24853, 1, 65536⟩
    (by decide) selected_cut_10012

theorem selected_cut_10013 : selected 8 ⟨275033, by decide⟩
    (prefixPartial 13 99416) = some ⟨13, 2, 0, 275033, 99416, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_99416_275033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99416 ⟨275033, by decide⟩ :=
  accepted_of_selected 13 99416 ⟨275033, by decide⟩ ⟨13, 2, 0, 275033, 99416, 1445, 16384⟩
    (by decide) selected_cut_10013

theorem selected_cut_10014 : selected 8 ⟨275057, by decide⟩
    (prefixPartial 13 99417) = some ⟨13, 2, 0, 275057, 99417, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_99417_275057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99417 ⟨275057, by decide⟩ :=
  accepted_of_selected 13 99417 ⟨275057, by decide⟩ ⟨13, 2, 0, 275057, 99417, 1889, 16384⟩
    (by decide) selected_cut_10014

theorem selected_cut_10015 : selected 8 ⟨275075, by decide⟩
    (prefixPartial 13 99418) = some ⟨13, 2, 0, 275075, 99418, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_99418_275075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99418 ⟨275075, by decide⟩ :=
  accepted_of_selected 13 99418 ⟨275075, by decide⟩ ⟨13, 2, 0, 275075, 99418, 1305, 16384⟩
    (by decide) selected_cut_10015

theorem selected_cut_10016 : selected 8 ⟨275087, by decide⟩
    (prefixPartial 13 99419) = some ⟨13, 2, 0, 275087, 99419, 825, 16384⟩ := by
  decide +kernel

theorem context_13_99419_275087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99419 ⟨275087, by decide⟩ :=
  accepted_of_selected 13 99419 ⟨275087, by decide⟩ ⟨13, 2, 0, 275087, 99419, 825, 16384⟩
    (by decide) selected_cut_10016

theorem unmarked_context_12_24854_275088 : frontier 9 ⟨275088, by decide⟩
    (prefixCache 12 24854) (prefixPartial 12 24854) = false := by
  decide +kernel

theorem node_context_12_24854_275088 : EJMOriginalGlobalDAGData.nodes 9 ⟨275088, by decide⟩ =
    .split (coordinate 12) (![⟨275033, by decide⟩,⟨275057, by decide⟩,⟨275075, by decide⟩,⟨275087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24854_275088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24854 ⟨275088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24854
    ⟨275088, by decide⟩ (by decide) (![⟨275033, by decide⟩,⟨275057, by decide⟩,⟨275075, by decide⟩,⟨275087, by decide⟩]) unmarked_context_12_24854_275088 node_context_12_24854_275088
  intro a
  fin_cases a
  · exact context_13_99416_275033
  · exact context_13_99417_275057
  · exact context_13_99418_275075
  · exact context_13_99419_275087

theorem selected_cut_10017 : selected 8 ⟨275111, by decide⟩
    (prefixPartial 13 99420) = some ⟨13, 2, 0, 275111, 99420, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_99420_275111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99420 ⟨275111, by decide⟩ :=
  accepted_of_selected 13 99420 ⟨275111, by decide⟩ ⟨13, 2, 0, 275111, 99420, 1633, 16384⟩
    (by decide) selected_cut_10017

theorem selected_cut_10018 : selected 8 ⟨275137, by decide⟩
    (prefixPartial 13 99421) = some ⟨13, 2, 0, 275137, 99421, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_99421_275137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99421 ⟨275137, by decide⟩ :=
  accepted_of_selected 13 99421 ⟨275137, by decide⟩ ⟨13, 2, 0, 275137, 99421, 2061, 16384⟩
    (by decide) selected_cut_10018

theorem selected_cut_10019 : selected 8 ⟨275152, by decide⟩
    (prefixPartial 13 99422) = some ⟨13, 2, 0, 275152, 99422, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_99422_275152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99422 ⟨275152, by decide⟩ :=
  accepted_of_selected 13 99422 ⟨275152, by decide⟩ ⟨13, 2, 0, 275152, 99422, 1517, 16384⟩
    (by decide) selected_cut_10019

theorem selected_cut_10020 : selected 8 ⟨275159, by decide⟩
    (prefixPartial 13 99423) = some ⟨13, 2, 0, 275159, 99423, 789, 16384⟩ := by
  decide +kernel

theorem context_13_99423_275159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99423 ⟨275159, by decide⟩ :=
  accepted_of_selected 13 99423 ⟨275159, by decide⟩ ⟨13, 2, 0, 275159, 99423, 789, 16384⟩
    (by decide) selected_cut_10020

theorem unmarked_context_12_24855_275160 : frontier 9 ⟨275160, by decide⟩
    (prefixCache 12 24855) (prefixPartial 12 24855) = false := by
  decide +kernel

theorem node_context_12_24855_275160 : EJMOriginalGlobalDAGData.nodes 9 ⟨275160, by decide⟩ =
    .split (coordinate 12) (![⟨275111, by decide⟩,⟨275137, by decide⟩,⟨275152, by decide⟩,⟨275159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24855_275160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24855 ⟨275160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24855
    ⟨275160, by decide⟩ (by decide) (![⟨275111, by decide⟩,⟨275137, by decide⟩,⟨275152, by decide⟩,⟨275159, by decide⟩]) unmarked_context_12_24855_275160 node_context_12_24855_275160
  intro a
  fin_cases a
  · exact context_13_99420_275111
  · exact context_13_99421_275137
  · exact context_13_99422_275152
  · exact context_13_99423_275159

theorem unmarked_context_11_6213_275161 : frontier 10 ⟨275161, by decide⟩
    (prefixCache 11 6213) (prefixPartial 11 6213) = false := by
  decide +kernel

theorem node_context_11_6213_275161 : EJMOriginalGlobalDAGData.nodes 10 ⟨275161, by decide⟩ =
    .split (coordinate 11) (![⟨275012, by decide⟩,⟨275013, by decide⟩,⟨275088, by decide⟩,⟨275160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6213_275161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6213 ⟨275161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6213
    ⟨275161, by decide⟩ (by decide) (![⟨275012, by decide⟩,⟨275013, by decide⟩,⟨275088, by decide⟩,⟨275160, by decide⟩]) unmarked_context_11_6213_275161 node_context_11_6213_275161
  intro a
  fin_cases a
  · exact context_12_24852_275012
  · exact context_12_24853_275013
  · exact context_12_24854_275088
  · exact context_12_24855_275160

theorem selected_cut_10021 : selected 8 ⟨275184, by decide⟩
    (prefixPartial 13 99424) = some ⟨13, 2, 0, 275184, 99424, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_99424_275184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99424 ⟨275184, by decide⟩ :=
  accepted_of_selected 13 99424 ⟨275184, by decide⟩ ⟨13, 2, 0, 275184, 99424, 1481, 16384⟩
    (by decide) selected_cut_10021

theorem selected_cut_10022 : selected 8 ⟨275209, by decide⟩
    (prefixPartial 13 99425) = some ⟨13, 2, 0, 275209, 99425, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_99425_275209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99425 ⟨275209, by decide⟩ :=
  accepted_of_selected 13 99425 ⟨275209, by decide⟩ ⟨13, 2, 0, 275209, 99425, 1805, 16384⟩
    (by decide) selected_cut_10022

theorem selected_cut_10023 : selected 8 ⟨275228, by decide⟩
    (prefixPartial 13 99426) = some ⟨13, 2, 0, 275228, 99426, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_99426_275228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99426 ⟨275228, by decide⟩ :=
  accepted_of_selected 13 99426 ⟨275228, by decide⟩ ⟨13, 2, 0, 275228, 99426, 1421, 16384⟩
    (by decide) selected_cut_10023

theorem selected_cut_10024 : selected 8 ⟨275235, by decide⟩
    (prefixPartial 13 99427) = some ⟨13, 2, 0, 275235, 99427, 713, 16384⟩ := by
  decide +kernel

theorem context_13_99427_275235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99427 ⟨275235, by decide⟩ :=
  accepted_of_selected 13 99427 ⟨275235, by decide⟩ ⟨13, 2, 0, 275235, 99427, 713, 16384⟩
    (by decide) selected_cut_10024

theorem unmarked_context_12_24856_275236 : frontier 9 ⟨275236, by decide⟩
    (prefixCache 12 24856) (prefixPartial 12 24856) = false := by
  decide +kernel

theorem node_context_12_24856_275236 : EJMOriginalGlobalDAGData.nodes 9 ⟨275236, by decide⟩ =
    .split (coordinate 12) (![⟨275184, by decide⟩,⟨275209, by decide⟩,⟨275228, by decide⟩,⟨275235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24856_275236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24856 ⟨275236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24856
    ⟨275236, by decide⟩ (by decide) (![⟨275184, by decide⟩,⟨275209, by decide⟩,⟨275228, by decide⟩,⟨275235, by decide⟩]) unmarked_context_12_24856_275236 node_context_12_24856_275236
  intro a
  fin_cases a
  · exact context_13_99424_275184
  · exact context_13_99425_275209
  · exact context_13_99426_275228
  · exact context_13_99427_275235

theorem selected_cut_10025 : selected 8 ⟨275255, by decide⟩
    (prefixPartial 13 99428) = some ⟨13, 2, 0, 275255, 99428, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_99428_275255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99428 ⟨275255, by decide⟩ :=
  accepted_of_selected 13 99428 ⟨275255, by decide⟩ ⟨13, 2, 0, 275255, 99428, 1353, 16384⟩
    (by decide) selected_cut_10025

theorem selected_cut_10026 : selected 8 ⟨275276, by decide⟩
    (prefixPartial 13 99429) = some ⟨13, 2, 0, 275276, 99429, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_99429_275276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99429 ⟨275276, by decide⟩ :=
  accepted_of_selected 13 99429 ⟨275276, by decide⟩ ⟨13, 2, 0, 275276, 99429, 1537, 16384⟩
    (by decide) selected_cut_10026

theorem selected_cut_10027 : selected 8 ⟨275293, by decide⟩
    (prefixPartial 13 99430) = some ⟨13, 2, 0, 275293, 99430, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_99430_275293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99430 ⟨275293, by decide⟩ :=
  accepted_of_selected 13 99430 ⟨275293, by decide⟩ ⟨13, 2, 0, 275293, 99430, 1413, 16384⟩
    (by decide) selected_cut_10027

theorem selected_cut_10028 : selected 8 ⟨275301, by decide⟩
    (prefixPartial 13 99431) = some ⟨13, 2, 0, 275301, 99431, 785, 16384⟩ := by
  decide +kernel

theorem context_13_99431_275301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99431 ⟨275301, by decide⟩ :=
  accepted_of_selected 13 99431 ⟨275301, by decide⟩ ⟨13, 2, 0, 275301, 99431, 785, 16384⟩
    (by decide) selected_cut_10028

theorem unmarked_context_12_24857_275302 : frontier 9 ⟨275302, by decide⟩
    (prefixCache 12 24857) (prefixPartial 12 24857) = false := by
  decide +kernel

theorem node_context_12_24857_275302 : EJMOriginalGlobalDAGData.nodes 9 ⟨275302, by decide⟩ =
    .split (coordinate 12) (![⟨275255, by decide⟩,⟨275276, by decide⟩,⟨275293, by decide⟩,⟨275301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24857_275302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24857 ⟨275302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24857
    ⟨275302, by decide⟩ (by decide) (![⟨275255, by decide⟩,⟨275276, by decide⟩,⟨275293, by decide⟩,⟨275301, by decide⟩]) unmarked_context_12_24857_275302 node_context_12_24857_275302
  intro a
  fin_cases a
  · exact context_13_99428_275255
  · exact context_13_99429_275276
  · exact context_13_99430_275293
  · exact context_13_99431_275301

theorem selected_cut_10029 : selected 8 ⟨275327, by decide⟩
    (prefixPartial 13 99432) = some ⟨13, 2, 0, 275327, 99432, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_99432_275327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99432 ⟨275327, by decide⟩ :=
  accepted_of_selected 13 99432 ⟨275327, by decide⟩ ⟨13, 2, 0, 275327, 99432, 1613, 16384⟩
    (by decide) selected_cut_10029

theorem selected_cut_10030 : selected 8 ⟨275354, by decide⟩
    (prefixPartial 13 99433) = some ⟨13, 2, 0, 275354, 99433, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_99433_275354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99433 ⟨275354, by decide⟩ :=
  accepted_of_selected 13 99433 ⟨275354, by decide⟩ ⟨13, 2, 0, 275354, 99433, 1997, 16384⟩
    (by decide) selected_cut_10030

theorem selected_cut_10031 : selected 8 ⟨275374, by decide⟩
    (prefixPartial 13 99434) = some ⟨13, 2, 0, 275374, 99434, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_99434_275374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99434 ⟨275374, by decide⟩ :=
  accepted_of_selected 13 99434 ⟨275374, by decide⟩ ⟨13, 2, 0, 275374, 99434, 1377, 16384⟩
    (by decide) selected_cut_10031

theorem selected_cut_10032 : selected 8 ⟨275383, by decide⟩
    (prefixPartial 13 99435) = some ⟨13, 2, 0, 275383, 99435, 785, 16384⟩ := by
  decide +kernel

theorem context_13_99435_275383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99435 ⟨275383, by decide⟩ :=
  accepted_of_selected 13 99435 ⟨275383, by decide⟩ ⟨13, 2, 0, 275383, 99435, 785, 16384⟩
    (by decide) selected_cut_10032

theorem unmarked_context_12_24858_275384 : frontier 9 ⟨275384, by decide⟩
    (prefixCache 12 24858) (prefixPartial 12 24858) = false := by
  decide +kernel

theorem node_context_12_24858_275384 : EJMOriginalGlobalDAGData.nodes 9 ⟨275384, by decide⟩ =
    .split (coordinate 12) (![⟨275327, by decide⟩,⟨275354, by decide⟩,⟨275374, by decide⟩,⟨275383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24858_275384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24858 ⟨275384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24858
    ⟨275384, by decide⟩ (by decide) (![⟨275327, by decide⟩,⟨275354, by decide⟩,⟨275374, by decide⟩,⟨275383, by decide⟩]) unmarked_context_12_24858_275384 node_context_12_24858_275384
  intro a
  fin_cases a
  · exact context_13_99432_275327
  · exact context_13_99433_275354
  · exact context_13_99434_275374
  · exact context_13_99435_275383

theorem selected_cut_10033 : selected 8 ⟨275414, by decide⟩
    (prefixPartial 13 99436) = some ⟨13, 2, 0, 275414, 99436, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_99436_275414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99436 ⟨275414, by decide⟩ :=
  accepted_of_selected 13 99436 ⟨275414, by decide⟩ ⟨13, 2, 0, 275414, 99436, 1825, 16384⟩
    (by decide) selected_cut_10033

theorem selected_cut_10034 : selected 8 ⟨275444, by decide⟩
    (prefixPartial 13 99437) = some ⟨13, 2, 0, 275444, 99437, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_99437_275444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99437 ⟨275444, by decide⟩ :=
  accepted_of_selected 13 99437 ⟨275444, by decide⟩ ⟨13, 2, 0, 275444, 99437, 2273, 16384⟩
    (by decide) selected_cut_10034

theorem selected_cut_10035 : selected 8 ⟨275462, by decide⟩
    (prefixPartial 13 99438) = some ⟨13, 2, 0, 275462, 99438, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_99438_275462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99438 ⟨275462, by decide⟩ :=
  accepted_of_selected 13 99438 ⟨275462, by decide⟩ ⟨13, 2, 0, 275462, 99438, 1473, 16384⟩
    (by decide) selected_cut_10035

theorem selected_cut_10036 : selected 8 ⟨275468, by decide⟩
    (prefixPartial 13 99439) = some ⟨13, 2, 0, 275468, 99439, 773, 16384⟩ := by
  decide +kernel

theorem context_13_99439_275468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99439 ⟨275468, by decide⟩ :=
  accepted_of_selected 13 99439 ⟨275468, by decide⟩ ⟨13, 2, 0, 275468, 99439, 773, 16384⟩
    (by decide) selected_cut_10036

theorem unmarked_context_12_24859_275469 : frontier 9 ⟨275469, by decide⟩
    (prefixCache 12 24859) (prefixPartial 12 24859) = false := by
  decide +kernel

theorem node_context_12_24859_275469 : EJMOriginalGlobalDAGData.nodes 9 ⟨275469, by decide⟩ =
    .split (coordinate 12) (![⟨275414, by decide⟩,⟨275444, by decide⟩,⟨275462, by decide⟩,⟨275468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24859_275469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24859 ⟨275469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24859
    ⟨275469, by decide⟩ (by decide) (![⟨275414, by decide⟩,⟨275444, by decide⟩,⟨275462, by decide⟩,⟨275468, by decide⟩]) unmarked_context_12_24859_275469 node_context_12_24859_275469
  intro a
  fin_cases a
  · exact context_13_99436_275414
  · exact context_13_99437_275444
  · exact context_13_99438_275462
  · exact context_13_99439_275468

theorem unmarked_context_11_6214_275470 : frontier 10 ⟨275470, by decide⟩
    (prefixCache 11 6214) (prefixPartial 11 6214) = false := by
  decide +kernel

theorem node_context_11_6214_275470 : EJMOriginalGlobalDAGData.nodes 10 ⟨275470, by decide⟩ =
    .split (coordinate 11) (![⟨275236, by decide⟩,⟨275302, by decide⟩,⟨275384, by decide⟩,⟨275469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6214_275470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6214 ⟨275470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6214
    ⟨275470, by decide⟩ (by decide) (![⟨275236, by decide⟩,⟨275302, by decide⟩,⟨275384, by decide⟩,⟨275469, by decide⟩]) unmarked_context_11_6214_275470 node_context_11_6214_275470
  intro a
  fin_cases a
  · exact context_12_24856_275236
  · exact context_12_24857_275302
  · exact context_12_24858_275384
  · exact context_12_24859_275469

theorem selected_cut_10037 : selected 8 ⟨275494, by decide⟩
    (prefixPartial 13 99440) = some ⟨13, 2, 0, 275494, 99440, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_99440_275494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99440 ⟨275494, by decide⟩ :=
  accepted_of_selected 13 99440 ⟨275494, by decide⟩ ⟨13, 2, 0, 275494, 99440, 1445, 16384⟩
    (by decide) selected_cut_10037

theorem selected_cut_10038 : selected 8 ⟨275519, by decide⟩
    (prefixPartial 13 99441) = some ⟨13, 2, 0, 275519, 99441, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_99441_275519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99441 ⟨275519, by decide⟩ :=
  accepted_of_selected 13 99441 ⟨275519, by decide⟩ ⟨13, 2, 0, 275519, 99441, 2001, 16384⟩
    (by decide) selected_cut_10038

theorem selected_cut_10039 : selected 8 ⟨275537, by decide⟩
    (prefixPartial 13 99442) = some ⟨13, 2, 0, 275537, 99442, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_99442_275537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99442 ⟨275537, by decide⟩ :=
  accepted_of_selected 13 99442 ⟨275537, by decide⟩ ⟨13, 2, 0, 275537, 99442, 1453, 16384⟩
    (by decide) selected_cut_10039

theorem selected_cut_10040 : selected 8 ⟨275542, by decide⟩
    (prefixPartial 13 99443) = some ⟨13, 2, 0, 275542, 99443, 793, 16384⟩ := by
  decide +kernel

theorem context_13_99443_275542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99443 ⟨275542, by decide⟩ :=
  accepted_of_selected 13 99443 ⟨275542, by decide⟩ ⟨13, 2, 0, 275542, 99443, 793, 16384⟩
    (by decide) selected_cut_10040

theorem unmarked_context_12_24860_275543 : frontier 9 ⟨275543, by decide⟩
    (prefixCache 12 24860) (prefixPartial 12 24860) = false := by
  decide +kernel

theorem node_context_12_24860_275543 : EJMOriginalGlobalDAGData.nodes 9 ⟨275543, by decide⟩ =
    .split (coordinate 12) (![⟨275494, by decide⟩,⟨275519, by decide⟩,⟨275537, by decide⟩,⟨275542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24860_275543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24860 ⟨275543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24860
    ⟨275543, by decide⟩ (by decide) (![⟨275494, by decide⟩,⟨275519, by decide⟩,⟨275537, by decide⟩,⟨275542, by decide⟩]) unmarked_context_12_24860_275543 node_context_12_24860_275543
  intro a
  fin_cases a
  · exact context_13_99440_275494
  · exact context_13_99441_275519
  · exact context_13_99442_275537
  · exact context_13_99443_275542

theorem selected_cut_10041 : selected 8 ⟨275565, by decide⟩
    (prefixPartial 13 99444) = some ⟨13, 2, 0, 275565, 99444, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_99444_275565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99444 ⟨275565, by decide⟩ :=
  accepted_of_selected 13 99444 ⟨275565, by decide⟩ ⟨13, 2, 0, 275565, 99444, 1349, 16384⟩
    (by decide) selected_cut_10041

theorem selected_cut_10042 : selected 8 ⟨275589, by decide⟩
    (prefixPartial 13 99445) = some ⟨13, 2, 0, 275589, 99445, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_99445_275589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99445 ⟨275589, by decide⟩ :=
  accepted_of_selected 13 99445 ⟨275589, by decide⟩ ⟨13, 2, 0, 275589, 99445, 1893, 16384⟩
    (by decide) selected_cut_10042

theorem selected_cut_10043 : selected 8 ⟨275607, by decide⟩
    (prefixPartial 13 99446) = some ⟨13, 2, 0, 275607, 99446, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_99446_275607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99446 ⟨275607, by decide⟩ :=
  accepted_of_selected 13 99446 ⟨275607, by decide⟩ ⟨13, 2, 0, 275607, 99446, 1509, 16384⟩
    (by decide) selected_cut_10043

theorem selected_cut_10044 : selected 8 ⟨275614, by decide⟩
    (prefixPartial 13 99447) = some ⟨13, 2, 0, 275614, 99447, 741, 16384⟩ := by
  decide +kernel

theorem context_13_99447_275614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99447 ⟨275614, by decide⟩ :=
  accepted_of_selected 13 99447 ⟨275614, by decide⟩ ⟨13, 2, 0, 275614, 99447, 741, 16384⟩
    (by decide) selected_cut_10044

theorem unmarked_context_12_24861_275615 : frontier 9 ⟨275615, by decide⟩
    (prefixCache 12 24861) (prefixPartial 12 24861) = false := by
  decide +kernel

theorem node_context_12_24861_275615 : EJMOriginalGlobalDAGData.nodes 9 ⟨275615, by decide⟩ =
    .split (coordinate 12) (![⟨275565, by decide⟩,⟨275589, by decide⟩,⟨275607, by decide⟩,⟨275614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24861_275615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24861 ⟨275615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24861
    ⟨275615, by decide⟩ (by decide) (![⟨275565, by decide⟩,⟨275589, by decide⟩,⟨275607, by decide⟩,⟨275614, by decide⟩]) unmarked_context_12_24861_275615 node_context_12_24861_275615
  intro a
  fin_cases a
  · exact context_13_99444_275565
  · exact context_13_99445_275589
  · exact context_13_99446_275607
  · exact context_13_99447_275614

theorem selected_cut_10045 : selected 8 ⟨275643, by decide⟩
    (prefixPartial 13 99448) = some ⟨13, 2, 0, 275643, 99448, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_99448_275643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99448 ⟨275643, by decide⟩ :=
  accepted_of_selected 13 99448 ⟨275643, by decide⟩ ⟨13, 2, 0, 275643, 99448, 1637, 16384⟩
    (by decide) selected_cut_10045

theorem selected_cut_10046 : selected 8 ⟨275669, by decide⟩
    (prefixPartial 13 99449) = some ⟨13, 2, 0, 275669, 99449, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_99449_275669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99449 ⟨275669, by decide⟩ :=
  accepted_of_selected 13 99449 ⟨275669, by decide⟩ ⟨13, 2, 0, 275669, 99449, 2329, 16384⟩
    (by decide) selected_cut_10046

theorem selected_cut_10047 : selected 8 ⟨275687, by decide⟩
    (prefixPartial 13 99450) = some ⟨13, 2, 0, 275687, 99450, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_99450_275687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99450 ⟨275687, by decide⟩ :=
  accepted_of_selected 13 99450 ⟨275687, by decide⟩ ⟨13, 2, 0, 275687, 99450, 1433, 16384⟩
    (by decide) selected_cut_10047

theorem selected_cut_10048 : selected 8 ⟨275697, by decide⟩
    (prefixPartial 13 99451) = some ⟨13, 2, 0, 275697, 99451, 829, 16384⟩ := by
  decide +kernel

theorem context_13_99451_275697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99451 ⟨275697, by decide⟩ :=
  accepted_of_selected 13 99451 ⟨275697, by decide⟩ ⟨13, 2, 0, 275697, 99451, 829, 16384⟩
    (by decide) selected_cut_10048

theorem unmarked_context_12_24862_275698 : frontier 9 ⟨275698, by decide⟩
    (prefixCache 12 24862) (prefixPartial 12 24862) = false := by
  decide +kernel

theorem node_context_12_24862_275698 : EJMOriginalGlobalDAGData.nodes 9 ⟨275698, by decide⟩ =
    .split (coordinate 12) (![⟨275643, by decide⟩,⟨275669, by decide⟩,⟨275687, by decide⟩,⟨275697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24862_275698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24862 ⟨275698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24862
    ⟨275698, by decide⟩ (by decide) (![⟨275643, by decide⟩,⟨275669, by decide⟩,⟨275687, by decide⟩,⟨275697, by decide⟩]) unmarked_context_12_24862_275698 node_context_12_24862_275698
  intro a
  fin_cases a
  · exact context_13_99448_275643
  · exact context_13_99449_275669
  · exact context_13_99450_275687
  · exact context_13_99451_275697

theorem selected_cut_10049 : selected 8 ⟨275722, by decide⟩
    (prefixPartial 13 99452) = some ⟨13, 2, 0, 275722, 99452, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_99452_275722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99452 ⟨275722, by decide⟩ :=
  accepted_of_selected 13 99452 ⟨275722, by decide⟩ ⟨13, 2, 0, 275722, 99452, 1789, 16384⟩
    (by decide) selected_cut_10049

theorem selected_cut_10050 : selected 8 ⟨275744, by decide⟩
    (prefixPartial 13 99453) = some ⟨13, 2, 0, 275744, 99453, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_99453_275744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99453 ⟨275744, by decide⟩ :=
  accepted_of_selected 13 99453 ⟨275744, by decide⟩ ⟨13, 2, 0, 275744, 99453, 2229, 16384⟩
    (by decide) selected_cut_10050

theorem selected_cut_10051 : selected 8 ⟨275764, by decide⟩
    (prefixPartial 13 99454) = some ⟨13, 2, 0, 275764, 99454, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_99454_275764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99454 ⟨275764, by decide⟩ :=
  accepted_of_selected 13 99454 ⟨275764, by decide⟩ ⟨13, 2, 0, 275764, 99454, 1541, 16384⟩
    (by decide) selected_cut_10051

theorem selected_cut_10052 : selected 8 ⟨275771, by decide⟩
    (prefixPartial 13 99455) = some ⟨13, 2, 0, 275771, 99455, 821, 16384⟩ := by
  decide +kernel

theorem context_13_99455_275771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99455 ⟨275771, by decide⟩ :=
  accepted_of_selected 13 99455 ⟨275771, by decide⟩ ⟨13, 2, 0, 275771, 99455, 821, 16384⟩
    (by decide) selected_cut_10052

theorem unmarked_context_12_24863_275772 : frontier 9 ⟨275772, by decide⟩
    (prefixCache 12 24863) (prefixPartial 12 24863) = false := by
  decide +kernel

theorem node_context_12_24863_275772 : EJMOriginalGlobalDAGData.nodes 9 ⟨275772, by decide⟩ =
    .split (coordinate 12) (![⟨275722, by decide⟩,⟨275744, by decide⟩,⟨275764, by decide⟩,⟨275771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24863_275772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24863 ⟨275772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24863
    ⟨275772, by decide⟩ (by decide) (![⟨275722, by decide⟩,⟨275744, by decide⟩,⟨275764, by decide⟩,⟨275771, by decide⟩]) unmarked_context_12_24863_275772 node_context_12_24863_275772
  intro a
  fin_cases a
  · exact context_13_99452_275722
  · exact context_13_99453_275744
  · exact context_13_99454_275764
  · exact context_13_99455_275771

theorem unmarked_context_11_6215_275773 : frontier 10 ⟨275773, by decide⟩
    (prefixCache 11 6215) (prefixPartial 11 6215) = false := by
  decide +kernel

theorem node_context_11_6215_275773 : EJMOriginalGlobalDAGData.nodes 10 ⟨275773, by decide⟩ =
    .split (coordinate 11) (![⟨275543, by decide⟩,⟨275615, by decide⟩,⟨275698, by decide⟩,⟨275772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6215_275773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6215 ⟨275773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6215
    ⟨275773, by decide⟩ (by decide) (![⟨275543, by decide⟩,⟨275615, by decide⟩,⟨275698, by decide⟩,⟨275772, by decide⟩]) unmarked_context_11_6215_275773 node_context_11_6215_275773
  intro a
  fin_cases a
  · exact context_12_24860_275543
  · exact context_12_24861_275615
  · exact context_12_24862_275698
  · exact context_12_24863_275772

theorem unmarked_context_10_1553_275774 : frontier 11 ⟨275774, by decide⟩
    (prefixCache 10 1553) (prefixPartial 10 1553) = false := by
  decide +kernel

theorem node_context_10_1553_275774 : EJMOriginalGlobalDAGData.nodes 11 ⟨275774, by decide⟩ =
    .split (coordinate 10) (![⟨274947, by decide⟩,⟨275161, by decide⟩,⟨275470, by decide⟩,⟨275773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1553_275774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1553 ⟨275774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1553
    ⟨275774, by decide⟩ (by decide) (![⟨274947, by decide⟩,⟨275161, by decide⟩,⟨275470, by decide⟩,⟨275773, by decide⟩]) unmarked_context_10_1553_275774 node_context_10_1553_275774
  intro a
  fin_cases a
  · exact context_11_6212_274947
  · exact context_11_6213_275161
  · exact context_11_6214_275470
  · exact context_11_6215_275773

theorem selected_cut_10053 : selected 8 ⟨275787, by decide⟩
    (prefixPartial 13 99456) = some ⟨13, 2, 0, 275787, 99456, 905, 16384⟩ := by
  decide +kernel

theorem context_13_99456_275787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99456 ⟨275787, by decide⟩ :=
  accepted_of_selected 13 99456 ⟨275787, by decide⟩ ⟨13, 2, 0, 275787, 99456, 905, 16384⟩
    (by decide) selected_cut_10053

theorem selected_cut_10054 : selected 8 ⟨275810, by decide⟩
    (prefixPartial 13 99457) = some ⟨13, 2, 0, 275810, 99457, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_99457_275810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99457 ⟨275810, by decide⟩ :=
  accepted_of_selected 13 99457 ⟨275810, by decide⟩ ⟨13, 2, 0, 275810, 99457, 1709, 16384⟩
    (by decide) selected_cut_10054

theorem selected_cut_10055 : selected 8 ⟨275825, by decide⟩
    (prefixPartial 13 99458) = some ⟨13, 2, 0, 275825, 99458, 977, 16384⟩ := by
  decide +kernel

theorem context_13_99458_275825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99458 ⟨275825, by decide⟩ :=
  accepted_of_selected 13 99458 ⟨275825, by decide⟩ ⟨13, 2, 0, 275825, 99458, 977, 16384⟩
    (by decide) selected_cut_10055

theorem selected_cut_10056 : selected 8 ⟨275831, by decide⟩
    (prefixPartial 13 99459) = some ⟨13, 2, 0, 275831, 99459, 689, 16384⟩ := by
  decide +kernel

theorem context_13_99459_275831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99459 ⟨275831, by decide⟩ :=
  accepted_of_selected 13 99459 ⟨275831, by decide⟩ ⟨13, 2, 0, 275831, 99459, 689, 16384⟩
    (by decide) selected_cut_10056

theorem unmarked_context_12_24864_275832 : frontier 9 ⟨275832, by decide⟩
    (prefixCache 12 24864) (prefixPartial 12 24864) = false := by
  decide +kernel

theorem node_context_12_24864_275832 : EJMOriginalGlobalDAGData.nodes 9 ⟨275832, by decide⟩ =
    .split (coordinate 12) (![⟨275787, by decide⟩,⟨275810, by decide⟩,⟨275825, by decide⟩,⟨275831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24864_275832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24864 ⟨275832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24864
    ⟨275832, by decide⟩ (by decide) (![⟨275787, by decide⟩,⟨275810, by decide⟩,⟨275825, by decide⟩,⟨275831, by decide⟩]) unmarked_context_12_24864_275832 node_context_12_24864_275832
  intro a
  fin_cases a
  · exact context_13_99456_275787
  · exact context_13_99457_275810
  · exact context_13_99458_275825
  · exact context_13_99459_275831

theorem selected_cut_10057 : selected 8 ⟨275842, by decide⟩
    (prefixPartial 13 99460) = some ⟨13, 2, 0, 275842, 99460, 865, 16384⟩ := by
  decide +kernel

theorem context_13_99460_275842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99460 ⟨275842, by decide⟩ :=
  accepted_of_selected 13 99460 ⟨275842, by decide⟩ ⟨13, 2, 0, 275842, 99460, 865, 16384⟩
    (by decide) selected_cut_10057

theorem selected_cut_10058 : selected 8 ⟨275863, by decide⟩
    (prefixPartial 13 99461) = some ⟨13, 2, 0, 275863, 99461, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_99461_275863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99461 ⟨275863, by decide⟩ :=
  accepted_of_selected 13 99461 ⟨275863, by decide⟩ ⟨13, 2, 0, 275863, 99461, 1833, 16384⟩
    (by decide) selected_cut_10058

theorem selected_cut_10059 : selected 8 ⟨275882, by decide⟩
    (prefixPartial 13 99462) = some ⟨13, 2, 0, 275882, 99462, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_99462_275882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99462 ⟨275882, by decide⟩ :=
  accepted_of_selected 13 99462 ⟨275882, by decide⟩ ⟨13, 2, 0, 275882, 99462, 1225, 16384⟩
    (by decide) selected_cut_10059

theorem selected_cut_10060 : selected 8 ⟨275892, by decide⟩
    (prefixPartial 13 99463) = some ⟨13, 2, 0, 275892, 99463, 889, 16384⟩ := by
  decide +kernel

theorem context_13_99463_275892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99463 ⟨275892, by decide⟩ :=
  accepted_of_selected 13 99463 ⟨275892, by decide⟩ ⟨13, 2, 0, 275892, 99463, 889, 16384⟩
    (by decide) selected_cut_10060

theorem unmarked_context_12_24865_275893 : frontier 9 ⟨275893, by decide⟩
    (prefixCache 12 24865) (prefixPartial 12 24865) = false := by
  decide +kernel

theorem node_context_12_24865_275893 : EJMOriginalGlobalDAGData.nodes 9 ⟨275893, by decide⟩ =
    .split (coordinate 12) (![⟨275842, by decide⟩,⟨275863, by decide⟩,⟨275882, by decide⟩,⟨275892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24865_275893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24865 ⟨275893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24865
    ⟨275893, by decide⟩ (by decide) (![⟨275842, by decide⟩,⟨275863, by decide⟩,⟨275882, by decide⟩,⟨275892, by decide⟩]) unmarked_context_12_24865_275893 node_context_12_24865_275893
  intro a
  fin_cases a
  · exact context_13_99460_275842
  · exact context_13_99461_275863
  · exact context_13_99462_275882
  · exact context_13_99463_275892

theorem selected_cut_10061 : selected 8 ⟨275906, by decide⟩
    (prefixPartial 13 99464) = some ⟨13, 2, 0, 275906, 99464, 941, 16384⟩ := by
  decide +kernel

theorem context_13_99464_275906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99464 ⟨275906, by decide⟩ :=
  accepted_of_selected 13 99464 ⟨275906, by decide⟩ ⟨13, 2, 0, 275906, 99464, 941, 16384⟩
    (by decide) selected_cut_10061

theorem selected_cut_10062 : selected 8 ⟨275942, by decide⟩
    (prefixPartial 13 99465) = some ⟨13, 2, 0, 275942, 99465, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_99465_275942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99465 ⟨275942, by decide⟩ :=
  accepted_of_selected 13 99465 ⟨275942, by decide⟩ ⟨13, 2, 0, 275942, 99465, 2009, 16384⟩
    (by decide) selected_cut_10062

theorem selected_cut_10063 : selected 8 ⟨275959, by decide⟩
    (prefixPartial 13 99466) = some ⟨13, 2, 0, 275959, 99466, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_99466_275959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99466 ⟨275959, by decide⟩ :=
  accepted_of_selected 13 99466 ⟨275959, by decide⟩ ⟨13, 2, 0, 275959, 99466, 1197, 16384⟩
    (by decide) selected_cut_10063

theorem selected_cut_10064 : selected 8 ⟨275968, by decide⟩
    (prefixPartial 13 99467) = some ⟨13, 2, 0, 275968, 99467, 841, 16384⟩ := by
  decide +kernel

theorem context_13_99467_275968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99467 ⟨275968, by decide⟩ :=
  accepted_of_selected 13 99467 ⟨275968, by decide⟩ ⟨13, 2, 0, 275968, 99467, 841, 16384⟩
    (by decide) selected_cut_10064

theorem unmarked_context_12_24866_275969 : frontier 9 ⟨275969, by decide⟩
    (prefixCache 12 24866) (prefixPartial 12 24866) = false := by
  decide +kernel

theorem node_context_12_24866_275969 : EJMOriginalGlobalDAGData.nodes 9 ⟨275969, by decide⟩ =
    .split (coordinate 12) (![⟨275906, by decide⟩,⟨275942, by decide⟩,⟨275959, by decide⟩,⟨275968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24866_275969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24866 ⟨275969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24866
    ⟨275969, by decide⟩ (by decide) (![⟨275906, by decide⟩,⟨275942, by decide⟩,⟨275959, by decide⟩,⟨275968, by decide⟩]) unmarked_context_12_24866_275969 node_context_12_24866_275969
  intro a
  fin_cases a
  · exact context_13_99464_275906
  · exact context_13_99465_275942
  · exact context_13_99466_275959
  · exact context_13_99467_275968

theorem selected_cut_10065 : selected 8 ⟨275988, by decide⟩
    (prefixPartial 13 99468) = some ⟨13, 2, 0, 275988, 99468, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_99468_275988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99468 ⟨275988, by decide⟩ :=
  accepted_of_selected 13 99468 ⟨275988, by decide⟩ ⟨13, 2, 0, 275988, 99468, 1181, 16384⟩
    (by decide) selected_cut_10065

theorem selected_cut_10066 : selected 8 ⟨276019, by decide⟩
    (prefixPartial 13 99469) = some ⟨13, 2, 0, 276019, 99469, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_99469_276019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99469 ⟨276019, by decide⟩ :=
  accepted_of_selected 13 99469 ⟨276019, by decide⟩ ⟨13, 2, 0, 276019, 99469, 2117, 16384⟩
    (by decide) selected_cut_10066

theorem selected_cut_10067 : selected 8 ⟨276039, by decide⟩
    (prefixPartial 13 99470) = some ⟨13, 2, 0, 276039, 99470, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_99470_276039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99470 ⟨276039, by decide⟩ :=
  accepted_of_selected 13 99470 ⟨276039, by decide⟩ ⟨13, 2, 0, 276039, 99470, 1297, 16384⟩
    (by decide) selected_cut_10067

theorem selected_cut_10068 : selected 8 ⟨276044, by decide⟩
    (prefixPartial 13 99471) = some ⟨13, 2, 0, 276044, 99471, 877, 16384⟩ := by
  decide +kernel

theorem context_13_99471_276044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99471 ⟨276044, by decide⟩ :=
  accepted_of_selected 13 99471 ⟨276044, by decide⟩ ⟨13, 2, 0, 276044, 99471, 877, 16384⟩
    (by decide) selected_cut_10068

theorem unmarked_context_12_24867_276045 : frontier 9 ⟨276045, by decide⟩
    (prefixCache 12 24867) (prefixPartial 12 24867) = false := by
  decide +kernel

theorem node_context_12_24867_276045 : EJMOriginalGlobalDAGData.nodes 9 ⟨276045, by decide⟩ =
    .split (coordinate 12) (![⟨275988, by decide⟩,⟨276019, by decide⟩,⟨276039, by decide⟩,⟨276044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24867_276045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24867 ⟨276045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24867
    ⟨276045, by decide⟩ (by decide) (![⟨275988, by decide⟩,⟨276019, by decide⟩,⟨276039, by decide⟩,⟨276044, by decide⟩]) unmarked_context_12_24867_276045 node_context_12_24867_276045
  intro a
  fin_cases a
  · exact context_13_99468_275988
  · exact context_13_99469_276019
  · exact context_13_99470_276039
  · exact context_13_99471_276044

theorem unmarked_context_11_6216_276046 : frontier 10 ⟨276046, by decide⟩
    (prefixCache 11 6216) (prefixPartial 11 6216) = false := by
  decide +kernel

theorem node_context_11_6216_276046 : EJMOriginalGlobalDAGData.nodes 10 ⟨276046, by decide⟩ =
    .split (coordinate 11) (![⟨275832, by decide⟩,⟨275893, by decide⟩,⟨275969, by decide⟩,⟨276045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6216_276046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6216 ⟨276046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6216
    ⟨276046, by decide⟩ (by decide) (![⟨275832, by decide⟩,⟨275893, by decide⟩,⟨275969, by decide⟩,⟨276045, by decide⟩]) unmarked_context_11_6216_276046 node_context_11_6216_276046
  intro a
  fin_cases a
  · exact context_12_24864_275832
  · exact context_12_24865_275893
  · exact context_12_24866_275969
  · exact context_12_24867_276045

theorem selected_cut_10069 : selected 8 ⟨276065, by decide⟩
    (prefixPartial 13 99472) = some ⟨13, 2, 0, 276065, 99472, 953, 16384⟩ := by
  decide +kernel

theorem context_13_99472_276065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99472 ⟨276065, by decide⟩ :=
  accepted_of_selected 13 99472 ⟨276065, by decide⟩ ⟨13, 2, 0, 276065, 99472, 953, 16384⟩
    (by decide) selected_cut_10069

theorem selected_cut_10070 : selected 8 ⟨276090, by decide⟩
    (prefixPartial 13 99473) = some ⟨13, 2, 0, 276090, 99473, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_99473_276090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99473 ⟨276090, by decide⟩ :=
  accepted_of_selected 13 99473 ⟨276090, by decide⟩ ⟨13, 2, 0, 276090, 99473, 1881, 16384⟩
    (by decide) selected_cut_10070

theorem selected_cut_10071 : selected 8 ⟨276107, by decide⟩
    (prefixPartial 13 99474) = some ⟨13, 2, 0, 276107, 99474, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_99474_276107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99474 ⟨276107, by decide⟩ :=
  accepted_of_selected 13 99474 ⟨276107, by decide⟩ ⟨13, 2, 0, 276107, 99474, 1225, 16384⟩
    (by decide) selected_cut_10071

theorem selected_cut_10072 : selected 8 ⟨276115, by decide⟩
    (prefixPartial 13 99475) = some ⟨13, 2, 0, 276115, 99475, 793, 16384⟩ := by
  decide +kernel

theorem context_13_99475_276115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99475 ⟨276115, by decide⟩ :=
  accepted_of_selected 13 99475 ⟨276115, by decide⟩ ⟨13, 2, 0, 276115, 99475, 793, 16384⟩
    (by decide) selected_cut_10072

theorem unmarked_context_12_24868_276116 : frontier 9 ⟨276116, by decide⟩
    (prefixCache 12 24868) (prefixPartial 12 24868) = false := by
  decide +kernel

theorem node_context_12_24868_276116 : EJMOriginalGlobalDAGData.nodes 9 ⟨276116, by decide⟩ =
    .split (coordinate 12) (![⟨276065, by decide⟩,⟨276090, by decide⟩,⟨276107, by decide⟩,⟨276115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24868_276116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24868 ⟨276116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24868
    ⟨276116, by decide⟩ (by decide) (![⟨276065, by decide⟩,⟨276090, by decide⟩,⟨276107, by decide⟩,⟨276115, by decide⟩]) unmarked_context_12_24868_276116 node_context_12_24868_276116
  intro a
  fin_cases a
  · exact context_13_99472_276065
  · exact context_13_99473_276090
  · exact context_13_99474_276107
  · exact context_13_99475_276115

theorem selected_cut_10073 : selected 8 ⟨276132, by decide⟩
    (prefixPartial 13 99476) = some ⟨13, 2, 0, 276132, 99476, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_99476_276132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99476 ⟨276132, by decide⟩ :=
  accepted_of_selected 13 99476 ⟨276132, by decide⟩ ⟨13, 2, 0, 276132, 99476, 1561, 16384⟩
    (by decide) selected_cut_10073

theorem selected_cut_10074 : selected 8 ⟨276183, by decide⟩
    (prefixPartial 13 99477) = some ⟨13, 2, 0, 276183, 99477, 3329, 16384⟩ := by
  decide +kernel

theorem context_13_99477_276183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99477 ⟨276183, by decide⟩ :=
  accepted_of_selected 13 99477 ⟨276183, by decide⟩ ⟨13, 2, 0, 276183, 99477, 3329, 16384⟩
    (by decide) selected_cut_10074

theorem selected_cut_10075 : selected 8 ⟨276201, by decide⟩
    (prefixPartial 13 99478) = some ⟨13, 2, 0, 276201, 99478, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_99478_276201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99478 ⟨276201, by decide⟩ :=
  accepted_of_selected 13 99478 ⟨276201, by decide⟩ ⟨13, 2, 0, 276201, 99478, 2137, 16384⟩
    (by decide) selected_cut_10075

theorem selected_cut_10076 : selected 8 ⟨276207, by decide⟩
    (prefixPartial 13 99479) = some ⟨13, 2, 0, 276207, 99479, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_99479_276207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99479 ⟨276207, by decide⟩ :=
  accepted_of_selected 13 99479 ⟨276207, by decide⟩ ⟨13, 2, 0, 276207, 99479, 1157, 16384⟩
    (by decide) selected_cut_10076

theorem unmarked_context_12_24869_276208 : frontier 9 ⟨276208, by decide⟩
    (prefixCache 12 24869) (prefixPartial 12 24869) = false := by
  decide +kernel

theorem node_context_12_24869_276208 : EJMOriginalGlobalDAGData.nodes 9 ⟨276208, by decide⟩ =
    .split (coordinate 12) (![⟨276132, by decide⟩,⟨276183, by decide⟩,⟨276201, by decide⟩,⟨276207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24869_276208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24869 ⟨276208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24869
    ⟨276208, by decide⟩ (by decide) (![⟨276132, by decide⟩,⟨276183, by decide⟩,⟨276201, by decide⟩,⟨276207, by decide⟩]) unmarked_context_12_24869_276208 node_context_12_24869_276208
  intro a
  fin_cases a
  · exact context_13_99476_276132
  · exact context_13_99477_276183
  · exact context_13_99478_276201
  · exact context_13_99479_276207

theorem selected_cut_10077 : selected 8 ⟨276226, by decide⟩
    (prefixPartial 13 99480) = some ⟨13, 2, 0, 276226, 99480, 965, 16384⟩ := by
  decide +kernel

theorem context_13_99480_276226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99480 ⟨276226, by decide⟩ :=
  accepted_of_selected 13 99480 ⟨276226, by decide⟩ ⟨13, 2, 0, 276226, 99480, 965, 16384⟩
    (by decide) selected_cut_10077

theorem selected_cut_10078 : selected 8 ⟨276247, by decide⟩
    (prefixPartial 13 99481) = some ⟨13, 2, 0, 276247, 99481, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_99481_276247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99481 ⟨276247, by decide⟩ :=
  accepted_of_selected 13 99481 ⟨276247, by decide⟩ ⟨13, 2, 0, 276247, 99481, 2073, 16384⟩
    (by decide) selected_cut_10078

theorem selected_cut_10079 : selected 8 ⟨276271, by decide⟩
    (prefixPartial 13 99482) = some ⟨13, 2, 0, 276271, 99482, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_99482_276271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99482 ⟨276271, by decide⟩ :=
  accepted_of_selected 13 99482 ⟨276271, by decide⟩ ⟨13, 2, 0, 276271, 99482, 1349, 16384⟩
    (by decide) selected_cut_10079

theorem selected_cut_10080 : selected 8 ⟨276278, by decide⟩
    (prefixPartial 13 99483) = some ⟨13, 2, 0, 276278, 99483, 905, 16384⟩ := by
  decide +kernel

theorem context_13_99483_276278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99483 ⟨276278, by decide⟩ :=
  accepted_of_selected 13 99483 ⟨276278, by decide⟩ ⟨13, 2, 0, 276278, 99483, 905, 16384⟩
    (by decide) selected_cut_10080

theorem unmarked_context_12_24870_276279 : frontier 9 ⟨276279, by decide⟩
    (prefixCache 12 24870) (prefixPartial 12 24870) = false := by
  decide +kernel

theorem node_context_12_24870_276279 : EJMOriginalGlobalDAGData.nodes 9 ⟨276279, by decide⟩ =
    .split (coordinate 12) (![⟨276226, by decide⟩,⟨276247, by decide⟩,⟨276271, by decide⟩,⟨276278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24870_276279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24870 ⟨276279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24870
    ⟨276279, by decide⟩ (by decide) (![⟨276226, by decide⟩,⟨276247, by decide⟩,⟨276271, by decide⟩,⟨276278, by decide⟩]) unmarked_context_12_24870_276279 node_context_12_24870_276279
  intro a
  fin_cases a
  · exact context_13_99480_276226
  · exact context_13_99481_276247
  · exact context_13_99482_276271
  · exact context_13_99483_276278

theorem selected_cut_10081 : selected 8 ⟨276296, by decide⟩
    (prefixPartial 13 99484) = some ⟨13, 2, 0, 276296, 99484, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_99484_276296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99484 ⟨276296, by decide⟩ :=
  accepted_of_selected 13 99484 ⟨276296, by decide⟩ ⟨13, 2, 0, 276296, 99484, 1081, 16384⟩
    (by decide) selected_cut_10081

theorem selected_cut_10082 : selected 8 ⟨276322, by decide⟩
    (prefixPartial 13 99485) = some ⟨13, 2, 0, 276322, 99485, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_99485_276322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99485 ⟨276322, by decide⟩ :=
  accepted_of_selected 13 99485 ⟨276322, by decide⟩ ⟨13, 2, 0, 276322, 99485, 2333, 16384⟩
    (by decide) selected_cut_10082

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
