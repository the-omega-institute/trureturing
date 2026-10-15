/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover050
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04898 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 18773) = some ⟨12, 1, 0, 126371, 18773, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18773_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18773 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 18773 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 18773, 1, 65536⟩
    (by decide) selected_cut_04898

theorem selected_cut_04899 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75096) = some ⟨13, 1, 0, 3444, 75096, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75096_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75096 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75096 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75096, 1, 16384⟩
    (by decide) selected_cut_04899

theorem selected_cut_04900 : selected 8 ⟨154597, by decide⟩
    (prefixPartial 13 75097) = some ⟨13, 2, 0, 154597, 75097, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_75097_154597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75097 ⟨154597, by decide⟩ :=
  accepted_of_selected 13 75097 ⟨154597, by decide⟩ ⟨13, 2, 0, 154597, 75097, 1509, 16384⟩
    (by decide) selected_cut_04900

theorem selected_cut_04901 : selected 8 ⟨154617, by decide⟩
    (prefixPartial 13 75098) = some ⟨13, 2, 0, 154617, 75098, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_75098_154617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75098 ⟨154617, by decide⟩ :=
  accepted_of_selected 13 75098 ⟨154617, by decide⟩ ⟨13, 2, 0, 154617, 75098, 1605, 16384⟩
    (by decide) selected_cut_04901

theorem selected_cut_04902 : selected 8 ⟨154628, by decide⟩
    (prefixPartial 13 75099) = some ⟨13, 2, 0, 154628, 75099, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_75099_154628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75099 ⟨154628, by decide⟩ :=
  accepted_of_selected 13 75099 ⟨154628, by decide⟩ ⟨13, 2, 0, 154628, 75099, 1033, 16384⟩
    (by decide) selected_cut_04902

theorem unmarked_context_12_18774_154629 : frontier 9 ⟨154629, by decide⟩
    (prefixCache 12 18774) (prefixPartial 12 18774) = false := by
  decide +kernel

theorem node_context_12_18774_154629 : EJMOriginalGlobalDAGData.nodes 9 ⟨154629, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154597, by decide⟩,⟨154617, by decide⟩,⟨154628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18774_154629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18774 ⟨154629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18774
    ⟨154629, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154597, by decide⟩,⟨154617, by decide⟩,⟨154628, by decide⟩]) unmarked_context_12_18774_154629 node_context_12_18774_154629
  intro a
  fin_cases a
  · exact context_13_75096_3444
  · exact context_13_75097_154597
  · exact context_13_75098_154617
  · exact context_13_75099_154628

theorem selected_cut_04903 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75100) = some ⟨13, 1, 0, 3444, 75100, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75100_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75100 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75100 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75100, 1, 16384⟩
    (by decide) selected_cut_04903

theorem selected_cut_04904 : selected 8 ⟨154648, by decide⟩
    (prefixPartial 13 75101) = some ⟨13, 2, 0, 154648, 75101, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_75101_154648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75101 ⟨154648, by decide⟩ :=
  accepted_of_selected 13 75101 ⟨154648, by decide⟩ ⟨13, 2, 0, 154648, 75101, 1553, 16384⟩
    (by decide) selected_cut_04904

theorem selected_cut_04905 : selected 8 ⟨154669, by decide⟩
    (prefixPartial 13 75102) = some ⟨13, 2, 0, 154669, 75102, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_75102_154669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75102 ⟨154669, by decide⟩ :=
  accepted_of_selected 13 75102 ⟨154669, by decide⟩ ⟨13, 2, 0, 154669, 75102, 1609, 16384⟩
    (by decide) selected_cut_04905

theorem selected_cut_04906 : selected 8 ⟨154679, by decide⟩
    (prefixPartial 13 75103) = some ⟨13, 2, 0, 154679, 75103, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_75103_154679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75103 ⟨154679, by decide⟩ :=
  accepted_of_selected 13 75103 ⟨154679, by decide⟩ ⟨13, 2, 0, 154679, 75103, 1013, 16384⟩
    (by decide) selected_cut_04906

theorem unmarked_context_12_18775_154680 : frontier 9 ⟨154680, by decide⟩
    (prefixCache 12 18775) (prefixPartial 12 18775) = false := by
  decide +kernel

theorem node_context_12_18775_154680 : EJMOriginalGlobalDAGData.nodes 9 ⟨154680, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154648, by decide⟩,⟨154669, by decide⟩,⟨154679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18775_154680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18775 ⟨154680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18775
    ⟨154680, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154648, by decide⟩,⟨154669, by decide⟩,⟨154679, by decide⟩]) unmarked_context_12_18775_154680 node_context_12_18775_154680
  intro a
  fin_cases a
  · exact context_13_75100_3444
  · exact context_13_75101_154648
  · exact context_13_75102_154669
  · exact context_13_75103_154679

theorem unmarked_context_11_4693_154681 : frontier 10 ⟨154681, by decide⟩
    (prefixCache 11 4693) (prefixPartial 11 4693) = false := by
  decide +kernel

theorem node_context_11_4693_154681 : EJMOriginalGlobalDAGData.nodes 10 ⟨154681, by decide⟩ =
    .split (coordinate 11) (![⟨154580, by decide⟩,⟨126371, by decide⟩,⟨154629, by decide⟩,⟨154680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4693_154681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4693 ⟨154681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4693
    ⟨154681, by decide⟩ (by decide) (![⟨154580, by decide⟩,⟨126371, by decide⟩,⟨154629, by decide⟩,⟨154680, by decide⟩]) unmarked_context_11_4693_154681 node_context_11_4693_154681
  intro a
  fin_cases a
  · exact context_12_18772_154580
  · exact context_12_18773_126371
  · exact context_12_18774_154629
  · exact context_12_18775_154680

theorem selected_cut_04907 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75104) = some ⟨13, 1, 0, 3444, 75104, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75104_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75104 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75104 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75104, 1, 16384⟩
    (by decide) selected_cut_04907

theorem selected_cut_04908 : selected 8 ⟨154698, by decide⟩
    (prefixPartial 13 75105) = some ⟨13, 2, 0, 154698, 75105, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_75105_154698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75105 ⟨154698, by decide⟩ :=
  accepted_of_selected 13 75105 ⟨154698, by decide⟩ ⟨13, 2, 0, 154698, 75105, 1533, 16384⟩
    (by decide) selected_cut_04908

theorem selected_cut_04909 : selected 8 ⟨154722, by decide⟩
    (prefixPartial 13 75106) = some ⟨13, 2, 0, 154722, 75106, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_75106_154722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75106 ⟨154722, by decide⟩ :=
  accepted_of_selected 13 75106 ⟨154722, by decide⟩ ⟨13, 2, 0, 154722, 75106, 1741, 16384⟩
    (by decide) selected_cut_04909

theorem selected_cut_04910 : selected 8 ⟨154729, by decide⟩
    (prefixPartial 13 75107) = some ⟨13, 2, 0, 154729, 75107, 969, 16384⟩ := by
  decide +kernel

theorem context_13_75107_154729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75107 ⟨154729, by decide⟩ :=
  accepted_of_selected 13 75107 ⟨154729, by decide⟩ ⟨13, 2, 0, 154729, 75107, 969, 16384⟩
    (by decide) selected_cut_04910

theorem unmarked_context_12_18776_154730 : frontier 9 ⟨154730, by decide⟩
    (prefixCache 12 18776) (prefixPartial 12 18776) = false := by
  decide +kernel

theorem node_context_12_18776_154730 : EJMOriginalGlobalDAGData.nodes 9 ⟨154730, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154698, by decide⟩,⟨154722, by decide⟩,⟨154729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18776_154730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18776 ⟨154730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18776
    ⟨154730, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154698, by decide⟩,⟨154722, by decide⟩,⟨154729, by decide⟩]) unmarked_context_12_18776_154730 node_context_12_18776_154730
  intro a
  fin_cases a
  · exact context_13_75104_3444
  · exact context_13_75105_154698
  · exact context_13_75106_154722
  · exact context_13_75107_154729

theorem selected_cut_04911 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75108) = some ⟨13, 1, 0, 3444, 75108, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75108_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75108 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75108 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75108, 1, 16384⟩
    (by decide) selected_cut_04911

theorem selected_cut_04912 : selected 8 ⟨154754, by decide⟩
    (prefixPartial 13 75109) = some ⟨13, 2, 0, 154754, 75109, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_75109_154754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75109 ⟨154754, by decide⟩ :=
  accepted_of_selected 13 75109 ⟨154754, by decide⟩ ⟨13, 2, 0, 154754, 75109, 1657, 16384⟩
    (by decide) selected_cut_04912

theorem selected_cut_04913 : selected 8 ⟨154788, by decide⟩
    (prefixPartial 13 75110) = some ⟨13, 2, 0, 154788, 75110, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_75110_154788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75110 ⟨154788, by decide⟩ :=
  accepted_of_selected 13 75110 ⟨154788, by decide⟩ ⟨13, 2, 0, 154788, 75110, 2297, 16384⟩
    (by decide) selected_cut_04913

theorem selected_cut_04914 : selected 8 ⟨154800, by decide⟩
    (prefixPartial 13 75111) = some ⟨13, 2, 0, 154800, 75111, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_75111_154800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75111 ⟨154800, by decide⟩ :=
  accepted_of_selected 13 75111 ⟨154800, by decide⟩ ⟨13, 2, 0, 154800, 75111, 1209, 16384⟩
    (by decide) selected_cut_04914

theorem unmarked_context_12_18777_154801 : frontier 9 ⟨154801, by decide⟩
    (prefixCache 12 18777) (prefixPartial 12 18777) = false := by
  decide +kernel

theorem node_context_12_18777_154801 : EJMOriginalGlobalDAGData.nodes 9 ⟨154801, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154754, by decide⟩,⟨154788, by decide⟩,⟨154800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18777_154801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18777 ⟨154801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18777
    ⟨154801, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154754, by decide⟩,⟨154788, by decide⟩,⟨154800, by decide⟩]) unmarked_context_12_18777_154801 node_context_12_18777_154801
  intro a
  fin_cases a
  · exact context_13_75108_3444
  · exact context_13_75109_154754
  · exact context_13_75110_154788
  · exact context_13_75111_154800

theorem selected_cut_04915 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75112) = some ⟨13, 1, 0, 3444, 75112, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75112_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75112 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75112 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75112, 1, 16384⟩
    (by decide) selected_cut_04915

theorem selected_cut_04916 : selected 8 ⟨154815, by decide⟩
    (prefixPartial 13 75113) = some ⟨13, 2, 0, 154815, 75113, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_75113_154815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75113 ⟨154815, by decide⟩ :=
  accepted_of_selected 13 75113 ⟨154815, by decide⟩ ⟨13, 2, 0, 154815, 75113, 1409, 16384⟩
    (by decide) selected_cut_04916

theorem selected_cut_04917 : selected 8 ⟨154848, by decide⟩
    (prefixPartial 13 75114) = some ⟨13, 2, 0, 154848, 75114, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_75114_154848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75114 ⟨154848, by decide⟩ :=
  accepted_of_selected 13 75114 ⟨154848, by decide⟩ ⟨13, 2, 0, 154848, 75114, 1957, 16384⟩
    (by decide) selected_cut_04917

theorem selected_cut_04918 : selected 8 ⟨154862, by decide⟩
    (prefixPartial 13 75115) = some ⟨13, 2, 0, 154862, 75115, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_75115_154862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75115 ⟨154862, by decide⟩ :=
  accepted_of_selected 13 75115 ⟨154862, by decide⟩ ⟨13, 2, 0, 154862, 75115, 1009, 16384⟩
    (by decide) selected_cut_04918

theorem unmarked_context_12_18778_154863 : frontier 9 ⟨154863, by decide⟩
    (prefixCache 12 18778) (prefixPartial 12 18778) = false := by
  decide +kernel

theorem node_context_12_18778_154863 : EJMOriginalGlobalDAGData.nodes 9 ⟨154863, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154815, by decide⟩,⟨154848, by decide⟩,⟨154862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18778_154863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18778 ⟨154863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18778
    ⟨154863, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154815, by decide⟩,⟨154848, by decide⟩,⟨154862, by decide⟩]) unmarked_context_12_18778_154863 node_context_12_18778_154863
  intro a
  fin_cases a
  · exact context_13_75112_3444
  · exact context_13_75113_154815
  · exact context_13_75114_154848
  · exact context_13_75115_154862

theorem selected_cut_04919 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75116) = some ⟨13, 1, 0, 3444, 75116, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75116_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75116 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75116 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75116, 1, 16384⟩
    (by decide) selected_cut_04919

theorem selected_cut_04920 : selected 8 ⟨154883, by decide⟩
    (prefixPartial 13 75117) = some ⟨13, 2, 0, 154883, 75117, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_75117_154883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75117 ⟨154883, by decide⟩ :=
  accepted_of_selected 13 75117 ⟨154883, by decide⟩ ⟨13, 2, 0, 154883, 75117, 1685, 16384⟩
    (by decide) selected_cut_04920

theorem selected_cut_04921 : selected 8 ⟨154917, by decide⟩
    (prefixPartial 13 75118) = some ⟨13, 2, 0, 154917, 75118, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_75118_154917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75118 ⟨154917, by decide⟩ :=
  accepted_of_selected 13 75118 ⟨154917, by decide⟩ ⟨13, 2, 0, 154917, 75118, 2165, 16384⟩
    (by decide) selected_cut_04921

theorem selected_cut_04922 : selected 8 ⟨154926, by decide⟩
    (prefixPartial 13 75119) = some ⟨13, 2, 0, 154926, 75119, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_75119_154926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75119 ⟨154926, by decide⟩ :=
  accepted_of_selected 13 75119 ⟨154926, by decide⟩ ⟨13, 2, 0, 154926, 75119, 1089, 16384⟩
    (by decide) selected_cut_04922

theorem unmarked_context_12_18779_154927 : frontier 9 ⟨154927, by decide⟩
    (prefixCache 12 18779) (prefixPartial 12 18779) = false := by
  decide +kernel

theorem node_context_12_18779_154927 : EJMOriginalGlobalDAGData.nodes 9 ⟨154927, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154883, by decide⟩,⟨154917, by decide⟩,⟨154926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18779_154927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18779 ⟨154927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18779
    ⟨154927, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154883, by decide⟩,⟨154917, by decide⟩,⟨154926, by decide⟩]) unmarked_context_12_18779_154927 node_context_12_18779_154927
  intro a
  fin_cases a
  · exact context_13_75116_3444
  · exact context_13_75117_154883
  · exact context_13_75118_154917
  · exact context_13_75119_154926

theorem unmarked_context_11_4694_154928 : frontier 10 ⟨154928, by decide⟩
    (prefixCache 11 4694) (prefixPartial 11 4694) = false := by
  decide +kernel

theorem node_context_11_4694_154928 : EJMOriginalGlobalDAGData.nodes 10 ⟨154928, by decide⟩ =
    .split (coordinate 11) (![⟨154730, by decide⟩,⟨154801, by decide⟩,⟨154863, by decide⟩,⟨154927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4694_154928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4694 ⟨154928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4694
    ⟨154928, by decide⟩ (by decide) (![⟨154730, by decide⟩,⟨154801, by decide⟩,⟨154863, by decide⟩,⟨154927, by decide⟩]) unmarked_context_11_4694_154928 node_context_11_4694_154928
  intro a
  fin_cases a
  · exact context_12_18776_154730
  · exact context_12_18777_154801
  · exact context_12_18778_154863
  · exact context_12_18779_154927

theorem selected_cut_04923 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75120) = some ⟨13, 1, 0, 3444, 75120, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75120_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75120 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75120 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75120, 1, 16384⟩
    (by decide) selected_cut_04923

theorem selected_cut_04924 : selected 8 ⟨154942, by decide⟩
    (prefixPartial 13 75121) = some ⟨13, 2, 0, 154942, 75121, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_75121_154942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75121 ⟨154942, by decide⟩ :=
  accepted_of_selected 13 75121 ⟨154942, by decide⟩ ⟨13, 2, 0, 154942, 75121, 1477, 16384⟩
    (by decide) selected_cut_04924

theorem selected_cut_04925 : selected 8 ⟨154968, by decide⟩
    (prefixPartial 13 75122) = some ⟨13, 2, 0, 154968, 75122, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_75122_154968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75122 ⟨154968, by decide⟩ :=
  accepted_of_selected 13 75122 ⟨154968, by decide⟩ ⟨13, 2, 0, 154968, 75122, 1621, 16384⟩
    (by decide) selected_cut_04925

theorem selected_cut_04926 : selected 8 ⟨154979, by decide⟩
    (prefixPartial 13 75123) = some ⟨13, 2, 0, 154979, 75123, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_75123_154979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75123 ⟨154979, by decide⟩ :=
  accepted_of_selected 13 75123 ⟨154979, by decide⟩ ⟨13, 2, 0, 154979, 75123, 1081, 16384⟩
    (by decide) selected_cut_04926

theorem unmarked_context_12_18780_154980 : frontier 9 ⟨154980, by decide⟩
    (prefixCache 12 18780) (prefixPartial 12 18780) = false := by
  decide +kernel

theorem node_context_12_18780_154980 : EJMOriginalGlobalDAGData.nodes 9 ⟨154980, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154942, by decide⟩,⟨154968, by decide⟩,⟨154979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18780_154980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18780 ⟨154980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18780
    ⟨154980, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154942, by decide⟩,⟨154968, by decide⟩,⟨154979, by decide⟩]) unmarked_context_12_18780_154980 node_context_12_18780_154980
  intro a
  fin_cases a
  · exact context_13_75120_3444
  · exact context_13_75121_154942
  · exact context_13_75122_154968
  · exact context_13_75123_154979

theorem selected_cut_04927 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75124) = some ⟨13, 1, 0, 3444, 75124, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75124_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75124 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75124 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75124, 1, 16384⟩
    (by decide) selected_cut_04927

theorem selected_cut_04928 : selected 8 ⟨154999, by decide⟩
    (prefixPartial 13 75125) = some ⟨13, 2, 0, 154999, 75125, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_75125_154999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75125 ⟨154999, by decide⟩ :=
  accepted_of_selected 13 75125 ⟨154999, by decide⟩ ⟨13, 2, 0, 154999, 75125, 1469, 16384⟩
    (by decide) selected_cut_04928

theorem selected_cut_04929 : selected 8 ⟨155034, by decide⟩
    (prefixPartial 13 75126) = some ⟨13, 2, 0, 155034, 75126, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_75126_155034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75126 ⟨155034, by decide⟩ :=
  accepted_of_selected 13 75126 ⟨155034, by decide⟩ ⟨13, 2, 0, 155034, 75126, 2261, 16384⟩
    (by decide) selected_cut_04929

theorem selected_cut_04930 : selected 8 ⟨155052, by decide⟩
    (prefixPartial 13 75127) = some ⟨13, 2, 0, 155052, 75127, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_75127_155052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75127 ⟨155052, by decide⟩ :=
  accepted_of_selected 13 75127 ⟨155052, by decide⟩ ⟨13, 2, 0, 155052, 75127, 1273, 16384⟩
    (by decide) selected_cut_04930

theorem unmarked_context_12_18781_155053 : frontier 9 ⟨155053, by decide⟩
    (prefixCache 12 18781) (prefixPartial 12 18781) = false := by
  decide +kernel

theorem node_context_12_18781_155053 : EJMOriginalGlobalDAGData.nodes 9 ⟨155053, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154999, by decide⟩,⟨155034, by decide⟩,⟨155052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18781_155053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18781 ⟨155053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18781
    ⟨155053, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154999, by decide⟩,⟨155034, by decide⟩,⟨155052, by decide⟩]) unmarked_context_12_18781_155053 node_context_12_18781_155053
  intro a
  fin_cases a
  · exact context_13_75124_3444
  · exact context_13_75125_154999
  · exact context_13_75126_155034
  · exact context_13_75127_155052

theorem selected_cut_04931 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75128) = some ⟨13, 1, 0, 3444, 75128, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75128_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75128 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75128 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75128, 1, 16384⟩
    (by decide) selected_cut_04931

theorem selected_cut_04932 : selected 8 ⟨155068, by decide⟩
    (prefixPartial 13 75129) = some ⟨13, 2, 0, 155068, 75129, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_75129_155068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75129 ⟨155068, by decide⟩ :=
  accepted_of_selected 13 75129 ⟨155068, by decide⟩ ⟨13, 2, 0, 155068, 75129, 1465, 16384⟩
    (by decide) selected_cut_04932

theorem selected_cut_04933 : selected 8 ⟨155098, by decide⟩
    (prefixPartial 13 75130) = some ⟨13, 2, 0, 155098, 75130, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_75130_155098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75130 ⟨155098, by decide⟩ :=
  accepted_of_selected 13 75130 ⟨155098, by decide⟩ ⟨13, 2, 0, 155098, 75130, 2133, 16384⟩
    (by decide) selected_cut_04933

theorem selected_cut_04934 : selected 8 ⟨155109, by decide⟩
    (prefixPartial 13 75131) = some ⟨13, 2, 0, 155109, 75131, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_75131_155109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75131 ⟨155109, by decide⟩ :=
  accepted_of_selected 13 75131 ⟨155109, by decide⟩ ⟨13, 2, 0, 155109, 75131, 1181, 16384⟩
    (by decide) selected_cut_04934

theorem unmarked_context_12_18782_155110 : frontier 9 ⟨155110, by decide⟩
    (prefixCache 12 18782) (prefixPartial 12 18782) = false := by
  decide +kernel

theorem node_context_12_18782_155110 : EJMOriginalGlobalDAGData.nodes 9 ⟨155110, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155068, by decide⟩,⟨155098, by decide⟩,⟨155109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18782_155110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18782 ⟨155110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18782
    ⟨155110, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155068, by decide⟩,⟨155098, by decide⟩,⟨155109, by decide⟩]) unmarked_context_12_18782_155110 node_context_12_18782_155110
  intro a
  fin_cases a
  · exact context_13_75128_3444
  · exact context_13_75129_155068
  · exact context_13_75130_155098
  · exact context_13_75131_155109

theorem selected_cut_04935 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75132) = some ⟨13, 1, 0, 3444, 75132, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75132_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75132 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75132 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75132, 1, 16384⟩
    (by decide) selected_cut_04935

theorem selected_cut_04936 : selected 8 ⟨155123, by decide⟩
    (prefixPartial 13 75133) = some ⟨13, 2, 0, 155123, 75133, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_75133_155123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75133 ⟨155123, by decide⟩ :=
  accepted_of_selected 13 75133 ⟨155123, by decide⟩ ⟨13, 2, 0, 155123, 75133, 1293, 16384⟩
    (by decide) selected_cut_04936

theorem selected_cut_04937 : selected 8 ⟨155148, by decide⟩
    (prefixPartial 13 75134) = some ⟨13, 2, 0, 155148, 75134, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_75134_155148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75134 ⟨155148, by decide⟩ :=
  accepted_of_selected 13 75134 ⟨155148, by decide⟩ ⟨13, 2, 0, 155148, 75134, 1829, 16384⟩
    (by decide) selected_cut_04937

theorem selected_cut_04938 : selected 8 ⟨155158, by decide⟩
    (prefixPartial 13 75135) = some ⟨13, 2, 0, 155158, 75135, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_75135_155158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75135 ⟨155158, by decide⟩ :=
  accepted_of_selected 13 75135 ⟨155158, by decide⟩ ⟨13, 2, 0, 155158, 75135, 1053, 16384⟩
    (by decide) selected_cut_04938

theorem unmarked_context_12_18783_155159 : frontier 9 ⟨155159, by decide⟩
    (prefixCache 12 18783) (prefixPartial 12 18783) = false := by
  decide +kernel

theorem node_context_12_18783_155159 : EJMOriginalGlobalDAGData.nodes 9 ⟨155159, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155123, by decide⟩,⟨155148, by decide⟩,⟨155158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18783_155159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18783 ⟨155159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18783
    ⟨155159, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155123, by decide⟩,⟨155148, by decide⟩,⟨155158, by decide⟩]) unmarked_context_12_18783_155159 node_context_12_18783_155159
  intro a
  fin_cases a
  · exact context_13_75132_3444
  · exact context_13_75133_155123
  · exact context_13_75134_155148
  · exact context_13_75135_155158

theorem unmarked_context_11_4695_155160 : frontier 10 ⟨155160, by decide⟩
    (prefixCache 11 4695) (prefixPartial 11 4695) = false := by
  decide +kernel

theorem node_context_11_4695_155160 : EJMOriginalGlobalDAGData.nodes 10 ⟨155160, by decide⟩ =
    .split (coordinate 11) (![⟨154980, by decide⟩,⟨155053, by decide⟩,⟨155110, by decide⟩,⟨155159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4695_155160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4695 ⟨155160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4695
    ⟨155160, by decide⟩ (by decide) (![⟨154980, by decide⟩,⟨155053, by decide⟩,⟨155110, by decide⟩,⟨155159, by decide⟩]) unmarked_context_11_4695_155160 node_context_11_4695_155160
  intro a
  fin_cases a
  · exact context_12_18780_154980
  · exact context_12_18781_155053
  · exact context_12_18782_155110
  · exact context_12_18783_155159

theorem unmarked_context_10_1173_155161 : frontier 11 ⟨155161, by decide⟩
    (prefixCache 10 1173) (prefixPartial 10 1173) = false := by
  decide +kernel

theorem node_context_10_1173_155161 : EJMOriginalGlobalDAGData.nodes 11 ⟨155161, by decide⟩ =
    .split (coordinate 10) (![⟨154536, by decide⟩,⟨154681, by decide⟩,⟨154928, by decide⟩,⟨155160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1173_155161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1173 ⟨155161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1173
    ⟨155161, by decide⟩ (by decide) (![⟨154536, by decide⟩,⟨154681, by decide⟩,⟨154928, by decide⟩,⟨155160, by decide⟩]) unmarked_context_10_1173_155161 node_context_10_1173_155161
  intro a
  fin_cases a
  · exact context_11_4692_154536
  · exact context_11_4693_154681
  · exact context_11_4694_154928
  · exact context_11_4695_155160

theorem selected_cut_04939 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75136) = some ⟨13, 1, 0, 3444, 75136, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75136_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75136 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75136 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75136, 1, 16384⟩
    (by decide) selected_cut_04939

theorem selected_cut_04940 : selected 8 ⟨155179, by decide⟩
    (prefixPartial 13 75137) = some ⟨13, 2, 0, 155179, 75137, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_75137_155179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75137 ⟨155179, by decide⟩ :=
  accepted_of_selected 13 75137 ⟨155179, by decide⟩ ⟨13, 2, 0, 155179, 75137, 1605, 16384⟩
    (by decide) selected_cut_04940

theorem selected_cut_04941 : selected 8 ⟨155200, by decide⟩
    (prefixPartial 13 75138) = some ⟨13, 2, 0, 155200, 75138, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_75138_155200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75138 ⟨155200, by decide⟩ :=
  accepted_of_selected 13 75138 ⟨155200, by decide⟩ ⟨13, 2, 0, 155200, 75138, 1749, 16384⟩
    (by decide) selected_cut_04941

theorem selected_cut_04942 : selected 8 ⟨155210, by decide⟩
    (prefixPartial 13 75139) = some ⟨13, 2, 0, 155210, 75139, 997, 16384⟩ := by
  decide +kernel

theorem context_13_75139_155210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75139 ⟨155210, by decide⟩ :=
  accepted_of_selected 13 75139 ⟨155210, by decide⟩ ⟨13, 2, 0, 155210, 75139, 997, 16384⟩
    (by decide) selected_cut_04942

theorem unmarked_context_12_18784_155211 : frontier 9 ⟨155211, by decide⟩
    (prefixCache 12 18784) (prefixPartial 12 18784) = false := by
  decide +kernel

theorem node_context_12_18784_155211 : EJMOriginalGlobalDAGData.nodes 9 ⟨155211, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155179, by decide⟩,⟨155200, by decide⟩,⟨155210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18784_155211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18784 ⟨155211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18784
    ⟨155211, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155179, by decide⟩,⟨155200, by decide⟩,⟨155210, by decide⟩]) unmarked_context_12_18784_155211 node_context_12_18784_155211
  intro a
  fin_cases a
  · exact context_13_75136_3444
  · exact context_13_75137_155179
  · exact context_13_75138_155200
  · exact context_13_75139_155210

theorem selected_cut_04943 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75140) = some ⟨13, 1, 0, 3444, 75140, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75140_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75140 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75140 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75140, 1, 16384⟩
    (by decide) selected_cut_04943

theorem selected_cut_04944 : selected 8 ⟨155226, by decide⟩
    (prefixPartial 13 75141) = some ⟨13, 2, 0, 155226, 75141, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_75141_155226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75141 ⟨155226, by decide⟩ :=
  accepted_of_selected 13 75141 ⟨155226, by decide⟩ ⟨13, 2, 0, 155226, 75141, 1509, 16384⟩
    (by decide) selected_cut_04944

theorem selected_cut_04945 : selected 8 ⟨155248, by decide⟩
    (prefixPartial 13 75142) = some ⟨13, 2, 0, 155248, 75142, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_75142_155248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75142 ⟨155248, by decide⟩ :=
  accepted_of_selected 13 75142 ⟨155248, by decide⟩ ⟨13, 2, 0, 155248, 75142, 2165, 16384⟩
    (by decide) selected_cut_04945

theorem selected_cut_04946 : selected 8 ⟨155258, by decide⟩
    (prefixPartial 13 75143) = some ⟨13, 2, 0, 155258, 75143, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_75143_155258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75143 ⟨155258, by decide⟩ :=
  accepted_of_selected 13 75143 ⟨155258, by decide⟩ ⟨13, 2, 0, 155258, 75143, 1109, 16384⟩
    (by decide) selected_cut_04946

theorem unmarked_context_12_18785_155259 : frontier 9 ⟨155259, by decide⟩
    (prefixCache 12 18785) (prefixPartial 12 18785) = false := by
  decide +kernel

theorem node_context_12_18785_155259 : EJMOriginalGlobalDAGData.nodes 9 ⟨155259, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155226, by decide⟩,⟨155248, by decide⟩,⟨155258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18785_155259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18785 ⟨155259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18785
    ⟨155259, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155226, by decide⟩,⟨155248, by decide⟩,⟨155258, by decide⟩]) unmarked_context_12_18785_155259 node_context_12_18785_155259
  intro a
  fin_cases a
  · exact context_13_75140_3444
  · exact context_13_75141_155226
  · exact context_13_75142_155248
  · exact context_13_75143_155258

theorem selected_cut_04947 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75144) = some ⟨13, 1, 0, 3444, 75144, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75144_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75144 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75144 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75144, 1, 16384⟩
    (by decide) selected_cut_04947

theorem selected_cut_04948 : selected 8 ⟨155272, by decide⟩
    (prefixPartial 13 75145) = some ⟨13, 2, 0, 155272, 75145, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_75145_155272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75145 ⟨155272, by decide⟩ :=
  accepted_of_selected 13 75145 ⟨155272, by decide⟩ ⟨13, 2, 0, 155272, 75145, 1281, 16384⟩
    (by decide) selected_cut_04948

theorem selected_cut_04949 : selected 8 ⟨155294, by decide⟩
    (prefixPartial 13 75146) = some ⟨13, 2, 0, 155294, 75146, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_75146_155294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75146 ⟨155294, by decide⟩ :=
  accepted_of_selected 13 75146 ⟨155294, by decide⟩ ⟨13, 2, 0, 155294, 75146, 1845, 16384⟩
    (by decide) selected_cut_04949

theorem selected_cut_04950 : selected 8 ⟨155301, by decide⟩
    (prefixPartial 13 75147) = some ⟨13, 2, 0, 155301, 75147, 989, 16384⟩ := by
  decide +kernel

theorem context_13_75147_155301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75147 ⟨155301, by decide⟩ :=
  accepted_of_selected 13 75147 ⟨155301, by decide⟩ ⟨13, 2, 0, 155301, 75147, 989, 16384⟩
    (by decide) selected_cut_04950

theorem unmarked_context_12_18786_155302 : frontier 9 ⟨155302, by decide⟩
    (prefixCache 12 18786) (prefixPartial 12 18786) = false := by
  decide +kernel

theorem node_context_12_18786_155302 : EJMOriginalGlobalDAGData.nodes 9 ⟨155302, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155272, by decide⟩,⟨155294, by decide⟩,⟨155301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18786_155302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18786 ⟨155302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18786
    ⟨155302, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155272, by decide⟩,⟨155294, by decide⟩,⟨155301, by decide⟩]) unmarked_context_12_18786_155302 node_context_12_18786_155302
  intro a
  fin_cases a
  · exact context_13_75144_3444
  · exact context_13_75145_155272
  · exact context_13_75146_155294
  · exact context_13_75147_155301

theorem selected_cut_04951 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75148) = some ⟨13, 1, 0, 3444, 75148, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75148_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75148 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75148 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75148, 1, 16384⟩
    (by decide) selected_cut_04951

theorem selected_cut_04952 : selected 8 ⟨155316, by decide⟩
    (prefixPartial 13 75149) = some ⟨13, 2, 0, 155316, 75149, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_75149_155316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75149 ⟨155316, by decide⟩ :=
  accepted_of_selected 13 75149 ⟨155316, by decide⟩ ⟨13, 2, 0, 155316, 75149, 1261, 16384⟩
    (by decide) selected_cut_04952

theorem selected_cut_04953 : selected 8 ⟨155341, by decide⟩
    (prefixPartial 13 75150) = some ⟨13, 2, 0, 155341, 75150, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_75150_155341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75150 ⟨155341, by decide⟩ :=
  accepted_of_selected 13 75150 ⟨155341, by decide⟩ ⟨13, 2, 0, 155341, 75150, 2077, 16384⟩
    (by decide) selected_cut_04953

theorem selected_cut_04954 : selected 8 ⟨155346, by decide⟩
    (prefixPartial 13 75151) = some ⟨13, 2, 0, 155346, 75151, 945, 16384⟩ := by
  decide +kernel

theorem context_13_75151_155346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75151 ⟨155346, by decide⟩ :=
  accepted_of_selected 13 75151 ⟨155346, by decide⟩ ⟨13, 2, 0, 155346, 75151, 945, 16384⟩
    (by decide) selected_cut_04954

theorem unmarked_context_12_18787_155347 : frontier 9 ⟨155347, by decide⟩
    (prefixCache 12 18787) (prefixPartial 12 18787) = false := by
  decide +kernel

theorem node_context_12_18787_155347 : EJMOriginalGlobalDAGData.nodes 9 ⟨155347, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155316, by decide⟩,⟨155341, by decide⟩,⟨155346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18787_155347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18787 ⟨155347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18787
    ⟨155347, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155316, by decide⟩,⟨155341, by decide⟩,⟨155346, by decide⟩]) unmarked_context_12_18787_155347 node_context_12_18787_155347
  intro a
  fin_cases a
  · exact context_13_75148_3444
  · exact context_13_75149_155316
  · exact context_13_75150_155341
  · exact context_13_75151_155346

theorem unmarked_context_11_4696_155348 : frontier 10 ⟨155348, by decide⟩
    (prefixCache 11 4696) (prefixPartial 11 4696) = false := by
  decide +kernel

theorem node_context_11_4696_155348 : EJMOriginalGlobalDAGData.nodes 10 ⟨155348, by decide⟩ =
    .split (coordinate 11) (![⟨155211, by decide⟩,⟨155259, by decide⟩,⟨155302, by decide⟩,⟨155347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4696_155348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4696 ⟨155348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4696
    ⟨155348, by decide⟩ (by decide) (![⟨155211, by decide⟩,⟨155259, by decide⟩,⟨155302, by decide⟩,⟨155347, by decide⟩]) unmarked_context_11_4696_155348 node_context_11_4696_155348
  intro a
  fin_cases a
  · exact context_12_18784_155211
  · exact context_12_18785_155259
  · exact context_12_18786_155302
  · exact context_12_18787_155347

theorem selected_cut_04955 : selected 9 ⟨155388, by decide⟩
    (prefixPartial 12 18788) = some ⟨12, 2, 0, 155388, 18788, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_18788_155388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18788 ⟨155388, by decide⟩ :=
  accepted_of_selected 12 18788 ⟨155388, by decide⟩ ⟨12, 2, 0, 155388, 18788, 3721, 65536⟩
    (by decide) selected_cut_04955

theorem selected_cut_04956 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 18789) = some ⟨12, 1, 0, 126884, 18789, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18789_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18789 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 18789 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 18789, 1, 65536⟩
    (by decide) selected_cut_04956

theorem selected_cut_04957 : selected 9 ⟨155432, by decide⟩
    (prefixPartial 12 18790) = some ⟨12, 2, 0, 155432, 18790, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_18790_155432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18790 ⟨155432, by decide⟩ :=
  accepted_of_selected 12 18790 ⟨155432, by decide⟩ ⟨12, 2, 0, 155432, 18790, 3941, 65536⟩
    (by decide) selected_cut_04957

theorem selected_cut_04958 : selected 9 ⟨155476, by decide⟩
    (prefixPartial 12 18791) = some ⟨12, 2, 0, 155476, 18791, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_18791_155476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18791 ⟨155476, by decide⟩ :=
  accepted_of_selected 12 18791 ⟨155476, by decide⟩ ⟨12, 2, 0, 155476, 18791, 4061, 65536⟩
    (by decide) selected_cut_04958

theorem unmarked_context_11_4697_155477 : frontier 10 ⟨155477, by decide⟩
    (prefixCache 11 4697) (prefixPartial 11 4697) = false := by
  decide +kernel

theorem node_context_11_4697_155477 : EJMOriginalGlobalDAGData.nodes 10 ⟨155477, by decide⟩ =
    .split (coordinate 11) (![⟨155388, by decide⟩,⟨126884, by decide⟩,⟨155432, by decide⟩,⟨155476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4697_155477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4697 ⟨155477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4697
    ⟨155477, by decide⟩ (by decide) (![⟨155388, by decide⟩,⟨126884, by decide⟩,⟨155432, by decide⟩,⟨155476, by decide⟩]) unmarked_context_11_4697_155477 node_context_11_4697_155477
  intro a
  fin_cases a
  · exact context_12_18788_155388
  · exact context_12_18789_126884
  · exact context_12_18790_155432
  · exact context_12_18791_155476

theorem selected_cut_04959 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75168) = some ⟨13, 1, 0, 3444, 75168, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75168_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75168 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75168 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75168, 1, 16384⟩
    (by decide) selected_cut_04959

theorem selected_cut_04960 : selected 8 ⟨155517, by decide⟩
    (prefixPartial 13 75169) = some ⟨13, 2, 0, 155517, 75169, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_75169_155517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75169 ⟨155517, by decide⟩ :=
  accepted_of_selected 13 75169 ⟨155517, by decide⟩ ⟨13, 2, 0, 155517, 75169, 1589, 16384⟩
    (by decide) selected_cut_04960

theorem selected_cut_04961 : selected 8 ⟨155548, by decide⟩
    (prefixPartial 13 75170) = some ⟨13, 2, 0, 155548, 75170, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_75170_155548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75170 ⟨155548, by decide⟩ :=
  accepted_of_selected 13 75170 ⟨155548, by decide⟩ ⟨13, 2, 0, 155548, 75170, 2449, 16384⟩
    (by decide) selected_cut_04961

theorem selected_cut_04962 : selected 8 ⟨155559, by decide⟩
    (prefixPartial 13 75171) = some ⟨13, 2, 0, 155559, 75171, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_75171_155559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75171 ⟨155559, by decide⟩ :=
  accepted_of_selected 13 75171 ⟨155559, by decide⟩ ⟨13, 2, 0, 155559, 75171, 1173, 16384⟩
    (by decide) selected_cut_04962

theorem unmarked_context_12_18792_155560 : frontier 9 ⟨155560, by decide⟩
    (prefixCache 12 18792) (prefixPartial 12 18792) = false := by
  decide +kernel

theorem node_context_12_18792_155560 : EJMOriginalGlobalDAGData.nodes 9 ⟨155560, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155517, by decide⟩,⟨155548, by decide⟩,⟨155559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18792_155560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18792 ⟨155560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18792
    ⟨155560, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155517, by decide⟩,⟨155548, by decide⟩,⟨155559, by decide⟩]) unmarked_context_12_18792_155560 node_context_12_18792_155560
  intro a
  fin_cases a
  · exact context_13_75168_3444
  · exact context_13_75169_155517
  · exact context_13_75170_155548
  · exact context_13_75171_155559

theorem selected_cut_04963 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75172) = some ⟨13, 1, 0, 3444, 75172, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75172_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75172 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75172 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75172, 1, 16384⟩
    (by decide) selected_cut_04963

theorem selected_cut_04964 : selected 8 ⟨155591, by decide⟩
    (prefixPartial 13 75173) = some ⟨13, 2, 0, 155591, 75173, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_75173_155591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75173 ⟨155591, by decide⟩ :=
  accepted_of_selected 13 75173 ⟨155591, by decide⟩ ⟨13, 2, 0, 155591, 75173, 1521, 16384⟩
    (by decide) selected_cut_04964

theorem selected_cut_04965 : selected 8 ⟨155670, by decide⟩
    (prefixPartial 13 75174) = some ⟨13, 2, 0, 155670, 75174, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_75174_155670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75174 ⟨155670, by decide⟩ :=
  accepted_of_selected 13 75174 ⟨155670, by decide⟩ ⟨13, 2, 0, 155670, 75174, 3229, 16384⟩
    (by decide) selected_cut_04965

theorem selected_cut_04966 : selected 8 ⟨155692, by decide⟩
    (prefixPartial 13 75175) = some ⟨13, 2, 0, 155692, 75175, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_75175_155692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75175 ⟨155692, by decide⟩ :=
  accepted_of_selected 13 75175 ⟨155692, by decide⟩ ⟨13, 2, 0, 155692, 75175, 1449, 16384⟩
    (by decide) selected_cut_04966

theorem unmarked_context_12_18793_155693 : frontier 9 ⟨155693, by decide⟩
    (prefixCache 12 18793) (prefixPartial 12 18793) = false := by
  decide +kernel

theorem node_context_12_18793_155693 : EJMOriginalGlobalDAGData.nodes 9 ⟨155693, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155591, by decide⟩,⟨155670, by decide⟩,⟨155692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18793_155693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18793 ⟨155693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18793
    ⟨155693, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155591, by decide⟩,⟨155670, by decide⟩,⟨155692, by decide⟩]) unmarked_context_12_18793_155693 node_context_12_18793_155693
  intro a
  fin_cases a
  · exact context_13_75172_3444
  · exact context_13_75173_155591
  · exact context_13_75174_155670
  · exact context_13_75175_155692

theorem selected_cut_04967 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75176) = some ⟨13, 1, 0, 3444, 75176, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75176_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75176 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75176 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75176, 1, 16384⟩
    (by decide) selected_cut_04967

theorem selected_cut_04968 : selected 8 ⟨155709, by decide⟩
    (prefixPartial 13 75177) = some ⟨13, 2, 0, 155709, 75177, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_75177_155709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75177 ⟨155709, by decide⟩ :=
  accepted_of_selected 13 75177 ⟨155709, by decide⟩ ⟨13, 2, 0, 155709, 75177, 1153, 16384⟩
    (by decide) selected_cut_04968

theorem selected_cut_04969 : selected 8 ⟨155744, by decide⟩
    (prefixPartial 13 75178) = some ⟨13, 2, 0, 155744, 75178, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_75178_155744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75178 ⟨155744, by decide⟩ :=
  accepted_of_selected 13 75178 ⟨155744, by decide⟩ ⟨13, 2, 0, 155744, 75178, 2473, 16384⟩
    (by decide) selected_cut_04969

theorem selected_cut_04970 : selected 8 ⟨155755, by decide⟩
    (prefixPartial 13 75179) = some ⟨13, 2, 0, 155755, 75179, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_75179_155755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75179 ⟨155755, by decide⟩ :=
  accepted_of_selected 13 75179 ⟨155755, by decide⟩ ⟨13, 2, 0, 155755, 75179, 1141, 16384⟩
    (by decide) selected_cut_04970

theorem unmarked_context_12_18794_155756 : frontier 9 ⟨155756, by decide⟩
    (prefixCache 12 18794) (prefixPartial 12 18794) = false := by
  decide +kernel

theorem node_context_12_18794_155756 : EJMOriginalGlobalDAGData.nodes 9 ⟨155756, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155709, by decide⟩,⟨155744, by decide⟩,⟨155755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18794_155756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18794 ⟨155756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18794
    ⟨155756, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155709, by decide⟩,⟨155744, by decide⟩,⟨155755, by decide⟩]) unmarked_context_12_18794_155756 node_context_12_18794_155756
  intro a
  fin_cases a
  · exact context_13_75176_3444
  · exact context_13_75177_155709
  · exact context_13_75178_155744
  · exact context_13_75179_155755

theorem selected_cut_04971 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75180) = some ⟨13, 1, 0, 3444, 75180, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75180_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75180 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75180 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75180, 1, 16384⟩
    (by decide) selected_cut_04971

theorem selected_cut_04972 : selected 8 ⟨155778, by decide⟩
    (prefixPartial 13 75181) = some ⟨13, 2, 0, 155778, 75181, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_75181_155778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75181 ⟨155778, by decide⟩ :=
  accepted_of_selected 13 75181 ⟨155778, by decide⟩ ⟨13, 2, 0, 155778, 75181, 1297, 16384⟩
    (by decide) selected_cut_04972

theorem selected_cut_04973 : selected 8 ⟨155830, by decide⟩
    (prefixPartial 13 75182) = some ⟨13, 2, 0, 155830, 75182, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_75182_155830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75182 ⟨155830, by decide⟩ :=
  accepted_of_selected 13 75182 ⟨155830, by decide⟩ ⟨13, 2, 0, 155830, 75182, 3001, 16384⟩
    (by decide) selected_cut_04973

theorem selected_cut_04974 : selected 8 ⟨155841, by decide⟩
    (prefixPartial 13 75183) = some ⟨13, 2, 0, 155841, 75183, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_75183_155841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75183 ⟨155841, by decide⟩ :=
  accepted_of_selected 13 75183 ⟨155841, by decide⟩ ⟨13, 2, 0, 155841, 75183, 1225, 16384⟩
    (by decide) selected_cut_04974

theorem unmarked_context_12_18795_155842 : frontier 9 ⟨155842, by decide⟩
    (prefixCache 12 18795) (prefixPartial 12 18795) = false := by
  decide +kernel

theorem node_context_12_18795_155842 : EJMOriginalGlobalDAGData.nodes 9 ⟨155842, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155778, by decide⟩,⟨155830, by decide⟩,⟨155841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18795_155842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18795 ⟨155842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18795
    ⟨155842, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155778, by decide⟩,⟨155830, by decide⟩,⟨155841, by decide⟩]) unmarked_context_12_18795_155842 node_context_12_18795_155842
  intro a
  fin_cases a
  · exact context_13_75180_3444
  · exact context_13_75181_155778
  · exact context_13_75182_155830
  · exact context_13_75183_155841

theorem unmarked_context_11_4698_155843 : frontier 10 ⟨155843, by decide⟩
    (prefixCache 11 4698) (prefixPartial 11 4698) = false := by
  decide +kernel

theorem node_context_11_4698_155843 : EJMOriginalGlobalDAGData.nodes 10 ⟨155843, by decide⟩ =
    .split (coordinate 11) (![⟨155560, by decide⟩,⟨155693, by decide⟩,⟨155756, by decide⟩,⟨155842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4698_155843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4698 ⟨155843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4698
    ⟨155843, by decide⟩ (by decide) (![⟨155560, by decide⟩,⟨155693, by decide⟩,⟨155756, by decide⟩,⟨155842, by decide⟩]) unmarked_context_11_4698_155843 node_context_11_4698_155843
  intro a
  fin_cases a
  · exact context_12_18792_155560
  · exact context_12_18793_155693
  · exact context_12_18794_155756
  · exact context_12_18795_155842

theorem selected_cut_04975 : selected 9 ⟨155883, by decide⟩
    (prefixPartial 12 18796) = some ⟨12, 2, 0, 155883, 18796, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_18796_155883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18796 ⟨155883, by decide⟩ :=
  accepted_of_selected 12 18796 ⟨155883, by decide⟩ ⟨12, 2, 0, 155883, 18796, 4073, 65536⟩
    (by decide) selected_cut_04975

theorem selected_cut_04976 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75188) = some ⟨13, 1, 0, 3444, 75188, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75188_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75188 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75188 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75188, 1, 16384⟩
    (by decide) selected_cut_04976

theorem selected_cut_04977 : selected 8 ⟨155892, by decide⟩
    (prefixPartial 13 75189) = some ⟨13, 2, 0, 155892, 75189, 941, 16384⟩ := by
  decide +kernel

theorem context_13_75189_155892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75189 ⟨155892, by decide⟩ :=
  accepted_of_selected 13 75189 ⟨155892, by decide⟩ ⟨13, 2, 0, 155892, 75189, 941, 16384⟩
    (by decide) selected_cut_04977

theorem selected_cut_04978 : selected 8 ⟨155924, by decide⟩
    (prefixPartial 13 75190) = some ⟨13, 2, 0, 155924, 75190, 2641, 16384⟩ := by
  decide +kernel

theorem context_13_75190_155924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75190 ⟨155924, by decide⟩ :=
  accepted_of_selected 13 75190 ⟨155924, by decide⟩ ⟨13, 2, 0, 155924, 75190, 2641, 16384⟩
    (by decide) selected_cut_04978

theorem selected_cut_04979 : selected 8 ⟨155936, by decide⟩
    (prefixPartial 13 75191) = some ⟨13, 2, 0, 155936, 75191, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_75191_155936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75191 ⟨155936, by decide⟩ :=
  accepted_of_selected 13 75191 ⟨155936, by decide⟩ ⟨13, 2, 0, 155936, 75191, 1297, 16384⟩
    (by decide) selected_cut_04979

theorem unmarked_context_12_18797_155937 : frontier 9 ⟨155937, by decide⟩
    (prefixCache 12 18797) (prefixPartial 12 18797) = false := by
  decide +kernel

theorem node_context_12_18797_155937 : EJMOriginalGlobalDAGData.nodes 9 ⟨155937, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155892, by decide⟩,⟨155924, by decide⟩,⟨155936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18797_155937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18797 ⟨155937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18797
    ⟨155937, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155892, by decide⟩,⟨155924, by decide⟩,⟨155936, by decide⟩]) unmarked_context_12_18797_155937 node_context_12_18797_155937
  intro a
  fin_cases a
  · exact context_13_75188_3444
  · exact context_13_75189_155892
  · exact context_13_75190_155924
  · exact context_13_75191_155936

theorem selected_cut_04980 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75192) = some ⟨13, 1, 0, 3444, 75192, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75192_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75192 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75192 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75192, 1, 16384⟩
    (by decide) selected_cut_04980

theorem selected_cut_04981 : selected 8 ⟨155945, by decide⟩
    (prefixPartial 13 75193) = some ⟨13, 2, 0, 155945, 75193, 833, 16384⟩ := by
  decide +kernel

theorem context_13_75193_155945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75193 ⟨155945, by decide⟩ :=
  accepted_of_selected 13 75193 ⟨155945, by decide⟩ ⟨13, 2, 0, 155945, 75193, 833, 16384⟩
    (by decide) selected_cut_04981

theorem selected_cut_04982 : selected 8 ⟨155969, by decide⟩
    (prefixPartial 13 75194) = some ⟨13, 2, 0, 155969, 75194, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_75194_155969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75194 ⟨155969, by decide⟩ :=
  accepted_of_selected 13 75194 ⟨155969, by decide⟩ ⟨13, 2, 0, 155969, 75194, 2253, 16384⟩
    (by decide) selected_cut_04982

theorem selected_cut_04983 : selected 8 ⟨155978, by decide⟩
    (prefixPartial 13 75195) = some ⟨13, 2, 0, 155978, 75195, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_75195_155978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75195 ⟨155978, by decide⟩ :=
  accepted_of_selected 13 75195 ⟨155978, by decide⟩ ⟨13, 2, 0, 155978, 75195, 1173, 16384⟩
    (by decide) selected_cut_04983

theorem unmarked_context_12_18798_155979 : frontier 9 ⟨155979, by decide⟩
    (prefixCache 12 18798) (prefixPartial 12 18798) = false := by
  decide +kernel

theorem node_context_12_18798_155979 : EJMOriginalGlobalDAGData.nodes 9 ⟨155979, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨155945, by decide⟩,⟨155969, by decide⟩,⟨155978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18798_155979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18798 ⟨155979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18798
    ⟨155979, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨155945, by decide⟩,⟨155969, by decide⟩,⟨155978, by decide⟩]) unmarked_context_12_18798_155979 node_context_12_18798_155979
  intro a
  fin_cases a
  · exact context_13_75192_3444
  · exact context_13_75193_155945
  · exact context_13_75194_155969
  · exact context_13_75195_155978

theorem selected_cut_04984 : selected 9 ⟨156018, by decide⟩
    (prefixPartial 12 18799) = some ⟨12, 2, 0, 156018, 18799, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_18799_156018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18799 ⟨156018, by decide⟩ :=
  accepted_of_selected 12 18799 ⟨156018, by decide⟩ ⟨12, 2, 0, 156018, 18799, 3989, 65536⟩
    (by decide) selected_cut_04984

theorem unmarked_context_11_4699_156019 : frontier 10 ⟨156019, by decide⟩
    (prefixCache 11 4699) (prefixPartial 11 4699) = false := by
  decide +kernel

theorem node_context_11_4699_156019 : EJMOriginalGlobalDAGData.nodes 10 ⟨156019, by decide⟩ =
    .split (coordinate 11) (![⟨155883, by decide⟩,⟨155937, by decide⟩,⟨155979, by decide⟩,⟨156018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4699_156019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4699 ⟨156019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4699
    ⟨156019, by decide⟩ (by decide) (![⟨155883, by decide⟩,⟨155937, by decide⟩,⟨155979, by decide⟩,⟨156018, by decide⟩]) unmarked_context_11_4699_156019 node_context_11_4699_156019
  intro a
  fin_cases a
  · exact context_12_18796_155883
  · exact context_12_18797_155937
  · exact context_12_18798_155979
  · exact context_12_18799_156018

theorem unmarked_context_10_1174_156020 : frontier 11 ⟨156020, by decide⟩
    (prefixCache 10 1174) (prefixPartial 10 1174) = false := by
  decide +kernel

theorem node_context_10_1174_156020 : EJMOriginalGlobalDAGData.nodes 11 ⟨156020, by decide⟩ =
    .split (coordinate 10) (![⟨155348, by decide⟩,⟨155477, by decide⟩,⟨155843, by decide⟩,⟨156019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1174_156020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1174 ⟨156020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1174
    ⟨156020, by decide⟩ (by decide) (![⟨155348, by decide⟩,⟨155477, by decide⟩,⟨155843, by decide⟩,⟨156019, by decide⟩]) unmarked_context_10_1174_156020 node_context_10_1174_156020
  intro a
  fin_cases a
  · exact context_11_4696_155348
  · exact context_11_4697_155477
  · exact context_11_4698_155843
  · exact context_11_4699_156019

theorem selected_cut_04985 : selected 9 ⟨156061, by decide⟩
    (prefixPartial 12 18800) = some ⟨12, 2, 0, 156061, 18800, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_18800_156061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18800 ⟨156061, by decide⟩ :=
  accepted_of_selected 12 18800 ⟨156061, by decide⟩ ⟨12, 2, 0, 156061, 18800, 3813, 65536⟩
    (by decide) selected_cut_04985

theorem selected_cut_04986 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75204) = some ⟨13, 1, 0, 3444, 75204, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75204_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75204 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75204 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75204, 1, 16384⟩
    (by decide) selected_cut_04986

theorem selected_cut_04987 : selected 8 ⟨156071, by decide⟩
    (prefixPartial 13 75205) = some ⟨13, 2, 0, 156071, 75205, 705, 16384⟩ := by
  decide +kernel

theorem context_13_75205_156071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75205 ⟨156071, by decide⟩ :=
  accepted_of_selected 13 75205 ⟨156071, by decide⟩ ⟨13, 2, 0, 156071, 75205, 705, 16384⟩
    (by decide) selected_cut_04987

theorem selected_cut_04988 : selected 8 ⟨156097, by decide⟩
    (prefixPartial 13 75206) = some ⟨13, 2, 0, 156097, 75206, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_75206_156097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75206 ⟨156097, by decide⟩ :=
  accepted_of_selected 13 75206 ⟨156097, by decide⟩ ⟨13, 2, 0, 156097, 75206, 2485, 16384⟩
    (by decide) selected_cut_04988

theorem selected_cut_04989 : selected 8 ⟨156111, by decide⟩
    (prefixPartial 13 75207) = some ⟨13, 2, 0, 156111, 75207, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_75207_156111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75207 ⟨156111, by decide⟩ :=
  accepted_of_selected 13 75207 ⟨156111, by decide⟩ ⟨13, 2, 0, 156111, 75207, 1205, 16384⟩
    (by decide) selected_cut_04989

theorem unmarked_context_12_18801_156112 : frontier 9 ⟨156112, by decide⟩
    (prefixCache 12 18801) (prefixPartial 12 18801) = false := by
  decide +kernel

theorem node_context_12_18801_156112 : EJMOriginalGlobalDAGData.nodes 9 ⟨156112, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨156071, by decide⟩,⟨156097, by decide⟩,⟨156111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18801_156112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18801 ⟨156112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18801
    ⟨156112, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨156071, by decide⟩,⟨156097, by decide⟩,⟨156111, by decide⟩]) unmarked_context_12_18801_156112 node_context_12_18801_156112
  intro a
  fin_cases a
  · exact context_13_75204_3444
  · exact context_13_75205_156071
  · exact context_13_75206_156097
  · exact context_13_75207_156111

theorem selected_cut_04990 : selected 9 ⟨156155, by decide⟩
    (prefixPartial 12 18802) = some ⟨12, 2, 0, 156155, 18802, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_18802_156155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18802 ⟨156155, by decide⟩ :=
  accepted_of_selected 12 18802 ⟨156155, by decide⟩ ⟨12, 2, 0, 156155, 18802, 3817, 65536⟩
    (by decide) selected_cut_04990

theorem selected_cut_04991 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75212) = some ⟨13, 1, 0, 3444, 75212, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75212_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75212 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75212 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75212, 1, 16384⟩
    (by decide) selected_cut_04991

theorem selected_cut_04992 : selected 8 ⟨156166, by decide⟩
    (prefixPartial 13 75213) = some ⟨13, 2, 0, 156166, 75213, 641, 16384⟩ := by
  decide +kernel

theorem context_13_75213_156166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75213 ⟨156166, by decide⟩ :=
  accepted_of_selected 13 75213 ⟨156166, by decide⟩ ⟨13, 2, 0, 156166, 75213, 641, 16384⟩
    (by decide) selected_cut_04992

theorem selected_cut_04993 : selected 8 ⟨156197, by decide⟩
    (prefixPartial 13 75214) = some ⟨13, 2, 0, 156197, 75214, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_75214_156197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75214 ⟨156197, by decide⟩ :=
  accepted_of_selected 13 75214 ⟨156197, by decide⟩ ⟨13, 2, 0, 156197, 75214, 2493, 16384⟩
    (by decide) selected_cut_04993

theorem selected_cut_04994 : selected 8 ⟨156205, by decide⟩
    (prefixPartial 13 75215) = some ⟨13, 2, 0, 156205, 75215, 973, 16384⟩ := by
  decide +kernel

theorem context_13_75215_156205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75215 ⟨156205, by decide⟩ :=
  accepted_of_selected 13 75215 ⟨156205, by decide⟩ ⟨13, 2, 0, 156205, 75215, 973, 16384⟩
    (by decide) selected_cut_04994

theorem unmarked_context_12_18803_156206 : frontier 9 ⟨156206, by decide⟩
    (prefixCache 12 18803) (prefixPartial 12 18803) = false := by
  decide +kernel

theorem node_context_12_18803_156206 : EJMOriginalGlobalDAGData.nodes 9 ⟨156206, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨156166, by decide⟩,⟨156197, by decide⟩,⟨156205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18803_156206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18803 ⟨156206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18803
    ⟨156206, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨156166, by decide⟩,⟨156197, by decide⟩,⟨156205, by decide⟩]) unmarked_context_12_18803_156206 node_context_12_18803_156206
  intro a
  fin_cases a
  · exact context_13_75212_3444
  · exact context_13_75213_156166
  · exact context_13_75214_156197
  · exact context_13_75215_156205

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
