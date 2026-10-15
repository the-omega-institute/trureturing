/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover256
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_24675 : selected 8 ⟨623770, by decide⟩
    (prefixPartial 13 309396) = some ⟨13, 2, 0, 623770, 309396, 965, 16384⟩ := by
  decide +kernel

theorem context_13_309396_623770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309396 ⟨623770, by decide⟩ :=
  accepted_of_selected 13 309396 ⟨623770, by decide⟩ ⟨13, 2, 0, 623770, 309396, 965, 16384⟩
    (by decide) selected_cut_24675

theorem selected_cut_24676 : selected 8 ⟨623801, by decide⟩
    (prefixPartial 13 309397) = some ⟨13, 2, 0, 623801, 309397, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_309397_623801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309397 ⟨623801, by decide⟩ :=
  accepted_of_selected 13 309397 ⟨623801, by decide⟩ ⟨13, 2, 0, 623801, 309397, 2181, 16384⟩
    (by decide) selected_cut_24676

theorem selected_cut_24677 : selected 8 ⟨623828, by decide⟩
    (prefixPartial 13 309398) = some ⟨13, 2, 0, 623828, 309398, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_309398_623828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309398 ⟨623828, by decide⟩ :=
  accepted_of_selected 13 309398 ⟨623828, by decide⟩ ⟨13, 2, 0, 623828, 309398, 1749, 16384⟩
    (by decide) selected_cut_24677

theorem selected_cut_24678 : selected 8 ⟨623840, by decide⟩
    (prefixPartial 13 309399) = some ⟨13, 2, 0, 623840, 309399, 925, 16384⟩ := by
  decide +kernel

theorem context_13_309399_623840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309399 ⟨623840, by decide⟩ :=
  accepted_of_selected 13 309399 ⟨623840, by decide⟩ ⟨13, 2, 0, 623840, 309399, 925, 16384⟩
    (by decide) selected_cut_24678

theorem unmarked_context_12_77349_623841 : frontier 9 ⟨623841, by decide⟩
    (prefixCache 12 77349) (prefixPartial 12 77349) = false := by
  decide +kernel

theorem node_context_12_77349_623841 : EJMOriginalGlobalDAGData.nodes 9 ⟨623841, by decide⟩ =
    .split (coordinate 12) (![⟨623770, by decide⟩,⟨623801, by decide⟩,⟨623828, by decide⟩,⟨623840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77349_623841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77349 ⟨623841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77349
    ⟨623841, by decide⟩ (by decide) (![⟨623770, by decide⟩,⟨623801, by decide⟩,⟨623828, by decide⟩,⟨623840, by decide⟩]) unmarked_context_12_77349_623841 node_context_12_77349_623841
  intro a
  fin_cases a
  · exact context_13_309396_623770
  · exact context_13_309397_623801
  · exact context_13_309398_623828
  · exact context_13_309399_623840

theorem selected_cut_24679 : selected 8 ⟨623859, by decide⟩
    (prefixPartial 13 309400) = some ⟨13, 2, 0, 623859, 309400, 721, 16384⟩ := by
  decide +kernel

theorem context_13_309400_623859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309400 ⟨623859, by decide⟩ :=
  accepted_of_selected 13 309400 ⟨623859, by decide⟩ ⟨13, 2, 0, 623859, 309400, 721, 16384⟩
    (by decide) selected_cut_24679

theorem selected_cut_24680 : selected 8 ⟨623886, by decide⟩
    (prefixPartial 13 309401) = some ⟨13, 2, 0, 623886, 309401, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_309401_623886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309401 ⟨623886, by decide⟩ :=
  accepted_of_selected 13 309401 ⟨623886, by decide⟩ ⟨13, 2, 0, 623886, 309401, 1661, 16384⟩
    (by decide) selected_cut_24680

theorem selected_cut_24681 : selected 8 ⟨623907, by decide⟩
    (prefixPartial 13 309402) = some ⟨13, 2, 0, 623907, 309402, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_309402_623907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309402 ⟨623907, by decide⟩ :=
  accepted_of_selected 13 309402 ⟨623907, by decide⟩ ⟨13, 2, 0, 623907, 309402, 1349, 16384⟩
    (by decide) selected_cut_24681

theorem selected_cut_24682 : selected 8 ⟨623918, by decide⟩
    (prefixPartial 13 309403) = some ⟨13, 2, 0, 623918, 309403, 893, 16384⟩ := by
  decide +kernel

theorem context_13_309403_623918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309403 ⟨623918, by decide⟩ :=
  accepted_of_selected 13 309403 ⟨623918, by decide⟩ ⟨13, 2, 0, 623918, 309403, 893, 16384⟩
    (by decide) selected_cut_24682

theorem unmarked_context_12_77350_623919 : frontier 9 ⟨623919, by decide⟩
    (prefixCache 12 77350) (prefixPartial 12 77350) = false := by
  decide +kernel

theorem node_context_12_77350_623919 : EJMOriginalGlobalDAGData.nodes 9 ⟨623919, by decide⟩ =
    .split (coordinate 12) (![⟨623859, by decide⟩,⟨623886, by decide⟩,⟨623907, by decide⟩,⟨623918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77350_623919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77350 ⟨623919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77350
    ⟨623919, by decide⟩ (by decide) (![⟨623859, by decide⟩,⟨623886, by decide⟩,⟨623907, by decide⟩,⟨623918, by decide⟩]) unmarked_context_12_77350_623919 node_context_12_77350_623919
  intro a
  fin_cases a
  · exact context_13_309400_623859
  · exact context_13_309401_623886
  · exact context_13_309402_623907
  · exact context_13_309403_623918

theorem selected_cut_24683 : selected 8 ⟨623936, by decide⟩
    (prefixPartial 13 309404) = some ⟨13, 2, 0, 623936, 309404, 973, 16384⟩ := by
  decide +kernel

theorem context_13_309404_623936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309404 ⟨623936, by decide⟩ :=
  accepted_of_selected 13 309404 ⟨623936, by decide⟩ ⟨13, 2, 0, 623936, 309404, 973, 16384⟩
    (by decide) selected_cut_24683

theorem selected_cut_24684 : selected 8 ⟨623962, by decide⟩
    (prefixPartial 13 309405) = some ⟨13, 2, 0, 623962, 309405, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_309405_623962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309405 ⟨623962, by decide⟩ :=
  accepted_of_selected 13 309405 ⟨623962, by decide⟩ ⟨13, 2, 0, 623962, 309405, 2249, 16384⟩
    (by decide) selected_cut_24684

theorem selected_cut_24685 : selected 8 ⟨623990, by decide⟩
    (prefixPartial 13 309406) = some ⟨13, 2, 0, 623990, 309406, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_309406_623990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309406 ⟨623990, by decide⟩ :=
  accepted_of_selected 13 309406 ⟨623990, by decide⟩ ⟨13, 2, 0, 623990, 309406, 1857, 16384⟩
    (by decide) selected_cut_24685

theorem selected_cut_24686 : selected 8 ⟨624007, by decide⟩
    (prefixPartial 13 309407) = some ⟨13, 2, 0, 624007, 309407, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_309407_624007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309407 ⟨624007, by decide⟩ :=
  accepted_of_selected 13 309407 ⟨624007, by decide⟩ ⟨13, 2, 0, 624007, 309407, 1057, 16384⟩
    (by decide) selected_cut_24686

theorem unmarked_context_12_77351_624008 : frontier 9 ⟨624008, by decide⟩
    (prefixCache 12 77351) (prefixPartial 12 77351) = false := by
  decide +kernel

theorem node_context_12_77351_624008 : EJMOriginalGlobalDAGData.nodes 9 ⟨624008, by decide⟩ =
    .split (coordinate 12) (![⟨623936, by decide⟩,⟨623962, by decide⟩,⟨623990, by decide⟩,⟨624007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77351_624008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77351 ⟨624008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77351
    ⟨624008, by decide⟩ (by decide) (![⟨623936, by decide⟩,⟨623962, by decide⟩,⟨623990, by decide⟩,⟨624007, by decide⟩]) unmarked_context_12_77351_624008 node_context_12_77351_624008
  intro a
  fin_cases a
  · exact context_13_309404_623936
  · exact context_13_309405_623962
  · exact context_13_309406_623990
  · exact context_13_309407_624007

theorem unmarked_context_11_19337_624009 : frontier 10 ⟨624009, by decide⟩
    (prefixCache 11 19337) (prefixPartial 11 19337) = false := by
  decide +kernel

theorem node_context_11_19337_624009 : EJMOriginalGlobalDAGData.nodes 10 ⟨624009, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨623841, by decide⟩,⟨623919, by decide⟩,⟨624008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19337_624009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19337 ⟨624009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19337
    ⟨624009, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨623841, by decide⟩,⟨623919, by decide⟩,⟨624008, by decide⟩]) unmarked_context_11_19337_624009 node_context_11_19337_624009
  intro a
  fin_cases a
  · exact context_12_77348_450498
  · exact context_12_77349_623841
  · exact context_12_77350_623919
  · exact context_12_77351_624008

theorem selected_cut_24687 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 77352) = some ⟨12, 1, 0, 435790, 77352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77352_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77352 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 77352 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 77352, 1, 65536⟩
    (by decide) selected_cut_24687

theorem selected_cut_24688 : selected 8 ⟨624024, by decide⟩
    (prefixPartial 13 309412) = some ⟨13, 2, 0, 624024, 309412, 857, 16384⟩ := by
  decide +kernel

theorem context_13_309412_624024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309412 ⟨624024, by decide⟩ :=
  accepted_of_selected 13 309412 ⟨624024, by decide⟩ ⟨13, 2, 0, 624024, 309412, 857, 16384⟩
    (by decide) selected_cut_24688

theorem selected_cut_24689 : selected 8 ⟨624053, by decide⟩
    (prefixPartial 13 309413) = some ⟨13, 2, 0, 624053, 309413, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_309413_624053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309413 ⟨624053, by decide⟩ :=
  accepted_of_selected 13 309413 ⟨624053, by decide⟩ ⟨13, 2, 0, 624053, 309413, 2185, 16384⟩
    (by decide) selected_cut_24689

theorem selected_cut_24690 : selected 8 ⟨624079, by decide⟩
    (prefixPartial 13 309414) = some ⟨13, 2, 0, 624079, 309414, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_309414_624079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309414 ⟨624079, by decide⟩ :=
  accepted_of_selected 13 309414 ⟨624079, by decide⟩ ⟨13, 2, 0, 624079, 309414, 2005, 16384⟩
    (by decide) selected_cut_24690

theorem selected_cut_24691 : selected 8 ⟨624090, by decide⟩
    (prefixPartial 13 309415) = some ⟨13, 2, 0, 624090, 309415, 981, 16384⟩ := by
  decide +kernel

theorem context_13_309415_624090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309415 ⟨624090, by decide⟩ :=
  accepted_of_selected 13 309415 ⟨624090, by decide⟩ ⟨13, 2, 0, 624090, 309415, 981, 16384⟩
    (by decide) selected_cut_24691

theorem unmarked_context_12_77353_624091 : frontier 9 ⟨624091, by decide⟩
    (prefixCache 12 77353) (prefixPartial 12 77353) = false := by
  decide +kernel

theorem node_context_12_77353_624091 : EJMOriginalGlobalDAGData.nodes 9 ⟨624091, by decide⟩ =
    .split (coordinate 12) (![⟨624024, by decide⟩,⟨624053, by decide⟩,⟨624079, by decide⟩,⟨624090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77353_624091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77353 ⟨624091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77353
    ⟨624091, by decide⟩ (by decide) (![⟨624024, by decide⟩,⟨624053, by decide⟩,⟨624079, by decide⟩,⟨624090, by decide⟩]) unmarked_context_12_77353_624091 node_context_12_77353_624091
  intro a
  fin_cases a
  · exact context_13_309412_624024
  · exact context_13_309413_624053
  · exact context_13_309414_624079
  · exact context_13_309415_624090

theorem selected_cut_24692 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 77354) = some ⟨12, 1, 0, 445248, 77354, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77354_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77354 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 77354 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 77354, 1, 65536⟩
    (by decide) selected_cut_24692

theorem selected_cut_24693 : selected 8 ⟨624103, by decide⟩
    (prefixPartial 13 309420) = some ⟨13, 2, 0, 624103, 309420, 737, 16384⟩ := by
  decide +kernel

theorem context_13_309420_624103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309420 ⟨624103, by decide⟩ :=
  accepted_of_selected 13 309420 ⟨624103, by decide⟩ ⟨13, 2, 0, 624103, 309420, 737, 16384⟩
    (by decide) selected_cut_24693

theorem selected_cut_24694 : selected 8 ⟨624133, by decide⟩
    (prefixPartial 13 309421) = some ⟨13, 2, 0, 624133, 309421, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_309421_624133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309421 ⟨624133, by decide⟩ :=
  accepted_of_selected 13 309421 ⟨624133, by decide⟩ ⟨13, 2, 0, 624133, 309421, 2353, 16384⟩
    (by decide) selected_cut_24694

theorem selected_cut_24695 : selected 8 ⟨624152, by decide⟩
    (prefixPartial 13 309422) = some ⟨13, 2, 0, 624152, 309422, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_309422_624152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309422 ⟨624152, by decide⟩ :=
  accepted_of_selected 13 309422 ⟨624152, by decide⟩ ⟨13, 2, 0, 624152, 309422, 1881, 16384⟩
    (by decide) selected_cut_24695

theorem selected_cut_24696 : selected 8 ⟨624161, by decide⟩
    (prefixPartial 13 309423) = some ⟨13, 2, 0, 624161, 309423, 993, 16384⟩ := by
  decide +kernel

theorem context_13_309423_624161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309423 ⟨624161, by decide⟩ :=
  accepted_of_selected 13 309423 ⟨624161, by decide⟩ ⟨13, 2, 0, 624161, 309423, 993, 16384⟩
    (by decide) selected_cut_24696

theorem unmarked_context_12_77355_624162 : frontier 9 ⟨624162, by decide⟩
    (prefixCache 12 77355) (prefixPartial 12 77355) = false := by
  decide +kernel

theorem node_context_12_77355_624162 : EJMOriginalGlobalDAGData.nodes 9 ⟨624162, by decide⟩ =
    .split (coordinate 12) (![⟨624103, by decide⟩,⟨624133, by decide⟩,⟨624152, by decide⟩,⟨624161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77355_624162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77355 ⟨624162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77355
    ⟨624162, by decide⟩ (by decide) (![⟨624103, by decide⟩,⟨624133, by decide⟩,⟨624152, by decide⟩,⟨624161, by decide⟩]) unmarked_context_12_77355_624162 node_context_12_77355_624162
  intro a
  fin_cases a
  · exact context_13_309420_624103
  · exact context_13_309421_624133
  · exact context_13_309422_624152
  · exact context_13_309423_624161

theorem unmarked_context_11_19338_624163 : frontier 10 ⟨624163, by decide⟩
    (prefixCache 11 19338) (prefixPartial 11 19338) = false := by
  decide +kernel

theorem node_context_11_19338_624163 : EJMOriginalGlobalDAGData.nodes 10 ⟨624163, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨624091, by decide⟩,⟨445248, by decide⟩,⟨624162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19338_624163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19338 ⟨624163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19338
    ⟨624163, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨624091, by decide⟩,⟨445248, by decide⟩,⟨624162, by decide⟩]) unmarked_context_11_19338_624163 node_context_11_19338_624163
  intro a
  fin_cases a
  · exact context_12_77352_435790
  · exact context_12_77353_624091
  · exact context_12_77354_445248
  · exact context_12_77355_624162

theorem selected_cut_24697 : selected 9 ⟨540189, by decide⟩
    (prefixPartial 12 77356) = some ⟨12, 1, 0, 540189, 77356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77356_540189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77356 ⟨540189, by decide⟩ :=
  accepted_of_selected 12 77356 ⟨540189, by decide⟩ ⟨12, 1, 0, 540189, 77356, 1, 65536⟩
    (by decide) selected_cut_24697

theorem selected_cut_24698 : selected 8 ⟨624177, by decide⟩
    (prefixPartial 13 309428) = some ⟨13, 2, 0, 624177, 309428, 713, 16384⟩ := by
  decide +kernel

theorem context_13_309428_624177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309428 ⟨624177, by decide⟩ :=
  accepted_of_selected 13 309428 ⟨624177, by decide⟩ ⟨13, 2, 0, 624177, 309428, 713, 16384⟩
    (by decide) selected_cut_24698

theorem selected_cut_24699 : selected 8 ⟨624212, by decide⟩
    (prefixPartial 13 309429) = some ⟨13, 2, 0, 624212, 309429, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_309429_624212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309429 ⟨624212, by decide⟩ :=
  accepted_of_selected 13 309429 ⟨624212, by decide⟩ ⟨13, 2, 0, 624212, 309429, 2369, 16384⟩
    (by decide) selected_cut_24699

theorem selected_cut_24700 : selected 8 ⟨624235, by decide⟩
    (prefixPartial 13 309430) = some ⟨13, 2, 0, 624235, 309430, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_309430_624235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309430 ⟨624235, by decide⟩ :=
  accepted_of_selected 13 309430 ⟨624235, by decide⟩ ⟨13, 2, 0, 624235, 309430, 1773, 16384⟩
    (by decide) selected_cut_24700

theorem selected_cut_24701 : selected 8 ⟨624242, by decide⟩
    (prefixPartial 13 309431) = some ⟨13, 2, 0, 624242, 309431, 761, 16384⟩ := by
  decide +kernel

theorem context_13_309431_624242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309431 ⟨624242, by decide⟩ :=
  accepted_of_selected 13 309431 ⟨624242, by decide⟩ ⟨13, 2, 0, 624242, 309431, 761, 16384⟩
    (by decide) selected_cut_24701

theorem unmarked_context_12_77357_624243 : frontier 9 ⟨624243, by decide⟩
    (prefixCache 12 77357) (prefixPartial 12 77357) = false := by
  decide +kernel

theorem node_context_12_77357_624243 : EJMOriginalGlobalDAGData.nodes 9 ⟨624243, by decide⟩ =
    .split (coordinate 12) (![⟨624177, by decide⟩,⟨624212, by decide⟩,⟨624235, by decide⟩,⟨624242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77357_624243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77357 ⟨624243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77357
    ⟨624243, by decide⟩ (by decide) (![⟨624177, by decide⟩,⟨624212, by decide⟩,⟨624235, by decide⟩,⟨624242, by decide⟩]) unmarked_context_12_77357_624243 node_context_12_77357_624243
  intro a
  fin_cases a
  · exact context_13_309428_624177
  · exact context_13_309429_624212
  · exact context_13_309430_624235
  · exact context_13_309431_624242

theorem selected_cut_24702 : selected 8 ⟨624255, by decide⟩
    (prefixPartial 13 309432) = some ⟨13, 2, 0, 624255, 309432, 441, 16384⟩ := by
  decide +kernel

theorem context_13_309432_624255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309432 ⟨624255, by decide⟩ :=
  accepted_of_selected 13 309432 ⟨624255, by decide⟩ ⟨13, 2, 0, 624255, 309432, 441, 16384⟩
    (by decide) selected_cut_24702

theorem selected_cut_24703 : selected 8 ⟨624281, by decide⟩
    (prefixPartial 13 309433) = some ⟨13, 2, 0, 624281, 309433, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_309433_624281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309433 ⟨624281, by decide⟩ :=
  accepted_of_selected 13 309433 ⟨624281, by decide⟩ ⟨13, 2, 0, 624281, 309433, 1741, 16384⟩
    (by decide) selected_cut_24703

theorem selected_cut_24704 : selected 8 ⟨624302, by decide⟩
    (prefixPartial 13 309434) = some ⟨13, 2, 0, 624302, 309434, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_309434_624302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309434 ⟨624302, by decide⟩ :=
  accepted_of_selected 13 309434 ⟨624302, by decide⟩ ⟨13, 2, 0, 624302, 309434, 1257, 16384⟩
    (by decide) selected_cut_24704

theorem selected_cut_24705 : selected 8 ⟨624310, by decide⟩
    (prefixPartial 13 309435) = some ⟨13, 2, 0, 624310, 309435, 689, 16384⟩ := by
  decide +kernel

theorem context_13_309435_624310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309435 ⟨624310, by decide⟩ :=
  accepted_of_selected 13 309435 ⟨624310, by decide⟩ ⟨13, 2, 0, 624310, 309435, 689, 16384⟩
    (by decide) selected_cut_24705

theorem unmarked_context_12_77358_624311 : frontier 9 ⟨624311, by decide⟩
    (prefixCache 12 77358) (prefixPartial 12 77358) = false := by
  decide +kernel

theorem node_context_12_77358_624311 : EJMOriginalGlobalDAGData.nodes 9 ⟨624311, by decide⟩ =
    .split (coordinate 12) (![⟨624255, by decide⟩,⟨624281, by decide⟩,⟨624302, by decide⟩,⟨624310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77358_624311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77358 ⟨624311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77358
    ⟨624311, by decide⟩ (by decide) (![⟨624255, by decide⟩,⟨624281, by decide⟩,⟨624302, by decide⟩,⟨624310, by decide⟩]) unmarked_context_12_77358_624311 node_context_12_77358_624311
  intro a
  fin_cases a
  · exact context_13_309432_624255
  · exact context_13_309433_624281
  · exact context_13_309434_624302
  · exact context_13_309435_624310

theorem selected_cut_24706 : selected 8 ⟨624324, by decide⟩
    (prefixPartial 13 309436) = some ⟨13, 2, 0, 624324, 309436, 593, 16384⟩ := by
  decide +kernel

theorem context_13_309436_624324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309436 ⟨624324, by decide⟩ :=
  accepted_of_selected 13 309436 ⟨624324, by decide⟩ ⟨13, 2, 0, 624324, 309436, 593, 16384⟩
    (by decide) selected_cut_24706

theorem selected_cut_24707 : selected 8 ⟨624350, by decide⟩
    (prefixPartial 13 309437) = some ⟨13, 2, 0, 624350, 309437, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_309437_624350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309437 ⟨624350, by decide⟩ :=
  accepted_of_selected 13 309437 ⟨624350, by decide⟩ ⟨13, 2, 0, 624350, 309437, 2301, 16384⟩
    (by decide) selected_cut_24707

theorem selected_cut_24708 : selected 8 ⟨624367, by decide⟩
    (prefixPartial 13 309438) = some ⟨13, 2, 0, 624367, 309438, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_309438_624367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309438 ⟨624367, by decide⟩ :=
  accepted_of_selected 13 309438 ⟨624367, by decide⟩ ⟨13, 2, 0, 624367, 309438, 1753, 16384⟩
    (by decide) selected_cut_24708

theorem selected_cut_24709 : selected 8 ⟨624378, by decide⟩
    (prefixPartial 13 309439) = some ⟨13, 2, 0, 624378, 309439, 961, 16384⟩ := by
  decide +kernel

theorem context_13_309439_624378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309439 ⟨624378, by decide⟩ :=
  accepted_of_selected 13 309439 ⟨624378, by decide⟩ ⟨13, 2, 0, 624378, 309439, 961, 16384⟩
    (by decide) selected_cut_24709

theorem unmarked_context_12_77359_624379 : frontier 9 ⟨624379, by decide⟩
    (prefixCache 12 77359) (prefixPartial 12 77359) = false := by
  decide +kernel

theorem node_context_12_77359_624379 : EJMOriginalGlobalDAGData.nodes 9 ⟨624379, by decide⟩ =
    .split (coordinate 12) (![⟨624324, by decide⟩,⟨624350, by decide⟩,⟨624367, by decide⟩,⟨624378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77359_624379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77359 ⟨624379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77359
    ⟨624379, by decide⟩ (by decide) (![⟨624324, by decide⟩,⟨624350, by decide⟩,⟨624367, by decide⟩,⟨624378, by decide⟩]) unmarked_context_12_77359_624379 node_context_12_77359_624379
  intro a
  fin_cases a
  · exact context_13_309436_624324
  · exact context_13_309437_624350
  · exact context_13_309438_624367
  · exact context_13_309439_624378

theorem unmarked_context_11_19339_624380 : frontier 10 ⟨624380, by decide⟩
    (prefixCache 11 19339) (prefixPartial 11 19339) = false := by
  decide +kernel

theorem node_context_11_19339_624380 : EJMOriginalGlobalDAGData.nodes 10 ⟨624380, by decide⟩ =
    .split (coordinate 11) (![⟨540189, by decide⟩,⟨624243, by decide⟩,⟨624311, by decide⟩,⟨624379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19339_624380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19339 ⟨624380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19339
    ⟨624380, by decide⟩ (by decide) (![⟨540189, by decide⟩,⟨624243, by decide⟩,⟨624311, by decide⟩,⟨624379, by decide⟩]) unmarked_context_11_19339_624380 node_context_11_19339_624380
  intro a
  fin_cases a
  · exact context_12_77356_540189
  · exact context_12_77357_624243
  · exact context_12_77358_624311
  · exact context_12_77359_624379

theorem unmarked_context_10_4834_624381 : frontier 11 ⟨624381, by decide⟩
    (prefixCache 10 4834) (prefixPartial 10 4834) = false := by
  decide +kernel

theorem node_context_10_4834_624381 : EJMOriginalGlobalDAGData.nodes 11 ⟨624381, by decide⟩ =
    .split (coordinate 10) (![⟨623751, by decide⟩,⟨624009, by decide⟩,⟨624163, by decide⟩,⟨624380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4834_624381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4834 ⟨624381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4834
    ⟨624381, by decide⟩ (by decide) (![⟨623751, by decide⟩,⟨624009, by decide⟩,⟨624163, by decide⟩,⟨624380, by decide⟩]) unmarked_context_10_4834_624381 node_context_10_4834_624381
  intro a
  fin_cases a
  · exact context_11_19336_623751
  · exact context_11_19337_624009
  · exact context_11_19338_624163
  · exact context_11_19339_624380

theorem selected_cut_24710 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 77360) = some ⟨12, 1, 0, 445562, 77360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77360_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77360 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 77360 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 77360, 1, 65536⟩
    (by decide) selected_cut_24710

theorem selected_cut_24711 : selected 8 ⟨624391, by decide⟩
    (prefixPartial 13 309444) = some ⟨13, 2, 0, 624391, 309444, 561, 16384⟩ := by
  decide +kernel

theorem context_13_309444_624391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309444 ⟨624391, by decide⟩ :=
  accepted_of_selected 13 309444 ⟨624391, by decide⟩ ⟨13, 2, 0, 624391, 309444, 561, 16384⟩
    (by decide) selected_cut_24711

theorem selected_cut_24712 : selected 8 ⟨624419, by decide⟩
    (prefixPartial 13 309445) = some ⟨13, 2, 0, 624419, 309445, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_309445_624419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309445 ⟨624419, by decide⟩ :=
  accepted_of_selected 13 309445 ⟨624419, by decide⟩ ⟨13, 2, 0, 624419, 309445, 2317, 16384⟩
    (by decide) selected_cut_24712

theorem selected_cut_24713 : selected 8 ⟨624437, by decide⟩
    (prefixPartial 13 309446) = some ⟨13, 2, 0, 624437, 309446, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_309446_624437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309446 ⟨624437, by decide⟩ :=
  accepted_of_selected 13 309446 ⟨624437, by decide⟩ ⟨13, 2, 0, 624437, 309446, 1613, 16384⟩
    (by decide) selected_cut_24713

theorem selected_cut_24714 : selected 8 ⟨624450, by decide⟩
    (prefixPartial 13 309447) = some ⟨13, 2, 0, 624450, 309447, 989, 16384⟩ := by
  decide +kernel

theorem context_13_309447_624450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309447 ⟨624450, by decide⟩ :=
  accepted_of_selected 13 309447 ⟨624450, by decide⟩ ⟨13, 2, 0, 624450, 309447, 989, 16384⟩
    (by decide) selected_cut_24714

theorem unmarked_context_12_77361_624451 : frontier 9 ⟨624451, by decide⟩
    (prefixCache 12 77361) (prefixPartial 12 77361) = false := by
  decide +kernel

theorem node_context_12_77361_624451 : EJMOriginalGlobalDAGData.nodes 9 ⟨624451, by decide⟩ =
    .split (coordinate 12) (![⟨624391, by decide⟩,⟨624419, by decide⟩,⟨624437, by decide⟩,⟨624450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77361_624451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77361 ⟨624451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77361
    ⟨624451, by decide⟩ (by decide) (![⟨624391, by decide⟩,⟨624419, by decide⟩,⟨624437, by decide⟩,⟨624450, by decide⟩]) unmarked_context_12_77361_624451 node_context_12_77361_624451
  intro a
  fin_cases a
  · exact context_13_309444_624391
  · exact context_13_309445_624419
  · exact context_13_309446_624437
  · exact context_13_309447_624450

theorem selected_cut_24715 : selected 8 ⟨624462, by decide⟩
    (prefixPartial 13 309448) = some ⟨13, 2, 0, 624462, 309448, 373, 16384⟩ := by
  decide +kernel

theorem context_13_309448_624462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309448 ⟨624462, by decide⟩ :=
  accepted_of_selected 13 309448 ⟨624462, by decide⟩ ⟨13, 2, 0, 624462, 309448, 373, 16384⟩
    (by decide) selected_cut_24715

theorem selected_cut_24716 : selected 8 ⟨624486, by decide⟩
    (prefixPartial 13 309449) = some ⟨13, 2, 0, 624486, 309449, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_309449_624486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309449 ⟨624486, by decide⟩ :=
  accepted_of_selected 13 309449 ⟨624486, by decide⟩ ⟨13, 2, 0, 624486, 309449, 1829, 16384⟩
    (by decide) selected_cut_24716

theorem selected_cut_24717 : selected 8 ⟨624507, by decide⟩
    (prefixPartial 13 309450) = some ⟨13, 2, 0, 624507, 309450, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_309450_624507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309450 ⟨624507, by decide⟩ :=
  accepted_of_selected 13 309450 ⟨624507, by decide⟩ ⟨13, 2, 0, 624507, 309450, 1209, 16384⟩
    (by decide) selected_cut_24717

theorem selected_cut_24718 : selected 8 ⟨624517, by decide⟩
    (prefixPartial 13 309451) = some ⟨13, 2, 0, 624517, 309451, 869, 16384⟩ := by
  decide +kernel

theorem context_13_309451_624517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309451 ⟨624517, by decide⟩ :=
  accepted_of_selected 13 309451 ⟨624517, by decide⟩ ⟨13, 2, 0, 624517, 309451, 869, 16384⟩
    (by decide) selected_cut_24718

theorem unmarked_context_12_77362_624518 : frontier 9 ⟨624518, by decide⟩
    (prefixCache 12 77362) (prefixPartial 12 77362) = false := by
  decide +kernel

theorem node_context_12_77362_624518 : EJMOriginalGlobalDAGData.nodes 9 ⟨624518, by decide⟩ =
    .split (coordinate 12) (![⟨624462, by decide⟩,⟨624486, by decide⟩,⟨624507, by decide⟩,⟨624517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77362_624518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77362 ⟨624518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77362
    ⟨624518, by decide⟩ (by decide) (![⟨624462, by decide⟩,⟨624486, by decide⟩,⟨624507, by decide⟩,⟨624517, by decide⟩]) unmarked_context_12_77362_624518 node_context_12_77362_624518
  intro a
  fin_cases a
  · exact context_13_309448_624462
  · exact context_13_309449_624486
  · exact context_13_309450_624507
  · exact context_13_309451_624517

theorem selected_cut_24719 : selected 8 ⟨624528, by decide⟩
    (prefixPartial 13 309452) = some ⟨13, 2, 0, 624528, 309452, 525, 16384⟩ := by
  decide +kernel

theorem context_13_309452_624528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309452 ⟨624528, by decide⟩ :=
  accepted_of_selected 13 309452 ⟨624528, by decide⟩ ⟨13, 2, 0, 624528, 309452, 525, 16384⟩
    (by decide) selected_cut_24719

theorem selected_cut_24720 : selected 8 ⟨624563, by decide⟩
    (prefixPartial 13 309453) = some ⟨13, 2, 0, 624563, 309453, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_309453_624563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309453 ⟨624563, by decide⟩ :=
  accepted_of_selected 13 309453 ⟨624563, by decide⟩ ⟨13, 2, 0, 624563, 309453, 2537, 16384⟩
    (by decide) selected_cut_24720

theorem selected_cut_24721 : selected 8 ⟨624586, by decide⟩
    (prefixPartial 13 309454) = some ⟨13, 2, 0, 624586, 309454, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_309454_624586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309454 ⟨624586, by decide⟩ :=
  accepted_of_selected 13 309454 ⟨624586, by decide⟩ ⟨13, 2, 0, 624586, 309454, 1573, 16384⟩
    (by decide) selected_cut_24721

theorem selected_cut_24722 : selected 8 ⟨624600, by decide⟩
    (prefixPartial 13 309455) = some ⟨13, 2, 0, 624600, 309455, 989, 16384⟩ := by
  decide +kernel

theorem context_13_309455_624600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309455 ⟨624600, by decide⟩ :=
  accepted_of_selected 13 309455 ⟨624600, by decide⟩ ⟨13, 2, 0, 624600, 309455, 989, 16384⟩
    (by decide) selected_cut_24722

theorem unmarked_context_12_77363_624601 : frontier 9 ⟨624601, by decide⟩
    (prefixCache 12 77363) (prefixPartial 12 77363) = false := by
  decide +kernel

theorem node_context_12_77363_624601 : EJMOriginalGlobalDAGData.nodes 9 ⟨624601, by decide⟩ =
    .split (coordinate 12) (![⟨624528, by decide⟩,⟨624563, by decide⟩,⟨624586, by decide⟩,⟨624600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77363_624601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77363 ⟨624601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77363
    ⟨624601, by decide⟩ (by decide) (![⟨624528, by decide⟩,⟨624563, by decide⟩,⟨624586, by decide⟩,⟨624600, by decide⟩]) unmarked_context_12_77363_624601 node_context_12_77363_624601
  intro a
  fin_cases a
  · exact context_13_309452_624528
  · exact context_13_309453_624563
  · exact context_13_309454_624586
  · exact context_13_309455_624600

theorem unmarked_context_11_19340_624602 : frontier 10 ⟨624602, by decide⟩
    (prefixCache 11 19340) (prefixPartial 11 19340) = false := by
  decide +kernel

theorem node_context_11_19340_624602 : EJMOriginalGlobalDAGData.nodes 10 ⟨624602, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨624451, by decide⟩,⟨624518, by decide⟩,⟨624601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19340_624602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19340 ⟨624602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19340
    ⟨624602, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨624451, by decide⟩,⟨624518, by decide⟩,⟨624601, by decide⟩]) unmarked_context_11_19340_624602 node_context_11_19340_624602
  intro a
  fin_cases a
  · exact context_12_77360_445562
  · exact context_12_77361_624451
  · exact context_12_77362_624518
  · exact context_12_77363_624601

theorem selected_cut_24723 : selected 9 ⟨567386, by decide⟩
    (prefixPartial 12 77364) = some ⟨12, 1, 0, 567386, 77364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77364_567386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77364 ⟨567386, by decide⟩ :=
  accepted_of_selected 12 77364 ⟨567386, by decide⟩ ⟨12, 1, 0, 567386, 77364, 1, 65536⟩
    (by decide) selected_cut_24723

theorem selected_cut_24724 : selected 8 ⟨624614, by decide⟩
    (prefixPartial 13 309460) = some ⟨13, 2, 0, 624614, 309460, 473, 16384⟩ := by
  decide +kernel

theorem context_13_309460_624614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309460 ⟨624614, by decide⟩ :=
  accepted_of_selected 13 309460 ⟨624614, by decide⟩ ⟨13, 2, 0, 624614, 309460, 473, 16384⟩
    (by decide) selected_cut_24724

theorem selected_cut_24725 : selected 8 ⟨624638, by decide⟩
    (prefixPartial 13 309461) = some ⟨13, 2, 0, 624638, 309461, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_309461_624638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309461 ⟨624638, by decide⟩ :=
  accepted_of_selected 13 309461 ⟨624638, by decide⟩ ⟨13, 2, 0, 624638, 309461, 1889, 16384⟩
    (by decide) selected_cut_24725

theorem selected_cut_24726 : selected 8 ⟨624659, by decide⟩
    (prefixPartial 13 309462) = some ⟨13, 2, 0, 624659, 309462, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_309462_624659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309462 ⟨624659, by decide⟩ :=
  accepted_of_selected 13 309462 ⟨624659, by decide⟩ ⟨13, 2, 0, 624659, 309462, 1693, 16384⟩
    (by decide) selected_cut_24726

theorem selected_cut_24727 : selected 8 ⟨624669, by decide⟩
    (prefixPartial 13 309463) = some ⟨13, 2, 0, 624669, 309463, 961, 16384⟩ := by
  decide +kernel

theorem context_13_309463_624669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309463 ⟨624669, by decide⟩ :=
  accepted_of_selected 13 309463 ⟨624669, by decide⟩ ⟨13, 2, 0, 624669, 309463, 961, 16384⟩
    (by decide) selected_cut_24727

theorem unmarked_context_12_77365_624670 : frontier 9 ⟨624670, by decide⟩
    (prefixCache 12 77365) (prefixPartial 12 77365) = false := by
  decide +kernel

theorem node_context_12_77365_624670 : EJMOriginalGlobalDAGData.nodes 9 ⟨624670, by decide⟩ =
    .split (coordinate 12) (![⟨624614, by decide⟩,⟨624638, by decide⟩,⟨624659, by decide⟩,⟨624669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77365_624670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77365 ⟨624670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77365
    ⟨624670, by decide⟩ (by decide) (![⟨624614, by decide⟩,⟨624638, by decide⟩,⟨624659, by decide⟩,⟨624669, by decide⟩]) unmarked_context_12_77365_624670 node_context_12_77365_624670
  intro a
  fin_cases a
  · exact context_13_309460_624614
  · exact context_13_309461_624638
  · exact context_13_309462_624659
  · exact context_13_309463_624669

theorem selected_cut_24728 : selected 8 ⟨624677, by decide⟩
    (prefixPartial 13 309464) = some ⟨13, 2, 0, 624677, 309464, 305, 16384⟩ := by
  decide +kernel

theorem context_13_309464_624677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309464 ⟨624677, by decide⟩ :=
  accepted_of_selected 13 309464 ⟨624677, by decide⟩ ⟨13, 2, 0, 624677, 309464, 305, 16384⟩
    (by decide) selected_cut_24728

theorem selected_cut_24729 : selected 8 ⟨624706, by decide⟩
    (prefixPartial 13 309465) = some ⟨13, 2, 0, 624706, 309465, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_309465_624706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309465 ⟨624706, by decide⟩ :=
  accepted_of_selected 13 309465 ⟨624706, by decide⟩ ⟨13, 2, 0, 624706, 309465, 1765, 16384⟩
    (by decide) selected_cut_24729

theorem selected_cut_24730 : selected 8 ⟨624726, by decide⟩
    (prefixPartial 13 309466) = some ⟨13, 2, 0, 624726, 309466, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_309466_624726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309466 ⟨624726, by decide⟩ :=
  accepted_of_selected 13 309466 ⟨624726, by decide⟩ ⟨13, 2, 0, 624726, 309466, 1357, 16384⟩
    (by decide) selected_cut_24730

theorem selected_cut_24731 : selected 8 ⟨624734, by decide⟩
    (prefixPartial 13 309467) = some ⟨13, 2, 0, 624734, 309467, 877, 16384⟩ := by
  decide +kernel

theorem context_13_309467_624734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309467 ⟨624734, by decide⟩ :=
  accepted_of_selected 13 309467 ⟨624734, by decide⟩ ⟨13, 2, 0, 624734, 309467, 877, 16384⟩
    (by decide) selected_cut_24731

theorem unmarked_context_12_77366_624735 : frontier 9 ⟨624735, by decide⟩
    (prefixCache 12 77366) (prefixPartial 12 77366) = false := by
  decide +kernel

theorem node_context_12_77366_624735 : EJMOriginalGlobalDAGData.nodes 9 ⟨624735, by decide⟩ =
    .split (coordinate 12) (![⟨624677, by decide⟩,⟨624706, by decide⟩,⟨624726, by decide⟩,⟨624734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77366_624735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77366 ⟨624735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77366
    ⟨624735, by decide⟩ (by decide) (![⟨624677, by decide⟩,⟨624706, by decide⟩,⟨624726, by decide⟩,⟨624734, by decide⟩]) unmarked_context_12_77366_624735 node_context_12_77366_624735
  intro a
  fin_cases a
  · exact context_13_309464_624677
  · exact context_13_309465_624706
  · exact context_13_309466_624726
  · exact context_13_309467_624734

theorem selected_cut_24732 : selected 8 ⟨624744, by decide⟩
    (prefixPartial 13 309468) = some ⟨13, 2, 0, 624744, 309468, 405, 16384⟩ := by
  decide +kernel

theorem context_13_309468_624744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309468 ⟨624744, by decide⟩ :=
  accepted_of_selected 13 309468 ⟨624744, by decide⟩ ⟨13, 2, 0, 624744, 309468, 405, 16384⟩
    (by decide) selected_cut_24732

theorem selected_cut_24733 : selected 8 ⟨624774, by decide⟩
    (prefixPartial 13 309469) = some ⟨13, 2, 0, 624774, 309469, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_309469_624774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309469 ⟨624774, by decide⟩ :=
  accepted_of_selected 13 309469 ⟨624774, by decide⟩ ⟨13, 2, 0, 624774, 309469, 2253, 16384⟩
    (by decide) selected_cut_24733

theorem selected_cut_24734 : selected 8 ⟨624798, by decide⟩
    (prefixPartial 13 309470) = some ⟨13, 2, 0, 624798, 309470, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_309470_624798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309470 ⟨624798, by decide⟩ :=
  accepted_of_selected 13 309470 ⟨624798, by decide⟩ ⟨13, 2, 0, 624798, 309470, 1737, 16384⟩
    (by decide) selected_cut_24734

theorem selected_cut_24735 : selected 8 ⟨624809, by decide⟩
    (prefixPartial 13 309471) = some ⟨13, 2, 0, 624809, 309471, 985, 16384⟩ := by
  decide +kernel

theorem context_13_309471_624809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309471 ⟨624809, by decide⟩ :=
  accepted_of_selected 13 309471 ⟨624809, by decide⟩ ⟨13, 2, 0, 624809, 309471, 985, 16384⟩
    (by decide) selected_cut_24735

theorem unmarked_context_12_77367_624810 : frontier 9 ⟨624810, by decide⟩
    (prefixCache 12 77367) (prefixPartial 12 77367) = false := by
  decide +kernel

theorem node_context_12_77367_624810 : EJMOriginalGlobalDAGData.nodes 9 ⟨624810, by decide⟩ =
    .split (coordinate 12) (![⟨624744, by decide⟩,⟨624774, by decide⟩,⟨624798, by decide⟩,⟨624809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77367_624810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77367 ⟨624810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77367
    ⟨624810, by decide⟩ (by decide) (![⟨624744, by decide⟩,⟨624774, by decide⟩,⟨624798, by decide⟩,⟨624809, by decide⟩]) unmarked_context_12_77367_624810 node_context_12_77367_624810
  intro a
  fin_cases a
  · exact context_13_309468_624744
  · exact context_13_309469_624774
  · exact context_13_309470_624798
  · exact context_13_309471_624809

theorem unmarked_context_11_19341_624811 : frontier 10 ⟨624811, by decide⟩
    (prefixCache 11 19341) (prefixPartial 11 19341) = false := by
  decide +kernel

theorem node_context_11_19341_624811 : EJMOriginalGlobalDAGData.nodes 10 ⟨624811, by decide⟩ =
    .split (coordinate 11) (![⟨567386, by decide⟩,⟨624670, by decide⟩,⟨624735, by decide⟩,⟨624810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19341_624811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19341 ⟨624811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19341
    ⟨624811, by decide⟩ (by decide) (![⟨567386, by decide⟩,⟨624670, by decide⟩,⟨624735, by decide⟩,⟨624810, by decide⟩]) unmarked_context_11_19341_624811 node_context_11_19341_624811
  intro a
  fin_cases a
  · exact context_12_77364_567386
  · exact context_12_77365_624670
  · exact context_12_77366_624735
  · exact context_12_77367_624810

theorem selected_cut_24736 : selected 9 ⟨540780, by decide⟩
    (prefixPartial 12 77368) = some ⟨12, 1, 0, 540780, 77368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77368_540780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77368 ⟨540780, by decide⟩ :=
  accepted_of_selected 12 77368 ⟨540780, by decide⟩ ⟨12, 1, 0, 540780, 77368, 1, 65536⟩
    (by decide) selected_cut_24736

theorem selected_cut_24737 : selected 8 ⟨624820, by decide⟩
    (prefixPartial 13 309476) = some ⟨13, 2, 0, 624820, 309476, 349, 16384⟩ := by
  decide +kernel

theorem context_13_309476_624820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309476 ⟨624820, by decide⟩ :=
  accepted_of_selected 13 309476 ⟨624820, by decide⟩ ⟨13, 2, 0, 624820, 309476, 349, 16384⟩
    (by decide) selected_cut_24737

theorem selected_cut_24738 : selected 8 ⟨624846, by decide⟩
    (prefixPartial 13 309477) = some ⟨13, 2, 0, 624846, 309477, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_309477_624846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309477 ⟨624846, by decide⟩ :=
  accepted_of_selected 13 309477 ⟨624846, by decide⟩ ⟨13, 2, 0, 624846, 309477, 2057, 16384⟩
    (by decide) selected_cut_24738

theorem selected_cut_24739 : selected 8 ⟨624865, by decide⟩
    (prefixPartial 13 309478) = some ⟨13, 2, 0, 624865, 309478, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_309478_624865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309478 ⟨624865, by decide⟩ :=
  accepted_of_selected 13 309478 ⟨624865, by decide⟩ ⟨13, 2, 0, 624865, 309478, 1821, 16384⟩
    (by decide) selected_cut_24739

theorem selected_cut_24740 : selected 8 ⟨624878, by decide⟩
    (prefixPartial 13 309479) = some ⟨13, 2, 0, 624878, 309479, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_309479_624878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309479 ⟨624878, by decide⟩ :=
  accepted_of_selected 13 309479 ⟨624878, by decide⟩ ⟨13, 2, 0, 624878, 309479, 1069, 16384⟩
    (by decide) selected_cut_24740

theorem unmarked_context_12_77369_624879 : frontier 9 ⟨624879, by decide⟩
    (prefixCache 12 77369) (prefixPartial 12 77369) = false := by
  decide +kernel

theorem node_context_12_77369_624879 : EJMOriginalGlobalDAGData.nodes 9 ⟨624879, by decide⟩ =
    .split (coordinate 12) (![⟨624820, by decide⟩,⟨624846, by decide⟩,⟨624865, by decide⟩,⟨624878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77369_624879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77369 ⟨624879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77369
    ⟨624879, by decide⟩ (by decide) (![⟨624820, by decide⟩,⟨624846, by decide⟩,⟨624865, by decide⟩,⟨624878, by decide⟩]) unmarked_context_12_77369_624879 node_context_12_77369_624879
  intro a
  fin_cases a
  · exact context_13_309476_624820
  · exact context_13_309477_624846
  · exact context_13_309478_624865
  · exact context_13_309479_624878

theorem selected_cut_24741 : selected 8 ⟨624886, by decide⟩
    (prefixPartial 13 309480) = some ⟨13, 2, 0, 624886, 309480, 301, 16384⟩ := by
  decide +kernel

theorem context_13_309480_624886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309480 ⟨624886, by decide⟩ :=
  accepted_of_selected 13 309480 ⟨624886, by decide⟩ ⟨13, 2, 0, 624886, 309480, 301, 16384⟩
    (by decide) selected_cut_24741

theorem selected_cut_24742 : selected 8 ⟨624936, by decide⟩
    (prefixPartial 13 309481) = some ⟨13, 2, 0, 624936, 309481, 3441, 16384⟩ := by
  decide +kernel

theorem context_13_309481_624936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309481 ⟨624936, by decide⟩ :=
  accepted_of_selected 13 309481 ⟨624936, by decide⟩ ⟨13, 2, 0, 624936, 309481, 3441, 16384⟩
    (by decide) selected_cut_24742

theorem selected_cut_24743 : selected 8 ⟨624976, by decide⟩
    (prefixPartial 13 309482) = some ⟨13, 2, 0, 624976, 309482, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_309482_624976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309482 ⟨624976, by decide⟩ :=
  accepted_of_selected 13 309482 ⟨624976, by decide⟩ ⟨13, 2, 0, 624976, 309482, 2345, 16384⟩
    (by decide) selected_cut_24743

theorem selected_cut_24744 : selected 8 ⟨624994, by decide⟩
    (prefixPartial 13 309483) = some ⟨13, 2, 0, 624994, 309483, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_309483_624994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309483 ⟨624994, by decide⟩ :=
  accepted_of_selected 13 309483 ⟨624994, by decide⟩ ⟨13, 2, 0, 624994, 309483, 1245, 16384⟩
    (by decide) selected_cut_24744

theorem unmarked_context_12_77370_624995 : frontier 9 ⟨624995, by decide⟩
    (prefixCache 12 77370) (prefixPartial 12 77370) = false := by
  decide +kernel

theorem node_context_12_77370_624995 : EJMOriginalGlobalDAGData.nodes 9 ⟨624995, by decide⟩ =
    .split (coordinate 12) (![⟨624886, by decide⟩,⟨624936, by decide⟩,⟨624976, by decide⟩,⟨624994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77370_624995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77370 ⟨624995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77370
    ⟨624995, by decide⟩ (by decide) (![⟨624886, by decide⟩,⟨624936, by decide⟩,⟨624976, by decide⟩,⟨624994, by decide⟩]) unmarked_context_12_77370_624995 node_context_12_77370_624995
  intro a
  fin_cases a
  · exact context_13_309480_624886
  · exact context_13_309481_624936
  · exact context_13_309482_624976
  · exact context_13_309483_624994

theorem selected_cut_24745 : selected 8 ⟨625001, by decide⟩
    (prefixPartial 13 309484) = some ⟨13, 2, 0, 625001, 309484, 169, 16384⟩ := by
  decide +kernel

theorem context_13_309484_625001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309484 ⟨625001, by decide⟩ :=
  accepted_of_selected 13 309484 ⟨625001, by decide⟩ ⟨13, 2, 0, 625001, 309484, 169, 16384⟩
    (by decide) selected_cut_24745

theorem selected_cut_24746 : selected 8 ⟨625040, by decide⟩
    (prefixPartial 13 309485) = some ⟨13, 2, 0, 625040, 309485, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_309485_625040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309485 ⟨625040, by decide⟩ :=
  accepted_of_selected 13 309485 ⟨625040, by decide⟩ ⟨13, 2, 0, 625040, 309485, 2505, 16384⟩
    (by decide) selected_cut_24746

theorem selected_cut_24747 : selected 8 ⟨625058, by decide⟩
    (prefixPartial 13 309486) = some ⟨13, 2, 0, 625058, 309486, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_309486_625058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309486 ⟨625058, by decide⟩ :=
  accepted_of_selected 13 309486 ⟨625058, by decide⟩ ⟨13, 2, 0, 625058, 309486, 1613, 16384⟩
    (by decide) selected_cut_24747

theorem selected_cut_24748 : selected 8 ⟨625071, by decide⟩
    (prefixPartial 13 309487) = some ⟨13, 2, 0, 625071, 309487, 925, 16384⟩ := by
  decide +kernel

theorem context_13_309487_625071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309487 ⟨625071, by decide⟩ :=
  accepted_of_selected 13 309487 ⟨625071, by decide⟩ ⟨13, 2, 0, 625071, 309487, 925, 16384⟩
    (by decide) selected_cut_24748

theorem unmarked_context_12_77371_625072 : frontier 9 ⟨625072, by decide⟩
    (prefixCache 12 77371) (prefixPartial 12 77371) = false := by
  decide +kernel

theorem node_context_12_77371_625072 : EJMOriginalGlobalDAGData.nodes 9 ⟨625072, by decide⟩ =
    .split (coordinate 12) (![⟨625001, by decide⟩,⟨625040, by decide⟩,⟨625058, by decide⟩,⟨625071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77371_625072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77371 ⟨625072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77371
    ⟨625072, by decide⟩ (by decide) (![⟨625001, by decide⟩,⟨625040, by decide⟩,⟨625058, by decide⟩,⟨625071, by decide⟩]) unmarked_context_12_77371_625072 node_context_12_77371_625072
  intro a
  fin_cases a
  · exact context_13_309484_625001
  · exact context_13_309485_625040
  · exact context_13_309486_625058
  · exact context_13_309487_625071

theorem unmarked_context_11_19342_625073 : frontier 10 ⟨625073, by decide⟩
    (prefixCache 11 19342) (prefixPartial 11 19342) = false := by
  decide +kernel

theorem node_context_11_19342_625073 : EJMOriginalGlobalDAGData.nodes 10 ⟨625073, by decide⟩ =
    .split (coordinate 11) (![⟨540780, by decide⟩,⟨624879, by decide⟩,⟨624995, by decide⟩,⟨625072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19342_625073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19342 ⟨625073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19342
    ⟨625073, by decide⟩ (by decide) (![⟨540780, by decide⟩,⟨624879, by decide⟩,⟨624995, by decide⟩,⟨625072, by decide⟩]) unmarked_context_11_19342_625073 node_context_11_19342_625073
  intro a
  fin_cases a
  · exact context_12_77368_540780
  · exact context_12_77369_624879
  · exact context_12_77370_624995
  · exact context_12_77371_625072

theorem selected_cut_24749 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 77372) = some ⟨12, 1, 0, 445562, 77372, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77372_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77372 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 77372 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 77372, 1, 65536⟩
    (by decide) selected_cut_24749

theorem selected_cut_24750 : selected 8 ⟨625078, by decide⟩
    (prefixPartial 13 309492) = some ⟨13, 2, 0, 625078, 309492, 193, 16384⟩ := by
  decide +kernel

theorem context_13_309492_625078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309492 ⟨625078, by decide⟩ :=
  accepted_of_selected 13 309492 ⟨625078, by decide⟩ ⟨13, 2, 0, 625078, 309492, 193, 16384⟩
    (by decide) selected_cut_24750

theorem selected_cut_24751 : selected 8 ⟨625123, by decide⟩
    (prefixPartial 13 309493) = some ⟨13, 2, 0, 625123, 309493, 3105, 16384⟩ := by
  decide +kernel

theorem context_13_309493_625123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309493 ⟨625123, by decide⟩ :=
  accepted_of_selected 13 309493 ⟨625123, by decide⟩ ⟨13, 2, 0, 625123, 309493, 3105, 16384⟩
    (by decide) selected_cut_24751

theorem selected_cut_24752 : selected 8 ⟨625163, by decide⟩
    (prefixPartial 13 309494) = some ⟨13, 2, 0, 625163, 309494, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_309494_625163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309494 ⟨625163, by decide⟩ :=
  accepted_of_selected 13 309494 ⟨625163, by decide⟩ ⟨13, 2, 0, 625163, 309494, 2173, 16384⟩
    (by decide) selected_cut_24752

theorem selected_cut_24753 : selected 8 ⟨625182, by decide⟩
    (prefixPartial 13 309495) = some ⟨13, 2, 0, 625182, 309495, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_309495_625182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309495 ⟨625182, by decide⟩ :=
  accepted_of_selected 13 309495 ⟨625182, by decide⟩ ⟨13, 2, 0, 625182, 309495, 1201, 16384⟩
    (by decide) selected_cut_24753

theorem unmarked_context_12_77373_625183 : frontier 9 ⟨625183, by decide⟩
    (prefixCache 12 77373) (prefixPartial 12 77373) = false := by
  decide +kernel

theorem node_context_12_77373_625183 : EJMOriginalGlobalDAGData.nodes 9 ⟨625183, by decide⟩ =
    .split (coordinate 12) (![⟨625078, by decide⟩,⟨625123, by decide⟩,⟨625163, by decide⟩,⟨625182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77373_625183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77373 ⟨625183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77373
    ⟨625183, by decide⟩ (by decide) (![⟨625078, by decide⟩,⟨625123, by decide⟩,⟨625163, by decide⟩,⟨625182, by decide⟩]) unmarked_context_12_77373_625183 node_context_12_77373_625183
  intro a
  fin_cases a
  · exact context_13_309492_625078
  · exact context_13_309493_625123
  · exact context_13_309494_625163
  · exact context_13_309495_625182

theorem selected_cut_24754 : selected 8 ⟨625186, by decide⟩
    (prefixPartial 13 309496) = some ⟨13, 2, 0, 625186, 309496, 53, 16384⟩ := by
  decide +kernel

theorem context_13_309496_625186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309496 ⟨625186, by decide⟩ :=
  accepted_of_selected 13 309496 ⟨625186, by decide⟩ ⟨13, 2, 0, 625186, 309496, 53, 16384⟩
    (by decide) selected_cut_24754

theorem selected_cut_24755 : selected 8 ⟨625224, by decide⟩
    (prefixPartial 13 309497) = some ⟨13, 2, 0, 625224, 309497, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_309497_625224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309497 ⟨625224, by decide⟩ :=
  accepted_of_selected 13 309497 ⟨625224, by decide⟩ ⟨13, 2, 0, 625224, 309497, 2633, 16384⟩
    (by decide) selected_cut_24755

theorem selected_cut_24756 : selected 8 ⟨625249, by decide⟩
    (prefixPartial 13 309498) = some ⟨13, 2, 0, 625249, 309498, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_309498_625249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309498 ⟨625249, by decide⟩ :=
  accepted_of_selected 13 309498 ⟨625249, by decide⟩ ⟨13, 2, 0, 625249, 309498, 1717, 16384⟩
    (by decide) selected_cut_24756

theorem selected_cut_24757 : selected 8 ⟨625262, by decide⟩
    (prefixPartial 13 309499) = some ⟨13, 2, 0, 625262, 309499, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_309499_625262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309499 ⟨625262, by decide⟩ :=
  accepted_of_selected 13 309499 ⟨625262, by decide⟩ ⟨13, 2, 0, 625262, 309499, 1101, 16384⟩
    (by decide) selected_cut_24757

theorem unmarked_context_12_77374_625263 : frontier 9 ⟨625263, by decide⟩
    (prefixCache 12 77374) (prefixPartial 12 77374) = false := by
  decide +kernel

theorem node_context_12_77374_625263 : EJMOriginalGlobalDAGData.nodes 9 ⟨625263, by decide⟩ =
    .split (coordinate 12) (![⟨625186, by decide⟩,⟨625224, by decide⟩,⟨625249, by decide⟩,⟨625262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77374_625263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77374 ⟨625263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77374
    ⟨625263, by decide⟩ (by decide) (![⟨625186, by decide⟩,⟨625224, by decide⟩,⟨625249, by decide⟩,⟨625262, by decide⟩]) unmarked_context_12_77374_625263 node_context_12_77374_625263
  intro a
  fin_cases a
  · exact context_13_309496_625186
  · exact context_13_309497_625224
  · exact context_13_309498_625249
  · exact context_13_309499_625262

theorem selected_cut_24758 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 77375) = some ⟨12, 1, 0, 607719, 77375, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77375_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77375 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 77375 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 77375, 1, 65536⟩
    (by decide) selected_cut_24758

theorem unmarked_context_11_19343_625264 : frontier 10 ⟨625264, by decide⟩
    (prefixCache 11 19343) (prefixPartial 11 19343) = false := by
  decide +kernel

theorem node_context_11_19343_625264 : EJMOriginalGlobalDAGData.nodes 10 ⟨625264, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨625183, by decide⟩,⟨625263, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19343_625264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19343 ⟨625264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19343
    ⟨625264, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨625183, by decide⟩,⟨625263, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_19343_625264 node_context_11_19343_625264
  intro a
  fin_cases a
  · exact context_12_77372_445562
  · exact context_12_77373_625183
  · exact context_12_77374_625263
  · exact context_12_77375_607719

theorem unmarked_context_10_4835_625265 : frontier 11 ⟨625265, by decide⟩
    (prefixCache 10 4835) (prefixPartial 10 4835) = false := by
  decide +kernel

theorem node_context_10_4835_625265 : EJMOriginalGlobalDAGData.nodes 11 ⟨625265, by decide⟩ =
    .split (coordinate 10) (![⟨624602, by decide⟩,⟨624811, by decide⟩,⟨625073, by decide⟩,⟨625264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4835_625265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4835 ⟨625265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4835
    ⟨625265, by decide⟩ (by decide) (![⟨624602, by decide⟩,⟨624811, by decide⟩,⟨625073, by decide⟩,⟨625264, by decide⟩]) unmarked_context_10_4835_625265 node_context_10_4835_625265
  intro a
  fin_cases a
  · exact context_11_19340_624602
  · exact context_11_19341_624811
  · exact context_11_19342_625073
  · exact context_11_19343_625264

theorem unmarked_context_9_1208_625266 : frontier 12 ⟨625266, by decide⟩
    (prefixCache 9 1208) (prefixPartial 9 1208) = false := by
  decide +kernel

theorem node_context_9_1208_625266 : EJMOriginalGlobalDAGData.nodes 12 ⟨625266, by decide⟩ =
    .split (coordinate 9) (![⟨621924, by decide⟩,⟨623506, by decide⟩,⟨624381, by decide⟩,⟨625265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1208_625266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1208 ⟨625266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1208
    ⟨625266, by decide⟩ (by decide) (![⟨621924, by decide⟩,⟨623506, by decide⟩,⟨624381, by decide⟩,⟨625265, by decide⟩]) unmarked_context_9_1208_625266 node_context_9_1208_625266
  intro a
  fin_cases a
  · exact context_10_4832_621924
  · exact context_10_4833_623506
  · exact context_10_4834_624381
  · exact context_10_4835_625265

theorem selected_cut_24759 : selected 9 ⟨625330, by decide⟩
    (prefixPartial 12 77376) = some ⟨12, 2, 0, 625330, 77376, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_77376_625330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77376 ⟨625330, by decide⟩ :=
  accepted_of_selected 12 77376 ⟨625330, by decide⟩ ⟨12, 2, 0, 625330, 77376, 4077, 65536⟩
    (by decide) selected_cut_24759

theorem selected_cut_24760 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309508) = some ⟨13, 1, 0, 3444, 309508, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309508_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309508 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309508 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309508, 1, 16384⟩
    (by decide) selected_cut_24760

theorem selected_cut_24761 : selected 8 ⟨625354, by decide⟩
    (prefixPartial 13 309509) = some ⟨13, 2, 0, 625354, 309509, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_309509_625354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309509 ⟨625354, by decide⟩ :=
  accepted_of_selected 13 309509 ⟨625354, by decide⟩ ⟨13, 2, 0, 625354, 309509, 2249, 16384⟩
    (by decide) selected_cut_24761

theorem selected_cut_24762 : selected 8 ⟨625373, by decide⟩
    (prefixPartial 13 309510) = some ⟨13, 2, 0, 625373, 309510, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_309510_625373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309510 ⟨625373, by decide⟩ :=
  accepted_of_selected 13 309510 ⟨625373, by decide⟩ ⟨13, 2, 0, 625373, 309510, 1441, 16384⟩
    (by decide) selected_cut_24762

theorem selected_cut_24763 : selected 8 ⟨625384, by decide⟩
    (prefixPartial 13 309511) = some ⟨13, 2, 0, 625384, 309511, 741, 16384⟩ := by
  decide +kernel

theorem context_13_309511_625384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309511 ⟨625384, by decide⟩ :=
  accepted_of_selected 13 309511 ⟨625384, by decide⟩ ⟨13, 2, 0, 625384, 309511, 741, 16384⟩
    (by decide) selected_cut_24763

theorem unmarked_context_12_77377_625385 : frontier 9 ⟨625385, by decide⟩
    (prefixCache 12 77377) (prefixPartial 12 77377) = false := by
  decide +kernel

theorem node_context_12_77377_625385 : EJMOriginalGlobalDAGData.nodes 9 ⟨625385, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨625354, by decide⟩,⟨625373, by decide⟩,⟨625384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77377_625385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77377 ⟨625385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77377
    ⟨625385, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨625354, by decide⟩,⟨625373, by decide⟩,⟨625384, by decide⟩]) unmarked_context_12_77377_625385 node_context_12_77377_625385
  intro a
  fin_cases a
  · exact context_13_309508_3444
  · exact context_13_309509_625354
  · exact context_13_309510_625373
  · exact context_13_309511_625384

theorem selected_cut_24764 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309512) = some ⟨13, 1, 0, 3444, 309512, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309512_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309512 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309512 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309512, 1, 16384⟩
    (by decide) selected_cut_24764

theorem selected_cut_24765 : selected 8 ⟨625418, by decide⟩
    (prefixPartial 13 309513) = some ⟨13, 2, 0, 625418, 309513, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_309513_625418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309513 ⟨625418, by decide⟩ :=
  accepted_of_selected 13 309513 ⟨625418, by decide⟩ ⟨13, 2, 0, 625418, 309513, 2357, 16384⟩
    (by decide) selected_cut_24765

theorem selected_cut_24766 : selected 8 ⟨625440, by decide⟩
    (prefixPartial 13 309514) = some ⟨13, 2, 0, 625440, 309514, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_309514_625440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309514 ⟨625440, by decide⟩ :=
  accepted_of_selected 13 309514 ⟨625440, by decide⟩ ⟨13, 2, 0, 625440, 309514, 1513, 16384⟩
    (by decide) selected_cut_24766

theorem selected_cut_24767 : selected 8 ⟨625454, by decide⟩
    (prefixPartial 13 309515) = some ⟨13, 2, 0, 625454, 309515, 877, 16384⟩ := by
  decide +kernel

theorem context_13_309515_625454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309515 ⟨625454, by decide⟩ :=
  accepted_of_selected 13 309515 ⟨625454, by decide⟩ ⟨13, 2, 0, 625454, 309515, 877, 16384⟩
    (by decide) selected_cut_24767

theorem unmarked_context_12_77378_625455 : frontier 9 ⟨625455, by decide⟩
    (prefixCache 12 77378) (prefixPartial 12 77378) = false := by
  decide +kernel

theorem node_context_12_77378_625455 : EJMOriginalGlobalDAGData.nodes 9 ⟨625455, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨625418, by decide⟩,⟨625440, by decide⟩,⟨625454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77378_625455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77378 ⟨625455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77378
    ⟨625455, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨625418, by decide⟩,⟨625440, by decide⟩,⟨625454, by decide⟩]) unmarked_context_12_77378_625455 node_context_12_77378_625455
  intro a
  fin_cases a
  · exact context_13_309512_3444
  · exact context_13_309513_625418
  · exact context_13_309514_625440
  · exact context_13_309515_625454

theorem selected_cut_24768 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309516) = some ⟨13, 1, 0, 3444, 309516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309516, 1, 16384⟩
    (by decide) selected_cut_24768

theorem selected_cut_24769 : selected 8 ⟨625491, by decide⟩
    (prefixPartial 13 309517) = some ⟨13, 2, 0, 625491, 309517, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_309517_625491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309517 ⟨625491, by decide⟩ :=
  accepted_of_selected 13 309517 ⟨625491, by decide⟩ ⟨13, 2, 0, 625491, 309517, 2673, 16384⟩
    (by decide) selected_cut_24769

theorem selected_cut_24770 : selected 8 ⟨625517, by decide⟩
    (prefixPartial 13 309518) = some ⟨13, 2, 0, 625517, 309518, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_309518_625517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309518 ⟨625517, by decide⟩ :=
  accepted_of_selected 13 309518 ⟨625517, by decide⟩ ⟨13, 2, 0, 625517, 309518, 1529, 16384⟩
    (by decide) selected_cut_24770

theorem selected_cut_24771 : selected 8 ⟨625528, by decide⟩
    (prefixPartial 13 309519) = some ⟨13, 2, 0, 625528, 309519, 913, 16384⟩ := by
  decide +kernel

theorem context_13_309519_625528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309519 ⟨625528, by decide⟩ :=
  accepted_of_selected 13 309519 ⟨625528, by decide⟩ ⟨13, 2, 0, 625528, 309519, 913, 16384⟩
    (by decide) selected_cut_24771

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
