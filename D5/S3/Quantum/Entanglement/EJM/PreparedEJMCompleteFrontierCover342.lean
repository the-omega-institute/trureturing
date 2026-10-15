/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover341
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_32835 : selected 8 ⟨845554, by decide⟩
    (prefixPartial 13 439362) = some ⟨13, 2, 0, 845554, 439362, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_439362_845554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439362 ⟨845554, by decide⟩ :=
  accepted_of_selected 13 439362 ⟨845554, by decide⟩ ⟨13, 2, 0, 845554, 439362, 1161, 16384⟩
    (by decide) selected_cut_32835

theorem selected_cut_32836 : selected 8 ⟨845561, by decide⟩
    (prefixPartial 13 439363) = some ⟨13, 2, 0, 845561, 439363, 693, 16384⟩ := by
  decide +kernel

theorem context_13_439363_845561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439363 ⟨845561, by decide⟩ :=
  accepted_of_selected 13 439363 ⟨845561, by decide⟩ ⟨13, 2, 0, 845561, 439363, 693, 16384⟩
    (by decide) selected_cut_32836

theorem unmarked_context_12_109840_845562 : frontier 9 ⟨845562, by decide⟩
    (prefixCache 12 109840) (prefixPartial 12 109840) = false := by
  decide +kernel

theorem node_context_12_109840_845562 : EJMOriginalGlobalDAGData.nodes 9 ⟨845562, by decide⟩ =
    .split (coordinate 12) (![⟨845508, by decide⟩,⟨845532, by decide⟩,⟨845554, by decide⟩,⟨845561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109840_845562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109840 ⟨845562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109840
    ⟨845562, by decide⟩ (by decide) (![⟨845508, by decide⟩,⟨845532, by decide⟩,⟨845554, by decide⟩,⟨845561, by decide⟩]) unmarked_context_12_109840_845562 node_context_12_109840_845562
  intro a
  fin_cases a
  · exact context_13_439360_845508
  · exact context_13_439361_845532
  · exact context_13_439362_845554
  · exact context_13_439363_845561

theorem selected_cut_32837 : selected 8 ⟨845595, by decide⟩
    (prefixPartial 13 439364) = some ⟨13, 2, 0, 845595, 439364, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_439364_845595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439364 ⟨845595, by decide⟩ :=
  accepted_of_selected 13 439364 ⟨845595, by decide⟩ ⟨13, 2, 0, 845595, 439364, 2169, 16384⟩
    (by decide) selected_cut_32837

theorem selected_cut_32838 : selected 8 ⟨845617, by decide⟩
    (prefixPartial 13 439365) = some ⟨13, 2, 0, 845617, 439365, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_439365_845617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439365 ⟨845617, by decide⟩ :=
  accepted_of_selected 13 439365 ⟨845617, by decide⟩ ⟨13, 2, 0, 845617, 439365, 2449, 16384⟩
    (by decide) selected_cut_32838

theorem selected_cut_32839 : selected 8 ⟨845641, by decide⟩
    (prefixPartial 13 439366) = some ⟨13, 2, 0, 845641, 439366, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_439366_845641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439366 ⟨845641, by decide⟩ :=
  accepted_of_selected 13 439366 ⟨845641, by decide⟩ ⟨13, 2, 0, 845641, 439366, 1333, 16384⟩
    (by decide) selected_cut_32839

theorem selected_cut_32840 : selected 8 ⟨845648, by decide⟩
    (prefixPartial 13 439367) = some ⟨13, 2, 0, 845648, 439367, 753, 16384⟩ := by
  decide +kernel

theorem context_13_439367_845648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439367 ⟨845648, by decide⟩ :=
  accepted_of_selected 13 439367 ⟨845648, by decide⟩ ⟨13, 2, 0, 845648, 439367, 753, 16384⟩
    (by decide) selected_cut_32840

theorem unmarked_context_12_109841_845649 : frontier 9 ⟨845649, by decide⟩
    (prefixCache 12 109841) (prefixPartial 12 109841) = false := by
  decide +kernel

theorem node_context_12_109841_845649 : EJMOriginalGlobalDAGData.nodes 9 ⟨845649, by decide⟩ =
    .split (coordinate 12) (![⟨845595, by decide⟩,⟨845617, by decide⟩,⟨845641, by decide⟩,⟨845648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109841_845649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109841 ⟨845649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109841
    ⟨845649, by decide⟩ (by decide) (![⟨845595, by decide⟩,⟨845617, by decide⟩,⟨845641, by decide⟩,⟨845648, by decide⟩]) unmarked_context_12_109841_845649 node_context_12_109841_845649
  intro a
  fin_cases a
  · exact context_13_439364_845595
  · exact context_13_439365_845617
  · exact context_13_439366_845641
  · exact context_13_439367_845648

theorem selected_cut_32841 : selected 8 ⟨845685, by decide⟩
    (prefixPartial 13 439368) = some ⟨13, 2, 0, 845685, 439368, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_439368_845685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439368 ⟨845685, by decide⟩ :=
  accepted_of_selected 13 439368 ⟨845685, by decide⟩ ⟨13, 2, 0, 845685, 439368, 1869, 16384⟩
    (by decide) selected_cut_32841

theorem selected_cut_32842 : selected 8 ⟨845713, by decide⟩
    (prefixPartial 13 439369) = some ⟨13, 2, 0, 845713, 439369, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_439369_845713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439369 ⟨845713, by decide⟩ :=
  accepted_of_selected 13 439369 ⟨845713, by decide⟩ ⟨13, 2, 0, 845713, 439369, 2453, 16384⟩
    (by decide) selected_cut_32842

theorem selected_cut_32843 : selected 8 ⟨845734, by decide⟩
    (prefixPartial 13 439370) = some ⟨13, 2, 0, 845734, 439370, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_439370_845734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439370 ⟨845734, by decide⟩ :=
  accepted_of_selected 13 439370 ⟨845734, by decide⟩ ⟨13, 2, 0, 845734, 439370, 1129, 16384⟩
    (by decide) selected_cut_32843

theorem selected_cut_32844 : selected 8 ⟨845741, by decide⟩
    (prefixPartial 13 439371) = some ⟨13, 2, 0, 845741, 439371, 821, 16384⟩ := by
  decide +kernel

theorem context_13_439371_845741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439371 ⟨845741, by decide⟩ :=
  accepted_of_selected 13 439371 ⟨845741, by decide⟩ ⟨13, 2, 0, 845741, 439371, 821, 16384⟩
    (by decide) selected_cut_32844

theorem unmarked_context_12_109842_845742 : frontier 9 ⟨845742, by decide⟩
    (prefixCache 12 109842) (prefixPartial 12 109842) = false := by
  decide +kernel

theorem node_context_12_109842_845742 : EJMOriginalGlobalDAGData.nodes 9 ⟨845742, by decide⟩ =
    .split (coordinate 12) (![⟨845685, by decide⟩,⟨845713, by decide⟩,⟨845734, by decide⟩,⟨845741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109842_845742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109842 ⟨845742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109842
    ⟨845742, by decide⟩ (by decide) (![⟨845685, by decide⟩,⟨845713, by decide⟩,⟨845734, by decide⟩,⟨845741, by decide⟩]) unmarked_context_12_109842_845742 node_context_12_109842_845742
  intro a
  fin_cases a
  · exact context_13_439368_845685
  · exact context_13_439369_845713
  · exact context_13_439370_845734
  · exact context_13_439371_845741

theorem selected_cut_32845 : selected 8 ⟨845786, by decide⟩
    (prefixPartial 13 439372) = some ⟨13, 2, 0, 845786, 439372, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_439372_845786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439372 ⟨845786, by decide⟩ :=
  accepted_of_selected 13 439372 ⟨845786, by decide⟩ ⟨13, 2, 0, 845786, 439372, 2149, 16384⟩
    (by decide) selected_cut_32845

theorem selected_cut_32846 : selected 8 ⟨845828, by decide⟩
    (prefixPartial 13 439373) = some ⟨13, 2, 0, 845828, 439373, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_439373_845828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439373 ⟨845828, by decide⟩ :=
  accepted_of_selected 13 439373 ⟨845828, by decide⟩ ⟨13, 2, 0, 845828, 439373, 2809, 16384⟩
    (by decide) selected_cut_32846

theorem selected_cut_32847 : selected 8 ⟨845867, by decide⟩
    (prefixPartial 13 439374) = some ⟨13, 2, 0, 845867, 439374, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_439374_845867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439374 ⟨845867, by decide⟩ :=
  accepted_of_selected 13 439374 ⟨845867, by decide⟩ ⟨13, 2, 0, 845867, 439374, 1437, 16384⟩
    (by decide) selected_cut_32847

theorem selected_cut_32848 : selected 8 ⟨845872, by decide⟩
    (prefixPartial 13 439375) = some ⟨13, 2, 0, 845872, 439375, 845, 16384⟩ := by
  decide +kernel

theorem context_13_439375_845872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439375 ⟨845872, by decide⟩ :=
  accepted_of_selected 13 439375 ⟨845872, by decide⟩ ⟨13, 2, 0, 845872, 439375, 845, 16384⟩
    (by decide) selected_cut_32848

theorem unmarked_context_12_109843_845873 : frontier 9 ⟨845873, by decide⟩
    (prefixCache 12 109843) (prefixPartial 12 109843) = false := by
  decide +kernel

theorem node_context_12_109843_845873 : EJMOriginalGlobalDAGData.nodes 9 ⟨845873, by decide⟩ =
    .split (coordinate 12) (![⟨845786, by decide⟩,⟨845828, by decide⟩,⟨845867, by decide⟩,⟨845872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109843_845873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109843 ⟨845873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109843
    ⟨845873, by decide⟩ (by decide) (![⟨845786, by decide⟩,⟨845828, by decide⟩,⟨845867, by decide⟩,⟨845872, by decide⟩]) unmarked_context_12_109843_845873 node_context_12_109843_845873
  intro a
  fin_cases a
  · exact context_13_439372_845786
  · exact context_13_439373_845828
  · exact context_13_439374_845867
  · exact context_13_439375_845872

theorem unmarked_context_11_27460_845874 : frontier 10 ⟨845874, by decide⟩
    (prefixCache 11 27460) (prefixPartial 11 27460) = false := by
  decide +kernel

theorem node_context_11_27460_845874 : EJMOriginalGlobalDAGData.nodes 10 ⟨845874, by decide⟩ =
    .split (coordinate 11) (![⟨845562, by decide⟩,⟨845649, by decide⟩,⟨845742, by decide⟩,⟨845873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27460_845874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27460 ⟨845874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27460
    ⟨845874, by decide⟩ (by decide) (![⟨845562, by decide⟩,⟨845649, by decide⟩,⟨845742, by decide⟩,⟨845873, by decide⟩]) unmarked_context_11_27460_845874 node_context_11_27460_845874
  intro a
  fin_cases a
  · exact context_12_109840_845562
  · exact context_12_109841_845649
  · exact context_12_109842_845742
  · exact context_12_109843_845873

theorem selected_cut_32849 : selected 8 ⟨845899, by decide⟩
    (prefixPartial 13 439376) = some ⟨13, 2, 0, 845899, 439376, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_439376_845899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439376 ⟨845899, by decide⟩ :=
  accepted_of_selected 13 439376 ⟨845899, by decide⟩ ⟨13, 2, 0, 845899, 439376, 1465, 16384⟩
    (by decide) selected_cut_32849

theorem selected_cut_32850 : selected 8 ⟨845923, by decide⟩
    (prefixPartial 13 439377) = some ⟨13, 2, 0, 845923, 439377, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_439377_845923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439377 ⟨845923, by decide⟩ :=
  accepted_of_selected 13 439377 ⟨845923, by decide⟩ ⟨13, 2, 0, 845923, 439377, 2077, 16384⟩
    (by decide) selected_cut_32850

theorem selected_cut_32851 : selected 8 ⟨845948, by decide⟩
    (prefixPartial 13 439378) = some ⟨13, 2, 0, 845948, 439378, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_439378_845948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439378 ⟨845948, by decide⟩ :=
  accepted_of_selected 13 439378 ⟨845948, by decide⟩ ⟨13, 2, 0, 845948, 439378, 1169, 16384⟩
    (by decide) selected_cut_32851

theorem selected_cut_32852 : selected 8 ⟨845958, by decide⟩
    (prefixPartial 13 439379) = some ⟨13, 2, 0, 845958, 439379, 677, 16384⟩ := by
  decide +kernel

theorem context_13_439379_845958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439379 ⟨845958, by decide⟩ :=
  accepted_of_selected 13 439379 ⟨845958, by decide⟩ ⟨13, 2, 0, 845958, 439379, 677, 16384⟩
    (by decide) selected_cut_32852

theorem unmarked_context_12_109844_845959 : frontier 9 ⟨845959, by decide⟩
    (prefixCache 12 109844) (prefixPartial 12 109844) = false := by
  decide +kernel

theorem node_context_12_109844_845959 : EJMOriginalGlobalDAGData.nodes 9 ⟨845959, by decide⟩ =
    .split (coordinate 12) (![⟨845899, by decide⟩,⟨845923, by decide⟩,⟨845948, by decide⟩,⟨845958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109844_845959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109844 ⟨845959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109844
    ⟨845959, by decide⟩ (by decide) (![⟨845899, by decide⟩,⟨845923, by decide⟩,⟨845948, by decide⟩,⟨845958, by decide⟩]) unmarked_context_12_109844_845959 node_context_12_109844_845959
  intro a
  fin_cases a
  · exact context_13_439376_845899
  · exact context_13_439377_845923
  · exact context_13_439378_845948
  · exact context_13_439379_845958

theorem selected_cut_32853 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 109845) = some ⟨12, 1, 0, 439069, 109845, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109845_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109845 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 109845 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 109845, 1, 65536⟩
    (by decide) selected_cut_32853

theorem selected_cut_32854 : selected 8 ⟨845986, by decide⟩
    (prefixPartial 13 439384) = some ⟨13, 2, 0, 845986, 439384, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_439384_845986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439384 ⟨845986, by decide⟩ :=
  accepted_of_selected 13 439384 ⟨845986, by decide⟩ ⟨13, 2, 0, 845986, 439384, 1553, 16384⟩
    (by decide) selected_cut_32854

theorem selected_cut_32855 : selected 8 ⟨846014, by decide⟩
    (prefixPartial 13 439385) = some ⟨13, 2, 0, 846014, 439385, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_439385_846014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439385 ⟨846014, by decide⟩ :=
  accepted_of_selected 13 439385 ⟨846014, by decide⟩ ⟨13, 2, 0, 846014, 439385, 2157, 16384⟩
    (by decide) selected_cut_32855

theorem selected_cut_32856 : selected 8 ⟨846034, by decide⟩
    (prefixPartial 13 439386) = some ⟨13, 2, 0, 846034, 439386, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_439386_846034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439386 ⟨846034, by decide⟩ :=
  accepted_of_selected 13 439386 ⟨846034, by decide⟩ ⟨13, 2, 0, 846034, 439386, 1097, 16384⟩
    (by decide) selected_cut_32856

theorem selected_cut_32857 : selected 8 ⟨846041, by decide⟩
    (prefixPartial 13 439387) = some ⟨13, 2, 0, 846041, 439387, 765, 16384⟩ := by
  decide +kernel

theorem context_13_439387_846041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439387 ⟨846041, by decide⟩ :=
  accepted_of_selected 13 439387 ⟨846041, by decide⟩ ⟨13, 2, 0, 846041, 439387, 765, 16384⟩
    (by decide) selected_cut_32857

theorem unmarked_context_12_109846_846042 : frontier 9 ⟨846042, by decide⟩
    (prefixCache 12 109846) (prefixPartial 12 109846) = false := by
  decide +kernel

theorem node_context_12_109846_846042 : EJMOriginalGlobalDAGData.nodes 9 ⟨846042, by decide⟩ =
    .split (coordinate 12) (![⟨845986, by decide⟩,⟨846014, by decide⟩,⟨846034, by decide⟩,⟨846041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109846_846042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109846 ⟨846042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109846
    ⟨846042, by decide⟩ (by decide) (![⟨845986, by decide⟩,⟨846014, by decide⟩,⟨846034, by decide⟩,⟨846041, by decide⟩]) unmarked_context_12_109846_846042 node_context_12_109846_846042
  intro a
  fin_cases a
  · exact context_13_439384_845986
  · exact context_13_439385_846014
  · exact context_13_439386_846034
  · exact context_13_439387_846041

theorem selected_cut_32858 : selected 8 ⟨846072, by decide⟩
    (prefixPartial 13 439388) = some ⟨13, 2, 0, 846072, 439388, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_439388_846072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439388 ⟨846072, by decide⟩ :=
  accepted_of_selected 13 439388 ⟨846072, by decide⟩ ⟨13, 2, 0, 846072, 439388, 1801, 16384⟩
    (by decide) selected_cut_32858

theorem selected_cut_32859 : selected 8 ⟨846110, by decide⟩
    (prefixPartial 13 439389) = some ⟨13, 2, 0, 846110, 439389, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_439389_846110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439389 ⟨846110, by decide⟩ :=
  accepted_of_selected 13 439389 ⟨846110, by decide⟩ ⟨13, 2, 0, 846110, 439389, 2501, 16384⟩
    (by decide) selected_cut_32859

theorem selected_cut_32860 : selected 8 ⟨846157, by decide⟩
    (prefixPartial 13 439390) = some ⟨13, 2, 0, 846157, 439390, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_439390_846157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439390 ⟨846157, by decide⟩ :=
  accepted_of_selected 13 439390 ⟨846157, by decide⟩ ⟨13, 2, 0, 846157, 439390, 1553, 16384⟩
    (by decide) selected_cut_32860

theorem selected_cut_32861 : selected 8 ⟨846163, by decide⟩
    (prefixPartial 13 439391) = some ⟨13, 2, 0, 846163, 439391, 721, 16384⟩ := by
  decide +kernel

theorem context_13_439391_846163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439391 ⟨846163, by decide⟩ :=
  accepted_of_selected 13 439391 ⟨846163, by decide⟩ ⟨13, 2, 0, 846163, 439391, 721, 16384⟩
    (by decide) selected_cut_32861

theorem unmarked_context_12_109847_846164 : frontier 9 ⟨846164, by decide⟩
    (prefixCache 12 109847) (prefixPartial 12 109847) = false := by
  decide +kernel

theorem node_context_12_109847_846164 : EJMOriginalGlobalDAGData.nodes 9 ⟨846164, by decide⟩ =
    .split (coordinate 12) (![⟨846072, by decide⟩,⟨846110, by decide⟩,⟨846157, by decide⟩,⟨846163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109847_846164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109847 ⟨846164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109847
    ⟨846164, by decide⟩ (by decide) (![⟨846072, by decide⟩,⟨846110, by decide⟩,⟨846157, by decide⟩,⟨846163, by decide⟩]) unmarked_context_12_109847_846164 node_context_12_109847_846164
  intro a
  fin_cases a
  · exact context_13_439388_846072
  · exact context_13_439389_846110
  · exact context_13_439390_846157
  · exact context_13_439391_846163

theorem unmarked_context_11_27461_846165 : frontier 10 ⟨846165, by decide⟩
    (prefixCache 11 27461) (prefixPartial 11 27461) = false := by
  decide +kernel

theorem node_context_11_27461_846165 : EJMOriginalGlobalDAGData.nodes 10 ⟨846165, by decide⟩ =
    .split (coordinate 11) (![⟨845959, by decide⟩,⟨439069, by decide⟩,⟨846042, by decide⟩,⟨846164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27461_846165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27461 ⟨846165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27461
    ⟨846165, by decide⟩ (by decide) (![⟨845959, by decide⟩,⟨439069, by decide⟩,⟨846042, by decide⟩,⟨846164, by decide⟩]) unmarked_context_11_27461_846165 node_context_11_27461_846165
  intro a
  fin_cases a
  · exact context_12_109844_845959
  · exact context_12_109845_439069
  · exact context_12_109846_846042
  · exact context_12_109847_846164

theorem selected_cut_32862 : selected 8 ⟨846190, by decide⟩
    (prefixPartial 13 439392) = some ⟨13, 2, 0, 846190, 439392, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_439392_846190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439392 ⟨846190, by decide⟩ :=
  accepted_of_selected 13 439392 ⟨846190, by decide⟩ ⟨13, 2, 0, 846190, 439392, 1577, 16384⟩
    (by decide) selected_cut_32862

theorem selected_cut_32863 : selected 8 ⟨846222, by decide⟩
    (prefixPartial 13 439393) = some ⟨13, 2, 0, 846222, 439393, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_439393_846222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439393 ⟨846222, by decide⟩ :=
  accepted_of_selected 13 439393 ⟨846222, by decide⟩ ⟨13, 2, 0, 846222, 439393, 2209, 16384⟩
    (by decide) selected_cut_32863

theorem selected_cut_32864 : selected 8 ⟨846263, by decide⟩
    (prefixPartial 13 439394) = some ⟨13, 2, 0, 846263, 439394, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_439394_846263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439394 ⟨846263, by decide⟩ :=
  accepted_of_selected 13 439394 ⟨846263, by decide⟩ ⟨13, 2, 0, 846263, 439394, 1381, 16384⟩
    (by decide) selected_cut_32864

theorem selected_cut_32865 : selected 8 ⟨846268, by decide⟩
    (prefixPartial 13 439395) = some ⟨13, 2, 0, 846268, 439395, 613, 16384⟩ := by
  decide +kernel

theorem context_13_439395_846268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439395 ⟨846268, by decide⟩ :=
  accepted_of_selected 13 439395 ⟨846268, by decide⟩ ⟨13, 2, 0, 846268, 439395, 613, 16384⟩
    (by decide) selected_cut_32865

theorem unmarked_context_12_109848_846269 : frontier 9 ⟨846269, by decide⟩
    (prefixCache 12 109848) (prefixPartial 12 109848) = false := by
  decide +kernel

theorem node_context_12_109848_846269 : EJMOriginalGlobalDAGData.nodes 9 ⟨846269, by decide⟩ =
    .split (coordinate 12) (![⟨846190, by decide⟩,⟨846222, by decide⟩,⟨846263, by decide⟩,⟨846268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109848_846269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109848 ⟨846269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109848
    ⟨846269, by decide⟩ (by decide) (![⟨846190, by decide⟩,⟨846222, by decide⟩,⟨846263, by decide⟩,⟨846268, by decide⟩]) unmarked_context_12_109848_846269 node_context_12_109848_846269
  intro a
  fin_cases a
  · exact context_13_439392_846190
  · exact context_13_439393_846222
  · exact context_13_439394_846263
  · exact context_13_439395_846268

theorem selected_cut_32866 : selected 8 ⟨846303, by decide⟩
    (prefixPartial 13 439396) = some ⟨13, 2, 0, 846303, 439396, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_439396_846303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439396 ⟨846303, by decide⟩ :=
  accepted_of_selected 13 439396 ⟨846303, by decide⟩ ⟨13, 2, 0, 846303, 439396, 1825, 16384⟩
    (by decide) selected_cut_32866

theorem selected_cut_32867 : selected 8 ⟨846332, by decide⟩
    (prefixPartial 13 439397) = some ⟨13, 2, 0, 846332, 439397, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_439397_846332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439397 ⟨846332, by decide⟩ :=
  accepted_of_selected 13 439397 ⟨846332, by decide⟩ ⟨13, 2, 0, 846332, 439397, 2185, 16384⟩
    (by decide) selected_cut_32867

theorem selected_cut_32868 : selected 8 ⟨846369, by decide⟩
    (prefixPartial 13 439398) = some ⟨13, 2, 0, 846369, 439398, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_439398_846369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439398 ⟨846369, by decide⟩ :=
  accepted_of_selected 13 439398 ⟨846369, by decide⟩ ⟨13, 2, 0, 846369, 439398, 1577, 16384⟩
    (by decide) selected_cut_32868

theorem selected_cut_32869 : selected 8 ⟨846374, by decide⟩
    (prefixPartial 13 439399) = some ⟨13, 2, 0, 846374, 439399, 633, 16384⟩ := by
  decide +kernel

theorem context_13_439399_846374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439399 ⟨846374, by decide⟩ :=
  accepted_of_selected 13 439399 ⟨846374, by decide⟩ ⟨13, 2, 0, 846374, 439399, 633, 16384⟩
    (by decide) selected_cut_32869

theorem unmarked_context_12_109849_846375 : frontier 9 ⟨846375, by decide⟩
    (prefixCache 12 109849) (prefixPartial 12 109849) = false := by
  decide +kernel

theorem node_context_12_109849_846375 : EJMOriginalGlobalDAGData.nodes 9 ⟨846375, by decide⟩ =
    .split (coordinate 12) (![⟨846303, by decide⟩,⟨846332, by decide⟩,⟨846369, by decide⟩,⟨846374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109849_846375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109849 ⟨846375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109849
    ⟨846375, by decide⟩ (by decide) (![⟨846303, by decide⟩,⟨846332, by decide⟩,⟨846369, by decide⟩,⟨846374, by decide⟩]) unmarked_context_12_109849_846375 node_context_12_109849_846375
  intro a
  fin_cases a
  · exact context_13_439396_846303
  · exact context_13_439397_846332
  · exact context_13_439398_846369
  · exact context_13_439399_846374

theorem selected_cut_32870 : selected 8 ⟨846411, by decide⟩
    (prefixPartial 13 439400) = some ⟨13, 2, 0, 846411, 439400, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_439400_846411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439400 ⟨846411, by decide⟩ :=
  accepted_of_selected 13 439400 ⟨846411, by decide⟩ ⟨13, 2, 0, 846411, 439400, 1553, 16384⟩
    (by decide) selected_cut_32870

theorem selected_cut_32871 : selected 8 ⟨846436, by decide⟩
    (prefixPartial 13 439401) = some ⟨13, 2, 0, 846436, 439401, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_439401_846436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439401 ⟨846436, by decide⟩ :=
  accepted_of_selected 13 439401 ⟨846436, by decide⟩ ⟨13, 2, 0, 846436, 439401, 2181, 16384⟩
    (by decide) selected_cut_32871

theorem selected_cut_32872 : selected 8 ⟨846461, by decide⟩
    (prefixPartial 13 439402) = some ⟨13, 2, 0, 846461, 439402, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_439402_846461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439402 ⟨846461, by decide⟩ :=
  accepted_of_selected 13 439402 ⟨846461, by decide⟩ ⟨13, 2, 0, 846461, 439402, 1225, 16384⟩
    (by decide) selected_cut_32872

theorem selected_cut_32873 : selected 8 ⟨846467, by decide⟩
    (prefixPartial 13 439403) = some ⟨13, 2, 0, 846467, 439403, 609, 16384⟩ := by
  decide +kernel

theorem context_13_439403_846467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439403 ⟨846467, by decide⟩ :=
  accepted_of_selected 13 439403 ⟨846467, by decide⟩ ⟨13, 2, 0, 846467, 439403, 609, 16384⟩
    (by decide) selected_cut_32873

theorem unmarked_context_12_109850_846468 : frontier 9 ⟨846468, by decide⟩
    (prefixCache 12 109850) (prefixPartial 12 109850) = false := by
  decide +kernel

theorem node_context_12_109850_846468 : EJMOriginalGlobalDAGData.nodes 9 ⟨846468, by decide⟩ =
    .split (coordinate 12) (![⟨846411, by decide⟩,⟨846436, by decide⟩,⟨846461, by decide⟩,⟨846467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109850_846468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109850 ⟨846468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109850
    ⟨846468, by decide⟩ (by decide) (![⟨846411, by decide⟩,⟨846436, by decide⟩,⟨846461, by decide⟩,⟨846467, by decide⟩]) unmarked_context_12_109850_846468 node_context_12_109850_846468
  intro a
  fin_cases a
  · exact context_13_439400_846411
  · exact context_13_439401_846436
  · exact context_13_439402_846461
  · exact context_13_439403_846467

theorem selected_cut_32874 : selected 8 ⟨846503, by decide⟩
    (prefixPartial 13 439404) = some ⟨13, 2, 0, 846503, 439404, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_439404_846503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439404 ⟨846503, by decide⟩ :=
  accepted_of_selected 13 439404 ⟨846503, by decide⟩ ⟨13, 2, 0, 846503, 439404, 1797, 16384⟩
    (by decide) selected_cut_32874

theorem selected_cut_32875 : selected 8 ⟨846549, by decide⟩
    (prefixPartial 13 439405) = some ⟨13, 2, 0, 846549, 439405, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_439405_846549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439405 ⟨846549, by decide⟩ :=
  accepted_of_selected 13 439405 ⟨846549, by decide⟩ ⟨13, 2, 0, 846549, 439405, 2689, 16384⟩
    (by decide) selected_cut_32875

theorem selected_cut_32876 : selected 8 ⟨846604, by decide⟩
    (prefixPartial 13 439406) = some ⟨13, 2, 0, 846604, 439406, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_439406_846604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439406 ⟨846604, by decide⟩ :=
  accepted_of_selected 13 439406 ⟨846604, by decide⟩ ⟨13, 2, 0, 846604, 439406, 1677, 16384⟩
    (by decide) selected_cut_32876

theorem selected_cut_32877 : selected 8 ⟨846612, by decide⟩
    (prefixPartial 13 439407) = some ⟨13, 2, 0, 846612, 439407, 613, 16384⟩ := by
  decide +kernel

theorem context_13_439407_846612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439407 ⟨846612, by decide⟩ :=
  accepted_of_selected 13 439407 ⟨846612, by decide⟩ ⟨13, 2, 0, 846612, 439407, 613, 16384⟩
    (by decide) selected_cut_32877

theorem unmarked_context_12_109851_846613 : frontier 9 ⟨846613, by decide⟩
    (prefixCache 12 109851) (prefixPartial 12 109851) = false := by
  decide +kernel

theorem node_context_12_109851_846613 : EJMOriginalGlobalDAGData.nodes 9 ⟨846613, by decide⟩ =
    .split (coordinate 12) (![⟨846503, by decide⟩,⟨846549, by decide⟩,⟨846604, by decide⟩,⟨846612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109851_846613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109851 ⟨846613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109851
    ⟨846613, by decide⟩ (by decide) (![⟨846503, by decide⟩,⟨846549, by decide⟩,⟨846604, by decide⟩,⟨846612, by decide⟩]) unmarked_context_12_109851_846613 node_context_12_109851_846613
  intro a
  fin_cases a
  · exact context_13_439404_846503
  · exact context_13_439405_846549
  · exact context_13_439406_846604
  · exact context_13_439407_846612

theorem unmarked_context_11_27462_846614 : frontier 10 ⟨846614, by decide⟩
    (prefixCache 11 27462) (prefixPartial 11 27462) = false := by
  decide +kernel

theorem node_context_11_27462_846614 : EJMOriginalGlobalDAGData.nodes 10 ⟨846614, by decide⟩ =
    .split (coordinate 11) (![⟨846269, by decide⟩,⟨846375, by decide⟩,⟨846468, by decide⟩,⟨846613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27462_846614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27462 ⟨846614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27462
    ⟨846614, by decide⟩ (by decide) (![⟨846269, by decide⟩,⟨846375, by decide⟩,⟨846468, by decide⟩,⟨846613, by decide⟩]) unmarked_context_11_27462_846614 node_context_11_27462_846614
  intro a
  fin_cases a
  · exact context_12_109848_846269
  · exact context_12_109849_846375
  · exact context_12_109850_846468
  · exact context_12_109851_846613

theorem selected_cut_32878 : selected 8 ⟨846633, by decide⟩
    (prefixPartial 13 439408) = some ⟨13, 2, 0, 846633, 439408, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_439408_846633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439408 ⟨846633, by decide⟩ :=
  accepted_of_selected 13 439408 ⟨846633, by decide⟩ ⟨13, 2, 0, 846633, 439408, 1389, 16384⟩
    (by decide) selected_cut_32878

theorem selected_cut_32879 : selected 8 ⟨846663, by decide⟩
    (prefixPartial 13 439409) = some ⟨13, 2, 0, 846663, 439409, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_439409_846663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439409 ⟨846663, by decide⟩ :=
  accepted_of_selected 13 439409 ⟨846663, by decide⟩ ⟨13, 2, 0, 846663, 439409, 2489, 16384⟩
    (by decide) selected_cut_32879

theorem selected_cut_32880 : selected 8 ⟨846682, by decide⟩
    (prefixPartial 13 439410) = some ⟨13, 2, 0, 846682, 439410, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_439410_846682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439410 ⟨846682, by decide⟩ :=
  accepted_of_selected 13 439410 ⟨846682, by decide⟩ ⟨13, 2, 0, 846682, 439410, 1305, 16384⟩
    (by decide) selected_cut_32880

theorem selected_cut_32881 : selected 8 ⟨846689, by decide⟩
    (prefixPartial 13 439411) = some ⟨13, 2, 0, 846689, 439411, 729, 16384⟩ := by
  decide +kernel

theorem context_13_439411_846689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439411 ⟨846689, by decide⟩ :=
  accepted_of_selected 13 439411 ⟨846689, by decide⟩ ⟨13, 2, 0, 846689, 439411, 729, 16384⟩
    (by decide) selected_cut_32881

theorem unmarked_context_12_109852_846690 : frontier 9 ⟨846690, by decide⟩
    (prefixCache 12 109852) (prefixPartial 12 109852) = false := by
  decide +kernel

theorem node_context_12_109852_846690 : EJMOriginalGlobalDAGData.nodes 9 ⟨846690, by decide⟩ =
    .split (coordinate 12) (![⟨846633, by decide⟩,⟨846663, by decide⟩,⟨846682, by decide⟩,⟨846689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109852_846690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109852 ⟨846690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109852
    ⟨846690, by decide⟩ (by decide) (![⟨846633, by decide⟩,⟨846663, by decide⟩,⟨846682, by decide⟩,⟨846689, by decide⟩]) unmarked_context_12_109852_846690 node_context_12_109852_846690
  intro a
  fin_cases a
  · exact context_13_439408_846633
  · exact context_13_439409_846663
  · exact context_13_439410_846682
  · exact context_13_439411_846689

theorem selected_cut_32882 : selected 8 ⟨846712, by decide⟩
    (prefixPartial 13 439412) = some ⟨13, 2, 0, 846712, 439412, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_439412_846712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439412 ⟨846712, by decide⟩ :=
  accepted_of_selected 13 439412 ⟨846712, by decide⟩ ⟨13, 2, 0, 846712, 439412, 1661, 16384⟩
    (by decide) selected_cut_32882

theorem selected_cut_32883 : selected 8 ⟨846746, by decide⟩
    (prefixPartial 13 439413) = some ⟨13, 2, 0, 846746, 439413, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_439413_846746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439413 ⟨846746, by decide⟩ :=
  accepted_of_selected 13 439413 ⟨846746, by decide⟩ ⟨13, 2, 0, 846746, 439413, 2521, 16384⟩
    (by decide) selected_cut_32883

theorem selected_cut_32884 : selected 8 ⟨846773, by decide⟩
    (prefixPartial 13 439414) = some ⟨13, 2, 0, 846773, 439414, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_439414_846773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439414 ⟨846773, by decide⟩ :=
  accepted_of_selected 13 439414 ⟨846773, by decide⟩ ⟨13, 2, 0, 846773, 439414, 1477, 16384⟩
    (by decide) selected_cut_32884

theorem selected_cut_32885 : selected 8 ⟨846780, by decide⟩
    (prefixPartial 13 439415) = some ⟨13, 2, 0, 846780, 439415, 721, 16384⟩ := by
  decide +kernel

theorem context_13_439415_846780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439415 ⟨846780, by decide⟩ :=
  accepted_of_selected 13 439415 ⟨846780, by decide⟩ ⟨13, 2, 0, 846780, 439415, 721, 16384⟩
    (by decide) selected_cut_32885

theorem unmarked_context_12_109853_846781 : frontier 9 ⟨846781, by decide⟩
    (prefixCache 12 109853) (prefixPartial 12 109853) = false := by
  decide +kernel

theorem node_context_12_109853_846781 : EJMOriginalGlobalDAGData.nodes 9 ⟨846781, by decide⟩ =
    .split (coordinate 12) (![⟨846712, by decide⟩,⟨846746, by decide⟩,⟨846773, by decide⟩,⟨846780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109853_846781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109853 ⟨846781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109853
    ⟨846781, by decide⟩ (by decide) (![⟨846712, by decide⟩,⟨846746, by decide⟩,⟨846773, by decide⟩,⟨846780, by decide⟩]) unmarked_context_12_109853_846781 node_context_12_109853_846781
  intro a
  fin_cases a
  · exact context_13_439412_846712
  · exact context_13_439413_846746
  · exact context_13_439414_846773
  · exact context_13_439415_846780

theorem selected_cut_32886 : selected 8 ⟨846807, by decide⟩
    (prefixPartial 13 439416) = some ⟨13, 2, 0, 846807, 439416, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_439416_846807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439416 ⟨846807, by decide⟩ :=
  accepted_of_selected 13 439416 ⟨846807, by decide⟩ ⟨13, 2, 0, 846807, 439416, 1369, 16384⟩
    (by decide) selected_cut_32886

theorem selected_cut_32887 : selected 8 ⟨846837, by decide⟩
    (prefixPartial 13 439417) = some ⟨13, 2, 0, 846837, 439417, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_439417_846837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439417 ⟨846837, by decide⟩ :=
  accepted_of_selected 13 439417 ⟨846837, by decide⟩ ⟨13, 2, 0, 846837, 439417, 2509, 16384⟩
    (by decide) selected_cut_32887

theorem selected_cut_32888 : selected 8 ⟨846852, by decide⟩
    (prefixPartial 13 439418) = some ⟨13, 2, 0, 846852, 439418, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_439418_846852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439418 ⟨846852, by decide⟩ :=
  accepted_of_selected 13 439418 ⟨846852, by decide⟩ ⟨13, 2, 0, 846852, 439418, 1181, 16384⟩
    (by decide) selected_cut_32888

theorem selected_cut_32889 : selected 8 ⟨846859, by decide⟩
    (prefixPartial 13 439419) = some ⟨13, 2, 0, 846859, 439419, 817, 16384⟩ := by
  decide +kernel

theorem context_13_439419_846859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439419 ⟨846859, by decide⟩ :=
  accepted_of_selected 13 439419 ⟨846859, by decide⟩ ⟨13, 2, 0, 846859, 439419, 817, 16384⟩
    (by decide) selected_cut_32889

theorem unmarked_context_12_109854_846860 : frontier 9 ⟨846860, by decide⟩
    (prefixCache 12 109854) (prefixPartial 12 109854) = false := by
  decide +kernel

theorem node_context_12_109854_846860 : EJMOriginalGlobalDAGData.nodes 9 ⟨846860, by decide⟩ =
    .split (coordinate 12) (![⟨846807, by decide⟩,⟨846837, by decide⟩,⟨846852, by decide⟩,⟨846859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109854_846860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109854 ⟨846860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109854
    ⟨846860, by decide⟩ (by decide) (![⟨846807, by decide⟩,⟨846837, by decide⟩,⟨846852, by decide⟩,⟨846859, by decide⟩]) unmarked_context_12_109854_846860 node_context_12_109854_846860
  intro a
  fin_cases a
  · exact context_13_439416_846807
  · exact context_13_439417_846837
  · exact context_13_439418_846852
  · exact context_13_439419_846859

theorem selected_cut_32890 : selected 8 ⟨846888, by decide⟩
    (prefixPartial 13 439420) = some ⟨13, 2, 0, 846888, 439420, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_439420_846888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439420 ⟨846888, by decide⟩ :=
  accepted_of_selected 13 439420 ⟨846888, by decide⟩ ⟨13, 2, 0, 846888, 439420, 1605, 16384⟩
    (by decide) selected_cut_32890

theorem selected_cut_32891 : selected 8 ⟨846929, by decide⟩
    (prefixPartial 13 439421) = some ⟨13, 2, 0, 846929, 439421, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_439421_846929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439421 ⟨846929, by decide⟩ :=
  accepted_of_selected 13 439421 ⟨846929, by decide⟩ ⟨13, 2, 0, 846929, 439421, 2777, 16384⟩
    (by decide) selected_cut_32891

theorem selected_cut_32892 : selected 8 ⟨846964, by decide⟩
    (prefixPartial 13 439422) = some ⟨13, 2, 0, 846964, 439422, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_439422_846964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439422 ⟨846964, by decide⟩ :=
  accepted_of_selected 13 439422 ⟨846964, by decide⟩ ⟨13, 2, 0, 846964, 439422, 1561, 16384⟩
    (by decide) selected_cut_32892

theorem selected_cut_32893 : selected 8 ⟨846973, by decide⟩
    (prefixPartial 13 439423) = some ⟨13, 2, 0, 846973, 439423, 777, 16384⟩ := by
  decide +kernel

theorem context_13_439423_846973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439423 ⟨846973, by decide⟩ :=
  accepted_of_selected 13 439423 ⟨846973, by decide⟩ ⟨13, 2, 0, 846973, 439423, 777, 16384⟩
    (by decide) selected_cut_32893

theorem unmarked_context_12_109855_846974 : frontier 9 ⟨846974, by decide⟩
    (prefixCache 12 109855) (prefixPartial 12 109855) = false := by
  decide +kernel

theorem node_context_12_109855_846974 : EJMOriginalGlobalDAGData.nodes 9 ⟨846974, by decide⟩ =
    .split (coordinate 12) (![⟨846888, by decide⟩,⟨846929, by decide⟩,⟨846964, by decide⟩,⟨846973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109855_846974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109855 ⟨846974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109855
    ⟨846974, by decide⟩ (by decide) (![⟨846888, by decide⟩,⟨846929, by decide⟩,⟨846964, by decide⟩,⟨846973, by decide⟩]) unmarked_context_12_109855_846974 node_context_12_109855_846974
  intro a
  fin_cases a
  · exact context_13_439420_846888
  · exact context_13_439421_846929
  · exact context_13_439422_846964
  · exact context_13_439423_846973

theorem unmarked_context_11_27463_846975 : frontier 10 ⟨846975, by decide⟩
    (prefixCache 11 27463) (prefixPartial 11 27463) = false := by
  decide +kernel

theorem node_context_11_27463_846975 : EJMOriginalGlobalDAGData.nodes 10 ⟨846975, by decide⟩ =
    .split (coordinate 11) (![⟨846690, by decide⟩,⟨846781, by decide⟩,⟨846860, by decide⟩,⟨846974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27463_846975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27463 ⟨846975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27463
    ⟨846975, by decide⟩ (by decide) (![⟨846690, by decide⟩,⟨846781, by decide⟩,⟨846860, by decide⟩,⟨846974, by decide⟩]) unmarked_context_11_27463_846975 node_context_11_27463_846975
  intro a
  fin_cases a
  · exact context_12_109852_846690
  · exact context_12_109853_846781
  · exact context_12_109854_846860
  · exact context_12_109855_846974

theorem unmarked_context_10_6865_846976 : frontier 11 ⟨846976, by decide⟩
    (prefixCache 10 6865) (prefixPartial 10 6865) = false := by
  decide +kernel

theorem node_context_10_6865_846976 : EJMOriginalGlobalDAGData.nodes 11 ⟨846976, by decide⟩ =
    .split (coordinate 10) (![⟨845874, by decide⟩,⟨846165, by decide⟩,⟨846614, by decide⟩,⟨846975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6865_846976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6865 ⟨846976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6865
    ⟨846976, by decide⟩ (by decide) (![⟨845874, by decide⟩,⟨846165, by decide⟩,⟨846614, by decide⟩,⟨846975, by decide⟩]) unmarked_context_10_6865_846976 node_context_10_6865_846976
  intro a
  fin_cases a
  · exact context_11_27460_845874
  · exact context_11_27461_846165
  · exact context_11_27462_846614
  · exact context_11_27463_846975

theorem selected_cut_32894 : selected 8 ⟨846998, by decide⟩
    (prefixPartial 13 439424) = some ⟨13, 2, 0, 846998, 439424, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_439424_846998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439424 ⟨846998, by decide⟩ :=
  accepted_of_selected 13 439424 ⟨846998, by decide⟩ ⟨13, 2, 0, 846998, 439424, 1549, 16384⟩
    (by decide) selected_cut_32894

theorem selected_cut_32895 : selected 8 ⟨847026, by decide⟩
    (prefixPartial 13 439425) = some ⟨13, 2, 0, 847026, 439425, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_439425_847026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439425 ⟨847026, by decide⟩ :=
  accepted_of_selected 13 439425 ⟨847026, by decide⟩ ⟨13, 2, 0, 847026, 439425, 2365, 16384⟩
    (by decide) selected_cut_32895

theorem selected_cut_32896 : selected 8 ⟨847045, by decide⟩
    (prefixPartial 13 439426) = some ⟨13, 2, 0, 847045, 439426, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_439426_847045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439426 ⟨847045, by decide⟩ :=
  accepted_of_selected 13 439426 ⟨847045, by decide⟩ ⟨13, 2, 0, 847045, 439426, 1237, 16384⟩
    (by decide) selected_cut_32896

theorem selected_cut_32897 : selected 8 ⟨847053, by decide⟩
    (prefixPartial 13 439427) = some ⟨13, 2, 0, 847053, 439427, 789, 16384⟩ := by
  decide +kernel

theorem context_13_439427_847053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439427 ⟨847053, by decide⟩ :=
  accepted_of_selected 13 439427 ⟨847053, by decide⟩ ⟨13, 2, 0, 847053, 439427, 789, 16384⟩
    (by decide) selected_cut_32897

theorem unmarked_context_12_109856_847054 : frontier 9 ⟨847054, by decide⟩
    (prefixCache 12 109856) (prefixPartial 12 109856) = false := by
  decide +kernel

theorem node_context_12_109856_847054 : EJMOriginalGlobalDAGData.nodes 9 ⟨847054, by decide⟩ =
    .split (coordinate 12) (![⟨846998, by decide⟩,⟨847026, by decide⟩,⟨847045, by decide⟩,⟨847053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109856_847054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109856 ⟨847054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109856
    ⟨847054, by decide⟩ (by decide) (![⟨846998, by decide⟩,⟨847026, by decide⟩,⟨847045, by decide⟩,⟨847053, by decide⟩]) unmarked_context_12_109856_847054 node_context_12_109856_847054
  intro a
  fin_cases a
  · exact context_13_439424_846998
  · exact context_13_439425_847026
  · exact context_13_439426_847045
  · exact context_13_439427_847053

theorem selected_cut_32898 : selected 8 ⟨847079, by decide⟩
    (prefixPartial 13 439428) = some ⟨13, 2, 0, 847079, 439428, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_439428_847079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439428 ⟨847079, by decide⟩ :=
  accepted_of_selected 13 439428 ⟨847079, by decide⟩ ⟨13, 2, 0, 847079, 439428, 1501, 16384⟩
    (by decide) selected_cut_32898

theorem selected_cut_32899 : selected 8 ⟨847102, by decide⟩
    (prefixPartial 13 439429) = some ⟨13, 2, 0, 847102, 439429, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_439429_847102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439429 ⟨847102, by decide⟩ :=
  accepted_of_selected 13 439429 ⟨847102, by decide⟩ ⟨13, 2, 0, 847102, 439429, 2377, 16384⟩
    (by decide) selected_cut_32899

theorem selected_cut_32900 : selected 8 ⟨847127, by decide⟩
    (prefixPartial 13 439430) = some ⟨13, 2, 0, 847127, 439430, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_439430_847127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439430 ⟨847127, by decide⟩ :=
  accepted_of_selected 13 439430 ⟨847127, by decide⟩ ⟨13, 2, 0, 847127, 439430, 1285, 16384⟩
    (by decide) selected_cut_32900

theorem selected_cut_32901 : selected 8 ⟨847133, by decide⟩
    (prefixPartial 13 439431) = some ⟨13, 2, 0, 847133, 439431, 745, 16384⟩ := by
  decide +kernel

theorem context_13_439431_847133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439431 ⟨847133, by decide⟩ :=
  accepted_of_selected 13 439431 ⟨847133, by decide⟩ ⟨13, 2, 0, 847133, 439431, 745, 16384⟩
    (by decide) selected_cut_32901

theorem unmarked_context_12_109857_847134 : frontier 9 ⟨847134, by decide⟩
    (prefixCache 12 109857) (prefixPartial 12 109857) = false := by
  decide +kernel

theorem node_context_12_109857_847134 : EJMOriginalGlobalDAGData.nodes 9 ⟨847134, by decide⟩ =
    .split (coordinate 12) (![⟨847079, by decide⟩,⟨847102, by decide⟩,⟨847127, by decide⟩,⟨847133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109857_847134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109857 ⟨847134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109857
    ⟨847134, by decide⟩ (by decide) (![⟨847079, by decide⟩,⟨847102, by decide⟩,⟨847127, by decide⟩,⟨847133, by decide⟩]) unmarked_context_12_109857_847134 node_context_12_109857_847134
  intro a
  fin_cases a
  · exact context_13_439428_847079
  · exact context_13_439429_847102
  · exact context_13_439430_847127
  · exact context_13_439431_847133

theorem selected_cut_32902 : selected 8 ⟨847159, by decide⟩
    (prefixPartial 13 439432) = some ⟨13, 2, 0, 847159, 439432, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_439432_847159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439432 ⟨847159, by decide⟩ :=
  accepted_of_selected 13 439432 ⟨847159, by decide⟩ ⟨13, 2, 0, 847159, 439432, 1401, 16384⟩
    (by decide) selected_cut_32902

theorem selected_cut_32903 : selected 8 ⟨847185, by decide⟩
    (prefixPartial 13 439433) = some ⟨13, 2, 0, 847185, 439433, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_439433_847185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439433 ⟨847185, by decide⟩ :=
  accepted_of_selected 13 439433 ⟨847185, by decide⟩ ⟨13, 2, 0, 847185, 439433, 2417, 16384⟩
    (by decide) selected_cut_32903

theorem selected_cut_32904 : selected 8 ⟨847202, by decide⟩
    (prefixPartial 13 439434) = some ⟨13, 2, 0, 847202, 439434, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_439434_847202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439434 ⟨847202, by decide⟩ :=
  accepted_of_selected 13 439434 ⟨847202, by decide⟩ ⟨13, 2, 0, 847202, 439434, 1133, 16384⟩
    (by decide) selected_cut_32904

theorem selected_cut_32905 : selected 8 ⟨847211, by decide⟩
    (prefixPartial 13 439435) = some ⟨13, 2, 0, 847211, 439435, 845, 16384⟩ := by
  decide +kernel

theorem context_13_439435_847211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439435 ⟨847211, by decide⟩ :=
  accepted_of_selected 13 439435 ⟨847211, by decide⟩ ⟨13, 2, 0, 847211, 439435, 845, 16384⟩
    (by decide) selected_cut_32905

theorem unmarked_context_12_109858_847212 : frontier 9 ⟨847212, by decide⟩
    (prefixCache 12 109858) (prefixPartial 12 109858) = false := by
  decide +kernel

theorem node_context_12_109858_847212 : EJMOriginalGlobalDAGData.nodes 9 ⟨847212, by decide⟩ =
    .split (coordinate 12) (![⟨847159, by decide⟩,⟨847185, by decide⟩,⟨847202, by decide⟩,⟨847211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109858_847212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109858 ⟨847212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109858
    ⟨847212, by decide⟩ (by decide) (![⟨847159, by decide⟩,⟨847185, by decide⟩,⟨847202, by decide⟩,⟨847211, by decide⟩]) unmarked_context_12_109858_847212 node_context_12_109858_847212
  intro a
  fin_cases a
  · exact context_13_439432_847159
  · exact context_13_439433_847185
  · exact context_13_439434_847202
  · exact context_13_439435_847211

theorem selected_cut_32906 : selected 8 ⟨847243, by decide⟩
    (prefixPartial 13 439436) = some ⟨13, 2, 0, 847243, 439436, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_439436_847243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439436 ⟨847243, by decide⟩ :=
  accepted_of_selected 13 439436 ⟨847243, by decide⟩ ⟨13, 2, 0, 847243, 439436, 1645, 16384⟩
    (by decide) selected_cut_32906

theorem selected_cut_32907 : selected 8 ⟨847280, by decide⟩
    (prefixPartial 13 439437) = some ⟨13, 2, 0, 847280, 439437, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_439437_847280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439437 ⟨847280, by decide⟩ :=
  accepted_of_selected 13 439437 ⟨847280, by decide⟩ ⟨13, 2, 0, 847280, 439437, 2661, 16384⟩
    (by decide) selected_cut_32907

theorem selected_cut_32908 : selected 8 ⟨847302, by decide⟩
    (prefixPartial 13 439438) = some ⟨13, 2, 0, 847302, 439438, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_439438_847302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439438 ⟨847302, by decide⟩ :=
  accepted_of_selected 13 439438 ⟨847302, by decide⟩ ⟨13, 2, 0, 847302, 439438, 1397, 16384⟩
    (by decide) selected_cut_32908

theorem selected_cut_32909 : selected 8 ⟨847310, by decide⟩
    (prefixPartial 13 439439) = some ⟨13, 2, 0, 847310, 439439, 861, 16384⟩ := by
  decide +kernel

theorem context_13_439439_847310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439439 ⟨847310, by decide⟩ :=
  accepted_of_selected 13 439439 ⟨847310, by decide⟩ ⟨13, 2, 0, 847310, 439439, 861, 16384⟩
    (by decide) selected_cut_32909

theorem unmarked_context_12_109859_847311 : frontier 9 ⟨847311, by decide⟩
    (prefixCache 12 109859) (prefixPartial 12 109859) = false := by
  decide +kernel

theorem node_context_12_109859_847311 : EJMOriginalGlobalDAGData.nodes 9 ⟨847311, by decide⟩ =
    .split (coordinate 12) (![⟨847243, by decide⟩,⟨847280, by decide⟩,⟨847302, by decide⟩,⟨847310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109859_847311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109859 ⟨847311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109859
    ⟨847311, by decide⟩ (by decide) (![⟨847243, by decide⟩,⟨847280, by decide⟩,⟨847302, by decide⟩,⟨847310, by decide⟩]) unmarked_context_12_109859_847311 node_context_12_109859_847311
  intro a
  fin_cases a
  · exact context_13_439436_847243
  · exact context_13_439437_847280
  · exact context_13_439438_847302
  · exact context_13_439439_847310

theorem unmarked_context_11_27464_847312 : frontier 10 ⟨847312, by decide⟩
    (prefixCache 11 27464) (prefixPartial 11 27464) = false := by
  decide +kernel

theorem node_context_11_27464_847312 : EJMOriginalGlobalDAGData.nodes 10 ⟨847312, by decide⟩ =
    .split (coordinate 11) (![⟨847054, by decide⟩,⟨847134, by decide⟩,⟨847212, by decide⟩,⟨847311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27464_847312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27464 ⟨847312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27464
    ⟨847312, by decide⟩ (by decide) (![⟨847054, by decide⟩,⟨847134, by decide⟩,⟨847212, by decide⟩,⟨847311, by decide⟩]) unmarked_context_11_27464_847312 node_context_11_27464_847312
  intro a
  fin_cases a
  · exact context_12_109856_847054
  · exact context_12_109857_847134
  · exact context_12_109858_847212
  · exact context_12_109859_847311

theorem selected_cut_32910 : selected 8 ⟨847335, by decide⟩
    (prefixPartial 13 439440) = some ⟨13, 2, 0, 847335, 439440, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_439440_847335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439440 ⟨847335, by decide⟩ :=
  accepted_of_selected 13 439440 ⟨847335, by decide⟩ ⟨13, 2, 0, 847335, 439440, 1261, 16384⟩
    (by decide) selected_cut_32910

theorem selected_cut_32911 : selected 8 ⟨847360, by decide⟩
    (prefixPartial 13 439441) = some ⟨13, 2, 0, 847360, 439441, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_439441_847360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439441 ⟨847360, by decide⟩ :=
  accepted_of_selected 13 439441 ⟨847360, by decide⟩ ⟨13, 2, 0, 847360, 439441, 2277, 16384⟩
    (by decide) selected_cut_32911

theorem selected_cut_32912 : selected 8 ⟨847379, by decide⟩
    (prefixPartial 13 439442) = some ⟨13, 2, 0, 847379, 439442, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_439442_847379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439442 ⟨847379, by decide⟩ :=
  accepted_of_selected 13 439442 ⟨847379, by decide⟩ ⟨13, 2, 0, 847379, 439442, 1237, 16384⟩
    (by decide) selected_cut_32912

theorem selected_cut_32913 : selected 8 ⟨847387, by decide⟩
    (prefixPartial 13 439443) = some ⟨13, 2, 0, 847387, 439443, 849, 16384⟩ := by
  decide +kernel

theorem context_13_439443_847387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439443 ⟨847387, by decide⟩ :=
  accepted_of_selected 13 439443 ⟨847387, by decide⟩ ⟨13, 2, 0, 847387, 439443, 849, 16384⟩
    (by decide) selected_cut_32913

theorem unmarked_context_12_109860_847388 : frontier 9 ⟨847388, by decide⟩
    (prefixCache 12 109860) (prefixPartial 12 109860) = false := by
  decide +kernel

theorem node_context_12_109860_847388 : EJMOriginalGlobalDAGData.nodes 9 ⟨847388, by decide⟩ =
    .split (coordinate 12) (![⟨847335, by decide⟩,⟨847360, by decide⟩,⟨847379, by decide⟩,⟨847387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109860_847388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109860 ⟨847388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109860
    ⟨847388, by decide⟩ (by decide) (![⟨847335, by decide⟩,⟨847360, by decide⟩,⟨847379, by decide⟩,⟨847387, by decide⟩]) unmarked_context_12_109860_847388 node_context_12_109860_847388
  intro a
  fin_cases a
  · exact context_13_439440_847335
  · exact context_13_439441_847360
  · exact context_13_439442_847379
  · exact context_13_439443_847387

theorem selected_cut_32914 : selected 8 ⟨847472, by decide⟩
    (prefixPartial 13 439444) = some ⟨13, 2, 0, 847472, 439444, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_439444_847472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439444 ⟨847472, by decide⟩ :=
  accepted_of_selected 13 439444 ⟨847472, by decide⟩ ⟨13, 2, 0, 847472, 439444, 1661, 16384⟩
    (by decide) selected_cut_32914

theorem selected_cut_32915 : selected 8 ⟨847588, by decide⟩
    (prefixPartial 13 439445) = some ⟨13, 2, 0, 847588, 439445, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_439445_847588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439445 ⟨847588, by decide⟩ :=
  accepted_of_selected 13 439445 ⟨847588, by decide⟩ ⟨13, 2, 0, 847588, 439445, 2549, 16384⟩
    (by decide) selected_cut_32915

theorem selected_cut_32916 : selected 8 ⟨847675, by decide⟩
    (prefixPartial 13 439446) = some ⟨13, 2, 0, 847675, 439446, 901, 16384⟩ := by
  decide +kernel

theorem context_13_439446_847675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439446 ⟨847675, by decide⟩ :=
  accepted_of_selected 13 439446 ⟨847675, by decide⟩ ⟨13, 2, 0, 847675, 439446, 901, 16384⟩
    (by decide) selected_cut_32916

theorem selected_cut_32917 : selected 8 ⟨847690, by decide⟩
    (prefixPartial 13 439447) = some ⟨13, 2, 0, 847690, 439447, 261, 16384⟩ := by
  decide +kernel

theorem context_13_439447_847690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439447 ⟨847690, by decide⟩ :=
  accepted_of_selected 13 439447 ⟨847690, by decide⟩ ⟨13, 2, 0, 847690, 439447, 261, 16384⟩
    (by decide) selected_cut_32917

theorem unmarked_context_12_109861_847691 : frontier 9 ⟨847691, by decide⟩
    (prefixCache 12 109861) (prefixPartial 12 109861) = false := by
  decide +kernel

theorem node_context_12_109861_847691 : EJMOriginalGlobalDAGData.nodes 9 ⟨847691, by decide⟩ =
    .split (coordinate 12) (![⟨847472, by decide⟩,⟨847588, by decide⟩,⟨847675, by decide⟩,⟨847690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109861_847691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109861 ⟨847691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109861
    ⟨847691, by decide⟩ (by decide) (![⟨847472, by decide⟩,⟨847588, by decide⟩,⟨847675, by decide⟩,⟨847690, by decide⟩]) unmarked_context_12_109861_847691 node_context_12_109861_847691
  intro a
  fin_cases a
  · exact context_13_439444_847472
  · exact context_13_439445_847588
  · exact context_13_439446_847675
  · exact context_13_439447_847690

theorem selected_cut_32918 : selected 8 ⟨847716, by decide⟩
    (prefixPartial 13 439448) = some ⟨13, 2, 0, 847716, 439448, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_439448_847716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439448 ⟨847716, by decide⟩ :=
  accepted_of_selected 13 439448 ⟨847716, by decide⟩ ⟨13, 2, 0, 847716, 439448, 1081, 16384⟩
    (by decide) selected_cut_32918

theorem selected_cut_32919 : selected 8 ⟨847746, by decide⟩
    (prefixPartial 13 439449) = some ⟨13, 2, 0, 847746, 439449, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_439449_847746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439449 ⟨847746, by decide⟩ :=
  accepted_of_selected 13 439449 ⟨847746, by decide⟩ ⟨13, 2, 0, 847746, 439449, 2249, 16384⟩
    (by decide) selected_cut_32919

theorem selected_cut_32920 : selected 8 ⟨847767, by decide⟩
    (prefixPartial 13 439450) = some ⟨13, 2, 0, 847767, 439450, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_439450_847767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439450 ⟨847767, by decide⟩ :=
  accepted_of_selected 13 439450 ⟨847767, by decide⟩ ⟨13, 2, 0, 847767, 439450, 1073, 16384⟩
    (by decide) selected_cut_32920

theorem selected_cut_32921 : selected 8 ⟨847774, by decide⟩
    (prefixPartial 13 439451) = some ⟨13, 2, 0, 847774, 439451, 897, 16384⟩ := by
  decide +kernel

theorem context_13_439451_847774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439451 ⟨847774, by decide⟩ :=
  accepted_of_selected 13 439451 ⟨847774, by decide⟩ ⟨13, 2, 0, 847774, 439451, 897, 16384⟩
    (by decide) selected_cut_32921

theorem unmarked_context_12_109862_847775 : frontier 9 ⟨847775, by decide⟩
    (prefixCache 12 109862) (prefixPartial 12 109862) = false := by
  decide +kernel

theorem node_context_12_109862_847775 : EJMOriginalGlobalDAGData.nodes 9 ⟨847775, by decide⟩ =
    .split (coordinate 12) (![⟨847716, by decide⟩,⟨847746, by decide⟩,⟨847767, by decide⟩,⟨847774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109862_847775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109862 ⟨847775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109862
    ⟨847775, by decide⟩ (by decide) (![⟨847716, by decide⟩,⟨847746, by decide⟩,⟨847767, by decide⟩,⟨847774, by decide⟩]) unmarked_context_12_109862_847775 node_context_12_109862_847775
  intro a
  fin_cases a
  · exact context_13_439448_847716
  · exact context_13_439449_847746
  · exact context_13_439450_847767
  · exact context_13_439451_847774

theorem selected_cut_32922 : selected 8 ⟨847805, by decide⟩
    (prefixPartial 13 439452) = some ⟨13, 2, 0, 847805, 439452, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_439452_847805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439452 ⟨847805, by decide⟩ :=
  accepted_of_selected 13 439452 ⟨847805, by decide⟩ ⟨13, 2, 0, 847805, 439452, 1285, 16384⟩
    (by decide) selected_cut_32922

theorem selected_cut_32923 : selected 8 ⟨847840, by decide⟩
    (prefixPartial 13 439453) = some ⟨13, 2, 0, 847840, 439453, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_439453_847840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439453 ⟨847840, by decide⟩ :=
  accepted_of_selected 13 439453 ⟨847840, by decide⟩ ⟨13, 2, 0, 847840, 439453, 2625, 16384⟩
    (by decide) selected_cut_32923

theorem selected_cut_32924 : selected 8 ⟨847876, by decide⟩
    (prefixPartial 13 439454) = some ⟨13, 2, 0, 847876, 439454, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_439454_847876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439454 ⟨847876, by decide⟩ :=
  accepted_of_selected 13 439454 ⟨847876, by decide⟩ ⟨13, 2, 0, 847876, 439454, 1489, 16384⟩
    (by decide) selected_cut_32924

theorem selected_cut_32925 : selected 8 ⟨847885, by decide⟩
    (prefixPartial 13 439455) = some ⟨13, 2, 0, 847885, 439455, 845, 16384⟩ := by
  decide +kernel

theorem context_13_439455_847885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439455 ⟨847885, by decide⟩ :=
  accepted_of_selected 13 439455 ⟨847885, by decide⟩ ⟨13, 2, 0, 847885, 439455, 845, 16384⟩
    (by decide) selected_cut_32925

theorem unmarked_context_12_109863_847886 : frontier 9 ⟨847886, by decide⟩
    (prefixCache 12 109863) (prefixPartial 12 109863) = false := by
  decide +kernel

theorem node_context_12_109863_847886 : EJMOriginalGlobalDAGData.nodes 9 ⟨847886, by decide⟩ =
    .split (coordinate 12) (![⟨847805, by decide⟩,⟨847840, by decide⟩,⟨847876, by decide⟩,⟨847885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109863_847886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109863 ⟨847886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109863
    ⟨847886, by decide⟩ (by decide) (![⟨847805, by decide⟩,⟨847840, by decide⟩,⟨847876, by decide⟩,⟨847885, by decide⟩]) unmarked_context_12_109863_847886 node_context_12_109863_847886
  intro a
  fin_cases a
  · exact context_13_439452_847805
  · exact context_13_439453_847840
  · exact context_13_439454_847876
  · exact context_13_439455_847885

theorem unmarked_context_11_27465_847887 : frontier 10 ⟨847887, by decide⟩
    (prefixCache 11 27465) (prefixPartial 11 27465) = false := by
  decide +kernel

theorem node_context_11_27465_847887 : EJMOriginalGlobalDAGData.nodes 10 ⟨847887, by decide⟩ =
    .split (coordinate 11) (![⟨847388, by decide⟩,⟨847691, by decide⟩,⟨847775, by decide⟩,⟨847886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27465_847887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27465 ⟨847887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27465
    ⟨847887, by decide⟩ (by decide) (![⟨847388, by decide⟩,⟨847691, by decide⟩,⟨847775, by decide⟩,⟨847886, by decide⟩]) unmarked_context_11_27465_847887 node_context_11_27465_847887
  intro a
  fin_cases a
  · exact context_12_109860_847388
  · exact context_12_109861_847691
  · exact context_12_109862_847775
  · exact context_12_109863_847886

theorem selected_cut_32926 : selected 8 ⟨847907, by decide⟩
    (prefixPartial 13 439456) = some ⟨13, 2, 0, 847907, 439456, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_439456_847907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439456 ⟨847907, by decide⟩ :=
  accepted_of_selected 13 439456 ⟨847907, by decide⟩ ⟨13, 2, 0, 847907, 439456, 1033, 16384⟩
    (by decide) selected_cut_32926

theorem selected_cut_32927 : selected 8 ⟨847934, by decide⟩
    (prefixPartial 13 439457) = some ⟨13, 2, 0, 847934, 439457, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_439457_847934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439457 ⟨847934, by decide⟩ :=
  accepted_of_selected 13 439457 ⟨847934, by decide⟩ ⟨13, 2, 0, 847934, 439457, 2345, 16384⟩
    (by decide) selected_cut_32927

theorem selected_cut_32928 : selected 8 ⟨847961, by decide⟩
    (prefixPartial 13 439458) = some ⟨13, 2, 0, 847961, 439458, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_439458_847961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439458 ⟨847961, by decide⟩ :=
  accepted_of_selected 13 439458 ⟨847961, by decide⟩ ⟨13, 2, 0, 847961, 439458, 1457, 16384⟩
    (by decide) selected_cut_32928

theorem selected_cut_32929 : selected 8 ⟨847966, by decide⟩
    (prefixPartial 13 439459) = some ⟨13, 2, 0, 847966, 439459, 813, 16384⟩ := by
  decide +kernel

theorem context_13_439459_847966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439459 ⟨847966, by decide⟩ :=
  accepted_of_selected 13 439459 ⟨847966, by decide⟩ ⟨13, 2, 0, 847966, 439459, 813, 16384⟩
    (by decide) selected_cut_32929

theorem unmarked_context_12_109864_847967 : frontier 9 ⟨847967, by decide⟩
    (prefixCache 12 109864) (prefixPartial 12 109864) = false := by
  decide +kernel

theorem node_context_12_109864_847967 : EJMOriginalGlobalDAGData.nodes 9 ⟨847967, by decide⟩ =
    .split (coordinate 12) (![⟨847907, by decide⟩,⟨847934, by decide⟩,⟨847961, by decide⟩,⟨847966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109864_847967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109864 ⟨847967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109864
    ⟨847967, by decide⟩ (by decide) (![⟨847907, by decide⟩,⟨847934, by decide⟩,⟨847961, by decide⟩,⟨847966, by decide⟩]) unmarked_context_12_109864_847967 node_context_12_109864_847967
  intro a
  fin_cases a
  · exact context_13_439456_847907
  · exact context_13_439457_847934
  · exact context_13_439458_847961
  · exact context_13_439459_847966

theorem selected_cut_32930 : selected 8 ⟨847980, by decide⟩
    (prefixPartial 13 439460) = some ⟨13, 2, 0, 847980, 439460, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_439460_847980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439460 ⟨847980, by decide⟩ :=
  accepted_of_selected 13 439460 ⟨847980, by decide⟩ ⟨13, 2, 0, 847980, 439460, 1117, 16384⟩
    (by decide) selected_cut_32930

theorem selected_cut_32931 : selected 8 ⟨848004, by decide⟩
    (prefixPartial 13 439461) = some ⟨13, 2, 0, 848004, 439461, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_439461_848004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439461 ⟨848004, by decide⟩ :=
  accepted_of_selected 13 439461 ⟨848004, by decide⟩ ⟨13, 2, 0, 848004, 439461, 2253, 16384⟩
    (by decide) selected_cut_32931

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
