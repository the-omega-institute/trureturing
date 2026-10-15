/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover237
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_22850 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76040) = some ⟨12, 1, 0, 448748, 76040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76040_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76040 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76040 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76040, 1, 65536⟩
    (by decide) selected_cut_22850

theorem selected_cut_22851 : selected 8 ⟨580489, by decide⟩
    (prefixPartial 13 304164) = some ⟨13, 2, 0, 580489, 304164, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_304164_580489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304164 ⟨580489, by decide⟩ :=
  accepted_of_selected 13 304164 ⟨580489, by decide⟩ ⟨13, 2, 0, 580489, 304164, 2593, 16384⟩
    (by decide) selected_cut_22851

theorem selected_cut_22852 : selected 8 ⟨580517, by decide⟩
    (prefixPartial 13 304165) = some ⟨13, 2, 0, 580517, 304165, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_304165_580517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304165 ⟨580517, by decide⟩ :=
  accepted_of_selected 13 304165 ⟨580517, by decide⟩ ⟨13, 2, 0, 580517, 304165, 2021, 16384⟩
    (by decide) selected_cut_22852

theorem selected_cut_22853 : selected 8 ⟨580537, by decide⟩
    (prefixPartial 13 304166) = some ⟨13, 2, 0, 580537, 304166, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_304166_580537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304166 ⟨580537, by decide⟩ :=
  accepted_of_selected 13 304166 ⟨580537, by decide⟩ ⟨13, 2, 0, 580537, 304166, 1669, 16384⟩
    (by decide) selected_cut_22853

theorem selected_cut_22854 : selected 8 ⟨580544, by decide⟩
    (prefixPartial 13 304167) = some ⟨13, 2, 0, 580544, 304167, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_304167_580544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304167 ⟨580544, by decide⟩ :=
  accepted_of_selected 13 304167 ⟨580544, by decide⟩ ⟨13, 2, 0, 580544, 304167, 1097, 16384⟩
    (by decide) selected_cut_22854

theorem unmarked_context_12_76041_580545 : frontier 9 ⟨580545, by decide⟩
    (prefixCache 12 76041) (prefixPartial 12 76041) = false := by
  decide +kernel

theorem node_context_12_76041_580545 : EJMOriginalGlobalDAGData.nodes 9 ⟨580545, by decide⟩ =
    .split (coordinate 12) (![⟨580489, by decide⟩,⟨580517, by decide⟩,⟨580537, by decide⟩,⟨580544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76041_580545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76041 ⟨580545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76041
    ⟨580545, by decide⟩ (by decide) (![⟨580489, by decide⟩,⟨580517, by decide⟩,⟨580537, by decide⟩,⟨580544, by decide⟩]) unmarked_context_12_76041_580545 node_context_12_76041_580545
  intro a
  fin_cases a
  · exact context_13_304164_580489
  · exact context_13_304165_580517
  · exact context_13_304166_580537
  · exact context_13_304167_580544

theorem selected_cut_22855 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 76042) = some ⟨12, 1, 0, 524302, 76042, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76042_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76042 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 76042 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 76042, 1, 65536⟩
    (by decide) selected_cut_22855

theorem selected_cut_22856 : selected 8 ⟨580587, by decide⟩
    (prefixPartial 13 304172) = some ⟨13, 2, 0, 580587, 304172, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_304172_580587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304172 ⟨580587, by decide⟩ :=
  accepted_of_selected 13 304172 ⟨580587, by decide⟩ ⟨13, 2, 0, 580587, 304172, 2441, 16384⟩
    (by decide) selected_cut_22856

theorem selected_cut_22857 : selected 8 ⟨580613, by decide⟩
    (prefixPartial 13 304173) = some ⟨13, 2, 0, 580613, 304173, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_304173_580613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304173 ⟨580613, by decide⟩ :=
  accepted_of_selected 13 304173 ⟨580613, by decide⟩ ⟨13, 2, 0, 580613, 304173, 2521, 16384⟩
    (by decide) selected_cut_22857

theorem selected_cut_22858 : selected 8 ⟨580630, by decide⟩
    (prefixPartial 13 304174) = some ⟨13, 2, 0, 580630, 304174, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_304174_580630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304174 ⟨580630, by decide⟩ :=
  accepted_of_selected 13 304174 ⟨580630, by decide⟩ ⟨13, 2, 0, 580630, 304174, 1805, 16384⟩
    (by decide) selected_cut_22858

theorem selected_cut_22859 : selected 8 ⟨580634, by decide⟩
    (prefixPartial 13 304175) = some ⟨13, 2, 0, 580634, 304175, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_304175_580634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304175 ⟨580634, by decide⟩ :=
  accepted_of_selected 13 304175 ⟨580634, by decide⟩ ⟨13, 2, 0, 580634, 304175, 1061, 16384⟩
    (by decide) selected_cut_22859

theorem unmarked_context_12_76043_580635 : frontier 9 ⟨580635, by decide⟩
    (prefixCache 12 76043) (prefixPartial 12 76043) = false := by
  decide +kernel

theorem node_context_12_76043_580635 : EJMOriginalGlobalDAGData.nodes 9 ⟨580635, by decide⟩ =
    .split (coordinate 12) (![⟨580587, by decide⟩,⟨580613, by decide⟩,⟨580630, by decide⟩,⟨580634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76043_580635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76043 ⟨580635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76043
    ⟨580635, by decide⟩ (by decide) (![⟨580587, by decide⟩,⟨580613, by decide⟩,⟨580630, by decide⟩,⟨580634, by decide⟩]) unmarked_context_12_76043_580635 node_context_12_76043_580635
  intro a
  fin_cases a
  · exact context_13_304172_580587
  · exact context_13_304173_580613
  · exact context_13_304174_580630
  · exact context_13_304175_580634

theorem unmarked_context_11_19010_580636 : frontier 10 ⟨580636, by decide⟩
    (prefixCache 11 19010) (prefixPartial 11 19010) = false := by
  decide +kernel

theorem node_context_11_19010_580636 : EJMOriginalGlobalDAGData.nodes 10 ⟨580636, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨580545, by decide⟩,⟨524302, by decide⟩,⟨580635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19010_580636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19010 ⟨580636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19010
    ⟨580636, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨580545, by decide⟩,⟨524302, by decide⟩,⟨580635, by decide⟩]) unmarked_context_11_19010_580636 node_context_11_19010_580636
  intro a
  fin_cases a
  · exact context_12_76040_448748
  · exact context_12_76041_580545
  · exact context_12_76042_524302
  · exact context_12_76043_580635

theorem selected_cut_22860 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76044) = some ⟨12, 1, 0, 448748, 76044, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76044_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76044 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76044 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76044, 1, 65536⟩
    (by decide) selected_cut_22860

theorem selected_cut_22861 : selected 8 ⟨580674, by decide⟩
    (prefixPartial 13 304180) = some ⟨13, 2, 0, 580674, 304180, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_304180_580674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304180 ⟨580674, by decide⟩ :=
  accepted_of_selected 13 304180 ⟨580674, by decide⟩ ⟨13, 2, 0, 580674, 304180, 2353, 16384⟩
    (by decide) selected_cut_22861

theorem selected_cut_22862 : selected 8 ⟨580703, by decide⟩
    (prefixPartial 13 304181) = some ⟨13, 2, 0, 580703, 304181, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_304181_580703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304181 ⟨580703, by decide⟩ :=
  accepted_of_selected 13 304181 ⟨580703, by decide⟩ ⟨13, 2, 0, 580703, 304181, 2433, 16384⟩
    (by decide) selected_cut_22862

theorem selected_cut_22863 : selected 8 ⟨580720, by decide⟩
    (prefixPartial 13 304182) = some ⟨13, 2, 0, 580720, 304182, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_304182_580720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304182 ⟨580720, by decide⟩ :=
  accepted_of_selected 13 304182 ⟨580720, by decide⟩ ⟨13, 2, 0, 580720, 304182, 1865, 16384⟩
    (by decide) selected_cut_22863

theorem selected_cut_22864 : selected 8 ⟨580723, by decide⟩
    (prefixPartial 13 304183) = some ⟨13, 2, 0, 580723, 304183, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_304183_580723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304183 ⟨580723, by decide⟩ :=
  accepted_of_selected 13 304183 ⟨580723, by decide⟩ ⟨13, 2, 0, 580723, 304183, 1065, 16384⟩
    (by decide) selected_cut_22864

theorem unmarked_context_12_76045_580724 : frontier 9 ⟨580724, by decide⟩
    (prefixCache 12 76045) (prefixPartial 12 76045) = false := by
  decide +kernel

theorem node_context_12_76045_580724 : EJMOriginalGlobalDAGData.nodes 9 ⟨580724, by decide⟩ =
    .split (coordinate 12) (![⟨580674, by decide⟩,⟨580703, by decide⟩,⟨580720, by decide⟩,⟨580723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76045_580724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76045 ⟨580724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76045
    ⟨580724, by decide⟩ (by decide) (![⟨580674, by decide⟩,⟨580703, by decide⟩,⟨580720, by decide⟩,⟨580723, by decide⟩]) unmarked_context_12_76045_580724 node_context_12_76045_580724
  intro a
  fin_cases a
  · exact context_13_304180_580674
  · exact context_13_304181_580703
  · exact context_13_304182_580720
  · exact context_13_304183_580723

theorem selected_cut_22865 : selected 9 ⟨573823, by decide⟩
    (prefixPartial 12 76046) = some ⟨12, 1, 0, 573823, 76046, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76046_573823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76046 ⟨573823, by decide⟩ :=
  accepted_of_selected 12 76046 ⟨573823, by decide⟩ ⟨12, 1, 0, 573823, 76046, 1, 65536⟩
    (by decide) selected_cut_22865

theorem selected_cut_22866 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 76047) = some ⟨12, 1, 0, 518278, 76047, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76047_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76047 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 76047 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 76047, 1, 65536⟩
    (by decide) selected_cut_22866

theorem unmarked_context_11_19011_580725 : frontier 10 ⟨580725, by decide⟩
    (prefixCache 11 19011) (prefixPartial 11 19011) = false := by
  decide +kernel

theorem node_context_11_19011_580725 : EJMOriginalGlobalDAGData.nodes 10 ⟨580725, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨580724, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19011_580725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19011 ⟨580725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19011
    ⟨580725, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨580724, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_19011_580725 node_context_11_19011_580725
  intro a
  fin_cases a
  · exact context_12_76044_448748
  · exact context_12_76045_580724
  · exact context_12_76046_573823
  · exact context_12_76047_518278

theorem unmarked_context_10_4752_580726 : frontier 11 ⟨580726, by decide⟩
    (prefixCache 10 4752) (prefixPartial 10 4752) = false := by
  decide +kernel

theorem node_context_10_4752_580726 : EJMOriginalGlobalDAGData.nodes 11 ⟨580726, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨580433, by decide⟩,⟨580636, by decide⟩,⟨580725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4752_580726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4752 ⟨580726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4752
    ⟨580726, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨580433, by decide⟩,⟨580636, by decide⟩,⟨580725, by decide⟩]) unmarked_context_10_4752_580726 node_context_10_4752_580726
  intro a
  fin_cases a
  · exact context_11_19008_434745
  · exact context_11_19009_580433
  · exact context_11_19010_580636
  · exact context_11_19011_580725

theorem selected_cut_22867 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76048) = some ⟨12, 1, 0, 435160, 76048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76048_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76048 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76048 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76048, 1, 65536⟩
    (by decide) selected_cut_22867

theorem selected_cut_22868 : selected 8 ⟨580756, by decide⟩
    (prefixPartial 13 304196) = some ⟨13, 2, 0, 580756, 304196, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_304196_580756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304196 ⟨580756, by decide⟩ :=
  accepted_of_selected 13 304196 ⟨580756, by decide⟩ ⟨13, 2, 0, 580756, 304196, 1693, 16384⟩
    (by decide) selected_cut_22868

theorem selected_cut_22869 : selected 8 ⟨580780, by decide⟩
    (prefixPartial 13 304197) = some ⟨13, 2, 0, 580780, 304197, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_304197_580780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304197 ⟨580780, by decide⟩ :=
  accepted_of_selected 13 304197 ⟨580780, by decide⟩ ⟨13, 2, 0, 580780, 304197, 1957, 16384⟩
    (by decide) selected_cut_22869

theorem selected_cut_22870 : selected 8 ⟨580795, by decide⟩
    (prefixPartial 13 304198) = some ⟨13, 2, 0, 580795, 304198, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_304198_580795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304198 ⟨580795, by decide⟩ :=
  accepted_of_selected 13 304198 ⟨580795, by decide⟩ ⟨13, 2, 0, 580795, 304198, 1405, 16384⟩
    (by decide) selected_cut_22870

theorem selected_cut_22871 : selected 8 ⟨580799, by decide⟩
    (prefixPartial 13 304199) = some ⟨13, 2, 0, 580799, 304199, 805, 16384⟩ := by
  decide +kernel

theorem context_13_304199_580799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304199 ⟨580799, by decide⟩ :=
  accepted_of_selected 13 304199 ⟨580799, by decide⟩ ⟨13, 2, 0, 580799, 304199, 805, 16384⟩
    (by decide) selected_cut_22871

theorem unmarked_context_12_76049_580800 : frontier 9 ⟨580800, by decide⟩
    (prefixCache 12 76049) (prefixPartial 12 76049) = false := by
  decide +kernel

theorem node_context_12_76049_580800 : EJMOriginalGlobalDAGData.nodes 9 ⟨580800, by decide⟩ =
    .split (coordinate 12) (![⟨580756, by decide⟩,⟨580780, by decide⟩,⟨580795, by decide⟩,⟨580799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76049_580800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76049 ⟨580800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76049
    ⟨580800, by decide⟩ (by decide) (![⟨580756, by decide⟩,⟨580780, by decide⟩,⟨580795, by decide⟩,⟨580799, by decide⟩]) unmarked_context_12_76049_580800 node_context_12_76049_580800
  intro a
  fin_cases a
  · exact context_13_304196_580756
  · exact context_13_304197_580780
  · exact context_13_304198_580795
  · exact context_13_304199_580799

theorem selected_cut_22872 : selected 8 ⟨580829, by decide⟩
    (prefixPartial 13 304200) = some ⟨13, 2, 0, 580829, 304200, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_304200_580829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304200 ⟨580829, by decide⟩ :=
  accepted_of_selected 13 304200 ⟨580829, by decide⟩ ⟨13, 2, 0, 580829, 304200, 1809, 16384⟩
    (by decide) selected_cut_22872

theorem selected_cut_22873 : selected 8 ⟨580856, by decide⟩
    (prefixPartial 13 304201) = some ⟨13, 2, 0, 580856, 304201, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_304201_580856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304201 ⟨580856, by decide⟩ :=
  accepted_of_selected 13 304201 ⟨580856, by decide⟩ ⟨13, 2, 0, 580856, 304201, 2317, 16384⟩
    (by decide) selected_cut_22873

theorem selected_cut_22874 : selected 8 ⟨580874, by decide⟩
    (prefixPartial 13 304202) = some ⟨13, 2, 0, 580874, 304202, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_304202_580874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304202 ⟨580874, by decide⟩ :=
  accepted_of_selected 13 304202 ⟨580874, by decide⟩ ⟨13, 2, 0, 580874, 304202, 1637, 16384⟩
    (by decide) selected_cut_22874

theorem selected_cut_22875 : selected 8 ⟨580880, by decide⟩
    (prefixPartial 13 304203) = some ⟨13, 2, 0, 580880, 304203, 921, 16384⟩ := by
  decide +kernel

theorem context_13_304203_580880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304203 ⟨580880, by decide⟩ :=
  accepted_of_selected 13 304203 ⟨580880, by decide⟩ ⟨13, 2, 0, 580880, 304203, 921, 16384⟩
    (by decide) selected_cut_22875

theorem unmarked_context_12_76050_580881 : frontier 9 ⟨580881, by decide⟩
    (prefixCache 12 76050) (prefixPartial 12 76050) = false := by
  decide +kernel

theorem node_context_12_76050_580881 : EJMOriginalGlobalDAGData.nodes 9 ⟨580881, by decide⟩ =
    .split (coordinate 12) (![⟨580829, by decide⟩,⟨580856, by decide⟩,⟨580874, by decide⟩,⟨580880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76050_580881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76050 ⟨580881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76050
    ⟨580881, by decide⟩ (by decide) (![⟨580829, by decide⟩,⟨580856, by decide⟩,⟨580874, by decide⟩,⟨580880, by decide⟩]) unmarked_context_12_76050_580881 node_context_12_76050_580881
  intro a
  fin_cases a
  · exact context_13_304200_580829
  · exact context_13_304201_580856
  · exact context_13_304202_580874
  · exact context_13_304203_580880

theorem selected_cut_22876 : selected 8 ⟨580909, by decide⟩
    (prefixPartial 13 304204) = some ⟨13, 2, 0, 580909, 304204, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_304204_580909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304204 ⟨580909, by decide⟩ :=
  accepted_of_selected 13 304204 ⟨580909, by decide⟩ ⟨13, 2, 0, 580909, 304204, 1889, 16384⟩
    (by decide) selected_cut_22876

theorem selected_cut_22877 : selected 8 ⟨580935, by decide⟩
    (prefixPartial 13 304205) = some ⟨13, 2, 0, 580935, 304205, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_304205_580935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304205 ⟨580935, by decide⟩ :=
  accepted_of_selected 13 304205 ⟨580935, by decide⟩ ⟨13, 2, 0, 580935, 304205, 2465, 16384⟩
    (by decide) selected_cut_22877

theorem selected_cut_22878 : selected 8 ⟨580954, by decide⟩
    (prefixPartial 13 304206) = some ⟨13, 2, 0, 580954, 304206, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_304206_580954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304206 ⟨580954, by decide⟩ :=
  accepted_of_selected 13 304206 ⟨580954, by decide⟩ ⟨13, 2, 0, 580954, 304206, 1565, 16384⟩
    (by decide) selected_cut_22878

theorem selected_cut_22879 : selected 8 ⟨580959, by decide⟩
    (prefixPartial 13 304207) = some ⟨13, 2, 0, 580959, 304207, 825, 16384⟩ := by
  decide +kernel

theorem context_13_304207_580959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304207 ⟨580959, by decide⟩ :=
  accepted_of_selected 13 304207 ⟨580959, by decide⟩ ⟨13, 2, 0, 580959, 304207, 825, 16384⟩
    (by decide) selected_cut_22879

theorem unmarked_context_12_76051_580960 : frontier 9 ⟨580960, by decide⟩
    (prefixCache 12 76051) (prefixPartial 12 76051) = false := by
  decide +kernel

theorem node_context_12_76051_580960 : EJMOriginalGlobalDAGData.nodes 9 ⟨580960, by decide⟩ =
    .split (coordinate 12) (![⟨580909, by decide⟩,⟨580935, by decide⟩,⟨580954, by decide⟩,⟨580959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76051_580960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76051 ⟨580960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76051
    ⟨580960, by decide⟩ (by decide) (![⟨580909, by decide⟩,⟨580935, by decide⟩,⟨580954, by decide⟩,⟨580959, by decide⟩]) unmarked_context_12_76051_580960 node_context_12_76051_580960
  intro a
  fin_cases a
  · exact context_13_304204_580909
  · exact context_13_304205_580935
  · exact context_13_304206_580954
  · exact context_13_304207_580959

theorem unmarked_context_11_19012_580961 : frontier 10 ⟨580961, by decide⟩
    (prefixCache 11 19012) (prefixPartial 11 19012) = false := by
  decide +kernel

theorem node_context_11_19012_580961 : EJMOriginalGlobalDAGData.nodes 10 ⟨580961, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨580800, by decide⟩,⟨580881, by decide⟩,⟨580960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19012_580961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19012 ⟨580961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19012
    ⟨580961, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨580800, by decide⟩,⟨580881, by decide⟩,⟨580960, by decide⟩]) unmarked_context_11_19012_580961 node_context_11_19012_580961
  intro a
  fin_cases a
  · exact context_12_76048_435160
  · exact context_12_76049_580800
  · exact context_12_76050_580881
  · exact context_12_76051_580960

theorem selected_cut_22880 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76052) = some ⟨12, 1, 0, 435160, 76052, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76052_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76052 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76052 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76052, 1, 65536⟩
    (by decide) selected_cut_22880

theorem selected_cut_22881 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 76053) = some ⟨12, 1, 0, 439069, 76053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76053_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76053 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 76053 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 76053, 1, 65536⟩
    (by decide) selected_cut_22881

theorem selected_cut_22882 : selected 8 ⟨580993, by decide⟩
    (prefixPartial 13 304216) = some ⟨13, 2, 0, 580993, 304216, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_304216_580993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304216 ⟨580993, by decide⟩ :=
  accepted_of_selected 13 304216 ⟨580993, by decide⟩ ⟨13, 2, 0, 580993, 304216, 1721, 16384⟩
    (by decide) selected_cut_22882

theorem selected_cut_22883 : selected 8 ⟨581015, by decide⟩
    (prefixPartial 13 304217) = some ⟨13, 2, 0, 581015, 304217, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_304217_581015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304217 ⟨581015, by decide⟩ :=
  accepted_of_selected 13 304217 ⟨581015, by decide⟩ ⟨13, 2, 0, 581015, 304217, 2249, 16384⟩
    (by decide) selected_cut_22883

theorem selected_cut_22884 : selected 8 ⟨581033, by decide⟩
    (prefixPartial 13 304218) = some ⟨13, 2, 0, 581033, 304218, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_304218_581033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304218 ⟨581033, by decide⟩ :=
  accepted_of_selected 13 304218 ⟨581033, by decide⟩ ⟨13, 2, 0, 581033, 304218, 1429, 16384⟩
    (by decide) selected_cut_22884

theorem selected_cut_22885 : selected 8 ⟨581039, by decide⟩
    (prefixPartial 13 304219) = some ⟨13, 2, 0, 581039, 304219, 969, 16384⟩ := by
  decide +kernel

theorem context_13_304219_581039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304219 ⟨581039, by decide⟩ :=
  accepted_of_selected 13 304219 ⟨581039, by decide⟩ ⟨13, 2, 0, 581039, 304219, 969, 16384⟩
    (by decide) selected_cut_22885

theorem unmarked_context_12_76054_581040 : frontier 9 ⟨581040, by decide⟩
    (prefixCache 12 76054) (prefixPartial 12 76054) = false := by
  decide +kernel

theorem node_context_12_76054_581040 : EJMOriginalGlobalDAGData.nodes 9 ⟨581040, by decide⟩ =
    .split (coordinate 12) (![⟨580993, by decide⟩,⟨581015, by decide⟩,⟨581033, by decide⟩,⟨581039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76054_581040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76054 ⟨581040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76054
    ⟨581040, by decide⟩ (by decide) (![⟨580993, by decide⟩,⟨581015, by decide⟩,⟨581033, by decide⟩,⟨581039, by decide⟩]) unmarked_context_12_76054_581040 node_context_12_76054_581040
  intro a
  fin_cases a
  · exact context_13_304216_580993
  · exact context_13_304217_581015
  · exact context_13_304218_581033
  · exact context_13_304219_581039

theorem selected_cut_22886 : selected 8 ⟨581073, by decide⟩
    (prefixPartial 13 304220) = some ⟨13, 2, 0, 581073, 304220, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_304220_581073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304220 ⟨581073, by decide⟩ :=
  accepted_of_selected 13 304220 ⟨581073, by decide⟩ ⟨13, 2, 0, 581073, 304220, 1809, 16384⟩
    (by decide) selected_cut_22886

theorem selected_cut_22887 : selected 8 ⟨581098, by decide⟩
    (prefixPartial 13 304221) = some ⟨13, 2, 0, 581098, 304221, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_304221_581098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304221 ⟨581098, by decide⟩ :=
  accepted_of_selected 13 304221 ⟨581098, by decide⟩ ⟨13, 2, 0, 581098, 304221, 2389, 16384⟩
    (by decide) selected_cut_22887

theorem selected_cut_22888 : selected 8 ⟨581117, by decide⟩
    (prefixPartial 13 304222) = some ⟨13, 2, 0, 581117, 304222, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_304222_581117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304222 ⟨581117, by decide⟩ :=
  accepted_of_selected 13 304222 ⟨581117, by decide⟩ ⟨13, 2, 0, 581117, 304222, 1501, 16384⟩
    (by decide) selected_cut_22888

theorem selected_cut_22889 : selected 8 ⟨581123, by decide⟩
    (prefixPartial 13 304223) = some ⟨13, 2, 0, 581123, 304223, 797, 16384⟩ := by
  decide +kernel

theorem context_13_304223_581123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304223 ⟨581123, by decide⟩ :=
  accepted_of_selected 13 304223 ⟨581123, by decide⟩ ⟨13, 2, 0, 581123, 304223, 797, 16384⟩
    (by decide) selected_cut_22889

theorem unmarked_context_12_76055_581124 : frontier 9 ⟨581124, by decide⟩
    (prefixCache 12 76055) (prefixPartial 12 76055) = false := by
  decide +kernel

theorem node_context_12_76055_581124 : EJMOriginalGlobalDAGData.nodes 9 ⟨581124, by decide⟩ =
    .split (coordinate 12) (![⟨581073, by decide⟩,⟨581098, by decide⟩,⟨581117, by decide⟩,⟨581123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76055_581124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76055 ⟨581124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76055
    ⟨581124, by decide⟩ (by decide) (![⟨581073, by decide⟩,⟨581098, by decide⟩,⟨581117, by decide⟩,⟨581123, by decide⟩]) unmarked_context_12_76055_581124 node_context_12_76055_581124
  intro a
  fin_cases a
  · exact context_13_304220_581073
  · exact context_13_304221_581098
  · exact context_13_304222_581117
  · exact context_13_304223_581123

theorem unmarked_context_11_19013_581125 : frontier 10 ⟨581125, by decide⟩
    (prefixCache 11 19013) (prefixPartial 11 19013) = false := by
  decide +kernel

theorem node_context_11_19013_581125 : EJMOriginalGlobalDAGData.nodes 10 ⟨581125, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨439069, by decide⟩,⟨581040, by decide⟩,⟨581124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19013_581125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19013 ⟨581125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19013
    ⟨581125, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨439069, by decide⟩,⟨581040, by decide⟩,⟨581124, by decide⟩]) unmarked_context_11_19013_581125 node_context_11_19013_581125
  intro a
  fin_cases a
  · exact context_12_76052_435160
  · exact context_12_76053_439069
  · exact context_12_76054_581040
  · exact context_12_76055_581124

theorem selected_cut_22890 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 76056) = some ⟨12, 1, 0, 449505, 76056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76056_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76056 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 76056 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 76056, 1, 65536⟩
    (by decide) selected_cut_22890

theorem selected_cut_22891 : selected 8 ⟨581149, by decide⟩
    (prefixPartial 13 304228) = some ⟨13, 2, 0, 581149, 304228, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_304228_581149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304228 ⟨581149, by decide⟩ :=
  accepted_of_selected 13 304228 ⟨581149, by decide⟩ ⟨13, 2, 0, 581149, 304228, 1393, 16384⟩
    (by decide) selected_cut_22891

theorem selected_cut_22892 : selected 8 ⟨581172, by decide⟩
    (prefixPartial 13 304229) = some ⟨13, 2, 0, 581172, 304229, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_304229_581172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304229 ⟨581172, by decide⟩ :=
  accepted_of_selected 13 304229 ⟨581172, by decide⟩ ⟨13, 2, 0, 581172, 304229, 1693, 16384⟩
    (by decide) selected_cut_22892

theorem selected_cut_22893 : selected 8 ⟨581189, by decide⟩
    (prefixPartial 13 304230) = some ⟨13, 2, 0, 581189, 304230, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_304230_581189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304230 ⟨581189, by decide⟩ :=
  accepted_of_selected 13 304230 ⟨581189, by decide⟩ ⟨13, 2, 0, 581189, 304230, 1373, 16384⟩
    (by decide) selected_cut_22893

theorem selected_cut_22894 : selected 8 ⟨581194, by decide⟩
    (prefixPartial 13 304231) = some ⟨13, 2, 0, 581194, 304231, 881, 16384⟩ := by
  decide +kernel

theorem context_13_304231_581194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304231 ⟨581194, by decide⟩ :=
  accepted_of_selected 13 304231 ⟨581194, by decide⟩ ⟨13, 2, 0, 581194, 304231, 881, 16384⟩
    (by decide) selected_cut_22894

theorem unmarked_context_12_76057_581195 : frontier 9 ⟨581195, by decide⟩
    (prefixCache 12 76057) (prefixPartial 12 76057) = false := by
  decide +kernel

theorem node_context_12_76057_581195 : EJMOriginalGlobalDAGData.nodes 9 ⟨581195, by decide⟩ =
    .split (coordinate 12) (![⟨581149, by decide⟩,⟨581172, by decide⟩,⟨581189, by decide⟩,⟨581194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76057_581195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76057 ⟨581195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76057
    ⟨581195, by decide⟩ (by decide) (![⟨581149, by decide⟩,⟨581172, by decide⟩,⟨581189, by decide⟩,⟨581194, by decide⟩]) unmarked_context_12_76057_581195 node_context_12_76057_581195
  intro a
  fin_cases a
  · exact context_13_304228_581149
  · exact context_13_304229_581172
  · exact context_13_304230_581189
  · exact context_13_304231_581194

theorem selected_cut_22895 : selected 8 ⟨581216, by decide⟩
    (prefixPartial 13 304232) = some ⟨13, 2, 0, 581216, 304232, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_304232_581216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304232 ⟨581216, by decide⟩ :=
  accepted_of_selected 13 304232 ⟨581216, by decide⟩ ⟨13, 2, 0, 581216, 304232, 1377, 16384⟩
    (by decide) selected_cut_22895

theorem selected_cut_22896 : selected 8 ⟨581238, by decide⟩
    (prefixPartial 13 304233) = some ⟨13, 2, 0, 581238, 304233, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_304233_581238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304233 ⟨581238, by decide⟩ :=
  accepted_of_selected 13 304233 ⟨581238, by decide⟩ ⟨13, 2, 0, 581238, 304233, 2069, 16384⟩
    (by decide) selected_cut_22896

theorem selected_cut_22897 : selected 8 ⟨581256, by decide⟩
    (prefixPartial 13 304234) = some ⟨13, 2, 0, 581256, 304234, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_304234_581256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304234 ⟨581256, by decide⟩ :=
  accepted_of_selected 13 304234 ⟨581256, by decide⟩ ⟨13, 2, 0, 581256, 304234, 1385, 16384⟩
    (by decide) selected_cut_22897

theorem selected_cut_22898 : selected 8 ⟨581262, by decide⟩
    (prefixPartial 13 304235) = some ⟨13, 2, 0, 581262, 304235, 909, 16384⟩ := by
  decide +kernel

theorem context_13_304235_581262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304235 ⟨581262, by decide⟩ :=
  accepted_of_selected 13 304235 ⟨581262, by decide⟩ ⟨13, 2, 0, 581262, 304235, 909, 16384⟩
    (by decide) selected_cut_22898

theorem unmarked_context_12_76058_581263 : frontier 9 ⟨581263, by decide⟩
    (prefixCache 12 76058) (prefixPartial 12 76058) = false := by
  decide +kernel

theorem node_context_12_76058_581263 : EJMOriginalGlobalDAGData.nodes 9 ⟨581263, by decide⟩ =
    .split (coordinate 12) (![⟨581216, by decide⟩,⟨581238, by decide⟩,⟨581256, by decide⟩,⟨581262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76058_581263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76058 ⟨581263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76058
    ⟨581263, by decide⟩ (by decide) (![⟨581216, by decide⟩,⟨581238, by decide⟩,⟨581256, by decide⟩,⟨581262, by decide⟩]) unmarked_context_12_76058_581263 node_context_12_76058_581263
  intro a
  fin_cases a
  · exact context_13_304232_581216
  · exact context_13_304233_581238
  · exact context_13_304234_581256
  · exact context_13_304235_581262

theorem selected_cut_22899 : selected 8 ⟨581289, by decide⟩
    (prefixPartial 13 304236) = some ⟨13, 2, 0, 581289, 304236, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_304236_581289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304236 ⟨581289, by decide⟩ :=
  accepted_of_selected 13 304236 ⟨581289, by decide⟩ ⟨13, 2, 0, 581289, 304236, 1513, 16384⟩
    (by decide) selected_cut_22899

theorem selected_cut_22900 : selected 8 ⟨581312, by decide⟩
    (prefixPartial 13 304237) = some ⟨13, 2, 0, 581312, 304237, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_304237_581312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304237 ⟨581312, by decide⟩ :=
  accepted_of_selected 13 304237 ⟨581312, by decide⟩ ⟨13, 2, 0, 581312, 304237, 2313, 16384⟩
    (by decide) selected_cut_22900

theorem selected_cut_22901 : selected 8 ⟨581331, by decide⟩
    (prefixPartial 13 304238) = some ⟨13, 2, 0, 581331, 304238, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_304238_581331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304238 ⟨581331, by decide⟩ :=
  accepted_of_selected 13 304238 ⟨581331, by decide⟩ ⟨13, 2, 0, 581331, 304238, 1425, 16384⟩
    (by decide) selected_cut_22901

theorem selected_cut_22902 : selected 8 ⟨581335, by decide⟩
    (prefixPartial 13 304239) = some ⟨13, 2, 0, 581335, 304239, 737, 16384⟩ := by
  decide +kernel

theorem context_13_304239_581335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304239 ⟨581335, by decide⟩ :=
  accepted_of_selected 13 304239 ⟨581335, by decide⟩ ⟨13, 2, 0, 581335, 304239, 737, 16384⟩
    (by decide) selected_cut_22902

theorem unmarked_context_12_76059_581336 : frontier 9 ⟨581336, by decide⟩
    (prefixCache 12 76059) (prefixPartial 12 76059) = false := by
  decide +kernel

theorem node_context_12_76059_581336 : EJMOriginalGlobalDAGData.nodes 9 ⟨581336, by decide⟩ =
    .split (coordinate 12) (![⟨581289, by decide⟩,⟨581312, by decide⟩,⟨581331, by decide⟩,⟨581335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76059_581336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76059 ⟨581336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76059
    ⟨581336, by decide⟩ (by decide) (![⟨581289, by decide⟩,⟨581312, by decide⟩,⟨581331, by decide⟩,⟨581335, by decide⟩]) unmarked_context_12_76059_581336 node_context_12_76059_581336
  intro a
  fin_cases a
  · exact context_13_304236_581289
  · exact context_13_304237_581312
  · exact context_13_304238_581331
  · exact context_13_304239_581335

theorem unmarked_context_11_19014_581337 : frontier 10 ⟨581337, by decide⟩
    (prefixCache 11 19014) (prefixPartial 11 19014) = false := by
  decide +kernel

theorem node_context_11_19014_581337 : EJMOriginalGlobalDAGData.nodes 10 ⟨581337, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨581195, by decide⟩,⟨581263, by decide⟩,⟨581336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19014_581337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19014 ⟨581337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19014
    ⟨581337, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨581195, by decide⟩,⟨581263, by decide⟩,⟨581336, by decide⟩]) unmarked_context_11_19014_581337 node_context_11_19014_581337
  intro a
  fin_cases a
  · exact context_12_76056_449505
  · exact context_12_76057_581195
  · exact context_12_76058_581263
  · exact context_12_76059_581336

theorem selected_cut_22903 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 76060) = some ⟨12, 1, 0, 539296, 76060, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76060_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76060 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 76060 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 76060, 1, 65536⟩
    (by decide) selected_cut_22903

theorem selected_cut_22904 : selected 8 ⟨581361, by decide⟩
    (prefixPartial 13 304244) = some ⟨13, 2, 0, 581361, 304244, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_304244_581361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304244 ⟨581361, by decide⟩ :=
  accepted_of_selected 13 304244 ⟨581361, by decide⟩ ⟨13, 2, 0, 581361, 304244, 1369, 16384⟩
    (by decide) selected_cut_22904

theorem selected_cut_22905 : selected 8 ⟨581389, by decide⟩
    (prefixPartial 13 304245) = some ⟨13, 2, 0, 581389, 304245, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_304245_581389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304245 ⟨581389, by decide⟩ :=
  accepted_of_selected 13 304245 ⟨581389, by decide⟩ ⟨13, 2, 0, 581389, 304245, 2097, 16384⟩
    (by decide) selected_cut_22905

theorem selected_cut_22906 : selected 8 ⟨581408, by decide⟩
    (prefixPartial 13 304246) = some ⟨13, 2, 0, 581408, 304246, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_304246_581408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304246 ⟨581408, by decide⟩ :=
  accepted_of_selected 13 304246 ⟨581408, by decide⟩ ⟨13, 2, 0, 581408, 304246, 1517, 16384⟩
    (by decide) selected_cut_22906

theorem selected_cut_22907 : selected 8 ⟨581413, by decide⟩
    (prefixPartial 13 304247) = some ⟨13, 2, 0, 581413, 304247, 825, 16384⟩ := by
  decide +kernel

theorem context_13_304247_581413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304247 ⟨581413, by decide⟩ :=
  accepted_of_selected 13 304247 ⟨581413, by decide⟩ ⟨13, 2, 0, 581413, 304247, 825, 16384⟩
    (by decide) selected_cut_22907

theorem unmarked_context_12_76061_581414 : frontier 9 ⟨581414, by decide⟩
    (prefixCache 12 76061) (prefixPartial 12 76061) = false := by
  decide +kernel

theorem node_context_12_76061_581414 : EJMOriginalGlobalDAGData.nodes 9 ⟨581414, by decide⟩ =
    .split (coordinate 12) (![⟨581361, by decide⟩,⟨581389, by decide⟩,⟨581408, by decide⟩,⟨581413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76061_581414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76061 ⟨581414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76061
    ⟨581414, by decide⟩ (by decide) (![⟨581361, by decide⟩,⟨581389, by decide⟩,⟨581408, by decide⟩,⟨581413, by decide⟩]) unmarked_context_12_76061_581414 node_context_12_76061_581414
  intro a
  fin_cases a
  · exact context_13_304244_581361
  · exact context_13_304245_581389
  · exact context_13_304246_581408
  · exact context_13_304247_581413

theorem selected_cut_22908 : selected 8 ⟨581442, by decide⟩
    (prefixPartial 13 304248) = some ⟨13, 2, 0, 581442, 304248, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_304248_581442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304248 ⟨581442, by decide⟩ :=
  accepted_of_selected 13 304248 ⟨581442, by decide⟩ ⟨13, 2, 0, 581442, 304248, 1501, 16384⟩
    (by decide) selected_cut_22908

theorem selected_cut_22909 : selected 8 ⟨581466, by decide⟩
    (prefixPartial 13 304249) = some ⟨13, 2, 0, 581466, 304249, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_304249_581466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304249 ⟨581466, by decide⟩ :=
  accepted_of_selected 13 304249 ⟨581466, by decide⟩ ⟨13, 2, 0, 581466, 304249, 2493, 16384⟩
    (by decide) selected_cut_22909

theorem selected_cut_22910 : selected 8 ⟨581488, by decide⟩
    (prefixPartial 13 304250) = some ⟨13, 2, 0, 581488, 304250, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_304250_581488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304250 ⟨581488, by decide⟩ :=
  accepted_of_selected 13 304250 ⟨581488, by decide⟩ ⟨13, 2, 0, 581488, 304250, 1625, 16384⟩
    (by decide) selected_cut_22910

theorem selected_cut_22911 : selected 8 ⟨581498, by decide⟩
    (prefixPartial 13 304251) = some ⟨13, 2, 0, 581498, 304251, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_304251_581498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304251 ⟨581498, by decide⟩ :=
  accepted_of_selected 13 304251 ⟨581498, by decide⟩ ⟨13, 2, 0, 581498, 304251, 1037, 16384⟩
    (by decide) selected_cut_22911

theorem unmarked_context_12_76062_581499 : frontier 9 ⟨581499, by decide⟩
    (prefixCache 12 76062) (prefixPartial 12 76062) = false := by
  decide +kernel

theorem node_context_12_76062_581499 : EJMOriginalGlobalDAGData.nodes 9 ⟨581499, by decide⟩ =
    .split (coordinate 12) (![⟨581442, by decide⟩,⟨581466, by decide⟩,⟨581488, by decide⟩,⟨581498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76062_581499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76062 ⟨581499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76062
    ⟨581499, by decide⟩ (by decide) (![⟨581442, by decide⟩,⟨581466, by decide⟩,⟨581488, by decide⟩,⟨581498, by decide⟩]) unmarked_context_12_76062_581499 node_context_12_76062_581499
  intro a
  fin_cases a
  · exact context_13_304248_581442
  · exact context_13_304249_581466
  · exact context_13_304250_581488
  · exact context_13_304251_581498

theorem selected_cut_22912 : selected 8 ⟨581524, by decide⟩
    (prefixPartial 13 304252) = some ⟨13, 2, 0, 581524, 304252, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_304252_581524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304252 ⟨581524, by decide⟩ :=
  accepted_of_selected 13 304252 ⟨581524, by decide⟩ ⟨13, 2, 0, 581524, 304252, 1533, 16384⟩
    (by decide) selected_cut_22912

theorem selected_cut_22913 : selected 8 ⟨581548, by decide⟩
    (prefixPartial 13 304253) = some ⟨13, 2, 0, 581548, 304253, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_304253_581548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304253 ⟨581548, by decide⟩ :=
  accepted_of_selected 13 304253 ⟨581548, by decide⟩ ⟨13, 2, 0, 581548, 304253, 2597, 16384⟩
    (by decide) selected_cut_22913

theorem selected_cut_22914 : selected 8 ⟨581566, by decide⟩
    (prefixPartial 13 304254) = some ⟨13, 2, 0, 581566, 304254, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_304254_581566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304254 ⟨581566, by decide⟩ :=
  accepted_of_selected 13 304254 ⟨581566, by decide⟩ ⟨13, 2, 0, 581566, 304254, 1641, 16384⟩
    (by decide) selected_cut_22914

theorem selected_cut_22915 : selected 8 ⟨581572, by decide⟩
    (prefixPartial 13 304255) = some ⟨13, 2, 0, 581572, 304255, 825, 16384⟩ := by
  decide +kernel

theorem context_13_304255_581572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304255 ⟨581572, by decide⟩ :=
  accepted_of_selected 13 304255 ⟨581572, by decide⟩ ⟨13, 2, 0, 581572, 304255, 825, 16384⟩
    (by decide) selected_cut_22915

theorem unmarked_context_12_76063_581573 : frontier 9 ⟨581573, by decide⟩
    (prefixCache 12 76063) (prefixPartial 12 76063) = false := by
  decide +kernel

theorem node_context_12_76063_581573 : EJMOriginalGlobalDAGData.nodes 9 ⟨581573, by decide⟩ =
    .split (coordinate 12) (![⟨581524, by decide⟩,⟨581548, by decide⟩,⟨581566, by decide⟩,⟨581572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76063_581573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76063 ⟨581573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76063
    ⟨581573, by decide⟩ (by decide) (![⟨581524, by decide⟩,⟨581548, by decide⟩,⟨581566, by decide⟩,⟨581572, by decide⟩]) unmarked_context_12_76063_581573 node_context_12_76063_581573
  intro a
  fin_cases a
  · exact context_13_304252_581524
  · exact context_13_304253_581548
  · exact context_13_304254_581566
  · exact context_13_304255_581572

theorem unmarked_context_11_19015_581574 : frontier 10 ⟨581574, by decide⟩
    (prefixCache 11 19015) (prefixPartial 11 19015) = false := by
  decide +kernel

theorem node_context_11_19015_581574 : EJMOriginalGlobalDAGData.nodes 10 ⟨581574, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨581414, by decide⟩,⟨581499, by decide⟩,⟨581573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19015_581574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19015 ⟨581574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19015
    ⟨581574, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨581414, by decide⟩,⟨581499, by decide⟩,⟨581573, by decide⟩]) unmarked_context_11_19015_581574 node_context_11_19015_581574
  intro a
  fin_cases a
  · exact context_12_76060_539296
  · exact context_12_76061_581414
  · exact context_12_76062_581499
  · exact context_12_76063_581573

theorem unmarked_context_10_4753_581575 : frontier 11 ⟨581575, by decide⟩
    (prefixCache 10 4753) (prefixPartial 10 4753) = false := by
  decide +kernel

theorem node_context_10_4753_581575 : EJMOriginalGlobalDAGData.nodes 11 ⟨581575, by decide⟩ =
    .split (coordinate 10) (![⟨580961, by decide⟩,⟨581125, by decide⟩,⟨581337, by decide⟩,⟨581574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4753_581575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4753 ⟨581575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4753
    ⟨581575, by decide⟩ (by decide) (![⟨580961, by decide⟩,⟨581125, by decide⟩,⟨581337, by decide⟩,⟨581574, by decide⟩]) unmarked_context_10_4753_581575 node_context_10_4753_581575
  intro a
  fin_cases a
  · exact context_11_19012_580961
  · exact context_11_19013_581125
  · exact context_11_19014_581337
  · exact context_11_19015_581574

theorem selected_cut_22916 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76064) = some ⟨12, 1, 0, 435790, 76064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76064_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76064 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76064 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76064, 1, 65536⟩
    (by decide) selected_cut_22916

theorem selected_cut_22917 : selected 8 ⟨581594, by decide⟩
    (prefixPartial 13 304260) = some ⟨13, 2, 0, 581594, 304260, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_304260_581594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304260 ⟨581594, by decide⟩ :=
  accepted_of_selected 13 304260 ⟨581594, by decide⟩ ⟨13, 2, 0, 581594, 304260, 1053, 16384⟩
    (by decide) selected_cut_22917

theorem selected_cut_22918 : selected 8 ⟨581615, by decide⟩
    (prefixPartial 13 304261) = some ⟨13, 2, 0, 581615, 304261, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_304261_581615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304261 ⟨581615, by decide⟩ :=
  accepted_of_selected 13 304261 ⟨581615, by decide⟩ ⟨13, 2, 0, 581615, 304261, 1545, 16384⟩
    (by decide) selected_cut_22918

theorem selected_cut_22919 : selected 8 ⟨581629, by decide⟩
    (prefixPartial 13 304262) = some ⟨13, 2, 0, 581629, 304262, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_304262_581629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304262 ⟨581629, by decide⟩ :=
  accepted_of_selected 13 304262 ⟨581629, by decide⟩ ⟨13, 2, 0, 581629, 304262, 1201, 16384⟩
    (by decide) selected_cut_22919

theorem selected_cut_22920 : selected 8 ⟨581635, by decide⟩
    (prefixPartial 13 304263) = some ⟨13, 2, 0, 581635, 304263, 793, 16384⟩ := by
  decide +kernel

theorem context_13_304263_581635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304263 ⟨581635, by decide⟩ :=
  accepted_of_selected 13 304263 ⟨581635, by decide⟩ ⟨13, 2, 0, 581635, 304263, 793, 16384⟩
    (by decide) selected_cut_22920

theorem unmarked_context_12_76065_581636 : frontier 9 ⟨581636, by decide⟩
    (prefixCache 12 76065) (prefixPartial 12 76065) = false := by
  decide +kernel

theorem node_context_12_76065_581636 : EJMOriginalGlobalDAGData.nodes 9 ⟨581636, by decide⟩ =
    .split (coordinate 12) (![⟨581594, by decide⟩,⟨581615, by decide⟩,⟨581629, by decide⟩,⟨581635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76065_581636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76065 ⟨581636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76065
    ⟨581636, by decide⟩ (by decide) (![⟨581594, by decide⟩,⟨581615, by decide⟩,⟨581629, by decide⟩,⟨581635, by decide⟩]) unmarked_context_12_76065_581636 node_context_12_76065_581636
  intro a
  fin_cases a
  · exact context_13_304260_581594
  · exact context_13_304261_581615
  · exact context_13_304262_581629
  · exact context_13_304263_581635

theorem selected_cut_22921 : selected 8 ⟨581654, by decide⟩
    (prefixPartial 13 304264) = some ⟨13, 2, 0, 581654, 304264, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_304264_581654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304264 ⟨581654, by decide⟩ :=
  accepted_of_selected 13 304264 ⟨581654, by decide⟩ ⟨13, 2, 0, 581654, 304264, 1041, 16384⟩
    (by decide) selected_cut_22921

theorem selected_cut_22922 : selected 8 ⟨581677, by decide⟩
    (prefixPartial 13 304265) = some ⟨13, 2, 0, 581677, 304265, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_304265_581677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304265 ⟨581677, by decide⟩ :=
  accepted_of_selected 13 304265 ⟨581677, by decide⟩ ⟨13, 2, 0, 581677, 304265, 1681, 16384⟩
    (by decide) selected_cut_22922

theorem selected_cut_22923 : selected 8 ⟨581693, by decide⟩
    (prefixPartial 13 304266) = some ⟨13, 2, 0, 581693, 304266, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_304266_581693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304266 ⟨581693, by decide⟩ :=
  accepted_of_selected 13 304266 ⟨581693, by decide⟩ ⟨13, 2, 0, 581693, 304266, 1233, 16384⟩
    (by decide) selected_cut_22923

theorem selected_cut_22924 : selected 8 ⟨581699, by decide⟩
    (prefixPartial 13 304267) = some ⟨13, 2, 0, 581699, 304267, 845, 16384⟩ := by
  decide +kernel

theorem context_13_304267_581699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304267 ⟨581699, by decide⟩ :=
  accepted_of_selected 13 304267 ⟨581699, by decide⟩ ⟨13, 2, 0, 581699, 304267, 845, 16384⟩
    (by decide) selected_cut_22924

theorem unmarked_context_12_76066_581700 : frontier 9 ⟨581700, by decide⟩
    (prefixCache 12 76066) (prefixPartial 12 76066) = false := by
  decide +kernel

theorem node_context_12_76066_581700 : EJMOriginalGlobalDAGData.nodes 9 ⟨581700, by decide⟩ =
    .split (coordinate 12) (![⟨581654, by decide⟩,⟨581677, by decide⟩,⟨581693, by decide⟩,⟨581699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76066_581700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76066 ⟨581700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76066
    ⟨581700, by decide⟩ (by decide) (![⟨581654, by decide⟩,⟨581677, by decide⟩,⟨581693, by decide⟩,⟨581699, by decide⟩]) unmarked_context_12_76066_581700 node_context_12_76066_581700
  intro a
  fin_cases a
  · exact context_13_304264_581654
  · exact context_13_304265_581677
  · exact context_13_304266_581693
  · exact context_13_304267_581699

theorem selected_cut_22925 : selected 8 ⟨581721, by decide⟩
    (prefixPartial 13 304268) = some ⟨13, 2, 0, 581721, 304268, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_304268_581721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304268 ⟨581721, by decide⟩ :=
  accepted_of_selected 13 304268 ⟨581721, by decide⟩ ⟨13, 2, 0, 581721, 304268, 1145, 16384⟩
    (by decide) selected_cut_22925

theorem selected_cut_22926 : selected 8 ⟨581747, by decide⟩
    (prefixPartial 13 304269) = some ⟨13, 2, 0, 581747, 304269, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_304269_581747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304269 ⟨581747, by decide⟩ :=
  accepted_of_selected 13 304269 ⟨581747, by decide⟩ ⟨13, 2, 0, 581747, 304269, 1785, 16384⟩
    (by decide) selected_cut_22926

theorem selected_cut_22927 : selected 8 ⟨581762, by decide⟩
    (prefixPartial 13 304270) = some ⟨13, 2, 0, 581762, 304270, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_304270_581762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304270 ⟨581762, by decide⟩ :=
  accepted_of_selected 13 304270 ⟨581762, by decide⟩ ⟨13, 2, 0, 581762, 304270, 1297, 16384⟩
    (by decide) selected_cut_22927

theorem selected_cut_22928 : selected 8 ⟨581769, by decide⟩
    (prefixPartial 13 304271) = some ⟨13, 2, 0, 581769, 304271, 785, 16384⟩ := by
  decide +kernel

theorem context_13_304271_581769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304271 ⟨581769, by decide⟩ :=
  accepted_of_selected 13 304271 ⟨581769, by decide⟩ ⟨13, 2, 0, 581769, 304271, 785, 16384⟩
    (by decide) selected_cut_22928

theorem unmarked_context_12_76067_581770 : frontier 9 ⟨581770, by decide⟩
    (prefixCache 12 76067) (prefixPartial 12 76067) = false := by
  decide +kernel

theorem node_context_12_76067_581770 : EJMOriginalGlobalDAGData.nodes 9 ⟨581770, by decide⟩ =
    .split (coordinate 12) (![⟨581721, by decide⟩,⟨581747, by decide⟩,⟨581762, by decide⟩,⟨581769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76067_581770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76067 ⟨581770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76067
    ⟨581770, by decide⟩ (by decide) (![⟨581721, by decide⟩,⟨581747, by decide⟩,⟨581762, by decide⟩,⟨581769, by decide⟩]) unmarked_context_12_76067_581770 node_context_12_76067_581770
  intro a
  fin_cases a
  · exact context_13_304268_581721
  · exact context_13_304269_581747
  · exact context_13_304270_581762
  · exact context_13_304271_581769

theorem unmarked_context_11_19016_581771 : frontier 10 ⟨581771, by decide⟩
    (prefixCache 11 19016) (prefixPartial 11 19016) = false := by
  decide +kernel

theorem node_context_11_19016_581771 : EJMOriginalGlobalDAGData.nodes 10 ⟨581771, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨581636, by decide⟩,⟨581700, by decide⟩,⟨581770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19016_581771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19016 ⟨581771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19016
    ⟨581771, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨581636, by decide⟩,⟨581700, by decide⟩,⟨581770, by decide⟩]) unmarked_context_11_19016_581771 node_context_11_19016_581771
  intro a
  fin_cases a
  · exact context_12_76064_435790
  · exact context_12_76065_581636
  · exact context_12_76066_581700
  · exact context_12_76067_581770

theorem selected_cut_22929 : selected 9 ⟨581834, by decide⟩
    (prefixPartial 12 76068) = some ⟨12, 2, 0, 581834, 76068, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_76068_581834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76068 ⟨581834, by decide⟩ :=
  accepted_of_selected 12 76068 ⟨581834, by decide⟩ ⟨12, 2, 0, 581834, 76068, 3425, 65536⟩
    (by decide) selected_cut_22929

theorem selected_cut_22930 : selected 8 ⟨581858, by decide⟩
    (prefixPartial 13 304276) = some ⟨13, 2, 0, 581858, 304276, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_304276_581858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304276 ⟨581858, by decide⟩ :=
  accepted_of_selected 13 304276 ⟨581858, by decide⟩ ⟨13, 2, 0, 581858, 304276, 1757, 16384⟩
    (by decide) selected_cut_22930

theorem selected_cut_22931 : selected 8 ⟨581882, by decide⟩
    (prefixPartial 13 304277) = some ⟨13, 2, 0, 581882, 304277, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_304277_581882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304277 ⟨581882, by decide⟩ :=
  accepted_of_selected 13 304277 ⟨581882, by decide⟩ ⟨13, 2, 0, 581882, 304277, 2673, 16384⟩
    (by decide) selected_cut_22931

theorem selected_cut_22932 : selected 8 ⟨581899, by decide⟩
    (prefixPartial 13 304278) = some ⟨13, 2, 0, 581899, 304278, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_304278_581899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304278 ⟨581899, by decide⟩ :=
  accepted_of_selected 13 304278 ⟨581899, by decide⟩ ⟨13, 2, 0, 581899, 304278, 1985, 16384⟩
    (by decide) selected_cut_22932

theorem selected_cut_22933 : selected 8 ⟨581908, by decide⟩
    (prefixPartial 13 304279) = some ⟨13, 2, 0, 581908, 304279, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_304279_581908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304279 ⟨581908, by decide⟩ :=
  accepted_of_selected 13 304279 ⟨581908, by decide⟩ ⟨13, 2, 0, 581908, 304279, 1201, 16384⟩
    (by decide) selected_cut_22933

theorem unmarked_context_12_76069_581909 : frontier 9 ⟨581909, by decide⟩
    (prefixCache 12 76069) (prefixPartial 12 76069) = false := by
  decide +kernel

theorem node_context_12_76069_581909 : EJMOriginalGlobalDAGData.nodes 9 ⟨581909, by decide⟩ =
    .split (coordinate 12) (![⟨581858, by decide⟩,⟨581882, by decide⟩,⟨581899, by decide⟩,⟨581908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76069_581909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76069 ⟨581909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76069
    ⟨581909, by decide⟩ (by decide) (![⟨581858, by decide⟩,⟨581882, by decide⟩,⟨581899, by decide⟩,⟨581908, by decide⟩]) unmarked_context_12_76069_581909 node_context_12_76069_581909
  intro a
  fin_cases a
  · exact context_13_304276_581858
  · exact context_13_304277_581882
  · exact context_13_304278_581899
  · exact context_13_304279_581908

theorem selected_cut_22934 : selected 8 ⟨581932, by decide⟩
    (prefixPartial 13 304280) = some ⟨13, 2, 0, 581932, 304280, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_304280_581932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304280 ⟨581932, by decide⟩ :=
  accepted_of_selected 13 304280 ⟨581932, by decide⟩ ⟨13, 2, 0, 581932, 304280, 1037, 16384⟩
    (by decide) selected_cut_22934

theorem selected_cut_22935 : selected 8 ⟨581950, by decide⟩
    (prefixPartial 13 304281) = some ⟨13, 2, 0, 581950, 304281, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_304281_581950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304281 ⟨581950, by decide⟩ :=
  accepted_of_selected 13 304281 ⟨581950, by decide⟩ ⟨13, 2, 0, 581950, 304281, 1545, 16384⟩
    (by decide) selected_cut_22935

theorem selected_cut_22936 : selected 8 ⟨581964, by decide⟩
    (prefixPartial 13 304282) = some ⟨13, 2, 0, 581964, 304282, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_304282_581964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304282 ⟨581964, by decide⟩ :=
  accepted_of_selected 13 304282 ⟨581964, by decide⟩ ⟨13, 2, 0, 581964, 304282, 1069, 16384⟩
    (by decide) selected_cut_22936

theorem selected_cut_22937 : selected 8 ⟨581968, by decide⟩
    (prefixPartial 13 304283) = some ⟨13, 2, 0, 581968, 304283, 909, 16384⟩ := by
  decide +kernel

theorem context_13_304283_581968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304283 ⟨581968, by decide⟩ :=
  accepted_of_selected 13 304283 ⟨581968, by decide⟩ ⟨13, 2, 0, 581968, 304283, 909, 16384⟩
    (by decide) selected_cut_22937

theorem unmarked_context_12_76070_581969 : frontier 9 ⟨581969, by decide⟩
    (prefixCache 12 76070) (prefixPartial 12 76070) = false := by
  decide +kernel

theorem node_context_12_76070_581969 : EJMOriginalGlobalDAGData.nodes 9 ⟨581969, by decide⟩ =
    .split (coordinate 12) (![⟨581932, by decide⟩,⟨581950, by decide⟩,⟨581964, by decide⟩,⟨581968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76070_581969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76070 ⟨581969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76070
    ⟨581969, by decide⟩ (by decide) (![⟨581932, by decide⟩,⟨581950, by decide⟩,⟨581964, by decide⟩,⟨581968, by decide⟩]) unmarked_context_12_76070_581969 node_context_12_76070_581969
  intro a
  fin_cases a
  · exact context_13_304280_581932
  · exact context_13_304281_581950
  · exact context_13_304282_581964
  · exact context_13_304283_581968

theorem selected_cut_22938 : selected 8 ⟨581993, by decide⟩
    (prefixPartial 13 304284) = some ⟨13, 2, 0, 581993, 304284, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_304284_581993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304284 ⟨581993, by decide⟩ :=
  accepted_of_selected 13 304284 ⟨581993, by decide⟩ ⟨13, 2, 0, 581993, 304284, 1065, 16384⟩
    (by decide) selected_cut_22938

theorem selected_cut_22939 : selected 8 ⟨582015, by decide⟩
    (prefixPartial 13 304285) = some ⟨13, 2, 0, 582015, 304285, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_304285_582015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304285 ⟨582015, by decide⟩ :=
  accepted_of_selected 13 304285 ⟨582015, by decide⟩ ⟨13, 2, 0, 582015, 304285, 1609, 16384⟩
    (by decide) selected_cut_22939

theorem selected_cut_22940 : selected 8 ⟨582032, by decide⟩
    (prefixPartial 13 304286) = some ⟨13, 2, 0, 582032, 304286, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_304286_582032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304286 ⟨582032, by decide⟩ :=
  accepted_of_selected 13 304286 ⟨582032, by decide⟩ ⟨13, 2, 0, 582032, 304286, 1257, 16384⟩
    (by decide) selected_cut_22940

theorem selected_cut_22941 : selected 8 ⟨582036, by decide⟩
    (prefixPartial 13 304287) = some ⟨13, 2, 0, 582036, 304287, 729, 16384⟩ := by
  decide +kernel

theorem context_13_304287_582036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304287 ⟨582036, by decide⟩ :=
  accepted_of_selected 13 304287 ⟨582036, by decide⟩ ⟨13, 2, 0, 582036, 304287, 729, 16384⟩
    (by decide) selected_cut_22941

theorem unmarked_context_12_76071_582037 : frontier 9 ⟨582037, by decide⟩
    (prefixCache 12 76071) (prefixPartial 12 76071) = false := by
  decide +kernel

theorem node_context_12_76071_582037 : EJMOriginalGlobalDAGData.nodes 9 ⟨582037, by decide⟩ =
    .split (coordinate 12) (![⟨581993, by decide⟩,⟨582015, by decide⟩,⟨582032, by decide⟩,⟨582036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76071_582037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76071 ⟨582037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76071
    ⟨582037, by decide⟩ (by decide) (![⟨581993, by decide⟩,⟨582015, by decide⟩,⟨582032, by decide⟩,⟨582036, by decide⟩]) unmarked_context_12_76071_582037 node_context_12_76071_582037
  intro a
  fin_cases a
  · exact context_13_304284_581993
  · exact context_13_304285_582015
  · exact context_13_304286_582032
  · exact context_13_304287_582036

theorem unmarked_context_11_19017_582038 : frontier 10 ⟨582038, by decide⟩
    (prefixCache 11 19017) (prefixPartial 11 19017) = false := by
  decide +kernel

theorem node_context_11_19017_582038 : EJMOriginalGlobalDAGData.nodes 10 ⟨582038, by decide⟩ =
    .split (coordinate 11) (![⟨581834, by decide⟩,⟨581909, by decide⟩,⟨581969, by decide⟩,⟨582037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19017_582038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19017 ⟨582038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19017
    ⟨582038, by decide⟩ (by decide) (![⟨581834, by decide⟩,⟨581909, by decide⟩,⟨581969, by decide⟩,⟨582037, by decide⟩]) unmarked_context_11_19017_582038 node_context_11_19017_582038
  intro a
  fin_cases a
  · exact context_12_76068_581834
  · exact context_12_76069_581909
  · exact context_12_76070_581969
  · exact context_12_76071_582037

theorem selected_cut_22942 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76072) = some ⟨12, 1, 0, 435790, 76072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76072_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76072 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76072 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76072, 1, 65536⟩
    (by decide) selected_cut_22942

theorem selected_cut_22943 : selected 8 ⟨582060, by decide⟩
    (prefixPartial 13 304292) = some ⟨13, 2, 0, 582060, 304292, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_304292_582060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304292 ⟨582060, by decide⟩ :=
  accepted_of_selected 13 304292 ⟨582060, by decide⟩ ⟨13, 2, 0, 582060, 304292, 1341, 16384⟩
    (by decide) selected_cut_22943

theorem selected_cut_22944 : selected 8 ⟨582084, by decide⟩
    (prefixPartial 13 304293) = some ⟨13, 2, 0, 582084, 304293, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_304293_582084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304293 ⟨582084, by decide⟩ :=
  accepted_of_selected 13 304293 ⟨582084, by decide⟩ ⟨13, 2, 0, 582084, 304293, 1997, 16384⟩
    (by decide) selected_cut_22944

theorem selected_cut_22945 : selected 8 ⟨582101, by decide⟩
    (prefixPartial 13 304294) = some ⟨13, 2, 0, 582101, 304294, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_304294_582101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304294 ⟨582101, by decide⟩ :=
  accepted_of_selected 13 304294 ⟨582101, by decide⟩ ⟨13, 2, 0, 582101, 304294, 1769, 16384⟩
    (by decide) selected_cut_22945

theorem selected_cut_22946 : selected 8 ⟨582106, by decide⟩
    (prefixPartial 13 304295) = some ⟨13, 2, 0, 582106, 304295, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_304295_582106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304295 ⟨582106, by decide⟩ :=
  accepted_of_selected 13 304295 ⟨582106, by decide⟩ ⟨13, 2, 0, 582106, 304295, 1097, 16384⟩
    (by decide) selected_cut_22946

theorem unmarked_context_12_76073_582107 : frontier 9 ⟨582107, by decide⟩
    (prefixCache 12 76073) (prefixPartial 12 76073) = false := by
  decide +kernel

theorem node_context_12_76073_582107 : EJMOriginalGlobalDAGData.nodes 9 ⟨582107, by decide⟩ =
    .split (coordinate 12) (![⟨582060, by decide⟩,⟨582084, by decide⟩,⟨582101, by decide⟩,⟨582106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76073_582107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76073 ⟨582107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76073
    ⟨582107, by decide⟩ (by decide) (![⟨582060, by decide⟩,⟨582084, by decide⟩,⟨582101, by decide⟩,⟨582106, by decide⟩]) unmarked_context_12_76073_582107 node_context_12_76073_582107
  intro a
  fin_cases a
  · exact context_13_304292_582060
  · exact context_13_304293_582084
  · exact context_13_304294_582101
  · exact context_13_304295_582106

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
