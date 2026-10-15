/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover071
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_06915 : selected 8 ⟨204460, by decide⟩
    (prefixPartial 13 88155) = some ⟨13, 2, 0, 204460, 88155, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_88155_204460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88155 ⟨204460, by decide⟩ :=
  accepted_of_selected 13 88155 ⟨204460, by decide⟩ ⟨13, 2, 0, 204460, 88155, 1161, 16384⟩
    (by decide) selected_cut_06915

theorem unmarked_context_12_22038_204461 : frontier 9 ⟨204461, by decide⟩
    (prefixCache 12 22038) (prefixPartial 12 22038) = false := by
  decide +kernel

theorem node_context_12_22038_204461 : EJMOriginalGlobalDAGData.nodes 9 ⟨204461, by decide⟩ =
    .split (coordinate 12) (![⟨204380, by decide⟩,⟨204428, by decide⟩,⟨204448, by decide⟩,⟨204460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22038_204461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22038 ⟨204461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22038
    ⟨204461, by decide⟩ (by decide) (![⟨204380, by decide⟩,⟨204428, by decide⟩,⟨204448, by decide⟩,⟨204460, by decide⟩]) unmarked_context_12_22038_204461 node_context_12_22038_204461
  intro a
  fin_cases a
  · exact context_13_88152_204380
  · exact context_13_88153_204428
  · exact context_13_88154_204448
  · exact context_13_88155_204460

theorem selected_cut_06916 : selected 8 ⟨204498, by decide⟩
    (prefixPartial 13 88156) = some ⟨13, 2, 0, 204498, 88156, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_88156_204498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88156 ⟨204498, by decide⟩ :=
  accepted_of_selected 13 88156 ⟨204498, by decide⟩ ⟨13, 2, 0, 204498, 88156, 2389, 16384⟩
    (by decide) selected_cut_06916

theorem selected_cut_06917 : selected 8 ⟨204561, by decide⟩
    (prefixPartial 13 88157) = some ⟨13, 2, 0, 204561, 88157, 3917, 16384⟩ := by
  decide +kernel

theorem context_13_88157_204561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88157 ⟨204561, by decide⟩ :=
  accepted_of_selected 13 88157 ⟨204561, by decide⟩ ⟨13, 2, 0, 204561, 88157, 3917, 16384⟩
    (by decide) selected_cut_06917

theorem selected_cut_06918 : selected 8 ⟨204587, by decide⟩
    (prefixPartial 13 88158) = some ⟨13, 2, 0, 204587, 88158, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_88158_204587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88158 ⟨204587, by decide⟩ :=
  accepted_of_selected 13 88158 ⟨204587, by decide⟩ ⟨13, 2, 0, 204587, 88158, 2089, 16384⟩
    (by decide) selected_cut_06918

theorem selected_cut_06919 : selected 8 ⟨204593, by decide⟩
    (prefixPartial 13 88159) = some ⟨13, 2, 0, 204593, 88159, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_88159_204593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88159 ⟨204593, by decide⟩ :=
  accepted_of_selected 13 88159 ⟨204593, by decide⟩ ⟨13, 2, 0, 204593, 88159, 1041, 16384⟩
    (by decide) selected_cut_06919

theorem unmarked_context_12_22039_204594 : frontier 9 ⟨204594, by decide⟩
    (prefixCache 12 22039) (prefixPartial 12 22039) = false := by
  decide +kernel

theorem node_context_12_22039_204594 : EJMOriginalGlobalDAGData.nodes 9 ⟨204594, by decide⟩ =
    .split (coordinate 12) (![⟨204498, by decide⟩,⟨204561, by decide⟩,⟨204587, by decide⟩,⟨204593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22039_204594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22039 ⟨204594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22039
    ⟨204594, by decide⟩ (by decide) (![⟨204498, by decide⟩,⟨204561, by decide⟩,⟨204587, by decide⟩,⟨204593, by decide⟩]) unmarked_context_12_22039_204594 node_context_12_22039_204594
  intro a
  fin_cases a
  · exact context_13_88156_204498
  · exact context_13_88157_204561
  · exact context_13_88158_204587
  · exact context_13_88159_204593

theorem unmarked_context_11_5509_204595 : frontier 10 ⟨204595, by decide⟩
    (prefixCache 11 5509) (prefixPartial 11 5509) = false := by
  decide +kernel

theorem node_context_11_5509_204595 : EJMOriginalGlobalDAGData.nodes 10 ⟨204595, by decide⟩ =
    .split (coordinate 11) (![⟨204255, by decide⟩,⟨204357, by decide⟩,⟨204461, by decide⟩,⟨204594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5509_204595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5509 ⟨204595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5509
    ⟨204595, by decide⟩ (by decide) (![⟨204255, by decide⟩,⟨204357, by decide⟩,⟨204461, by decide⟩,⟨204594, by decide⟩]) unmarked_context_11_5509_204595 node_context_11_5509_204595
  intro a
  fin_cases a
  · exact context_12_22036_204255
  · exact context_12_22037_204357
  · exact context_12_22038_204461
  · exact context_12_22039_204594

theorem selected_cut_06920 : selected 8 ⟨204607, by decide⟩
    (prefixPartial 13 88160) = some ⟨13, 2, 0, 204607, 88160, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_88160_204607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88160 ⟨204607, by decide⟩ :=
  accepted_of_selected 13 88160 ⟨204607, by decide⟩ ⟨13, 2, 0, 204607, 88160, 1045, 16384⟩
    (by decide) selected_cut_06920

theorem selected_cut_06921 : selected 8 ⟨204629, by decide⟩
    (prefixPartial 13 88161) = some ⟨13, 2, 0, 204629, 88161, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_88161_204629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88161 ⟨204629, by decide⟩ :=
  accepted_of_selected 13 88161 ⟨204629, by decide⟩ ⟨13, 2, 0, 204629, 88161, 1717, 16384⟩
    (by decide) selected_cut_06921

theorem selected_cut_06922 : selected 8 ⟨204647, by decide⟩
    (prefixPartial 13 88162) = some ⟨13, 2, 0, 204647, 88162, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_88162_204647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88162 ⟨204647, by decide⟩ :=
  accepted_of_selected 13 88162 ⟨204647, by decide⟩ ⟨13, 2, 0, 204647, 88162, 1349, 16384⟩
    (by decide) selected_cut_06922

theorem selected_cut_06923 : selected 8 ⟨204654, by decide⟩
    (prefixPartial 13 88163) = some ⟨13, 2, 0, 204654, 88163, 853, 16384⟩ := by
  decide +kernel

theorem context_13_88163_204654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88163 ⟨204654, by decide⟩ :=
  accepted_of_selected 13 88163 ⟨204654, by decide⟩ ⟨13, 2, 0, 204654, 88163, 853, 16384⟩
    (by decide) selected_cut_06923

theorem unmarked_context_12_22040_204655 : frontier 9 ⟨204655, by decide⟩
    (prefixCache 12 22040) (prefixPartial 12 22040) = false := by
  decide +kernel

theorem node_context_12_22040_204655 : EJMOriginalGlobalDAGData.nodes 9 ⟨204655, by decide⟩ =
    .split (coordinate 12) (![⟨204607, by decide⟩,⟨204629, by decide⟩,⟨204647, by decide⟩,⟨204654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22040_204655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22040 ⟨204655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22040
    ⟨204655, by decide⟩ (by decide) (![⟨204607, by decide⟩,⟨204629, by decide⟩,⟨204647, by decide⟩,⟨204654, by decide⟩]) unmarked_context_12_22040_204655 node_context_12_22040_204655
  intro a
  fin_cases a
  · exact context_13_88160_204607
  · exact context_13_88161_204629
  · exact context_13_88162_204647
  · exact context_13_88163_204654

theorem selected_cut_06924 : selected 8 ⟨204678, by decide⟩
    (prefixPartial 13 88164) = some ⟨13, 2, 0, 204678, 88164, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_88164_204678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88164 ⟨204678, by decide⟩ :=
  accepted_of_selected 13 88164 ⟨204678, by decide⟩ ⟨13, 2, 0, 204678, 88164, 1229, 16384⟩
    (by decide) selected_cut_06924

theorem selected_cut_06925 : selected 8 ⟨204701, by decide⟩
    (prefixPartial 13 88165) = some ⟨13, 2, 0, 204701, 88165, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_88165_204701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88165 ⟨204701, by decide⟩ :=
  accepted_of_selected 13 88165 ⟨204701, by decide⟩ ⟨13, 2, 0, 204701, 88165, 1321, 16384⟩
    (by decide) selected_cut_06925

theorem selected_cut_06926 : selected 8 ⟨204724, by decide⟩
    (prefixPartial 13 88166) = some ⟨13, 2, 0, 204724, 88166, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_88166_204724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88166 ⟨204724, by decide⟩ :=
  accepted_of_selected 13 88166 ⟨204724, by decide⟩ ⟨13, 2, 0, 204724, 88166, 1209, 16384⟩
    (by decide) selected_cut_06926

theorem selected_cut_06927 : selected 8 ⟨204732, by decide⟩
    (prefixPartial 13 88167) = some ⟨13, 2, 0, 204732, 88167, 881, 16384⟩ := by
  decide +kernel

theorem context_13_88167_204732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88167 ⟨204732, by decide⟩ :=
  accepted_of_selected 13 88167 ⟨204732, by decide⟩ ⟨13, 2, 0, 204732, 88167, 881, 16384⟩
    (by decide) selected_cut_06927

theorem unmarked_context_12_22041_204733 : frontier 9 ⟨204733, by decide⟩
    (prefixCache 12 22041) (prefixPartial 12 22041) = false := by
  decide +kernel

theorem node_context_12_22041_204733 : EJMOriginalGlobalDAGData.nodes 9 ⟨204733, by decide⟩ =
    .split (coordinate 12) (![⟨204678, by decide⟩,⟨204701, by decide⟩,⟨204724, by decide⟩,⟨204732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22041_204733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22041 ⟨204733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22041
    ⟨204733, by decide⟩ (by decide) (![⟨204678, by decide⟩,⟨204701, by decide⟩,⟨204724, by decide⟩,⟨204732, by decide⟩]) unmarked_context_12_22041_204733 node_context_12_22041_204733
  intro a
  fin_cases a
  · exact context_13_88164_204678
  · exact context_13_88165_204701
  · exact context_13_88166_204724
  · exact context_13_88167_204732

theorem selected_cut_06928 : selected 8 ⟨204758, by decide⟩
    (prefixPartial 13 88168) = some ⟨13, 2, 0, 204758, 88168, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_88168_204758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88168 ⟨204758, by decide⟩ :=
  accepted_of_selected 13 88168 ⟨204758, by decide⟩ ⟨13, 2, 0, 204758, 88168, 2133, 16384⟩
    (by decide) selected_cut_06928

theorem selected_cut_06929 : selected 8 ⟨204807, by decide⟩
    (prefixPartial 13 88169) = some ⟨13, 2, 0, 204807, 88169, 3265, 16384⟩ := by
  decide +kernel

theorem context_13_88169_204807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88169 ⟨204807, by decide⟩ :=
  accepted_of_selected 13 88169 ⟨204807, by decide⟩ ⟨13, 2, 0, 204807, 88169, 3265, 16384⟩
    (by decide) selected_cut_06929

theorem selected_cut_06930 : selected 8 ⟨204833, by decide⟩
    (prefixPartial 13 88170) = some ⟨13, 2, 0, 204833, 88170, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_88170_204833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88170 ⟨204833, by decide⟩ :=
  accepted_of_selected 13 88170 ⟨204833, by decide⟩ ⟨13, 2, 0, 204833, 88170, 2033, 16384⟩
    (by decide) selected_cut_06930

theorem selected_cut_06931 : selected 8 ⟨204847, by decide⟩
    (prefixPartial 13 88171) = some ⟨13, 2, 0, 204847, 88171, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_88171_204847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88171 ⟨204847, by decide⟩ :=
  accepted_of_selected 13 88171 ⟨204847, by decide⟩ ⟨13, 2, 0, 204847, 88171, 1313, 16384⟩
    (by decide) selected_cut_06931

theorem unmarked_context_12_22042_204848 : frontier 9 ⟨204848, by decide⟩
    (prefixCache 12 22042) (prefixPartial 12 22042) = false := by
  decide +kernel

theorem node_context_12_22042_204848 : EJMOriginalGlobalDAGData.nodes 9 ⟨204848, by decide⟩ =
    .split (coordinate 12) (![⟨204758, by decide⟩,⟨204807, by decide⟩,⟨204833, by decide⟩,⟨204847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22042_204848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22042 ⟨204848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22042
    ⟨204848, by decide⟩ (by decide) (![⟨204758, by decide⟩,⟨204807, by decide⟩,⟨204833, by decide⟩,⟨204847, by decide⟩]) unmarked_context_12_22042_204848 node_context_12_22042_204848
  intro a
  fin_cases a
  · exact context_13_88168_204758
  · exact context_13_88169_204807
  · exact context_13_88170_204833
  · exact context_13_88171_204847

theorem selected_cut_06932 : selected 8 ⟨204866, by decide⟩
    (prefixPartial 13 88172) = some ⟨13, 2, 0, 204866, 88172, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_88172_204866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88172 ⟨204866, by decide⟩ :=
  accepted_of_selected 13 88172 ⟨204866, by decide⟩ ⟨13, 2, 0, 204866, 88172, 1381, 16384⟩
    (by decide) selected_cut_06932

theorem selected_cut_06933 : selected 8 ⟨204893, by decide⟩
    (prefixPartial 13 88173) = some ⟨13, 2, 0, 204893, 88173, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_88173_204893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88173 ⟨204893, by decide⟩ :=
  accepted_of_selected 13 88173 ⟨204893, by decide⟩ ⟨13, 2, 0, 204893, 88173, 2121, 16384⟩
    (by decide) selected_cut_06933

theorem selected_cut_06934 : selected 8 ⟨204912, by decide⟩
    (prefixPartial 13 88174) = some ⟨13, 2, 0, 204912, 88174, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_88174_204912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88174 ⟨204912, by decide⟩ :=
  accepted_of_selected 13 88174 ⟨204912, by decide⟩ ⟨13, 2, 0, 204912, 88174, 1433, 16384⟩
    (by decide) selected_cut_06934

theorem selected_cut_06935 : selected 8 ⟨204918, by decide⟩
    (prefixPartial 13 88175) = some ⟨13, 2, 0, 204918, 88175, 865, 16384⟩ := by
  decide +kernel

theorem context_13_88175_204918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88175 ⟨204918, by decide⟩ :=
  accepted_of_selected 13 88175 ⟨204918, by decide⟩ ⟨13, 2, 0, 204918, 88175, 865, 16384⟩
    (by decide) selected_cut_06935

theorem unmarked_context_12_22043_204919 : frontier 9 ⟨204919, by decide⟩
    (prefixCache 12 22043) (prefixPartial 12 22043) = false := by
  decide +kernel

theorem node_context_12_22043_204919 : EJMOriginalGlobalDAGData.nodes 9 ⟨204919, by decide⟩ =
    .split (coordinate 12) (![⟨204866, by decide⟩,⟨204893, by decide⟩,⟨204912, by decide⟩,⟨204918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22043_204919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22043 ⟨204919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22043
    ⟨204919, by decide⟩ (by decide) (![⟨204866, by decide⟩,⟨204893, by decide⟩,⟨204912, by decide⟩,⟨204918, by decide⟩]) unmarked_context_12_22043_204919 node_context_12_22043_204919
  intro a
  fin_cases a
  · exact context_13_88172_204866
  · exact context_13_88173_204893
  · exact context_13_88174_204912
  · exact context_13_88175_204918

theorem unmarked_context_11_5510_204920 : frontier 10 ⟨204920, by decide⟩
    (prefixCache 11 5510) (prefixPartial 11 5510) = false := by
  decide +kernel

theorem node_context_11_5510_204920 : EJMOriginalGlobalDAGData.nodes 10 ⟨204920, by decide⟩ =
    .split (coordinate 11) (![⟨204655, by decide⟩,⟨204733, by decide⟩,⟨204848, by decide⟩,⟨204919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5510_204920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5510 ⟨204920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5510
    ⟨204920, by decide⟩ (by decide) (![⟨204655, by decide⟩,⟨204733, by decide⟩,⟨204848, by decide⟩,⟨204919, by decide⟩]) unmarked_context_11_5510_204920 node_context_11_5510_204920
  intro a
  fin_cases a
  · exact context_12_22040_204655
  · exact context_12_22041_204733
  · exact context_12_22042_204848
  · exact context_12_22043_204919

theorem selected_cut_06936 : selected 8 ⟨204934, by decide⟩
    (prefixPartial 13 88176) = some ⟨13, 2, 0, 204934, 88176, 985, 16384⟩ := by
  decide +kernel

theorem context_13_88176_204934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88176 ⟨204934, by decide⟩ :=
  accepted_of_selected 13 88176 ⟨204934, by decide⟩ ⟨13, 2, 0, 204934, 88176, 985, 16384⟩
    (by decide) selected_cut_06936

theorem selected_cut_06937 : selected 8 ⟨204962, by decide⟩
    (prefixPartial 13 88177) = some ⟨13, 2, 0, 204962, 88177, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_88177_204962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88177 ⟨204962, by decide⟩ :=
  accepted_of_selected 13 88177 ⟨204962, by decide⟩ ⟨13, 2, 0, 204962, 88177, 2009, 16384⟩
    (by decide) selected_cut_06937

theorem selected_cut_06938 : selected 8 ⟨204983, by decide⟩
    (prefixPartial 13 88178) = some ⟨13, 2, 0, 204983, 88178, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_88178_204983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88178 ⟨204983, by decide⟩ :=
  accepted_of_selected 13 88178 ⟨204983, by decide⟩ ⟨13, 2, 0, 204983, 88178, 1725, 16384⟩
    (by decide) selected_cut_06938

theorem selected_cut_06939 : selected 8 ⟨204991, by decide⟩
    (prefixPartial 13 88179) = some ⟨13, 2, 0, 204991, 88179, 873, 16384⟩ := by
  decide +kernel

theorem context_13_88179_204991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88179 ⟨204991, by decide⟩ :=
  accepted_of_selected 13 88179 ⟨204991, by decide⟩ ⟨13, 2, 0, 204991, 88179, 873, 16384⟩
    (by decide) selected_cut_06939

theorem unmarked_context_12_22044_204992 : frontier 9 ⟨204992, by decide⟩
    (prefixCache 12 22044) (prefixPartial 12 22044) = false := by
  decide +kernel

theorem node_context_12_22044_204992 : EJMOriginalGlobalDAGData.nodes 9 ⟨204992, by decide⟩ =
    .split (coordinate 12) (![⟨204934, by decide⟩,⟨204962, by decide⟩,⟨204983, by decide⟩,⟨204991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22044_204992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22044 ⟨204992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22044
    ⟨204992, by decide⟩ (by decide) (![⟨204934, by decide⟩,⟨204962, by decide⟩,⟨204983, by decide⟩,⟨204991, by decide⟩]) unmarked_context_12_22044_204992 node_context_12_22044_204992
  intro a
  fin_cases a
  · exact context_13_88176_204934
  · exact context_13_88177_204962
  · exact context_13_88178_204983
  · exact context_13_88179_204991

theorem selected_cut_06940 : selected 8 ⟨205010, by decide⟩
    (prefixPartial 13 88180) = some ⟨13, 2, 0, 205010, 88180, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_88180_205010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88180 ⟨205010, by decide⟩ :=
  accepted_of_selected 13 88180 ⟨205010, by decide⟩ ⟨13, 2, 0, 205010, 88180, 1105, 16384⟩
    (by decide) selected_cut_06940

theorem selected_cut_06941 : selected 8 ⟨205037, by decide⟩
    (prefixPartial 13 88181) = some ⟨13, 2, 0, 205037, 88181, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_88181_205037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88181 ⟨205037, by decide⟩ :=
  accepted_of_selected 13 88181 ⟨205037, by decide⟩ ⟨13, 2, 0, 205037, 88181, 1501, 16384⟩
    (by decide) selected_cut_06941

theorem selected_cut_06942 : selected 8 ⟨205059, by decide⟩
    (prefixPartial 13 88182) = some ⟨13, 2, 0, 205059, 88182, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_88182_205059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88182 ⟨205059, by decide⟩ :=
  accepted_of_selected 13 88182 ⟨205059, by decide⟩ ⟨13, 2, 0, 205059, 88182, 1521, 16384⟩
    (by decide) selected_cut_06942

theorem selected_cut_06943 : selected 8 ⟨205068, by decide⟩
    (prefixPartial 13 88183) = some ⟨13, 2, 0, 205068, 88183, 781, 16384⟩ := by
  decide +kernel

theorem context_13_88183_205068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88183 ⟨205068, by decide⟩ :=
  accepted_of_selected 13 88183 ⟨205068, by decide⟩ ⟨13, 2, 0, 205068, 88183, 781, 16384⟩
    (by decide) selected_cut_06943

theorem unmarked_context_12_22045_205069 : frontier 9 ⟨205069, by decide⟩
    (prefixCache 12 22045) (prefixPartial 12 22045) = false := by
  decide +kernel

theorem node_context_12_22045_205069 : EJMOriginalGlobalDAGData.nodes 9 ⟨205069, by decide⟩ =
    .split (coordinate 12) (![⟨205010, by decide⟩,⟨205037, by decide⟩,⟨205059, by decide⟩,⟨205068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22045_205069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22045 ⟨205069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22045
    ⟨205069, by decide⟩ (by decide) (![⟨205010, by decide⟩,⟨205037, by decide⟩,⟨205059, by decide⟩,⟨205068, by decide⟩]) unmarked_context_12_22045_205069 node_context_12_22045_205069
  intro a
  fin_cases a
  · exact context_13_88180_205010
  · exact context_13_88181_205037
  · exact context_13_88182_205059
  · exact context_13_88183_205068

theorem selected_cut_06944 : selected 8 ⟨205085, by decide⟩
    (prefixPartial 13 88184) = some ⟨13, 2, 0, 205085, 88184, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_88184_205085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88184 ⟨205085, by decide⟩ :=
  accepted_of_selected 13 88184 ⟨205085, by decide⟩ ⟨13, 2, 0, 205085, 88184, 1093, 16384⟩
    (by decide) selected_cut_06944

theorem selected_cut_06945 : selected 8 ⟨205112, by decide⟩
    (prefixPartial 13 88185) = some ⟨13, 2, 0, 205112, 88185, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_88185_205112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88185 ⟨205112, by decide⟩ :=
  accepted_of_selected 13 88185 ⟨205112, by decide⟩ ⟨13, 2, 0, 205112, 88185, 2173, 16384⟩
    (by decide) selected_cut_06945

theorem selected_cut_06946 : selected 8 ⟨205130, by decide⟩
    (prefixPartial 13 88186) = some ⟨13, 2, 0, 205130, 88186, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_88186_205130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88186 ⟨205130, by decide⟩ :=
  accepted_of_selected 13 88186 ⟨205130, by decide⟩ ⟨13, 2, 0, 205130, 88186, 1437, 16384⟩
    (by decide) selected_cut_06946

theorem selected_cut_06947 : selected 8 ⟨205135, by decide⟩
    (prefixPartial 13 88187) = some ⟨13, 2, 0, 205135, 88187, 821, 16384⟩ := by
  decide +kernel

theorem context_13_88187_205135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88187 ⟨205135, by decide⟩ :=
  accepted_of_selected 13 88187 ⟨205135, by decide⟩ ⟨13, 2, 0, 205135, 88187, 821, 16384⟩
    (by decide) selected_cut_06947

theorem unmarked_context_12_22046_205136 : frontier 9 ⟨205136, by decide⟩
    (prefixCache 12 22046) (prefixPartial 12 22046) = false := by
  decide +kernel

theorem node_context_12_22046_205136 : EJMOriginalGlobalDAGData.nodes 9 ⟨205136, by decide⟩ =
    .split (coordinate 12) (![⟨205085, by decide⟩,⟨205112, by decide⟩,⟨205130, by decide⟩,⟨205135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22046_205136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22046 ⟨205136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22046
    ⟨205136, by decide⟩ (by decide) (![⟨205085, by decide⟩,⟨205112, by decide⟩,⟨205130, by decide⟩,⟨205135, by decide⟩]) unmarked_context_12_22046_205136 node_context_12_22046_205136
  intro a
  fin_cases a
  · exact context_13_88184_205085
  · exact context_13_88185_205112
  · exact context_13_88186_205130
  · exact context_13_88187_205135

theorem selected_cut_06948 : selected 8 ⟨205154, by decide⟩
    (prefixPartial 13 88188) = some ⟨13, 2, 0, 205154, 88188, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_88188_205154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88188 ⟨205154, by decide⟩ :=
  accepted_of_selected 13 88188 ⟨205154, by decide⟩ ⟨13, 2, 0, 205154, 88188, 1233, 16384⟩
    (by decide) selected_cut_06948

theorem selected_cut_06949 : selected 8 ⟨205182, by decide⟩
    (prefixPartial 13 88189) = some ⟨13, 2, 0, 205182, 88189, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_88189_205182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88189 ⟨205182, by decide⟩ :=
  accepted_of_selected 13 88189 ⟨205182, by decide⟩ ⟨13, 2, 0, 205182, 88189, 2229, 16384⟩
    (by decide) selected_cut_06949

theorem selected_cut_06950 : selected 8 ⟨205200, by decide⟩
    (prefixPartial 13 88190) = some ⟨13, 2, 0, 205200, 88190, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_88190_205200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88190 ⟨205200, by decide⟩ :=
  accepted_of_selected 13 88190 ⟨205200, by decide⟩ ⟨13, 2, 0, 205200, 88190, 1653, 16384⟩
    (by decide) selected_cut_06950

theorem selected_cut_06951 : selected 8 ⟨205208, by decide⟩
    (prefixPartial 13 88191) = some ⟨13, 2, 0, 205208, 88191, 809, 16384⟩ := by
  decide +kernel

theorem context_13_88191_205208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88191 ⟨205208, by decide⟩ :=
  accepted_of_selected 13 88191 ⟨205208, by decide⟩ ⟨13, 2, 0, 205208, 88191, 809, 16384⟩
    (by decide) selected_cut_06951

theorem unmarked_context_12_22047_205209 : frontier 9 ⟨205209, by decide⟩
    (prefixCache 12 22047) (prefixPartial 12 22047) = false := by
  decide +kernel

theorem node_context_12_22047_205209 : EJMOriginalGlobalDAGData.nodes 9 ⟨205209, by decide⟩ =
    .split (coordinate 12) (![⟨205154, by decide⟩,⟨205182, by decide⟩,⟨205200, by decide⟩,⟨205208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22047_205209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22047 ⟨205209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22047
    ⟨205209, by decide⟩ (by decide) (![⟨205154, by decide⟩,⟨205182, by decide⟩,⟨205200, by decide⟩,⟨205208, by decide⟩]) unmarked_context_12_22047_205209 node_context_12_22047_205209
  intro a
  fin_cases a
  · exact context_13_88188_205154
  · exact context_13_88189_205182
  · exact context_13_88190_205200
  · exact context_13_88191_205208

theorem unmarked_context_11_5511_205210 : frontier 10 ⟨205210, by decide⟩
    (prefixCache 11 5511) (prefixPartial 11 5511) = false := by
  decide +kernel

theorem node_context_11_5511_205210 : EJMOriginalGlobalDAGData.nodes 10 ⟨205210, by decide⟩ =
    .split (coordinate 11) (![⟨204992, by decide⟩,⟨205069, by decide⟩,⟨205136, by decide⟩,⟨205209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5511_205210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5511 ⟨205210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5511
    ⟨205210, by decide⟩ (by decide) (![⟨204992, by decide⟩,⟨205069, by decide⟩,⟨205136, by decide⟩,⟨205209, by decide⟩]) unmarked_context_11_5511_205210 node_context_11_5511_205210
  intro a
  fin_cases a
  · exact context_12_22044_204992
  · exact context_12_22045_205069
  · exact context_12_22046_205136
  · exact context_12_22047_205209

theorem unmarked_context_10_1377_205211 : frontier 11 ⟨205211, by decide⟩
    (prefixCache 10 1377) (prefixPartial 10 1377) = false := by
  decide +kernel

theorem node_context_10_1377_205211 : EJMOriginalGlobalDAGData.nodes 11 ⟨205211, by decide⟩ =
    .split (coordinate 10) (![⟨204136, by decide⟩,⟨204595, by decide⟩,⟨204920, by decide⟩,⟨205210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1377_205211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1377 ⟨205211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1377
    ⟨205211, by decide⟩ (by decide) (![⟨204136, by decide⟩,⟨204595, by decide⟩,⟨204920, by decide⟩,⟨205210, by decide⟩]) unmarked_context_10_1377_205211 node_context_10_1377_205211
  intro a
  fin_cases a
  · exact context_11_5508_204136
  · exact context_11_5509_204595
  · exact context_11_5510_204920
  · exact context_11_5511_205210

theorem selected_cut_06952 : selected 8 ⟨205222, by decide⟩
    (prefixPartial 13 88192) = some ⟨13, 2, 0, 205222, 88192, 973, 16384⟩ := by
  decide +kernel

theorem context_13_88192_205222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88192 ⟨205222, by decide⟩ :=
  accepted_of_selected 13 88192 ⟨205222, by decide⟩ ⟨13, 2, 0, 205222, 88192, 973, 16384⟩
    (by decide) selected_cut_06952

theorem selected_cut_06953 : selected 8 ⟨205245, by decide⟩
    (prefixPartial 13 88193) = some ⟨13, 2, 0, 205245, 88193, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_88193_205245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88193 ⟨205245, by decide⟩ :=
  accepted_of_selected 13 88193 ⟨205245, by decide⟩ ⟨13, 2, 0, 205245, 88193, 1865, 16384⟩
    (by decide) selected_cut_06953

theorem selected_cut_06954 : selected 8 ⟨205263, by decide⟩
    (prefixPartial 13 88194) = some ⟨13, 2, 0, 205263, 88194, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_88194_205263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88194 ⟨205263, by decide⟩ :=
  accepted_of_selected 13 88194 ⟨205263, by decide⟩ ⟨13, 2, 0, 205263, 88194, 1337, 16384⟩
    (by decide) selected_cut_06954

theorem selected_cut_06955 : selected 8 ⟨205270, by decide⟩
    (prefixPartial 13 88195) = some ⟨13, 2, 0, 205270, 88195, 741, 16384⟩ := by
  decide +kernel

theorem context_13_88195_205270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88195 ⟨205270, by decide⟩ :=
  accepted_of_selected 13 88195 ⟨205270, by decide⟩ ⟨13, 2, 0, 205270, 88195, 741, 16384⟩
    (by decide) selected_cut_06955

theorem unmarked_context_12_22048_205271 : frontier 9 ⟨205271, by decide⟩
    (prefixCache 12 22048) (prefixPartial 12 22048) = false := by
  decide +kernel

theorem node_context_12_22048_205271 : EJMOriginalGlobalDAGData.nodes 9 ⟨205271, by decide⟩ =
    .split (coordinate 12) (![⟨205222, by decide⟩,⟨205245, by decide⟩,⟨205263, by decide⟩,⟨205270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22048_205271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22048 ⟨205271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22048
    ⟨205271, by decide⟩ (by decide) (![⟨205222, by decide⟩,⟨205245, by decide⟩,⟨205263, by decide⟩,⟨205270, by decide⟩]) unmarked_context_12_22048_205271 node_context_12_22048_205271
  intro a
  fin_cases a
  · exact context_13_88192_205222
  · exact context_13_88193_205245
  · exact context_13_88194_205263
  · exact context_13_88195_205270

theorem selected_cut_06956 : selected 8 ⟨205284, by decide⟩
    (prefixPartial 13 88196) = some ⟨13, 2, 0, 205284, 88196, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_88196_205284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88196 ⟨205284, by decide⟩ :=
  accepted_of_selected 13 88196 ⟨205284, by decide⟩ ⟨13, 2, 0, 205284, 88196, 1125, 16384⟩
    (by decide) selected_cut_06956

theorem selected_cut_06957 : selected 8 ⟨205313, by decide⟩
    (prefixPartial 13 88197) = some ⟨13, 2, 0, 205313, 88197, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_88197_205313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88197 ⟨205313, by decide⟩ :=
  accepted_of_selected 13 88197 ⟨205313, by decide⟩ ⟨13, 2, 0, 205313, 88197, 1913, 16384⟩
    (by decide) selected_cut_06957

theorem selected_cut_06958 : selected 8 ⟨205331, by decide⟩
    (prefixPartial 13 88198) = some ⟨13, 2, 0, 205331, 88198, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_88198_205331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88198 ⟨205331, by decide⟩ :=
  accepted_of_selected 13 88198 ⟨205331, by decide⟩ ⟨13, 2, 0, 205331, 88198, 1189, 16384⟩
    (by decide) selected_cut_06958

theorem selected_cut_06959 : selected 8 ⟨205339, by decide⟩
    (prefixPartial 13 88199) = some ⟨13, 2, 0, 205339, 88199, 769, 16384⟩ := by
  decide +kernel

theorem context_13_88199_205339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88199 ⟨205339, by decide⟩ :=
  accepted_of_selected 13 88199 ⟨205339, by decide⟩ ⟨13, 2, 0, 205339, 88199, 769, 16384⟩
    (by decide) selected_cut_06959

theorem unmarked_context_12_22049_205340 : frontier 9 ⟨205340, by decide⟩
    (prefixCache 12 22049) (prefixPartial 12 22049) = false := by
  decide +kernel

theorem node_context_12_22049_205340 : EJMOriginalGlobalDAGData.nodes 9 ⟨205340, by decide⟩ =
    .split (coordinate 12) (![⟨205284, by decide⟩,⟨205313, by decide⟩,⟨205331, by decide⟩,⟨205339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22049_205340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22049 ⟨205340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22049
    ⟨205340, by decide⟩ (by decide) (![⟨205284, by decide⟩,⟨205313, by decide⟩,⟨205331, by decide⟩,⟨205339, by decide⟩]) unmarked_context_12_22049_205340 node_context_12_22049_205340
  intro a
  fin_cases a
  · exact context_13_88196_205284
  · exact context_13_88197_205313
  · exact context_13_88198_205331
  · exact context_13_88199_205339

theorem selected_cut_06960 : selected 8 ⟨205351, by decide⟩
    (prefixPartial 13 88200) = some ⟨13, 2, 0, 205351, 88200, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_88200_205351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88200 ⟨205351, by decide⟩ :=
  accepted_of_selected 13 88200 ⟨205351, by decide⟩ ⟨13, 2, 0, 205351, 88200, 1165, 16384⟩
    (by decide) selected_cut_06960

theorem selected_cut_06961 : selected 8 ⟨205379, by decide⟩
    (prefixPartial 13 88201) = some ⟨13, 2, 0, 205379, 88201, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_88201_205379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88201 ⟨205379, by decide⟩ :=
  accepted_of_selected 13 88201 ⟨205379, by decide⟩ ⟨13, 2, 0, 205379, 88201, 2205, 16384⟩
    (by decide) selected_cut_06961

theorem selected_cut_06962 : selected 8 ⟨205390, by decide⟩
    (prefixPartial 13 88202) = some ⟨13, 2, 0, 205390, 88202, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_88202_205390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88202 ⟨205390, by decide⟩ :=
  accepted_of_selected 13 88202 ⟨205390, by decide⟩ ⟨13, 2, 0, 205390, 88202, 1049, 16384⟩
    (by decide) selected_cut_06962

theorem selected_cut_06963 : selected 8 ⟨205396, by decide⟩
    (prefixPartial 13 88203) = some ⟨13, 2, 0, 205396, 88203, 801, 16384⟩ := by
  decide +kernel

theorem context_13_88203_205396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88203 ⟨205396, by decide⟩ :=
  accepted_of_selected 13 88203 ⟨205396, by decide⟩ ⟨13, 2, 0, 205396, 88203, 801, 16384⟩
    (by decide) selected_cut_06963

theorem unmarked_context_12_22050_205397 : frontier 9 ⟨205397, by decide⟩
    (prefixCache 12 22050) (prefixPartial 12 22050) = false := by
  decide +kernel

theorem node_context_12_22050_205397 : EJMOriginalGlobalDAGData.nodes 9 ⟨205397, by decide⟩ =
    .split (coordinate 12) (![⟨205351, by decide⟩,⟨205379, by decide⟩,⟨205390, by decide⟩,⟨205396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22050_205397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22050 ⟨205397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22050
    ⟨205397, by decide⟩ (by decide) (![⟨205351, by decide⟩,⟨205379, by decide⟩,⟨205390, by decide⟩,⟨205396, by decide⟩]) unmarked_context_12_22050_205397 node_context_12_22050_205397
  intro a
  fin_cases a
  · exact context_13_88200_205351
  · exact context_13_88201_205379
  · exact context_13_88202_205390
  · exact context_13_88203_205396

theorem selected_cut_06964 : selected 8 ⟨205415, by decide⟩
    (prefixPartial 13 88204) = some ⟨13, 2, 0, 205415, 88204, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_88204_205415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88204 ⟨205415, by decide⟩ :=
  accepted_of_selected 13 88204 ⟨205415, by decide⟩ ⟨13, 2, 0, 205415, 88204, 1201, 16384⟩
    (by decide) selected_cut_06964

theorem selected_cut_06965 : selected 8 ⟨205451, by decide⟩
    (prefixPartial 13 88205) = some ⟨13, 2, 0, 205451, 88205, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_88205_205451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88205 ⟨205451, by decide⟩ :=
  accepted_of_selected 13 88205 ⟨205451, by decide⟩ ⟨13, 2, 0, 205451, 88205, 2493, 16384⟩
    (by decide) selected_cut_06965

theorem selected_cut_06966 : selected 8 ⟨205467, by decide⟩
    (prefixPartial 13 88206) = some ⟨13, 2, 0, 205467, 88206, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_88206_205467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88206 ⟨205467, by decide⟩ :=
  accepted_of_selected 13 88206 ⟨205467, by decide⟩ ⟨13, 2, 0, 205467, 88206, 1301, 16384⟩
    (by decide) selected_cut_06966

theorem selected_cut_06967 : selected 8 ⟨205474, by decide⟩
    (prefixPartial 13 88207) = some ⟨13, 2, 0, 205474, 88207, 757, 16384⟩ := by
  decide +kernel

theorem context_13_88207_205474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88207 ⟨205474, by decide⟩ :=
  accepted_of_selected 13 88207 ⟨205474, by decide⟩ ⟨13, 2, 0, 205474, 88207, 757, 16384⟩
    (by decide) selected_cut_06967

theorem unmarked_context_12_22051_205475 : frontier 9 ⟨205475, by decide⟩
    (prefixCache 12 22051) (prefixPartial 12 22051) = false := by
  decide +kernel

theorem node_context_12_22051_205475 : EJMOriginalGlobalDAGData.nodes 9 ⟨205475, by decide⟩ =
    .split (coordinate 12) (![⟨205415, by decide⟩,⟨205451, by decide⟩,⟨205467, by decide⟩,⟨205474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22051_205475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22051 ⟨205475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22051
    ⟨205475, by decide⟩ (by decide) (![⟨205415, by decide⟩,⟨205451, by decide⟩,⟨205467, by decide⟩,⟨205474, by decide⟩]) unmarked_context_12_22051_205475 node_context_12_22051_205475
  intro a
  fin_cases a
  · exact context_13_88204_205415
  · exact context_13_88205_205451
  · exact context_13_88206_205467
  · exact context_13_88207_205474

theorem unmarked_context_11_5512_205476 : frontier 10 ⟨205476, by decide⟩
    (prefixCache 11 5512) (prefixPartial 11 5512) = false := by
  decide +kernel

theorem node_context_11_5512_205476 : EJMOriginalGlobalDAGData.nodes 10 ⟨205476, by decide⟩ =
    .split (coordinate 11) (![⟨205271, by decide⟩,⟨205340, by decide⟩,⟨205397, by decide⟩,⟨205475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5512_205476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5512 ⟨205476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5512
    ⟨205476, by decide⟩ (by decide) (![⟨205271, by decide⟩,⟨205340, by decide⟩,⟨205397, by decide⟩,⟨205475, by decide⟩]) unmarked_context_11_5512_205476 node_context_11_5512_205476
  intro a
  fin_cases a
  · exact context_12_22048_205271
  · exact context_12_22049_205340
  · exact context_12_22050_205397
  · exact context_12_22051_205475

theorem selected_cut_06968 : selected 8 ⟨205487, by decide⟩
    (prefixPartial 13 88208) = some ⟨13, 2, 0, 205487, 88208, 901, 16384⟩ := by
  decide +kernel

theorem context_13_88208_205487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88208 ⟨205487, by decide⟩ :=
  accepted_of_selected 13 88208 ⟨205487, by decide⟩ ⟨13, 2, 0, 205487, 88208, 901, 16384⟩
    (by decide) selected_cut_06968

theorem selected_cut_06969 : selected 8 ⟨205519, by decide⟩
    (prefixPartial 13 88209) = some ⟨13, 2, 0, 205519, 88209, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_88209_205519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88209 ⟨205519, by decide⟩ :=
  accepted_of_selected 13 88209 ⟨205519, by decide⟩ ⟨13, 2, 0, 205519, 88209, 2409, 16384⟩
    (by decide) selected_cut_06969

theorem selected_cut_06970 : selected 8 ⟨205536, by decide⟩
    (prefixPartial 13 88210) = some ⟨13, 2, 0, 205536, 88210, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_88210_205536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88210 ⟨205536, by decide⟩ :=
  accepted_of_selected 13 88210 ⟨205536, by decide⟩ ⟨13, 2, 0, 205536, 88210, 1393, 16384⟩
    (by decide) selected_cut_06970

theorem selected_cut_06971 : selected 8 ⟨205543, by decide⟩
    (prefixPartial 13 88211) = some ⟨13, 2, 0, 205543, 88211, 773, 16384⟩ := by
  decide +kernel

theorem context_13_88211_205543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88211 ⟨205543, by decide⟩ :=
  accepted_of_selected 13 88211 ⟨205543, by decide⟩ ⟨13, 2, 0, 205543, 88211, 773, 16384⟩
    (by decide) selected_cut_06971

theorem unmarked_context_12_22052_205544 : frontier 9 ⟨205544, by decide⟩
    (prefixCache 12 22052) (prefixPartial 12 22052) = false := by
  decide +kernel

theorem node_context_12_22052_205544 : EJMOriginalGlobalDAGData.nodes 9 ⟨205544, by decide⟩ =
    .split (coordinate 12) (![⟨205487, by decide⟩,⟨205519, by decide⟩,⟨205536, by decide⟩,⟨205543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22052_205544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22052 ⟨205544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22052
    ⟨205544, by decide⟩ (by decide) (![⟨205487, by decide⟩,⟨205519, by decide⟩,⟨205536, by decide⟩,⟨205543, by decide⟩]) unmarked_context_12_22052_205544 node_context_12_22052_205544
  intro a
  fin_cases a
  · exact context_13_88208_205487
  · exact context_13_88209_205519
  · exact context_13_88210_205536
  · exact context_13_88211_205543

theorem selected_cut_06972 : selected 8 ⟨205556, by decide⟩
    (prefixPartial 13 88212) = some ⟨13, 2, 0, 205556, 88212, 881, 16384⟩ := by
  decide +kernel

theorem context_13_88212_205556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88212 ⟨205556, by decide⟩ :=
  accepted_of_selected 13 88212 ⟨205556, by decide⟩ ⟨13, 2, 0, 205556, 88212, 881, 16384⟩
    (by decide) selected_cut_06972

theorem selected_cut_06973 : selected 8 ⟨205581, by decide⟩
    (prefixPartial 13 88213) = some ⟨13, 2, 0, 205581, 88213, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_88213_205581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88213 ⟨205581, by decide⟩ :=
  accepted_of_selected 13 88213 ⟨205581, by decide⟩ ⟨13, 2, 0, 205581, 88213, 1973, 16384⟩
    (by decide) selected_cut_06973

theorem selected_cut_06974 : selected 8 ⟨205600, by decide⟩
    (prefixPartial 13 88214) = some ⟨13, 2, 0, 205600, 88214, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_88214_205600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88214 ⟨205600, by decide⟩ :=
  accepted_of_selected 13 88214 ⟨205600, by decide⟩ ⟨13, 2, 0, 205600, 88214, 1297, 16384⟩
    (by decide) selected_cut_06974

theorem selected_cut_06975 : selected 8 ⟨205606, by decide⟩
    (prefixPartial 13 88215) = some ⟨13, 2, 0, 205606, 88215, 749, 16384⟩ := by
  decide +kernel

theorem context_13_88215_205606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88215 ⟨205606, by decide⟩ :=
  accepted_of_selected 13 88215 ⟨205606, by decide⟩ ⟨13, 2, 0, 205606, 88215, 749, 16384⟩
    (by decide) selected_cut_06975

theorem unmarked_context_12_22053_205607 : frontier 9 ⟨205607, by decide⟩
    (prefixCache 12 22053) (prefixPartial 12 22053) = false := by
  decide +kernel

theorem node_context_12_22053_205607 : EJMOriginalGlobalDAGData.nodes 9 ⟨205607, by decide⟩ =
    .split (coordinate 12) (![⟨205556, by decide⟩,⟨205581, by decide⟩,⟨205600, by decide⟩,⟨205606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22053_205607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22053 ⟨205607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22053
    ⟨205607, by decide⟩ (by decide) (![⟨205556, by decide⟩,⟨205581, by decide⟩,⟨205600, by decide⟩,⟨205606, by decide⟩]) unmarked_context_12_22053_205607 node_context_12_22053_205607
  intro a
  fin_cases a
  · exact context_13_88212_205556
  · exact context_13_88213_205581
  · exact context_13_88214_205600
  · exact context_13_88215_205606

theorem selected_cut_06976 : selected 8 ⟨205618, by decide⟩
    (prefixPartial 13 88216) = some ⟨13, 2, 0, 205618, 88216, 909, 16384⟩ := by
  decide +kernel

theorem context_13_88216_205618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88216 ⟨205618, by decide⟩ :=
  accepted_of_selected 13 88216 ⟨205618, by decide⟩ ⟨13, 2, 0, 205618, 88216, 909, 16384⟩
    (by decide) selected_cut_06976

theorem selected_cut_06977 : selected 8 ⟨205650, by decide⟩
    (prefixPartial 13 88217) = some ⟨13, 2, 0, 205650, 88217, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_88217_205650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88217 ⟨205650, by decide⟩ :=
  accepted_of_selected 13 88217 ⟨205650, by decide⟩ ⟨13, 2, 0, 205650, 88217, 2329, 16384⟩
    (by decide) selected_cut_06977

theorem selected_cut_06978 : selected 8 ⟨205663, by decide⟩
    (prefixPartial 13 88218) = some ⟨13, 2, 0, 205663, 88218, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_88218_205663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88218 ⟨205663, by decide⟩ :=
  accepted_of_selected 13 88218 ⟨205663, by decide⟩ ⟨13, 2, 0, 205663, 88218, 1033, 16384⟩
    (by decide) selected_cut_06978

theorem selected_cut_06979 : selected 8 ⟨205669, by decide⟩
    (prefixPartial 13 88219) = some ⟨13, 2, 0, 205669, 88219, 793, 16384⟩ := by
  decide +kernel

theorem context_13_88219_205669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88219 ⟨205669, by decide⟩ :=
  accepted_of_selected 13 88219 ⟨205669, by decide⟩ ⟨13, 2, 0, 205669, 88219, 793, 16384⟩
    (by decide) selected_cut_06979

theorem unmarked_context_12_22054_205670 : frontier 9 ⟨205670, by decide⟩
    (prefixCache 12 22054) (prefixPartial 12 22054) = false := by
  decide +kernel

theorem node_context_12_22054_205670 : EJMOriginalGlobalDAGData.nodes 9 ⟨205670, by decide⟩ =
    .split (coordinate 12) (![⟨205618, by decide⟩,⟨205650, by decide⟩,⟨205663, by decide⟩,⟨205669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22054_205670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22054 ⟨205670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22054
    ⟨205670, by decide⟩ (by decide) (![⟨205618, by decide⟩,⟨205650, by decide⟩,⟨205663, by decide⟩,⟨205669, by decide⟩]) unmarked_context_12_22054_205670 node_context_12_22054_205670
  intro a
  fin_cases a
  · exact context_13_88216_205618
  · exact context_13_88217_205650
  · exact context_13_88218_205663
  · exact context_13_88219_205669

theorem selected_cut_06980 : selected 8 ⟨205686, by decide⟩
    (prefixPartial 13 88220) = some ⟨13, 2, 0, 205686, 88220, 969, 16384⟩ := by
  decide +kernel

theorem context_13_88220_205686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88220 ⟨205686, by decide⟩ :=
  accepted_of_selected 13 88220 ⟨205686, by decide⟩ ⟨13, 2, 0, 205686, 88220, 969, 16384⟩
    (by decide) selected_cut_06980

theorem selected_cut_06981 : selected 8 ⟨205720, by decide⟩
    (prefixPartial 13 88221) = some ⟨13, 2, 0, 205720, 88221, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_88221_205720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88221 ⟨205720, by decide⟩ :=
  accepted_of_selected 13 88221 ⟨205720, by decide⟩ ⟨13, 2, 0, 205720, 88221, 2541, 16384⟩
    (by decide) selected_cut_06981

theorem selected_cut_06982 : selected 8 ⟨205744, by decide⟩
    (prefixPartial 13 88222) = some ⟨13, 2, 0, 205744, 88222, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_88222_205744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88222 ⟨205744, by decide⟩ :=
  accepted_of_selected 13 88222 ⟨205744, by decide⟩ ⟨13, 2, 0, 205744, 88222, 1509, 16384⟩
    (by decide) selected_cut_06982

theorem selected_cut_06983 : selected 8 ⟨205751, by decide⟩
    (prefixPartial 13 88223) = some ⟨13, 2, 0, 205751, 88223, 709, 16384⟩ := by
  decide +kernel

theorem context_13_88223_205751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88223 ⟨205751, by decide⟩ :=
  accepted_of_selected 13 88223 ⟨205751, by decide⟩ ⟨13, 2, 0, 205751, 88223, 709, 16384⟩
    (by decide) selected_cut_06983

theorem unmarked_context_12_22055_205752 : frontier 9 ⟨205752, by decide⟩
    (prefixCache 12 22055) (prefixPartial 12 22055) = false := by
  decide +kernel

theorem node_context_12_22055_205752 : EJMOriginalGlobalDAGData.nodes 9 ⟨205752, by decide⟩ =
    .split (coordinate 12) (![⟨205686, by decide⟩,⟨205720, by decide⟩,⟨205744, by decide⟩,⟨205751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22055_205752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22055 ⟨205752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22055
    ⟨205752, by decide⟩ (by decide) (![⟨205686, by decide⟩,⟨205720, by decide⟩,⟨205744, by decide⟩,⟨205751, by decide⟩]) unmarked_context_12_22055_205752 node_context_12_22055_205752
  intro a
  fin_cases a
  · exact context_13_88220_205686
  · exact context_13_88221_205720
  · exact context_13_88222_205744
  · exact context_13_88223_205751

theorem unmarked_context_11_5513_205753 : frontier 10 ⟨205753, by decide⟩
    (prefixCache 11 5513) (prefixPartial 11 5513) = false := by
  decide +kernel

theorem node_context_11_5513_205753 : EJMOriginalGlobalDAGData.nodes 10 ⟨205753, by decide⟩ =
    .split (coordinate 11) (![⟨205544, by decide⟩,⟨205607, by decide⟩,⟨205670, by decide⟩,⟨205752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5513_205753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5513 ⟨205753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5513
    ⟨205753, by decide⟩ (by decide) (![⟨205544, by decide⟩,⟨205607, by decide⟩,⟨205670, by decide⟩,⟨205752, by decide⟩]) unmarked_context_11_5513_205753 node_context_11_5513_205753
  intro a
  fin_cases a
  · exact context_12_22052_205544
  · exact context_12_22053_205607
  · exact context_12_22054_205670
  · exact context_12_22055_205752

theorem selected_cut_06984 : selected 8 ⟨205762, by decide⟩
    (prefixPartial 13 88224) = some ⟨13, 2, 0, 205762, 88224, 669, 16384⟩ := by
  decide +kernel

theorem context_13_88224_205762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88224 ⟨205762, by decide⟩ :=
  accepted_of_selected 13 88224 ⟨205762, by decide⟩ ⟨13, 2, 0, 205762, 88224, 669, 16384⟩
    (by decide) selected_cut_06984

theorem selected_cut_06985 : selected 8 ⟨205789, by decide⟩
    (prefixPartial 13 88225) = some ⟨13, 2, 0, 205789, 88225, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_88225_205789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88225 ⟨205789, by decide⟩ :=
  accepted_of_selected 13 88225 ⟨205789, by decide⟩ ⟨13, 2, 0, 205789, 88225, 1993, 16384⟩
    (by decide) selected_cut_06985

theorem selected_cut_06986 : selected 8 ⟨205804, by decide⟩
    (prefixPartial 13 88226) = some ⟨13, 2, 0, 205804, 88226, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_88226_205804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88226 ⟨205804, by decide⟩ :=
  accepted_of_selected 13 88226 ⟨205804, by decide⟩ ⟨13, 2, 0, 205804, 88226, 1309, 16384⟩
    (by decide) selected_cut_06986

theorem selected_cut_06987 : selected 8 ⟨205810, by decide⟩
    (prefixPartial 13 88227) = some ⟨13, 2, 0, 205810, 88227, 805, 16384⟩ := by
  decide +kernel

theorem context_13_88227_205810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88227 ⟨205810, by decide⟩ :=
  accepted_of_selected 13 88227 ⟨205810, by decide⟩ ⟨13, 2, 0, 205810, 88227, 805, 16384⟩
    (by decide) selected_cut_06987

theorem unmarked_context_12_22056_205811 : frontier 9 ⟨205811, by decide⟩
    (prefixCache 12 22056) (prefixPartial 12 22056) = false := by
  decide +kernel

theorem node_context_12_22056_205811 : EJMOriginalGlobalDAGData.nodes 9 ⟨205811, by decide⟩ =
    .split (coordinate 12) (![⟨205762, by decide⟩,⟨205789, by decide⟩,⟨205804, by decide⟩,⟨205810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22056_205811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22056 ⟨205811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22056
    ⟨205811, by decide⟩ (by decide) (![⟨205762, by decide⟩,⟨205789, by decide⟩,⟨205804, by decide⟩,⟨205810, by decide⟩]) unmarked_context_12_22056_205811 node_context_12_22056_205811
  intro a
  fin_cases a
  · exact context_13_88224_205762
  · exact context_13_88225_205789
  · exact context_13_88226_205804
  · exact context_13_88227_205810

theorem selected_cut_06988 : selected 8 ⟨205822, by decide⟩
    (prefixPartial 13 88228) = some ⟨13, 2, 0, 205822, 88228, 793, 16384⟩ := by
  decide +kernel

theorem context_13_88228_205822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88228 ⟨205822, by decide⟩ :=
  accepted_of_selected 13 88228 ⟨205822, by decide⟩ ⟨13, 2, 0, 205822, 88228, 793, 16384⟩
    (by decide) selected_cut_06988

theorem selected_cut_06989 : selected 8 ⟨205845, by decide⟩
    (prefixPartial 13 88229) = some ⟨13, 2, 0, 205845, 88229, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_88229_205845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88229 ⟨205845, by decide⟩ :=
  accepted_of_selected 13 88229 ⟨205845, by decide⟩ ⟨13, 2, 0, 205845, 88229, 1781, 16384⟩
    (by decide) selected_cut_06989

theorem selected_cut_06990 : selected 8 ⟨205865, by decide⟩
    (prefixPartial 13 88230) = some ⟨13, 2, 0, 205865, 88230, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_88230_205865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88230 ⟨205865, by decide⟩ :=
  accepted_of_selected 13 88230 ⟨205865, by decide⟩ ⟨13, 2, 0, 205865, 88230, 1305, 16384⟩
    (by decide) selected_cut_06990

theorem selected_cut_06991 : selected 8 ⟨205874, by decide⟩
    (prefixPartial 13 88231) = some ⟨13, 2, 0, 205874, 88231, 829, 16384⟩ := by
  decide +kernel

theorem context_13_88231_205874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88231 ⟨205874, by decide⟩ :=
  accepted_of_selected 13 88231 ⟨205874, by decide⟩ ⟨13, 2, 0, 205874, 88231, 829, 16384⟩
    (by decide) selected_cut_06991

theorem unmarked_context_12_22057_205875 : frontier 9 ⟨205875, by decide⟩
    (prefixCache 12 22057) (prefixPartial 12 22057) = false := by
  decide +kernel

theorem node_context_12_22057_205875 : EJMOriginalGlobalDAGData.nodes 9 ⟨205875, by decide⟩ =
    .split (coordinate 12) (![⟨205822, by decide⟩,⟨205845, by decide⟩,⟨205865, by decide⟩,⟨205874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22057_205875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22057 ⟨205875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22057
    ⟨205875, by decide⟩ (by decide) (![⟨205822, by decide⟩,⟨205845, by decide⟩,⟨205865, by decide⟩,⟨205874, by decide⟩]) unmarked_context_12_22057_205875 node_context_12_22057_205875
  intro a
  fin_cases a
  · exact context_13_88228_205822
  · exact context_13_88229_205845
  · exact context_13_88230_205865
  · exact context_13_88231_205874

theorem selected_cut_06992 : selected 8 ⟨205893, by decide⟩
    (prefixPartial 13 88232) = some ⟨13, 2, 0, 205893, 88232, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_88232_205893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88232 ⟨205893, by decide⟩ :=
  accepted_of_selected 13 88232 ⟨205893, by decide⟩ ⟨13, 2, 0, 205893, 88232, 1245, 16384⟩
    (by decide) selected_cut_06992

theorem selected_cut_06993 : selected 8 ⟨205945, by decide⟩
    (prefixPartial 13 88233) = some ⟨13, 2, 0, 205945, 88233, 3573, 16384⟩ := by
  decide +kernel

theorem context_13_88233_205945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88233 ⟨205945, by decide⟩ :=
  accepted_of_selected 13 88233 ⟨205945, by decide⟩ ⟨13, 2, 0, 205945, 88233, 3573, 16384⟩
    (by decide) selected_cut_06993

theorem selected_cut_06994 : selected 8 ⟨205974, by decide⟩
    (prefixPartial 13 88234) = some ⟨13, 2, 0, 205974, 88234, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_88234_205974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88234 ⟨205974, by decide⟩ :=
  accepted_of_selected 13 88234 ⟨205974, by decide⟩ ⟨13, 2, 0, 205974, 88234, 1925, 16384⟩
    (by decide) selected_cut_06994

theorem selected_cut_06995 : selected 8 ⟨205984, by decide⟩
    (prefixPartial 13 88235) = some ⟨13, 2, 0, 205984, 88235, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_88235_205984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88235 ⟨205984, by decide⟩ :=
  accepted_of_selected 13 88235 ⟨205984, by decide⟩ ⟨13, 2, 0, 205984, 88235, 1193, 16384⟩
    (by decide) selected_cut_06995

theorem unmarked_context_12_22058_205985 : frontier 9 ⟨205985, by decide⟩
    (prefixCache 12 22058) (prefixPartial 12 22058) = false := by
  decide +kernel

theorem node_context_12_22058_205985 : EJMOriginalGlobalDAGData.nodes 9 ⟨205985, by decide⟩ =
    .split (coordinate 12) (![⟨205893, by decide⟩,⟨205945, by decide⟩,⟨205974, by decide⟩,⟨205984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22058_205985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22058 ⟨205985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22058
    ⟨205985, by decide⟩ (by decide) (![⟨205893, by decide⟩,⟨205945, by decide⟩,⟨205974, by decide⟩,⟨205984, by decide⟩]) unmarked_context_12_22058_205985 node_context_12_22058_205985
  intro a
  fin_cases a
  · exact context_13_88232_205893
  · exact context_13_88233_205945
  · exact context_13_88234_205974
  · exact context_13_88235_205984

theorem selected_cut_06996 : selected 8 ⟨205997, by decide⟩
    (prefixPartial 13 88236) = some ⟨13, 2, 0, 205997, 88236, 773, 16384⟩ := by
  decide +kernel

theorem context_13_88236_205997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88236 ⟨205997, by decide⟩ :=
  accepted_of_selected 13 88236 ⟨205997, by decide⟩ ⟨13, 2, 0, 205997, 88236, 773, 16384⟩
    (by decide) selected_cut_06996

theorem selected_cut_06997 : selected 8 ⟨206026, by decide⟩
    (prefixPartial 13 88237) = some ⟨13, 2, 0, 206026, 88237, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_88237_206026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88237 ⟨206026, by decide⟩ :=
  accepted_of_selected 13 88237 ⟨206026, by decide⟩ ⟨13, 2, 0, 206026, 88237, 2413, 16384⟩
    (by decide) selected_cut_06997

theorem selected_cut_06998 : selected 8 ⟨206049, by decide⟩
    (prefixPartial 13 88238) = some ⟨13, 2, 0, 206049, 88238, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_88238_206049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88238 ⟨206049, by decide⟩ :=
  accepted_of_selected 13 88238 ⟨206049, by decide⟩ ⟨13, 2, 0, 206049, 88238, 1365, 16384⟩
    (by decide) selected_cut_06998

theorem selected_cut_06999 : selected 8 ⟨206056, by decide⟩
    (prefixPartial 13 88239) = some ⟨13, 2, 0, 206056, 88239, 745, 16384⟩ := by
  decide +kernel

theorem context_13_88239_206056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88239 ⟨206056, by decide⟩ :=
  accepted_of_selected 13 88239 ⟨206056, by decide⟩ ⟨13, 2, 0, 206056, 88239, 745, 16384⟩
    (by decide) selected_cut_06999

theorem unmarked_context_12_22059_206057 : frontier 9 ⟨206057, by decide⟩
    (prefixCache 12 22059) (prefixPartial 12 22059) = false := by
  decide +kernel

theorem node_context_12_22059_206057 : EJMOriginalGlobalDAGData.nodes 9 ⟨206057, by decide⟩ =
    .split (coordinate 12) (![⟨205997, by decide⟩,⟨206026, by decide⟩,⟨206049, by decide⟩,⟨206056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22059_206057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22059 ⟨206057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22059
    ⟨206057, by decide⟩ (by decide) (![⟨205997, by decide⟩,⟨206026, by decide⟩,⟨206049, by decide⟩,⟨206056, by decide⟩]) unmarked_context_12_22059_206057 node_context_12_22059_206057
  intro a
  fin_cases a
  · exact context_13_88236_205997
  · exact context_13_88237_206026
  · exact context_13_88238_206049
  · exact context_13_88239_206056

theorem unmarked_context_11_5514_206058 : frontier 10 ⟨206058, by decide⟩
    (prefixCache 11 5514) (prefixPartial 11 5514) = false := by
  decide +kernel

theorem node_context_11_5514_206058 : EJMOriginalGlobalDAGData.nodes 10 ⟨206058, by decide⟩ =
    .split (coordinate 11) (![⟨205811, by decide⟩,⟨205875, by decide⟩,⟨205985, by decide⟩,⟨206057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5514_206058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5514 ⟨206058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5514
    ⟨206058, by decide⟩ (by decide) (![⟨205811, by decide⟩,⟨205875, by decide⟩,⟨205985, by decide⟩,⟨206057, by decide⟩]) unmarked_context_11_5514_206058 node_context_11_5514_206058
  intro a
  fin_cases a
  · exact context_12_22056_205811
  · exact context_12_22057_205875
  · exact context_12_22058_205985
  · exact context_12_22059_206057

theorem selected_cut_07000 : selected 8 ⟨206066, by decide⟩
    (prefixPartial 13 88240) = some ⟨13, 2, 0, 206066, 88240, 525, 16384⟩ := by
  decide +kernel

theorem context_13_88240_206066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88240 ⟨206066, by decide⟩ :=
  accepted_of_selected 13 88240 ⟨206066, by decide⟩ ⟨13, 2, 0, 206066, 88240, 525, 16384⟩
    (by decide) selected_cut_07000

theorem selected_cut_07001 : selected 8 ⟨206091, by decide⟩
    (prefixPartial 13 88241) = some ⟨13, 2, 0, 206091, 88241, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_88241_206091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88241 ⟨206091, by decide⟩ :=
  accepted_of_selected 13 88241 ⟨206091, by decide⟩ ⟨13, 2, 0, 206091, 88241, 2353, 16384⟩
    (by decide) selected_cut_07001

theorem selected_cut_07002 : selected 8 ⟨206107, by decide⟩
    (prefixPartial 13 88242) = some ⟨13, 2, 0, 206107, 88242, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_88242_206107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88242 ⟨206107, by decide⟩ :=
  accepted_of_selected 13 88242 ⟨206107, by decide⟩ ⟨13, 2, 0, 206107, 88242, 1545, 16384⟩
    (by decide) selected_cut_07002

theorem selected_cut_07003 : selected 8 ⟨206112, by decide⟩
    (prefixPartial 13 88243) = some ⟨13, 2, 0, 206112, 88243, 801, 16384⟩ := by
  decide +kernel

theorem context_13_88243_206112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88243 ⟨206112, by decide⟩ :=
  accepted_of_selected 13 88243 ⟨206112, by decide⟩ ⟨13, 2, 0, 206112, 88243, 801, 16384⟩
    (by decide) selected_cut_07003

theorem unmarked_context_12_22060_206113 : frontier 9 ⟨206113, by decide⟩
    (prefixCache 12 22060) (prefixPartial 12 22060) = false := by
  decide +kernel

theorem node_context_12_22060_206113 : EJMOriginalGlobalDAGData.nodes 9 ⟨206113, by decide⟩ =
    .split (coordinate 12) (![⟨206066, by decide⟩,⟨206091, by decide⟩,⟨206107, by decide⟩,⟨206112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22060_206113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22060 ⟨206113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22060
    ⟨206113, by decide⟩ (by decide) (![⟨206066, by decide⟩,⟨206091, by decide⟩,⟨206107, by decide⟩,⟨206112, by decide⟩]) unmarked_context_12_22060_206113 node_context_12_22060_206113
  intro a
  fin_cases a
  · exact context_13_88240_206066
  · exact context_13_88241_206091
  · exact context_13_88242_206107
  · exact context_13_88243_206112

theorem selected_cut_07004 : selected 8 ⟨206121, by decide⟩
    (prefixPartial 13 88244) = some ⟨13, 2, 0, 206121, 88244, 585, 16384⟩ := by
  decide +kernel

theorem context_13_88244_206121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88244 ⟨206121, by decide⟩ :=
  accepted_of_selected 13 88244 ⟨206121, by decide⟩ ⟨13, 2, 0, 206121, 88244, 585, 16384⟩
    (by decide) selected_cut_07004

theorem selected_cut_07005 : selected 8 ⟨206146, by decide⟩
    (prefixPartial 13 88245) = some ⟨13, 2, 0, 206146, 88245, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_88245_206146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88245 ⟨206146, by decide⟩ :=
  accepted_of_selected 13 88245 ⟨206146, by decide⟩ ⟨13, 2, 0, 206146, 88245, 2077, 16384⟩
    (by decide) selected_cut_07005

theorem selected_cut_07006 : selected 8 ⟨206166, by decide⟩
    (prefixPartial 13 88246) = some ⟨13, 2, 0, 206166, 88246, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_88246_206166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88246 ⟨206166, by decide⟩ :=
  accepted_of_selected 13 88246 ⟨206166, by decide⟩ ⟨13, 2, 0, 206166, 88246, 1485, 16384⟩
    (by decide) selected_cut_07006

theorem selected_cut_07007 : selected 8 ⟨206172, by decide⟩
    (prefixPartial 13 88247) = some ⟨13, 2, 0, 206172, 88247, 757, 16384⟩ := by
  decide +kernel

theorem context_13_88247_206172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88247 ⟨206172, by decide⟩ :=
  accepted_of_selected 13 88247 ⟨206172, by decide⟩ ⟨13, 2, 0, 206172, 88247, 757, 16384⟩
    (by decide) selected_cut_07007

theorem unmarked_context_12_22061_206173 : frontier 9 ⟨206173, by decide⟩
    (prefixCache 12 22061) (prefixPartial 12 22061) = false := by
  decide +kernel

theorem node_context_12_22061_206173 : EJMOriginalGlobalDAGData.nodes 9 ⟨206173, by decide⟩ =
    .split (coordinate 12) (![⟨206121, by decide⟩,⟨206146, by decide⟩,⟨206166, by decide⟩,⟨206172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22061_206173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22061 ⟨206173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22061
    ⟨206173, by decide⟩ (by decide) (![⟨206121, by decide⟩,⟨206146, by decide⟩,⟨206166, by decide⟩,⟨206172, by decide⟩]) unmarked_context_12_22061_206173 node_context_12_22061_206173
  intro a
  fin_cases a
  · exact context_13_88244_206121
  · exact context_13_88245_206146
  · exact context_13_88246_206166
  · exact context_13_88247_206172

theorem selected_cut_07008 : selected 8 ⟨206182, by decide⟩
    (prefixPartial 13 88248) = some ⟨13, 2, 0, 206182, 88248, 561, 16384⟩ := by
  decide +kernel

theorem context_13_88248_206182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88248 ⟨206182, by decide⟩ :=
  accepted_of_selected 13 88248 ⟨206182, by decide⟩ ⟨13, 2, 0, 206182, 88248, 561, 16384⟩
    (by decide) selected_cut_07008

theorem selected_cut_07009 : selected 8 ⟨206211, by decide⟩
    (prefixPartial 13 88249) = some ⟨13, 2, 0, 206211, 88249, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_88249_206211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88249 ⟨206211, by decide⟩ :=
  accepted_of_selected 13 88249 ⟨206211, by decide⟩ ⟨13, 2, 0, 206211, 88249, 2521, 16384⟩
    (by decide) selected_cut_07009

theorem selected_cut_07010 : selected 8 ⟨206223, by decide⟩
    (prefixPartial 13 88250) = some ⟨13, 2, 0, 206223, 88250, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_88250_206223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88250 ⟨206223, by decide⟩ :=
  accepted_of_selected 13 88250 ⟨206223, by decide⟩ ⟨13, 2, 0, 206223, 88250, 1233, 16384⟩
    (by decide) selected_cut_07010

theorem selected_cut_07011 : selected 8 ⟨206228, by decide⟩
    (prefixPartial 13 88251) = some ⟨13, 2, 0, 206228, 88251, 765, 16384⟩ := by
  decide +kernel

theorem context_13_88251_206228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88251 ⟨206228, by decide⟩ :=
  accepted_of_selected 13 88251 ⟨206228, by decide⟩ ⟨13, 2, 0, 206228, 88251, 765, 16384⟩
    (by decide) selected_cut_07011

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
