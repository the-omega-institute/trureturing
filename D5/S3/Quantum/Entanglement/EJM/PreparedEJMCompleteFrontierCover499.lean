/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover498
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_47908 : selected 10 ⟨1283737, by decide⟩
    (prefixPartial 11 93658) = some ⟨11, 1, 0, 1283737, 93658, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93658_1283737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93658 ⟨1283737, by decide⟩ :=
  accepted_of_selected 11 93658 ⟨1283737, by decide⟩ ⟨11, 1, 0, 1283737, 93658, 1, 262144⟩
    (by decide) selected_cut_47908

theorem selected_cut_47909 : selected 10 ⟨1341805, by decide⟩
    (prefixPartial 11 93659) = some ⟨11, 2, 0, 1341805, 93659, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_93659_1341805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93659 ⟨1341805, by decide⟩ :=
  accepted_of_selected 11 93659 ⟨1341805, by decide⟩ ⟨11, 2, 0, 1341805, 93659, 2565, 262144⟩
    (by decide) selected_cut_47909

theorem unmarked_context_10_23414_1341806 : frontier 11 ⟨1341806, by decide⟩
    (prefixCache 10 23414) (prefixPartial 10 23414) = false := by
  decide +kernel

theorem node_context_10_23414_1341806 : EJMOriginalGlobalDAGData.nodes 11 ⟨1341806, by decide⟩ =
    .split (coordinate 10) (![⟨1341700, by decide⟩,⟨1341760, by decide⟩,⟨1283737, by decide⟩,⟨1341805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23414_1341806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23414 ⟨1341806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23414
    ⟨1341806, by decide⟩ (by decide) (![⟨1341700, by decide⟩,⟨1341760, by decide⟩,⟨1283737, by decide⟩,⟨1341805, by decide⟩]) unmarked_context_10_23414_1341806 node_context_10_23414_1341806
  intro a
  fin_cases a
  · exact context_11_93656_1341700
  · exact context_11_93657_1341760
  · exact context_11_93658_1283737
  · exact context_11_93659_1341805

theorem selected_cut_47910 : selected 10 ⟨1341858, by decide⟩
    (prefixPartial 11 93660) = some ⟨11, 2, 0, 1341858, 93660, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_93660_1341858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93660 ⟨1341858, by decide⟩ :=
  accepted_of_selected 11 93660 ⟨1341858, by decide⟩ ⟨11, 2, 0, 1341858, 93660, 3417, 262144⟩
    (by decide) selected_cut_47910

theorem selected_cut_47911 : selected 10 ⟨1341909, by decide⟩
    (prefixPartial 11 93661) = some ⟨11, 2, 0, 1341909, 93661, 2981, 262144⟩ := by
  decide +kernel

theorem context_11_93661_1341909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93661 ⟨1341909, by decide⟩ :=
  accepted_of_selected 11 93661 ⟨1341909, by decide⟩ ⟨11, 2, 0, 1341909, 93661, 2981, 262144⟩
    (by decide) selected_cut_47911

theorem selected_cut_47912 : selected 10 ⟨1341950, by decide⟩
    (prefixPartial 11 93662) = some ⟨11, 2, 0, 1341950, 93662, 2209, 262144⟩ := by
  decide +kernel

theorem context_11_93662_1341950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93662 ⟨1341950, by decide⟩ :=
  accepted_of_selected 11 93662 ⟨1341950, by decide⟩ ⟨11, 2, 0, 1341950, 93662, 2209, 262144⟩
    (by decide) selected_cut_47912

theorem selected_cut_47913 : selected 10 ⟨1284138, by decide⟩
    (prefixPartial 11 93663) = some ⟨11, 1, 0, 1284138, 93663, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93663_1284138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93663 ⟨1284138, by decide⟩ :=
  accepted_of_selected 11 93663 ⟨1284138, by decide⟩ ⟨11, 1, 0, 1284138, 93663, 1, 262144⟩
    (by decide) selected_cut_47913

theorem unmarked_context_10_23415_1341951 : frontier 11 ⟨1341951, by decide⟩
    (prefixCache 10 23415) (prefixPartial 10 23415) = false := by
  decide +kernel

theorem node_context_10_23415_1341951 : EJMOriginalGlobalDAGData.nodes 11 ⟨1341951, by decide⟩ =
    .split (coordinate 10) (![⟨1341858, by decide⟩,⟨1341909, by decide⟩,⟨1341950, by decide⟩,⟨1284138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23415_1341951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23415 ⟨1341951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23415
    ⟨1341951, by decide⟩ (by decide) (![⟨1341858, by decide⟩,⟨1341909, by decide⟩,⟨1341950, by decide⟩,⟨1284138, by decide⟩]) unmarked_context_10_23415_1341951 node_context_10_23415_1341951
  intro a
  fin_cases a
  · exact context_11_93660_1341858
  · exact context_11_93661_1341909
  · exact context_11_93662_1341950
  · exact context_11_93663_1284138

theorem unmarked_context_9_5853_1341952 : frontier 12 ⟨1341952, by decide⟩
    (prefixCache 9 5853) (prefixPartial 9 5853) = false := by
  decide +kernel

theorem node_context_9_5853_1341952 : EJMOriginalGlobalDAGData.nodes 12 ⟨1341952, by decide⟩ =
    .split (coordinate 9) (![⟨1341631, by decide⟩,⟨893098, by decide⟩,⟨1341806, by decide⟩,⟨1341951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5853_1341952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5853 ⟨1341952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5853
    ⟨1341952, by decide⟩ (by decide) (![⟨1341631, by decide⟩,⟨893098, by decide⟩,⟨1341806, by decide⟩,⟨1341951, by decide⟩]) unmarked_context_9_5853_1341952 node_context_9_5853_1341952
  intro a
  fin_cases a
  · exact context_10_23412_1341631
  · exact context_10_23413_893098
  · exact context_10_23414_1341806
  · exact context_10_23415_1341951

theorem selected_cut_47914 : selected 10 ⟨1341987, by decide⟩
    (prefixPartial 11 93664) = some ⟨11, 2, 0, 1341987, 93664, 1233, 262144⟩ := by
  decide +kernel

theorem context_11_93664_1341987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93664 ⟨1341987, by decide⟩ :=
  accepted_of_selected 11 93664 ⟨1341987, by decide⟩ ⟨11, 2, 0, 1341987, 93664, 1233, 262144⟩
    (by decide) selected_cut_47914

theorem selected_cut_47915 : selected 10 ⟨1342028, by decide⟩
    (prefixPartial 11 93665) = some ⟨11, 2, 0, 1342028, 93665, 2609, 262144⟩ := by
  decide +kernel

theorem context_11_93665_1342028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93665 ⟨1342028, by decide⟩ :=
  accepted_of_selected 11 93665 ⟨1342028, by decide⟩ ⟨11, 2, 0, 1342028, 93665, 2609, 262144⟩
    (by decide) selected_cut_47915

theorem selected_cut_47916 : selected 10 ⟨1342077, by decide⟩
    (prefixPartial 11 93666) = some ⟨11, 2, 0, 1342077, 93666, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_93666_1342077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93666 ⟨1342077, by decide⟩ :=
  accepted_of_selected 11 93666 ⟨1342077, by decide⟩ ⟨11, 2, 0, 1342077, 93666, 2521, 262144⟩
    (by decide) selected_cut_47916

theorem selected_cut_47917 : selected 10 ⟨1342100, by decide⟩
    (prefixPartial 11 93667) = some ⟨11, 2, 0, 1342100, 93667, 1389, 262144⟩ := by
  decide +kernel

theorem context_11_93667_1342100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93667 ⟨1342100, by decide⟩ :=
  accepted_of_selected 11 93667 ⟨1342100, by decide⟩ ⟨11, 2, 0, 1342100, 93667, 1389, 262144⟩
    (by decide) selected_cut_47917

theorem unmarked_context_10_23416_1342101 : frontier 11 ⟨1342101, by decide⟩
    (prefixCache 10 23416) (prefixPartial 10 23416) = false := by
  decide +kernel

theorem node_context_10_23416_1342101 : EJMOriginalGlobalDAGData.nodes 11 ⟨1342101, by decide⟩ =
    .split (coordinate 10) (![⟨1341987, by decide⟩,⟨1342028, by decide⟩,⟨1342077, by decide⟩,⟨1342100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23416_1342101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23416 ⟨1342101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23416
    ⟨1342101, by decide⟩ (by decide) (![⟨1341987, by decide⟩,⟨1342028, by decide⟩,⟨1342077, by decide⟩,⟨1342100, by decide⟩]) unmarked_context_10_23416_1342101 node_context_10_23416_1342101
  intro a
  fin_cases a
  · exact context_11_93664_1341987
  · exact context_11_93665_1342028
  · exact context_11_93666_1342077
  · exact context_11_93667_1342100

theorem selected_cut_47918 : selected 10 ⟨1342122, by decide⟩
    (prefixPartial 11 93668) = some ⟨11, 2, 0, 1342122, 93668, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_93668_1342122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93668 ⟨1342122, by decide⟩ :=
  accepted_of_selected 11 93668 ⟨1342122, by decide⟩ ⟨11, 2, 0, 1342122, 93668, 1801, 262144⟩
    (by decide) selected_cut_47918

theorem selected_cut_47919 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93669) = some ⟨11, 1, 0, 892405, 93669, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93669_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93669 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93669 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93669, 1, 262144⟩
    (by decide) selected_cut_47919

theorem selected_cut_47920 : selected 10 ⟨1342142, by decide⟩
    (prefixPartial 11 93670) = some ⟨11, 2, 0, 1342142, 93670, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_93670_1342142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93670 ⟨1342142, by decide⟩ :=
  accepted_of_selected 11 93670 ⟨1342142, by decide⟩ ⟨11, 2, 0, 1342142, 93670, 1757, 262144⟩
    (by decide) selected_cut_47920

theorem selected_cut_47921 : selected 10 ⟨1342161, by decide⟩
    (prefixPartial 11 93671) = some ⟨11, 2, 0, 1342161, 93671, 1061, 262144⟩ := by
  decide +kernel

theorem context_11_93671_1342161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93671 ⟨1342161, by decide⟩ :=
  accepted_of_selected 11 93671 ⟨1342161, by decide⟩ ⟨11, 2, 0, 1342161, 93671, 1061, 262144⟩
    (by decide) selected_cut_47921

theorem unmarked_context_10_23417_1342162 : frontier 11 ⟨1342162, by decide⟩
    (prefixCache 10 23417) (prefixPartial 10 23417) = false := by
  decide +kernel

theorem node_context_10_23417_1342162 : EJMOriginalGlobalDAGData.nodes 11 ⟨1342162, by decide⟩ =
    .split (coordinate 10) (![⟨1342122, by decide⟩,⟨892405, by decide⟩,⟨1342142, by decide⟩,⟨1342161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23417_1342162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23417 ⟨1342162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23417
    ⟨1342162, by decide⟩ (by decide) (![⟨1342122, by decide⟩,⟨892405, by decide⟩,⟨1342142, by decide⟩,⟨1342161, by decide⟩]) unmarked_context_10_23417_1342162 node_context_10_23417_1342162
  intro a
  fin_cases a
  · exact context_11_93668_1342122
  · exact context_11_93669_892405
  · exact context_11_93670_1342142
  · exact context_11_93671_1342161

theorem selected_cut_47922 : selected 11 ⟨1342185, by decide⟩
    (prefixPartial 10 23418) = some ⟨10, 2, 0, 1342185, 23418, 1497, 1048576⟩ := by
  decide +kernel

theorem context_10_23418_1342185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23418 ⟨1342185, by decide⟩ :=
  accepted_of_selected 10 23418 ⟨1342185, by decide⟩ ⟨10, 2, 0, 1342185, 23418, 1497, 1048576⟩
    (by decide) selected_cut_47922

theorem selected_cut_47923 : selected 11 ⟨1342243, by decide⟩
    (prefixPartial 10 23419) = some ⟨10, 2, 0, 1342243, 23419, 4081, 1048576⟩ := by
  decide +kernel

theorem context_10_23419_1342243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23419 ⟨1342243, by decide⟩ :=
  accepted_of_selected 10 23419 ⟨1342243, by decide⟩ ⟨10, 2, 0, 1342243, 23419, 4081, 1048576⟩
    (by decide) selected_cut_47923

theorem unmarked_context_9_5854_1342244 : frontier 12 ⟨1342244, by decide⟩
    (prefixCache 9 5854) (prefixPartial 9 5854) = false := by
  decide +kernel

theorem node_context_9_5854_1342244 : EJMOriginalGlobalDAGData.nodes 12 ⟨1342244, by decide⟩ =
    .split (coordinate 9) (![⟨1342101, by decide⟩,⟨1342162, by decide⟩,⟨1342185, by decide⟩,⟨1342243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5854_1342244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5854 ⟨1342244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5854
    ⟨1342244, by decide⟩ (by decide) (![⟨1342101, by decide⟩,⟨1342162, by decide⟩,⟨1342185, by decide⟩,⟨1342243, by decide⟩]) unmarked_context_9_5854_1342244 node_context_9_5854_1342244
  intro a
  fin_cases a
  · exact context_10_23416_1342101
  · exact context_10_23417_1342162
  · exact context_10_23418_1342185
  · exact context_10_23419_1342243

theorem selected_cut_47924 : selected 11 ⟨1342299, by decide⟩
    (prefixPartial 10 23420) = some ⟨10, 2, 0, 1342299, 23420, 2901, 1048576⟩ := by
  decide +kernel

theorem context_10_23420_1342299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23420 ⟨1342299, by decide⟩ :=
  accepted_of_selected 10 23420 ⟨1342299, by decide⟩ ⟨10, 2, 0, 1342299, 23420, 2901, 1048576⟩
    (by decide) selected_cut_47924

theorem selected_cut_47925 : selected 11 ⟨1342331, by decide⟩
    (prefixPartial 10 23421) = some ⟨10, 2, 0, 1342331, 23421, 1561, 1048576⟩ := by
  decide +kernel

theorem context_10_23421_1342331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23421 ⟨1342331, by decide⟩ :=
  accepted_of_selected 10 23421 ⟨1342331, by decide⟩ ⟨10, 2, 0, 1342331, 23421, 1561, 1048576⟩
    (by decide) selected_cut_47925

theorem selected_cut_47926 : selected 11 ⟨1342360, by decide⟩
    (prefixPartial 10 23422) = some ⟨10, 2, 0, 1342360, 23422, 777, 1048576⟩ := by
  decide +kernel

theorem context_10_23422_1342360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23422 ⟨1342360, by decide⟩ :=
  accepted_of_selected 10 23422 ⟨1342360, by decide⟩ ⟨10, 2, 0, 1342360, 23422, 777, 1048576⟩
    (by decide) selected_cut_47926

theorem selected_cut_47927 : selected 11 ⟨1342369, by decide⟩
    (prefixPartial 10 23423) = some ⟨10, 2, 0, 1342369, 23423, 77, 1048576⟩ := by
  decide +kernel

theorem context_10_23423_1342369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23423 ⟨1342369, by decide⟩ :=
  accepted_of_selected 10 23423 ⟨1342369, by decide⟩ ⟨10, 2, 0, 1342369, 23423, 77, 1048576⟩
    (by decide) selected_cut_47927

theorem unmarked_context_9_5855_1342370 : frontier 12 ⟨1342370, by decide⟩
    (prefixCache 9 5855) (prefixPartial 9 5855) = false := by
  decide +kernel

theorem node_context_9_5855_1342370 : EJMOriginalGlobalDAGData.nodes 12 ⟨1342370, by decide⟩ =
    .split (coordinate 9) (![⟨1342299, by decide⟩,⟨1342331, by decide⟩,⟨1342360, by decide⟩,⟨1342369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5855_1342370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5855 ⟨1342370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5855
    ⟨1342370, by decide⟩ (by decide) (![⟨1342299, by decide⟩,⟨1342331, by decide⟩,⟨1342360, by decide⟩,⟨1342369, by decide⟩]) unmarked_context_9_5855_1342370 node_context_9_5855_1342370
  intro a
  fin_cases a
  · exact context_10_23420_1342299
  · exact context_10_23421_1342331
  · exact context_10_23422_1342360
  · exact context_10_23423_1342369

theorem unmarked_context_8_1463_1342371 : frontier 13 ⟨1342371, by decide⟩
    (prefixCache 8 1463) (prefixPartial 8 1463) = false := by
  decide +kernel

theorem node_context_8_1463_1342371 : EJMOriginalGlobalDAGData.nodes 13 ⟨1342371, by decide⟩ =
    .split (coordinate 8) (![⟨1341303, by decide⟩,⟨1341952, by decide⟩,⟨1342244, by decide⟩,⟨1342370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1463_1342371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1463 ⟨1342371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1463
    ⟨1342371, by decide⟩ (by decide) (![⟨1341303, by decide⟩,⟨1341952, by decide⟩,⟨1342244, by decide⟩,⟨1342370, by decide⟩]) unmarked_context_8_1463_1342371 node_context_8_1463_1342371
  intro a
  fin_cases a
  · exact context_9_5852_1341303
  · exact context_9_5853_1341952
  · exact context_9_5854_1342244
  · exact context_9_5855_1342370

theorem unmarked_context_7_365_1342372 : frontier 14 ⟨1342372, by decide⟩
    (prefixCache 7 365) (prefixPartial 7 365) = false := by
  decide +kernel

theorem node_context_7_365_1342372 : EJMOriginalGlobalDAGData.nodes 14 ⟨1342372, by decide⟩ =
    .split (coordinate 7) (![⟨1334617, by decide⟩,⟨1336925, by decide⟩,⟨1339896, by decide⟩,⟨1342371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_365_1342372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 365 ⟨1342372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 365
    ⟨1342372, by decide⟩ (by decide) (![⟨1334617, by decide⟩,⟨1336925, by decide⟩,⟨1339896, by decide⟩,⟨1342371, by decide⟩]) unmarked_context_7_365_1342372 node_context_7_365_1342372
  intro a
  fin_cases a
  · exact context_8_1460_1334617
  · exact context_8_1461_1336925
  · exact context_8_1462_1339896
  · exact context_8_1463_1342371

theorem selected_cut_47928 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93696) = some ⟨11, 1, 0, 434745, 93696, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93696_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93696 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93696 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93696, 1, 262144⟩
    (by decide) selected_cut_47928

theorem selected_cut_47929 : selected 10 ⟨1342439, by decide⟩
    (prefixPartial 11 93697) = some ⟨11, 2, 0, 1342439, 93697, 1869, 262144⟩ := by
  decide +kernel

theorem context_11_93697_1342439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93697 ⟨1342439, by decide⟩ :=
  accepted_of_selected 11 93697 ⟨1342439, by decide⟩ ⟨11, 2, 0, 1342439, 93697, 1869, 262144⟩
    (by decide) selected_cut_47929

theorem selected_cut_47930 : selected 10 ⟨1342507, by decide⟩
    (prefixPartial 11 93698) = some ⟨11, 2, 0, 1342507, 93698, 2929, 262144⟩ := by
  decide +kernel

theorem context_11_93698_1342507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93698 ⟨1342507, by decide⟩ :=
  accepted_of_selected 11 93698 ⟨1342507, by decide⟩ ⟨11, 2, 0, 1342507, 93698, 2929, 262144⟩
    (by decide) selected_cut_47930

theorem selected_cut_47931 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 374796) = some ⟨12, 1, 0, 448748, 374796, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374796_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374796 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 374796 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 374796, 1, 65536⟩
    (by decide) selected_cut_47931

theorem selected_cut_47932 : selected 9 ⟨1342581, by decide⟩
    (prefixPartial 12 374797) = some ⟨12, 2, 0, 1342581, 374797, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_374797_1342581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374797 ⟨1342581, by decide⟩ :=
  accepted_of_selected 12 374797 ⟨1342581, by decide⟩ ⟨12, 2, 0, 1342581, 374797, 3401, 65536⟩
    (by decide) selected_cut_47932

theorem selected_cut_47933 : selected 9 ⟨1342665, by decide⟩
    (prefixPartial 12 374798) = some ⟨12, 2, 0, 1342665, 374798, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_374798_1342665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374798 ⟨1342665, by decide⟩ :=
  accepted_of_selected 12 374798 ⟨1342665, by decide⟩ ⟨12, 2, 0, 1342665, 374798, 3309, 65536⟩
    (by decide) selected_cut_47933

theorem selected_cut_47934 : selected 9 ⟨1294595, by decide⟩
    (prefixPartial 12 374799) = some ⟨12, 1, 0, 1294595, 374799, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374799_1294595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374799 ⟨1294595, by decide⟩ :=
  accepted_of_selected 12 374799 ⟨1294595, by decide⟩ ⟨12, 1, 0, 1294595, 374799, 1, 65536⟩
    (by decide) selected_cut_47934

theorem unmarked_context_11_93699_1342666 : frontier 10 ⟨1342666, by decide⟩
    (prefixCache 11 93699) (prefixPartial 11 93699) = false := by
  decide +kernel

theorem node_context_11_93699_1342666 : EJMOriginalGlobalDAGData.nodes 10 ⟨1342666, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1342581, by decide⟩,⟨1342665, by decide⟩,⟨1294595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93699_1342666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93699 ⟨1342666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93699
    ⟨1342666, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1342581, by decide⟩,⟨1342665, by decide⟩,⟨1294595, by decide⟩]) unmarked_context_11_93699_1342666 node_context_11_93699_1342666
  intro a
  fin_cases a
  · exact context_12_374796_448748
  · exact context_12_374797_1342581
  · exact context_12_374798_1342665
  · exact context_12_374799_1294595

theorem unmarked_context_10_23424_1342667 : frontier 11 ⟨1342667, by decide⟩
    (prefixCache 10 23424) (prefixPartial 10 23424) = false := by
  decide +kernel

theorem node_context_10_23424_1342667 : EJMOriginalGlobalDAGData.nodes 11 ⟨1342667, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1342439, by decide⟩,⟨1342507, by decide⟩,⟨1342666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23424_1342667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23424 ⟨1342667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23424
    ⟨1342667, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1342439, by decide⟩,⟨1342507, by decide⟩,⟨1342666, by decide⟩]) unmarked_context_10_23424_1342667 node_context_10_23424_1342667
  intro a
  fin_cases a
  · exact context_11_93696_434745
  · exact context_11_93697_1342439
  · exact context_11_93698_1342507
  · exact context_11_93699_1342666

theorem selected_cut_47935 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 374800) = some ⟨12, 1, 0, 985390, 374800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374800_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374800 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 374800 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 374800, 1, 65536⟩
    (by decide) selected_cut_47935

theorem selected_cut_47936 : selected 9 ⟨1342712, by decide⟩
    (prefixPartial 12 374801) = some ⟨12, 2, 0, 1342712, 374801, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_374801_1342712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374801 ⟨1342712, by decide⟩ :=
  accepted_of_selected 12 374801 ⟨1342712, by decide⟩ ⟨12, 2, 0, 1342712, 374801, 2617, 65536⟩
    (by decide) selected_cut_47936

theorem selected_cut_47937 : selected 9 ⟨1342748, by decide⟩
    (prefixPartial 12 374802) = some ⟨12, 2, 0, 1342748, 374802, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_374802_1342748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374802 ⟨1342748, by decide⟩ :=
  accepted_of_selected 12 374802 ⟨1342748, by decide⟩ ⟨12, 2, 0, 1342748, 374802, 2401, 65536⟩
    (by decide) selected_cut_47937

theorem selected_cut_47938 : selected 9 ⟨1342791, by decide⟩
    (prefixPartial 12 374803) = some ⟨12, 2, 0, 1342791, 374803, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_374803_1342791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374803 ⟨1342791, by decide⟩ :=
  accepted_of_selected 12 374803 ⟨1342791, by decide⟩ ⟨12, 2, 0, 1342791, 374803, 2521, 65536⟩
    (by decide) selected_cut_47938

theorem unmarked_context_11_93700_1342792 : frontier 10 ⟨1342792, by decide⟩
    (prefixCache 11 93700) (prefixPartial 11 93700) = false := by
  decide +kernel

theorem node_context_11_93700_1342792 : EJMOriginalGlobalDAGData.nodes 10 ⟨1342792, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1342712, by decide⟩,⟨1342748, by decide⟩,⟨1342791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93700_1342792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93700 ⟨1342792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93700
    ⟨1342792, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1342712, by decide⟩,⟨1342748, by decide⟩,⟨1342791, by decide⟩]) unmarked_context_11_93700_1342792 node_context_11_93700_1342792
  intro a
  fin_cases a
  · exact context_12_374800_985390
  · exact context_12_374801_1342712
  · exact context_12_374802_1342748
  · exact context_12_374803_1342791

theorem selected_cut_47939 : selected 9 ⟨1342843, by decide⟩
    (prefixPartial 12 374804) = some ⟨12, 2, 0, 1342843, 374804, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_374804_1342843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374804 ⟨1342843, by decide⟩ :=
  accepted_of_selected 12 374804 ⟨1342843, by decide⟩ ⟨12, 2, 0, 1342843, 374804, 2701, 65536⟩
    (by decide) selected_cut_47939

theorem selected_cut_47940 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 374805) = some ⟨12, 1, 0, 1118965, 374805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374805_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374805 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 374805 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 374805, 1, 65536⟩
    (by decide) selected_cut_47940

theorem selected_cut_47941 : selected 9 ⟨333638, by decide⟩
    (prefixPartial 12 374806) = some ⟨12, 1, 0, 333638, 374806, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374806_333638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374806 ⟨333638, by decide⟩ :=
  accepted_of_selected 12 374806 ⟨333638, by decide⟩ ⟨12, 1, 0, 333638, 374806, 1, 65536⟩
    (by decide) selected_cut_47941

theorem selected_cut_47942 : selected 9 ⟨1342889, by decide⟩
    (prefixPartial 12 374807) = some ⟨12, 2, 0, 1342889, 374807, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_374807_1342889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374807 ⟨1342889, by decide⟩ :=
  accepted_of_selected 12 374807 ⟨1342889, by decide⟩ ⟨12, 2, 0, 1342889, 374807, 2773, 65536⟩
    (by decide) selected_cut_47942

theorem unmarked_context_11_93701_1342890 : frontier 10 ⟨1342890, by decide⟩
    (prefixCache 11 93701) (prefixPartial 11 93701) = false := by
  decide +kernel

theorem node_context_11_93701_1342890 : EJMOriginalGlobalDAGData.nodes 10 ⟨1342890, by decide⟩ =
    .split (coordinate 11) (![⟨1342843, by decide⟩,⟨1118965, by decide⟩,⟨333638, by decide⟩,⟨1342889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93701_1342890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93701 ⟨1342890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93701
    ⟨1342890, by decide⟩ (by decide) (![⟨1342843, by decide⟩,⟨1118965, by decide⟩,⟨333638, by decide⟩,⟨1342889, by decide⟩]) unmarked_context_11_93701_1342890 node_context_11_93701_1342890
  intro a
  fin_cases a
  · exact context_12_374804_1342843
  · exact context_12_374805_1118965
  · exact context_12_374806_333638
  · exact context_12_374807_1342889

theorem selected_cut_47943 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 374808) = some ⟨12, 1, 0, 994572, 374808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374808_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374808 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 374808 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 374808, 1, 65536⟩
    (by decide) selected_cut_47943

theorem selected_cut_47944 : selected 9 ⟨1342930, by decide⟩
    (prefixPartial 12 374809) = some ⟨12, 2, 0, 1342930, 374809, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_374809_1342930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374809 ⟨1342930, by decide⟩ :=
  accepted_of_selected 12 374809 ⟨1342930, by decide⟩ ⟨12, 2, 0, 1342930, 374809, 2553, 65536⟩
    (by decide) selected_cut_47944

theorem selected_cut_47945 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 374810) = some ⟨12, 1, 0, 806997, 374810, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374810_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374810 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 374810 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 374810, 1, 65536⟩
    (by decide) selected_cut_47945

theorem selected_cut_47946 : selected 9 ⟨1342975, by decide⟩
    (prefixPartial 12 374811) = some ⟨12, 2, 0, 1342975, 374811, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_374811_1342975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374811 ⟨1342975, by decide⟩ :=
  accepted_of_selected 12 374811 ⟨1342975, by decide⟩ ⟨12, 2, 0, 1342975, 374811, 2633, 65536⟩
    (by decide) selected_cut_47946

theorem unmarked_context_11_93702_1342976 : frontier 10 ⟨1342976, by decide⟩
    (prefixCache 11 93702) (prefixPartial 11 93702) = false := by
  decide +kernel

theorem node_context_11_93702_1342976 : EJMOriginalGlobalDAGData.nodes 10 ⟨1342976, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1342930, by decide⟩,⟨806997, by decide⟩,⟨1342975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93702_1342976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93702 ⟨1342976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93702
    ⟨1342976, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1342930, by decide⟩,⟨806997, by decide⟩,⟨1342975, by decide⟩]) unmarked_context_11_93702_1342976 node_context_11_93702_1342976
  intro a
  fin_cases a
  · exact context_12_374808_994572
  · exact context_12_374809_1342930
  · exact context_12_374810_806997
  · exact context_12_374811_1342975

theorem selected_cut_47947 : selected 9 ⟨1343018, by decide⟩
    (prefixPartial 12 374812) = some ⟨12, 2, 0, 1343018, 374812, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_374812_1343018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374812 ⟨1343018, by decide⟩ :=
  accepted_of_selected 12 374812 ⟨1343018, by decide⟩ ⟨12, 2, 0, 1343018, 374812, 2365, 65536⟩
    (by decide) selected_cut_47947

theorem selected_cut_47948 : selected 9 ⟨1343066, by decide⟩
    (prefixPartial 12 374813) = some ⟨12, 2, 0, 1343066, 374813, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_374813_1343066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374813 ⟨1343066, by decide⟩ :=
  accepted_of_selected 12 374813 ⟨1343066, by decide⟩ ⟨12, 2, 0, 1343066, 374813, 2709, 65536⟩
    (by decide) selected_cut_47948

theorem selected_cut_47949 : selected 9 ⟨1343114, by decide⟩
    (prefixPartial 12 374814) = some ⟨12, 2, 0, 1343114, 374814, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_374814_1343114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374814 ⟨1343114, by decide⟩ :=
  accepted_of_selected 12 374814 ⟨1343114, by decide⟩ ⟨12, 2, 0, 1343114, 374814, 2629, 65536⟩
    (by decide) selected_cut_47949

theorem selected_cut_47950 : selected 9 ⟨1343158, by decide⟩
    (prefixPartial 12 374815) = some ⟨12, 2, 0, 1343158, 374815, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_374815_1343158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374815 ⟨1343158, by decide⟩ :=
  accepted_of_selected 12 374815 ⟨1343158, by decide⟩ ⟨12, 2, 0, 1343158, 374815, 2513, 65536⟩
    (by decide) selected_cut_47950

theorem unmarked_context_11_93703_1343159 : frontier 10 ⟨1343159, by decide⟩
    (prefixCache 11 93703) (prefixPartial 11 93703) = false := by
  decide +kernel

theorem node_context_11_93703_1343159 : EJMOriginalGlobalDAGData.nodes 10 ⟨1343159, by decide⟩ =
    .split (coordinate 11) (![⟨1343018, by decide⟩,⟨1343066, by decide⟩,⟨1343114, by decide⟩,⟨1343158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93703_1343159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93703 ⟨1343159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93703
    ⟨1343159, by decide⟩ (by decide) (![⟨1343018, by decide⟩,⟨1343066, by decide⟩,⟨1343114, by decide⟩,⟨1343158, by decide⟩]) unmarked_context_11_93703_1343159 node_context_11_93703_1343159
  intro a
  fin_cases a
  · exact context_12_374812_1343018
  · exact context_12_374813_1343066
  · exact context_12_374814_1343114
  · exact context_12_374815_1343158

theorem unmarked_context_10_23425_1343160 : frontier 11 ⟨1343160, by decide⟩
    (prefixCache 10 23425) (prefixPartial 10 23425) = false := by
  decide +kernel

theorem node_context_10_23425_1343160 : EJMOriginalGlobalDAGData.nodes 11 ⟨1343160, by decide⟩ =
    .split (coordinate 10) (![⟨1342792, by decide⟩,⟨1342890, by decide⟩,⟨1342976, by decide⟩,⟨1343159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23425_1343160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23425 ⟨1343160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23425
    ⟨1343160, by decide⟩ (by decide) (![⟨1342792, by decide⟩,⟨1342890, by decide⟩,⟨1342976, by decide⟩,⟨1343159, by decide⟩]) unmarked_context_10_23425_1343160 node_context_10_23425_1343160
  intro a
  fin_cases a
  · exact context_11_93700_1342792
  · exact context_11_93701_1342890
  · exact context_11_93702_1342976
  · exact context_11_93703_1343159

theorem selected_cut_47951 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374816) = some ⟨12, 1, 0, 435790, 374816, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374816_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374816 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374816 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374816, 1, 65536⟩
    (by decide) selected_cut_47951

theorem selected_cut_47952 : selected 9 ⟨1343201, by decide⟩
    (prefixPartial 12 374817) = some ⟨12, 2, 0, 1343201, 374817, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_374817_1343201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374817 ⟨1343201, by decide⟩ :=
  accepted_of_selected 12 374817 ⟨1343201, by decide⟩ ⟨12, 2, 0, 1343201, 374817, 2197, 65536⟩
    (by decide) selected_cut_47952

theorem selected_cut_47953 : selected 9 ⟨1343237, by decide⟩
    (prefixPartial 12 374818) = some ⟨12, 2, 0, 1343237, 374818, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_374818_1343237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374818 ⟨1343237, by decide⟩ :=
  accepted_of_selected 12 374818 ⟨1343237, by decide⟩ ⟨12, 2, 0, 1343237, 374818, 2013, 65536⟩
    (by decide) selected_cut_47953

theorem selected_cut_47954 : selected 9 ⟨1343268, by decide⟩
    (prefixPartial 12 374819) = some ⟨12, 2, 0, 1343268, 374819, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_374819_1343268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374819 ⟨1343268, by decide⟩ :=
  accepted_of_selected 12 374819 ⟨1343268, by decide⟩ ⟨12, 2, 0, 1343268, 374819, 2001, 65536⟩
    (by decide) selected_cut_47954

theorem unmarked_context_11_93704_1343269 : frontier 10 ⟨1343269, by decide⟩
    (prefixCache 11 93704) (prefixPartial 11 93704) = false := by
  decide +kernel

theorem node_context_11_93704_1343269 : EJMOriginalGlobalDAGData.nodes 10 ⟨1343269, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1343201, by decide⟩,⟨1343237, by decide⟩,⟨1343268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93704_1343269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93704 ⟨1343269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93704
    ⟨1343269, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1343201, by decide⟩,⟨1343237, by decide⟩,⟨1343268, by decide⟩]) unmarked_context_11_93704_1343269 node_context_11_93704_1343269
  intro a
  fin_cases a
  · exact context_12_374816_435790
  · exact context_12_374817_1343201
  · exact context_12_374818_1343237
  · exact context_12_374819_1343268

theorem selected_cut_47955 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 374820) = some ⟨12, 1, 0, 435790, 374820, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374820_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374820 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 374820 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 374820, 1, 65536⟩
    (by decide) selected_cut_47955

theorem selected_cut_47956 : selected 9 ⟨1321747, by decide⟩
    (prefixPartial 12 374821) = some ⟨12, 1, 0, 1321747, 374821, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374821_1321747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374821 ⟨1321747, by decide⟩ :=
  accepted_of_selected 12 374821 ⟨1321747, by decide⟩ ⟨12, 1, 0, 1321747, 374821, 1, 65536⟩
    (by decide) selected_cut_47956

theorem selected_cut_47957 : selected 9 ⟨1343315, by decide⟩
    (prefixPartial 12 374822) = some ⟨12, 2, 0, 1343315, 374822, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_374822_1343315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374822 ⟨1343315, by decide⟩ :=
  accepted_of_selected 12 374822 ⟨1343315, by decide⟩ ⟨12, 2, 0, 1343315, 374822, 2613, 65536⟩
    (by decide) selected_cut_47957

theorem selected_cut_47958 : selected 9 ⟨1343355, by decide⟩
    (prefixPartial 12 374823) = some ⟨12, 2, 0, 1343355, 374823, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_374823_1343355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374823 ⟨1343355, by decide⟩ :=
  accepted_of_selected 12 374823 ⟨1343355, by decide⟩ ⟨12, 2, 0, 1343355, 374823, 2477, 65536⟩
    (by decide) selected_cut_47958

theorem unmarked_context_11_93705_1343356 : frontier 10 ⟨1343356, by decide⟩
    (prefixCache 11 93705) (prefixPartial 11 93705) = false := by
  decide +kernel

theorem node_context_11_93705_1343356 : EJMOriginalGlobalDAGData.nodes 10 ⟨1343356, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1321747, by decide⟩,⟨1343315, by decide⟩,⟨1343355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93705_1343356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93705 ⟨1343356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93705
    ⟨1343356, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1321747, by decide⟩,⟨1343315, by decide⟩,⟨1343355, by decide⟩]) unmarked_context_11_93705_1343356 node_context_11_93705_1343356
  intro a
  fin_cases a
  · exact context_12_374820_435790
  · exact context_12_374821_1321747
  · exact context_12_374822_1343315
  · exact context_12_374823_1343355

theorem selected_cut_47959 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93706) = some ⟨11, 1, 0, 900587, 93706, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93706_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93706 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93706 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93706, 1, 262144⟩
    (by decide) selected_cut_47959

theorem selected_cut_47960 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 374828) = some ⟨12, 1, 0, 450498, 374828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374828_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374828 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 374828 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 374828, 1, 65536⟩
    (by decide) selected_cut_47960

theorem selected_cut_47961 : selected 9 ⟨1343401, by decide⟩
    (prefixPartial 12 374829) = some ⟨12, 2, 0, 1343401, 374829, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_374829_1343401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374829 ⟨1343401, by decide⟩ :=
  accepted_of_selected 12 374829 ⟨1343401, by decide⟩ ⟨12, 2, 0, 1343401, 374829, 2517, 65536⟩
    (by decide) selected_cut_47961

theorem selected_cut_47962 : selected 9 ⟨1343442, by decide⟩
    (prefixPartial 12 374830) = some ⟨12, 2, 0, 1343442, 374830, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_374830_1343442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374830 ⟨1343442, by decide⟩ :=
  accepted_of_selected 12 374830 ⟨1343442, by decide⟩ ⟨12, 2, 0, 1343442, 374830, 2473, 65536⟩
    (by decide) selected_cut_47962

theorem selected_cut_47963 : selected 9 ⟨1321995, by decide⟩
    (prefixPartial 12 374831) = some ⟨12, 1, 0, 1321995, 374831, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374831_1321995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374831 ⟨1321995, by decide⟩ :=
  accepted_of_selected 12 374831 ⟨1321995, by decide⟩ ⟨12, 1, 0, 1321995, 374831, 1, 65536⟩
    (by decide) selected_cut_47963

theorem unmarked_context_11_93707_1343443 : frontier 10 ⟨1343443, by decide⟩
    (prefixCache 11 93707) (prefixPartial 11 93707) = false := by
  decide +kernel

theorem node_context_11_93707_1343443 : EJMOriginalGlobalDAGData.nodes 10 ⟨1343443, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1343401, by decide⟩,⟨1343442, by decide⟩,⟨1321995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93707_1343443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93707 ⟨1343443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93707
    ⟨1343443, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1343401, by decide⟩,⟨1343442, by decide⟩,⟨1321995, by decide⟩]) unmarked_context_11_93707_1343443 node_context_11_93707_1343443
  intro a
  fin_cases a
  · exact context_12_374828_450498
  · exact context_12_374829_1343401
  · exact context_12_374830_1343442
  · exact context_12_374831_1321995

theorem unmarked_context_10_23426_1343444 : frontier 11 ⟨1343444, by decide⟩
    (prefixCache 10 23426) (prefixPartial 10 23426) = false := by
  decide +kernel

theorem node_context_10_23426_1343444 : EJMOriginalGlobalDAGData.nodes 11 ⟨1343444, by decide⟩ =
    .split (coordinate 10) (![⟨1343269, by decide⟩,⟨1343356, by decide⟩,⟨900587, by decide⟩,⟨1343443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23426_1343444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23426 ⟨1343444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23426
    ⟨1343444, by decide⟩ (by decide) (![⟨1343269, by decide⟩,⟨1343356, by decide⟩,⟨900587, by decide⟩,⟨1343443, by decide⟩]) unmarked_context_10_23426_1343444 node_context_10_23426_1343444
  intro a
  fin_cases a
  · exact context_11_93704_1343269
  · exact context_11_93705_1343356
  · exact context_11_93706_900587
  · exact context_11_93707_1343443

theorem selected_cut_47964 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 374832) = some ⟨12, 1, 0, 985390, 374832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374832_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374832 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 374832 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 374832, 1, 65536⟩
    (by decide) selected_cut_47964

theorem selected_cut_47965 : selected 9 ⟨1343481, by decide⟩
    (prefixPartial 12 374833) = some ⟨12, 2, 0, 1343481, 374833, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_374833_1343481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374833 ⟨1343481, by decide⟩ :=
  accepted_of_selected 12 374833 ⟨1343481, by decide⟩ ⟨12, 2, 0, 1343481, 374833, 2273, 65536⟩
    (by decide) selected_cut_47965

theorem selected_cut_47966 : selected 9 ⟨1343515, by decide⟩
    (prefixPartial 12 374834) = some ⟨12, 2, 0, 1343515, 374834, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_374834_1343515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374834 ⟨1343515, by decide⟩ :=
  accepted_of_selected 12 374834 ⟨1343515, by decide⟩ ⟨12, 2, 0, 1343515, 374834, 2209, 65536⟩
    (by decide) selected_cut_47966

theorem selected_cut_47967 : selected 9 ⟨1343555, by decide⟩
    (prefixPartial 12 374835) = some ⟨12, 2, 0, 1343555, 374835, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_374835_1343555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374835 ⟨1343555, by decide⟩ :=
  accepted_of_selected 12 374835 ⟨1343555, by decide⟩ ⟨12, 2, 0, 1343555, 374835, 2221, 65536⟩
    (by decide) selected_cut_47967

theorem unmarked_context_11_93708_1343556 : frontier 10 ⟨1343556, by decide⟩
    (prefixCache 11 93708) (prefixPartial 11 93708) = false := by
  decide +kernel

theorem node_context_11_93708_1343556 : EJMOriginalGlobalDAGData.nodes 10 ⟨1343556, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1343481, by decide⟩,⟨1343515, by decide⟩,⟨1343555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93708_1343556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93708 ⟨1343556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93708
    ⟨1343556, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1343481, by decide⟩,⟨1343515, by decide⟩,⟨1343555, by decide⟩]) unmarked_context_11_93708_1343556 node_context_11_93708_1343556
  intro a
  fin_cases a
  · exact context_12_374832_985390
  · exact context_12_374833_1343481
  · exact context_12_374834_1343515
  · exact context_12_374835_1343555

theorem selected_cut_47968 : selected 9 ⟨1343606, by decide⟩
    (prefixPartial 12 374836) = some ⟨12, 2, 0, 1343606, 374836, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_374836_1343606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374836 ⟨1343606, by decide⟩ :=
  accepted_of_selected 12 374836 ⟨1343606, by decide⟩ ⟨12, 2, 0, 1343606, 374836, 2573, 65536⟩
    (by decide) selected_cut_47968

theorem selected_cut_47969 : selected 9 ⟨1343651, by decide⟩
    (prefixPartial 12 374837) = some ⟨12, 2, 0, 1343651, 374837, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_374837_1343651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374837 ⟨1343651, by decide⟩ :=
  accepted_of_selected 12 374837 ⟨1343651, by decide⟩ ⟨12, 2, 0, 1343651, 374837, 1329, 65536⟩
    (by decide) selected_cut_47969

theorem selected_cut_47970 : selected 9 ⟨1343695, by decide⟩
    (prefixPartial 12 374838) = some ⟨12, 2, 0, 1343695, 374838, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_374838_1343695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374838 ⟨1343695, by decide⟩ :=
  accepted_of_selected 12 374838 ⟨1343695, by decide⟩ ⟨12, 2, 0, 1343695, 374838, 2473, 65536⟩
    (by decide) selected_cut_47970

theorem selected_cut_47971 : selected 9 ⟨1343735, by decide⟩
    (prefixPartial 12 374839) = some ⟨12, 2, 0, 1343735, 374839, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_374839_1343735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374839 ⟨1343735, by decide⟩ :=
  accepted_of_selected 12 374839 ⟨1343735, by decide⟩ ⟨12, 2, 0, 1343735, 374839, 2437, 65536⟩
    (by decide) selected_cut_47971

theorem unmarked_context_11_93709_1343736 : frontier 10 ⟨1343736, by decide⟩
    (prefixCache 11 93709) (prefixPartial 11 93709) = false := by
  decide +kernel

theorem node_context_11_93709_1343736 : EJMOriginalGlobalDAGData.nodes 10 ⟨1343736, by decide⟩ =
    .split (coordinate 11) (![⟨1343606, by decide⟩,⟨1343651, by decide⟩,⟨1343695, by decide⟩,⟨1343735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93709_1343736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93709 ⟨1343736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93709
    ⟨1343736, by decide⟩ (by decide) (![⟨1343606, by decide⟩,⟨1343651, by decide⟩,⟨1343695, by decide⟩,⟨1343735, by decide⟩]) unmarked_context_11_93709_1343736 node_context_11_93709_1343736
  intro a
  fin_cases a
  · exact context_12_374836_1343606
  · exact context_12_374837_1343651
  · exact context_12_374838_1343695
  · exact context_12_374839_1343735

theorem selected_cut_47972 : selected 10 ⟨1343803, by decide⟩
    (prefixPartial 11 93710) = some ⟨11, 2, 0, 1343803, 93710, 3797, 262144⟩ := by
  decide +kernel

theorem context_11_93710_1343803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93710 ⟨1343803, by decide⟩ :=
  accepted_of_selected 11 93710 ⟨1343803, by decide⟩ ⟨11, 2, 0, 1343803, 93710, 3797, 262144⟩
    (by decide) selected_cut_47972

theorem selected_cut_47973 : selected 10 ⟨1343874, by decide⟩
    (prefixPartial 11 93711) = some ⟨11, 2, 0, 1343874, 93711, 3929, 262144⟩ := by
  decide +kernel

theorem context_11_93711_1343874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93711 ⟨1343874, by decide⟩ :=
  accepted_of_selected 11 93711 ⟨1343874, by decide⟩ ⟨11, 2, 0, 1343874, 93711, 3929, 262144⟩
    (by decide) selected_cut_47973

theorem unmarked_context_10_23427_1343875 : frontier 11 ⟨1343875, by decide⟩
    (prefixCache 10 23427) (prefixPartial 10 23427) = false := by
  decide +kernel

theorem node_context_10_23427_1343875 : EJMOriginalGlobalDAGData.nodes 11 ⟨1343875, by decide⟩ =
    .split (coordinate 10) (![⟨1343556, by decide⟩,⟨1343736, by decide⟩,⟨1343803, by decide⟩,⟨1343874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23427_1343875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23427 ⟨1343875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23427
    ⟨1343875, by decide⟩ (by decide) (![⟨1343556, by decide⟩,⟨1343736, by decide⟩,⟨1343803, by decide⟩,⟨1343874, by decide⟩]) unmarked_context_10_23427_1343875 node_context_10_23427_1343875
  intro a
  fin_cases a
  · exact context_11_93708_1343556
  · exact context_11_93709_1343736
  · exact context_11_93710_1343803
  · exact context_11_93711_1343874

theorem unmarked_context_9_5856_1343876 : frontier 12 ⟨1343876, by decide⟩
    (prefixCache 9 5856) (prefixPartial 9 5856) = false := by
  decide +kernel

theorem node_context_9_5856_1343876 : EJMOriginalGlobalDAGData.nodes 12 ⟨1343876, by decide⟩ =
    .split (coordinate 9) (![⟨1342667, by decide⟩,⟨1343160, by decide⟩,⟨1343444, by decide⟩,⟨1343875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5856_1343876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5856 ⟨1343876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5856
    ⟨1343876, by decide⟩ (by decide) (![⟨1342667, by decide⟩,⟨1343160, by decide⟩,⟨1343444, by decide⟩,⟨1343875, by decide⟩]) unmarked_context_9_5856_1343876 node_context_9_5856_1343876
  intro a
  fin_cases a
  · exact context_10_23424_1342667
  · exact context_10_23425_1343160
  · exact context_10_23426_1343444
  · exact context_10_23427_1343875

theorem selected_cut_47974 : selected 10 ⟨1343931, by decide⟩
    (prefixPartial 11 93712) = some ⟨11, 2, 0, 1343931, 93712, 3401, 262144⟩ := by
  decide +kernel

theorem context_11_93712_1343931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93712 ⟨1343931, by decide⟩ :=
  accepted_of_selected 11 93712 ⟨1343931, by decide⟩ ⟨11, 2, 0, 1343931, 93712, 3401, 262144⟩
    (by decide) selected_cut_47974

theorem selected_cut_47975 : selected 9 ⟨1343968, by decide⟩
    (prefixPartial 12 374852) = some ⟨12, 2, 0, 1343968, 374852, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_374852_1343968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374852 ⟨1343968, by decide⟩ :=
  accepted_of_selected 12 374852 ⟨1343968, by decide⟩ ⟨12, 2, 0, 1343968, 374852, 1973, 65536⟩
    (by decide) selected_cut_47975

theorem selected_cut_47976 : selected 9 ⟨275013, by decide⟩
    (prefixPartial 12 374853) = some ⟨12, 1, 0, 275013, 374853, 1, 65536⟩ := by
  decide +kernel

theorem context_12_374853_275013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374853 ⟨275013, by decide⟩ :=
  accepted_of_selected 12 374853 ⟨275013, by decide⟩ ⟨12, 1, 0, 275013, 374853, 1, 65536⟩
    (by decide) selected_cut_47976

theorem selected_cut_47977 : selected 9 ⟨1344002, by decide⟩
    (prefixPartial 12 374854) = some ⟨12, 2, 0, 1344002, 374854, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_374854_1344002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374854 ⟨1344002, by decide⟩ :=
  accepted_of_selected 12 374854 ⟨1344002, by decide⟩ ⟨12, 2, 0, 1344002, 374854, 1973, 65536⟩
    (by decide) selected_cut_47977

theorem selected_cut_47978 : selected 9 ⟨1344039, by decide⟩
    (prefixPartial 12 374855) = some ⟨12, 2, 0, 1344039, 374855, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_374855_1344039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374855 ⟨1344039, by decide⟩ :=
  accepted_of_selected 12 374855 ⟨1344039, by decide⟩ ⟨12, 2, 0, 1344039, 374855, 1965, 65536⟩
    (by decide) selected_cut_47978

theorem unmarked_context_11_93713_1344040 : frontier 10 ⟨1344040, by decide⟩
    (prefixCache 11 93713) (prefixPartial 11 93713) = false := by
  decide +kernel

theorem node_context_11_93713_1344040 : EJMOriginalGlobalDAGData.nodes 10 ⟨1344040, by decide⟩ =
    .split (coordinate 11) (![⟨1343968, by decide⟩,⟨275013, by decide⟩,⟨1344002, by decide⟩,⟨1344039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93713_1344040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93713 ⟨1344040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93713
    ⟨1344040, by decide⟩ (by decide) (![⟨1343968, by decide⟩,⟨275013, by decide⟩,⟨1344002, by decide⟩,⟨1344039, by decide⟩]) unmarked_context_11_93713_1344040 node_context_11_93713_1344040
  intro a
  fin_cases a
  · exact context_12_374852_1343968
  · exact context_12_374853_275013
  · exact context_12_374854_1344002
  · exact context_12_374855_1344039

theorem selected_cut_47979 : selected 10 ⟨1344102, by decide⟩
    (prefixPartial 11 93714) = some ⟨11, 2, 0, 1344102, 93714, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_93714_1344102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93714 ⟨1344102, by decide⟩ :=
  accepted_of_selected 11 93714 ⟨1344102, by decide⟩ ⟨11, 2, 0, 1344102, 93714, 3181, 262144⟩
    (by decide) selected_cut_47979

theorem selected_cut_47980 : selected 9 ⟨1344134, by decide⟩
    (prefixPartial 12 374860) = some ⟨12, 2, 0, 1344134, 374860, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_374860_1344134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374860 ⟨1344134, by decide⟩ :=
  accepted_of_selected 12 374860 ⟨1344134, by decide⟩ ⟨12, 2, 0, 1344134, 374860, 1689, 65536⟩
    (by decide) selected_cut_47980

theorem selected_cut_47981 : selected 9 ⟨1344159, by decide⟩
    (prefixPartial 12 374861) = some ⟨12, 2, 0, 1344159, 374861, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_374861_1344159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374861 ⟨1344159, by decide⟩ :=
  accepted_of_selected 12 374861 ⟨1344159, by decide⟩ ⟨12, 2, 0, 1344159, 374861, 1605, 65536⟩
    (by decide) selected_cut_47981

theorem selected_cut_47982 : selected 9 ⟨1344197, by decide⟩
    (prefixPartial 12 374862) = some ⟨12, 2, 0, 1344197, 374862, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_374862_1344197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374862 ⟨1344197, by decide⟩ :=
  accepted_of_selected 12 374862 ⟨1344197, by decide⟩ ⟨12, 2, 0, 1344197, 374862, 1765, 65536⟩
    (by decide) selected_cut_47982

theorem selected_cut_47983 : selected 9 ⟨1344233, by decide⟩
    (prefixPartial 12 374863) = some ⟨12, 2, 0, 1344233, 374863, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_374863_1344233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 374863 ⟨1344233, by decide⟩ :=
  accepted_of_selected 12 374863 ⟨1344233, by decide⟩ ⟨12, 2, 0, 1344233, 374863, 1721, 65536⟩
    (by decide) selected_cut_47983

theorem unmarked_context_11_93715_1344234 : frontier 10 ⟨1344234, by decide⟩
    (prefixCache 11 93715) (prefixPartial 11 93715) = false := by
  decide +kernel

theorem node_context_11_93715_1344234 : EJMOriginalGlobalDAGData.nodes 10 ⟨1344234, by decide⟩ =
    .split (coordinate 11) (![⟨1344134, by decide⟩,⟨1344159, by decide⟩,⟨1344197, by decide⟩,⟨1344233, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93715_1344234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93715 ⟨1344234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93715
    ⟨1344234, by decide⟩ (by decide) (![⟨1344134, by decide⟩,⟨1344159, by decide⟩,⟨1344197, by decide⟩,⟨1344233, by decide⟩]) unmarked_context_11_93715_1344234 node_context_11_93715_1344234
  intro a
  fin_cases a
  · exact context_12_374860_1344134
  · exact context_12_374861_1344159
  · exact context_12_374862_1344197
  · exact context_12_374863_1344233

theorem unmarked_context_10_23428_1344235 : frontier 11 ⟨1344235, by decide⟩
    (prefixCache 10 23428) (prefixPartial 10 23428) = false := by
  decide +kernel

theorem node_context_10_23428_1344235 : EJMOriginalGlobalDAGData.nodes 11 ⟨1344235, by decide⟩ =
    .split (coordinate 10) (![⟨1343931, by decide⟩,⟨1344040, by decide⟩,⟨1344102, by decide⟩,⟨1344234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23428_1344235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23428 ⟨1344235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23428
    ⟨1344235, by decide⟩ (by decide) (![⟨1343931, by decide⟩,⟨1344040, by decide⟩,⟨1344102, by decide⟩,⟨1344234, by decide⟩]) unmarked_context_10_23428_1344235 node_context_10_23428_1344235
  intro a
  fin_cases a
  · exact context_11_93712_1343931
  · exact context_11_93713_1344040
  · exact context_11_93714_1344102
  · exact context_11_93715_1344234

theorem selected_cut_47984 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23429) = some ⟨10, 1, 0, 893098, 23429, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23429_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23429 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23429 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23429, 1, 1048576⟩
    (by decide) selected_cut_47984

theorem selected_cut_47985 : selected 10 ⟨1344285, by decide⟩
    (prefixPartial 11 93720) = some ⟨11, 2, 0, 1344285, 93720, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_93720_1344285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93720 ⟨1344285, by decide⟩ :=
  accepted_of_selected 11 93720 ⟨1344285, by decide⟩ ⟨11, 2, 0, 1344285, 93720, 2441, 262144⟩
    (by decide) selected_cut_47985

theorem selected_cut_47986 : selected 10 ⟨1344358, by decide⟩
    (prefixPartial 11 93721) = some ⟨11, 2, 0, 1344358, 93721, 4069, 262144⟩ := by
  decide +kernel

theorem context_11_93721_1344358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93721 ⟨1344358, by decide⟩ :=
  accepted_of_selected 11 93721 ⟨1344358, by decide⟩ ⟨11, 2, 0, 1344358, 93721, 4069, 262144⟩
    (by decide) selected_cut_47986

theorem selected_cut_47987 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93722) = some ⟨11, 1, 0, 900587, 93722, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93722_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93722 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93722 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93722, 1, 262144⟩
    (by decide) selected_cut_47987

theorem selected_cut_47988 : selected 10 ⟨1344421, by decide⟩
    (prefixPartial 11 93723) = some ⟨11, 2, 0, 1344421, 93723, 3561, 262144⟩ := by
  decide +kernel

theorem context_11_93723_1344421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93723 ⟨1344421, by decide⟩ :=
  accepted_of_selected 11 93723 ⟨1344421, by decide⟩ ⟨11, 2, 0, 1344421, 93723, 3561, 262144⟩
    (by decide) selected_cut_47988

theorem unmarked_context_10_23430_1344422 : frontier 11 ⟨1344422, by decide⟩
    (prefixCache 10 23430) (prefixPartial 10 23430) = false := by
  decide +kernel

theorem node_context_10_23430_1344422 : EJMOriginalGlobalDAGData.nodes 11 ⟨1344422, by decide⟩ =
    .split (coordinate 10) (![⟨1344285, by decide⟩,⟨1344358, by decide⟩,⟨900587, by decide⟩,⟨1344421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23430_1344422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23430 ⟨1344422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23430
    ⟨1344422, by decide⟩ (by decide) (![⟨1344285, by decide⟩,⟨1344358, by decide⟩,⟨900587, by decide⟩,⟨1344421, by decide⟩]) unmarked_context_10_23430_1344422 node_context_10_23430_1344422
  intro a
  fin_cases a
  · exact context_11_93720_1344285
  · exact context_11_93721_1344358
  · exact context_11_93722_900587
  · exact context_11_93723_1344421

theorem selected_cut_47989 : selected 10 ⟨1344472, by decide⟩
    (prefixPartial 11 93724) = some ⟨11, 2, 0, 1344472, 93724, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_93724_1344472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93724 ⟨1344472, by decide⟩ :=
  accepted_of_selected 11 93724 ⟨1344472, by decide⟩ ⟨11, 2, 0, 1344472, 93724, 3169, 262144⟩
    (by decide) selected_cut_47989

theorem selected_cut_47990 : selected 10 ⟨1344527, by decide⟩
    (prefixPartial 11 93725) = some ⟨11, 2, 0, 1344527, 93725, 3401, 262144⟩ := by
  decide +kernel

theorem context_11_93725_1344527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93725 ⟨1344527, by decide⟩ :=
  accepted_of_selected 11 93725 ⟨1344527, by decide⟩ ⟨11, 2, 0, 1344527, 93725, 3401, 262144⟩
    (by decide) selected_cut_47990

theorem selected_cut_47991 : selected 10 ⟨1344573, by decide⟩
    (prefixPartial 11 93726) = some ⟨11, 2, 0, 1344573, 93726, 2789, 262144⟩ := by
  decide +kernel

theorem context_11_93726_1344573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93726 ⟨1344573, by decide⟩ :=
  accepted_of_selected 11 93726 ⟨1344573, by decide⟩ ⟨11, 2, 0, 1344573, 93726, 2789, 262144⟩
    (by decide) selected_cut_47991

theorem selected_cut_47992 : selected 10 ⟨1344620, by decide⟩
    (prefixPartial 11 93727) = some ⟨11, 2, 0, 1344620, 93727, 2701, 262144⟩ := by
  decide +kernel

theorem context_11_93727_1344620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93727 ⟨1344620, by decide⟩ :=
  accepted_of_selected 11 93727 ⟨1344620, by decide⟩ ⟨11, 2, 0, 1344620, 93727, 2701, 262144⟩
    (by decide) selected_cut_47992

theorem unmarked_context_10_23431_1344621 : frontier 11 ⟨1344621, by decide⟩
    (prefixCache 10 23431) (prefixPartial 10 23431) = false := by
  decide +kernel

theorem node_context_10_23431_1344621 : EJMOriginalGlobalDAGData.nodes 11 ⟨1344621, by decide⟩ =
    .split (coordinate 10) (![⟨1344472, by decide⟩,⟨1344527, by decide⟩,⟨1344573, by decide⟩,⟨1344620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23431_1344621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23431 ⟨1344621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23431
    ⟨1344621, by decide⟩ (by decide) (![⟨1344472, by decide⟩,⟨1344527, by decide⟩,⟨1344573, by decide⟩,⟨1344620, by decide⟩]) unmarked_context_10_23431_1344621 node_context_10_23431_1344621
  intro a
  fin_cases a
  · exact context_11_93724_1344472
  · exact context_11_93725_1344527
  · exact context_11_93726_1344573
  · exact context_11_93727_1344620

theorem unmarked_context_9_5857_1344622 : frontier 12 ⟨1344622, by decide⟩
    (prefixCache 9 5857) (prefixPartial 9 5857) = false := by
  decide +kernel

theorem node_context_9_5857_1344622 : EJMOriginalGlobalDAGData.nodes 12 ⟨1344622, by decide⟩ =
    .split (coordinate 9) (![⟨1344235, by decide⟩,⟨893098, by decide⟩,⟨1344422, by decide⟩,⟨1344621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5857_1344622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5857 ⟨1344622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5857
    ⟨1344622, by decide⟩ (by decide) (![⟨1344235, by decide⟩,⟨893098, by decide⟩,⟨1344422, by decide⟩,⟨1344621, by decide⟩]) unmarked_context_9_5857_1344622 node_context_9_5857_1344622
  intro a
  fin_cases a
  · exact context_10_23428_1344235
  · exact context_10_23429_893098
  · exact context_10_23430_1344422
  · exact context_10_23431_1344621

theorem selected_cut_47993 : selected 10 ⟨1344623, by decide⟩
    (prefixPartial 11 93728) = some ⟨11, 2, 0, 1344623, 93728, 5, 262144⟩ := by
  decide +kernel

theorem context_11_93728_1344623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93728 ⟨1344623, by decide⟩ :=
  accepted_of_selected 11 93728 ⟨1344623, by decide⟩ ⟨11, 2, 0, 1344623, 93728, 5, 262144⟩
    (by decide) selected_cut_47993

theorem selected_cut_47994 : selected 10 ⟨1344673, by decide⟩
    (prefixPartial 11 93729) = some ⟨11, 2, 0, 1344673, 93729, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_93729_1344673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93729 ⟨1344673, by decide⟩ :=
  accepted_of_selected 11 93729 ⟨1344673, by decide⟩ ⟨11, 2, 0, 1344673, 93729, 2357, 262144⟩
    (by decide) selected_cut_47994

theorem selected_cut_47995 : selected 10 ⟨1344719, by decide⟩
    (prefixPartial 11 93730) = some ⟨11, 2, 0, 1344719, 93730, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_93730_1344719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93730 ⟨1344719, by decide⟩ :=
  accepted_of_selected 11 93730 ⟨1344719, by decide⟩ ⟨11, 2, 0, 1344719, 93730, 2825, 262144⟩
    (by decide) selected_cut_47995

theorem selected_cut_47996 : selected 10 ⟨1344750, by decide⟩
    (prefixPartial 11 93731) = some ⟨11, 2, 0, 1344750, 93731, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_93731_1344750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93731 ⟨1344750, by decide⟩ :=
  accepted_of_selected 11 93731 ⟨1344750, by decide⟩ ⟨11, 2, 0, 1344750, 93731, 1861, 262144⟩
    (by decide) selected_cut_47996

theorem unmarked_context_10_23432_1344751 : frontier 11 ⟨1344751, by decide⟩
    (prefixCache 10 23432) (prefixPartial 10 23432) = false := by
  decide +kernel

theorem node_context_10_23432_1344751 : EJMOriginalGlobalDAGData.nodes 11 ⟨1344751, by decide⟩ =
    .split (coordinate 10) (![⟨1344623, by decide⟩,⟨1344673, by decide⟩,⟨1344719, by decide⟩,⟨1344750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23432_1344751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23432 ⟨1344751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23432
    ⟨1344751, by decide⟩ (by decide) (![⟨1344623, by decide⟩,⟨1344673, by decide⟩,⟨1344719, by decide⟩,⟨1344750, by decide⟩]) unmarked_context_10_23432_1344751 node_context_10_23432_1344751
  intro a
  fin_cases a
  · exact context_11_93728_1344623
  · exact context_11_93729_1344673
  · exact context_11_93730_1344719
  · exact context_11_93731_1344750

theorem selected_cut_47997 : selected 10 ⟨1344773, by decide⟩
    (prefixPartial 11 93732) = some ⟨11, 2, 0, 1344773, 93732, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_93732_1344773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93732 ⟨1344773, by decide⟩ :=
  accepted_of_selected 11 93732 ⟨1344773, by decide⟩ ⟨11, 2, 0, 1344773, 93732, 1653, 262144⟩
    (by decide) selected_cut_47997

theorem selected_cut_47998 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 93733) = some ⟨11, 1, 0, 1192826, 93733, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93733_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93733 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 93733 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 93733, 1, 262144⟩
    (by decide) selected_cut_47998

theorem selected_cut_47999 : selected 10 ⟨1344809, by decide⟩
    (prefixPartial 11 93734) = some ⟨11, 2, 0, 1344809, 93734, 2273, 262144⟩ := by
  decide +kernel

theorem context_11_93734_1344809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93734 ⟨1344809, by decide⟩ :=
  accepted_of_selected 11 93734 ⟨1344809, by decide⟩ ⟨11, 2, 0, 1344809, 93734, 2273, 262144⟩
    (by decide) selected_cut_47999

theorem selected_cut_48000 : selected 10 ⟨1344849, by decide⟩
    (prefixPartial 11 93735) = some ⟨11, 2, 0, 1344849, 93735, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_93735_1344849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93735 ⟨1344849, by decide⟩ :=
  accepted_of_selected 11 93735 ⟨1344849, by decide⟩ ⟨11, 2, 0, 1344849, 93735, 2253, 262144⟩
    (by decide) selected_cut_48000

theorem unmarked_context_10_23433_1344850 : frontier 11 ⟨1344850, by decide⟩
    (prefixCache 10 23433) (prefixPartial 10 23433) = false := by
  decide +kernel

theorem node_context_10_23433_1344850 : EJMOriginalGlobalDAGData.nodes 11 ⟨1344850, by decide⟩ =
    .split (coordinate 10) (![⟨1344773, by decide⟩,⟨1192826, by decide⟩,⟨1344809, by decide⟩,⟨1344849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23433_1344850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23433 ⟨1344850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23433
    ⟨1344850, by decide⟩ (by decide) (![⟨1344773, by decide⟩,⟨1192826, by decide⟩,⟨1344809, by decide⟩,⟨1344849, by decide⟩]) unmarked_context_10_23433_1344850 node_context_10_23433_1344850
  intro a
  fin_cases a
  · exact context_11_93732_1344773
  · exact context_11_93733_1192826
  · exact context_11_93734_1344809
  · exact context_11_93735_1344849

theorem selected_cut_48001 : selected 11 ⟨1344884, by decide⟩
    (prefixPartial 10 23434) = some ⟨10, 2, 0, 1344884, 23434, 1853, 1048576⟩ := by
  decide +kernel

theorem context_10_23434_1344884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23434 ⟨1344884, by decide⟩ :=
  accepted_of_selected 10 23434 ⟨1344884, by decide⟩ ⟨10, 2, 0, 1344884, 23434, 1853, 1048576⟩
    (by decide) selected_cut_48001

theorem selected_cut_48002 : selected 10 ⟨1344900, by decide⟩
    (prefixPartial 11 93740) = some ⟨11, 2, 0, 1344900, 93740, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_93740_1344900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93740 ⟨1344900, by decide⟩ :=
  accepted_of_selected 11 93740 ⟨1344900, by decide⟩ ⟨11, 2, 0, 1344900, 93740, 1101, 262144⟩
    (by decide) selected_cut_48002

theorem selected_cut_48003 : selected 10 ⟨1344935, by decide⟩
    (prefixPartial 11 93741) = some ⟨11, 2, 0, 1344935, 93741, 1785, 262144⟩ := by
  decide +kernel

theorem context_11_93741_1344935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93741 ⟨1344935, by decide⟩ :=
  accepted_of_selected 11 93741 ⟨1344935, by decide⟩ ⟨11, 2, 0, 1344935, 93741, 1785, 262144⟩
    (by decide) selected_cut_48003

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
