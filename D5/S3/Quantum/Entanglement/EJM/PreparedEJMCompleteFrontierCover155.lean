/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover154
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14885 : selected 8 ⟨383022, by decide⟩
    (prefixPartial 13 109823) = some ⟨13, 2, 0, 383022, 109823, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_109823_383022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109823 ⟨383022, by decide⟩ :=
  accepted_of_selected 13 109823 ⟨383022, by decide⟩ ⟨13, 2, 0, 383022, 109823, 1101, 16384⟩
    (by decide) selected_cut_14885

theorem unmarked_context_12_27455_383023 : frontier 9 ⟨383023, by decide⟩
    (prefixCache 12 27455) (prefixPartial 12 27455) = false := by
  decide +kernel

theorem node_context_12_27455_383023 : EJMOriginalGlobalDAGData.nodes 9 ⟨383023, by decide⟩ =
    .split (coordinate 12) (![⟨382901, by decide⟩,⟨382971, by decide⟩,⟨382997, by decide⟩,⟨383022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27455_383023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27455 ⟨383023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27455
    ⟨383023, by decide⟩ (by decide) (![⟨382901, by decide⟩,⟨382971, by decide⟩,⟨382997, by decide⟩,⟨383022, by decide⟩]) unmarked_context_12_27455_383023 node_context_12_27455_383023
  intro a
  fin_cases a
  · exact context_13_109820_382901
  · exact context_13_109821_382971
  · exact context_13_109822_382997
  · exact context_13_109823_383022

theorem unmarked_context_11_6863_383024 : frontier 10 ⟨383024, by decide⟩
    (prefixCache 11 6863) (prefixPartial 11 6863) = false := by
  decide +kernel

theorem node_context_11_6863_383024 : EJMOriginalGlobalDAGData.nodes 10 ⟨383024, by decide⟩ =
    .split (coordinate 11) (![⟨382797, by decide⟩,⟨382846, by decide⟩,⟨382896, by decide⟩,⟨383023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6863_383024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6863 ⟨383024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6863
    ⟨383024, by decide⟩ (by decide) (![⟨382797, by decide⟩,⟨382846, by decide⟩,⟨382896, by decide⟩,⟨383023, by decide⟩]) unmarked_context_11_6863_383024 node_context_11_6863_383024
  intro a
  fin_cases a
  · exact context_12_27452_382797
  · exact context_12_27453_382846
  · exact context_12_27454_382896
  · exact context_12_27455_383023

theorem unmarked_context_10_1715_383025 : frontier 11 ⟨383025, by decide⟩
    (prefixCache 10 1715) (prefixPartial 10 1715) = false := by
  decide +kernel

theorem node_context_10_1715_383025 : EJMOriginalGlobalDAGData.nodes 11 ⟨383025, by decide⟩ =
    .split (coordinate 10) (![⟨382273, by decide⟩,⟨382499, by decide⟩,⟨382743, by decide⟩,⟨383024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1715_383025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1715 ⟨383025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1715
    ⟨383025, by decide⟩ (by decide) (![⟨382273, by decide⟩,⟨382499, by decide⟩,⟨382743, by decide⟩,⟨383024, by decide⟩]) unmarked_context_10_1715_383025 node_context_10_1715_383025
  intro a
  fin_cases a
  · exact context_11_6860_382273
  · exact context_11_6861_382499
  · exact context_11_6862_382743
  · exact context_11_6863_383024

theorem unmarked_context_9_428_383026 : frontier 12 ⟨383026, by decide⟩
    (prefixCache 9 428) (prefixPartial 9 428) = false := by
  decide +kernel

theorem node_context_9_428_383026 : EJMOriginalGlobalDAGData.nodes 12 ⟨383026, by decide⟩ =
    .split (coordinate 9) (![⟨379283, by decide⟩,⟨380641, by decide⟩,⟨382043, by decide⟩,⟨383025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_428_383026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 428 ⟨383026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 428
    ⟨383026, by decide⟩ (by decide) (![⟨379283, by decide⟩,⟨380641, by decide⟩,⟨382043, by decide⟩,⟨383025, by decide⟩]) unmarked_context_9_428_383026 node_context_9_428_383026
  intro a
  fin_cases a
  · exact context_10_1712_379283
  · exact context_10_1713_380641
  · exact context_10_1714_382043
  · exact context_10_1715_383025

theorem selected_cut_14886 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109824) = some ⟨13, 1, 0, 3444, 109824, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109824_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109824 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109824 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109824, 1, 16384⟩
    (by decide) selected_cut_14886

theorem selected_cut_14887 : selected 8 ⟨383078, by decide⟩
    (prefixPartial 13 109825) = some ⟨13, 2, 0, 383078, 109825, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_109825_383078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109825 ⟨383078, by decide⟩ :=
  accepted_of_selected 13 109825 ⟨383078, by decide⟩ ⟨13, 2, 0, 383078, 109825, 3229, 16384⟩
    (by decide) selected_cut_14887

theorem selected_cut_14888 : selected 8 ⟨383100, by decide⟩
    (prefixPartial 13 109826) = some ⟨13, 2, 0, 383100, 109826, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_109826_383100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109826 ⟨383100, by decide⟩ :=
  accepted_of_selected 13 109826 ⟨383100, by decide⟩ ⟨13, 2, 0, 383100, 109826, 1385, 16384⟩
    (by decide) selected_cut_14888

theorem selected_cut_14889 : selected 8 ⟨383106, by decide⟩
    (prefixPartial 13 109827) = some ⟨13, 2, 0, 383106, 109827, 849, 16384⟩ := by
  decide +kernel

theorem context_13_109827_383106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109827 ⟨383106, by decide⟩ :=
  accepted_of_selected 13 109827 ⟨383106, by decide⟩ ⟨13, 2, 0, 383106, 109827, 849, 16384⟩
    (by decide) selected_cut_14889

theorem unmarked_context_12_27456_383107 : frontier 9 ⟨383107, by decide⟩
    (prefixCache 12 27456) (prefixPartial 12 27456) = false := by
  decide +kernel

theorem node_context_12_27456_383107 : EJMOriginalGlobalDAGData.nodes 9 ⟨383107, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383078, by decide⟩,⟨383100, by decide⟩,⟨383106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27456_383107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27456 ⟨383107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27456
    ⟨383107, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383078, by decide⟩,⟨383100, by decide⟩,⟨383106, by decide⟩]) unmarked_context_12_27456_383107 node_context_12_27456_383107
  intro a
  fin_cases a
  · exact context_13_109824_3444
  · exact context_13_109825_383078
  · exact context_13_109826_383100
  · exact context_13_109827_383106

theorem selected_cut_14890 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109828) = some ⟨13, 1, 0, 3444, 109828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109828, 1, 16384⟩
    (by decide) selected_cut_14890

theorem selected_cut_14891 : selected 7 ⟨383138, by decide⟩
    (prefixPartial 14 439316) = some ⟨14, 2, 0, 383138, 439316, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_439316_383138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 439316 ⟨383138, by decide⟩ :=
  accepted_of_selected 14 439316 ⟨383138, by decide⟩ ⟨14, 2, 0, 383138, 439316, 1221, 4096⟩
    (by decide) selected_cut_14891

theorem selected_cut_14892 : selected 7 ⟨383157, by decide⟩
    (prefixPartial 14 439317) = some ⟨14, 2, 0, 383157, 439317, 877, 4096⟩ := by
  decide +kernel

theorem context_14_439317_383157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 439317 ⟨383157, by decide⟩ :=
  accepted_of_selected 14 439317 ⟨383157, by decide⟩ ⟨14, 2, 0, 383157, 439317, 877, 4096⟩
    (by decide) selected_cut_14892

theorem selected_cut_14893 : selected 7 ⟨383185, by decide⟩
    (prefixPartial 14 439318) = some ⟨14, 2, 0, 383185, 439318, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_439318_383185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 439318 ⟨383185, by decide⟩ :=
  accepted_of_selected 14 439318 ⟨383185, by decide⟩ ⟨14, 2, 0, 383185, 439318, 1289, 4096⟩
    (by decide) selected_cut_14893

theorem selected_cut_14894 : selected 7 ⟨383216, by decide⟩
    (prefixPartial 14 439319) = some ⟨14, 2, 0, 383216, 439319, 993, 4096⟩ := by
  decide +kernel

theorem context_14_439319_383216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 439319 ⟨383216, by decide⟩ :=
  accepted_of_selected 14 439319 ⟨383216, by decide⟩ ⟨14, 2, 0, 383216, 439319, 993, 4096⟩
    (by decide) selected_cut_14894

theorem unmarked_context_13_109829_383217 : frontier 8 ⟨383217, by decide⟩
    (prefixCache 13 109829) (prefixPartial 13 109829) = false := by
  decide +kernel

theorem node_context_13_109829_383217 : EJMOriginalGlobalDAGData.nodes 8 ⟨383217, by decide⟩ =
    .split (coordinate 13) (![⟨383138, by decide⟩,⟨383157, by decide⟩,⟨383185, by decide⟩,⟨383216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_109829_383217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109829 ⟨383217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 109829
    ⟨383217, by decide⟩ (by decide) (![⟨383138, by decide⟩,⟨383157, by decide⟩,⟨383185, by decide⟩,⟨383216, by decide⟩]) unmarked_context_13_109829_383217 node_context_13_109829_383217
  intro a
  fin_cases a
  · exact context_14_439316_383138
  · exact context_14_439317_383157
  · exact context_14_439318_383185
  · exact context_14_439319_383216

theorem selected_cut_14895 : selected 8 ⟨383246, by decide⟩
    (prefixPartial 13 109830) = some ⟨13, 2, 0, 383246, 109830, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_109830_383246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109830 ⟨383246, by decide⟩ :=
  accepted_of_selected 13 109830 ⟨383246, by decide⟩ ⟨13, 2, 0, 383246, 109830, 2049, 16384⟩
    (by decide) selected_cut_14895

theorem selected_cut_14896 : selected 8 ⟨383258, by decide⟩
    (prefixPartial 13 109831) = some ⟨13, 2, 0, 383258, 109831, 877, 16384⟩ := by
  decide +kernel

theorem context_13_109831_383258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109831 ⟨383258, by decide⟩ :=
  accepted_of_selected 13 109831 ⟨383258, by decide⟩ ⟨13, 2, 0, 383258, 109831, 877, 16384⟩
    (by decide) selected_cut_14896

theorem unmarked_context_12_27457_383259 : frontier 9 ⟨383259, by decide⟩
    (prefixCache 12 27457) (prefixPartial 12 27457) = false := by
  decide +kernel

theorem node_context_12_27457_383259 : EJMOriginalGlobalDAGData.nodes 9 ⟨383259, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383217, by decide⟩,⟨383246, by decide⟩,⟨383258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27457_383259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27457 ⟨383259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27457
    ⟨383259, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383217, by decide⟩,⟨383246, by decide⟩,⟨383258, by decide⟩]) unmarked_context_12_27457_383259 node_context_12_27457_383259
  intro a
  fin_cases a
  · exact context_13_109828_3444
  · exact context_13_109829_383217
  · exact context_13_109830_383246
  · exact context_13_109831_383258

theorem selected_cut_14897 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109832) = some ⟨13, 1, 0, 3444, 109832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109832, 1, 16384⟩
    (by decide) selected_cut_14897

theorem selected_cut_14898 : selected 8 ⟨383312, by decide⟩
    (prefixPartial 13 109833) = some ⟨13, 2, 0, 383312, 109833, 3309, 16384⟩ := by
  decide +kernel

theorem context_13_109833_383312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109833 ⟨383312, by decide⟩ :=
  accepted_of_selected 13 109833 ⟨383312, by decide⟩ ⟨13, 2, 0, 383312, 109833, 3309, 16384⟩
    (by decide) selected_cut_14898

theorem selected_cut_14899 : selected 8 ⟨383333, by decide⟩
    (prefixPartial 13 109834) = some ⟨13, 2, 0, 383333, 109834, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_109834_383333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109834 ⟨383333, by decide⟩ :=
  accepted_of_selected 13 109834 ⟨383333, by decide⟩ ⟨13, 2, 0, 383333, 109834, 1637, 16384⟩
    (by decide) selected_cut_14899

theorem selected_cut_14900 : selected 8 ⟨383338, by decide⟩
    (prefixPartial 13 109835) = some ⟨13, 2, 0, 383338, 109835, 697, 16384⟩ := by
  decide +kernel

theorem context_13_109835_383338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109835 ⟨383338, by decide⟩ :=
  accepted_of_selected 13 109835 ⟨383338, by decide⟩ ⟨13, 2, 0, 383338, 109835, 697, 16384⟩
    (by decide) selected_cut_14900

theorem unmarked_context_12_27458_383339 : frontier 9 ⟨383339, by decide⟩
    (prefixCache 12 27458) (prefixPartial 12 27458) = false := by
  decide +kernel

theorem node_context_12_27458_383339 : EJMOriginalGlobalDAGData.nodes 9 ⟨383339, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383312, by decide⟩,⟨383333, by decide⟩,⟨383338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27458_383339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27458 ⟨383339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27458
    ⟨383339, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383312, by decide⟩,⟨383333, by decide⟩,⟨383338, by decide⟩]) unmarked_context_12_27458_383339 node_context_12_27458_383339
  intro a
  fin_cases a
  · exact context_13_109832_3444
  · exact context_13_109833_383312
  · exact context_13_109834_383333
  · exact context_13_109835_383338

theorem selected_cut_14901 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109836) = some ⟨13, 1, 0, 3444, 109836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109836, 1, 16384⟩
    (by decide) selected_cut_14901

theorem selected_cut_14902 : selected 8 ⟨383382, by decide⟩
    (prefixPartial 13 109837) = some ⟨13, 2, 0, 383382, 109837, 3237, 16384⟩ := by
  decide +kernel

theorem context_13_109837_383382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109837 ⟨383382, by decide⟩ :=
  accepted_of_selected 13 109837 ⟨383382, by decide⟩ ⟨13, 2, 0, 383382, 109837, 3237, 16384⟩
    (by decide) selected_cut_14902

theorem selected_cut_14903 : selected 8 ⟨383403, by decide⟩
    (prefixPartial 13 109838) = some ⟨13, 2, 0, 383403, 109838, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_109838_383403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109838 ⟨383403, by decide⟩ :=
  accepted_of_selected 13 109838 ⟨383403, by decide⟩ ⟨13, 2, 0, 383403, 109838, 1605, 16384⟩
    (by decide) selected_cut_14903

theorem selected_cut_14904 : selected 8 ⟨383408, by decide⟩
    (prefixPartial 13 109839) = some ⟨13, 2, 0, 383408, 109839, 609, 16384⟩ := by
  decide +kernel

theorem context_13_109839_383408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109839 ⟨383408, by decide⟩ :=
  accepted_of_selected 13 109839 ⟨383408, by decide⟩ ⟨13, 2, 0, 383408, 109839, 609, 16384⟩
    (by decide) selected_cut_14904

theorem unmarked_context_12_27459_383409 : frontier 9 ⟨383409, by decide⟩
    (prefixCache 12 27459) (prefixPartial 12 27459) = false := by
  decide +kernel

theorem node_context_12_27459_383409 : EJMOriginalGlobalDAGData.nodes 9 ⟨383409, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383382, by decide⟩,⟨383403, by decide⟩,⟨383408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27459_383409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27459 ⟨383409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27459
    ⟨383409, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383382, by decide⟩,⟨383403, by decide⟩,⟨383408, by decide⟩]) unmarked_context_12_27459_383409 node_context_12_27459_383409
  intro a
  fin_cases a
  · exact context_13_109836_3444
  · exact context_13_109837_383382
  · exact context_13_109838_383403
  · exact context_13_109839_383408

theorem unmarked_context_11_6864_383410 : frontier 10 ⟨383410, by decide⟩
    (prefixCache 11 6864) (prefixPartial 11 6864) = false := by
  decide +kernel

theorem node_context_11_6864_383410 : EJMOriginalGlobalDAGData.nodes 10 ⟨383410, by decide⟩ =
    .split (coordinate 11) (![⟨383107, by decide⟩,⟨383259, by decide⟩,⟨383339, by decide⟩,⟨383409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6864_383410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6864 ⟨383410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6864
    ⟨383410, by decide⟩ (by decide) (![⟨383107, by decide⟩,⟨383259, by decide⟩,⟨383339, by decide⟩,⟨383409, by decide⟩]) unmarked_context_11_6864_383410 node_context_11_6864_383410
  intro a
  fin_cases a
  · exact context_12_27456_383107
  · exact context_12_27457_383259
  · exact context_12_27458_383339
  · exact context_12_27459_383409

theorem selected_cut_14905 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109840) = some ⟨13, 1, 0, 3444, 109840, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109840_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109840 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109840 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109840, 1, 16384⟩
    (by decide) selected_cut_14905

theorem selected_cut_14906 : selected 8 ⟨383477, by decide⟩
    (prefixPartial 13 109841) = some ⟨13, 2, 0, 383477, 109841, 3361, 16384⟩ := by
  decide +kernel

theorem context_13_109841_383477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109841 ⟨383477, by decide⟩ :=
  accepted_of_selected 13 109841 ⟨383477, by decide⟩ ⟨13, 2, 0, 383477, 109841, 3361, 16384⟩
    (by decide) selected_cut_14906

theorem selected_cut_14907 : selected 8 ⟨383500, by decide⟩
    (prefixPartial 13 109842) = some ⟨13, 2, 0, 383500, 109842, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_109842_383500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109842 ⟨383500, by decide⟩ :=
  accepted_of_selected 13 109842 ⟨383500, by decide⟩ ⟨13, 2, 0, 383500, 109842, 1717, 16384⟩
    (by decide) selected_cut_14907

theorem selected_cut_14908 : selected 8 ⟨383508, by decide⟩
    (prefixPartial 13 109843) = some ⟨13, 2, 0, 383508, 109843, 953, 16384⟩ := by
  decide +kernel

theorem context_13_109843_383508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109843 ⟨383508, by decide⟩ :=
  accepted_of_selected 13 109843 ⟨383508, by decide⟩ ⟨13, 2, 0, 383508, 109843, 953, 16384⟩
    (by decide) selected_cut_14908

theorem unmarked_context_12_27460_383509 : frontier 9 ⟨383509, by decide⟩
    (prefixCache 12 27460) (prefixPartial 12 27460) = false := by
  decide +kernel

theorem node_context_12_27460_383509 : EJMOriginalGlobalDAGData.nodes 9 ⟨383509, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383477, by decide⟩,⟨383500, by decide⟩,⟨383508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27460_383509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27460 ⟨383509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27460
    ⟨383509, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383477, by decide⟩,⟨383500, by decide⟩,⟨383508, by decide⟩]) unmarked_context_12_27460_383509 node_context_12_27460_383509
  intro a
  fin_cases a
  · exact context_13_109840_3444
  · exact context_13_109841_383477
  · exact context_13_109842_383500
  · exact context_13_109843_383508

theorem selected_cut_14909 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109844) = some ⟨13, 1, 0, 3444, 109844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109844, 1, 16384⟩
    (by decide) selected_cut_14909

theorem selected_cut_14910 : selected 8 ⟨383635, by decide⟩
    (prefixPartial 13 109845) = some ⟨13, 2, 0, 383635, 109845, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_109845_383635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109845 ⟨383635, by decide⟩ :=
  accepted_of_selected 13 109845 ⟨383635, by decide⟩ ⟨13, 2, 0, 383635, 109845, 2621, 16384⟩
    (by decide) selected_cut_14910

theorem selected_cut_14911 : selected 8 ⟨383676, by decide⟩
    (prefixPartial 13 109846) = some ⟨13, 2, 0, 383676, 109846, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_109846_383676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109846 ⟨383676, by decide⟩ :=
  accepted_of_selected 13 109846 ⟨383676, by decide⟩ ⟨13, 2, 0, 383676, 109846, 1649, 16384⟩
    (by decide) selected_cut_14911

theorem selected_cut_14912 : selected 8 ⟨383705, by decide⟩
    (prefixPartial 13 109847) = some ⟨13, 2, 0, 383705, 109847, 789, 16384⟩ := by
  decide +kernel

theorem context_13_109847_383705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109847 ⟨383705, by decide⟩ :=
  accepted_of_selected 13 109847 ⟨383705, by decide⟩ ⟨13, 2, 0, 383705, 109847, 789, 16384⟩
    (by decide) selected_cut_14912

theorem unmarked_context_12_27461_383706 : frontier 9 ⟨383706, by decide⟩
    (prefixCache 12 27461) (prefixPartial 12 27461) = false := by
  decide +kernel

theorem node_context_12_27461_383706 : EJMOriginalGlobalDAGData.nodes 9 ⟨383706, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383635, by decide⟩,⟨383676, by decide⟩,⟨383705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27461_383706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27461 ⟨383706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27461
    ⟨383706, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383635, by decide⟩,⟨383676, by decide⟩,⟨383705, by decide⟩]) unmarked_context_12_27461_383706 node_context_12_27461_383706
  intro a
  fin_cases a
  · exact context_13_109844_3444
  · exact context_13_109845_383635
  · exact context_13_109846_383676
  · exact context_13_109847_383705

theorem selected_cut_14913 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109848) = some ⟨13, 1, 0, 3444, 109848, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109848_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109848 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109848 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109848, 1, 16384⟩
    (by decide) selected_cut_14913

theorem selected_cut_14914 : selected 8 ⟨383765, by decide⟩
    (prefixPartial 13 109849) = some ⟨13, 2, 0, 383765, 109849, 3221, 16384⟩ := by
  decide +kernel

theorem context_13_109849_383765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109849 ⟨383765, by decide⟩ :=
  accepted_of_selected 13 109849 ⟨383765, by decide⟩ ⟨13, 2, 0, 383765, 109849, 3221, 16384⟩
    (by decide) selected_cut_14914

theorem selected_cut_14915 : selected 8 ⟨383791, by decide⟩
    (prefixPartial 13 109850) = some ⟨13, 2, 0, 383791, 109850, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_109850_383791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109850 ⟨383791, by decide⟩ :=
  accepted_of_selected 13 109850 ⟨383791, by decide⟩ ⟨13, 2, 0, 383791, 109850, 1841, 16384⟩
    (by decide) selected_cut_14915

theorem selected_cut_14916 : selected 8 ⟨383800, by decide⟩
    (prefixPartial 13 109851) = some ⟨13, 2, 0, 383800, 109851, 929, 16384⟩ := by
  decide +kernel

theorem context_13_109851_383800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109851 ⟨383800, by decide⟩ :=
  accepted_of_selected 13 109851 ⟨383800, by decide⟩ ⟨13, 2, 0, 383800, 109851, 929, 16384⟩
    (by decide) selected_cut_14916

theorem unmarked_context_12_27462_383801 : frontier 9 ⟨383801, by decide⟩
    (prefixCache 12 27462) (prefixPartial 12 27462) = false := by
  decide +kernel

theorem node_context_12_27462_383801 : EJMOriginalGlobalDAGData.nodes 9 ⟨383801, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383765, by decide⟩,⟨383791, by decide⟩,⟨383800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27462_383801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27462 ⟨383801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27462
    ⟨383801, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383765, by decide⟩,⟨383791, by decide⟩,⟨383800, by decide⟩]) unmarked_context_12_27462_383801 node_context_12_27462_383801
  intro a
  fin_cases a
  · exact context_13_109848_3444
  · exact context_13_109849_383765
  · exact context_13_109850_383791
  · exact context_13_109851_383800

theorem selected_cut_14917 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109852) = some ⟨13, 1, 0, 3444, 109852, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109852_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109852 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109852 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109852, 1, 16384⟩
    (by decide) selected_cut_14917

theorem selected_cut_14918 : selected 8 ⟨383851, by decide⟩
    (prefixPartial 13 109853) = some ⟨13, 2, 0, 383851, 109853, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_109853_383851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109853 ⟨383851, by decide⟩ :=
  accepted_of_selected 13 109853 ⟨383851, by decide⟩ ⟨13, 2, 0, 383851, 109853, 2913, 16384⟩
    (by decide) selected_cut_14918

theorem selected_cut_14919 : selected 8 ⟨383870, by decide⟩
    (prefixPartial 13 109854) = some ⟨13, 2, 0, 383870, 109854, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_109854_383870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109854 ⟨383870, by decide⟩ :=
  accepted_of_selected 13 109854 ⟨383870, by decide⟩ ⟨13, 2, 0, 383870, 109854, 1897, 16384⟩
    (by decide) selected_cut_14919

theorem selected_cut_14920 : selected 8 ⟨383878, by decide⟩
    (prefixPartial 13 109855) = some ⟨13, 2, 0, 383878, 109855, 801, 16384⟩ := by
  decide +kernel

theorem context_13_109855_383878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109855 ⟨383878, by decide⟩ :=
  accepted_of_selected 13 109855 ⟨383878, by decide⟩ ⟨13, 2, 0, 383878, 109855, 801, 16384⟩
    (by decide) selected_cut_14920

theorem unmarked_context_12_27463_383879 : frontier 9 ⟨383879, by decide⟩
    (prefixCache 12 27463) (prefixPartial 12 27463) = false := by
  decide +kernel

theorem node_context_12_27463_383879 : EJMOriginalGlobalDAGData.nodes 9 ⟨383879, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383851, by decide⟩,⟨383870, by decide⟩,⟨383878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27463_383879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27463 ⟨383879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27463
    ⟨383879, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383851, by decide⟩,⟨383870, by decide⟩,⟨383878, by decide⟩]) unmarked_context_12_27463_383879 node_context_12_27463_383879
  intro a
  fin_cases a
  · exact context_13_109852_3444
  · exact context_13_109853_383851
  · exact context_13_109854_383870
  · exact context_13_109855_383878

theorem unmarked_context_11_6865_383880 : frontier 10 ⟨383880, by decide⟩
    (prefixCache 11 6865) (prefixPartial 11 6865) = false := by
  decide +kernel

theorem node_context_11_6865_383880 : EJMOriginalGlobalDAGData.nodes 10 ⟨383880, by decide⟩ =
    .split (coordinate 11) (![⟨383509, by decide⟩,⟨383706, by decide⟩,⟨383801, by decide⟩,⟨383879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6865_383880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6865 ⟨383880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6865
    ⟨383880, by decide⟩ (by decide) (![⟨383509, by decide⟩,⟨383706, by decide⟩,⟨383801, by decide⟩,⟨383879, by decide⟩]) unmarked_context_11_6865_383880 node_context_11_6865_383880
  intro a
  fin_cases a
  · exact context_12_27460_383509
  · exact context_12_27461_383706
  · exact context_12_27462_383801
  · exact context_12_27463_383879

theorem selected_cut_14921 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109856) = some ⟨13, 1, 0, 3444, 109856, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109856_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109856 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109856 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109856, 1, 16384⟩
    (by decide) selected_cut_14921

theorem selected_cut_14922 : selected 8 ⟨383919, by decide⟩
    (prefixPartial 13 109857) = some ⟨13, 2, 0, 383919, 109857, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_109857_383919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109857 ⟨383919, by decide⟩ :=
  accepted_of_selected 13 109857 ⟨383919, by decide⟩ ⟨13, 2, 0, 383919, 109857, 2881, 16384⟩
    (by decide) selected_cut_14922

theorem selected_cut_14923 : selected 8 ⟨383939, by decide⟩
    (prefixPartial 13 109858) = some ⟨13, 2, 0, 383939, 109858, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_109858_383939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109858 ⟨383939, by decide⟩ :=
  accepted_of_selected 13 109858 ⟨383939, by decide⟩ ⟨13, 2, 0, 383939, 109858, 1733, 16384⟩
    (by decide) selected_cut_14923

theorem selected_cut_14924 : selected 8 ⟨383952, by decide⟩
    (prefixPartial 13 109859) = some ⟨13, 2, 0, 383952, 109859, 973, 16384⟩ := by
  decide +kernel

theorem context_13_109859_383952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109859 ⟨383952, by decide⟩ :=
  accepted_of_selected 13 109859 ⟨383952, by decide⟩ ⟨13, 2, 0, 383952, 109859, 973, 16384⟩
    (by decide) selected_cut_14924

theorem unmarked_context_12_27464_383953 : frontier 9 ⟨383953, by decide⟩
    (prefixCache 12 27464) (prefixPartial 12 27464) = false := by
  decide +kernel

theorem node_context_12_27464_383953 : EJMOriginalGlobalDAGData.nodes 9 ⟨383953, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨383919, by decide⟩,⟨383939, by decide⟩,⟨383952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27464_383953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27464 ⟨383953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27464
    ⟨383953, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨383919, by decide⟩,⟨383939, by decide⟩,⟨383952, by decide⟩]) unmarked_context_12_27464_383953 node_context_12_27464_383953
  intro a
  fin_cases a
  · exact context_13_109856_3444
  · exact context_13_109857_383919
  · exact context_13_109858_383939
  · exact context_13_109859_383952

theorem selected_cut_14925 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109860) = some ⟨13, 1, 0, 3444, 109860, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109860_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109860 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109860 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109860, 1, 16384⟩
    (by decide) selected_cut_14925

theorem selected_cut_14926 : selected 8 ⟨384037, by decide⟩
    (prefixPartial 13 109861) = some ⟨13, 2, 0, 384037, 109861, 3653, 16384⟩ := by
  decide +kernel

theorem context_13_109861_384037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109861 ⟨384037, by decide⟩ :=
  accepted_of_selected 13 109861 ⟨384037, by decide⟩ ⟨13, 2, 0, 384037, 109861, 3653, 16384⟩
    (by decide) selected_cut_14926

theorem selected_cut_14927 : selected 8 ⟨384065, by decide⟩
    (prefixPartial 13 109862) = some ⟨13, 2, 0, 384065, 109862, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_109862_384065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109862 ⟨384065, by decide⟩ :=
  accepted_of_selected 13 109862 ⟨384065, by decide⟩ ⟨13, 2, 0, 384065, 109862, 2161, 16384⟩
    (by decide) selected_cut_14927

theorem selected_cut_14928 : selected 8 ⟨384088, by decide⟩
    (prefixPartial 13 109863) = some ⟨13, 2, 0, 384088, 109863, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_109863_384088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109863 ⟨384088, by decide⟩ :=
  accepted_of_selected 13 109863 ⟨384088, by decide⟩ ⟨13, 2, 0, 384088, 109863, 1221, 16384⟩
    (by decide) selected_cut_14928

theorem unmarked_context_12_27465_384089 : frontier 9 ⟨384089, by decide⟩
    (prefixCache 12 27465) (prefixPartial 12 27465) = false := by
  decide +kernel

theorem node_context_12_27465_384089 : EJMOriginalGlobalDAGData.nodes 9 ⟨384089, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384037, by decide⟩,⟨384065, by decide⟩,⟨384088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27465_384089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27465 ⟨384089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27465
    ⟨384089, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384037, by decide⟩,⟨384065, by decide⟩,⟨384088, by decide⟩]) unmarked_context_12_27465_384089 node_context_12_27465_384089
  intro a
  fin_cases a
  · exact context_13_109860_3444
  · exact context_13_109861_384037
  · exact context_13_109862_384065
  · exact context_13_109863_384088

theorem selected_cut_14929 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109864) = some ⟨13, 1, 0, 3444, 109864, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109864_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109864 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109864 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109864, 1, 16384⟩
    (by decide) selected_cut_14929

theorem selected_cut_14930 : selected 8 ⟨384121, by decide⟩
    (prefixPartial 13 109865) = some ⟨13, 2, 0, 384121, 109865, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_109865_384121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109865 ⟨384121, by decide⟩ :=
  accepted_of_selected 13 109865 ⟨384121, by decide⟩ ⟨13, 2, 0, 384121, 109865, 2617, 16384⟩
    (by decide) selected_cut_14930

theorem selected_cut_14931 : selected 8 ⟨384143, by decide⟩
    (prefixPartial 13 109866) = some ⟨13, 2, 0, 384143, 109866, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_109866_384143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109866 ⟨384143, by decide⟩ :=
  accepted_of_selected 13 109866 ⟨384143, by decide⟩ ⟨13, 2, 0, 384143, 109866, 1781, 16384⟩
    (by decide) selected_cut_14931

theorem selected_cut_14932 : selected 8 ⟨384154, by decide⟩
    (prefixPartial 13 109867) = some ⟨13, 2, 0, 384154, 109867, 885, 16384⟩ := by
  decide +kernel

theorem context_13_109867_384154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109867 ⟨384154, by decide⟩ :=
  accepted_of_selected 13 109867 ⟨384154, by decide⟩ ⟨13, 2, 0, 384154, 109867, 885, 16384⟩
    (by decide) selected_cut_14932

theorem unmarked_context_12_27466_384155 : frontier 9 ⟨384155, by decide⟩
    (prefixCache 12 27466) (prefixPartial 12 27466) = false := by
  decide +kernel

theorem node_context_12_27466_384155 : EJMOriginalGlobalDAGData.nodes 9 ⟨384155, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384121, by decide⟩,⟨384143, by decide⟩,⟨384154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27466_384155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27466 ⟨384155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27466
    ⟨384155, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384121, by decide⟩,⟨384143, by decide⟩,⟨384154, by decide⟩]) unmarked_context_12_27466_384155 node_context_12_27466_384155
  intro a
  fin_cases a
  · exact context_13_109864_3444
  · exact context_13_109865_384121
  · exact context_13_109866_384143
  · exact context_13_109867_384154

theorem selected_cut_14933 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109868) = some ⟨13, 1, 0, 3444, 109868, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109868_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109868 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109868 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109868, 1, 16384⟩
    (by decide) selected_cut_14933

theorem selected_cut_14934 : selected 8 ⟨384195, by decide⟩
    (prefixPartial 13 109869) = some ⟨13, 2, 0, 384195, 109869, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_109869_384195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109869 ⟨384195, by decide⟩ :=
  accepted_of_selected 13 109869 ⟨384195, by decide⟩ ⟨13, 2, 0, 384195, 109869, 2553, 16384⟩
    (by decide) selected_cut_14934

theorem selected_cut_14935 : selected 8 ⟨384215, by decide⟩
    (prefixPartial 13 109870) = some ⟨13, 2, 0, 384215, 109870, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_109870_384215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109870 ⟨384215, by decide⟩ :=
  accepted_of_selected 13 109870 ⟨384215, by decide⟩ ⟨13, 2, 0, 384215, 109870, 1701, 16384⟩
    (by decide) selected_cut_14935

theorem selected_cut_14936 : selected 8 ⟨384221, by decide⟩
    (prefixPartial 13 109871) = some ⟨13, 2, 0, 384221, 109871, 777, 16384⟩ := by
  decide +kernel

theorem context_13_109871_384221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109871 ⟨384221, by decide⟩ :=
  accepted_of_selected 13 109871 ⟨384221, by decide⟩ ⟨13, 2, 0, 384221, 109871, 777, 16384⟩
    (by decide) selected_cut_14936

theorem unmarked_context_12_27467_384222 : frontier 9 ⟨384222, by decide⟩
    (prefixCache 12 27467) (prefixPartial 12 27467) = false := by
  decide +kernel

theorem node_context_12_27467_384222 : EJMOriginalGlobalDAGData.nodes 9 ⟨384222, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384195, by decide⟩,⟨384215, by decide⟩,⟨384221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27467_384222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27467 ⟨384222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27467
    ⟨384222, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384195, by decide⟩,⟨384215, by decide⟩,⟨384221, by decide⟩]) unmarked_context_12_27467_384222 node_context_12_27467_384222
  intro a
  fin_cases a
  · exact context_13_109868_3444
  · exact context_13_109869_384195
  · exact context_13_109870_384215
  · exact context_13_109871_384221

theorem unmarked_context_11_6866_384223 : frontier 10 ⟨384223, by decide⟩
    (prefixCache 11 6866) (prefixPartial 11 6866) = false := by
  decide +kernel

theorem node_context_11_6866_384223 : EJMOriginalGlobalDAGData.nodes 10 ⟨384223, by decide⟩ =
    .split (coordinate 11) (![⟨383953, by decide⟩,⟨384089, by decide⟩,⟨384155, by decide⟩,⟨384222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6866_384223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6866 ⟨384223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6866
    ⟨384223, by decide⟩ (by decide) (![⟨383953, by decide⟩,⟨384089, by decide⟩,⟨384155, by decide⟩,⟨384222, by decide⟩]) unmarked_context_11_6866_384223 node_context_11_6866_384223
  intro a
  fin_cases a
  · exact context_12_27464_383953
  · exact context_12_27465_384089
  · exact context_12_27466_384155
  · exact context_12_27467_384222

theorem selected_cut_14937 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109872) = some ⟨13, 1, 0, 3444, 109872, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109872_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109872 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109872 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109872, 1, 16384⟩
    (by decide) selected_cut_14937

theorem selected_cut_14938 : selected 8 ⟨384261, by decide⟩
    (prefixPartial 13 109873) = some ⟨13, 2, 0, 384261, 109873, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_109873_384261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109873 ⟨384261, by decide⟩ :=
  accepted_of_selected 13 109873 ⟨384261, by decide⟩ ⟨13, 2, 0, 384261, 109873, 2041, 16384⟩
    (by decide) selected_cut_14938

theorem selected_cut_14939 : selected 8 ⟨384275, by decide⟩
    (prefixPartial 13 109874) = some ⟨13, 2, 0, 384275, 109874, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_109874_384275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109874 ⟨384275, by decide⟩ :=
  accepted_of_selected 13 109874 ⟨384275, by decide⟩ ⟨13, 2, 0, 384275, 109874, 1401, 16384⟩
    (by decide) selected_cut_14939

theorem selected_cut_14940 : selected 8 ⟨384282, by decide⟩
    (prefixPartial 13 109875) = some ⟨13, 2, 0, 384282, 109875, 845, 16384⟩ := by
  decide +kernel

theorem context_13_109875_384282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109875 ⟨384282, by decide⟩ :=
  accepted_of_selected 13 109875 ⟨384282, by decide⟩ ⟨13, 2, 0, 384282, 109875, 845, 16384⟩
    (by decide) selected_cut_14940

theorem unmarked_context_12_27468_384283 : frontier 9 ⟨384283, by decide⟩
    (prefixCache 12 27468) (prefixPartial 12 27468) = false := by
  decide +kernel

theorem node_context_12_27468_384283 : EJMOriginalGlobalDAGData.nodes 9 ⟨384283, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384261, by decide⟩,⟨384275, by decide⟩,⟨384282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27468_384283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27468 ⟨384283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27468
    ⟨384283, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384261, by decide⟩,⟨384275, by decide⟩,⟨384282, by decide⟩]) unmarked_context_12_27468_384283 node_context_12_27468_384283
  intro a
  fin_cases a
  · exact context_13_109872_3444
  · exact context_13_109873_384261
  · exact context_13_109874_384275
  · exact context_13_109875_384282

theorem selected_cut_14941 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109876) = some ⟨13, 1, 0, 3444, 109876, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109876_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109876 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109876 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109876, 1, 16384⟩
    (by decide) selected_cut_14941

theorem selected_cut_14942 : selected 8 ⟨384339, by decide⟩
    (prefixPartial 13 109877) = some ⟨13, 2, 0, 384339, 109877, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_109877_384339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109877 ⟨384339, by decide⟩ :=
  accepted_of_selected 13 109877 ⟨384339, by decide⟩ ⟨13, 2, 0, 384339, 109877, 2773, 16384⟩
    (by decide) selected_cut_14942

theorem selected_cut_14943 : selected 8 ⟨384367, by decide⟩
    (prefixPartial 13 109878) = some ⟨13, 2, 0, 384367, 109878, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_109878_384367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109878 ⟨384367, by decide⟩ :=
  accepted_of_selected 13 109878 ⟨384367, by decide⟩ ⟨13, 2, 0, 384367, 109878, 2005, 16384⟩
    (by decide) selected_cut_14943

theorem selected_cut_14944 : selected 8 ⟨384380, by decide⟩
    (prefixPartial 13 109879) = some ⟨13, 2, 0, 384380, 109879, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_109879_384380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109879 ⟨384380, by decide⟩ :=
  accepted_of_selected 13 109879 ⟨384380, by decide⟩ ⟨13, 2, 0, 384380, 109879, 1005, 16384⟩
    (by decide) selected_cut_14944

theorem unmarked_context_12_27469_384381 : frontier 9 ⟨384381, by decide⟩
    (prefixCache 12 27469) (prefixPartial 12 27469) = false := by
  decide +kernel

theorem node_context_12_27469_384381 : EJMOriginalGlobalDAGData.nodes 9 ⟨384381, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384339, by decide⟩,⟨384367, by decide⟩,⟨384380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27469_384381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27469 ⟨384381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27469
    ⟨384381, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384339, by decide⟩,⟨384367, by decide⟩,⟨384380, by decide⟩]) unmarked_context_12_27469_384381 node_context_12_27469_384381
  intro a
  fin_cases a
  · exact context_13_109876_3444
  · exact context_13_109877_384339
  · exact context_13_109878_384367
  · exact context_13_109879_384380

theorem selected_cut_14945 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109880) = some ⟨13, 1, 0, 3444, 109880, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109880_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109880 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109880 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109880, 1, 16384⟩
    (by decide) selected_cut_14945

theorem selected_cut_14946 : selected 8 ⟨384414, by decide⟩
    (prefixPartial 13 109881) = some ⟨13, 2, 0, 384414, 109881, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_109881_384414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109881 ⟨384414, by decide⟩ :=
  accepted_of_selected 13 109881 ⟨384414, by decide⟩ ⟨13, 2, 0, 384414, 109881, 2253, 16384⟩
    (by decide) selected_cut_14946

theorem selected_cut_14947 : selected 8 ⟨384435, by decide⟩
    (prefixPartial 13 109882) = some ⟨13, 2, 0, 384435, 109882, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_109882_384435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109882 ⟨384435, by decide⟩ :=
  accepted_of_selected 13 109882 ⟨384435, by decide⟩ ⟨13, 2, 0, 384435, 109882, 1537, 16384⟩
    (by decide) selected_cut_14947

theorem selected_cut_14948 : selected 8 ⟨384444, by decide⟩
    (prefixPartial 13 109883) = some ⟨13, 2, 0, 384444, 109883, 785, 16384⟩ := by
  decide +kernel

theorem context_13_109883_384444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109883 ⟨384444, by decide⟩ :=
  accepted_of_selected 13 109883 ⟨384444, by decide⟩ ⟨13, 2, 0, 384444, 109883, 785, 16384⟩
    (by decide) selected_cut_14948

theorem unmarked_context_12_27470_384445 : frontier 9 ⟨384445, by decide⟩
    (prefixCache 12 27470) (prefixPartial 12 27470) = false := by
  decide +kernel

theorem node_context_12_27470_384445 : EJMOriginalGlobalDAGData.nodes 9 ⟨384445, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384414, by decide⟩,⟨384435, by decide⟩,⟨384444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27470_384445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27470 ⟨384445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27470
    ⟨384445, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384414, by decide⟩,⟨384435, by decide⟩,⟨384444, by decide⟩]) unmarked_context_12_27470_384445 node_context_12_27470_384445
  intro a
  fin_cases a
  · exact context_13_109880_3444
  · exact context_13_109881_384414
  · exact context_13_109882_384435
  · exact context_13_109883_384444

theorem selected_cut_14949 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109884) = some ⟨13, 1, 0, 3444, 109884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109884, 1, 16384⟩
    (by decide) selected_cut_14949

theorem selected_cut_14950 : selected 8 ⟨384530, by decide⟩
    (prefixPartial 13 109885) = some ⟨13, 2, 0, 384530, 109885, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_109885_384530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109885 ⟨384530, by decide⟩ :=
  accepted_of_selected 13 109885 ⟨384530, by decide⟩ ⟨13, 2, 0, 384530, 109885, 3245, 16384⟩
    (by decide) selected_cut_14950

theorem selected_cut_14951 : selected 8 ⟨384570, by decide⟩
    (prefixPartial 13 109886) = some ⟨13, 2, 0, 384570, 109886, 2545, 16384⟩ := by
  decide +kernel

theorem context_13_109886_384570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109886 ⟨384570, by decide⟩ :=
  accepted_of_selected 13 109886 ⟨384570, by decide⟩ ⟨13, 2, 0, 384570, 109886, 2545, 16384⟩
    (by decide) selected_cut_14951

theorem selected_cut_14952 : selected 8 ⟨384606, by decide⟩
    (prefixPartial 13 109887) = some ⟨13, 2, 0, 384606, 109887, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_109887_384606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109887 ⟨384606, by decide⟩ :=
  accepted_of_selected 13 109887 ⟨384606, by decide⟩ ⟨13, 2, 0, 384606, 109887, 1265, 16384⟩
    (by decide) selected_cut_14952

theorem unmarked_context_12_27471_384607 : frontier 9 ⟨384607, by decide⟩
    (prefixCache 12 27471) (prefixPartial 12 27471) = false := by
  decide +kernel

theorem node_context_12_27471_384607 : EJMOriginalGlobalDAGData.nodes 9 ⟨384607, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384530, by decide⟩,⟨384570, by decide⟩,⟨384606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27471_384607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27471 ⟨384607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27471
    ⟨384607, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384530, by decide⟩,⟨384570, by decide⟩,⟨384606, by decide⟩]) unmarked_context_12_27471_384607 node_context_12_27471_384607
  intro a
  fin_cases a
  · exact context_13_109884_3444
  · exact context_13_109885_384530
  · exact context_13_109886_384570
  · exact context_13_109887_384606

theorem unmarked_context_11_6867_384608 : frontier 10 ⟨384608, by decide⟩
    (prefixCache 11 6867) (prefixPartial 11 6867) = false := by
  decide +kernel

theorem node_context_11_6867_384608 : EJMOriginalGlobalDAGData.nodes 10 ⟨384608, by decide⟩ =
    .split (coordinate 11) (![⟨384283, by decide⟩,⟨384381, by decide⟩,⟨384445, by decide⟩,⟨384607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6867_384608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6867 ⟨384608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6867
    ⟨384608, by decide⟩ (by decide) (![⟨384283, by decide⟩,⟨384381, by decide⟩,⟨384445, by decide⟩,⟨384607, by decide⟩]) unmarked_context_11_6867_384608 node_context_11_6867_384608
  intro a
  fin_cases a
  · exact context_12_27468_384283
  · exact context_12_27469_384381
  · exact context_12_27470_384445
  · exact context_12_27471_384607

theorem unmarked_context_10_1716_384609 : frontier 11 ⟨384609, by decide⟩
    (prefixCache 10 1716) (prefixPartial 10 1716) = false := by
  decide +kernel

theorem node_context_10_1716_384609 : EJMOriginalGlobalDAGData.nodes 11 ⟨384609, by decide⟩ =
    .split (coordinate 10) (![⟨383410, by decide⟩,⟨383880, by decide⟩,⟨384223, by decide⟩,⟨384608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1716_384609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1716 ⟨384609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1716
    ⟨384609, by decide⟩ (by decide) (![⟨383410, by decide⟩,⟨383880, by decide⟩,⟨384223, by decide⟩,⟨384608, by decide⟩]) unmarked_context_10_1716_384609 node_context_10_1716_384609
  intro a
  fin_cases a
  · exact context_11_6864_383410
  · exact context_11_6865_383880
  · exact context_11_6866_384223
  · exact context_11_6867_384608

theorem selected_cut_14953 : selected 9 ⟨384655, by decide⟩
    (prefixPartial 12 27472) = some ⟨12, 2, 0, 384655, 27472, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_27472_384655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27472 ⟨384655, by decide⟩ :=
  accepted_of_selected 12 27472 ⟨384655, by decide⟩ ⟨12, 2, 0, 384655, 27472, 3925, 65536⟩
    (by decide) selected_cut_14953

theorem selected_cut_14954 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27473) = some ⟨12, 1, 0, 170504, 27473, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27473_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27473 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27473 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27473, 1, 65536⟩
    (by decide) selected_cut_14954

theorem selected_cut_14955 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109896) = some ⟨13, 1, 0, 3444, 109896, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109896_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109896 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109896 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109896, 1, 16384⟩
    (by decide) selected_cut_14955

theorem selected_cut_14956 : selected 8 ⟨384697, by decide⟩
    (prefixPartial 13 109897) = some ⟨13, 2, 0, 384697, 109897, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_109897_384697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109897 ⟨384697, by decide⟩ :=
  accepted_of_selected 13 109897 ⟨384697, by decide⟩ ⟨13, 2, 0, 384697, 109897, 2257, 16384⟩
    (by decide) selected_cut_14956

theorem selected_cut_14957 : selected 8 ⟨384718, by decide⟩
    (prefixPartial 13 109898) = some ⟨13, 2, 0, 384718, 109898, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_109898_384718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109898 ⟨384718, by decide⟩ :=
  accepted_of_selected 13 109898 ⟨384718, by decide⟩ ⟨13, 2, 0, 384718, 109898, 1749, 16384⟩
    (by decide) selected_cut_14957

theorem selected_cut_14958 : selected 8 ⟨384725, by decide⟩
    (prefixPartial 13 109899) = some ⟨13, 2, 0, 384725, 109899, 761, 16384⟩ := by
  decide +kernel

theorem context_13_109899_384725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109899 ⟨384725, by decide⟩ :=
  accepted_of_selected 13 109899 ⟨384725, by decide⟩ ⟨13, 2, 0, 384725, 109899, 761, 16384⟩
    (by decide) selected_cut_14958

theorem unmarked_context_12_27474_384726 : frontier 9 ⟨384726, by decide⟩
    (prefixCache 12 27474) (prefixPartial 12 27474) = false := by
  decide +kernel

theorem node_context_12_27474_384726 : EJMOriginalGlobalDAGData.nodes 9 ⟨384726, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384697, by decide⟩,⟨384718, by decide⟩,⟨384725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27474_384726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27474 ⟨384726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27474
    ⟨384726, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384697, by decide⟩,⟨384718, by decide⟩,⟨384725, by decide⟩]) unmarked_context_12_27474_384726 node_context_12_27474_384726
  intro a
  fin_cases a
  · exact context_13_109896_3444
  · exact context_13_109897_384697
  · exact context_13_109898_384718
  · exact context_13_109899_384725

theorem selected_cut_14959 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109900) = some ⟨13, 1, 0, 3444, 109900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109900, 1, 16384⟩
    (by decide) selected_cut_14959

theorem selected_cut_14960 : selected 8 ⟨384755, by decide⟩
    (prefixPartial 13 109901) = some ⟨13, 2, 0, 384755, 109901, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_109901_384755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109901 ⟨384755, by decide⟩ :=
  accepted_of_selected 13 109901 ⟨384755, by decide⟩ ⟨13, 2, 0, 384755, 109901, 2185, 16384⟩
    (by decide) selected_cut_14960

theorem selected_cut_14961 : selected 8 ⟨384775, by decide⟩
    (prefixPartial 13 109902) = some ⟨13, 2, 0, 384775, 109902, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_109902_384775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109902 ⟨384775, by decide⟩ :=
  accepted_of_selected 13 109902 ⟨384775, by decide⟩ ⟨13, 2, 0, 384775, 109902, 1649, 16384⟩
    (by decide) selected_cut_14961

theorem selected_cut_14962 : selected 8 ⟨384783, by decide⟩
    (prefixPartial 13 109903) = some ⟨13, 2, 0, 384783, 109903, 713, 16384⟩ := by
  decide +kernel

theorem context_13_109903_384783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109903 ⟨384783, by decide⟩ :=
  accepted_of_selected 13 109903 ⟨384783, by decide⟩ ⟨13, 2, 0, 384783, 109903, 713, 16384⟩
    (by decide) selected_cut_14962

theorem unmarked_context_12_27475_384784 : frontier 9 ⟨384784, by decide⟩
    (prefixCache 12 27475) (prefixPartial 12 27475) = false := by
  decide +kernel

theorem node_context_12_27475_384784 : EJMOriginalGlobalDAGData.nodes 9 ⟨384784, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384755, by decide⟩,⟨384775, by decide⟩,⟨384783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27475_384784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27475 ⟨384784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27475
    ⟨384784, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384755, by decide⟩,⟨384775, by decide⟩,⟨384783, by decide⟩]) unmarked_context_12_27475_384784 node_context_12_27475_384784
  intro a
  fin_cases a
  · exact context_13_109900_3444
  · exact context_13_109901_384755
  · exact context_13_109902_384775
  · exact context_13_109903_384783

theorem unmarked_context_11_6868_384785 : frontier 10 ⟨384785, by decide⟩
    (prefixCache 11 6868) (prefixPartial 11 6868) = false := by
  decide +kernel

theorem node_context_11_6868_384785 : EJMOriginalGlobalDAGData.nodes 10 ⟨384785, by decide⟩ =
    .split (coordinate 11) (![⟨384655, by decide⟩,⟨170504, by decide⟩,⟨384726, by decide⟩,⟨384784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6868_384785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6868 ⟨384785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6868
    ⟨384785, by decide⟩ (by decide) (![⟨384655, by decide⟩,⟨170504, by decide⟩,⟨384726, by decide⟩,⟨384784, by decide⟩]) unmarked_context_11_6868_384785 node_context_11_6868_384785
  intro a
  fin_cases a
  · exact context_12_27472_384655
  · exact context_12_27473_170504
  · exact context_12_27474_384726
  · exact context_12_27475_384784

theorem selected_cut_14963 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109904) = some ⟨13, 1, 0, 3444, 109904, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109904_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109904 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109904 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109904, 1, 16384⟩
    (by decide) selected_cut_14963

theorem selected_cut_14964 : selected 8 ⟨384810, by decide⟩
    (prefixPartial 13 109905) = some ⟨13, 2, 0, 384810, 109905, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_109905_384810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109905 ⟨384810, by decide⟩ :=
  accepted_of_selected 13 109905 ⟨384810, by decide⟩ ⟨13, 2, 0, 384810, 109905, 1941, 16384⟩
    (by decide) selected_cut_14964

theorem selected_cut_14965 : selected 8 ⟨384826, by decide⟩
    (prefixPartial 13 109906) = some ⟨13, 2, 0, 384826, 109906, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_109906_384826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109906 ⟨384826, by decide⟩ :=
  accepted_of_selected 13 109906 ⟨384826, by decide⟩ ⟨13, 2, 0, 384826, 109906, 1453, 16384⟩
    (by decide) selected_cut_14965

theorem selected_cut_14966 : selected 8 ⟨384833, by decide⟩
    (prefixPartial 13 109907) = some ⟨13, 2, 0, 384833, 109907, 909, 16384⟩ := by
  decide +kernel

theorem context_13_109907_384833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109907 ⟨384833, by decide⟩ :=
  accepted_of_selected 13 109907 ⟨384833, by decide⟩ ⟨13, 2, 0, 384833, 109907, 909, 16384⟩
    (by decide) selected_cut_14966

theorem unmarked_context_12_27476_384834 : frontier 9 ⟨384834, by decide⟩
    (prefixCache 12 27476) (prefixPartial 12 27476) = false := by
  decide +kernel

theorem node_context_12_27476_384834 : EJMOriginalGlobalDAGData.nodes 9 ⟨384834, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384810, by decide⟩,⟨384826, by decide⟩,⟨384833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27476_384834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27476 ⟨384834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27476
    ⟨384834, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384810, by decide⟩,⟨384826, by decide⟩,⟨384833, by decide⟩]) unmarked_context_12_27476_384834 node_context_12_27476_384834
  intro a
  fin_cases a
  · exact context_13_109904_3444
  · exact context_13_109905_384810
  · exact context_13_109906_384826
  · exact context_13_109907_384833

theorem selected_cut_14967 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27477) = some ⟨12, 1, 0, 170504, 27477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27477_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27477 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27477 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27477, 1, 65536⟩
    (by decide) selected_cut_14967

theorem selected_cut_14968 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109912) = some ⟨13, 1, 0, 3444, 109912, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109912_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109912 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109912 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109912, 1, 16384⟩
    (by decide) selected_cut_14968

theorem selected_cut_14969 : selected 8 ⟨384866, by decide⟩
    (prefixPartial 13 109913) = some ⟨13, 2, 0, 384866, 109913, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_109913_384866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109913 ⟨384866, by decide⟩ :=
  accepted_of_selected 13 109913 ⟨384866, by decide⟩ ⟨13, 2, 0, 384866, 109913, 2133, 16384⟩
    (by decide) selected_cut_14969

theorem selected_cut_14970 : selected 8 ⟨384890, by decide⟩
    (prefixPartial 13 109914) = some ⟨13, 2, 0, 384890, 109914, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_109914_384890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109914 ⟨384890, by decide⟩ :=
  accepted_of_selected 13 109914 ⟨384890, by decide⟩ ⟨13, 2, 0, 384890, 109914, 1833, 16384⟩
    (by decide) selected_cut_14970

theorem selected_cut_14971 : selected 8 ⟨384902, by decide⟩
    (prefixPartial 13 109915) = some ⟨13, 2, 0, 384902, 109915, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_109915_384902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109915 ⟨384902, by decide⟩ :=
  accepted_of_selected 13 109915 ⟨384902, by decide⟩ ⟨13, 2, 0, 384902, 109915, 1017, 16384⟩
    (by decide) selected_cut_14971

theorem unmarked_context_12_27478_384903 : frontier 9 ⟨384903, by decide⟩
    (prefixCache 12 27478) (prefixPartial 12 27478) = false := by
  decide +kernel

theorem node_context_12_27478_384903 : EJMOriginalGlobalDAGData.nodes 9 ⟨384903, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384866, by decide⟩,⟨384890, by decide⟩,⟨384902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27478_384903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27478 ⟨384903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27478
    ⟨384903, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384866, by decide⟩,⟨384890, by decide⟩,⟨384902, by decide⟩]) unmarked_context_12_27478_384903 node_context_12_27478_384903
  intro a
  fin_cases a
  · exact context_13_109912_3444
  · exact context_13_109913_384866
  · exact context_13_109914_384890
  · exact context_13_109915_384902

theorem selected_cut_14972 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109916) = some ⟨13, 1, 0, 3444, 109916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109916, 1, 16384⟩
    (by decide) selected_cut_14972

theorem selected_cut_14973 : selected 8 ⟨384919, by decide⟩
    (prefixPartial 13 109917) = some ⟨13, 2, 0, 384919, 109917, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_109917_384919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109917 ⟨384919, by decide⟩ :=
  accepted_of_selected 13 109917 ⟨384919, by decide⟩ ⟨13, 2, 0, 384919, 109917, 1841, 16384⟩
    (by decide) selected_cut_14973

theorem selected_cut_14974 : selected 8 ⟨384938, by decide⟩
    (prefixPartial 13 109918) = some ⟨13, 2, 0, 384938, 109918, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_109918_384938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109918 ⟨384938, by decide⟩ :=
  accepted_of_selected 13 109918 ⟨384938, by decide⟩ ⟨13, 2, 0, 384938, 109918, 1769, 16384⟩
    (by decide) selected_cut_14974

theorem selected_cut_14975 : selected 8 ⟨384948, by decide⟩
    (prefixPartial 13 109919) = some ⟨13, 2, 0, 384948, 109919, 897, 16384⟩ := by
  decide +kernel

theorem context_13_109919_384948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109919 ⟨384948, by decide⟩ :=
  accepted_of_selected 13 109919 ⟨384948, by decide⟩ ⟨13, 2, 0, 384948, 109919, 897, 16384⟩
    (by decide) selected_cut_14975

theorem unmarked_context_12_27479_384949 : frontier 9 ⟨384949, by decide⟩
    (prefixCache 12 27479) (prefixPartial 12 27479) = false := by
  decide +kernel

theorem node_context_12_27479_384949 : EJMOriginalGlobalDAGData.nodes 9 ⟨384949, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨384919, by decide⟩,⟨384938, by decide⟩,⟨384948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27479_384949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27479 ⟨384949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27479
    ⟨384949, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨384919, by decide⟩,⟨384938, by decide⟩,⟨384948, by decide⟩]) unmarked_context_12_27479_384949 node_context_12_27479_384949
  intro a
  fin_cases a
  · exact context_13_109916_3444
  · exact context_13_109917_384919
  · exact context_13_109918_384938
  · exact context_13_109919_384948

theorem unmarked_context_11_6869_384950 : frontier 10 ⟨384950, by decide⟩
    (prefixCache 11 6869) (prefixPartial 11 6869) = false := by
  decide +kernel

theorem node_context_11_6869_384950 : EJMOriginalGlobalDAGData.nodes 10 ⟨384950, by decide⟩ =
    .split (coordinate 11) (![⟨384834, by decide⟩,⟨170504, by decide⟩,⟨384903, by decide⟩,⟨384949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6869_384950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6869 ⟨384950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6869
    ⟨384950, by decide⟩ (by decide) (![⟨384834, by decide⟩,⟨170504, by decide⟩,⟨384903, by decide⟩,⟨384949, by decide⟩]) unmarked_context_11_6869_384950 node_context_11_6869_384950
  intro a
  fin_cases a
  · exact context_12_27476_384834
  · exact context_12_27477_170504
  · exact context_12_27478_384903
  · exact context_12_27479_384949

theorem selected_cut_14976 : selected 9 ⟨384992, by decide⟩
    (prefixPartial 12 27480) = some ⟨12, 2, 0, 384992, 27480, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_27480_384992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27480 ⟨384992, by decide⟩ :=
  accepted_of_selected 12 27480 ⟨384992, by decide⟩ ⟨12, 2, 0, 384992, 27480, 3829, 65536⟩
    (by decide) selected_cut_14976

theorem selected_cut_14977 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 109924) = some ⟨13, 1, 0, 3444, 109924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_109924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 109924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 109924, 1, 16384⟩
    (by decide) selected_cut_14977

theorem selected_cut_14978 : selected 8 ⟨385027, by decide⟩
    (prefixPartial 13 109925) = some ⟨13, 2, 0, 385027, 109925, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_109925_385027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109925 ⟨385027, by decide⟩ :=
  accepted_of_selected 13 109925 ⟨385027, by decide⟩ ⟨13, 2, 0, 385027, 109925, 1981, 16384⟩
    (by decide) selected_cut_14978

theorem selected_cut_14979 : selected 8 ⟨385051, by decide⟩
    (prefixPartial 13 109926) = some ⟨13, 2, 0, 385051, 109926, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_109926_385051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 109926 ⟨385051, by decide⟩ :=
  accepted_of_selected 13 109926 ⟨385051, by decide⟩ ⟨13, 2, 0, 385051, 109926, 2173, 16384⟩
    (by decide) selected_cut_14979

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
