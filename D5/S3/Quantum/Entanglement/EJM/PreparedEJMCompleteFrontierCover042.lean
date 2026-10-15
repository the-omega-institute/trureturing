/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover041
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04034 : selected 8 ⟨128649, by decide⟩
    (prefixPartial 13 71720) = some ⟨13, 2, 0, 128649, 71720, 3913, 16384⟩ := by
  decide +kernel

theorem context_13_71720_128649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71720 ⟨128649, by decide⟩ :=
  accepted_of_selected 13 71720 ⟨128649, by decide⟩ ⟨13, 2, 0, 128649, 71720, 3913, 16384⟩
    (by decide) selected_cut_04034

theorem selected_cut_04035 : selected 8 ⟨128716, by decide⟩
    (prefixPartial 13 71721) = some ⟨13, 2, 0, 128716, 71721, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_71721_128716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71721 ⟨128716, by decide⟩ :=
  accepted_of_selected 13 71721 ⟨128716, by decide⟩ ⟨13, 2, 0, 128716, 71721, 2601, 16384⟩
    (by decide) selected_cut_04035

theorem selected_cut_04036 : selected 8 ⟨128740, by decide⟩
    (prefixPartial 13 71722) = some ⟨13, 2, 0, 128740, 71722, 681, 16384⟩ := by
  decide +kernel

theorem context_13_71722_128740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71722 ⟨128740, by decide⟩ :=
  accepted_of_selected 13 71722 ⟨128740, by decide⟩ ⟨13, 2, 0, 128740, 71722, 681, 16384⟩
    (by decide) selected_cut_04036

theorem selected_cut_04037 : selected 8 ⟨128742, by decide⟩
    (prefixPartial 13 71723) = some ⟨13, 2, 0, 128742, 71723, 125, 16384⟩ := by
  decide +kernel

theorem context_13_71723_128742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71723 ⟨128742, by decide⟩ :=
  accepted_of_selected 13 71723 ⟨128742, by decide⟩ ⟨13, 2, 0, 128742, 71723, 125, 16384⟩
    (by decide) selected_cut_04037

theorem unmarked_context_12_17930_128743 : frontier 9 ⟨128743, by decide⟩
    (prefixCache 12 17930) (prefixPartial 12 17930) = false := by
  decide +kernel

theorem node_context_12_17930_128743 : EJMOriginalGlobalDAGData.nodes 9 ⟨128743, by decide⟩ =
    .split (coordinate 12) (![⟨128649, by decide⟩,⟨128716, by decide⟩,⟨128740, by decide⟩,⟨128742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17930_128743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17930 ⟨128743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17930
    ⟨128743, by decide⟩ (by decide) (![⟨128649, by decide⟩,⟨128716, by decide⟩,⟨128740, by decide⟩,⟨128742, by decide⟩]) unmarked_context_12_17930_128743 node_context_12_17930_128743
  intro a
  fin_cases a
  · exact context_13_71720_128649
  · exact context_13_71721_128716
  · exact context_13_71722_128740
  · exact context_13_71723_128742

theorem selected_cut_04038 : selected 8 ⟨128796, by decide⟩
    (prefixPartial 13 71724) = some ⟨13, 2, 0, 128796, 71724, 3201, 16384⟩ := by
  decide +kernel

theorem context_13_71724_128796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71724 ⟨128796, by decide⟩ :=
  accepted_of_selected 13 71724 ⟨128796, by decide⟩ ⟨13, 2, 0, 128796, 71724, 3201, 16384⟩
    (by decide) selected_cut_04038

theorem selected_cut_04039 : selected 8 ⟨128855, by decide⟩
    (prefixPartial 13 71725) = some ⟨13, 2, 0, 128855, 71725, 3505, 16384⟩ := by
  decide +kernel

theorem context_13_71725_128855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71725 ⟨128855, by decide⟩ :=
  accepted_of_selected 13 71725 ⟨128855, by decide⟩ ⟨13, 2, 0, 128855, 71725, 3505, 16384⟩
    (by decide) selected_cut_04039

theorem selected_cut_04040 : selected 8 ⟨128885, by decide⟩
    (prefixPartial 13 71726) = some ⟨13, 2, 0, 128885, 71726, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_71726_128885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71726 ⟨128885, by decide⟩ :=
  accepted_of_selected 13 71726 ⟨128885, by decide⟩ ⟨13, 2, 0, 128885, 71726, 1861, 16384⟩
    (by decide) selected_cut_04040

theorem selected_cut_04041 : selected 8 ⟨128895, by decide⟩
    (prefixPartial 13 71727) = some ⟨13, 2, 0, 128895, 71727, 937, 16384⟩ := by
  decide +kernel

theorem context_13_71727_128895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71727 ⟨128895, by decide⟩ :=
  accepted_of_selected 13 71727 ⟨128895, by decide⟩ ⟨13, 2, 0, 128895, 71727, 937, 16384⟩
    (by decide) selected_cut_04041

theorem unmarked_context_12_17931_128896 : frontier 9 ⟨128896, by decide⟩
    (prefixCache 12 17931) (prefixPartial 12 17931) = false := by
  decide +kernel

theorem node_context_12_17931_128896 : EJMOriginalGlobalDAGData.nodes 9 ⟨128896, by decide⟩ =
    .split (coordinate 12) (![⟨128796, by decide⟩,⟨128855, by decide⟩,⟨128885, by decide⟩,⟨128895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17931_128896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17931 ⟨128896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17931
    ⟨128896, by decide⟩ (by decide) (![⟨128796, by decide⟩,⟨128855, by decide⟩,⟨128885, by decide⟩,⟨128895, by decide⟩]) unmarked_context_12_17931_128896 node_context_12_17931_128896
  intro a
  fin_cases a
  · exact context_13_71724_128796
  · exact context_13_71725_128855
  · exact context_13_71726_128885
  · exact context_13_71727_128895

theorem unmarked_context_11_4482_128897 : frontier 10 ⟨128897, by decide⟩
    (prefixCache 11 4482) (prefixPartial 11 4482) = false := by
  decide +kernel

theorem node_context_11_4482_128897 : EJMOriginalGlobalDAGData.nodes 10 ⟨128897, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨128743, by decide⟩,⟨128896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4482_128897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4482 ⟨128897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4482
    ⟨128897, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨128743, by decide⟩,⟨128896, by decide⟩]) unmarked_context_11_4482_128897 node_context_11_4482_128897
  intro a
  fin_cases a
  · exact context_12_17928_895
  · exact context_12_17929_895
  · exact context_12_17930_128743
  · exact context_12_17931_128896

theorem selected_cut_04042 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17932) = some ⟨12, 1, 0, 895, 17932, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17932_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17932 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17932 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17932, 1, 65536⟩
    (by decide) selected_cut_04042

theorem selected_cut_04043 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17933) = some ⟨12, 1, 0, 895, 17933, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17933_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17933 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17933 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17933, 1, 65536⟩
    (by decide) selected_cut_04043

theorem selected_cut_04044 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 17934) = some ⟨12, 1, 0, 895, 17934, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17934_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17934 ⟨895, by decide⟩ :=
  accepted_of_selected 12 17934 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 17934, 1, 65536⟩
    (by decide) selected_cut_04044

theorem selected_cut_04045 : selected 8 ⟨128955, by decide⟩
    (prefixPartial 13 71740) = some ⟨13, 2, 0, 128955, 71740, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_71740_128955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71740 ⟨128955, by decide⟩ :=
  accepted_of_selected 13 71740 ⟨128955, by decide⟩ ⟨13, 2, 0, 128955, 71740, 2717, 16384⟩
    (by decide) selected_cut_04045

theorem selected_cut_04046 : selected 8 ⟨129001, by decide⟩
    (prefixPartial 13 71741) = some ⟨13, 2, 0, 129001, 71741, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_71741_129001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71741 ⟨129001, by decide⟩ :=
  accepted_of_selected 13 71741 ⟨129001, by decide⟩ ⟨13, 2, 0, 129001, 71741, 1761, 16384⟩
    (by decide) selected_cut_04046

theorem selected_cut_04047 : selected 8 ⟨129014, by decide⟩
    (prefixPartial 13 71742) = some ⟨13, 2, 0, 129014, 71742, 529, 16384⟩ := by
  decide +kernel

theorem context_13_71742_129014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71742 ⟨129014, by decide⟩ :=
  accepted_of_selected 13 71742 ⟨129014, by decide⟩ ⟨13, 2, 0, 129014, 71742, 529, 16384⟩
    (by decide) selected_cut_04047

theorem selected_cut_04048 : selected 8 ⟨129016, by decide⟩
    (prefixPartial 13 71743) = some ⟨13, 2, 0, 129016, 71743, 117, 16384⟩ := by
  decide +kernel

theorem context_13_71743_129016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71743 ⟨129016, by decide⟩ :=
  accepted_of_selected 13 71743 ⟨129016, by decide⟩ ⟨13, 2, 0, 129016, 71743, 117, 16384⟩
    (by decide) selected_cut_04048

theorem unmarked_context_12_17935_129017 : frontier 9 ⟨129017, by decide⟩
    (prefixCache 12 17935) (prefixPartial 12 17935) = false := by
  decide +kernel

theorem node_context_12_17935_129017 : EJMOriginalGlobalDAGData.nodes 9 ⟨129017, by decide⟩ =
    .split (coordinate 12) (![⟨128955, by decide⟩,⟨129001, by decide⟩,⟨129014, by decide⟩,⟨129016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17935_129017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17935 ⟨129017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17935
    ⟨129017, by decide⟩ (by decide) (![⟨128955, by decide⟩,⟨129001, by decide⟩,⟨129014, by decide⟩,⟨129016, by decide⟩]) unmarked_context_12_17935_129017 node_context_12_17935_129017
  intro a
  fin_cases a
  · exact context_13_71740_128955
  · exact context_13_71741_129001
  · exact context_13_71742_129014
  · exact context_13_71743_129016

theorem unmarked_context_11_4483_129018 : frontier 10 ⟨129018, by decide⟩
    (prefixCache 11 4483) (prefixPartial 11 4483) = false := by
  decide +kernel

theorem node_context_11_4483_129018 : EJMOriginalGlobalDAGData.nodes 10 ⟨129018, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨895, by decide⟩,⟨129017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4483_129018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4483 ⟨129018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4483
    ⟨129018, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨895, by decide⟩,⟨129017, by decide⟩]) unmarked_context_11_4483_129018 node_context_11_4483_129018
  intro a
  fin_cases a
  · exact context_12_17932_895
  · exact context_12_17933_895
  · exact context_12_17934_895
  · exact context_12_17935_129017

theorem unmarked_context_10_1120_129019 : frontier 11 ⟨129019, by decide⟩
    (prefixCache 10 1120) (prefixPartial 10 1120) = false := by
  decide +kernel

theorem node_context_10_1120_129019 : EJMOriginalGlobalDAGData.nodes 11 ⟨129019, by decide⟩ =
    .split (coordinate 10) (![⟨128178, by decide⟩,⟨128570, by decide⟩,⟨128897, by decide⟩,⟨129018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1120_129019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1120 ⟨129019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1120
    ⟨129019, by decide⟩ (by decide) (![⟨128178, by decide⟩,⟨128570, by decide⟩,⟨128897, by decide⟩,⟨129018, by decide⟩]) unmarked_context_10_1120_129019 node_context_10_1120_129019
  intro a
  fin_cases a
  · exact context_11_4480_128178
  · exact context_11_4481_128570
  · exact context_11_4482_128897
  · exact context_11_4483_129018

theorem selected_cut_04049 : selected 8 ⟨129051, by decide⟩
    (prefixPartial 13 71744) = some ⟨13, 2, 0, 129051, 71744, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_71744_129051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71744 ⟨129051, by decide⟩ :=
  accepted_of_selected 13 71744 ⟨129051, by decide⟩ ⟨13, 2, 0, 129051, 71744, 2149, 16384⟩
    (by decide) selected_cut_04049

theorem selected_cut_04050 : selected 8 ⟨129073, by decide⟩
    (prefixPartial 13 71745) = some ⟨13, 2, 0, 129073, 71745, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_71745_129073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71745 ⟨129073, by decide⟩ :=
  accepted_of_selected 13 71745 ⟨129073, by decide⟩ ⟨13, 2, 0, 129073, 71745, 1825, 16384⟩
    (by decide) selected_cut_04050

theorem selected_cut_04051 : selected 8 ⟨129092, by decide⟩
    (prefixPartial 13 71746) = some ⟨13, 2, 0, 129092, 71746, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_71746_129092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71746 ⟨129092, by decide⟩ :=
  accepted_of_selected 13 71746 ⟨129092, by decide⟩ ⟨13, 2, 0, 129092, 71746, 1713, 16384⟩
    (by decide) selected_cut_04051

theorem selected_cut_04052 : selected 8 ⟨129101, by decide⟩
    (prefixPartial 13 71747) = some ⟨13, 2, 0, 129101, 71747, 953, 16384⟩ := by
  decide +kernel

theorem context_13_71747_129101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71747 ⟨129101, by decide⟩ :=
  accepted_of_selected 13 71747 ⟨129101, by decide⟩ ⟨13, 2, 0, 129101, 71747, 953, 16384⟩
    (by decide) selected_cut_04052

theorem unmarked_context_12_17936_129102 : frontier 9 ⟨129102, by decide⟩
    (prefixCache 12 17936) (prefixPartial 12 17936) = false := by
  decide +kernel

theorem node_context_12_17936_129102 : EJMOriginalGlobalDAGData.nodes 9 ⟨129102, by decide⟩ =
    .split (coordinate 12) (![⟨129051, by decide⟩,⟨129073, by decide⟩,⟨129092, by decide⟩,⟨129101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17936_129102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17936 ⟨129102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17936
    ⟨129102, by decide⟩ (by decide) (![⟨129051, by decide⟩,⟨129073, by decide⟩,⟨129092, by decide⟩,⟨129101, by decide⟩]) unmarked_context_12_17936_129102 node_context_12_17936_129102
  intro a
  fin_cases a
  · exact context_13_71744_129051
  · exact context_13_71745_129073
  · exact context_13_71746_129092
  · exact context_13_71747_129101

theorem selected_cut_04053 : selected 8 ⟨129135, by decide⟩
    (prefixPartial 13 71748) = some ⟨13, 2, 0, 129135, 71748, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_71748_129135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71748 ⟨129135, by decide⟩ :=
  accepted_of_selected 13 71748 ⟨129135, by decide⟩ ⟨13, 2, 0, 129135, 71748, 2297, 16384⟩
    (by decide) selected_cut_04053

theorem selected_cut_04054 : selected 8 ⟨129163, by decide⟩
    (prefixPartial 13 71749) = some ⟨13, 2, 0, 129163, 71749, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_71749_129163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71749 ⟨129163, by decide⟩ :=
  accepted_of_selected 13 71749 ⟨129163, by decide⟩ ⟨13, 2, 0, 129163, 71749, 1737, 16384⟩
    (by decide) selected_cut_04054

theorem selected_cut_04055 : selected 8 ⟨129184, by decide⟩
    (prefixPartial 13 71750) = some ⟨13, 2, 0, 129184, 71750, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_71750_129184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71750 ⟨129184, by decide⟩ :=
  accepted_of_selected 13 71750 ⟨129184, by decide⟩ ⟨13, 2, 0, 129184, 71750, 1217, 16384⟩
    (by decide) selected_cut_04055

theorem selected_cut_04056 : selected 8 ⟨129195, by decide⟩
    (prefixPartial 13 71751) = some ⟨13, 2, 0, 129195, 71751, 901, 16384⟩ := by
  decide +kernel

theorem context_13_71751_129195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71751 ⟨129195, by decide⟩ :=
  accepted_of_selected 13 71751 ⟨129195, by decide⟩ ⟨13, 2, 0, 129195, 71751, 901, 16384⟩
    (by decide) selected_cut_04056

theorem unmarked_context_12_17937_129196 : frontier 9 ⟨129196, by decide⟩
    (prefixCache 12 17937) (prefixPartial 12 17937) = false := by
  decide +kernel

theorem node_context_12_17937_129196 : EJMOriginalGlobalDAGData.nodes 9 ⟨129196, by decide⟩ =
    .split (coordinate 12) (![⟨129135, by decide⟩,⟨129163, by decide⟩,⟨129184, by decide⟩,⟨129195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17937_129196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17937 ⟨129196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17937
    ⟨129196, by decide⟩ (by decide) (![⟨129135, by decide⟩,⟨129163, by decide⟩,⟨129184, by decide⟩,⟨129195, by decide⟩]) unmarked_context_12_17937_129196 node_context_12_17937_129196
  intro a
  fin_cases a
  · exact context_13_71748_129135
  · exact context_13_71749_129163
  · exact context_13_71750_129184
  · exact context_13_71751_129195

theorem selected_cut_04057 : selected 8 ⟨129224, by decide⟩
    (prefixPartial 13 71752) = some ⟨13, 2, 0, 129224, 71752, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_71752_129224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71752 ⟨129224, by decide⟩ :=
  accepted_of_selected 13 71752 ⟨129224, by decide⟩ ⟨13, 2, 0, 129224, 71752, 1829, 16384⟩
    (by decide) selected_cut_04057

theorem selected_cut_04058 : selected 8 ⟨129253, by decide⟩
    (prefixPartial 13 71753) = some ⟨13, 2, 0, 129253, 71753, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_71753_129253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71753 ⟨129253, by decide⟩ :=
  accepted_of_selected 13 71753 ⟨129253, by decide⟩ ⟨13, 2, 0, 129253, 71753, 1845, 16384⟩
    (by decide) selected_cut_04058

theorem selected_cut_04059 : selected 8 ⟨129270, by decide⟩
    (prefixPartial 13 71754) = some ⟨13, 2, 0, 129270, 71754, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_71754_129270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71754 ⟨129270, by decide⟩ :=
  accepted_of_selected 13 71754 ⟨129270, by decide⟩ ⟨13, 2, 0, 129270, 71754, 1053, 16384⟩
    (by decide) selected_cut_04059

theorem selected_cut_04060 : selected 8 ⟨129277, by decide⟩
    (prefixPartial 13 71755) = some ⟨13, 2, 0, 129277, 71755, 833, 16384⟩ := by
  decide +kernel

theorem context_13_71755_129277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71755 ⟨129277, by decide⟩ :=
  accepted_of_selected 13 71755 ⟨129277, by decide⟩ ⟨13, 2, 0, 129277, 71755, 833, 16384⟩
    (by decide) selected_cut_04060

theorem unmarked_context_12_17938_129278 : frontier 9 ⟨129278, by decide⟩
    (prefixCache 12 17938) (prefixPartial 12 17938) = false := by
  decide +kernel

theorem node_context_12_17938_129278 : EJMOriginalGlobalDAGData.nodes 9 ⟨129278, by decide⟩ =
    .split (coordinate 12) (![⟨129224, by decide⟩,⟨129253, by decide⟩,⟨129270, by decide⟩,⟨129277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17938_129278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17938 ⟨129278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17938
    ⟨129278, by decide⟩ (by decide) (![⟨129224, by decide⟩,⟨129253, by decide⟩,⟨129270, by decide⟩,⟨129277, by decide⟩]) unmarked_context_12_17938_129278 node_context_12_17938_129278
  intro a
  fin_cases a
  · exact context_13_71752_129224
  · exact context_13_71753_129253
  · exact context_13_71754_129270
  · exact context_13_71755_129277

theorem selected_cut_04061 : selected 8 ⟨129311, by decide⟩
    (prefixPartial 13 71756) = some ⟨13, 2, 0, 129311, 71756, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_71756_129311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71756 ⟨129311, by decide⟩ :=
  accepted_of_selected 13 71756 ⟨129311, by decide⟩ ⟨13, 2, 0, 129311, 71756, 2409, 16384⟩
    (by decide) selected_cut_04061

theorem selected_cut_04062 : selected 8 ⟨129346, by decide⟩
    (prefixPartial 13 71757) = some ⟨13, 2, 0, 129346, 71757, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_71757_129346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71757 ⟨129346, by decide⟩ :=
  accepted_of_selected 13 71757 ⟨129346, by decide⟩ ⟨13, 2, 0, 129346, 71757, 2129, 16384⟩
    (by decide) selected_cut_04062

theorem selected_cut_04063 : selected 8 ⟨129365, by decide⟩
    (prefixPartial 13 71758) = some ⟨13, 2, 0, 129365, 71758, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_71758_129365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71758 ⟨129365, by decide⟩ :=
  accepted_of_selected 13 71758 ⟨129365, by decide⟩ ⟨13, 2, 0, 129365, 71758, 1241, 16384⟩
    (by decide) selected_cut_04063

theorem selected_cut_04064 : selected 8 ⟨129370, by decide⟩
    (prefixPartial 13 71759) = some ⟨13, 2, 0, 129370, 71759, 937, 16384⟩ := by
  decide +kernel

theorem context_13_71759_129370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71759 ⟨129370, by decide⟩ :=
  accepted_of_selected 13 71759 ⟨129370, by decide⟩ ⟨13, 2, 0, 129370, 71759, 937, 16384⟩
    (by decide) selected_cut_04064

theorem unmarked_context_12_17939_129371 : frontier 9 ⟨129371, by decide⟩
    (prefixCache 12 17939) (prefixPartial 12 17939) = false := by
  decide +kernel

theorem node_context_12_17939_129371 : EJMOriginalGlobalDAGData.nodes 9 ⟨129371, by decide⟩ =
    .split (coordinate 12) (![⟨129311, by decide⟩,⟨129346, by decide⟩,⟨129365, by decide⟩,⟨129370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17939_129371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17939 ⟨129371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17939
    ⟨129371, by decide⟩ (by decide) (![⟨129311, by decide⟩,⟨129346, by decide⟩,⟨129365, by decide⟩,⟨129370, by decide⟩]) unmarked_context_12_17939_129371 node_context_12_17939_129371
  intro a
  fin_cases a
  · exact context_13_71756_129311
  · exact context_13_71757_129346
  · exact context_13_71758_129365
  · exact context_13_71759_129370

theorem unmarked_context_11_4484_129372 : frontier 10 ⟨129372, by decide⟩
    (prefixCache 11 4484) (prefixPartial 11 4484) = false := by
  decide +kernel

theorem node_context_11_4484_129372 : EJMOriginalGlobalDAGData.nodes 10 ⟨129372, by decide⟩ =
    .split (coordinate 11) (![⟨129102, by decide⟩,⟨129196, by decide⟩,⟨129278, by decide⟩,⟨129371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4484_129372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4484 ⟨129372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4484
    ⟨129372, by decide⟩ (by decide) (![⟨129102, by decide⟩,⟨129196, by decide⟩,⟨129278, by decide⟩,⟨129371, by decide⟩]) unmarked_context_11_4484_129372 node_context_11_4484_129372
  intro a
  fin_cases a
  · exact context_12_17936_129102
  · exact context_12_17937_129196
  · exact context_12_17938_129278
  · exact context_12_17939_129371

theorem selected_cut_04065 : selected 8 ⟨129411, by decide⟩
    (prefixPartial 13 71760) = some ⟨13, 2, 0, 129411, 71760, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_71760_129411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71760 ⟨129411, by decide⟩ :=
  accepted_of_selected 13 71760 ⟨129411, by decide⟩ ⟨13, 2, 0, 129411, 71760, 2257, 16384⟩
    (by decide) selected_cut_04065

theorem selected_cut_04066 : selected 8 ⟨129463, by decide⟩
    (prefixPartial 13 71761) = some ⟨13, 2, 0, 129463, 71761, 3481, 16384⟩ := by
  decide +kernel

theorem context_13_71761_129463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71761 ⟨129463, by decide⟩ :=
  accepted_of_selected 13 71761 ⟨129463, by decide⟩ ⟨13, 2, 0, 129463, 71761, 3481, 16384⟩
    (by decide) selected_cut_04066

theorem selected_cut_04067 : selected 8 ⟨129480, by decide⟩
    (prefixPartial 13 71762) = some ⟨13, 2, 0, 129480, 71762, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_71762_129480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71762 ⟨129480, by decide⟩ :=
  accepted_of_selected 13 71762 ⟨129480, by decide⟩ ⟨13, 2, 0, 129480, 71762, 2193, 16384⟩
    (by decide) selected_cut_04067

theorem selected_cut_04068 : selected 8 ⟨129487, by decide⟩
    (prefixPartial 13 71763) = some ⟨13, 2, 0, 129487, 71763, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_71763_129487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71763 ⟨129487, by decide⟩ :=
  accepted_of_selected 13 71763 ⟨129487, by decide⟩ ⟨13, 2, 0, 129487, 71763, 1229, 16384⟩
    (by decide) selected_cut_04068

theorem unmarked_context_12_17940_129488 : frontier 9 ⟨129488, by decide⟩
    (prefixCache 12 17940) (prefixPartial 12 17940) = false := by
  decide +kernel

theorem node_context_12_17940_129488 : EJMOriginalGlobalDAGData.nodes 9 ⟨129488, by decide⟩ =
    .split (coordinate 12) (![⟨129411, by decide⟩,⟨129463, by decide⟩,⟨129480, by decide⟩,⟨129487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17940_129488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17940 ⟨129488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17940
    ⟨129488, by decide⟩ (by decide) (![⟨129411, by decide⟩,⟨129463, by decide⟩,⟨129480, by decide⟩,⟨129487, by decide⟩]) unmarked_context_12_17940_129488 node_context_12_17940_129488
  intro a
  fin_cases a
  · exact context_13_71760_129411
  · exact context_13_71761_129463
  · exact context_13_71762_129480
  · exact context_13_71763_129487

theorem selected_cut_04069 : selected 8 ⟨129532, by decide⟩
    (prefixPartial 13 71764) = some ⟨13, 2, 0, 129532, 71764, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_71764_129532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71764 ⟨129532, by decide⟩ :=
  accepted_of_selected 13 71764 ⟨129532, by decide⟩ ⟨13, 2, 0, 129532, 71764, 2753, 16384⟩
    (by decide) selected_cut_04069

theorem selected_cut_04070 : selected 8 ⟨129594, by decide⟩
    (prefixPartial 13 71765) = some ⟨13, 2, 0, 129594, 71765, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_71765_129594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71765 ⟨129594, by decide⟩ :=
  accepted_of_selected 13 71765 ⟨129594, by decide⟩ ⟨13, 2, 0, 129594, 71765, 3205, 16384⟩
    (by decide) selected_cut_04070

theorem selected_cut_04071 : selected 8 ⟨129616, by decide⟩
    (prefixPartial 13 71766) = some ⟨13, 2, 0, 129616, 71766, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_71766_129616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71766 ⟨129616, by decide⟩ :=
  accepted_of_selected 13 71766 ⟨129616, by decide⟩ ⟨13, 2, 0, 129616, 71766, 1877, 16384⟩
    (by decide) selected_cut_04071

theorem selected_cut_04072 : selected 8 ⟨129632, by decide⟩
    (prefixPartial 13 71767) = some ⟨13, 2, 0, 129632, 71767, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_71767_129632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71767 ⟨129632, by decide⟩ :=
  accepted_of_selected 13 71767 ⟨129632, by decide⟩ ⟨13, 2, 0, 129632, 71767, 1133, 16384⟩
    (by decide) selected_cut_04072

theorem unmarked_context_12_17941_129633 : frontier 9 ⟨129633, by decide⟩
    (prefixCache 12 17941) (prefixPartial 12 17941) = false := by
  decide +kernel

theorem node_context_12_17941_129633 : EJMOriginalGlobalDAGData.nodes 9 ⟨129633, by decide⟩ =
    .split (coordinate 12) (![⟨129532, by decide⟩,⟨129594, by decide⟩,⟨129616, by decide⟩,⟨129632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17941_129633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17941 ⟨129633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17941
    ⟨129633, by decide⟩ (by decide) (![⟨129532, by decide⟩,⟨129594, by decide⟩,⟨129616, by decide⟩,⟨129632, by decide⟩]) unmarked_context_12_17941_129633 node_context_12_17941_129633
  intro a
  fin_cases a
  · exact context_13_71764_129532
  · exact context_13_71765_129594
  · exact context_13_71766_129616
  · exact context_13_71767_129632

theorem selected_cut_04073 : selected 8 ⟨129680, by decide⟩
    (prefixPartial 13 71768) = some ⟨13, 2, 0, 129680, 71768, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_71768_129680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71768 ⟨129680, by decide⟩ :=
  accepted_of_selected 13 71768 ⟨129680, by decide⟩ ⟨13, 2, 0, 129680, 71768, 2521, 16384⟩
    (by decide) selected_cut_04073

theorem selected_cut_04074 : selected 8 ⟨129750, by decide⟩
    (prefixPartial 13 71769) = some ⟨13, 2, 0, 129750, 71769, 3557, 16384⟩ := by
  decide +kernel

theorem context_13_71769_129750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71769 ⟨129750, by decide⟩ :=
  accepted_of_selected 13 71769 ⟨129750, by decide⟩ ⟨13, 2, 0, 129750, 71769, 3557, 16384⟩
    (by decide) selected_cut_04074

theorem selected_cut_04075 : selected 8 ⟨129770, by decide⟩
    (prefixPartial 13 71770) = some ⟨13, 2, 0, 129770, 71770, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_71770_129770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71770 ⟨129770, by decide⟩ :=
  accepted_of_selected 13 71770 ⟨129770, by decide⟩ ⟨13, 2, 0, 129770, 71770, 1861, 16384⟩
    (by decide) selected_cut_04075

theorem selected_cut_04076 : selected 8 ⟨129780, by decide⟩
    (prefixPartial 13 71771) = some ⟨13, 2, 0, 129780, 71771, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_71771_129780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71771 ⟨129780, by decide⟩ :=
  accepted_of_selected 13 71771 ⟨129780, by decide⟩ ⟨13, 2, 0, 129780, 71771, 1201, 16384⟩
    (by decide) selected_cut_04076

theorem unmarked_context_12_17942_129781 : frontier 9 ⟨129781, by decide⟩
    (prefixCache 12 17942) (prefixPartial 12 17942) = false := by
  decide +kernel

theorem node_context_12_17942_129781 : EJMOriginalGlobalDAGData.nodes 9 ⟨129781, by decide⟩ =
    .split (coordinate 12) (![⟨129680, by decide⟩,⟨129750, by decide⟩,⟨129770, by decide⟩,⟨129780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17942_129781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17942 ⟨129781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17942
    ⟨129781, by decide⟩ (by decide) (![⟨129680, by decide⟩,⟨129750, by decide⟩,⟨129770, by decide⟩,⟨129780, by decide⟩]) unmarked_context_12_17942_129781 node_context_12_17942_129781
  intro a
  fin_cases a
  · exact context_13_71768_129680
  · exact context_13_71769_129750
  · exact context_13_71770_129770
  · exact context_13_71771_129780

theorem selected_cut_04077 : selected 8 ⟨129843, by decide⟩
    (prefixPartial 13 71772) = some ⟨13, 2, 0, 129843, 71772, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_71772_129843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71772 ⟨129843, by decide⟩ :=
  accepted_of_selected 13 71772 ⟨129843, by decide⟩ ⟨13, 2, 0, 129843, 71772, 3229, 16384⟩
    (by decide) selected_cut_04077

theorem selected_cut_04078 : selected 8 ⟨129916, by decide⟩
    (prefixPartial 13 71773) = some ⟨13, 2, 0, 129916, 71773, 3941, 16384⟩ := by
  decide +kernel

theorem context_13_71773_129916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71773 ⟨129916, by decide⟩ :=
  accepted_of_selected 13 71773 ⟨129916, by decide⟩ ⟨13, 2, 0, 129916, 71773, 3941, 16384⟩
    (by decide) selected_cut_04078

theorem selected_cut_04079 : selected 8 ⟨129940, by decide⟩
    (prefixPartial 13 71774) = some ⟨13, 2, 0, 129940, 71774, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_71774_129940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71774 ⟨129940, by decide⟩ :=
  accepted_of_selected 13 71774 ⟨129940, by decide⟩ ⟨13, 2, 0, 129940, 71774, 2117, 16384⟩
    (by decide) selected_cut_04079

theorem selected_cut_04080 : selected 8 ⟨129948, by decide⟩
    (prefixPartial 13 71775) = some ⟨13, 2, 0, 129948, 71775, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_71775_129948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71775 ⟨129948, by decide⟩ :=
  accepted_of_selected 13 71775 ⟨129948, by decide⟩ ⟨13, 2, 0, 129948, 71775, 1249, 16384⟩
    (by decide) selected_cut_04080

theorem unmarked_context_12_17943_129949 : frontier 9 ⟨129949, by decide⟩
    (prefixCache 12 17943) (prefixPartial 12 17943) = false := by
  decide +kernel

theorem node_context_12_17943_129949 : EJMOriginalGlobalDAGData.nodes 9 ⟨129949, by decide⟩ =
    .split (coordinate 12) (![⟨129843, by decide⟩,⟨129916, by decide⟩,⟨129940, by decide⟩,⟨129948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17943_129949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17943 ⟨129949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17943
    ⟨129949, by decide⟩ (by decide) (![⟨129843, by decide⟩,⟨129916, by decide⟩,⟨129940, by decide⟩,⟨129948, by decide⟩]) unmarked_context_12_17943_129949 node_context_12_17943_129949
  intro a
  fin_cases a
  · exact context_13_71772_129843
  · exact context_13_71773_129916
  · exact context_13_71774_129940
  · exact context_13_71775_129948

theorem unmarked_context_11_4485_129950 : frontier 10 ⟨129950, by decide⟩
    (prefixCache 11 4485) (prefixPartial 11 4485) = false := by
  decide +kernel

theorem node_context_11_4485_129950 : EJMOriginalGlobalDAGData.nodes 10 ⟨129950, by decide⟩ =
    .split (coordinate 11) (![⟨129488, by decide⟩,⟨129633, by decide⟩,⟨129781, by decide⟩,⟨129949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4485_129950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4485 ⟨129950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4485
    ⟨129950, by decide⟩ (by decide) (![⟨129488, by decide⟩,⟨129633, by decide⟩,⟨129781, by decide⟩,⟨129949, by decide⟩]) unmarked_context_11_4485_129950 node_context_11_4485_129950
  intro a
  fin_cases a
  · exact context_12_17940_129488
  · exact context_12_17941_129633
  · exact context_12_17942_129781
  · exact context_12_17943_129949

theorem selected_cut_04081 : selected 8 ⟨129970, by decide⟩
    (prefixPartial 13 71776) = some ⟨13, 2, 0, 129970, 71776, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_71776_129970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71776 ⟨129970, by decide⟩ :=
  accepted_of_selected 13 71776 ⟨129970, by decide⟩ ⟨13, 2, 0, 129970, 71776, 1309, 16384⟩
    (by decide) selected_cut_04081

theorem selected_cut_04082 : selected 8 ⟨129992, by decide⟩
    (prefixPartial 13 71777) = some ⟨13, 2, 0, 129992, 71777, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_71777_129992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71777 ⟨129992, by decide⟩ :=
  accepted_of_selected 13 71777 ⟨129992, by decide⟩ ⟨13, 2, 0, 129992, 71777, 1601, 16384⟩
    (by decide) selected_cut_04082

theorem selected_cut_04083 : selected 8 ⟨130011, by decide⟩
    (prefixPartial 13 71778) = some ⟨13, 2, 0, 130011, 71778, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_71778_130011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71778 ⟨130011, by decide⟩ :=
  accepted_of_selected 13 71778 ⟨130011, by decide⟩ ⟨13, 2, 0, 130011, 71778, 1341, 16384⟩
    (by decide) selected_cut_04083

theorem selected_cut_04084 : selected 8 ⟨130018, by decide⟩
    (prefixPartial 13 71779) = some ⟨13, 2, 0, 130018, 71779, 941, 16384⟩ := by
  decide +kernel

theorem context_13_71779_130018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71779 ⟨130018, by decide⟩ :=
  accepted_of_selected 13 71779 ⟨130018, by decide⟩ ⟨13, 2, 0, 130018, 71779, 941, 16384⟩
    (by decide) selected_cut_04084

theorem unmarked_context_12_17944_130019 : frontier 9 ⟨130019, by decide⟩
    (prefixCache 12 17944) (prefixPartial 12 17944) = false := by
  decide +kernel

theorem node_context_12_17944_130019 : EJMOriginalGlobalDAGData.nodes 9 ⟨130019, by decide⟩ =
    .split (coordinate 12) (![⟨129970, by decide⟩,⟨129992, by decide⟩,⟨130011, by decide⟩,⟨130018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17944_130019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17944 ⟨130019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17944
    ⟨130019, by decide⟩ (by decide) (![⟨129970, by decide⟩,⟨129992, by decide⟩,⟨130011, by decide⟩,⟨130018, by decide⟩]) unmarked_context_12_17944_130019 node_context_12_17944_130019
  intro a
  fin_cases a
  · exact context_13_71776_129970
  · exact context_13_71777_129992
  · exact context_13_71778_130011
  · exact context_13_71779_130018

theorem selected_cut_04085 : selected 8 ⟨130047, by decide⟩
    (prefixPartial 13 71780) = some ⟨13, 2, 0, 130047, 71780, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_71780_130047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71780 ⟨130047, by decide⟩ :=
  accepted_of_selected 13 71780 ⟨130047, by decide⟩ ⟨13, 2, 0, 130047, 71780, 1785, 16384⟩
    (by decide) selected_cut_04085

theorem selected_cut_04086 : selected 8 ⟨130076, by decide⟩
    (prefixPartial 13 71781) = some ⟨13, 2, 0, 130076, 71781, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_71781_130076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71781 ⟨130076, by decide⟩ :=
  accepted_of_selected 13 71781 ⟨130076, by decide⟩ ⟨13, 2, 0, 130076, 71781, 1549, 16384⟩
    (by decide) selected_cut_04086

theorem selected_cut_04087 : selected 8 ⟨130097, by decide⟩
    (prefixPartial 13 71782) = some ⟨13, 2, 0, 130097, 71782, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_71782_130097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71782 ⟨130097, by decide⟩ :=
  accepted_of_selected 13 71782 ⟨130097, by decide⟩ ⟨13, 2, 0, 130097, 71782, 1421, 16384⟩
    (by decide) selected_cut_04087

theorem selected_cut_04088 : selected 8 ⟨130110, by decide⟩
    (prefixPartial 13 71783) = some ⟨13, 2, 0, 130110, 71783, 889, 16384⟩ := by
  decide +kernel

theorem context_13_71783_130110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71783 ⟨130110, by decide⟩ :=
  accepted_of_selected 13 71783 ⟨130110, by decide⟩ ⟨13, 2, 0, 130110, 71783, 889, 16384⟩
    (by decide) selected_cut_04088

theorem unmarked_context_12_17945_130111 : frontier 9 ⟨130111, by decide⟩
    (prefixCache 12 17945) (prefixPartial 12 17945) = false := by
  decide +kernel

theorem node_context_12_17945_130111 : EJMOriginalGlobalDAGData.nodes 9 ⟨130111, by decide⟩ =
    .split (coordinate 12) (![⟨130047, by decide⟩,⟨130076, by decide⟩,⟨130097, by decide⟩,⟨130110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17945_130111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17945 ⟨130111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17945
    ⟨130111, by decide⟩ (by decide) (![⟨130047, by decide⟩,⟨130076, by decide⟩,⟨130097, by decide⟩,⟨130110, by decide⟩]) unmarked_context_12_17945_130111 node_context_12_17945_130111
  intro a
  fin_cases a
  · exact context_13_71780_130047
  · exact context_13_71781_130076
  · exact context_13_71782_130097
  · exact context_13_71783_130110

theorem selected_cut_04089 : selected 8 ⟨130145, by decide⟩
    (prefixPartial 13 71784) = some ⟨13, 2, 0, 130145, 71784, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_71784_130145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71784 ⟨130145, by decide⟩ :=
  accepted_of_selected 13 71784 ⟨130145, by decide⟩ ⟨13, 2, 0, 130145, 71784, 2225, 16384⟩
    (by decide) selected_cut_04089

theorem selected_cut_04090 : selected 8 ⟨130183, by decide⟩
    (prefixPartial 13 71785) = some ⟨13, 2, 0, 130183, 71785, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_71785_130183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71785 ⟨130183, by decide⟩ :=
  accepted_of_selected 13 71785 ⟨130183, by decide⟩ ⟨13, 2, 0, 130183, 71785, 2749, 16384⟩
    (by decide) selected_cut_04090

theorem selected_cut_04091 : selected 8 ⟨130208, by decide⟩
    (prefixPartial 13 71786) = some ⟨13, 2, 0, 130208, 71786, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_71786_130208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71786 ⟨130208, by decide⟩ :=
  accepted_of_selected 13 71786 ⟨130208, by decide⟩ ⟨13, 2, 0, 130208, 71786, 1937, 16384⟩
    (by decide) selected_cut_04091

theorem selected_cut_04092 : selected 8 ⟨130215, by decide⟩
    (prefixPartial 13 71787) = some ⟨13, 2, 0, 130215, 71787, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_71787_130215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71787 ⟨130215, by decide⟩ :=
  accepted_of_selected 13 71787 ⟨130215, by decide⟩ ⟨13, 2, 0, 130215, 71787, 1145, 16384⟩
    (by decide) selected_cut_04092

theorem unmarked_context_12_17946_130216 : frontier 9 ⟨130216, by decide⟩
    (prefixCache 12 17946) (prefixPartial 12 17946) = false := by
  decide +kernel

theorem node_context_12_17946_130216 : EJMOriginalGlobalDAGData.nodes 9 ⟨130216, by decide⟩ =
    .split (coordinate 12) (![⟨130145, by decide⟩,⟨130183, by decide⟩,⟨130208, by decide⟩,⟨130215, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17946_130216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17946 ⟨130216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17946
    ⟨130216, by decide⟩ (by decide) (![⟨130145, by decide⟩,⟨130183, by decide⟩,⟨130208, by decide⟩,⟨130215, by decide⟩]) unmarked_context_12_17946_130216 node_context_12_17946_130216
  intro a
  fin_cases a
  · exact context_13_71784_130145
  · exact context_13_71785_130183
  · exact context_13_71786_130208
  · exact context_13_71787_130215

theorem selected_cut_04093 : selected 8 ⟨130246, by decide⟩
    (prefixPartial 13 71788) = some ⟨13, 2, 0, 130246, 71788, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_71788_130246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71788 ⟨130246, by decide⟩ :=
  accepted_of_selected 13 71788 ⟨130246, by decide⟩ ⟨13, 2, 0, 130246, 71788, 1673, 16384⟩
    (by decide) selected_cut_04093

theorem selected_cut_04094 : selected 8 ⟨130279, by decide⟩
    (prefixPartial 13 71789) = some ⟨13, 2, 0, 130279, 71789, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_71789_130279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71789 ⟨130279, by decide⟩ :=
  accepted_of_selected 13 71789 ⟨130279, by decide⟩ ⟨13, 2, 0, 130279, 71789, 1925, 16384⟩
    (by decide) selected_cut_04094

theorem selected_cut_04095 : selected 8 ⟨130300, by decide⟩
    (prefixPartial 13 71790) = some ⟨13, 2, 0, 130300, 71790, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_71790_130300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71790 ⟨130300, by decide⟩ :=
  accepted_of_selected 13 71790 ⟨130300, by decide⟩ ⟨13, 2, 0, 130300, 71790, 1401, 16384⟩
    (by decide) selected_cut_04095

theorem selected_cut_04096 : selected 8 ⟨130308, by decide⟩
    (prefixPartial 13 71791) = some ⟨13, 2, 0, 130308, 71791, 913, 16384⟩ := by
  decide +kernel

theorem context_13_71791_130308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71791 ⟨130308, by decide⟩ :=
  accepted_of_selected 13 71791 ⟨130308, by decide⟩ ⟨13, 2, 0, 130308, 71791, 913, 16384⟩
    (by decide) selected_cut_04096

theorem unmarked_context_12_17947_130309 : frontier 9 ⟨130309, by decide⟩
    (prefixCache 12 17947) (prefixPartial 12 17947) = false := by
  decide +kernel

theorem node_context_12_17947_130309 : EJMOriginalGlobalDAGData.nodes 9 ⟨130309, by decide⟩ =
    .split (coordinate 12) (![⟨130246, by decide⟩,⟨130279, by decide⟩,⟨130300, by decide⟩,⟨130308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17947_130309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17947 ⟨130309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17947
    ⟨130309, by decide⟩ (by decide) (![⟨130246, by decide⟩,⟨130279, by decide⟩,⟨130300, by decide⟩,⟨130308, by decide⟩]) unmarked_context_12_17947_130309 node_context_12_17947_130309
  intro a
  fin_cases a
  · exact context_13_71788_130246
  · exact context_13_71789_130279
  · exact context_13_71790_130300
  · exact context_13_71791_130308

theorem unmarked_context_11_4486_130310 : frontier 10 ⟨130310, by decide⟩
    (prefixCache 11 4486) (prefixPartial 11 4486) = false := by
  decide +kernel

theorem node_context_11_4486_130310 : EJMOriginalGlobalDAGData.nodes 10 ⟨130310, by decide⟩ =
    .split (coordinate 11) (![⟨130019, by decide⟩,⟨130111, by decide⟩,⟨130216, by decide⟩,⟨130309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4486_130310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4486 ⟨130310, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4486
    ⟨130310, by decide⟩ (by decide) (![⟨130019, by decide⟩,⟨130111, by decide⟩,⟨130216, by decide⟩,⟨130309, by decide⟩]) unmarked_context_11_4486_130310 node_context_11_4486_130310
  intro a
  fin_cases a
  · exact context_12_17944_130019
  · exact context_12_17945_130111
  · exact context_12_17946_130216
  · exact context_12_17947_130309

theorem selected_cut_04097 : selected 8 ⟨130327, by decide⟩
    (prefixPartial 13 71792) = some ⟨13, 2, 0, 130327, 71792, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_71792_130327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71792 ⟨130327, by decide⟩ :=
  accepted_of_selected 13 71792 ⟨130327, by decide⟩ ⟨13, 2, 0, 130327, 71792, 1197, 16384⟩
    (by decide) selected_cut_04097

theorem selected_cut_04098 : selected 8 ⟨130354, by decide⟩
    (prefixPartial 13 71793) = some ⟨13, 2, 0, 130354, 71793, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_71793_130354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71793 ⟨130354, by decide⟩ :=
  accepted_of_selected 13 71793 ⟨130354, by decide⟩ ⟨13, 2, 0, 130354, 71793, 1493, 16384⟩
    (by decide) selected_cut_04098

theorem selected_cut_04099 : selected 8 ⟨130375, by decide⟩
    (prefixPartial 13 71794) = some ⟨13, 2, 0, 130375, 71794, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_71794_130375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71794 ⟨130375, by decide⟩ :=
  accepted_of_selected 13 71794 ⟨130375, by decide⟩ ⟨13, 2, 0, 130375, 71794, 1869, 16384⟩
    (by decide) selected_cut_04099

theorem selected_cut_04100 : selected 8 ⟨130387, by decide⟩
    (prefixPartial 13 71795) = some ⟨13, 2, 0, 130387, 71795, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_71795_130387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71795 ⟨130387, by decide⟩ :=
  accepted_of_selected 13 71795 ⟨130387, by decide⟩ ⟨13, 2, 0, 130387, 71795, 1001, 16384⟩
    (by decide) selected_cut_04100

theorem unmarked_context_12_17948_130388 : frontier 9 ⟨130388, by decide⟩
    (prefixCache 12 17948) (prefixPartial 12 17948) = false := by
  decide +kernel

theorem node_context_12_17948_130388 : EJMOriginalGlobalDAGData.nodes 9 ⟨130388, by decide⟩ =
    .split (coordinate 12) (![⟨130327, by decide⟩,⟨130354, by decide⟩,⟨130375, by decide⟩,⟨130387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17948_130388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17948 ⟨130388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17948
    ⟨130388, by decide⟩ (by decide) (![⟨130327, by decide⟩,⟨130354, by decide⟩,⟨130375, by decide⟩,⟨130387, by decide⟩]) unmarked_context_12_17948_130388 node_context_12_17948_130388
  intro a
  fin_cases a
  · exact context_13_71792_130327
  · exact context_13_71793_130354
  · exact context_13_71794_130375
  · exact context_13_71795_130387

theorem selected_cut_04101 : selected 8 ⟨130419, by decide⟩
    (prefixPartial 13 71796) = some ⟨13, 2, 0, 130419, 71796, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_71796_130419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71796 ⟨130419, by decide⟩ :=
  accepted_of_selected 13 71796 ⟨130419, by decide⟩ ⟨13, 2, 0, 130419, 71796, 1701, 16384⟩
    (by decide) selected_cut_04101

theorem selected_cut_04102 : selected 8 ⟨130457, by decide⟩
    (prefixPartial 13 71797) = some ⟨13, 2, 0, 130457, 71797, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_71797_130457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71797 ⟨130457, by decide⟩ :=
  accepted_of_selected 13 71797 ⟨130457, by decide⟩ ⟨13, 2, 0, 130457, 71797, 1757, 16384⟩
    (by decide) selected_cut_04102

theorem selected_cut_04103 : selected 8 ⟨130478, by decide⟩
    (prefixPartial 13 71798) = some ⟨13, 2, 0, 130478, 71798, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_71798_130478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71798 ⟨130478, by decide⟩ :=
  accepted_of_selected 13 71798 ⟨130478, by decide⟩ ⟨13, 2, 0, 130478, 71798, 1685, 16384⟩
    (by decide) selected_cut_04103

theorem selected_cut_04104 : selected 8 ⟨130488, by decide⟩
    (prefixPartial 13 71799) = some ⟨13, 2, 0, 130488, 71799, 893, 16384⟩ := by
  decide +kernel

theorem context_13_71799_130488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71799 ⟨130488, by decide⟩ :=
  accepted_of_selected 13 71799 ⟨130488, by decide⟩ ⟨13, 2, 0, 130488, 71799, 893, 16384⟩
    (by decide) selected_cut_04104

theorem unmarked_context_12_17949_130489 : frontier 9 ⟨130489, by decide⟩
    (prefixCache 12 17949) (prefixPartial 12 17949) = false := by
  decide +kernel

theorem node_context_12_17949_130489 : EJMOriginalGlobalDAGData.nodes 9 ⟨130489, by decide⟩ =
    .split (coordinate 12) (![⟨130419, by decide⟩,⟨130457, by decide⟩,⟨130478, by decide⟩,⟨130488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17949_130489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17949 ⟨130489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17949
    ⟨130489, by decide⟩ (by decide) (![⟨130419, by decide⟩,⟨130457, by decide⟩,⟨130478, by decide⟩,⟨130488, by decide⟩]) unmarked_context_12_17949_130489 node_context_12_17949_130489
  intro a
  fin_cases a
  · exact context_13_71796_130419
  · exact context_13_71797_130457
  · exact context_13_71798_130478
  · exact context_13_71799_130488

theorem selected_cut_04105 : selected 8 ⟨130511, by decide⟩
    (prefixPartial 13 71800) = some ⟨13, 2, 0, 130511, 71800, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_71800_130511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71800 ⟨130511, by decide⟩ :=
  accepted_of_selected 13 71800 ⟨130511, by decide⟩ ⟨13, 2, 0, 130511, 71800, 1329, 16384⟩
    (by decide) selected_cut_04105

theorem selected_cut_04106 : selected 8 ⟨130548, by decide⟩
    (prefixPartial 13 71801) = some ⟨13, 2, 0, 130548, 71801, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_71801_130548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71801 ⟨130548, by decide⟩ :=
  accepted_of_selected 13 71801 ⟨130548, by decide⟩ ⟨13, 2, 0, 130548, 71801, 1785, 16384⟩
    (by decide) selected_cut_04106

theorem selected_cut_04107 : selected 8 ⟨130568, by decide⟩
    (prefixPartial 13 71802) = some ⟨13, 2, 0, 130568, 71802, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_71802_130568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71802 ⟨130568, by decide⟩ :=
  accepted_of_selected 13 71802 ⟨130568, by decide⟩ ⟨13, 2, 0, 130568, 71802, 1357, 16384⟩
    (by decide) selected_cut_04107

theorem selected_cut_04108 : selected 8 ⟨130577, by decide⟩
    (prefixPartial 13 71803) = some ⟨13, 2, 0, 130577, 71803, 889, 16384⟩ := by
  decide +kernel

theorem context_13_71803_130577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71803 ⟨130577, by decide⟩ :=
  accepted_of_selected 13 71803 ⟨130577, by decide⟩ ⟨13, 2, 0, 130577, 71803, 889, 16384⟩
    (by decide) selected_cut_04108

theorem unmarked_context_12_17950_130578 : frontier 9 ⟨130578, by decide⟩
    (prefixCache 12 17950) (prefixPartial 12 17950) = false := by
  decide +kernel

theorem node_context_12_17950_130578 : EJMOriginalGlobalDAGData.nodes 9 ⟨130578, by decide⟩ =
    .split (coordinate 12) (![⟨130511, by decide⟩,⟨130548, by decide⟩,⟨130568, by decide⟩,⟨130577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17950_130578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17950 ⟨130578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17950
    ⟨130578, by decide⟩ (by decide) (![⟨130511, by decide⟩,⟨130548, by decide⟩,⟨130568, by decide⟩,⟨130577, by decide⟩]) unmarked_context_12_17950_130578 node_context_12_17950_130578
  intro a
  fin_cases a
  · exact context_13_71800_130511
  · exact context_13_71801_130548
  · exact context_13_71802_130568
  · exact context_13_71803_130577

theorem selected_cut_04109 : selected 8 ⟨130601, by decide⟩
    (prefixPartial 13 71804) = some ⟨13, 2, 0, 130601, 71804, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_71804_130601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71804 ⟨130601, by decide⟩ :=
  accepted_of_selected 13 71804 ⟨130601, by decide⟩ ⟨13, 2, 0, 130601, 71804, 1453, 16384⟩
    (by decide) selected_cut_04109

theorem selected_cut_04110 : selected 8 ⟨130630, by decide⟩
    (prefixPartial 13 71805) = some ⟨13, 2, 0, 130630, 71805, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_71805_130630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71805 ⟨130630, by decide⟩ :=
  accepted_of_selected 13 71805 ⟨130630, by decide⟩ ⟨13, 2, 0, 130630, 71805, 1717, 16384⟩
    (by decide) selected_cut_04110

theorem selected_cut_04111 : selected 8 ⟨130650, by decide⟩
    (prefixPartial 13 71806) = some ⟨13, 2, 0, 130650, 71806, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_71806_130650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71806 ⟨130650, by decide⟩ :=
  accepted_of_selected 13 71806 ⟨130650, by decide⟩ ⟨13, 2, 0, 130650, 71806, 1453, 16384⟩
    (by decide) selected_cut_04111

theorem selected_cut_04112 : selected 8 ⟨130658, by decide⟩
    (prefixPartial 13 71807) = some ⟨13, 2, 0, 130658, 71807, 869, 16384⟩ := by
  decide +kernel

theorem context_13_71807_130658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71807 ⟨130658, by decide⟩ :=
  accepted_of_selected 13 71807 ⟨130658, by decide⟩ ⟨13, 2, 0, 130658, 71807, 869, 16384⟩
    (by decide) selected_cut_04112

theorem unmarked_context_12_17951_130659 : frontier 9 ⟨130659, by decide⟩
    (prefixCache 12 17951) (prefixPartial 12 17951) = false := by
  decide +kernel

theorem node_context_12_17951_130659 : EJMOriginalGlobalDAGData.nodes 9 ⟨130659, by decide⟩ =
    .split (coordinate 12) (![⟨130601, by decide⟩,⟨130630, by decide⟩,⟨130650, by decide⟩,⟨130658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17951_130659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17951 ⟨130659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17951
    ⟨130659, by decide⟩ (by decide) (![⟨130601, by decide⟩,⟨130630, by decide⟩,⟨130650, by decide⟩,⟨130658, by decide⟩]) unmarked_context_12_17951_130659 node_context_12_17951_130659
  intro a
  fin_cases a
  · exact context_13_71804_130601
  · exact context_13_71805_130630
  · exact context_13_71806_130650
  · exact context_13_71807_130658

theorem unmarked_context_11_4487_130660 : frontier 10 ⟨130660, by decide⟩
    (prefixCache 11 4487) (prefixPartial 11 4487) = false := by
  decide +kernel

theorem node_context_11_4487_130660 : EJMOriginalGlobalDAGData.nodes 10 ⟨130660, by decide⟩ =
    .split (coordinate 11) (![⟨130388, by decide⟩,⟨130489, by decide⟩,⟨130578, by decide⟩,⟨130659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4487_130660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4487 ⟨130660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4487
    ⟨130660, by decide⟩ (by decide) (![⟨130388, by decide⟩,⟨130489, by decide⟩,⟨130578, by decide⟩,⟨130659, by decide⟩]) unmarked_context_11_4487_130660 node_context_11_4487_130660
  intro a
  fin_cases a
  · exact context_12_17948_130388
  · exact context_12_17949_130489
  · exact context_12_17950_130578
  · exact context_12_17951_130659

theorem unmarked_context_10_1121_130661 : frontier 11 ⟨130661, by decide⟩
    (prefixCache 10 1121) (prefixPartial 10 1121) = false := by
  decide +kernel

theorem node_context_10_1121_130661 : EJMOriginalGlobalDAGData.nodes 11 ⟨130661, by decide⟩ =
    .split (coordinate 10) (![⟨129372, by decide⟩,⟨129950, by decide⟩,⟨130310, by decide⟩,⟨130660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1121_130661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1121 ⟨130661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1121
    ⟨130661, by decide⟩ (by decide) (![⟨129372, by decide⟩,⟨129950, by decide⟩,⟨130310, by decide⟩,⟨130660, by decide⟩]) unmarked_context_10_1121_130661 node_context_10_1121_130661
  intro a
  fin_cases a
  · exact context_11_4484_129372
  · exact context_11_4485_129950
  · exact context_11_4486_130310
  · exact context_11_4487_130660

theorem selected_cut_04113 : selected 8 ⟨130693, by decide⟩
    (prefixPartial 13 71808) = some ⟨13, 2, 0, 130693, 71808, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_71808_130693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71808 ⟨130693, by decide⟩ :=
  accepted_of_selected 13 71808 ⟨130693, by decide⟩ ⟨13, 2, 0, 130693, 71808, 1357, 16384⟩
    (by decide) selected_cut_04113

theorem selected_cut_04114 : selected 8 ⟨130713, by decide⟩
    (prefixPartial 13 71809) = some ⟨13, 2, 0, 130713, 71809, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_71809_130713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71809 ⟨130713, by decide⟩ :=
  accepted_of_selected 13 71809 ⟨130713, by decide⟩ ⟨13, 2, 0, 130713, 71809, 1661, 16384⟩
    (by decide) selected_cut_04114

theorem selected_cut_04115 : selected 8 ⟨130735, by decide⟩
    (prefixPartial 13 71810) = some ⟨13, 2, 0, 130735, 71810, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_71810_130735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71810 ⟨130735, by decide⟩ :=
  accepted_of_selected 13 71810 ⟨130735, by decide⟩ ⟨13, 2, 0, 130735, 71810, 1289, 16384⟩
    (by decide) selected_cut_04115

theorem selected_cut_04116 : selected 8 ⟨130745, by decide⟩
    (prefixPartial 13 71811) = some ⟨13, 2, 0, 130745, 71811, 805, 16384⟩ := by
  decide +kernel

theorem context_13_71811_130745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71811 ⟨130745, by decide⟩ :=
  accepted_of_selected 13 71811 ⟨130745, by decide⟩ ⟨13, 2, 0, 130745, 71811, 805, 16384⟩
    (by decide) selected_cut_04116

theorem unmarked_context_12_17952_130746 : frontier 9 ⟨130746, by decide⟩
    (prefixCache 12 17952) (prefixPartial 12 17952) = false := by
  decide +kernel

theorem node_context_12_17952_130746 : EJMOriginalGlobalDAGData.nodes 9 ⟨130746, by decide⟩ =
    .split (coordinate 12) (![⟨130693, by decide⟩,⟨130713, by decide⟩,⟨130735, by decide⟩,⟨130745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17952_130746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17952 ⟨130746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17952
    ⟨130746, by decide⟩ (by decide) (![⟨130693, by decide⟩,⟨130713, by decide⟩,⟨130735, by decide⟩,⟨130745, by decide⟩]) unmarked_context_12_17952_130746 node_context_12_17952_130746
  intro a
  fin_cases a
  · exact context_13_71808_130693
  · exact context_13_71809_130713
  · exact context_13_71810_130735
  · exact context_13_71811_130745

theorem selected_cut_04117 : selected 8 ⟨130777, by decide⟩
    (prefixPartial 13 71812) = some ⟨13, 2, 0, 130777, 71812, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_71812_130777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71812 ⟨130777, by decide⟩ :=
  accepted_of_selected 13 71812 ⟨130777, by decide⟩ ⟨13, 2, 0, 130777, 71812, 1501, 16384⟩
    (by decide) selected_cut_04117

theorem selected_cut_04118 : selected 8 ⟨130811, by decide⟩
    (prefixPartial 13 71813) = some ⟨13, 2, 0, 130811, 71813, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_71813_130811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71813 ⟨130811, by decide⟩ :=
  accepted_of_selected 13 71813 ⟨130811, by decide⟩ ⟨13, 2, 0, 130811, 71813, 2001, 16384⟩
    (by decide) selected_cut_04118

theorem selected_cut_04119 : selected 8 ⟨130830, by decide⟩
    (prefixPartial 13 71814) = some ⟨13, 2, 0, 130830, 71814, 957, 16384⟩ := by
  decide +kernel

theorem context_13_71814_130830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71814 ⟨130830, by decide⟩ :=
  accepted_of_selected 13 71814 ⟨130830, by decide⟩ ⟨13, 2, 0, 130830, 71814, 957, 16384⟩
    (by decide) selected_cut_04119

theorem selected_cut_04120 : selected 8 ⟨130838, by decide⟩
    (prefixPartial 13 71815) = some ⟨13, 2, 0, 130838, 71815, 845, 16384⟩ := by
  decide +kernel

theorem context_13_71815_130838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71815 ⟨130838, by decide⟩ :=
  accepted_of_selected 13 71815 ⟨130838, by decide⟩ ⟨13, 2, 0, 130838, 71815, 845, 16384⟩
    (by decide) selected_cut_04120

theorem unmarked_context_12_17953_130839 : frontier 9 ⟨130839, by decide⟩
    (prefixCache 12 17953) (prefixPartial 12 17953) = false := by
  decide +kernel

theorem node_context_12_17953_130839 : EJMOriginalGlobalDAGData.nodes 9 ⟨130839, by decide⟩ =
    .split (coordinate 12) (![⟨130777, by decide⟩,⟨130811, by decide⟩,⟨130830, by decide⟩,⟨130838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17953_130839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17953 ⟨130839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17953
    ⟨130839, by decide⟩ (by decide) (![⟨130777, by decide⟩,⟨130811, by decide⟩,⟨130830, by decide⟩,⟨130838, by decide⟩]) unmarked_context_12_17953_130839 node_context_12_17953_130839
  intro a
  fin_cases a
  · exact context_13_71812_130777
  · exact context_13_71813_130811
  · exact context_13_71814_130830
  · exact context_13_71815_130838

theorem selected_cut_04121 : selected 8 ⟨130860, by decide⟩
    (prefixPartial 13 71816) = some ⟨13, 2, 0, 130860, 71816, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_71816_130860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71816 ⟨130860, by decide⟩ :=
  accepted_of_selected 13 71816 ⟨130860, by decide⟩ ⟨13, 2, 0, 130860, 71816, 1181, 16384⟩
    (by decide) selected_cut_04121

theorem selected_cut_04122 : selected 8 ⟨130892, by decide⟩
    (prefixPartial 13 71817) = some ⟨13, 2, 0, 130892, 71817, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_71817_130892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71817 ⟨130892, by decide⟩ :=
  accepted_of_selected 13 71817 ⟨130892, by decide⟩ ⟨13, 2, 0, 130892, 71817, 1693, 16384⟩
    (by decide) selected_cut_04122

theorem selected_cut_04123 : selected 8 ⟨130905, by decide⟩
    (prefixPartial 13 71818) = some ⟨13, 2, 0, 130905, 71818, 849, 16384⟩ := by
  decide +kernel

theorem context_13_71818_130905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71818 ⟨130905, by decide⟩ :=
  accepted_of_selected 13 71818 ⟨130905, by decide⟩ ⟨13, 2, 0, 130905, 71818, 849, 16384⟩
    (by decide) selected_cut_04123

theorem selected_cut_04124 : selected 8 ⟨130912, by decide⟩
    (prefixPartial 13 71819) = some ⟨13, 2, 0, 130912, 71819, 761, 16384⟩ := by
  decide +kernel

theorem context_13_71819_130912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71819 ⟨130912, by decide⟩ :=
  accepted_of_selected 13 71819 ⟨130912, by decide⟩ ⟨13, 2, 0, 130912, 71819, 761, 16384⟩
    (by decide) selected_cut_04124

theorem unmarked_context_12_17954_130913 : frontier 9 ⟨130913, by decide⟩
    (prefixCache 12 17954) (prefixPartial 12 17954) = false := by
  decide +kernel

theorem node_context_12_17954_130913 : EJMOriginalGlobalDAGData.nodes 9 ⟨130913, by decide⟩ =
    .split (coordinate 12) (![⟨130860, by decide⟩,⟨130892, by decide⟩,⟨130905, by decide⟩,⟨130912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17954_130913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17954 ⟨130913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17954
    ⟨130913, by decide⟩ (by decide) (![⟨130860, by decide⟩,⟨130892, by decide⟩,⟨130905, by decide⟩,⟨130912, by decide⟩]) unmarked_context_12_17954_130913 node_context_12_17954_130913
  intro a
  fin_cases a
  · exact context_13_71816_130860
  · exact context_13_71817_130892
  · exact context_13_71818_130905
  · exact context_13_71819_130912

theorem selected_cut_04125 : selected 8 ⟨130945, by decide⟩
    (prefixPartial 13 71820) = some ⟨13, 2, 0, 130945, 71820, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_71820_130945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71820 ⟨130945, by decide⟩ :=
  accepted_of_selected 13 71820 ⟨130945, by decide⟩ ⟨13, 2, 0, 130945, 71820, 1361, 16384⟩
    (by decide) selected_cut_04125

theorem selected_cut_04126 : selected 8 ⟨130989, by decide⟩
    (prefixPartial 13 71821) = some ⟨13, 2, 0, 130989, 71821, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_71821_130989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71821 ⟨130989, by decide⟩ :=
  accepted_of_selected 13 71821 ⟨130989, by decide⟩ ⟨13, 2, 0, 130989, 71821, 2001, 16384⟩
    (by decide) selected_cut_04126

theorem selected_cut_04127 : selected 8 ⟨131007, by decide⟩
    (prefixPartial 13 71822) = some ⟨13, 2, 0, 131007, 71822, 981, 16384⟩ := by
  decide +kernel

theorem context_13_71822_131007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71822 ⟨131007, by decide⟩ :=
  accepted_of_selected 13 71822 ⟨131007, by decide⟩ ⟨13, 2, 0, 131007, 71822, 981, 16384⟩
    (by decide) selected_cut_04127

theorem selected_cut_04128 : selected 8 ⟨131013, by decide⟩
    (prefixPartial 13 71823) = some ⟨13, 2, 0, 131013, 71823, 829, 16384⟩ := by
  decide +kernel

theorem context_13_71823_131013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71823 ⟨131013, by decide⟩ :=
  accepted_of_selected 13 71823 ⟨131013, by decide⟩ ⟨13, 2, 0, 131013, 71823, 829, 16384⟩
    (by decide) selected_cut_04128

theorem unmarked_context_12_17955_131014 : frontier 9 ⟨131014, by decide⟩
    (prefixCache 12 17955) (prefixPartial 12 17955) = false := by
  decide +kernel

theorem node_context_12_17955_131014 : EJMOriginalGlobalDAGData.nodes 9 ⟨131014, by decide⟩ =
    .split (coordinate 12) (![⟨130945, by decide⟩,⟨130989, by decide⟩,⟨131007, by decide⟩,⟨131013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17955_131014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17955 ⟨131014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17955
    ⟨131014, by decide⟩ (by decide) (![⟨130945, by decide⟩,⟨130989, by decide⟩,⟨131007, by decide⟩,⟨131013, by decide⟩]) unmarked_context_12_17955_131014 node_context_12_17955_131014
  intro a
  fin_cases a
  · exact context_13_71820_130945
  · exact context_13_71821_130989
  · exact context_13_71822_131007
  · exact context_13_71823_131013

theorem unmarked_context_11_4488_131015 : frontier 10 ⟨131015, by decide⟩
    (prefixCache 11 4488) (prefixPartial 11 4488) = false := by
  decide +kernel

theorem node_context_11_4488_131015 : EJMOriginalGlobalDAGData.nodes 10 ⟨131015, by decide⟩ =
    .split (coordinate 11) (![⟨130746, by decide⟩,⟨130839, by decide⟩,⟨130913, by decide⟩,⟨131014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4488_131015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4488 ⟨131015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4488
    ⟨131015, by decide⟩ (by decide) (![⟨130746, by decide⟩,⟨130839, by decide⟩,⟨130913, by decide⟩,⟨131014, by decide⟩]) unmarked_context_11_4488_131015 node_context_11_4488_131015
  intro a
  fin_cases a
  · exact context_12_17952_130746
  · exact context_12_17953_130839
  · exact context_12_17954_130913
  · exact context_12_17955_131014

theorem selected_cut_04129 : selected 8 ⟨131035, by decide⟩
    (prefixPartial 13 71824) = some ⟨13, 2, 0, 131035, 71824, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_71824_131035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71824 ⟨131035, by decide⟩ :=
  accepted_of_selected 13 71824 ⟨131035, by decide⟩ ⟨13, 2, 0, 131035, 71824, 1045, 16384⟩
    (by decide) selected_cut_04129

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
