/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover027
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_02691 : selected 8 ⟨83691, by decide⟩
    (prefixPartial 13 23013) = some ⟨13, 2, 0, 83691, 23013, 461, 16384⟩ := by
  decide +kernel

theorem context_13_23013_83691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23013 ⟨83691, by decide⟩ :=
  accepted_of_selected 13 23013 ⟨83691, by decide⟩ ⟨13, 2, 0, 83691, 23013, 461, 16384⟩
    (by decide) selected_cut_02691

theorem selected_cut_02692 : selected 8 ⟨83732, by decide⟩
    (prefixPartial 13 23014) = some ⟨13, 2, 0, 83732, 23014, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_23014_83732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23014 ⟨83732, by decide⟩ :=
  accepted_of_selected 13 23014 ⟨83732, by decide⟩ ⟨13, 2, 0, 83732, 23014, 2729, 16384⟩
    (by decide) selected_cut_02692

theorem selected_cut_02693 : selected 8 ⟨83744, by decide⟩
    (prefixPartial 13 23015) = some ⟨13, 2, 0, 83744, 23015, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_23015_83744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23015 ⟨83744, by decide⟩ :=
  accepted_of_selected 13 23015 ⟨83744, by decide⟩ ⟨13, 2, 0, 83744, 23015, 1265, 16384⟩
    (by decide) selected_cut_02693

theorem unmarked_context_12_5753_83745 : frontier 9 ⟨83745, by decide⟩
    (prefixCache 12 5753) (prefixPartial 12 5753) = false := by
  decide +kernel

theorem node_context_12_5753_83745 : EJMOriginalGlobalDAGData.nodes 9 ⟨83745, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83691, by decide⟩,⟨83732, by decide⟩,⟨83744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5753_83745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5753 ⟨83745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5753
    ⟨83745, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83691, by decide⟩,⟨83732, by decide⟩,⟨83744, by decide⟩]) unmarked_context_12_5753_83745 node_context_12_5753_83745
  intro a
  fin_cases a
  · exact context_13_23012_3444
  · exact context_13_23013_83691
  · exact context_13_23014_83732
  · exact context_13_23015_83744

theorem selected_cut_02694 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23016) = some ⟨13, 1, 0, 3444, 23016, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23016_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23016 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23016 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23016, 1, 16384⟩
    (by decide) selected_cut_02694

theorem selected_cut_02695 : selected 8 ⟨83758, by decide⟩
    (prefixPartial 13 23017) = some ⟨13, 2, 0, 83758, 23017, 621, 16384⟩ := by
  decide +kernel

theorem context_13_23017_83758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23017 ⟨83758, by decide⟩ :=
  accepted_of_selected 13 23017 ⟨83758, by decide⟩ ⟨13, 2, 0, 83758, 23017, 621, 16384⟩
    (by decide) selected_cut_02695

theorem selected_cut_02696 : selected 7 ⟨83784, by decide⟩
    (prefixPartial 14 92072) = some ⟨14, 2, 0, 83784, 92072, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_92072_83784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 92072 ⟨83784, by decide⟩ :=
  accepted_of_selected 14 92072 ⟨83784, by decide⟩ ⟨14, 2, 0, 83784, 92072, 1117, 4096⟩
    (by decide) selected_cut_02696

theorem selected_cut_02697 : selected 7 ⟨83810, by decide⟩
    (prefixPartial 14 92073) = some ⟨14, 2, 0, 83810, 92073, 1393, 4096⟩ := by
  decide +kernel

theorem context_14_92073_83810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 92073 ⟨83810, by decide⟩ :=
  accepted_of_selected 14 92073 ⟨83810, by decide⟩ ⟨14, 2, 0, 83810, 92073, 1393, 4096⟩
    (by decide) selected_cut_02697

theorem selected_cut_02698 : selected 7 ⟨83827, by decide⟩
    (prefixPartial 14 92074) = some ⟨14, 2, 0, 83827, 92074, 997, 4096⟩ := by
  decide +kernel

theorem context_14_92074_83827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 92074 ⟨83827, by decide⟩ :=
  accepted_of_selected 14 92074 ⟨83827, by decide⟩ ⟨14, 2, 0, 83827, 92074, 997, 4096⟩
    (by decide) selected_cut_02698

theorem selected_cut_02699 : selected 7 ⟨83847, by decide⟩
    (prefixPartial 14 92075) = some ⟨14, 2, 0, 83847, 92075, 1097, 4096⟩ := by
  decide +kernel

theorem context_14_92075_83847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 92075 ⟨83847, by decide⟩ :=
  accepted_of_selected 14 92075 ⟨83847, by decide⟩ ⟨14, 2, 0, 83847, 92075, 1097, 4096⟩
    (by decide) selected_cut_02699

theorem unmarked_context_13_23018_83848 : frontier 8 ⟨83848, by decide⟩
    (prefixCache 13 23018) (prefixPartial 13 23018) = false := by
  decide +kernel

theorem node_context_13_23018_83848 : EJMOriginalGlobalDAGData.nodes 8 ⟨83848, by decide⟩ =
    .split (coordinate 13) (![⟨83784, by decide⟩,⟨83810, by decide⟩,⟨83827, by decide⟩,⟨83847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_23018_83848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23018 ⟨83848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 23018
    ⟨83848, by decide⟩ (by decide) (![⟨83784, by decide⟩,⟨83810, by decide⟩,⟨83827, by decide⟩,⟨83847, by decide⟩]) unmarked_context_13_23018_83848 node_context_13_23018_83848
  intro a
  fin_cases a
  · exact context_14_92072_83784
  · exact context_14_92073_83810
  · exact context_14_92074_83827
  · exact context_14_92075_83847

theorem selected_cut_02700 : selected 8 ⟨83897, by decide⟩
    (prefixPartial 13 23019) = some ⟨13, 2, 0, 83897, 23019, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_23019_83897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23019 ⟨83897, by decide⟩ :=
  accepted_of_selected 13 23019 ⟨83897, by decide⟩ ⟨13, 2, 0, 83897, 23019, 1945, 16384⟩
    (by decide) selected_cut_02700

theorem unmarked_context_12_5754_83898 : frontier 9 ⟨83898, by decide⟩
    (prefixCache 12 5754) (prefixPartial 12 5754) = false := by
  decide +kernel

theorem node_context_12_5754_83898 : EJMOriginalGlobalDAGData.nodes 9 ⟨83898, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83758, by decide⟩,⟨83848, by decide⟩,⟨83897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5754_83898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5754 ⟨83898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5754
    ⟨83898, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83758, by decide⟩,⟨83848, by decide⟩,⟨83897, by decide⟩]) unmarked_context_12_5754_83898 node_context_12_5754_83898
  intro a
  fin_cases a
  · exact context_13_23016_3444
  · exact context_13_23017_83758
  · exact context_13_23018_83848
  · exact context_13_23019_83897

theorem selected_cut_02701 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23020) = some ⟨13, 1, 0, 3444, 23020, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23020_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23020 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23020 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23020, 1, 16384⟩
    (by decide) selected_cut_02701

theorem selected_cut_02702 : selected 8 ⟨83905, by decide⟩
    (prefixPartial 13 23021) = some ⟨13, 2, 0, 83905, 23021, 381, 16384⟩ := by
  decide +kernel

theorem context_13_23021_83905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23021 ⟨83905, by decide⟩ :=
  accepted_of_selected 13 23021 ⟨83905, by decide⟩ ⟨13, 2, 0, 83905, 23021, 381, 16384⟩
    (by decide) selected_cut_02702

theorem selected_cut_02703 : selected 8 ⟨83942, by decide⟩
    (prefixPartial 13 23022) = some ⟨13, 2, 0, 83942, 23022, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_23022_83942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23022 ⟨83942, by decide⟩ :=
  accepted_of_selected 13 23022 ⟨83942, by decide⟩ ⟨13, 2, 0, 83942, 23022, 2817, 16384⟩
    (by decide) selected_cut_02703

theorem selected_cut_02704 : selected 8 ⟨83955, by decide⟩
    (prefixPartial 13 23023) = some ⟨13, 2, 0, 83955, 23023, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_23023_83955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23023 ⟨83955, by decide⟩ :=
  accepted_of_selected 13 23023 ⟨83955, by decide⟩ ⟨13, 2, 0, 83955, 23023, 1157, 16384⟩
    (by decide) selected_cut_02704

theorem unmarked_context_12_5755_83956 : frontier 9 ⟨83956, by decide⟩
    (prefixCache 12 5755) (prefixPartial 12 5755) = false := by
  decide +kernel

theorem node_context_12_5755_83956 : EJMOriginalGlobalDAGData.nodes 9 ⟨83956, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨83905, by decide⟩,⟨83942, by decide⟩,⟨83955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5755_83956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5755 ⟨83956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5755
    ⟨83956, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨83905, by decide⟩,⟨83942, by decide⟩,⟨83955, by decide⟩]) unmarked_context_12_5755_83956 node_context_12_5755_83956
  intro a
  fin_cases a
  · exact context_13_23020_3444
  · exact context_13_23021_83905
  · exact context_13_23022_83942
  · exact context_13_23023_83955

theorem unmarked_context_11_1438_83957 : frontier 10 ⟨83957, by decide⟩
    (prefixCache 11 1438) (prefixPartial 11 1438) = false := by
  decide +kernel

theorem node_context_11_1438_83957 : EJMOriginalGlobalDAGData.nodes 10 ⟨83957, by decide⟩ =
    .split (coordinate 11) (![⟨83685, by decide⟩,⟨83745, by decide⟩,⟨83898, by decide⟩,⟨83956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1438_83957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1438 ⟨83957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1438
    ⟨83957, by decide⟩ (by decide) (![⟨83685, by decide⟩,⟨83745, by decide⟩,⟨83898, by decide⟩,⟨83956, by decide⟩]) unmarked_context_11_1438_83957 node_context_11_1438_83957
  intro a
  fin_cases a
  · exact context_12_5752_83685
  · exact context_12_5753_83745
  · exact context_12_5754_83898
  · exact context_12_5755_83956

theorem selected_cut_02705 : selected 9 ⟨84007, by decide⟩
    (prefixPartial 12 5756) = some ⟨12, 2, 0, 84007, 5756, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_5756_84007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5756 ⟨84007, by decide⟩ :=
  accepted_of_selected 12 5756 ⟨84007, by decide⟩ ⟨12, 2, 0, 84007, 5756, 3881, 65536⟩
    (by decide) selected_cut_02705

theorem selected_cut_02706 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23028) = some ⟨13, 1, 0, 3444, 23028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23028, 1, 16384⟩
    (by decide) selected_cut_02706

theorem selected_cut_02707 : selected 8 ⟨84011, by decide⟩
    (prefixPartial 13 23029) = some ⟨13, 2, 0, 84011, 23029, 217, 16384⟩ := by
  decide +kernel

theorem context_13_23029_84011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23029 ⟨84011, by decide⟩ :=
  accepted_of_selected 13 23029 ⟨84011, by decide⟩ ⟨13, 2, 0, 84011, 23029, 217, 16384⟩
    (by decide) selected_cut_02707

theorem selected_cut_02708 : selected 8 ⟨84053, by decide⟩
    (prefixPartial 13 23030) = some ⟨13, 2, 0, 84053, 23030, 2921, 16384⟩ := by
  decide +kernel

theorem context_13_23030_84053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23030 ⟨84053, by decide⟩ :=
  accepted_of_selected 13 23030 ⟨84053, by decide⟩ ⟨13, 2, 0, 84053, 23030, 2921, 16384⟩
    (by decide) selected_cut_02708

theorem selected_cut_02709 : selected 8 ⟨84062, by decide⟩
    (prefixPartial 13 23031) = some ⟨13, 2, 0, 84062, 23031, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_23031_84062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23031 ⟨84062, by decide⟩ :=
  accepted_of_selected 13 23031 ⟨84062, by decide⟩ ⟨13, 2, 0, 84062, 23031, 1193, 16384⟩
    (by decide) selected_cut_02709

theorem unmarked_context_12_5757_84063 : frontier 9 ⟨84063, by decide⟩
    (prefixCache 12 5757) (prefixPartial 12 5757) = false := by
  decide +kernel

theorem node_context_12_5757_84063 : EJMOriginalGlobalDAGData.nodes 9 ⟨84063, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨84011, by decide⟩,⟨84053, by decide⟩,⟨84062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5757_84063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5757 ⟨84063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5757
    ⟨84063, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨84011, by decide⟩,⟨84053, by decide⟩,⟨84062, by decide⟩]) unmarked_context_12_5757_84063 node_context_12_5757_84063
  intro a
  fin_cases a
  · exact context_13_23028_3444
  · exact context_13_23029_84011
  · exact context_13_23030_84053
  · exact context_13_23031_84062

theorem selected_cut_02710 : selected 9 ⟨84112, by decide⟩
    (prefixPartial 12 5758) = some ⟨12, 2, 0, 84112, 5758, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_5758_84112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5758 ⟨84112, by decide⟩ :=
  accepted_of_selected 12 5758 ⟨84112, by decide⟩ ⟨12, 2, 0, 84112, 5758, 3921, 65536⟩
    (by decide) selected_cut_02710

theorem selected_cut_02711 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23036) = some ⟨13, 1, 0, 3444, 23036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23036, 1, 16384⟩
    (by decide) selected_cut_02711

theorem selected_cut_02712 : selected 8 ⟨84115, by decide⟩
    (prefixPartial 13 23037) = some ⟨13, 2, 0, 84115, 23037, 73, 16384⟩ := by
  decide +kernel

theorem context_13_23037_84115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23037 ⟨84115, by decide⟩ :=
  accepted_of_selected 13 23037 ⟨84115, by decide⟩ ⟨13, 2, 0, 84115, 23037, 73, 16384⟩
    (by decide) selected_cut_02712

theorem selected_cut_02713 : selected 8 ⟨84154, by decide⟩
    (prefixPartial 13 23038) = some ⟨13, 2, 0, 84154, 23038, 2829, 16384⟩ := by
  decide +kernel

theorem context_13_23038_84154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23038 ⟨84154, by decide⟩ :=
  accepted_of_selected 13 23038 ⟨84154, by decide⟩ ⟨13, 2, 0, 84154, 23038, 2829, 16384⟩
    (by decide) selected_cut_02713

theorem selected_cut_02714 : selected 8 ⟨84167, by decide⟩
    (prefixPartial 13 23039) = some ⟨13, 2, 0, 84167, 23039, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_23039_84167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23039 ⟨84167, by decide⟩ :=
  accepted_of_selected 13 23039 ⟨84167, by decide⟩ ⟨13, 2, 0, 84167, 23039, 1241, 16384⟩
    (by decide) selected_cut_02714

theorem unmarked_context_12_5759_84168 : frontier 9 ⟨84168, by decide⟩
    (prefixCache 12 5759) (prefixPartial 12 5759) = false := by
  decide +kernel

theorem node_context_12_5759_84168 : EJMOriginalGlobalDAGData.nodes 9 ⟨84168, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨84115, by decide⟩,⟨84154, by decide⟩,⟨84167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5759_84168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5759 ⟨84168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5759
    ⟨84168, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨84115, by decide⟩,⟨84154, by decide⟩,⟨84167, by decide⟩]) unmarked_context_12_5759_84168 node_context_12_5759_84168
  intro a
  fin_cases a
  · exact context_13_23036_3444
  · exact context_13_23037_84115
  · exact context_13_23038_84154
  · exact context_13_23039_84167

theorem unmarked_context_11_1439_84169 : frontier 10 ⟨84169, by decide⟩
    (prefixCache 11 1439) (prefixPartial 11 1439) = false := by
  decide +kernel

theorem node_context_11_1439_84169 : EJMOriginalGlobalDAGData.nodes 10 ⟨84169, by decide⟩ =
    .split (coordinate 11) (![⟨84007, by decide⟩,⟨84063, by decide⟩,⟨84112, by decide⟩,⟨84168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1439_84169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1439 ⟨84169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1439
    ⟨84169, by decide⟩ (by decide) (![⟨84007, by decide⟩,⟨84063, by decide⟩,⟨84112, by decide⟩,⟨84168, by decide⟩]) unmarked_context_11_1439_84169 node_context_11_1439_84169
  intro a
  fin_cases a
  · exact context_12_5756_84007
  · exact context_12_5757_84063
  · exact context_12_5758_84112
  · exact context_12_5759_84168

theorem unmarked_context_10_359_84170 : frontier 11 ⟨84170, by decide⟩
    (prefixCache 10 359) (prefixPartial 10 359) = false := by
  decide +kernel

theorem node_context_10_359_84170 : EJMOriginalGlobalDAGData.nodes 11 ⟨84170, by decide⟩ =
    .split (coordinate 10) (![⟨83389, by decide⟩,⟨83642, by decide⟩,⟨83957, by decide⟩,⟨84169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_359_84170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 359 ⟨84170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 359
    ⟨84170, by decide⟩ (by decide) (![⟨83389, by decide⟩,⟨83642, by decide⟩,⟨83957, by decide⟩,⟨84169, by decide⟩]) unmarked_context_10_359_84170 node_context_10_359_84170
  intro a
  fin_cases a
  · exact context_11_1436_83389
  · exact context_11_1437_83642
  · exact context_11_1438_83957
  · exact context_11_1439_84169

theorem unmarked_context_9_89_84171 : frontier 12 ⟨84171, by decide⟩
    (prefixCache 9 89) (prefixPartial 9 89) = false := by
  decide +kernel

theorem node_context_9_89_84171 : EJMOriginalGlobalDAGData.nodes 12 ⟨84171, by decide⟩ =
    .split (coordinate 9) (![⟨80677, by decide⟩,⟨82054, by decide⟩,⟨83128, by decide⟩,⟨84170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_89_84171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 89 ⟨84171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 89
    ⟨84171, by decide⟩ (by decide) (![⟨80677, by decide⟩,⟨82054, by decide⟩,⟨83128, by decide⟩,⟨84170, by decide⟩]) unmarked_context_9_89_84171 node_context_9_89_84171
  intro a
  fin_cases a
  · exact context_10_356_80677
  · exact context_10_357_82054
  · exact context_10_358_83128
  · exact context_10_359_84170

theorem selected_cut_02715 : selected 9 ⟨84207, by decide⟩
    (prefixPartial 12 5760) = some ⟨12, 2, 0, 84207, 5760, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_5760_84207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5760 ⟨84207, by decide⟩ :=
  accepted_of_selected 12 5760 ⟨84207, by decide⟩ ⟨12, 2, 0, 84207, 5760, 2697, 65536⟩
    (by decide) selected_cut_02715

theorem selected_cut_02716 : selected 9 ⟨84238, by decide⟩
    (prefixPartial 12 5761) = some ⟨12, 2, 0, 84238, 5761, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_5761_84238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5761 ⟨84238, by decide⟩ :=
  accepted_of_selected 12 5761 ⟨84238, by decide⟩ ⟨12, 2, 0, 84238, 5761, 2933, 65536⟩
    (by decide) selected_cut_02716

theorem selected_cut_02717 : selected 9 ⟨84269, by decide⟩
    (prefixPartial 12 5762) = some ⟨12, 2, 0, 84269, 5762, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_5762_84269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5762 ⟨84269, by decide⟩ :=
  accepted_of_selected 12 5762 ⟨84269, by decide⟩ ⟨12, 2, 0, 84269, 5762, 2713, 65536⟩
    (by decide) selected_cut_02717

theorem selected_cut_02718 : selected 9 ⟨84303, by decide⟩
    (prefixPartial 12 5763) = some ⟨12, 2, 0, 84303, 5763, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_5763_84303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5763 ⟨84303, by decide⟩ :=
  accepted_of_selected 12 5763 ⟨84303, by decide⟩ ⟨12, 2, 0, 84303, 5763, 2893, 65536⟩
    (by decide) selected_cut_02718

theorem unmarked_context_11_1440_84304 : frontier 10 ⟨84304, by decide⟩
    (prefixCache 11 1440) (prefixPartial 11 1440) = false := by
  decide +kernel

theorem node_context_11_1440_84304 : EJMOriginalGlobalDAGData.nodes 10 ⟨84304, by decide⟩ =
    .split (coordinate 11) (![⟨84207, by decide⟩,⟨84238, by decide⟩,⟨84269, by decide⟩,⟨84303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1440_84304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1440 ⟨84304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1440
    ⟨84304, by decide⟩ (by decide) (![⟨84207, by decide⟩,⟨84238, by decide⟩,⟨84269, by decide⟩,⟨84303, by decide⟩]) unmarked_context_11_1440_84304 node_context_11_1440_84304
  intro a
  fin_cases a
  · exact context_12_5760_84207
  · exact context_12_5761_84238
  · exact context_12_5762_84269
  · exact context_12_5763_84303

theorem selected_cut_02719 : selected 9 ⟨84331, by decide⟩
    (prefixPartial 12 5764) = some ⟨12, 2, 0, 84331, 5764, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_5764_84331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5764 ⟨84331, by decide⟩ :=
  accepted_of_selected 12 5764 ⟨84331, by decide⟩ ⟨12, 2, 0, 84331, 5764, 2693, 65536⟩
    (by decide) selected_cut_02719

theorem selected_cut_02720 : selected 9 ⟨84363, by decide⟩
    (prefixPartial 12 5765) = some ⟨12, 2, 0, 84363, 5765, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_5765_84363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5765 ⟨84363, by decide⟩ :=
  accepted_of_selected 12 5765 ⟨84363, by decide⟩ ⟨12, 2, 0, 84363, 5765, 2925, 65536⟩
    (by decide) selected_cut_02720

theorem selected_cut_02721 : selected 9 ⟨84401, by decide⟩
    (prefixPartial 12 5766) = some ⟨12, 2, 0, 84401, 5766, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_5766_84401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5766 ⟨84401, by decide⟩ :=
  accepted_of_selected 12 5766 ⟨84401, by decide⟩ ⟨12, 2, 0, 84401, 5766, 2713, 65536⟩
    (by decide) selected_cut_02721

theorem selected_cut_02722 : selected 9 ⟨84433, by decide⟩
    (prefixPartial 12 5767) = some ⟨12, 2, 0, 84433, 5767, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_5767_84433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5767 ⟨84433, by decide⟩ :=
  accepted_of_selected 12 5767 ⟨84433, by decide⟩ ⟨12, 2, 0, 84433, 5767, 2929, 65536⟩
    (by decide) selected_cut_02722

theorem unmarked_context_11_1441_84434 : frontier 10 ⟨84434, by decide⟩
    (prefixCache 11 1441) (prefixPartial 11 1441) = false := by
  decide +kernel

theorem node_context_11_1441_84434 : EJMOriginalGlobalDAGData.nodes 10 ⟨84434, by decide⟩ =
    .split (coordinate 11) (![⟨84331, by decide⟩,⟨84363, by decide⟩,⟨84401, by decide⟩,⟨84433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1441_84434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1441 ⟨84434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1441
    ⟨84434, by decide⟩ (by decide) (![⟨84331, by decide⟩,⟨84363, by decide⟩,⟨84401, by decide⟩,⟨84433, by decide⟩]) unmarked_context_11_1441_84434 node_context_11_1441_84434
  intro a
  fin_cases a
  · exact context_12_5764_84331
  · exact context_12_5765_84363
  · exact context_12_5766_84401
  · exact context_12_5767_84433

theorem selected_cut_02723 : selected 9 ⟨84461, by decide⟩
    (prefixPartial 12 5768) = some ⟨12, 2, 0, 84461, 5768, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_5768_84461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5768 ⟨84461, by decide⟩ :=
  accepted_of_selected 12 5768 ⟨84461, by decide⟩ ⟨12, 2, 0, 84461, 5768, 2577, 65536⟩
    (by decide) selected_cut_02723

theorem selected_cut_02724 : selected 9 ⟨84494, by decide⟩
    (prefixPartial 12 5769) = some ⟨12, 2, 0, 84494, 5769, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_5769_84494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5769 ⟨84494, by decide⟩ :=
  accepted_of_selected 12 5769 ⟨84494, by decide⟩ ⟨12, 2, 0, 84494, 5769, 2901, 65536⟩
    (by decide) selected_cut_02724

theorem selected_cut_02725 : selected 9 ⟨84557, by decide⟩
    (prefixPartial 12 5770) = some ⟨12, 2, 0, 84557, 5770, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_5770_84557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5770 ⟨84557, by decide⟩ :=
  accepted_of_selected 12 5770 ⟨84557, by decide⟩ ⟨12, 2, 0, 84557, 5770, 3885, 65536⟩
    (by decide) selected_cut_02725

theorem selected_cut_02726 : selected 9 ⟨84590, by decide⟩
    (prefixPartial 12 5771) = some ⟨12, 2, 0, 84590, 5771, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_5771_84590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5771 ⟨84590, by decide⟩ :=
  accepted_of_selected 12 5771 ⟨84590, by decide⟩ ⟨12, 2, 0, 84590, 5771, 2761, 65536⟩
    (by decide) selected_cut_02726

theorem unmarked_context_11_1442_84591 : frontier 10 ⟨84591, by decide⟩
    (prefixCache 11 1442) (prefixPartial 11 1442) = false := by
  decide +kernel

theorem node_context_11_1442_84591 : EJMOriginalGlobalDAGData.nodes 10 ⟨84591, by decide⟩ =
    .split (coordinate 11) (![⟨84461, by decide⟩,⟨84494, by decide⟩,⟨84557, by decide⟩,⟨84590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1442_84591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1442 ⟨84591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1442
    ⟨84591, by decide⟩ (by decide) (![⟨84461, by decide⟩,⟨84494, by decide⟩,⟨84557, by decide⟩,⟨84590, by decide⟩]) unmarked_context_11_1442_84591 node_context_11_1442_84591
  intro a
  fin_cases a
  · exact context_12_5768_84461
  · exact context_12_5769_84494
  · exact context_12_5770_84557
  · exact context_12_5771_84590

theorem selected_cut_02727 : selected 9 ⟨84620, by decide⟩
    (prefixPartial 12 5772) = some ⟨12, 2, 0, 84620, 5772, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_5772_84620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5772 ⟨84620, by decide⟩ :=
  accepted_of_selected 12 5772 ⟨84620, by decide⟩ ⟨12, 2, 0, 84620, 5772, 2761, 65536⟩
    (by decide) selected_cut_02727

theorem selected_cut_02728 : selected 9 ⟨84652, by decide⟩
    (prefixPartial 12 5773) = some ⟨12, 2, 0, 84652, 5773, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_5773_84652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5773 ⟨84652, by decide⟩ :=
  accepted_of_selected 12 5773 ⟨84652, by decide⟩ ⟨12, 2, 0, 84652, 5773, 2949, 65536⟩
    (by decide) selected_cut_02728

theorem selected_cut_02729 : selected 9 ⟨84681, by decide⟩
    (prefixPartial 12 5774) = some ⟨12, 2, 0, 84681, 5774, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_5774_84681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5774 ⟨84681, by decide⟩ :=
  accepted_of_selected 12 5774 ⟨84681, by decide⟩ ⟨12, 2, 0, 84681, 5774, 2625, 65536⟩
    (by decide) selected_cut_02729

theorem selected_cut_02730 : selected 9 ⟨84708, by decide⟩
    (prefixPartial 12 5775) = some ⟨12, 2, 0, 84708, 5775, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_5775_84708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5775 ⟨84708, by decide⟩ :=
  accepted_of_selected 12 5775 ⟨84708, by decide⟩ ⟨12, 2, 0, 84708, 5775, 2813, 65536⟩
    (by decide) selected_cut_02730

theorem unmarked_context_11_1443_84709 : frontier 10 ⟨84709, by decide⟩
    (prefixCache 11 1443) (prefixPartial 11 1443) = false := by
  decide +kernel

theorem node_context_11_1443_84709 : EJMOriginalGlobalDAGData.nodes 10 ⟨84709, by decide⟩ =
    .split (coordinate 11) (![⟨84620, by decide⟩,⟨84652, by decide⟩,⟨84681, by decide⟩,⟨84708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1443_84709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1443 ⟨84709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1443
    ⟨84709, by decide⟩ (by decide) (![⟨84620, by decide⟩,⟨84652, by decide⟩,⟨84681, by decide⟩,⟨84708, by decide⟩]) unmarked_context_11_1443_84709 node_context_11_1443_84709
  intro a
  fin_cases a
  · exact context_12_5772_84620
  · exact context_12_5773_84652
  · exact context_12_5774_84681
  · exact context_12_5775_84708

theorem unmarked_context_10_360_84710 : frontier 11 ⟨84710, by decide⟩
    (prefixCache 10 360) (prefixPartial 10 360) = false := by
  decide +kernel

theorem node_context_10_360_84710 : EJMOriginalGlobalDAGData.nodes 11 ⟨84710, by decide⟩ =
    .split (coordinate 10) (![⟨84304, by decide⟩,⟨84434, by decide⟩,⟨84591, by decide⟩,⟨84709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_360_84710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 360 ⟨84710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 360
    ⟨84710, by decide⟩ (by decide) (![⟨84304, by decide⟩,⟨84434, by decide⟩,⟨84591, by decide⟩,⟨84709, by decide⟩]) unmarked_context_10_360_84710 node_context_10_360_84710
  intro a
  fin_cases a
  · exact context_11_1440_84304
  · exact context_11_1441_84434
  · exact context_11_1442_84591
  · exact context_11_1443_84709

theorem selected_cut_02731 : selected 9 ⟨84743, by decide⟩
    (prefixPartial 12 5776) = some ⟨12, 2, 0, 84743, 5776, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_5776_84743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5776 ⟨84743, by decide⟩ :=
  accepted_of_selected 12 5776 ⟨84743, by decide⟩ ⟨12, 2, 0, 84743, 5776, 2761, 65536⟩
    (by decide) selected_cut_02731

theorem selected_cut_02732 : selected 9 ⟨84781, by decide⟩
    (prefixPartial 12 5777) = some ⟨12, 2, 0, 84781, 5777, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_5777_84781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5777 ⟨84781, by decide⟩ :=
  accepted_of_selected 12 5777 ⟨84781, by decide⟩ ⟨12, 2, 0, 84781, 5777, 2981, 65536⟩
    (by decide) selected_cut_02732

theorem selected_cut_02733 : selected 9 ⟨84810, by decide⟩
    (prefixPartial 12 5778) = some ⟨12, 2, 0, 84810, 5778, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_5778_84810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5778 ⟨84810, by decide⟩ :=
  accepted_of_selected 12 5778 ⟨84810, by decide⟩ ⟨12, 2, 0, 84810, 5778, 2729, 65536⟩
    (by decide) selected_cut_02733

theorem selected_cut_02734 : selected 9 ⟨84843, by decide⟩
    (prefixPartial 12 5779) = some ⟨12, 2, 0, 84843, 5779, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_5779_84843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5779 ⟨84843, by decide⟩ :=
  accepted_of_selected 12 5779 ⟨84843, by decide⟩ ⟨12, 2, 0, 84843, 5779, 3021, 65536⟩
    (by decide) selected_cut_02734

theorem unmarked_context_11_1444_84844 : frontier 10 ⟨84844, by decide⟩
    (prefixCache 11 1444) (prefixPartial 11 1444) = false := by
  decide +kernel

theorem node_context_11_1444_84844 : EJMOriginalGlobalDAGData.nodes 10 ⟨84844, by decide⟩ =
    .split (coordinate 11) (![⟨84743, by decide⟩,⟨84781, by decide⟩,⟨84810, by decide⟩,⟨84843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1444_84844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1444 ⟨84844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1444
    ⟨84844, by decide⟩ (by decide) (![⟨84743, by decide⟩,⟨84781, by decide⟩,⟨84810, by decide⟩,⟨84843, by decide⟩]) unmarked_context_11_1444_84844 node_context_11_1444_84844
  intro a
  fin_cases a
  · exact context_12_5776_84743
  · exact context_12_5777_84781
  · exact context_12_5778_84810
  · exact context_12_5779_84843

theorem selected_cut_02735 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23120) = some ⟨13, 1, 0, 3444, 23120, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23120_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23120 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23120 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23120, 1, 16384⟩
    (by decide) selected_cut_02735

theorem selected_cut_02736 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23121) = some ⟨13, 1, 0, 3444, 23121, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23121_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23121 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23121 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23121, 1, 16384⟩
    (by decide) selected_cut_02736

theorem selected_cut_02737 : selected 8 ⟨84883, by decide⟩
    (prefixPartial 13 23122) = some ⟨13, 2, 0, 84883, 23122, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_23122_84883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23122 ⟨84883, by decide⟩ :=
  accepted_of_selected 13 23122 ⟨84883, by decide⟩ ⟨13, 2, 0, 84883, 23122, 2357, 16384⟩
    (by decide) selected_cut_02737

theorem selected_cut_02738 : selected 8 ⟨84918, by decide⟩
    (prefixPartial 13 23123) = some ⟨13, 2, 0, 84918, 23123, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_23123_84918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23123 ⟨84918, by decide⟩ :=
  accepted_of_selected 13 23123 ⟨84918, by decide⟩ ⟨13, 2, 0, 84918, 23123, 1841, 16384⟩
    (by decide) selected_cut_02738

theorem unmarked_context_12_5780_84919 : frontier 9 ⟨84919, by decide⟩
    (prefixCache 12 5780) (prefixPartial 12 5780) = false := by
  decide +kernel

theorem node_context_12_5780_84919 : EJMOriginalGlobalDAGData.nodes 9 ⟨84919, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨84883, by decide⟩,⟨84918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5780_84919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5780 ⟨84919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5780
    ⟨84919, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨84883, by decide⟩,⟨84918, by decide⟩]) unmarked_context_12_5780_84919 node_context_12_5780_84919
  intro a
  fin_cases a
  · exact context_13_23120_3444
  · exact context_13_23121_3444
  · exact context_13_23122_84883
  · exact context_13_23123_84918

theorem selected_cut_02739 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23124) = some ⟨13, 1, 0, 3444, 23124, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23124_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23124 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23124 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23124, 1, 16384⟩
    (by decide) selected_cut_02739

theorem selected_cut_02740 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23125) = some ⟨13, 1, 0, 3444, 23125, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23125_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23125 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23125 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23125, 1, 16384⟩
    (by decide) selected_cut_02740

theorem selected_cut_02741 : selected 8 ⟨84966, by decide⟩
    (prefixPartial 13 23126) = some ⟨13, 2, 0, 84966, 23126, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_23126_84966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23126 ⟨84966, by decide⟩ :=
  accepted_of_selected 13 23126 ⟨84966, by decide⟩ ⟨13, 2, 0, 84966, 23126, 2389, 16384⟩
    (by decide) selected_cut_02741

theorem selected_cut_02742 : selected 8 ⟨84998, by decide⟩
    (prefixPartial 13 23127) = some ⟨13, 2, 0, 84998, 23127, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_23127_84998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23127 ⟨84998, by decide⟩ :=
  accepted_of_selected 13 23127 ⟨84998, by decide⟩ ⟨13, 2, 0, 84998, 23127, 1765, 16384⟩
    (by decide) selected_cut_02742

theorem unmarked_context_12_5781_84999 : frontier 9 ⟨84999, by decide⟩
    (prefixCache 12 5781) (prefixPartial 12 5781) = false := by
  decide +kernel

theorem node_context_12_5781_84999 : EJMOriginalGlobalDAGData.nodes 9 ⟨84999, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨84966, by decide⟩,⟨84998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5781_84999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5781 ⟨84999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5781
    ⟨84999, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨84966, by decide⟩,⟨84998, by decide⟩]) unmarked_context_12_5781_84999 node_context_12_5781_84999
  intro a
  fin_cases a
  · exact context_13_23124_3444
  · exact context_13_23125_3444
  · exact context_13_23126_84966
  · exact context_13_23127_84998

theorem selected_cut_02743 : selected 9 ⟨85060, by decide⟩
    (prefixPartial 12 5782) = some ⟨12, 2, 0, 85060, 5782, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_5782_85060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5782 ⟨85060, by decide⟩ :=
  accepted_of_selected 12 5782 ⟨85060, by decide⟩ ⟨12, 2, 0, 85060, 5782, 3869, 65536⟩
    (by decide) selected_cut_02743

theorem selected_cut_02744 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23132) = some ⟨13, 1, 0, 3444, 23132, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23132_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23132 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23132 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23132, 1, 16384⟩
    (by decide) selected_cut_02744

theorem selected_cut_02745 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 23133) = some ⟨13, 1, 0, 3444, 23133, 1, 16384⟩ := by
  decide +kernel

theorem context_13_23133_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23133 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 23133 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 23133, 1, 16384⟩
    (by decide) selected_cut_02745

theorem selected_cut_02746 : selected 8 ⟨85102, by decide⟩
    (prefixPartial 13 23134) = some ⟨13, 2, 0, 85102, 23134, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_23134_85102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23134 ⟨85102, by decide⟩ :=
  accepted_of_selected 13 23134 ⟨85102, by decide⟩ ⟨13, 2, 0, 85102, 23134, 2405, 16384⟩
    (by decide) selected_cut_02746

theorem selected_cut_02747 : selected 8 ⟨85138, by decide⟩
    (prefixPartial 13 23135) = some ⟨13, 2, 0, 85138, 23135, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_23135_85138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 23135 ⟨85138, by decide⟩ :=
  accepted_of_selected 13 23135 ⟨85138, by decide⟩ ⟨13, 2, 0, 85138, 23135, 1933, 16384⟩
    (by decide) selected_cut_02747

theorem unmarked_context_12_5783_85139 : frontier 9 ⟨85139, by decide⟩
    (prefixCache 12 5783) (prefixPartial 12 5783) = false := by
  decide +kernel

theorem node_context_12_5783_85139 : EJMOriginalGlobalDAGData.nodes 9 ⟨85139, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨85102, by decide⟩,⟨85138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5783_85139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5783 ⟨85139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5783
    ⟨85139, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨85102, by decide⟩,⟨85138, by decide⟩]) unmarked_context_12_5783_85139 node_context_12_5783_85139
  intro a
  fin_cases a
  · exact context_13_23132_3444
  · exact context_13_23133_3444
  · exact context_13_23134_85102
  · exact context_13_23135_85138

theorem unmarked_context_11_1445_85140 : frontier 10 ⟨85140, by decide⟩
    (prefixCache 11 1445) (prefixPartial 11 1445) = false := by
  decide +kernel

theorem node_context_11_1445_85140 : EJMOriginalGlobalDAGData.nodes 10 ⟨85140, by decide⟩ =
    .split (coordinate 11) (![⟨84919, by decide⟩,⟨84999, by decide⟩,⟨85060, by decide⟩,⟨85139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1445_85140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1445 ⟨85140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1445
    ⟨85140, by decide⟩ (by decide) (![⟨84919, by decide⟩,⟨84999, by decide⟩,⟨85060, by decide⟩,⟨85139, by decide⟩]) unmarked_context_11_1445_85140 node_context_11_1445_85140
  intro a
  fin_cases a
  · exact context_12_5780_84919
  · exact context_12_5781_84999
  · exact context_12_5782_85060
  · exact context_12_5783_85139

theorem selected_cut_02748 : selected 9 ⟨85169, by decide⟩
    (prefixPartial 12 5784) = some ⟨12, 2, 0, 85169, 5784, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_5784_85169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5784 ⟨85169, by decide⟩ :=
  accepted_of_selected 12 5784 ⟨85169, by decide⟩ ⟨12, 2, 0, 85169, 5784, 2633, 65536⟩
    (by decide) selected_cut_02748

theorem selected_cut_02749 : selected 9 ⟨85199, by decide⟩
    (prefixPartial 12 5785) = some ⟨12, 2, 0, 85199, 5785, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_5785_85199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5785 ⟨85199, by decide⟩ :=
  accepted_of_selected 12 5785 ⟨85199, by decide⟩ ⟨12, 2, 0, 85199, 5785, 2905, 65536⟩
    (by decide) selected_cut_02749

theorem selected_cut_02750 : selected 9 ⟨85255, by decide⟩
    (prefixPartial 12 5786) = some ⟨12, 2, 0, 85255, 5786, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_5786_85255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5786 ⟨85255, by decide⟩ :=
  accepted_of_selected 12 5786 ⟨85255, by decide⟩ ⟨12, 2, 0, 85255, 5786, 3829, 65536⟩
    (by decide) selected_cut_02750

theorem selected_cut_02751 : selected 9 ⟨85285, by decide⟩
    (prefixPartial 12 5787) = some ⟨12, 2, 0, 85285, 5787, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_5787_85285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5787 ⟨85285, by decide⟩ :=
  accepted_of_selected 12 5787 ⟨85285, by decide⟩ ⟨12, 2, 0, 85285, 5787, 2749, 65536⟩
    (by decide) selected_cut_02751

theorem unmarked_context_11_1446_85286 : frontier 10 ⟨85286, by decide⟩
    (prefixCache 11 1446) (prefixPartial 11 1446) = false := by
  decide +kernel

theorem node_context_11_1446_85286 : EJMOriginalGlobalDAGData.nodes 10 ⟨85286, by decide⟩ =
    .split (coordinate 11) (![⟨85169, by decide⟩,⟨85199, by decide⟩,⟨85255, by decide⟩,⟨85285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1446_85286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1446 ⟨85286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1446
    ⟨85286, by decide⟩ (by decide) (![⟨85169, by decide⟩,⟨85199, by decide⟩,⟨85255, by decide⟩,⟨85285, by decide⟩]) unmarked_context_11_1446_85286 node_context_11_1446_85286
  intro a
  fin_cases a
  · exact context_12_5784_85169
  · exact context_12_5785_85199
  · exact context_12_5786_85255
  · exact context_12_5787_85285

theorem selected_cut_02752 : selected 9 ⟨85316, by decide⟩
    (prefixPartial 12 5788) = some ⟨12, 2, 0, 85316, 5788, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_5788_85316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5788 ⟨85316, by decide⟩ :=
  accepted_of_selected 12 5788 ⟨85316, by decide⟩ ⟨12, 2, 0, 85316, 5788, 2537, 65536⟩
    (by decide) selected_cut_02752

theorem selected_cut_02753 : selected 9 ⟨85343, by decide⟩
    (prefixPartial 12 5789) = some ⟨12, 2, 0, 85343, 5789, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_5789_85343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5789 ⟨85343, by decide⟩ :=
  accepted_of_selected 12 5789 ⟨85343, by decide⟩ ⟨12, 2, 0, 85343, 5789, 2621, 65536⟩
    (by decide) selected_cut_02753

theorem selected_cut_02754 : selected 9 ⟨85365, by decide⟩
    (prefixPartial 12 5790) = some ⟨12, 2, 0, 85365, 5790, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_5790_85365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5790 ⟨85365, by decide⟩ :=
  accepted_of_selected 12 5790 ⟨85365, by decide⟩ ⟨12, 2, 0, 85365, 5790, 2321, 65536⟩
    (by decide) selected_cut_02754

theorem selected_cut_02755 : selected 9 ⟨85387, by decide⟩
    (prefixPartial 12 5791) = some ⟨12, 2, 0, 85387, 5791, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_5791_85387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5791 ⟨85387, by decide⟩ :=
  accepted_of_selected 12 5791 ⟨85387, by decide⟩ ⟨12, 2, 0, 85387, 5791, 2521, 65536⟩
    (by decide) selected_cut_02755

theorem unmarked_context_11_1447_85388 : frontier 10 ⟨85388, by decide⟩
    (prefixCache 11 1447) (prefixPartial 11 1447) = false := by
  decide +kernel

theorem node_context_11_1447_85388 : EJMOriginalGlobalDAGData.nodes 10 ⟨85388, by decide⟩ =
    .split (coordinate 11) (![⟨85316, by decide⟩,⟨85343, by decide⟩,⟨85365, by decide⟩,⟨85387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1447_85388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1447 ⟨85388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1447
    ⟨85388, by decide⟩ (by decide) (![⟨85316, by decide⟩,⟨85343, by decide⟩,⟨85365, by decide⟩,⟨85387, by decide⟩]) unmarked_context_11_1447_85388 node_context_11_1447_85388
  intro a
  fin_cases a
  · exact context_12_5788_85316
  · exact context_12_5789_85343
  · exact context_12_5790_85365
  · exact context_12_5791_85387

theorem unmarked_context_10_361_85389 : frontier 11 ⟨85389, by decide⟩
    (prefixCache 10 361) (prefixPartial 10 361) = false := by
  decide +kernel

theorem node_context_10_361_85389 : EJMOriginalGlobalDAGData.nodes 11 ⟨85389, by decide⟩ =
    .split (coordinate 10) (![⟨84844, by decide⟩,⟨85140, by decide⟩,⟨85286, by decide⟩,⟨85388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_361_85389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 361 ⟨85389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 361
    ⟨85389, by decide⟩ (by decide) (![⟨84844, by decide⟩,⟨85140, by decide⟩,⟨85286, by decide⟩,⟨85388, by decide⟩]) unmarked_context_10_361_85389 node_context_10_361_85389
  intro a
  fin_cases a
  · exact context_11_1444_84844
  · exact context_11_1445_85140
  · exact context_11_1446_85286
  · exact context_11_1447_85388

theorem selected_cut_02756 : selected 9 ⟨85411, by decide⟩
    (prefixPartial 12 5792) = some ⟨12, 2, 0, 85411, 5792, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_5792_85411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5792 ⟨85411, by decide⟩ :=
  accepted_of_selected 12 5792 ⟨85411, by decide⟩ ⟨12, 2, 0, 85411, 5792, 1989, 65536⟩
    (by decide) selected_cut_02756

theorem selected_cut_02757 : selected 9 ⟨85438, by decide⟩
    (prefixPartial 12 5793) = some ⟨12, 2, 0, 85438, 5793, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_5793_85438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5793 ⟨85438, by decide⟩ :=
  accepted_of_selected 12 5793 ⟨85438, by decide⟩ ⟨12, 2, 0, 85438, 5793, 2273, 65536⟩
    (by decide) selected_cut_02757

theorem selected_cut_02758 : selected 9 ⟨85459, by decide⟩
    (prefixPartial 12 5794) = some ⟨12, 2, 0, 85459, 5794, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_5794_85459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5794 ⟨85459, by decide⟩ :=
  accepted_of_selected 12 5794 ⟨85459, by decide⟩ ⟨12, 2, 0, 85459, 5794, 2013, 65536⟩
    (by decide) selected_cut_02758

theorem selected_cut_02759 : selected 9 ⟨85483, by decide⟩
    (prefixPartial 12 5795) = some ⟨12, 2, 0, 85483, 5795, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_5795_85483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5795 ⟨85483, by decide⟩ :=
  accepted_of_selected 12 5795 ⟨85483, by decide⟩ ⟨12, 2, 0, 85483, 5795, 2197, 65536⟩
    (by decide) selected_cut_02759

theorem unmarked_context_11_1448_85484 : frontier 10 ⟨85484, by decide⟩
    (prefixCache 11 1448) (prefixPartial 11 1448) = false := by
  decide +kernel

theorem node_context_11_1448_85484 : EJMOriginalGlobalDAGData.nodes 10 ⟨85484, by decide⟩ =
    .split (coordinate 11) (![⟨85411, by decide⟩,⟨85438, by decide⟩,⟨85459, by decide⟩,⟨85483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1448_85484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1448 ⟨85484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1448
    ⟨85484, by decide⟩ (by decide) (![⟨85411, by decide⟩,⟨85438, by decide⟩,⟨85459, by decide⟩,⟨85483, by decide⟩]) unmarked_context_11_1448_85484 node_context_11_1448_85484
  intro a
  fin_cases a
  · exact context_12_5792_85411
  · exact context_12_5793_85438
  · exact context_12_5794_85459
  · exact context_12_5795_85483

theorem selected_cut_02760 : selected 9 ⟨85508, by decide⟩
    (prefixPartial 12 5796) = some ⟨12, 2, 0, 85508, 5796, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_5796_85508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5796 ⟨85508, by decide⟩ :=
  accepted_of_selected 12 5796 ⟨85508, by decide⟩ ⟨12, 2, 0, 85508, 5796, 1945, 65536⟩
    (by decide) selected_cut_02760

theorem selected_cut_02761 : selected 9 ⟨85529, by decide⟩
    (prefixPartial 12 5797) = some ⟨12, 2, 0, 85529, 5797, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_5797_85529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5797 ⟨85529, by decide⟩ :=
  accepted_of_selected 12 5797 ⟨85529, by decide⟩ ⟨12, 2, 0, 85529, 5797, 2209, 65536⟩
    (by decide) selected_cut_02761

theorem selected_cut_02762 : selected 9 ⟨85546, by decide⟩
    (prefixPartial 12 5798) = some ⟨12, 2, 0, 85546, 5798, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_5798_85546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5798 ⟨85546, by decide⟩ :=
  accepted_of_selected 12 5798 ⟨85546, by decide⟩ ⟨12, 2, 0, 85546, 5798, 2037, 65536⟩
    (by decide) selected_cut_02762

theorem selected_cut_02763 : selected 9 ⟨85570, by decide⟩
    (prefixPartial 12 5799) = some ⟨12, 2, 0, 85570, 5799, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_5799_85570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5799 ⟨85570, by decide⟩ :=
  accepted_of_selected 12 5799 ⟨85570, by decide⟩ ⟨12, 2, 0, 85570, 5799, 2161, 65536⟩
    (by decide) selected_cut_02763

theorem unmarked_context_11_1449_85571 : frontier 10 ⟨85571, by decide⟩
    (prefixCache 11 1449) (prefixPartial 11 1449) = false := by
  decide +kernel

theorem node_context_11_1449_85571 : EJMOriginalGlobalDAGData.nodes 10 ⟨85571, by decide⟩ =
    .split (coordinate 11) (![⟨85508, by decide⟩,⟨85529, by decide⟩,⟨85546, by decide⟩,⟨85570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1449_85571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1449 ⟨85571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1449
    ⟨85571, by decide⟩ (by decide) (![⟨85508, by decide⟩,⟨85529, by decide⟩,⟨85546, by decide⟩,⟨85570, by decide⟩]) unmarked_context_11_1449_85571 node_context_11_1449_85571
  intro a
  fin_cases a
  · exact context_12_5796_85508
  · exact context_12_5797_85529
  · exact context_12_5798_85546
  · exact context_12_5799_85570

theorem selected_cut_02764 : selected 9 ⟨85589, by decide⟩
    (prefixPartial 12 5800) = some ⟨12, 2, 0, 85589, 5800, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_5800_85589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5800 ⟨85589, by decide⟩ :=
  accepted_of_selected 12 5800 ⟨85589, by decide⟩ ⟨12, 2, 0, 85589, 5800, 1805, 65536⟩
    (by decide) selected_cut_02764

theorem selected_cut_02765 : selected 9 ⟨85610, by decide⟩
    (prefixPartial 12 5801) = some ⟨12, 2, 0, 85610, 5801, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_5801_85610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5801 ⟨85610, by decide⟩ :=
  accepted_of_selected 12 5801 ⟨85610, by decide⟩ ⟨12, 2, 0, 85610, 5801, 2085, 65536⟩
    (by decide) selected_cut_02765

theorem selected_cut_02766 : selected 9 ⟨85659, by decide⟩
    (prefixPartial 12 5802) = some ⟨12, 2, 0, 85659, 5802, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_5802_85659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5802 ⟨85659, by decide⟩ :=
  accepted_of_selected 12 5802 ⟨85659, by decide⟩ ⟨12, 2, 0, 85659, 5802, 2585, 65536⟩
    (by decide) selected_cut_02766

theorem selected_cut_02767 : selected 9 ⟨85678, by decide⟩
    (prefixPartial 12 5803) = some ⟨12, 2, 0, 85678, 5803, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_5803_85678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5803 ⟨85678, by decide⟩ :=
  accepted_of_selected 12 5803 ⟨85678, by decide⟩ ⟨12, 2, 0, 85678, 5803, 1961, 65536⟩
    (by decide) selected_cut_02767

theorem unmarked_context_11_1450_85679 : frontier 10 ⟨85679, by decide⟩
    (prefixCache 11 1450) (prefixPartial 11 1450) = false := by
  decide +kernel

theorem node_context_11_1450_85679 : EJMOriginalGlobalDAGData.nodes 10 ⟨85679, by decide⟩ =
    .split (coordinate 11) (![⟨85589, by decide⟩,⟨85610, by decide⟩,⟨85659, by decide⟩,⟨85678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1450_85679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1450 ⟨85679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1450
    ⟨85679, by decide⟩ (by decide) (![⟨85589, by decide⟩,⟨85610, by decide⟩,⟨85659, by decide⟩,⟨85678, by decide⟩]) unmarked_context_11_1450_85679 node_context_11_1450_85679
  intro a
  fin_cases a
  · exact context_12_5800_85589
  · exact context_12_5801_85610
  · exact context_12_5802_85659
  · exact context_12_5803_85678

theorem selected_cut_02768 : selected 9 ⟨85701, by decide⟩
    (prefixPartial 12 5804) = some ⟨12, 2, 0, 85701, 5804, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_5804_85701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5804 ⟨85701, by decide⟩ :=
  accepted_of_selected 12 5804 ⟨85701, by decide⟩ ⟨12, 2, 0, 85701, 5804, 1925, 65536⟩
    (by decide) selected_cut_02768

theorem selected_cut_02769 : selected 9 ⟨85720, by decide⟩
    (prefixPartial 12 5805) = some ⟨12, 2, 0, 85720, 5805, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_5805_85720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5805 ⟨85720, by decide⟩ :=
  accepted_of_selected 12 5805 ⟨85720, by decide⟩ ⟨12, 2, 0, 85720, 5805, 1997, 65536⟩
    (by decide) selected_cut_02769

theorem selected_cut_02770 : selected 9 ⟨85735, by decide⟩
    (prefixPartial 12 5806) = some ⟨12, 2, 0, 85735, 5806, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_5806_85735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5806 ⟨85735, by decide⟩ :=
  accepted_of_selected 12 5806 ⟨85735, by decide⟩ ⟨12, 2, 0, 85735, 5806, 1705, 65536⟩
    (by decide) selected_cut_02770

theorem selected_cut_02771 : selected 9 ⟨85755, by decide⟩
    (prefixPartial 12 5807) = some ⟨12, 2, 0, 85755, 5807, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_5807_85755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5807 ⟨85755, by decide⟩ :=
  accepted_of_selected 12 5807 ⟨85755, by decide⟩ ⟨12, 2, 0, 85755, 5807, 1869, 65536⟩
    (by decide) selected_cut_02771

theorem unmarked_context_11_1451_85756 : frontier 10 ⟨85756, by decide⟩
    (prefixCache 11 1451) (prefixPartial 11 1451) = false := by
  decide +kernel

theorem node_context_11_1451_85756 : EJMOriginalGlobalDAGData.nodes 10 ⟨85756, by decide⟩ =
    .split (coordinate 11) (![⟨85701, by decide⟩,⟨85720, by decide⟩,⟨85735, by decide⟩,⟨85755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1451_85756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1451 ⟨85756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1451
    ⟨85756, by decide⟩ (by decide) (![⟨85701, by decide⟩,⟨85720, by decide⟩,⟨85735, by decide⟩,⟨85755, by decide⟩]) unmarked_context_11_1451_85756 node_context_11_1451_85756
  intro a
  fin_cases a
  · exact context_12_5804_85701
  · exact context_12_5805_85720
  · exact context_12_5806_85735
  · exact context_12_5807_85755

theorem unmarked_context_10_362_85757 : frontier 11 ⟨85757, by decide⟩
    (prefixCache 10 362) (prefixPartial 10 362) = false := by
  decide +kernel

theorem node_context_10_362_85757 : EJMOriginalGlobalDAGData.nodes 11 ⟨85757, by decide⟩ =
    .split (coordinate 10) (![⟨85484, by decide⟩,⟨85571, by decide⟩,⟨85679, by decide⟩,⟨85756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_362_85757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 362 ⟨85757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 362
    ⟨85757, by decide⟩ (by decide) (![⟨85484, by decide⟩,⟨85571, by decide⟩,⟨85679, by decide⟩,⟨85756, by decide⟩]) unmarked_context_10_362_85757 node_context_10_362_85757
  intro a
  fin_cases a
  · exact context_11_1448_85484
  · exact context_11_1449_85571
  · exact context_11_1450_85679
  · exact context_11_1451_85756

theorem selected_cut_02772 : selected 9 ⟨85776, by decide⟩
    (prefixPartial 12 5808) = some ⟨12, 2, 0, 85776, 5808, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_5808_85776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5808 ⟨85776, by decide⟩ :=
  accepted_of_selected 12 5808 ⟨85776, by decide⟩ ⟨12, 2, 0, 85776, 5808, 1657, 65536⟩
    (by decide) selected_cut_02772

theorem selected_cut_02773 : selected 9 ⟨85800, by decide⟩
    (prefixPartial 12 5809) = some ⟨12, 2, 0, 85800, 5809, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_5809_85800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5809 ⟨85800, by decide⟩ :=
  accepted_of_selected 12 5809 ⟨85800, by decide⟩ ⟨12, 2, 0, 85800, 5809, 1805, 65536⟩
    (by decide) selected_cut_02773

theorem selected_cut_02774 : selected 9 ⟨85820, by decide⟩
    (prefixPartial 12 5810) = some ⟨12, 2, 0, 85820, 5810, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_5810_85820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5810 ⟨85820, by decide⟩ :=
  accepted_of_selected 12 5810 ⟨85820, by decide⟩ ⟨12, 2, 0, 85820, 5810, 1685, 65536⟩
    (by decide) selected_cut_02774

theorem selected_cut_02775 : selected 9 ⟨85844, by decide⟩
    (prefixPartial 12 5811) = some ⟨12, 2, 0, 85844, 5811, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_5811_85844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5811 ⟨85844, by decide⟩ :=
  accepted_of_selected 12 5811 ⟨85844, by decide⟩ ⟨12, 2, 0, 85844, 5811, 1749, 65536⟩
    (by decide) selected_cut_02775

theorem unmarked_context_11_1452_85845 : frontier 10 ⟨85845, by decide⟩
    (prefixCache 11 1452) (prefixPartial 11 1452) = false := by
  decide +kernel

theorem node_context_11_1452_85845 : EJMOriginalGlobalDAGData.nodes 10 ⟨85845, by decide⟩ =
    .split (coordinate 11) (![⟨85776, by decide⟩,⟨85800, by decide⟩,⟨85820, by decide⟩,⟨85844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1452_85845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1452 ⟨85845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1452
    ⟨85845, by decide⟩ (by decide) (![⟨85776, by decide⟩,⟨85800, by decide⟩,⟨85820, by decide⟩,⟨85844, by decide⟩]) unmarked_context_11_1452_85845 node_context_11_1452_85845
  intro a
  fin_cases a
  · exact context_12_5808_85776
  · exact context_12_5809_85800
  · exact context_12_5810_85820
  · exact context_12_5811_85844

theorem selected_cut_02776 : selected 9 ⟨85866, by decide⟩
    (prefixPartial 12 5812) = some ⟨12, 2, 0, 85866, 5812, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_5812_85866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5812 ⟨85866, by decide⟩ :=
  accepted_of_selected 12 5812 ⟨85866, by decide⟩ ⟨12, 2, 0, 85866, 5812, 1573, 65536⟩
    (by decide) selected_cut_02776

theorem selected_cut_02777 : selected 9 ⟨85880, by decide⟩
    (prefixPartial 12 5813) = some ⟨12, 2, 0, 85880, 5813, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_5813_85880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5813 ⟨85880, by decide⟩ :=
  accepted_of_selected 12 5813 ⟨85880, by decide⟩ ⟨12, 2, 0, 85880, 5813, 1621, 65536⟩
    (by decide) selected_cut_02777

theorem selected_cut_02778 : selected 9 ⟨85898, by decide⟩
    (prefixPartial 12 5814) = some ⟨12, 2, 0, 85898, 5814, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_5814_85898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5814 ⟨85898, by decide⟩ :=
  accepted_of_selected 12 5814 ⟨85898, by decide⟩ ⟨12, 2, 0, 85898, 5814, 1573, 65536⟩
    (by decide) selected_cut_02778

theorem selected_cut_02779 : selected 9 ⟨85920, by decide⟩
    (prefixPartial 12 5815) = some ⟨12, 2, 0, 85920, 5815, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_5815_85920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5815 ⟨85920, by decide⟩ :=
  accepted_of_selected 12 5815 ⟨85920, by decide⟩ ⟨12, 2, 0, 85920, 5815, 1617, 65536⟩
    (by decide) selected_cut_02779

theorem unmarked_context_11_1453_85921 : frontier 10 ⟨85921, by decide⟩
    (prefixCache 11 1453) (prefixPartial 11 1453) = false := by
  decide +kernel

theorem node_context_11_1453_85921 : EJMOriginalGlobalDAGData.nodes 10 ⟨85921, by decide⟩ =
    .split (coordinate 11) (![⟨85866, by decide⟩,⟨85880, by decide⟩,⟨85898, by decide⟩,⟨85920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1453_85921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1453 ⟨85921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1453
    ⟨85921, by decide⟩ (by decide) (![⟨85866, by decide⟩,⟨85880, by decide⟩,⟨85898, by decide⟩,⟨85920, by decide⟩]) unmarked_context_11_1453_85921 node_context_11_1453_85921
  intro a
  fin_cases a
  · exact context_12_5812_85866
  · exact context_12_5813_85880
  · exact context_12_5814_85898
  · exact context_12_5815_85920

theorem selected_cut_02780 : selected 9 ⟨85939, by decide⟩
    (prefixPartial 12 5816) = some ⟨12, 2, 0, 85939, 5816, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_5816_85939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5816 ⟨85939, by decide⟩ :=
  accepted_of_selected 12 5816 ⟨85939, by decide⟩ ⟨12, 2, 0, 85939, 5816, 1529, 65536⟩
    (by decide) selected_cut_02780

theorem selected_cut_02781 : selected 9 ⟨85956, by decide⟩
    (prefixPartial 12 5817) = some ⟨12, 2, 0, 85956, 5817, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_5817_85956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5817 ⟨85956, by decide⟩ :=
  accepted_of_selected 12 5817 ⟨85956, by decide⟩ ⟨12, 2, 0, 85956, 5817, 1701, 65536⟩
    (by decide) selected_cut_02781

theorem selected_cut_02782 : selected 9 ⟨86004, by decide⟩
    (prefixPartial 12 5818) = some ⟨12, 2, 0, 86004, 5818, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_5818_86004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5818 ⟨86004, by decide⟩ :=
  accepted_of_selected 12 5818 ⟨86004, by decide⟩ ⟨12, 2, 0, 86004, 5818, 2273, 65536⟩
    (by decide) selected_cut_02782

theorem selected_cut_02783 : selected 9 ⟨86018, by decide⟩
    (prefixPartial 12 5819) = some ⟨12, 2, 0, 86018, 5819, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_5819_86018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5819 ⟨86018, by decide⟩ :=
  accepted_of_selected 12 5819 ⟨86018, by decide⟩ ⟨12, 2, 0, 86018, 5819, 1517, 65536⟩
    (by decide) selected_cut_02783

theorem unmarked_context_11_1454_86019 : frontier 10 ⟨86019, by decide⟩
    (prefixCache 11 1454) (prefixPartial 11 1454) = false := by
  decide +kernel

theorem node_context_11_1454_86019 : EJMOriginalGlobalDAGData.nodes 10 ⟨86019, by decide⟩ =
    .split (coordinate 11) (![⟨85939, by decide⟩,⟨85956, by decide⟩,⟨86004, by decide⟩,⟨86018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1454_86019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1454 ⟨86019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1454
    ⟨86019, by decide⟩ (by decide) (![⟨85939, by decide⟩,⟨85956, by decide⟩,⟨86004, by decide⟩,⟨86018, by decide⟩]) unmarked_context_11_1454_86019 node_context_11_1454_86019
  intro a
  fin_cases a
  · exact context_12_5816_85939
  · exact context_12_5817_85956
  · exact context_12_5818_86004
  · exact context_12_5819_86018

theorem selected_cut_02784 : selected 9 ⟨86033, by decide⟩
    (prefixPartial 12 5820) = some ⟨12, 2, 0, 86033, 5820, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_5820_86033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5820 ⟨86033, by decide⟩ :=
  accepted_of_selected 12 5820 ⟨86033, by decide⟩ ⟨12, 2, 0, 86033, 5820, 1353, 65536⟩
    (by decide) selected_cut_02784

theorem selected_cut_02785 : selected 9 ⟨86049, by decide⟩
    (prefixPartial 12 5821) = some ⟨12, 2, 0, 86049, 5821, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_5821_86049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5821 ⟨86049, by decide⟩ :=
  accepted_of_selected 12 5821 ⟨86049, by decide⟩ ⟨12, 2, 0, 86049, 5821, 1365, 65536⟩
    (by decide) selected_cut_02785

theorem selected_cut_02786 : selected 9 ⟨86058, by decide⟩
    (prefixPartial 12 5822) = some ⟨12, 2, 0, 86058, 5822, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_5822_86058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5822 ⟨86058, by decide⟩ :=
  accepted_of_selected 12 5822 ⟨86058, by decide⟩ ⟨12, 2, 0, 86058, 5822, 1229, 65536⟩
    (by decide) selected_cut_02786

theorem selected_cut_02787 : selected 9 ⟨86070, by decide⟩
    (prefixPartial 12 5823) = some ⟨12, 2, 0, 86070, 5823, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_5823_86070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5823 ⟨86070, by decide⟩ :=
  accepted_of_selected 12 5823 ⟨86070, by decide⟩ ⟨12, 2, 0, 86070, 5823, 1313, 65536⟩
    (by decide) selected_cut_02787

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
