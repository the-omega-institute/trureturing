/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover060
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05859 : selected 7 ⟨179317, by decide⟩
    (prefixPartial 14 336039) = some ⟨14, 2, 0, 179317, 336039, 1261, 4096⟩ := by
  decide +kernel

theorem context_14_336039_179317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336039 ⟨179317, by decide⟩ :=
  accepted_of_selected 14 336039 ⟨179317, by decide⟩ ⟨14, 2, 0, 179317, 336039, 1261, 4096⟩
    (by decide) selected_cut_05859

theorem unmarked_context_13_84009_179318 : frontier 8 ⟨179318, by decide⟩
    (prefixCache 13 84009) (prefixPartial 13 84009) = false := by
  decide +kernel

theorem node_context_13_84009_179318 : EJMOriginalGlobalDAGData.nodes 8 ⟨179318, by decide⟩ =
    .split (coordinate 13) (![⟨179229, by decide⟩,⟨179272, by decide⟩,⟨179296, by decide⟩,⟨179317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_84009_179318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84009 ⟨179318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 84009
    ⟨179318, by decide⟩ (by decide) (![⟨179229, by decide⟩,⟨179272, by decide⟩,⟨179296, by decide⟩,⟨179317, by decide⟩]) unmarked_context_13_84009_179318 node_context_13_84009_179318
  intro a
  fin_cases a
  · exact context_14_336036_179229
  · exact context_14_336037_179272
  · exact context_14_336038_179296
  · exact context_14_336039_179317

theorem selected_cut_05860 : selected 8 ⟨179378, by decide⟩
    (prefixPartial 13 84010) = some ⟨13, 2, 0, 179378, 84010, 3437, 16384⟩ := by
  decide +kernel

theorem context_13_84010_179378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84010 ⟨179378, by decide⟩ :=
  accepted_of_selected 13 84010 ⟨179378, by decide⟩ ⟨13, 2, 0, 179378, 84010, 3437, 16384⟩
    (by decide) selected_cut_05860

theorem selected_cut_05861 : selected 8 ⟨179406, by decide⟩
    (prefixPartial 13 84011) = some ⟨13, 2, 0, 179406, 84011, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_84011_179406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84011 ⟨179406, by decide⟩ :=
  accepted_of_selected 13 84011 ⟨179406, by decide⟩ ⟨13, 2, 0, 179406, 84011, 1501, 16384⟩
    (by decide) selected_cut_05861

theorem unmarked_context_12_21002_179407 : frontier 9 ⟨179407, by decide⟩
    (prefixCache 12 21002) (prefixPartial 12 21002) = false := by
  decide +kernel

theorem node_context_12_21002_179407 : EJMOriginalGlobalDAGData.nodes 9 ⟨179407, by decide⟩ =
    .split (coordinate 12) (![⟨179190, by decide⟩,⟨179318, by decide⟩,⟨179378, by decide⟩,⟨179406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21002_179407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21002 ⟨179407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21002
    ⟨179407, by decide⟩ (by decide) (![⟨179190, by decide⟩,⟨179318, by decide⟩,⟨179378, by decide⟩,⟨179406, by decide⟩]) unmarked_context_12_21002_179407 node_context_12_21002_179407
  intro a
  fin_cases a
  · exact context_13_84008_179190
  · exact context_13_84009_179318
  · exact context_13_84010_179378
  · exact context_13_84011_179406

theorem selected_cut_05862 : selected 8 ⟨179463, by decide⟩
    (prefixPartial 13 84012) = some ⟨13, 2, 0, 179463, 84012, 3697, 16384⟩ := by
  decide +kernel

theorem context_13_84012_179463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84012 ⟨179463, by decide⟩ :=
  accepted_of_selected 13 84012 ⟨179463, by decide⟩ ⟨13, 2, 0, 179463, 84012, 3697, 16384⟩
    (by decide) selected_cut_05862

theorem selected_cut_05863 : selected 8 ⟨179535, by decide⟩
    (prefixPartial 13 84013) = some ⟨13, 2, 0, 179535, 84013, 3965, 16384⟩ := by
  decide +kernel

theorem context_13_84013_179535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84013 ⟨179535, by decide⟩ :=
  accepted_of_selected 13 84013 ⟨179535, by decide⟩ ⟨13, 2, 0, 179535, 84013, 3965, 16384⟩
    (by decide) selected_cut_05863

theorem selected_cut_05864 : selected 8 ⟨179559, by decide⟩
    (prefixPartial 13 84014) = some ⟨13, 2, 0, 179559, 84014, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_84014_179559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84014 ⟨179559, by decide⟩ :=
  accepted_of_selected 13 84014 ⟨179559, by decide⟩ ⟨13, 2, 0, 179559, 84014, 2093, 16384⟩
    (by decide) selected_cut_05864

theorem selected_cut_05865 : selected 8 ⟨179572, by decide⟩
    (prefixPartial 13 84015) = some ⟨13, 2, 0, 179572, 84015, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_84015_179572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84015 ⟨179572, by decide⟩ :=
  accepted_of_selected 13 84015 ⟨179572, by decide⟩ ⟨13, 2, 0, 179572, 84015, 1165, 16384⟩
    (by decide) selected_cut_05865

theorem unmarked_context_12_21003_179573 : frontier 9 ⟨179573, by decide⟩
    (prefixCache 12 21003) (prefixPartial 12 21003) = false := by
  decide +kernel

theorem node_context_12_21003_179573 : EJMOriginalGlobalDAGData.nodes 9 ⟨179573, by decide⟩ =
    .split (coordinate 12) (![⟨179463, by decide⟩,⟨179535, by decide⟩,⟨179559, by decide⟩,⟨179572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21003_179573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21003 ⟨179573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21003
    ⟨179573, by decide⟩ (by decide) (![⟨179463, by decide⟩,⟨179535, by decide⟩,⟨179559, by decide⟩,⟨179572, by decide⟩]) unmarked_context_12_21003_179573 node_context_12_21003_179573
  intro a
  fin_cases a
  · exact context_13_84012_179463
  · exact context_13_84013_179535
  · exact context_13_84014_179559
  · exact context_13_84015_179572

theorem unmarked_context_11_5250_179574 : frontier 10 ⟨179574, by decide⟩
    (prefixCache 11 5250) (prefixPartial 11 5250) = false := by
  decide +kernel

theorem node_context_11_5250_179574 : EJMOriginalGlobalDAGData.nodes 10 ⟨179574, by decide⟩ =
    .split (coordinate 11) (![⟨178945, by decide⟩,⟨179096, by decide⟩,⟨179407, by decide⟩,⟨179573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5250_179574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5250 ⟨179574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5250
    ⟨179574, by decide⟩ (by decide) (![⟨178945, by decide⟩,⟨179096, by decide⟩,⟨179407, by decide⟩,⟨179573, by decide⟩]) unmarked_context_11_5250_179574 node_context_11_5250_179574
  intro a
  fin_cases a
  · exact context_12_21000_178945
  · exact context_12_21001_179096
  · exact context_12_21002_179407
  · exact context_12_21003_179573

theorem selected_cut_05866 : selected 8 ⟨179621, by decide⟩
    (prefixPartial 13 84016) = some ⟨13, 2, 0, 179621, 84016, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_84016_179621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84016 ⟨179621, by decide⟩ :=
  accepted_of_selected 13 84016 ⟨179621, by decide⟩ ⟨13, 2, 0, 179621, 84016, 2801, 16384⟩
    (by decide) selected_cut_05866

theorem selected_cut_05867 : selected 8 ⟨179659, by decide⟩
    (prefixPartial 13 84017) = some ⟨13, 2, 0, 179659, 84017, 3365, 16384⟩ := by
  decide +kernel

theorem context_13_84017_179659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84017 ⟨179659, by decide⟩ :=
  accepted_of_selected 13 84017 ⟨179659, by decide⟩ ⟨13, 2, 0, 179659, 84017, 3365, 16384⟩
    (by decide) selected_cut_05867

theorem selected_cut_05868 : selected 8 ⟨179683, by decide⟩
    (prefixPartial 13 84018) = some ⟨13, 2, 0, 179683, 84018, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_84018_179683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84018 ⟨179683, by decide⟩ :=
  accepted_of_selected 13 84018 ⟨179683, by decide⟩ ⟨13, 2, 0, 179683, 84018, 2201, 16384⟩
    (by decide) selected_cut_05868

theorem selected_cut_05869 : selected 8 ⟨179694, by decide⟩
    (prefixPartial 13 84019) = some ⟨13, 2, 0, 179694, 84019, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_84019_179694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84019 ⟨179694, by decide⟩ :=
  accepted_of_selected 13 84019 ⟨179694, by decide⟩ ⟨13, 2, 0, 179694, 84019, 1125, 16384⟩
    (by decide) selected_cut_05869

theorem unmarked_context_12_21004_179695 : frontier 9 ⟨179695, by decide⟩
    (prefixCache 12 21004) (prefixPartial 12 21004) = false := by
  decide +kernel

theorem node_context_12_21004_179695 : EJMOriginalGlobalDAGData.nodes 9 ⟨179695, by decide⟩ =
    .split (coordinate 12) (![⟨179621, by decide⟩,⟨179659, by decide⟩,⟨179683, by decide⟩,⟨179694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21004_179695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21004 ⟨179695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21004
    ⟨179695, by decide⟩ (by decide) (![⟨179621, by decide⟩,⟨179659, by decide⟩,⟨179683, by decide⟩,⟨179694, by decide⟩]) unmarked_context_12_21004_179695 node_context_12_21004_179695
  intro a
  fin_cases a
  · exact context_13_84016_179621
  · exact context_13_84017_179659
  · exact context_13_84018_179683
  · exact context_13_84019_179694

theorem selected_cut_05870 : selected 8 ⟨179750, by decide⟩
    (prefixPartial 13 84020) = some ⟨13, 2, 0, 179750, 84020, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_84020_179750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84020 ⟨179750, by decide⟩ :=
  accepted_of_selected 13 84020 ⟨179750, by decide⟩ ⟨13, 2, 0, 179750, 84020, 3085, 16384⟩
    (by decide) selected_cut_05870

theorem selected_cut_05871 : selected 8 ⟨179813, by decide⟩
    (prefixPartial 13 84021) = some ⟨13, 2, 0, 179813, 84021, 3897, 16384⟩ := by
  decide +kernel

theorem context_13_84021_179813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84021 ⟨179813, by decide⟩ :=
  accepted_of_selected 13 84021 ⟨179813, by decide⟩ ⟨13, 2, 0, 179813, 84021, 3897, 16384⟩
    (by decide) selected_cut_05871

theorem selected_cut_05872 : selected 8 ⟨179839, by decide⟩
    (prefixPartial 13 84022) = some ⟨13, 2, 0, 179839, 84022, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_84022_179839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84022 ⟨179839, by decide⟩ :=
  accepted_of_selected 13 84022 ⟨179839, by decide⟩ ⟨13, 2, 0, 179839, 84022, 2501, 16384⟩
    (by decide) selected_cut_05872

theorem selected_cut_05873 : selected 8 ⟨179850, by decide⟩
    (prefixPartial 13 84023) = some ⟨13, 2, 0, 179850, 84023, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_84023_179850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84023 ⟨179850, by decide⟩ :=
  accepted_of_selected 13 84023 ⟨179850, by decide⟩ ⟨13, 2, 0, 179850, 84023, 1101, 16384⟩
    (by decide) selected_cut_05873

theorem unmarked_context_12_21005_179851 : frontier 9 ⟨179851, by decide⟩
    (prefixCache 12 21005) (prefixPartial 12 21005) = false := by
  decide +kernel

theorem node_context_12_21005_179851 : EJMOriginalGlobalDAGData.nodes 9 ⟨179851, by decide⟩ =
    .split (coordinate 12) (![⟨179750, by decide⟩,⟨179813, by decide⟩,⟨179839, by decide⟩,⟨179850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21005_179851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21005 ⟨179851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21005
    ⟨179851, by decide⟩ (by decide) (![⟨179750, by decide⟩,⟨179813, by decide⟩,⟨179839, by decide⟩,⟨179850, by decide⟩]) unmarked_context_12_21005_179851 node_context_12_21005_179851
  intro a
  fin_cases a
  · exact context_13_84020_179750
  · exact context_13_84021_179813
  · exact context_13_84022_179839
  · exact context_13_84023_179850

theorem selected_cut_05874 : selected 8 ⟨179911, by decide⟩
    (prefixPartial 13 84024) = some ⟨13, 2, 0, 179911, 84024, 3349, 16384⟩ := by
  decide +kernel

theorem context_13_84024_179911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84024 ⟨179911, by decide⟩ :=
  accepted_of_selected 13 84024 ⟨179911, by decide⟩ ⟨13, 2, 0, 179911, 84024, 3349, 16384⟩
    (by decide) selected_cut_05874

theorem selected_cut_05875 : selected 7 ⟨179937, by decide⟩
    (prefixPartial 14 336100) = some ⟨14, 2, 0, 179937, 336100, 1285, 4096⟩ := by
  decide +kernel

theorem context_14_336100_179937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336100 ⟨179937, by decide⟩ :=
  accepted_of_selected 14 336100 ⟨179937, by decide⟩ ⟨14, 2, 0, 179937, 336100, 1285, 4096⟩
    (by decide) selected_cut_05875

theorem selected_cut_05876 : selected 7 ⟨179962, by decide⟩
    (prefixPartial 14 336101) = some ⟨14, 2, 0, 179962, 336101, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_336101_179962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336101 ⟨179962, by decide⟩ :=
  accepted_of_selected 14 336101 ⟨179962, by decide⟩ ⟨14, 2, 0, 179962, 336101, 1173, 4096⟩
    (by decide) selected_cut_05876

theorem selected_cut_05877 : selected 7 ⟨179975, by decide⟩
    (prefixPartial 14 336102) = some ⟨14, 2, 0, 179975, 336102, 925, 4096⟩ := by
  decide +kernel

theorem context_14_336102_179975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336102 ⟨179975, by decide⟩ :=
  accepted_of_selected 14 336102 ⟨179975, by decide⟩ ⟨14, 2, 0, 179975, 336102, 925, 4096⟩
    (by decide) selected_cut_05877

theorem selected_cut_05878 : selected 7 ⟨179983, by decide⟩
    (prefixPartial 14 336103) = some ⟨14, 2, 0, 179983, 336103, 809, 4096⟩ := by
  decide +kernel

theorem context_14_336103_179983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 336103 ⟨179983, by decide⟩ :=
  accepted_of_selected 14 336103 ⟨179983, by decide⟩ ⟨14, 2, 0, 179983, 336103, 809, 4096⟩
    (by decide) selected_cut_05878

theorem unmarked_context_13_84025_179984 : frontier 8 ⟨179984, by decide⟩
    (prefixCache 13 84025) (prefixPartial 13 84025) = false := by
  decide +kernel

theorem node_context_13_84025_179984 : EJMOriginalGlobalDAGData.nodes 8 ⟨179984, by decide⟩ =
    .split (coordinate 13) (![⟨179937, by decide⟩,⟨179962, by decide⟩,⟨179975, by decide⟩,⟨179983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_84025_179984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84025 ⟨179984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 84025
    ⟨179984, by decide⟩ (by decide) (![⟨179937, by decide⟩,⟨179962, by decide⟩,⟨179975, by decide⟩,⟨179983, by decide⟩]) unmarked_context_13_84025_179984 node_context_13_84025_179984
  intro a
  fin_cases a
  · exact context_14_336100_179937
  · exact context_14_336101_179962
  · exact context_14_336102_179975
  · exact context_14_336103_179983

theorem selected_cut_05879 : selected 8 ⟨180015, by decide⟩
    (prefixPartial 13 84026) = some ⟨13, 2, 0, 180015, 84026, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_84026_180015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84026 ⟨180015, by decide⟩ :=
  accepted_of_selected 13 84026 ⟨180015, by decide⟩ ⟨13, 2, 0, 180015, 84026, 2265, 16384⟩
    (by decide) selected_cut_05879

theorem selected_cut_05880 : selected 8 ⟨180023, by decide⟩
    (prefixPartial 13 84027) = some ⟨13, 2, 0, 180023, 84027, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_84027_180023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84027 ⟨180023, by decide⟩ :=
  accepted_of_selected 13 84027 ⟨180023, by decide⟩ ⟨13, 2, 0, 180023, 84027, 1069, 16384⟩
    (by decide) selected_cut_05880

theorem unmarked_context_12_21006_180024 : frontier 9 ⟨180024, by decide⟩
    (prefixCache 12 21006) (prefixPartial 12 21006) = false := by
  decide +kernel

theorem node_context_12_21006_180024 : EJMOriginalGlobalDAGData.nodes 9 ⟨180024, by decide⟩ =
    .split (coordinate 12) (![⟨179911, by decide⟩,⟨179984, by decide⟩,⟨180015, by decide⟩,⟨180023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21006_180024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21006 ⟨180024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21006
    ⟨180024, by decide⟩ (by decide) (![⟨179911, by decide⟩,⟨179984, by decide⟩,⟨180015, by decide⟩,⟨180023, by decide⟩]) unmarked_context_12_21006_180024 node_context_12_21006_180024
  intro a
  fin_cases a
  · exact context_13_84024_179911
  · exact context_13_84025_179984
  · exact context_13_84026_180015
  · exact context_13_84027_180023

theorem selected_cut_05881 : selected 8 ⟨180077, by decide⟩
    (prefixPartial 13 84028) = some ⟨13, 2, 0, 180077, 84028, 3289, 16384⟩ := by
  decide +kernel

theorem context_13_84028_180077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84028 ⟨180077, by decide⟩ :=
  accepted_of_selected 13 84028 ⟨180077, by decide⟩ ⟨13, 2, 0, 180077, 84028, 3289, 16384⟩
    (by decide) selected_cut_05881

theorem selected_cut_05882 : selected 8 ⟨180136, by decide⟩
    (prefixPartial 13 84029) = some ⟨13, 2, 0, 180136, 84029, 4057, 16384⟩ := by
  decide +kernel

theorem context_13_84029_180136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84029 ⟨180136, by decide⟩ :=
  accepted_of_selected 13 84029 ⟨180136, by decide⟩ ⟨13, 2, 0, 180136, 84029, 4057, 16384⟩
    (by decide) selected_cut_05882

theorem selected_cut_05883 : selected 8 ⟨180162, by decide⟩
    (prefixPartial 13 84030) = some ⟨13, 2, 0, 180162, 84030, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_84030_180162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84030 ⟨180162, by decide⟩ :=
  accepted_of_selected 13 84030 ⟨180162, by decide⟩ ⟨13, 2, 0, 180162, 84030, 2233, 16384⟩
    (by decide) selected_cut_05883

theorem selected_cut_05884 : selected 8 ⟨180173, by decide⟩
    (prefixPartial 13 84031) = some ⟨13, 2, 0, 180173, 84031, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_84031_180173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84031 ⟨180173, by decide⟩ :=
  accepted_of_selected 13 84031 ⟨180173, by decide⟩ ⟨13, 2, 0, 180173, 84031, 1193, 16384⟩
    (by decide) selected_cut_05884

theorem unmarked_context_12_21007_180174 : frontier 9 ⟨180174, by decide⟩
    (prefixCache 12 21007) (prefixPartial 12 21007) = false := by
  decide +kernel

theorem node_context_12_21007_180174 : EJMOriginalGlobalDAGData.nodes 9 ⟨180174, by decide⟩ =
    .split (coordinate 12) (![⟨180077, by decide⟩,⟨180136, by decide⟩,⟨180162, by decide⟩,⟨180173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21007_180174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21007 ⟨180174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21007
    ⟨180174, by decide⟩ (by decide) (![⟨180077, by decide⟩,⟨180136, by decide⟩,⟨180162, by decide⟩,⟨180173, by decide⟩]) unmarked_context_12_21007_180174 node_context_12_21007_180174
  intro a
  fin_cases a
  · exact context_13_84028_180077
  · exact context_13_84029_180136
  · exact context_13_84030_180162
  · exact context_13_84031_180173

theorem unmarked_context_11_5251_180175 : frontier 10 ⟨180175, by decide⟩
    (prefixCache 11 5251) (prefixPartial 11 5251) = false := by
  decide +kernel

theorem node_context_11_5251_180175 : EJMOriginalGlobalDAGData.nodes 10 ⟨180175, by decide⟩ =
    .split (coordinate 11) (![⟨179695, by decide⟩,⟨179851, by decide⟩,⟨180024, by decide⟩,⟨180174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5251_180175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5251 ⟨180175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5251
    ⟨180175, by decide⟩ (by decide) (![⟨179695, by decide⟩,⟨179851, by decide⟩,⟨180024, by decide⟩,⟨180174, by decide⟩]) unmarked_context_11_5251_180175 node_context_11_5251_180175
  intro a
  fin_cases a
  · exact context_12_21004_179695
  · exact context_12_21005_179851
  · exact context_12_21006_180024
  · exact context_12_21007_180174

theorem unmarked_context_10_1312_180176 : frontier 11 ⟨180176, by decide⟩
    (prefixCache 10 1312) (prefixPartial 10 1312) = false := by
  decide +kernel

theorem node_context_10_1312_180176 : EJMOriginalGlobalDAGData.nodes 11 ⟨180176, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨178827, by decide⟩,⟨179574, by decide⟩,⟨180175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1312_180176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1312 ⟨180176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1312
    ⟨180176, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨178827, by decide⟩,⟨179574, by decide⟩,⟨180175, by decide⟩]) unmarked_context_10_1312_180176 node_context_10_1312_180176
  intro a
  fin_cases a
  · exact context_11_5248_167448
  · exact context_11_5249_178827
  · exact context_11_5250_179574
  · exact context_11_5251_180175

theorem selected_cut_05885 : selected 8 ⟨180198, by decide⟩
    (prefixPartial 13 84032) = some ⟨13, 2, 0, 180198, 84032, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_84032_180198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84032 ⟨180198, by decide⟩ :=
  accepted_of_selected 13 84032 ⟨180198, by decide⟩ ⟨13, 2, 0, 180198, 84032, 1289, 16384⟩
    (by decide) selected_cut_05885

theorem selected_cut_05886 : selected 8 ⟨180213, by decide⟩
    (prefixPartial 13 84033) = some ⟨13, 2, 0, 180213, 84033, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_84033_180213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84033 ⟨180213, by decide⟩ :=
  accepted_of_selected 13 84033 ⟨180213, by decide⟩ ⟨13, 2, 0, 180213, 84033, 1217, 16384⟩
    (by decide) selected_cut_05886

theorem selected_cut_05887 : selected 8 ⟨180232, by decide⟩
    (prefixPartial 13 84034) = some ⟨13, 2, 0, 180232, 84034, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_84034_180232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84034 ⟨180232, by decide⟩ :=
  accepted_of_selected 13 84034 ⟨180232, by decide⟩ ⟨13, 2, 0, 180232, 84034, 1225, 16384⟩
    (by decide) selected_cut_05887

theorem selected_cut_05888 : selected 8 ⟨180235, by decide⟩
    (prefixPartial 13 84035) = some ⟨13, 2, 0, 180235, 84035, 613, 16384⟩ := by
  decide +kernel

theorem context_13_84035_180235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84035 ⟨180235, by decide⟩ :=
  accepted_of_selected 13 84035 ⟨180235, by decide⟩ ⟨13, 2, 0, 180235, 84035, 613, 16384⟩
    (by decide) selected_cut_05888

theorem unmarked_context_12_21008_180236 : frontier 9 ⟨180236, by decide⟩
    (prefixCache 12 21008) (prefixPartial 12 21008) = false := by
  decide +kernel

theorem node_context_12_21008_180236 : EJMOriginalGlobalDAGData.nodes 9 ⟨180236, by decide⟩ =
    .split (coordinate 12) (![⟨180198, by decide⟩,⟨180213, by decide⟩,⟨180232, by decide⟩,⟨180235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21008_180236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21008 ⟨180236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21008
    ⟨180236, by decide⟩ (by decide) (![⟨180198, by decide⟩,⟨180213, by decide⟩,⟨180232, by decide⟩,⟨180235, by decide⟩]) unmarked_context_12_21008_180236 node_context_12_21008_180236
  intro a
  fin_cases a
  · exact context_13_84032_180198
  · exact context_13_84033_180213
  · exact context_13_84034_180232
  · exact context_13_84035_180235

theorem selected_cut_05889 : selected 8 ⟨180255, by decide⟩
    (prefixPartial 13 84036) = some ⟨13, 2, 0, 180255, 84036, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_84036_180255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84036 ⟨180255, by decide⟩ :=
  accepted_of_selected 13 84036 ⟨180255, by decide⟩ ⟨13, 2, 0, 180255, 84036, 1233, 16384⟩
    (by decide) selected_cut_05889

theorem selected_cut_05890 : selected 8 ⟨180277, by decide⟩
    (prefixPartial 13 84037) = some ⟨13, 2, 0, 180277, 84037, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_84037_180277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84037 ⟨180277, by decide⟩ :=
  accepted_of_selected 13 84037 ⟨180277, by decide⟩ ⟨13, 2, 0, 180277, 84037, 1613, 16384⟩
    (by decide) selected_cut_05890

theorem selected_cut_05891 : selected 8 ⟨180299, by decide⟩
    (prefixPartial 13 84038) = some ⟨13, 2, 0, 180299, 84038, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_84038_180299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84038 ⟨180299, by decide⟩ :=
  accepted_of_selected 13 84038 ⟨180299, by decide⟩ ⟨13, 2, 0, 180299, 84038, 1381, 16384⟩
    (by decide) selected_cut_05891

theorem selected_cut_05892 : selected 8 ⟨180306, by decide⟩
    (prefixPartial 13 84039) = some ⟨13, 2, 0, 180306, 84039, 725, 16384⟩ := by
  decide +kernel

theorem context_13_84039_180306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84039 ⟨180306, by decide⟩ :=
  accepted_of_selected 13 84039 ⟨180306, by decide⟩ ⟨13, 2, 0, 180306, 84039, 725, 16384⟩
    (by decide) selected_cut_05892

theorem unmarked_context_12_21009_180307 : frontier 9 ⟨180307, by decide⟩
    (prefixCache 12 21009) (prefixPartial 12 21009) = false := by
  decide +kernel

theorem node_context_12_21009_180307 : EJMOriginalGlobalDAGData.nodes 9 ⟨180307, by decide⟩ =
    .split (coordinate 12) (![⟨180255, by decide⟩,⟨180277, by decide⟩,⟨180299, by decide⟩,⟨180306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21009_180307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21009 ⟨180307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21009
    ⟨180307, by decide⟩ (by decide) (![⟨180255, by decide⟩,⟨180277, by decide⟩,⟨180299, by decide⟩,⟨180306, by decide⟩]) unmarked_context_12_21009_180307 node_context_12_21009_180307
  intro a
  fin_cases a
  · exact context_13_84036_180255
  · exact context_13_84037_180277
  · exact context_13_84038_180299
  · exact context_13_84039_180306

theorem selected_cut_05893 : selected 8 ⟨180329, by decide⟩
    (prefixPartial 13 84040) = some ⟨13, 2, 0, 180329, 84040, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_84040_180329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84040 ⟨180329, by decide⟩ :=
  accepted_of_selected 13 84040 ⟨180329, by decide⟩ ⟨13, 2, 0, 180329, 84040, 1493, 16384⟩
    (by decide) selected_cut_05893

theorem selected_cut_05894 : selected 8 ⟨180357, by decide⟩
    (prefixPartial 13 84041) = some ⟨13, 2, 0, 180357, 84041, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_84041_180357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84041 ⟨180357, by decide⟩ :=
  accepted_of_selected 13 84041 ⟨180357, by decide⟩ ⟨13, 2, 0, 180357, 84041, 1925, 16384⟩
    (by decide) selected_cut_05894

theorem selected_cut_05895 : selected 8 ⟨180376, by decide⟩
    (prefixPartial 13 84042) = some ⟨13, 2, 0, 180376, 84042, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_84042_180376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84042 ⟨180376, by decide⟩ :=
  accepted_of_selected 13 84042 ⟨180376, by decide⟩ ⟨13, 2, 0, 180376, 84042, 1453, 16384⟩
    (by decide) selected_cut_05895

theorem selected_cut_05896 : selected 8 ⟨180381, by decide⟩
    (prefixPartial 13 84043) = some ⟨13, 2, 0, 180381, 84043, 741, 16384⟩ := by
  decide +kernel

theorem context_13_84043_180381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84043 ⟨180381, by decide⟩ :=
  accepted_of_selected 13 84043 ⟨180381, by decide⟩ ⟨13, 2, 0, 180381, 84043, 741, 16384⟩
    (by decide) selected_cut_05896

theorem unmarked_context_12_21010_180382 : frontier 9 ⟨180382, by decide⟩
    (prefixCache 12 21010) (prefixPartial 12 21010) = false := by
  decide +kernel

theorem node_context_12_21010_180382 : EJMOriginalGlobalDAGData.nodes 9 ⟨180382, by decide⟩ =
    .split (coordinate 12) (![⟨180329, by decide⟩,⟨180357, by decide⟩,⟨180376, by decide⟩,⟨180381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21010_180382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21010 ⟨180382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21010
    ⟨180382, by decide⟩ (by decide) (![⟨180329, by decide⟩,⟨180357, by decide⟩,⟨180376, by decide⟩,⟨180381, by decide⟩]) unmarked_context_12_21010_180382 node_context_12_21010_180382
  intro a
  fin_cases a
  · exact context_13_84040_180329
  · exact context_13_84041_180357
  · exact context_13_84042_180376
  · exact context_13_84043_180381

theorem selected_cut_05897 : selected 8 ⟨180409, by decide⟩
    (prefixPartial 13 84044) = some ⟨13, 2, 0, 180409, 84044, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_84044_180409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84044 ⟨180409, by decide⟩ :=
  accepted_of_selected 13 84044 ⟨180409, by decide⟩ ⟨13, 2, 0, 180409, 84044, 1657, 16384⟩
    (by decide) selected_cut_05897

theorem selected_cut_05898 : selected 8 ⟨180436, by decide⟩
    (prefixPartial 13 84045) = some ⟨13, 2, 0, 180436, 84045, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_84045_180436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84045 ⟨180436, by decide⟩ :=
  accepted_of_selected 13 84045 ⟨180436, by decide⟩ ⟨13, 2, 0, 180436, 84045, 2037, 16384⟩
    (by decide) selected_cut_05898

theorem selected_cut_05899 : selected 8 ⟨180458, by decide⟩
    (prefixPartial 13 84046) = some ⟨13, 2, 0, 180458, 84046, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_84046_180458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84046 ⟨180458, by decide⟩ :=
  accepted_of_selected 13 84046 ⟨180458, by decide⟩ ⟨13, 2, 0, 180458, 84046, 1513, 16384⟩
    (by decide) selected_cut_05899

theorem selected_cut_05900 : selected 8 ⟨180465, by decide⟩
    (prefixPartial 13 84047) = some ⟨13, 2, 0, 180465, 84047, 761, 16384⟩ := by
  decide +kernel

theorem context_13_84047_180465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84047 ⟨180465, by decide⟩ :=
  accepted_of_selected 13 84047 ⟨180465, by decide⟩ ⟨13, 2, 0, 180465, 84047, 761, 16384⟩
    (by decide) selected_cut_05900

theorem unmarked_context_12_21011_180466 : frontier 9 ⟨180466, by decide⟩
    (prefixCache 12 21011) (prefixPartial 12 21011) = false := by
  decide +kernel

theorem node_context_12_21011_180466 : EJMOriginalGlobalDAGData.nodes 9 ⟨180466, by decide⟩ =
    .split (coordinate 12) (![⟨180409, by decide⟩,⟨180436, by decide⟩,⟨180458, by decide⟩,⟨180465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21011_180466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21011 ⟨180466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21011
    ⟨180466, by decide⟩ (by decide) (![⟨180409, by decide⟩,⟨180436, by decide⟩,⟨180458, by decide⟩,⟨180465, by decide⟩]) unmarked_context_12_21011_180466 node_context_12_21011_180466
  intro a
  fin_cases a
  · exact context_13_84044_180409
  · exact context_13_84045_180436
  · exact context_13_84046_180458
  · exact context_13_84047_180465

theorem unmarked_context_11_5252_180467 : frontier 10 ⟨180467, by decide⟩
    (prefixCache 11 5252) (prefixPartial 11 5252) = false := by
  decide +kernel

theorem node_context_11_5252_180467 : EJMOriginalGlobalDAGData.nodes 10 ⟨180467, by decide⟩ =
    .split (coordinate 11) (![⟨180236, by decide⟩,⟨180307, by decide⟩,⟨180382, by decide⟩,⟨180466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5252_180467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5252 ⟨180467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5252
    ⟨180467, by decide⟩ (by decide) (![⟨180236, by decide⟩,⟨180307, by decide⟩,⟨180382, by decide⟩,⟨180466, by decide⟩]) unmarked_context_11_5252_180467 node_context_11_5252_180467
  intro a
  fin_cases a
  · exact context_12_21008_180236
  · exact context_12_21009_180307
  · exact context_12_21010_180382
  · exact context_12_21011_180466

theorem selected_cut_05901 : selected 8 ⟨180490, by decide⟩
    (prefixPartial 13 84048) = some ⟨13, 2, 0, 180490, 84048, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_84048_180490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84048 ⟨180490, by decide⟩ :=
  accepted_of_selected 13 84048 ⟨180490, by decide⟩ ⟨13, 2, 0, 180490, 84048, 1513, 16384⟩
    (by decide) selected_cut_05901

theorem selected_cut_05902 : selected 8 ⟨180518, by decide⟩
    (prefixPartial 13 84049) = some ⟨13, 2, 0, 180518, 84049, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_84049_180518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84049 ⟨180518, by decide⟩ :=
  accepted_of_selected 13 84049 ⟨180518, by decide⟩ ⟨13, 2, 0, 180518, 84049, 1869, 16384⟩
    (by decide) selected_cut_05902

theorem selected_cut_05903 : selected 8 ⟨180536, by decide⟩
    (prefixPartial 13 84050) = some ⟨13, 2, 0, 180536, 84050, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_84050_180536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84050 ⟨180536, by decide⟩ :=
  accepted_of_selected 13 84050 ⟨180536, by decide⟩ ⟨13, 2, 0, 180536, 84050, 1213, 16384⟩
    (by decide) selected_cut_05903

theorem selected_cut_05904 : selected 8 ⟨180544, by decide⟩
    (prefixPartial 13 84051) = some ⟨13, 2, 0, 180544, 84051, 733, 16384⟩ := by
  decide +kernel

theorem context_13_84051_180544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84051 ⟨180544, by decide⟩ :=
  accepted_of_selected 13 84051 ⟨180544, by decide⟩ ⟨13, 2, 0, 180544, 84051, 733, 16384⟩
    (by decide) selected_cut_05904

theorem unmarked_context_12_21012_180545 : frontier 9 ⟨180545, by decide⟩
    (prefixCache 12 21012) (prefixPartial 12 21012) = false := by
  decide +kernel

theorem node_context_12_21012_180545 : EJMOriginalGlobalDAGData.nodes 9 ⟨180545, by decide⟩ =
    .split (coordinate 12) (![⟨180490, by decide⟩,⟨180518, by decide⟩,⟨180536, by decide⟩,⟨180544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21012_180545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21012 ⟨180545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21012
    ⟨180545, by decide⟩ (by decide) (![⟨180490, by decide⟩,⟨180518, by decide⟩,⟨180536, by decide⟩,⟨180544, by decide⟩]) unmarked_context_12_21012_180545 node_context_12_21012_180545
  intro a
  fin_cases a
  · exact context_13_84048_180490
  · exact context_13_84049_180518
  · exact context_13_84050_180536
  · exact context_13_84051_180544

theorem selected_cut_05905 : selected 8 ⟨180561, by decide⟩
    (prefixPartial 13 84052) = some ⟨13, 2, 0, 180561, 84052, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_84052_180561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84052 ⟨180561, by decide⟩ :=
  accepted_of_selected 13 84052 ⟨180561, by decide⟩ ⟨13, 2, 0, 180561, 84052, 1265, 16384⟩
    (by decide) selected_cut_05905

theorem selected_cut_05906 : selected 8 ⟨180587, by decide⟩
    (prefixPartial 13 84053) = some ⟨13, 2, 0, 180587, 84053, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_84053_180587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84053 ⟨180587, by decide⟩ :=
  accepted_of_selected 13 84053 ⟨180587, by decide⟩ ⟨13, 2, 0, 180587, 84053, 1833, 16384⟩
    (by decide) selected_cut_05906

theorem selected_cut_05907 : selected 8 ⟨180605, by decide⟩
    (prefixPartial 13 84054) = some ⟨13, 2, 0, 180605, 84054, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_84054_180605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84054 ⟨180605, by decide⟩ :=
  accepted_of_selected 13 84054 ⟨180605, by decide⟩ ⟨13, 2, 0, 180605, 84054, 1281, 16384⟩
    (by decide) selected_cut_05907

theorem selected_cut_05908 : selected 8 ⟨180612, by decide⟩
    (prefixPartial 13 84055) = some ⟨13, 2, 0, 180612, 84055, 761, 16384⟩ := by
  decide +kernel

theorem context_13_84055_180612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84055 ⟨180612, by decide⟩ :=
  accepted_of_selected 13 84055 ⟨180612, by decide⟩ ⟨13, 2, 0, 180612, 84055, 761, 16384⟩
    (by decide) selected_cut_05908

theorem unmarked_context_12_21013_180613 : frontier 9 ⟨180613, by decide⟩
    (prefixCache 12 21013) (prefixPartial 12 21013) = false := by
  decide +kernel

theorem node_context_12_21013_180613 : EJMOriginalGlobalDAGData.nodes 9 ⟨180613, by decide⟩ =
    .split (coordinate 12) (![⟨180561, by decide⟩,⟨180587, by decide⟩,⟨180605, by decide⟩,⟨180612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21013_180613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21013 ⟨180613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21013
    ⟨180613, by decide⟩ (by decide) (![⟨180561, by decide⟩,⟨180587, by decide⟩,⟨180605, by decide⟩,⟨180612, by decide⟩]) unmarked_context_12_21013_180613 node_context_12_21013_180613
  intro a
  fin_cases a
  · exact context_13_84052_180561
  · exact context_13_84053_180587
  · exact context_13_84054_180605
  · exact context_13_84055_180612

theorem selected_cut_05909 : selected 8 ⟨180638, by decide⟩
    (prefixPartial 13 84056) = some ⟨13, 2, 0, 180638, 84056, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_84056_180638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84056 ⟨180638, by decide⟩ :=
  accepted_of_selected 13 84056 ⟨180638, by decide⟩ ⟨13, 2, 0, 180638, 84056, 1549, 16384⟩
    (by decide) selected_cut_05909

theorem selected_cut_05910 : selected 8 ⟨180668, by decide⟩
    (prefixPartial 13 84057) = some ⟨13, 2, 0, 180668, 84057, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_84057_180668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84057 ⟨180668, by decide⟩ :=
  accepted_of_selected 13 84057 ⟨180668, by decide⟩ ⟨13, 2, 0, 180668, 84057, 2133, 16384⟩
    (by decide) selected_cut_05910

theorem selected_cut_05911 : selected 8 ⟨180686, by decide⟩
    (prefixPartial 13 84058) = some ⟨13, 2, 0, 180686, 84058, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_84058_180686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84058 ⟨180686, by decide⟩ :=
  accepted_of_selected 13 84058 ⟨180686, by decide⟩ ⟨13, 2, 0, 180686, 84058, 1293, 16384⟩
    (by decide) selected_cut_05911

theorem selected_cut_05912 : selected 8 ⟨180694, by decide⟩
    (prefixPartial 13 84059) = some ⟨13, 2, 0, 180694, 84059, 829, 16384⟩ := by
  decide +kernel

theorem context_13_84059_180694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84059 ⟨180694, by decide⟩ :=
  accepted_of_selected 13 84059 ⟨180694, by decide⟩ ⟨13, 2, 0, 180694, 84059, 829, 16384⟩
    (by decide) selected_cut_05912

theorem unmarked_context_12_21014_180695 : frontier 9 ⟨180695, by decide⟩
    (prefixCache 12 21014) (prefixPartial 12 21014) = false := by
  decide +kernel

theorem node_context_12_21014_180695 : EJMOriginalGlobalDAGData.nodes 9 ⟨180695, by decide⟩ =
    .split (coordinate 12) (![⟨180638, by decide⟩,⟨180668, by decide⟩,⟨180686, by decide⟩,⟨180694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21014_180695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21014 ⟨180695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21014
    ⟨180695, by decide⟩ (by decide) (![⟨180638, by decide⟩,⟨180668, by decide⟩,⟨180686, by decide⟩,⟨180694, by decide⟩]) unmarked_context_12_21014_180695 node_context_12_21014_180695
  intro a
  fin_cases a
  · exact context_13_84056_180638
  · exact context_13_84057_180668
  · exact context_13_84058_180686
  · exact context_13_84059_180694

theorem selected_cut_05913 : selected 8 ⟨180721, by decide⟩
    (prefixPartial 13 84060) = some ⟨13, 2, 0, 180721, 84060, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_84060_180721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84060 ⟨180721, by decide⟩ :=
  accepted_of_selected 13 84060 ⟨180721, by decide⟩ ⟨13, 2, 0, 180721, 84060, 1705, 16384⟩
    (by decide) selected_cut_05913

theorem selected_cut_05914 : selected 8 ⟨180749, by decide⟩
    (prefixPartial 13 84061) = some ⟨13, 2, 0, 180749, 84061, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_84061_180749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84061 ⟨180749, by decide⟩ :=
  accepted_of_selected 13 84061 ⟨180749, by decide⟩ ⟨13, 2, 0, 180749, 84061, 2205, 16384⟩
    (by decide) selected_cut_05914

theorem selected_cut_05915 : selected 8 ⟨180765, by decide⟩
    (prefixPartial 13 84062) = some ⟨13, 2, 0, 180765, 84062, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_84062_180765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84062 ⟨180765, by decide⟩ :=
  accepted_of_selected 13 84062 ⟨180765, by decide⟩ ⟨13, 2, 0, 180765, 84062, 1525, 16384⟩
    (by decide) selected_cut_05915

theorem selected_cut_05916 : selected 8 ⟨180772, by decide⟩
    (prefixPartial 13 84063) = some ⟨13, 2, 0, 180772, 84063, 829, 16384⟩ := by
  decide +kernel

theorem context_13_84063_180772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84063 ⟨180772, by decide⟩ :=
  accepted_of_selected 13 84063 ⟨180772, by decide⟩ ⟨13, 2, 0, 180772, 84063, 829, 16384⟩
    (by decide) selected_cut_05916

theorem unmarked_context_12_21015_180773 : frontier 9 ⟨180773, by decide⟩
    (prefixCache 12 21015) (prefixPartial 12 21015) = false := by
  decide +kernel

theorem node_context_12_21015_180773 : EJMOriginalGlobalDAGData.nodes 9 ⟨180773, by decide⟩ =
    .split (coordinate 12) (![⟨180721, by decide⟩,⟨180749, by decide⟩,⟨180765, by decide⟩,⟨180772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21015_180773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21015 ⟨180773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21015
    ⟨180773, by decide⟩ (by decide) (![⟨180721, by decide⟩,⟨180749, by decide⟩,⟨180765, by decide⟩,⟨180772, by decide⟩]) unmarked_context_12_21015_180773 node_context_12_21015_180773
  intro a
  fin_cases a
  · exact context_13_84060_180721
  · exact context_13_84061_180749
  · exact context_13_84062_180765
  · exact context_13_84063_180772

theorem unmarked_context_11_5253_180774 : frontier 10 ⟨180774, by decide⟩
    (prefixCache 11 5253) (prefixPartial 11 5253) = false := by
  decide +kernel

theorem node_context_11_5253_180774 : EJMOriginalGlobalDAGData.nodes 10 ⟨180774, by decide⟩ =
    .split (coordinate 11) (![⟨180545, by decide⟩,⟨180613, by decide⟩,⟨180695, by decide⟩,⟨180773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5253_180774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5253 ⟨180774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5253
    ⟨180774, by decide⟩ (by decide) (![⟨180545, by decide⟩,⟨180613, by decide⟩,⟨180695, by decide⟩,⟨180773, by decide⟩]) unmarked_context_11_5253_180774 node_context_11_5253_180774
  intro a
  fin_cases a
  · exact context_12_21012_180545
  · exact context_12_21013_180613
  · exact context_12_21014_180695
  · exact context_12_21015_180773

theorem selected_cut_05917 : selected 8 ⟨180802, by decide⟩
    (prefixPartial 13 84064) = some ⟨13, 2, 0, 180802, 84064, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_84064_180802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84064 ⟨180802, by decide⟩ :=
  accepted_of_selected 13 84064 ⟨180802, by decide⟩ ⟨13, 2, 0, 180802, 84064, 1637, 16384⟩
    (by decide) selected_cut_05917

theorem selected_cut_05918 : selected 8 ⟨180825, by decide⟩
    (prefixPartial 13 84065) = some ⟨13, 2, 0, 180825, 84065, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_84065_180825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84065 ⟨180825, by decide⟩ :=
  accepted_of_selected 13 84065 ⟨180825, by decide⟩ ⟨13, 2, 0, 180825, 84065, 1533, 16384⟩
    (by decide) selected_cut_05918

theorem selected_cut_05919 : selected 8 ⟨180846, by decide⟩
    (prefixPartial 13 84066) = some ⟨13, 2, 0, 180846, 84066, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_84066_180846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84066 ⟨180846, by decide⟩ :=
  accepted_of_selected 13 84066 ⟨180846, by decide⟩ ⟨13, 2, 0, 180846, 84066, 1365, 16384⟩
    (by decide) selected_cut_05919

theorem selected_cut_05920 : selected 8 ⟨180854, by decide⟩
    (prefixPartial 13 84067) = some ⟨13, 2, 0, 180854, 84067, 745, 16384⟩ := by
  decide +kernel

theorem context_13_84067_180854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84067 ⟨180854, by decide⟩ :=
  accepted_of_selected 13 84067 ⟨180854, by decide⟩ ⟨13, 2, 0, 180854, 84067, 745, 16384⟩
    (by decide) selected_cut_05920

theorem unmarked_context_12_21016_180855 : frontier 9 ⟨180855, by decide⟩
    (prefixCache 12 21016) (prefixPartial 12 21016) = false := by
  decide +kernel

theorem node_context_12_21016_180855 : EJMOriginalGlobalDAGData.nodes 9 ⟨180855, by decide⟩ =
    .split (coordinate 12) (![⟨180802, by decide⟩,⟨180825, by decide⟩,⟨180846, by decide⟩,⟨180854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21016_180855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21016 ⟨180855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21016
    ⟨180855, by decide⟩ (by decide) (![⟨180802, by decide⟩,⟨180825, by decide⟩,⟨180846, by decide⟩,⟨180854, by decide⟩]) unmarked_context_12_21016_180855 node_context_12_21016_180855
  intro a
  fin_cases a
  · exact context_13_84064_180802
  · exact context_13_84065_180825
  · exact context_13_84066_180846
  · exact context_13_84067_180854

theorem selected_cut_05921 : selected 8 ⟨180884, by decide⟩
    (prefixPartial 13 84068) = some ⟨13, 2, 0, 180884, 84068, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_84068_180884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84068 ⟨180884, by decide⟩ :=
  accepted_of_selected 13 84068 ⟨180884, by decide⟩ ⟨13, 2, 0, 180884, 84068, 1633, 16384⟩
    (by decide) selected_cut_05921

theorem selected_cut_05922 : selected 8 ⟨180912, by decide⟩
    (prefixPartial 13 84069) = some ⟨13, 2, 0, 180912, 84069, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_84069_180912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84069 ⟨180912, by decide⟩ :=
  accepted_of_selected 13 84069 ⟨180912, by decide⟩ ⟨13, 2, 0, 180912, 84069, 1849, 16384⟩
    (by decide) selected_cut_05922

theorem selected_cut_05923 : selected 8 ⟨180936, by decide⟩
    (prefixPartial 13 84070) = some ⟨13, 2, 0, 180936, 84070, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_84070_180936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84070 ⟨180936, by decide⟩ :=
  accepted_of_selected 13 84070 ⟨180936, by decide⟩ ⟨13, 2, 0, 180936, 84070, 1593, 16384⟩
    (by decide) selected_cut_05923

theorem selected_cut_05924 : selected 8 ⟨180945, by decide⟩
    (prefixPartial 13 84071) = some ⟨13, 2, 0, 180945, 84071, 877, 16384⟩ := by
  decide +kernel

theorem context_13_84071_180945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84071 ⟨180945, by decide⟩ :=
  accepted_of_selected 13 84071 ⟨180945, by decide⟩ ⟨13, 2, 0, 180945, 84071, 877, 16384⟩
    (by decide) selected_cut_05924

theorem unmarked_context_12_21017_180946 : frontier 9 ⟨180946, by decide⟩
    (prefixCache 12 21017) (prefixPartial 12 21017) = false := by
  decide +kernel

theorem node_context_12_21017_180946 : EJMOriginalGlobalDAGData.nodes 9 ⟨180946, by decide⟩ =
    .split (coordinate 12) (![⟨180884, by decide⟩,⟨180912, by decide⟩,⟨180936, by decide⟩,⟨180945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21017_180946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21017 ⟨180946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21017
    ⟨180946, by decide⟩ (by decide) (![⟨180884, by decide⟩,⟨180912, by decide⟩,⟨180936, by decide⟩,⟨180945, by decide⟩]) unmarked_context_12_21017_180946 node_context_12_21017_180946
  intro a
  fin_cases a
  · exact context_13_84068_180884
  · exact context_13_84069_180912
  · exact context_13_84070_180936
  · exact context_13_84071_180945

theorem selected_cut_05925 : selected 8 ⟨180988, by decide⟩
    (prefixPartial 13 84072) = some ⟨13, 2, 0, 180988, 84072, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_84072_180988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84072 ⟨180988, by decide⟩ :=
  accepted_of_selected 13 84072 ⟨180988, by decide⟩ ⟨13, 2, 0, 180988, 84072, 3061, 16384⟩
    (by decide) selected_cut_05925

theorem selected_cut_05926 : selected 8 ⟨181046, by decide⟩
    (prefixPartial 13 84073) = some ⟨13, 2, 0, 181046, 84073, 3825, 16384⟩ := by
  decide +kernel

theorem context_13_84073_181046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84073 ⟨181046, by decide⟩ :=
  accepted_of_selected 13 84073 ⟨181046, by decide⟩ ⟨13, 2, 0, 181046, 84073, 3825, 16384⟩
    (by decide) selected_cut_05926

theorem selected_cut_05927 : selected 8 ⟨181083, by decide⟩
    (prefixPartial 13 84074) = some ⟨13, 2, 0, 181083, 84074, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_84074_181083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84074 ⟨181083, by decide⟩ :=
  accepted_of_selected 13 84074 ⟨181083, by decide⟩ ⟨13, 2, 0, 181083, 84074, 2749, 16384⟩
    (by decide) selected_cut_05927

theorem selected_cut_05928 : selected 8 ⟨181096, by decide⟩
    (prefixPartial 13 84075) = some ⟨13, 2, 0, 181096, 84075, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_84075_181096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84075 ⟨181096, by decide⟩ :=
  accepted_of_selected 13 84075 ⟨181096, by decide⟩ ⟨13, 2, 0, 181096, 84075, 1201, 16384⟩
    (by decide) selected_cut_05928

theorem unmarked_context_12_21018_181097 : frontier 9 ⟨181097, by decide⟩
    (prefixCache 12 21018) (prefixPartial 12 21018) = false := by
  decide +kernel

theorem node_context_12_21018_181097 : EJMOriginalGlobalDAGData.nodes 9 ⟨181097, by decide⟩ =
    .split (coordinate 12) (![⟨180988, by decide⟩,⟨181046, by decide⟩,⟨181083, by decide⟩,⟨181096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21018_181097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21018 ⟨181097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21018
    ⟨181097, by decide⟩ (by decide) (![⟨180988, by decide⟩,⟨181046, by decide⟩,⟨181083, by decide⟩,⟨181096, by decide⟩]) unmarked_context_12_21018_181097 node_context_12_21018_181097
  intro a
  fin_cases a
  · exact context_13_84072_180988
  · exact context_13_84073_181046
  · exact context_13_84074_181083
  · exact context_13_84075_181096

theorem selected_cut_05929 : selected 8 ⟨181130, by decide⟩
    (prefixPartial 13 84076) = some ⟨13, 2, 0, 181130, 84076, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_84076_181130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84076 ⟨181130, by decide⟩ :=
  accepted_of_selected 13 84076 ⟨181130, by decide⟩ ⟨13, 2, 0, 181130, 84076, 1997, 16384⟩
    (by decide) selected_cut_05929

theorem selected_cut_05930 : selected 8 ⟨181168, by decide⟩
    (prefixPartial 13 84077) = some ⟨13, 2, 0, 181168, 84077, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_84077_181168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84077 ⟨181168, by decide⟩ :=
  accepted_of_selected 13 84077 ⟨181168, by decide⟩ ⟨13, 2, 0, 181168, 84077, 2405, 16384⟩
    (by decide) selected_cut_05930

theorem selected_cut_05931 : selected 8 ⟨181190, by decide⟩
    (prefixPartial 13 84078) = some ⟨13, 2, 0, 181190, 84078, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_84078_181190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84078 ⟨181190, by decide⟩ :=
  accepted_of_selected 13 84078 ⟨181190, by decide⟩ ⟨13, 2, 0, 181190, 84078, 1633, 16384⟩
    (by decide) selected_cut_05931

theorem selected_cut_05932 : selected 8 ⟨181199, by decide⟩
    (prefixPartial 13 84079) = some ⟨13, 2, 0, 181199, 84079, 881, 16384⟩ := by
  decide +kernel

theorem context_13_84079_181199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84079 ⟨181199, by decide⟩ :=
  accepted_of_selected 13 84079 ⟨181199, by decide⟩ ⟨13, 2, 0, 181199, 84079, 881, 16384⟩
    (by decide) selected_cut_05932

theorem unmarked_context_12_21019_181200 : frontier 9 ⟨181200, by decide⟩
    (prefixCache 12 21019) (prefixPartial 12 21019) = false := by
  decide +kernel

theorem node_context_12_21019_181200 : EJMOriginalGlobalDAGData.nodes 9 ⟨181200, by decide⟩ =
    .split (coordinate 12) (![⟨181130, by decide⟩,⟨181168, by decide⟩,⟨181190, by decide⟩,⟨181199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21019_181200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21019 ⟨181200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21019
    ⟨181200, by decide⟩ (by decide) (![⟨181130, by decide⟩,⟨181168, by decide⟩,⟨181190, by decide⟩,⟨181199, by decide⟩]) unmarked_context_12_21019_181200 node_context_12_21019_181200
  intro a
  fin_cases a
  · exact context_13_84076_181130
  · exact context_13_84077_181168
  · exact context_13_84078_181190
  · exact context_13_84079_181199

theorem unmarked_context_11_5254_181201 : frontier 10 ⟨181201, by decide⟩
    (prefixCache 11 5254) (prefixPartial 11 5254) = false := by
  decide +kernel

theorem node_context_11_5254_181201 : EJMOriginalGlobalDAGData.nodes 10 ⟨181201, by decide⟩ =
    .split (coordinate 11) (![⟨180855, by decide⟩,⟨180946, by decide⟩,⟨181097, by decide⟩,⟨181200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5254_181201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5254 ⟨181201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5254
    ⟨181201, by decide⟩ (by decide) (![⟨180855, by decide⟩,⟨180946, by decide⟩,⟨181097, by decide⟩,⟨181200, by decide⟩]) unmarked_context_11_5254_181201 node_context_11_5254_181201
  intro a
  fin_cases a
  · exact context_12_21016_180855
  · exact context_12_21017_180946
  · exact context_12_21018_181097
  · exact context_12_21019_181200

theorem selected_cut_05933 : selected 8 ⟨181225, by decide⟩
    (prefixPartial 13 84080) = some ⟨13, 2, 0, 181225, 84080, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_84080_181225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84080 ⟨181225, by decide⟩ :=
  accepted_of_selected 13 84080 ⟨181225, by decide⟩ ⟨13, 2, 0, 181225, 84080, 1549, 16384⟩
    (by decide) selected_cut_05933

theorem selected_cut_05934 : selected 8 ⟨181252, by decide⟩
    (prefixPartial 13 84081) = some ⟨13, 2, 0, 181252, 84081, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_84081_181252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84081 ⟨181252, by decide⟩ :=
  accepted_of_selected 13 84081 ⟨181252, by decide⟩ ⟨13, 2, 0, 181252, 84081, 2009, 16384⟩
    (by decide) selected_cut_05934

theorem selected_cut_05935 : selected 8 ⟨181271, by decide⟩
    (prefixPartial 13 84082) = some ⟨13, 2, 0, 181271, 84082, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_84082_181271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84082 ⟨181271, by decide⟩ :=
  accepted_of_selected 13 84082 ⟨181271, by decide⟩ ⟨13, 2, 0, 181271, 84082, 1633, 16384⟩
    (by decide) selected_cut_05935

theorem selected_cut_05936 : selected 8 ⟨181280, by decide⟩
    (prefixPartial 13 84083) = some ⟨13, 2, 0, 181280, 84083, 793, 16384⟩ := by
  decide +kernel

theorem context_13_84083_181280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84083 ⟨181280, by decide⟩ :=
  accepted_of_selected 13 84083 ⟨181280, by decide⟩ ⟨13, 2, 0, 181280, 84083, 793, 16384⟩
    (by decide) selected_cut_05936

theorem unmarked_context_12_21020_181281 : frontier 9 ⟨181281, by decide⟩
    (prefixCache 12 21020) (prefixPartial 12 21020) = false := by
  decide +kernel

theorem node_context_12_21020_181281 : EJMOriginalGlobalDAGData.nodes 9 ⟨181281, by decide⟩ =
    .split (coordinate 12) (![⟨181225, by decide⟩,⟨181252, by decide⟩,⟨181271, by decide⟩,⟨181280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21020_181281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21020 ⟨181281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21020
    ⟨181281, by decide⟩ (by decide) (![⟨181225, by decide⟩,⟨181252, by decide⟩,⟨181271, by decide⟩,⟨181280, by decide⟩]) unmarked_context_12_21020_181281 node_context_12_21020_181281
  intro a
  fin_cases a
  · exact context_13_84080_181225
  · exact context_13_84081_181252
  · exact context_13_84082_181271
  · exact context_13_84083_181280

theorem selected_cut_05937 : selected 8 ⟨181305, by decide⟩
    (prefixPartial 13 84084) = some ⟨13, 2, 0, 181305, 84084, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_84084_181305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84084 ⟨181305, by decide⟩ :=
  accepted_of_selected 13 84084 ⟨181305, by decide⟩ ⟨13, 2, 0, 181305, 84084, 1477, 16384⟩
    (by decide) selected_cut_05937

theorem selected_cut_05938 : selected 8 ⟨181332, by decide⟩
    (prefixPartial 13 84085) = some ⟨13, 2, 0, 181332, 84085, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_84085_181332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84085 ⟨181332, by decide⟩ :=
  accepted_of_selected 13 84085 ⟨181332, by decide⟩ ⟨13, 2, 0, 181332, 84085, 2181, 16384⟩
    (by decide) selected_cut_05938

theorem selected_cut_05939 : selected 8 ⟨181356, by decide⟩
    (prefixPartial 13 84086) = some ⟨13, 2, 0, 181356, 84086, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_84086_181356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84086 ⟨181356, by decide⟩ :=
  accepted_of_selected 13 84086 ⟨181356, by decide⟩ ⟨13, 2, 0, 181356, 84086, 1889, 16384⟩
    (by decide) selected_cut_05939

theorem selected_cut_05940 : selected 8 ⟨181366, by decide⟩
    (prefixPartial 13 84087) = some ⟨13, 2, 0, 181366, 84087, 841, 16384⟩ := by
  decide +kernel

theorem context_13_84087_181366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84087 ⟨181366, by decide⟩ :=
  accepted_of_selected 13 84087 ⟨181366, by decide⟩ ⟨13, 2, 0, 181366, 84087, 841, 16384⟩
    (by decide) selected_cut_05940

theorem unmarked_context_12_21021_181367 : frontier 9 ⟨181367, by decide⟩
    (prefixCache 12 21021) (prefixPartial 12 21021) = false := by
  decide +kernel

theorem node_context_12_21021_181367 : EJMOriginalGlobalDAGData.nodes 9 ⟨181367, by decide⟩ =
    .split (coordinate 12) (![⟨181305, by decide⟩,⟨181332, by decide⟩,⟨181356, by decide⟩,⟨181366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21021_181367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21021 ⟨181367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21021
    ⟨181367, by decide⟩ (by decide) (![⟨181305, by decide⟩,⟨181332, by decide⟩,⟨181356, by decide⟩,⟨181366, by decide⟩]) unmarked_context_12_21021_181367 node_context_12_21021_181367
  intro a
  fin_cases a
  · exact context_13_84084_181305
  · exact context_13_84085_181332
  · exact context_13_84086_181356
  · exact context_13_84087_181366

theorem selected_cut_05941 : selected 8 ⟨181394, by decide⟩
    (prefixPartial 13 84088) = some ⟨13, 2, 0, 181394, 84088, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_84088_181394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84088 ⟨181394, by decide⟩ :=
  accepted_of_selected 13 84088 ⟨181394, by decide⟩ ⟨13, 2, 0, 181394, 84088, 1669, 16384⟩
    (by decide) selected_cut_05941

theorem selected_cut_05942 : selected 8 ⟨181426, by decide⟩
    (prefixPartial 13 84089) = some ⟨13, 2, 0, 181426, 84089, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_84089_181426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84089 ⟨181426, by decide⟩ :=
  accepted_of_selected 13 84089 ⟨181426, by decide⟩ ⟨13, 2, 0, 181426, 84089, 2573, 16384⟩
    (by decide) selected_cut_05942

theorem selected_cut_05943 : selected 8 ⟨181452, by decide⟩
    (prefixPartial 13 84090) = some ⟨13, 2, 0, 181452, 84090, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_84090_181452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84090 ⟨181452, by decide⟩ :=
  accepted_of_selected 13 84090 ⟨181452, by decide⟩ ⟨13, 2, 0, 181452, 84090, 1801, 16384⟩
    (by decide) selected_cut_05943

theorem selected_cut_05944 : selected 8 ⟨181461, by decide⟩
    (prefixPartial 13 84091) = some ⟨13, 2, 0, 181461, 84091, 821, 16384⟩ := by
  decide +kernel

theorem context_13_84091_181461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84091 ⟨181461, by decide⟩ :=
  accepted_of_selected 13 84091 ⟨181461, by decide⟩ ⟨13, 2, 0, 181461, 84091, 821, 16384⟩
    (by decide) selected_cut_05944

theorem unmarked_context_12_21022_181462 : frontier 9 ⟨181462, by decide⟩
    (prefixCache 12 21022) (prefixPartial 12 21022) = false := by
  decide +kernel

theorem node_context_12_21022_181462 : EJMOriginalGlobalDAGData.nodes 9 ⟨181462, by decide⟩ =
    .split (coordinate 12) (![⟨181394, by decide⟩,⟨181426, by decide⟩,⟨181452, by decide⟩,⟨181461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21022_181462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21022 ⟨181462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21022
    ⟨181462, by decide⟩ (by decide) (![⟨181394, by decide⟩,⟨181426, by decide⟩,⟨181452, by decide⟩,⟨181461, by decide⟩]) unmarked_context_12_21022_181462 node_context_12_21022_181462
  intro a
  fin_cases a
  · exact context_13_84088_181394
  · exact context_13_84089_181426
  · exact context_13_84090_181452
  · exact context_13_84091_181461

theorem selected_cut_05945 : selected 8 ⟨181488, by decide⟩
    (prefixPartial 13 84092) = some ⟨13, 2, 0, 181488, 84092, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_84092_181488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84092 ⟨181488, by decide⟩ :=
  accepted_of_selected 13 84092 ⟨181488, by decide⟩ ⟨13, 2, 0, 181488, 84092, 1701, 16384⟩
    (by decide) selected_cut_05945

theorem selected_cut_05946 : selected 8 ⟨181517, by decide⟩
    (prefixPartial 13 84093) = some ⟨13, 2, 0, 181517, 84093, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_84093_181517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84093 ⟨181517, by decide⟩ :=
  accepted_of_selected 13 84093 ⟨181517, by decide⟩ ⟨13, 2, 0, 181517, 84093, 2505, 16384⟩
    (by decide) selected_cut_05946

theorem selected_cut_05947 : selected 8 ⟨181538, by decide⟩
    (prefixPartial 13 84094) = some ⟨13, 2, 0, 181538, 84094, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_84094_181538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84094 ⟨181538, by decide⟩ :=
  accepted_of_selected 13 84094 ⟨181538, by decide⟩ ⟨13, 2, 0, 181538, 84094, 1833, 16384⟩
    (by decide) selected_cut_05947

theorem selected_cut_05948 : selected 8 ⟨181546, by decide⟩
    (prefixPartial 13 84095) = some ⟨13, 2, 0, 181546, 84095, 885, 16384⟩ := by
  decide +kernel

theorem context_13_84095_181546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84095 ⟨181546, by decide⟩ :=
  accepted_of_selected 13 84095 ⟨181546, by decide⟩ ⟨13, 2, 0, 181546, 84095, 885, 16384⟩
    (by decide) selected_cut_05948

theorem unmarked_context_12_21023_181547 : frontier 9 ⟨181547, by decide⟩
    (prefixCache 12 21023) (prefixPartial 12 21023) = false := by
  decide +kernel

theorem node_context_12_21023_181547 : EJMOriginalGlobalDAGData.nodes 9 ⟨181547, by decide⟩ =
    .split (coordinate 12) (![⟨181488, by decide⟩,⟨181517, by decide⟩,⟨181538, by decide⟩,⟨181546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21023_181547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21023 ⟨181547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21023
    ⟨181547, by decide⟩ (by decide) (![⟨181488, by decide⟩,⟨181517, by decide⟩,⟨181538, by decide⟩,⟨181546, by decide⟩]) unmarked_context_12_21023_181547 node_context_12_21023_181547
  intro a
  fin_cases a
  · exact context_13_84092_181488
  · exact context_13_84093_181517
  · exact context_13_84094_181538
  · exact context_13_84095_181546

theorem unmarked_context_11_5255_181548 : frontier 10 ⟨181548, by decide⟩
    (prefixCache 11 5255) (prefixPartial 11 5255) = false := by
  decide +kernel

theorem node_context_11_5255_181548 : EJMOriginalGlobalDAGData.nodes 10 ⟨181548, by decide⟩ =
    .split (coordinate 11) (![⟨181281, by decide⟩,⟨181367, by decide⟩,⟨181462, by decide⟩,⟨181547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5255_181548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5255 ⟨181548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5255
    ⟨181548, by decide⟩ (by decide) (![⟨181281, by decide⟩,⟨181367, by decide⟩,⟨181462, by decide⟩,⟨181547, by decide⟩]) unmarked_context_11_5255_181548 node_context_11_5255_181548
  intro a
  fin_cases a
  · exact context_12_21020_181281
  · exact context_12_21021_181367
  · exact context_12_21022_181462
  · exact context_12_21023_181547

theorem unmarked_context_10_1313_181549 : frontier 11 ⟨181549, by decide⟩
    (prefixCache 10 1313) (prefixPartial 10 1313) = false := by
  decide +kernel

theorem node_context_10_1313_181549 : EJMOriginalGlobalDAGData.nodes 11 ⟨181549, by decide⟩ =
    .split (coordinate 10) (![⟨180467, by decide⟩,⟨180774, by decide⟩,⟨181201, by decide⟩,⟨181548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1313_181549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1313 ⟨181549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1313
    ⟨181549, by decide⟩ (by decide) (![⟨180467, by decide⟩,⟨180774, by decide⟩,⟨181201, by decide⟩,⟨181548, by decide⟩]) unmarked_context_10_1313_181549 node_context_10_1313_181549
  intro a
  fin_cases a
  · exact context_11_5252_180467
  · exact context_11_5253_180774
  · exact context_11_5254_181201
  · exact context_11_5255_181548

theorem selected_cut_05949 : selected 9 ⟨181612, by decide⟩
    (prefixPartial 12 21024) = some ⟨12, 2, 0, 181612, 21024, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_21024_181612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21024 ⟨181612, by decide⟩ :=
  accepted_of_selected 12 21024 ⟨181612, by decide⟩ ⟨12, 2, 0, 181612, 21024, 4093, 65536⟩
    (by decide) selected_cut_05949

theorem selected_cut_05950 : selected 8 ⟨181627, by decide⟩
    (prefixPartial 13 84100) = some ⟨13, 2, 0, 181627, 84100, 973, 16384⟩ := by
  decide +kernel

theorem context_13_84100_181627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84100 ⟨181627, by decide⟩ :=
  accepted_of_selected 13 84100 ⟨181627, by decide⟩ ⟨13, 2, 0, 181627, 84100, 973, 16384⟩
    (by decide) selected_cut_05950

theorem selected_cut_05951 : selected 8 ⟨181653, by decide⟩
    (prefixPartial 13 84101) = some ⟨13, 2, 0, 181653, 84101, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_84101_181653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84101 ⟨181653, by decide⟩ :=
  accepted_of_selected 13 84101 ⟨181653, by decide⟩ ⟨13, 2, 0, 181653, 84101, 1733, 16384⟩
    (by decide) selected_cut_05951

theorem selected_cut_05952 : selected 8 ⟨181672, by decide⟩
    (prefixPartial 13 84102) = some ⟨13, 2, 0, 181672, 84102, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_84102_181672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84102 ⟨181672, by decide⟩ :=
  accepted_of_selected 13 84102 ⟨181672, by decide⟩ ⟨13, 2, 0, 181672, 84102, 1237, 16384⟩
    (by decide) selected_cut_05952

theorem selected_cut_05953 : selected 8 ⟨181679, by decide⟩
    (prefixPartial 13 84103) = some ⟨13, 2, 0, 181679, 84103, 677, 16384⟩ := by
  decide +kernel

theorem context_13_84103_181679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84103 ⟨181679, by decide⟩ :=
  accepted_of_selected 13 84103 ⟨181679, by decide⟩ ⟨13, 2, 0, 181679, 84103, 677, 16384⟩
    (by decide) selected_cut_05953

theorem unmarked_context_12_21025_181680 : frontier 9 ⟨181680, by decide⟩
    (prefixCache 12 21025) (prefixPartial 12 21025) = false := by
  decide +kernel

theorem node_context_12_21025_181680 : EJMOriginalGlobalDAGData.nodes 9 ⟨181680, by decide⟩ =
    .split (coordinate 12) (![⟨181627, by decide⟩,⟨181653, by decide⟩,⟨181672, by decide⟩,⟨181679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21025_181680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21025 ⟨181680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21025
    ⟨181680, by decide⟩ (by decide) (![⟨181627, by decide⟩,⟨181653, by decide⟩,⟨181672, by decide⟩,⟨181679, by decide⟩]) unmarked_context_12_21025_181680 node_context_12_21025_181680
  intro a
  fin_cases a
  · exact context_13_84100_181627
  · exact context_13_84101_181653
  · exact context_13_84102_181672
  · exact context_13_84103_181679

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
