/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover373
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35907 : selected 9 ⟨946101, by decide⟩
    (prefixPartial 12 287517) = some ⟨12, 2, 0, 946101, 287517, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_287517_946101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287517 ⟨946101, by decide⟩ :=
  accepted_of_selected 12 287517 ⟨946101, by decide⟩ ⟨12, 2, 0, 946101, 287517, 3357, 65536⟩
    (by decide) selected_cut_35907

theorem selected_cut_35908 : selected 9 ⟨946149, by decide⟩
    (prefixPartial 12 287518) = some ⟨12, 2, 0, 946149, 287518, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_287518_946149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287518 ⟨946149, by decide⟩ :=
  accepted_of_selected 12 287518 ⟨946149, by decide⟩ ⟨12, 2, 0, 946149, 287518, 3341, 65536⟩
    (by decide) selected_cut_35908

theorem selected_cut_35909 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 287519) = some ⟨12, 1, 0, 903806, 287519, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287519_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287519 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 287519 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 287519, 1, 65536⟩
    (by decide) selected_cut_35909

theorem unmarked_context_11_71879_946150 : frontier 10 ⟨946150, by decide⟩
    (prefixCache 11 71879) (prefixPartial 11 71879) = false := by
  decide +kernel

theorem node_context_11_71879_946150 : EJMOriginalGlobalDAGData.nodes 10 ⟨946150, by decide⟩ =
    .split (coordinate 11) (![⟨946046, by decide⟩,⟨946101, by decide⟩,⟨946149, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71879_946150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71879 ⟨946150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71879
    ⟨946150, by decide⟩ (by decide) (![⟨946046, by decide⟩,⟨946101, by decide⟩,⟨946149, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_71879_946150 node_context_11_71879_946150
  intro a
  fin_cases a
  · exact context_12_287516_946046
  · exact context_12_287517_946101
  · exact context_12_287518_946149
  · exact context_12_287519_903806

theorem unmarked_context_10_17969_946151 : frontier 11 ⟨946151, by decide⟩
    (prefixCache 10 17969) (prefixPartial 10 17969) = false := by
  decide +kernel

theorem node_context_10_17969_946151 : EJMOriginalGlobalDAGData.nodes 11 ⟨946151, by decide⟩ =
    .split (coordinate 10) (![⟨945450, by decide⟩,⟨945688, by decide⟩,⟨945986, by decide⟩,⟨946150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17969_946151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17969 ⟨946151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17969
    ⟨946151, by decide⟩ (by decide) (![⟨945450, by decide⟩,⟨945688, by decide⟩,⟨945986, by decide⟩,⟨946150, by decide⟩]) unmarked_context_10_17969_946151 node_context_10_17969_946151
  intro a
  fin_cases a
  · exact context_11_71876_945450
  · exact context_11_71877_945688
  · exact context_11_71878_945986
  · exact context_11_71879_946150

theorem selected_cut_35910 : selected 9 ⟨946212, by decide⟩
    (prefixPartial 12 287520) = some ⟨12, 2, 0, 946212, 287520, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_287520_946212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287520 ⟨946212, by decide⟩ :=
  accepted_of_selected 12 287520 ⟨946212, by decide⟩ ⟨12, 2, 0, 946212, 287520, 3305, 65536⟩
    (by decide) selected_cut_35910

theorem selected_cut_35911 : selected 9 ⟨946260, by decide⟩
    (prefixPartial 12 287521) = some ⟨12, 2, 0, 946260, 287521, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_287521_946260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287521 ⟨946260, by decide⟩ :=
  accepted_of_selected 12 287521 ⟨946260, by decide⟩ ⟨12, 2, 0, 946260, 287521, 2909, 65536⟩
    (by decide) selected_cut_35911

theorem selected_cut_35912 : selected 9 ⟨946313, by decide⟩
    (prefixPartial 12 287522) = some ⟨12, 2, 0, 946313, 287522, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_287522_946313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287522 ⟨946313, by decide⟩ :=
  accepted_of_selected 12 287522 ⟨946313, by decide⟩ ⟨12, 2, 0, 946313, 287522, 3105, 65536⟩
    (by decide) selected_cut_35912

theorem selected_cut_35913 : selected 9 ⟨946367, by decide⟩
    (prefixPartial 12 287523) = some ⟨12, 2, 0, 946367, 287523, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_287523_946367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287523 ⟨946367, by decide⟩ :=
  accepted_of_selected 12 287523 ⟨946367, by decide⟩ ⟨12, 2, 0, 946367, 287523, 3017, 65536⟩
    (by decide) selected_cut_35913

theorem unmarked_context_11_71880_946368 : frontier 10 ⟨946368, by decide⟩
    (prefixCache 11 71880) (prefixPartial 11 71880) = false := by
  decide +kernel

theorem node_context_11_71880_946368 : EJMOriginalGlobalDAGData.nodes 10 ⟨946368, by decide⟩ =
    .split (coordinate 11) (![⟨946212, by decide⟩,⟨946260, by decide⟩,⟨946313, by decide⟩,⟨946367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71880_946368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71880 ⟨946368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71880
    ⟨946368, by decide⟩ (by decide) (![⟨946212, by decide⟩,⟨946260, by decide⟩,⟨946313, by decide⟩,⟨946367, by decide⟩]) unmarked_context_11_71880_946368 node_context_11_71880_946368
  intro a
  fin_cases a
  · exact context_12_287520_946212
  · exact context_12_287521_946260
  · exact context_12_287522_946313
  · exact context_12_287523_946367

theorem selected_cut_35914 : selected 9 ⟨946431, by decide⟩
    (prefixPartial 12 287524) = some ⟨12, 2, 0, 946431, 287524, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_287524_946431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287524 ⟨946431, by decide⟩ :=
  accepted_of_selected 12 287524 ⟨946431, by decide⟩ ⟨12, 2, 0, 946431, 287524, 3421, 65536⟩
    (by decide) selected_cut_35914

theorem selected_cut_35915 : selected 9 ⟨946475, by decide⟩
    (prefixPartial 12 287525) = some ⟨12, 2, 0, 946475, 287525, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_287525_946475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287525 ⟨946475, by decide⟩ :=
  accepted_of_selected 12 287525 ⟨946475, by decide⟩ ⟨12, 2, 0, 946475, 287525, 2917, 65536⟩
    (by decide) selected_cut_35915

theorem selected_cut_35916 : selected 9 ⟨946516, by decide⟩
    (prefixPartial 12 287526) = some ⟨12, 2, 0, 946516, 287526, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_287526_946516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287526 ⟨946516, by decide⟩ :=
  accepted_of_selected 12 287526 ⟨946516, by decide⟩ ⟨12, 2, 0, 946516, 287526, 2989, 65536⟩
    (by decide) selected_cut_35916

theorem selected_cut_35917 : selected 9 ⟨946560, by decide⟩
    (prefixPartial 12 287527) = some ⟨12, 2, 0, 946560, 287527, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_287527_946560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287527 ⟨946560, by decide⟩ :=
  accepted_of_selected 12 287527 ⟨946560, by decide⟩ ⟨12, 2, 0, 946560, 287527, 3025, 65536⟩
    (by decide) selected_cut_35917

theorem unmarked_context_11_71881_946561 : frontier 10 ⟨946561, by decide⟩
    (prefixCache 11 71881) (prefixPartial 11 71881) = false := by
  decide +kernel

theorem node_context_11_71881_946561 : EJMOriginalGlobalDAGData.nodes 10 ⟨946561, by decide⟩ =
    .split (coordinate 11) (![⟨946431, by decide⟩,⟨946475, by decide⟩,⟨946516, by decide⟩,⟨946560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71881_946561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71881 ⟨946561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71881
    ⟨946561, by decide⟩ (by decide) (![⟨946431, by decide⟩,⟨946475, by decide⟩,⟨946516, by decide⟩,⟨946560, by decide⟩]) unmarked_context_11_71881_946561 node_context_11_71881_946561
  intro a
  fin_cases a
  · exact context_12_287524_946431
  · exact context_12_287525_946475
  · exact context_12_287526_946516
  · exact context_12_287527_946560

theorem selected_cut_35918 : selected 9 ⟨946634, by decide⟩
    (prefixPartial 12 287528) = some ⟨12, 2, 0, 946634, 287528, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_287528_946634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287528 ⟨946634, by decide⟩ :=
  accepted_of_selected 12 287528 ⟨946634, by decide⟩ ⟨12, 2, 0, 946634, 287528, 3897, 65536⟩
    (by decide) selected_cut_35918

theorem selected_cut_35919 : selected 9 ⟨946691, by decide⟩
    (prefixPartial 12 287529) = some ⟨12, 2, 0, 946691, 287529, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_287529_946691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287529 ⟨946691, by decide⟩ :=
  accepted_of_selected 12 287529 ⟨946691, by decide⟩ ⟨12, 2, 0, 946691, 287529, 3277, 65536⟩
    (by decide) selected_cut_35919

theorem selected_cut_35920 : selected 9 ⟨946735, by decide⟩
    (prefixPartial 12 287530) = some ⟨12, 2, 0, 946735, 287530, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_287530_946735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287530 ⟨946735, by decide⟩ :=
  accepted_of_selected 12 287530 ⟨946735, by decide⟩ ⟨12, 2, 0, 946735, 287530, 3017, 65536⟩
    (by decide) selected_cut_35920

theorem selected_cut_35921 : selected 9 ⟨946788, by decide⟩
    (prefixPartial 12 287531) = some ⟨12, 2, 0, 946788, 287531, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_287531_946788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287531 ⟨946788, by decide⟩ :=
  accepted_of_selected 12 287531 ⟨946788, by decide⟩ ⟨12, 2, 0, 946788, 287531, 3309, 65536⟩
    (by decide) selected_cut_35921

theorem unmarked_context_11_71882_946789 : frontier 10 ⟨946789, by decide⟩
    (prefixCache 11 71882) (prefixPartial 11 71882) = false := by
  decide +kernel

theorem node_context_11_71882_946789 : EJMOriginalGlobalDAGData.nodes 10 ⟨946789, by decide⟩ =
    .split (coordinate 11) (![⟨946634, by decide⟩,⟨946691, by decide⟩,⟨946735, by decide⟩,⟨946788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71882_946789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71882 ⟨946789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71882
    ⟨946789, by decide⟩ (by decide) (![⟨946634, by decide⟩,⟨946691, by decide⟩,⟨946735, by decide⟩,⟨946788, by decide⟩]) unmarked_context_11_71882_946789 node_context_11_71882_946789
  intro a
  fin_cases a
  · exact context_12_287528_946634
  · exact context_12_287529_946691
  · exact context_12_287530_946735
  · exact context_12_287531_946788

theorem selected_cut_35922 : selected 9 ⟨946855, by decide⟩
    (prefixPartial 12 287532) = some ⟨12, 2, 0, 946855, 287532, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_287532_946855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287532 ⟨946855, by decide⟩ :=
  accepted_of_selected 12 287532 ⟨946855, by decide⟩ ⟨12, 2, 0, 946855, 287532, 3413, 65536⟩
    (by decide) selected_cut_35922

theorem selected_cut_35923 : selected 9 ⟨946907, by decide⟩
    (prefixPartial 12 287533) = some ⟨12, 2, 0, 946907, 287533, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_287533_946907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287533 ⟨946907, by decide⟩ :=
  accepted_of_selected 12 287533 ⟨946907, by decide⟩ ⟨12, 2, 0, 946907, 287533, 3041, 65536⟩
    (by decide) selected_cut_35923

theorem selected_cut_35924 : selected 9 ⟨946964, by decide⟩
    (prefixPartial 12 287534) = some ⟨12, 2, 0, 946964, 287534, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_287534_946964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287534 ⟨946964, by decide⟩ :=
  accepted_of_selected 12 287534 ⟨946964, by decide⟩ ⟨12, 2, 0, 946964, 287534, 3261, 65536⟩
    (by decide) selected_cut_35924

theorem selected_cut_35925 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 287535) = some ⟨12, 1, 0, 903806, 287535, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287535_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287535 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 287535 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 287535, 1, 65536⟩
    (by decide) selected_cut_35925

theorem unmarked_context_11_71883_946965 : frontier 10 ⟨946965, by decide⟩
    (prefixCache 11 71883) (prefixPartial 11 71883) = false := by
  decide +kernel

theorem node_context_11_71883_946965 : EJMOriginalGlobalDAGData.nodes 10 ⟨946965, by decide⟩ =
    .split (coordinate 11) (![⟨946855, by decide⟩,⟨946907, by decide⟩,⟨946964, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71883_946965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71883 ⟨946965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71883
    ⟨946965, by decide⟩ (by decide) (![⟨946855, by decide⟩,⟨946907, by decide⟩,⟨946964, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_71883_946965 node_context_11_71883_946965
  intro a
  fin_cases a
  · exact context_12_287532_946855
  · exact context_12_287533_946907
  · exact context_12_287534_946964
  · exact context_12_287535_903806

theorem unmarked_context_10_17970_946966 : frontier 11 ⟨946966, by decide⟩
    (prefixCache 10 17970) (prefixPartial 10 17970) = false := by
  decide +kernel

theorem node_context_10_17970_946966 : EJMOriginalGlobalDAGData.nodes 11 ⟨946966, by decide⟩ =
    .split (coordinate 10) (![⟨946368, by decide⟩,⟨946561, by decide⟩,⟨946789, by decide⟩,⟨946965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17970_946966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17970 ⟨946966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17970
    ⟨946966, by decide⟩ (by decide) (![⟨946368, by decide⟩,⟨946561, by decide⟩,⟨946789, by decide⟩,⟨946965, by decide⟩]) unmarked_context_10_17970_946966 node_context_10_17970_946966
  intro a
  fin_cases a
  · exact context_11_71880_946368
  · exact context_11_71881_946561
  · exact context_11_71882_946789
  · exact context_11_71883_946965

theorem selected_cut_35926 : selected 9 ⟨947021, by decide⟩
    (prefixPartial 12 287536) = some ⟨12, 2, 0, 947021, 287536, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_287536_947021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287536 ⟨947021, by decide⟩ :=
  accepted_of_selected 12 287536 ⟨947021, by decide⟩ ⟨12, 2, 0, 947021, 287536, 3125, 65536⟩
    (by decide) selected_cut_35926

theorem selected_cut_35927 : selected 9 ⟨947064, by decide⟩
    (prefixPartial 12 287537) = some ⟨12, 2, 0, 947064, 287537, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_287537_947064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287537 ⟨947064, by decide⟩ :=
  accepted_of_selected 12 287537 ⟨947064, by decide⟩ ⟨12, 2, 0, 947064, 287537, 2893, 65536⟩
    (by decide) selected_cut_35927

theorem selected_cut_35928 : selected 9 ⟨947104, by decide⟩
    (prefixPartial 12 287538) = some ⟨12, 2, 0, 947104, 287538, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_287538_947104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287538 ⟨947104, by decide⟩ :=
  accepted_of_selected 12 287538 ⟨947104, by decide⟩ ⟨12, 2, 0, 947104, 287538, 2789, 65536⟩
    (by decide) selected_cut_35928

theorem selected_cut_35929 : selected 9 ⟨947154, by decide⟩
    (prefixPartial 12 287539) = some ⟨12, 2, 0, 947154, 287539, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_287539_947154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287539 ⟨947154, by decide⟩ :=
  accepted_of_selected 12 287539 ⟨947154, by decide⟩ ⟨12, 2, 0, 947154, 287539, 3001, 65536⟩
    (by decide) selected_cut_35929

theorem unmarked_context_11_71884_947155 : frontier 10 ⟨947155, by decide⟩
    (prefixCache 11 71884) (prefixPartial 11 71884) = false := by
  decide +kernel

theorem node_context_11_71884_947155 : EJMOriginalGlobalDAGData.nodes 10 ⟨947155, by decide⟩ =
    .split (coordinate 11) (![⟨947021, by decide⟩,⟨947064, by decide⟩,⟨947104, by decide⟩,⟨947154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71884_947155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71884 ⟨947155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71884
    ⟨947155, by decide⟩ (by decide) (![⟨947021, by decide⟩,⟨947064, by decide⟩,⟨947104, by decide⟩,⟨947154, by decide⟩]) unmarked_context_11_71884_947155 node_context_11_71884_947155
  intro a
  fin_cases a
  · exact context_12_287536_947021
  · exact context_12_287537_947064
  · exact context_12_287538_947104
  · exact context_12_287539_947154

theorem selected_cut_35930 : selected 9 ⟨947221, by decide⟩
    (prefixPartial 12 287540) = some ⟨12, 2, 0, 947221, 287540, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_287540_947221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287540 ⟨947221, by decide⟩ :=
  accepted_of_selected 12 287540 ⟨947221, by decide⟩ ⟨12, 2, 0, 947221, 287540, 3117, 65536⟩
    (by decide) selected_cut_35930

theorem selected_cut_35931 : selected 9 ⟨947266, by decide⟩
    (prefixPartial 12 287541) = some ⟨12, 2, 0, 947266, 287541, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_287541_947266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287541 ⟨947266, by decide⟩ :=
  accepted_of_selected 12 287541 ⟨947266, by decide⟩ ⟨12, 2, 0, 947266, 287541, 2841, 65536⟩
    (by decide) selected_cut_35931

theorem selected_cut_35932 : selected 9 ⟨947305, by decide⟩
    (prefixPartial 12 287542) = some ⟨12, 2, 0, 947305, 287542, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_287542_947305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287542 ⟨947305, by decide⟩ :=
  accepted_of_selected 12 287542 ⟨947305, by decide⟩ ⟨12, 2, 0, 947305, 287542, 2649, 65536⟩
    (by decide) selected_cut_35932

theorem selected_cut_35933 : selected 9 ⟨947350, by decide⟩
    (prefixPartial 12 287543) = some ⟨12, 2, 0, 947350, 287543, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_287543_947350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287543 ⟨947350, by decide⟩ :=
  accepted_of_selected 12 287543 ⟨947350, by decide⟩ ⟨12, 2, 0, 947350, 287543, 2881, 65536⟩
    (by decide) selected_cut_35933

theorem unmarked_context_11_71885_947351 : frontier 10 ⟨947351, by decide⟩
    (prefixCache 11 71885) (prefixPartial 11 71885) = false := by
  decide +kernel

theorem node_context_11_71885_947351 : EJMOriginalGlobalDAGData.nodes 10 ⟨947351, by decide⟩ =
    .split (coordinate 11) (![⟨947221, by decide⟩,⟨947266, by decide⟩,⟨947305, by decide⟩,⟨947350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71885_947351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71885 ⟨947351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71885
    ⟨947351, by decide⟩ (by decide) (![⟨947221, by decide⟩,⟨947266, by decide⟩,⟨947305, by decide⟩,⟨947350, by decide⟩]) unmarked_context_11_71885_947351 node_context_11_71885_947351
  intro a
  fin_cases a
  · exact context_12_287540_947221
  · exact context_12_287541_947266
  · exact context_12_287542_947305
  · exact context_12_287543_947350

theorem selected_cut_35934 : selected 9 ⟨947436, by decide⟩
    (prefixPartial 12 287544) = some ⟨12, 2, 0, 947436, 287544, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_287544_947436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287544 ⟨947436, by decide⟩ :=
  accepted_of_selected 12 287544 ⟨947436, by decide⟩ ⟨12, 2, 0, 947436, 287544, 3825, 65536⟩
    (by decide) selected_cut_35934

theorem selected_cut_35935 : selected 9 ⟨947488, by decide⟩
    (prefixPartial 12 287545) = some ⟨12, 2, 0, 947488, 287545, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_287545_947488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287545 ⟨947488, by decide⟩ :=
  accepted_of_selected 12 287545 ⟨947488, by decide⟩ ⟨12, 2, 0, 947488, 287545, 3289, 65536⟩
    (by decide) selected_cut_35935

theorem selected_cut_35936 : selected 9 ⟨947538, by decide⟩
    (prefixPartial 12 287546) = some ⟨12, 2, 0, 947538, 287546, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_287546_947538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287546 ⟨947538, by decide⟩ :=
  accepted_of_selected 12 287546 ⟨947538, by decide⟩ ⟨12, 2, 0, 947538, 287546, 2853, 65536⟩
    (by decide) selected_cut_35936

theorem selected_cut_35937 : selected 9 ⟨947601, by decide⟩
    (prefixPartial 12 287547) = some ⟨12, 2, 0, 947601, 287547, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_287547_947601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287547 ⟨947601, by decide⟩ :=
  accepted_of_selected 12 287547 ⟨947601, by decide⟩ ⟨12, 2, 0, 947601, 287547, 3249, 65536⟩
    (by decide) selected_cut_35937

theorem unmarked_context_11_71886_947602 : frontier 10 ⟨947602, by decide⟩
    (prefixCache 11 71886) (prefixPartial 11 71886) = false := by
  decide +kernel

theorem node_context_11_71886_947602 : EJMOriginalGlobalDAGData.nodes 10 ⟨947602, by decide⟩ =
    .split (coordinate 11) (![⟨947436, by decide⟩,⟨947488, by decide⟩,⟨947538, by decide⟩,⟨947601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71886_947602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71886 ⟨947602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71886
    ⟨947602, by decide⟩ (by decide) (![⟨947436, by decide⟩,⟨947488, by decide⟩,⟨947538, by decide⟩,⟨947601, by decide⟩]) unmarked_context_11_71886_947602 node_context_11_71886_947602
  intro a
  fin_cases a
  · exact context_12_287544_947436
  · exact context_12_287545_947488
  · exact context_12_287546_947538
  · exact context_12_287547_947601

theorem selected_cut_35938 : selected 9 ⟨947648, by decide⟩
    (prefixPartial 12 287548) = some ⟨12, 2, 0, 947648, 287548, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_287548_947648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287548 ⟨947648, by decide⟩ :=
  accepted_of_selected 12 287548 ⟨947648, by decide⟩ ⟨12, 2, 0, 947648, 287548, 2873, 65536⟩
    (by decide) selected_cut_35938

theorem selected_cut_35939 : selected 9 ⟨947687, by decide⟩
    (prefixPartial 12 287549) = some ⟨12, 2, 0, 947687, 287549, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_287549_947687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287549 ⟨947687, by decide⟩ :=
  accepted_of_selected 12 287549 ⟨947687, by decide⟩ ⟨12, 2, 0, 947687, 287549, 2633, 65536⟩
    (by decide) selected_cut_35939

theorem selected_cut_35940 : selected 9 ⟨947725, by decide⟩
    (prefixPartial 12 287550) = some ⟨12, 2, 0, 947725, 287550, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_287550_947725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287550 ⟨947725, by decide⟩ :=
  accepted_of_selected 12 287550 ⟨947725, by decide⟩ ⟨12, 2, 0, 947725, 287550, 2597, 65536⟩
    (by decide) selected_cut_35940

theorem selected_cut_35941 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 287551) = some ⟨12, 1, 0, 429285, 287551, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287551_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287551 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 287551 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 287551, 1, 65536⟩
    (by decide) selected_cut_35941

theorem unmarked_context_11_71887_947726 : frontier 10 ⟨947726, by decide⟩
    (prefixCache 11 71887) (prefixPartial 11 71887) = false := by
  decide +kernel

theorem node_context_11_71887_947726 : EJMOriginalGlobalDAGData.nodes 10 ⟨947726, by decide⟩ =
    .split (coordinate 11) (![⟨947648, by decide⟩,⟨947687, by decide⟩,⟨947725, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71887_947726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71887 ⟨947726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71887
    ⟨947726, by decide⟩ (by decide) (![⟨947648, by decide⟩,⟨947687, by decide⟩,⟨947725, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_71887_947726 node_context_11_71887_947726
  intro a
  fin_cases a
  · exact context_12_287548_947648
  · exact context_12_287549_947687
  · exact context_12_287550_947725
  · exact context_12_287551_429285

theorem unmarked_context_10_17971_947727 : frontier 11 ⟨947727, by decide⟩
    (prefixCache 10 17971) (prefixPartial 10 17971) = false := by
  decide +kernel

theorem node_context_10_17971_947727 : EJMOriginalGlobalDAGData.nodes 11 ⟨947727, by decide⟩ =
    .split (coordinate 10) (![⟨947155, by decide⟩,⟨947351, by decide⟩,⟨947602, by decide⟩,⟨947726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17971_947727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17971 ⟨947727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17971
    ⟨947727, by decide⟩ (by decide) (![⟨947155, by decide⟩,⟨947351, by decide⟩,⟨947602, by decide⟩,⟨947726, by decide⟩]) unmarked_context_10_17971_947727 node_context_10_17971_947727
  intro a
  fin_cases a
  · exact context_11_71884_947155
  · exact context_11_71885_947351
  · exact context_11_71886_947602
  · exact context_11_71887_947726

theorem unmarked_context_9_4492_947728 : frontier 12 ⟨947728, by decide⟩
    (prefixCache 9 4492) (prefixPartial 9 4492) = false := by
  decide +kernel

theorem node_context_9_4492_947728 : EJMOriginalGlobalDAGData.nodes 12 ⟨947728, by decide⟩ =
    .split (coordinate 9) (![⟨945226, by decide⟩,⟨946151, by decide⟩,⟨946966, by decide⟩,⟨947727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4492_947728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4492 ⟨947728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4492
    ⟨947728, by decide⟩ (by decide) (![⟨945226, by decide⟩,⟨946151, by decide⟩,⟨946966, by decide⟩,⟨947727, by decide⟩]) unmarked_context_9_4492_947728 node_context_9_4492_947728
  intro a
  fin_cases a
  · exact context_10_17968_945226
  · exact context_10_17969_946151
  · exact context_10_17970_946966
  · exact context_10_17971_947727

theorem selected_cut_35942 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71888) = some ⟨11, 1, 0, 907917, 71888, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71888_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71888 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71888 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71888, 1, 262144⟩
    (by decide) selected_cut_35942

theorem selected_cut_35943 : selected 9 ⟨947764, by decide⟩
    (prefixPartial 12 287556) = some ⟨12, 2, 0, 947764, 287556, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_287556_947764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287556 ⟨947764, by decide⟩ :=
  accepted_of_selected 12 287556 ⟨947764, by decide⟩ ⟨12, 2, 0, 947764, 287556, 2257, 65536⟩
    (by decide) selected_cut_35943

theorem selected_cut_35944 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287557) = some ⟨12, 1, 0, 896706, 287557, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287557_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287557 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287557 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287557, 1, 65536⟩
    (by decide) selected_cut_35944

theorem selected_cut_35945 : selected 9 ⟨947795, by decide⟩
    (prefixPartial 12 287558) = some ⟨12, 2, 0, 947795, 287558, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_287558_947795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287558 ⟨947795, by decide⟩ :=
  accepted_of_selected 12 287558 ⟨947795, by decide⟩ ⟨12, 2, 0, 947795, 287558, 2093, 65536⟩
    (by decide) selected_cut_35945

theorem selected_cut_35946 : selected 9 ⟨947833, by decide⟩
    (prefixPartial 12 287559) = some ⟨12, 2, 0, 947833, 287559, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_287559_947833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287559 ⟨947833, by decide⟩ :=
  accepted_of_selected 12 287559 ⟨947833, by decide⟩ ⟨12, 2, 0, 947833, 287559, 2153, 65536⟩
    (by decide) selected_cut_35946

theorem unmarked_context_11_71889_947834 : frontier 10 ⟨947834, by decide⟩
    (prefixCache 11 71889) (prefixPartial 11 71889) = false := by
  decide +kernel

theorem node_context_11_71889_947834 : EJMOriginalGlobalDAGData.nodes 10 ⟨947834, by decide⟩ =
    .split (coordinate 11) (![⟨947764, by decide⟩,⟨896706, by decide⟩,⟨947795, by decide⟩,⟨947833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71889_947834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71889 ⟨947834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71889
    ⟨947834, by decide⟩ (by decide) (![⟨947764, by decide⟩,⟨896706, by decide⟩,⟨947795, by decide⟩,⟨947833, by decide⟩]) unmarked_context_11_71889_947834 node_context_11_71889_947834
  intro a
  fin_cases a
  · exact context_12_287556_947764
  · exact context_12_287557_896706
  · exact context_12_287558_947795
  · exact context_12_287559_947833

theorem selected_cut_35947 : selected 9 ⟨947874, by decide⟩
    (prefixPartial 12 287560) = some ⟨12, 2, 0, 947874, 287560, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_287560_947874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287560 ⟨947874, by decide⟩ :=
  accepted_of_selected 12 287560 ⟨947874, by decide⟩ ⟨12, 2, 0, 947874, 287560, 2705, 65536⟩
    (by decide) selected_cut_35947

theorem selected_cut_35948 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287561) = some ⟨12, 1, 0, 896706, 287561, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287561_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287561 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287561 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287561, 1, 65536⟩
    (by decide) selected_cut_35948

theorem selected_cut_35949 : selected 9 ⟨947909, by decide⟩
    (prefixPartial 12 287562) = some ⟨12, 2, 0, 947909, 287562, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_287562_947909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287562 ⟨947909, by decide⟩ :=
  accepted_of_selected 12 287562 ⟨947909, by decide⟩ ⟨12, 2, 0, 947909, 287562, 2297, 65536⟩
    (by decide) selected_cut_35949

theorem selected_cut_35950 : selected 9 ⟨947953, by decide⟩
    (prefixPartial 12 287563) = some ⟨12, 2, 0, 947953, 287563, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_287563_947953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287563 ⟨947953, by decide⟩ :=
  accepted_of_selected 12 287563 ⟨947953, by decide⟩ ⟨12, 2, 0, 947953, 287563, 2593, 65536⟩
    (by decide) selected_cut_35950

theorem unmarked_context_11_71890_947954 : frontier 10 ⟨947954, by decide⟩
    (prefixCache 11 71890) (prefixPartial 11 71890) = false := by
  decide +kernel

theorem node_context_11_71890_947954 : EJMOriginalGlobalDAGData.nodes 10 ⟨947954, by decide⟩ =
    .split (coordinate 11) (![⟨947874, by decide⟩,⟨896706, by decide⟩,⟨947909, by decide⟩,⟨947953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71890_947954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71890 ⟨947954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71890
    ⟨947954, by decide⟩ (by decide) (![⟨947874, by decide⟩,⟨896706, by decide⟩,⟨947909, by decide⟩,⟨947953, by decide⟩]) unmarked_context_11_71890_947954 node_context_11_71890_947954
  intro a
  fin_cases a
  · exact context_12_287560_947874
  · exact context_12_287561_896706
  · exact context_12_287562_947909
  · exact context_12_287563_947953

theorem selected_cut_35951 : selected 9 ⟨947983, by decide⟩
    (prefixPartial 12 287564) = some ⟨12, 2, 0, 947983, 287564, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_287564_947983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287564 ⟨947983, by decide⟩ :=
  accepted_of_selected 12 287564 ⟨947983, by decide⟩ ⟨12, 2, 0, 947983, 287564, 2197, 65536⟩
    (by decide) selected_cut_35951

theorem selected_cut_35952 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287565) = some ⟨12, 1, 0, 896706, 287565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287565_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287565 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287565 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287565, 1, 65536⟩
    (by decide) selected_cut_35952

theorem selected_cut_35953 : selected 9 ⟨948020, by decide⟩
    (prefixPartial 12 287566) = some ⟨12, 2, 0, 948020, 287566, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_287566_948020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287566 ⟨948020, by decide⟩ :=
  accepted_of_selected 12 287566 ⟨948020, by decide⟩ ⟨12, 2, 0, 948020, 287566, 2085, 65536⟩
    (by decide) selected_cut_35953

theorem selected_cut_35954 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 287567) = some ⟨12, 1, 0, 903806, 287567, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287567_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287567 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 287567 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 287567, 1, 65536⟩
    (by decide) selected_cut_35954

theorem unmarked_context_11_71891_948021 : frontier 10 ⟨948021, by decide⟩
    (prefixCache 11 71891) (prefixPartial 11 71891) = false := by
  decide +kernel

theorem node_context_11_71891_948021 : EJMOriginalGlobalDAGData.nodes 10 ⟨948021, by decide⟩ =
    .split (coordinate 11) (![⟨947983, by decide⟩,⟨896706, by decide⟩,⟨948020, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71891_948021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71891 ⟨948021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71891
    ⟨948021, by decide⟩ (by decide) (![⟨947983, by decide⟩,⟨896706, by decide⟩,⟨948020, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_71891_948021 node_context_11_71891_948021
  intro a
  fin_cases a
  · exact context_12_287564_947983
  · exact context_12_287565_896706
  · exact context_12_287566_948020
  · exact context_12_287567_903806

theorem unmarked_context_10_17972_948022 : frontier 11 ⟨948022, by decide⟩
    (prefixCache 10 17972) (prefixPartial 10 17972) = false := by
  decide +kernel

theorem node_context_10_17972_948022 : EJMOriginalGlobalDAGData.nodes 11 ⟨948022, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨947834, by decide⟩,⟨947954, by decide⟩,⟨948021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17972_948022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17972 ⟨948022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17972
    ⟨948022, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨947834, by decide⟩,⟨947954, by decide⟩,⟨948021, by decide⟩]) unmarked_context_10_17972_948022 node_context_10_17972_948022
  intro a
  fin_cases a
  · exact context_11_71888_907917
  · exact context_11_71889_947834
  · exact context_11_71890_947954
  · exact context_11_71891_948021

theorem selected_cut_35955 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17973) = some ⟨10, 1, 0, 893098, 17973, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17973_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17973 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17973 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17973, 1, 1048576⟩
    (by decide) selected_cut_35955

theorem selected_cut_35956 : selected 9 ⟨948044, by decide⟩
    (prefixPartial 12 287584) = some ⟨12, 2, 0, 948044, 287584, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_287584_948044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287584 ⟨948044, by decide⟩ :=
  accepted_of_selected 12 287584 ⟨948044, by decide⟩ ⟨12, 2, 0, 948044, 287584, 1749, 65536⟩
    (by decide) selected_cut_35956

theorem selected_cut_35957 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287585) = some ⟨12, 1, 0, 896706, 287585, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287585_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287585 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287585 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287585, 1, 65536⟩
    (by decide) selected_cut_35957

theorem selected_cut_35958 : selected 9 ⟨948076, by decide⟩
    (prefixPartial 12 287586) = some ⟨12, 2, 0, 948076, 287586, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_287586_948076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287586 ⟨948076, by decide⟩ :=
  accepted_of_selected 12 287586 ⟨948076, by decide⟩ ⟨12, 2, 0, 948076, 287586, 2129, 65536⟩
    (by decide) selected_cut_35958

theorem selected_cut_35959 : selected 9 ⟨948106, by decide⟩
    (prefixPartial 12 287587) = some ⟨12, 2, 0, 948106, 287587, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_287587_948106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287587 ⟨948106, by decide⟩ :=
  accepted_of_selected 12 287587 ⟨948106, by decide⟩ ⟨12, 2, 0, 948106, 287587, 1949, 65536⟩
    (by decide) selected_cut_35959

theorem unmarked_context_11_71896_948107 : frontier 10 ⟨948107, by decide⟩
    (prefixCache 11 71896) (prefixPartial 11 71896) = false := by
  decide +kernel

theorem node_context_11_71896_948107 : EJMOriginalGlobalDAGData.nodes 10 ⟨948107, by decide⟩ =
    .split (coordinate 11) (![⟨948044, by decide⟩,⟨896706, by decide⟩,⟨948076, by decide⟩,⟨948106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71896_948107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71896 ⟨948107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71896
    ⟨948107, by decide⟩ (by decide) (![⟨948044, by decide⟩,⟨896706, by decide⟩,⟨948076, by decide⟩,⟨948106, by decide⟩]) unmarked_context_11_71896_948107 node_context_11_71896_948107
  intro a
  fin_cases a
  · exact context_12_287584_948044
  · exact context_12_287585_896706
  · exact context_12_287586_948076
  · exact context_12_287587_948106

theorem selected_cut_35960 : selected 9 ⟨948127, by decide⟩
    (prefixPartial 12 287588) = some ⟨12, 2, 0, 948127, 287588, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_287588_948127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287588 ⟨948127, by decide⟩ :=
  accepted_of_selected 12 287588 ⟨948127, by decide⟩ ⟨12, 2, 0, 948127, 287588, 1761, 65536⟩
    (by decide) selected_cut_35960

theorem selected_cut_35961 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287589) = some ⟨12, 1, 0, 896706, 287589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287589_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287589 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287589 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287589, 1, 65536⟩
    (by decide) selected_cut_35961

theorem selected_cut_35962 : selected 9 ⟨948152, by decide⟩
    (prefixPartial 12 287590) = some ⟨12, 2, 0, 948152, 287590, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_287590_948152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287590 ⟨948152, by decide⟩ :=
  accepted_of_selected 12 287590 ⟨948152, by decide⟩ ⟨12, 2, 0, 948152, 287590, 1933, 65536⟩
    (by decide) selected_cut_35962

theorem selected_cut_35963 : selected 9 ⟨948176, by decide⟩
    (prefixPartial 12 287591) = some ⟨12, 2, 0, 948176, 287591, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_287591_948176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287591 ⟨948176, by decide⟩ :=
  accepted_of_selected 12 287591 ⟨948176, by decide⟩ ⟨12, 2, 0, 948176, 287591, 1773, 65536⟩
    (by decide) selected_cut_35963

theorem unmarked_context_11_71897_948177 : frontier 10 ⟨948177, by decide⟩
    (prefixCache 11 71897) (prefixPartial 11 71897) = false := by
  decide +kernel

theorem node_context_11_71897_948177 : EJMOriginalGlobalDAGData.nodes 10 ⟨948177, by decide⟩ =
    .split (coordinate 11) (![⟨948127, by decide⟩,⟨896706, by decide⟩,⟨948152, by decide⟩,⟨948176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71897_948177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71897 ⟨948177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71897
    ⟨948177, by decide⟩ (by decide) (![⟨948127, by decide⟩,⟨896706, by decide⟩,⟨948152, by decide⟩,⟨948176, by decide⟩]) unmarked_context_11_71897_948177 node_context_11_71897_948177
  intro a
  fin_cases a
  · exact context_12_287588_948127
  · exact context_12_287589_896706
  · exact context_12_287590_948152
  · exact context_12_287591_948176

theorem selected_cut_35964 : selected 9 ⟨948200, by decide⟩
    (prefixPartial 12 287592) = some ⟨12, 2, 0, 948200, 287592, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_287592_948200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287592 ⟨948200, by decide⟩ :=
  accepted_of_selected 12 287592 ⟨948200, by decide⟩ ⟨12, 2, 0, 948200, 287592, 1853, 65536⟩
    (by decide) selected_cut_35964

theorem selected_cut_35965 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287593) = some ⟨12, 1, 0, 896706, 287593, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287593_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287593 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287593 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287593, 1, 65536⟩
    (by decide) selected_cut_35965

theorem selected_cut_35966 : selected 9 ⟨948231, by decide⟩
    (prefixPartial 12 287594) = some ⟨12, 2, 0, 948231, 287594, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_287594_948231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287594 ⟨948231, by decide⟩ :=
  accepted_of_selected 12 287594 ⟨948231, by decide⟩ ⟨12, 2, 0, 948231, 287594, 1893, 65536⟩
    (by decide) selected_cut_35966

theorem selected_cut_35967 : selected 9 ⟨948260, by decide⟩
    (prefixPartial 12 287595) = some ⟨12, 2, 0, 948260, 287595, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_287595_948260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287595 ⟨948260, by decide⟩ :=
  accepted_of_selected 12 287595 ⟨948260, by decide⟩ ⟨12, 2, 0, 948260, 287595, 1885, 65536⟩
    (by decide) selected_cut_35967

theorem unmarked_context_11_71898_948261 : frontier 10 ⟨948261, by decide⟩
    (prefixCache 11 71898) (prefixPartial 11 71898) = false := by
  decide +kernel

theorem node_context_11_71898_948261 : EJMOriginalGlobalDAGData.nodes 10 ⟨948261, by decide⟩ =
    .split (coordinate 11) (![⟨948200, by decide⟩,⟨896706, by decide⟩,⟨948231, by decide⟩,⟨948260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71898_948261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71898 ⟨948261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71898
    ⟨948261, by decide⟩ (by decide) (![⟨948200, by decide⟩,⟨896706, by decide⟩,⟨948231, by decide⟩,⟨948260, by decide⟩]) unmarked_context_11_71898_948261 node_context_11_71898_948261
  intro a
  fin_cases a
  · exact context_12_287592_948200
  · exact context_12_287593_896706
  · exact context_12_287594_948231
  · exact context_12_287595_948260

theorem selected_cut_35968 : selected 10 ⟨948318, by decide⟩
    (prefixPartial 11 71899) = some ⟨11, 2, 0, 948318, 71899, 3921, 262144⟩ := by
  decide +kernel

theorem context_11_71899_948318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71899 ⟨948318, by decide⟩ :=
  accepted_of_selected 11 71899 ⟨948318, by decide⟩ ⟨11, 2, 0, 948318, 71899, 3921, 262144⟩
    (by decide) selected_cut_35968

theorem unmarked_context_10_17974_948319 : frontier 11 ⟨948319, by decide⟩
    (prefixCache 10 17974) (prefixPartial 10 17974) = false := by
  decide +kernel

theorem node_context_10_17974_948319 : EJMOriginalGlobalDAGData.nodes 11 ⟨948319, by decide⟩ =
    .split (coordinate 10) (![⟨948107, by decide⟩,⟨948177, by decide⟩,⟨948261, by decide⟩,⟨948318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17974_948319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17974 ⟨948319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17974
    ⟨948319, by decide⟩ (by decide) (![⟨948107, by decide⟩,⟨948177, by decide⟩,⟨948261, by decide⟩,⟨948318, by decide⟩]) unmarked_context_10_17974_948319 node_context_10_17974_948319
  intro a
  fin_cases a
  · exact context_11_71896_948107
  · exact context_11_71897_948177
  · exact context_11_71898_948261
  · exact context_11_71899_948318

theorem selected_cut_35969 : selected 9 ⟨948341, by decide⟩
    (prefixPartial 12 287600) = some ⟨12, 2, 0, 948341, 287600, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_287600_948341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287600 ⟨948341, by decide⟩ :=
  accepted_of_selected 12 287600 ⟨948341, by decide⟩ ⟨12, 2, 0, 948341, 287600, 1717, 65536⟩
    (by decide) selected_cut_35969

theorem selected_cut_35970 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287601) = some ⟨12, 1, 0, 896706, 287601, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287601_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287601 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287601 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287601, 1, 65536⟩
    (by decide) selected_cut_35970

theorem selected_cut_35971 : selected 9 ⟨948372, by decide⟩
    (prefixPartial 12 287602) = some ⟨12, 2, 0, 948372, 287602, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_287602_948372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287602 ⟨948372, by decide⟩ :=
  accepted_of_selected 12 287602 ⟨948372, by decide⟩ ⟨12, 2, 0, 948372, 287602, 1873, 65536⟩
    (by decide) selected_cut_35971

theorem selected_cut_35972 : selected 9 ⟨948400, by decide⟩
    (prefixPartial 12 287603) = some ⟨12, 2, 0, 948400, 287603, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_287603_948400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287603 ⟨948400, by decide⟩ :=
  accepted_of_selected 12 287603 ⟨948400, by decide⟩ ⟨12, 2, 0, 948400, 287603, 1841, 65536⟩
    (by decide) selected_cut_35972

theorem unmarked_context_11_71900_948401 : frontier 10 ⟨948401, by decide⟩
    (prefixCache 11 71900) (prefixPartial 11 71900) = false := by
  decide +kernel

theorem node_context_11_71900_948401 : EJMOriginalGlobalDAGData.nodes 10 ⟨948401, by decide⟩ =
    .split (coordinate 11) (![⟨948341, by decide⟩,⟨896706, by decide⟩,⟨948372, by decide⟩,⟨948400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71900_948401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71900 ⟨948401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71900
    ⟨948401, by decide⟩ (by decide) (![⟨948341, by decide⟩,⟨896706, by decide⟩,⟨948372, by decide⟩,⟨948400, by decide⟩]) unmarked_context_11_71900_948401 node_context_11_71900_948401
  intro a
  fin_cases a
  · exact context_12_287600_948341
  · exact context_12_287601_896706
  · exact context_12_287602_948372
  · exact context_12_287603_948400

theorem selected_cut_35973 : selected 9 ⟨948427, by decide⟩
    (prefixPartial 12 287604) = some ⟨12, 2, 0, 948427, 287604, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_287604_948427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287604 ⟨948427, by decide⟩ :=
  accepted_of_selected 12 287604 ⟨948427, by decide⟩ ⟨12, 2, 0, 948427, 287604, 1765, 65536⟩
    (by decide) selected_cut_35973

theorem selected_cut_35974 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287605) = some ⟨12, 1, 0, 896706, 287605, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287605_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287605 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287605 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287605, 1, 65536⟩
    (by decide) selected_cut_35974

theorem selected_cut_35975 : selected 9 ⟨948455, by decide⟩
    (prefixPartial 12 287606) = some ⟨12, 2, 0, 948455, 287606, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_287606_948455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287606 ⟨948455, by decide⟩ :=
  accepted_of_selected 12 287606 ⟨948455, by decide⟩ ⟨12, 2, 0, 948455, 287606, 1673, 65536⟩
    (by decide) selected_cut_35975

theorem selected_cut_35976 : selected 9 ⟨948485, by decide⟩
    (prefixPartial 12 287607) = some ⟨12, 2, 0, 948485, 287607, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_287607_948485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287607 ⟨948485, by decide⟩ :=
  accepted_of_selected 12 287607 ⟨948485, by decide⟩ ⟨12, 2, 0, 948485, 287607, 1845, 65536⟩
    (by decide) selected_cut_35976

theorem unmarked_context_11_71901_948486 : frontier 10 ⟨948486, by decide⟩
    (prefixCache 11 71901) (prefixPartial 11 71901) = false := by
  decide +kernel

theorem node_context_11_71901_948486 : EJMOriginalGlobalDAGData.nodes 10 ⟨948486, by decide⟩ =
    .split (coordinate 11) (![⟨948427, by decide⟩,⟨896706, by decide⟩,⟨948455, by decide⟩,⟨948485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71901_948486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71901 ⟨948486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71901
    ⟨948486, by decide⟩ (by decide) (![⟨948427, by decide⟩,⟨896706, by decide⟩,⟨948455, by decide⟩,⟨948485, by decide⟩]) unmarked_context_11_71901_948486 node_context_11_71901_948486
  intro a
  fin_cases a
  · exact context_12_287604_948427
  · exact context_12_287605_896706
  · exact context_12_287606_948455
  · exact context_12_287607_948485

theorem selected_cut_35977 : selected 9 ⟨948514, by decide⟩
    (prefixPartial 12 287608) = some ⟨12, 2, 0, 948514, 287608, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_287608_948514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287608 ⟨948514, by decide⟩ :=
  accepted_of_selected 12 287608 ⟨948514, by decide⟩ ⟨12, 2, 0, 948514, 287608, 2021, 65536⟩
    (by decide) selected_cut_35977

theorem selected_cut_35978 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287609) = some ⟨12, 1, 0, 896706, 287609, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287609_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287609 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287609 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287609, 1, 65536⟩
    (by decide) selected_cut_35978

theorem selected_cut_35979 : selected 9 ⟨948538, by decide⟩
    (prefixPartial 12 287610) = some ⟨12, 2, 0, 948538, 287610, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_287610_948538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287610 ⟨948538, by decide⟩ :=
  accepted_of_selected 12 287610 ⟨948538, by decide⟩ ⟨12, 2, 0, 948538, 287610, 1821, 65536⟩
    (by decide) selected_cut_35979

theorem selected_cut_35980 : selected 9 ⟨948566, by decide⟩
    (prefixPartial 12 287611) = some ⟨12, 2, 0, 948566, 287611, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_287611_948566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287611 ⟨948566, by decide⟩ :=
  accepted_of_selected 12 287611 ⟨948566, by decide⟩ ⟨12, 2, 0, 948566, 287611, 2001, 65536⟩
    (by decide) selected_cut_35980

theorem unmarked_context_11_71902_948567 : frontier 10 ⟨948567, by decide⟩
    (prefixCache 11 71902) (prefixPartial 11 71902) = false := by
  decide +kernel

theorem node_context_11_71902_948567 : EJMOriginalGlobalDAGData.nodes 10 ⟨948567, by decide⟩ =
    .split (coordinate 11) (![⟨948514, by decide⟩,⟨896706, by decide⟩,⟨948538, by decide⟩,⟨948566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71902_948567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71902 ⟨948567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71902
    ⟨948567, by decide⟩ (by decide) (![⟨948514, by decide⟩,⟨896706, by decide⟩,⟨948538, by decide⟩,⟨948566, by decide⟩]) unmarked_context_11_71902_948567 node_context_11_71902_948567
  intro a
  fin_cases a
  · exact context_12_287608_948514
  · exact context_12_287609_896706
  · exact context_12_287610_948538
  · exact context_12_287611_948566

theorem selected_cut_35981 : selected 10 ⟨948620, by decide⟩
    (prefixPartial 11 71903) = some ⟨11, 2, 0, 948620, 71903, 3437, 262144⟩ := by
  decide +kernel

theorem context_11_71903_948620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71903 ⟨948620, by decide⟩ :=
  accepted_of_selected 11 71903 ⟨948620, by decide⟩ ⟨11, 2, 0, 948620, 71903, 3437, 262144⟩
    (by decide) selected_cut_35981

theorem unmarked_context_10_17975_948621 : frontier 11 ⟨948621, by decide⟩
    (prefixCache 10 17975) (prefixPartial 10 17975) = false := by
  decide +kernel

theorem node_context_10_17975_948621 : EJMOriginalGlobalDAGData.nodes 11 ⟨948621, by decide⟩ =
    .split (coordinate 10) (![⟨948401, by decide⟩,⟨948486, by decide⟩,⟨948567, by decide⟩,⟨948620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17975_948621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17975 ⟨948621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17975
    ⟨948621, by decide⟩ (by decide) (![⟨948401, by decide⟩,⟨948486, by decide⟩,⟨948567, by decide⟩,⟨948620, by decide⟩]) unmarked_context_10_17975_948621 node_context_10_17975_948621
  intro a
  fin_cases a
  · exact context_11_71900_948401
  · exact context_11_71901_948486
  · exact context_11_71902_948567
  · exact context_11_71903_948620

theorem unmarked_context_9_4493_948622 : frontier 12 ⟨948622, by decide⟩
    (prefixCache 9 4493) (prefixPartial 9 4493) = false := by
  decide +kernel

theorem node_context_9_4493_948622 : EJMOriginalGlobalDAGData.nodes 12 ⟨948622, by decide⟩ =
    .split (coordinate 9) (![⟨948022, by decide⟩,⟨893098, by decide⟩,⟨948319, by decide⟩,⟨948621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4493_948622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4493 ⟨948622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4493
    ⟨948622, by decide⟩ (by decide) (![⟨948022, by decide⟩,⟨893098, by decide⟩,⟨948319, by decide⟩,⟨948621, by decide⟩]) unmarked_context_9_4493_948622 node_context_9_4493_948622
  intro a
  fin_cases a
  · exact context_10_17972_948022
  · exact context_10_17973_893098
  · exact context_10_17974_948319
  · exact context_10_17975_948621

theorem selected_cut_35982 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71904) = some ⟨11, 1, 0, 907917, 71904, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71904_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71904 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71904 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71904, 1, 262144⟩
    (by decide) selected_cut_35982

theorem selected_cut_35983 : selected 9 ⟨948640, by decide⟩
    (prefixPartial 12 287620) = some ⟨12, 2, 0, 948640, 287620, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_287620_948640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287620 ⟨948640, by decide⟩ :=
  accepted_of_selected 12 287620 ⟨948640, by decide⟩ ⟨12, 2, 0, 948640, 287620, 1649, 65536⟩
    (by decide) selected_cut_35983

theorem selected_cut_35984 : selected 9 ⟨948660, by decide⟩
    (prefixPartial 12 287621) = some ⟨12, 2, 0, 948660, 287621, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_287621_948660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287621 ⟨948660, by decide⟩ :=
  accepted_of_selected 12 287621 ⟨948660, by decide⟩ ⟨12, 2, 0, 948660, 287621, 1449, 65536⟩
    (by decide) selected_cut_35984

theorem selected_cut_35985 : selected 9 ⟨948679, by decide⟩
    (prefixPartial 12 287622) = some ⟨12, 2, 0, 948679, 287622, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_287622_948679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287622 ⟨948679, by decide⟩ :=
  accepted_of_selected 12 287622 ⟨948679, by decide⟩ ⟨12, 2, 0, 948679, 287622, 1605, 65536⟩
    (by decide) selected_cut_35985

theorem selected_cut_35986 : selected 9 ⟨948701, by decide⟩
    (prefixPartial 12 287623) = some ⟨12, 2, 0, 948701, 287623, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_287623_948701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287623 ⟨948701, by decide⟩ :=
  accepted_of_selected 12 287623 ⟨948701, by decide⟩ ⟨12, 2, 0, 948701, 287623, 1593, 65536⟩
    (by decide) selected_cut_35986

theorem unmarked_context_11_71905_948702 : frontier 10 ⟨948702, by decide⟩
    (prefixCache 11 71905) (prefixPartial 11 71905) = false := by
  decide +kernel

theorem node_context_11_71905_948702 : EJMOriginalGlobalDAGData.nodes 10 ⟨948702, by decide⟩ =
    .split (coordinate 11) (![⟨948640, by decide⟩,⟨948660, by decide⟩,⟨948679, by decide⟩,⟨948701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71905_948702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71905 ⟨948702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71905
    ⟨948702, by decide⟩ (by decide) (![⟨948640, by decide⟩,⟨948660, by decide⟩,⟨948679, by decide⟩,⟨948701, by decide⟩]) unmarked_context_11_71905_948702 node_context_11_71905_948702
  intro a
  fin_cases a
  · exact context_12_287620_948640
  · exact context_12_287621_948660
  · exact context_12_287622_948679
  · exact context_12_287623_948701

theorem selected_cut_35987 : selected 9 ⟨948734, by decide⟩
    (prefixPartial 12 287624) = some ⟨12, 2, 0, 948734, 287624, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_287624_948734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287624 ⟨948734, by decide⟩ :=
  accepted_of_selected 12 287624 ⟨948734, by decide⟩ ⟨12, 2, 0, 948734, 287624, 1925, 65536⟩
    (by decide) selected_cut_35987

theorem selected_cut_35988 : selected 9 ⟨948758, by decide⟩
    (prefixPartial 12 287625) = some ⟨12, 2, 0, 948758, 287625, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_287625_948758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287625 ⟨948758, by decide⟩ :=
  accepted_of_selected 12 287625 ⟨948758, by decide⟩ ⟨12, 2, 0, 948758, 287625, 1581, 65536⟩
    (by decide) selected_cut_35988

theorem selected_cut_35989 : selected 9 ⟨948778, by decide⟩
    (prefixPartial 12 287626) = some ⟨12, 2, 0, 948778, 287626, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_287626_948778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287626 ⟨948778, by decide⟩ :=
  accepted_of_selected 12 287626 ⟨948778, by decide⟩ ⟨12, 2, 0, 948778, 287626, 1609, 65536⟩
    (by decide) selected_cut_35989

theorem selected_cut_35990 : selected 9 ⟨948805, by decide⟩
    (prefixPartial 12 287627) = some ⟨12, 2, 0, 948805, 287627, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_287627_948805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287627 ⟨948805, by decide⟩ :=
  accepted_of_selected 12 287627 ⟨948805, by decide⟩ ⟨12, 2, 0, 948805, 287627, 1757, 65536⟩
    (by decide) selected_cut_35990

theorem unmarked_context_11_71906_948806 : frontier 10 ⟨948806, by decide⟩
    (prefixCache 11 71906) (prefixPartial 11 71906) = false := by
  decide +kernel

theorem node_context_11_71906_948806 : EJMOriginalGlobalDAGData.nodes 10 ⟨948806, by decide⟩ =
    .split (coordinate 11) (![⟨948734, by decide⟩,⟨948758, by decide⟩,⟨948778, by decide⟩,⟨948805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71906_948806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71906 ⟨948806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71906
    ⟨948806, by decide⟩ (by decide) (![⟨948734, by decide⟩,⟨948758, by decide⟩,⟨948778, by decide⟩,⟨948805, by decide⟩]) unmarked_context_11_71906_948806 node_context_11_71906_948806
  intro a
  fin_cases a
  · exact context_12_287624_948734
  · exact context_12_287625_948758
  · exact context_12_287626_948778
  · exact context_12_287627_948805

theorem selected_cut_35991 : selected 9 ⟨948829, by decide⟩
    (prefixPartial 12 287628) = some ⟨12, 2, 0, 948829, 287628, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_287628_948829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287628 ⟨948829, by decide⟩ :=
  accepted_of_selected 12 287628 ⟨948829, by decide⟩ ⟨12, 2, 0, 948829, 287628, 1537, 65536⟩
    (by decide) selected_cut_35991

theorem selected_cut_35992 : selected 9 ⟨948846, by decide⟩
    (prefixPartial 12 287629) = some ⟨12, 2, 0, 948846, 287629, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_287629_948846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287629 ⟨948846, by decide⟩ :=
  accepted_of_selected 12 287629 ⟨948846, by decide⟩ ⟨12, 2, 0, 948846, 287629, 1285, 65536⟩
    (by decide) selected_cut_35992

theorem selected_cut_35993 : selected 9 ⟨948869, by decide⟩
    (prefixPartial 12 287630) = some ⟨12, 2, 0, 948869, 287630, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_287630_948869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287630 ⟨948869, by decide⟩ :=
  accepted_of_selected 12 287630 ⟨948869, by decide⟩ ⟨12, 2, 0, 948869, 287630, 1393, 65536⟩
    (by decide) selected_cut_35993

theorem selected_cut_35994 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 287631) = some ⟨12, 1, 0, 903806, 287631, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287631_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287631 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 287631 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 287631, 1, 65536⟩
    (by decide) selected_cut_35994

theorem unmarked_context_11_71907_948870 : frontier 10 ⟨948870, by decide⟩
    (prefixCache 11 71907) (prefixPartial 11 71907) = false := by
  decide +kernel

theorem node_context_11_71907_948870 : EJMOriginalGlobalDAGData.nodes 10 ⟨948870, by decide⟩ =
    .split (coordinate 11) (![⟨948829, by decide⟩,⟨948846, by decide⟩,⟨948869, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71907_948870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71907 ⟨948870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71907
    ⟨948870, by decide⟩ (by decide) (![⟨948829, by decide⟩,⟨948846, by decide⟩,⟨948869, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_71907_948870 node_context_11_71907_948870
  intro a
  fin_cases a
  · exact context_12_287628_948829
  · exact context_12_287629_948846
  · exact context_12_287630_948869
  · exact context_12_287631_903806

theorem unmarked_context_10_17976_948871 : frontier 11 ⟨948871, by decide⟩
    (prefixCache 10 17976) (prefixPartial 10 17976) = false := by
  decide +kernel

theorem node_context_10_17976_948871 : EJMOriginalGlobalDAGData.nodes 11 ⟨948871, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨948702, by decide⟩,⟨948806, by decide⟩,⟨948870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17976_948871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17976 ⟨948871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17976
    ⟨948871, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨948702, by decide⟩,⟨948806, by decide⟩,⟨948870, by decide⟩]) unmarked_context_10_17976_948871 node_context_10_17976_948871
  intro a
  fin_cases a
  · exact context_11_71904_907917
  · exact context_11_71905_948702
  · exact context_11_71906_948806
  · exact context_11_71907_948870

theorem selected_cut_35995 : selected 9 ⟨948883, by decide⟩
    (prefixPartial 12 287632) = some ⟨12, 2, 0, 948883, 287632, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_287632_948883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287632 ⟨948883, by decide⟩ :=
  accepted_of_selected 12 287632 ⟨948883, by decide⟩ ⟨12, 2, 0, 948883, 287632, 1309, 65536⟩
    (by decide) selected_cut_35995

theorem selected_cut_35996 : selected 9 ⟨948901, by decide⟩
    (prefixPartial 12 287633) = some ⟨12, 2, 0, 948901, 287633, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_287633_948901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287633 ⟨948901, by decide⟩ :=
  accepted_of_selected 12 287633 ⟨948901, by decide⟩ ⟨12, 2, 0, 948901, 287633, 1433, 65536⟩
    (by decide) selected_cut_35996

theorem selected_cut_35997 : selected 9 ⟨948923, by decide⟩
    (prefixPartial 12 287634) = some ⟨12, 2, 0, 948923, 287634, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_287634_948923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287634 ⟨948923, by decide⟩ :=
  accepted_of_selected 12 287634 ⟨948923, by decide⟩ ⟨12, 2, 0, 948923, 287634, 1461, 65536⟩
    (by decide) selected_cut_35997

theorem selected_cut_35998 : selected 9 ⟨948941, by decide⟩
    (prefixPartial 12 287635) = some ⟨12, 2, 0, 948941, 287635, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_287635_948941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287635 ⟨948941, by decide⟩ :=
  accepted_of_selected 12 287635 ⟨948941, by decide⟩ ⟨12, 2, 0, 948941, 287635, 1401, 65536⟩
    (by decide) selected_cut_35998

theorem unmarked_context_11_71908_948942 : frontier 10 ⟨948942, by decide⟩
    (prefixCache 11 71908) (prefixPartial 11 71908) = false := by
  decide +kernel

theorem node_context_11_71908_948942 : EJMOriginalGlobalDAGData.nodes 10 ⟨948942, by decide⟩ =
    .split (coordinate 11) (![⟨948883, by decide⟩,⟨948901, by decide⟩,⟨948923, by decide⟩,⟨948941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71908_948942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71908 ⟨948942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71908
    ⟨948942, by decide⟩ (by decide) (![⟨948883, by decide⟩,⟨948901, by decide⟩,⟨948923, by decide⟩,⟨948941, by decide⟩]) unmarked_context_11_71908_948942 node_context_11_71908_948942
  intro a
  fin_cases a
  · exact context_12_287632_948883
  · exact context_12_287633_948901
  · exact context_12_287634_948923
  · exact context_12_287635_948941

theorem selected_cut_35999 : selected 9 ⟨948953, by decide⟩
    (prefixPartial 12 287636) = some ⟨12, 2, 0, 948953, 287636, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_287636_948953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287636 ⟨948953, by decide⟩ :=
  accepted_of_selected 12 287636 ⟨948953, by decide⟩ ⟨12, 2, 0, 948953, 287636, 1237, 65536⟩
    (by decide) selected_cut_35999

theorem selected_cut_36000 : selected 9 ⟨948968, by decide⟩
    (prefixPartial 12 287637) = some ⟨12, 2, 0, 948968, 287637, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_287637_948968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287637 ⟨948968, by decide⟩ :=
  accepted_of_selected 12 287637 ⟨948968, by decide⟩ ⟨12, 2, 0, 948968, 287637, 1201, 65536⟩
    (by decide) selected_cut_36000

theorem selected_cut_36001 : selected 9 ⟨948984, by decide⟩
    (prefixPartial 12 287638) = some ⟨12, 2, 0, 948984, 287638, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_287638_948984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287638 ⟨948984, by decide⟩ :=
  accepted_of_selected 12 287638 ⟨948984, by decide⟩ ⟨12, 2, 0, 948984, 287638, 1289, 65536⟩
    (by decide) selected_cut_36001

theorem selected_cut_36002 : selected 9 ⟨949001, by decide⟩
    (prefixPartial 12 287639) = some ⟨12, 2, 0, 949001, 287639, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_287639_949001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287639 ⟨949001, by decide⟩ :=
  accepted_of_selected 12 287639 ⟨949001, by decide⟩ ⟨12, 2, 0, 949001, 287639, 1237, 65536⟩
    (by decide) selected_cut_36002

theorem unmarked_context_11_71909_949002 : frontier 10 ⟨949002, by decide⟩
    (prefixCache 11 71909) (prefixPartial 11 71909) = false := by
  decide +kernel

theorem node_context_11_71909_949002 : EJMOriginalGlobalDAGData.nodes 10 ⟨949002, by decide⟩ =
    .split (coordinate 11) (![⟨948953, by decide⟩,⟨948968, by decide⟩,⟨948984, by decide⟩,⟨949001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71909_949002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71909 ⟨949002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71909
    ⟨949002, by decide⟩ (by decide) (![⟨948953, by decide⟩,⟨948968, by decide⟩,⟨948984, by decide⟩,⟨949001, by decide⟩]) unmarked_context_11_71909_949002 node_context_11_71909_949002
  intro a
  fin_cases a
  · exact context_12_287636_948953
  · exact context_12_287637_948968
  · exact context_12_287638_948984
  · exact context_12_287639_949001

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
