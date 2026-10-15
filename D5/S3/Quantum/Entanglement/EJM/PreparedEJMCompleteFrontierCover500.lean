/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover499
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48004 : selected 10 ⟨1344955, by decide⟩
    (prefixPartial 11 93742) = some ⟨11, 2, 0, 1344955, 93742, 1385, 262144⟩ := by
  decide +kernel

theorem context_11_93742_1344955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93742 ⟨1344955, by decide⟩ :=
  accepted_of_selected 11 93742 ⟨1344955, by decide⟩ ⟨11, 2, 0, 1344955, 93742, 1385, 262144⟩
    (by decide) selected_cut_48004

theorem selected_cut_48005 : selected 10 ⟨1344962, by decide⟩
    (prefixPartial 11 93743) = some ⟨11, 2, 0, 1344962, 93743, 433, 262144⟩ := by
  decide +kernel

theorem context_11_93743_1344962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93743 ⟨1344962, by decide⟩ :=
  accepted_of_selected 11 93743 ⟨1344962, by decide⟩ ⟨11, 2, 0, 1344962, 93743, 433, 262144⟩
    (by decide) selected_cut_48005

theorem unmarked_context_10_23435_1344963 : frontier 11 ⟨1344963, by decide⟩
    (prefixCache 10 23435) (prefixPartial 10 23435) = false := by
  decide +kernel

theorem node_context_10_23435_1344963 : EJMOriginalGlobalDAGData.nodes 11 ⟨1344963, by decide⟩ =
    .split (coordinate 10) (![⟨1344900, by decide⟩,⟨1344935, by decide⟩,⟨1344955, by decide⟩,⟨1344962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23435_1344963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23435 ⟨1344963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23435
    ⟨1344963, by decide⟩ (by decide) (![⟨1344900, by decide⟩,⟨1344935, by decide⟩,⟨1344955, by decide⟩,⟨1344962, by decide⟩]) unmarked_context_10_23435_1344963 node_context_10_23435_1344963
  intro a
  fin_cases a
  · exact context_11_93740_1344900
  · exact context_11_93741_1344935
  · exact context_11_93742_1344955
  · exact context_11_93743_1344962

theorem unmarked_context_9_5858_1344964 : frontier 12 ⟨1344964, by decide⟩
    (prefixCache 9 5858) (prefixPartial 9 5858) = false := by
  decide +kernel

theorem node_context_9_5858_1344964 : EJMOriginalGlobalDAGData.nodes 12 ⟨1344964, by decide⟩ =
    .split (coordinate 9) (![⟨1344751, by decide⟩,⟨1344850, by decide⟩,⟨1344884, by decide⟩,⟨1344963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5858_1344964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5858 ⟨1344964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5858
    ⟨1344964, by decide⟩ (by decide) (![⟨1344751, by decide⟩,⟨1344850, by decide⟩,⟨1344884, by decide⟩,⟨1344963, by decide⟩]) unmarked_context_9_5858_1344964 node_context_9_5858_1344964
  intro a
  fin_cases a
  · exact context_10_23432_1344751
  · exact context_10_23433_1344850
  · exact context_10_23434_1344884
  · exact context_10_23435_1344963

theorem selected_cut_48006 : selected 10 ⟨1344975, by decide⟩
    (prefixPartial 11 93744) = some ⟨11, 2, 0, 1344975, 93744, 901, 262144⟩ := by
  decide +kernel

theorem context_11_93744_1344975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93744 ⟨1344975, by decide⟩ :=
  accepted_of_selected 11 93744 ⟨1344975, by decide⟩ ⟨11, 2, 0, 1344975, 93744, 901, 262144⟩
    (by decide) selected_cut_48006

theorem selected_cut_48007 : selected 10 ⟨1345010, by decide⟩
    (prefixPartial 11 93745) = some ⟨11, 2, 0, 1345010, 93745, 1565, 262144⟩ := by
  decide +kernel

theorem context_11_93745_1345010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93745 ⟨1345010, by decide⟩ :=
  accepted_of_selected 11 93745 ⟨1345010, by decide⟩ ⟨11, 2, 0, 1345010, 93745, 1565, 262144⟩
    (by decide) selected_cut_48007

theorem selected_cut_48008 : selected 10 ⟨1345025, by decide⟩
    (prefixPartial 11 93746) = some ⟨11, 2, 0, 1345025, 93746, 913, 262144⟩ := by
  decide +kernel

theorem context_11_93746_1345025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93746 ⟨1345025, by decide⟩ :=
  accepted_of_selected 11 93746 ⟨1345025, by decide⟩ ⟨11, 2, 0, 1345025, 93746, 913, 262144⟩
    (by decide) selected_cut_48008

theorem selected_cut_48009 : selected 10 ⟨1345042, by decide⟩
    (prefixPartial 11 93747) = some ⟨11, 2, 0, 1345042, 93747, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_93747_1345042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93747 ⟨1345042, by decide⟩ :=
  accepted_of_selected 11 93747 ⟨1345042, by decide⟩ ⟨11, 2, 0, 1345042, 93747, 1293, 262144⟩
    (by decide) selected_cut_48009

theorem unmarked_context_10_23436_1345043 : frontier 11 ⟨1345043, by decide⟩
    (prefixCache 10 23436) (prefixPartial 10 23436) = false := by
  decide +kernel

theorem node_context_10_23436_1345043 : EJMOriginalGlobalDAGData.nodes 11 ⟨1345043, by decide⟩ =
    .split (coordinate 10) (![⟨1344975, by decide⟩,⟨1345010, by decide⟩,⟨1345025, by decide⟩,⟨1345042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23436_1345043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23436 ⟨1345043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23436
    ⟨1345043, by decide⟩ (by decide) (![⟨1344975, by decide⟩,⟨1345010, by decide⟩,⟨1345025, by decide⟩,⟨1345042, by decide⟩]) unmarked_context_10_23436_1345043 node_context_10_23436_1345043
  intro a
  fin_cases a
  · exact context_11_93744_1344975
  · exact context_11_93745_1345010
  · exact context_11_93746_1345025
  · exact context_11_93747_1345042

theorem selected_cut_48010 : selected 11 ⟨1345096, by decide⟩
    (prefixPartial 10 23437) = some ⟨10, 2, 0, 1345096, 23437, 3241, 1048576⟩ := by
  decide +kernel

theorem context_10_23437_1345096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23437 ⟨1345096, by decide⟩ :=
  accepted_of_selected 10 23437 ⟨1345096, by decide⟩ ⟨10, 2, 0, 1345096, 23437, 3241, 1048576⟩
    (by decide) selected_cut_48010

theorem selected_cut_48011 : selected 11 ⟨1345127, by decide⟩
    (prefixPartial 10 23438) = some ⟨10, 2, 0, 1345127, 23438, 1193, 1048576⟩ := by
  decide +kernel

theorem context_10_23438_1345127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23438 ⟨1345127, by decide⟩ :=
  accepted_of_selected 10 23438 ⟨1345127, by decide⟩ ⟨10, 2, 0, 1345127, 23438, 1193, 1048576⟩
    (by decide) selected_cut_48011

theorem selected_cut_48012 : selected 11 ⟨1345140, by decide⟩
    (prefixPartial 10 23439) = some ⟨10, 2, 0, 1345140, 23439, 233, 1048576⟩ := by
  decide +kernel

theorem context_10_23439_1345140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23439 ⟨1345140, by decide⟩ :=
  accepted_of_selected 10 23439 ⟨1345140, by decide⟩ ⟨10, 2, 0, 1345140, 23439, 233, 1048576⟩
    (by decide) selected_cut_48012

theorem unmarked_context_9_5859_1345141 : frontier 12 ⟨1345141, by decide⟩
    (prefixCache 9 5859) (prefixPartial 9 5859) = false := by
  decide +kernel

theorem node_context_9_5859_1345141 : EJMOriginalGlobalDAGData.nodes 12 ⟨1345141, by decide⟩ =
    .split (coordinate 9) (![⟨1345043, by decide⟩,⟨1345096, by decide⟩,⟨1345127, by decide⟩,⟨1345140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5859_1345141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5859 ⟨1345141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5859
    ⟨1345141, by decide⟩ (by decide) (![⟨1345043, by decide⟩,⟨1345096, by decide⟩,⟨1345127, by decide⟩,⟨1345140, by decide⟩]) unmarked_context_9_5859_1345141 node_context_9_5859_1345141
  intro a
  fin_cases a
  · exact context_10_23436_1345043
  · exact context_10_23437_1345096
  · exact context_10_23438_1345127
  · exact context_10_23439_1345140

theorem unmarked_context_8_1464_1345142 : frontier 13 ⟨1345142, by decide⟩
    (prefixCache 8 1464) (prefixPartial 8 1464) = false := by
  decide +kernel

theorem node_context_8_1464_1345142 : EJMOriginalGlobalDAGData.nodes 13 ⟨1345142, by decide⟩ =
    .split (coordinate 8) (![⟨1343876, by decide⟩,⟨1344622, by decide⟩,⟨1344964, by decide⟩,⟨1345141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1464_1345142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1464 ⟨1345142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1464
    ⟨1345142, by decide⟩ (by decide) (![⟨1343876, by decide⟩,⟨1344622, by decide⟩,⟨1344964, by decide⟩,⟨1345141, by decide⟩]) unmarked_context_8_1464_1345142 node_context_8_1464_1345142
  intro a
  fin_cases a
  · exact context_9_5856_1343876
  · exact context_9_5857_1344622
  · exact context_9_5858_1344964
  · exact context_9_5859_1345141

theorem selected_cut_48013 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93760) = some ⟨11, 1, 0, 434745, 93760, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93760_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93760 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93760 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93760, 1, 262144⟩
    (by decide) selected_cut_48013

theorem selected_cut_48014 : selected 10 ⟨1345191, by decide⟩
    (prefixPartial 11 93761) = some ⟨11, 2, 0, 1345191, 93761, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_93761_1345191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93761 ⟨1345191, by decide⟩ :=
  accepted_of_selected 11 93761 ⟨1345191, by decide⟩ ⟨11, 2, 0, 1345191, 93761, 1717, 262144⟩
    (by decide) selected_cut_48014

theorem selected_cut_48015 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 375048) = some ⟨12, 1, 0, 448748, 375048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375048_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375048 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 375048 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 375048, 1, 65536⟩
    (by decide) selected_cut_48015

theorem selected_cut_48016 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 375049) = some ⟨12, 1, 0, 34034, 375049, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375049_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375049 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 375049 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 375049, 1, 65536⟩
    (by decide) selected_cut_48016

theorem selected_cut_48017 : selected 9 ⟨1345247, by decide⟩
    (prefixPartial 12 375050) = some ⟨12, 2, 0, 1345247, 375050, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_375050_1345247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375050 ⟨1345247, by decide⟩ :=
  accepted_of_selected 12 375050 ⟨1345247, by decide⟩ ⟨12, 2, 0, 1345247, 375050, 2729, 65536⟩
    (by decide) selected_cut_48017

theorem selected_cut_48018 : selected 9 ⟨1345291, by decide⟩
    (prefixPartial 12 375051) = some ⟨12, 2, 0, 1345291, 375051, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_375051_1345291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375051 ⟨1345291, by decide⟩ :=
  accepted_of_selected 12 375051 ⟨1345291, by decide⟩ ⟨12, 2, 0, 1345291, 375051, 2441, 65536⟩
    (by decide) selected_cut_48018

theorem unmarked_context_11_93762_1345292 : frontier 10 ⟨1345292, by decide⟩
    (prefixCache 11 93762) (prefixPartial 11 93762) = false := by
  decide +kernel

theorem node_context_11_93762_1345292 : EJMOriginalGlobalDAGData.nodes 10 ⟨1345292, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1345247, by decide⟩,⟨1345291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93762_1345292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93762 ⟨1345292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93762
    ⟨1345292, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1345247, by decide⟩,⟨1345291, by decide⟩]) unmarked_context_11_93762_1345292 node_context_11_93762_1345292
  intro a
  fin_cases a
  · exact context_12_375048_448748
  · exact context_12_375049_34034
  · exact context_12_375050_1345247
  · exact context_12_375051_1345291

theorem selected_cut_48019 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 375052) = some ⟨12, 1, 0, 448748, 375052, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375052_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375052 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 375052 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 375052, 1, 65536⟩
    (by decide) selected_cut_48019

theorem selected_cut_48020 : selected 9 ⟨1345383, by decide⟩
    (prefixPartial 12 375053) = some ⟨12, 2, 0, 1345383, 375053, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_375053_1345383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375053 ⟨1345383, by decide⟩ :=
  accepted_of_selected 12 375053 ⟨1345383, by decide⟩ ⟨12, 2, 0, 1345383, 375053, 3401, 65536⟩
    (by decide) selected_cut_48020

theorem selected_cut_48021 : selected 9 ⟨1345443, by decide⟩
    (prefixPartial 12 375054) = some ⟨12, 2, 0, 1345443, 375054, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_375054_1345443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375054 ⟨1345443, by decide⟩ :=
  accepted_of_selected 12 375054 ⟨1345443, by decide⟩ ⟨12, 2, 0, 1345443, 375054, 2893, 65536⟩
    (by decide) selected_cut_48021

theorem selected_cut_48022 : selected 9 ⟨1345491, by decide⟩
    (prefixPartial 12 375055) = some ⟨12, 2, 0, 1345491, 375055, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_375055_1345491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375055 ⟨1345491, by decide⟩ :=
  accepted_of_selected 12 375055 ⟨1345491, by decide⟩ ⟨12, 2, 0, 1345491, 375055, 2729, 65536⟩
    (by decide) selected_cut_48022

theorem unmarked_context_11_93763_1345492 : frontier 10 ⟨1345492, by decide⟩
    (prefixCache 11 93763) (prefixPartial 11 93763) = false := by
  decide +kernel

theorem node_context_11_93763_1345492 : EJMOriginalGlobalDAGData.nodes 10 ⟨1345492, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1345383, by decide⟩,⟨1345443, by decide⟩,⟨1345491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93763_1345492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93763 ⟨1345492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93763
    ⟨1345492, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1345383, by decide⟩,⟨1345443, by decide⟩,⟨1345491, by decide⟩]) unmarked_context_11_93763_1345492 node_context_11_93763_1345492
  intro a
  fin_cases a
  · exact context_12_375052_448748
  · exact context_12_375053_1345383
  · exact context_12_375054_1345443
  · exact context_12_375055_1345491

theorem unmarked_context_10_23440_1345493 : frontier 11 ⟨1345493, by decide⟩
    (prefixCache 10 23440) (prefixPartial 10 23440) = false := by
  decide +kernel

theorem node_context_10_23440_1345493 : EJMOriginalGlobalDAGData.nodes 11 ⟨1345493, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1345191, by decide⟩,⟨1345292, by decide⟩,⟨1345492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23440_1345493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23440 ⟨1345493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23440
    ⟨1345493, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1345191, by decide⟩,⟨1345292, by decide⟩,⟨1345492, by decide⟩]) unmarked_context_10_23440_1345493 node_context_10_23440_1345493
  intro a
  fin_cases a
  · exact context_11_93760_434745
  · exact context_11_93761_1345191
  · exact context_11_93762_1345292
  · exact context_11_93763_1345492

theorem selected_cut_48023 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 375056) = some ⟨12, 1, 0, 307381, 375056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375056_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375056 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 375056 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 375056, 1, 65536⟩
    (by decide) selected_cut_48023

theorem selected_cut_48024 : selected 9 ⟨1345547, by decide⟩
    (prefixPartial 12 375057) = some ⟨12, 2, 0, 1345547, 375057, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_375057_1345547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375057 ⟨1345547, by decide⟩ :=
  accepted_of_selected 12 375057 ⟨1345547, by decide⟩ ⟨12, 2, 0, 1345547, 375057, 2841, 65536⟩
    (by decide) selected_cut_48024

theorem selected_cut_48025 : selected 9 ⟨1345584, by decide⟩
    (prefixPartial 12 375058) = some ⟨12, 2, 0, 1345584, 375058, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_375058_1345584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375058 ⟨1345584, by decide⟩ :=
  accepted_of_selected 12 375058 ⟨1345584, by decide⟩ ⟨12, 2, 0, 1345584, 375058, 2361, 65536⟩
    (by decide) selected_cut_48025

theorem selected_cut_48026 : selected 9 ⟨1345632, by decide⟩
    (prefixPartial 12 375059) = some ⟨12, 2, 0, 1345632, 375059, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_375059_1345632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375059 ⟨1345632, by decide⟩ :=
  accepted_of_selected 12 375059 ⟨1345632, by decide⟩ ⟨12, 2, 0, 1345632, 375059, 2493, 65536⟩
    (by decide) selected_cut_48026

theorem unmarked_context_11_93764_1345633 : frontier 10 ⟨1345633, by decide⟩
    (prefixCache 11 93764) (prefixPartial 11 93764) = false := by
  decide +kernel

theorem node_context_11_93764_1345633 : EJMOriginalGlobalDAGData.nodes 10 ⟨1345633, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨1345547, by decide⟩,⟨1345584, by decide⟩,⟨1345632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93764_1345633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93764 ⟨1345633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93764
    ⟨1345633, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨1345547, by decide⟩,⟨1345584, by decide⟩,⟨1345632, by decide⟩]) unmarked_context_11_93764_1345633 node_context_11_93764_1345633
  intro a
  fin_cases a
  · exact context_12_375056_307381
  · exact context_12_375057_1345547
  · exact context_12_375058_1345584
  · exact context_12_375059_1345632

theorem selected_cut_48027 : selected 9 ⟨1345673, by decide⟩
    (prefixPartial 12 375060) = some ⟨12, 2, 0, 1345673, 375060, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_375060_1345673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375060 ⟨1345673, by decide⟩ :=
  accepted_of_selected 12 375060 ⟨1345673, by decide⟩ ⟨12, 2, 0, 1345673, 375060, 2201, 65536⟩
    (by decide) selected_cut_48027

theorem selected_cut_48028 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 375061) = some ⟨12, 1, 0, 1118965, 375061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375061_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375061 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 375061 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 375061, 1, 65536⟩
    (by decide) selected_cut_48028

theorem selected_cut_48029 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 375062) = some ⟨12, 1, 0, 692793, 375062, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375062_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375062 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 375062 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 375062, 1, 65536⟩
    (by decide) selected_cut_48029

theorem selected_cut_48030 : selected 9 ⟨1345713, by decide⟩
    (prefixPartial 12 375063) = some ⟨12, 2, 0, 1345713, 375063, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_375063_1345713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375063 ⟨1345713, by decide⟩ :=
  accepted_of_selected 12 375063 ⟨1345713, by decide⟩ ⟨12, 2, 0, 1345713, 375063, 2457, 65536⟩
    (by decide) selected_cut_48030

theorem unmarked_context_11_93765_1345714 : frontier 10 ⟨1345714, by decide⟩
    (prefixCache 11 93765) (prefixPartial 11 93765) = false := by
  decide +kernel

theorem node_context_11_93765_1345714 : EJMOriginalGlobalDAGData.nodes 10 ⟨1345714, by decide⟩ =
    .split (coordinate 11) (![⟨1345673, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1345713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93765_1345714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93765 ⟨1345714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93765
    ⟨1345714, by decide⟩ (by decide) (![⟨1345673, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1345713, by decide⟩]) unmarked_context_11_93765_1345714 node_context_11_93765_1345714
  intro a
  fin_cases a
  · exact context_12_375060_1345673
  · exact context_12_375061_1118965
  · exact context_12_375062_692793
  · exact context_12_375063_1345713

theorem selected_cut_48031 : selected 9 ⟨1072955, by decide⟩
    (prefixPartial 12 375064) = some ⟨12, 1, 0, 1072955, 375064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375064_1072955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375064 ⟨1072955, by decide⟩ :=
  accepted_of_selected 12 375064 ⟨1072955, by decide⟩ ⟨12, 1, 0, 1072955, 375064, 1, 65536⟩
    (by decide) selected_cut_48031

theorem selected_cut_48032 : selected 9 ⟨1345750, by decide⟩
    (prefixPartial 12 375065) = some ⟨12, 2, 0, 1345750, 375065, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_375065_1345750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375065 ⟨1345750, by decide⟩ :=
  accepted_of_selected 12 375065 ⟨1345750, by decide⟩ ⟨12, 2, 0, 1345750, 375065, 2405, 65536⟩
    (by decide) selected_cut_48032

theorem selected_cut_48033 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 375066) = some ⟨12, 1, 0, 660636, 375066, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375066_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375066 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 375066 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 375066, 1, 65536⟩
    (by decide) selected_cut_48033

theorem selected_cut_48034 : selected 9 ⟨1345784, by decide⟩
    (prefixPartial 12 375067) = some ⟨12, 2, 0, 1345784, 375067, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_375067_1345784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375067 ⟨1345784, by decide⟩ :=
  accepted_of_selected 12 375067 ⟨1345784, by decide⟩ ⟨12, 2, 0, 1345784, 375067, 2273, 65536⟩
    (by decide) selected_cut_48034

theorem unmarked_context_11_93766_1345785 : frontier 10 ⟨1345785, by decide⟩
    (prefixCache 11 93766) (prefixPartial 11 93766) = false := by
  decide +kernel

theorem node_context_11_93766_1345785 : EJMOriginalGlobalDAGData.nodes 10 ⟨1345785, by decide⟩ =
    .split (coordinate 11) (![⟨1072955, by decide⟩,⟨1345750, by decide⟩,⟨660636, by decide⟩,⟨1345784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93766_1345785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93766 ⟨1345785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93766
    ⟨1345785, by decide⟩ (by decide) (![⟨1072955, by decide⟩,⟨1345750, by decide⟩,⟨660636, by decide⟩,⟨1345784, by decide⟩]) unmarked_context_11_93766_1345785 node_context_11_93766_1345785
  intro a
  fin_cases a
  · exact context_12_375064_1072955
  · exact context_12_375065_1345750
  · exact context_12_375066_660636
  · exact context_12_375067_1345784

theorem selected_cut_48035 : selected 9 ⟨1345823, by decide⟩
    (prefixPartial 12 375068) = some ⟨12, 2, 0, 1345823, 375068, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_375068_1345823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375068 ⟨1345823, by decide⟩ :=
  accepted_of_selected 12 375068 ⟨1345823, by decide⟩ ⟨12, 2, 0, 1345823, 375068, 2189, 65536⟩
    (by decide) selected_cut_48035

theorem selected_cut_48036 : selected 9 ⟨1345874, by decide⟩
    (prefixPartial 12 375069) = some ⟨12, 2, 0, 1345874, 375069, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_375069_1345874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375069 ⟨1345874, by decide⟩ :=
  accepted_of_selected 12 375069 ⟨1345874, by decide⟩ ⟨12, 2, 0, 1345874, 375069, 2605, 65536⟩
    (by decide) selected_cut_48036

theorem selected_cut_48037 : selected 9 ⟨1345909, by decide⟩
    (prefixPartial 12 375070) = some ⟨12, 2, 0, 1345909, 375070, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_375070_1345909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375070 ⟨1345909, by decide⟩ :=
  accepted_of_selected 12 375070 ⟨1345909, by decide⟩ ⟨12, 2, 0, 1345909, 375070, 2273, 65536⟩
    (by decide) selected_cut_48037

theorem selected_cut_48038 : selected 9 ⟨1345988, by decide⟩
    (prefixPartial 12 375071) = some ⟨12, 2, 0, 1345988, 375071, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_375071_1345988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375071 ⟨1345988, by decide⟩ :=
  accepted_of_selected 12 375071 ⟨1345988, by decide⟩ ⟨12, 2, 0, 1345988, 375071, 1405, 65536⟩
    (by decide) selected_cut_48038

theorem unmarked_context_11_93767_1345989 : frontier 10 ⟨1345989, by decide⟩
    (prefixCache 11 93767) (prefixPartial 11 93767) = false := by
  decide +kernel

theorem node_context_11_93767_1345989 : EJMOriginalGlobalDAGData.nodes 10 ⟨1345989, by decide⟩ =
    .split (coordinate 11) (![⟨1345823, by decide⟩,⟨1345874, by decide⟩,⟨1345909, by decide⟩,⟨1345988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93767_1345989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93767 ⟨1345989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93767
    ⟨1345989, by decide⟩ (by decide) (![⟨1345823, by decide⟩,⟨1345874, by decide⟩,⟨1345909, by decide⟩,⟨1345988, by decide⟩]) unmarked_context_11_93767_1345989 node_context_11_93767_1345989
  intro a
  fin_cases a
  · exact context_12_375068_1345823
  · exact context_12_375069_1345874
  · exact context_12_375070_1345909
  · exact context_12_375071_1345988

theorem unmarked_context_10_23441_1345990 : frontier 11 ⟨1345990, by decide⟩
    (prefixCache 10 23441) (prefixPartial 10 23441) = false := by
  decide +kernel

theorem node_context_10_23441_1345990 : EJMOriginalGlobalDAGData.nodes 11 ⟨1345990, by decide⟩ =
    .split (coordinate 10) (![⟨1345633, by decide⟩,⟨1345714, by decide⟩,⟨1345785, by decide⟩,⟨1345989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23441_1345990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23441 ⟨1345990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23441
    ⟨1345990, by decide⟩ (by decide) (![⟨1345633, by decide⟩,⟨1345714, by decide⟩,⟨1345785, by decide⟩,⟨1345989, by decide⟩]) unmarked_context_10_23441_1345990 node_context_10_23441_1345990
  intro a
  fin_cases a
  · exact context_11_93764_1345633
  · exact context_11_93765_1345714
  · exact context_11_93766_1345785
  · exact context_11_93767_1345989

theorem selected_cut_48039 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375072) = some ⟨12, 1, 0, 435790, 375072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375072_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375072 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375072 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375072, 1, 65536⟩
    (by decide) selected_cut_48039

theorem selected_cut_48040 : selected 9 ⟨1346032, by decide⟩
    (prefixPartial 12 375073) = some ⟨12, 2, 0, 1346032, 375073, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_375073_1346032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375073 ⟨1346032, by decide⟩ :=
  accepted_of_selected 12 375073 ⟨1346032, by decide⟩ ⟨12, 2, 0, 1346032, 375073, 2377, 65536⟩
    (by decide) selected_cut_48040

theorem selected_cut_48041 : selected 9 ⟨1346067, by decide⟩
    (prefixPartial 12 375074) = some ⟨12, 2, 0, 1346067, 375074, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_375074_1346067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375074 ⟨1346067, by decide⟩ :=
  accepted_of_selected 12 375074 ⟨1346067, by decide⟩ ⟨12, 2, 0, 1346067, 375074, 1961, 65536⟩
    (by decide) selected_cut_48041

theorem selected_cut_48042 : selected 9 ⟨1346102, by decide⟩
    (prefixPartial 12 375075) = some ⟨12, 2, 0, 1346102, 375075, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_375075_1346102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375075 ⟨1346102, by decide⟩ :=
  accepted_of_selected 12 375075 ⟨1346102, by decide⟩ ⟨12, 2, 0, 1346102, 375075, 1933, 65536⟩
    (by decide) selected_cut_48042

theorem unmarked_context_11_93768_1346103 : frontier 10 ⟨1346103, by decide⟩
    (prefixCache 11 93768) (prefixPartial 11 93768) = false := by
  decide +kernel

theorem node_context_11_93768_1346103 : EJMOriginalGlobalDAGData.nodes 10 ⟨1346103, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1346032, by decide⟩,⟨1346067, by decide⟩,⟨1346102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93768_1346103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93768 ⟨1346103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93768
    ⟨1346103, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1346032, by decide⟩,⟨1346067, by decide⟩,⟨1346102, by decide⟩]) unmarked_context_11_93768_1346103 node_context_11_93768_1346103
  intro a
  fin_cases a
  · exact context_12_375072_435790
  · exact context_12_375073_1346032
  · exact context_12_375074_1346067
  · exact context_12_375075_1346102

theorem selected_cut_48043 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375076) = some ⟨12, 1, 0, 435790, 375076, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375076_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375076 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375076 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375076, 1, 65536⟩
    (by decide) selected_cut_48043

theorem selected_cut_48044 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 375077) = some ⟨12, 1, 0, 891951, 375077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375077_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375077 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 375077 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 375077, 1, 65536⟩
    (by decide) selected_cut_48044

theorem selected_cut_48045 : selected 9 ⟨1346139, by decide⟩
    (prefixPartial 12 375078) = some ⟨12, 2, 0, 1346139, 375078, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_375078_1346139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375078 ⟨1346139, by decide⟩ :=
  accepted_of_selected 12 375078 ⟨1346139, by decide⟩ ⟨12, 2, 0, 1346139, 375078, 2221, 65536⟩
    (by decide) selected_cut_48045

theorem selected_cut_48046 : selected 9 ⟨1346173, by decide⟩
    (prefixPartial 12 375079) = some ⟨12, 2, 0, 1346173, 375079, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_375079_1346173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375079 ⟨1346173, by decide⟩ :=
  accepted_of_selected 12 375079 ⟨1346173, by decide⟩ ⟨12, 2, 0, 1346173, 375079, 2065, 65536⟩
    (by decide) selected_cut_48046

theorem unmarked_context_11_93769_1346174 : frontier 10 ⟨1346174, by decide⟩
    (prefixCache 11 93769) (prefixPartial 11 93769) = false := by
  decide +kernel

theorem node_context_11_93769_1346174 : EJMOriginalGlobalDAGData.nodes 10 ⟨1346174, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1346139, by decide⟩,⟨1346173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93769_1346174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93769 ⟨1346174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93769
    ⟨1346174, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1346139, by decide⟩,⟨1346173, by decide⟩]) unmarked_context_11_93769_1346174 node_context_11_93769_1346174
  intro a
  fin_cases a
  · exact context_12_375076_435790
  · exact context_12_375077_891951
  · exact context_12_375078_1346139
  · exact context_12_375079_1346173

theorem selected_cut_48047 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93770) = some ⟨11, 1, 0, 900587, 93770, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93770_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93770 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93770 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93770, 1, 262144⟩
    (by decide) selected_cut_48047

theorem selected_cut_48048 : selected 9 ⟨1346198, by decide⟩
    (prefixPartial 12 375084) = some ⟨12, 2, 0, 1346198, 375084, 1053, 65536⟩ := by
  decide +kernel

theorem context_12_375084_1346198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375084 ⟨1346198, by decide⟩ :=
  accepted_of_selected 12 375084 ⟨1346198, by decide⟩ ⟨12, 2, 0, 1346198, 375084, 1053, 65536⟩
    (by decide) selected_cut_48048

theorem selected_cut_48049 : selected 9 ⟨1346237, by decide⟩
    (prefixPartial 12 375085) = some ⟨12, 2, 0, 1346237, 375085, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_375085_1346237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375085 ⟨1346237, by decide⟩ :=
  accepted_of_selected 12 375085 ⟨1346237, by decide⟩ ⟨12, 2, 0, 1346237, 375085, 2369, 65536⟩
    (by decide) selected_cut_48049

theorem selected_cut_48050 : selected 9 ⟨1346273, by decide⟩
    (prefixPartial 12 375086) = some ⟨12, 2, 0, 1346273, 375086, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_375086_1346273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375086 ⟨1346273, by decide⟩ :=
  accepted_of_selected 12 375086 ⟨1346273, by decide⟩ ⟨12, 2, 0, 1346273, 375086, 2097, 65536⟩
    (by decide) selected_cut_48050

theorem selected_cut_48051 : selected 9 ⟨1346300, by decide⟩
    (prefixPartial 12 375087) = some ⟨12, 2, 0, 1346300, 375087, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_375087_1346300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375087 ⟨1346300, by decide⟩ :=
  accepted_of_selected 12 375087 ⟨1346300, by decide⟩ ⟨12, 2, 0, 1346300, 375087, 1969, 65536⟩
    (by decide) selected_cut_48051

theorem unmarked_context_11_93771_1346301 : frontier 10 ⟨1346301, by decide⟩
    (prefixCache 11 93771) (prefixPartial 11 93771) = false := by
  decide +kernel

theorem node_context_11_93771_1346301 : EJMOriginalGlobalDAGData.nodes 10 ⟨1346301, by decide⟩ =
    .split (coordinate 11) (![⟨1346198, by decide⟩,⟨1346237, by decide⟩,⟨1346273, by decide⟩,⟨1346300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93771_1346301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93771 ⟨1346301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93771
    ⟨1346301, by decide⟩ (by decide) (![⟨1346198, by decide⟩,⟨1346237, by decide⟩,⟨1346273, by decide⟩,⟨1346300, by decide⟩]) unmarked_context_11_93771_1346301 node_context_11_93771_1346301
  intro a
  fin_cases a
  · exact context_12_375084_1346198
  · exact context_12_375085_1346237
  · exact context_12_375086_1346273
  · exact context_12_375087_1346300

theorem unmarked_context_10_23442_1346302 : frontier 11 ⟨1346302, by decide⟩
    (prefixCache 10 23442) (prefixPartial 10 23442) = false := by
  decide +kernel

theorem node_context_10_23442_1346302 : EJMOriginalGlobalDAGData.nodes 11 ⟨1346302, by decide⟩ =
    .split (coordinate 10) (![⟨1346103, by decide⟩,⟨1346174, by decide⟩,⟨900587, by decide⟩,⟨1346301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23442_1346302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23442 ⟨1346302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23442
    ⟨1346302, by decide⟩ (by decide) (![⟨1346103, by decide⟩,⟨1346174, by decide⟩,⟨900587, by decide⟩,⟨1346301, by decide⟩]) unmarked_context_10_23442_1346302 node_context_10_23442_1346302
  intro a
  fin_cases a
  · exact context_11_93768_1346103
  · exact context_11_93769_1346174
  · exact context_11_93770_900587
  · exact context_11_93771_1346301

theorem selected_cut_48052 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 375088) = some ⟨12, 1, 0, 1255011, 375088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375088_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375088 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 375088 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 375088, 1, 65536⟩
    (by decide) selected_cut_48052

theorem selected_cut_48053 : selected 9 ⟨1346333, by decide⟩
    (prefixPartial 12 375089) = some ⟨12, 2, 0, 1346333, 375089, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_375089_1346333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375089 ⟨1346333, by decide⟩ :=
  accepted_of_selected 12 375089 ⟨1346333, by decide⟩ ⟨12, 2, 0, 1346333, 375089, 2021, 65536⟩
    (by decide) selected_cut_48053

theorem selected_cut_48054 : selected 9 ⟨1346370, by decide⟩
    (prefixPartial 12 375090) = some ⟨12, 2, 0, 1346370, 375090, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_375090_1346370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375090 ⟨1346370, by decide⟩ :=
  accepted_of_selected 12 375090 ⟨1346370, by decide⟩ ⟨12, 2, 0, 1346370, 375090, 1821, 65536⟩
    (by decide) selected_cut_48054

theorem selected_cut_48055 : selected 9 ⟨1346405, by decide⟩
    (prefixPartial 12 375091) = some ⟨12, 2, 0, 1346405, 375091, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_375091_1346405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375091 ⟨1346405, by decide⟩ :=
  accepted_of_selected 12 375091 ⟨1346405, by decide⟩ ⟨12, 2, 0, 1346405, 375091, 1805, 65536⟩
    (by decide) selected_cut_48055

theorem unmarked_context_11_93772_1346406 : frontier 10 ⟨1346406, by decide⟩
    (prefixCache 11 93772) (prefixPartial 11 93772) = false := by
  decide +kernel

theorem node_context_11_93772_1346406 : EJMOriginalGlobalDAGData.nodes 10 ⟨1346406, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1346333, by decide⟩,⟨1346370, by decide⟩,⟨1346405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93772_1346406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93772 ⟨1346406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93772
    ⟨1346406, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1346333, by decide⟩,⟨1346370, by decide⟩,⟨1346405, by decide⟩]) unmarked_context_11_93772_1346406 node_context_11_93772_1346406
  intro a
  fin_cases a
  · exact context_12_375088_1255011
  · exact context_12_375089_1346333
  · exact context_12_375090_1346370
  · exact context_12_375091_1346405

theorem selected_cut_48056 : selected 9 ⟨1346448, by decide⟩
    (prefixPartial 12 375092) = some ⟨12, 2, 0, 1346448, 375092, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_375092_1346448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375092 ⟨1346448, by decide⟩ :=
  accepted_of_selected 12 375092 ⟨1346448, by decide⟩ ⟨12, 2, 0, 1346448, 375092, 2017, 65536⟩
    (by decide) selected_cut_48056

theorem selected_cut_48057 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 375093) = some ⟨12, 1, 0, 891951, 375093, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375093_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375093 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 375093 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 375093, 1, 65536⟩
    (by decide) selected_cut_48057

theorem selected_cut_48058 : selected 9 ⟨1346486, by decide⟩
    (prefixPartial 12 375094) = some ⟨12, 2, 0, 1346486, 375094, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_375094_1346486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375094 ⟨1346486, by decide⟩ :=
  accepted_of_selected 12 375094 ⟨1346486, by decide⟩ ⟨12, 2, 0, 1346486, 375094, 1973, 65536⟩
    (by decide) selected_cut_48058

theorem selected_cut_48059 : selected 9 ⟨1346521, by decide⟩
    (prefixPartial 12 375095) = some ⟨12, 2, 0, 1346521, 375095, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_375095_1346521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375095 ⟨1346521, by decide⟩ :=
  accepted_of_selected 12 375095 ⟨1346521, by decide⟩ ⟨12, 2, 0, 1346521, 375095, 1853, 65536⟩
    (by decide) selected_cut_48059

theorem unmarked_context_11_93773_1346522 : frontier 10 ⟨1346522, by decide⟩
    (prefixCache 11 93773) (prefixPartial 11 93773) = false := by
  decide +kernel

theorem node_context_11_93773_1346522 : EJMOriginalGlobalDAGData.nodes 10 ⟨1346522, by decide⟩ =
    .split (coordinate 11) (![⟨1346448, by decide⟩,⟨891951, by decide⟩,⟨1346486, by decide⟩,⟨1346521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93773_1346522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93773 ⟨1346522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93773
    ⟨1346522, by decide⟩ (by decide) (![⟨1346448, by decide⟩,⟨891951, by decide⟩,⟨1346486, by decide⟩,⟨1346521, by decide⟩]) unmarked_context_11_93773_1346522 node_context_11_93773_1346522
  intro a
  fin_cases a
  · exact context_12_375092_1346448
  · exact context_12_375093_891951
  · exact context_12_375094_1346486
  · exact context_12_375095_1346521

theorem selected_cut_48060 : selected 9 ⟨1346578, by decide⟩
    (prefixPartial 12 375096) = some ⟨12, 2, 0, 1346578, 375096, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_375096_1346578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375096 ⟨1346578, by decide⟩ :=
  accepted_of_selected 12 375096 ⟨1346578, by decide⟩ ⟨12, 2, 0, 1346578, 375096, 1157, 65536⟩
    (by decide) selected_cut_48060

theorem selected_cut_48061 : selected 9 ⟨1346603, by decide⟩
    (prefixPartial 12 375097) = some ⟨12, 2, 0, 1346603, 375097, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_375097_1346603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375097 ⟨1346603, by decide⟩ :=
  accepted_of_selected 12 375097 ⟨1346603, by decide⟩ ⟨12, 2, 0, 1346603, 375097, 1613, 65536⟩
    (by decide) selected_cut_48061

theorem selected_cut_48062 : selected 9 ⟨1346634, by decide⟩
    (prefixPartial 12 375098) = some ⟨12, 2, 0, 1346634, 375098, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_375098_1346634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375098 ⟨1346634, by decide⟩ :=
  accepted_of_selected 12 375098 ⟨1346634, by decide⟩ ⟨12, 2, 0, 1346634, 375098, 1673, 65536⟩
    (by decide) selected_cut_48062

theorem selected_cut_48063 : selected 9 ⟨1346659, by decide⟩
    (prefixPartial 12 375099) = some ⟨12, 2, 0, 1346659, 375099, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_375099_1346659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375099 ⟨1346659, by decide⟩ :=
  accepted_of_selected 12 375099 ⟨1346659, by decide⟩ ⟨12, 2, 0, 1346659, 375099, 1481, 65536⟩
    (by decide) selected_cut_48063

theorem unmarked_context_11_93774_1346660 : frontier 10 ⟨1346660, by decide⟩
    (prefixCache 11 93774) (prefixPartial 11 93774) = false := by
  decide +kernel

theorem node_context_11_93774_1346660 : EJMOriginalGlobalDAGData.nodes 10 ⟨1346660, by decide⟩ =
    .split (coordinate 11) (![⟨1346578, by decide⟩,⟨1346603, by decide⟩,⟨1346634, by decide⟩,⟨1346659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93774_1346660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93774 ⟨1346660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93774
    ⟨1346660, by decide⟩ (by decide) (![⟨1346578, by decide⟩,⟨1346603, by decide⟩,⟨1346634, by decide⟩,⟨1346659, by decide⟩]) unmarked_context_11_93774_1346660 node_context_11_93774_1346660
  intro a
  fin_cases a
  · exact context_12_375096_1346578
  · exact context_12_375097_1346603
  · exact context_12_375098_1346634
  · exact context_12_375099_1346659

theorem selected_cut_48064 : selected 10 ⟨1346765, by decide⟩
    (prefixPartial 11 93775) = some ⟨11, 2, 0, 1346765, 93775, 3693, 262144⟩ := by
  decide +kernel

theorem context_11_93775_1346765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93775 ⟨1346765, by decide⟩ :=
  accepted_of_selected 11 93775 ⟨1346765, by decide⟩ ⟨11, 2, 0, 1346765, 93775, 3693, 262144⟩
    (by decide) selected_cut_48064

theorem unmarked_context_10_23443_1346766 : frontier 11 ⟨1346766, by decide⟩
    (prefixCache 10 23443) (prefixPartial 10 23443) = false := by
  decide +kernel

theorem node_context_10_23443_1346766 : EJMOriginalGlobalDAGData.nodes 11 ⟨1346766, by decide⟩ =
    .split (coordinate 10) (![⟨1346406, by decide⟩,⟨1346522, by decide⟩,⟨1346660, by decide⟩,⟨1346765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23443_1346766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23443 ⟨1346766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23443
    ⟨1346766, by decide⟩ (by decide) (![⟨1346406, by decide⟩,⟨1346522, by decide⟩,⟨1346660, by decide⟩,⟨1346765, by decide⟩]) unmarked_context_10_23443_1346766 node_context_10_23443_1346766
  intro a
  fin_cases a
  · exact context_11_93772_1346406
  · exact context_11_93773_1346522
  · exact context_11_93774_1346660
  · exact context_11_93775_1346765

theorem unmarked_context_9_5860_1346767 : frontier 12 ⟨1346767, by decide⟩
    (prefixCache 9 5860) (prefixPartial 9 5860) = false := by
  decide +kernel

theorem node_context_9_5860_1346767 : EJMOriginalGlobalDAGData.nodes 12 ⟨1346767, by decide⟩ =
    .split (coordinate 9) (![⟨1345493, by decide⟩,⟨1345990, by decide⟩,⟨1346302, by decide⟩,⟨1346766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5860_1346767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5860 ⟨1346767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5860
    ⟨1346767, by decide⟩ (by decide) (![⟨1345493, by decide⟩,⟨1345990, by decide⟩,⟨1346302, by decide⟩,⟨1346766, by decide⟩]) unmarked_context_9_5860_1346767 node_context_9_5860_1346767
  intro a
  fin_cases a
  · exact context_10_23440_1345493
  · exact context_10_23441_1345990
  · exact context_10_23442_1346302
  · exact context_10_23443_1346766

theorem selected_cut_48065 : selected 10 ⟨1346823, by decide⟩
    (prefixPartial 11 93776) = some ⟨11, 2, 0, 1346823, 93776, 2701, 262144⟩ := by
  decide +kernel

theorem context_11_93776_1346823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93776 ⟨1346823, by decide⟩ :=
  accepted_of_selected 11 93776 ⟨1346823, by decide⟩ ⟨11, 2, 0, 1346823, 93776, 2701, 262144⟩
    (by decide) selected_cut_48065

theorem selected_cut_48066 : selected 9 ⟨1346851, by decide⟩
    (prefixPartial 12 375108) = some ⟨12, 2, 0, 1346851, 375108, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_375108_1346851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375108 ⟨1346851, by decide⟩ :=
  accepted_of_selected 12 375108 ⟨1346851, by decide⟩ ⟨12, 2, 0, 1346851, 375108, 1577, 65536⟩
    (by decide) selected_cut_48066

theorem selected_cut_48067 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 375109) = some ⟨12, 1, 0, 891951, 375109, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375109_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375109 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 375109 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 375109, 1, 65536⟩
    (by decide) selected_cut_48067

theorem selected_cut_48068 : selected 9 ⟨1346874, by decide⟩
    (prefixPartial 12 375110) = some ⟨12, 2, 0, 1346874, 375110, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_375110_1346874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375110 ⟨1346874, by decide⟩ :=
  accepted_of_selected 12 375110 ⟨1346874, by decide⟩ ⟨12, 2, 0, 1346874, 375110, 1481, 65536⟩
    (by decide) selected_cut_48068

theorem selected_cut_48069 : selected 9 ⟨1346896, by decide⟩
    (prefixPartial 12 375111) = some ⟨12, 2, 0, 1346896, 375111, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_375111_1346896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375111 ⟨1346896, by decide⟩ :=
  accepted_of_selected 12 375111 ⟨1346896, by decide⟩ ⟨12, 2, 0, 1346896, 375111, 1365, 65536⟩
    (by decide) selected_cut_48069

theorem unmarked_context_11_93777_1346897 : frontier 10 ⟨1346897, by decide⟩
    (prefixCache 11 93777) (prefixPartial 11 93777) = false := by
  decide +kernel

theorem node_context_11_93777_1346897 : EJMOriginalGlobalDAGData.nodes 10 ⟨1346897, by decide⟩ =
    .split (coordinate 11) (![⟨1346851, by decide⟩,⟨891951, by decide⟩,⟨1346874, by decide⟩,⟨1346896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93777_1346897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93777 ⟨1346897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93777
    ⟨1346897, by decide⟩ (by decide) (![⟨1346851, by decide⟩,⟨891951, by decide⟩,⟨1346874, by decide⟩,⟨1346896, by decide⟩]) unmarked_context_11_93777_1346897 node_context_11_93777_1346897
  intro a
  fin_cases a
  · exact context_12_375108_1346851
  · exact context_12_375109_891951
  · exact context_12_375110_1346874
  · exact context_12_375111_1346896

theorem selected_cut_48070 : selected 10 ⟨1346940, by decide⟩
    (prefixPartial 11 93778) = some ⟨11, 2, 0, 1346940, 93778, 2621, 262144⟩ := by
  decide +kernel

theorem context_11_93778_1346940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93778 ⟨1346940, by decide⟩ :=
  accepted_of_selected 11 93778 ⟨1346940, by decide⟩ ⟨11, 2, 0, 1346940, 93778, 2621, 262144⟩
    (by decide) selected_cut_48070

theorem selected_cut_48071 : selected 9 ⟨1346963, by decide⟩
    (prefixPartial 12 375116) = some ⟨12, 2, 0, 1346963, 375116, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_375116_1346963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375116 ⟨1346963, by decide⟩ :=
  accepted_of_selected 12 375116 ⟨1346963, by decide⟩ ⟨12, 2, 0, 1346963, 375116, 1421, 65536⟩
    (by decide) selected_cut_48071

theorem selected_cut_48072 : selected 9 ⟨1346988, by decide⟩
    (prefixPartial 12 375117) = some ⟨12, 2, 0, 1346988, 375117, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_375117_1346988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375117 ⟨1346988, by decide⟩ :=
  accepted_of_selected 12 375117 ⟨1346988, by decide⟩ ⟨12, 2, 0, 1346988, 375117, 1433, 65536⟩
    (by decide) selected_cut_48072

theorem selected_cut_48073 : selected 9 ⟨1347012, by decide⟩
    (prefixPartial 12 375118) = some ⟨12, 2, 0, 1347012, 375118, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_375118_1347012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375118 ⟨1347012, by decide⟩ :=
  accepted_of_selected 12 375118 ⟨1347012, by decide⟩ ⟨12, 2, 0, 1347012, 375118, 1477, 65536⟩
    (by decide) selected_cut_48073

theorem selected_cut_48074 : selected 9 ⟨1347042, by decide⟩
    (prefixPartial 12 375119) = some ⟨12, 2, 0, 1347042, 375119, 713, 65536⟩ := by
  decide +kernel

theorem context_12_375119_1347042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375119 ⟨1347042, by decide⟩ :=
  accepted_of_selected 12 375119 ⟨1347042, by decide⟩ ⟨12, 2, 0, 1347042, 375119, 713, 65536⟩
    (by decide) selected_cut_48074

theorem unmarked_context_11_93779_1347043 : frontier 10 ⟨1347043, by decide⟩
    (prefixCache 11 93779) (prefixPartial 11 93779) = false := by
  decide +kernel

theorem node_context_11_93779_1347043 : EJMOriginalGlobalDAGData.nodes 10 ⟨1347043, by decide⟩ =
    .split (coordinate 11) (![⟨1346963, by decide⟩,⟨1346988, by decide⟩,⟨1347012, by decide⟩,⟨1347042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93779_1347043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93779 ⟨1347043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93779
    ⟨1347043, by decide⟩ (by decide) (![⟨1346963, by decide⟩,⟨1346988, by decide⟩,⟨1347012, by decide⟩,⟨1347042, by decide⟩]) unmarked_context_11_93779_1347043 node_context_11_93779_1347043
  intro a
  fin_cases a
  · exact context_12_375116_1346963
  · exact context_12_375117_1346988
  · exact context_12_375118_1347012
  · exact context_12_375119_1347042

theorem unmarked_context_10_23444_1347044 : frontier 11 ⟨1347044, by decide⟩
    (prefixCache 10 23444) (prefixPartial 10 23444) = false := by
  decide +kernel

theorem node_context_10_23444_1347044 : EJMOriginalGlobalDAGData.nodes 11 ⟨1347044, by decide⟩ =
    .split (coordinate 10) (![⟨1346823, by decide⟩,⟨1346897, by decide⟩,⟨1346940, by decide⟩,⟨1347043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23444_1347044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23444 ⟨1347044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23444
    ⟨1347044, by decide⟩ (by decide) (![⟨1346823, by decide⟩,⟨1346897, by decide⟩,⟨1346940, by decide⟩,⟨1347043, by decide⟩]) unmarked_context_10_23444_1347044 node_context_10_23444_1347044
  intro a
  fin_cases a
  · exact context_11_93776_1346823
  · exact context_11_93777_1346897
  · exact context_11_93778_1346940
  · exact context_11_93779_1347043

theorem selected_cut_48075 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23445) = some ⟨10, 1, 0, 893098, 23445, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23445_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23445 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23445 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23445, 1, 1048576⟩
    (by decide) selected_cut_48075

theorem selected_cut_48076 : selected 10 ⟨1347075, by decide⟩
    (prefixPartial 11 93784) = some ⟨11, 2, 0, 1347075, 93784, 1997, 262144⟩ := by
  decide +kernel

theorem context_11_93784_1347075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93784 ⟨1347075, by decide⟩ :=
  accepted_of_selected 11 93784 ⟨1347075, by decide⟩ ⟨11, 2, 0, 1347075, 93784, 1997, 262144⟩
    (by decide) selected_cut_48076

theorem selected_cut_48077 : selected 10 ⟨1347136, by decide⟩
    (prefixPartial 11 93785) = some ⟨11, 2, 0, 1347136, 93785, 3161, 262144⟩ := by
  decide +kernel

theorem context_11_93785_1347136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93785 ⟨1347136, by decide⟩ :=
  accepted_of_selected 11 93785 ⟨1347136, by decide⟩ ⟨11, 2, 0, 1347136, 93785, 3161, 262144⟩
    (by decide) selected_cut_48077

theorem selected_cut_48078 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 93786) = some ⟨11, 1, 0, 900587, 93786, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93786_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93786 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 93786 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 93786, 1, 262144⟩
    (by decide) selected_cut_48078

theorem selected_cut_48079 : selected 10 ⟨1347169, by decide⟩
    (prefixPartial 11 93787) = some ⟨11, 2, 0, 1347169, 93787, 2097, 262144⟩ := by
  decide +kernel

theorem context_11_93787_1347169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93787 ⟨1347169, by decide⟩ :=
  accepted_of_selected 11 93787 ⟨1347169, by decide⟩ ⟨11, 2, 0, 1347169, 93787, 2097, 262144⟩
    (by decide) selected_cut_48079

theorem unmarked_context_10_23446_1347170 : frontier 11 ⟨1347170, by decide⟩
    (prefixCache 10 23446) (prefixPartial 10 23446) = false := by
  decide +kernel

theorem node_context_10_23446_1347170 : EJMOriginalGlobalDAGData.nodes 11 ⟨1347170, by decide⟩ =
    .split (coordinate 10) (![⟨1347075, by decide⟩,⟨1347136, by decide⟩,⟨900587, by decide⟩,⟨1347169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23446_1347170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23446 ⟨1347170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23446
    ⟨1347170, by decide⟩ (by decide) (![⟨1347075, by decide⟩,⟨1347136, by decide⟩,⟨900587, by decide⟩,⟨1347169, by decide⟩]) unmarked_context_10_23446_1347170 node_context_10_23446_1347170
  intro a
  fin_cases a
  · exact context_11_93784_1347075
  · exact context_11_93785_1347136
  · exact context_11_93786_900587
  · exact context_11_93787_1347169

theorem selected_cut_48080 : selected 10 ⟨1347240, by decide⟩
    (prefixPartial 11 93788) = some ⟨11, 2, 0, 1347240, 93788, 3297, 262144⟩ := by
  decide +kernel

theorem context_11_93788_1347240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93788 ⟨1347240, by decide⟩ :=
  accepted_of_selected 11 93788 ⟨1347240, by decide⟩ ⟨11, 2, 0, 1347240, 93788, 3297, 262144⟩
    (by decide) selected_cut_48080

theorem selected_cut_48081 : selected 10 ⟨1347286, by decide⟩
    (prefixPartial 11 93789) = some ⟨11, 2, 0, 1347286, 93789, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_93789_1347286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93789 ⟨1347286, by decide⟩ :=
  accepted_of_selected 11 93789 ⟨1347286, by decide⟩ ⟨11, 2, 0, 1347286, 93789, 2817, 262144⟩
    (by decide) selected_cut_48081

theorem selected_cut_48082 : selected 10 ⟨1347315, by decide⟩
    (prefixPartial 11 93790) = some ⟨11, 2, 0, 1347315, 93790, 1617, 262144⟩ := by
  decide +kernel

theorem context_11_93790_1347315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93790 ⟨1347315, by decide⟩ :=
  accepted_of_selected 11 93790 ⟨1347315, by decide⟩ ⟨11, 2, 0, 1347315, 93790, 1617, 262144⟩
    (by decide) selected_cut_48082

theorem selected_cut_48083 : selected 10 ⟨1347341, by decide⟩
    (prefixPartial 11 93791) = some ⟨11, 2, 0, 1347341, 93791, 1689, 262144⟩ := by
  decide +kernel

theorem context_11_93791_1347341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93791 ⟨1347341, by decide⟩ :=
  accepted_of_selected 11 93791 ⟨1347341, by decide⟩ ⟨11, 2, 0, 1347341, 93791, 1689, 262144⟩
    (by decide) selected_cut_48083

theorem unmarked_context_10_23447_1347342 : frontier 11 ⟨1347342, by decide⟩
    (prefixCache 10 23447) (prefixPartial 10 23447) = false := by
  decide +kernel

theorem node_context_10_23447_1347342 : EJMOriginalGlobalDAGData.nodes 11 ⟨1347342, by decide⟩ =
    .split (coordinate 10) (![⟨1347240, by decide⟩,⟨1347286, by decide⟩,⟨1347315, by decide⟩,⟨1347341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23447_1347342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23447 ⟨1347342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23447
    ⟨1347342, by decide⟩ (by decide) (![⟨1347240, by decide⟩,⟨1347286, by decide⟩,⟨1347315, by decide⟩,⟨1347341, by decide⟩]) unmarked_context_10_23447_1347342 node_context_10_23447_1347342
  intro a
  fin_cases a
  · exact context_11_93788_1347240
  · exact context_11_93789_1347286
  · exact context_11_93790_1347315
  · exact context_11_93791_1347341

theorem unmarked_context_9_5861_1347343 : frontier 12 ⟨1347343, by decide⟩
    (prefixCache 9 5861) (prefixPartial 9 5861) = false := by
  decide +kernel

theorem node_context_9_5861_1347343 : EJMOriginalGlobalDAGData.nodes 12 ⟨1347343, by decide⟩ =
    .split (coordinate 9) (![⟨1347044, by decide⟩,⟨893098, by decide⟩,⟨1347170, by decide⟩,⟨1347342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5861_1347343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5861 ⟨1347343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5861
    ⟨1347343, by decide⟩ (by decide) (![⟨1347044, by decide⟩,⟨893098, by decide⟩,⟨1347170, by decide⟩,⟨1347342, by decide⟩]) unmarked_context_9_5861_1347343 node_context_9_5861_1347343
  intro a
  fin_cases a
  · exact context_10_23444_1347044
  · exact context_10_23445_893098
  · exact context_10_23446_1347170
  · exact context_10_23447_1347342

theorem selected_cut_48084 : selected 10 ⟨1347344, by decide⟩
    (prefixPartial 11 93792) = some ⟨11, 2, 0, 1347344, 93792, 5, 262144⟩ := by
  decide +kernel

theorem context_11_93792_1347344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93792 ⟨1347344, by decide⟩ :=
  accepted_of_selected 11 93792 ⟨1347344, by decide⟩ ⟨11, 2, 0, 1347344, 93792, 5, 262144⟩
    (by decide) selected_cut_48084

theorem selected_cut_48085 : selected 10 ⟨1347387, by decide⟩
    (prefixPartial 11 93793) = some ⟨11, 2, 0, 1347387, 93793, 2093, 262144⟩ := by
  decide +kernel

theorem context_11_93793_1347387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93793 ⟨1347387, by decide⟩ :=
  accepted_of_selected 11 93793 ⟨1347387, by decide⟩ ⟨11, 2, 0, 1347387, 93793, 2093, 262144⟩
    (by decide) selected_cut_48085

theorem selected_cut_48086 : selected 10 ⟨1347439, by decide⟩
    (prefixPartial 11 93794) = some ⟨11, 2, 0, 1347439, 93794, 2693, 262144⟩ := by
  decide +kernel

theorem context_11_93794_1347439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93794 ⟨1347439, by decide⟩ :=
  accepted_of_selected 11 93794 ⟨1347439, by decide⟩ ⟨11, 2, 0, 1347439, 93794, 2693, 262144⟩
    (by decide) selected_cut_48086

theorem selected_cut_48087 : selected 10 ⟨1347499, by decide⟩
    (prefixPartial 11 93795) = some ⟨11, 2, 0, 1347499, 93795, 2701, 262144⟩ := by
  decide +kernel

theorem context_11_93795_1347499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93795 ⟨1347499, by decide⟩ :=
  accepted_of_selected 11 93795 ⟨1347499, by decide⟩ ⟨11, 2, 0, 1347499, 93795, 2701, 262144⟩
    (by decide) selected_cut_48087

theorem unmarked_context_10_23448_1347500 : frontier 11 ⟨1347500, by decide⟩
    (prefixCache 10 23448) (prefixPartial 10 23448) = false := by
  decide +kernel

theorem node_context_10_23448_1347500 : EJMOriginalGlobalDAGData.nodes 11 ⟨1347500, by decide⟩ =
    .split (coordinate 10) (![⟨1347344, by decide⟩,⟨1347387, by decide⟩,⟨1347439, by decide⟩,⟨1347499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23448_1347500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23448 ⟨1347500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23448
    ⟨1347500, by decide⟩ (by decide) (![⟨1347344, by decide⟩,⟨1347387, by decide⟩,⟨1347439, by decide⟩,⟨1347499, by decide⟩]) unmarked_context_10_23448_1347500 node_context_10_23448_1347500
  intro a
  fin_cases a
  · exact context_11_93792_1347344
  · exact context_11_93793_1347387
  · exact context_11_93794_1347439
  · exact context_11_93795_1347499

theorem selected_cut_48088 : selected 10 ⟨1347531, by decide⟩
    (prefixPartial 11 93796) = some ⟨11, 2, 0, 1347531, 93796, 1541, 262144⟩ := by
  decide +kernel

theorem context_11_93796_1347531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93796 ⟨1347531, by decide⟩ :=
  accepted_of_selected 11 93796 ⟨1347531, by decide⟩ ⟨11, 2, 0, 1347531, 93796, 1541, 262144⟩
    (by decide) selected_cut_48088

theorem selected_cut_48089 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 93797) = some ⟨11, 1, 0, 1192826, 93797, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93797_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93797 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 93797 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 93797, 1, 262144⟩
    (by decide) selected_cut_48089

theorem selected_cut_48090 : selected 10 ⟨1347566, by decide⟩
    (prefixPartial 11 93798) = some ⟨11, 2, 0, 1347566, 93798, 1909, 262144⟩ := by
  decide +kernel

theorem context_11_93798_1347566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93798 ⟨1347566, by decide⟩ :=
  accepted_of_selected 11 93798 ⟨1347566, by decide⟩ ⟨11, 2, 0, 1347566, 93798, 1909, 262144⟩
    (by decide) selected_cut_48090

theorem selected_cut_48091 : selected 10 ⟨1347589, by decide⟩
    (prefixPartial 11 93799) = some ⟨11, 2, 0, 1347589, 93799, 1225, 262144⟩ := by
  decide +kernel

theorem context_11_93799_1347589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93799 ⟨1347589, by decide⟩ :=
  accepted_of_selected 11 93799 ⟨1347589, by decide⟩ ⟨11, 2, 0, 1347589, 93799, 1225, 262144⟩
    (by decide) selected_cut_48091

theorem unmarked_context_10_23449_1347590 : frontier 11 ⟨1347590, by decide⟩
    (prefixCache 10 23449) (prefixPartial 10 23449) = false := by
  decide +kernel

theorem node_context_10_23449_1347590 : EJMOriginalGlobalDAGData.nodes 11 ⟨1347590, by decide⟩ =
    .split (coordinate 10) (![⟨1347531, by decide⟩,⟨1192826, by decide⟩,⟨1347566, by decide⟩,⟨1347589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23449_1347590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23449 ⟨1347590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23449
    ⟨1347590, by decide⟩ (by decide) (![⟨1347531, by decide⟩,⟨1192826, by decide⟩,⟨1347566, by decide⟩,⟨1347589, by decide⟩]) unmarked_context_10_23449_1347590 node_context_10_23449_1347590
  intro a
  fin_cases a
  · exact context_11_93796_1347531
  · exact context_11_93797_1192826
  · exact context_11_93798_1347566
  · exact context_11_93799_1347589

theorem selected_cut_48092 : selected 11 ⟨1347641, by decide⟩
    (prefixPartial 10 23450) = some ⟨10, 2, 0, 1347641, 23450, 2245, 1048576⟩ := by
  decide +kernel

theorem context_10_23450_1347641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23450 ⟨1347641, by decide⟩ :=
  accepted_of_selected 10 23450 ⟨1347641, by decide⟩ ⟨10, 2, 0, 1347641, 23450, 2245, 1048576⟩
    (by decide) selected_cut_48092

theorem selected_cut_48093 : selected 11 ⟨1347716, by decide⟩
    (prefixPartial 10 23451) = some ⟨10, 2, 0, 1347716, 23451, 3533, 1048576⟩ := by
  decide +kernel

theorem context_10_23451_1347716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23451 ⟨1347716, by decide⟩ :=
  accepted_of_selected 10 23451 ⟨1347716, by decide⟩ ⟨10, 2, 0, 1347716, 23451, 3533, 1048576⟩
    (by decide) selected_cut_48093

theorem unmarked_context_9_5862_1347717 : frontier 12 ⟨1347717, by decide⟩
    (prefixCache 9 5862) (prefixPartial 9 5862) = false := by
  decide +kernel

theorem node_context_9_5862_1347717 : EJMOriginalGlobalDAGData.nodes 12 ⟨1347717, by decide⟩ =
    .split (coordinate 9) (![⟨1347500, by decide⟩,⟨1347590, by decide⟩,⟨1347641, by decide⟩,⟨1347716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5862_1347717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5862 ⟨1347717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5862
    ⟨1347717, by decide⟩ (by decide) (![⟨1347500, by decide⟩,⟨1347590, by decide⟩,⟨1347641, by decide⟩,⟨1347716, by decide⟩]) unmarked_context_9_5862_1347717 node_context_9_5862_1347717
  intro a
  fin_cases a
  · exact context_10_23448_1347500
  · exact context_10_23449_1347590
  · exact context_10_23450_1347641
  · exact context_10_23451_1347716

theorem selected_cut_48094 : selected 10 ⟨1347742, by decide⟩
    (prefixPartial 11 93808) = some ⟨11, 2, 0, 1347742, 93808, 905, 262144⟩ := by
  decide +kernel

theorem context_11_93808_1347742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93808 ⟨1347742, by decide⟩ :=
  accepted_of_selected 11 93808 ⟨1347742, by decide⟩ ⟨11, 2, 0, 1347742, 93808, 905, 262144⟩
    (by decide) selected_cut_48094

theorem selected_cut_48095 : selected 10 ⟨1347771, by decide⟩
    (prefixPartial 11 93809) = some ⟨11, 2, 0, 1347771, 93809, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_93809_1347771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93809 ⟨1347771, by decide⟩ :=
  accepted_of_selected 11 93809 ⟨1347771, by decide⟩ ⟨11, 2, 0, 1347771, 93809, 1309, 262144⟩
    (by decide) selected_cut_48095

theorem selected_cut_48096 : selected 10 ⟨1347797, by decide⟩
    (prefixPartial 11 93810) = some ⟨11, 2, 0, 1347797, 93810, 1213, 262144⟩ := by
  decide +kernel

theorem context_11_93810_1347797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93810 ⟨1347797, by decide⟩ :=
  accepted_of_selected 11 93810 ⟨1347797, by decide⟩ ⟨11, 2, 0, 1347797, 93810, 1213, 262144⟩
    (by decide) selected_cut_48096

theorem selected_cut_48097 : selected 10 ⟨1347836, by decide⟩
    (prefixPartial 11 93811) = some ⟨11, 2, 0, 1347836, 93811, 1245, 262144⟩ := by
  decide +kernel

theorem context_11_93811_1347836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93811 ⟨1347836, by decide⟩ :=
  accepted_of_selected 11 93811 ⟨1347836, by decide⟩ ⟨11, 2, 0, 1347836, 93811, 1245, 262144⟩
    (by decide) selected_cut_48097

theorem unmarked_context_10_23452_1347837 : frontier 11 ⟨1347837, by decide⟩
    (prefixCache 10 23452) (prefixPartial 10 23452) = false := by
  decide +kernel

theorem node_context_10_23452_1347837 : EJMOriginalGlobalDAGData.nodes 11 ⟨1347837, by decide⟩ =
    .split (coordinate 10) (![⟨1347742, by decide⟩,⟨1347771, by decide⟩,⟨1347797, by decide⟩,⟨1347836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23452_1347837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23452 ⟨1347837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23452
    ⟨1347837, by decide⟩ (by decide) (![⟨1347742, by decide⟩,⟨1347771, by decide⟩,⟨1347797, by decide⟩,⟨1347836, by decide⟩]) unmarked_context_10_23452_1347837 node_context_10_23452_1347837
  intro a
  fin_cases a
  · exact context_11_93808_1347742
  · exact context_11_93809_1347771
  · exact context_11_93810_1347797
  · exact context_11_93811_1347836

theorem selected_cut_48098 : selected 11 ⟨1347899, by decide⟩
    (prefixPartial 10 23453) = some ⟨10, 2, 0, 1347899, 23453, 2489, 1048576⟩ := by
  decide +kernel

theorem context_10_23453_1347899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23453 ⟨1347899, by decide⟩ :=
  accepted_of_selected 10 23453 ⟨1347899, by decide⟩ ⟨10, 2, 0, 1347899, 23453, 2489, 1048576⟩
    (by decide) selected_cut_48098

theorem selected_cut_48099 : selected 11 ⟨1347931, by decide⟩
    (prefixPartial 10 23454) = some ⟨10, 2, 0, 1347931, 23454, 1069, 1048576⟩ := by
  decide +kernel

theorem context_10_23454_1347931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23454 ⟨1347931, by decide⟩ :=
  accepted_of_selected 10 23454 ⟨1347931, by decide⟩ ⟨10, 2, 0, 1347931, 23454, 1069, 1048576⟩
    (by decide) selected_cut_48099

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
