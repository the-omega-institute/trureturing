/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover305
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_93489_741745 : frontier 9 ⟨741745, by decide⟩
    (prefixCache 12 93489) (prefixPartial 12 93489) = false := by
  decide +kernel

theorem node_context_12_93489_741745 : EJMOriginalGlobalDAGData.nodes 9 ⟨741745, by decide⟩ =
    .split (coordinate 12) (![⟨741696, by decide⟩,⟨741718, by decide⟩,⟨741736, by decide⟩,⟨741744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93489_741745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93489 ⟨741745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93489
    ⟨741745, by decide⟩ (by decide) (![⟨741696, by decide⟩,⟨741718, by decide⟩,⟨741736, by decide⟩,⟨741744, by decide⟩]) unmarked_context_12_93489_741745 node_context_12_93489_741745
  intro a
  fin_cases a
  · exact context_13_373956_741696
  · exact context_13_373957_741718
  · exact context_13_373958_741736
  · exact context_13_373959_741744

theorem selected_cut_29380 : selected 8 ⟨741755, by decide⟩
    (prefixPartial 13 373960) = some ⟨13, 2, 0, 741755, 373960, 605, 16384⟩ := by
  decide +kernel

theorem context_13_373960_741755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373960 ⟨741755, by decide⟩ :=
  accepted_of_selected 13 373960 ⟨741755, by decide⟩ ⟨13, 2, 0, 741755, 373960, 605, 16384⟩
    (by decide) selected_cut_29380

theorem selected_cut_29381 : selected 8 ⟨741790, by decide⟩
    (prefixPartial 13 373961) = some ⟨13, 2, 0, 741790, 373961, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_373961_741790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373961 ⟨741790, by decide⟩ :=
  accepted_of_selected 13 373961 ⟨741790, by decide⟩ ⟨13, 2, 0, 741790, 373961, 2105, 16384⟩
    (by decide) selected_cut_29381

theorem selected_cut_29382 : selected 8 ⟨741814, by decide⟩
    (prefixPartial 13 373962) = some ⟨13, 2, 0, 741814, 373962, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_373962_741814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373962 ⟨741814, by decide⟩ :=
  accepted_of_selected 13 373962 ⟨741814, by decide⟩ ⟨13, 2, 0, 741814, 373962, 1765, 16384⟩
    (by decide) selected_cut_29382

theorem selected_cut_29383 : selected 8 ⟨741822, by decide⟩
    (prefixPartial 13 373963) = some ⟨13, 2, 0, 741822, 373963, 905, 16384⟩ := by
  decide +kernel

theorem context_13_373963_741822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373963 ⟨741822, by decide⟩ :=
  accepted_of_selected 13 373963 ⟨741822, by decide⟩ ⟨13, 2, 0, 741822, 373963, 905, 16384⟩
    (by decide) selected_cut_29383

theorem unmarked_context_12_93490_741823 : frontier 9 ⟨741823, by decide⟩
    (prefixCache 12 93490) (prefixPartial 12 93490) = false := by
  decide +kernel

theorem node_context_12_93490_741823 : EJMOriginalGlobalDAGData.nodes 9 ⟨741823, by decide⟩ =
    .split (coordinate 12) (![⟨741755, by decide⟩,⟨741790, by decide⟩,⟨741814, by decide⟩,⟨741822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93490_741823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93490 ⟨741823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93490
    ⟨741823, by decide⟩ (by decide) (![⟨741755, by decide⟩,⟨741790, by decide⟩,⟨741814, by decide⟩,⟨741822, by decide⟩]) unmarked_context_12_93490_741823 node_context_12_93490_741823
  intro a
  fin_cases a
  · exact context_13_373960_741755
  · exact context_13_373961_741790
  · exact context_13_373962_741814
  · exact context_13_373963_741822

theorem selected_cut_29384 : selected 8 ⟨741839, by decide⟩
    (prefixPartial 13 373964) = some ⟨13, 2, 0, 741839, 373964, 709, 16384⟩ := by
  decide +kernel

theorem context_13_373964_741839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373964 ⟨741839, by decide⟩ :=
  accepted_of_selected 13 373964 ⟨741839, by decide⟩ ⟨13, 2, 0, 741839, 373964, 709, 16384⟩
    (by decide) selected_cut_29384

theorem selected_cut_29385 : selected 8 ⟨741878, by decide⟩
    (prefixPartial 13 373965) = some ⟨13, 2, 0, 741878, 373965, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_373965_741878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373965 ⟨741878, by decide⟩ :=
  accepted_of_selected 13 373965 ⟨741878, by decide⟩ ⟨13, 2, 0, 741878, 373965, 2453, 16384⟩
    (by decide) selected_cut_29385

theorem selected_cut_29386 : selected 8 ⟨741903, by decide⟩
    (prefixPartial 13 373966) = some ⟨13, 2, 0, 741903, 373966, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_373966_741903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373966 ⟨741903, by decide⟩ :=
  accepted_of_selected 13 373966 ⟨741903, by decide⟩ ⟨13, 2, 0, 741903, 373966, 2009, 16384⟩
    (by decide) selected_cut_29386

theorem selected_cut_29387 : selected 8 ⟨741910, by decide⟩
    (prefixPartial 13 373967) = some ⟨13, 2, 0, 741910, 373967, 897, 16384⟩ := by
  decide +kernel

theorem context_13_373967_741910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373967 ⟨741910, by decide⟩ :=
  accepted_of_selected 13 373967 ⟨741910, by decide⟩ ⟨13, 2, 0, 741910, 373967, 897, 16384⟩
    (by decide) selected_cut_29387

theorem unmarked_context_12_93491_741911 : frontier 9 ⟨741911, by decide⟩
    (prefixCache 12 93491) (prefixPartial 12 93491) = false := by
  decide +kernel

theorem node_context_12_93491_741911 : EJMOriginalGlobalDAGData.nodes 9 ⟨741911, by decide⟩ =
    .split (coordinate 12) (![⟨741839, by decide⟩,⟨741878, by decide⟩,⟨741903, by decide⟩,⟨741910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93491_741911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93491 ⟨741911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93491
    ⟨741911, by decide⟩ (by decide) (![⟨741839, by decide⟩,⟨741878, by decide⟩,⟨741903, by decide⟩,⟨741910, by decide⟩]) unmarked_context_12_93491_741911 node_context_12_93491_741911
  intro a
  fin_cases a
  · exact context_13_373964_741839
  · exact context_13_373965_741878
  · exact context_13_373966_741903
  · exact context_13_373967_741910

theorem unmarked_context_11_23372_741912 : frontier 10 ⟨741912, by decide⟩
    (prefixCache 11 23372) (prefixPartial 11 23372) = false := by
  decide +kernel

theorem node_context_11_23372_741912 : EJMOriginalGlobalDAGData.nodes 10 ⟨741912, by decide⟩ =
    .split (coordinate 11) (![⟨741685, by decide⟩,⟨741745, by decide⟩,⟨741823, by decide⟩,⟨741911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23372_741912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23372 ⟨741912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23372
    ⟨741912, by decide⟩ (by decide) (![⟨741685, by decide⟩,⟨741745, by decide⟩,⟨741823, by decide⟩,⟨741911, by decide⟩]) unmarked_context_11_23372_741912 node_context_11_23372_741912
  intro a
  fin_cases a
  · exact context_12_93488_741685
  · exact context_12_93489_741745
  · exact context_12_93490_741823
  · exact context_12_93491_741911

theorem selected_cut_29388 : selected 8 ⟨741921, by decide⟩
    (prefixPartial 13 373968) = some ⟨13, 2, 0, 741921, 373968, 449, 16384⟩ := by
  decide +kernel

theorem context_13_373968_741921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373968 ⟨741921, by decide⟩ :=
  accepted_of_selected 13 373968 ⟨741921, by decide⟩ ⟨13, 2, 0, 741921, 373968, 449, 16384⟩
    (by decide) selected_cut_29388

theorem selected_cut_29389 : selected 8 ⟨741942, by decide⟩
    (prefixPartial 13 373969) = some ⟨13, 2, 0, 741942, 373969, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_373969_741942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373969 ⟨741942, by decide⟩ :=
  accepted_of_selected 13 373969 ⟨741942, by decide⟩ ⟨13, 2, 0, 741942, 373969, 1637, 16384⟩
    (by decide) selected_cut_29389

theorem selected_cut_29390 : selected 8 ⟨741963, by decide⟩
    (prefixPartial 13 373970) = some ⟨13, 2, 0, 741963, 373970, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_373970_741963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373970 ⟨741963, by decide⟩ :=
  accepted_of_selected 13 373970 ⟨741963, by decide⟩ ⟨13, 2, 0, 741963, 373970, 1421, 16384⟩
    (by decide) selected_cut_29390

theorem selected_cut_29391 : selected 8 ⟨741972, by decide⟩
    (prefixPartial 13 373971) = some ⟨13, 2, 0, 741972, 373971, 729, 16384⟩ := by
  decide +kernel

theorem context_13_373971_741972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373971 ⟨741972, by decide⟩ :=
  accepted_of_selected 13 373971 ⟨741972, by decide⟩ ⟨13, 2, 0, 741972, 373971, 729, 16384⟩
    (by decide) selected_cut_29391

theorem unmarked_context_12_93492_741973 : frontier 9 ⟨741973, by decide⟩
    (prefixCache 12 93492) (prefixPartial 12 93492) = false := by
  decide +kernel

theorem node_context_12_93492_741973 : EJMOriginalGlobalDAGData.nodes 9 ⟨741973, by decide⟩ =
    .split (coordinate 12) (![⟨741921, by decide⟩,⟨741942, by decide⟩,⟨741963, by decide⟩,⟨741972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93492_741973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93492 ⟨741973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93492
    ⟨741973, by decide⟩ (by decide) (![⟨741921, by decide⟩,⟨741942, by decide⟩,⟨741963, by decide⟩,⟨741972, by decide⟩]) unmarked_context_12_93492_741973 node_context_12_93492_741973
  intro a
  fin_cases a
  · exact context_13_373968_741921
  · exact context_13_373969_741942
  · exact context_13_373970_741963
  · exact context_13_373971_741972

theorem selected_cut_29392 : selected 9 ⟨402280, by decide⟩
    (prefixPartial 12 93493) = some ⟨12, 1, 0, 402280, 93493, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93493_402280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93493 ⟨402280, by decide⟩ :=
  accepted_of_selected 12 93493 ⟨402280, by decide⟩ ⟨12, 1, 0, 402280, 93493, 1, 65536⟩
    (by decide) selected_cut_29392

theorem selected_cut_29393 : selected 8 ⟨741979, by decide⟩
    (prefixPartial 13 373976) = some ⟨13, 2, 0, 741979, 373976, 393, 16384⟩ := by
  decide +kernel

theorem context_13_373976_741979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373976 ⟨741979, by decide⟩ :=
  accepted_of_selected 13 373976 ⟨741979, by decide⟩ ⟨13, 2, 0, 741979, 373976, 393, 16384⟩
    (by decide) selected_cut_29393

theorem selected_cut_29394 : selected 8 ⟨742000, by decide⟩
    (prefixPartial 13 373977) = some ⟨13, 2, 0, 742000, 373977, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_373977_742000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373977 ⟨742000, by decide⟩ :=
  accepted_of_selected 13 373977 ⟨742000, by decide⟩ ⟨13, 2, 0, 742000, 373977, 1593, 16384⟩
    (by decide) selected_cut_29394

theorem selected_cut_29395 : selected 8 ⟨742022, by decide⟩
    (prefixPartial 13 373978) = some ⟨13, 2, 0, 742022, 373978, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_373978_742022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373978 ⟨742022, by decide⟩ :=
  accepted_of_selected 13 373978 ⟨742022, by decide⟩ ⟨13, 2, 0, 742022, 373978, 1377, 16384⟩
    (by decide) selected_cut_29395

theorem selected_cut_29396 : selected 8 ⟨742026, by decide⟩
    (prefixPartial 13 373979) = some ⟨13, 2, 0, 742026, 373979, 805, 16384⟩ := by
  decide +kernel

theorem context_13_373979_742026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373979 ⟨742026, by decide⟩ :=
  accepted_of_selected 13 373979 ⟨742026, by decide⟩ ⟨13, 2, 0, 742026, 373979, 805, 16384⟩
    (by decide) selected_cut_29396

theorem unmarked_context_12_93494_742027 : frontier 9 ⟨742027, by decide⟩
    (prefixCache 12 93494) (prefixPartial 12 93494) = false := by
  decide +kernel

theorem node_context_12_93494_742027 : EJMOriginalGlobalDAGData.nodes 9 ⟨742027, by decide⟩ =
    .split (coordinate 12) (![⟨741979, by decide⟩,⟨742000, by decide⟩,⟨742022, by decide⟩,⟨742026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93494_742027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93494 ⟨742027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93494
    ⟨742027, by decide⟩ (by decide) (![⟨741979, by decide⟩,⟨742000, by decide⟩,⟨742022, by decide⟩,⟨742026, by decide⟩]) unmarked_context_12_93494_742027 node_context_12_93494_742027
  intro a
  fin_cases a
  · exact context_13_373976_741979
  · exact context_13_373977_742000
  · exact context_13_373978_742022
  · exact context_13_373979_742026

theorem selected_cut_29397 : selected 8 ⟨742034, by decide⟩
    (prefixPartial 13 373980) = some ⟨13, 2, 0, 742034, 373980, 409, 16384⟩ := by
  decide +kernel

theorem context_13_373980_742034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373980 ⟨742034, by decide⟩ :=
  accepted_of_selected 13 373980 ⟨742034, by decide⟩ ⟨13, 2, 0, 742034, 373980, 409, 16384⟩
    (by decide) selected_cut_29397

theorem selected_cut_29398 : selected 8 ⟨742056, by decide⟩
    (prefixPartial 13 373981) = some ⟨13, 2, 0, 742056, 373981, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_373981_742056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373981 ⟨742056, by decide⟩ :=
  accepted_of_selected 13 373981 ⟨742056, by decide⟩ ⟨13, 2, 0, 742056, 373981, 1913, 16384⟩
    (by decide) selected_cut_29398

theorem selected_cut_29399 : selected 8 ⟨742076, by decide⟩
    (prefixPartial 13 373982) = some ⟨13, 2, 0, 742076, 373982, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_373982_742076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373982 ⟨742076, by decide⟩ :=
  accepted_of_selected 13 373982 ⟨742076, by decide⟩ ⟨13, 2, 0, 742076, 373982, 1785, 16384⟩
    (by decide) selected_cut_29399

theorem selected_cut_29400 : selected 8 ⟨742082, by decide⟩
    (prefixPartial 13 373983) = some ⟨13, 2, 0, 742082, 373983, 773, 16384⟩ := by
  decide +kernel

theorem context_13_373983_742082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373983 ⟨742082, by decide⟩ :=
  accepted_of_selected 13 373983 ⟨742082, by decide⟩ ⟨13, 2, 0, 742082, 373983, 773, 16384⟩
    (by decide) selected_cut_29400

theorem unmarked_context_12_93495_742083 : frontier 9 ⟨742083, by decide⟩
    (prefixCache 12 93495) (prefixPartial 12 93495) = false := by
  decide +kernel

theorem node_context_12_93495_742083 : EJMOriginalGlobalDAGData.nodes 9 ⟨742083, by decide⟩ =
    .split (coordinate 12) (![⟨742034, by decide⟩,⟨742056, by decide⟩,⟨742076, by decide⟩,⟨742082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93495_742083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93495 ⟨742083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93495
    ⟨742083, by decide⟩ (by decide) (![⟨742034, by decide⟩,⟨742056, by decide⟩,⟨742076, by decide⟩,⟨742082, by decide⟩]) unmarked_context_12_93495_742083 node_context_12_93495_742083
  intro a
  fin_cases a
  · exact context_13_373980_742034
  · exact context_13_373981_742056
  · exact context_13_373982_742076
  · exact context_13_373983_742082

theorem unmarked_context_11_23373_742084 : frontier 10 ⟨742084, by decide⟩
    (prefixCache 11 23373) (prefixPartial 11 23373) = false := by
  decide +kernel

theorem node_context_11_23373_742084 : EJMOriginalGlobalDAGData.nodes 10 ⟨742084, by decide⟩ =
    .split (coordinate 11) (![⟨741973, by decide⟩,⟨402280, by decide⟩,⟨742027, by decide⟩,⟨742083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23373_742084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23373 ⟨742084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23373
    ⟨742084, by decide⟩ (by decide) (![⟨741973, by decide⟩,⟨402280, by decide⟩,⟨742027, by decide⟩,⟨742083, by decide⟩]) unmarked_context_11_23373_742084 node_context_11_23373_742084
  intro a
  fin_cases a
  · exact context_12_93492_741973
  · exact context_12_93493_402280
  · exact context_12_93494_742027
  · exact context_12_93495_742083

theorem selected_cut_29401 : selected 8 ⟨742089, by decide⟩
    (prefixPartial 13 373984) = some ⟨13, 2, 0, 742089, 373984, 325, 16384⟩ := by
  decide +kernel

theorem context_13_373984_742089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373984 ⟨742089, by decide⟩ :=
  accepted_of_selected 13 373984 ⟨742089, by decide⟩ ⟨13, 2, 0, 742089, 373984, 325, 16384⟩
    (by decide) selected_cut_29401

theorem selected_cut_29402 : selected 8 ⟨742113, by decide⟩
    (prefixPartial 13 373985) = some ⟨13, 2, 0, 742113, 373985, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_373985_742113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373985 ⟨742113, by decide⟩ :=
  accepted_of_selected 13 373985 ⟨742113, by decide⟩ ⟨13, 2, 0, 742113, 373985, 1941, 16384⟩
    (by decide) selected_cut_29402

theorem selected_cut_29403 : selected 8 ⟨742133, by decide⟩
    (prefixPartial 13 373986) = some ⟨13, 2, 0, 742133, 373986, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_373986_742133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373986 ⟨742133, by decide⟩ :=
  accepted_of_selected 13 373986 ⟨742133, by decide⟩ ⟨13, 2, 0, 742133, 373986, 1809, 16384⟩
    (by decide) selected_cut_29403

theorem selected_cut_29404 : selected 8 ⟨742141, by decide⟩
    (prefixPartial 13 373987) = some ⟨13, 2, 0, 742141, 373987, 845, 16384⟩ := by
  decide +kernel

theorem context_13_373987_742141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373987 ⟨742141, by decide⟩ :=
  accepted_of_selected 13 373987 ⟨742141, by decide⟩ ⟨13, 2, 0, 742141, 373987, 845, 16384⟩
    (by decide) selected_cut_29404

theorem unmarked_context_12_93496_742142 : frontier 9 ⟨742142, by decide⟩
    (prefixCache 12 93496) (prefixPartial 12 93496) = false := by
  decide +kernel

theorem node_context_12_93496_742142 : EJMOriginalGlobalDAGData.nodes 9 ⟨742142, by decide⟩ =
    .split (coordinate 12) (![⟨742089, by decide⟩,⟨742113, by decide⟩,⟨742133, by decide⟩,⟨742141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93496_742142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93496 ⟨742142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93496
    ⟨742142, by decide⟩ (by decide) (![⟨742089, by decide⟩,⟨742113, by decide⟩,⟨742133, by decide⟩,⟨742141, by decide⟩]) unmarked_context_12_93496_742142 node_context_12_93496_742142
  intro a
  fin_cases a
  · exact context_13_373984_742089
  · exact context_13_373985_742113
  · exact context_13_373986_742133
  · exact context_13_373987_742141

theorem selected_cut_29405 : selected 8 ⟨742150, by decide⟩
    (prefixPartial 13 373988) = some ⟨13, 2, 0, 742150, 373988, 285, 16384⟩ := by
  decide +kernel

theorem context_13_373988_742150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373988 ⟨742150, by decide⟩ :=
  accepted_of_selected 13 373988 ⟨742150, by decide⟩ ⟨13, 2, 0, 742150, 373988, 285, 16384⟩
    (by decide) selected_cut_29405

theorem selected_cut_29406 : selected 8 ⟨742174, by decide⟩
    (prefixPartial 13 373989) = some ⟨13, 2, 0, 742174, 373989, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_373989_742174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373989 ⟨742174, by decide⟩ :=
  accepted_of_selected 13 373989 ⟨742174, by decide⟩ ⟨13, 2, 0, 742174, 373989, 1561, 16384⟩
    (by decide) selected_cut_29406

theorem selected_cut_29407 : selected 8 ⟨742195, by decide⟩
    (prefixPartial 13 373990) = some ⟨13, 2, 0, 742195, 373990, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_373990_742195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373990 ⟨742195, by decide⟩ :=
  accepted_of_selected 13 373990 ⟨742195, by decide⟩ ⟨13, 2, 0, 742195, 373990, 1877, 16384⟩
    (by decide) selected_cut_29407

theorem selected_cut_29408 : selected 8 ⟨742202, by decide⟩
    (prefixPartial 13 373991) = some ⟨13, 2, 0, 742202, 373991, 901, 16384⟩ := by
  decide +kernel

theorem context_13_373991_742202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373991 ⟨742202, by decide⟩ :=
  accepted_of_selected 13 373991 ⟨742202, by decide⟩ ⟨13, 2, 0, 742202, 373991, 901, 16384⟩
    (by decide) selected_cut_29408

theorem unmarked_context_12_93497_742203 : frontier 9 ⟨742203, by decide⟩
    (prefixCache 12 93497) (prefixPartial 12 93497) = false := by
  decide +kernel

theorem node_context_12_93497_742203 : EJMOriginalGlobalDAGData.nodes 9 ⟨742203, by decide⟩ =
    .split (coordinate 12) (![⟨742150, by decide⟩,⟨742174, by decide⟩,⟨742195, by decide⟩,⟨742202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93497_742203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93497 ⟨742203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93497
    ⟨742203, by decide⟩ (by decide) (![⟨742150, by decide⟩,⟨742174, by decide⟩,⟨742195, by decide⟩,⟨742202, by decide⟩]) unmarked_context_12_93497_742203 node_context_12_93497_742203
  intro a
  fin_cases a
  · exact context_13_373988_742150
  · exact context_13_373989_742174
  · exact context_13_373990_742195
  · exact context_13_373991_742202

theorem selected_cut_29409 : selected 8 ⟨742210, by decide⟩
    (prefixPartial 13 373992) = some ⟨13, 2, 0, 742210, 373992, 209, 16384⟩ := by
  decide +kernel

theorem context_13_373992_742210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373992 ⟨742210, by decide⟩ :=
  accepted_of_selected 13 373992 ⟨742210, by decide⟩ ⟨13, 2, 0, 742210, 373992, 209, 16384⟩
    (by decide) selected_cut_29409

theorem selected_cut_29410 : selected 8 ⟨742233, by decide⟩
    (prefixPartial 13 373993) = some ⟨13, 2, 0, 742233, 373993, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_373993_742233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373993 ⟨742233, by decide⟩ :=
  accepted_of_selected 13 373993 ⟨742233, by decide⟩ ⟨13, 2, 0, 742233, 373993, 1897, 16384⟩
    (by decide) selected_cut_29410

theorem selected_cut_29411 : selected 8 ⟨742256, by decide⟩
    (prefixPartial 13 373994) = some ⟨13, 2, 0, 742256, 373994, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_373994_742256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373994 ⟨742256, by decide⟩ :=
  accepted_of_selected 13 373994 ⟨742256, by decide⟩ ⟨13, 2, 0, 742256, 373994, 1781, 16384⟩
    (by decide) selected_cut_29411

theorem selected_cut_29412 : selected 8 ⟨742265, by decide⟩
    (prefixPartial 13 373995) = some ⟨13, 2, 0, 742265, 373995, 889, 16384⟩ := by
  decide +kernel

theorem context_13_373995_742265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373995 ⟨742265, by decide⟩ :=
  accepted_of_selected 13 373995 ⟨742265, by decide⟩ ⟨13, 2, 0, 742265, 373995, 889, 16384⟩
    (by decide) selected_cut_29412

theorem unmarked_context_12_93498_742266 : frontier 9 ⟨742266, by decide⟩
    (prefixCache 12 93498) (prefixPartial 12 93498) = false := by
  decide +kernel

theorem node_context_12_93498_742266 : EJMOriginalGlobalDAGData.nodes 9 ⟨742266, by decide⟩ =
    .split (coordinate 12) (![⟨742210, by decide⟩,⟨742233, by decide⟩,⟨742256, by decide⟩,⟨742265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93498_742266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93498 ⟨742266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93498
    ⟨742266, by decide⟩ (by decide) (![⟨742210, by decide⟩,⟨742233, by decide⟩,⟨742256, by decide⟩,⟨742265, by decide⟩]) unmarked_context_12_93498_742266 node_context_12_93498_742266
  intro a
  fin_cases a
  · exact context_13_373992_742210
  · exact context_13_373993_742233
  · exact context_13_373994_742256
  · exact context_13_373995_742265

theorem selected_cut_29413 : selected 8 ⟨742272, by decide⟩
    (prefixPartial 13 373996) = some ⟨13, 2, 0, 742272, 373996, 193, 16384⟩ := by
  decide +kernel

theorem context_13_373996_742272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373996 ⟨742272, by decide⟩ :=
  accepted_of_selected 13 373996 ⟨742272, by decide⟩ ⟨13, 2, 0, 742272, 373996, 193, 16384⟩
    (by decide) selected_cut_29413

theorem selected_cut_29414 : selected 8 ⟨742305, by decide⟩
    (prefixPartial 13 373997) = some ⟨13, 2, 0, 742305, 373997, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_373997_742305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373997 ⟨742305, by decide⟩ :=
  accepted_of_selected 13 373997 ⟨742305, by decide⟩ ⟨13, 2, 0, 742305, 373997, 2313, 16384⟩
    (by decide) selected_cut_29414

theorem selected_cut_29415 : selected 8 ⟨742335, by decide⟩
    (prefixPartial 13 373998) = some ⟨13, 2, 0, 742335, 373998, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_373998_742335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373998 ⟨742335, by decide⟩ :=
  accepted_of_selected 13 373998 ⟨742335, by decide⟩ ⟨13, 2, 0, 742335, 373998, 2121, 16384⟩
    (by decide) selected_cut_29415

theorem selected_cut_29416 : selected 8 ⟨742340, by decide⟩
    (prefixPartial 13 373999) = some ⟨13, 2, 0, 742340, 373999, 865, 16384⟩ := by
  decide +kernel

theorem context_13_373999_742340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 373999 ⟨742340, by decide⟩ :=
  accepted_of_selected 13 373999 ⟨742340, by decide⟩ ⟨13, 2, 0, 742340, 373999, 865, 16384⟩
    (by decide) selected_cut_29416

theorem unmarked_context_12_93499_742341 : frontier 9 ⟨742341, by decide⟩
    (prefixCache 12 93499) (prefixPartial 12 93499) = false := by
  decide +kernel

theorem node_context_12_93499_742341 : EJMOriginalGlobalDAGData.nodes 9 ⟨742341, by decide⟩ =
    .split (coordinate 12) (![⟨742272, by decide⟩,⟨742305, by decide⟩,⟨742335, by decide⟩,⟨742340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93499_742341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93499 ⟨742341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93499
    ⟨742341, by decide⟩ (by decide) (![⟨742272, by decide⟩,⟨742305, by decide⟩,⟨742335, by decide⟩,⟨742340, by decide⟩]) unmarked_context_12_93499_742341 node_context_12_93499_742341
  intro a
  fin_cases a
  · exact context_13_373996_742272
  · exact context_13_373997_742305
  · exact context_13_373998_742335
  · exact context_13_373999_742340

theorem unmarked_context_11_23374_742342 : frontier 10 ⟨742342, by decide⟩
    (prefixCache 11 23374) (prefixPartial 11 23374) = false := by
  decide +kernel

theorem node_context_11_23374_742342 : EJMOriginalGlobalDAGData.nodes 10 ⟨742342, by decide⟩ =
    .split (coordinate 11) (![⟨742142, by decide⟩,⟨742203, by decide⟩,⟨742266, by decide⟩,⟨742341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23374_742342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23374 ⟨742342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23374
    ⟨742342, by decide⟩ (by decide) (![⟨742142, by decide⟩,⟨742203, by decide⟩,⟨742266, by decide⟩,⟨742341, by decide⟩]) unmarked_context_11_23374_742342 node_context_11_23374_742342
  intro a
  fin_cases a
  · exact context_12_93496_742142
  · exact context_12_93497_742203
  · exact context_12_93498_742266
  · exact context_12_93499_742341

theorem selected_cut_29417 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 93500) = some ⟨12, 1, 0, 399383, 93500, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93500_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93500 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 93500 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 93500, 1, 65536⟩
    (by decide) selected_cut_29417

theorem selected_cut_29418 : selected 9 ⟨399384, by decide⟩
    (prefixPartial 12 93501) = some ⟨12, 1, 0, 399384, 93501, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93501_399384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93501 ⟨399384, by decide⟩ :=
  accepted_of_selected 12 93501 ⟨399384, by decide⟩ ⟨12, 1, 0, 399384, 93501, 1, 65536⟩
    (by decide) selected_cut_29418

theorem selected_cut_29419 : selected 8 ⟨742347, by decide⟩
    (prefixPartial 13 374008) = some ⟨13, 2, 0, 742347, 374008, 105, 16384⟩ := by
  decide +kernel

theorem context_13_374008_742347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374008 ⟨742347, by decide⟩ :=
  accepted_of_selected 13 374008 ⟨742347, by decide⟩ ⟨13, 2, 0, 742347, 374008, 105, 16384⟩
    (by decide) selected_cut_29419

theorem selected_cut_29420 : selected 8 ⟨742382, by decide⟩
    (prefixPartial 13 374009) = some ⟨13, 2, 0, 742382, 374009, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_374009_742382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374009 ⟨742382, by decide⟩ :=
  accepted_of_selected 13 374009 ⟨742382, by decide⟩ ⟨13, 2, 0, 742382, 374009, 2361, 16384⟩
    (by decide) selected_cut_29420

theorem selected_cut_29421 : selected 8 ⟨742407, by decide⟩
    (prefixPartial 13 374010) = some ⟨13, 2, 0, 742407, 374010, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_374010_742407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374010 ⟨742407, by decide⟩ :=
  accepted_of_selected 13 374010 ⟨742407, by decide⟩ ⟨13, 2, 0, 742407, 374010, 1793, 16384⟩
    (by decide) selected_cut_29421

theorem selected_cut_29422 : selected 8 ⟨742413, by decide⟩
    (prefixPartial 13 374011) = some ⟨13, 2, 0, 742413, 374011, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_374011_742413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374011 ⟨742413, by decide⟩ :=
  accepted_of_selected 13 374011 ⟨742413, by decide⟩ ⟨13, 2, 0, 742413, 374011, 1121, 16384⟩
    (by decide) selected_cut_29422

theorem unmarked_context_12_93502_742414 : frontier 9 ⟨742414, by decide⟩
    (prefixCache 12 93502) (prefixPartial 12 93502) = false := by
  decide +kernel

theorem node_context_12_93502_742414 : EJMOriginalGlobalDAGData.nodes 9 ⟨742414, by decide⟩ =
    .split (coordinate 12) (![⟨742347, by decide⟩,⟨742382, by decide⟩,⟨742407, by decide⟩,⟨742413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93502_742414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93502 ⟨742414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93502
    ⟨742414, by decide⟩ (by decide) (![⟨742347, by decide⟩,⟨742382, by decide⟩,⟨742407, by decide⟩,⟨742413, by decide⟩]) unmarked_context_12_93502_742414 node_context_12_93502_742414
  intro a
  fin_cases a
  · exact context_13_374008_742347
  · exact context_13_374009_742382
  · exact context_13_374010_742407
  · exact context_13_374011_742413

theorem selected_cut_29423 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 93503) = some ⟨12, 1, 0, 399383, 93503, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93503_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93503 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 93503 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 93503, 1, 65536⟩
    (by decide) selected_cut_29423

theorem unmarked_context_11_23375_742415 : frontier 10 ⟨742415, by decide⟩
    (prefixCache 11 23375) (prefixPartial 11 23375) = false := by
  decide +kernel

theorem node_context_11_23375_742415 : EJMOriginalGlobalDAGData.nodes 10 ⟨742415, by decide⟩ =
    .split (coordinate 11) (![⟨399383, by decide⟩,⟨399384, by decide⟩,⟨742414, by decide⟩,⟨399383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23375_742415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23375 ⟨742415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23375
    ⟨742415, by decide⟩ (by decide) (![⟨399383, by decide⟩,⟨399384, by decide⟩,⟨742414, by decide⟩,⟨399383, by decide⟩]) unmarked_context_11_23375_742415 node_context_11_23375_742415
  intro a
  fin_cases a
  · exact context_12_93500_399383
  · exact context_12_93501_399384
  · exact context_12_93502_742414
  · exact context_12_93503_399383

theorem unmarked_context_10_5843_742416 : frontier 11 ⟨742416, by decide⟩
    (prefixCache 10 5843) (prefixPartial 10 5843) = false := by
  decide +kernel

theorem node_context_10_5843_742416 : EJMOriginalGlobalDAGData.nodes 11 ⟨742416, by decide⟩ =
    .split (coordinate 10) (![⟨741912, by decide⟩,⟨742084, by decide⟩,⟨742342, by decide⟩,⟨742415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5843_742416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5843 ⟨742416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5843
    ⟨742416, by decide⟩ (by decide) (![⟨741912, by decide⟩,⟨742084, by decide⟩,⟨742342, by decide⟩,⟨742415, by decide⟩]) unmarked_context_10_5843_742416 node_context_10_5843_742416
  intro a
  fin_cases a
  · exact context_11_23372_741912
  · exact context_11_23373_742084
  · exact context_11_23374_742342
  · exact context_11_23375_742415

theorem unmarked_context_9_1460_742417 : frontier 12 ⟨742417, by decide⟩
    (prefixCache 9 1460) (prefixPartial 9 1460) = false := by
  decide +kernel

theorem node_context_9_1460_742417 : EJMOriginalGlobalDAGData.nodes 12 ⟨742417, by decide⟩ =
    .split (coordinate 9) (![⟨739276, by decide⟩,⟨740469, by decide⟩,⟨741617, by decide⟩,⟨742416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1460_742417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1460 ⟨742417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1460
    ⟨742417, by decide⟩ (by decide) (![⟨739276, by decide⟩,⟨740469, by decide⟩,⟨741617, by decide⟩,⟨742416, by decide⟩]) unmarked_context_9_1460_742417 node_context_9_1460_742417
  intro a
  fin_cases a
  · exact context_10_5840_739276
  · exact context_10_5841_740469
  · exact context_10_5842_741617
  · exact context_10_5843_742416

theorem selected_cut_29424 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 374016) = some ⟨13, 1, 0, 3444, 374016, 1, 16384⟩ := by
  decide +kernel

theorem context_13_374016_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374016 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 374016 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 374016, 1, 16384⟩
    (by decide) selected_cut_29424

theorem selected_cut_29425 : selected 8 ⟨742441, by decide⟩
    (prefixPartial 13 374017) = some ⟨13, 2, 0, 742441, 374017, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_374017_742441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374017 ⟨742441, by decide⟩ :=
  accepted_of_selected 13 374017 ⟨742441, by decide⟩ ⟨13, 2, 0, 742441, 374017, 1837, 16384⟩
    (by decide) selected_cut_29425

theorem selected_cut_29426 : selected 8 ⟨742464, by decide⟩
    (prefixPartial 13 374018) = some ⟨13, 2, 0, 742464, 374018, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_374018_742464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374018 ⟨742464, by decide⟩ :=
  accepted_of_selected 13 374018 ⟨742464, by decide⟩ ⟨13, 2, 0, 742464, 374018, 1621, 16384⟩
    (by decide) selected_cut_29426

theorem selected_cut_29427 : selected 8 ⟨742473, by decide⟩
    (prefixPartial 13 374019) = some ⟨13, 2, 0, 742473, 374019, 777, 16384⟩ := by
  decide +kernel

theorem context_13_374019_742473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374019 ⟨742473, by decide⟩ :=
  accepted_of_selected 13 374019 ⟨742473, by decide⟩ ⟨13, 2, 0, 742473, 374019, 777, 16384⟩
    (by decide) selected_cut_29427

theorem unmarked_context_12_93504_742474 : frontier 9 ⟨742474, by decide⟩
    (prefixCache 12 93504) (prefixPartial 12 93504) = false := by
  decide +kernel

theorem node_context_12_93504_742474 : EJMOriginalGlobalDAGData.nodes 9 ⟨742474, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨742441, by decide⟩,⟨742464, by decide⟩,⟨742473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93504_742474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93504 ⟨742474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93504
    ⟨742474, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨742441, by decide⟩,⟨742464, by decide⟩,⟨742473, by decide⟩]) unmarked_context_12_93504_742474 node_context_12_93504_742474
  intro a
  fin_cases a
  · exact context_13_374016_3444
  · exact context_13_374017_742441
  · exact context_13_374018_742464
  · exact context_13_374019_742473

theorem selected_cut_29428 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 93505) = some ⟨12, 1, 0, 170504, 93505, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93505_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93505 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 93505 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 93505, 1, 65536⟩
    (by decide) selected_cut_29428

theorem selected_cut_29429 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 374024) = some ⟨13, 1, 0, 3444, 374024, 1, 16384⟩ := by
  decide +kernel

theorem context_13_374024_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374024 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 374024 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 374024, 1, 16384⟩
    (by decide) selected_cut_29429

theorem selected_cut_29430 : selected 8 ⟨742493, by decide⟩
    (prefixPartial 13 374025) = some ⟨13, 2, 0, 742493, 374025, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_374025_742493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374025 ⟨742493, by decide⟩ :=
  accepted_of_selected 13 374025 ⟨742493, by decide⟩ ⟨13, 2, 0, 742493, 374025, 1885, 16384⟩
    (by decide) selected_cut_29430

theorem selected_cut_29431 : selected 8 ⟨742514, by decide⟩
    (prefixPartial 13 374026) = some ⟨13, 2, 0, 742514, 374026, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_374026_742514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374026 ⟨742514, by decide⟩ :=
  accepted_of_selected 13 374026 ⟨742514, by decide⟩ ⟨13, 2, 0, 742514, 374026, 1793, 16384⟩
    (by decide) selected_cut_29431

theorem selected_cut_29432 : selected 8 ⟨742520, by decide⟩
    (prefixPartial 13 374027) = some ⟨13, 2, 0, 742520, 374027, 873, 16384⟩ := by
  decide +kernel

theorem context_13_374027_742520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374027 ⟨742520, by decide⟩ :=
  accepted_of_selected 13 374027 ⟨742520, by decide⟩ ⟨13, 2, 0, 742520, 374027, 873, 16384⟩
    (by decide) selected_cut_29432

theorem unmarked_context_12_93506_742521 : frontier 9 ⟨742521, by decide⟩
    (prefixCache 12 93506) (prefixPartial 12 93506) = false := by
  decide +kernel

theorem node_context_12_93506_742521 : EJMOriginalGlobalDAGData.nodes 9 ⟨742521, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨742493, by decide⟩,⟨742514, by decide⟩,⟨742520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93506_742521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93506 ⟨742521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93506
    ⟨742521, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨742493, by decide⟩,⟨742514, by decide⟩,⟨742520, by decide⟩]) unmarked_context_12_93506_742521 node_context_12_93506_742521
  intro a
  fin_cases a
  · exact context_13_374024_3444
  · exact context_13_374025_742493
  · exact context_13_374026_742514
  · exact context_13_374027_742520

theorem selected_cut_29433 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 374028) = some ⟨13, 1, 0, 3444, 374028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_374028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 374028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 374028, 1, 16384⟩
    (by decide) selected_cut_29433

theorem selected_cut_29434 : selected 8 ⟨742542, by decide⟩
    (prefixPartial 13 374029) = some ⟨13, 2, 0, 742542, 374029, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_374029_742542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374029 ⟨742542, by decide⟩ :=
  accepted_of_selected 13 374029 ⟨742542, by decide⟩ ⟨13, 2, 0, 742542, 374029, 1801, 16384⟩
    (by decide) selected_cut_29434

theorem selected_cut_29435 : selected 8 ⟨742564, by decide⟩
    (prefixPartial 13 374030) = some ⟨13, 2, 0, 742564, 374030, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_374030_742564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374030 ⟨742564, by decide⟩ :=
  accepted_of_selected 13 374030 ⟨742564, by decide⟩ ⟨13, 2, 0, 742564, 374030, 1885, 16384⟩
    (by decide) selected_cut_29435

theorem selected_cut_29436 : selected 8 ⟨742572, by decide⟩
    (prefixPartial 13 374031) = some ⟨13, 2, 0, 742572, 374031, 957, 16384⟩ := by
  decide +kernel

theorem context_13_374031_742572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374031 ⟨742572, by decide⟩ :=
  accepted_of_selected 13 374031 ⟨742572, by decide⟩ ⟨13, 2, 0, 742572, 374031, 957, 16384⟩
    (by decide) selected_cut_29436

theorem unmarked_context_12_93507_742573 : frontier 9 ⟨742573, by decide⟩
    (prefixCache 12 93507) (prefixPartial 12 93507) = false := by
  decide +kernel

theorem node_context_12_93507_742573 : EJMOriginalGlobalDAGData.nodes 9 ⟨742573, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨742542, by decide⟩,⟨742564, by decide⟩,⟨742572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93507_742573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93507 ⟨742573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93507
    ⟨742573, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨742542, by decide⟩,⟨742564, by decide⟩,⟨742572, by decide⟩]) unmarked_context_12_93507_742573 node_context_12_93507_742573
  intro a
  fin_cases a
  · exact context_13_374028_3444
  · exact context_13_374029_742542
  · exact context_13_374030_742564
  · exact context_13_374031_742572

theorem unmarked_context_11_23376_742574 : frontier 10 ⟨742574, by decide⟩
    (prefixCache 11 23376) (prefixPartial 11 23376) = false := by
  decide +kernel

theorem node_context_11_23376_742574 : EJMOriginalGlobalDAGData.nodes 10 ⟨742574, by decide⟩ =
    .split (coordinate 11) (![⟨742474, by decide⟩,⟨170504, by decide⟩,⟨742521, by decide⟩,⟨742573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23376_742574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23376 ⟨742574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23376
    ⟨742574, by decide⟩ (by decide) (![⟨742474, by decide⟩,⟨170504, by decide⟩,⟨742521, by decide⟩,⟨742573, by decide⟩]) unmarked_context_11_23376_742574 node_context_11_23376_742574
  intro a
  fin_cases a
  · exact context_12_93504_742474
  · exact context_12_93505_170504
  · exact context_12_93506_742521
  · exact context_12_93507_742573

theorem selected_cut_29437 : selected 9 ⟨742620, by decide⟩
    (prefixPartial 12 93508) = some ⟨12, 2, 0, 742620, 93508, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_93508_742620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93508 ⟨742620, by decide⟩ :=
  accepted_of_selected 12 93508 ⟨742620, by decide⟩ ⟨12, 2, 0, 742620, 93508, 3193, 65536⟩
    (by decide) selected_cut_29437

theorem selected_cut_29438 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 93509) = some ⟨12, 1, 0, 170504, 93509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93509_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93509 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 93509 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 93509, 1, 65536⟩
    (by decide) selected_cut_29438

theorem selected_cut_29439 : selected 9 ⟨742664, by decide⟩
    (prefixPartial 12 93510) = some ⟨12, 2, 0, 742664, 93510, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_93510_742664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93510 ⟨742664, by decide⟩ :=
  accepted_of_selected 12 93510 ⟨742664, by decide⟩ ⟨12, 2, 0, 742664, 93510, 3329, 65536⟩
    (by decide) selected_cut_29439

theorem selected_cut_29440 : selected 9 ⟨742715, by decide⟩
    (prefixPartial 12 93511) = some ⟨12, 2, 0, 742715, 93511, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_93511_742715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93511 ⟨742715, by decide⟩ :=
  accepted_of_selected 12 93511 ⟨742715, by decide⟩ ⟨12, 2, 0, 742715, 93511, 3521, 65536⟩
    (by decide) selected_cut_29440

theorem unmarked_context_11_23377_742716 : frontier 10 ⟨742716, by decide⟩
    (prefixCache 11 23377) (prefixPartial 11 23377) = false := by
  decide +kernel

theorem node_context_11_23377_742716 : EJMOriginalGlobalDAGData.nodes 10 ⟨742716, by decide⟩ =
    .split (coordinate 11) (![⟨742620, by decide⟩,⟨170504, by decide⟩,⟨742664, by decide⟩,⟨742715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23377_742716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23377 ⟨742716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23377
    ⟨742716, by decide⟩ (by decide) (![⟨742620, by decide⟩,⟨170504, by decide⟩,⟨742664, by decide⟩,⟨742715, by decide⟩]) unmarked_context_11_23377_742716 node_context_11_23377_742716
  intro a
  fin_cases a
  · exact context_12_93508_742620
  · exact context_12_93509_170504
  · exact context_12_93510_742664
  · exact context_12_93511_742715

theorem selected_cut_29441 : selected 9 ⟨742771, by decide⟩
    (prefixPartial 12 93512) = some ⟨12, 2, 0, 742771, 93512, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_93512_742771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93512 ⟨742771, by decide⟩ :=
  accepted_of_selected 12 93512 ⟨742771, by decide⟩ ⟨12, 2, 0, 742771, 93512, 3757, 65536⟩
    (by decide) selected_cut_29441

theorem selected_cut_29442 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 93513) = some ⟨12, 1, 0, 126371, 93513, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93513_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93513 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 93513 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 93513, 1, 65536⟩
    (by decide) selected_cut_29442

theorem selected_cut_29443 : selected 9 ⟨742817, by decide⟩
    (prefixPartial 12 93514) = some ⟨12, 2, 0, 742817, 93514, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_93514_742817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93514 ⟨742817, by decide⟩ :=
  accepted_of_selected 12 93514 ⟨742817, by decide⟩ ⟨12, 2, 0, 742817, 93514, 3801, 65536⟩
    (by decide) selected_cut_29443

theorem selected_cut_29444 : selected 9 ⟨742874, by decide⟩
    (prefixPartial 12 93515) = some ⟨12, 2, 0, 742874, 93515, 4069, 65536⟩ := by
  decide +kernel

theorem context_12_93515_742874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93515 ⟨742874, by decide⟩ :=
  accepted_of_selected 12 93515 ⟨742874, by decide⟩ ⟨12, 2, 0, 742874, 93515, 4069, 65536⟩
    (by decide) selected_cut_29444

theorem unmarked_context_11_23378_742875 : frontier 10 ⟨742875, by decide⟩
    (prefixCache 11 23378) (prefixPartial 11 23378) = false := by
  decide +kernel

theorem node_context_11_23378_742875 : EJMOriginalGlobalDAGData.nodes 10 ⟨742875, by decide⟩ =
    .split (coordinate 11) (![⟨742771, by decide⟩,⟨126371, by decide⟩,⟨742817, by decide⟩,⟨742874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23378_742875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23378 ⟨742875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23378
    ⟨742875, by decide⟩ (by decide) (![⟨742771, by decide⟩,⟨126371, by decide⟩,⟨742817, by decide⟩,⟨742874, by decide⟩]) unmarked_context_11_23378_742875 node_context_11_23378_742875
  intro a
  fin_cases a
  · exact context_12_93512_742771
  · exact context_12_93513_126371
  · exact context_12_93514_742817
  · exact context_12_93515_742874

theorem selected_cut_29445 : selected 9 ⟨742924, by decide⟩
    (prefixPartial 12 93516) = some ⟨12, 2, 0, 742924, 93516, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_93516_742924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93516 ⟨742924, by decide⟩ :=
  accepted_of_selected 12 93516 ⟨742924, by decide⟩ ⟨12, 2, 0, 742924, 93516, 3549, 65536⟩
    (by decide) selected_cut_29445

theorem selected_cut_29446 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 93517) = some ⟨12, 1, 0, 320864, 93517, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93517_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93517 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 93517 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 93517, 1, 65536⟩
    (by decide) selected_cut_29446

theorem selected_cut_29447 : selected 9 ⟨742965, by decide⟩
    (prefixPartial 12 93518) = some ⟨12, 2, 0, 742965, 93518, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_93518_742965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93518 ⟨742965, by decide⟩ :=
  accepted_of_selected 12 93518 ⟨742965, by decide⟩ ⟨12, 2, 0, 742965, 93518, 3481, 65536⟩
    (by decide) selected_cut_29447

theorem selected_cut_29448 : selected 9 ⟨743014, by decide⟩
    (prefixPartial 12 93519) = some ⟨12, 2, 0, 743014, 93519, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_93519_743014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93519 ⟨743014, by decide⟩ :=
  accepted_of_selected 12 93519 ⟨743014, by decide⟩ ⟨12, 2, 0, 743014, 93519, 3757, 65536⟩
    (by decide) selected_cut_29448

theorem unmarked_context_11_23379_743015 : frontier 10 ⟨743015, by decide⟩
    (prefixCache 11 23379) (prefixPartial 11 23379) = false := by
  decide +kernel

theorem node_context_11_23379_743015 : EJMOriginalGlobalDAGData.nodes 10 ⟨743015, by decide⟩ =
    .split (coordinate 11) (![⟨742924, by decide⟩,⟨320864, by decide⟩,⟨742965, by decide⟩,⟨743014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23379_743015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23379 ⟨743015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23379
    ⟨743015, by decide⟩ (by decide) (![⟨742924, by decide⟩,⟨320864, by decide⟩,⟨742965, by decide⟩,⟨743014, by decide⟩]) unmarked_context_11_23379_743015 node_context_11_23379_743015
  intro a
  fin_cases a
  · exact context_12_93516_742924
  · exact context_12_93517_320864
  · exact context_12_93518_742965
  · exact context_12_93519_743014

theorem unmarked_context_10_5844_743016 : frontier 11 ⟨743016, by decide⟩
    (prefixCache 10 5844) (prefixPartial 10 5844) = false := by
  decide +kernel

theorem node_context_10_5844_743016 : EJMOriginalGlobalDAGData.nodes 11 ⟨743016, by decide⟩ =
    .split (coordinate 10) (![⟨742574, by decide⟩,⟨742716, by decide⟩,⟨742875, by decide⟩,⟨743015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5844_743016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5844 ⟨743016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5844
    ⟨743016, by decide⟩ (by decide) (![⟨742574, by decide⟩,⟨742716, by decide⟩,⟨742875, by decide⟩,⟨743015, by decide⟩]) unmarked_context_10_5844_743016 node_context_10_5844_743016
  intro a
  fin_cases a
  · exact context_11_23376_742574
  · exact context_11_23377_742716
  · exact context_11_23378_742875
  · exact context_11_23379_743015

theorem selected_cut_29449 : selected 9 ⟨743063, by decide⟩
    (prefixPartial 12 93520) = some ⟨12, 2, 0, 743063, 93520, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_93520_743063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93520 ⟨743063, by decide⟩ :=
  accepted_of_selected 12 93520 ⟨743063, by decide⟩ ⟨12, 2, 0, 743063, 93520, 3493, 65536⟩
    (by decide) selected_cut_29449

theorem selected_cut_29450 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93521) = some ⟨12, 1, 0, 642341, 93521, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93521_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93521 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93521 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93521, 1, 65536⟩
    (by decide) selected_cut_29450

theorem selected_cut_29451 : selected 9 ⟨743117, by decide⟩
    (prefixPartial 12 93522) = some ⟨12, 2, 0, 743117, 93522, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_93522_743117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93522 ⟨743117, by decide⟩ :=
  accepted_of_selected 12 93522 ⟨743117, by decide⟩ ⟨12, 2, 0, 743117, 93522, 3905, 65536⟩
    (by decide) selected_cut_29451

theorem selected_cut_29452 : selected 9 ⟨743169, by decide⟩
    (prefixPartial 12 93523) = some ⟨12, 2, 0, 743169, 93523, 4013, 65536⟩ := by
  decide +kernel

theorem context_12_93523_743169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93523 ⟨743169, by decide⟩ :=
  accepted_of_selected 12 93523 ⟨743169, by decide⟩ ⟨12, 2, 0, 743169, 93523, 4013, 65536⟩
    (by decide) selected_cut_29452

theorem unmarked_context_11_23380_743170 : frontier 10 ⟨743170, by decide⟩
    (prefixCache 11 23380) (prefixPartial 11 23380) = false := by
  decide +kernel

theorem node_context_11_23380_743170 : EJMOriginalGlobalDAGData.nodes 10 ⟨743170, by decide⟩ =
    .split (coordinate 11) (![⟨743063, by decide⟩,⟨642341, by decide⟩,⟨743117, by decide⟩,⟨743169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23380_743170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23380 ⟨743170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23380
    ⟨743170, by decide⟩ (by decide) (![⟨743063, by decide⟩,⟨642341, by decide⟩,⟨743117, by decide⟩,⟨743169, by decide⟩]) unmarked_context_11_23380_743170 node_context_11_23380_743170
  intro a
  fin_cases a
  · exact context_12_93520_743063
  · exact context_12_93521_642341
  · exact context_12_93522_743117
  · exact context_12_93523_743169

theorem selected_cut_29453 : selected 9 ⟨743207, by decide⟩
    (prefixPartial 12 93524) = some ⟨12, 2, 0, 743207, 93524, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_93524_743207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93524 ⟨743207, by decide⟩ :=
  accepted_of_selected 12 93524 ⟨743207, by decide⟩ ⟨12, 2, 0, 743207, 93524, 2745, 65536⟩
    (by decide) selected_cut_29453

theorem selected_cut_29454 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93525) = some ⟨12, 1, 0, 642341, 93525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93525_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93525 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93525 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93525, 1, 65536⟩
    (by decide) selected_cut_29454

theorem selected_cut_29455 : selected 9 ⟨743247, by decide⟩
    (prefixPartial 12 93526) = some ⟨12, 2, 0, 743247, 93526, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_93526_743247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93526 ⟨743247, by decide⟩ :=
  accepted_of_selected 12 93526 ⟨743247, by decide⟩ ⟨12, 2, 0, 743247, 93526, 2985, 65536⟩
    (by decide) selected_cut_29455

theorem selected_cut_29456 : selected 9 ⟨743285, by decide⟩
    (prefixPartial 12 93527) = some ⟨12, 2, 0, 743285, 93527, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_93527_743285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93527 ⟨743285, by decide⟩ :=
  accepted_of_selected 12 93527 ⟨743285, by decide⟩ ⟨12, 2, 0, 743285, 93527, 3129, 65536⟩
    (by decide) selected_cut_29456

theorem unmarked_context_11_23381_743286 : frontier 10 ⟨743286, by decide⟩
    (prefixCache 11 23381) (prefixPartial 11 23381) = false := by
  decide +kernel

theorem node_context_11_23381_743286 : EJMOriginalGlobalDAGData.nodes 10 ⟨743286, by decide⟩ =
    .split (coordinate 11) (![⟨743207, by decide⟩,⟨642341, by decide⟩,⟨743247, by decide⟩,⟨743285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23381_743286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23381 ⟨743286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23381
    ⟨743286, by decide⟩ (by decide) (![⟨743207, by decide⟩,⟨642341, by decide⟩,⟨743247, by decide⟩,⟨743285, by decide⟩]) unmarked_context_11_23381_743286 node_context_11_23381_743286
  intro a
  fin_cases a
  · exact context_12_93524_743207
  · exact context_12_93525_642341
  · exact context_12_93526_743247
  · exact context_12_93527_743285

theorem selected_cut_29457 : selected 9 ⟨743327, by decide⟩
    (prefixPartial 12 93528) = some ⟨12, 2, 0, 743327, 93528, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_93528_743327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93528 ⟨743327, by decide⟩ :=
  accepted_of_selected 12 93528 ⟨743327, by decide⟩ ⟨12, 2, 0, 743327, 93528, 3009, 65536⟩
    (by decide) selected_cut_29457

theorem selected_cut_29458 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93529) = some ⟨12, 1, 0, 642341, 93529, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93529_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93529 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93529 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93529, 1, 65536⟩
    (by decide) selected_cut_29458

theorem selected_cut_29459 : selected 9 ⟨743369, by decide⟩
    (prefixPartial 12 93530) = some ⟨12, 2, 0, 743369, 93530, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_93530_743369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93530 ⟨743369, by decide⟩ :=
  accepted_of_selected 12 93530 ⟨743369, by decide⟩ ⟨12, 2, 0, 743369, 93530, 3053, 65536⟩
    (by decide) selected_cut_29459

theorem selected_cut_29460 : selected 9 ⟨743412, by decide⟩
    (prefixPartial 12 93531) = some ⟨12, 2, 0, 743412, 93531, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_93531_743412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93531 ⟨743412, by decide⟩ :=
  accepted_of_selected 12 93531 ⟨743412, by decide⟩ ⟨12, 2, 0, 743412, 93531, 3253, 65536⟩
    (by decide) selected_cut_29460

theorem unmarked_context_11_23382_743413 : frontier 10 ⟨743413, by decide⟩
    (prefixCache 11 23382) (prefixPartial 11 23382) = false := by
  decide +kernel

theorem node_context_11_23382_743413 : EJMOriginalGlobalDAGData.nodes 10 ⟨743413, by decide⟩ =
    .split (coordinate 11) (![⟨743327, by decide⟩,⟨642341, by decide⟩,⟨743369, by decide⟩,⟨743412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23382_743413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23382 ⟨743413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23382
    ⟨743413, by decide⟩ (by decide) (![⟨743327, by decide⟩,⟨642341, by decide⟩,⟨743369, by decide⟩,⟨743412, by decide⟩]) unmarked_context_11_23382_743413 node_context_11_23382_743413
  intro a
  fin_cases a
  · exact context_12_93528_743327
  · exact context_12_93529_642341
  · exact context_12_93530_743369
  · exact context_12_93531_743412

theorem selected_cut_29461 : selected 9 ⟨743451, by decide⟩
    (prefixPartial 12 93532) = some ⟨12, 2, 0, 743451, 93532, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_93532_743451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93532 ⟨743451, by decide⟩ :=
  accepted_of_selected 12 93532 ⟨743451, by decide⟩ ⟨12, 2, 0, 743451, 93532, 2925, 65536⟩
    (by decide) selected_cut_29461

theorem selected_cut_29462 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93533) = some ⟨12, 1, 0, 642341, 93533, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93533_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93533 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93533 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93533, 1, 65536⟩
    (by decide) selected_cut_29462

theorem selected_cut_29463 : selected 9 ⟨743491, by decide⟩
    (prefixPartial 12 93534) = some ⟨12, 2, 0, 743491, 93534, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_93534_743491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93534 ⟨743491, by decide⟩ :=
  accepted_of_selected 12 93534 ⟨743491, by decide⟩ ⟨12, 2, 0, 743491, 93534, 3005, 65536⟩
    (by decide) selected_cut_29463

theorem selected_cut_29464 : selected 9 ⟨743536, by decide⟩
    (prefixPartial 12 93535) = some ⟨12, 2, 0, 743536, 93535, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_93535_743536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93535 ⟨743536, by decide⟩ :=
  accepted_of_selected 12 93535 ⟨743536, by decide⟩ ⟨12, 2, 0, 743536, 93535, 3221, 65536⟩
    (by decide) selected_cut_29464

theorem unmarked_context_11_23383_743537 : frontier 10 ⟨743537, by decide⟩
    (prefixCache 11 23383) (prefixPartial 11 23383) = false := by
  decide +kernel

theorem node_context_11_23383_743537 : EJMOriginalGlobalDAGData.nodes 10 ⟨743537, by decide⟩ =
    .split (coordinate 11) (![⟨743451, by decide⟩,⟨642341, by decide⟩,⟨743491, by decide⟩,⟨743536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23383_743537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23383 ⟨743537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23383
    ⟨743537, by decide⟩ (by decide) (![⟨743451, by decide⟩,⟨642341, by decide⟩,⟨743491, by decide⟩,⟨743536, by decide⟩]) unmarked_context_11_23383_743537 node_context_11_23383_743537
  intro a
  fin_cases a
  · exact context_12_93532_743451
  · exact context_12_93533_642341
  · exact context_12_93534_743491
  · exact context_12_93535_743536

theorem unmarked_context_10_5845_743538 : frontier 11 ⟨743538, by decide⟩
    (prefixCache 10 5845) (prefixPartial 10 5845) = false := by
  decide +kernel

theorem node_context_10_5845_743538 : EJMOriginalGlobalDAGData.nodes 11 ⟨743538, by decide⟩ =
    .split (coordinate 10) (![⟨743170, by decide⟩,⟨743286, by decide⟩,⟨743413, by decide⟩,⟨743537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5845_743538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5845 ⟨743538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5845
    ⟨743538, by decide⟩ (by decide) (![⟨743170, by decide⟩,⟨743286, by decide⟩,⟨743413, by decide⟩,⟨743537, by decide⟩]) unmarked_context_10_5845_743538 node_context_10_5845_743538
  intro a
  fin_cases a
  · exact context_11_23380_743170
  · exact context_11_23381_743286
  · exact context_11_23382_743413
  · exact context_11_23383_743537

theorem selected_cut_29465 : selected 9 ⟨743585, by decide⟩
    (prefixPartial 12 93536) = some ⟨12, 2, 0, 743585, 93536, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_93536_743585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93536 ⟨743585, by decide⟩ :=
  accepted_of_selected 12 93536 ⟨743585, by decide⟩ ⟨12, 2, 0, 743585, 93536, 3725, 65536⟩
    (by decide) selected_cut_29465

theorem selected_cut_29466 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 93537) = some ⟨12, 1, 0, 126884, 93537, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93537_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93537 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 93537 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 93537, 1, 65536⟩
    (by decide) selected_cut_29466

theorem selected_cut_29467 : selected 9 ⟨743629, by decide⟩
    (prefixPartial 12 93538) = some ⟨12, 2, 0, 743629, 93538, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_93538_743629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93538 ⟨743629, by decide⟩ :=
  accepted_of_selected 12 93538 ⟨743629, by decide⟩ ⟨12, 2, 0, 743629, 93538, 3921, 65536⟩
    (by decide) selected_cut_29467

theorem selected_cut_29468 : selected 9 ⟨743680, by decide⟩
    (prefixPartial 12 93539) = some ⟨12, 2, 0, 743680, 93539, 3985, 65536⟩ := by
  decide +kernel

theorem context_12_93539_743680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93539 ⟨743680, by decide⟩ :=
  accepted_of_selected 12 93539 ⟨743680, by decide⟩ ⟨12, 2, 0, 743680, 93539, 3985, 65536⟩
    (by decide) selected_cut_29468

theorem unmarked_context_11_23384_743681 : frontier 10 ⟨743681, by decide⟩
    (prefixCache 11 23384) (prefixPartial 11 23384) = false := by
  decide +kernel

theorem node_context_11_23384_743681 : EJMOriginalGlobalDAGData.nodes 10 ⟨743681, by decide⟩ =
    .split (coordinate 11) (![⟨743585, by decide⟩,⟨126884, by decide⟩,⟨743629, by decide⟩,⟨743680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23384_743681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23384 ⟨743681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23384
    ⟨743681, by decide⟩ (by decide) (![⟨743585, by decide⟩,⟨126884, by decide⟩,⟨743629, by decide⟩,⟨743680, by decide⟩]) unmarked_context_11_23384_743681 node_context_11_23384_743681
  intro a
  fin_cases a
  · exact context_12_93536_743585
  · exact context_12_93537_126884
  · exact context_12_93538_743629
  · exact context_12_93539_743680

theorem selected_cut_29469 : selected 9 ⟨743719, by decide⟩
    (prefixPartial 12 93540) = some ⟨12, 2, 0, 743719, 93540, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_93540_743719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93540 ⟨743719, by decide⟩ :=
  accepted_of_selected 12 93540 ⟨743719, by decide⟩ ⟨12, 2, 0, 743719, 93540, 2817, 65536⟩
    (by decide) selected_cut_29469

theorem selected_cut_29470 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 93541) = some ⟨12, 1, 0, 642794, 93541, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93541_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93541 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 93541 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 93541, 1, 65536⟩
    (by decide) selected_cut_29470

theorem selected_cut_29471 : selected 9 ⟨743760, by decide⟩
    (prefixPartial 12 93542) = some ⟨12, 2, 0, 743760, 93542, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_93542_743760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93542 ⟨743760, by decide⟩ :=
  accepted_of_selected 12 93542 ⟨743760, by decide⟩ ⟨12, 2, 0, 743760, 93542, 2793, 65536⟩
    (by decide) selected_cut_29471

theorem selected_cut_29472 : selected 9 ⟨743806, by decide⟩
    (prefixPartial 12 93543) = some ⟨12, 2, 0, 743806, 93543, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_93543_743806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93543 ⟨743806, by decide⟩ :=
  accepted_of_selected 12 93543 ⟨743806, by decide⟩ ⟨12, 2, 0, 743806, 93543, 3177, 65536⟩
    (by decide) selected_cut_29472

theorem unmarked_context_11_23385_743807 : frontier 10 ⟨743807, by decide⟩
    (prefixCache 11 23385) (prefixPartial 11 23385) = false := by
  decide +kernel

theorem node_context_11_23385_743807 : EJMOriginalGlobalDAGData.nodes 10 ⟨743807, by decide⟩ =
    .split (coordinate 11) (![⟨743719, by decide⟩,⟨642794, by decide⟩,⟨743760, by decide⟩,⟨743806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23385_743807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23385 ⟨743807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23385
    ⟨743807, by decide⟩ (by decide) (![⟨743719, by decide⟩,⟨642794, by decide⟩,⟨743760, by decide⟩,⟨743806, by decide⟩]) unmarked_context_11_23385_743807 node_context_11_23385_743807
  intro a
  fin_cases a
  · exact context_12_93540_743719
  · exact context_12_93541_642794
  · exact context_12_93542_743760
  · exact context_12_93543_743806

theorem selected_cut_29473 : selected 9 ⟨743849, by decide⟩
    (prefixPartial 12 93544) = some ⟨12, 2, 0, 743849, 93544, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_93544_743849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93544 ⟨743849, by decide⟩ :=
  accepted_of_selected 12 93544 ⟨743849, by decide⟩ ⟨12, 2, 0, 743849, 93544, 3161, 65536⟩
    (by decide) selected_cut_29473

theorem selected_cut_29474 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 93545) = some ⟨12, 1, 0, 691709, 93545, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93545_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93545 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 93545 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 93545, 1, 65536⟩
    (by decide) selected_cut_29474

theorem selected_cut_29475 : selected 9 ⟨743897, by decide⟩
    (prefixPartial 12 93546) = some ⟨12, 2, 0, 743897, 93546, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_93546_743897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93546 ⟨743897, by decide⟩ :=
  accepted_of_selected 12 93546 ⟨743897, by decide⟩ ⟨12, 2, 0, 743897, 93546, 3045, 65536⟩
    (by decide) selected_cut_29475

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
