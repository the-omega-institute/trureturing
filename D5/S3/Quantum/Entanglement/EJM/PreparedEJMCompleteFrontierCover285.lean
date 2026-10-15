/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover284
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_22875_691894 : frontier 10 ⟨691894, by decide⟩
    (prefixCache 11 22875) (prefixPartial 11 22875) = false := by
  decide +kernel

theorem node_context_11_22875_691894 : EJMOriginalGlobalDAGData.nodes 10 ⟨691894, by decide⟩ =
    .split (coordinate 11) (![⟨691821, by decide⟩,⟨691822, by decide⟩,⟨691855, by decide⟩,⟨691893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22875_691894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22875 ⟨691894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22875
    ⟨691894, by decide⟩ (by decide) (![⟨691821, by decide⟩,⟨691822, by decide⟩,⟨691855, by decide⟩,⟨691893, by decide⟩]) unmarked_context_11_22875_691894 node_context_11_22875_691894
  intro a
  fin_cases a
  · exact context_12_91500_691821
  · exact context_12_91501_691822
  · exact context_12_91502_691855
  · exact context_12_91503_691893

theorem unmarked_context_10_5718_691895 : frontier 11 ⟨691895, by decide⟩
    (prefixCache 10 5718) (prefixPartial 10 5718) = false := by
  decide +kernel

theorem node_context_10_5718_691895 : EJMOriginalGlobalDAGData.nodes 11 ⟨691895, by decide⟩ =
    .split (coordinate 10) (![⟨691566, by decide⟩,⟨691670, by decide⟩,⟨691780, by decide⟩,⟨691894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5718_691895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5718 ⟨691895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5718
    ⟨691895, by decide⟩ (by decide) (![⟨691566, by decide⟩,⟨691670, by decide⟩,⟨691780, by decide⟩,⟨691894, by decide⟩]) unmarked_context_10_5718_691895 node_context_10_5718_691895
  intro a
  fin_cases a
  · exact context_11_22872_691566
  · exact context_11_22873_691670
  · exact context_11_22874_691780
  · exact context_11_22875_691894

theorem selected_cut_27364 : selected 9 ⟨691936, by decide⟩
    (prefixPartial 12 91504) = some ⟨12, 2, 0, 691936, 91504, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_91504_691936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91504 ⟨691936, by decide⟩ :=
  accepted_of_selected 12 91504 ⟨691936, by decide⟩ ⟨12, 2, 0, 691936, 91504, 3177, 65536⟩
    (by decide) selected_cut_27364

theorem selected_cut_27365 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 91505) = some ⟨12, 1, 0, 126884, 91505, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91505_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91505 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 91505 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 91505, 1, 65536⟩
    (by decide) selected_cut_27365

theorem selected_cut_27366 : selected 9 ⟨691981, by decide⟩
    (prefixPartial 12 91506) = some ⟨12, 2, 0, 691981, 91506, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_91506_691981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91506 ⟨691981, by decide⟩ :=
  accepted_of_selected 12 91506 ⟨691981, by decide⟩ ⟨12, 2, 0, 691981, 91506, 3313, 65536⟩
    (by decide) selected_cut_27366

theorem selected_cut_27367 : selected 9 ⟨692024, by decide⟩
    (prefixPartial 12 91507) = some ⟨12, 2, 0, 692024, 91507, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_91507_692024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91507 ⟨692024, by decide⟩ :=
  accepted_of_selected 12 91507 ⟨692024, by decide⟩ ⟨12, 2, 0, 692024, 91507, 3257, 65536⟩
    (by decide) selected_cut_27367

theorem unmarked_context_11_22876_692025 : frontier 10 ⟨692025, by decide⟩
    (prefixCache 11 22876) (prefixPartial 11 22876) = false := by
  decide +kernel

theorem node_context_11_22876_692025 : EJMOriginalGlobalDAGData.nodes 10 ⟨692025, by decide⟩ =
    .split (coordinate 11) (![⟨691936, by decide⟩,⟨126884, by decide⟩,⟨691981, by decide⟩,⟨692024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22876_692025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22876 ⟨692025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22876
    ⟨692025, by decide⟩ (by decide) (![⟨691936, by decide⟩,⟨126884, by decide⟩,⟨691981, by decide⟩,⟨692024, by decide⟩]) unmarked_context_11_22876_692025 node_context_11_22876_692025
  intro a
  fin_cases a
  · exact context_12_91504_691936
  · exact context_12_91505_126884
  · exact context_12_91506_691981
  · exact context_12_91507_692024

theorem selected_cut_27368 : selected 9 ⟨692054, by decide⟩
    (prefixPartial 12 91508) = some ⟨12, 2, 0, 692054, 91508, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_91508_692054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91508 ⟨692054, by decide⟩ :=
  accepted_of_selected 12 91508 ⟨692054, by decide⟩ ⟨12, 2, 0, 692054, 91508, 2085, 65536⟩
    (by decide) selected_cut_27368

theorem selected_cut_27369 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 91509) = some ⟨12, 1, 0, 689956, 91509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91509_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91509 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 91509 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 91509, 1, 65536⟩
    (by decide) selected_cut_27369

theorem selected_cut_27370 : selected 9 ⟨692086, by decide⟩
    (prefixPartial 12 91510) = some ⟨12, 2, 0, 692086, 91510, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_91510_692086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91510 ⟨692086, by decide⟩ :=
  accepted_of_selected 12 91510 ⟨692086, by decide⟩ ⟨12, 2, 0, 692086, 91510, 2153, 65536⟩
    (by decide) selected_cut_27370

theorem selected_cut_27371 : selected 9 ⟨692114, by decide⟩
    (prefixPartial 12 91511) = some ⟨12, 2, 0, 692114, 91511, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_91511_692114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91511 ⟨692114, by decide⟩ :=
  accepted_of_selected 12 91511 ⟨692114, by decide⟩ ⟨12, 2, 0, 692114, 91511, 2113, 65536⟩
    (by decide) selected_cut_27371

theorem unmarked_context_11_22877_692115 : frontier 10 ⟨692115, by decide⟩
    (prefixCache 11 22877) (prefixPartial 11 22877) = false := by
  decide +kernel

theorem node_context_11_22877_692115 : EJMOriginalGlobalDAGData.nodes 10 ⟨692115, by decide⟩ =
    .split (coordinate 11) (![⟨692054, by decide⟩,⟨689956, by decide⟩,⟨692086, by decide⟩,⟨692114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22877_692115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22877 ⟨692115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22877
    ⟨692115, by decide⟩ (by decide) (![⟨692054, by decide⟩,⟨689956, by decide⟩,⟨692086, by decide⟩,⟨692114, by decide⟩]) unmarked_context_11_22877_692115 node_context_11_22877_692115
  intro a
  fin_cases a
  · exact context_12_91508_692054
  · exact context_12_91509_689956
  · exact context_12_91510_692086
  · exact context_12_91511_692114

theorem selected_cut_27372 : selected 9 ⟨692144, by decide⟩
    (prefixPartial 12 91512) = some ⟨12, 2, 0, 692144, 91512, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_91512_692144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91512 ⟨692144, by decide⟩ :=
  accepted_of_selected 12 91512 ⟨692144, by decide⟩ ⟨12, 2, 0, 692144, 91512, 2921, 65536⟩
    (by decide) selected_cut_27372

theorem selected_cut_27373 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 91513) = some ⟨12, 1, 0, 691709, 91513, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91513_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91513 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 91513 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 91513, 1, 65536⟩
    (by decide) selected_cut_27373

theorem selected_cut_27374 : selected 9 ⟨692178, by decide⟩
    (prefixPartial 12 91514) = some ⟨12, 2, 0, 692178, 91514, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_91514_692178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91514 ⟨692178, by decide⟩ :=
  accepted_of_selected 12 91514 ⟨692178, by decide⟩ ⟨12, 2, 0, 692178, 91514, 2673, 65536⟩
    (by decide) selected_cut_27374

theorem selected_cut_27375 : selected 9 ⟨692215, by decide⟩
    (prefixPartial 12 91515) = some ⟨12, 2, 0, 692215, 91515, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_91515_692215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91515 ⟨692215, by decide⟩ :=
  accepted_of_selected 12 91515 ⟨692215, by decide⟩ ⟨12, 2, 0, 692215, 91515, 2729, 65536⟩
    (by decide) selected_cut_27375

theorem unmarked_context_11_22878_692216 : frontier 10 ⟨692216, by decide⟩
    (prefixCache 11 22878) (prefixPartial 11 22878) = false := by
  decide +kernel

theorem node_context_11_22878_692216 : EJMOriginalGlobalDAGData.nodes 10 ⟨692216, by decide⟩ =
    .split (coordinate 11) (![⟨692144, by decide⟩,⟨691709, by decide⟩,⟨692178, by decide⟩,⟨692215, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22878_692216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22878 ⟨692216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22878
    ⟨692216, by decide⟩ (by decide) (![⟨692144, by decide⟩,⟨691709, by decide⟩,⟨692178, by decide⟩,⟨692215, by decide⟩]) unmarked_context_11_22878_692216 node_context_11_22878_692216
  intro a
  fin_cases a
  · exact context_12_91512_692144
  · exact context_12_91513_691709
  · exact context_12_91514_692178
  · exact context_12_91515_692215

theorem selected_cut_27376 : selected 9 ⟨692248, by decide⟩
    (prefixPartial 12 91516) = some ⟨12, 2, 0, 692248, 91516, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_91516_692248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91516 ⟨692248, by decide⟩ :=
  accepted_of_selected 12 91516 ⟨692248, by decide⟩ ⟨12, 2, 0, 692248, 91516, 2669, 65536⟩
    (by decide) selected_cut_27376

theorem selected_cut_27377 : selected 9 ⟨691822, by decide⟩
    (prefixPartial 12 91517) = some ⟨12, 1, 0, 691822, 91517, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91517_691822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91517 ⟨691822, by decide⟩ :=
  accepted_of_selected 12 91517 ⟨691822, by decide⟩ ⟨12, 1, 0, 691822, 91517, 1, 65536⟩
    (by decide) selected_cut_27377

theorem selected_cut_27378 : selected 9 ⟨692279, by decide⟩
    (prefixPartial 12 91518) = some ⟨12, 2, 0, 692279, 91518, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_91518_692279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91518 ⟨692279, by decide⟩ :=
  accepted_of_selected 12 91518 ⟨692279, by decide⟩ ⟨12, 2, 0, 692279, 91518, 2589, 65536⟩
    (by decide) selected_cut_27378

theorem selected_cut_27379 : selected 9 ⟨692312, by decide⟩
    (prefixPartial 12 91519) = some ⟨12, 2, 0, 692312, 91519, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_91519_692312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91519 ⟨692312, by decide⟩ :=
  accepted_of_selected 12 91519 ⟨692312, by decide⟩ ⟨12, 2, 0, 692312, 91519, 2553, 65536⟩
    (by decide) selected_cut_27379

theorem unmarked_context_11_22879_692313 : frontier 10 ⟨692313, by decide⟩
    (prefixCache 11 22879) (prefixPartial 11 22879) = false := by
  decide +kernel

theorem node_context_11_22879_692313 : EJMOriginalGlobalDAGData.nodes 10 ⟨692313, by decide⟩ =
    .split (coordinate 11) (![⟨692248, by decide⟩,⟨691822, by decide⟩,⟨692279, by decide⟩,⟨692312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22879_692313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22879 ⟨692313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22879
    ⟨692313, by decide⟩ (by decide) (![⟨692248, by decide⟩,⟨691822, by decide⟩,⟨692279, by decide⟩,⟨692312, by decide⟩]) unmarked_context_11_22879_692313 node_context_11_22879_692313
  intro a
  fin_cases a
  · exact context_12_91516_692248
  · exact context_12_91517_691822
  · exact context_12_91518_692279
  · exact context_12_91519_692312

theorem unmarked_context_10_5719_692314 : frontier 11 ⟨692314, by decide⟩
    (prefixCache 10 5719) (prefixPartial 10 5719) = false := by
  decide +kernel

theorem node_context_10_5719_692314 : EJMOriginalGlobalDAGData.nodes 11 ⟨692314, by decide⟩ =
    .split (coordinate 10) (![⟨692025, by decide⟩,⟨692115, by decide⟩,⟨692216, by decide⟩,⟨692313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5719_692314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5719 ⟨692314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5719
    ⟨692314, by decide⟩ (by decide) (![⟨692025, by decide⟩,⟨692115, by decide⟩,⟨692216, by decide⟩,⟨692313, by decide⟩]) unmarked_context_10_5719_692314 node_context_10_5719_692314
  intro a
  fin_cases a
  · exact context_11_22876_692025
  · exact context_11_22877_692115
  · exact context_11_22878_692216
  · exact context_11_22879_692313

theorem unmarked_context_9_1429_692315 : frontier 12 ⟨692315, by decide⟩
    (prefixCache 9 1429) (prefixPartial 9 1429) = false := by
  decide +kernel

theorem node_context_9_1429_692315 : EJMOriginalGlobalDAGData.nodes 12 ⟨692315, by decide⟩ =
    .split (coordinate 9) (![⟨691082, by decide⟩,⟨691442, by decide⟩,⟨691895, by decide⟩,⟨692314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1429_692315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1429 ⟨692315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1429
    ⟨692315, by decide⟩ (by decide) (![⟨691082, by decide⟩,⟨691442, by decide⟩,⟨691895, by decide⟩,⟨692314, by decide⟩]) unmarked_context_9_1429_692315 node_context_9_1429_692315
  intro a
  fin_cases a
  · exact context_10_5716_691082
  · exact context_10_5717_691442
  · exact context_10_5718_691895
  · exact context_10_5719_692314

theorem selected_cut_27380 : selected 9 ⟨692342, by decide⟩
    (prefixPartial 12 91520) = some ⟨12, 2, 0, 692342, 91520, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_91520_692342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91520 ⟨692342, by decide⟩ :=
  accepted_of_selected 12 91520 ⟨692342, by decide⟩ ⟨12, 2, 0, 692342, 91520, 2073, 65536⟩
    (by decide) selected_cut_27380

theorem selected_cut_27381 : selected 9 ⟨692364, by decide⟩
    (prefixPartial 12 91521) = some ⟨12, 2, 0, 692364, 91521, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_91521_692364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91521 ⟨692364, by decide⟩ :=
  accepted_of_selected 12 91521 ⟨692364, by decide⟩ ⟨12, 2, 0, 692364, 91521, 1853, 65536⟩
    (by decide) selected_cut_27381

theorem selected_cut_27382 : selected 9 ⟨692390, by decide⟩
    (prefixPartial 12 91522) = some ⟨12, 2, 0, 692390, 91522, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_91522_692390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91522 ⟨692390, by decide⟩ :=
  accepted_of_selected 12 91522 ⟨692390, by decide⟩ ⟨12, 2, 0, 692390, 91522, 2185, 65536⟩
    (by decide) selected_cut_27382

theorem selected_cut_27383 : selected 9 ⟨692420, by decide⟩
    (prefixPartial 12 91523) = some ⟨12, 2, 0, 692420, 91523, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_91523_692420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91523 ⟨692420, by decide⟩ :=
  accepted_of_selected 12 91523 ⟨692420, by decide⟩ ⟨12, 2, 0, 692420, 91523, 2337, 65536⟩
    (by decide) selected_cut_27383

theorem unmarked_context_11_22880_692421 : frontier 10 ⟨692421, by decide⟩
    (prefixCache 11 22880) (prefixPartial 11 22880) = false := by
  decide +kernel

theorem node_context_11_22880_692421 : EJMOriginalGlobalDAGData.nodes 10 ⟨692421, by decide⟩ =
    .split (coordinate 11) (![⟨692342, by decide⟩,⟨692364, by decide⟩,⟨692390, by decide⟩,⟨692420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22880_692421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22880 ⟨692421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22880
    ⟨692421, by decide⟩ (by decide) (![⟨692342, by decide⟩,⟨692364, by decide⟩,⟨692390, by decide⟩,⟨692420, by decide⟩]) unmarked_context_11_22880_692421 node_context_11_22880_692421
  intro a
  fin_cases a
  · exact context_12_91520_692342
  · exact context_12_91521_692364
  · exact context_12_91522_692390
  · exact context_12_91523_692420

theorem selected_cut_27384 : selected 9 ⟨692442, by decide⟩
    (prefixPartial 12 91524) = some ⟨12, 2, 0, 692442, 91524, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_91524_692442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91524 ⟨692442, by decide⟩ :=
  accepted_of_selected 12 91524 ⟨692442, by decide⟩ ⟨12, 2, 0, 692442, 91524, 1741, 65536⟩
    (by decide) selected_cut_27384

theorem selected_cut_27385 : selected 9 ⟨692443, by decide⟩
    (prefixPartial 12 91525) = some ⟨12, 1, 0, 692443, 91525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91525_692443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91525 ⟨692443, by decide⟩ :=
  accepted_of_selected 12 91525 ⟨692443, by decide⟩ ⟨12, 1, 0, 692443, 91525, 1, 65536⟩
    (by decide) selected_cut_27385

theorem selected_cut_27386 : selected 9 ⟨692466, by decide⟩
    (prefixPartial 12 91526) = some ⟨12, 2, 0, 692466, 91526, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_91526_692466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91526 ⟨692466, by decide⟩ :=
  accepted_of_selected 12 91526 ⟨692466, by decide⟩ ⟨12, 2, 0, 692466, 91526, 1833, 65536⟩
    (by decide) selected_cut_27386

theorem selected_cut_27387 : selected 9 ⟨692493, by decide⟩
    (prefixPartial 12 91527) = some ⟨12, 2, 0, 692493, 91527, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_91527_692493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91527 ⟨692493, by decide⟩ :=
  accepted_of_selected 12 91527 ⟨692493, by decide⟩ ⟨12, 2, 0, 692493, 91527, 2009, 65536⟩
    (by decide) selected_cut_27387

theorem unmarked_context_11_22881_692494 : frontier 10 ⟨692494, by decide⟩
    (prefixCache 11 22881) (prefixPartial 11 22881) = false := by
  decide +kernel

theorem node_context_11_22881_692494 : EJMOriginalGlobalDAGData.nodes 10 ⟨692494, by decide⟩ =
    .split (coordinate 11) (![⟨692442, by decide⟩,⟨692443, by decide⟩,⟨692466, by decide⟩,⟨692493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22881_692494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22881 ⟨692494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22881
    ⟨692494, by decide⟩ (by decide) (![⟨692442, by decide⟩,⟨692443, by decide⟩,⟨692466, by decide⟩,⟨692493, by decide⟩]) unmarked_context_11_22881_692494 node_context_11_22881_692494
  intro a
  fin_cases a
  · exact context_12_91524_692442
  · exact context_12_91525_692443
  · exact context_12_91526_692466
  · exact context_12_91527_692493

theorem selected_cut_27388 : selected 9 ⟨692518, by decide⟩
    (prefixPartial 12 91528) = some ⟨12, 2, 0, 692518, 91528, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_91528_692518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91528 ⟨692518, by decide⟩ :=
  accepted_of_selected 12 91528 ⟨692518, by decide⟩ ⟨12, 2, 0, 692518, 91528, 2249, 65536⟩
    (by decide) selected_cut_27388

theorem selected_cut_27389 : selected 9 ⟨692542, by decide⟩
    (prefixPartial 12 91529) = some ⟨12, 2, 0, 692542, 91529, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_91529_692542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91529 ⟨692542, by decide⟩ :=
  accepted_of_selected 12 91529 ⟨692542, by decide⟩ ⟨12, 2, 0, 692542, 91529, 2085, 65536⟩
    (by decide) selected_cut_27389

theorem selected_cut_27390 : selected 9 ⟨692566, by decide⟩
    (prefixPartial 12 91530) = some ⟨12, 2, 0, 692566, 91530, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_91530_692566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91530 ⟨692566, by decide⟩ :=
  accepted_of_selected 12 91530 ⟨692566, by decide⟩ ⟨12, 2, 0, 692566, 91530, 2105, 65536⟩
    (by decide) selected_cut_27390

theorem selected_cut_27391 : selected 9 ⟨692593, by decide⟩
    (prefixPartial 12 91531) = some ⟨12, 2, 0, 692593, 91531, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_91531_692593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91531 ⟨692593, by decide⟩ :=
  accepted_of_selected 12 91531 ⟨692593, by decide⟩ ⟨12, 2, 0, 692593, 91531, 2285, 65536⟩
    (by decide) selected_cut_27391

theorem unmarked_context_11_22882_692594 : frontier 10 ⟨692594, by decide⟩
    (prefixCache 11 22882) (prefixPartial 11 22882) = false := by
  decide +kernel

theorem node_context_11_22882_692594 : EJMOriginalGlobalDAGData.nodes 10 ⟨692594, by decide⟩ =
    .split (coordinate 11) (![⟨692518, by decide⟩,⟨692542, by decide⟩,⟨692566, by decide⟩,⟨692593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22882_692594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22882 ⟨692594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22882
    ⟨692594, by decide⟩ (by decide) (![⟨692518, by decide⟩,⟨692542, by decide⟩,⟨692566, by decide⟩,⟨692593, by decide⟩]) unmarked_context_11_22882_692594 node_context_11_22882_692594
  intro a
  fin_cases a
  · exact context_12_91528_692518
  · exact context_12_91529_692542
  · exact context_12_91530_692566
  · exact context_12_91531_692593

theorem selected_cut_27392 : selected 9 ⟨692625, by decide⟩
    (prefixPartial 12 91532) = some ⟨12, 2, 0, 692625, 91532, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_91532_692625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91532 ⟨692625, by decide⟩ :=
  accepted_of_selected 12 91532 ⟨692625, by decide⟩ ⟨12, 2, 0, 692625, 91532, 1933, 65536⟩
    (by decide) selected_cut_27392

theorem selected_cut_27393 : selected 9 ⟨692648, by decide⟩
    (prefixPartial 12 91533) = some ⟨12, 2, 0, 692648, 91533, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_91533_692648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91533 ⟨692648, by decide⟩ :=
  accepted_of_selected 12 91533 ⟨692648, by decide⟩ ⟨12, 2, 0, 692648, 91533, 1561, 65536⟩
    (by decide) selected_cut_27393

theorem selected_cut_27394 : selected 9 ⟨692675, by decide⟩
    (prefixPartial 12 91534) = some ⟨12, 2, 0, 692675, 91534, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_91534_692675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91534 ⟨692675, by decide⟩ :=
  accepted_of_selected 12 91534 ⟨692675, by decide⟩ ⟨12, 2, 0, 692675, 91534, 1909, 65536⟩
    (by decide) selected_cut_27394

theorem selected_cut_27395 : selected 9 ⟨692701, by decide⟩
    (prefixPartial 12 91535) = some ⟨12, 2, 0, 692701, 91535, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_91535_692701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91535 ⟨692701, by decide⟩ :=
  accepted_of_selected 12 91535 ⟨692701, by decide⟩ ⟨12, 2, 0, 692701, 91535, 1917, 65536⟩
    (by decide) selected_cut_27395

theorem unmarked_context_11_22883_692702 : frontier 10 ⟨692702, by decide⟩
    (prefixCache 11 22883) (prefixPartial 11 22883) = false := by
  decide +kernel

theorem node_context_11_22883_692702 : EJMOriginalGlobalDAGData.nodes 10 ⟨692702, by decide⟩ =
    .split (coordinate 11) (![⟨692625, by decide⟩,⟨692648, by decide⟩,⟨692675, by decide⟩,⟨692701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22883_692702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22883 ⟨692702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22883
    ⟨692702, by decide⟩ (by decide) (![⟨692625, by decide⟩,⟨692648, by decide⟩,⟨692675, by decide⟩,⟨692701, by decide⟩]) unmarked_context_11_22883_692702 node_context_11_22883_692702
  intro a
  fin_cases a
  · exact context_12_91532_692625
  · exact context_12_91533_692648
  · exact context_12_91534_692675
  · exact context_12_91535_692701

theorem unmarked_context_10_5720_692703 : frontier 11 ⟨692703, by decide⟩
    (prefixCache 10 5720) (prefixPartial 10 5720) = false := by
  decide +kernel

theorem node_context_10_5720_692703 : EJMOriginalGlobalDAGData.nodes 11 ⟨692703, by decide⟩ =
    .split (coordinate 10) (![⟨692421, by decide⟩,⟨692494, by decide⟩,⟨692594, by decide⟩,⟨692702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5720_692703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5720 ⟨692703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5720
    ⟨692703, by decide⟩ (by decide) (![⟨692421, by decide⟩,⟨692494, by decide⟩,⟨692594, by decide⟩,⟨692702, by decide⟩]) unmarked_context_10_5720_692703 node_context_10_5720_692703
  intro a
  fin_cases a
  · exact context_11_22880_692421
  · exact context_11_22881_692494
  · exact context_11_22882_692594
  · exact context_11_22883_692702

theorem selected_cut_27396 : selected 9 ⟨692726, by decide⟩
    (prefixPartial 12 91536) = some ⟨12, 2, 0, 692726, 91536, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_91536_692726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91536 ⟨692726, by decide⟩ :=
  accepted_of_selected 12 91536 ⟨692726, by decide⟩ ⟨12, 2, 0, 692726, 91536, 1781, 65536⟩
    (by decide) selected_cut_27396

theorem selected_cut_27397 : selected 9 ⟨692745, by decide⟩
    (prefixPartial 12 91537) = some ⟨12, 2, 0, 692745, 91537, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_91537_692745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91537 ⟨692745, by decide⟩ :=
  accepted_of_selected 12 91537 ⟨692745, by decide⟩ ⟨12, 2, 0, 692745, 91537, 1593, 65536⟩
    (by decide) selected_cut_27397

theorem selected_cut_27398 : selected 9 ⟨692769, by decide⟩
    (prefixPartial 12 91538) = some ⟨12, 2, 0, 692769, 91538, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_91538_692769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91538 ⟨692769, by decide⟩ :=
  accepted_of_selected 12 91538 ⟨692769, by decide⟩ ⟨12, 2, 0, 692769, 91538, 1901, 65536⟩
    (by decide) selected_cut_27398

theorem selected_cut_27399 : selected 9 ⟨692791, by decide⟩
    (prefixPartial 12 91539) = some ⟨12, 2, 0, 692791, 91539, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_91539_692791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91539 ⟨692791, by decide⟩ :=
  accepted_of_selected 12 91539 ⟨692791, by decide⟩ ⟨12, 2, 0, 692791, 91539, 1905, 65536⟩
    (by decide) selected_cut_27399

theorem unmarked_context_11_22884_692792 : frontier 10 ⟨692792, by decide⟩
    (prefixCache 11 22884) (prefixPartial 11 22884) = false := by
  decide +kernel

theorem node_context_11_22884_692792 : EJMOriginalGlobalDAGData.nodes 10 ⟨692792, by decide⟩ =
    .split (coordinate 11) (![⟨692726, by decide⟩,⟨692745, by decide⟩,⟨692769, by decide⟩,⟨692791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22884_692792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22884 ⟨692792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22884
    ⟨692792, by decide⟩ (by decide) (![⟨692726, by decide⟩,⟨692745, by decide⟩,⟨692769, by decide⟩,⟨692791, by decide⟩]) unmarked_context_11_22884_692792 node_context_11_22884_692792
  intro a
  fin_cases a
  · exact context_12_91536_692726
  · exact context_12_91537_692745
  · exact context_12_91538_692769
  · exact context_12_91539_692791

theorem selected_cut_27400 : selected 10 ⟨692795, by decide⟩
    (prefixPartial 11 22885) = some ⟨11, 2, 0, 692795, 22885, 5, 262144⟩ := by
  decide +kernel

theorem context_11_22885_692795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22885 ⟨692795, by decide⟩ :=
  accepted_of_selected 11 22885 ⟨692795, by decide⟩ ⟨11, 2, 0, 692795, 22885, 5, 262144⟩
    (by decide) selected_cut_27400

theorem selected_cut_27401 : selected 9 ⟨692815, by decide⟩
    (prefixPartial 12 91544) = some ⟨12, 2, 0, 692815, 91544, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_91544_692815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91544 ⟨692815, by decide⟩ :=
  accepted_of_selected 12 91544 ⟨692815, by decide⟩ ⟨12, 2, 0, 692815, 91544, 1889, 65536⟩
    (by decide) selected_cut_27401

theorem selected_cut_27402 : selected 9 ⟨692831, by decide⟩
    (prefixPartial 12 91545) = some ⟨12, 2, 0, 692831, 91545, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_91545_692831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91545 ⟨692831, by decide⟩ :=
  accepted_of_selected 12 91545 ⟨692831, by decide⟩ ⟨12, 2, 0, 692831, 91545, 1645, 65536⟩
    (by decide) selected_cut_27402

theorem selected_cut_27403 : selected 9 ⟨692852, by decide⟩
    (prefixPartial 12 91546) = some ⟨12, 2, 0, 692852, 91546, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_91546_692852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91546 ⟨692852, by decide⟩ :=
  accepted_of_selected 12 91546 ⟨692852, by decide⟩ ⟨12, 2, 0, 692852, 91546, 1757, 65536⟩
    (by decide) selected_cut_27403

theorem selected_cut_27404 : selected 9 ⟨692872, by decide⟩
    (prefixPartial 12 91547) = some ⟨12, 2, 0, 692872, 91547, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_91547_692872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91547 ⟨692872, by decide⟩ :=
  accepted_of_selected 12 91547 ⟨692872, by decide⟩ ⟨12, 2, 0, 692872, 91547, 1753, 65536⟩
    (by decide) selected_cut_27404

theorem unmarked_context_11_22886_692873 : frontier 10 ⟨692873, by decide⟩
    (prefixCache 11 22886) (prefixPartial 11 22886) = false := by
  decide +kernel

theorem node_context_11_22886_692873 : EJMOriginalGlobalDAGData.nodes 10 ⟨692873, by decide⟩ =
    .split (coordinate 11) (![⟨692815, by decide⟩,⟨692831, by decide⟩,⟨692852, by decide⟩,⟨692872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22886_692873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22886 ⟨692873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22886
    ⟨692873, by decide⟩ (by decide) (![⟨692815, by decide⟩,⟨692831, by decide⟩,⟨692852, by decide⟩,⟨692872, by decide⟩]) unmarked_context_11_22886_692873 node_context_11_22886_692873
  intro a
  fin_cases a
  · exact context_12_91544_692815
  · exact context_12_91545_692831
  · exact context_12_91546_692852
  · exact context_12_91547_692872

theorem selected_cut_27405 : selected 9 ⟨692894, by decide⟩
    (prefixPartial 12 91548) = some ⟨12, 2, 0, 692894, 91548, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_91548_692894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91548 ⟨692894, by decide⟩ :=
  accepted_of_selected 12 91548 ⟨692894, by decide⟩ ⟨12, 2, 0, 692894, 91548, 1629, 65536⟩
    (by decide) selected_cut_27405

theorem selected_cut_27406 : selected 9 ⟨692911, by decide⟩
    (prefixPartial 12 91549) = some ⟨12, 2, 0, 692911, 91549, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_91549_692911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91549 ⟨692911, by decide⟩ :=
  accepted_of_selected 12 91549 ⟨692911, by decide⟩ ⟨12, 2, 0, 692911, 91549, 1297, 65536⟩
    (by decide) selected_cut_27406

theorem selected_cut_27407 : selected 9 ⟨692933, by decide⟩
    (prefixPartial 12 91550) = some ⟨12, 2, 0, 692933, 91550, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_91550_692933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91550 ⟨692933, by decide⟩ :=
  accepted_of_selected 12 91550 ⟨692933, by decide⟩ ⟨12, 2, 0, 692933, 91550, 1561, 65536⟩
    (by decide) selected_cut_27407

theorem selected_cut_27408 : selected 9 ⟨692952, by decide⟩
    (prefixPartial 12 91551) = some ⟨12, 2, 0, 692952, 91551, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_91551_692952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91551 ⟨692952, by decide⟩ :=
  accepted_of_selected 12 91551 ⟨692952, by decide⟩ ⟨12, 2, 0, 692952, 91551, 1501, 65536⟩
    (by decide) selected_cut_27408

theorem unmarked_context_11_22887_692953 : frontier 10 ⟨692953, by decide⟩
    (prefixCache 11 22887) (prefixPartial 11 22887) = false := by
  decide +kernel

theorem node_context_11_22887_692953 : EJMOriginalGlobalDAGData.nodes 10 ⟨692953, by decide⟩ =
    .split (coordinate 11) (![⟨692894, by decide⟩,⟨692911, by decide⟩,⟨692933, by decide⟩,⟨692952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22887_692953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22887 ⟨692953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22887
    ⟨692953, by decide⟩ (by decide) (![⟨692894, by decide⟩,⟨692911, by decide⟩,⟨692933, by decide⟩,⟨692952, by decide⟩]) unmarked_context_11_22887_692953 node_context_11_22887_692953
  intro a
  fin_cases a
  · exact context_12_91548_692894
  · exact context_12_91549_692911
  · exact context_12_91550_692933
  · exact context_12_91551_692952

theorem unmarked_context_10_5721_692954 : frontier 11 ⟨692954, by decide⟩
    (prefixCache 10 5721) (prefixPartial 10 5721) = false := by
  decide +kernel

theorem node_context_10_5721_692954 : EJMOriginalGlobalDAGData.nodes 11 ⟨692954, by decide⟩ =
    .split (coordinate 10) (![⟨692792, by decide⟩,⟨692795, by decide⟩,⟨692873, by decide⟩,⟨692953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5721_692954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5721 ⟨692954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5721
    ⟨692954, by decide⟩ (by decide) (![⟨692792, by decide⟩,⟨692795, by decide⟩,⟨692873, by decide⟩,⟨692953, by decide⟩]) unmarked_context_10_5721_692954 node_context_10_5721_692954
  intro a
  fin_cases a
  · exact context_11_22884_692792
  · exact context_11_22885_692795
  · exact context_11_22886_692873
  · exact context_11_22887_692953

theorem selected_cut_27409 : selected 9 ⟨692974, by decide⟩
    (prefixPartial 12 91552) = some ⟨12, 2, 0, 692974, 91552, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_91552_692974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91552 ⟨692974, by decide⟩ :=
  accepted_of_selected 12 91552 ⟨692974, by decide⟩ ⟨12, 2, 0, 692974, 91552, 1477, 65536⟩
    (by decide) selected_cut_27409

theorem selected_cut_27410 : selected 9 ⟨692988, by decide⟩
    (prefixPartial 12 91553) = some ⟨12, 2, 0, 692988, 91553, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_91553_692988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91553 ⟨692988, by decide⟩ :=
  accepted_of_selected 12 91553 ⟨692988, by decide⟩ ⟨12, 2, 0, 692988, 91553, 1301, 65536⟩
    (by decide) selected_cut_27410

theorem selected_cut_27411 : selected 9 ⟨693005, by decide⟩
    (prefixPartial 12 91554) = some ⟨12, 2, 0, 693005, 91554, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_91554_693005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91554 ⟨693005, by decide⟩ :=
  accepted_of_selected 12 91554 ⟨693005, by decide⟩ ⟨12, 2, 0, 693005, 91554, 1401, 65536⟩
    (by decide) selected_cut_27411

theorem selected_cut_27412 : selected 9 ⟨693023, by decide⟩
    (prefixPartial 12 91555) = some ⟨12, 2, 0, 693023, 91555, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_91555_693023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91555 ⟨693023, by decide⟩ :=
  accepted_of_selected 12 91555 ⟨693023, by decide⟩ ⟨12, 2, 0, 693023, 91555, 1409, 65536⟩
    (by decide) selected_cut_27412

theorem unmarked_context_11_22888_693024 : frontier 10 ⟨693024, by decide⟩
    (prefixCache 11 22888) (prefixPartial 11 22888) = false := by
  decide +kernel

theorem node_context_11_22888_693024 : EJMOriginalGlobalDAGData.nodes 10 ⟨693024, by decide⟩ =
    .split (coordinate 11) (![⟨692974, by decide⟩,⟨692988, by decide⟩,⟨693005, by decide⟩,⟨693023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22888_693024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22888 ⟨693024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22888
    ⟨693024, by decide⟩ (by decide) (![⟨692974, by decide⟩,⟨692988, by decide⟩,⟨693005, by decide⟩,⟨693023, by decide⟩]) unmarked_context_11_22888_693024 node_context_11_22888_693024
  intro a
  fin_cases a
  · exact context_12_91552_692974
  · exact context_12_91553_692988
  · exact context_12_91554_693005
  · exact context_12_91555_693023

theorem selected_cut_27413 : selected 10 ⟨693068, by decide⟩
    (prefixPartial 11 22889) = some ⟨11, 2, 0, 693068, 22889, 3377, 262144⟩ := by
  decide +kernel

theorem context_11_22889_693068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22889 ⟨693068, by decide⟩ :=
  accepted_of_selected 11 22889 ⟨693068, by decide⟩ ⟨11, 2, 0, 693068, 22889, 3377, 262144⟩
    (by decide) selected_cut_27413

theorem selected_cut_27414 : selected 9 ⟨693085, by decide⟩
    (prefixPartial 12 91560) = some ⟨12, 2, 0, 693085, 91560, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_91560_693085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91560 ⟨693085, by decide⟩ :=
  accepted_of_selected 12 91560 ⟨693085, by decide⟩ ⟨12, 2, 0, 693085, 91560, 1437, 65536⟩
    (by decide) selected_cut_27414

theorem selected_cut_27415 : selected 9 ⟨693099, by decide⟩
    (prefixPartial 12 91561) = some ⟨12, 2, 0, 693099, 91561, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_91561_693099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91561 ⟨693099, by decide⟩ :=
  accepted_of_selected 12 91561 ⟨693099, by decide⟩ ⟨12, 2, 0, 693099, 91561, 1165, 65536⟩
    (by decide) selected_cut_27415

theorem selected_cut_27416 : selected 9 ⟨693117, by decide⟩
    (prefixPartial 12 91562) = some ⟨12, 2, 0, 693117, 91562, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_91562_693117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91562 ⟨693117, by decide⟩ :=
  accepted_of_selected 12 91562 ⟨693117, by decide⟩ ⟨12, 2, 0, 693117, 91562, 1161, 65536⟩
    (by decide) selected_cut_27416

theorem selected_cut_27417 : selected 9 ⟨693132, by decide⟩
    (prefixPartial 12 91563) = some ⟨12, 2, 0, 693132, 91563, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_91563_693132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91563 ⟨693132, by decide⟩ :=
  accepted_of_selected 12 91563 ⟨693132, by decide⟩ ⟨12, 2, 0, 693132, 91563, 1205, 65536⟩
    (by decide) selected_cut_27417

theorem unmarked_context_11_22890_693133 : frontier 10 ⟨693133, by decide⟩
    (prefixCache 11 22890) (prefixPartial 11 22890) = false := by
  decide +kernel

theorem node_context_11_22890_693133 : EJMOriginalGlobalDAGData.nodes 10 ⟨693133, by decide⟩ =
    .split (coordinate 11) (![⟨693085, by decide⟩,⟨693099, by decide⟩,⟨693117, by decide⟩,⟨693132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22890_693133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22890 ⟨693133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22890
    ⟨693133, by decide⟩ (by decide) (![⟨693085, by decide⟩,⟨693099, by decide⟩,⟨693117, by decide⟩,⟨693132, by decide⟩]) unmarked_context_11_22890_693133 node_context_11_22890_693133
  intro a
  fin_cases a
  · exact context_12_91560_693085
  · exact context_12_91561_693099
  · exact context_12_91562_693117
  · exact context_12_91563_693132

theorem selected_cut_27418 : selected 9 ⟨693149, by decide⟩
    (prefixPartial 12 91564) = some ⟨12, 2, 0, 693149, 91564, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_91564_693149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91564 ⟨693149, by decide⟩ :=
  accepted_of_selected 12 91564 ⟨693149, by decide⟩ ⟨12, 2, 0, 693149, 91564, 1321, 65536⟩
    (by decide) selected_cut_27418

theorem selected_cut_27419 : selected 9 ⟨693165, by decide⟩
    (prefixPartial 12 91565) = some ⟨12, 2, 0, 693165, 91565, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_91565_693165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91565 ⟨693165, by decide⟩ :=
  accepted_of_selected 12 91565 ⟨693165, by decide⟩ ⟨12, 2, 0, 693165, 91565, 1029, 65536⟩
    (by decide) selected_cut_27419

theorem selected_cut_27420 : selected 9 ⟨693177, by decide⟩
    (prefixPartial 12 91566) = some ⟨12, 2, 0, 693177, 91566, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_91566_693177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91566 ⟨693177, by decide⟩ :=
  accepted_of_selected 12 91566 ⟨693177, by decide⟩ ⟨12, 2, 0, 693177, 91566, 1149, 65536⟩
    (by decide) selected_cut_27420

theorem selected_cut_27421 : selected 9 ⟨693190, by decide⟩
    (prefixPartial 12 91567) = some ⟨12, 2, 0, 693190, 91567, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_91567_693190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91567 ⟨693190, by decide⟩ :=
  accepted_of_selected 12 91567 ⟨693190, by decide⟩ ⟨12, 2, 0, 693190, 91567, 1101, 65536⟩
    (by decide) selected_cut_27421

theorem unmarked_context_11_22891_693191 : frontier 10 ⟨693191, by decide⟩
    (prefixCache 11 22891) (prefixPartial 11 22891) = false := by
  decide +kernel

theorem node_context_11_22891_693191 : EJMOriginalGlobalDAGData.nodes 10 ⟨693191, by decide⟩ =
    .split (coordinate 11) (![⟨693149, by decide⟩,⟨693165, by decide⟩,⟨693177, by decide⟩,⟨693190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22891_693191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22891 ⟨693191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22891
    ⟨693191, by decide⟩ (by decide) (![⟨693149, by decide⟩,⟨693165, by decide⟩,⟨693177, by decide⟩,⟨693190, by decide⟩]) unmarked_context_11_22891_693191 node_context_11_22891_693191
  intro a
  fin_cases a
  · exact context_12_91564_693149
  · exact context_12_91565_693165
  · exact context_12_91566_693177
  · exact context_12_91567_693190

theorem unmarked_context_10_5722_693192 : frontier 11 ⟨693192, by decide⟩
    (prefixCache 10 5722) (prefixPartial 10 5722) = false := by
  decide +kernel

theorem node_context_10_5722_693192 : EJMOriginalGlobalDAGData.nodes 11 ⟨693192, by decide⟩ =
    .split (coordinate 10) (![⟨693024, by decide⟩,⟨693068, by decide⟩,⟨693133, by decide⟩,⟨693191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5722_693192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5722 ⟨693192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5722
    ⟨693192, by decide⟩ (by decide) (![⟨693024, by decide⟩,⟨693068, by decide⟩,⟨693133, by decide⟩,⟨693191, by decide⟩]) unmarked_context_10_5722_693192 node_context_10_5722_693192
  intro a
  fin_cases a
  · exact context_11_22888_693024
  · exact context_11_22889_693068
  · exact context_11_22890_693133
  · exact context_11_22891_693191

theorem selected_cut_27422 : selected 9 ⟨693209, by decide⟩
    (prefixPartial 12 91568) = some ⟨12, 2, 0, 693209, 91568, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_91568_693209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91568 ⟨693209, by decide⟩ :=
  accepted_of_selected 12 91568 ⟨693209, by decide⟩ ⟨12, 2, 0, 693209, 91568, 1277, 65536⟩
    (by decide) selected_cut_27422

theorem selected_cut_27423 : selected 9 ⟨693225, by decide⟩
    (prefixPartial 12 91569) = some ⟨12, 2, 0, 693225, 91569, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_91569_693225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91569 ⟨693225, by decide⟩ :=
  accepted_of_selected 12 91569 ⟨693225, by decide⟩ ⟨12, 2, 0, 693225, 91569, 1093, 65536⟩
    (by decide) selected_cut_27423

theorem selected_cut_27424 : selected 9 ⟨693241, by decide⟩
    (prefixPartial 12 91570) = some ⟨12, 2, 0, 693241, 91570, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_91570_693241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91570 ⟨693241, by decide⟩ :=
  accepted_of_selected 12 91570 ⟨693241, by decide⟩ ⟨12, 2, 0, 693241, 91570, 1277, 65536⟩
    (by decide) selected_cut_27424

theorem selected_cut_27425 : selected 9 ⟨693256, by decide⟩
    (prefixPartial 12 91571) = some ⟨12, 2, 0, 693256, 91571, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_91571_693256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91571 ⟨693256, by decide⟩ :=
  accepted_of_selected 12 91571 ⟨693256, by decide⟩ ⟨12, 2, 0, 693256, 91571, 1189, 65536⟩
    (by decide) selected_cut_27425

theorem unmarked_context_11_22892_693257 : frontier 10 ⟨693257, by decide⟩
    (prefixCache 11 22892) (prefixPartial 11 22892) = false := by
  decide +kernel

theorem node_context_11_22892_693257 : EJMOriginalGlobalDAGData.nodes 10 ⟨693257, by decide⟩ =
    .split (coordinate 11) (![⟨693209, by decide⟩,⟨693225, by decide⟩,⟨693241, by decide⟩,⟨693256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22892_693257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22892 ⟨693257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22892
    ⟨693257, by decide⟩ (by decide) (![⟨693209, by decide⟩,⟨693225, by decide⟩,⟨693241, by decide⟩,⟨693256, by decide⟩]) unmarked_context_11_22892_693257 node_context_11_22892_693257
  intro a
  fin_cases a
  · exact context_12_91568_693209
  · exact context_12_91569_693225
  · exact context_12_91570_693241
  · exact context_12_91571_693256

theorem selected_cut_27426 : selected 10 ⟨693296, by decide⟩
    (prefixPartial 11 22893) = some ⟨11, 2, 0, 693296, 22893, 2833, 262144⟩ := by
  decide +kernel

theorem context_11_22893_693296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22893 ⟨693296, by decide⟩ :=
  accepted_of_selected 11 22893 ⟨693296, by decide⟩ ⟨11, 2, 0, 693296, 22893, 2833, 262144⟩
    (by decide) selected_cut_27426

theorem selected_cut_27427 : selected 10 ⟨693345, by decide⟩
    (prefixPartial 11 22894) = some ⟨11, 2, 0, 693345, 22894, 4033, 262144⟩ := by
  decide +kernel

theorem context_11_22894_693345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22894 ⟨693345, by decide⟩ :=
  accepted_of_selected 11 22894 ⟨693345, by decide⟩ ⟨11, 2, 0, 693345, 22894, 4033, 262144⟩
    (by decide) selected_cut_27427

theorem selected_cut_27428 : selected 10 ⟨693386, by decide⟩
    (prefixPartial 11 22895) = some ⟨11, 2, 0, 693386, 22895, 3381, 262144⟩ := by
  decide +kernel

theorem context_11_22895_693386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22895 ⟨693386, by decide⟩ :=
  accepted_of_selected 11 22895 ⟨693386, by decide⟩ ⟨11, 2, 0, 693386, 22895, 3381, 262144⟩
    (by decide) selected_cut_27428

theorem unmarked_context_10_5723_693387 : frontier 11 ⟨693387, by decide⟩
    (prefixCache 10 5723) (prefixPartial 10 5723) = false := by
  decide +kernel

theorem node_context_10_5723_693387 : EJMOriginalGlobalDAGData.nodes 11 ⟨693387, by decide⟩ =
    .split (coordinate 10) (![⟨693257, by decide⟩,⟨693296, by decide⟩,⟨693345, by decide⟩,⟨693386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5723_693387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5723 ⟨693387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5723
    ⟨693387, by decide⟩ (by decide) (![⟨693257, by decide⟩,⟨693296, by decide⟩,⟨693345, by decide⟩,⟨693386, by decide⟩]) unmarked_context_10_5723_693387 node_context_10_5723_693387
  intro a
  fin_cases a
  · exact context_11_22892_693257
  · exact context_11_22893_693296
  · exact context_11_22894_693345
  · exact context_11_22895_693386

theorem unmarked_context_9_1430_693388 : frontier 12 ⟨693388, by decide⟩
    (prefixCache 9 1430) (prefixPartial 9 1430) = false := by
  decide +kernel

theorem node_context_9_1430_693388 : EJMOriginalGlobalDAGData.nodes 12 ⟨693388, by decide⟩ =
    .split (coordinate 9) (![⟨692703, by decide⟩,⟨692954, by decide⟩,⟨693192, by decide⟩,⟨693387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1430_693388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1430 ⟨693388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1430
    ⟨693388, by decide⟩ (by decide) (![⟨692703, by decide⟩,⟨692954, by decide⟩,⟨693192, by decide⟩,⟨693387, by decide⟩]) unmarked_context_9_1430_693388 node_context_9_1430_693388
  intro a
  fin_cases a
  · exact context_10_5720_692703
  · exact context_10_5721_692954
  · exact context_10_5722_693192
  · exact context_10_5723_693387

theorem selected_cut_27429 : selected 10 ⟨693423, by decide⟩
    (prefixPartial 11 22896) = some ⟨11, 2, 0, 693423, 22896, 2925, 262144⟩ := by
  decide +kernel

theorem context_11_22896_693423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22896 ⟨693423, by decide⟩ :=
  accepted_of_selected 11 22896 ⟨693423, by decide⟩ ⟨11, 2, 0, 693423, 22896, 2925, 262144⟩
    (by decide) selected_cut_27429

theorem selected_cut_27430 : selected 10 ⟨693443, by decide⟩
    (prefixPartial 11 22897) = some ⟨11, 2, 0, 693443, 22897, 1981, 262144⟩ := by
  decide +kernel

theorem context_11_22897_693443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22897 ⟨693443, by decide⟩ :=
  accepted_of_selected 11 22897 ⟨693443, by decide⟩ ⟨11, 2, 0, 693443, 22897, 1981, 262144⟩
    (by decide) selected_cut_27430

theorem selected_cut_27431 : selected 10 ⟨693476, by decide⟩
    (prefixPartial 11 22898) = some ⟨11, 2, 0, 693476, 22898, 2589, 262144⟩ := by
  decide +kernel

theorem context_11_22898_693476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22898 ⟨693476, by decide⟩ :=
  accepted_of_selected 11 22898 ⟨693476, by decide⟩ ⟨11, 2, 0, 693476, 22898, 2589, 262144⟩
    (by decide) selected_cut_27431

theorem selected_cut_27432 : selected 10 ⟨693516, by decide⟩
    (prefixPartial 11 22899) = some ⟨11, 2, 0, 693516, 22899, 2841, 262144⟩ := by
  decide +kernel

theorem context_11_22899_693516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22899 ⟨693516, by decide⟩ :=
  accepted_of_selected 11 22899 ⟨693516, by decide⟩ ⟨11, 2, 0, 693516, 22899, 2841, 262144⟩
    (by decide) selected_cut_27432

theorem unmarked_context_10_5724_693517 : frontier 11 ⟨693517, by decide⟩
    (prefixCache 10 5724) (prefixPartial 10 5724) = false := by
  decide +kernel

theorem node_context_10_5724_693517 : EJMOriginalGlobalDAGData.nodes 11 ⟨693517, by decide⟩ =
    .split (coordinate 10) (![⟨693423, by decide⟩,⟨693443, by decide⟩,⟨693476, by decide⟩,⟨693516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5724_693517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5724 ⟨693517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5724
    ⟨693517, by decide⟩ (by decide) (![⟨693423, by decide⟩,⟨693443, by decide⟩,⟨693476, by decide⟩,⟨693516, by decide⟩]) unmarked_context_10_5724_693517 node_context_10_5724_693517
  intro a
  fin_cases a
  · exact context_11_22896_693423
  · exact context_11_22897_693443
  · exact context_11_22898_693476
  · exact context_11_22899_693516

theorem selected_cut_27433 : selected 10 ⟨693538, by decide⟩
    (prefixPartial 11 22900) = some ⟨11, 2, 0, 693538, 22900, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_22900_693538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22900 ⟨693538, by decide⟩ :=
  accepted_of_selected 11 22900 ⟨693538, by decide⟩ ⟨11, 2, 0, 693538, 22900, 2141, 262144⟩
    (by decide) selected_cut_27433

theorem selected_cut_27434 : selected 10 ⟨692795, by decide⟩
    (prefixPartial 11 22901) = some ⟨11, 2, 0, 692795, 22901, 5, 262144⟩ := by
  decide +kernel

theorem context_11_22901_692795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22901 ⟨692795, by decide⟩ :=
  accepted_of_selected 11 22901 ⟨692795, by decide⟩ ⟨11, 2, 0, 692795, 22901, 5, 262144⟩
    (by decide) selected_cut_27434

theorem selected_cut_27435 : selected 10 ⟨693557, by decide⟩
    (prefixPartial 11 22902) = some ⟨11, 2, 0, 693557, 22902, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_22902_693557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22902 ⟨693557, by decide⟩ :=
  accepted_of_selected 11 22902 ⟨693557, by decide⟩ ⟨11, 2, 0, 693557, 22902, 1857, 262144⟩
    (by decide) selected_cut_27435

theorem selected_cut_27436 : selected 10 ⟨693584, by decide⟩
    (prefixPartial 11 22903) = some ⟨11, 2, 0, 693584, 22903, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_22903_693584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22903 ⟨693584, by decide⟩ :=
  accepted_of_selected 11 22903 ⟨693584, by decide⟩ ⟨11, 2, 0, 693584, 22903, 1857, 262144⟩
    (by decide) selected_cut_27436

theorem unmarked_context_10_5725_693585 : frontier 11 ⟨693585, by decide⟩
    (prefixCache 10 5725) (prefixPartial 10 5725) = false := by
  decide +kernel

theorem node_context_10_5725_693585 : EJMOriginalGlobalDAGData.nodes 11 ⟨693585, by decide⟩ =
    .split (coordinate 10) (![⟨693538, by decide⟩,⟨692795, by decide⟩,⟨693557, by decide⟩,⟨693584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5725_693585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5725 ⟨693585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5725
    ⟨693585, by decide⟩ (by decide) (![⟨693538, by decide⟩,⟨692795, by decide⟩,⟨693557, by decide⟩,⟨693584, by decide⟩]) unmarked_context_10_5725_693585 node_context_10_5725_693585
  intro a
  fin_cases a
  · exact context_11_22900_693538
  · exact context_11_22901_692795
  · exact context_11_22902_693557
  · exact context_11_22903_693584

theorem selected_cut_27437 : selected 10 ⟨693599, by decide⟩
    (prefixPartial 11 22904) = some ⟨11, 2, 0, 693599, 22904, 1405, 262144⟩ := by
  decide +kernel

theorem context_11_22904_693599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22904 ⟨693599, by decide⟩ :=
  accepted_of_selected 11 22904 ⟨693599, by decide⟩ ⟨11, 2, 0, 693599, 22904, 1405, 262144⟩
    (by decide) selected_cut_27437

theorem selected_cut_27438 : selected 10 ⟨693612, by decide⟩
    (prefixPartial 11 22905) = some ⟨11, 2, 0, 693612, 22905, 877, 262144⟩ := by
  decide +kernel

theorem context_11_22905_693612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22905 ⟨693612, by decide⟩ :=
  accepted_of_selected 11 22905 ⟨693612, by decide⟩ ⟨11, 2, 0, 693612, 22905, 877, 262144⟩
    (by decide) selected_cut_27438

theorem selected_cut_27439 : selected 10 ⟨693628, by decide⟩
    (prefixPartial 11 22906) = some ⟨11, 2, 0, 693628, 22906, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_22906_693628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22906 ⟨693628, by decide⟩ :=
  accepted_of_selected 11 22906 ⟨693628, by decide⟩ ⟨11, 2, 0, 693628, 22906, 1101, 262144⟩
    (by decide) selected_cut_27439

theorem selected_cut_27440 : selected 10 ⟨693644, by decide⟩
    (prefixPartial 11 22907) = some ⟨11, 2, 0, 693644, 22907, 913, 262144⟩ := by
  decide +kernel

theorem context_11_22907_693644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22907 ⟨693644, by decide⟩ :=
  accepted_of_selected 11 22907 ⟨693644, by decide⟩ ⟨11, 2, 0, 693644, 22907, 913, 262144⟩
    (by decide) selected_cut_27440

theorem unmarked_context_10_5726_693645 : frontier 11 ⟨693645, by decide⟩
    (prefixCache 10 5726) (prefixPartial 10 5726) = false := by
  decide +kernel

theorem node_context_10_5726_693645 : EJMOriginalGlobalDAGData.nodes 11 ⟨693645, by decide⟩ =
    .split (coordinate 10) (![⟨693599, by decide⟩,⟨693612, by decide⟩,⟨693628, by decide⟩,⟨693644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5726_693645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5726 ⟨693645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5726
    ⟨693645, by decide⟩ (by decide) (![⟨693599, by decide⟩,⟨693612, by decide⟩,⟨693628, by decide⟩,⟨693644, by decide⟩]) unmarked_context_10_5726_693645 node_context_10_5726_693645
  intro a
  fin_cases a
  · exact context_11_22904_693599
  · exact context_11_22905_693612
  · exact context_11_22906_693628
  · exact context_11_22907_693644

theorem selected_cut_27441 : selected 11 ⟨693670, by decide⟩
    (prefixPartial 10 5727) = some ⟨10, 2, 0, 693670, 5727, 1661, 1048576⟩ := by
  decide +kernel

theorem context_10_5727_693670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5727 ⟨693670, by decide⟩ :=
  accepted_of_selected 10 5727 ⟨693670, by decide⟩ ⟨10, 2, 0, 693670, 5727, 1661, 1048576⟩
    (by decide) selected_cut_27441

theorem unmarked_context_9_1431_693671 : frontier 12 ⟨693671, by decide⟩
    (prefixCache 9 1431) (prefixPartial 9 1431) = false := by
  decide +kernel

theorem node_context_9_1431_693671 : EJMOriginalGlobalDAGData.nodes 12 ⟨693671, by decide⟩ =
    .split (coordinate 9) (![⟨693517, by decide⟩,⟨693585, by decide⟩,⟨693645, by decide⟩,⟨693670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1431_693671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1431 ⟨693671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1431
    ⟨693671, by decide⟩ (by decide) (![⟨693517, by decide⟩,⟨693585, by decide⟩,⟨693645, by decide⟩,⟨693670, by decide⟩]) unmarked_context_9_1431_693671 node_context_9_1431_693671
  intro a
  fin_cases a
  · exact context_10_5724_693517
  · exact context_10_5725_693585
  · exact context_10_5726_693645
  · exact context_10_5727_693670

theorem unmarked_context_8_357_693672 : frontier 13 ⟨693672, by decide⟩
    (prefixCache 8 357) (prefixPartial 8 357) = false := by
  decide +kernel

theorem node_context_8_357_693672 : EJMOriginalGlobalDAGData.nodes 13 ⟨693672, by decide⟩ =
    .split (coordinate 8) (![⟨690553, by decide⟩,⟨692315, by decide⟩,⟨693388, by decide⟩,⟨693671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_357_693672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 357 ⟨693672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 357
    ⟨693672, by decide⟩ (by decide) (![⟨690553, by decide⟩,⟨692315, by decide⟩,⟨693388, by decide⟩,⟨693671, by decide⟩]) unmarked_context_8_357_693672 node_context_8_357_693672
  intro a
  fin_cases a
  · exact context_9_1428_690553
  · exact context_9_1429_692315
  · exact context_9_1430_693388
  · exact context_9_1431_693671

theorem selected_cut_27442 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 22912) = some ⟨11, 1, 0, 434745, 22912, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22912_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22912 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 22912 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 22912, 1, 262144⟩
    (by decide) selected_cut_27442

theorem selected_cut_27443 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91652) = some ⟨12, 1, 0, 448748, 91652, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91652_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91652 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91652 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91652, 1, 65536⟩
    (by decide) selected_cut_27443

theorem selected_cut_27444 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 91653) = some ⟨12, 1, 0, 34034, 91653, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91653_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91653 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 91653 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 91653, 1, 65536⟩
    (by decide) selected_cut_27444

theorem selected_cut_27445 : selected 8 ⟨693724, by decide⟩
    (prefixPartial 13 366616) = some ⟨13, 2, 0, 693724, 366616, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_366616_693724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366616 ⟨693724, by decide⟩ :=
  accepted_of_selected 13 366616 ⟨693724, by decide⟩ ⟨13, 2, 0, 693724, 366616, 2133, 16384⟩
    (by decide) selected_cut_27445

theorem selected_cut_27446 : selected 8 ⟨693758, by decide⟩
    (prefixPartial 13 366617) = some ⟨13, 2, 0, 693758, 366617, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_366617_693758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366617 ⟨693758, by decide⟩ :=
  accepted_of_selected 13 366617 ⟨693758, by decide⟩ ⟨13, 2, 0, 693758, 366617, 1301, 16384⟩
    (by decide) selected_cut_27446

theorem selected_cut_27447 : selected 8 ⟨693766, by decide⟩
    (prefixPartial 13 366618) = some ⟨13, 2, 0, 693766, 366618, 561, 16384⟩ := by
  decide +kernel

theorem context_13_366618_693766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366618 ⟨693766, by decide⟩ :=
  accepted_of_selected 13 366618 ⟨693766, by decide⟩ ⟨13, 2, 0, 693766, 366618, 561, 16384⟩
    (by decide) selected_cut_27447

theorem selected_cut_27448 : selected 8 ⟨676864, by decide⟩
    (prefixPartial 13 366619) = some ⟨13, 2, 0, 676864, 366619, 145, 16384⟩ := by
  decide +kernel

theorem context_13_366619_676864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366619 ⟨676864, by decide⟩ :=
  accepted_of_selected 13 366619 ⟨676864, by decide⟩ ⟨13, 2, 0, 676864, 366619, 145, 16384⟩
    (by decide) selected_cut_27448

theorem unmarked_context_12_91654_693767 : frontier 9 ⟨693767, by decide⟩
    (prefixCache 12 91654) (prefixPartial 12 91654) = false := by
  decide +kernel

theorem node_context_12_91654_693767 : EJMOriginalGlobalDAGData.nodes 9 ⟨693767, by decide⟩ =
    .split (coordinate 12) (![⟨693724, by decide⟩,⟨693758, by decide⟩,⟨693766, by decide⟩,⟨676864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91654_693767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91654 ⟨693767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91654
    ⟨693767, by decide⟩ (by decide) (![⟨693724, by decide⟩,⟨693758, by decide⟩,⟨693766, by decide⟩,⟨676864, by decide⟩]) unmarked_context_12_91654_693767 node_context_12_91654_693767
  intro a
  fin_cases a
  · exact context_13_366616_693724
  · exact context_13_366617_693758
  · exact context_13_366618_693766
  · exact context_13_366619_676864

theorem selected_cut_27449 : selected 8 ⟨693830, by decide⟩
    (prefixPartial 13 366620) = some ⟨13, 2, 0, 693830, 366620, 3213, 16384⟩ := by
  decide +kernel

theorem context_13_366620_693830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366620 ⟨693830, by decide⟩ :=
  accepted_of_selected 13 366620 ⟨693830, by decide⟩ ⟨13, 2, 0, 693830, 366620, 3213, 16384⟩
    (by decide) selected_cut_27449

theorem selected_cut_27450 : selected 8 ⟨693880, by decide⟩
    (prefixPartial 13 366621) = some ⟨13, 2, 0, 693880, 366621, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_366621_693880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366621 ⟨693880, by decide⟩ :=
  accepted_of_selected 13 366621 ⟨693880, by decide⟩ ⟨13, 2, 0, 693880, 366621, 2589, 16384⟩
    (by decide) selected_cut_27450

theorem selected_cut_27451 : selected 8 ⟨693900, by decide⟩
    (prefixPartial 13 366622) = some ⟨13, 2, 0, 693900, 366622, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_366622_693900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366622 ⟨693900, by decide⟩ :=
  accepted_of_selected 13 366622 ⟨693900, by decide⟩ ⟨13, 2, 0, 693900, 366622, 1801, 16384⟩
    (by decide) selected_cut_27451

theorem selected_cut_27452 : selected 8 ⟨693906, by decide⟩
    (prefixPartial 13 366623) = some ⟨13, 2, 0, 693906, 366623, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_366623_693906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366623 ⟨693906, by decide⟩ :=
  accepted_of_selected 13 366623 ⟨693906, by decide⟩ ⟨13, 2, 0, 693906, 366623, 1121, 16384⟩
    (by decide) selected_cut_27452

theorem unmarked_context_12_91655_693907 : frontier 9 ⟨693907, by decide⟩
    (prefixCache 12 91655) (prefixPartial 12 91655) = false := by
  decide +kernel

theorem node_context_12_91655_693907 : EJMOriginalGlobalDAGData.nodes 9 ⟨693907, by decide⟩ =
    .split (coordinate 12) (![⟨693830, by decide⟩,⟨693880, by decide⟩,⟨693900, by decide⟩,⟨693906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91655_693907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91655 ⟨693907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91655
    ⟨693907, by decide⟩ (by decide) (![⟨693830, by decide⟩,⟨693880, by decide⟩,⟨693900, by decide⟩,⟨693906, by decide⟩]) unmarked_context_12_91655_693907 node_context_12_91655_693907
  intro a
  fin_cases a
  · exact context_13_366620_693830
  · exact context_13_366621_693880
  · exact context_13_366622_693900
  · exact context_13_366623_693906

theorem unmarked_context_11_22913_693908 : frontier 10 ⟨693908, by decide⟩
    (prefixCache 11 22913) (prefixPartial 11 22913) = false := by
  decide +kernel

theorem node_context_11_22913_693908 : EJMOriginalGlobalDAGData.nodes 10 ⟨693908, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨693767, by decide⟩,⟨693907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22913_693908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22913 ⟨693908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22913
    ⟨693908, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨693767, by decide⟩,⟨693907, by decide⟩]) unmarked_context_11_22913_693908 node_context_11_22913_693908
  intro a
  fin_cases a
  · exact context_12_91652_448748
  · exact context_12_91653_34034
  · exact context_12_91654_693767
  · exact context_12_91655_693907

theorem selected_cut_27453 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91656) = some ⟨12, 1, 0, 448748, 91656, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91656_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91656 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91656 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91656, 1, 65536⟩
    (by decide) selected_cut_27453

theorem selected_cut_27454 : selected 8 ⟨693987, by decide⟩
    (prefixPartial 13 366628) = some ⟨13, 2, 0, 693987, 366628, 3733, 16384⟩ := by
  decide +kernel

theorem context_13_366628_693987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366628 ⟨693987, by decide⟩ :=
  accepted_of_selected 13 366628 ⟨693987, by decide⟩ ⟨13, 2, 0, 693987, 366628, 3733, 16384⟩
    (by decide) selected_cut_27454

theorem selected_cut_27455 : selected 8 ⟨694064, by decide⟩
    (prefixPartial 13 366629) = some ⟨13, 2, 0, 694064, 366629, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_366629_694064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366629 ⟨694064, by decide⟩ :=
  accepted_of_selected 13 366629 ⟨694064, by decide⟩ ⟨13, 2, 0, 694064, 366629, 2981, 16384⟩
    (by decide) selected_cut_27455

theorem selected_cut_27456 : selected 8 ⟨694088, by decide⟩
    (prefixPartial 13 366630) = some ⟨13, 2, 0, 694088, 366630, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_366630_694088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366630 ⟨694088, by decide⟩ :=
  accepted_of_selected 13 366630 ⟨694088, by decide⟩ ⟨13, 2, 0, 694088, 366630, 1817, 16384⟩
    (by decide) selected_cut_27456

theorem selected_cut_27457 : selected 8 ⟨694104, by decide⟩
    (prefixPartial 13 366631) = some ⟨13, 2, 0, 694104, 366631, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_366631_694104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 366631 ⟨694104, by decide⟩ :=
  accepted_of_selected 13 366631 ⟨694104, by decide⟩ ⟨13, 2, 0, 694104, 366631, 1145, 16384⟩
    (by decide) selected_cut_27457

theorem unmarked_context_12_91657_694105 : frontier 9 ⟨694105, by decide⟩
    (prefixCache 12 91657) (prefixPartial 12 91657) = false := by
  decide +kernel

theorem node_context_12_91657_694105 : EJMOriginalGlobalDAGData.nodes 9 ⟨694105, by decide⟩ =
    .split (coordinate 12) (![⟨693987, by decide⟩,⟨694064, by decide⟩,⟨694088, by decide⟩,⟨694104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91657_694105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91657 ⟨694105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91657
    ⟨694105, by decide⟩ (by decide) (![⟨693987, by decide⟩,⟨694064, by decide⟩,⟨694088, by decide⟩,⟨694104, by decide⟩]) unmarked_context_12_91657_694105 node_context_12_91657_694105
  intro a
  fin_cases a
  · exact context_13_366628_693987
  · exact context_13_366629_694064
  · exact context_13_366630_694088
  · exact context_13_366631_694104

theorem selected_cut_27458 : selected 7 ⟨694130, by decide⟩
    (prefixPartial 14 1466528) = some ⟨14, 2, 0, 694130, 1466528, 989, 4096⟩ := by
  decide +kernel

theorem context_14_1466528_694130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1466528 ⟨694130, by decide⟩ :=
  accepted_of_selected 14 1466528 ⟨694130, by decide⟩ ⟨14, 2, 0, 694130, 1466528, 989, 4096⟩
    (by decide) selected_cut_27458

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
